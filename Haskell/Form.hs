module Form where

{-
Paradox/Equinox -- Copyright (c) 2003-2007, Koen Claessen, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-}

import Data.Set as S( Set )
import qualified Data.Set as S
import Data.Map as M( Map )
import qualified Data.Map as M
import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad

import Name

----------------------------------------------------------------------
-- Type

data Type
  = Type
  { tname  :: Name
  , tsize  :: Maybe Int
  , tequal :: Equality
  }
 deriving ( Eq, Ord )

data Equality
  -- this order matters!
  = Safe
  | Half
  | Full
 deriving ( Eq, Ord, Show )

instance Show Type where
  show (Type t s e) = show t ++ showSize s ++ showEq e
   where
    showEq Half = "_eq"
    showEq Full = "_heq"
    showEq _    = ""
    
    showSize Nothing  = ""
    showSize (Just n) = "_" ++ show n

tdomain :: Type -> Maybe Int
tdomain t =
  case tsize t of
    Nothing -> Nothing
    Just n  -> case tequal t of
                 Safe -> Just n
                 Half -> Just (n+1)
                 Full -> Nothing

top, bool :: Type
top  = Type (prim "Top")  Nothing  Full
bool = Type (prim "Bool") (Just 2) Safe

data Typing
  = [Type] :-> Type
  | V Type
 deriving ( Eq, Ord )

opers :: Show a => String -> [a] -> ShowS
opers op xs = foldr (.) id (intersperse (showString op) (map shows xs))

commas :: Show a => [a] -> ShowS
commas = opers ","

instance Show Typing where
  showsPrec n (V t)       = showsPrec n t
  showsPrec n ([]  :-> t) = showsPrec n t
  showsPrec n ([s] :-> t) = showsPrec n s
                          . showString " -> "
                          . showsPrec n t
  showsPrec n (ts  :-> t) = showString "("
                          . commas ts
                          . showString ") -> "
                          . showsPrec n t

----------------------------------------------------------------------
-- Symbol

data Symbol
  = Name ::: Typing
 deriving ( Eq, Ord )

instance Show Symbol where
{-
  showsPrec n (x ::: V t) | t /= top =
      showsPrec n x
    . showString ":"
    . showsPrec n t
-}
  showsPrec n (x ::: _) =
      showsPrec n x

arity :: Symbol -> Int
arity (_ ::: (xs :-> _)) = length xs
arity _                  = 0

typing :: Symbol -> Typing
typing (_ ::: tp) = tp

isVarSymbol :: Symbol -> Bool
isVarSymbol (_ ::: V _) = True
isVarSymbol _           = False

isPredSymbol :: Symbol -> Bool
isPredSymbol s@(_ ::: (_ :-> t)) = t == bool
isPredSymbol _                   = False

isFunSymbol s = not (isVarSymbol s || isPredSymbol s)
isConstantSymbol s = isFunSymbol s && arity s == 0

----------------------------------------------------------------------
-- Term

data Term
  = Fun Symbol [Term]
  | Var Symbol
 deriving ( Eq, Ord )

typ :: Term -> Type
typ (Var (_ ::: V tp))         = tp
typ (Fun (_ ::: (_ :-> tp)) _) = tp

instance Show Term where
  showsPrec n (Fun f []) = showsPrec n f
  showsPrec n (Fun f xs) = showsPrec n f
                         . showString "("
                         . commas xs
                         . showString ")"
  showsPrec n (Var x)    = showsPrec n x

var :: Type -> Int -> Symbol
var t i = (vr % i) ::: V t

data Atom
  = Term :=: Term
 deriving ( Eq, Ord )

instance Show Atom where
  showsPrec n (a :=: b)
    | b == truth = showsPrec n a
    | otherwise  = showsPrec n a
                 . showString " = "
                 . showsPrec n b

truth :: Term
truth = Fun (tr ::: ([] :-> bool)) []

prd :: Symbol -> [Term] -> Atom
prd p ts = Fun p ts :=: truth

data Bind a
  = Bind Symbol a
 deriving ( Eq, Ord )

instance Show a => Show (Bind a) where
  showsPrec n (Bind x a) = showString "["
                         . showsPrec n x
                         . showString "] : "
                         . showsPrec n a

data Form
  = Atom Atom
  | And (Set Form)
  | Or (Set Form)
  | Form `Equiv` Form
  | Not Form
  | ForAll (Bind Form)
  | Exists (Bind Form)
 deriving ( Eq, Ord )

instance Show Form where
  showsPrec n (Not (Atom (a :=: b))) | b /= truth
                            = showsPrec n a
                            . showString " != "
                            . showsPrec n b

  showsPrec n (Atom (a :=: t)) | t == truth
                            = showsPrec n a

  showsPrec n (Atom a)      = showsPrec n a
  showsPrec n (And xs)      = showsOps "&" "$true" (S.toList xs)
  showsPrec n (Or xs)       = showsOps "|" "$false" (S.toList xs)
  showsPrec n (x `Equiv` y) = showString "("
                            . showsPrec n x
                            . showString " <=> "
                            . showsPrec n y
                            . showString ")"
  showsPrec n (Not x)       = showString "~" . showsPrec n x
  showsPrec n (ForAll b)    = showString "!"
                            . showsPrec n b
  showsPrec n (Exists b)    = showString "?"
                            . showsPrec n b

showsOps op unit []  = showString unit
showsOps op unit [x] = shows x
showsOps op unit xs  = showString "("
                     . opers (" " ++ op ++ " ") xs
                     . showString ")"

mapOverTerms :: (Term -> Term) -> Form -> Form
mapOverTerms f (Atom (t1 :=: t2)) = Atom ((f t1) :=: (f t2))
mapOverTerms f form                                                 = mapOverAtoms (mapOverTerms f) form 

mapOverAtoms :: (Form -> Form) -> Form -> Form
mapOverAtoms f (Not form)               = Not (f (mapOverAtoms f form))
mapOverAtoms f (And fs)                 = And $ S.map (mapOverAtoms f) fs
mapOverAtoms f (Or fs)                          = Or  $ S.map (mapOverAtoms f) fs
mapOverAtoms f (Equiv f1 f2)  = Equiv (mapOverAtoms f f1) (mapOverAtoms f f2)
mapOverAtoms f (Exists (Bind b form)) = Exists (Bind b (mapOverAtoms f form))
mapOverAtoms f (ForAll (Bind b form)) = ForAll (Bind b (mapOverAtoms f form))
mapOverAtoms f form = f form



funArity (Fun s _) = arity s
predArity (Atom (t :=: _)) = funArity t



data Signed a
  = Pos a
  | Neg a
 deriving ( Eq, Ord )

instance Show a => Show (Signed a) where
  showsPrec n (Pos x) = showsPrec n x
  showsPrec n (Neg x) = showString "~"
                      . showsPrec n x

instance Functor Signed where
  fmap f (Pos x) = Pos (f x)
  fmap f (Neg x) = Neg (f x)

negat :: Signed a -> Signed a
negat (Pos x) = Neg x
negat (Neg x) = Pos x

the :: Signed a -> a
the (Pos x) = x
the (Neg x) = x

sign :: Signed a -> Bool
sign (Pos _) = True
sign (Neg _) = False

type Clause = [Signed Atom]

showClause :: Clause -> String
showClause [] = "$false"
showClause c  = show (foldr1 (\/) ([ Atom a | Pos a <- c ] ++ [ Not (Atom a) | Neg a <- c ]))

toForm :: Clause -> Form
toForm ls = foldr forAll (Or (S.fromList (map sign ls))) (S.toList (free ls))
 where
  sign (Pos x) = Atom x
  sign (Neg x) = Not (Atom x)

data QClause = Uniq (Bind Clause)
  deriving ( Eq, Ord, Show )


----------------------------------------------------------------------
-- constructors

true, false :: Form
true  = And S.empty
false = Or S.empty

nt :: Form -> Form
nt (Not a) = a
nt a       = Not a

(.=>) :: Form -> Form -> Form
p .=> q = nt p \/ q

(/\), (\/) :: Form -> Form -> Form
And as /\ And bs = And (as `S.union` bs)
a      /\ b 
  | a == false   = false
  | b == false   = false
And as /\ b      = And (b `S.insert` as)
a      /\ And bs = And (a `S.insert` bs)
a      /\ b      = And (S.fromList [a,b])

Or as \/ Or bs = Or (as `S.union` bs)
a     \/ b
  | a == true  = true
  | b == true  = true
Or as \/ b     = Or (b `S.insert` as)
a     \/ Or bs = Or (a `S.insert` bs)
a     \/ b     = Or (S.fromList [a,b])

-- quantify over all variables found in first argument
forEvery, exist :: Symbolic a => a -> Form -> Form
forEvery vs a = foldr forAll a (S.toList (free vs))
exist    vs a = foldr exists a (S.toList (free vs))

forAll_, exists_ :: Symbol -> Form -> Form
forAll_ v a = ForAll (Bind v a)
exists_ v a = Exists (Bind v a)

forAll, exists :: Symbol -> Form -> Form
--forAll x a = ForAll (Bind x a)
--exists x a = Exists (Bind x a)

forAll v a = 
  case positive a of
    And as ->
      And (S.map (forAll v) as)
    
    ForAll (Bind w a)
      | v == w    -> ForAll (Bind w a)
      | otherwise -> ForAll (Bind w (forAll v a))

    Or as -> yes \/ no
     where
      avss      = [ (a, free a) | a <- S.toList as ]
      (bs1,bs2) = partition ((v `S.member`) . snd) avss
      no        = orl [ b | (b,_) <- bs2 ]
      body      = orl [ b | (b,_) <- bs1 ]
      yes       = case bs1 of
                    []      -> orl []
                    [(b,_)] -> forAll v b
                    _       -> ForAll (Bind v body)

      orl [a] = a
      orl as  = Or (S.fromList as)

    _ -> ForAll (Bind v a)

    --a | v `member` vs -> ForAll (v `delete` vs) v a
    --  | otherwise     -> a
    -- where
    --  vs = free a 
   
exists v a = nt (forAll v (nt a))

positive :: Form -> Form
positive (Not (And as))            = Or (S.map nt as)
positive (Not (Or as))             = And (S.map nt as)
positive (Not (a `Equiv` b))       = nt a `Equiv` b
positive (Not (Not a))             = positive a
positive (Not (ForAll (Bind v a))) = Exists (Bind v (nt a))
positive (Not (Exists (Bind v a))) = ForAll (Bind v (nt a))
positive a                         = a -- only (negations of) atoms

simple :: Form -> Form
simple (Or as)             = Not (And (S.map nt as))
simple (Exists (Bind v a)) = Not (ForAll (Bind v (nt a)))
simple a                   = a

----------------------------------------------------------------------
-- substitution

data Subst 
  = Subst
  { vars :: Set Symbol
  , mapp :: Map Symbol Term
  }
 deriving ( Eq, Ord )

instance Show Subst where
  showsPrec n sub = showsPrec n (mapp sub)

ids :: Subst
ids = Subst S.empty M.empty

(|=>) :: Symbol -> Term -> Subst
v |=> x = Subst (free x) (M.singleton v x)

(|+|) :: Subst -> Subst -> Subst
Subst vs mp |+| Subst vs' mp' = Subst (vs `S.union` vs') (mp `M.union` mp')

look :: Symbol -> Term -> Subst -> Term
look v t sub =
  case M.lookup v (mapp sub) of
    Nothing -> t
    Just t' -> t'

----------------------------------------------------------------------
-- my own maybe type

type Mybe r a = r -> (a -> r) -> r

nothing :: Mybe r a
nothing = \no yes -> no

just :: a -> Mybe r a
just x = \no yes -> yes x

mlift1 :: (a -> b) -> Mybe r a -> Mybe r b
mlift1 f m = \no yes -> m no (\x -> yes (f x))

mlift2 :: (a -> b -> c) -> Mybe r a -> Mybe r b -> Mybe r c
mlift2 f m1 m2 = \no yes -> m1 no (\x -> m2 no (\y -> yes (f x y)))

----------------------------------------------------------------------
-- destructors

class Symbolic a where
  symbols   :: a -> Set Symbol
  free      :: a -> Set Symbol
  subterms  :: a -> Set Term
  subst'    :: Subst -> a -> Maybe a
  occurring :: Symbol -> a -> State [Term] a

{-
  symbols{| Unit |}    Unit      = S.empty
  symbols{| a :*: b |} (x :*: y) = symbols x `S.union` symbols y
  symbols{| a :+: b |} (Inl x)   = symbols x
  symbols{| a :+: b |} (Inr y)   = symbols y

  free{| Unit |}    Unit      = S.empty
  free{| a :*: b |} (x :*: y) = free x `S.union` free y
  free{| a :+: b |} (Inl x)   = free x
  free{| a :+: b |} (Inr y)   = free y

  subterms{| Unit |}    Unit      = S.empty
  subterms{| a :*: b |} (x :*: y) = subterms x `S.union` subterms y
  subterms{| a :+: b |} (Inl x)   = subterms x
  subterms{| a :+: b |} (Inr y)   = subterms y

  subst'{| Unit |}    sub Unit      = nothing
  subst'{| a :*: b |} sub (x :*: y) = \no yes ->
    subst' sub x (subst' sub y no (\y' -> yes (x :*: y'))) (\x' ->
      subst' sub y (yes (x' :*: y)) (\y' -> yes (x' :*: y')))
  subst'{| a :+: b |} sub (Inl x)   = mlift1 Inl (subst' sub x)
  subst'{| a :+: b |} sub (Inr y)   = mlift1 Inr (subst' sub y)
-}

subst :: Symbolic a => Subst -> a -> a
subst sub a = case subst' sub a of
                Nothing -> a
                Just a' -> a'

isGround :: Symbolic a => a -> Bool
isGround x = S.null (free x)

takeTerm :: Term -> State [Term] Term
takeTerm t = do
  ts <- get
  case ts of
    [] -> return t
    (t':ts') -> do
      put ts'
      return t'

instance Symbolic () where
  symbols     () = S.empty
  free        () = S.empty
  subterms    () = S.empty
  subst' sub  () = Nothing
  occurring s () = return ()

instance (Symbolic a, Symbolic b) => Symbolic (a,b) where
  symbols     (x,y) = symbols x `S.union` symbols y
  free        (x,y) = free x `S.union` free y
  subterms    (x,y) = subterms x `S.union` subterms y
  subst' sub  (x,y) =
    case (subst' sub x, subst' sub y) of
      (Nothing, Nothing) -> Nothing
      (mx,      my)      -> Just (maybe x id mx, maybe y id my)
  occurring s (x,y) = liftM2 (,) (occurring s x) (occurring s y)

instance Symbolic a => Symbolic (Signed a) where
  symbols (Pos x) = symbols x
  symbols (Neg x) = symbols x
  
  free (Pos x) = free x
  free (Neg x) = free x
  
  subterms (Pos x) = subterms x
  subterms (Neg x) = subterms x
  
  subst' sub (Pos x) = Pos `fmap` subst' sub x
  subst' sub (Neg x) = Neg `fmap` subst' sub x

  occurring s (Pos x) = Pos `fmap` occurring s x
  occurring s (Neg x) = Neg `fmap` occurring s x

instance Symbolic a => Symbolic [a] where
  symbols []     = S.empty
  symbols (x:xs) = symbols (x,xs)
  
  free []     = S.empty
  free (x:xs) = free (x,xs)
  
  subterms []     = S.empty
  subterms (x:xs) = subterms (x,xs)
  
  subst' sub []     = Nothing
  subst' sub (x:xs) = uncurry (:) `fmap` subst' sub (x,xs)

  occurring s [] = return []
  occurring s (x:xs) = liftM2 (:) (occurring s x) (occurring s xs)

instance (Ord a, Symbolic a) => Symbolic (Set a) where
  symbols s        = symbols (S.toList s)
  free s           = free (S.toList s)
  subterms s       = subterms (S.toList s)
  subst' sub       = (S.fromList `fmap`) . subst' sub . S.toList
  occurring s set  = fmap S.fromList (occurring s (S.toList set))

instance Symbolic Atom where
  symbols     (s :=: t) = symbols (s,t)
  free        (s :=: t) = free (s,t)
  subterms    (s :=: t) = subterms (s,t)
  subst' sub  (s :=: t) = uncurry (:=:) `fmap` subst' sub (s,t)
  occurring u (s :=: t) = liftM2 (:=:) (occurring u s) (occurring u t)

instance Symbolic QClause where
  symbols     (Uniq q) = symbols q
  free        (Uniq q) = free q
  subterms    (Uniq q) = subterms q
  subst' sub  (Uniq q) = Uniq `fmap` subst' sub q
  occurring s (Uniq q) = Uniq `fmap` occurring s q

instance Symbolic Form where
  symbols (Atom a)      = symbols a
  symbols (And xs)      = symbols xs
  symbols (Or xs)       = symbols xs
  symbols (x `Equiv` y) = symbols (x,y)
  symbols (Not x)       = symbols x
  symbols (ForAll q)    = symbols q
  symbols (Exists q)    = symbols q

  free (Atom a)      = free a
  free (And xs)      = free xs
  free (Or xs)       = free xs
  free (x `Equiv` y) = free (x,y)
  free (Not x)       = free x
  free (ForAll q)    = free q
  free (Exists q)    = free q

  subterms (Atom a)      = subterms a
  subterms (And xs)      = subterms xs
  subterms (Or xs)       = subterms xs
  subterms (x `Equiv` y) = subterms (x,y)
  subterms (Not x)       = subterms x
  subterms (ForAll q)    = subterms q
  subterms (Exists q)    = subterms q

  subst' sub (Atom a)      = Atom `fmap` subst' sub a
  subst' sub (And xs)      = And `fmap` subst' sub xs
  subst' sub (Or xs)       = Or `fmap` subst' sub xs
  subst' sub (x `Equiv` y) = uncurry Equiv `fmap` subst' sub (x,y)
  subst' sub (Not x)       = Not `fmap` subst' sub x
  subst' sub (ForAll q)    = ForAll `fmap` subst' sub q
  subst' sub (Exists q)    = Exists `fmap` subst' sub q

  occurring s (Atom a)      = Atom `fmap` occurring s a
  occurring s (And xs)      = And `fmap` occurring s xs
  occurring s (Or xs)       = Or `fmap` occurring s xs
  occurring s (x `Equiv` y) = liftM2 Equiv (occurring s x) (occurring s y)
  occurring s (Not x)       = Not `fmap` occurring s x
  occurring s (ForAll q)    = ForAll `fmap` occurring s q
  occurring s (Exists q)    = Exists `fmap` occurring s q

instance Symbolic Term where
  symbols (Fun f xs) = f `S.insert` symbols xs
  symbols (Var x)    = S.singleton x

  free (Fun _ xs) = free xs
  free (Var v)    = S.singleton v

  --subst sub (Fun f xs) = Fun f (subst sub xs)
  --subst sub x@(Var v)  = look v x sub

  subterms t = t `S.insert`
    case t of
      Fun f xs -> subterms xs
      _        -> S.empty

  subst' sub (Fun f xs) = Fun f `fmap` subst' sub xs
  subst' sub x@(Var v)  = M.lookup v (mapp sub)

  occurring s (Fun f xs) = Fun f `fmap` occurring s xs
  occurring s x@(Var v)
    | s == v = takeTerm x
    | otherwise = return x

instance Symbolic a => Symbolic (Bind a) where
  symbols   (Bind v a) = v `S.insert` symbols a
  free      (Bind v a) = v `S.delete` free a
  subterms  (Bind v a) = subterms a
{-
  subst sub (Bind v a) = Bind v' (subst (Subst vs' mp') a)
   where
    Subst vs mp = sub
   
    forbidden = vs `S.union` free a

    allowed   = [ v'
                | let n ::: t = v
                , v' <- v
                      : [ name [c] ::: t | c <- ['V'..'Z'] ]
                     ++ [ (n % i) ::: t | i <- [0..] ]
                , not (v' `S.member` forbidden) 
                ]

    v'        = head allowed

    vs'       = v' `S.insert` vs

    mp'       = M.fromList
                ( [ (v, Var v')
                  | v /= v'
                  ]
               ++ [ wx
                  | wx@(w,_) <- M.toList mp
                  , w /= v
                  , w /= v'
                  ]
                )
-}  
  subst' sub (Bind v a) = Bind v' `fmap` subst' (Subst vs' mp') a
   where
    Subst vs mp = sub
   
    forbidden = vs `S.union` (S.delete v (free a))

    allowed   = [ v'
                | let n ::: t = v
                , v' <- v
                     -- : [ name [c] ::: t | c <- ['V'..'Z'] ]
                      : [ (n % i) ::: t | i <- [0..] ]
                , not (v' `S.member` forbidden) 
                ]

    v'        = head allowed

    vs'       = v' `S.insert` vs

    mp'       = M.fromList
                ( [ (v, Var v')
                  | v /= v'
                  ]
               ++ [ wx
                  | wx@(w,_) <- M.toList mp
                  , w /= v
                  , w /= v'
                  ]
                )

  occurring s x@(Bind v a)
    | s == v = return x
    | otherwise = Bind v `fmap` occurring s a

----------------------------------------------------------------------
-- input clauses

data Kind
  = Fact
  | NegatedConjecture
  | Conjecture
 deriving ( Eq, Ord, Show )

data Input a
  = Input
  { kind :: Kind
  , tag  :: String
  , what :: a
  }
 deriving ( Eq, Ord, Show )

type Problem = [Input Form]

----------------------------------------------------------------------
-- answers

data ConjectureAnswer
  = CounterSatisfiable
  | Theorem -- CounterUnsatisfiable :-)
  | FinitelyCounterUnsatisfiable
  | NoAnswerConjecture NoAnswerReason
 deriving ( Eq )

instance Show ConjectureAnswer where
  show CounterSatisfiable           = "CounterSatisfiable"
  show Theorem                      = "Theorem"
  show FinitelyCounterUnsatisfiable = "FinitelyCounterUnsatisfiable"
  show (NoAnswerConjecture r)       = show r

data ClauseAnswer
  = Satisfiable
  | Unsatisfiable
  | FinitelyUnsatisfiable
  | NoAnswerClause NoAnswerReason
 deriving ( Eq )

instance Show ClauseAnswer where
  show Satisfiable           = "Satisfiable"
  show Unsatisfiable         = "Unsatisfiable"
  show FinitelyUnsatisfiable = "FinitelyUnsatisfiable"
  show (NoAnswerClause r)    = show r

data NoAnswerReason
  = GaveUp
  | Timeout
 deriving ( Show, Eq )

toConjectureAnswer :: ClauseAnswer -> ConjectureAnswer
toConjectureAnswer Satisfiable           = CounterSatisfiable
toConjectureAnswer Unsatisfiable         = Theorem
toConjectureAnswer FinitelyUnsatisfiable = FinitelyCounterUnsatisfiable
toConjectureAnswer (NoAnswerClause r)    = NoAnswerConjecture r

----------------------------------------------------------------------
-- the end.
