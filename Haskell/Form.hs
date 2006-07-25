{-# OPTIONS -fglasgow-exts -fgenerics #-}
module Form where

import Data.Set as S( Set )
import qualified Data.Set as S
import Data.Map as M( Map )
import qualified Data.Map as M
import Data.Generics
import Data.List 

import Name

----------------------------------------------------------------------
-- Type

data Type
  = Type Name -- todo: more info here
 deriving ( Eq, Ord )

instance Show Type where
  showsPrec n (Type t) = showsPrec n t

top, bool :: Type
top  = Type (prim "Domain")
bool = Type (prim "Bool")

data Typing
  = [Type] :-> Type
  | V Type
 deriving ( Eq, Ord )

opers :: Show a => String -> [a] -> ShowS
opers op xs = foldr (.) id (intersperse (showString op) (map shows xs))

commas :: Show a => [a] -> ShowS
commas = opers ", "

instance Show Typing where
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
  showsPrec n (x ::: _) = showsPrec n x

arity :: Symbol -> Int
arity (_ ::: (xs :-> _)) = length xs
arity _                  = 0

isVarSymbol :: Symbol -> Bool
isVarSymbol (_ ::: V _) = True
isVarSymbol _           = False

----------------------------------------------------------------------
-- Term

data Term
  = Fun Symbol [Term]
  | Var Symbol
 deriving ( Eq, Ord )

instance Show Term where
  showsPrec n (Fun f []) = showsPrec n f
  showsPrec n (Fun f xs) = showsPrec n f
                         . showString "("
                         . commas xs
                         . showString ")"
  showsPrec n (Var x)    = showsPrec n x

var :: Type -> Int -> Symbol
var t i = (prim "X" % i) ::: V t

data Atom
  = Term :=: Term
 deriving ( Eq, Ord )

instance Show Atom where
  showsPrec n (a :=: b) = showsPrec n a
                        . showString " = "
                        . showsPrec n b
truth :: Term
truth = Fun (prim "truth" ::: ([] :-> bool)) []

prd :: Symbol -> [Term] -> Atom
prd p ts = Fun p ts :=: truth

data Bind a
  = Bind Symbol a
 deriving ( Eq, Ord )

instance Show a => Show (Bind a) where
  showsPrec n (Bind x a) = showsPrec n x
                         . showString " . "
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
  showsPrec n (Atom a)      = showsPrec n a
  showsPrec n (And xs)      = showsOps "&" "$true" (S.toList xs)
  showsPrec n (Or xs)       = showsOps "|" "$false" (S.toList xs)
  showsPrec n (x `Equiv` y) = showString "("
                            . showsPrec n x
                            . showString " <-> "
                            . showsPrec n y
                            . showString ")"
  showsPrec n (Not x)       = showString "~" . showsPrec n x
  showsPrec n (ForAll b)    = showString "(all "
                            . showsPrec n b
                            . showString ")"
  showsPrec n (Exists b)    = showString "(exi "
                            . showsPrec n b
                            . showString ")"

showsOps op unit []  = showString unit
showsOps op unit [x] = shows x
showsOps op unit xs  = showString "("
                     . opers (" " ++ op ++ " ") xs
                     . showString ")"

data Signed a
  = Pos a
  | Neg a
 deriving ( Eq, Ord )

instance Show a => Show (Signed a) where
  showsPrec n (Pos x) = showsPrec n x
  showsPrec n (Neg x) = showString "~"
                      . showsPrec n x

----------------------------------------------------------------------
-- constructors

true, false :: Form
true  = And S.empty
false = Or S.empty

nt :: Form -> Form
nt (Not a) = a
nt a       = Not a

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

{-
forAll, exists :: Name -> Form -> Form
forAll v a = 
  case positive a of
    And as ->
      And (smap (forAll v) as)
    
    ForAll ws w a ->
      ForAll (v `delete` ws) w (forAll v a)
    
    Or as -> yes \/ no
     where
      avss      = [ (a, free a) | a <- elements as ]
      (bs1,bs2) = partition ((v `member`) . snd) avss
      no        = orl [ b | (b,_) <- bs2 ]
      vs        = v `delete` unionList [ vs | (_,vs) <- bs1 ]
      body      = orl [ b | (b,_) <- bs1 ]
      yes       = case bs1 of
                    []      -> orl []
                    [(b,_)] -> forAll v b
                    _       -> ForAll vs v body

      orl [a] = a
      orl as  = Or (set as)

    a | v `member` vs -> ForAll (v `delete` vs) v a
      | otherwise     -> a
     where
      vs = free a    

exists v a = nt (forAll v (nt a))

positive :: Form -> Form
positive (Not (And as))        = Or (smap nt as)
positive (Not (Or as))         = And (smap nt as)
positive (Not (a `Equiv` b))   = nt a `Equiv` b
positive (Not (Not a))         = positive a
positive (Not (ForAll vs v a)) = Exists vs v (nt a)
positive (Not (Exists vs v a)) = ForAll vs v (nt a)
positive a                     = a -- only atoms

simple :: Form -> Form
simple (Or as)         = nt (And (smap nt as))
simple (Exists vs v a) = nt (ForAll vs v (nt a))
simple (Not (Not a))   = simple a
simple a               = a -- no Or, Exists on top-level
-}

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
-- destructors

class Symbolic a where
  symbols :: a -> Set Symbol
  free    :: a -> Set Symbol
  subst   :: Subst -> a -> a
  --todo: implement subst using continuations

  symbols{| Unit |}    Unit      = S.empty
  symbols{| a :*: b |} (x :*: y) = symbols x `S.union` symbols y
  symbols{| a :+: b |} (Inl x)   = symbols x
  symbols{| a :+: b |} (Inr y)   = symbols y

  free{| Unit |}    Unit      = S.empty
  free{| a :*: b |} (x :*: y) = free x `S.union` free y
  free{| a :+: b |} (Inl x)   = free x
  free{| a :+: b |} (Inr y)   = free y

  subst{| Unit |}    sub Unit      = Unit
  subst{| a :*: b |} sub (x :*: y) = subst sub x :*: subst sub y
  subst{| a :+: b |} sub (Inl x)   = Inl (subst sub x)
  subst{| a :+: b |} sub (Inr y)   = Inr (subst sub y)

instance                             Symbolic ()
instance (Symbolic a, Symbolic b) => Symbolic (a,b)
instance Symbolic a               => Symbolic [a]
instance Symbolic a               => Symbolic (Signed a)

instance (Ord a, Symbolic a) => Symbolic (Set a) where
  symbols s   = symbols (S.toList s)
  free s      = free (S.toList s)
  subst sub s = S.map (subst sub) s

instance Symbolic Atom
instance Symbolic Form

instance Symbolic Term where
  symbols (Fun f xs) = f `S.insert` symbols xs
  symbols (Var x)    = S.singleton x

  free (Fun _ xs) = free xs
  free (Var v)    = S.singleton v

  subst sub (Fun f xs) = Fun f (subst sub xs)
  subst sub x@(Var v)  = look v x sub

instance Symbolic a => Symbolic (Bind a) where
  symbols   (Bind v a) = v `S.insert` symbols a
  free      (Bind v a) = v `S.delete` free a
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

----------------------------------------------------------------------
-- input clauses

data Kind
  = Axiom
  | Hypothesis
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

----------------------------------------------------------------------
-- the end.
