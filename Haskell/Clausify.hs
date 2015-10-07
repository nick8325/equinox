module Clausify
  ( clausify
  )
 where

import Form
import qualified Form
import Name
import Data.Set( Set )
import Data.List( nub, maximumBy, sortBy )
import Data.Ord
import qualified Data.Set as S
import Flags
import Control.Applicative
import Control.Monad

----------------------------------------------------------------------
-- clausify

clausify :: (?flags :: Flags) => Problem -> ([Clause],[[Clause]])
clausify inps = run $ clausifyInputs nil nil inps
 where
  clausifyInputs theory obligs [] =
    do return ( map clean (toList theory)
              , map (map clean) (toList obligs)
              )
  
  -- Here, one could imagine adding NegatedConjecture as ONE oblig also ...
  clausifyInputs theory obligs (inp:inps) | kind inp /= Conjecture =
    do cs <- clausForm (tag inp) (what inp)
       clausifyInputs (theory +++ fromList cs) obligs inps

  clausifyInputs theory obligs (inp:inps) =
    do clausifyObligs theory obligs (tag inp) (split' (what inp)) inps

  clausifyObligs theory obligs s [] inps =
    do clausifyInputs theory obligs inps
  
  clausifyObligs theory obligs s (a:as) inps =
    do cs <- clausForm s (nt a)
       clausifyObligs theory (obligs +++ fromList [cs]) s as inps

  split' a | splitting ?flags = if null split_a then [true] else split_a
   where
    split_a = split a
  split' a                    = [a]

clean :: Clause -> Clause
clean cl = nub (subst sub cl)
 where
  xs  = free cl
  sub = makeTab ids S.empty ([1..] `zip` S.toList xs)
 
  makeTab sub used []                   = sub
  makeTab sub used ((i,x@(n ::: t)):xs) = makeTab sub' (S.insert n' used) xs
   where
    strippedN = strip n
    
    n' = head [ n'
              | let new j = "SV" ++ show i
                         ++ "_" ++ show strippedN
                         ++ (if j == 0 then "" else show j)
              , n' <- strippedN : [ name (new j) | j <- [1..] ]
              , not (n' `S.member` used)
              ]
    
    x' = n' ::: t 
    
    sub' | x == x'   = sub
         | otherwise = (x |=> Var x') |+| sub

split :: Form -> [Form]
split p =
  case positive p of
    ForAll (Bind x p) ->
      [ ForAll (Bind x p') | p' <- split p ]
    
    And ps ->
      concatMap split (S.toList ps)
    
    p `Equiv` q ->
      split (nt p \/ q) ++ split (p \/ nt q)

    Or ps ->
      snd $
      maximumBy first
      [ (siz q, [ Or (S.fromList (q':qs)) | q' <- sq ])
      | (q,qs) <- select (S.toList ps)
      , let sq = split q
      ]

    _ ->
      [p]
 where
  select []     = []
  select (x:xs) = (x,xs) : [ (y,x:ys) | (y,ys) <- select xs ]
  
  first (n,x) (m,y) = n `compare` m
  
  siz (And ps)            = S.size ps
  siz (ForAll (Bind _ p)) = siz p
  siz (_ `Equiv` _)       = 2
  siz _                   = 0

{-  
    Or ps | S.size ps > 0 && n > 0 ->
      [ Or (S.fromList (p':ps')) | p' <- split p ]
     where
      pns = [(p,siz p) | p <- S.toList ps]
      ((p,n),pns') = getMax (head pns) [] (tail pns)
      ps' = [ p' | (p',_) <- pns' ]
    
  getMax pn@(p,n) pns [] = (pn,pns)
  getMax pn@(p,n) pns (qm@(q,m):qms)
    | m > n     = getMax qm (pn:pns) qms
    | otherwise = getMax pn (qm:pns) qms
-}

----------------------------------------------------------------------
-- core clausification algorithm

clausForm :: String -> Form -> M [Clause]
clausForm s p =
  withName s $
    do noEquivPs       <-             removeEquiv       p
       noExistsPs      <-  sequence [ removeExists      p | p <- noEquivPs ]
       noExpensiveOrPs <- csequence [ removeExpensiveOr p | p <- noExistsPs ]
       noForAllPs      <-  sequence [ removeForAll      p | p <- noExpensiveOrPs ]
       return (concat [ cnf p | p <- noForAllPs ])
 where
  csequence = fmap concat . sequence

----------------------------------------------------------------------
-- removing equivalences

-- removeEquiv p -> ps :
--   POST: And ps is equivalent to p (modulo extra symbols)
--   POST: ps has no Equiv and only Not on Atoms
removeEquiv :: Form -> M [Form]
removeEquiv p =
  do (defs,pos,_) <- removeEquivAux False p
     return (toList (defs+++fromList [pos]))

-- removeEquivAux inEquiv p -> (defs,pos,neg) :
--   PRE: inEquiv is True when we are "under" an Equiv
--   POST: defs is a list of definitions, under which
--         pos is equivalent to p and neg is equivalent to nt p
-- (the reason why "neg" and "nt pos" can be different, is
-- because we want to always code an equivalence as
-- a conjunction of two disjunctions, which leads to fewer
-- clauses -- the "neg" part of the result for the case Equiv
-- below makes use of this)
removeEquivAux :: Bool -> Form -> M (Seq Form,Form,Form)
removeEquivAux inEquiv p =
  case simple p of
    Not p ->
      do (defs,pos,neg) <- removeEquivAux inEquiv p
         return (defs,neg,pos)
  
    And ps ->
      do dps <- sequence [ removeEquivAux inEquiv p | p <- S.toList ps ]
         let (defss,poss,negs) = unzip3 dps
         return ( conc defss
                , And (S.fromList poss)
                , Or  (S.fromList negs)
                )

    ForAll (Bind x p) ->
      do (defs,pos,neg) <- removeEquivAux inEquiv p
         return ( defs
                , ForAll (Bind x pos)
                , Exists (Bind x neg)
                )

    p `Equiv` q ->
      do (defsp,posp,negp)    <- removeEquivAux True p
         (defsq,posq,negq)    <- removeEquivAux True q
         (defsp',posp',negp') <- makeCopyable inEquiv posp negp
         (defsq',posq',negq') <- makeCopyable inEquiv posq negq
         return ( defsp +++ defsq +++ defsp' +++ defsq'
                , (negp' \/ posq') /\ (posp' \/ negq')
                , (negp' \/ negq') /\ (posp' \/ posq')
                )

    atom ->
      do return (nil,atom,nt atom)

-- makeCopyable turns an argument to an Equiv into something that we are
-- willing to copy. There are two such cases: (1) when the Equiv is
-- not under another Equiv (because we have to copy arguments to an Equiv
-- at least once anyway), (2) if the formula is small.
-- All other formulas will be made small (by means of a definition)
-- before we copy them.
makeCopyable :: Bool -> Form -> Form -> M (Seq Form,Form,Form)
makeCopyable inEquiv pos neg
  | isSmall pos || not inEquiv =
    -- we skolemize here so that we reuse the skolem function
    -- (if we do this after copying, we get several skolemfunctions)
    do pos' <- removeExists pos
       neg' <- removeExists neg
       return (nil,pos',neg')

  | otherwise =
    do dp <- Atom `fmap` literal "equiv" (free pos)
       return (fromList [nt dp \/ pos, dp \/ neg],dp, nt dp)
 where
  -- a formula is small if it is already a literal
  isSmall (Atom _)            = True
  isSmall (Not p)             = isSmall p
  isSmall (ForAll (Bind _ p)) = isSmall p
  isSmall (Exists (Bind _ p)) = isSmall p
  isSmall _                   = False

----------------------------------------------------------------------
-- skolemization

-- removeExists p -> p'
--   PRE: p has no Equiv
--   POST: p' is equivalent to p (modulo extra symbols)
--   POST: p' has no Equiv, no Exists, and only Not on Atoms
removeExists :: Form -> M Form
removeExists (And ps) =
  do ps <- sequence [ removeExists p | p <- S.toList ps ]
     return (And (S.fromList ps))

removeExists (Or ps) =
  do ps <- sequence [ removeExists p | p <- S.toList ps ]
     return (Or (S.fromList ps))
    
removeExists (ForAll (Bind x p)) =
  do p' <- removeExists p
     return (ForAll (Bind x p'))
    
removeExists (Exists b@(Bind x p)) =
  -- skolemterms have only variables as arguments, arities are large(r)
  do t <- skolem x (free b)
     removeExists (subst (x |=> t) p)
  {-
  -- skolemterms can have other skolemterms as arguments, arities are small(er)
  -- disadvantage: skolemterms are very complicated and deep
  do p' <- skolemize p
     t <- skolem x (S.delete x (free p'))
     return (subst (x |=> t) p')
  -}

removeExists lit =
  do return lit

-- TODO: Avoid recomputing "free" at every step, by having
-- skolemize return the set of free variables as well

-- TODO: Investigate skolemizing top-down instead, find the right
-- optimization

----------------------------------------------------------------------
-- make cheap Ors

removeExpensiveOr :: Form -> M [Form]
removeExpensiveOr p =
  do (defs,p',_) <- removeExpensiveOrAux p
     return (toList (defs +++ fromList [p']))

-- cost: represents how it expensive it is to clausify a formula
type Cost = (Int,Int) -- (#clauses, #literals)

unitCost :: Cost
unitCost = (1,1)

andCost :: [Cost] -> Cost
andCost cs = (sum (map fst cs), sum (map snd cs))

orCost :: [Cost] -> Cost
orCost []           = (1,0)
orCost [c]          = c
orCost ((c1,l1):cs) = (c1 * c2, c1 * l2 + c2 * l1)
 where
  (c2,l2) = orCost cs

removeExpensiveOrAux :: Form -> M (Seq Form,Form,Cost)
removeExpensiveOrAux (And ps) =
  do dcs <- sequence [ removeExpensiveOrAux p | p <- S.toList ps ]
     let (defss,ps,costs) = unzip3 dcs
     return (conc defss, And (S.fromList ps), andCost costs)

removeExpensiveOrAux (Or ps) =
  do dcs <- sequence [ removeExpensiveOrAux p | p <- S.toList ps ]
     let (defss,ps,costs) = unzip3 dcs
     (defs2,p,c) <- makeOr (sortBy (comparing snd) (zip ps costs))
     return (conc defss+++defs2,p,c)

removeExpensiveOrAux (ForAll (Bind x p)) =
  do (defs,p',cost) <- removeExpensiveOrAux p
     return (fmap (\p -> ForAll (Bind x p)) defs, ForAll (Bind x p'), cost)

removeExpensiveOrAux lit =
  do return (nil, lit, unitCost)

-- input is sorted; small costs first
makeOr :: [(Form,Cost)] -> M (Seq Form,Form,Cost)
makeOr [] =
  do return (nil, false, orCost [])

makeOr [(f,c)] =
  do return (nil,f,c)

makeOr fcs
  | null fcs2 =
    do return (nil, Or (S.fromList (map fst fcs1)), orCost (map snd fcs1))

  | otherwise =
    do d <- Atom `fmap` literal "or" (free (map fst fcs2))
       (defs,p,_) <- makeOr ((nt d,unitCost):fcs2)
       return ( defs+++fromList [p]
              , Or (S.fromList (d : map fst fcs1))
              , orCost (unitCost : map snd fcs1)
              )
 where
  (fcs1,fcs2) = split [] fcs
  
  split fcs1 []                            = (fcs1,[])
  split fcs1 (fc@(_,(cc,_)):fcs) | cc <= 1 = split (fc:fcs1) fcs
  split fcs1 fcs@((_,(cc,_)):_)  | cc <= 2 = (take 2 fcs ++ fcs1, drop 2 fcs)
  split fcs1 fcs                           = (take 1 fcs ++ fcs1, drop 1 fcs)

----------------------------------------------------------------------
-- removing ForAll

-- removeForAll p -> p'
--   PRE: p has no Equiv, no Exists, and only Not on Atoms
--   POST: p' is equivalent to p (modulo implicitly quantified variables)
--   POST: p' has no Equiv, no Exists, no ForAll, and only Not on Atoms
removeForAll :: Form -> M Form
removeForAll (And ps) =
  do ps <- sequence [ removeForAll p | p <- S.toList ps ]
     return (And (S.fromList ps))

removeForAll (Or ps) =
  do ps <- sequence [ removeForAll p | p <- S.toList ps ]
     return (Or (S.fromList ps))
    
removeForAll (ForAll (Bind x p)) =
  do x' <- fresh x
     p' <- removeForAll p
     return (subst (x |=> Var x') p')

removeForAll lit =
  do return lit

-- TODO: Add an extra argument that is the substitution and apply it
-- once you get to the final literal

----------------------------------------------------------------------
-- clausification

-- cnf p = cs
--   PRE: p has no Equiv, no Exists, no ForAll, and only Not on Atoms
--   POST: And (map Or cs) is equivalent to p
cnf :: Form -> [Clause]
cnf (And ps)       = concatMap cnf (S.toList ps)
cnf (Or ps)        = cross (map cnf (S.toList ps))
cnf (Atom a)       = [[Pos a]]
cnf (Not (Atom a)) = [[Neg a]]

cross :: [[Clause]] -> [Clause]
cross []       = [[]]
cross (cs:css) = [ c1++c2 | c1 <- cs, c2 <- cross css ]

----------------------------------------------------------------------
-- monad

newtype M a = M (String -> Int -> (a, Int))

instance Functor M where
  fmap f (M h) = M (\s n -> let (x,n') = h s n in (f x, n'))

instance Applicative M where
  pure = return
  (<*>) = liftM2 ($)

instance Monad M where
  return x =
    M (\s n -> (x, n))
  
  M h >>= f =
    M (\s n -> let (x,n') = h s n; M h' = f x in h' s n')

run :: M a -> a
run (M h) = let (x,_) = h "" 0 in x

next :: M Int
next = M (\s n -> let n'=n+1 in (n,n'))

withName :: String -> M a -> M a
withName s (M h) = M (\_ n -> h s n)

getName :: M String
getName = M (\s n -> (s,n))

fresh :: Symbol -> M Symbol
fresh (v ::: t) =
  do i <- next
     return ((v % i) ::: t)

skolem :: Symbol -> Set Symbol -> M Term
skolem (v ::: V t) vs =
  do i <- next
     s <- getName
     let f = name ("sK" ++ show i ++ concat [ "_" ++ t | t <- [s,show v], not (null t) ]) ::: ([ t | _ ::: V t <- args ] :-> t)
     return (Fun f [ Var v | v <- args ])
 where
  args = S.toList vs

literal :: String -> Set Symbol -> M Atom
literal w vs =
  do i <- next
     s <- getName
     let p = (name ("sP" ++ show i ++ concat [ "_" ++ t | t <- [s,w], not (null t) ])) ::: ([ t | _ ::: V t <- args ] :-> bool)
     return (prd p [ Var v | v <- args ])
 where
  args = S.toList vs

----------------------------------------------------------------------
-- sequences

data Seq a = List [a] | Seq a `Cat` Seq a

instance Symbolic a => Symbolic (Seq a) where
  symbols    = symbols . toList
  free       = free . toList
  subterms   = subterms . toList
  subst' sub = (fromList `fmap`) . subst' sub . toList

instance Functor Seq where
  fmap f (List xs)   = List (map f xs)
  fmap f (a `Cat` b) = fmap f a `Cat` fmap f b

fromList :: [a] -> Seq a
fromList xs = List xs

nil = List []

(+++) :: Seq a -> Seq a -> Seq a
p +++ q = p `Cat` q

conc :: [Seq a] -> Seq a
conc [] = nil
conc ss = foldr1 (+++) ss

toList :: Seq a -> [a]
toList s = list s []
 where
  list (List xs)   ys = xs ++ ys
  list (p `Cat` q) ys = list p (list q ys)

----------------------------------------------------------------------
-- the end.
