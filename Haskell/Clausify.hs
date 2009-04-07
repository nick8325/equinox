{-# OPTIONS -XGenerics #-}
module Clausify
  ( clausify
  )
 where

import Form
import qualified Form
import Name
import Data.Set( Set )
import Data.List( nub, maximumBy )
import qualified Data.Set as S
import Control.Monad.State.Strict
import Flags

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
    do cs <- clausForm (what inp)
       clausifyInputs (theory +++ fromList cs) obligs inps

  clausifyInputs theory obligs (inp:inps) =
    do clausifyObligs theory obligs (split' (what inp)) inps

  clausifyObligs theory obligs [] inps =
    do clausifyInputs theory obligs inps
  
  clausifyObligs theory obligs (a:as) inps =
    do cs <- clausForm (nt a)
       clausifyObligs theory (obligs +++ fromList [cs]) as inps

  split' a | splitting ?flags = if null split_a then [true] else split_a
   where
    split_a = split a
  split' a                    = [a]

clean :: Clause -> Clause
clean cl = nub (subst sub cl)
 where
  xs  = free cl
  sub = makeTab ids S.empty (S.toList xs)
 
  makeTab sub used []                 = sub
  makeTab sub used ((x@(n ::: t)):xs) = makeTab sub' (S.insert n' used) xs
   where
    strippedN = strip n
    
    n' = head [ n'
              | n' <- strippedN : [ strippedN % i | i <- [1..] ]
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

clausForm :: Form -> M [Clause]
clausForm p =
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
     return (defs++[pos])

-- removeEquivAux inEquiv p -> (defs,pos,neg) :
--   PRE: inEquiv is True when we are "under" an Equiv
--   POST: defs is a list of definitions, under which
--         pos is equivalent to p and neg is equivalent to nt p
-- (the reason why "neg" and "nt pos" can be different, is
-- because we want to always code an equivalence as
-- a conjunction of two disjunctions, which leads to fewer
-- clauses -- the "neg" part of the result for the case Equiv
-- below makes use of this)
removeEquivAux :: Bool -> Form -> M ([Form],Form,Form)
removeEquivAux inEquiv p =
  case simple p of
    Not p ->
      do (defs,pos,neg) <- removeEquivAux inEquiv p
         return (defs,neg,pos)
  
    And ps ->
      do dps <- sequence [ removeEquivAux inEquiv p | p <- S.toList ps ]
         let (defss,poss,negs) = unzip3 dps
         return ( concat defss
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
         (defsp',posp',negp') <- makeSmall inEquiv posp negp
         (defsq',posq',negq') <- makeSmall inEquiv posq negq
         return ( defsp ++ defsq ++ defsp' ++ defsq'
                , (negp' \/ posq') /\ (posp' \/ negq')
                , (negp' \/ negq') /\ (posp' \/ posq')
                )

    atom ->
      do return ([],atom,nt atom)

-- makeSmall turns a formula into something that we are
-- willing to copy: (1) any formula that is not under an Equiv
-- (because we have to copy these at least once anyway), (2)
-- any formula that is small. All other formulas will be made
-- small (by means of a definition) before we copy them.
makeSmall :: Bool -> Form -> Form -> M ([Form],Form,Form)
makeSmall inEquiv pos neg
  | isSmall pos || not inEquiv =
    do return ([],pos,neg)

  | otherwise =
    do dp <- Atom `fmap` literal (name "d_eq") (free pos)
       return ([nt dp \/ pos, dp \/ neg],dp, nt dp)
 where
  -- a formula is small if it is already a literal
  isSmall (Atom _) = True
  isSmall (Not p)  = isSmall p
  isSmall _        = False

-- TODO: Replace the list of definitions by a sequence where
-- concatenation is O(1)

-- TODO: Small formulas should also be able to contain quantifiers.
-- however, this messes up skolemization, so that should be done first then!

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
     return (defs ++ [p'])

type Cost = Int
-- how much does it cost (in clauses) to flatten this formula to clauses?

tooLarge :: Cost -> Bool
tooLarge c = c > 2 -- completely arbitrarily chosen; TODO: investigate best value

removeExpensiveOrAux :: Form -> M ([Form],Form,Cost)
removeExpensiveOrAux (And ps) =
  do dcs <- sequence [ removeExpensiveOrAux p | p <- S.toList ps ]
     let (defss,ps,costs) = unzip3 dcs
     return (concat defss, And (S.fromList ps), sum costs)

removeExpensiveOrAux (Or ps) =
  do dcs <- sequence [ removeExpensiveOrAux p | p <- S.toList ps ]
     makeOr dcs

removeExpensiveOrAux (ForAll (Bind x p)) =
  do (defs,p',cost) <- removeExpensiveOrAux p
     return (map (\p -> ForAll (Bind x p)) defs, ForAll (Bind x p'), cost)

removeExpensiveOrAux lit =
  do return ([], lit, 1)

makeOr :: [([Form],Form,Cost)] -> M ([Form],Form,Cost)
makeOr [] =
  do return ([], false, 1)

makeOr [dc] =
  do return dc

makeOr ((defs1,p1,cost1):dcs) =
  do (defs2,p2,cost2) <- makeOr dcs
     let tooCostly = tooLarge cost1 && tooLarge cost2
     (defs1',p1',cost1') <- if tooCostly && cost1 >= cost2
                              then makeDef p1
                              else return ([],p1,cost1)
     (defs2',p2',cost2') <- if tooCostly && cost2 > cost1
                              then makeDef p2
                              else return ([],p2,cost2)
     return (defs1++defs2++defs1'++defs2',p1' \/ p2',cost1' * cost2')
 where
  makeDef p =
    do d <- Atom `fmap` literal (name "d_or") (free p)
       return ([d .=> p], d, 1)

-- TODO: Avoid recomputing "free" at every step, by having
-- makeOr return the set of free variables as well

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

type M = State Int

run :: M a -> a
run m = evalState m 0

next :: M Int
next =
  do i <- get
     let i' = i+1
     i' `seq` put i'
     return i

fresh :: Symbol -> M Symbol
fresh (x ::: t) =
  do i <- next
     return ((x % i) ::: t)

skolem :: Symbol -> Set Symbol -> M Term
skolem (_ ::: V t) vs =
  do i <- next
     let f = (sk % i) ::: ([ t | _ ::: V t <- args ] :-> t)
     return (Fun f [ Var v | v <- args ])
 where
  args = S.toList vs

literal :: Name -> Set Symbol -> M Atom
literal dp vs =
  do i <- next
     let p = (dp % i) ::: ([ t | _ ::: V t <- args ] :-> bool)
     return (prd p [ Var v | v <- args ])
 where
  args = S.toList vs

----------------------------------------------------------------------
-- sequences

data Seq a = List [a] | Seq a `Cat` Seq a

instance Symbolic a => Symbolic (Seq a)

instance Functor Seq where
  fmap f (List xs)   = List (map f xs)
  fmap f (a `Cat` b) = fmap f a `Cat` fmap f b

fromList :: [a] -> Seq a
fromList xs = List xs

nil = fromList []

(+++) :: Seq a -> Seq a -> Seq a
p +++ q = p `Cat` q

toList :: Seq a -> [a]
toList s = list s []
 where
  list (List xs)   ys = xs ++ ys
  list (p `Cat` q) ys = list p (list q ys)

----------------------------------------------------------------------
-- the end.
