{-# OPTIONS -XGenerics #-}
module ClausifyNew
  ( clausify
  )
 where

import Form
import qualified Form
import Name
import Data.Set( Set )
import List
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
  do noEquivPs  <- removeEquiv p
     skolemedPs <- sequence [ skolemize p | p <- noEquivPs ]
     cheapOrPs  <- sequence [ makeCheapOr p | p <- skolemedPs ]
     noQuantPs  <- sequence [ removeForAll p | p <- cheapOrPs ]
     return (concat [ cnf p | p <- noQuantPs ])

----------------------------------------------------------------------
-- removing equivalences

-- removeEquiv p -> ps :
--   POST: And ps is equivalent to p (modulo extra symbols)
--   POST: ps has no Equiv and only Not on Atoms
removeEquiv :: Form -> M [Form]
removeEquiv p =
  do (defs,p') <- removeEquiv' False p
     return (p' : defs)

-- removeEquiv' inEquiv p -> (defs,p') :
--   PRE: inEquiv is True when we are "under" an Equiv
--   POST: defs is a list of definitions, under which
--         p' is equivalent to p
removeEquiv' :: Bool -> Form -> M ([Form], Form)
removeEquiv' inEquiv p =
  case positive p of
    And ps ->
      do dps <- sequence [ removeEquiv' inEquiv p | p <- toList ps ]
         return ( concatMap fst dps
                , And (fromList (map snd dps))
                )

    Or ps ->
      do dps <- sequence [ removeEquiv' inEquiv p | p <- toList ps ]
         return ( concatMap fst dps
                , Or (fromList (map snd dps))
                )

    ForAll (Bind x p) ->
      do (defs,p') <- removeEquiv' inEquiv p
         return ( defs
                , ForAll (Bind x p)
                )

    Exists (Bind x p) ->
      do (defs,p') <- removeEquiv' inEquiv p
         return ( defs
                , Exists (Bind x p)
                )

    p `Equiv` q ->
      do (defsp,p') <- removeEquivArg inEquiv p
         (defsq,q') <- removeEquivArg inEquiv q
         return ( defsp ++ defsq
                , (nt p' \/ q') /\ (p' \/ nt q')
                )

    lit ->
      do return ([],lit)

-- removeEquivArg inEquiv p -> (defs,p'):
-- deals with the argument to an Equiv.
--   PRE: inEquiv is True when we are "under" an Equiv
--   POST: defs is a list of definitions, under which
--         p' is equivalent to p
removeEquivArg :: Bool -> Form -> M ([Form],Form)
removeEquivArg inEquiv p
  -- if we are not already under an Equiv, we can safely expand without
  --   causing an explosion
  -- if we are under an equiv, we have to force the argument to be small;
  --   we do this by introducing a new predicate symbol and a definition
  | not inEquiv || isSmall p =
      do removeEquiv' True p

  | otherwise =
      do dp   <- Atom `fmap` literal (free p)
         defs <- removeEquiv (forEvery dp (dp `Equiv` p))
         return (defs, dp)
 where
  -- a formula is small if it does not contain any boolean connectives
  isSmall (Atom _)            = True
  isSmall (Not p)             = isSmall p
  isSmall (ForAll (Bind _ p)) = isSmall p
  isSmall (Exists (Bind _ p)) = isSmall p
  isSmall _                   = False

-- TODO: Replace the list of definitions by a sequence where
-- concatenation is O(1)

----------------------------------------------------------------------
-- skolemization

-- skolemize p -> p'
--   PRE: p has no Equiv
--   POST: p' is equivalent to p (modulo extra symbols)
--   POST: p' has no Equiv, no Exists, and only Not on Atoms
skolemize :: Form -> M Form
skolemize p =
  case positive p of
    And ps ->
      do ps <- sequence [ skolemize p | p <- toList ps ]
         return (And (fromList ps))

    Or ps ->
      do ps <- sequence [ skolemize p | p <- toList ps ]
         return (Or (fromList ps))

    ForAll (Bind x p) ->
      do p' <- skolemize p
         return (ForAll (Bind x p'))

    Exists b@(Bind x p) ->
      -- skolemterms have only variables as arguments, arities are large(r)
      do t <- skolem x (free b)
         skolemize (subst (x |=> t) p)
      {-
      -- skolemterms can have other skolemterms as arguments, arities are small(er)
      -- disadvantage: skolemterms are very complicated and deep
      do p' <- skolemize p
         t <- skolem x (S.delete x (free p'))
         return (subst (x |=> t) p')
      -}

     lit ->
       do return lit

-- TODO: Avoid recomputing "free" at every step, by having
-- skolemize return the set of free variables as well

-- TODO: Investigate skolemizing top-down instead, find the right
-- optimization

----------------------------------------------------------------------
-- make cheap Ors

makeCheapOr :: Form -> M [Form]
makeCheapOr p =
  do (defs,p',_) <- makeCheapOr' p
     return (defs ++ [p'])

type Cost = Int
-- how much does it cost (in clauses) to flatten this formula to clauses?

tooLarge :: Cost -> Bool
tooLarge c = c > 2 -- completely arbitrarily chosen; TODO: investigate best value

makeCheapOr' :: Form -> M ([Form],Form,Cost)
makeCheapOr' (And ps) =
  do dcs <- sequence [ makeCheapOr' p | p <- S.toList ps ]
     return (concatMap fst3 dcs,  And (S.fromList (map snd3 dcs)), sum (map thd3 dcs))

makeCheapOr' (Or ps) =
  do dcs <- sequence [ makeCheapOr' p | p <- S.toList ps ]
     makeOr dcs
     (defs1',p1',cost1') <- makeArg p1 cost1 cost2

makeCheapOr' (ForAll (Bind x p)) =
  do (defs,p',cost) <- makeCheapOr' p
     return (map (\p -> ForAll (Bind x p)) defs, ForAll (Bind x p'), cost)

makeCheapOr' lit =
  do return ([], lit, 1)

makeOr :: [([Form],Form,Cost)] -> ([Form],Form,Cost)
makeOr [] =
  do return ([], false, 1)

makeOr [dc] =
  do return dc

makeOr ((defs1,p1,cost1):dcs) =
  do (defs2,p2,cost2) <- makeOr dcs
     let costly = tooLarge cost1 && tooLarge cost2
     (defs1',p1',cost1') <- if costly && cost1 >= cost2
                              then makeDef p1
                              else return ([],p1,cost1)
     (defs2',p2',cost2') <- if costly && cost2 > cost1
                              then makeDef p2
                              else return ([],p2,cost2)
     return (defs1++defs2++defs1'++defs2',p1' \/ p2',cost1' * cost2')

makeDef :: Form -> M ([Form],Form,Cost)
makeDef p =
  do d <- Atom `fmap` literal (free p)
     return ([nt d \/ p], d, 1)

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
  do ps <- sequence [ removeForAll p | p <- toList ps ]
     return (And (fromList ps))

removeForAll (Or ps) =
  do ps <- sequence [ removeForAll p | p <- toList ps ]
     return (Or (fromList ps))

removeForAll (ForAll (Bind x p)) =
  do x' <- fresh x
     p' <- removeForAll p
     return (ForAll (Bind x' (subst (x |=> Var x') p')))

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
cnf (And ps)       = concatMap cnf (S.fromList ps)
cnf (Or ps)        = cross (map cnf (S.fromList ps))
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

skolem :: Symbol -> Set Symbol -> M Term
skolem (_ ::: V t) vs =
  do i <- next
     let f = (sk % i) ::: ([ t | _ ::: V t <- args ] :-> t)
     return (Fun f [ Var v | v <- args ])
 where
  args = S.toList vs

literal :: Set Symbol -> M Atom
literal vs =
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
