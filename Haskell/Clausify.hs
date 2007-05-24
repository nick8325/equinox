{-# OPTIONS -fgenerics #-}
module Clausify
  ( clausify
  )
 where

import Form hiding ( Signed(..) )
import qualified Form
import Name
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import List( maximumBy, minimumBy, partition, nub )
import Control.Monad.State
import Control.Monad.Reader
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
-- monad

type M = State (Int,Int)

run :: M a -> a
run m = evalState m (0,0)

next :: M Int
next =
  do (i,j) <- get
     let i' = i+1
     i' `seq` put (i',j)
     return i

next' :: M Int
next' =
  do (i,j) <- get
     let j' = j+1
     j' `seq` put (i,j')
     return j

fresh :: Symbol -> M Symbol
fresh (v ::: t) =
  do i <- next
     return ((v % i) ::: t)

skolemn :: Symbol -> Set Symbol -> M Term
skolemn (_ ::: V t) vs =
  do i <- next'
     let f = (sk % i) ::: ([ t | _ ::: V t <- args ] :-> t)
     return (Fun f [ Var v | v <- args ])
 where
  args = S.toList vs

literal :: Set Symbol -> M Atom
literal vs =
  do i <- next'
     let p = (dp % i) ::: ([ t | _ ::: V t <- args ] :-> bool)
     return (prd p [ Var v | v <- args ])
 where
  args = S.toList vs

----------------------------------------------------------------------
-- algorithm

-- TODO: generalize to n-ary and/or

type Value  = (Integer, Integer)    -- (#lits, #clauses)
type Weight = (Value, Value, Value) -- (def, pos, neg)
type Try    = (Weight, M (Seq Clause, Seq Clause, Seq Clause))
type Result = (Set Symbol, [Try])

clausForm :: Form -> M [Clause]
clausForm a | isClause a =
  do return [toClause a]
 where
  isClause (ForAll (Bind _ p)) = isClause p
  isClause (Or ps)             = all isClause (S.toList ps)
  isClause (Atom _)            = True
  isClause (Not (Atom _))      = True
  isClause _                   = False

  toClause (ForAll (Bind _ p)) = toClause p
  toClause (Or ps)             = concatMap toClause (S.toList ps)
  toClause (Atom a)            = [Form.Pos a]
  toClause (Not (Atom a))      = [Form.Neg a]

clausForm a =
  do (defs, poss, _) <- m
     return (toList (defs +++ poss))
 where
  (_, tries) = claus Pos a
  (_, m)     = best tries

data Mode = Pos | Neg | Both deriving ( Eq, Ord, Show )

swap :: Mode -> Mode
swap Pos  = Neg
swap Neg  = Pos
swap Both = Both

claus :: Mode -> Form -> Result
claus mod a =
  case simple a of
    Atom a ->
      ( free a
      , [ ( ( (0,0)
            , (1,1) ?. pos
            , (1,1) ?. neg
            )
          , do return ( nil
                      , fromList [ [Form.Pos a] | pos]
                      , fromList [ [Form.Neg a] | neg]
                      )
          )
        ]
      )

    And as | S.size as == 0 ->
      ( S.empty
      , [ ( ( (0,0)
            , (0,0)
            , (0,1) ?. neg
            )
          , do return ( nil
                      , nil
                      , fromList [ [] | neg ]
                      )
          )
        ]
      )

    And as -> foldr2 conj [ claus mod a | a <- S.toList as ]
     where
      (vs1, tries1) `conj` (vs2, tries2) =
        ( vs
        , [ best tries
          , best [ def mod vs t | t <- tries ]
          ]
        )
       where
        vs    = vs1 `S.union` vs2
        tries = [ directAnd s t
                | s <- tries1
                , t <- tries2
                ]
      
    a `Equiv` b -> 
      ( vs
      , [ best tries
        , best [ def mod vs t | t <- tries ]
        ]
      )
     where
      vs            = vs1 `S.union` vs2
      (vs1, tries1) = claus Both a
      (vs2, tries2) = claus Both b
      tries         = [ directEquiv mod s t
                      | s <- tries1
                      , t <- tries2
                      ]
    
    ForAll (Bind v a) ->
      ( vs'
      , [ ( vals
          , do (defs, poss, negs) <- m
               v' <- iff pos (fresh v)
               x  <- iff neg (skolemn v vs')
               return ( defs
                      , subst (v |=> Var v') poss
                      , fmap (map (fmap (substSkAtom v x))) negs
                      -- , subst (v |=> x)      negs
                      )
          )
        | (vals,m) <- tries
        ]
      )
     where
      vs'         = v `S.delete` vs
      (vs, tries) = claus mod a
    
    Not a ->
      ( vs
      , [ ( (d,n,p)
          , do (defs, poss, negs) <- m
               return (defs, negs, poss)
          )
        | ((d,p,n),m) <- tries
        ] 
      )
     where
      (vs, tries) = claus (swap mod) a

 where
  pos = mod /= Neg
  neg = mod /= Pos

  iff True  m = m
  iff False _ = return (error "pos/neg violation")

  substSkAtom v x (a :=: b) =
    substSk v x a :=: substSk v x b
  
  substSk v x (Var w)
    | v == w    = x
    | otherwise = Var w

  substSk v x@(Fun (f ::: (tsf :-> tf)) xsf) (Fun (g ::: (tsg :-> tg)) xsg)
    | isSkolemnName g && Var v `elem` xsg && length xsg' <= length xsg =
      Fun (g ::: (tsg' :-> tg)) (map (substSk v x) xsg')
   where
    (xsg',tsg') = unzip $
      [ (x,t)
      | (x,t) <- xsg `zip` tsg
      , x /= Var v
      ] ++
      [ (x,t)
      | (x,t) <- xsf `zip` tsf
      , x `notElem` xsg
      ]
    
  substSk v x (Fun g xs) =
    Fun g (map (substSk v x) xs)

lc      ?. b       = if b then lc else (0,0)
inc (l,c)          = (l+c,c)
(l1,c1) +. (l2,c2) = (l1+l2,c1+c2)
(l1,c1) /. (l2,c2) = (l1*c2+c1*l2,c1*c2)


cs  ?? b   = if b then cs else nil
cs1 // cs2 = fromList [ c1 ++ c2 | c1 <- toList cs1, c2 <- toList cs2 ]

-- FIXME: This is completely arbitrary and should be evaluated
-- Added comment:
--   * #clauses are more expensive than #literals
--   * #things in definitions should be more expensive
best :: [Try] -> Try
best = minimumBy cmp
 where
  (w1, _) `cmp` (w2, _) = weight w1 `compare` weight w2
  
  weight (v1,v2,v3) = 3*value v1 + value v2 + value v3
  value (l,c)       = 3*c + l

directAnd :: Try -> Try -> Try
directAnd ((d1, p1, n1), m1) ((d2, p2, n2), m2) =
  ( ( d1 +. d2
    , p1 +. p2
    , n1 /. n2
    )
  , do (defs1, pos1, neg1) <- m1
       (defs2, pos2, neg2) <- m2
       return ( defs1 +++ defs2
              , pos1  +++ pos2
              , neg1  //  neg2
              )
  )

directEquiv :: Mode -> Try -> Try -> Try
directEquiv mod ((d1, p1, n1), m1) ((d2, p2, n2), m2) =
  ( ( d1 +. d2
    , ((n1 /. p2) +. (p1 /. n2)) ?. pos
    , ((p1 /. p2) +. (n1 /. n2)) ?. neg
    )
  , do (defs1, pos1, neg1) <- m1
       (defs2, pos2, neg2) <- m2
       return ( defs1 +++ defs2
              , ((neg1 // pos2) +++ (pos1 // neg2)) ?? pos
              , ((pos1 // pos2) +++ (neg1 // neg2)) ?? neg
              )
  )
 where
  pos = mod /= Neg
  neg = mod /= Pos

def :: Mode -> Set Symbol -> Try -> Try
def mod vs ((d, p, n), m) =
  ( ( d +. inc p +. inc n
    , (1,1) ?. pos
    , (1,1) ?. neg
    )
  , do (defs, poss, negs) <- m
       l <- literal vs
       return ( defs
            +++ fromList [ Form.Neg l : c | c <- toList poss ]
            +++ fromList [ Form.Pos l : c | c <- toList negs ]
              , fromList [ [Form.Pos l] | pos ]
              , fromList [ [Form.Neg l] | neg ]
              )
  )
 where
  pos = mod /= Neg
  neg = mod /= Pos

foldr2 :: (a -> a -> a) -> [a] -> a
foldr2 op []  = error "foldr2: empty list" --undefined
foldr2 op [x] = x
foldr2 op xs  = foldr2 op (sweep xs)
 where
  sweep (x:y:xs) = (x `op` y) : sweep xs
  sweep xs       = xs

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
toList s = list [s]
 where
  list []                 = []
  list (List xs     : qs) = xs ++ list qs
  list ((p `Cat` q) : qs) = list (p:q:qs)

----------------------------------------------------------------------
-- the end.
