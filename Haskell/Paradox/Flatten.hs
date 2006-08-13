module Paradox.Flatten where

import Form
import Name
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import List ( (\\), sortBy, minimumBy, partition )
import Paradox.AnalysisTypes
import Paradox.Instantiate
import Maybe
  ( fromJust
  )

import Monad
  ( mplus
  )

import List
  ( groupBy
  , sort
  )

-------------------------------------------------------------------------
-- macify

macify :: [Clause] -> ([(Type,Int)], [Clause], [QClause])
macify cs = ([(t,length ts)|(t,ts) <- cliques], flattenedCs, functionCs)
 where
  flattenedCs =
    [ c'
    | (c, i) <- assigns
    , let d i = Fun (elt i) []
    , c' <- [ Pos (c :=: d i) ]
          : [ [ Neg (c :=: d j) ]
            | j <- [1..i-1]
            ]
    ] ++
    splitAll (concatMap (flatten assignCons) (defCs ++ coreCs))
  
  (ds, defCs, coreCs) =
    definitions cs
    
  functionCs =
    [ Uniq (Bind y
      ( [ Pos (t :=: Var y) ]
      ))
    | f <- S.toList fs ++ ds
    , let n = arity f
          tps :-> tp = typing f
          xs = [ Var (var tp i) | (i,tp) <- [1..n] `zip` tps ]
          y  = var tp 0
          t  = Fun f xs
    , M.lookup t assignCons == Nothing
    ]

  constants =
    map (\g@((t,_):_) -> (t,map snd g)) $
    groupBy (\x y -> fst x == fst y) $
    sort $
    [ (typ t,t)
    | c <- S.toList fs
    , arity c == 0
    , let t = Fun c []
    ]

  units =
    [ lit
    | [lit] <- cs
    , S.size (free lit) <= 2
    ]

  cliques =
    [ (t,findClique cs units)
    | (t,cs) <- constants
    ]

  assigns =
    [ (t,i)
    | (_,ts) <- cliques
    , (t,i)  <- ts `zip` [1..]
    ]

  assignCons =
    M.fromList
      [ (t, Fun (elt i) [])
      | (t,i) <- assigns
      ]

  syms = symbols cs
  fs   = S.filter (\f -> case typing f of
                           _ :-> tp -> tp /= bool
                           _        -> False) syms

findClique :: [Term] -> [Signed Atom] -> [Term]
findClique [] units = []
findClique ts units = S.toList (largestClique S.empty graph)
 where
  cons = S.fromList ts
  
  (posInfo, negInfo) = foldr gather (S.empty, S.empty) units
   where
    gather (Pos p) (pos, neg) = (pos `S.union` inst p, neg)
    gather (Neg p) (pos, neg) = (pos, neg `S.union` inst p)
  
    inst p = S.fromList [ norm (subst sub p) | sub <- subs (S.toList (free p)) ]
     where
      norm (a :=: b) | b < a = b :=: a
      norm p                 = p
    
    subs []     = [ids]
    subs (x:xs) = [ (x |=> t) |+| sub | sub <- subs xs, t <- ts ]
  
  edges = 
    [ (a,b)
    | (a,b) <- pairs (S.toList cons)
    , a `notEqual` b
    ]
   where
    a `notEqual` b = a `eqNotEqual` b || a `repNotEqual` b

    a `eqNotEqual` b =
      (a :=: b) `S.member` negInfo

    a `repNotEqual` b =
      S.size (rep posInfo `S.intersection` rep negInfo) > 0
     where
      rep xs = S.fromList [ p `prd` map (replace a b) ys
                          | Fun p ys :=: t <- S.toList xs
                          , t == truth
                          ]

      replace a b a' | a == a' = b
      replace a b (Fun f xs) = Fun f (map (replace a b) xs)
  
  graph = 
    M.fromListWith S.union $
      concat [ [(a, S.singleton b), (b, S.singleton a)]
             | (a,b) <- edges
             ]
        ++ [ (a, S.empty)
           | a <- ts
           ]
  
  largestClique cl gr
    | M.null gr = cl
    | S.size cl >= 1 + S.size bs
       || S.size cl >= S.size cl' = largestClique cl gr'
    | otherwise                   = largestClique cl' gr'
   where
    ((a,bs),rest) = M.deleteFindMin gr
    gr'   = M.map (a `S.delete`) rest
    cl'   = a `S.insert` largestClique S.empty subgr
    subgr = M.fromList [ (x, xs `S.intersection` bs)
                       | x <- S.toList bs
                       , let xs = case M.lookup x gr' of
                                    Just a -> a
                                    Nothing -> error "clique: not in table"
                       ]

  pairs []     = []
  pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs

-------------------------------------------------------------------------
-- definitions

definitions :: [Clause] -> ([Symbol], [Clause], [Clause])
definitions cs = ([ f | (_, Fun f _) <- list ], defCs, coreCs)
 where
  deepTerms =
    [ t'
    | t <- S.toList (subterms cs)
    , typ t /= bool
    , let (_,t') = normalize t
    , isOkTerm (t' `S.member` ts) t'
    ]
   where
    ts = topterms cs
   
  list =
    [ (t, Fun (df % i ::: (map typ xs :-> typ t)) xs)
    | (t,i) <- deepTerms `zip` [1..]
    , let xs = map Var (S.toList (free t))
    ]

  defCs =
    [ [Pos (deft :=: Fun f (map replace xs))]
    | (Fun f xs, deft) <- list
    ]

  coreCs =
    [ map replaceLit c
    | c <- cs
    ]

  tab =
    M.fromList list

  normalize t =
    norm t ids [vr % i | i <- [1..]] (\t' sub _ -> (sub,t'))
   where
    norm (Var v)    sub (w:ws) k = k (Var v) (((w ::: typing v) |=> Var v) |+| sub) ws
    norm (Fun f xs) sub ws     k =
      norms xs sub ws $ \xs' sub' ws' ->
        k (Fun f xs') sub' ws'
    
    norms []     sub ws k = k [] sub ws
    norms (t:ts) sub ws k =
      norm t sub ws $ \t' sub' ws' ->
        norms ts sub' ws' $ \ts' sub'' ws'' ->
          k (t':ts') sub'' ws''
  
  isOkTerm top (Var _)    = False
  isOkTerm top (Fun _ xs) = any (not . isVar) xs
                          -- && S.size (free xs) <= 1
                         && any (isAlreadyConnected (free xs)) xs
                          -- && (not top || all isGroundTerm xs)
   where
    isVar (Var _) = True
    isVar _       = False
    
    isAlreadyConnected vs (Var v)    = vs `S.isSubsetOf` S.fromList [v]
    isAlreadyConnected vs (Fun _ xs) = vs `S.isSubsetOf` S.fromList [ v | Var v <- xs ]
                                    || any (isAlreadyConnected vs) xs

  topterms []     = S.empty
  topterms (c:cs) = tops c `S.union` topterms cs
   where
    tops ls =
      S.fromList [ t
                 | l <- ls
                 , let a :=: b = the l
                 , t <- case a of
                          Fun p ts | b == truth -> ts
                          _                     -> [a,b]
                 ]

  replaceLit (Pos a) = Pos (replaceAtom a)
  replaceLit (Neg a) = Neg (replaceAtom a)

  replaceAtom (a :=: b) = replace a :=: replace b
  
  replace (Var v)        = Var v
  replace t@(Fun f xs) =
    case M.lookup t' tab of
      Nothing  -> Fun f (map replace xs)
      Just t'' -> subst sub t''
   where
    (sub,t') = normalize t

-------------------------------------------------------------------------
-- flatten

flatten :: (Map Term Term) -> Clause -> [Clause]
flatten assignCons ls = simplify (defs ++ flatLs)
 where
  fls = free ls
  
  vs = [ v
       | i <- [1..]
       , let v = vr % i
       ]
  
  tab =
    M.fromList
      [ (t,v)
      | (t,fv) <- S.toList (subterms ls) `zip` vs
      , typ t /= bool
      , let v = case t of
                  Var v -> v
                  _     -> fv ::: V (typ t)
      ]
  
  var t =
    case M.lookup t assignCons of
      Just ci                       -> ci
      Nothing 
        | tdomain (typ t) == Just 1 -> Fun (elt 1) []
        | otherwise                 -> Var (case M.lookup t tab of
                                              Just t' -> t'
                                              Nothing -> error ("flatten: not in var-table: " ++ show t))

  defs =
    [ Neg (Fun f (map var ts) :=: Var v)
    | (t@(Fun f ts), v) <- M.toList tab
    , M.lookup t assignCons == Nothing
    ]
  
  flatLs =
    [ flat `fmap` l
    | l <- ls
    ]
  
  flat (Fun p ts :=: b) | b == truth =
    p `prd` map var ts

  flat (a :=: b) =
    var a :=: var b

-------------------------------------------------------------------------
-- simplify

-- rules:
-- P | -P               | C         ==>   { }                          (truth)
-- X  = X               | C         ==>   { }                          (truth)
-- X != X               | C         ==>   { C }                        (falsity)
-- X != Y               | C[X,Y]    ==>   { C[X,X] }                   (subst)
-- f(X1..Xk) != Y | Z=Y | C[X,Z]    ==>   { f(X1..Xk) = Z | C[X,Z] }   (subst)

simplify :: Clause -> [Clause]
simplify = simp
 where
  simp c0 =
    [ c4
    | c1 <- trivial c0
    , c2 <- identEq c1
    , c3 <- substVarEq c2
    , c4 <- substFunEq c3
    ]
  
  trivial ls
    | any ((`S.member` S.fromList ls) . negat) ls = []
    | otherwise                                   = [ls]
  
  identEq ls =
    case [ ()
         | Pos (s :=: t) <- ls
         , s == t
         ] of
      [] -> [ls]
      _  -> []
  
  substVarEq ls = substVar [] ls
   where
    substVar ls' (Neg (Var v :=: Var w) : ls) =
      simp (subst (v |=> Var w) (ls' ++ ls))
    
    substVar ls' (Neg (Var v :=: t@(Fun c [])) : ls) | isElt c =
      simp (subst (v |=> t) (ls' ++ ls))
    
    substVar ls' (Neg ((Fun c1 []) :=: t@(Fun c2 [])) : ls) | isElt c1 && isElt c2 && c1 /= c2 =
      []
    
    substVar ls' (l:ls) =
      substVar (l:ls') ls
    
    substVar ls' [] =
      [ls']
  
  substFunEq ls = substFun [] ls
   where
    substFun ls' (l@(Neg (t :=: Var v)) : ls)
      | not (v `S.member` free t) =
      substTerm v t [] (ls' ++ ls) (substFun (l:ls') ls)
    
    substFun ls' (l:ls) =
      substFun (l:ls') ls
    
    substFun ls' [] =
      [ls']

    substTerm v t ls' (Pos (t1 :=: t2) : ls) k
      | leftSubst  = substTerm v t (Pos (t :=: t2):ls') ls k
      | rightSubst = substTerm v t (Pos (t :=: t1):ls') ls k
     where
      leftSubst  = t1 == Var v && isSmall t2
      rightSubst = t2 == Var v && isSmall t1
      
      isSmall (Var _)    = True
      isSmall (Fun c []) = isElt c
      isSmall _          = False

    substTerm v t ls' (l:ls) k
      | v `S.member` free l = k
      | otherwise           = substTerm v t (l:ls') ls k
    
    substTerm v t ls' [] k =
      simp ls'

-------------------------------------------------------------------------
-- purify

purify :: [Clause] -> ([(Symbol,Bool)],[Clause])
purify cs
  | null ps   = (ps,cs')
  | otherwise = (ps'++ps,cs'')
  -- | otherwise = ([],cs)
 where
  (ps,cs')   = pure M.empty cs
  (ps',cs'') = purify cs'
  
  pure tab [] =
    ( removePs
    , [ c
      | c <- cs
      , all (not . isRemoveP . the) c
      ]
    )
   where
    removePs =
      [ (p,head (S.toList sgns))
      | (p,sgns) <- M.toList tab
      , S.size sgns == 1
      ]
    
    setPs = S.fromList [ p | (p,_) <- removePs ]
    isRemoveP (Fun p _ :=: b) = b == truth && p `S.member` setPs

  pure tab (c:cs) = pure (M.unionWith S.union occurs tab) cs
   where
    posP = S.fromList [ p | Pos (Fun p xs :=: b) <- c, b == truth ]
    negP = S.fromList [ p | Neg (Fun p xs :=: b) <- c, b == truth ]
   
    occurs =
      M.fromList $
        [ (pn,S.singleton True)  | pn <- S.toList $ posP `S.difference` negP ] ++
        [ (pn,S.singleton False) | pn <- S.toList $ negP `S.difference` posP ]

-------------------------------------------------------------------------
-- split

splitAll :: [Clause] -> [Clause]
splitAll cs = splitting 1 cs (\_ -> [])
 where
  splitting i []     k = k i
  splitting i (c:cs) k = hyper i connections ls (\i -> splitting i cs k)
   where
    ls  = c
    n   = S.size (free ls)
    lvs = map free ls

    connections =
      [ (v,ws)
      | (v,ws) <- 
          M.toList $
            M.fromListWith S.union
              [ (v,S.fromList ws)
              | vs     <- lvs
              , (v,ws) <- select (S.toList vs)
              ]
      , S.size ws < n-1
      ]

    hyper i []   ls k = break i ls k
    hyper i cons ls k = break (i+1) (Neg p : left)
                        (\i -> hyper i cons' (Pos p : right) k)
     where
      (v,_) = minimumBy siz cons
      rest  = [ x | x@(w,_) <- cons, v /= w ]
      (v1,s1) `siz` (v2,s2) =
        (S.size s1,tpsize v2,inter s2) `compare` (S.size s2,tpsize v1,inter s1)

      tpsize v = case tdomain (typ (Var v)) of
                   Nothing -> maxBound
                   Just d  -> d

      inter s =
        sum [ S.size (s `S.intersection` vs) | (v,vs) <- cons, v `S.member` s  ]
       where
        xs = S.toList s

      cons' =
        [ (w,ws')
        | (w,ws) <- rest
        , w `S.member` freeRight
        , let ws' = (ws `S.union` extra) `S.intersection` freeRight
              extra | w `S.member` vs = vs
                    | otherwise       = S.empty
        , S.size ws' < S.size freeRight-1
        ]

      vs           = free left `S.intersection` freeRight
      p            = (sp % i ::: (map typ xs :-> bool)) `prd` xs
      xs           = map Var (S.toList vs)
      (left,right) = partition ((v `S.member`) . free) ls
      freeRight    = free right

    break i ls k =
      case [ ls'
           
           -- only try when number of variables is at least 3
           | S.size (free ls) >= 3
           
           -- for all "non-recursive" definitions in ls
           , def@(Neg (t@(Fun _ _) :=: Var y)) <- ls
           , not (y `S.member` free t)
           
           -- gather literals which contain y
           , let (lsWithY, lsWithoutY) =
                   partition ((y `S.member`) . free) (ls \\ [def])
                 
           -- there should be at least 2 such literals ...
           , lWithY:(lsWithY'@(_:_)) <- [lsWithY]
           
           -- now, partition the literals containing y
           -- into two separate groups, not containing
           -- any overlapping variables except the variables in def
           , let connToY = y `S.delete` free lsWithY
                 ok      = free def
           
                 (lsLeft, lsRight) =
                   part (free lWithY) [lWithY] [] lsWithY'
                  where
                   part vs left right [] = (left, right)
                   part vs left right (l:ls)
                     | S.size ((ws `S.intersection` vs) `S.difference` ok) == 0 =
                         part vs left (l:right) ls
                     
                     | otherwise =
                         part (vs `S.union` ws) (l:left) right ls
                    where
                     ws = free l
           
           -- they should not all end up on one side
           , not (null lsRight)
           
           -- construct the new clause with the extra literal
           , let y'  = prim "C" % i ::: typing y
                 ls' = [ def
                       , Neg (t :=: Var y')
                       ]
                    ++ subst (y |=> Var y') lsLeft
                    ++ lsRight
                    ++ lsWithoutY
           ] of
        -- _       -> set ls : k i
        []      -> ls : k i
        (ls':_) -> splitting (i+1) [ls'] k
    
select :: [a] -> [(a,[a])]
select []     = []
select (x:xs) = (x,xs) : [ (y,x:ys) | (y,ys) <- select xs ]

-------------------------------------------------------------------------
-- the end.
