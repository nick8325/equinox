module Paradox.Instantiate where

{-
Paradox -- Copyright (c) 2003-2007, Koen Claessen, Niklas Sorensson

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

import Form hiding ( Form(..) )
import Name
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import List hiding ( insert, delete, union )
import Paradox.AnalysisTypes
import Flags

-------------------------------------------------------------------------
-- clause sets

data ClauseSet
  = ForAll [Clause]
  | ForAllNew Int [Clause]
 deriving (Show, Eq)

elt :: Int -> Symbol
elt = \i -> (el % i) ::: ([] :-> top)

isElt :: Symbol -> Bool
isElt (c ::: _) = isEltName c

-------------------------------------------------------------------------
-- instantiate

instantiate :: Flags -> [(Type,Int)] -> [Clause] -> [QClause] -> [(Symbol,[ClauseSet])]
instantiate flags predefs cs qcs =
  [ (assump, ForAll symcs : cs)
  | ((assump,cs),symcs) <- parts 1 [] patterns nonGroundCs
                     `zip` symmetries
  ]
 where
  (groundCs, nonGroundCs) = partition isGround (sortBy siz cs)
   where
    c1 `siz` c2 = length c1 `compare` length c2

  iqcs = [1..] `zip` qcs
  
  syms = symbols cs

  isGround c = S.size (free c) == 0
  
  con k = Fun (elt k) []
  
  symmetries :: [[Clause]]
  symmetries =
    transp
    [ symmForType tp predef
    | (tp,predef) <- predefs
    ]
   where
    transp []  = repeat []
    transp xss = concat [ x | x:_ <- xss ] : transp [ xs | _:xs <- xss ]
   
    symmForType tp predef =
      zipWith (\k f -> f k) [1..]
        -- do not use symmetries before predef size
         $ replicate predef (\_ -> [])

        -- constant-triangle
        ++ [ \k ->
               [ [ Pos (t :=: con i) | i <- [1..k] ]
               ]
           | t <- allCons
           ]

        -- predicate-symmetries
        ++ [ \k -> if k <= predef then error "predef???" else [] | not (null allUnitPreds)]
        ++ concat
           [ repeat $ \k ->
               [ [ Neg (p `prd` [con k])
                 , Pos (p `prd` [con (k-1)])
                 ]
               ]
           | (p:_) <- [allUnitPreds]
           ]

        -- function-symmetries
        ++ concat
           [ repeat $ \k ->
               [ c
               | k > n
               , c <- [ [ Pos ((Fun f [con (k-j) | j <- [1..n]]) :=: con i)
                        | i <- [1..k]
                        ]
                      ] ++
                      [ Neg ((Fun f [con (k-1)]) :=: con k)
                      : Neg ((Fun f [con (k-2)]) :=: con (k-1))
                      : [ Pos (Fun f [con j] :=: con (k-2))
                        | j <- [numCons..k-2]
                        , j > 0
                        ]
                      | k > ((numCons + 2) `max` 3)
                      , n == 1
                      ]
               ]
           | ((f,n):_) <- [allFuns]
           , n > 0
           ]
     where
      numCons = predef + length allCons
      
      allCons =
        [ t
        | Uniq (Bind v c) <- qcs
        , [Pos (t@(Fun f []) :=: Var v')] <- [c]
        , v == v'
        , typ t == tp
        ]

      allFuns =
        sortBy cmp
        [ (f,length xs)
        | Uniq (Bind v c) <- qcs
        , [Pos (t@(Fun f (xs@(_:_))) :=: Var v')] <- [c]
        , v == v'
        , typ t == tp
        ]
       where
        (_,x) `cmp` (_,y) = x `compare` y

      allUnitPreds =
        [ p
        | p@(_ ::: ([tp'] :-> b)) <- S.toList syms
        , b == bool
        , tp' == tp
        ]

  parts :: Int -> [Term] -> [[Bool]] -> [Clause] -> [(Symbol,[ClauseSet])]
  parts k oldCons (pat:pats) cs =
    (dom, clauses) : parts (k+1) allCons pats (extra ++ cs)
   where
    dom  = (dm % k) ::: ([] :-> bool)
    domk = dom `prd` []
    
    newCon  = con k
    allCons = newCon : oldCons
    
    qclauses =
      [ c
      | (i,qc) <- iqcs
      , c      <- atMostOne i qc
      ]

    extra =
      [ c
      | c <- qclauses
      , not (isGround c)
      ]
    
    clauses =
      [ ForAll
        ( -- constant equalities
             [ [ Pos (newCon :=: newCon) ] ]
          ++ concat
             [ [ [ Neg (c :=: newCon) ]
               , [ Neg (newCon :=: c) ]
               ]
             | c <- oldCons
             ]

          -- ground clauses (only if k == 1)
          ++ [ c
             | k == 1
             , c <- groundCs
             ]
        )
      , ForAllNew k
        ( -- instantiate clauses
          cs
        )
      , ForAll
        ( -- uniqueness clauses
             [ c
             | qc <- qcs
             , c  <- atLeastOne qc
             ]

          ++ qclauses
        )
      ]
  
    atLeastOne :: QClause -> [Clause]
    atLeastOne (Uniq (Bind v@(_ ::: V tp) c)) =
      [ pre
        [ l
        | a <- allCons
        , l <- subst (v |=> a) c
        ]
      | pre <- case tdomain tp of
                 Just k' | k' == k -> [id]
                         | k  > k' -> []
                 _                 -> [(Neg domk :)]
      ]
  
    atMostOne :: Int -> QClause -> [Clause]
    atMostOne i (Uniq (Bind v@(_ ::: V tp) c)) =
      [ [negat l, a]
      | case tdomain tp of
          Just k' | k > k' -> False
          _                -> True
      , l <- ls
      , a <- pattern i
      ]
     where
      ls      = subst (v |=> newCon) c
      vs      = S.toList (v `S.delete` free c)
      uni i j = (un % i % j ::: (map typ xs :-> bool)) `prd` xs
      xs      = map Var vs

      pattern i =
        [ sgn (uni i j)
        | (j,b) <- [0..] `zip` pat
        , let sgn = if b then Pos else Neg
        ]

-- unique non-empty non-overlapping infinite list of 0/1 patterns

patterns :: [[Bool]]
patterns = pats 4
 where
  pats n = init base ++ map (last base ++) (pats (n+1))
   where
    base = bits n

  bits 0 = [[]]
  bits k = [ False : bs | bs <- bits (k-1) ]
        ++ [ True  : bs | bs <- bits (k-1) ]

-------------------------------------------------------------------------
-- the end.
