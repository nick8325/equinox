module Main where

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

import Runner
import Flags

import Form
import Name
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import Paradox.Flatten
import Paradox.Instantiate
import Paradox.AnalysisTypes
import Paradox.SolveInstances

import Output

import System.IO
  ( hFlush
  , stdout
  )

import Data.List
  ( group
  , sort
  , nub
  , intersperse
  )

import System.Exit
  ( exitWith
  , ExitCode(..)
  )

---------------------------------------------------------------------------
-- main

main :: IO ()
main =
  do putStrLn "Paradox, version 4.0, 2010-06-29."
     --putStrLn "*** NOTE: THIS IS A NON-STANDARD, DELIBERATELY UNSOUND VERSION!"
     runner Paradox solveProblem

-------------------------------------------------------------------------
-- problem

solveProblem :: (?flags :: Flags) => [Clause] -> [Clause] -> IO ClauseAnswer
solveProblem theory oblig =
  do {-
     putStrLn "==> Input clauses"
     sequence_ [ putStrLn (showClause c) | c <- csIn ]
     print (length csIn)
     putStrLn "==> Simplified clauses"
     sequence_ [ putStrLn (showClause c) | c <- csSimp ]
     print (length csSimp)
     --putStrLn "==> Purified clauses"
     --sequence_ [ putStrLn (showClause c) | c <- csPure ]
     --sequence_ [ putStrLn ("pure: " ++ show p ++ " " ++ show b) | (p,b) <- predsPure ]
     --print (length csPure)
     putStrLn "==> Types"
     sequence_ [ putStrLn (show t ++ maybe "" (\n -> " <= " ++ show n) (tsize t) ++ " -- " ++ show (tequal t)) | t <- typs ]
     sequence_ [ putStrLn (show f ++ " : " ++ show (typing f)) | f <- S.toList (symbols cs), not (isVarSymbol f) ]
     --print (length typs)
     putStrLn "==> Flattened clauses"
     sequence_ [ putStrLn (show c) | c <- predefs ]
     sequence_ [ putStrLn ("[" ++ show (S.size (free c)) ++ "] " ++ showClause c) | c <- fcs ]
     sequence_ [ putStrLn (show c) | c <- qcs ]
     print (length fcs + length qcs)
     putStrLn "==> Solving..."
     -}
     (r,k) <- solveInstances
                flags
                predsPure
                minSize
                (annotate [1..] ns' (instantiate flags predefs fcs qcs))
     return $
       case r of
         Satisfiable                        -> Satisfiable
         NoAnswerClause GaveUp
           | not isFinite || k <= maxDomain -> NoAnswerClause GaveUp
         _                                  -> Unsatisfiable
 where
  flags = ?flags

  csIn                       = theory ++ oblig
  csSimp                     = concatMap simplify csIn
  (predsPure,csPure)         = purify csSimp
  mTypeResult                = types csPure
  Right (typs,annotateTypes) = mTypeResult
  cs                         = map annotateTypes csPure
  (predefs,fcs,qcs)          = macify cs

  minSize = maximum (1 : map snd predefs)

  degree :: Symbolic a => a -> Int
  degree x = S.size . free $ x
  ds       = map degree fcs ++ map degree qcs
  d        = maximum (0:ds)

  n = fromInteger (search0 (\n -> estimate n - big) 1 (fromIntegral bigDom + 1))
   where
    search0 :: (Integer -> Integer) -> Integer -> Integer -> Integer
    search0 f mn mx = srch mn mx
     where
      srch mn mx
        | mn+1 >= mx = mn
        | y < 0      = srch x mx
        | y > 0      = srch mn x
        | y == 0     = x
       where
        x = (mn+mx) `div` 2
        y = f x

    bigDom = if isFinite then maxDomain else 9999999 -- max domain size
    big    = 999999999

    isize v = case tdomain t of
                Nothing -> bigDom
                Just k  -> k
     where
      V t = typing v

    groupN :: Ord a => [a] -> [(Int,a)]
    groupN = map (\xs -> (length xs, head xs))
           . group
           . sort

    mask :: Symbolic a => a -> [(Int, Int)]
    mask c = groupN
           . map isize
           . S.toList
           . free
           $ c

    masks = groupN
          $ map mask fcs ++ map mask qcs

    estimate n =
      let x = sum [ fromIntegral a
                  * product [ (fromIntegral n' `min` n) ^ fromIntegral b
                            | (b,n') <- msk
                            ]
                  | (a,msk) <- masks
                  ]

       in x -- spy "est" (n,x) `seq` x

  ns' = [ i | i <- [1..n], i >= minSize ]

  annotate ks     []         syss                            = []
  annotate (k:ks) _          _   | isFinite && k > maxDomain = []
  annotate (k:ks) is@(i:is') ((ass,sys):syss) =
    (k,k==i,ass,sys) : annotate ks (if k==i then is' else is) syss

  -- statistics original problem
  syms = symbols cs

  numFuns = length [ () | f <- S.toList syms, _  :-> b <- [typing f], b /= bool ]
  numCons = length [ () | c <- S.toList syms, [] :-> b <- [typing c], b /= bool ]

  (isFinite,maxDomain,maxDom,whyDom) = minn
    [ (numCons == numFuns, maximum (1 : [ n | t <- typs
                                            , Just n <- [tsize t]
                                            ]), "epr")
    , case [ n | Just n <- map limited cs ] of
        [] -> (False, 0, "")
        ns -> (True, minimum ns, "equality")
    ]
   where
    minn xs =
      case [ (n,why) | (True,n,why) <- xs ] of
        [] -> (False, error "There is no upper bound", "-", "")
        ns -> (True, mn, show mn, "  (" ++ why ++ ")")
         where
          (mn,why) = foldr1 (\(a,x) (b,y) -> if a < b then (a,x) else (b,y)) ns

    limited c =
      case c of
        Pos (Var x :=: t) : ls
          | not (x `S.member` free t) && lim x ls -> Just n

        Pos (t :=: Var x) : ls
          | not (x `S.member` free t) && lim x ls -> Just n

        _ -> Nothing
       where
        lim x [] = True
        lim x (Pos (Var y :=: t) : ls)
          | x == y && not (x `S.member` free t) = lim x ls
        lim x (Pos (t :=: Var y) : ls)
          | x == y && not (x `S.member` free t) = lim x ls
        lim x _ = False

        n = length c

---------------------------------------------------------------------------
-- the end.
