------------------------------------------------------------------
-- Paradox, a Finite Domain Model Finder for First Order Logic  --
-- Copyright (c) 2003 Koen Claessen and Niklas Sörensson        --
-- {koen,nik}@cs.chalmers.se                                    --
--                                                              --
-- This file is part of Paradox.                                --
--                                                              --
-- Paradox is free software; you can redistribute it and/or     --
-- modify it under the terms of the GNU General Public License  --
-- as published by the Free Software Foundation; either version --
-- 2 of the License, or (at your option) any later version.     --
--                                                              --
-- Paradox is distributed in the hope that it will be useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty  --
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See  --
-- the GNU General Public License for more details.             --
--                                                              --
-- You should have received a copy of the GNU General Public    --
-- License along with Paradox; if not, write to the Free        --
-- Software Foundation, Inc., 59 Temple Place, Suite 330,       --
-- Boston, MA 02111-1307 USA.                                   --
------------------------------------------------------------------
module SolveProblem where

{-

This module transforms and instantiates a clause set and calls
the incremental SAT solver on it.

-}

import Flatten
import Instantiate
import AnalysisTypes
import SolveInstances

import Data hiding ( Type )
import Flags
import Set

import Output

import Utils
  ( search0
  , ljust
  , rjust
  )

import IO
  ( hFlush
  , stdout
  )

import List
  ( group
  , sort
  , nub
  , intersperse
  )

import System
  ( exitWith
  , ExitCode(..)
  )

import Trace

-------------------------------------------------------------------------
-- problem

solveProblem :: Flags -> [Int] -> [Clause] -> IO ()
solveProblem flags ns csIn =    
  do putBlock (Original `elem` prints flags)
       "Original problem" $
         map pclause cs

     case mTypeResult of
       Left s ->
         do putStrLn ("TYPE ERROR: " ++ s)
            exitWith (ExitFailure 1)

       _ -> return ()

     case cfile flags of
       Nothing   -> return ()
       Just file -> do writeFile file $ unlines $
                         [ "% Original problem:"
                         ]
                       appendFile file (unlines (map tclause cs))

     putBlock (Types `elem` prints flags)
       "Types" $
         [ "type " ++ show t ++ " "
        ++ (case tsize t of
              Nothing -> ""
              Just n  -> "<= " ++ show n ++ " ")
        ++ (case equality t of
              Safe -> ""
              Half -> " % half equality"
              Full -> " % full equality")
         | t <- typs
         ] ++
         [ ""
         ] ++
         [ show p ++ " : " ++ show t
         | (p ::- t,n) <- elements ps
         ] ++
         [ ""
         | size ((Equal,2) `delete` ps) > 0
         , size fs > 0
         ] ++
         [ show f ++ " : " ++ show t
         | (f ::- t,n) <- elements fs
         ]

     putBlock (Flattened `elem` prints flags)
       "Flattened problem" $
         map pclause fcs ++ map qclause qcs

     putBlock (Statistics `elem` prints flags) "Statistics"
       [ "Original problem"
       , ljust 20 "  clauses:"        ++ rjust 6 (show (length cs))
       , ljust 20 "  functions:"      ++ rjust 6 (show numFuns)
       , ljust 20 "    - constants:"  ++ rjust 6 (show numCons)
       , ljust 20 "    - max arity:"  ++ rjust 6 arFuns
       , ljust 20 "  predicates:"     ++ rjust 6 (show numPreds)
       , ljust 20 "    - max arity:"  ++ rjust 6 arPreds
       , ljust 20 "  types:"          ++ rjust 6 (show numTypes)
       , "Flattened problem"
       , ljust 20 "  normal clauses:"   ++ rjust 6 (show (length fcs))
       , ljust 20 "  defining clauses:" ++ rjust 6 (show (length qcs))
       , ljust 20 "  predicate splits:" ++ rjust 6 (show numSplits)
       , ljust 20 "  term splits:"      ++ rjust 6 (show numTermDefs)
       , ljust 20 "  variable splits:"  ++ rjust 6 (show numDupVars)
       , ljust 20 "  pure predicates:"  ++ rjust 6 (show (length predsPure))
       , ljust 20 "  pre-assigned:"     ++ rjust 6 (show (sum (map snd predefs)))
       , ljust 20 "  degree:"           ++ rjust 6 (show d)
       , "Judgement"
       , ljust 20 "  max. feasible:"    ++ rjust 6 (show n)
       , ljust 20 "  max. necessary:"   ++ rjust 6 maxDom ++ whyDom
       ]

     res <- solveInstances flags predsPure
              minSize (annotate [1..] ns' (instantiate flags predefs fcs qcs))

     t <- getTimeSpentS flags
     putBlock True "Result" $
       [ rjust 9 t ++ " | " ++
         if pretend flags
           then "PRETENDING"
           else case res of
                  Solution k ->
                    "SATISFIABLE (size = " ++ show k ++ ")"

                  Inconclusive k | not isFinite || k <= maxDomain ->
                    "INCONCLUSIVE (size >= " ++ show k ++ ")"

                  _ ->
                    "CONTRADICTION"
       ]
 where
  csSimp                     = concatMap simplify csIn -- (map trans csIn)
  (predsPure,csPure)         = purify csSimp
  mTypeResult                = types csPure
  Right (typs,annotateTypes) = mTypeResult
  cs                         = map annotateTypes csPure
  (predefs,fcs,qcs)          = macify cs

  minSize = maximum (1 : map snd predefs)

  degree x = size . free $ x
  ds       = map degree fcs ++ map degree qcs
  d        = maximum (0:ds)

  n = fromInteger (search0 (\n -> estimate n - big) 1 (fromIntegral bigDom + 1))
   where
    bigDom = if isFinite then maxDomain else 10000 -- max domain size
    big    = 15000000  -- max #clauses
  
    isize v = case tdomain t of
                Nothing -> bigDom
                Just k  -> k
     where
      VType t = typing v 
   
    groupN :: Ord a => [a] -> [(Int,a)]
    groupN = map (\xs -> (length xs, head xs))
           . group
           . sort
   
    mask :: Abstraction s => s -> [(Int,Int)]
    mask c = groupN
           . map isize
           . elements
           . free
           $ c
    
    masks :: [(Int,[(Int,Int)])]
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

  ns' | null ns   = [ i | i <- [1..n], i >= minSize ]
      | otherwise = [ i | i <- nub (sort ns), i >= minSize ]

  annotate ks     []         syss                            = []
  annotate (k:ks) _          _   | isFinite && k > maxDomain = []
  annotate (k:ks) is@(i:is') ((ass,sys):syss) =
    (k,k==i,ass,sys) : annotate ks (if k==i then is' else is) syss

  -- statistics original problem
  (vs,fs,ps) = symbols cs

  numFuns  = length [ () | _     <- elements fs ]
  numCons  = length [ () | (_,0) <- elements fs ]
  arFuns   = max'   [ n  | (_,n) <- elements fs ]
  numPreds = length [ () | _     <- elements ps ]
  arPreds  = max'   [ n  | (_,n) <- elements ps ]

  max' [] = "-"
  max' xs = show (maximum xs)

  numTypes = length typs
  
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
      case elements c of
        Pos (Pred _ Equal [Var x, t]) : ls
          | x `notMember` free t && lim x ls -> Just n
        
        Pos (Pred _ Equal [t, Var x]) : ls
          | x `notMember` free t && lim x ls -> Just n
        
        _ -> Nothing
       where
        lim x [] = True
        lim x (Pos (Pred _ Equal [Var y, t]) : ls)
          | x == y && x `notMember` free t = lim x ls
        lim x (Pos (Pred _ Equal [t, Var y]) : ls)
          | x == y && x `notMember` free t = lim x ls
        lim x _ = False
        
        n = size c
    
  -- statistics flattened problem
  (vs',fs',ps') = symbols fcs

  numTermDefs = length [ () | (f,_) <- elements fs', isDefSymbol f ]
  numSplits   = length [ () | (p,_) <- elements ps', isSplitSymbol p ]
  numDupVars  = length [ () | v     <- elements vs', isVarCopySymbol v ]

trans :: Clause -> Clause
trans c = set (map transLit ls)
 where
  ls = elements c

  transLit (Pos a) = Pos (transAtom a)
  transLit (Neg a) = Neg (transAtom a)
  
  transAtom (Pred _ p xs) = p `prd` map transTerm xs
  
  transTerm (App _ f@(MkName _ (Extern "skf18") ::- _) xs) =
    f `app` [tup 1 [tup 4 [tup 3 [tup 2 [a1,a2],a3],a4],a5],a6,a7]
   where
    [a1,a2,a3,a4,a5,a6,a7] = xs
    
    tup i = app (name "tup" % i ::- Unknown)
  
  transTerm (App _ f xs) = f `app` map transTerm xs
  transTerm t            = t

-------------------------------------------------------------------------
-- the end.
