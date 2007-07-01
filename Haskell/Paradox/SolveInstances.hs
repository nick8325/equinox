module Paradox.SolveInstances where

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

import qualified Sat as S
import Sat
import Form hiding ( Form(..) )
import Name
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import Data.IORef
import Flags
import List( sortBy, intersperse )
import IO
import Paradox.Instantiate
import Output
import Paradox.AnalysisTypes
import Monad

{-
data Loc = Loc

newLoc = undefined

addClauses = undefined

data Arg = ArgV Int | ArgN Int

data Atm = Loc :@ [Arg]

getLit = undefined
-}

-------------------------------------------------------------------------
-- solver

solveInstances :: Flags -> [(Symbol,Bool)] -> Int -> [(Int,Bool,Symbol,[ClauseSet])] -> IO (Answer,Int)
solveInstances flags predsPure minSize css =
  do ref  <- newIORef (M.empty,M.empty)
     
     let getFunLoc f =
           do (tabf,tabp) <- lift $ readIORef ref
              case M.lookup f tabf of
                Nothing  -> do loc <- newLoc (arity f+1)
                               lift $ writeIORef ref (M.insert f loc tabf,tabp)
                               return loc
                Just loc -> do return loc
                               
         getPredLoc p =
           do (tabf,tabp) <- lift $ readIORef ref
              case M.lookup p tabp of
                Nothing  -> do loc <- newLoc (arity p)
                               lift $ writeIORef ref (tabf,M.insert p loc tabp)
                               return loc
                Just loc -> do return loc
     
         processClauseSet k (ForAll cs) =
           do sequence_ [ processClause Nothing k c | c <- cs ]
         
         processClauseSet k (ForAllNew k' cs) =
           do sequence_ [ processClause (Just k') k c | c <- cs ]
         
         processClause mn k c =
           do ls' <- mapM processLit ls
              let args = [ isize t | v <- vs, let V t = typing v ]
              {-
              lift $ putStr {- printStderr -} $ (++ "\n") $ unwords $
                [ "==>"
                ] ++
                [ show n
                | Just n <- [mn]
                ] ++
                [ show (vs `zip` args)
                , "["
                ] ++ (intersperse "|"
                [ show l
                | l <- c
                ]) ++
                [ "]"
                ]
              -}
              addClauses mn args ls'
          where
           ls = c
           vs = S.toList (free c)
           
           isize t =
             case tdomain t of
               Just n  -> n `min` k
               Nothing -> k
           
           processLit l =
             do a <- processAtom (the l)
                return (fmap (const a) l)
           
           processAtom (Fun f xs :=: y) | y /= truth && not (isElt f) =
             do loc <- getFunLoc f
                if arity f /= length xs then error ("arity fel! " ++ show (f,typing f)) else return ()
                return (loc :@ (xs' ++ [y']))
            where
             xs' = map processTerm xs
             y'  = processTerm y
           
           processAtom (Fun p xs :=: b) | b == truth =
             do loc <- getPredLoc p
                return (loc :@ xs')
            where
             xs' = map processTerm xs
           
           processAtom (a :=: b) =
             do loc <- getPredLoc (eq ::: ([top,top] :-> bool))
                return (loc :@ (map processTerm [a,b]))
           
           processTerm (Var v) =
             ArgV (v `ind` vs)
           
           processTerm (Fun (c ::: _) []) | isEltName c =
             ArgN (getIndex c)
         
           x `ind` (y:ys)
             | x == y    = 1
             | otherwise = 1 + (x `ind` ys)             
         
         domains minSize [] =
           do return (GaveUp,minSize)

         domains minSize ((k,check,assump,clauses):rest) =
           do lift $ putStrLn ("domain size " ++ show k)
              --lift $ sequence_ [ putStrLn s | c <- clauses, s <- showClauseSet c ]
              let clauses' = flat clauses
              
                  flat []                     = []
                  flat (ForAll cs       : ds) = map (\c -> ForAll [c])       cs ++ flat ds
                  flat (ForAllNew k' cs : ds) = map (\c -> ForAllNew k' [c]) cs ++ flat ds

                  tot = length clauses'
              
              sequence_
                [ do --lift $ print c
                     processClauseSet k c
                | (i,c) <- [1..] `zip` clauses' 
                ]
              
              assumption <- getPredLoc assump >>= \l -> return (Pos (l :@ []))
              ass <- getLit assumption
              
              --simplify True False
              
              r <- if minSize > k then return False else solve [ass]
              if r then
                do if printModel flags then
                     printTheModel flags k ref predsPure
                    else
                     return ()
                   return (Satisfiable,k)
               else
                do c <- okay
                   if not c then
                     do return (Unsatisfiable,k)
                    else
                     do addClause [-ass]
                        let minSize' | k == minSize = k+1
                                     | otherwise    = minSize
                        domains minSize' rest

     run $ do --Sat.verbose 1
              domains minSize css

printTheModel flags k ref predsPure =
  do lift $ putOfficial "BEGIN MODEL"
     putStrLnTSTP ("SZS output start FiniteModel for " ++ thisFile flags)
     lift $ putStrLn ("% domain size is " ++ show k)
     putStrLnTSTP "fof(domain, fi_domain,"
     putStrLnTSTP ("  (![X] . (" ++ concat (intersperse " | " [ "X = " ++ dom i | i <- [1..k] ]) ++ "))")
     putStrLnTSTP  ")."

     lift $ putStrLn ""

     (tabf,tabp) <- lift $ readIORef ref
     let trans (f,mx) =
           do x <- mx
              return (f,x)
     entries <- sequence $ map trans $ sortBy first $
       [ (f,
            do as <- sequence
                 [ do bs <- sequence [ do l <- getLit (Pos (loc :@ ([ ArgN i | i <- is ] ++ [ ArgN j ])))
                                          getModelValue l
                                     | j <- [1.. tdomain' t `min` k]
                                     ]
                      let defd = or bs
                          c    = length (takeWhile not bs) + 1
                      return ( []
                             , (show f `app` [ dom i | i <- is ])
                            ++ " = "
                            ++ dom (if defd then c else 0)
                             )
                 | is <- count ms
                 ]
               bs <- sequence
                 [ return ( [ "X" ++ show i | i <- [1..arity f], i /= j ]
                          , (show f `app` [ if i == j then dom n
                                                      else "X" ++ show i
                                          | i <- [1..arity f]
                                          ])
                         ++ " = "
                         ++ (show f `app` [ if i == j then dom (n-1)
                                                      else "X" ++ show i
                                          | i <- [1..arity f]
                                          ])
                          )
                 | (t,j) <- ts `zip` [1..]
                 , n <- [tdomain' t+1..k]
                 ]
               return (as ++ bs)
         )
       | (f@(s ::: (ts :-> t)),loc) <- M.toList tabf
       , isSimpleName s
       , let ms = [ tdomain' t `min` k | t <- ts ]
       ] ++
       [ (f,
            do as <- sequence
                 [ do l <- getLit (Pos (loc :@ [ ArgN i | i <- is ]))
                      b <- getModelValue l
                      return ( []
                             , (show f `app` [ dom i | i <- is ])
                            ++ " <=> "
                            ++ (if b then "$true" else "$false")
                             )
                 | is <- count ms
                 ]
               bs <- sequence
                 [ return ( [ "X" ++ show i | i <- [1..arity f], i /= j ]
                          , (show f `app` [ if i == j then dom n
                                                      else "X" ++ show i
                                          | i <- [1..arity f]
                                          ])
                         ++ " <=> "
                         ++ (show f `app` [ if i == j then dom (n-1)
                                                      else "X" ++ show i
                                          | i <- [1..arity f]
                                          ])
                          )
                 | (t,j) <- ts `zip` [1..]
                 , n <- [tdomain' t+1..k]
                 ]
               return (as ++ bs)
         )
       | (f@(s ::: (ts :-> _)),loc) <- M.toList tabp
       , isSimpleName s
       , let ms = [ tdomain' t `min` k | t <- ts ]
       ] ++
       [ (p,
            return [( [ "X" ++ show i | i <- [1..arity p] ]
                    , show p `app` [ "X" ++ show i | i <- [1..arity p] ]
                   ++ " <=> "
                   ++ (if b then "$true" else "$false")
                    )]
         )
       | (p,b) <- predsPure
       ]
     lift $ sequence_ $ intersperse (putStrLn "") $
       [ if tstp flags then
           do putStrLn ( "fof("
                      ++ show f
                      ++ ", fi_"
                      ++ (if isPredSymbol f then "predicates" else "functors")
                      ++ ","
                       )
              sequence_
                [ putStrLn ( "  "
                          ++ [c]
                          ++ " "
                          ++ (if null xs then ""
                                         else "![" ++ concat (intersperse "," xs) ++ "] . ")
                          ++ ent
                           )
                | (c,(xs,ent)) <- ('(' : repeat '&') `zip` tab
                ]
              putStrLn "  )"
              putStrLn ")."
         else
           do sequence_
                [ putStrLn ent
                | (_,ent) <- tab
                ]
       | (f,tab) <- entries
       ]
     putStrLnTSTP ("SZS output end FiniteModel for " ++ thisFile flags)
     lift $ putOfficial "END MODEL"
 where
  putStrLnTSTP s
    | tstp flags = lift $ putStrLn s
    | otherwise  = return ()
    
  (x,_) `first` (y,_) = show x `compare` show y

  tdomain' t = case tdomain t of
                 Nothing -> maxBound - 1
                 Just k  -> k

  f `app` [] = f
  f `app` xs = f ++ "(" ++ concat (intersperse "," xs) ++ ")"

  dom i | tstp flags = show (show i)
        | otherwise  = '!' : show i

  count [] = [[]]
  count (m:ms) =
    [ i:is
    | i <- [1..m]
    , is <- count ms
    ]

showClauseSet :: ClauseSet -> [String]
showClauseSet (ForAll cs)      = [ show c | c <- cs ]
showClauseSet (ForAllNew x cs) = [ "#" ++ show x ++ ". " ++ show c | c <- cs ]

-------------------------------------------------------------------------
-- the end.
