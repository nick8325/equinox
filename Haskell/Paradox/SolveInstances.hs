module Paradox.SolveInstances where

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

-- {-
data Loc = Loc

newLoc = undefined

addClauses = undefined

data Arg = ArgV Int | ArgN Int

data Atm = Loc :@ [Arg]

getLit = undefined
-- -}

-------------------------------------------------------------------------
-- solver

solveInstances :: Flags -> [(Symbol,Bool)] -> Int -> [(Int,Bool,Symbol,[ClauseSet])] -> IO Answer
solveInstances flags predsPure minSize css =
  do line <- newIORef False
     ref  <- newIORef (M.empty,M.empty)
     
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
           do sequence_ [ do processClause k c | c <- cs ]
         
         processClauseSet k (ForAllNew k' cs) =
           do sequence_ [ processClause k (subst (x |=> Fun (elt k') []) c)
                        | c <- cs
                        , x <- S.toList (free c)
                        , case tdomain (typ (Var x)) of
                            Just k  -> k >= k'
                            Nothing -> True
                        ]
         
         processClause k c =
           do ls' <- mapM processLit ls
              let args = [ isize t | v <- vs, let V t = typing v ]
              addClauses args ls'
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
         
         domains [] =
           do return Unknown

         domains ((k,check,assump,clauses):rest) =
           do lift $ putStrLn ("domain " ++ show k)
              let clauses' = flat clauses
              
                  flat []                     = []
                  flat (ForAll cs       : ds) = map (\c -> ForAll [c])       cs ++ flat ds
                  flat (ForAllNew k' cs : ds) = map (\c -> ForAllNew k' [c]) cs ++ flat ds

                  tot = length clauses'
              
              sequence_
                [ processClauseSet k c
                | (i,c) <- [1..] `zip` clauses' 
                ]
              
              assumption <- getPredLoc assump >>= \l -> return (Pos (l :@ []))
              ass <- getLit assumption
              
              simplify False False
              
              r <- solve [ass]
              if r then
                do if printModel flags then
                     printTheModel k ref predsPure
                    else
                     return ()
                   return Satisfiable
               else
                domains rest

     run $ domains css

printTheModel k ref predsPure =
  do lift $ putOfficial "BEGIN MODEL"
     lift $ putStrLn ("-- domain size is " ++ show k)
     lift $ putStrLn ""
     (tabf,tabp) <- lift $ readIORef ref
     sequence_ $ intersperse (lift $ putStrLn "") $ map snd $ sortBy first $
       [ (show f,
            do sequence_
                 [ do bs <- sequence [ do l <- getLit (loc :@ ([ ArgN i | i <- is ] ++ [ ArgN j ]))
                                          getModelValue l
                                     | j <- [1.. tdomain' t `min` k]
                                     ]
                      let c = length (takeWhile not bs) + 1
                      lift $ print (Fun f [ Fun (elt i) [] | i <- is ] :=: Fun (elt c) [])
                 | is <- count ms
                 ]
               sequence_
                 [ lift $ print ( Fun f [ if i == j then Fun (elt n) [] else Var (name ("X" ++ show i) ::: V top)
                                        | i <- [1..arity f]
                                        ]
                              :=: Fun f [ if i == j then Fun (elt n) [] else Fun (elt 1) []
                                        | i <- [1..arity f]
                                        ]
                                )
                 | (t,j) <- ts `zip` [1..]
                 , n <- [tdomain' t+1..k]
                 ]
         )
       | (f@(s ::: (ts :-> t)),loc) <- M.toList tabf
       , isSimpleName s
       , let ms = [ tdomain' t `min` k | t <- ts ]
       ] ++
       [ (show f,
            do sequence_
                 [ do l <- getLit (loc :@ [ ArgN i | i <- is ])
                      b <- getModelValue l
                      lift $ print $ (if b then Pos else Neg) $ (Fun f [ Fun (elt i) [] | i <- is ] :=: truth)
                 | is <- count ms
                 ]
               sequence_
                 [ lift $ print ( Fun f [ if i == j then Fun (elt n) [] else Var (name ("X" ++ show i) ::: V top)
                                        | i <- [1..arity f]
                                        ]
                              :=: Fun f [ if i == j then Fun (elt n) [] else Fun (elt 1) []
                                        | i <- [1..arity f]
                                        ]
                                )
                 | (t,j) <- ts `zip` [1..]
                 , n <- [tdomain' t+1..k]
                 ]
         )
       | (f@(s ::: (ts :-> _)),loc) <- M.toList tabp
       , isSimpleName s
       , let ms = [ tdomain' t `min` k | t <- ts ]
       ] ++
       [ (show p,
            lift $
              print $
                (if b then Pos else Neg) $
                  p `prd` [ Var (name ("X" ++ show i) ::: V top) | i <- [1..arity p] ]
         )
       | (p,b) <- predsPure
       ]
     lift $ putOfficial "END MODEL"
 where
  (x,_) `first` (y,_) = x `compare` y

  tdomain' t = case tdomain t of
                 Nothing -> maxBound - 1
                 Just k  -> k

  count [] = [[]]
  count (m:ms) =
    [ i:is
    | i <- [1..m]
    , is <- count ms
    ]

-------------------------------------------------------------------------
-- the end.
