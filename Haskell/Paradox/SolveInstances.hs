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

-- external

data Loc = Abstract_Loc

newLoc :: Int -> S Loc
newLoc = error "not implemented yet"

data Arg
  = ArgV Int
  | ArgN Int

data Atm
  = Loc :@ [Arg]

addClauses :: [Int] -> [Signed Atm] -> S ()
addClauses = error "not implemented yet"

getLit :: Signed Atm -> S Lit
getLit = error "not implemented yet"

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
                        ]
         
         processClause k c =
           do ls' <- mapM processLit ls
              let args = [ k `min` isize t | v <- vs, let V t = typing v ]
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
             do loc <- getPredLoc (prim "eq" ::: ([top,top] :-> bool))
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
           do let clauses' = flat clauses
              
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
                return Satisfiable
               else
                domains rest

     run $ domains css

-------------------------------------------------------------------------
-- the end.
