module Main where

import Form
import Control.Concurrent
import Control.Exception
import System
--import Flags
--import ParseProblem
--import Clausify
import IO( hSetBuffering, stdout, BufferMode(..) )

import Output

---------------------------------------------------------------------------
-- main

type Flags = ()

time :: Flags -> Maybe Int
time = undefined

files :: Flags -> [FilePath]
files = undefined

roots :: Flags -> [FilePath]
roots = undefined

getFlags :: IO Flags
getFlags = undefined

type Clause = ()
type Problem = ()

readProblemWithRoots :: [FilePath] -> FilePath -> IO Problem
readProblemWithRoots = undefined

clausify :: Flags -> Problem -> ([Clause], [[Clause]])
clausify = undefined


main :: ([Clause] -> IO Answer) -> IO ()
main solveProblem =
  do hSetBuffering stdout LineBuffering
     flags <- getFlags
     case time flags of
       Just n ->
         do timeoutVar <- newEmptyMVar

            pid1 <- forkIO $
              do try (main' flags solveProblem)
                 putMVar timeoutVar False

            pid2 <- forkIO $
              do threadDelay (1000000 * n)
                 putMVar timeoutVar True

            timeout <- takeMVar timeoutVar
            if timeout
              then do killThread pid1
                      putInfo ""
                      putWarning ("TIMEOUT (" ++ show n ++ " seconds)")
                      putResult Unknown "" 
              else do killThread pid2

       Nothing ->
         do main' flags solveProblem

main' :: Flags -> ([Clause] -> IO Answer) -> IO ()
main' flags solveProblem =
  do require (not (null (files flags))) $
       putWarning "No input files specified! Try --help."

     sequence_
       [ do putHeader file
            ins <- readProblemWithRoots ("" : map (++"/") (roots flags)) file
            let (theory,obligs) = clausify flags ins
                n               = length obligs
                file' | length (files flags) > 1 = file
                      | otherwise        = ""
            
            case obligs of
              -- Satisfiable/Unsatisfiable
              [] ->
                do putOfficial "PROBLEM: Satisfiable/Unsatisfiable"
                   ans <- solveProblem theory
                   putResult ans file'
              
              -- CounterSatisfiable/Theorem
              [oblig] ->
                do putOfficial "PROBLEM: CounterSatisfiable/Theorem"
                   ans <- solveProblem (theory ++ oblig)
                   putResult (nega ans) file'
              
              -- Unknown/Theorem
              obligs ->
                do putOfficial "PROBLEM: Unknown/Theorem"
                   
                   let solveAll i [] =
                         do return Theorem
                       
                       solveAll i (oblig:obligs) =
                         do putSubHeader ("Part " ++ show i ++ "/" ++ show n)
                            ans <- solveProblem (theory ++ oblig)
                            putOfficial ("PARTIAL: " ++ show ans)
                            case ans of
                              Unsatisfiable -> solveAll (i+1) obligs
                              _             -> return Unknown
                   
                   ans <- solveAll 1 obligs
                   putResult ans file'
       | file <- files flags
       ]
        
require :: Bool -> IO () -> IO ()
require False m = do m; exitWith (ExitFailure 1)
require True  m = do return ()

---------------------------------------------------------------------------
-- the end.




