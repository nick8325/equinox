module Main where

import Form
import Control.Concurrent
import Control.Exception
import System
import Flags
import ParseProblem
import Clausify
import IO( hSetBuffering, stdout, BufferMode(..) )

import Output

---------------------------------------------------------------------------
-- main

main :: ((?flags :: Flags) => [Clause] -> IO Answer) -> IO ()
main solveProblem =
  do hSetBuffering stdout LineBuffering
     theFlags <- getFlags
     let ?flags = theFlags
     case time ?flags of
       Just n ->
         do timeoutVar <- newEmptyMVar

            pid1 <- forkIO $
              do try (main' solveProblem)
                 putMVar timeoutVar False

            pid2 <- forkIO $
              do threadDelay (1000000 * n)
                 putMVar timeoutVar True

            timeout <- takeMVar timeoutVar
            if timeout
              then do killThread pid1
                      putInfo ""
                      putWarning ("TIMEOUT (" ++ show n ++ " seconds)")
              else do killThread pid2

       Nothing ->
         do main' solveProblem

main' :: (?flags :: Flags) => ([Clause] -> IO Answer) -> IO ()
main' solveProblem =
  do require (not (null (files ?flags))) $
       putWarning "No input files specified! Try --help."

     sequence_
       [ do putOfficial ("PROBLEM: " ++ file)
            ins <- readProblemWithRoots ("" : map (++"/") (roots ?flags)) file
            --sequence_ [ print inp | inp <- ins ]
            let (theory,obligs) = clausify ins
                n               = length obligs
                file' | length (files ?flags) > 1 = file
                      | otherwise                 = ""
            
            case obligs of
              -- Satisfiable/Unsatisfiable
              [] ->
                do ans <- solveProblem theory
                   putResult ans file'
              
              -- CounterSatisfiable/Theorem
              [oblig] ->
                do ans <- solveProblem (theory ++ oblig)
                   putResult (nega ans) file'
              
              -- Unknown/Theorem
              obligs ->
                do let solveAll i [] =
                         do return Theorem
                       
                       solveAll i (oblig:obligs) =
                         do putSubHeader ("Part " ++ show i ++ "/" ++ show n)
                            ans <- solveProblem (theory ++ oblig)
                            putOfficial ("PARTIAL (" ++ show i ++ "/" ++ show n ++ "): " ++ show ans)
                            case ans of
                              Unsatisfiable -> solveAll (i+1) obligs
                              _             -> return Unknown
                   
                   ans <- solveAll 1 obligs
                   putResult ans file'
       | file <- files ?flags
       ]
        
require :: Bool -> IO () -> IO ()
require False m = do m; exitWith (ExitFailure 1)
require True  m = do return ()

---------------------------------------------------------------------------
-- the end.




