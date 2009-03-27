module Main where

{-
Paradox/Equinox -- Copyright (c) 2003-2007, Koen Claessen, Niklas Sorensson

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

main :: Tool -> ((?flags :: Flags) => [Clause] -> IO ClauseAnswer) -> IO ()
main tool solveProblem =
  do hSetBuffering stdout LineBuffering
     theFlags <- getFlags tool
     let ?flags = theFlags

     problems <- (case filelist ?flags of
       Nothing      -> return []
       Just flist   -> do
        s <- readFile flist
        return $ lines s)

     let ?flags = ?flags{ files = files ?flags ++ problems }

     case time ?flags of
       Just n ->
         do timeoutVar <- newEmptyMVar

            pid1 <- forkIO $
              do try (main' solveProblem) :: IO (Either IOError ())
                 putMVar timeoutVar False

            pid2 <- forkIO $
              do threadDelay (1000000 * n)
                 putMVar timeoutVar True

            timeout <- takeMVar timeoutVar
            if timeout
              then do killThread pid1
                      putInfo ""
                      putWarning ("TIMEOUT (" ++ show n ++ " seconds)")
                      let ?flags = ?flags{ thisFile = unwords (files ?flags) }
                      putResult (show Timeout)
              else do killThread pid2

       Nothing ->
         do main' solveProblem

main' :: (?flags :: Flags) => ((?flags :: Flags) => [Clause] -> IO ClauseAnswer) -> IO ()
main' solveProblem =
  do require (not (null (files ?flags))) $
       putWarning "No input files specified! Try --help."

     sequence_
       [ do putOfficial ("PROBLEM: " ++ file)
            ins <- readProblemWithRoots ("" : map (++"/") (roots ?flags)) file
            --putStrLn "--> inputs"
            --print (length ins, ins == ins)
            --sequence_ [ print inp | inp <- ins ]
            let (theory,obligs) = clausify ins
                n               = length obligs
            let ?flags          = ?flags{ thisFile = file }
            
            putOfficial ("SOLVING: " ++ file)
            case obligs of
              -- Satisfiable/Unsatisfiable
              [] ->
                do ans <- solveProblem theory
                   putResult (show ans)
              
              -- CounterSatisfiable/Theorem
              [oblig] ->
                do ans <- solveProblem (theory ++ oblig)
                   putResult (show (toConjectureAnswer ans))
              
              -- Unknown/Theorem
              obligs ->
                do let solveAll i [] =
                         do return Theorem
                       
                       solveAll i (oblig:obligs) =
                         do putSubHeader ("Part " ++ show i ++ "/" ++ show n)
                            ans <- solveProblem (theory ++ oblig)
                            putOfficial ("PARTIAL (" ++ show i ++ "/" ++ show n ++ "): " ++ show (toConjectureAnswer ans))
                            case ans of
                              Unsatisfiable -> solveAll (i+1) obligs
                              _             -> return (NoAnswerConjecture GaveUp)
                   
                   ans <- solveAll 1 obligs
                   putResult (show ans)
       | file <- files ?flags
       ]
        
require :: Bool -> IO () -> IO ()
require False m = do m; exitWith (ExitFailure 1)
require True  m = do return ()

---------------------------------------------------------------------------
-- the end.




