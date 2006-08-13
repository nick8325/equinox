module Equinox.Main where

import Sat
import qualified Main
import Form
import Flags

---------------------------------------------------------------------------
-- main

main :: IO ()
main =
  do putStrLn "Equinox, version 1.0-alpha, 2006-08-13."
     Main.main solveProblem
  
---------------------------------------------------------------------------
-- solve

solveProblem :: (?flags :: Flags) => [Clause] -> IO Answer
solveProblem cs =
  do sequence_ [ print c | c <- cs ]
     return Unknown

---------------------------------------------------------------------------
-- the end.
