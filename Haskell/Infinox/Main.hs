module Infinox.Main where

import Runner
import Flags
import Infinox.Classify
---------------------------------------------------------------------------
-- main

main :: IO ()
main =
  do putStrLn "Infinox, version 1.0, 2009-07-20."
     runner Infinox classifyProblem

---------------------------------------------------------------------------
-- the end.
