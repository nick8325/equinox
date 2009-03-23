module Infinox.Main where

import Sat
import qualified Main
import Form
import Flags
import Infinox.Classify

---------------------------------------------------------------------------
-- main

main :: IO ()
main =
  do putStrLn "Infinox, version 1.0, 2009-03-17."
     Main.main Infinox classifyProblem

---------------------------------------------------------------------------
-- the end.
