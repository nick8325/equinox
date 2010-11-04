module Main where

import SmellySox.BNFC
import SmellySox.CNF
import SmellySox.Cheese
import System
import Control.Monad

main = do
  args <- getArgs
  forM_ args $ \arg -> do
    tree <- readFile arg >>= preprocess . parseString arg
    let formula = clausify (convert tree)
    print formula
    putStrLn ""
    forM_ (types formula) $ \ty -> do
      r <- isMonotone formula ty
      case r of
        Nothing -> putStrLn $ "Not monotone in " ++ show ty
        Just val -> do
               putStrLn $ "Yay, monotone in " ++ show ty ++ "!"
               forM_ val $ \(p, method) -> putStrLn $ "  " ++ show p ++ ": " ++ show method
                 
