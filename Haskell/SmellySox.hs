module Main where

import SmellySox.BNFC
import SmellySox.CNF
import SmellySox.Cheese
import SmellySox.Fluff
import SmellySox.Test
import System
import Control.Monad

main = do
  args <- getArgs
  if (null args) then smellysox test else
    forM_ args $ \arg -> do
      tree <- readFile arg >>= preprocess . parseString arg
      smellysox (convert tree)

smellysox formula = do
    r <- check (clausify formula)
    when (not r) $ do
      formula' <- annotate formula
      check (clausify formula')
      return ()

check formula = do
    print formula
    putStrLn ""
    res <- forM (types formula) $ \ty -> do
      r <- isMonotone formula ty
      case r of
        Nothing -> do
               putStrLn $ "Not monotone in " ++ show ty
               return False
        Just val -> do
               putStrLn $ "Yay, monotone in " ++ show ty ++ "!"
               forM_ val $ \(p, method) -> putStrLn $ "  " ++ show p ++ ": " ++ show method
               return True
    return (and res)
