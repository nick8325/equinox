module Main where

import SmellySox.BNFC
import SmellySox.CNF
import SmellySox.Cheese
import SmellySox.Fluff
import SmellySox.Test
import SmellySox.Write
import System
import System.IO
import Control.Monad

main = do
  args <- getArgs
  if (null args) then smellysox test else
    forM_ args $ \arg -> do
      tree <- readFile arg >>= preprocess . parseString arg
      smellysox (convert tree)

smellysox formula = do
    r <- check (clausify formula)
    if r then putStrLn (prettyPrint formula) else do
      formula' <- annotate formula
      check (clausify formula')
      putStrLn (prettyPrint formula')

check formula = do
    hPutStrLn stderr (show formula)
    hPutStrLn stderr ""
    res <- forM (types formula) $ \ty -> do
      r <- isMonotone formula ty
      case r of
        Nothing -> do
               hPutStrLn stderr $ "Not monotone in " ++ show ty
               return False
        Just val -> do
               hPutStrLn stderr $ "Yay, monotone in " ++ show ty ++ "!"
               forM_ val $ \(p, method) -> hPutStrLn stderr $ "  " ++ show p ++ ": " ++ show method
               return True
    return (and res)
