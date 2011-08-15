{-# LANGUAGE BangPatterns #-}
module Main where

import SmellySox.Parser.Abstff
import SmellySox.BNFC
import SmellySox.CNF
import SmellySox.Cheese
import qualified SmellySox.FluffFun
import qualified SmellySox.FluffPred
import SmellySox.Test
import SmellySox.Write
import System
import System.IO
import Control.Monad
import Data.List
import SmellySox.Formula hiding (getArgs, types, (:=:))
import qualified SmellySox.Formula as F

main = do
  args <- getArgs
  let (options, files) = partition ("--" `isPrefixOf`) args
  when ("--help" `elem` options || (null files && "--demo" `notElem` options)) $ do
    progName <- getProgName
    putStrLn "Monopoly: a typed FOL to untyped FOL translator"
    putStrLn $ "Usage: " ++ progName ++ " [options] [tff files]"
    putStrLn "Untyped TPTP problem is written to stdout"
    putStrLn "Options:"
    putStrLn "  --help: show this help message"
    putStrLn "  --demo: use built-in category theory example"
    putStrLn "  --pred: use typing predicates to enforce types (default is typing functions)"
    putStrLn "  --arith: include arithmetic axioms"

  let pred = "--pred" `elem` options
      arith = "--arith" `elem` options
      demo = "--demo" `elem` options
      fluff = if pred then SmellySox.FluffPred.annotate else SmellySox.FluffFun.annotate

  when demo $ smellysox fluff test
  forM_ files $ \file -> do
    let addArithmetic (Tffs xs) | arith = Tffs (TffIncl (FPath "Haskell/SmellySox/arith.ax"):xs)
                                | otherwise = Tffs xs
    tree <- readFile file >>= preprocess . addArithmetic . parseString file
    putStrLn file
    smellysox fluff (convert tree)

smellysox fluff formula = do
    r <- check (clausify formula)
    if r then putStrLn (prettyPrint formula) else do
      formula' <- fluff formula
      check (clausify formula')
      putStrLn (prettyPrint formula')

check formula = do
--    hPutStrLn stderr (show formula)
--    hPutStrLn stderr ""
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
