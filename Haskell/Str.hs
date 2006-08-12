module Str
  ( Str -- :: *; Show, Eq, Ord
  , str -- :: String -> Str
  )
 where

import qualified Data.Map as M
import Data.Char
import Data.IORef
import System.IO.Unsafe

-- This module provides an abstract datatype for atoms, such that:
--   * Each atom string is only in memory once
--   * O(n) creation time
--   * O(1) equality-comparison
--   * O(1) (in practice) ord-comparison
--   * ord-comparison results are independent on evaluation order

---------------------------------------------------------------------------
-- str

data Str
  = MkAtom !Int [Int] String

instance Show Str where
  show (MkAtom _ _ s) = s
 
instance Eq Str where
  MkAtom i1 _ _ == MkAtom i2 _ _ = i1 == i2

instance Ord Str where
  MkAtom i1 c1 _ `compare` MkAtom i2 c2 _
    | i1 == i2  = EQ
    | otherwise = c1 `compare` c2

-- mkAtom

mkAtom :: Int -> String -> Str
mkAtom n s = MkAtom n c s
 where
  is = map ord s
  c  = [ hash p is | p <- bigprimes ]

  hash p []     = 0
  hash p (i:is) = i + p * hash p is

primes, bigprimes :: [Int]
primes = 2 : [ n | n <- [3..], all (n !/) (takeWhile (<= sqr n) primes) ]
 where
  a !/ b = a `mod` b /= 0
  sqr    = floor . sqrt . fromIntegral

bigprimes = dropWhile (<= 258) primes

-- str

{-# NOINLINE str #-}
str :: String -> Str
str =
  unsafePerformIO $
    do cnt <- newIORef 0
       tab <- newIORef M.empty
       return $ \s ->
         unsafePerformIO $
           do t <- readIORef tab
              case M.lookup s t of
                Just at ->
                  do return at
                
                Nothing ->
                  do n <- readIORef cnt
                     let n' = n+1
                         at = mkAtom n s
                     n' `seq` writeIORef cnt n'
                     writeIORef tab (M.insert s at t)
                     return at

---------------------------------------------------------------------------
-- the end.
