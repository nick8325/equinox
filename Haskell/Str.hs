module Str
  ( Str -- :: *; Show, Eq, Ord
  , str -- :: String -> Str
  )
 where

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
-- str spec
{-
newtype Str = Str String
  deriving ( Eq, Ord )

str = Str

instance Show Str where
  show (Str s) = s
-}
---------------------------------------------------------------------------
-- str spec that maintains same order
-- {-
data Str = Str String [Int]

str :: String -> Str
str s = Str s c
 where
  is = map ord s
  c  = [ hash p is | p <- bigprimes ]

instance Show Str where
  show (Str s _) = s

instance Eq Str where
  Str s1 _ == Str s2 _ = s1 == s2

instance Ord Str where
  Str s1 c1 `compare` Str s2 c2
    | s1 == s2  = EQ
    | otherwise = c1 `compare` c2
-- -}
---------------------------------------------------------------------------
-- str
{-
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
-}
---------------------------------------------------------------------------
-- hash stuff

hash :: Int -> [Int] -> Int
hash p []     = 0
hash p (i:is) = i + p * hash p is

primes, bigprimes :: [Int]
primes = 2 : [ n | n <- [3..], all (n !/) (takeWhile (<= sqr n) primes) ]
 where
  a !/ b = a `mod` b /= 0
  sqr    = floor . sqrt . fromIntegral

bigprimes = dropWhile (<= 258) primes

---------------------------------------------------------------------------
-- the end.
