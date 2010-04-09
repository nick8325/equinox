module Equinox.PSequence where

{-
Equinox -- Copyright (c) 2003-2007, Koen Claessen

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

import Data.List
import Data.Maybe
import qualified Data.Map as M
import System.IO
import Control.Concurrent
{-
import Control.Parallel
import Control.Parallel.Strategies
import System.IO.Unsafe
-}

psequence :: Int -> [(Int,(Char -> IO ()) -> IO a)] -> IO [a]
psequence 1 ios =
  do sequence [ do putStr " "
                   fio (\c -> do putStr ['\b',c]; hFlush stdout)
              | (_,fio) <- ios
              ]

psequence n ios =
  do chan <- newChan
     let actions = [ (w, do x <- fio (\k -> writeChan chan (n,Left k))
                            writeChan chan (n, Right x))
                   | (n,(w,fio)) <- [(0 :: Int)..] `zip` ios
                   ]
     st <- newStealQueue n (map snd ({- sortBy cmp -} actions))
     sequence_ [ forkOS (serve i st) | (i,_) <- [0..n-1] `zip` ios ]
     results 0 ios M.empty chan
 where
  (w1,_) `cmp` (w2,_) = w2 `compare` w1
 
  serve i st =
    do mio <- takeFromStealQueue i st
       case mio of
         Nothing -> do return ()
         Just io -> do io
                       serve i st

  

  results k [] _ _ =
    do return []

  results k ios futs chan =
    do putStr " "
       wait k ' ' ios futs chan
  
  wait k c ios futs chan =
    do if c /= c' then
         do putStr ['\b',c']
            hFlush stdout
        else
         do return ()

       case mr of
         Just x ->
           do xs <- results (k+1) (tail ios) futs chan
              return (x:xs)
         
         Nothing ->
           do (n,p) <- readChan chan
              let f (Left c)  Nothing       = Just (c,Nothing)
                  f (Right x) Nothing       = Just (' ', Just x)
                  f (Left c)  (Just (_,mr)) = if isJust mr then error "que?" else Just (c, mr)
                  f (Right x) (Just (c,_))  = Just (c, Just x)
              wait k c' ios (M.alter (f p) n futs) chan
   where
    (c',mr) = case M.lookup k futs of
               Just (c,mr) -> (c,mr)
               Nothing     -> (' ',Nothing)

-- steal queues

newtype StealQueue a = SQ [MVar [a]]

newStealQueue :: Int -> [a] -> IO (StealQueue a)
newStealQueue n xs =
  do mvars <- sequence [ newMVar ys | ys <- divide n xs ]
     return (SQ mvars)
 where
  divide n [] = replicate n []
  divide n xs = xs `add` divide n (drop n xs)

  _      `add` []       = []
  []     `add` yss      = yss
  (x:xs) `add` (ys:yss) = (x:ys) : (xs `add` yss)

takeFromStealQueue :: Int -> StealQueue a -> IO (Maybe a)
takeFromStealQueue k (SQ mvars) = tryTakeMVars (shift k mvars)
 where
  shift k xs = drop k xs ++ take k xs

  tryTakeMVars (mvar:mvars) =
    do xs <- takeMVar mvar
       case xs of
         x:xs' -> do putMVar mvar xs'
                     return (Just x)
         []    -> do putMVar mvar []
                     xs <- steal mvars
                     case xs of
                       x:xs' -> do ys <- takeMVar mvar
                                   putMVar mvar (ys++xs')
                                   return (Just x)
                       []    -> do return Nothing

  steal [] =
    do return []
  
  steal (mvar:mvars) =
    do --putStr ("<p" ++ show k ++ " steals ")
       xs <- takeMVar mvar
       --let ys = xs
       ys <- case xs of
               [] -> do putMVar mvar []
                        ys <- steal mvars
                        xs <- takeMVar mvar
                        return (xs++ys)
               _  -> do return xs
       let k   = length ys `div` 2
           ys1 = take k ys
           ys2 = drop k ys
       putMVar mvar ys1
       --putStr (show (length ys2) ++ ">")
       return ys2

