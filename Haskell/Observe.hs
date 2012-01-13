module Observe where

import System.IO.Unsafe
  ( unsafePerformIO
  )

import Data.IORef
import Data.List

obsRef :: IORef [(String,String)]
obsRef = unsafePerformIO (newIORef [])

observe :: Show a => String -> a -> a
observe s x =
  (sx==sx) `seq` 
    unsafePerformIO $
      do table <- readIORef obsRef
         writeIORef obsRef ((s,sx):table)
         return x
 where
  sx = show x

observing :: IO a -> IO a
observing io =
  do writeIORef obsRef []
     x <- io
     table <- readIORef obsRef
     putStrLn ""
     putStrLn "*** observations ***"
     sequence_
       [ do putStrLn ("+++ " ++ s)
            putStr $ unlines $
              [ x ++ ": " ++ show n
              | (n,x) <- reverse
                       . sort
                       . map (\(xs@(x:_)) -> (length xs, x))
                       . group
                       . sort
                       $ xs
              ]
       | (s,xs) <- map (\(sxs@((s,_):_)) -> (s,map snd sxs))
                 . groupBy (\(s1,_) (s2,_) -> s1==s2)
                 . sort
                 $ table
       ]
     return x

