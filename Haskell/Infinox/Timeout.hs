{-# OPTIONS -fglasgow-exts #-}
-------------------------------------------------------------------------------
-- |
-- Module      :  System.Timeout
-- Copyright   :  (c) The University of Glasgow 2007
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Attach a timeout event to arbitrary 'IO' computations.
--
-------------------------------------------------------------------------------

module Infinox.Timeout  where

-- #if __NHC__
-- timeout :: Int -> IO a -> IO (Maybe a)
-- timeout n f = fmap Just f
-- #else

import Prelude             --(IO, Ord((<)), Eq((==)), Int, (.), otherwise, fmap)
import Data.Maybe          --(Maybe(..))
import Control.Monad       (Monad(..), guard)
import Control.OldException   hiding (catch) --(handleJust, throwDynTo, dynExceptions, bracket)
import Data.Dynamic        (Typeable, fromDynamic)
import Data.Unique         (Unique, newUnique)

import Control.Concurrent
import Control.Concurrent.MVar
import System.Process
import System.Posix hiding (killProcess)
import System.IO.Error hiding (try,catch)
import System
import System.IO

-- An internal type that is thrown as a dynamic exception to
-- interrupt the running IO computation when the timeout has
-- expired.

data Timeout = Timeout Unique deriving (Eq, Typeable)

-- |Wrap an 'IO' computation to time out and return @Nothing@ in case no result
-- is available within @n@ microseconds (@1\/10^6@ seconds). In case a result
-- is available before the timeout expires, @Just a@ is returned. A negative
-- timeout interval means \"wait indefinitely\". When specifying long timeouts,
-- be careful not to exceed @maxBound :: Int@.
--
-- The design of this combinator was guided by the objective that @timeout n f@
-- should behave exactly the same as @f@ as long as @f@ doesn't time out. This
-- means that @f@ has the same 'myThreadId' it would have without the timeout
-- wrapper. Any exceptions @f@ might throw cancel the timeout and propagate
-- further up. It also possible for @f@ to receive exceptions thrown to it by
-- another thread.
--
-- A tricky implementation detail is the question of how to abort an @IO@
-- computation. This combinator relies on asynchronous exceptions internally.
-- The technique works very well for computations executing inside of the
-- Haskell runtime system, but it doesn't work at all for non-Haskell code.
-- Foreign function calls, for example, cannot be timed out with this
-- combinator simply because an arbitrary C function cannot receive
-- asynchronous exceptions. When @timeout@ is used to wrap an FFI call that
-- blocks, no timeout event can be delivered until the FFI call returns, which
-- pretty much negates the purpose of the combinator. In practice, however,
-- this limitation is less severe than it may sound. Standard I\/O functions
-- like 'System.IO.hGetBuf', 'System.IO.hPutBuf', Network.Socket.accept, or
-- 'System.IO.hWaitForInput' appear to be blocking, but they really don't
-- because the runtime system uses scheduling mechanisms like @select(2)@ to
-- perform asynchronous I\/O, so it is possible to interrupt standard socket
-- I\/O or file I\/O using this combinator.

timeout :: Int -> IO a -> IO (Maybe a)
timeout n f
    | n <  0    = fmap Just f
    | n == 0    = return Nothing
    | otherwise = do
        pid <- myThreadId
        ex  <- fmap Timeout newUnique
        handleJust (\e -> dynExceptions e >>= fromDynamic >>= guard . (ex ==))
                   (\_ -> return Nothing)
                   (bracket (forkIO (threadDelay n >> throwDynTo pid ex))
                            (killThread)
                            (\_ -> fmap Just f))
-- #endif


test = do
	timeOut2 (2*(10^6)) "eprover" "utdata" (words "--tstp-in --tstp-out -tAuto -xAuto --output-level=0 /home/ann/Documents/Infinox/TPTP-v3.5.0/Problems/ALG/ALG221+1.p") 

timeOut2 :: Int  -> String -> String -> [String] -> IO (Maybe ExitCode)
timeOut2 n exe output args =
   do
      h2 <- openFile output WriteMode
      h  <- runProcess exe args Nothing Nothing Nothing (Just h2) Nothing
      res <- newEmptyMVar

      forkIO (do 
         ex <- waitForProcess h 
         putMVar res (Just ex)
			)

      id <- forkIO (do 
         threadDelay n
         --terminateProcess h
         let 
            kill 0 = do 
               putStrLn "Paradox still running..."
               return ()
            kill m = do
               ex <- try (terminateProcess h)
               case ex of
                  Left _ -> do 
                              threadDelay (n `div` 10) 
                              kill (m-1)
                  Right _ -> return () 
         kill 100
         putMVar res Nothing
			)
      
      x <- takeMVar res
      hClose h2
      killThread id
      return x 
		

