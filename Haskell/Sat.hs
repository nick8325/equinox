module Sat
  ( S             -- :: * -> *; Functor, Monad
  , M.Lit         -- :: *; Eq, Ord, Show
  , Arg(..)       -- :: *
  , Atm(..)       -- :: *

  , run           -- :: S a -> IO a
  , lift          -- :: IO a -> S a
  , contradiction -- :: S ()
  , newLit        -- :: S Lit
  , M.neg         -- :: Lit -> Lit
  , getValue      -- :: Lit -> S (Maybe Bool)
  , getModelValue -- :: Lit -> S Bool -- use only after model has been found!
  , conflict      -- :: S [Lit]       -- use only after solve has failed to find a model!
  , addClause     -- :: [Lit] -> S Bool
  , solve         -- :: [Lit] -> S Bool
  , simplify      -- :: S Bool
  , okay          -- :: S Bool

  , newLoc        -- :: Int -> S Loc
  , getLit        -- :: Signed Atm -> S Lit
  , addClauses    -- :: [Int] -> [Signed Atm] -> S ()

  , mkTrue
  , mkFalse

  -- for debugging
  --, printStderr   -- :: String -> IO ()
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

import qualified MiniSat as M
import Foreign.C.Types       ( CInt(..) )
import Foreign.C.String      ( CString, withCString )
import Foreign.Ptr           ( Ptr, FunPtr, nullPtr )
import Foreign.ForeignPtr    ( ForeignPtr, newForeignPtr, newForeignPtr_, withForeignPtr )
import Foreign.Storable      ( peek )
import Foreign.Marshal.Array ( withArray0, peekArray0 )
import Foreign.Marshal.Alloc ( malloc, free )
import System.IO             ( FilePath )
import Foreign.Storable      ( Storable )
import Control.Exception     ( finally )
import System.Random
import Control.Applicative
import Control.Monad
import Data.Maybe


import Form                  ( Signed(..), the, sign )

newLoc :: Int -> S Loc
newLoc p = lift $ do
  ptr  <- loc_new (fromIntegral p)
  fptr <- newForeignPtr loc_free ptr
  return (Loc fptr)

addClauses :: Maybe Int -> [Int] -> [Signed Atm] -> S ()
addClauses mn d ls = MiniSatM (\(_, s) -> addClauses_ mn d ls s)

addClauses_ mn d ls s =
  do solver_clause_begin s
     mapM_ (signed addLit) ls
     mapM_ (solver_clause_add_size s . fromIntegral) d
     solver_clause_commit s (fromIntegral (maybe 0 (subtract 1) mn))

 where addArg (ArgN i) = solver_clause_add_lit_con s (fromIntegral i)
       addArg (ArgV i) = solver_clause_add_lit_var s (fromIntegral i)
       addLit (Loc l :@ args) b = do
         withForeignPtr l (flip (solver_clause_add_lit s) (toCBool b))
         mapM_ addArg args

       signed f x = f (the x) (sign x)


getLit :: Signed Atm -> S M.Lit
getLit atom = MiniSatM $ \(_, s) -> do
    withForeignPtr l (flip (solver_lit_begin s) (toCBool (sign atom)))
    mapM_ (solver_lit_add_con s) [ fromIntegral d | ArgN d <- args ]
    solver_lit_read s

  where (Loc l :@ args) = the atom

toCBool :: Bool -> CInt
toCBool True  = 1
toCBool False = 0

----------------------------------------------------------------------------------
-- Monad

newtype S a    = MiniSatM ((M.Solver, Inst) -> IO a)

instance Applicative S where
  pure = return
  (<*>) = liftM2 ($)

instance Monad S where
  return x =
    MiniSatM (const (return x))

  MiniSatM f >>= g =
    MiniSatM (\s -> f s >>= \x -> case g x of { MiniSatM m -> m s })

instance Functor S where
  fmap f (MiniSatM g) = MiniSatM (fmap f . g)

----------------------------------------------------------------------------------------------------
-- types

newtype Loc = Loc (ForeignPtr ())
 deriving ( Eq, Show )

data Arg
  = ArgV Int
  | ArgN Int
 deriving ( Eq, Show )

data Atm
  = Loc :@ [Arg]
 deriving ( Eq, Show )

----------------------------------------------------------------------------------------------------
-- MiniSatM functions

run :: S a -> IO a
run (MiniSatM f) =
  M.withNewSolver $ \s -> do
    inst <- s_new s
    flip finally (s_delete inst) $ do
      -- Needed for defs of mkTrue and mkFalse
      true <- M.newLit s
      if true /= mkTrue then error "Expected first variable to have number 0" else do
        M.addClause s [mkTrue]
        M.simplify s
        f (s, inst)

mkTrue, mkFalse :: M.Lit
mkTrue  = M.MkLit 0
mkFalse = M.neg mkTrue

solve ls = MiniSatM (\(s, _) -> M.solve s ls)
newLit = MiniSatM (\(s, _) -> M.newLit s)

addClause ls = MiniSatM (\(s, _) -> M.addClause s ls)

getModelValue l = MiniSatM (\(s, _) -> fromMaybe (M.minisat_sign l) <$> M.modelValue s l)
conflict = MiniSatM (\(s, _) -> M.conflict s)
getValue l  = MiniSatM (\(s, _) -> M.value s l)
contradiction = addClause [] >> return ()
simplify = MiniSatM (\(s, _) -> M.simplify s)
okay = MiniSatM (\(s, _) -> M.minisat_okay s)

lift       f  = MiniSatM (const f)

----------------------------------------------------------------------------------------------------
-- foreign imports

newtype Inst = Inst (Ptr ())

foreign import ccall unsafe "static Wrapper.h"   s_new            :: M.Solver -> IO Inst
foreign import ccall unsafe "static Wrapper.h"   s_delete         :: Inst -> IO ()
foreign import ccall unsafe "static Wrapper.h"   loc_new          :: CInt -> IO (Ptr ())
foreign import ccall unsafe "static Wrapper.h &loc_free"   loc_free         :: FunPtr ((Ptr ()) -> IO ())
foreign import ccall unsafe "static Wrapper.h"   loc_arity        :: (Ptr ()) -> IO CInt

foreign import ccall unsafe "static Wrapper.h"   solver_clause_begin       :: Inst -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_add_lit     :: Inst -> (Ptr ()) -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_add_lit_var :: Inst -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_add_lit_con :: Inst -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_add_size    :: Inst -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_commit      :: Inst -> CInt -> IO ()

foreign import ccall unsafe "static Wrapper.h"   solver_lit_begin :: Inst -> (Ptr ()) -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_lit_add_con :: Inst -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_lit_read :: Inst -> IO M.Lit
