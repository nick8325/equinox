module Sat
  ( S             -- :: * -> *; Functor, Monad
  , Lit           -- :: *; Eq, Ord, Show
  , Arg(..)       -- :: *
  , Atm(..)       -- :: *
  
  , run           -- :: S a -> IO a
  , okay          -- :: S Bool
  , lift          -- :: IO a -> S a
  , contradiction -- :: S ()
  , newLit        -- :: S Lit
  , neg           -- :: Lit -> Lit
  , getValue      -- :: Lit -> S (Maybe Bool)
  , getModelValue -- :: Lit -> S Bool -- use only after model has been found!
  , addClause     -- :: [Lit] -> S Bool
  , solve         -- :: [Lit] -> S Bool
  , simplify      -- :: Bool -> Bool -> S Bool

  , newLoc        -- :: Int -> S Loc
  , getLit        -- :: Signed Atm -> S Lit
  , addClauses    -- :: [Int] -> [Signed Atm] -> S ()
  )
 where

import Foreign.C.Types       ( CInt )
import Foreign.C.String      ( CString, withCString )
import Foreign.Ptr           ( Ptr, FunPtr, nullPtr )
import Foreign.ForeignPtr    ( ForeignPtr, newForeignPtr, withForeignPtr )
import Foreign.Storable      ( peek )
import Foreign.Marshal.Array ( withArray0, peekArray0 )
import Foreign.Marshal.Alloc ( malloc, free )
import System.IO             ( FilePath )
import Foreign.Storable      ( Storable )
import Control.Exception     ( finally )


import Form                  ( Signed(..), the, sign )


newLoc :: Int -> S Loc
newLoc p = lift $ do
  ptr  <- loc_new (fromIntegral p)
  fptr <- newForeignPtr loc_free ptr
  return (Loc fptr)

addClauses :: [Int] -> [Signed Atm] -> S ()
addClauses d ls = MiniSatM (\s -> addClauses_ d ls s)

addClauses_ d ls s = 
  do solver_clause_begin s
     mapM_ (signed addLit) ls
     mapM_ (solver_clause_add_size s . fromIntegral) d
     solver_clause_commit s 0

 where addArg (ArgN i) = solver_clause_add_lit_con s (fromIntegral i)
       addArg (ArgV i) = solver_clause_add_lit_var s (fromIntegral i)
       addLit (Loc l :@ args) b = do
         withForeignPtr l (flip (solver_clause_add_lit s) (toCBool b))
	 mapM_ addArg args

       signed f x = f (the x) (sign x)
    

getLit :: Signed Atm -> S Lit
getLit atom = MiniSatM $ \s -> do
    withForeignPtr l (flip (solver_lit_begin s) (toCBool (sign atom)))
    mapM_ (solver_lit_add_con s) [ fromIntegral d | ArgN d <- args ]
    solver_lit_read s

  where (Loc l :@ args) = the atom

----------------------------------------------------------------------------------
-- Monad

newtype Solver = Solver (Ptr ())
newtype S a    = MiniSatM (Solver -> IO a)

instance Monad S where
  return x =
    MiniSatM (const (return x))

  MiniSatM f >>= g =
    MiniSatM (\s -> f s >>= \x -> case g x of { MiniSatM m -> m s })

instance Functor S where
  fmap f (MiniSatM g) = MiniSatM (fmap f . g)

----------------------------------------------------------------------------------------------------
-- types

newtype Lit
  = Lit CInt
 deriving (Eq, Num, Ord, Storable)

newtype Loc = Loc (ForeignPtr ())
 deriving ( Eq, Show )

data Arg
  = ArgV Int
  | ArgN Int
 deriving ( Eq, Show )

data Atm
  = Loc :@ [Arg]
 deriving ( Eq, Show )

neg :: Lit -> Lit
neg x = -x

instance Show Lit where
  showsPrec i (Lit l) = showsPrec i l

instance Read Lit where
  readsPrec i = map (\ (x,r) -> (Lit x, r)) . readsPrec i

mkTrue  = Lit 1
mkFalse = -mkTrue

----------------------------------------------------------------------------------------------------
-- MiniSatM functions

lower :: S a -> Solver -> IO a
lower (MiniSatM f) = f

withSolverLog :: FilePath -> (Solver -> IO a) -> IO a
withSolverLog log f = withCString log (flip withSolverPrim f)

withSolver :: (Solver -> IO a) -> IO a
withSolver = withSolverPrim nullPtr

withSolverPrim :: CString -> (Solver -> IO a) -> IO a
withSolverPrim log f =
    do s <- s_new log
       r <- f s `finally` s_delete s
       return r

run :: S a -> IO a
run m = withSolver (lower m)

{-
    mkLit       :: m Lit
    clause      :: [Lit] -> m Bool

    solve       :: [Lit] -> m Bool
    solve_      :: Bool  -> [Lit] -> m Bool
    modelValue  :: Lit   -> m Bool
    value       :: Lit   -> m (Maybe Bool)
    contr       :: m [Lit]
    okay        :: m Bool

    -- for convenience
    lift        :: IO a -> m a

    -- default *with* simplification
    solve = solve_ True

    freezeLit   :: Lit   -> m ()
    unfreezeLit :: Lit   -> m ()
    simplify    :: Bool -> Bool -> m Bool

    freezeLit   l = return ()
    unfreezeLit l = return ()
    simplify  x y = return True
    
    -- formula creation (with simple defaults)
    mkAnd       :: Lit -> Lit -> m Lit
    mkAnd       = defAnd

    mkOr        :: Lit -> Lit -> m Lit
    mkOr x y    = mkAnd (-x) (-y) >>= return . negate

    mkEqu       :: Lit -> Lit -> m Lit
    mkEqu       = defEqu

    mkXor       :: Lit -> Lit -> m Lit
    mkXor x y   = mkEqu (-x) (-y) >>= return . negate

    mkIte       :: Lit -> Lit -> Lit -> m Lit
    mkIte       = defIte

    mkAdd       :: Lit -> Lit -> Lit -> m (Lit, Lit)
    mkAdd       = defAdd
-}

solve = solve_ True

newLit         = MiniSatM s_newlit
addClause ls     = fmap fromCBool $ MiniSatM (withArray0 (Lit 0) ls . s_clause)
solve_ b ls   = fmap fromCBool $ MiniSatM (withArray0 (Lit 0) ls . flip s_solve (toCBool b))

freezeLit l   = MiniSatM (\s -> s_freezelit s l)
unfreezeLit l = MiniSatM (\s -> s_unfreezelit s l)
getModelValue l  = fmap fromCBool $ MiniSatM (flip s_modelvalue l)
getValue      l  = fmap fromLBool $ MiniSatM (flip s_value l)
reason   = MiniSatM (\s -> s_contr s >>= peekArray0 (Lit 0))
contradiction = addClause [] >> return ()
okay          = fmap fromCBool $ MiniSatM s_okay
simplify elim  turnoffelim = fmap fromCBool $ MiniSatM (\s -> s_simplify s (toCBool elim) (toCBool turnoffelim))

lift       f  = MiniSatM (const f)

mkAnd x y = MiniSatM (\s -> s_and s x y)
mkOr  x y = MiniSatM (\s -> s_or  s x y)
mkEqu x y = MiniSatM (\s -> s_equ s x y)
mkXor x y = MiniSatM (\s -> s_xor s x y)
mkIte x y z = MiniSatM (\s -> s_ite s x y z)
mkAdd x y z = MiniSatM $ \s -> 
    do cp <- malloc
       sp <- malloc
       s_add s x y z cp sp
       c  <- peek cp
       s  <- peek sp
       free cp
       free sp
       return (c,s)

verbose n = MiniSatM (\s -> s_verbose s (fromIntegral n))

nVars, nClauses, nConflicts, nRemembered :: S Int
nVars       = fmap fromIntegral $ MiniSatM s_nvars
nClauses    = fmap fromIntegral $ MiniSatM s_nclauses
nConflicts  = fmap fromIntegral $ MiniSatM s_nconflicts
nRemembered = fmap fromIntegral $ MiniSatM s_nremembered

----------------------------------------------------------------------------------------------------
-- helpers

fromCBool :: CInt -> Bool
fromCBool 0 = False
fromCBool _ = True

-- should import the correct constants really
fromLBool :: CInt -> Maybe Bool
fromLBool 0    = Nothing
fromLBool 1    = Just True
fromLBool (-1) = Just False

toCBool :: Bool -> CInt
toCBool True  = 1
toCBool False = 0

----------------------------------------------------------------------------------------------------
-- foreign imports

foreign import ccall unsafe "static Wrapper.h"   s_new            :: CString -> IO Solver
foreign import ccall unsafe "static Wrapper.h"   s_delete         :: Solver -> IO () 
foreign import ccall unsafe "static Wrapper.h"   s_newlit         :: Solver -> IO Lit
foreign import ccall unsafe "static Wrapper.h"   s_clause         :: Solver -> Ptr Lit -> IO CInt
foreign import ccall unsafe "static Wrapper.h"   s_solve          :: Solver -> CInt -> Ptr Lit -> IO CInt
foreign import ccall unsafe "static Wrapper.h"   s_simplify       :: Solver -> CInt -> CInt -> IO CInt
foreign import ccall unsafe "static Wrapper.h"   s_freezelit      :: Solver -> Lit -> IO ()
foreign import ccall unsafe "static Wrapper.h"   s_unfreezelit    :: Solver -> Lit -> IO ()
foreign import ccall unsafe "static Wrapper.h"   s_setpolarity    :: Solver -> Lit -> IO ()
foreign import ccall unsafe "static Wrapper.h"   s_setdecisionvar :: Solver -> Lit -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   s_value          :: Solver -> Lit -> IO CInt
foreign import ccall unsafe "static Wrapper.h"   s_and            :: Solver -> Lit -> Lit -> IO Lit
foreign import ccall unsafe "static Wrapper.h"   s_or             :: Solver -> Lit -> Lit -> IO Lit
foreign import ccall unsafe "static Wrapper.h"   s_equ            :: Solver -> Lit -> Lit -> IO Lit
foreign import ccall unsafe "static Wrapper.h"   s_xor            :: Solver -> Lit -> Lit -> IO Lit
foreign import ccall unsafe "static Wrapper.h"   s_ite            :: Solver -> Lit -> Lit -> Lit -> IO Lit
foreign import ccall unsafe "static Wrapper.h"   s_add            :: Solver -> Lit -> Lit -> Lit -> Ptr Lit -> Ptr Lit -> IO ()
foreign import ccall unsafe "static Wrapper.h"   s_modelvalue     :: Solver -> Lit -> IO CInt
foreign import ccall unsafe "static Wrapper.h"   s_contr          :: Solver -> IO (Ptr Lit)
foreign import ccall unsafe "static Wrapper.h"   s_verbose        :: Solver -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   s_okay           :: Solver -> IO CInt
foreign import ccall unsafe "static Wrapper.h"   s_nvars          :: Solver -> IO CInt
foreign import ccall unsafe "static Wrapper.h"   s_nclauses       :: Solver -> IO CInt
foreign import ccall unsafe "static Wrapper.h"   s_nconflicts     :: Solver -> IO CInt
foreign import ccall unsafe "static Wrapper.h"   s_nremembered    :: Solver -> IO CInt

foreign import ccall unsafe "static Wrapper.h"   loc_new          :: CInt -> IO (Ptr ())
foreign import ccall unsafe "static Wrapper.h &loc_free"   loc_free         :: FunPtr ((Ptr ()) -> IO ())
foreign import ccall unsafe "static Wrapper.h"   loc_arity        :: (Ptr ()) -> IO CInt

foreign import ccall unsafe "static Wrapper.h"   solver_clause_begin       :: Solver -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_add_lit     :: Solver -> (Ptr ()) -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_add_lit_var :: Solver -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_add_lit_con :: Solver -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_add_size    :: Solver -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_clause_commit      :: Solver -> CInt -> IO ()

foreign import ccall unsafe "static Wrapper.h"   solver_lit_begin :: Solver -> (Ptr ()) -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_lit_add_con :: Solver -> CInt -> IO ()
foreign import ccall unsafe "static Wrapper.h"   solver_lit_read :: Solver -> IO Lit
