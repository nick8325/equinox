module Name
  ( Name   -- :: *; Show, Eq, Ord, Hash
  , (%)    -- :: Name -> Int -> Name
  , name, prim   -- :: String -> Name
  , eq, ap -- :: Name
  , strip  -- :: Name -> Name
  )
 where

import Data.Map as M
import Data.IORef
import System.IO.Unsafe

-- names

data Name
  = MkName !Int String
  | Name :% Int

strip :: Name -> Name
strip (n :% _) = strip n
strip n        = n

prim :: String -> Name
prim s = name ("$" ++ s)

(%) :: Name -> Int -> Name
n % i = n :% i

eq :: Name
eq = name "="

ap :: Name
ap = name "@"

instance Show Name where
  show (MkName n s) = s -- ++ "{" ++ show n ++ "}"
  show (nm :% i)    = show nm ++ "'" ++ show i
 
instance Eq Name where
  nm1 == nm2 = (nm1 `compare` nm2) == EQ

instance Ord Name where
  MkName n1 _ `compare` MkName n2 _ = n1 `compare` n2
  (nm1 :% i1) `compare` (nm2 :% i2) = (i1,nm1) `compare` (i2,nm2)
  MkName _ _  `compare` (_ :% _)    = LT
  (_ :% _)    `compare` MkName _ _  = GT

-- name

{-# NOINLINE name #-}
name :: String -> Name
name =
  unsafePerformIO $
    do cnt <- newIORef 0
       tab <- newIORef empty
       return $ \s ->
         unsafePerformIO $
           do t <- readIORef tab
              case M.lookup s t of
                Just nm ->
                  do return nm
                
                Nothing ->
                  do n <- readIORef cnt
                     let n' = n+1
                         nm = MkName n s
                     n' `seq` writeIORef cnt n'
                     writeIORef tab (M.insert s nm t)
                     return nm
