module Name
  ( Name       -- :: *; Show, Eq, Ord, Hash
  , (%)        -- :: Name -> Int -> Name
  , name, prim -- :: String -> Name
  --, strip      -- :: Name -> Name
  
  -- names
  , eq, ap, sk, sp, tr
  )
 where

import Str

---------------------------------------------------------------------------
-- name

data Name
  = Name !Str
  | Prim !Str
  | !Name :% Int
 deriving ( Eq, Ord )

instance Show Name where
  show (Name a)  = show a
  show (Prim a)  = "$" ++ show a
  show (nm :% i) = show nm ++ "!" ++ show i

-- functions

name :: String -> Name
name s = Name (str s)

prim :: String -> Name
prim s = Prim (str s)

(%) :: Name -> Int -> Name
n % i = n :% i

strip :: Name -> Name
strip (n :% _) = strip n
strip n        = n

-- internal names

eq = prim "="
ap = prim "@"
sk = prim "sk"
sp = prim "sp"
tr = prim "truth"

---------------------------------------------------------------------------
-- the end.

