module Name
  ( Name       -- :: *; Show, Eq, Ord, Hash
  , (%)        -- :: Name -> Int -> Name
  , name, prim -- :: String -> Name
  , strip      -- :: Name -> Name
  
  -- names
  , vr, sk, dp, sp, tr, dm, un, df, el, eq
  , isSimpleName
  , isSkolemnName
  , isEltName
  , getIndex
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

vr = prim "X"
eq = prim "eq"
sk = prim "sk"
dp = prim "dp"
sp = prim "sp"
tr = prim "truth"
dm = prim "dm"
un = prim "un"
df = prim "df"
el = name ""

isName :: (Name -> Bool) -> Name -> Bool
isName p n | p n  = True
isName p (n :% _) = isName p n
isName p _        = False

isSimpleName (Name _) = True
isSimpleName _        = False

isSkolemnName = isName (== sk)
isEltName     = isName (== el)

getIndex :: Name -> Int
getIndex (_ :% i) = i
getIndex _        = 0

---------------------------------------------------------------------------
-- the end.

