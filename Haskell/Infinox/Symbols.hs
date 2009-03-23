module Infinox.Symbols where

import Name
import Form

x, y, z :: Symbol
x = name "X" ::: V top
y = name "Y" ::: V top
z = name "Z" ::: V top

star :: Symbol
star = prim "*" ::: V top
