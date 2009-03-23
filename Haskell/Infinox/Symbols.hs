module Infinox.Symbols where

import Name
import Form

type Function  = Term -- has one variable X
type Relation  = Form -- has two variables X, Y
type Predicate = Form -- has one variable X

x, y, z :: Symbol
x = name "X" ::: V top
y = name "Y" ::: V top
z = name "Z" ::: V top

a, b, c :: Symbol
a = name "a" ::: ([] :-> top)
b = name "b" ::: ([] :-> top)
c = name "c" ::: ([] :-> top)

star :: Symbol
star = prim "*" ::: V top