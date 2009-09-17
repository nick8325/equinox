module SatPlay.Main where

import Sat

main :: IO ()
main = run $
  do a   <- newVar 5
     b   <- newVar 5
     ab  <- times a b
     require $ equal ab (number 27)
     requireNot $ equal a (number 1)
     requireNot $ equal b (number 1)

     ans <- solve []
     if not ans
       then lift (putStrLn "no model!")
       else do n <- getModelNumber a
               m <- getModelNumber b
               lift (print (n,m))

require :: S Bit -> S ()
require constr =
  do b <- constr
     [] ==> [b]

requireNot :: S Bit -> S ()
requireNot constr =
  do b <- constr
     [] ==> [ng b]

data Bit    = Lit Lit | Bool Bool deriving Eq
type Number = [Bit] -- lsb first (omvänt)   (011 = 2+4 = 6)

b0, b1 :: Bit
b0 = Bool False
b1 = Bool True

ng :: Bit -> Bit
ng (Lit x)  = Lit (neg x)
ng (Bool b) = Bool (not b)

newBit :: S Bit
newBit = (Lit . neg) `fmap` newLit

number :: Int -> Number
number 0 = []
number n = Bool (odd n) : number (n `div` 2)

getModelNumber :: Number -> S Int
getModelNumber []     = return 0
getModelNumber (x:xs) =
  do n <- getModelNumber xs
     b <- getModelValue' x
     return ((if b then 1 else 0) + 2*n)
 where
  getModelValue' (Bool b) = return b
  getModelValue' (Lit x)  = getModelValue x

newVar :: Int -> S Number
newVar k = sequence [ newBit | i <- [1..k] ]

plus :: Bit -> Number -> Number -> S Number
plus c []     []     = return [c] 
plus c []     ys     = plus c [b0] ys
plus c xs     []     = plus c xs [b0]
plus c (x:xs) (y:ys) =
  do z  <- sumBit c x y
     c' <- carryBit c x y
     zs <- plus c' xs ys
     return (z:zs)

(==>) :: [Bit] -> [Bit] -> S ()
xs ==> ys = clause (map ng xs ++ ys)
 where
  clause ls
    | Bool True `elem` ls = return ()
    | otherwise           = addClause [ x | Lit x <- ls ] >> return ()

sumBit :: Bit -> Bit -> Bit -> S Bit
sumBit a b c =
  do s <- newBit
     [ng a, ng b, ng c] ==> [ng s]
     [   a,    b, ng c] ==> [ng s]
     [   a, ng b,    c] ==> [ng s]
     [ng a,    b,    c] ==> [ng s]
     [   a, ng b, ng c] ==> [s]
     [ng a,    b, ng c] ==> [s]
     [ng a, ng b,    c] ==> [s]
     [   a,    b,    c] ==> [s]
     return s

carryBit :: Bit -> Bit -> Bit -> S Bit
carryBit a b c =
  do d <- newBit
     [ng a, ng b, ng c] ==> [ng d]
     [   a, ng b, ng c] ==> [ng d]
     [ng a,    b, ng c] ==> [ng d]
     [ng a, ng b,    c] ==> [ng d]
     [   a,    b, ng c] ==> [d]
     [   a, ng b,    c] ==> [d]
     [ng a,    b,    c] ==> [d]
     [   a,    b,    c] ==> [d]
     return d

timesBit :: Bit -> Number -> S Number
timesBit (Bool b) xs = return [ Bool b | _ <- xs ]
timesBit a        xs =
  sequence [ do y <- newBit
                [a,x]  ==> [y]
                [ng a] ==> [ng y]
                [ng x] ==> [ng y]
                return y
           | x <- xs
           ]

times :: Number -> Number -> S Number
times []     ys = return []
times (x:xs) ys =
  do p:ps <- timesBit x ys
     qs   <- times xs ys
     rs   <- plus b0 ps qs
     return (p:rs)

equal :: Number -> Number -> S Bit
equal []     []     = return b1
equal []     ys     = allZero ys 
equal xs     []     = allZero xs
equal (x:xs) (y:ys) =
  do e  <- newBit
     eq <- equal xs ys
     [ng eq]          ==> [ng e]
     [ng x, y]        ==> [ng e]
     [x, ng y]        ==> [ng e]
     [x, y, eq]       ==> [e]
     [ng x, ng y, eq] ==> [e]
     return e

allZero :: Number -> S Bit
allZero [] = return b1
allZero xs =
  do z <- newBit
     map ng xs ==> [z]
     sequence_ [ [x] ==> [ng z] | x <- xs ]
     return z

