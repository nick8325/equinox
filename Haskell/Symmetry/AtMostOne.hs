module AtMostOne where

import Data.List

type Cost = (String,Integer,Integer)

cost :: Integer -> Cost
cost n = costs !! fromIntegral n

costs :: [Cost]
costs = [ cost' i | i <- [0..] ]

cost' :: Integer -> Cost
cost' n = best $ [ costNaive n, costBinary n ] ++ [ costMatrix n k | k <- [2,3] ]
 where
  best = minimumBy cmp

  (_, c1, v1) `cmp` (_, c2, v2) = compare (c1 + v1) (c2 + v2)

costNaive :: Integer -> Cost
costNaive n = ("N", n * (n-1), 0)

costBinary :: Integer -> Cost
costBinary n = ("B", n * log2 n, log2 n)

costMatrix :: Integer -> Integer -> Cost
costMatrix n k
  | nk >= n   = costNaive n
  | otherwise = ("M" ++ show k ++ s, k*n + k*c, k*nk + k*v)
 where
  nk      = n `nthroot` k
  (s,c,v) = cost nk

costMatrix2 :: Integer -> Cost
costMatrix2 n
  | n <= 8 = costBinary n
  | otherwise = ("M2" ++ s, 2*n + 2*c, 2*n2 + 2*v)
 where
  n2      = discr sqrt n
  (s,c,v) = costMatrix2 n2

log2 :: Integer -> Integer
log2 k | k <= 1 = 0
log2 k          = 1 + log2 (discr (/2) k)

nthroot :: Integer -> Integer -> Integer
n `nthroot` k = suchThat 0 n (\a -> a^k >= n)
 where
  suchThat a b p
    | a+1 >= b  = b
    | p c       = suchThat a c p
    | otherwise = suchThat c b p
   where
    c = (a+b) `div` 2

discr :: (Double -> Double) -> Integer -> Integer
discr f n = ceiling (f (fromIntegral n))

main :: IO ()
main =
  sequence_ $ take 400
    [ putStrLn (show n ++ ": " ++ show c ++ " (" ++ show v ++ ") " ++ s)
    | (n,(s,c,v)) <- [0..] `zip` costs
    ]

