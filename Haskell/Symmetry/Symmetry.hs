module Symmetry where

import Data.List( sort, nub )
import Test.QuickCheck
import qualified Test.QuickCheck.Function as F

type Perm = [Int]

permutations :: Int -> [Perm]
permutations 1 = [[1]]
permutations k = [ take (i-1) p ++ [k] ++ drop (i-1) p | p <- permutations (k-1), i <- [1..k] ]

inverse :: Perm -> Perm
inverse p = [ index i p | (i,_) <- [1..] `zip` p ]
 where
  index i (j:p) | i == j    = 1
                | otherwise = 1 + index i p

apply :: Perm -> Int -> Int
apply p i | i <= 0 || i >= length p+1 = error (show p ++ " @ " ++ show 0)
apply p i = p !! (i-1)

newtype Small = Small Int deriving ( Show )

instance Arbitrary Small where
  arbitrary        = Small `fmap` choose (1,7)
  shrink (Small x) = [ Small x' | x' <- shrink x, x' > 0 ]

prop_Inverse (Small k) =
  forAll (elements (permutations k)) $ \p ->
    inverse (inverse p) == p

prop_Symmetry (Small k) =
  func k >>= \f ->
    whenFail (print [ f x | x <- [1..k] ]) $
    or
    [ sorted (map (apply p . f . apply (inverse p)) [1..k])
    | p <- permutations k
    ]

prop_SymmetryRel (Small k) (F.Fun _ rel) =
  or
  [ sorted (map vec [1..k])
  | p <- permutations k
  , let vec x = [ x/=1]
             ++ [ rel (apply p x,apply p i) | i <- [1..k] ]
             ++ [ rel (apply p i,apply p x) | i <- [1..k] ] :: [Bool]
  ]

bad (1,1) = True
bad (1,2) = False
bad (2,1) = False
bad (2,2) = True


func :: Int -> Gen (Int -> Int)
func k =
  do ys <- vectorOf k (choose (1,k))
     return (apply ys)

sorted :: Ord a => [a] -> Bool
sorted xs = sort xs == xs


