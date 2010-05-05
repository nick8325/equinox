module Equinox.TopSort
  ( Graph
  , nodes
  , follow
  , topsort
  )
 where

import Data.Map(Map)
import Data.Map as M
import Data.Set(Set)
import Data.Set as S
import Data.List
import Test.QuickCheck

type Graph a = Map a [a]

nodes :: Ord a => Graph a -> Set a
nodes g = S.fromList [ y | (x,xs) <- M.toList g, y <- x:xs ]

follow :: Ord a => Graph a -> a -> [a]
follow g x = case M.lookup x g of
               Nothing -> []
               Just xs -> xs  

topsort :: Ord a => Graph a -> (Set a, [a])
topsort g = (cyc, deps)
 where
  (cyc, deps, _) = process S.empty S.empty (S.toList (nodes g))
 
  process seen busy [] =
    (S.empty, [], seen)
  
  process seen busy (x:xs) | x `S.member` seen =
    process seen busy xs

  process seen busy (x:xs) | x `S.member` busy =
    (S.insert x cycxs, depsxs, seenxs)
   where
    (cycxs, depsxs, seenxs)  = process (S.insert x seen) busy xs

  process seen busy (x:xs) =
    (cycx `S.union` cycxs, depsx ++ [x | not (x `S.member` cycx)] ++ depsxs, seenxs)
   where
    (cycx,  depsx,  seenx)  = process seen (S.insert x busy) (follow g x)
    (cycxs, depsxs, seenxs) = process (S.insert x seenx) busy xs

prop_Topsort_sorts g' =
  let g           = M.fromList (g' :: [(Int,[Int])])
      (cyc, deps) = topsort g in
    check g cyc deps

check :: Ord a => Graph a -> Set a -> [a] -> Bool
check g seen []     = True
check g seen (x:xs) = (x `S.member` seen || all (`S.member` seen) (follow g x))
                   && check g (S.insert x seen) xs

prop_Topsort_complete g' =
  let g           = M.fromList (g' :: [(Int,[Int])])
      (cyc, deps) = topsort g in
    all (\x -> x `S.member` cyc || x `elem` deps) (S.toList (nodes g))

prop_Topsort_noDoubles g' =
  let g           = M.fromList (g' :: [(Int,[Int])])
      (cyc, deps) = topsort g
      xs          = S.toList cyc ++ deps in
    xs == nub xs

