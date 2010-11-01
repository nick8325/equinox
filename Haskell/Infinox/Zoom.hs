module Infinox.Zoom (zoom,shrink) where

import IO
import Form
import Infinox.Util (finiteModel)
import Infinox.Conjecture (form2axioms)
import Random
import Data.List

-------------------------------------------------------------------------------

zoom :: FilePath -> [Form] -> String -> Int -> IO [Form]
zoom dir fs noClash plimit   = do
	cs <- zoom' dir fs  (shrink fs) noClash plimit 0 
	return $ sort cs 

zoom' :: FilePath -> [Form] -> [[Form]] -> String -> Int -> Int -> IO [Form]
zoom' dir best [] _ _ _  = return best
zoom' dir best fs noClash plim n  = do  
   (f,count) <- smallestUnsat dir best fs noClash plim n 
   if f == best then return f else do
		f' <- permute f
		zoom' dir f (shrink f') noClash plim count 

permute :: Eq a => [a] -> IO [a]
permute as = do 
	g <- getStdGen
	permute' g as

permute' :: Eq a => StdGen -> [a] -> IO [a]
permute' _ [] = return []
permute' g  xs = do
	let 
		(a,g') 		= randomR (0,(length xs) -1) g 
		el				= xs !! a
	xs'			<- permute' g' (delete el xs)
	return (el:xs')

smallestUnsat _ best [] _ _ count  = return (best,count)
smallestUnsat dir best (f:fs) noClash plim n  = do
   if n >= 350 then return (best,n) else do
    h <- openFile (dir ++ "zoom"++(show n)) WriteMode
    hPutStr h $ (form2axioms f noClash)
    hClose h
    b <- finiteModel (dir ++ "zoom"++(show n)) plim
    if b then do
	 smallestUnsat dir best fs noClash plim (n+1)  
      --if finite model - discard f and try the other shrinked lists
     else return (f,n+1) --if no finite model - return f

	
shrink :: [a] -> [[a]]
shrink xs = removeChunks xs
 where
  removeChunks xs = rem (length xs) xs
   where
    rem 0 _  = []
    rem 1 _  = [[]]
    rem n xs = xs1
             : xs2
             : ( [ xs1' ++ xs2 | xs1' <- rem n1 xs1, not (null xs1') ]
           `ilv` [ xs1 ++ xs2' | xs2' <- rem n2 xs2, not (null xs2') ]
               )
     where
      n1  = n `div` 2
      xs1 = take n1 xs
      n2  = n - n1
      xs2 = drop n1 xs
  
      []     `ilv` ys     = ys
      xs     `ilv` []     = xs
      (x:xs) `ilv` (y:ys) = x : y : (xs `ilv` ys)




