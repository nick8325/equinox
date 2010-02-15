module Infinox.Zoom (zoom,shrink) where

import IO
import Form
import Infinox.Util (finiteModel)
import Infinox.Conjecture (form2axioms)

-------------------------------------------------------------------------------

zoom :: FilePath -> [Form] -> String -> Int -> IO [Form]
zoom dir fs noClash plimit   = do
		
	zoom' dir fs  (shrink fs) noClash plimit 0 

zoom' :: FilePath -> [Form] -> [[Form]] -> String -> Int -> Int -> IO [Form]
zoom' dir best [] _ _ _  = return best
zoom' dir best fs noClash plim n  = do  

   (f,count) <- smallestUnsat dir best fs noClash plim n 
   
   if f == best || count >= 500 then do return best else 
      zoom' dir f (shrink f) noClash plim count 

smallestUnsat _ best [] _ _ count  = return (best,count)
smallestUnsat dir best (f:fs) noClash plim n  = do
 
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




