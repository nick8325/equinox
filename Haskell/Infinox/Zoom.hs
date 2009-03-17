module Infinox.Zoom (zoom) where

import IO
import Form
import Util (finiteModel)
import Conjecture (form2axioms)

-------------------------------------------------------------------------------

zoom :: FilePath -> [Form] -> Int -> IO [Form]
zoom dir fs plimit   = zoom' dir fs (shrink fs) plimit 0 

zoom' :: FilePath -> [Form] -> [[Form]] -> Int -> Int -> IO [Form]
zoom' dir best [] _ _  = return best
zoom' dir best fs plim n  = do 
   (f,count) <- smallestUnsat dir best fs plim n 
   if f == best then return f else 
      zoom' dir f (shrink f) plim count 

smallestUnsat _ best [] _ count  = return (best,count)
smallestUnsat dir best (f:fs) plim n  = do
   h <- openFile (dir ++ "zoom"++(show n)) WriteMode
   hPutStr h $ (form2axioms f)
   hClose h
   b <- finiteModel (dir ++ "zoom"++(show n)) plim
   if b then smallestUnsat dir best fs plim (n+1)  
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




