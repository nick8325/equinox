module Infinox.Util where

import System
import IO
import System.Directory
import Infinox.Timeout
import Infinox.Conjecture
-------------------------------------------------------------------------------

maybePrint :: (Show a) => Bool -> String -> Maybe a -> IO ()
maybePrint vb t m = if not vb then putStr "" else
	case m of
		Nothing -> putStr ""
		Just m' -> putStrLn $ t ++ (show m')

mappy f xs = do
	(res,_) <- mapUntilSuccess f xs
	return res

mapUntilSuccess _ [] = return ([],[])
--mapping that stops when the result != [],
--and returns the pair of the result and the remaining list.
mapUntilSuccess f (x:xs)  = do
   y <- f x
   case y of
      [] -> mapUntilSuccess f xs
      _  -> return (y,xs)

proveProperty dir fs timeout vb method (t,r,p)  = do
	maybePrint vb "t: " t
	maybePrint vb "r: " r
	maybePrint vb "p: " p
	let 
		conj =  form2conjecture fs 0 (method t r p) 
		provefile = dir ++ "proveProperty"
	b <- prove conj fs provefile timeout
--	removeFile provefile
	if b then return [(t,r,p)] 
		else return [] 

prove conj fs provefile timeout = do   
   h' <- try $ openFile provefile WriteMode			
   case h' of 
      Left e -> do 
         return False	
      Right h -> do
         let 
            s = form2axioms fs 
         hPutStr h (s ++ conj)		
         hClose h		
         eprove provefile timeout

-------------------------------------------------------------------------------

--Call eprover on the input file
eprove :: FilePath  -> Int -> IO Bool
eprove f n  = do
   let 
      limits = "--cpu-limit=" ++ (show n) ++ " " 
      resultfile = f ++ "_result"
   system $ "eprover --tstp-in --tstp-out -tAuto -xAuto --output-level=0 " 
      ++ limits ++ f ++ " > " ++ resultfile	
   h <- openFile resultfile ReadMode	
   r <- hGetContents h				
   let 
      ls = lines r 	
      result = ls !! 1 == "# Proof found!" && 
         ls !! 2 == "# SZS status Theorem" 
   if (result == result) then do   
      -- to close h properly without losing the result.... 
      hClose h 
      removeFile resultfile
      return result
    else error "this never happens" 


--checks if the problem in the input file has a model 
--that can be found by Paradox in plim seconds.
--(interrupts when paradox hasnt responded in plim+3 secs)
finiteModel :: FilePath -> Int -> IO Bool
finiteModel f plim = do
   result <- timeout ((plim+3)*10^6) (timeOut2 ((plim+2)*10^6) "paradox" 
							(f ++ "presult") [f, "--time",show plim])
   case result of
      Just _	->	do
         c <- readFile $ f  ++ "presult"  
         let r = last (lines c)
        -- putStr $ show result
         system $ "rm " ++ f ++ "presult" 
         return $ r /= "+++ RESULT: Timeout"
      Nothing	-> return False
	
-------------------------------------------------------------------------------



