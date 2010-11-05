module Infinox.Util where

import System (system)
import IO
import System.Directory
import Infinox.Timeout
import Infinox.Conjecture
import Infinox.Settings
import Data.List (isInfixOf)
import Form
import Flags(Method,Prover(..))

import Control.Monad.Reader

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

leqfive	x =   x <= 5

proveProperty method (t,r,p) = do
--	liftIO $ putStrLn $ "proveProperty "  ++ show (t,r,p)
	settings <- ask --dir axioms noClash timeout vb method (t,r,p)  = do
	let 
		noClash'	=		noClash settings
		conj 			=  	form2conjecture noClash' 0 (method t r p) 
		provefile = 	tempdir settings ++ "proveProperty"
		vb				=		verbose settings
		axioms		=		axiomfile settings
		to				=		elimit settings
		pr		    =   prover settings    
	liftIO $  do
								maybePrint vb "\nt: " t
								maybePrint vb "r: " r
								maybePrint vb "p: " p
								system ("cp " ++ axioms ++ " " ++ provefile)
								b <- prove pr conj provefile to
								--	removeFile provefile
								if b then return [(t,r,p)] 
									else return [] 

prove prover conj provefile timeout = do   
   h' <- try $ openFile provefile AppendMode			
   case h' of 
      Left e -> do 
         putStrLn "Error: unable to open provefile"					
         return False	
      Right h -> do
         hSetBuffering h NoBuffering
         hPutStr h conj	
         hClose h		
         if prover == E then eprove provefile timeout else equinox provefile timeout  
        


leoprove conj provefile = do
	h' <- try $ openFile provefile AppendMode
	case h' of 
		Left e -> do 
			putStrLn "Error: unable to open provefile"					
			return False	
		Right h -> do
			hSetBuffering h NoBuffering
			hPutStr h conj	
			hClose h		
			leo provefile

-------------------------------------------------------------------------------

equinoxprove :: String -> FilePath -> IO Bool
equinoxprove conjecture file = do
	h' <- try $ openFile file AppendMode
	case h' of 
		Left e -> do 
			putStrLn "Error: unable to open provefile"					
			return False	
		Right h -> do
			hSetBuffering h NoBuffering
			hPutStr h conjecture	
			hClose h		
			equinox file (10*10^6)

equinox :: FilePath -> Int ->  IO Bool
equinox file to = 
	do

		let resultfile = file ++ "_result"
--		putStrLn $ "trying equinox... " ++ resultfile
		result <- (timeOut2 (to*10^6) "equinox" 
							resultfile [file, "--time",show to])
		case result of
			Just _	->	do	
					c <- readFile resultfile
					let r = last (lines c)
					
		--			system $ "rm " ++ resultfile
			        	
					return $  "+++ RESULT: Theorem" `isInfixOf` r
			Nothing	-> return False

{-
		system $ "equinox --time 300 " ++ file ++ " > " ++ resultfile
		h <- openFile resultfile ReadMode
		r <- hGetContents h
		let 
			ls = lines r
			ans = any ((isInfixOf) "+++ RESULT: Unsatisfiable") ls
		mapM putStrLn ls
		if (ans == ans) then do
			hClose h		
			removeFile resultfile
			return ans
		 else error "this never happens"
-}

leo :: FilePath -> IO Bool
leo file = 
	do

		let resultfile = file ++ "_result"
		system $ "leo -t 60 " ++ file ++ " > " ++ resultfile
		h <- openFile resultfile ReadMode
		r <- hGetContents h
		let 
			ls = lines r
			ans = any ((isInfixOf) "% SZS status Theorem") ls
		mapM putStrLn ls
		if (ans == ans) then do
			hClose h		
			removeFile resultfile
			return ans
		 else error "this never happens"


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
      result = elem "# Proof found!" ls && elem "# SZS status Theorem" ls 
   if (result == result) then do   
      -- to close h properly without losing the result.... 
      hClose h 
      removeFile resultfile
      return result
    else error "this never happens" 


--checks if the problem in the input file has a model 
--that can be found by Paradox in plim seconds.
--(interrupts when paradox hasnt responded in plim+2 secs)
finiteModel :: FilePath -> Int -> IO Bool
finiteModel f plim = do
   result <- (timeOut2 ((plim+2)*10^6) "paradox" 
							(f ++ "presult") [f, "--time",show plim])
   case result of
      Just _	->	do	
         c <- readFile $ f  ++ "presult"  
         let r = last (lines c)
         system $ "rm " ++ f ++ "presult" 	 
         return $ r /= "+++ RESULT: Timeout"
      Nothing	-> return False

-------------------------------------------------------------------------------



