module Infinox.Classify where

import qualified Flags as F
import Flags( Flags, Method(InjNotSurj,SurjNotInj,Serial))
import IO
import System (system)
import System.Time 
import System.Directory (removeFile,createDirectoryIfMissing) 
import Control.Concurrent (threadDelay)

import Form
import Infinox.Conjecture
import Output
import Infinox.Generate
import Infinox.Serial
import Infinox.Zoom 
import Infinox.InjOnto

-----------------------------------------------------------------------------------------

classifyProblem :: (?flags :: Flags) => [Clause] -> IO ClauseAnswer
classifyProblem cs = do
	createDirectoryIfMissing False (F.temp ?flags)
	let
		tempdir 					= (F.temp ?flags) ++ "/" ++ (subdir ((F.thisFile ?flags))) 
		verbose						=  F.verbose ?flags > 0	
		mflag							=  F.method ?flags	
		eflag							=  F.elimit ?flags
	createDirectoryIfMissing False tempdir
	starttime   <- getClockTime

	let 
		forms 		= map toForm cs
		noClash 	= noClashString forms
	fs  <- if (F.zoom ?flags) then zoom tempdir forms noClash (F.plimit ?flags)
						else return forms --the formulas in which to search for candidates
	let
		sig 		= getSignature fs
		axioms 	= form2axioms forms noClash
		
	result <-	
		(if mflag == Serial then 				
				continueSerial tempdir sig axioms noClash (F.relation ?flags) verbose eflag
			else if mflag == InjNotSurj || mflag == SurjNotInj then
					let
						pflag = F.subset ?flags
						funs	=	collectTestTerms sig (F.function ?flags) fs (F.termdepth ?flags)
						(method,rflag)		=		if mflag == InjNotSurj then (conjInjNotOnto,F.relation ?flags) 
																		else (conjNotInjOnto,Nothing) in
					continueInjOnto tempdir sig axioms noClash funs method rflag pflag verbose eflag
				else	
					undefined --Add new methods here!		 			
		)
	finish starttime result tempdir (F.thisFile ?flags) (F.outfile ?flags)

-----------------------------------------------------------------------------------------

finish time1 result dir file out = do
   time2 <- getClockTime
   let
      time = tdSec $ diffClockTimes time2 time1
   threadDelay 1000000
   system $ "rm -r " ++  dir
   maybeAppendFile out ( file ++ ": " ++ show result ++ ", Time: " ++ show time ++ "\n" )
   case result of
    None				->	return $ NoAnswerClause GaveUp
    _						->	return FinitelyUnsatisfiable	
   where
      maybeAppendFile Nothing _     =  return ()
      maybeAppendFile (Just fun) x  =  appendFile fun x

subdir inputfile = (filter ( (not . (flip elem) ['/','.','-',' '])) inputfile) ++ "_TEMP/"


