module Infinox.Classify where

import qualified Flags as F
import Flags( Flags, Method(InjNotSurj,SurjNotInj,Serial,Relation,Auto, Leo))
import IO
import System (system)
import System.Time 
import System.Directory (removeFile,createDirectoryIfMissing) 
import Control.Concurrent (threadDelay)
import Data.List

import Form
import Infinox.Conjecture
import Output
import Infinox.Generate
import Infinox.Relations
import Infinox.Zoom
import Infinox.InjOnto
import Infinox.Util	
import Infinox.Auto (continueAuto)
import Infinox.Leo (classifyWithLeo)

-----------------------------------------------------------------------------------------

classifyProblem :: (?flags :: Flags) => [Clause] -> IO ClauseAnswer
classifyProblem cs = do

	createDirectoryIfMissing False (F.temp ?flags)

	let
		tempdir 					= (F.temp ?flags) ++ "/" ++ (subdir ((F.thisFile ?flags))) 
		verbose						=  F.verbose ?flags > 0	
		methods						=  F.method ?flags	
		eflag						=  F.elimit ?flags
		pflag 						=  F.subset ?flags
		forms 						= map toForm cs
		noClash 					= noClashString forms
		axiomfile					= tempdir ++ "axiomfile"
		termdepth					= F.termdepth ?flags
		funflag						= F.function ?flags
		relflag						= F.relation ?flags
	--	leoflag						= F.leo ?flags
	
	createDirectoryIfMissing False tempdir


	
	starttime   	<- getClockTime
	fs  		<- if (F.zoom ?flags) then do
											
						putStrLn $ if verbose then "Zooming..." else ""
						zoom tempdir forms noClash (F.plimit ?flags)
			else return forms --the formulas in which to search for candidates																	
			
	let
		sig 		= getSignature fs (F.function ?flags)
		axioms 	= form2axioms forms noClash

	h <- openFile axiomfile WriteMode			
	hSetBuffering h NoBuffering
	hPutStr h axioms	
	hClose h
	result <- classifyWithMethods methods 
		(axiomfile,tempdir, fs, noClash, verbose, sig, funflag, relflag,pflag ,termdepth, eflag)	
	finish starttime result tempdir (F.thisFile ?flags) (F.outfile ?flags)
{-	 
classifyWithLeo axiomfile  = do
	let
		conj = "thf(c4,conjecture, ?[G:$i>$i] : ( (![X:$i] : (![Y:$i] : (~((G @ X) = (G @ Y)) | (X = Y)))) & (?[Y:$i] : ![X:$i] : ~((G@X) = Y))))."
	h' <- try $ openFile axiomfile AppendMode			
	case h' of 
		Left e -> do 
			return None
		Right h -> do
			hSetBuffering h NoBuffering
			hPutStr h conj	
			hClose h		
			b <- leoprove conj axiomfile
			if b then return Some
				else return None 
-}	
		

classifyWithMethods [] _ = return None
classifyWithMethods (m:ms) args  = do
	result <- classifyWithMethod m args
	case result of 
		None -> classifyWithMethods ms args
		_		 -> return result


--classifyWithMethod Leo (axiomfile,_,_,_,_,_,_,_,_,_,_) = classifyWithLeo axiomfile

classifyWithMethod m (axiomfile,tempdir, fs, noClash, verbose, sig, funflag, relflag, pflag, depthflag, eflag)  = 
	if m == Serial || m == Relation then do
				let		
					funs	=	filter (leqfour . funArity) $ sortTerms $ nub $ getFunsFromSymbols (fsymbs sig) funflag 1
					rels	= concatMap makeRelations funs
				continueRelations m tempdir sig rels axiomfile noClash (F.relation ?flags) pflag verbose eflag
		else if m == InjNotSurj || m == SurjNotInj then 		
					let
						funs	=	collectTestTerms sig funflag fs depthflag
						(method,rflag)		=		if m == InjNotSurj then (conjInjNotOnto,F.relation ?flags) 
																		else (conjNotInjOnto,Nothing) in do
					
						continueInjOnto tempdir axiomfile sig noClash funs method rflag pflag verbose eflag
		 
			else if m == Auto then
				continueAuto tempdir noClash fs sig (F.relation ?flags) pflag verbose
			 else if m == Leo then do		
				classifyWithLeo axiomfile
			 	else undefined -- add new methods here!!
	

-----------------------------------------------------------------------------------------

finish time1 result dir file out = do
   time2 <- getClockTime
   let
      time = tdSec $ diffClockTimes time2 time1
   threadDelay 1000000
 --  system $ "rm -r " ++  dir
   maybeAppendFile out ( file ++ " : " ++ show result ++ " : " ++ show time ++ "\n" )
   case result of
    None				->	return $ NoAnswerClause GaveUp
    _					->	return FinitelyUnsatisfiable	
   where
      maybeAppendFile Nothing _     =  return ()
      maybeAppendFile (Just f) x    =  appendFile f x

subdir inputfile = (filter ( (not . (flip elem) ['/','.','-',' '])) inputfile) ++ "_TEMP/"


