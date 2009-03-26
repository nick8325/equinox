module Infinox.Classify where

import qualified Flags as F
import Flags( Flags, Method(InjNotSurj,SurjNotInj,Serial))
import IO
import List (nub,delete)
import System (system)
import System.Time 
import System.Directory (removeFile,createDirectoryIfMissing) 
import Control.Concurrent (threadDelay)
import Data.Set as S( Set )
import qualified Data.Set as S
import Data.Maybe ( fromJust )

import Name (name)
import Form
import Infinox.Util
import Infinox.Conjecture
import Infinox.Generate
import Infinox.Serial
import Infinox.Zoom 
import Infinox.InjOnto

-----------------------------------------------------------------------------------------

classifyProblem :: (?flags :: Flags) => [Clause] -> IO ClauseAnswer
classifyProblem cs = do
	createDirectoryIfMissing False (F.temp ?flags)

	let
		tempdir = (F.temp ?flags) ++ "/" ++ (subdir ((F.thisFile ?flags))) 
		verbose	= F.verbose ?flags > 0
			--the name of the temp directory is given as a flag to infinox. 
			--each input file has its own subdirectory.
 --Create temp dir, get start time, parse the problem and collect the 
	 --list of clauses.	
	createDirectoryIfMissing False tempdir
	starttime   <- getClockTime
	let forms = map toForm cs
	fs       		<- if (F.zoom ?flags) then zoom tempdir forms (F.plimit ?flags)
									else return forms --the formulas in which to search for candidates

	let

		funterms'  = getFuns $ S.unions $ map subterms fs --all functional terms
		funterms   = case (F.function ?flags) of 
									"-"     -> funterms' --no -term flag given - use all functional terms
									fun     -> getFun fun funterms' --o.w. use only fun 
		funsymbols = S.toList $ getFunSymbols funterms
		terms      = sortTerms $ nub $ generateFromSymbols funsymbols (F.termdepth ?flags) ++
										(S.toList (generateFromTerms funterms))
									--Use both the terms from the problem (trying out each present variable
									--as argument to the function), and the terms generated from
                  --the symbols!
		preds			= S.toList $ S.unions $ map getPredSymbols fs	
                  --all predicate symbols	
		rs        =  case F.relation ?flags of
										Just rel			->  getRs $ getSymb rel preds
										Nothing 			->  nub $ sortForms $ getRs preds --use all refl rels.
		ps = case (F.subset ?flags) of
			Nothing	-> Nothing : (map Just $ sortForms  $ nub $ deleteEqs $ getPs preds False False False)
			Just p' -> case getSymb p' preds of 
               --test the given limiting predicate only
												[p]   -> map Just $ getPs [p] False False False
												[]    -> []
--	putStrLn $ "TERMS: " ++ (show terms)
--	putStrLn $ "SUBSETS: " ++ (show ps) ++ "\n\n"
--	putStrLn $ "RELATIONS: " ++ (show rs) ++ "\n\n"

	if (F.method ?flags == Serial) then do
		let
			rs' 		= deleteEqs $ nub $ concatMap genRs rs	
		result <- continueSR tempdir forms (rs'++(map nt rs')) verbose (F.elimit ?flags)  
		finish starttime result tempdir  
	 
	 else do --look for inj and ~surj or ~inj and surj function
		if terms == [] || rs == [] then finish starttime [] tempdir						
		 else do        
				let 
					method = case (F.method ?flags) of
																					InjNotSurj -> conjInjNotOnto 
																					SurjNotInj -> conjNotInjOnto
					rels = map Just $ rs ++ map nt rs			
				result <- continuePartOne tempdir forms (F.elimit ?flags) 
											(map Just terms) (rels,rels) [] ps method verbose
				finish starttime result tempdir		

	
subdir inputfile = (filter ( (not . (flip elem) ['/','.','-',' '])) inputfile) ++ "_TEMP/"

finish time1 result dir = do
   time2 <- getClockTime
   let
      time = tdSec $ diffClockTimes time2 time1
   threadDelay 5000000
 --  system $ "rm -r " ++  dir
   case result of
    []				->	return $ NoAnswerClause GaveUp
    _					->	return FinitelyUnsatisfiable
--   return (result,time)

-------------------------------------------------------------------------------

deleteEqs [] = []
deleteEqs (x@(Atom ((Fun symb _) :=: _)):xs) = if show (symbolname symb) == "=" 
	then deleteEqs xs
		else x:(deleteEqs xs)
deleteEqs (x:xs) = x:(deleteEqs xs)

-------------------------------------------------------------------------------

--combining predicates with conjunction and negation...
pairall :: [Form] -> [Form]
pairall fs = nub [f1 /\ f2 | f1 <- fs, f2 <- fs, f1 /= f2]

negall fs = [Not f | f <- fs]

--Search for a symbol with  given name in a list of terms.

getSymb s xs = filter (((==) s).show.symbolname) xs
delSymb s xs = filter (((/=) s).show.symbolname) xs

symbolname (r ::: _) = r

getFun :: String -> Set Term -> Set Term
getFun fun set = S.filter (((==) fun).funname) set
	where
		funname (Fun symb _) = show $ symbolname symb


