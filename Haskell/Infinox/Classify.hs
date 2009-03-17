module Infinox.Classify where

import qualified Flags as F
import Flags( Flags ) 
import IO
import List (nub,delete)
import System (system)
import System.Time 
import System.Directory (removeFile,createDirectoryIfMissing) 
import Control.Concurrent (threadDelay)
import Data.Set as S( Set )
import qualified Data.Set as S
import Data.Maybe ( fromJust )

import Form
import Infinox.Util
import Infinox.Conjecture
import Infinox.Generate
import Infinox.Zoom 
import Infinox.InjOnto
import Infinox.Serial

-----------------------------------------------------------------------------------------

classifyProblem :: (?flags :: Flags) => [Clause] -> IO ClauseAnswer
classifyProblem cs = do
	createDirectoryIfMissing False (F.temp ?flags)

	let
		tempdir = (F.temp ?flags) ++ "/" ++ (subdir (fromJust (F.mfile ?flags))) 
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
                        Nothing -> 
        
        
        case (relflag inputs) of
										(_, Just rel)  					-> getRs $ getSymb rel preds
            			--try only the refl. rel. given as flag to main.
										(useReflRels,Nothing) 	-> 
											nub $ sortForms $ getRs $ 
											(if (useReflRels || (mflag inputs == SR)) 
												then preds 
													else if elem ("=" ::: PredArity 2) preds then 
														[("=" ::: PredArity 2)] else [])
             -- if useReflRels - all "reflexive predicates" (predicates w at least 2 "X"),
             --(reflexivity yet to be checked at this point), o.w. just "="

		((usePs,limpred),(och,eller,inte)) = pflag inputs
	
		ps  = case limpred of 
				Nothing  -> 
					Nothing : (map Just $ sortForms  $ nub $ deleteEqs $ getPs preds och eller inte)

          --No -p=(..) flag given - test all limiting predicates (starting with Nothing)
				Just p'   -> case getSymb p' preds of 
               --test the given limiting predicate only
												[p]   -> map Just $ getPs [p] och eller inte
												[]    -> []
	
		--look for a relation that is serial, transitive and irreflexive
	if (mflag inputs == SR) then do 
		let 
			rs' = delete equality (nub (concatMap genRs rs)) 
		result <- continueSR tempdir forms (rs'++(map nt rs')) (vflag inputs) (elimit inputs)  
		finish starttime result tempdir       

	 else do --look for inj and ~surj or ~inj and surj function
		if terms == [] then finish starttime [] tempdir						
		 else do        
				let 
					method = case (mflag inputs) of
																					Ino -> checkProperty conjInjNotOnto 
																					Oni -> checkProperty conjNotInjOnto
					rels = map Just $ rs ++ map nt rs
				
				result <- continuePartOne tempdir forms (elimit inputs) 
											(map Just terms) (rels,rels) [] ps method (vflag inputs)
				finish starttime result tempdir		

			
subdir inputfile = (filter ( (not . (flip elem) ['/','.','-',' '])) inputfile) ++ "_TEMP/"

finish time1 result dir = do
   time2 <- getClockTime
   let
      time = tdSec $ diffClockTimes time2 time1
   threadDelay 5000000
   system $ "rm -r " ++  dir
   return (result,time)

-------------------------------------------------------------------------------

deleteEqs [] = []
deleteEqs ((Atom (Pred ("=" ::: PredArity 2) _)):xs) = deleteEqs xs
deleteEqs (x:xs) = x:(deleteEqs xs)

-------------------------------------------------------------------------------

--combining predicates with conjunction and negation...
pairall :: [Form] -> [Form]
pairall fs = nub [f1 /\ f2 | f1 <- fs, f2 <- fs, f1 /= f2]

negall fs = [Not f | f <- fs]

--Search for a symbol with  given name in a list of terms.

getSymb s xs = filter (((==) s).symbolname) xs

symbolname (r ::: _) = r

getFun :: String -> Set Term -> Set Term
getFun fun set = S.filter (((==) fun).funname) set
	where
		funname (Fun symb _) = symbolname symb


