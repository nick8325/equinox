module Infinox.Serial where

import Form
import Infinox.Conjecture
import Infinox.Generate
import Infinox.Util
import System.Directory
import qualified Data.Set as S
import qualified Infinox.Symbols as Sym
import Infinox.Types

import Data.List (nub)
import Data.Set as S( Set )
import Output
import qualified Data.Set as S

-------------------------------------------------------------------------------

continueSerial tempdir sig problem  noClash rflag pflag v elim = do
	let
			rflag'		=		case rflag of
											Nothing 	-> Just "-"
											Just "-"	-> Just "-"
											_					-> rflag
			psymbols	=		S.toList (psymbs sig)
			ps				=		Nothing : (map Just $ collectSubsets pflag psymbols)
			rs        =  	collectRelations rflag' psymbols (hasEq sig)
										--collect all predicates with at least two "X"
			rs' 			= 	nub $ concatMap genRelsXY rs
										--convert to predicates containing (all combinations of) 
										--variables "X" and "Y"
	continueSerial' tempdir problem noClash (rs'++(map nt rs')) (rs'++(map nt rs')) ps v elim
	
continueSerial' _ _ _ _ _ [] _ _ = return None
	
continueSerial' tempdir problem noClash [] rs (p:ps) v elim = 
	continueSerial' tempdir problem noClash rs rs ps v elim

continueSerial' tempdir problem noClash (r:rs) rs' (p:ps) v elim = do
	b <-  checkSerial tempdir problem noClash r p v elim
	if b then return $ F r 
		else
			continueSerial' tempdir problem noClash rs rs' (p:ps) v elim

-------------------------------------------------------------------------------

checkSerial tempdir problem noClash r p v elim = do
	let
		r' = And (S.fromList [r,Not equality])
		conj = form2conjecture noClash 0 (conjSerial r' p)
		provefile = tempdir ++ "checksr"
	maybePrint v "Checking irreflexivity, transitivity, seriality: " (Just r')
	maybePrint v "under " p	
	b <- prove conj provefile elim
	removeFile provefile
	return b

-------------------------------------------------------------------------------	

--seriality
conjSerial :: Relation -> Maybe Form -> Form		
conjSerial rel subset =
	case subset of
		Nothing	-> 
			existsRel "R" rel $ \r ->  
  		  forEvery x (nt (r x x)) --not reflexive
  		  /\ 

			  (((forEvery [x,y,z] ((nt (r x y)) \/ (nt (r y z)) \/ (r x z) )) 
				/\ (forEvery x (exist y (r x y)))) --transitive & serial
			
				\/ --or left-transitive & left-serial

				((forEvery [x,y,z] ((nt (r y x)) \/ (nt (r z y)) \/ (r z x) )) --left-transitive
				/\ (forEvery x (exist y (r y x))))) --left-serial

		Just pr	->
			existsPred "P" pr $ \p -> 
				existsRel "R" rel $ \r ->  
  		  	forEvery x ((nt (p x)) \/ nt (r x x)) --not reflexive in p
  		  	/\ 

			  	(((forEvery [x,y,z] ( (nt (p x) \/ nt (p y) \/ nt (p z)) \/ 
																((nt (r x y)) \/ (nt (r y z)) \/ (r x z) ))) 
					/\ (forEvery x (nt (p x) \/ exist y (p y /\ r x y)))) --transitive & serial in p
				
					\/ --or left-transitive & left-serial

					((forEvery [x,y,z] ((nt (p x) \/ nt (p y) \/ nt (p z)) \/ (nt (r y x)) \/ (nt (r z y)) \/ (r z x) )) --left-transitive in p
					/\ (forEvery x (nt (p x) \/ (exist y (p y /\ r y x)))))) --left-serial in p
 where
  x = Var Sym.x
  y = Var Sym.y
  z = Var Sym.z

