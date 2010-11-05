module Infinox.Relations where

import Form
import Flags( Flags, Method(InjNotSurj,SurjNotInj,Serial,Relation,Trans))
import Infinox.Conjecture
import Infinox.Generate
import Infinox.Util
import System.Directory
import qualified Data.Set as S
import qualified Infinox.Symbols as Sym
import Infinox.Types
import Infinox.Settings

import Control.Monad.Reader


import Data.List (nub)
import Data.Set as S( Set )
import Output
import System (system)
import qualified Data.Set as S

continueRelations :: Method -> [Relation] -> Settings Result
continueRelations method rels = do 
	settings <- ask
	let
			rflag'		=		case relflag settings of
											Nothing 	-> Just "-"
											Just "-"	-> Just "-"
											_					-> relflag settings
			sig'			=   sig settings
			psymbols	=		S.toList (psymbs sig')
			ps				=		Nothing : (map Just $ collectSubsets (pflag settings) psymbols)
			rs        =  	collectRelations rflag' psymbols (hasEq sig')
										--collect all predicates with at least two "X"
			rs' 			= 	concatMap genRelsXY rs
										--convert to predicates containing (all combinations of) 
										--variables "X" and "Y"
			
			testrels = (nub (rels ++ rs')) ++ map nt rs'
	continueRelations' method testrels testrels ps 

continueRelations' :: Method -> [Relation] -> [Relation] -> [Maybe Form] -> Settings Result	
continueRelations' _ _ _ [] = return None
	
continueRelations' method [] rs (p:ps) = 
	continueRelations' method rs rs ps

continueRelations' method (r:rs) rs' (p:ps) = do
	b <-  checkProperty method r p 
	if b then case p of
		Nothing ->	return $ F r
		Just p'	->	return $ FF r p' 
		else
			continueRelations' method rs rs' (p:ps) 

-------------------------------------------------------------------------------

checkProperty :: Method -> Relation -> Maybe Form -> Settings Bool
checkProperty method r p = 
	do
		settings <- ask
		let 
			v        = verbose settings
			noClash' = noClash settings
			tempdir' = tempdir settings
			problem  = axiomfile settings
			pr		   = prover settings
			conj = case method of 
				Serial -> let
										r' = And (S.fromList [r,Not equality]) in
									 form2conjecture noClash' 0 (conjSerial r' p)
				Relation -> form2conjecture noClash' 0 (conjRelation r p)
				Trans    -> form2conjecture noClash' 0 (conjTrans r p)

			provefile = tempdir' ++ "checksr"
		Settings $ lift $ maybePrint v "Checking relation: " (Just r)
		Settings $ lift $ maybePrint v "under " p	
		Settings $ lift $ system $ "cp " ++ problem ++ " " ++ provefile
		b <- Settings $ lift $ prove pr conj provefile (elimit settings)
		Settings $ lift $ removeFile provefile
		return b							
		
			 
{-
checkProperty Serial r p  = 
	do
		settings <- ask
		let
			v       = verbose settings
			noClash = noClash settings
			tempdir = tempdir settings
			r' = And (S.fromList [r,Not equality])
			conj = form2conjecture noClash 0 (conjSerial r' p)
			provefile = tempdir ++ "checksr"
		system $ "cp " ++ axiomfile settings ++ " " ++ provefile
		maybePrint v "Checking irreflexivity, transitivity, seriality: " (Just r')
		maybePrint v "under " p	
		b <- prove conj provefile (elimit settings)
		removeFile provefile
		return b

checkProperty Relation r p = do
	let
		conj = form2conjecture noClash 0 (conjRelation r p)
		provefile = tempdir ++ "checkrel"
	system $ "cp " ++ problem ++ " " ++ provefile
	maybePrint v "Checking relation: " (Just r)
	maybePrint v "under " p	
	b <- prove conj provefile elim
	removeFile provefile
	return b
-}
-------------------------------------------------------------------------------	

equal = \x -> \y -> Atom (x :=: y)

conjRelation :: Relation -> Maybe Form -> Form
conjRelation rel subset = 
	case subset of
		Nothing	-> 
			existsRel "R" rel $ \r ->
				let 
					surjective = forEvery y (exist x (r x y))
					injective	 = forEvery [x,y,z] $ (equal x y) \/ nt (r x z /\ r y z) --(nt (r x z)) \/ (nt (r y z)) \/ equal x y
					total			 = forEvery x $ exist y $ r x y 
					function	 = forEvery [x,y,z] $ (nt (r x y)) \/ (nt (r x z)) \/ equal y z 
				in
					((total /\ injective) `Equiv`  (nt (surjective /\ function)))		
						-- \/ (serial /\ transitive /\ irreflexive)		
		Just p' ->
			existsPred "P" p' $ \p -> 
				existsRel "R" rel $ \r ->
					let
						surjective = forEvery y $ (nt (p y)) \/ (exist x (p x /\ (r x y)))
						injective  = forEvery [x,y,z] $ (nt(p x) \/ nt(p y) \/ nt(p z))  \/  
																							 (equal x y) \/ nt (r x z /\ r y z)
						total			 = forEvery x $ nt(p x) \/ (exist y $ p y /\ r x y) 
						function	 = forEvery [x,y,z] $ (nt (p x) \/ nt (p y) \/ nt (p z)) \/ 
														((nt (r x y)) \/ (nt (r x z)) \/ equal y z) 
					in
						((total /\ injective) `Equiv`  (nt (surjective /\ function)))	
	 where
	  x = Var Sym.x
	  y = Var Sym.y
	  z = Var Sym.z


--seriality
conjSerial :: Relation -> Maybe Form -> Form		
conjSerial rel subset =
	case subset of
		Nothing	-> 
			(exist x (x `eq` x)) /\
			(existsRel "R" rel $ \r ->  
  		  forEvery x (nt (r x x)) --not reflexive
  		  /\ 

			  (((forEvery [x,y,z] ((nt (r x y)) \/ (nt (r y z)) \/ (r x z) )) 
				/\ (forEvery x (exist y (r x y)))) --transitive & serial
			
				\/ --or left-transitive & left-serial

				((forEvery [x,y,z] ((nt (r y x)) \/ (nt (r z y)) \/ (r z x) )) --left-transitive
				/\ (forEvery x (exist y (r y x)))))) --left-serial

		Just pr	->
			existsPred "P" pr $ \p -> 
				existsRel "R" rel $ \r ->
					exist x (p x) /\ --p non empty  
  		  	forEvery x ((nt (p x)) \/ nt (r x x)) --r not reflexive in p
  		  	/\ 

			  	(((forEvery [x,y,z] ( (nt (p x) \/ nt (p y) \/ nt (p z)) \/ 
																((nt (r x y)) \/ (nt (r y z)) \/ (r x z) ))) 
					/\ (forEvery x (nt (p x) \/ exist y (p y /\ r x y)))) --transitive & serial in p
				
					\/ --or left-transitive & left-serial

					((forEvery [x,y,z] ((nt (p x) \/ nt (p y) \/ nt (p z)) \/ (nt (r y x)) 
							\/ (nt (r z y)) \/ (r z x) )) --left-transitive in p
					/\ (forEvery x (nt (p x) \/ (exist y (p y /\ r y x)))))) --left-serial in p
 where
  x = Var Sym.x
  y = Var Sym.y
  z = Var Sym.z


conjTrans :: Relation -> Maybe Form -> Form
conjTrans rel subset = 
	case subset of
		Nothing ->
     			existsRel "R" rel $ \r ->
				let 
					domsize      = exist x $ exist y $ nt (equal x y)
					antisym      = forEvery x $ forEvery y $ (equal x y) \/ (nt (r x y)) \/  (nt (r y x)) 
					transitive	 = forEvery [x,y,z] ((nt (r x y)) \/ (nt (r y z)) \/ (r x z) ) 

					total	  		 = forEvery x $ forEvery y $ (r x y) \/ (r y x) 
					doubserial	 = forEvery x $ forEvery y $ (equal x y \/ (nt (r x y))) \/ (exist z $ (nt (equal x z)) /\ (nt (equal y z)) /\ (r x z))

				in
					antisym /\ transitive /\ total /\ doubserial
		Just pr -> 
				
			existsPred "P" pr $ \p -> 
				existsRel "R" rel $ \r ->
					exist [x,y] $ p(x) /\ p(y) /\ (nt (equal x y)) /\

			let 
				antisym    = forEvery [x,y] $ (nt (p x)) \/ (nt (p y)) \/ (equal x y) \/ (nt (r x y)) \/  (nt (r y x)) 
				transitive = (forEvery [x,y,z] ( (nt (p x) \/ nt (p y) \/ nt (p z)) \/ 
																((nt (r x y)) \/ (nt (r y z)) \/ (r x z) ))) 
				total      = forEvery [x,y] $ (nt (p x) \/ nt (p y)) \/ (r x y)  \/ (r y x)
				doubserial = forEvery [x,y] $ (nt (p x) \/ nt (p y) \/ nt (p z)) \/   (equal x y \/ (nt (r x y))) \/ (exist z $ (nt (equal x z)) /\ (nt (equal y z)) /\ (r x z))
			in antisym /\ transitive /\ total /\ doubserial
		where
		  x = Var Sym.x
		  y = Var Sym.y
		  z = Var Sym.z
				



