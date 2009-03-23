module Infinox.Serial where

import Form
import Infinox.Conjecture	
import Infinox.Util
import System.Directory
import qualified Data.Set as S

-------------------------------------------------------------------------------

continueSR dir problem [] v tout =  return []
continueSR tempdir problem (r:rs) v tout = do
   b <-  checkSR tempdir problem r v tout
   if b then return [(Just (Fun ("none" ::: (FunArity 0)) []),Just r,Nothing)] 
    else
      continueSR tempdir problem rs v tout

-------------------------------------------------------------------------------


checkSR tempdir problem r v tout = do
	let
		r' = And (S.fromList [r,Not (Atom (Pred ("=" ::: PredArity 2)  
					[Var ("X" ::: Variable),Var ("Y" ::: Variable)]))])
		conj = form2conjecture 0 (checkProperty conjSerial Nothing (Just r') Nothing)
		provefile = tempdir ++ "checksr"
	maybePrint v "Checking irreflexivity, transitivity, seriality: " (Just r')
	b <- prove conj problem provefile tout
	removeFile provefile
	return b

-------------------------------------------------------------------------------	

--seriality			
conjSerial _ (Just r) _ = 
	let (x,y,z) = (var "X", var "Y", var "Z") in
		forall [x]  (nt (r x x)) --not reflexive
		/\ 
		(forall [x,y,z] (nt (r x y)) \/ (nt (r y z)) \/ (r x z) ) --transitive
		/\
		(forall [x] (exist [y] (r x y))) --serial
