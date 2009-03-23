module Infinox.Serial where

import Form
import Infinox.Conjecture
import Infinox.Generate
import Infinox.Util
import System.Directory
import qualified Data.Set as S
import qualified Infinox.Symbols as Sym
import Infinox.Types

-------------------------------------------------------------------------------

continueSR dir problem [] v tout =  return []
continueSR tempdir problem (r:rs) v tout = do
   b <-  checkSR tempdir problem r v tout
   if b then return [(Nothing,Just r,Nothing)] 
    else
      continueSR tempdir problem rs v tout

-------------------------------------------------------------------------------


checkSR tempdir problem r v tout = do
	let
		r' = And (S.fromList [r,Not equality])
		conj = form2conjecture 0 (conjSerial r')
		provefile = tempdir ++ "checksr"
	maybePrint v "Checking irreflexivity, transitivity, seriality: " (Just r')
	b <- prove conj problem provefile tout
	removeFile provefile
	return b

-------------------------------------------------------------------------------	

--seriality
conjSerial :: Relation -> Form		
conjSerial rel =
  existsRel "R" rel $ \r ->  
    forEvery x (nt (r x x)) --not reflexive
    /\ 
    (forEvery [x,y,z] (nt (r x y)) \/ (nt (r y z)) \/ (r x z) ) --transitive
    /\
    (forEvery x (exist y (r x y))) --serial
 where
  x = Sym.x
  y = Sym.y
  z = Sym.z
