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

continueSerial tempdir sig problem  noClash rflag v elim = do
	let
			rs        =  	collectRelations rflag (S.toList (psymbs sig)) (hasEq sig)
			rs' 			= 	nub $ concatMap genRelsXY rs
	continueSerial' tempdir problem noClash (rs'++(map nt rs')) v elim
	
continueSerial' _ _ _ [] _ _ = return None

continueSerial' tempdir problem noClash (r:rs) v elim = do
	b <-  checkSerial tempdir problem noClash r v elim
	if b then return $ F r 
		else
			continueSerial' tempdir problem noClash rs v elim

-------------------------------------------------------------------------------

checkSerial tempdir problem noClash r v elim = do
	let
		r' = And (S.fromList [r,Not equality])
		conj = form2conjecture noClash 0 (conjSerial r')
		provefile = tempdir ++ "checksr"
	maybePrint v "Checking irreflexivity, transitivity, seriality: " (Just r')
	b <- prove conj provefile elim
	removeFile provefile
	return b

-------------------------------------------------------------------------------	

--seriality
conjSerial :: Relation -> Form		
conjSerial rel =
  existsRel "R" rel $ \r ->  
    forEvery x (nt (r x x)) --not reflexive
    /\ 
    (forEvery [x,y,z] ((nt (r x y)) \/ (nt (r y z)) \/ (r x z) )) --transitive
    /\
    (forEvery x (exist y (r x y))) --serial
 where
  x = Var Sym.x
  y = Var Sym.y
  z = Var Sym.z

