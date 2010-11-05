
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Infinox.Settings where

import Control.Monad.Reader
import Form
import Data.Set as S( Set )
import qualified Data.Set as S

import Flags 


newtype Settings a = Settings { unSettings :: ReaderT MethodSettings IO a }
   deriving (Monad, MonadReader MethodSettings, MonadIO )

data MethodSettings = MSet 
   { axiomfile :: FilePath
   , tempdir   :: FilePath
   , forms     :: [Form]
   , sig       :: Signature
   , noClash   :: String
   , verbose   :: Bool
   , funflag   :: String
   , relflag   :: Maybe String
   , pflag     :: Maybe String
   , depthflag :: Int
   , elimit    :: Int
   , prover    :: Prover
   
  }

runWithSettings :: MethodSettings -> Settings a  -> IO a
runWithSettings msig =  flip runReaderT msig . unSettings

data Signature = Sig {psymbs :: Set Symbol, fsymbs :: Set Symbol,  hasEq :: Bool}
	deriving (Eq,Show)

getSignature :: [Form] -> String -> Signature
getSignature fs t = Sig 
	(S.filter isPredSymbol syms)
	(case t of 
			"-"				->	(S.filter isFunSymbol syms)
			s					->	S.fromList $ getSymb s (S.toList syms)
	)
	(or (map hasEquality fs))
	where
		syms = symbols fs
		hasEquality (Atom (t1 :=: t2)) = t2 /= truth
		hasEquality (And fs) = S.member True $ S.map hasEquality fs
		hasEquality (Or fs) = S.member True $ S.map hasEquality fs
		hasEquality (Not f) = hasEquality f
		hasEquality (Equiv f1 f2) = hasEquality f1 || hasEquality f2
		hasEquality (ForAll (Bind s f)) = hasEquality f
		hasEquality (Exists (Bind s f)) = hasEquality f
  
-------------- collecting symbols ---------------------------------------------

getSymb s xs = filter (((==) s).show.symbolname) xs
symbolname (r ::: _) = r	

-------------------------------------------------------------------------------


