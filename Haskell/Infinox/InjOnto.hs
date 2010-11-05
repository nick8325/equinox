module Infinox.InjOnto where

import qualified Data.Set as S
import System.Directory

import IO


import Form
import Output
import Infinox.Generate
import Infinox.Util
import Infinox.Conjecture
import Data.List
import System (system)
import qualified Infinox.Symbols as Sym
import Infinox.Settings
import Flags(Method(InjNotSurj,SurjNotInj))

import Control.Monad.Reader

continueInjOnto method funs rflag = do
	
		settings <- ask

	
		let
			sig'				=		sig settings
			pflag'			=		pflag settings	
			noClash'		=		noClash settings
			ps					=		filter (leqfive . arity) (S.toList $ psymbs sig') 
                    --all predicates in the signature with arity <= 5

			relations		=  	collectRelations rflag ps (hasEq sig') 
										--relations with two or more "X"-variables, with equality if it is present.
										--after establishing reflexivity of a relation, relations with "X" and "Y"
										--variables will be generated.
			subsets			=		collectSubsets pflag' ps	--collect subset-predicates depending on flag given	
	
--			candidates  =		combine funs $ combine (map Just (concatMap genRelsXY relations)) (Nothing:(map Just subsets))

{-		
		liftIO $ do
						putStrLn $ show relations
						putStrLn $ show subsets
						putStrLn $ show funs
						let 
						--	conj = form2conjecture (noClash settings) 0 (conjPimpliesRef r p)	
							provefile = tempdir settings ++ "check_all" 
           
						system ("cp " ++ axiomfile settings ++ " " ++ provefile)
						addAxioms noClash' (candidates) provefile
						b <- prove "" provefile (elimit settings)
				--		removeFile provefile
						if b then return Some else return None

combine xs ys = [(x,y) | x <- xs, y <- ys ]

addAxioms noClash' candidates file = do
		h' <- try $ openFile file AppendMode			
		case h' of 
			Right h -> do
				hSetBuffering h NoBuffering
				hPutStrLn h  $ form2axioms (map mkAxiom candidates) noClash'	
	--			hPutStrLn h $ form2conjecture noClash' 1 (mkAxiom (head candidates)) 
				hClose h	
				equinox file 	
--				eprove file 60
			_	-> error "wsfsdzf"

mkAxiom (t,(r,p)) = (nt (conjNotInjOnto (Just t) Nothing p))

-}

	
	--	liftIO $ putStrLn $ show candidates
	
		(result,refl_rels) <- tryFullDomain funs relations [] 
								--while testing the full domain - collect all reflexive relations to avoid
								--testing them again!
		case result of
			[]	-> do
								let testrels = deleteRels refl_rels relations 
								(result,fsps) <- trySubdomains_Refl funs refl_rels subsets []
								--First test the relations that are reflexive on the full domain
								--and test the resulting candidate triples.
								--collect matching pairs of functions and subsets to reuse in next steps
								case result of 
									None	-> trySubdomains fsps (nub [p | (_,p) <- fsps]) testrels testrels
									--Next, given pairs of functions and subsets, test all others relations
									--for reflexivity on these subsets, and test the resulting candidate triples.
									_			-> return result
			_		-> return $ toResult result

	where
		combine xs ys = concat [[(x,y) | x <- xs] | y <- ys] 
		tryFullDomain _ [] allrefls = return ([],allrefls)	
		tryFullDomain funs relations refls = do

			(psrs,rs) <- getPairs Nothing checkPR relations 
			--getPairs stops as soon as we find a relation that is reflexive on the full domain. 
			--psrs are the matching pairs subset-relation pairs, rs are the relations to be checked the next round.
			let
				newrefls = map snd psrs
				allrefls = newrefls ++ refls
--			putStrLn $ "Found reflexive predicates: " ++ show newrefls
			result <- (mappy (proveProperty method) $ 
							[(Just fun,Just r,Nothing) | r <- newrefls, fun <- funs])
			case result of
				[]	->	tryFullDomain funs rs allrefls
				_		->	return $ (result,[])

		trySubdomains_Refl _ _ [] fsps = return (None,fsps)
		trySubdomains_Refl funs refl_rels (p:ps) oldfsps = do
			(result,newfsps) <- trySubdomains_Refl' funs refl_rels p []
			case result of
				[]	-> trySubdomains_Refl funs refl_rels ps (newfsps ++ oldfsps)
				_		-> return (toResult result, newfsps ++ oldfsps)

		trySubdomains_Refl' [] _ _ fsps 					= return ([],fsps)
		trySubdomains_Refl' funs refl_rels p fsps = do
			(fsps',unprocessed_funs) <- collectMatchingFunsAndSubset p funs
			case fsps' of
				[]	-> return ([],fsps)
				_		-> do
								let 
									candidates = zippy fsps' (zip (repeat (Just p)) refl_rels)
								result <- (mappy (proveProperty method) candidates)
								case result of
									[]	->  trySubdomains_Refl' unprocessed_funs refl_rels p (fsps++fsps')
									_		->  return (result,fsps ++ fsps') 	
							
		trySubdomains _ [] _ _ = return None
		trySubdomains fsps (p:ps) relations [] = trySubdomains fsps ps relations relations 
		trySubdomains fsps (p:ps) relations rs = do
			(psrs,rs') <- getPairs p checkPR rs 
			case psrs of 
				[]	-> trySubdomains fsps ps relations rs'
				_		-> do
							let candidates = zippy fsps psrs
							result <- (mappy (proveProperty method) candidates)
							case result of
								[]	-> trySubdomains fsps (p:ps) relations rs'
								_		-> return $ toResult result
													
		collectMatchingFunsAndSubset p funs =
			getPairs (Just p) checkFP funs
			
		collectMatchingRelationsAndSubset p rs = 
			getPairs (Just p) checkPR rs

toResult []													= None
toResult [(Just f,Just r,Nothing)]  = TF f r
toResult [(Just f, Just r, Just p)] = TFF f r p

deleteRels :: [Form] -> [Form] -> [Form]
deleteRels rels1 rels2 = delSymbols rels2 (S.toList (symbols rels1))
delSymbols [] _ = []
delSymbols (r@(Atom ( (Fun s ts) :=: _)):rs) ss = if elem s ss 
	then delSymbols rs ss else r:(delSymbols rs ss)
delSymbols (r:rs) ss = delSymbols rs ss
-------------------------------------------------------------------------------
zippy [] _ = []
--zip together triples from pairs with matching "p's"
zippy ((f,p):fsps) psrs = 
   [(Just f,Just r,p') | (p',r) <- psrs, p' == p]  ++ zippy fsps psrs

getPairs p checkfun ts_or_rs = 
	mapUntilSuccess (checkfun p) ts_or_rs
-------------------------------------------------------------------------------

checkPR :: Maybe Form -> Form -> Settings [(Maybe Form, Form)]
checkPR p r  = do
	settings <- ask
	let 
			vb						= verbose settings
			pr						= prover settings      
	if r == equalityX then return $ zip (repeat p) (genRelsXY r)
		else
			liftIO $ do
						let 
							conj = form2conjecture (noClash settings) 0 (conjPimpliesRef r p)	
							provefile = tempdir settings ++ "checkpr" 
           
						system ("cp " ++ axiomfile settings ++ " " ++ provefile)
						maybePrint vb "Checking reflexivity of " (Just r)
						maybePrint vb "under " p				  	
						b <- prove pr conj provefile (elimit settings)
						removeFile provefile
						if b then return (zip (repeat p) (genRelsXY r)) else return []


checkFP :: Maybe Form -> Term -> Settings [(Term,Maybe Form)]
checkFP p f  = do
	settings <- ask
	let 
			conj 			= form2conjecture (noClash settings) 0 (conjPClosedUnderF f p)
			provefile = tempdir settings ++ "checkfp"
			vb 				= verbose settings
			pr				= prover settings
	liftIO $ do
							system $ "cp " ++ axiomfile settings ++ " " ++ provefile	
							maybePrint vb "Checking " p
							maybePrint vb "closed under " (Just f)
							b <- prove pr conj provefile (elimit settings)
							removeFile provefile
							if b then return [(f,p)] else return []

------properties---------------------------------------------------------------

--injectivity and non-surjectivity

conjInjNotOnto (Just fun) (Just rel) pr = 
	let 	
	 	z    =   Var Sym.z
		x    =   Var Sym.x
		y    =   Var Sym.y
	in
	 existsFun "F" fun $ \f ->
		existsRel "R" rel $ \r ->
	 
		 case pr of

			Nothing		-> --no limiting predicate!
				forEvery x (r x x) -- r refl
				/\
				forEvery [x,y] (r x y \/  nt (r (f x) (f y))) --f inj w.r.t r
				/\
				exist z (
					(forEvery x (nt (r (f x) z))) --f non-surj w.r.t. r (right or left)
					\/
					(forEvery x (nt (r z (f x)))))

			Just p' 	-> --limiting predicate!
			 existsPred "P" p' $ \p -> 
				(forEvery [x] ( --reflexivity + p closed under f
					(nt (p x)) \/ ( p (f x) /\ r x x)
				)) --p(X) ==> p(f(X)) & r(X,X)
				/\
				(exist y ( --left/right non-surjectivity
					p y /\ forEvery [x] ((nt (p x)) \/ nt (r (f x) y)))
            --Exists y : p(Y) & forall x (p(X) ==> ~r(f(X),Y))
				\/
				exist y (
					p y /\ forEvery x ((nt (p x)) \/ nt (r y (f x)))
				)) --Exists y : p(Y) & forall x (p(X) ==> ~r(Y,f(X)))
				/\ 
				forEvery [x,y]  --injectivity of f by r in p
					((nt (p x /\ p y)) \/ ((nt (r (f x) (f y))) \/ r x y))
            --p(X) & p(Y) => (r(f(X),f(Y) => r(X,Y)))


--surjectivity and non-injectivity
conjNotInjOnto (Just fun) _ pr =
	let 
			x    =   Var Sym.x
			y    =   Var Sym.y
	in

	existsFun "F" fun $ \f -> 

		case pr of
			Nothing ->  
				exist [x,y] ( --f not injective
					nt (x `eq` y) /\ (f x `eq` f y)
				)
				/\
				forEvery y (exist x ( --f surjective
				f x `eq` y))

			Just p' -> 
				existsPred "P" p' $ \p ->				
					forEvery x (
						(nt (p x)) \/ p (f x) --p closed under f
					)
					/\
					exist [x,y] ( --f not injective in p
						p x /\ p y /\ (nt (x `eq` y)) /\ (f x `eq` f y)
					)
					/\
					forEvery y ( --f surjective in p
						(nt (p y)) \/ exist x (p x /\ (f x `eq` y))
					)

--r reflexive in p
conjPimpliesRef rel (Just pr) = 
	existsPred "P" pr $ \p -> 
		existsRel "R" rel $ \r ->
			forEvery x (
				r x x \/ nt (p x)
			)
 where
  x = Var Sym.x
 
--r reflexive
conjPimpliesRef rel Nothing = 
	existsRel "R" rel $ \r ->
		forEvery x (		
			r x x
		)
 where
  x = Var Sym.x

--p closed under f
conjPClosedUnderF fun (Just pr) =
	existsPred "P" pr $ \p -> 
			(existsFun "F" fun $ \f ->	
			forEvery x (
				p (f x) \/ nt (p x)
			))
 where
  x = Var Sym.x

-------------------------------------------------------------------------------

