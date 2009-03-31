module Infinox.InjOnto where
import Infinox.Generate
import Form
import Output
import Infinox.Conjecture
import List
import Infinox.Util
import qualified Infinox.Symbols as Sym

import System.Directory
import qualified Data.Set as S



continueInjOnto tempdir (Sig (psymbs,fsymbs,hasEq)) forms funs method
	rflag pflag verbose eflag =
		let
			ps				=		S.toList psymbs
			relations	=  	collectRelations rflag ps hasEq
			subsets		=		collectSubsets pflag ps		
		in
		continuePartOne tempdir forms eflag funs (relations,relations) [] subsets method verbose

continuePartOne _ _ _ _ _ _ [] _ _ = return None

continuePartOne dir forms elim ts (_,rs) refls ((Just p):ps) method v =
	continuePartTwo dir forms elim ts rs refls ((Just p):ps) method v

continuePartOne dir forms elim ts (rs1,rs2) refls (Nothing:ps) method v =
--collect all relations that are reflexive on the full domain before
--checking subdomains!
   do
			(psrs',rs') <- getPairs dir forms elim v Nothing checkPR rs1 
			--"getPairs" stops as soon as it founds a matching p-r tuple.
			--rs' are the remaining relations we need to check.
			--psrs' are the pairs "(Nothing,r)" where r is reflexive on the full domain
			let 
					refls' 		= map snd psrs'
					newrefls	= refls' ++ refls --save all refl.relations for later use!
			mt <- (mappy (proveProperty dir forms elim v method) $ 
						[(Just fun,Just r,Nothing) | r <- refls', fun <- ts])
			case mt of
				[]	  -> case rs' of
										[] -> continuePartTwo dir forms elim ts (rs2 \\ refls') newrefls ps method v 
					--no success -> continue with limiting predicates, keep the list of refl. 
					--preds, and remove refl. preds from testlist to avoid testing them twice.
										_	-> continuePartOne dir forms elim ts (rs',rs2) newrefls (Nothing:ps) method v 
					--more relations to check...   
				_      -> return $ toResult mt
         --success -> finish.

continuePartTwo _ _ _ _ _ _ [] _ _ = return None

continuePartTwo dir forms elim ts rs refls ((Just p):ps) method v  = 
   continueWithT ts --start by collecting the terms that match the lim.pred p.
   where 
      continueWithT ts = do
         (fsps,ts')  <- getPairs dir forms elim v (Just p) checkFP ts
         --fsps are the matching pairs, ts' are the terms that have not yet been processed.
         --(getPairs stops as soon as a matching pair is found)
         case fsps of
               [] -> continuePartTwo dir forms elim ts rs refls ps method v
               --no terms match with p - continue with next lim. pred
               _  -> continueWithR True rs ts' fsps 
               --if we have matching pairs -collect the refl. relations that match with p
               --"True" means that the relations in "refls" should be considered in this round,
      continueWithR b rs ts fsps  = do
         (rsps',rs') <- getPairs dir forms elim v (Just p) checkPR rs 
         --rsps' are matching (r,p) pairs, rs' are the relations not yet processed.
         let 
            psrs = (if b then [(Just p,r) | r <- refls] else []) ++ rsps' 
            --if b - include the predicates already shown to be reflexive.
            candidates = zippy fsps psrs --candidate triples :: (Maybe Term, Maybe Form, Maybe Form)
         --putStrLn (show candidates)
         mt <- (mappy (proveProperty dir forms elim v method) candidates)
         --use the given method on the candidate triples.
         --"mappy" stops when successful.
         case mt of
            []	->       --property does not hold for any candidate
               case rs' of 
               --check remaining list of relations r
                  []    -> continueWithT ts 
                  --no more relations - check remaining list of terms
                  _     -> continueWithR False rs' ts fsps 
                  --more relations to check - collect new (r,p) pairs, "False" means disregard
                  --relations shown to be reflexive on the full domain since they were checked
                  --in the first round (with every new term)
            _		-> return $ toResult mt


toResult [(Just f,Just r,Nothing)]  = TF f r
toResult [(Just f, Just r, Just p)] = TFF f r p

zippy [] _ = []
--zip together triples from pairs with matching "p's"
zippy ((f,p):fsps) psrs = 
   [(Just f,Just r,p') | (p',r) <- psrs, p' == p]  ++ zippy fsps psrs

getPairs dir fs elim v p checkfun ts_or_rs = 
   mapUntilSuccess (checkfun dir fs elim v p) ts_or_rs
-------------------------------------------------------------------------------


checkPR :: FilePath -> [Form] -> 
   Int -> Bool -> Maybe Form -> Form -> IO [(Maybe Form, Form)]
checkPR dir problem to vb p r  = do
	if r == equalityX then return $ zip (repeat p) (genRs r)
		else do
            let 
               conj = form2conjecture problem 0 (conjPimpliesRef r p)	
               provefile = dir ++ "checkpr" 
            maybePrint vb "Checking reflexivity of " (Just r)
            maybePrint vb "under " p				  	
            b <- prove conj problem provefile to
            removeFile provefile
            if b then return (zip (repeat p) (genRs r)) else return []


checkFP dir problem to vb p f  = do
   let 
      conj = form2conjecture problem 0 (conjPClosedUnderF f p)
      provefile = dir ++ "checkfp"
   maybePrint vb "Checking " p
   maybePrint vb "closed under " (Just f)
   b <- prove conj problem provefile to
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
				exist z (forEvery x (nt (r (f x) z))) --f non-surj w.r.t. r

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
		existsFun "F" fun $ \f ->		
			forEvery x (
				p (f x) \/ nt (p x)
			)
 where
  x = Var Sym.x

-------------------------------------------------------------------------------


