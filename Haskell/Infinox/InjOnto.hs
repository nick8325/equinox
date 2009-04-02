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



continueInjOnto tempdir sig axioms noClash funs method rflag pflag verbose eflag =
		let
			ps				=		S.toList $ psymbs sig
			relations	=  	collectRelations rflag ps (hasEq sig)
			subsets		=		collectSubsets pflag ps		
		in
		continuePartOne tempdir axioms noClash eflag funs (relations,relations) [] 
			subsets method verbose


continuePartOne _ _ _ _ _ _ _ [] _ _ = return None

continuePartOne dir axioms noClash elim ts (_,rs) refls ((Just p):ps) method v =
	continuePartTwo dir axioms noClash elim ts rs refls ((Just p):ps) [] method v

continuePartOne dir axioms noClash elim ts (rs1,rs2) refls (Nothing:ps) method v =
--collect all relations that are reflexive on the full domain before
--checking subdomains!
   do
--			putStr $ if v then "Searching for reflexive relations...\n" else ""
			
			(psrs',rs') <- getPairs dir axioms noClash elim v Nothing checkPR rs1 
			--"getPairs" stops as soon as it founds a matching p-r tuple.
			--rs' are the remaining relations we need to check.
			--psrs' are the pairs "(Nothing,r)" where r is reflexive on the full domain
			let 
					refls' 		= map snd psrs' --these relations are reflexive on the full domain, and
																		--thus we do not need to check them for reflexivity in combination
																		--with subsets...
					newrefls	= refls' ++ refls --save all refl.relations for later use!
--			putStr $ if v then "Found reflexive relations: " ++ show refls' ++ "\n" else ""
			mt <- (mappy (proveProperty dir axioms noClash elim v method) $ 
						[(Just fun,Just r,Nothing) | r <- refls', fun <- ts]) --run the chosen method on each function
																																	--together w. each reflexive relation.
			case mt of
				[]	  -> case rs' of
										[] -> continuePartTwo dir axioms noClash elim ts (rs2 \\ refls') newrefls ps [] method v 
										--no success and no more relations to check on the full domain -> continue with limiting predicates, 
										--keeping the list of refl. relations, and remove these from the testlist to avoid testing them twice.
										_	-> continuePartOne dir axioms noClash elim ts (rs',rs2) newrefls (Nothing:ps) method v 
										--more relations to check..   
				_      -> return $ toResult mt
         --success -> finish.

continuePartTwo _ _ _ _ _ _ _ [] _ _ _ = return None
--If we run out of subsets to test, there are no more candidates, and we must give up!

continuePartTwo dir axioms noClash elim ts rs refls ((Just p):ps) oldpsrs method v  = 
   continueWithTerms ts oldpsrs --start by collecting the terms that match the lim.pred p.
   where 
      continueWithTerms ts oldpsrs = do
--        putStr $ if v then "Searching for functions under which " ++ show p ++ " is closed\n" else ""
         (fsps,ts')  <- getPairs dir axioms noClash elim v (Just p) checkFP ts
         --fsps are the matching pairs, ts' are the terms that have not yet been processed.
         --(getPairs stops as soon as a matching pair is found)
         case fsps of
               [] -> continuePartTwo dir axioms noClash elim ts rs refls ps [] method v
               --no terms match with p - continue with next lim. pred, reset oldpsrs
               _  -> do
--                     putStr $ if v then "Found matching pairs: " ++ show fsps ++ "\n" else ""	     
                     continueWithRelations True rs ts' fsps oldpsrs
               --if we have matching pairs -collect the refl. relations that match with p
               --"True" means that the relations in "refls" should be considered in this round,
      continueWithRelations b rs ts fsps oldpsrs  = do
         putStr $ if v then "Searching for relations that are reflexive under " ++ show p ++ "\n" else "" 
         (rsps',rs') <- getPairs dir axioms noClash elim v (Just p) checkPR (rs\\(map snd oldpsrs)) 					
         --rsps' are matching (r,p) pairs, rs' are the relations not yet processed.
         let
            newoldpsrs = oldpsrs ++ rsps'
            prefls = [(Just p,r) | r <- refls]
            psrs = (if b then prefls else []) ++ newoldpsrs
						
            --if b - include the predicates already shown to be reflexive.
            candidates = zippy fsps psrs --candidate triples :: (Maybe Term, Maybe Form, Maybe Form)
         --putStrLn (show candidates)
--         putStr $ if v then "Found new matching pairs: " ++ show rsps' ++ "\n" else ""	     
--         putStr $ if v then "Matching pairs already found: " ++ show oldpsrs ++ "\n" else ""	 
--         putStr $ if v && b then "Trivially matching pairs: " ++ show prefls ++ "\n" else ""	 
         mt <- (mappy (proveProperty dir axioms noClash elim v method) candidates)
         --use the given method on the candidate triples.
         --"mappy" stops when successful.
         case mt of
            []	->       --property does not hold for any candidate
               case rs' of 
               --check remaining list of relations r
                  []    -> continueWithTerms ts $ newoldpsrs
                  --no more relations - check remaining list of terms
                  _     -> continueWithRelations False rs' ts fsps newoldpsrs 
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

getPairs dir axioms noClash elim v p checkfun ts_or_rs = 
   mapUntilSuccess (checkfun dir axioms noClash elim v p) ts_or_rs
-------------------------------------------------------------------------------


checkPR :: FilePath -> String -> String ->
   Int -> Bool -> Maybe Form -> Form -> IO [(Maybe Form, Form)]
checkPR dir axioms noClash to vb p r  = do
	if r == equalityX then return $ zip (repeat p) (genRelsXY r)
		else do
            let 
               conj = form2conjecture axioms noClash 0 (conjPimpliesRef r p)	
               provefile = dir ++ "checkpr" 
            maybePrint vb "Checking reflexivity of " (Just r)
            maybePrint vb "under " p				  	
            b <- prove conj axioms provefile to
            removeFile provefile
            if b then return (zip (repeat p) (genRelsXY r)) else return []


checkFP dir axioms noClash to vb p f  = do
   let 
      conj = form2conjecture axioms noClash 0 (conjPClosedUnderF f p)
      provefile = dir ++ "checkfp"
   maybePrint vb "Checking " p
   maybePrint vb "closed under " (Just f)
   b <- prove conj axioms provefile to
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
		existsFun "F" fun $ \f ->		
			forEvery x (
				p (f x) \/ nt (p x)
			)
 where
  x = Var Sym.x

-------------------------------------------------------------------------------


