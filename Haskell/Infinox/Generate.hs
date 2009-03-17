module Infinox.Generate where

--functions for collecting and generating predicates and terms

import Form
import Data.List (nub,sortBy,init,permutations)
import Data.Set as S( Set )
import qualified Data.Set as S

-------------------------------------------------------------------------------

getForms :: Problem ->  [Form]
--convert a problem to a list of formulas
getForms [] = []
getForms ((Input k t f):fs) = 
   case k of 
      Conjecture  -> (nt f):(getForms fs)
      _	          -> (f:(getForms fs))

------------------to simplify notation-----------------------------------------

equality :: Form
equality = Atom (Pred ("=" ::: (PredArity 2)) 
	[Var ("X" ::: Variable), Var ("Y" ::: Variable)])

star = (Var ("*" ::: Variable))

----for testing----

testterm = Fun ("f" ::: (FunArity 1)) 
	[Fun ("g" ::: (FunArity 3)) [Var ("X" ::: Variable),
		Var ("Y" ::: Variable),Var ("X" ::: Variable)]]
		
-----------collecting terms and predicates from the problem--------------------

--pick out the functional terms
getFuns :: Set Term -> Set Term
getFuns = S.filter function
	where
		function (Fun f ts) = or $ map hasVariable ts
		function _ = False
		hasVariable (Var _) = True
		hasVariable t = function t

--collect all function symbols
getFunSymbols :: Set Term -> Set Symbol
getFunSymbols = (S.filter funsymbol).symbols
	where
		funsymbol (_ ::: (FunArity _)) = True
		funsymbol _ = False
	
--collects all the variables of a term
getVars :: Term -> Set Symbol
getVars (Var x) = S.insert x S.empty
getVars (Fun _ ts) = S.unions $ map getVars ts

--collect all predicate symbols
getPredSymbols :: Form -> Set Symbol
getPredSymbols f  = S.filter predsymbol $ symbols f
	where 
		predsymbol (_ ::: (PredArity _)) = True
		predsymbol _ = False

-----------Generation of new terms---------------------------------------------

--generation of new terms based on the terms found in the problem
--Ex:  f(X,Y,g(X,Y)) becomes f(X,*,g(X,*)) and f(*,X,g(*,X))
generateFromTerms ts = S.unions $ map fixVars (S.toList ts)
	where
		fixVars t = S.map (fixVar t) (getVars t)

		fixVar (Var (x ::: Variable)) (z ::: Variable)   = 
			if x == z then (Var ("X" ::: Variable)) else star

		fixVar (Fun f ts)  z   = if and [not (includesVar z t) | t <- ts] then 
			star else Fun f [fixVar t z | t <- ts]

		includesVar (z ::: Variable) (Var (x ::: Variable)) = z == x
		includesVar z (Fun f ts) = or [includesVar z t | t <- ts]
		

--generate all terms with the given symbols, up to depth n
--WARNING! with many symbols or arities > 2, do not use depths > 2!
generateFromSymbols ss n = concat $ init $
	generate ss [[star, Var ("X" ::: Variable)]] n
	
generate _ ts 0 = ts
		--invariant: ts non-empty.
generate ss ts n = generate ss (funs:ts) (n-1)
	where
		funs = [ Fun (f ::: (FunArity a)) terms | 
							(f ::: (FunArity a)) <- ss, terms <- termLists a ts, hasX terms ]
		termLists 0 _ = [[]] 
		termLists n (ts:tts) = 
		--at least one argument in each produced list must have depth (n-1)
		  	nub $ concat [ insertions t terms | 
												t <- ts, terms <- arglists (n-1) (concat (ts:tts)) ]


arglists 0 list = [[]]
arglists m list = let tails = arglists (m-1) list in
									[ (x:xs) | x <- list, xs <- tails]

isArg a [] 		= False
isArg a ((Fun _ ts):tts) = isArg a ts || isArg a tts
isArg a (x:xs) = if a == x then True else isArg a xs

hasX = isArg (Var ("X" ::: Variable))

insertions :: a -> [a] -> [[a]] 
insertions a [] = [ [a] ] 
insertions a list@(x : xs) = (a : list) : [ x : z | z <- insertions a xs ] 
	
----------Generation of predicates---------------------------------------------
	
--Generation of predicates containing at least one "X"-argument,
--all other arguments are represented by "*"
generateFromP (p ::: (PredArity a)) = 
   [ Atom ( Pred (p ::: (PredArity a)) ts) | ts <- args a, hasX ts]
	where
		args n = arglists n [star, Var ("X" ::: Variable)]

generatePs  [] = []
generatePs (p:ps) = generateFromP p ++ generatePs ps
		
genRs :: Form -> [Form]
--used after checking reflexivity.
--ex p(X,*,X,*,X) ==> [p(X,*,Y,*,X), p(X,*,Y,*,Y), p(X,*,X,*,Y)]
--create all predicates with at least one X and one Y, *'s are left unchanged. 
genRs (Not form) = map Not $ genRs form
genRs (Atom (Pred p ts)) = map Atom $ filter hasXY [(Pred p ts')| ts' <- (genRs' ts)]
   where
      genRs'   [] = [[]]
      genRs'  ((Var ("X" ::: Variable)):ts) = map  ((Var ("X" ::: Variable)) : )   (genRs'' ts)
			--the first variable that is not a star is always "X"
      genRs'  ((Var ("*" ::: Variable)):ts) = map  ((Var ("*" ::: Variable)) : )   (genRs' ts)

			--after fixing the first variable to "X", any "X" can be substituted for either "X" or "Y".
      genRs'' [] = [[]]
      genRs'' ((Var ("*" ::: Variable)):ts) = map ((Var ("*" ::: Variable)) : )   (genRs'' ts)
      genRs'' ((Var ("X" ::: Variable)):ts) = (map ((Var ("X" ::: Variable)) : ) (genRs'' ts)) ++ 	 
	(map ((Var ("Y" ::: Variable)) : ) (genRs'' ts))
			--all predicates in the resultlist must include both X and Y.
      hasXY (Pred p ts) = isArg (Var ("X" ::: Variable)) ts  && isArg (Var ("Y" ::: Variable)) ts

--generate limiting predicates, possibly using connectives ~, /\, \/								
getPs ps och eller inte = let 
   ps' = sortForms $ generatePs ps 
   ps1 = (if inte then [Not p | p <- ps',not (eq p)] else []) 
   ps2 = (if eller then
      [Or (S.fromList [p1,p2]) | 
         p1 <- ps', p2 <- ps', p1  <  p2, not (eq p1), not (eq p2)]   else [])
   ps3 = if och then [And (S.fromList [p1,p2]) | 
            p1 <- ps', p2 <- ps', p1 < p2, not (eq p1), not (eq p2) ] else [] in
      ps' ++ ps1 ++ ps2 ++ ps3
	where
		eq (Atom (Pred ("=" ::: _) _)) = True
		eq _ = False

getRs = (filter twoOrMorex) . generatePs 
   where 
      twoOrMorex (Atom (Pred p ts)) = foldl (+) 0 [countx t | t <- ts] >= 2
      countx (Var ("X" ::: Variable)) = 1
      countx (Var _) = 0
      countx (Fun f ts) = foldl (+) 0 [countx t | t <- ts]
-------------------------------------------------------------------------------

--sorting

compareForms :: Form -> Form -> Ordering
-- "=" should come first in all lists, and is thus "less than" any other predicate
compareForms (Atom (Pred ("=" ::: PredArity 2) _)) 
								(Atom (Pred ("=" ::: PredArity 2) _)) = EQ
compareForms (Atom (Pred ("=" ::: PredArity 2) _)) _ = LT
compareForms _ (Atom (Pred ("=" ::: PredArity 2) _)) = Prelude.GT

compareForms (Atom (Pred _ ts)) (Atom (Pred _ ts2)) =  
	compare (countArgs ts) (countArgs ts2) 
	where
		countArgs list = foldl (+) 0 (map numberOfArgs list)

compareForms p (Not f) 				= compareForms p f
compareForms (Not f) p 				= compareForms f p
compareForms (Atom _) _ 		  = LT
compareForms _ (Atom _)				= Prelude.GT
compareForms _ _ = EQ --I don't bother about more complicated structures...

compareTerms :: Term -> Term -> Ordering
compareTerms t1 t2 = compare (numberOfArgs t1) (numberOfArgs t2)

numberOfArgs :: Term -> Int
numberOfArgs (Var _) = 1
numberOfArgs (Fun _ ts) = foldl (+) 0 $ map numberOfArgs ts

sortForms :: [Form] -> [Form]
sortForms = sortBy compareForms

sortTerms :: [Term] -> [Term]
sortTerms = sortBy compareTerms

-------------------------------------------------------------------------------

