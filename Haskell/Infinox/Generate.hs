module Infinox.Generate where

--functions for collecting and generating predicates and terms

import Form
import Flags
import Data.List (nub,sortBy,init,permutations)
import Data.Set as S( Set )
import qualified Data.Set as S
import Infinox.Types
import qualified Infinox.Symbols as Sym
import Infinox.Symbols( star )

-------------------------------------------------------------------------------

data Signature = Sig {psymbs :: Set Symbol, fsymbs :: Set Symbol,  hasEq :: Bool}
	deriving (Eq,Show)

getSignature :: [Form] -> Signature
getSignature fs = Sig 
	(S.filter isPredSymbol syms)
	(S.filter isFunSymbol syms)
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

------------------to simplify notation-----------------------------------------

equality :: Relation
equality = Atom (Var Sym.x :=: Var Sym.y)

equalityX :: Relation
equalityX = Atom (Var Sym.x :=: Var Sym.x)

eq t1 t2 = Atom (t1 :=: t2)

-----------collecting terms and predicates from the problem--------------------

collectRelations rel preds hasEq = 
	let 
		rels = case rel of
							Nothing		-> []
							Just "-"	-> nub $ sortForms $ getRelations preds
							Just r		-> getRelations $ getSymb r preds
	in
	if hasEq then equalityX:rels else rels

collectSubsets p preds = 
	case p of
			Nothing 		-> []
			Just "-"		-> sortForms  $ nub $ getSubsets preds False False False
											--Possibility to add negation, conjunction and disjunction here
			Just p' -> case getSymb p' preds of 
										[p]   -> getSubsets [p] False False False
										[]    -> []

collectTestTerms sig t fs depth =   
	let
		funterms' = getFuns $ S.unions $ map subterms fs
		funterms	= case t of 
											"-" -> funterms'
											_		-> getNamedFun t funterms'		
	in
	 sortTerms $ nub $ getFunsFromSymbols (fsymbs sig) t depth
		 ++
		 (S.toList $ generateFromTerms (S.toList funterms))
		
		
getFunsFromSymbols syms t depth = 
	let
		funsymbols = S.toList (S.filter isFunSymbol syms) in
			generateFromSymbols funsymbols depth
		
--pick out the functional terms - i.e. all functions with at least one variable
getFuns :: Set Term -> Set Term
getFuns = S.filter function
	where
		function (Fun f ts) = isFunSymbol f && (or $ map hasVariable ts)
		function _ = False
		hasVariable (Var _) = True
		hasVariable t = function t

--get the functions with a given name only.
getNamedFun :: String -> Set Term -> Set Term
getNamedFun fun ts = S.filter (((==) fun).funname) ts
	where
		funname (Fun symb _) = show $ symbolname symb

getSymb s xs = filter (((==) s).show.symbolname) xs
symbolname (r ::: _) = r	

-----------Generation of new terms---------------------------------------------

--generation of new terms based on the terms found in the problem
--Ex:  f(X,Y,g(X,Y)) becomes f(X,*,g(X,*)) and f(*,X,g(*,X))
generateFromTerms ts = S.unions $ map fixVars ts
	where
		fixVars t = S.map (fixVar t) (free t)

		fixVar (Var x) z   = 
			Var (if x == z then Sym.x else star)

		fixVar (Fun f ts)  z   = if and [not (includesVar z t) | t <- ts] then 
			Var star else Fun f [fixVar t z | t <- ts]

		includesVar z (Var x) = z == x
		includesVar z (Fun f ts) = or [includesVar z t | t <- ts]
		

--generate all terms with the given symbols, up to depth n
--WARNING! with many symbols or arities > 2, do not use depths > 2!
generateFromSymbols ss depth = concat $ init $
	generate ss [[Var star, Var Sym.x]] depth
	
generate _ ts 0 = ts
		--invariant: ts non-empty.
generate ss ts n = generate ss (funs:ts) (n-1)
	where
		funs = [ Fun (f ::: ftype) terms | f ::: (ftype@(args :-> _)) <- ss, 
																				terms <- termLists (length args) ts, hasX terms ]
		termLists 0 _ = [[]] 
		termLists n (ts:tts) = 
		--at least one argument in each produced list must have depth (n-1)
		  	nub $ concat [ insertions t terms | 
												t <- ts, terms <- arglists (n-1) (concat (ts:tts)) ]

arglists 0 args = [[]]
arglists m args = let tails = arglists (m-1) args in
									[ (x:xs) | x <- args, xs <- tails]

isArg a [] 		= False
isArg a ((Fun _ ts):tts) = isArg a ts || isArg a tts
isArg a (x:xs) = a == x || isArg a xs

hasX = isArg (Var Sym.x)

insertions :: a -> [a] -> [[a]] 
insertions a [] = [ [a] ] 
insertions a list@(x : xs) = (a : list) : [ x : z | z <- insertions a xs ] 
	
----------Generation of predicates---------------------------------------------

--generate limiting predicates, possibly using connectives ~, /\, \/								
getSubsets ps och eller inte = let 
   ps' = sortForms $ generatePreds ps 
   ps1 = (if inte then [Not p | p <- ps',not (eq p)] else []) 
   ps2 = (if eller then
      [Or (S.fromList [p1,p2]) | 
         p1 <- ps', p2 <- ps', p1  <  p2, not (eq p1), not (eq p2)]   else [])
   ps3 = if och then [And (S.fromList [p1,p2]) | 
            p1 <- ps', p2 <- ps', p1 < p2, not (eq p1), not (eq p2) ] else [] in
      ps' ++ ps1 ++ ps2 ++ ps3
	where
		eq (Atom (Fun (_ ::: (_ :-> rtype)) _ :=: _)) = rtype == top
		eq _                                          = False

--Get all relations with 2 or more "X-variables" - to check for reflexivity
getRelations = (filter twoOrMorex) . generatePreds 
   where 
      twoOrMorex (Atom (t1 :=: t2)) = sum [countx t | t <- [t1,t2]] >= 2
      countx (Var x) | x == Sym.x = 1
      countx (Var _)              = 0
      countx (Fun f ts)           = sum [countx t | t <- ts]
	
--Generation of predicates containing at least one "X"-argument,
--all other arguments are represented by "*"
generatePreds  [] = []
generatePreds (p:ps) = generateFromPSymbol p ++ generatePreds ps
	where
		args n = arglists n [Var star, Var Sym.x]
		generateFromPSymbol (p ::: ptype@(pargs :-> rtype)) | rtype == bool = 
				[ Atom ( prd (p ::: ptype) ts) | ts <- args (length pargs), hasX ts]


		
genRelsXY :: Form -> [Form]
--ex p(X,*,X,*,X) ==> [p(X,*,Y,*,X), p(X,*,Y,*,Y), p(X,*,X,*,Y)]
--From predicates with arguments "*" and "X", create all predicates with at 
--least one X and one Y, *'s are left unchanged. 
genRelsXY (Not form) = map Not $ genRelsXY form
genRelsXY (Atom (t1 :=: t2)) = map Atom $ filter hasXY [ t1' :=: t2' | (t1',t2') <- getRelations t1 t2]

   where
		hasXY (t1 :=: t2) = isArg (Var Sym.x) [t1,t2]  && isArg (Var Sym.y) [t1,t2]
		getRelations t1 t2 = case t1 of
			Fun f ts 	-> zip (map (Fun f) $ genRelsXY' ts) (repeat t2)
			Var _			-> [(Var Sym.x,Var Sym.y)] 
		genRelsXY'   [] = [[]]
		genRelsXY'  (Var x:ts) 
							| x == Sym.x = map  ((Var Sym.x) : )   (genRelsXY'' ts)
			--the first variable that is not a star is always "X"
							| x == star  = map  ((Var star) : )   (genRelsXY' ts)

			--after fixing the first variable to "X", any "X" can be substituted for either "X" or "Y".
		genRelsXY'' [] = [[]]
		genRelsXY'' (Var s:ts) 
							| s == star  = map ((Var star) : )   (genRelsXY'' ts)
							| s == Sym.x = (map ((Var Sym.x) : ) (genRelsXY'' ts)) ++ 	 
									(map ((Var Sym.y) : ) (genRelsXY'' ts))
			--all predicates in the resultlist must include both X and Y.
      
-------------------------------------------------------------------------------

--sorting

compareForms :: Form -> Form -> Ordering
a `compareForms` b = stamp a `compare` stamp b
 where
  stamp a = (arity a, size a)
  
  arity (Atom (t1 :=: t2))  = numberOfArgs t1 + numberOfArgs t2
  arity (And xs)            = sum (map arity (S.toList xs))
  arity (Or xs)             = sum (map arity (S.toList xs))
  arity (x `Equiv` y)       = arity x + arity y
  arity (Not a)             = arity a
  arity (ForAll (Bind x a)) = arity (subst (x |=> Fun Sym.c []) a)
  arity (Exists (Bind x a)) = arity (subst (x |=> Fun Sym.c []) a)

  size (Atom (t1 :=: t2))  = 1 + sizeTerm t1 + sizeTerm t2
  size (And xs)            = 1 + sum (map size (S.toList xs))
  size (Or xs)             = 1 + sum (map size (S.toList xs))
  size (x `Equiv` y)       = 1 + size x + size y
  size (Not a)             = 1 + size a
  size (ForAll (Bind x a)) = 1 + size a
  size (Exists (Bind x a)) = 1 + size a

  sizeTerm (Var _)    = 1
  sizeTerm (Fun f xs) = 1 + sum (map sizeTerm xs)

compareTerms :: Term -> Term -> Ordering
compareTerms t1 t2 = compare (numberOfArgs t1) (numberOfArgs t2)

numberOfArgs :: Term -> Int
numberOfArgs (Var _) = 1
numberOfArgs (Fun _ ts) = sum $ map numberOfArgs ts

sortForms :: [Form] -> [Form]
sortForms = sortBy compareForms

sortTerms :: [Term] -> [Term]
sortTerms = sortBy compareTerms

-------------------------------------------------------------------------------

