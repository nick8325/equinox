module Infinox.Generate where

--functions for collecting and generating predicates and terms

import Form
import Data.List (nub,sortBy,init,permutations)
import Data.Set as S( Set )
import qualified Data.Set as S
import Infinox.Types
import qualified Infinox.Symbols as Sym
import Infinox.Symbols( star )

-------------------------------------------------------------------------------

{- -- obsolete, because now Clauses
getForms :: Problem ->  [Form]
--convert a problem to a list of formulas
getForms [] = []
getForms ((Input k t f):fs) = 
   case k of 
      Conjecture  -> (nt f):(getForms fs)
      _	          -> (f:(getForms fs))
-}

------------------to simplify notation-----------------------------------------

equality :: Relation
equality = Atom (Var Sym.x :=: Var Sym.y)

----for testing----

{-
testterm = Fun ("f" ::: (FunArity 1)) 
	[Fun ("g" ::: (FunArity 3)) [Var ("X" ::: Variable),
		Var ("Y" ::: Variable),Var ("X" ::: Variable)]]
-}

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
		funsymbol (_ ::: (_ :-> rtype)) = rtype == top
		funsymbol _ = False
	
--collects all the variables of a term
getVars :: Term -> Set Symbol
getVars (Var x) = S.insert x S.empty
getVars (Fun _ ts) = S.unions $ map getVars ts

--collect all predicate symbols
getPredSymbols :: Form -> Set Symbol
getPredSymbols f  = S.filter predsymbol $ symbols f
	where 
		predsymbol (_ ::: (_ :-> rtype)) = rtype == bool
		predsymbol _ = False

-----------Generation of new terms---------------------------------------------

--generation of new terms based on the terms found in the problem
--Ex:  f(X,Y,g(X,Y)) becomes f(X,*,g(X,*)) and f(*,X,g(*,X))
generateFromTerms ts = S.unions $ map fixVars (S.toList ts)
	where
		fixVars t = S.map (fixVar t) (getVars t)

		fixVar (Var x) z   = 
			Var (if x == z then Sym.x else star)

		fixVar (Fun f ts)  z   = if and [not (includesVar z t) | t <- ts] then 
			Var star else Fun f [fixVar t z | t <- ts]

		includesVar z (Var x) = z == x
		includesVar z (Fun f ts) = or [includesVar z t | t <- ts]
		

--generate all terms with the given symbols, up to depth n
--WARNING! with many symbols or arities > 2, do not use depths > 2!
generateFromSymbols ss n = concat $ init $
	generate ss [[Var star, Var Sym.x]] n
	
generate _ ts 0 = ts
		--invariant: ts non-empty.
generate ss ts n = generate ss (funs:ts) (n-1)
	where
		funs = [ Fun (f ::: ftype) terms | f ::: (ftype@(args :-> _)) <- ss, terms <- termLists (length args) ts, hasX terms ]
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

hasX = isArg (Var Sym.x)

insertions :: a -> [a] -> [[a]] 
insertions a [] = [ [a] ] 
insertions a list@(x : xs) = (a : list) : [ x : z | z <- insertions a xs ] 
	
----------Generation of predicates---------------------------------------------
	
--Generation of predicates containing at least one "X"-argument,
--all other arguments are represented by "*"
generateFromP (p ::: ptype@(pargs :-> rtype)) | rtype == bool = 
   [ Atom ( prd (p ::: ptype) ts) | ts <- args (length pargs), hasX ts]
	where
		args n = arglists n [Var star, Var Sym.x]

generatePs  [] = []
generatePs (p:ps) = generateFromP p ++ generatePs ps
		
genRs :: Form -> [Form]
--used after checking reflexivity.
--ex p(X,*,X,*,X) ==> [p(X,*,Y,*,X), p(X,*,Y,*,Y), p(X,*,X,*,Y)]
--create all predicates with at least one X and one Y, *'s are left unchanged. 
genRs (Not form) = map Not $ genRs form
genRs (Atom (t1 :=: t2)) = map Atom $ filter hasXY [ t1' :=: t2' | [t1',t2'] <- genRs' [t1,t2]]
   where
      genRs'   [] = [[]]
      genRs'  (Var x:ts) | x == Sym.x = map  ((Var Sym.x) : )   (genRs'' ts)
			--the first variable that is not a star is always "X"
      genRs'  (Var s:ts) | s == star  = map  ((Var star) : )   (genRs' ts)

			--after fixing the first variable to "X", any "X" can be substituted for either "X" or "Y".
      genRs'' [] = [[]]
      genRs'' (Var s:ts) | s == star  = map ((Var star) : )   (genRs'' ts)
      genRs'' (Var x:ts) | x == Sym.x = (map ((Var Sym.x) : ) (genRs'' ts)) ++ 	 
	(map ((Var Sym.y) : ) (genRs'' ts))
			--all predicates in the resultlist must include both X and Y.
      hasXY (t1 :=: t2) = isArg (Var Sym.x) [t1,t2]  && isArg (Var Sym.y) [t1,t2]

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
		eq (Atom (Fun (_ ::: (_ :-> rtype)) _ :=: _)) = rtype == top
		eq _                                          = False

getRs = (filter twoOrMorex) . generatePs 
   where 
      twoOrMorex (Atom (t1 :=: t2)) = sum [countx t | t <- [t1,t2]] >= 2
      countx (Var x) | x == Sym.x = 1
      countx (Var _)              = 0
      countx (Fun f ts)           = sum [countx t | t <- ts]
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

