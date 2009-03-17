module Infinox.Conjecture where

import Form
import qualified Data.Set as Set
import List


--for testing	
testt =  Fun ("f" ::: FunArity 2) [Var ("X" ::: Variable), Var ("*" ::: Variable)]
testp =  Atom $ Pred ("p" ::: PredArity 2) 
   [Var ("*" ::: Variable), Var ("X" ::: Variable)]
testr =  Atom $ Pred ("r" ::: PredArity 3) 
   [Var ("*" ::: Variable), Var ("X" ::: Variable), Var ("Y" ::: Variable)]

-----------------------------------------------------------------------------------------

--constructs the conjecture of a given property 
--conj on fun, rel and p (all of type Maybe)
checkProperty conj fun rel p =
	exist (vs ++ vs2 ++ vs3) (conj fun' rel' p')
	where
		(fun',vs) 	= starVars fun "F"
		(rel',vs2) 	= starVarsR rel "R"
		(p', vs3)		= starVarsP p "P"


--Applying a predicate containing variables X (and possibly Y) to 
--one or two arguments.
(@@) :: Form -> [Term] -> Form
(@@) p [x] = subp ("X" ::: Variable) x p
(@@) p [x,y] = 
   let 
      p'  = subp ("X" ::: Variable) (Var ("temp" ::: Variable)) p 
      p'' = subp ("Y" ::: Variable) y p' in
   subp ("temp" ::: Variable) x p''
(@@) _ _ = undefined

--Applying a function containing a variable "X" to one argument.
(@@@) :: Term -> Term -> Term
(@@@) (Var ("X" ::: Variable)) x = x
(@@@) (Var x) _ = Var x
(@@@) (Fun f ts) x = Fun f (map ((flip (@@@)) x) ts) 

--Substituting all "*"-symbols in a list of formulas with variables
(@*) :: [Form] -> [Term] -> [Form]
(@*) [] _ = []
(@*) (f:fs) vs = case f of
   Atom (Pred p ts)  -> Atom (Pred p (ts @@* vs)) : fs' 
   And ps            -> (And $ Set.fromList $ (Set.toList ps) @* vs) : fs'
   Or ps             -> (Or  $ Set.fromList $ (Set.toList ps) @* vs) : fs'
   Not p             -> (Not $ head ([p] @* vs)) : fs'
   where
      fs' = fs @* (drop (predstars f) vs)

--Substituting all "*"-symbols in a list of terms with variables
(@@*)  :: [Term] -> [Term] -> [Term]
(@@*) [] _ = []
(@@*) (f:fs) vs = case f of
   Var ("*" ::: Variable)  -> head vs :(fs @@* (drop 1 vs))
   Var x                   -> f:(fs @@* vs)
   (Fun f ts)              -> let n = foldl (+) 0 (map stars ts) in
                                 Fun f (ts @@* vs): (fs @@* drop n vs)

eq :: Term -> Term -> Form
eq x y = Atom $ Pred ("=" ::: (FunArity 2)) [x,y]

forall :: [Term] -> Form -> Form
forall [] f = f
forall ((Var x):xs) f = forAll x (forall xs f)

exist :: [Term] -> Form -> Form
exist [] f = f
exist ((Var x):xs) f = exists x $ exist xs $ f

var :: String -> Term
var x = Var (x ::: Variable)


starVarsR Nothing _ = (Nothing, [])
starVarsR (Just rel) t = (Just r,vars)
   where
      vars     = map Var $ genVars (predstars rel) t
      [rel']   = [rel] @* vars
      r        = \x -> \y -> rel' @@ [x,y]

starVars Nothing _ = (Nothing, [])
starVars (Just fun) s = (Just f,vars)
   where
      vars       = map Var $ genVars (stars fun) s
      [fun']     = [fun] @@* vars
      f          = \x -> fun' @@@ x 

starVarsP Nothing _ = (Nothing, [])
starVarsP (Just p) s = (Just p',vars)
   where
      vars     = map Var $ genVars (predstars p) s
      [p'']    = [p] @* vars
      p'       = \x  -> p'' @@ [x]
		
-------------------------------------------------------------------------------
			 
stars (Var ("*" ::: Variable))  = 1
stars (Var _)	 = 0
stars (Fun f ts) = foldl (+) 0 (map stars ts)

predstars (Atom (Pred p ts)) = foldl (+) 0 (map stars ts) 
predstars (And ps) = foldl (+) 0 (map predstars (Set.toList ps))
predstars (Or ps) = foldl (+) 0 (map predstars (Set.toList ps))
predstars (Not p) = predstars p

genVars 0 s = []
genVars n s = ((s++(show n)) ::: Variable) : genVars (n-1) s
				
-------------------------------------------------------------------------------
		 
--substitution
subt x t (Var y) = if x == y then t else Var y
subt x t (Fun s ts) = Fun s (map (subt x t) ts)

subp x y (Atom (Pred p ts))  = Atom (Pred p (map (subt x y) ts))
subp x y (And ps) = And $ Set.map (subp x y) ps
subp x y (Or ps) = Or $ Set.map (subp x y) ps
subp x y (Not p) = Not (subp x y p)

-------------------------------------------------------------------------------

--translating to fof-form.

form2axioms [] = ""
form2axioms fs = form2axioms' fs 0
form2axioms' [] _ = ""
form2axioms' (f:fs) n = form2axiom f n ++ form2axioms' fs (n+1)

form2axiom f n = 	"fof(" ++ "a_" ++ (show n) ++ ", " ++ "axiom" ++ 
		", (" ++ show f ++ "))."

form2conjecture :: Int -> Form -> String		
form2conjecture n f = 	"fof(" ++ "c_" ++ (show n) ++ ", " ++ "conjecture" ++ 
		", (" ++ show f ++ "))."

---------------------------------------------------------------------------------

