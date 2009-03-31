module Infinox.Conjecture where

import Form
import Name
import qualified Data.Set as Set
import Data.List
import qualified Infinox.Symbols as Sym
import Infinox.Types

-----------------------------------------------------------------------------------------

--Applying a function/predicate containing variables X (and possibly Y) to 
--one or two arguments.
(@@) :: Symbolic a => a -> [Term] -> a
p @@ [x]   = subst (Sym.x |=> x) p
p @@ [x,y] = subst ((Sym.x |=> x) |+| (Sym.y |=> y)) p
_ @@ _     = error "@@"

-----------------------------------------------------------------------------------------

existsFun :: String -> Function -> ((Term -> Term) -> Form) -> Form
existsFun s t p = existsSymbol s t (\f -> p (\x -> f [x]))

existsRel :: String -> Relation -> ((Term -> Term -> Form) -> Form) -> Form
existsRel s t p = existsSymbol s t (\f -> p (\x y -> f [x,y]))

existsPred :: String -> Predicate -> ((Term -> Form) -> Form) -> Form
existsPred s t p = existsSymbol s t (\f -> p (\x -> f [x]))

existsSymbol :: Symbolic a => String -> a -> (([Term] -> a) -> Form) -> Form
existsSymbol s t p = exist (Bind Sym.x (Bind Sym.y t')) (p f)
 where
  ts     = [ Var (name (s ++ "_" ++ show i) ::: V top) | i <- [1..] ]
  (t',_) = occurring Sym.star ts t
  f      = \xs -> t' @@ xs

-------------------------------------------------------------------------------

--translating to fof-form.

noClashString :: [Form] -> String
noClashString p = head [ s | i <- [0..] , let s = "x" ++ show i,
	null (filter (isInfixOf s) (map show (Set.toList (symbols p))))]

form2axioms [] = ""
form2axioms fs = form2axioms' fs 0
form2axioms' [] _ = ""
form2axioms' (f:fs) n = form2axiom fs f n ++ "\n" ++  form2axioms' fs (n+1)

form2axiom fs f n = 	let x = noClashString fs in
	"fof(" ++ "a_" ++ (show n) ++ ", " ++ "axiom" ++ 
		", " ++ showNormal x f ++ ")."
 
form2conjecture :: [Form] ->  Int -> Form -> String
form2conjecture fs n f = let x = noClashString fs in 
	"fof(" ++ "c_" ++ (show n) ++ ", " ++ "conjecture" ++ 
			", (" ++ showNormal x f ++ "))."

showNormal x f = showForm x $ mapOverTerms (giveNormalName x) f

showForm x (Atom (t1 :=: t2)) = show (Atom (t1 :=: t2))
showForm x (Not form) = 	"~(" ++ showForm x form ++ ")"
showForm x (And fs)	  = 	"(" ++ showWithSymbol " & " (map (showForm x) (Set.toList fs)) ++ ")"
showForm x (Or fs) 		= 	"(" ++ showWithSymbol " | " (map (showForm x) (Set.toList fs)) ++ ")"
showForm x (Equiv f1 f2) 				 = 	"(" ++ showForm x f1 ++ " = " ++ showForm x f2 ++ ")"
showForm x (ForAll (Bind b f)) 	 = 	"![" ++ show (normalSymb x b) ++ "] : (" ++ showForm x f ++ ")"
showForm x (Exists  (Bind b f))  = 	"?[" ++ show (normalSymb x b) ++ "] : (" ++ showForm x f ++ ")"

showWithSymbol _ [] = ""
showWithSymbol symb [f] = f
showWithSymbol symb (f:fs) = f ++ symb ++ showWithSymbol symb fs 

giveNormalName x fun@(Fun symb ts) = 
	if fun == truth then fun 
		else Fun (normalSymb x symb) (map (giveNormalName x) ts)
giveNormalName x (Var symb) = Var $ normalSymb x symb

normalSymb x (n ::: typing) = let newname = name (normalName x n) in
	(newname ::: typing)

trt = Fun ((prim "truth") ::: ([] :-> bool)) []
n1 = name "hej"
s1 = (n1 :::  ([top] :-> bool))
t1 = Fun s1  [Var ((name "x") ::: (V top))] 
test3 = Atom $  t1 :=: truth

---------------------------------------------------------------------------------

