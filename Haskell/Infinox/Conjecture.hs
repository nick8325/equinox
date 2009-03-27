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
form2axioms' (f:fs) n = form2axiom fs f n ++ form2axioms' fs (n+1)

form2axiom fs f n = 	let x = noClashString fs in
	"fof(" ++ "a_" ++ (show n) ++ ", " ++ "axiom" ++ 
		", (" ++ showNormal x f ++ "))."
 
form2conjecture :: [Form] ->  Int -> Form -> String
form2conjecture fs n f = let x = noClashString fs in 
	"fof(" ++ "c_" ++ (show n) ++ ", " ++ "conjecture" ++ 
			", (" ++ showNormal x f ++ "))."


eqsymbol = (name "=" ::: ([top,top] :-> bool))

normalForm x (Atom (t1 :=: t2)) = 
	let
		nt1 = normalTerm x t1
		nt2 = normalTerm x t2 in
	case nt1 of 
		(Fun symb [t1',t2'])	-> 
				if symb == eqsymbol then
					if nt2 == truth then Atom (t1' :=: t2') else Not (Atom (t1' :=: t2'))
				 else Atom (nt1 :=: nt2)
		_	-> Atom (nt1 :=: nt2)
normalForm x (And ts) = 
	let
		newts = Set.map (normalForm x) ts 
	in
	And newts
normalForm x (Or ts) = 
	let
		newts = Set.map (normalForm x) ts 
	in
	Or newts
normalForm x (Not f) = Not (normalForm x f)
normalForm x (Equiv f1 f2) = Equiv (normalForm x f1) (normalForm x f2)
normalForm x (ForAll (Bind b f)) = ForAll (Bind b (normalForm x f))
normalForm x (Exists (Bind b f)) = Exists (Bind b (normalForm x f))	

normalTerm x (Fun (n ::: typing) ts) =  
	let 
		newname = name (normalName x n) in
	Fun (newname ::: typing) (map (normalTerm x) ts)
normalTerm x var = var

showNormal x  = show.(normalForm x)

---------------------------------------------------------------------------------

