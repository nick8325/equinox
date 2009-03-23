module Infinox.Conjecture where

import Form
import Name
import qualified Data.Set as Set
import List
import qualified Infinox.Symbols as Sym
import Infinox.Types

{-
--for testing	
testt =  Fun ("f" ::: FunArity 2) [Var ("X" ::: Variable), Var ("*" ::: Variable)]
testp =  Atom $ Pred ("p" ::: PredArity 2) 
   [Var ("*" ::: Variable), Var ("X" ::: Variable)]
testr =  Atom $ Pred ("r" ::: PredArity 3) 
   [Var ("*" ::: Variable), Var ("X" ::: Variable), Var ("Y" ::: Variable)]
-}

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

