module Infinox.Conjecture where

import Form
import Name
import qualified Data.Set as Set
import Data.List
import qualified Infinox.Symbols as Sym
import Infinox.Types
import Control.Monad.State

-----------------------------------------------------------------------------------------

--Applying a function/predicate containing variables X (and possibly Y and Z) to
--one or two or three arguments.
(@@) :: Symbolic a => a -> [Term] -> a
p @@ []                 = p
p @@ [x]        = subst (Sym.x |=> x) p
p @@ [x,y]      = subst ((Sym.x |=> x) |+| (Sym.y |=> y)) p
p @@ [x,y,z]    = subst ((Sym.x |=> x) |+| (Sym.y |=> y) |+| (Sym.z |=> z)) p
p @@ [x,y,z,v]          = subst ((Sym.x |=> x) |+| (Sym.y |=> y) |+| (Sym.z |=> z) |+| (Sym.v |=> v)) p
p @@ [x,y,z,v,w]        = subst ((Sym.x |=> x) |+| (Sym.y |=> y) |+| (Sym.z |=> z) |+| (Sym.v |=> v) |+| (Sym.w |=> w)) p
p @@ xs                         = error $ "@@: " ++ show xs

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
  ts = [ Var (name (s ++ "_" ++ show i) ::: V top) | i <- [1..] ]
  t' = evalState (occurring Sym.star t) ts
  f  = \xs -> t' @@ xs

-----------------------------------------------------------------------------------------

--translating to fof-form.

noClashString :: [Form] -> String
noClashString p = head [ s | i <- [0..] , let s = "x" ++ show i,
        null (filter (isInfixOf s) (map show (Set.toList (symbols p))))]

form2axioms :: [Form] -> String -> String
form2axioms fs noClash = form2axioms' fs noClash 0
        where
                form2axioms' [] _ _ = ""
                form2axioms' (f:fs) s n = form2axiom f s n ++ "\n" ++  form2axioms' fs s (n+1)

form2axiom :: Form -> String -> Int -> String
form2axiom f s n =
        "fof(" ++ "a_" ++ (show n) ++ ", " ++ "axiom" ++
                ", " ++ showNormal s f ++ ")."

form2conjecture :: String ->  Int -> Form -> String
form2conjecture noClash n f =
        "fof(" ++ "c_" ++ (show n) ++ ", " ++ "conjecture" ++
                        ", (" ++ showNormal noClash f ++ "))."

showNormal x f = show  $ normalBinds x $ mapOverTerms (giveNormalName x) f

giveNormalName x fun@(Fun symb ts) =
        if fun == truth then fun
                else Fun (normalSymb x symb) (map (giveNormalName x) ts)
giveNormalName x (Var symb) = Var $ normalSymb x symb

normalBinds x (Not f) = Not $ normalBinds x f
normalBinds x (And fs) = And (Set.map (normalBinds x) fs)
normalBinds x (Or fs) =  Or (Set.map (normalBinds x) fs)
normalBinds x (Equiv f1 f2) = Equiv (normalBinds x f1) (normalBinds x f2)
normalBinds x (ForAll (Bind b f)) = ForAll (Bind (normalSymb x b) (normalBinds x f))
normalBinds x (Exists (Bind b f)) = Exists (Bind (normalSymb x b) (normalBinds x f))
normalBinds _ atom = atom

normalSymb x (n ::: typing) = let newname = name (normalName x n) in
        (newname ::: typing)

trt = Fun ((prim "truth") ::: ([] :-> bool)) []
n1 = name "f"
n2 = name "subset"
s1 = (n1 :::  ([top] :-> bool))
s2 = (n2 :::  ([top] :-> bool))
t1 = Fun s1  [Var ((name "X") ::: (V top))]
t2 = Fun s2  [Var ((name "X") ::: (V top))]

test3 = Atom $  t1 :=: truth

p1 = Atom $ t2 :=: truth


-----------------------------------------------------------------------------------------

