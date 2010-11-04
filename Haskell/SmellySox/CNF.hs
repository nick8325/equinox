module SmellySox.CNF where

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified SmellySox.Formula as Formula
import SmellySox.Formula hiding ((:=:), constants, types)
import SmellySox.Utils
import Data.List

data CNF = CNF { types :: [Type], constants :: [Atom], clauses :: [Clause] }
data Clause = Clause { vars :: [Atom], literals :: [Literal] }
data Literal = Term :=: Term | Term :/=: Term | Pos Term | Neg Term

instance Show Literal where
  show (t1 :=: t2) = show t1 ++ "=" ++ show t2
  show (t1 :/=: t2) = show t1 ++ "!=" ++ show t2
  show (Pos t) = show t
  show (Neg t) = "~" ++ show t

instance Show Clause where
  show Clause{vars = [], literals = ls} = intercalate " | " (map show ls)
  show c = "![" ++ intercalate ", " (map showTypedAtom (vars c))
                ++ "]. "
                ++ intercalate " | " (map show (literals c))

instance Show CNF where
  show cnf =
    unlines $
      ["Types: " ++ intercalate ", " (map show (types cnf))] ++
      map showTypedAtom (constants cnf) ++
      [] ++
      map show (clauses cnf)

alphaRename :: Formula -> Formula
alphaRename f = evalState (onFormulaM go f) Set.empty
  where go e@(Literal _) = return e
        go e@(_ Formula.:=: _) = return e
        go e@(Const _) = return e
        go (Binop op e1 e2) = liftM2 (Binop op) (go e1) (go e2)
        go (Not e) = fmap Not (go e)
        go (Quant q x e) = do
          s <- get
          let origName = case q of Exists -> "sk" ++ name x
                                   ForAll -> name x
              names = origName:[origName ++ show i | i <- [1..] ]
              name':_ = filter (`Set.notMember` s) names
              x' = x { name = name' }
          modify (Set.insert name')
          e' <- go e
          if x == x'
             then return (Quant q x' e')
             else return (Quant q x' (subst x (x' :@: []) e'))

subst :: Atom -> Term -> Form -> Form
subst x v (Literal l) = Literal (substTerm x v l)
subst x v (t Formula.:=: u) = substTerm x v t Formula.:=: substTerm x v u
subst _ _ e@(Const _) = e
subst x v (Binop op e1 e2) = Binop op (subst x v e1) (subst x v e2)
subst x v (Not e) = Not (subst x v e)
subst x v (Quant q y e) | x == y = Quant q y e
                        | otherwise = Quant q y (subst x v e)

substTerm :: Atom -> Term -> Term -> Term
substTerm x v (y :@: []) | y == x = v
substTerm x v (f :@: xs) | f == x = error "can't substitute for a function"
                         | otherwise = f :@: map (substTerm x v) xs

noConjectures :: Formula -> Formula
noConjectures formula = formula { forms = map f (forms formula) }
  where f (name, Conjecture, e) = (name, NegatedConjecture, Not e)
        f fm = fm

awayWithImplication :: Formula -> Formula
awayWithImplication = onFormula go
  where go e@(Literal _) = e
        go e@(_ Formula.:=: _) = e
        go e@(Const _) = e
        go (Binop Implies e1 e2) = e1 `implies` e2
        go (Binop Equiv e1 e2) = Binop And (e1 `implies` e2) (e2 `implies` e1)
        go (Binop op e1 e2) = Binop op (go e1) (go e2)
        go (Not e) = Not (go e)
        go (Quant q x e) = Quant q x (go e)
        e1 `implies` e2 = Binop Or (Not (go e1)) (go e2)

pushNotInwards :: Formula -> Formula
pushNotInwards = onFormula go
  where go e@(Literal _) = e
        go e@(_ Formula.:=: _) = e
        go e@(Const _) = e
        go (Binop op e1 e2) = Binop op (go e1) (go e2)
        go (Quant q x e) = Quant q x (go e)
        go (Not e) = not e

        not (Const True) = Const False
        not (Const False) = Const True
        not e@(Literal _) = Not e
        not e@(_ Formula.:=: _) = Not e
        not (Binop op e1 e2) = Binop (dual op) (not e1) (not e2)
          where dual And = Or
                dual Or = And
        not (Not e) = go e
        not (Quant q x e) = Quant (dual q) x (not e)
          where dual ForAll = Exists
                dual Exists = ForAll


skolemize :: Formula -> Formula
skolemize e = e' { Formula.constants = Formula.constants e' ++ skolemFunctions }
  where (e', skolemFunctions) = runWriter (onFormulaM (go []) e)
        go _ e@(Literal _) = return e
        go _ e@(_ Formula.:=: _) = return e
        go _ e@(Const _) = return e
        go ctx (Binop op e1 e2) = liftM2 (Binop op) (go ctx e1) (go ctx e2)
        go ctx (Not e) = fmap Not (go ctx e)
        go ctx (Quant ForAll x e) = fmap (Quant ForAll x) (go (x:ctx) e)
        go ctx (Quant Exists x e) = do
          e' <- go ctx e
          let ctx' = reverse ctx
              f = Fun { name = name x, args = map ty ctx', ty = ty x }
              x' = f :@: map (:@: []) ctx'
          tell [f]
          return (subst x x' e')

killForAll :: Formula -> Formula
killForAll = onFormula go
  where go e@(Literal _) = e
        go e@(_ Formula.:=: _) = e
        go e@(Const _) = e
        go (Binop op e1 e2) = Binop op (go e1) (go e2)
        go (Not e) = Not (go e)
        go (Quant ForAll x e) = go e

cnf :: Formula -> CNF
cnf e = CNF { types = Formula.types e,
              constants = Formula.constants e,
              clauses = concatMap (map clause . go . formula) (forms e) }
  where formula (_, Conjecture, e) = error "cnf: Conjecture found"
        formula (_, _, e) = e
        go (Const True) = []
        go (Const False) = [[]]
        go (Literal l) = [[Pos l]]
        go (t1 Formula.:=: t2) = [[t1 :=: t2]]
        go (Not (Literal l)) = [[Neg l]]
        go (Not (t1 Formula.:=: t2)) = [[t1 :/=: t2]]
        go (Binop And e1 e2) = go e1 ++ go e2
        go (Binop Or e1 e2) = [ c1 ++ c2 | c1 <- go e1, c2 <- go e2 ]
        clause ls = Clause { vars = nubSort (concatMap litVars ls),
                             literals = ls }
        litVars (Pos l) = vars l
        litVars (Neg l) = vars l
        litVars (t1 :=: t2) = vars t1 ++ vars t2
        litVars (t1 :/=: t2) = vars t1 ++ vars t2
        vars (f@Var{} :@: ts) = f:concatMap vars ts
        vars (_:@:ts) = concatMap vars ts

clausify :: Formula -> CNF
clausify = cnf . killForAll . skolemize . alphaRename . pushNotInwards . awayWithImplication . noConjectures
