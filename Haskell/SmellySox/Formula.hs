module SmellySox.Formula where

import Data.List

data Type = Top | Type String deriving (Eq, Ord)
data Atom = Fun { name :: String, args :: [Type], ty :: Type }
          | Pred { name :: String, args :: [Type] }
          | Var { name :: String, ty :: Type } deriving (Eq, Ord)
data Term = Atom :@: [Term]
  deriving Eq

data Binop = And | Or | Implies | Equiv
  deriving Eq

data Quant = ForAll | Exists
  deriving Eq


instance Show Type where
  show Top = "$i"
  show (Type ty) = ty

instance Show Atom where
  show = name

typeOf :: Term -> Type
typeOf ((Fun _ _ ty) :@: _) = ty
typeOf ((Var _ ty) :@: _)   = ty

isVar :: Term -> Bool
isVar ((Var _ _) :@: _) = True
isVar _           = False

getArgs :: Term -> [Term]
getArgs (_ :@: ts) = ts

showTypedAtom :: Atom -> String
showTypedAtom f@Fun{} = name f ++ " : " ++ showArgs (args f) ++ show (ty f)
showTypedAtom p@Pred{} = name p ++ " : " ++ showArgs (args p) ++ "$o"
showTypedAtom v@Var{} = name v ++ ":" ++ show (ty v)

showArgs [] = ""
showArgs [ty] = show ty ++ " -> "
showArgs tys = "(" ++ intercalate ", " (map show tys) ++ ") -> "

instance Show Term where
  show (x :@: []) = show x
  show (f :@: ts) = show f ++ "(" ++ intercalate "," (map show ts) ++ ")"

infix :@:
infix 8 :=:

data Form = Const Bool
          | Literal Term
          | Term :=: Term
          | Binop Binop Form Form
          | Not Form
          | Quant Quant Atom Form


data Kind = Axiom | Hypothesis | Definition | Conjecture | NegatedConjecture

data Formula = Formula { types :: [Type], constants :: [Atom], forms :: [(String, Kind, Form)] }

onFormula :: (Form -> Form) -> Formula -> Formula
onFormula f formula = formula { forms = [ (name, kind, f form) | (name, kind, form) <- forms formula ] }

onFormulaM :: Monad m => (Form -> m Form) -> Formula -> m Formula
onFormulaM f formula = do
  result <- sequence [ f form | (_, _, form) <- forms formula ]
  return formula{ forms = [ (name, kind, form') | ((name, kind, _), form') <- zip (forms formula) result ]}
