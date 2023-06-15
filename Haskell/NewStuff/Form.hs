module Form where

-- HOF

data Expr
  = Expr :@ Expr
  | Lambda Symbol Expr
  | Symbol Symbol
  | Expr := Expr
  | Expr :& Expr
  | Neg Expr
  | Truth
 deriving ( Eq, Ord )

data Symbol
  = Name ::: Type
 deriving ( Eq, Ord )

forAll :: Symbol -> Expr -> Expr
forAll x p = Lambda x p := Lambda x Truth

(/\) :: Expr -> Expr -> Expr
p /\ q = conj :@ p :@ q

type Name
  = String

data Type
  = Base Name -- more info here
  | Type :-> Type
 deriving ( Eq, Ord )

ind, bool :: Type
ind  = Base "$i"
bool = Base "$o"

-- FOF

data Form
  = Term :=: Term
  | Not Form
  | Form :&: Form
  | Form :|: Form
  | ForAll Symbol Form
  | Exists Symbol Form
  | Bool Bool

data Term
  = Fun Symbol [Term]
  | Var Symbol

