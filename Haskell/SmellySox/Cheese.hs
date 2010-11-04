module SmellySox.Cheese where

{- Monotonicity calculus

   Formulas: 

   K |- C1, ... K |- Cn
   -----------------------  (alpha)
   K |- C1 & ... & Cn

   _________________________________________________________________________________

   Clauses:

   G = union {guarded L1 K,...,guarded Lm K},   G ,K |- L1, ... G,K |- Lm
   -----------------------------------------------------------------------  (alpha)
   K |- L1 | ... | Lm

   guarded :: Literal -> Context -> {Var}

   _________________________________________________________________________________

   Literals:

   G,K |- L    (alpha, ~S)
   ---------- 
   G,K |- ~L   (alpha,S)

    
   ------------- (alpha, -)
   G,K |- t = u

    
   t,u have type b != alpha
   ------------------------- (alpha, +)
   G,K |- t = u  
 

   safe(G,t)  safe(G,u)  t,u have type alpha
   ------------------------------------------ (alpha, +)
   G,K |- t = u


   K(p) = "copy" | (safe(G,t1) & ... & safe(G,tn))
   ------------------------------------------------ (alpha,+)
   K,G |- p(t1,...,tn)

   
   -------------------- (alpha,-)
   K,G |- p(t1,...,tn)


   safe(G,t) = isVar(t) ==> elem t G 


-}

import SmellySox.Sat hiding ((:=:))
import SmellySox.CNF
import SmellySox.Formula (Type,getArgs,typeOf,isVar) 
import Data.List
import Maybe

isMonotone :: CNF -> Type -> IO Bool
isMonotone cnf ty = do
  r <- solve (formula cnf ty)
  return $ isJust r

formula :: CNF -> Type -> Formula String
formula (CNF ts cs cls) ty   = conj $ map (flip clause ty) cls 

clause :: Clause -> Type -> Formula String 
clause (Clause vars lits) ty = 
  let
      (neqs,eqs) = partition (badEquality ty) lits 
  in
    if null eqs then FTrue else conj $ map (guard ty neqs) eqs

badEquality ty (t1 :=: t2) = typeOf t1 == ty && (isVar t1 || isVar t2)
badEquality _ _            = False

guard ty neqs (t1 :=: t2) = undefined

guards ty (_ :=: _)  _              = FFalse
guards ty (_ :/=: _) _              = FFalse
guards ty (Pos p)  x    = if elem x (getArgs p) then undefined else FFalse
guards ty (Neg p)  x    = if elem x (getArgs p) then undefined else FFalse






literal :: Literal -> Type -> Formula String
literal l ty = 
  case l of (t1 :=: t2)  -> if typeOf t1 /= ty then FTrue
                             else safe t1 :&: safe t2
            (t1 :/=: t2) -> FTrue
            (Pos t1)     -> undefined
            (Neg t1)     -> undefined

safe t = if not (isVar t) then FTrue else undefined


