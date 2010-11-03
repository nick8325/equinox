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
import SmellySox.Formula (Type,typeOf)
import Maybe

isMonotone :: CNF -> Type -> IO Bool
isMonotone cnf ty = do
  r <- solve (formula cnf ty)
  return $ isJust r

formula :: CNF -> Type -> Formula String
formula (CNF ts cs cls) ty   = conj $ map (flip clause ty) cls 

clause :: Clause -> Type -> Formula String 
clause (Clause vars lits) ty = disj $ map (flip literal ty) lits

literal :: Literal -> Type -> Formula String
literal l ty = 
  case l of (t1 :=: t2)  -> if typeOf t1 /= ty then FTrue
                             else safe t1 :&: safe t2
            (t1 :/=: t2) -> undefined
            (Pos t1)     -> undefined
            (Neg t1)     -> undefined


safe = undefined


