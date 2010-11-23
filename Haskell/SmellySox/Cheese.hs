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
import SmellySox.Formula hiding (Not, (:=:), constants)
import Data.List
import Maybe

data ExtensionVar = FalseExtended Atom | TrueExtended Atom deriving (Eq, Ord)
data Method = FalseExtend | TrueExtend | Copy deriving Show

isMonotone :: CNF -> Type -> IO (Maybe [(Atom, Method)])
isMonotone cnf (Type "$int") = return (Just []) -- hack hack
isMonotone cnf ty = do
  r <- solve (formula cnf ty)
  case r of
    Nothing -> return Nothing
    Just val -> return (Just [(p, method p) | p@Pred{} <- constants cnf, args p == [ty]])
      where method p =
              case (val (FalseExtended p), val (TrueExtended p)) of
                (False, False) -> Copy
                (False, True) -> TrueExtend
                (True, False) -> FalseExtend
                (True, True)  -> error "OH NO!! D:"

formula :: CNF -> Type -> SatFormula ExtensionVar
formula (CNF ts cs cls) ty = conj $ map (flip clause ty) cls ++ map constraint cs
  where constraint p@Pred{} | args p == [ty] = Not (SatVar (TrueExtended p) :&: SatVar (FalseExtended p))
        constraint _ = FTrue

clause :: Clause -> Type -> SatFormula ExtensionVar
clause c@(Clause vars lits) ty = conj $ map (flip (literal c) ty) lits

guards (_ :=: _)  _               = FFalse
guards (_ :/=: _) _               = FFalse
guards (Pos (p :@: [y :@: []])) x = if x == y then SatVar (TrueExtended p) else FFalse
guards (Neg (p :@: [y :@: []])) x = if x == y then SatVar (FalseExtended p) else FFalse
guards (Pos _) _                  = FFalse
guards (Neg _) _                  = FFalse

literal :: Clause -> Literal -> Type -> SatFormula ExtensionVar
literal c l ty = 
  case l of (t1 :=: t2)  -> if typeOf t1 /= ty then FTrue
                             else safe c t1 :&: safe c t2
            (t1 :/=: t2) -> FTrue
            (Pos (p :@: [x])) | typeOf x /= ty -> FTrue
            (Neg (p :@: [x])) | typeOf x /= ty -> FTrue
            (Pos (p :@: [x])) -> Not (SatVar (FalseExtended p)) :|: safe c x
            (Neg (p :@: [x])) -> Not (SatVar (TrueExtended p))  :|: safe c x
            _ -> FTrue

safe c (x@Var{} :@: []) = disj [ guards l x | l <- literals c ]
safe _ _ = FTrue
