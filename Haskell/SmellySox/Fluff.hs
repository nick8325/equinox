module SmellySox.Fluff where

import SmellySox.Formula
import SmellySox.CNF hiding (types, (:=:), constants)
import SmellySox.Cheese
import Control.Monad
import qualified Data.Set as Set

annotate :: Formula -> IO Formula
annotate formula = do
  let cnf = clausify formula
  nonMonotone <- fmap Set.fromList . flip filterM (types formula) $ \ty -> do
    r <- isMonotone cnf ty
    case r of
      Nothing -> return True
      Just{} -> return False
  let typingPred ty = Pred { name = "smellySox_" ++ show ty,
                             args = [ty] }
      forAll x e | ty x `Set.member` nonMonotone =
                     Quant ForAll x (Binop Implies (Literal (typingPred (ty x) :@: [x :@: []]))
                                                   e)
                 | otherwise = Quant ForAll x e
      exists x e | ty x `Set.member` nonMonotone =
                     Quant Exists x (Binop And (Literal (typingPred (ty x) :@: [x :@: []]))
                                               e)
                 | otherwise = Quant Exists x e
      transform e@Const{} = e
      transform e@Literal{} = e
      transform e@(_ :=: _) = e
      transform (Binop op e1 e2) = Binop op (transform e1) (transform e2)
      transform (Not e) = Not (transform e)
      transform (Quant ForAll x e) = forAll x (transform e)
      transform (Quant Exists x e) = exists x (transform e)
      typingAxiom ty = ("smellySox_" ++ show ty, Axiom,
                           foldr (Binop And) (Const True)
                             (map functionAxiom [ f | f@Fun{ty = x} <- constants formula,
                                                      x == ty ]))
      functionAxiom f = foldr forAll (Literal (typingPred (ty f) :@: [f :@: map (:@: []) vars])) vars
        where vars = [ Var ("SmellySox" ++ show i) ty | (i, ty) <- zip [1..] (args f) ]
  return formula{constants = map typingPred (Set.toList nonMonotone) ++ constants formula,
                 forms = [ (name, kind, transform e) | (name, kind, e) <- forms formula ] ++
                         map typingAxiom (Set.toList nonMonotone) }
