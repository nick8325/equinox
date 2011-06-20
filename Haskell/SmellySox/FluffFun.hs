module SmellySox.FluffFun where

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
  let typingFun ty = Fun { name = "smellySox_" ++ show ty,
                           args = [ty],
                           ty = ty }
      transform e@Const{} = e
      transform e@Literal{} = e
      transform (t :=: u) = transformTerm t :=: transformTerm u
      transform (Binop op e1 e2) = Binop op (transform e1) (transform e2)
      transform (Not e) = Not (transform e)
      -- We might think that we should translate exists x p into
      -- exists x (t(x)=x & p). But this way is OK too because when
      -- deciding whether to guard a variable we don't pay any
      -- attention to how it was bound: it always gets turned into
      -- t(x) if it appears in an unsafe position.
      transform (Quant q x e) = Quant q x (transform e)
      transformTerm (v@Var{} :@: []) | ty v `Set.member` nonMonotone =
                                       typingFun (ty v) :@: [v :@: []]
      transformTerm (f :@: xs) = f :@: xs
      constants' = map typingFun (Set.toList nonMonotone) ++ constants formula
      typingAxiom f = foldr (Quant ForAll) axiom vars
        where vars = [ Var{name = "SmellySox" ++ show i, ty = ty} | (ty, i) <- zip (args f) [1..] ]
              axiom = 
                foldr (Binop And) resultAxiom
                      [(f :@: map (:@: []) vars) `eq`
                        (f :@: (map (:@: []) prefix ++ 
                                [typingFun (ty v) :@: [v :@: []]] ++
                                map (:@: []) suffix))
                      | n <- [0..length vars-1],
                        let (prefix, (v:suffix)) = splitAt n vars,
                        ty v `Set.member` nonMonotone
                      ]
              resultAxiom =
                case f of
                  Fun{} | ty f `Set.member` nonMonotone ->
                    f :@: map (:@: []) vars :=:
                      typingFun (ty f) :@: [f :@: map (:@: []) vars]
                  _ -> Const True
              eq =
                case f of
                  Pred{} -> \t u -> Binop Equiv (Literal t) (Literal u)
                  Fun{} -> (:=:)
  return formula{constants = constants',
                 forms = [ (name, kind, transform e) | (name, kind, e) <- forms formula ] ++
                         [ ("smellySox_" ++ name f, Axiom, typingAxiom f) | f <- constants' ] }

