module SmellySox.BNFC where

import SmellySox.Parser.Abstff
import SmellySox.Parser.Lextff
import SmellySox.Parser.Partff
import SmellySox.Parser.ErrM
import SmellySox.Formula
import qualified Data.Map as Map

parseString :: String -> String -> Tffs
parseString name s =
  case pTffs (myLexer s) of
    Bad s -> error $ "Parse error in " ++ name ++ ": " ++ show s
    Ok t -> t

preprocess :: Tffs -> IO Tffs
preprocess (Tffs xs) = fmap (Tffs . concat) (mapM preprocess1 xs)
  where preprocess1 (TffIncl (FPath file)) = fmap unTffs (readFile (strip file) >>= preprocess . parseString file)
        preprocess1 x = return [x]
        unTffs (Tffs xs) = xs
        strip name = filter (/= '\'') name

convert :: Tffs -> Formula
convert (Tffs xs) = Formula { types = types, constants = constants, forms = forms }
  where types = [ Type ty | TffTyp _ (LIdent ty) TypTyp <- xs ] ++
                [ Type ty | TffTyp2 _ (LIdent ty) TypTyp <- xs ]
        constants = [ convertType f ty | TffTyp _ (LIdent f) ty <- xs, ty /= TypTyp ] ++
                    [ convertType f ty | TffTyp2 _ (LIdent f) ty <- xs, ty /= TypTyp ]
        forms = [ (axIdent name, convertKind kind, typecheck (retype (convertExpr expr)))
                | Tff name kind expr <- xs ]
        axIdent (AxLIdent (LIdent s)) = s
        axIdent (AxUIdent (UIdent s)) = s
        axIdent (AxInt n) = show n
        axIdent AxInclude = "include"
        axIdent AxTff = "tff"
        axIdent AxType = "type"
        axIdent AxDefinition = "definition"
        axIdent AxAxiom = "axiom"
        axIdent AxHypothesis = "hypothesis"
        axIdent AxConjecture = "conjecture"
        axIdent AxNegatedConjecture = "negated_conjecture"
        axIdent AxTrue = "$true"
        axIdent AxFalse = "$false"
        axIdent AxI = "$i"
        axIdent AxO = "$o"
        axIdent AxTtype = "$tType"
        convertType _ TypTyp = error "convert: unexpected $tType"
        convertType b TypBool = Pred { name = b, args = [] }
        convertType x (TypConst ty) = Fun { name = x, args = [], ty = convertBaseType ty }
        convertType p (TypPred args) = Pred { name = p, args = convertArgs args }
        convertType f (TypFun args ty) = Fun { name = f, args = convertArgs args, ty = convertBaseType ty }
        convertArgs (OneArg ty) = [convertBaseType ty]
        convertArgs (SomeArgs tys) = [ convertBaseType ty | Arg ty <- tys ]
        convertBaseType TypTop = error "$i not supported, GO AWAY"
        convertBaseType (TypIdent (LIdent ty)) = Type ty
        convertKind CTDef = Definition
        convertKind CTAxiom = Axiom
        convertKind CTHyp = Hypothesis
        convertKind CTConj = Conjecture
        convertKind CTNegConj = NegatedConjecture
        convertExpr (EOr e1 e2) = Binop Or (convertExpr e1) (convertExpr e2)
        convertExpr (EAnd e1 e2) = Binop And (convertExpr e1) (convertExpr e2)
        convertExpr (EImplies e1 e2) = Binop Implies (convertExpr e1) (convertExpr e2)
        convertExpr (EEquiv e1 e2) = Binop Equiv (convertExpr e1) (convertExpr e2)
        convertExpr (EEq t u) = convertTerm t :=: convertTerm u
        convertExpr (ENeq t u) = Not (convertTerm t :=: convertTerm u)
        convertExpr (EForAll xs e) = foldr (quant ForAll) (convertExpr e) xs
        convertExpr (EExists xs e) = foldr (quant Exists) (convertExpr e) xs
        convertExpr (ENeg e) = Not (convertExpr e)
        convertExpr ETrue = Const True
        convertExpr EFalse = Const False
        convertExpr (ELit a) = Literal (convertAtom a)
        convertTerm (TConst (LIdent x)) = mkFun x :@: []
        convertTerm (TVar (UIdent x)) = mkVar x :@: []
        convertTerm (TFun (LIdent f) xs) = mkFun f :@: map convertTerm xs
        convertTerm (TInt x) = iterate suc zero !! fromInteger x
          where suc t = mkFun "$succ" :@: [t]
                zero = mkFun "$zero" :@: []
        convertTerm (TNegInt x) =
          mkFun "$uminus" :@: [convertTerm (TInt x)]
        convertAtom (APred (LIdent p) xs) = mkPred p :@: map convertTerm xs
        convertAtom (AConst (LIdent p)) = mkPred p :@: []

        quant q (ETyp (UIdent x) (TypConst ty)) = Quant q Var{name = x, ty = convertBaseType ty}
        quant _ (ETyp (UIdent _) _) = error "quantified over higher-order type"

        mkFun x = Fun { name = x, args = error "mkFun", ty = error "mkFun" }
        mkVar x = Var { name = x, ty = error "mkFun" }
        mkPred x = Pred { name = x, args = error "mkFun" }

        retype = retypeFrom (Map.fromList [(name k, k) | k <- constants])
        retypeFrom ctx e@(Const _) = e
        retypeFrom ctx (Literal t) = Literal (retypeTerm ctx t)
        retypeFrom ctx (t :=: u) = retypeTerm ctx t :=: retypeTerm ctx u
        retypeFrom ctx (Binop op e1 e2) = Binop op (retypeFrom ctx e1) (retypeFrom ctx e2)
        retypeFrom ctx (Not e) = Not (retypeFrom ctx e)
        retypeFrom ctx (Quant q x e) = Quant q x (retypeFrom (Map.insert (name x) x ctx) e)
        retypeTerm ctx (f :@: xs) =
          Map.findWithDefault (error $ "unknown term " ++ name f) (name f) ctx :@:
             map (retypeTerm ctx) xs

        typecheck e@(Const _) = e
        typecheck e@(Literal l) | typeOf l == Type "$o" = e
                                | otherwise = error $ show l ++ " has type " ++ show (typeOf l) ++ " but was used as a predicate"
        typecheck e@(t :=: u) | typeOf t == typeOf u = e
                              | otherwise = error $ "Type mismatch in " ++ show t ++ " = " ++ show u ++ ": " ++ show (typeOf t) ++  " vs " ++ show (typeOf u)
        typecheck (Binop op e1 e2) = Binop op (typecheck e1) (typecheck e2)
        typecheck (Not e) = Not (typecheck e)
        typecheck (Quant q x e) = Quant q x (typecheck e)
        typeOf (x@Var{} :@: []) = ty x
        typeOf l@(Var{} :@: _) = error $ "Variable used as head of literal: " ++ show l
        typeOf l@(p@Pred{} :@: xs) | map typeOf xs == args p = Type "$o"
                                   | otherwise = error $ "Type mismatch in " ++ show l ++ ": " ++ show p ++ " has argument type " ++ show (args p) ++ " but was given " ++ show (map typeOf xs)

        typeOf l@(f@Fun{} :@: xs) | map typeOf xs == args f = ty f
                                  | otherwise = error $ "Type mismatch in " ++ show l ++ ": " ++ show f ++ " has argument type " ++ show (args f) ++ " but was given " ++ show (map typeOf xs)
