module Infinox.Auto where
import Data.Set as S( Set )
import qualified Data.Set as S
import Form
import Name hiding (eq)
import Data.List
import Infinox.Conjecture
import qualified Infinox.Symbols as Sym
import System.IO
import Infinox.Util
import Output

import Control.Monad.Reader
import Infinox.Settings


--metoden funkar inte för testfil:

--(Testa med annan teorembevisare??)

{-


fof(a_0, axiom, ![Y] : (![X] : ((X = Y | f(X) != f(Y)) | ~dom(X)) | ~dom(Y))).
fof(a_1, axiom, ![V] : (f(V) != sk2 | ~dom(V))).

fof(a_2, axiom, dom(sk2)).
fof(a_3, axiom, ![X] : (f(X) = app(fun_f,X) | ~dom(X))).

fof(a3, axiom, ![X] : (![F] : (dom(X) => dom(app(F,X))))).



fof(c, conjecture, ?[F] :
 ( ![X] :
      (dom(X) => dom(app(F,X)))
 & ?[Z] :
     (dom(Z) & ![X] :
                    (dom(X) => app(F,X) != Z)
     )
 & ![X] :
     (dom(X) => ![Y] :
                    (dom(Y) => (X = Y | app(F,X) != app(F,Y)))
     )
 )).

-}

continueAuto :: Settings Result
continueAuto = do
        settings <- ask
        let
                fs                                              = forms settings
                ss                                              = symbols fs
                giveup        = or [arity s > 5 | s <- S.toList ss] --if any symbol has arity > 5  - just give up!
                noClash'                        = noClash settings
                tempdir'                        = tempdir settings

        if giveup then return None
                else
                        do
                                let
                                        constants               = S.toList $ S.filter isConstantSymbol ss
                                        domclauses              = addDomains domain constants fs
                                                                --for each constant c occuring in the problem, add a clause dom(c),
                                                                --where dom is a predicate symbol not occuring elsewhere in the problem.
                                                                --for each clause C, construct dom(x1) & ... & dom(xn) => C, where x1,..xn are all
                                                                --variables occuring in C.
                                        funsymbs                = S.toList (S.filter isFunSymbol ss)
                                        app                             = Fun ((name ("app_" ++ noClash')) ::: ((take 2 (repeat top)) :-> bool)) (take 2 [x | x <- variables])
                                        appclauses      = addAppClauses funsymbs app domain noClash'
                                                                        --for each function f, add the clause f(X) = app(f,X), etc..
                                        closeFuns               = addCloseClauses funsymbs domain
                                        domain                  = prd ((name ("dom_" ++ noClash')) ::: ([top] :-> bool)) [Var ((name "X") ::: V top)]
                                        axioms                  = form2axioms (domclauses ++ appclauses ++ closeFuns) noClash'
                                        axiomfile       = tempdir' ++ "axiomfile2"

                                liftIO $ do
                                                h <- openFile axiomfile WriteMode
                                                hSetBuffering h NoBuffering
                                                hPutStr h axioms
                                                hClose h
                                                b <- equinoxprove (mkConjecture (Atom domain) noClash' ) axiomfile
                                                if b then return Some else return None

addDomains :: Atom ->  [Symbol] -> [Form] -> [Form]
addDomains domain constants fs =
                case fs of
                        []                      -> [Atom (domain @@ [Fun c []]) | c <- constants]
                        --dom(c) for all constants c
                        (f:fs)  -> (applyDomainsToVars domain f) : (addDomains domain constants fs)

addCloseClauses :: [Symbol] -> Atom -> [Form]
addCloseClauses [] _  = []
addCloseClauses (s:ss) domain  = if arity s < 1 then addCloseClauses ss domain else
        ((addCloseClause s domain) : (addCloseClauses ss domain))
        where
                addCloseClause s domain =
                        let
                                a               = arity s
                                vars    = take a variables
                        in
                        forEvery vars $ Or $ S.fromList ((Atom (domain @@ [Fun s vars])):[Not (Atom (domain @@ [v])) | v <- vars])

                --dom(X) => dom(app(s,X))

applyDomainsToVars :: Atom -> Form -> Form
applyDomainsToVars domain f = let appDom = applyDomainsToVars domain in
        case f of
                ForAll (Bind s f')      -> ForAll (Bind s (Or  (S.fromList [Not (Atom (domain @@ [Var s])), appDom f'])))
                Exists (Bind s f')      -> Exists (Bind s (Or  (S.fromList [Not (Atom (domain @@ [Var s])), appDom f'])))
                And fs                                                  -> And $ S.map appDom fs
                Or fs                                                           -> Or $ S.map appDom fs
                f1 `Equiv` f2                           -> (appDom f1) `Equiv` (appDom f2)
                Not f'                                                  -> Not $ appDom f'
                Atom a                                                  -> Atom a
--              Or $ S.insert f $ S.map Not $ S.fromList ([Atom (domain @@ [v]) | v <- vars' a])
--              Or $ S.insert f $ S.map Not $ S.fromList ([Atom (domain @@ [v]) | v <- vars' f])
--              dom(X1) & ... & dom(Xn) => f, where X1,.,Xn are all variable occurences in f.


addAppClauses :: [Symbol] -> Term -> Atom -> String -> [Form]
addAppClauses [] _ _ _ = []
addAppClauses (f@(f' ::: _):fs) app domain noClash
        | arity f < 6 && arity f > 0    =
                let
                        a               = arity f
                        appclauses = addAppClause f a app domain noClash
                 in
                        (map (applyDomainsToVars domain) appclauses) ++ (addAppClauses fs app domain noClash)
        | otherwise     = (addAppClauses fs app domain noClash)

vars' f = map Var $ nub $ filter isVar $ S.toList $ symbols f
isVar (_ ::: V _) = True
isVar _                         = False

addAppClause :: Symbol -> Int -> Term -> Atom -> String -> [Form]
addAppClause s@(n ::: _) ar app domain noClash =
        let
                vars    = permutations (take ar variables)
                fun     i = Fun ((name ("fun" ++ noClash ++ "_" ++ show i ++ normalName noClash n)) ::: ((take (ar-1) (repeat top)) :-> top)) (take (ar-1) variables)
                mkAppTerms _ [] = []
                mkAppTerms i (v:vs) = (app @@ [((fun i) @@ (take (ar-1) variables)), variables !! (ar-1)]):(mkAppTerms (i+1) vs)
        in
                [forEvery (vars) (Atom ((Fun s args) :=: apps)) | (args,apps) <- zip vars (mkAppTerms 1 vars)]


variables = map toVar ["X","Y","Z","V","W"]
toVar :: String -> Term
toVar s = Var ((name s) ::: (V top))

mkConjecture domain noClash =
        let
                app = Fun ((name ("app_" ++ noClash)) ::: ([top,top] :-> top)) [x,y]
                x = toVar "X"
                y = toVar "Y"
                f = toVar "F"
                z = toVar "Z"
        in
        "fof(" ++ "c, " ++ "conjecture" ++
                        ", (" ++
        "?[F] : (" ++
                        "![X] :  (" ++ show ((nt domain) \/ (domain @@ [(app @@ [f,x])])) ++
                        ") & " ++
                        "((![X] : (![Y] :  (" ++ show ((nt domain) \/ (nt (domain @@ [y]))
                                                                                                                \/
                                                                                                                (x `eq` y) \/  (nt ((app @@ [f,x]) `eq` (app @@ [f,y])))) ++
                        " & " ++
                        "(?[Z] : (" ++ show ((domain @@ [z]) /\
                                                                                        ((nt domain) \/ (nt (app @@ [f,x] `eq` z)))) ++
                        ")))))))))."

eq t1 t2 = Atom (t1 :=: t2)

