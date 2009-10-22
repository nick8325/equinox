module Infinox.Auto where
import Data.Set as S( Set )
import qualified Data.Set as S
import Form
import Name hiding (eq)
import Data.List
import Infinox.Conjecture
import qualified Infinox.Symbols as Sym
import IO
import Infinox.Util
import Output

continueAuto tempdir noClash fs sig rflag pflag verbose = do
	let 
		ss 						= symbols fs
		constants 		=  S.toList $ S.filter isConstantSymbol ss
		domclauses 		= addDomains domain constants fs 
								--for each constant c occuring in the problem, add a clause dom(c),
								--where dom is a predicate symbol not occuring elsewhere in the problem.
								--for each clause C, construct dom(x1) & ... & dom(xn) => C, where x1,..xn are all 
								--variables occuring in C.
		appclauses 	= addAppClauses (S.toList (S.filter isFunSymbol ss)) domain noClash
									--for each function f, add the clause f(X) = app(f,X), etc..						
		domain 			= prd ((name ("dom_" ++ noClash)) ::: ([top] :-> bool)) [Var ((name "X") ::: V top)]
		axioms 			= form2axioms (domclauses ++ appclauses) noClash
		axiomfile 	= tempdir ++ "axiomfile2"
	h <- openFile axiomfile WriteMode			
	hSetBuffering h NoBuffering
	hPutStr h axioms
	hClose h
	b <- prove (mkConjecture (Atom domain) noClash ) axiomfile 600
	if b then return Some else return None

addDomains :: Atom ->  [Symbol] -> [Form] -> [Form] 
addDomains domain constants fs = 
		case fs of	
			[]			-> [Atom (domain @@ [Fun c []]) | c <- constants]
			--dom(c) for all constants c
			(f:fs)	-> (applyDomainsToVars domain f) : (addDomains domain constants fs)
	
applyDomainsToVars domain f =
			Or $ S.insert f $ S.map Not $ S.fromList ([Atom (domain @@ [v]) | v <- vars' f])
			--dom(X1) & ... & dom(Xn) => f, where X1,.,Xn are all variable occurences in f.

addAppClauses :: [Symbol] -> Atom -> String -> [Form]
addAppClauses [] _ _ = []
addAppClauses (f@(f' ::: _):fs) domain noClash   
	| arity f < 6 && arity f > 0  	= 
		let 
			fun	= Fun ((name ("fun" ++ noClash ++ "_" ++ normalName noClash f')) ::: ([] :-> top)) []
			app = Fun ((name ("app_" ++ noClash)) ::: ((take 2 (repeat top)) :-> bool)) (take 2 [x | x <- variables]) 
			appclauses = addAppClause f fun (arity f) app domain noClash 
		 in
			(map (applyDomainsToVars domain) appclauses) ++ (addAppClauses fs domain noClash) 
	| otherwise   	= (addAppClauses fs domain noClash)

vars' f = map Var $ nub $ filter isVar $ S.toList $ symbols f
isVar (_ ::: V _) = True
isVar _ 			= False

mkAppTerm :: Term -> Int -> Term -> Atom -> String -> Maybe Term
mkAppTerm fun a app domain noClash = 
	case a of
		0	-> Nothing
		n -> 
			case mkAppTerm fun (a-1) app domain noClash of
				Nothing 	-> Just $ app @@ [fun, toVar "X"]
				Just t 		-> Just $ app @@ ([t,variables !! (n-1)])   

addAppClause :: Symbol -> Term -> Int -> Term -> Atom -> String -> [Form]
addAppClause f' fun a app domain noClash = 
	case mkAppTerm fun a app domain noClash of
		Just appterm 	-> [Atom $ Fun f' (take a variables) :=: appterm]
		_							-> error "addAppClause"
	
variables = map toVar ["X","Y","Z","V","W"]
toVar :: String -> Term
toVar s = Var ((name s) ::: (V top)) 

mkConjecture domain noClash = 
	let 
		x = toVar "X"
		y = toVar "Y"
		f = toVar "F"
		z = toVar "Z"
		app = Fun ((name ("app_" ++ noClash)) ::: ([top,top] :-> bool)) [x,y] 
	in
	form2conjecture noClash 0 $
		(exists Sym.f $ (forEvery (Var Sym.x) ( forEvery (Var Sym.y) $
			(nt domain) \/ (nt (domain @@ [y])) \/ (x `eq` y) \/ (nt ((app @@ [f,x]) `eq` (app @@ [f,y]))))
		/\
		(exists Sym.z $ domain @@ [z] /\ (forEvery [x] $ (nt (domain @@ [x])) \/ (nt (app @@ [f,x] `eq` z))))))

		 \/ --or Surjective and non injective...
				(exists Sym.x $ exists Sym.y $ domain /\ domain @@ [y] 
			  	/\ (x `eq` y) /\ ((app @@ [f,x]) `eq` (app @@ [f,y]))
				 /\
				(forEvery [Var Sym.z] $ (nt (domain @@ [z])) \/ (exists Sym.x $ (domain @@ [x]) /\ (app @@ [f,x] `eq` z))))

eq t1 t2 = Atom (t1 :=: t2)

{-
fof(conjecture,conjecture, (
  ?[F] : ( (![X,Y] : ((dom(X) & dom(Y)) => (app(F,X) = app(F,Y) => X=Y)))
         & (?[A] : (dom(A) & ![X] : (dom(X) => app(F,X) != A)))
         )
)).
-}



