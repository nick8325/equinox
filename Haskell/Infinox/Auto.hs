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
		constants 		= S.toList $ S.filter isConstantSymbol ss
		domclauses 		= addDomains domain constants fs 
								--for each constant c occuring in the problem, add a clause dom(c),
								--where dom is a predicate symbol not occuring elsewhere in the problem.
								--for each clause C, construct dom(x1) & ... & dom(xn) => C, where x1,..xn are all 
								--variables occuring in C.
		funsymbs		= S.toList (S.filter isFunSymbol ss)
		app 				= Fun ((name ("app_" ++ noClash)) ::: ((take 2 (repeat top)) :-> bool)) (take 2 [x | x <- variables]) 
		appclauses 	= addAppClauses funsymbs app domain noClash
									--for each function f, add the clause f(X) = app(f,X), etc..			
		closeFuns		= addCloseClauses funsymbs domain 	
		domain 			= prd ((name ("dom_" ++ noClash)) ::: ([top] :-> bool)) [Var ((name "X") ::: V top)]
		axioms 			= form2axioms (domclauses ++ appclauses ++ closeFuns ) noClash
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

addCloseClauses :: [Symbol] -> Atom -> [Form]
addCloseClauses [] _  = []
addCloseClauses (s:ss) domain  = if arity s < 1 then addCloseClauses ss domain else
	((addCloseClause s domain) : (addCloseClauses ss domain))
	where
		addCloseClause s domain = 
			let 
				a 		= arity s 
				vars 	= take a variables 
			in
			forEvery vars $ Or $ S.fromList ((Atom (domain @@ [Fun s vars])):[Not (Atom (domain @@ [v])) | v <- vars])
			
		--dom(X) => dom(app(s,X))

applyDomainsToVars :: Atom -> Form -> Form	
applyDomainsToVars domain f = let appDom = applyDomainsToVars domain in
	case f of
		ForAll (Bind s f') 	-> ForAll (Bind s (Or  (S.fromList [Not (Atom (domain @@ [Var s])), appDom f'])))
		Exists (Bind s f') 	-> Exists (Bind s (Or  (S.fromList [Not (Atom (domain @@ [Var s])), appDom f'])))
		And fs			 				-> And $ S.map appDom fs
		Or fs				 				-> Or $ S.map appDom fs
		f1 `Equiv` f2			 	-> (appDom f1) `Equiv` (appDom f2)		
		Not f'						 	-> Not $ appDom f'
		Atom a							-> Atom a --Or $ S.insert f $ S.map Not $ S.fromList ([Atom (domain @@ [v]) | v <- vars' a])
--		Or $ S.insert f $ S.map Not $ S.fromList ([Atom (domain @@ [v]) | v <- vars' f])
			--dom(X1) & ... & dom(Xn) => f, where X1,.,Xn are all variable occurences in f.


addAppClauses :: [Symbol] -> Term -> Atom -> String -> [Form]
addAppClauses [] _ _ _ = []
addAppClauses (f@(f' ::: _):fs) app domain noClash   
	| arity f < 6 && arity f > 0  	= 
		let 
			a		= arity f			
			appclauses = addAppClause f a app domain noClash 
		 in
			(map (applyDomainsToVars domain) appclauses) ++ (addAppClauses fs app domain noClash) 
	| otherwise   	= (addAppClauses fs app domain noClash)

vars' f = map Var $ nub $ filter isVar $ S.toList $ symbols f
isVar (_ ::: V _) = True
isVar _ 			= False

addAppClause :: Symbol -> Int -> Term -> Atom -> String -> [Form]
addAppClause s@(n ::: _) ar app domain noClash =  
	let 
		vars 	= permutations (take ar variables) 
		fun	i = Fun ((name ("fun" ++ noClash ++ "_" ++ show i ++ normalName noClash n)) ::: ((take (ar-1) (repeat top)) :-> top)) (take (ar-1) variables)
		mkAppTerms _ [] = []
		mkAppTerms i (v:vs) = (app @@ [((fun i) @@ (take (ar-1) variables)), variables !! (ar-1)]):(mkAppTerms (i+1) vs) 
	in
		[forEvery (vars) (Atom ((Fun s args) :=: apps)) | (args,apps) <- zip vars (mkAppTerms 1 vars)]


variables = map toVar ["X","Y","Z","V","W"]
toVar :: String -> Term
toVar s = Var ((name s) ::: (V top)) 

mkConjecture domain noClash = 
	let 
		x = toVar "X"
		y = toVar "Y"
		f = toVar "F"
		z = toVar "Z"
		app = Fun ((name ("app_" ++ noClash)) ::: ([top,top] :-> top)) [x,y] 
	in
	form2conjecture noClash 0 $
		exists Sym.f $
			forEvery (Var Sym.x) $ forEvery (Var Sym.y) (
				(nt domain) \/ (nt (domain @@ [y])) 
				\/
				(x `eq` y) \/  (nt ((app @@ [f,x]) `eq` (app @@ [f,y]))) 
			)
			/\
			(exists Sym.z $ (domain @@ [z]) /\
				((nt domain) \/ (nt (app @@ [f,x] `eq` z))))
				



{-
		exists Sym.f $ exists Sym.z ((domain @@ [z]) /\  (
			forEvery (Var Sym.x) $ forEvery (Var Sym.y) $
				(nt domain) \/ (nt (domain @@ [y])) \/ 

			(((x `eq` y) \/  (nt ((app @@ [f,x]) `eq` (app @@ [f,y]))))
		
				/\
			(
				(nt (app @@ [f,x] `eq` z))))
		))
-}
--		 \/ --or Surjective and non injective...
--				(exists Sym.x $ exists Sym.y $ domain /\ domain @@ [y] 
--			  	/\ (x `eq` y) /\ ((app @@ [f,x]) `eq` (app @@ [f,y]))
--				 /\
--				(forEvery [Var Sym.z] $ (nt (domain @@ [z])) \/ (exists Sym.x $ (domain @@ [x]) /\ (app @@ [f,x] `eq` z))))

eq t1 t2 = Atom (t1 :=: t2)

{-
fof(conjecture,conjecture, (
  ?[F] : ( (![X,Y] : ((dom(X) & dom(Y)) => (app(F,X) = app(F,Y) => X=Y)))
         & (?[A] : (dom(A) & ![X] : (dom(X) => app(F,X) != A)))
         )
)).
-}

{-
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
-}	

{-
		ForAll (Bind s f') 	-> ForAll (Bind s (appDom f'))
		Exists (Bind s f') 	-> Exists (Bind s (appDom f'))
		And fs			 				-> And $ S.map appDom fs
		Or fs				 				-> Or $ S.map appDom fs
		f1 `Equiv` f2			 	-> (appDom f1) `Equiv` (appDom f2)		
		Not f'						 	-> Not $ appDom f'
		Atom a							-> Or $ S.insert f $ S.map Not $ S.fromList ([Atom (domain @@ [v]) | v <- vars' a])
--			Or $ S.insert f $ S.map Not $ S.fromList ([Atom (domain @@ [v]) | v <- vars' f])
			--dom(X1) & ... & dom(Xn) => f, where X1,.,Xn are all variable occurences in f.
-}




