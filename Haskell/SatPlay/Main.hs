module SatPlay.Main where

import qualified Main
import Sat
import Form
import Name
import List

import Flags
import qualified Data.Set as S


main =
  do putStrLn "SatPlay, version 1.0, 2009-10-02."
     Main.main SatPlay solveProblem
{-
main = --undefined


  run $ do
                lift $ putStrLn "SatPlay, version 1.0, 2009-10-02."
     --Main.main SatPlay solveProblem
                v1 <- newVar 3
                v2 <- newVar 3
                l  <- less v1 v2

                ans <- solve []
                if not ans then do
                        lift (putStrLn "no model!")
                        ls <- conflict
                        lift $ putStrLn $ show ls
                        lift $ return $ NoAnswerClause GaveUp
                 else do
                                lift (putStrLn "model found!")
                                v <- getModelValue v1
                        --      v' <- getModelValue v2
                                v'' <- getModelValue' l
                                --lift $ putStrLn $  show v
                                lift $ putStrLn $ show v''
                                lift $ return Satisfiable

                return ()
-}
getModelValue' (Lit l) = getModelValue l


binary :: Int -> Integer -> Number
binary 0 _              = []
binary k n | even n     = Bool False : binary (k-1) (n `div` 2)
           | otherwise  = Bool True  : binary (k-1) (n `div` 2)

align :: Number -> Number-> (Number,Number)
align (x:xs) (y:ys)
  | not (null xs || null ys)
 || (null xs && null ys)
  = (x:xs',y:ys')
 where
  (xs',ys') = align xs ys
align [] []                      = ([],[])
align [x] (y:ys) | not (null ys) = align [x,x] (y:ys)
align (x:xs) [y] | not (null xs) = align (x:xs) [y,y]
align xs ys = error ("align not defined for " ++ show (length xs, length ys))

varRange        = 3::Int
varValues = map number [0..2^varRange]
coefficientRange = 3::Int

solveProblem :: (?flags :: Flags) => [Clause] -> IO ClauseAnswer
solveProblem cs = run $ do
        let
                funsymbols      = S.toList $ S.filter isFunSymbol $ symbols cs
                predsymbols     = S.toList $ S.filter isPredSymbol $ symbols cs

        funreps         <- makeFunReps funsymbols --funktionssymboler med respektive koefficienter (newVars)
        predreps        <- makePredReps predsymbols
        addConstraints funreps cs
        addPredConstraints predreps cs
        ans <- solve []
        if not ans then do
                        lift (putStrLn "no model!")
                        ls <- conflict
                        lift $ putStrLn $ show ls
                        lift $ return $ NoAnswerClause GaveUp
                 else do
                                lift (putStrLn "Possible model found!")
                                printFuns funreps
                                lift $ return Satisfiable

variables = ["X","Y","Z","V","W"]

makePredReps :: [Symbol] -> S [[(Symbol,[Number])]]
makePredReps [] = return [[]]
makePredReps (x:xs) = do
        let
                a       = arity x
        case a of
                1 -> do
                        v       <- newVar varRange
                        xvs <- makePredReps xs
                        return ([(x,[v])]:xvs)
                _ -> error "Predarity > 1"


makeFunReps :: [Symbol] -> S [(Symbol,[Number])]
--Every function symbol is associated with a list of coefficients
makeFunReps []  = return []
makeFunReps (x:xs) = do
        let a = (arity x) + 1
        vs      <- newVars coefficientRange a
        xvs     <- makeFunReps xs
        return ((x,vs):xvs)

newVars :: Int -> Int -> S [Number]
newVars n 0 = return []
newVars n m = do
        vs <- newVars n (m-1)
        v  <- newVar n
        return (v:vs)

addPredConstraints  :: [[(Symbol, [Number])]] -> [Clause] -> S()
addPredConstraints [] _ = return ()
addPredConstraints (ps:pps) (c:cs) = do
        let
                ps'     = [(s,n) | (s,n) <- ps, elem s (S.toList (symbols c))]
                vars            = nub $ concat [getVarsSigned c' | c' <- c]
                varMap  = varAssigns vars
        addPredConstraint ps' c varMap
        addPredConstraints pps cs

addPredConstraint :: [(Symbol,[Number])] -> Clause -> [[(Symbol,Number)]] -> S ()
addPredConstraint _ _ [] = return () -- Decide what to do here!
addPredConstraint [] _ _ = return ()

varAssigns []           = [[]]
varAssigns (v:vs) =
        let ms = varAssigns vs in -- all possible assignments for the variables that occur in the clause
                concat [map ((v,i) :) ms | i <- varValues]

addConstraints :: [(Symbol,[Number])] -> [Clause] -> S ()
addConstraints _ [] = return ()
addConstraints funreps (c:cs) = do
        let
                vars            = nub $ concat [getVarsSigned c' | c' <- c]
                varMap  = varAssigns vars
        addConstraint funreps c varMap --add the constraints of each clause
        addConstraints funreps cs

addConstraint :: [(Symbol,[Number])] -> [Signed Atom] -> [[(Symbol,Number)]]-> S ()
addConstraint _ _ [] = return ()
addConstraint funreps xs (v:vars)       = do
        cs <- constructClauses funreps xs v
        clause cs --lägger till clause cs för alla möjliga variabeltilldelningar av en klausul.
        addConstraint funreps xs vars

constructClauses :: [(Symbol,[Number])] -> [Signed Atom] -> [(Symbol,Number)] -> S [Bit]
constructClauses _ [] _ = return []
constructClauses funreps (x:xs) vars = do
        b       <- apply x funreps vars
        bs      <- constructClauses funreps xs vars
        return (b:bs)

apply (Neg t) funreps v = do
        b <- apply (Pos t) funreps v
        return $ ng b

apply (Pos (t1 :=: t2)) reps v =
        case (t1,t2) of
                (Var s1, Var s2) -> case lookup s1 v of
                                                                                                        Just n1 -> case lookup s2 v of
                                                                                                                                                        Just n2 -> equal n1 n2
                (Fun s1 ts1,t)  ->
                        if t == truth then return (Bool True) --case lookup s1 reps of --s1 is a pred symbol.
                         else
                                do

                                                args1 <- appArgs ts1 v reps
                                                case lookup s1 reps of
                                                                Just ns1 -> do
                                                                                b1 <- eval ns1 args1
                                                                                b2 <- (case t of
                                                                                                                Var s2          -> case lookup s2 v of
                                                                                                                                                                        Just ns2 -> return ns2
                                                                                                                Fun s2 ts2 ->
                                                                                                                                                                         case lookup s2 reps of
                                                                                                                                                                                Just ns2 -> do
                                                                                                                                                                                        args2 <- appArgs ts2 v reps
                                                                                                                                                                                        eval ns2 args2
                                                                                                                                                                                Nothing         -> error $ show (Fun s1 ts1, t))
                                                                                equal b2 b1
                                                                --Nothing -> return $ Bool True

                (x,y)                                           -> apply (Pos (y :=: x)) reps v


eval :: [Number] -> [Number] -> S Number
eval [c] [] = return c
eval (c:coeffs) (v:vars) = do
        b       <- times c v
        b2      <- eval coeffs vars
        plus b0 b b2

appArgs [] _ _ = return []
appArgs ((Var x):xs) v funreps = case lookup x v of
        Just n  -> do
                ns <- appArgs xs v funreps
                return (n:ns)

appArgs ((Fun f ts):xs) v funreps = case lookup f funreps of
        Just ns -> do
                args    <- appArgs ts v funreps
                n                       <- eval ns args
                xs'             <- appArgs xs v funreps
                return (n:xs')

getVarsSigned (Pos a) = getVarsAtom a
getVarsSigned (Neg a) = getVarsAtom a

getVarsAtom (t1 :=: t2) = nub ((getVarsTerm t1) ++ (getVarsTerm t2))
getVarsTerm (Var x) = [x]
getVarsTerm (Fun _ ts)   = nub $ concat [getVarsTerm v | v <- ts]

printFuns [] = return ()
printFuns ((f,vs):fs) = do
        ns <- mapM getModelNumber vs
        let
                zips = zip ns variables
                vs       = listVars $ take ((length ns) - 1) variables
                listVars [] = ""
                listVars [x] = x
                listVars (x:xs) = x ++ "," ++ listVars xs
                str1 n = show f ++ "(" ++ vs ++ ") = "
                str2 []                                         = ""
                str2 [_]                                 = show $ last ns
                str2 ((z,v):zs) = show z ++ v ++ " + " ++ (str2 zs)
        lift $ putStrLn $ (str1 ((length ns) -1)) ++ (str2 zips)
        printFuns fs



-------------------------------------------------------------------------------

requireEqual :: Number -> Number -> S ()
requireEqual a b = do
        e <- equal a b
        []      ==> [e]

require :: S Bit -> S ()
require constr =
  do b <- constr
     [] ==> [b]

requireNot :: S Bit -> S ()
requireNot constr =
  do b <- constr
     [] ==> [ng b]

data Bit    = Lit Lit | Bool Bool deriving (Eq,Show)
type Number = [Bit] -- lsb first (omvänt)   (011 = 2+4 = 6)

b0, b1 :: Bit
b0 = Bool False
b1 = Bool True

ng :: Bit -> Bit
ng (Lit x)  = Lit (neg x)
ng (Bool b) = Bool (not b)

newBit :: S Bit
newBit = (Lit . neg) `fmap` newLit

number :: Int -> Number
number 0 = []
number n = Bool (odd n) : number (n `div` 2)

getModelNumber :: Number -> S Int
getModelNumber []     = return 0
getModelNumber (x:xs) =
  do n <- getModelNumber xs
     b <- getModelValue' x
     return ((if b then 1 else 0) + 2*n)
 where
  getModelValue' (Bool b) = return b
  getModelValue' (Lit x)  = getModelValue x

newVar :: Int -> S Number
newVar k = sequence [ newBit | i <- [1..k] ]

plus :: Bit -> Number -> Number -> S Number
plus c []     []     = return [c]
plus c []     ys     = plus c [b0] ys
plus c xs     []     = plus c xs [b0]
plus c (x:xs) (y:ys) =
  do z  <- sumBit c x y
     c' <- carryBit c x y
     zs <- plus c' xs ys
     return (z:zs)

(==>) :: [Bit] -> [Bit] -> S ()
xs ==> ys = clause (map ng xs ++ ys)

clause ls
    | Bool True `elem` ls = return ()
    | otherwise           = addClause [ x | Lit x <- ls ] >> return ()

sumBit :: Bit -> Bit -> Bit -> S Bit
sumBit a b c =
  do s <- newBit
     [ng a, ng b, ng c] ==> [ng s]
     [   a,    b, ng c] ==> [ng s]
     [   a, ng b,    c] ==> [ng s]
     [ng a,    b,    c] ==> [ng s]
     [   a, ng b, ng c] ==> [s]
     [ng a,    b, ng c] ==> [s]
     [ng a, ng b,    c] ==> [s]
     [   a,    b,    c] ==> [s]
     return s

carryBit :: Bit -> Bit -> Bit -> S Bit
carryBit a b c =
  do d <- newBit
     [ng a, ng b, ng c] ==> [ng d]
     [   a, ng b, ng c] ==> [ng d]
     [ng a,    b, ng c] ==> [ng d]
     [ng a, ng b,    c] ==> [ng d]
     [   a,    b, ng c] ==> [d]
     [   a, ng b,    c] ==> [d]
     [ng a,    b,    c] ==> [d]
     [   a,    b,    c] ==> [d]
     return d

timesBit :: Bit -> Number -> S Number
timesBit (Bool b) xs = return [ Bool b | _ <- xs ]
timesBit a        xs =
  sequence [ do y <- newBit
                [a,x]  ==> [y]
                [ng a] ==> [ng y]
                [ng x] ==> [ng y]
                return y
           | x <- xs
           ]

times :: Number -> Number -> S Number
times []     ys = return []
times _ []                      = return []
times (x:xs) ys =
  do p:ps <- timesBit x ys
     qs   <- times xs ys
     rs   <- plus b0 ps qs
     return (p:rs)

equal :: Number -> Number -> S Bit
equal []     []     = return b1
equal []     ys     = allZero ys
equal xs     []     = allZero xs
equal (x:xs) (y:ys) =
  do e  <- newBit
     eq <- equal xs ys
     [ng eq]          ==> [ng e]
     [ng x, y]        ==> [ng e]
     [x, ng y]        ==> [ng e]
     [x, y, eq]       ==> [e]
     [ng x, ng y, eq] ==> [e]
     return e

less :: Number -> Number -> S Bit
less x y =
  do c <- lt ((ng x', ng y') : tail xys)
     return c
 where
  xys     = reverse (align' x y)
  (x',y') = head xys

  lt [] =
    do return (Bool False)

  lt ((x,y):xys) | x == ng y =
    return y

  lt ((x,y):xys) | x == y =
    lt xys

  lt ((x,y):xys) =
    do c' <- lt xys
       c <- newBit
       [y,c']       ==> [c]
       [x,ng c']    ==> [ng c]
       [ng x,c']    ==> [c]
       [ng y,ng c'] ==> [ng c]
       [x,ng y]     ==> [ng c]
       [ng x,y]     ==> [c]
       return c

align' :: Number -> Number -> [(Bit,Bit)]
align' x y = uncurry zip (align x y)

allZero :: Number -> S Bit
allZero [] = return b1
allZero xs =
  do z <- newBit
     map ng xs ==> [z]
     sequence_ [ [x] ==> [ng z] | x <- xs ]
     return z

