module Equinox.FolSat where

{-
Equinox -- Copyright (c) 2003-2007, Koen Claessen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-}

import Form
import Name( prim, tr, (%) )
import List hiding ( union, insert, delete )
import Maybe
import Equinox.Fair
import Equinox.TermSat hiding ( Lit(..) )
import Equinox.TermSat ( Lit )
import qualified Equinox.TermSat as T
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import IO
import Flags
import Control.Monad

prove :: Flags -> [Clause] -> IO Bool
prove flags cs' =
  run $
    do true <- newCon "$true"
       st   <- star `app` []
       
       sequence_
         [ do put 1 "P: "
              addClauseSub true (M.fromList [ (x, st) | x <- S.toList (free c) ]) c
         | c <- cs
         ]

       let getModelCons =
             do tabs <- sequence [ getModelTable f | f <- S.toList fs ]
                return (S.toList (S.fromList [ c | tab <- tabs, (_,c) <- tab ]))

       let refineGuess  = refine flags true getModelCons True  True  nonGroundCs
           refineStar   = refine flags true getModelCons True  False nonGroundCs
           refineNoStar = refine flags true getModelCons False False nonGroundCs

       r <- cegar Nothing                 refineGuess
          $ cegar (Just (strength flags)) refineStar
          $ cegar Nothing                 refineNoStar
          $ Just `fmap` solve flags []

       return (r == Just False)
 where
  put   v s = when (v <= verbose flags) $ lift $ do putStr s;   hFlush stdout
  putLn v s = when (v <= verbose flags) $ lift $ do putStrLn s; hFlush stdout
  
  cs = concatMap (norm []) cs'
  
  nonGroundCs = filter (not . isGround) cs
  
  syms = symbols cs
  
  fs' = S.filter (\f ->
    case f of
      _ ::: (_ :-> t) -> t /= bool
      _               -> False) syms
  
  fs = star `S.insert` fs'

trueX, star :: Symbol
trueX = prim "True" ::: V bool
star  = prim "*" ::: ([] :-> top)

norm :: [Signed Atom] -> [Signed Atom] -> [[Signed Atom]]
norm ls' [] =
  [reverse ls']

norm ls' (Neg (Var x :=: Var y) : ls) =
  norm [] (subst (x |=> Var y) (reverse ls' ++ ls))

norm ls' (Pos (Var x :=: Fun f ts) : ls) =
  norm (Pos (Fun f ts :=: Var x) : ls') ls

norm ls' (Neg (Var x :=: Fun f ts) : ls) =
  norm (Neg (Fun f ts :=: Var x) : ls') ls

norm ls' (Pos (s :=: t) : ls) | s == t =
  []

norm ls' (Neg (s :=: t) : ls) | s == t =
  norm ls' ls

norm ls' (l : ls) =
  norm (l : ls') ls

cclause :: [Signed Atom] -> ([(Term,Symbol)],[(Symbol,Symbol)])
cclause cl = (defs,neqs)
 where
  theX i = var top i
    
  (defs,neqs) = lits 1 cl
    
  lits i [] =
    ([],[])
    
  lits i (Neg (s :=: Var x) : ls) =
    ((s,x):defs,neqs)
   where
    (defs,neqs) = lits i ls

  lits i (Neg (s :=: t) : ls) | t /= truth =
    ((s,x):(t,x):defs,neqs)
   where
    x = theX i
    (defs,neqs) = lits (i+1) ls

  lits i (Pos (Var x :=: Var y) : ls) =
    (defs,(x,y):neqs)
   where
    (defs,neqs) = lits i ls

  lits i (Pos (s :=: Var y) : ls) =
    ((s,x):defs,(x,y):neqs)
   where
    x = theX i
    (defs,neqs) = lits (i+1) ls

  lits i (Pos (s :=: t) : ls) | t /= truth =
    ((s,x):(t,y):defs,(x,y):neqs)
   where
    x = theX i
    y = theX (i+1)
    (defs,neqs) = lits (i+2) ls

  lits i (Neg (Fun p ts :=: t) : ls) | t == truth =
    ((Fun p ts,trueX):defs,neqs)
   where
    (defs,neqs) = lits i ls

  lits i (Pos (Fun p ts :=: t) : ls) | t == truth =
    ((Fun p ts,x):defs,(x,trueX):neqs)
   where
    x = theX i
    (defs,neqs) = lits (i+1) ls

addClauseSub :: Con -> Map Symbol Con -> Clause -> T ()
addClauseSub true sub cl =
  do ls <- sequence [ literal l | l <- cl ]
     --lift (print cl)
     --lift (print sub)
     --lift (print ls)
     addClause ls
 where
  term (Var x) =
    do return (fromJust $ M.lookup x sub)
  
  term (Fun f ts) =
    do as <- sequence [ term t | t <- ts ]
       f `app` as
  
  atom (s :=: t) | t == truth =
    do a <- term s
       return (a T.:=: true)
  
  atom (s :=: t) =
    do a <- term s
       b <- term t
       return (a T.:=: b)
  
  literal (Pos a) = atom a
  literal (Neg a) = neg `fmap` atom a

tryAll []     = do return False
tryAll (m:ms) = do b  <- m
                   b' <- tryAll ms
                   return (b || b')

findOne []     = do return False
findOne (m:ms) = do b <- m
                    if b
                      then return True
                      else findOne ms

matches x xys = [ y | (x',y) <- xys, x == x' ]
             ++ [ y | (y,x') <- xys, x == x' ]

cegar :: Maybe Int -> T Bool -> T (Maybe Bool) -> T (Maybe Bool)
cegar mk refine solve =
  do mb <- solve
     case mb of
       Just True | mk /= Just 0 ->
         do r <- refine
            if r then
              cegar (subtract 1 `fmap` mk) refine solve
             else
              return (Just True)
       
       _ ->
         do return mb

refine :: Flags -> Con -> T [Con] -> Bool -> Bool -> [[Signed Atom]] -> T Bool
refine flags true getCons liberal guess cs =
  do cons' <- getCons
     st'   <- star `app` []
     st    <- getModelRep st'
     let cons = st : (cons' \\ [st])
     lift (putStrLn ("==> refining: liberal=" ++ show liberal
                            ++ ", guess=" ++ show guess
                            ++ ", #elements=" ++ show (length cons)))
     {-
     sequence_
       [ do tab <- getModelTable f
            sequence_
              [ lift (putStrLn (show f ++ "("
                                       ++ concat (intersperse "," (map show xs))
                                       ++ ") = "
                                       ++ show y))
              | (xs,y) <- reverse (sort tab)
              ]
       | f <- S.toList fs
       ]
     -}
     tryAll [ check liberal guess c true cons st
            | c <- cs
            ]
 where
  fs = S.filter (\f ->
    case f of
      _ ::: ((_:_) :-> t) -> True
      _                   -> False) (symbols cs)


check :: Bool -> Bool -> [Signed Atom] -> Con -> [Con] -> Con -> T Bool
check liberal guess cl true cons st = checkDefs 0 defs (M.fromList [(trueX,[true])])
 where
  (defs,neqs) = cclause cl
  
  vr i = (prim "D" % i) ::: V top
 
  -- going through the definitions
  checkDefs i [] vinfo
    | not guess && or [ True | x <- S.toList (free cl), Just (_:_:_) <- [M.lookup x vinfo] ] =
        do lift (putStrLn "no guessing!")
           return False
           
    | otherwise =
        do case findSolution st cons vinfo neqs of
             Nothing  -> do if guess && or [ True | x <- S.toList (free cl), Just (_:_:_) <- [M.lookup x vinfo] ]  then lift (do print (defs,neqs); print vinfo) else return ()
                            return False
             Just sub -> do lift (putStrLn (if liberal then "L: " else "B: "))
                            addClauseSub true sub cl
                            return True

  checkDefs i ((Fun f ts,y):defs) vinfo =
    do tab <- getModelTable f
       checkTab i (reverse (sort tab)) [] ts y defs vinfo
  
  -- going through the table entries
  checkTab i [] assign ts y defs vinfo =
    do return False
  
  checkTab i tab@(([],c):_) assign [] y defs vinfo =
    do checkAssign i ((Var y,[c]):assign) defs vinfo

  checkTab i tab assign (t:ts) y defs vinfo =
    do let ds = nub (map (head . fst) tab)
       tryAll [ checkTab i [ (xs,c) | (x:xs,c) <- tab
                                    , x == d || (liberal && x == st) ]
                           (argument t d ds : assign) ts y defs vinfo
              | d <- ds
              ]
   where
    argument t d ds
      | liberal && d == st = (t,cons \\ (ds \\ [d]))
      | otherwise          = (t,[d])

  -- going through the assignments
  checkAssign i [] defs vinfo =
    do checkDefs i defs vinfo
  
  checkAssign i ((Var x,ds):assign) defs vinfo
    | null ds' || conflict = return False
    | otherwise            = checkAssign i assign defs (M.insert x ds' vinfo)
   where
    ds' = case M.lookup x vinfo of
            Just ds0 -> ds0 `intersect` ds
            Nothing  -> ds
  
    conflict = or [ M.lookup y vinfo == Just [d]
                  | [d] <- [ds']
                  , y <- matches x neqs
                  ]
  
  checkAssign i ((t,ds):assign) defs vinfo =
    checkAssign (i+1) ((Var x,ds):assign) ((t,x):defs) vinfo
   where
    x = vr i

data Result c a
  = Cost c (Result c a)
  | Result a
  | Fail

result :: a -> Result c a
result x = Result x

cost :: Ord c => c -> Result c a -> Result c a
cost d p = Cost d (pay d p)
 where
  pay d (Cost e p) | d >= e    = pay d p
                   | otherwise = Cost e p
  pay d p                      = p

(+++) :: Ord c => Result c a -> Result c a -> Result c a
Fail     +++ q        = q
p        +++ Fail     = p
Result x +++ q        = Result x
p        +++ Result y = Result y
Cost d p +++ Cost e q
  | d < e             = Cost d (p +++ Cost e q)
  | d == e            = Cost d (p +++ q)
  | otherwise         = Cost e (Cost d p +++ q)

toMaybe :: Result c a -> Maybe a
toMaybe Fail       = Nothing
toMaybe (Result x) = Just x
toMaybe (Cost _ p) = toMaybe p

findSolution :: Con -> [Con] -> Map Symbol [Con] -> [(Symbol,Symbol)] -> Maybe (Map Symbol Con)
findSolution st cons vinfo neqs = toMaybe (find vinfo neqs [])
 where
  find vinfo [] neqs' =
    result (M.map head vinfo)
  
  find vinfo ((x,y):neqs) neqs'
    | value x /= value y = find vinfo neqs ((x,y):neqs')
    | otherwise          = bump x +++ bump y
   where
    value x = case M.lookup x vinfo of
                Just (d:_) -> d
                Nothing    -> st

    bump z = case ds of
               _:(ds'@(d:_)) -> cost d (find (M.insert z ds' vinfo) (neqs++neqs') [(x,y)])
               _             -> Fail
     where
      ds = case M.lookup z vinfo of
             Just ds -> ds
             Nothing -> cons

