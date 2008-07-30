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
import List hiding ( union, insert, intersect, delete )
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

data C = C
  { quantVars :: Set Symbol
  , freeVars  :: Set Symbol
  , defs      :: [(Symbol,Term)]
  , eqs       :: [(Symbol,Symbol)]
  }
 deriving ( Show, Eq )

isGroundC :: C -> Bool
isGroundC cl = S.null (quantVars cl) && S.null (freeVars cl)

prove :: Flags -> [Clause] -> IO Bool
prove flags cs =
  run $
    do let (ground,clauses) =
             partition isGroundC
               [ cl | c <- cs, Just cl <- [convert c] ]

       sequence_
         [ instantiate M.empty c
         | c <- ground
         ]

       sequence_
         [ term M.empty t
         | cl <- clauses
         , (_,t) <- defs cl
         ]

       sequence_
         [ star `app` []
         | noConstants
         ]

       let getModelCons =
             do {-
                sequence_
                  [ do tab <- getModelTable f
                       sequence [ lift $ print (f,xs,y) | (xs,y) <- tab ]
                       return tab
                  | f <- [ f | f@(_ ::: (_ :-> _)) <- S.toList syms ]
                  ]
                -}
                tabs <- sequence [ getModelTable f | f <- S.toList fs ]
                return (S.fromList [ c | tab <- tabs, (_,c) <- tab ])

       let refineLitsNotTrue  = refines flags getModelCons Mode{ allowUndefinedTerms = True } clauses
           refineLitsFalse    = refines flags getModelCons Mode{ allowUndefinedTerms = False } clauses

       r <- cegar Nothing                 (return True) -- (createNewTerms clauses)
          $ cegar (Just (strength flags)) refineLitsNotTrue
          $ cegar Nothing                 refineLitsFalse
          $ Just `fmap` solve flags []

       return (r == Just False)
 where
  put   v s = when (v <= verbose flags) $ lift $ do putStr s;   hFlush stdout
  putLn v s = when (v <= verbose flags) $ lift $ do putStrLn s; hFlush stdout
  
  syms = symbols cs
  
  fs' = S.filter (\f ->
    case f of
      _ ::: (_ :-> t) -> t /= bool
      _               -> False) syms
  
  star = prim "*" ::: ([] :-> top)

  noConstants =
    null [ c | c@(_ ::: ([] :-> _)) <- S.toList fs' ]

  fs | noConstants = star `S.insert` fs'
     | otherwise   = fs'

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

--

convert :: Clause -> Maybe C
convert c = conv [ (prim "X" % i) ::: V top | i <- [1..] ] [] [] c'
 where
  c' = norm c [] []
 
  norm (Neg (Var x :=: Var y) : ls) ns ps =
    norm (subst (x |=> Var y) (ls ++ ns ++ ps)) [] []
  norm (Neg (t :=: Var y):ls) ns ps =
    norm ls (Neg (Var y :=: t):ns) ps
  norm (Neg (Var y :=: t):ls) ns ps =
    norm ls (Neg (Var y :=: t):ns) ps
  norm (Pos (t@(Fun _ _) :=: Var y):ls) ns ps =
    norm ls ns (Pos (Var y :=: t):ps)
  norm (l:ls) ns ps =
    norm ls ns (l:ps)
  norm [] ns ps = ns ++ ps

  conv _ defs eqs [] =
    Just (C{ quantVars = quantVars
           , freeVars  = freeVars
           , defs      = defs'
           , eqs       = eqs
           })
   where
    freeVars = S.fromList [ z | (x,y) <- eqs, z <- [x,y] ] S.\\ (free (map snd defs) `S.union` S.fromList (map fst defs))
    
    (quantVars,defs') = topSort S.empty [] (sortBy siz [ (x,t,free t) | (x,t) <- defs ])
    
    (_,_,s1) `siz` (_,_,s2) = S.size s1 `compare` S.size s2
    
    topSort quantVars defs' [] =
      (quantVars,reverse defs')
    
    topSort quantVars defs' ((x,t,ys):defs) =
      topSort (quantVars `S.union` ys) ((x,t):defs') (sortBy siz [ (x,t,ys S.\\ new) | (x,t,ys) <- defs ])
     where
      new = S.insert x ys

  conv zs defs eqs (Neg (Var x :=: t) : ls) =
    conv zs ((x,t):defs) eqs ls

  conv (z:zs) defs eqs (Neg (s :=: t) : ls) =
    conv zs ((z,s):(z,t):defs) eqs ls
 
  conv zs defs eqs (Pos (s :=: t) : ls) | s == t =
    Nothing

  conv zs defs eqs (Pos (Var x :=: Var y) : ls) =
    conv zs defs ((x,y):eqs) ls

  conv (z:zs) defs eqs (Pos (Var x :=: t) : ls) =
    conv zs ((z,t):defs) ((x,z):eqs) ls

  conv (z1:z2:zs) defs eqs (Pos (s :=: t) : ls) =
    conv zs ((z1,s):(z2,t):defs) ((z1,z2):eqs) ls

--

tryAll :: Monad m => [m Bool] -> m Bool
tryAll []     = do return False
tryAll (m:ms) = do b  <- m
                   b' <- tryAll ms
                   return (b || b')

--

createNewTerms :: [C] -> T Bool
createNewTerms _ = undefined

--

data Mode
  = Mode
  { allowUndefinedTerms :: Bool
  }
 deriving ( Show )

refines :: Flags -> T (Set Con) -> Mode -> [C] -> T Bool
refines flags getCons mode cs =
  do cons <- getCons
     putLn 1 ( "--> Refining ("
            ++ show mode
            ++ "), with "
            ++ show (S.size cons)
            ++ " domain elements"
             )
     tryAll [ refine (S.toList cons) mode c | c <- cs ]
 where
  put   v s = when (v <= verbose flags) $ lift $ do putStr s;   hFlush stdout
  putLn v s = when (v <= verbose flags) $ lift $ do putStrLn s; hFlush stdout

refine :: [Con] -> Mode -> C -> T Bool
refine cons mode cl = match [] (defs cl) M.empty
 where
  -- variable x must have a particular value c
  match ((c,Var x):ass) defs sub =
    case M.lookup x sub of
      Nothing ->
        if and [ c /= c' | Just c' <- [ M.lookup y sub | y <- matches x (eqs cl) ] ]
          then match ass defs (M.insert x c sub)
          else return False
      
      Just c' | c /= c' ->
        do return False
      
      _ ->
        do match ass defs sub

  -- term t must have a particular value c
  match ((c,Fun f ts):ass) defs sub =
    do tab <- getModelTable f
       tryAll
         [ match (sortW (xs `zip` ts) `mergeW` ass) defs sub
         | (xs,y) <- tab
         , y == c
         ]

  -- process one definition
  match [] ((x,Fun f ts):defs) sub =
    do tab <- getModelTable f
       tryAll $
         [ match (sortW ((c,Var x):(as `zip` ts))) defs sub
         | (as,c) <- tab
         ] ++
         [ match [] defs sub
         | allowUndefinedTerms mode
         ]
  
  -- everything is processed; however some variables are still not defined
  match [] [] sub
    | not (null [ x
                | x <- S.toList (quantVars cl)
                , Nothing <- [M.lookup x sub]
                ]) =
    do return False

  -- everything is processed; instantiate clause
  match [] [] sub =
    instFree (S.toList (freeVars cl)) sub 
   where
    instFree []     sub = instantiate sub cl
    instFree (x:xs) sub = tryAll [ instFree xs (M.insert x c sub)
                                 | c <- cons
                                 , and [ c /= c' | Just c' <- [ M.lookup y sub | y <- matches x (eqs cl) ] ]
                                 ]

matches :: Eq a => a -> [(a,a)] -> [a]
matches x xys = [ y | (x',y) <- xys, x == x' ]
             ++ [ y | (y,x') <- xys, x == x' ]

mergeW :: [(Con,Term)] -> [(Con,Term)] -> [(Con,Term)]
mergeW xs [] = xs
mergeW [] ys = ys
mergeW xs@(x@(_,s):xs') ys@(y@(_,t):ys')
  | weight s <= weight t = x : mergeW xs' ys
  | otherwise            = y : mergeW xs ys'
 where
  weight (Var _)    = 1
  weight (Fun _ []) = 0
  weight (Fun _ ts) = length ts + 2

sortW :: [(Con,Term)] -> [(Con,Term)]
sortW []  = []
sortW [x] = [x]
sortW xs  = sortW (take n xs) `mergeW` sortW (drop n xs)
 where
  n = length xs `div` 2

instantiate :: Map Symbol Con -> C -> T Bool
instantiate sub cl = inst sub (defs cl)
 where
  inst sub [] =
    do ls1 <- sequence [ do Just a <- term sub (Var x)
                            Just b <- term sub t
                            return (a T.:/=: b)
                       | (x,t) <- defs cl
                       ]
       ls2 <- sequence [ do Just a <- term sub (Var x)
                            Just b <- term sub (Var y)
                            return (a T.:=: b)
                       | (x,y) <- eqs cl
                       ]
       addClause (ls1 ++ ls2)
       return True
  
  inst sub ((x,t):defs)
    | x `S.member` quantVars cl =
      do inst sub defs
    | otherwise =    
      do Just a <- term sub t
         inst (M.insert x a sub) defs
     
term :: Map Symbol Con -> Term -> T (Maybe Con)
term sub (Var x) =
  return (M.lookup x sub)

term sub (Fun f ts) =
  do as <- sequence [ term sub t | t <- ts ]
     if any isNothing as
       then return Nothing
       else Just `fmap` (f `app` [ a | Just a <- as ])
