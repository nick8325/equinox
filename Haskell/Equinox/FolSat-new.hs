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
  { realVars :: Set Symbol
  , unrVars  :: Set Symbol
  , defs     :: [(Symbol,Term)]
  , lits     :: [(Symbol,Term)]
  , eqs      :: [(Symbol,Symbol)]
  }
 deriving ( Show, Eq )

prove :: Flags -> [Clause] -> IO Bool
prove flags cs =
  run $
    do let (ground,clauses) =
             partition (S.null . realVars)
               [ cl | c <- cs, Just cl <- [convert c] ]

       sequence_
         [ instantiate [] M.empty c
         | c <- ground
         ]

       sequence_
         [ lift $ print c
         | c <- clauses
         , S.size (unrVars c) > 0
         ]

       sequence_
         [ term M.empty t
         | c <- clauses
         , (_,t) <- defs c ++ lits c
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

       let refineUnrestricted = refines flags getModelCons True  True  clauses
           refineLitsNotTrue  = refines flags getModelCons True  False clauses
           refineLitsFalse    = refines flags getModelCons False False clauses

       r <- cegar Nothing                 (return True) -- (createNewTerms clauses)
          $ cegar (Just 1)                refineUnrestricted
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
convert c = conv 1 [] [] [] (norm c [] [])
 where
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

  conv _ defs lits eqs [] =
    Just (C realVars unrVars (topSort S.empty defs []) lits eqs)
   where
    realVars =
      (free [ t | (_,t) <- defs ++ lits ] `S.union` S.fromList [ z | (x,y) <- eqs, z <- [x,y] ])
        `S.difference` S.fromList [ x | (x,_) <- defs ]

    unrVars =
      realVars
        `S.difference` restrVars

    restrVars = fix expand s0
     where
      s0 =
        free [ t | (_,t) <- lits ]
          `S.union` S.fromList [ x | (x,_) <- lits ]

      expand s =
        s `S.union` S.unions [ free t | (x,t) <- defs, x `S.member` s ]

      fix f x | x == fx   = x
              | otherwise = fix f fx
             where
              fx = f x

    dxs = S.fromList [ x | (x,_) <- defs ]

    topSort defd ((x,t):ds) ds' | (free t `S.intersection` dxs) `S.isSubsetOf` defd =
      (x,t) : topSort (x `S.insert` defd) ds ds'

    topSort defd (d:ds) ds' =
      topSort defd ds (d:ds')

    topSort defd [] [] =
      []

    topSort defd [] ds' =
      topSort defd ds' []

  conv i defs lits eqs (Neg (Var x :=: t) : ls)
    | not (cyclic S.empty (S.toList (free t))) && x `notElem` map fst defs =
      conv i ((x,t):defs) lits eqs ls
   where
    cyclic vis [] =
      False

    cyclic vis (y:ys) | x == y =
      True

    cyclic vis (y:ys) | y `S.member` vis =
      cyclic vis ys

    cyclic vis (y:ys) =
      cyclic (y `S.insert` vis) (concat [ S.toList (free t) | (z,t) <- defs, y == z ] ++ ys)

  conv i defs lits eqs (Neg (Var x :=: t) : ls) =
    conv i defs ((x,t):lits) eqs ls

  conv i defs lits eqs (Neg (s :=: t) : ls) =
    define i t defs $ \(x,defs') ->
      conv (i+1) defs' ((x,s):lits) eqs ls

  conv i defs lits eqs (Pos (s :=: t) : ls) | s == t =
    Nothing

  conv i defs lits eqs (Pos (Var x :=: Var y) : ls) =
    conv i defs lits ((x,y):eqs) ls

  conv i defs lits eqs (Pos (Var x :=: t) : ls) =
    define i t defs $ \(y,defs') ->
      conv (i+1) defs' lits ((x,y):eqs) ls

  conv i defs lits eqs (Pos (s :=: t) : ls) =
    define i s defs $ \(x,defs') ->
      define (i+1) t defs' $ \(y,defs'') ->
        conv (i+2) defs'' lits ((x,y):eqs) ls

  define i t defs h =
    case [ x | (x,t') <- defs, t == t' ] of
      x:_ -> h (x,defs)
      _   -> h (x,defs ++ [(x,t)])
       where
        x = var top i

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

refines :: Flags -> T (Set Con) -> Bool -> Bool -> [C] -> T Bool
refines flags getCons liberal unrestr cs =
  do cons <- getCons
     putLn 1 ( "--> Refining ("
            ++ concat (intersperse "|" (["liberal" | liberal] ++ ["unrestr"|unrestr]))
            ++ "), with "
            ++ show (S.size cons)
            ++ " domain elements"
             )
     tryAll [ refine (S.toList cons) liberal unrestr c | c <- cs ]
 where
  put   v s = when (v <= verbose flags) $ lift $ do putStr s;   hFlush stdout
  putLn v s = when (v <= verbose flags) $ lift $ do putStrLn s; hFlush stdout

refine :: [Con] -> Bool -> Bool -> C -> T Bool
refine cons liberal unrestr cl = match False [] (sortW (defs cl ++ lits cl)) M.empty
 where
  match cheated [] [] assign
    | all (\x -> x `M.member` assign
              || (unrestr && x `S.member` (unrVars cl)))
          (S.toList (realVars cl)) = instantiate cons assign cl
    | otherwise                    = return False

  match cheated ((c,Var x):as) ls assign =
    case M.lookup x assign of
      Just c'
        | c /= c'   -> return False
        | otherwise -> match cheated as ls assign

      Nothing
        | and [ M.lookup y assign /= Just c
              | y <- matches x (eqs cl)
              ]     -> match cheated as ls (M.insert x c assign)
        | otherwise -> return False

  match cheated ((c,Fun f ts):as) ls assign =
    do tab <- getModelTable f
       tryAll
         [ match cheated (sortW (xs `zip` ts) `mergeW` as) ls assign
         | (xs,y) <- tab
         , y == c
         ]

  match cheated [] ((x,Fun f ts):ls) assign =
    do tab <- getModelTable f
       tryAll $
         [ match cheated ((y,Var x) : sortW (xs `zip` ts)) ls assign
         | (xs,y) <- tab
         ] ++
         [ match cheated [] ls assign
         | liberal
         ] ++
         [ match True [] ([ (x,t) | (x,t@(Fun _ _)) <- xs `zip` ts ] ++ ls) assign
         | False
         , not cheated
         , not liberal
         --, isPredSymbol f
         --, length (eqs cl) <= 1
         , x `elem` (map fst (eqs cl) ++ map snd (eqs cl))
         , let xs = [ (v % i) ::: V top | let v ::: _ = x, i <- [1..] ]
         ]

matches :: Eq a => a -> [(a,a)] -> [a]
matches x xys = [ y | (x',y) <- xys, x == x' ]
             ++ [ y | (y,x') <- xys, x == x' ]

sortW :: [(a,Term)] -> [(a,Term)]
sortW = sortBy cmp

mergeW :: [(a,Term)] -> [(a,Term)] -> [(a,Term)]
mergeW = mergeBy cmp

cmp :: (a,Term) -> (a,Term) -> Ordering
(_,t1) `cmp` (_,t2) = weight t1 `compare` weight t2
 where
  weight (Var _)    = -1
  weight (Fun _ xs) = length xs

mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy cmp xs [] = xs
mergeBy cmp [] ys = ys
mergeBy cmp (x:xs) (y:ys) =
  case x `cmp` y of
    LT -> x : mergeBy cmp xs (y:ys)
    _  -> y : mergeBy cmp (x:xs) ys

instantiate :: [Con] -> Map Symbol Con -> C -> T Bool
instantiate cons sub cl = inst vs sub
 where
  vs = [ v
       | v <- S.toList (unrVars cl)
       , not (v `M.member` sub)
       ]

  inst (v:vs) sub =
    do lift $ print "unr var"
       tryAll
         [ inst vs (M.insert v c sub)
         | c <- cons
         ]

  inst [] sub =
    do mb <- eval sub
       case mb of
         Just True -> return False
         _ ->
           do sub <- defns sub (defs cl)
              ns <- sequence [ do Just a <- term sub (Var x)
                                  Just b <- term sub t
                                  return (a T.:/=: b)
                             | (x,t) <- lits cl
                             ]
              ps <- sequence [ do Just a <- term sub (Var x)
                                  Just b <- term sub (Var y)
                                  return (a T.:=: b)
                             | (x,y) <- eqs cl
                             ]
              --lift $ putStrLn ("=> " ++ show (ns ++ ps))
              addClause (ns ++ ps)
              return True

  defns sub [] =
    do return sub

  defns sub ((x,t):ds) =
    do Just c <- term sub t
       defns (M.insert x c sub) ds

  eval sub =
    do sub <- defns sub (defs cl)
       ns <- sequence [ lit sub l | l <- lits cl ]
       ps <- sequence [ eqlit sub l | l <- eqs cl ]
       let ls = map (fmap not) ns ++ ps
       return $
         if Just True `elem` ls
           then Just True
           else if all (== Just False) ls
                  then Just False
                  else Nothing
   where
    defns sub [] =
      do return sub

    defns sub ((x,t):ds) =
      do mc <- term sub t
         case mc of
           Just c  -> defns (M.insert x c sub) ds
           Nothing -> defns sub ds

    lit sub (x,t) =
      do ma <- term sub (Var x)
         mb <- term sub t
         return (ma =? mb)

    eqlit sub (x,y) =
      do ma <- term sub (Var x)
         mb <- term sub (Var y)
         return (ma =? mb)

    Nothing =? Nothing = Nothing
    Nothing =? Just _  = Just False
    Just _  =? Nothing = Just False
    Just a  =? Just b  = Just (a == b)

    term sub (Var x) =
      do return (M.lookup x sub)

    term sub (Fun f ts) =
      do mas <- sequence [ term sub t | t <- ts ]
         if any isNothing mas
           then do return Nothing
           else do tab <- getModelTable f
                   case [ y | (xs,y) <- tab, map Just xs == mas ] of
                     y:_ -> return (Just y)
                     _   -> return Nothing

term :: Map Symbol Con -> Term -> T (Maybe Con)
term sub (Var x) =
  return (M.lookup x sub)

term sub (Fun f ts) =
  do as <- sequence [ term sub t | t <- ts ]
     if any isNothing as
       then return Nothing
       else Just `fmap` (f `app` [ a | Just a <- as ])
