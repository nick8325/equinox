module Equinox.FolSat where

{-
Equinox -- Copyright (c) 2003-2011, Koen Claessen

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
import qualified Sat
import Name( name, prim, (%), tr )
import Data.List hiding ( union, insert, delete )
import Data.Maybe
import Equinox.Fair
import Equinox.TermSat hiding ( Lit(..) )
import Equinox.TermSat ( Lit )
import qualified Equinox.TermSat as T
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import Data.Maybe( isJust, fromJust )
import System.IO
import Flags
import Control.Monad
import Equinox.PSequence
import Equinox.TopSort

-----------------------------------------------------------------------------

prove :: Flags -> [Clause] -> [Clause] -> IO ClauseAnswer
prove flags theory oblig =
  run $
    do st <- newCon "*"
       (tr ::: ([] :-> bool)) `app` []

       sequence_
         [ addClauseSub M.empty c
         | c <- groundCs
         ]

       sequence_
         [ addGroundTerm x
         | c <- nonGroundCs -- was: oblig
         , l <- c
         , a :=: b <- [the l]
         , x <- [a,b]
         , x /= truth
         ]

       lift (putStrLn "#elt|#instances")
       solveFOL flags syms st nonGroundCs
 where
  cs = concatMap (norm []) (theory ++ oblig)
  (groundCs,nonGroundCs) = partition isGround cs
  syms = S.filter (not . isVarSymbol) (symbols cs)

-----------------------------------------------------------------------------

norm :: [Signed Atom] -> [Signed Atom] -> [[Signed Atom]]
norm ls' [] =
  [reverse ls']

norm ls' (Neg (Var x :=: Var y) : ls) =
  norm [] (subst (x |=> Var y) (reverse ls' ++ ls))

norm ls' (Neg (Var x :=: t) : ls) | not (x `S.member` free t) = -- just testing
  norm [] (subst (x |=> t) (reverse ls' ++ ls))

norm ls' (Neg (t :=: Var x) : ls) | not (x `S.member` free t) = -- just testing
  norm [] (subst (x |=> t) (reverse ls' ++ ls))

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

-----------------------------------------------------------------------------

data Refine = B | L
 deriving (Show, Eq)

data Model
  = Model
  { domain  :: [Con]
  , star    :: Con
  , tables  :: Map Symbol [([Con],Con)]
  , same    :: Set Symbol
  , sameDom :: Bool
  }

type Send = Char -> IO ()

data Thread = Thread Int (Refine -> Model -> Send -> IO (T Bool, Thread))

-----------------------------------------------------------------------------

solveFOL :: Flags -> Set Symbol -> Con -> [[Signed Atom]] -> T ClauseAnswer
solveFOL flags syms st cls =
  do refine B Nothing st [ clauseThread cl | cl <- cls ]
 where
  funs = S.filter isFunSymbol syms

  fs = S.toList funs

  answer = head $ [ ans
                  | ans@(nam ::: (_ :-> t)) <- S.toList syms
                  , t == bool
                  , nam == name "$answer"
                  ] ++ [ name "$no_answer" ::: ([] :-> bool) ]

  min    = head $ [ mn
                  | mn@(nam ::: (_ :-> t)) <- S.toList syms
                  , t == bool
                  , nam == name "$min"
                  ] ++ [ name "$no_min" ::: ([] :-> bool) ]

  refine rf mOldModel st ths =
    do ans   <- getTable answer
       mins  <- getTable min
       preds <- concat `fmap` sequence [ getTable p | p <- S.toList syms, isPredSymbol p ]
       true  <- (tr ::: ([] :-> bool)) `app` []
       mls   <- solveWithConflict flags [ y T.:=: true  | (_,y) <- mins ]
                                        [ y T.:/=: true | (_,y) <- ans ]
       case mls of
         -- found a proof
         Just ls ->
           do if not (null ls) then
                lift $ putStrLn $ ("+++ ANSWER: " ++) $
                  concat $ intersperse " | " $
                    [ "(" ++ concat (intersperse "," (map show xs)) ++ ")"
                    | (xs,y) <- ans
                    , (y T.:=: true) `elem` ls
                    ]
               else
                return ()
              return Unsatisfiable

         -- found a candidate model, let's check it
         _ ->
           do model <- getModel mOldModel st
              lift (putStr ( let s = show (length (domain model))
                              in replicate (4 - length s) ' ' ++ s
                          ++ case rf of
                               B -> "|"
                               L -> "+"
                           ) >> hFlush stdout)
              rs <- lift $ psequence (nrOfThreads flags)
                      [ (n, \send -> h rf model send)
                      | Thread n h <- ths
                      ]
              lift $ putStrLn ""
              let (adds,ths') = unzip rs
              b <- or `fmap` sequence [ add | add <- adds ]
              if b
                -- the candidate model was no good
                then refine B (Just model) st ths'
                -- it seemed to be OK...
                else do case mfile flags of
                          Just file -> writeModel file (S.toList syms)
                          Nothing   -> return ()
                        case rf of
                          -- let's try harder
                          B -> refine L Nothing st ths'
                          -- everything checks out!
                          L -> return Satisfiable

  getModel mOldModel st =
    do tabs <- getModelTables
       st'  <- getRep st

       let dom = S.toList $ S.fromList $
             st' :
             [ c
             | (f,tab) <- M.toList tabs
             , isFunSymbol f
             , (_,c) <- tab
             ]

           (sameFs, sameD) =
             case mOldModel of
               Nothing ->
                 (S.empty, False)

               Just oldModel ->
                 ( S.fromList
                     [ f
                     | (f,tab) <- M.toList tabs
                     , Just tab' <- [M.lookup f (tables oldModel)]
                     , sort tab == sort tab' -- can we do something weaker here?
                     ]
                 , all (`S.member` S.fromList (domain oldModel)) dom
                 )

       return Model
         { domain  = dom
         , star    = st'
         , tables  = tabs
         , same    = sameFs
         , sameDom = sameD
         }

-----------------------------------------------------------------------------

solveWithConflict flags mins ass =
  do b <- solve flags ass
     if b then
       do a <- T.newLit

          let try mins =
                do mins' <- sequence
                            [ do b <- getModelValue m
                                 if b then do return [m]
                                      else do addClause [T.neg a, T.neg m]
                                              return []
                            | m <- mins
                            ]
                   let mins = concat mins'
                   addClause (T.neg a : map T.neg mins)
                   b <- solve flags (a:ass)
                   if b then try mins else return ()

          try mins
          return Nothing
      else
       do ls <- conflict
          let ass' = map neg ls

          let try [] =
                do return (Just ls)

              try (ass:asss) =
                do mls <- solveWithConflict flags [] ass
                   case mls of
                     Nothing -> do try asss
                     _       -> do lift $ putStr "<>"
                                   return mls

           in try [ ass' \\ [a] | a <- ass' ]

-----------------------------------------------------------------------------

clauseThread :: [Signed Atom] -> Thread
clauseThread cl = thread True funs
 where
  fs   = (tr ::: ([] :-> bool)) : filter (not . isVarSymbol) (S.toList (symbols cl))
  xs   = S.toList (free cl)
  funs = S.fromList fs

  thread dom deps =
    Thread (length xs)
      (\ref model send ->
        if (not dom || sameDom model)
        && deps `S.isSubsetOf` same model
          then skip dom deps
          else check ref model send)

  skip dom deps =
    do return ( do return False
              , thread dom deps
              )

  check ref model send = Sat.run $
    do vs    <- sequence [ newValue (domain model) | x <- xs ]
       dom   <- Sat.newLit
       ms    <- sequence [ Sat.newLit | f <- fs, show f /= "$weak" ]
       let st   = star model
           mmap = M.fromList (fs `zip` ms)
           fmap = tables model
           vmap = M.fromList (xs `zip` vs)

           base  = case ref of B -> Sat.mkTrue; L -> Sat.mkFalse
           stars = Sat.mkFalse
       sequence_ [ buildLit (base,stars) st dom mmap fmap vmap l
                 | l <- cl
                 ]

       let findAllSubs i | i > 100 = -- an arbitrary choice! just testing
             -- ouch
             do Sat.lift (send '>')
                return (Left [])

           findAllSubs i =
             do b <- solveMin [ Sat.neg (v =? st) | v <- vs ] ([dom] ++ ms)
                if b then
                  do Sat.lift (showOne send (i+1))
                     cs <- sequence [ getModelValueValue v | v <- vs ]
                     let sub = M.fromList (xs `zip` cs)
                     Sat.addClause [ Sat.neg (v =? c) | (v,c) <- vs `zip` cs, c /= st ]
                     Left subs <- findAllSubs (i+1)
                     return (Left (sub:subs))
                 else
                  do if i == 0 then
                       do cfl <- Sat.conflict
                          Sat.lift (send '.')
                          return (Right ( Sat.neg dom `elem` cfl
                                        , S.fromList [ f | (f,m) <- M.toList mmap, Sat.neg m `elem` cfl ]
                                        ))
                      else
                       do return (Left [])

       Sat.lift (send '-')
       esubs <- findAllSubs 0
       return ( do --case esubs of
                   --  Right (dom,deps') -> lift $ print (cl,dom,deps')
                   --  Left subs         -> lift $ print (cl,subs)
                   sequence_ [ addClauseSub sub cl | Left subs <- [esubs], sub <- subs ]
                   return (case esubs of
                             Right _ -> False
                             Left _  -> True)
              , case esubs of
                  Right (dom,deps') -> thread dom deps'
                  _                 -> thread True funs
              )

  showOne send i
    | i <=    9 = send (head (show i))
    | i ==   10 = send 'X'
    | i ==   25 = send 'L'
    | i ==   75 = send 'C'
    | i ==  250 = send 'D'
    | i ==  750 = send 'M'
    | i == 2000 = send '#'
    | otherwise = return ()

-----------------------------------------------------------------------------

addClauseSub :: Map Symbol Con -> Clause -> T ()
addClauseSub sub cl =
  do --lift (print (sub,cl))
     --lift (print sub)
     ls <- sequence [ literal l | l <- cl ]
     --lift (print ls)
     addClause ls
 where
  term (Var x) =
    do return (fromJust $ M.lookup x sub)

  term (Fun f [t]) | show f == "$weak" =
    do term t

  term (Fun f ts) =
    do as <- sequence [ term t | t <- ts ]
       f `app` as

  atom (s :=: t) =
    do a <- term s
       b <- term t
       return (a T.:=: b)

  literal (Pos a) = atom a
  literal (Neg a) = neg `fmap` atom a

addGroundTerm :: Term -> T (Maybe Con)
addGroundTerm (Var _) =
  do return Nothing

addGroundTerm (Fun f [t]) | show f == "$weak" =
  addGroundTerm t

addGroundTerm (Fun f ts) =
  do mxs <- sequence [ addGroundTerm t | t <- ts ]
     if all isJust mxs
       then Just `fmap` (f `app` map fromJust mxs)
       else return Nothing

-----------------------------------------------------------------------------

buildLit :: (Sat.Lit,Sat.Lit) -> Con -> Sat.Lit -> Map Symbol Sat.Lit -> Map Symbol [([Con],Con)] -> Map Symbol (Value Con) -> Signed Atom -> Sat.S ()
buildLit opts st dom mmap fmap vmap (Pos (s :=: t)) =
  do a <- build opts st mmap fmap vmap s
     b <- build opts st mmap fmap vmap t
     notEqualOr [ Sat.neg dom | Var _ <- [s,t] ] a b

buildLit opts st dom mmap fmap vmap (Neg (s :=: t)) =
  do a <- build opts st mmap fmap vmap s
     b <- build opts st mmap fmap vmap t
     equalOr [] a b

build :: (Sat.Lit,Sat.Lit) -> Con -> Map Symbol Sat.Lit -> Map Symbol [([Con],Con)] -> Map Symbol (Value Con) -> Term -> Sat.S (Value Con)
build opts st mmap fmap vmap (Var x) =
  do return val
 where
  Just val = M.lookup x vmap

build opts@(base,stars) st mmap fmap vmap (Fun f [t]) | show f == "$weak" =
  do build (Sat.mkFalse,stars) st mmap fmap vmap t

build opts@(base,stars) st mmap fmap vmap (Fun f ts) =
  do ls <- sequence [ Sat.newLit | y <- ys ]
     Sat.addClause (Sat.neg m : ls)
     atMostOr 1 Sat.mkFalse ls
     let z = zip ys ls
     let opts' | show f == "$answer" = (Sat.mkFalse,stars)
               | otherwise           = opts
     vs <- sequence [ build opts' st mmap fmap vmap t | t <- ts ]

     let entries hist [] =
           do return []

         entries hist ((xs,y):tab) =
           do e <- conj ( [ v =? x    | (v,x) <- vs `zip` xs, x /= st ]
                       ++ [ Sat.neg e | (zs,e) <- hist, and (zipWith over zs xs) ]
                        )
              Sat.addClause [Sat.neg e, Sat.neg m, z =? y]
              sequence_ [ Sat.addClause [Sat.neg base, Sat.neg e, Sat.neg m, v =? st]
                        | isFunSymbol f
                        , (v,x) <- vs `zip` xs
                        , x == st
                        ]
              if null tab then -- final f(*,*,*) = ?
                do Sat.addClause [Sat.neg stars, Sat.neg m, Sat.neg e]
                   return ()
               else
                do return ()
              es <- entries ((xs,e):hist) tab
              return (e:es)

         x `over` y = x==st || y==st || x==y

     es <- entries [] tab
     Sat.addClause (Sat.neg m : es)
     return z
 where
  Just m = M.lookup f mmap `mplus` error (show f)
  tab'   = case M.lookup f fmap of
             Just tab' -> tab'
             Nothing   -> []
  ys     = S.toList (S.fromList (map snd tab))

  tab = ( map snd $ sort
          [ (number (==st) xs,(xs,y))
          | (xs,y) <- tab'
          ] ) ++ [(replicate (arity f) st, df)]
   where
    number p = length . filter p

    df | isFunSymbol f = head (results ++ [st])
       | otherwise     = st

    results = map snd
            . reverse
            . sort
            . map (\xs -> (length xs, head xs))
            . group
            . sort
            . map snd
            $ tab'

occursMost :: Ord a => a -> [a] -> a
occursMost y [] = y
occursMost _ xs = snd . head . reverse . sort . map (\xs -> (length xs, head xs)) . group . sort $ xs

-----------------------------------------------------------------------------

solveMin :: [Sat.Lit] -> [Sat.Lit] -> Sat.S Bool
solveMin xs as =
  do b <- Sat.solve as
     if b then
       let mins a =
             do bs <- sequence [ Sat.getModelValue x | x <- xs ]
                let k = length [ b | b <- bs, b ]
                if k >= 1 then
                  do atMostOr (k-1) a xs
                     b <- Sat.solve (Sat.neg a:as)
                     if b then mins a else return True
                 else
                  do return True

        in do a <- Sat.newLit
              mins a
      else
       do return False

-----------------------------------------------------------------------------

atMostOr :: Int -> Sat.Lit -> [Sat.Lit] -> Sat.S ()
atMostOr k x _ | k < 0 =
  do Sat.addClause [x]
     return ()

atMostOr k x ls | k == 0 =
  do sequence_ [ Sat.addClause [x, Sat.neg l] | l <- ls ]

atMostOr k x ls | k >= length ls =
  do return ()

atMostOr k y ls =
  do Sat.addClause (y : map Sat.neg lsa)
     if not (null lsb) then
       do zs <- sequence [ Sat.newLit | i <- [1..k] ]
          sequence_ [ Sat.addClause ([y, Sat.neg x, z]) | (x,z) <- lsa `zip` zs ]
          let x = last lsa
          sequence_ [ Sat.addClause ([y, Sat.neg x] ++ map Sat.neg (take i lsa) ++ [z]) | (i,z) <- [0..] `zip` zs ]
          atMostOr k y (zs ++ lsb)
      else
       do return ()
 where
  lsa = take (k+1) ls
  lsb = drop (k+1) ls

-----------------------------------------------------------------------------

conj, disj :: [Sat.Lit] -> Sat.S Sat.Lit
conj xs
  | Sat.mkFalse `elem` xs = return Sat.mkFalse
  | otherwise             = conj' (nub [ x | x <- xs, x /= Sat.mkTrue ])
 where
  conj' [] =
    do return Sat.mkTrue
  conj' [x] =
    do return x
  conj' xs =
    do z <- Sat.newLit
       Sat.addClause (z : map Sat.neg xs)
       sequence_ [ Sat.addClause [ Sat.neg z, x ] | x <- xs ]
       return z

disj xs = Sat.neg `fmap` conj (map Sat.neg xs)

-----------------------------------------------------------------------------

type Value a = [(a,Sat.Lit)]

(=?) :: Eq a => Value a -> a -> Sat.Lit
xls =? x = head ([ l | (x',l) <- xls, x' == x ] ++ [ Sat.mkFalse ])

equalOr :: Ord a => [Sat.Lit] -> Value a -> Value a -> Sat.S ()
equalOr c [] ys =
  do sequence_ [ Sat.addClause ([Sat.neg q] ++ c) | (_,q) <- ys ]
equalOr c xs [] =
  do sequence_ [ Sat.addClause ([Sat.neg p] ++ c) | (_,p) <- xs ]
equalOr c ((x,p):xs) ((y,q):ys) =
  case x `compare` y of
    LT -> do Sat.addClause ([Sat.neg p] ++ c)
             equalOr c xs ((y,q):ys)
    EQ -> do -- only one of these is enough, really
             Sat.addClause ([Sat.neg p, q] ++ c)
             Sat.addClause ([Sat.neg q, p] ++ c)
             equalOr c xs ys
    GT -> do Sat.addClause ([Sat.neg q] ++ c)
             equalOr c ((x,p):xs) ys

notEqualOr :: Ord a => [Sat.Lit] -> Value a -> Value a -> Sat.S ()
notEqualOr c [] ys = do return ()
notEqualOr c xs [] = do return ()
notEqualOr c ((x,p):xs) ((y,q):ys) =
  case x `compare` y of
    LT -> do notEqualOr c xs ((y,q):ys)
    EQ -> do Sat.addClause ([Sat.neg p, Sat.neg q] ++ c)
             notEqualOr c xs ys
    GT -> do notEqualOr c ((x,p):xs) ys

newValue :: Ord a => [a] -> Sat.S (Value a)
newValue xs = new (map head . group . sort $ xs)
 where
  new [x] =
    do return [(x,Sat.mkTrue)]

  new [x,y] =
    do l <- Sat.newLit
       return [(x,Sat.neg l), (y, l)]

  new xs =
    do ls <- sequence [ Sat.newLit | x <- xs ]
       Sat.addClause ls
       atMostOr 1 Sat.mkFalse ls
       return (xs `zip` ls)

getModelValueValue :: Value a -> Sat.S a
getModelValueValue [(x,_)] =
  do return x

getModelValueValue ((x,l):xls) =
  do b <- Sat.getModelValue l
     if b then return x else getModelValueValue xls

-----------------------------------------------------------------------------

writeModel :: FilePath -> [Symbol] -> T ()
writeModel file fs =
  do tabs <- getModelTables
     let ts = M.toList tabs
     lift $ writeFile file $ unlines $ concat $ intersperse [""] $
       [ [ show a ++ " := " ++ rep S.empty ts c ]
       | (a,[([],c)]) <- ts
       , isFunSymbol a
       , take 2 (show a) == "a_"
       ] ++
       [ table f tab
       | f <- fs
       , Just tab <- [M.lookup f tabs]
       ]

table :: Symbol -> [([Con],Con)] -> [String]
table f tab = [ lhs
             ++ " = "
             ++ if lhs == rhs then "<..>" else rhs
              | (xs,y) <- tab
              , let lhs = sapp f (map show xs)
                    rhs = show y
              ]

sapp f [] = show f
sapp f xs = show f ++ "(" ++ concat (intersperse "," xs) ++ ")"

rep :: Set Con -> [(Symbol,[([Con],Con)])] -> Con -> String
rep seen tabs c = head $
  [ sapp f (map (rep (S.insert c seen) tabs) xs)
  | not (c `S.member` seen)
  , (f,tab) <- tabs
  , isFunSymbol f
  , take 2 (show f) == "c_"
  , (xs,y) <- tab
  , y == c
  ] ++
  [ show (show c)
  ]

-----------------------------------------------------------------------------

