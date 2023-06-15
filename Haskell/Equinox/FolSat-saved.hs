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
import Name( prim, tr )
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

prove :: Flags -> [Clause] -> IO Bool
prove flags cs =
  run $
    do true <- newCon "$true"

       sequence_
         [ do put 1 "P: "
              addClauseSub true M.empty c
         | c <- groundCs
         ]

       sequence_
         [ addGroundAtom (the l)
         | c <- nonGroundCs
         , l <- c
         ]

       if noConstants
         then star `app` []
         else return true

       solveAndPatch False true 0 0 nonGroundCs
 where
  put   v s = when (v <= verbose flags) $ lift $ do putStr s;   hFlush stdout
  putLn v s = when (v <= verbose flags) $ lift $ do putStrLn s; hFlush stdout

  (groundCs,nonGroundCs') = partition isGround cs

  nonGroundCs = concatMap (norm []) nonGroundCs'

  syms = symbols cs

  fs' = S.filter (\f ->
    case f of
      _ ::: (_ :-> t) -> t /= bool
      _               -> False) syms

  trueX = prim "True" ::: V bool

  star = prim "*" ::: ([] :-> top)

  noConstants =
    null [ c | c@(_ ::: ([] :-> _)) <- S.toList fs' ]

  fs | noConstants = star `S.insert` fs'
     | otherwise   = fs'

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
    [[]]

  norm ls' (l : ls) =
    norm (l : ls') ls

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

  solveAndPatch starred true m n nonGroundCs =
    do putLn 2  "==> FolSat: solving..."
       b <- solve flags []
       if b then
         do putLn 2 "==> FolSat: checking (for all-false clauses)..."
            true' <- getModelRep true
            conss <- getModelCons
            putLn 2 ("(" ++ show (S.size conss) ++ " elements in domain)")
            let cons = S.toList conss
            b <- checkNonGoodCases true' cons False False nonGroundCs
            if b then
              do solveAndPatch starred true m n nonGroundCs
             else
              do case dot flags of
                   Just ds -> writeModel ("model-" ++ show m) true' syms ds
                   Nothing -> return ()
                 b <- if n > strength flags then
                        do return False
                       else
                        do putLn 2 "==> FolSat: checking (for non-true clauses)..."
                           checkNonGoodCases true' cons True False nonGroundCs
                 if b then
                   do solveAndPatch starred true (m+1) (n+1) nonGroundCs
                  else
                   do if not starred then
                        do putLn 2 "==> FolSat: instantiating with * ..."
                           sequence_
                             [ do s <- star `app` []
                                  addClauseSub true (M.fromList [ (x,s) | x <- S.toList (free c) ]) c
                             | c <- nonGroundCs
                             ]
                           solveAndPatch True true (m+1) 0 nonGroundCs
                       else
                         do putLn 2 "==> FolSat: checking (for liberal false clauses)..."
                            b <- checkNonGoodCases true' cons False True nonGroundCs
                            if b then
                              do solveAndPatch starred true (m+1) 0 nonGroundCs
                             else
                              do putLn 2 "==> FolSat: NO"
                                 return False
         else
          do return True

  dollard m ('%':'d':s) = show m ++ dollard m s
  dollard m (c:s)       = c : dollard m s
  dollard m ""          = ""

  getModelCons =
    do tabs <- sequence [ getModelTable f | f <- S.toList fs ]
       return (S.fromList [ c | tab <- tabs, (_,c) <- tab ])

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

  checkNonGoodCases true cons undef liberal nonGroundCs =
    do tryAll [ do --lift $ print ("==>",cl,defs,neqs)
                   r <- nonGoodCases [] defs neqs [] (S.delete trueX (free cl)) (M.singleton trueX true) $ \sub ->
                     do --lift $ putStrLn "Adding..."
                        b <- evalClauseSub true sub cl
                        if b then
                          do -- this substitution is already True
                             --lift $ print ("NO:",cl,sub)
                             return False
                         else
                          do put 1 (if liberal then "L: " else if undef then "U: " else "I: ")
                             --lift $ print (cl,sub)
                             addClauseSub true sub cl
                             return True
                   --lift $ putStrLn "OK"
                   return r

              | cl <- nonGroundCs
              , let (defs,neqs) = cclause cl
              ]
   where
    nonGoodCasesSub x c eqs defs neqs undefs still sub add =
      do --lift (print (x,c,eqs,sub))
         st <- star `app` []
         s <- getModelRep st
         let look_c = M.lookup x sub

             new_c = case look_c of
                       Just c' | c == s -> c'
                       _                -> c
          in case look_c of
               Just c' | c' /= c && (not liberal || s /= c && s /= c') ->
                 do --lift (print "no 1")
                    return False

               _ | null [ x' | (_,x') <- undefs, x == x' ]
                     && and [ case M.lookup y sub of
                                Just c' | c == c' -> False
                                _                 -> True
                            | y <- matches x neqs
                            ] ->
                 do --lift (print "yes")
                    nonGoodCases eqs defs neqs undefs (S.delete x still) (M.insert x new_c sub) add

               _ ->
                 do --lift (print "no 2")
                    return False

    nonGoodCases ((Var x,c):eqs) defs neqs undefs still sub add =
      nonGoodCasesSub x c eqs defs neqs undefs still sub add

    nonGoodCases ((Fun f ts,c):eqs) defs neqs undefs still sub add =
      do --lift $ print ((Fun f ts,c):eqs,defs,neqs,undefs,still)
         st <- star `app` []
         s <- getModelRep st
         tab <- getModelTable f
         tryAll [ nonGoodCases ((ts `zip` xs) ++ eqs) defs neqs undefs still sub add
                | (xs,y) <- tab
                , y == c || liberal && (y == s || c == s)
               -- , y == c -- STAR SUBST TEMP. REMOVED FOR EXPERIMENTAL REASONS
                ]

    nonGoodCases [] ((Fun f ts,x):defs) neqs undefs still sub add =
      do --lift $ print ("defs",(Fun f ts,x):defs,neqs,undefs,still)
         tab <- getModelTable f
         --lift $ print tab
         many $ [ nonGoodCasesSub x y (ts `zip` xs) defs neqs undefs still sub add
                | (xs,y) <- tab
                ]
             ++ [ nonGoodCases [] defs neqs ((Fun f ts,x):undefs) (S.delete x still) sub add
                | undef
                , M.lookup x sub == Nothing
                , not (x `S.member` free ts)
                , null [ y
                       | y <- matches x neqs
                       , (_,y') <- undefs
                       , y == y'
                       ]
                ]
     where
      many | not undef = tryAll
           | otherwise = findOne

{-
    nonGoodCases [] [] neqs undefs still sub add
     | acyclic && (not undef || S.size still == 0) =
      do --lift $ print ("acyclic",neqs,undefs,still)
         many [ instantiate undefs sub' add
              | sub' <- (sub `M.union`) `fmap` fairEnums (S.toList still)
              , all (\(x,y) -> (M.lookup x sub' :: Maybe Con) /= M.lookup y sub') neqs
              ]
-}
    nonGoodCases [] [] neqs undefs still sub add
     | acyclic
         && ( S.size still == 0
           || ( not liberal
             && all (`S.member` neqs') (S.toList still)
              )
            ) =
      do --lift $ print ("acyclic",(neqs,undefs,still,sub,enums))
         many [ do instantiate undefs sub' add
              | sub' <- (sub `M.union`) `fmap` enums
              , all (\(x,y) -> (M.lookup x sub' :: Maybe Con) /= M.lookup y sub') neqs
              ]
     where
      enums = fairEnums (S.toList still)

      neqs' = S.fromList [ z | (x,y) <- neqs, z <- [x,y] ]

      many = findOne

      unTab =
        M.fromList [ (x,t) | (t,x) <- undefs ]

      uns =
        S.fromList [ x | (_,x) <- undefs ]

      acyclic = top degrees indeps
       where
        nodes =
          [ (x, S.toList (free t `S.intersection` uns))
          | (t,x) <- undefs
          ]

        indeps =
          [ x
          | (x,_) <- nodes
          , M.lookup x degrees == Nothing
          ]

        graph =
          M.fromList nodes

        degrees =
          M.fromListWith (+)
          [ (y,1)
          | (x,ys) <- nodes
          , y <- ys
          ]

        top degrees []     = M.null degrees
        top degrees (x:xs) =
          case M.lookup x graph of
            Just ys -> tops degrees ys xs

        tops degrees []     xs = top degrees xs
        tops degrees (y:ys) xs =
          case M.lookup y degrees of
            Just k
              | k == 1    -> tops (M.delete y degrees) ys (y:xs)
              | otherwise -> tops (M.insert y (k-1) degrees) ys xs
            Nothing       -> tops degrees ys xs

      fairEnums xs =
        [ M.fromList (xs `zip` cs) | cs <- fair (length xs) cons ]

      instantiate undefs sub add =
        do as <- sequence [ eval t | (t,_) <- undefs ]
           if all isNothing as
             then do sub' <- createSubList undefs sub
                     add sub'
             else do return False
       where
        createSubList [] sub =
          do return sub

        createSubList ((t,x):undefs) sub =
          case M.lookup x sub of
            Nothing ->
              do (c,sub') <- createSubTerm t sub
                 createSubList undefs (M.insert x c sub')

            Just _ ->
              do createSubList undefs sub

        createSubTerm (Var x) sub =
          case M.lookup x sub of
            Nothing ->
              case M.lookup x unTab of
                Just t ->
                  do (c,sub') <- createSubTerm t sub
                     return (c,M.insert x c sub')

                Nothing ->
                  error "variable not defined: A"
                  --do return (c0, M.insert x c0 sub)

            Just c ->
              do return (c,sub)

        createSubTerm (Fun f ts) sub =
          do (cs,sub') <- createSubTermList ts sub
             c <- f `app` cs
             return (c,sub')

        createSubTermList [] sub =
          do return ([],sub)

        createSubTermList (t:ts) sub =
          do (c,sub') <- createSubTerm t sub
             (cs,sub2) <- createSubTermList ts sub'
             return (c:cs,sub2)

        eval (Var x) =
          return $
            case M.lookup x sub of
              Just c               -> Just c
              Nothing
                | x `S.member` M.keysSet unTab -> Nothing
                | otherwise          -> error "variable not defined: B"

        eval (Fun f ts) =
          do tab <- getModelTable f
             mcs <- sequence [ eval t | t <- ts ]
             if Nothing `elem` mcs
               then return Nothing
               else return (lookup [ c | Just c <- mcs ] tab)

    nonGoodCases [] [] neqs undefs still sub add =
      do return False

evalClauseSub :: Con -> Map Symbol Con -> Clause -> T Bool
evalClauseSub true sub cl =
  do ls <- sequence [ literal l | l <- cl ]
     return (any (== Just True) ls)
 where
  term (Var x) =
    do return (M.lookup x sub)

  term (Fun f ts) =
    do as <- sequence [ term t | t <- ts ]
       if all isJust as
         then do tab <- getModelTable f
                 case [ y | (xs,y) <- tab, xs == [ a | Just a <- as ] ] of
                   []  -> return Nothing
                   y:_ -> return (Just y)
         else do return Nothing

  atom (s :=: t) | t == truth =
    do a <- term s
       return (a =?= Just true)

  atom (s :=: t) =
    do a <- term s
       b <- term t
       return (a =?= b)

  Nothing =?= _       = Nothing
  _       =?= Nothing = Nothing
  Just x  =?= Just y  = Just (x == y)

  literal (Pos a) = atom a
  literal (Neg a) = fmap not `fmap` atom a

addClauseSub :: Con -> Map Symbol Con -> Clause -> T ()
addClauseSub true sub cl =
  do ls <- sequence [ literal l | l <- cl ]
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

addGroundAtom :: Atom -> T ()
addGroundAtom (a :=: b) =
  do term a
     term b
     return ()
 where
  term t | t == truth =
    do return Nothing

  term (Var x) =
    do return Nothing

  term (Fun f ts) =
    do mas <- sequence [ term t | t <- ts ]
       if any isNothing mas
         then do return Nothing
         else do b <- f `app` [ a | Just a <- mas ]
                 return (Just b)

--writeModel :: FilePath -> Con -> Set (Name,Int) -> Set (Name,Int) -> T ()
writeModel file true fs ds =
  do lift $ putStrLn ("(writing model in " ++ file ++ ")")
     h <- lift $ openFile file WriteMode
     lift $ hPutStrLn h "digraph G {"

     -- nodes
     nodess <-
       sequence
         [ do tab <- getModelTable f
              return [ x | (xs,y) <- tab, x <- y:xs ]
         | f <- S.toList fs
         , show f `elem` interesting
         ]

     -- attributes
     attrss <-
       sequence
         [ do tab <- getModelTable f
              return $
                [ (x,f)
                | isPred f
                , ([x],tr) <- tab
                , tr == true
                ] ++
                [ (x,f)
                | not (isPred f)
                , ([],x) <- tab
                ]
         | f <- S.toList fs
         , show f `elem` interesting
         ]
     let attrs = concat attrss

     -- arrows
     arrowss <-
       sequence
         [ do tab <- getModelTable f
              return $
                [ (x,y,f)
                | isPred f
                , ([x,y],tr) <- tab
                , tr == true
                ] ++
                [ (x,y,f)
                | not (isPred f)
                , ([x],y) <- tab
                ]
         | f <- S.toList fs
         , show f `elem` interesting
         ]
     let arrows = concat arrowss

     let nodes = nub ( [ x | (x,_) <- attrs ]
                    ++ [ z | (x,y,_) <- arrows, z <- [x,y] ]
                     )

     sequence_
       [ lift $ hPutStrLn h (shown x ++ " [label=\"" ++ lab ++ "\"];")
       | x <- nodes
       , let attr = [ p | (y,p) <- attrs, x == y ]
             lab  | null attr = show x
                  | otherwise = show x ++ "\\n" ++ concat (intersperse "," (map show attr))
       ]

     sequence_
       [ lift $ hPutStrLn h (shown x ++ " -> " ++ shown y ++ " [label=\"" ++ show f ++ "\"];")
       | (x,y,f) <- arrows
       ]
     lift $ hPutStrLn h "}"
     lift $ hClose h
 where
  showArgs f [] = show f
  showArgs f ts = show f ++ show ts

  --line f xs y = showArgs f xs ++ " = " ++ show y

  isPred (_ ::: (_ :-> t)) = t == bool
  isPred _                 = False

  shown n = tail (show n)

  interesting = words (map (\c -> if c == ',' then ' ' else c) ds)

