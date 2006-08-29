module Equinox.FolSat where

import Form
import Name( prim )
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
              do putLn 2 "==> FolSat: checking (for non-true clauses)..."
                 b <- return False -- checkNonGoodCases true' cons True False nonGroundCs
                 if b && n <= strength flags then
                   do solveAndPatch starred true m (n+1) nonGroundCs
                  else
                   if not starred then
                     do putLn 2 "==> FolSat: instantiating with * ..."
                        sequence_
                          [ do s <- star `app` []
                               addClauseSub true (M.fromList [ (x,s) | x <- S.toList (free c) ]) c
                          | c <- nonGroundCs
                          ]
                        solveAndPatch True true m 0 nonGroundCs
                    else
                     do putLn 2 "==> FolSat: checking (for liberal non-true clauses)..."
                        b <- checkNonGoodCases true' cons False {- True -} True nonGroundCs
                        if b then
                          do solveAndPatch starred true m 0 nonGroundCs
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
                          do put 1 (if undef then if liberal then "L: " else "U: " else "I: ")
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

    nonGoodCases [] [] neqs undefs still sub add
     | acyclic && (not undef || S.size still == 0) =
      do --lift $ print ("acyclic",neqs,undefs,still)
         many [ instantiate undefs sub' add
              | sub' <- (sub `M.union`) `fmap` fairEnums (S.toList still)
              , all (\(x,y) -> (M.lookup x sub' :: Maybe Con) /= M.lookup y sub') neqs
              ]
     where
      many = tryAll -- | not undef = tryAll
           -- | otherwise = findOne
      
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
             (cs,sub'') <- createSubTermList ts sub'
             return (c:cs,sub'')

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

{-
writeModel :: FilePath -> Con -> Set (Name,Int) -> Set (Name,Int) -> T ()
writeModel file true fs ps =
  do h <- lift $ openFile file WriteMode
     sequence_
       [ do tab <- getModelTable f
            sequence_
              [ lift $ hPutStrLn h (showArgs f xs ++ " = " ++ show y)
              | (xs,y) <- tab
              ]
            lift $ hPutStrLn h ""
       | (f,_) <- S.toList fs
       ]
     sequence_
       [ do tab <- getModelTable p
            sequence_
              [ lift $ hPutStrLn h (showArgs p xs ++ " : " ++
                  (if y == true then "$true" else "$false"))
              | (xs,y) <- tab
              ]
            lift $ hPutStrLn h ""
       | (p,_) <- S.toList ps
       , p /= eq
       ]
     lift $ hClose h
 where
  showArgs f [] = show f
  showArgs f ts = show f ++ show ts
-}
