module Paradox.AnalysisTypes
  ( types
  )
 where

import Form
import Name
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M

import Control.Monad.ST
  ( ST
  , runST
  )

import Data.STRef
  ( STRef
  , newSTRef
  , readSTRef
  , writeSTRef
  )

import Char
  ( ord
  , chr
  )

import List
  ( nub
  )

import Maybe
  ( fromJust
  )

---------------------------------------------------------------------------------
-- types

types :: [Clause] -> Either String ([Type], Clause -> Clause)
types cs = runT (inferClauses cs)

---------------------------------------------------------------------------------
-- infer

inferClauses :: [Clause] -> T s ()
inferClauses [] =
  do return ()

inferClauses (c:cs) =
  do scope (free c) $
       do sequence_ [ inferLit l | l <- c ]
     inferClauses cs

inferLit :: Signed Atom -> T s ()
inferLit (Pos x) = inferAtom True x
inferLit (Neg x) = inferAtom False x

inferAtom :: Bool -> Atom -> T s ()
inferAtom sgn (x :=: y) =
  do t1 <- inferTerm x
     t2 <- inferTerm y
     t1 =:= t2
     if sgn then
       touchEq t1 eq
      else
       return ()
 where
  eq = case (x,y) of
         (Var _, Var _) -> Full
         (Var _, _    ) -> Half
         (_    , Var _) -> Half
         _              -> Safe

inferTerm :: Term -> T s (TypeId s)
inferTerm (Var v) =
  do getVar v

inferTerm (Fun f xs) =
  do (ts,t) <- getFun f (length xs)
     inferAndUnify f xs ts
     return t

inferAndUnify :: Symbol -> [Term] -> [TypeId s] -> T s ()
inferAndUnify s xs ts
  | length xs == length ts = 
      sequence_
        [ do t' <- inferTerm x
             t =:= t'
        | (x,t) <- xs `zip` ts
        ]
  | otherwise =
      throw ( "Symbol '"
           ++ show s
           ++ "' used with different arities "
           ++ show (length xs)
           ++ " and "
           ++ show (length ts)
            )

---------------------------------------------------------------------------------
-- run

runT :: (forall s . T s a) -> Either String ([Type], Clause -> Clause)
runT tm =
  runST (
    do idfs  <- newSTRef 0
       preds <- newSTRef M.empty
       funs  <- newSTRef M.empty
       vars  <- newSTRef M.empty

       m idfs preds funs vars (\s -> return (Left s)) (\_ ->
         do ps' <- readSTRef preds
            fs' <- readSTRef funs

            ps <- sequence
                    [ do ts <- sequence [ do (_,t,_) <- typeInfo t'
                                             return t
                                        | t' <- ts'
                                        ]
                         return (p,ts)
                    | (p,ts') <- M.toList ps'
                    ]

            fs <- sequence
                    [ do ts <- sequence [ do (_,t,_) <- typeInfo t'
                                             return t
                                        | t' <- ts'
                                        ]
                         (_,t,_) <- typeInfo t'
                         return (f,(ts,t))
                    | (f,(ts',t')) <- M.toList fs'
                    ]

            typeIds' <- sequence
                          [ do ((_,eq),t,_) <- typeInfo t' 
                               return (t,eq)
                          | t' <- [ t | (_,ts)      <- M.toList ps', t <- ts ]
                               ++ [ t | (_,(ts,tr)) <- M.toList fs', t <- tr:ts ]
                          ]

            let typeIds = S.toList (S.fromList typeIds')

                names =
                  [ s
                  | i <- [1..]
                  , let s | i <= 26   = name [chr (ord 'A' + i - 1)]
                          | otherwise = name "T" % (i-26)
                  ]

                typesAndTypeIds =
                  [ ( Type
                      { tname   = s
                      , tdomain = n
                      , tequal  = eq
                      }
                    , t
                    )
                  | (s,(t,eq)) <- names `zip` typeIds
                  , let fResT = [ (f,length ts) | (f,(ts,t')) <- fs, t == t' ]
                        n = case [ ar | (f,ar) <- fResT, ar > 0 ] of
                              [] -> Just (length fResT `max` 1)
                              _  -> Nothing
                  ]

                types =
                  [ t | (t,_) <- typesAndTypeIds ]

                typeIdToType =
                  M.fromList [ (tid,t)
                             | (t,tid) <- typesAndTypeIds
                             ]

                typeOfId tid =
                  case M.lookup tid typeIdToType of
                    Just t  -> t
                    Nothing -> error "Types: no type"

                predTable =
                  M.fromList [ (n, map typeOfId ts :-> bool)
                             | (n ::: _, ts) <- ps
                             ]

                funTable =
                  M.fromList [ (n, map typeOfId ts :-> typeOfId t)
                             | (n ::: _, (ts,t)) <- fs
                             ]

                typeOfPred (p ::: _) =
                  case M.lookup p predTable of
                    Just t  -> t
                    Nothing -> error $ "Types: no pred type"

                typeOfFun (f ::: _) =
                  case M.lookup f funTable of
                    Just t  -> t
                    Nothing -> error "Types: no fun type"

                trans c = map transLit c
                 where
                  ls = c

                  varsLit (Pos a) = varsAtom a
                  varsLit (Neg a) = varsAtom a

                  varsAtom (y :=: Fun f xs) =
                    varsTerms ((y,t):(xs `zip` ts))
                   where
                    ts :-> t = typeOfFun f

                  varsAtom (Fun f xs :=: y) =
                    varsTerms ((y,t):(xs `zip` ts))
                   where
                    ts :-> t = typeOfFun f

                  varsAtom (x :=: y) =
                    varsTerms [(x,top),(y,top)]

                  varsTerms [] = []
                  varsTerms ((Fun f xs,_):xts) = varsTerms ((xs `zip` ts)++xts)
                   where
                    ts :-> _ = typeOfFun f

                  varsTerms ((Var (n ::: _),t):xts)
                    | t == top  = varsTerms xts
                    | otherwise = (n,V t) : varsTerms xts

                  varTable =
                    M.fromList (concatMap varsLit ls)

                  transLit (Pos a) = Pos (transAtom a)
                  transLit (Neg a) = Neg (transAtom a)

                  transAtom (x :=: y) = transTerm x :=: transTerm y

                  transTerm (Fun f@(n ::: (_ :-> t)) xs) = Fun f' (map transTerm xs)
                   where
                    ts :-> t' = typeOfFun f
                    f' = n ::: (ts :-> (if t == bool then bool else t'))

                  transTerm (Var v@(n ::: _)) = Var v'
                   where
                    v' = n ::: case M.lookup n varTable of
                                 Just t  -> t
                                 Nothing -> V top

            return (Right (types, trans))
        )
  )
 where
  MkT m = tm

-------------------------------------------------------------------------
-- T monad

type TypeInfo =
  (Int,Equality)

data TypeId s =
  MkTypeId !Int !(STRef s (Either TypeInfo (TypeId s)))

instance Eq (TypeId s) where
  MkTypeId n1 _ == MkTypeId n2 _ = n1 == n2

instance Ord (TypeId s) where
  MkTypeId n1 _ `compare` MkTypeId n2 _ = n1 `compare` n2

newtype T s a =
  MkT ( forall b
      . STRef s Int                                 -- unique name table
     -> STRef s (Map Symbol [TypeId s])             -- predicate table
     -> STRef s (Map Symbol ([TypeId s], TypeId s)) -- function table
     -> STRef s (Map Symbol (TypeId s))             -- variable table
     -> (String -> ST s b)
     -> (a -> ST s b)
     -> ST s b
      )

-- monad

instance Monad (T s) where
  return x =
    MkT (\idfs preds funs vars fail ok ->
      ok x
    )

  MkT m1 >>= k =
    MkT (\idfs preds funs vars fail ok ->
      m1 idfs preds funs vars fail (\a ->
        let MkT m2 = k a in
          m2 idfs preds funs vars fail ok
    ))

-- primitives

getIdfs :: T s (STRef s Int)
getIdfs = MkT (\idfs preds funs vars fail ok -> ok idfs)

getPreds :: T s (STRef s (Map Symbol [TypeId s]))
getPreds = MkT (\idfs preds funs vars fail ok -> ok preds)

getFuns :: T s (STRef s (Map Symbol ([TypeId s], TypeId s)))
getFuns = MkT (\idfs preds funs vars fail ok -> ok funs)

getVars :: T s (STRef s (Map Symbol (TypeId s)))
getVars = MkT (\idfs preds funs vars fail ok -> ok vars)

throw :: String -> T s a
throw s = MkT (\idfs preds funs vars fail ok -> fail s)

lift :: ST s a -> T s a
lift m = MkT (\_ _ _ _ _ ok -> do a <- m; ok a)

-- derived

new :: T s (TypeId s)
new =
  do ref  <- lift (newSTRef (Left (1,Safe)))
     idfs <- getIdfs
     n    <- lift $ readSTRef idfs
     let n' = n + 1
     n' `seq` lift (writeSTRef idfs n')
     return (MkTypeId n ref)

typeInfo :: TypeId s -> ST s (TypeInfo, Int, STRef s (Either TypeInfo (TypeId s)))
typeInfo (MkTypeId i ref) =
  do mref <- readSTRef ref
     case mref of
       Left inf -> do return (inf,i,ref)
       Right t  -> do (inf,i,c) <- typeInfo t
                      writeSTRef ref (Right (MkTypeId i c))
                      return (inf,i,c)
                      
touchEq :: TypeId s -> Equality -> T s ()
touchEq t eq' =
  do ((n,eq),_,ref) <- lift (typeInfo t)
     lift $ writeSTRef ref (Left (n,eq `max` eq'))

getPred :: Symbol -> Int -> T s [TypeId s]
getPred p n =
  do preds <- getPreds
     ps    <- lift (readSTRef preds)
     case M.lookup p ps of
       Just ts -> do return ts
       Nothing -> do ts <- sequence [ new | i <- [1..n] ]
                     lift (writeSTRef preds (M.insert p ts ps))
                     return ts

getFun :: Symbol -> Int -> T s ([TypeId s], TypeId s)
getFun f n =
  do funs <- getFuns
     fs   <- lift (readSTRef funs)
     case M.lookup f fs of
       Just (ts,t) -> do return (ts,t)
       Nothing     -> do ts <- sequence [ new | i <- [1..n] ]
                         t  <- new
                         lift (writeSTRef funs (M.insert f (ts,t) fs))
                         return (ts,t)

scope :: Set Symbol -> T s a -> T s a
scope news tm =
  do vars <- getVars
     vs   <- lift (readSTRef vars)
     vts  <- sequence
               [ do t <- new
                    return (v,t)
               | v <- S.toList news
               ]
     lift (writeSTRef vars (vs `M.union` M.fromList vts)) -- order is important
     a    <- tm
     lift (writeSTRef vars vs)
     return a

getVar :: Symbol -> T s (TypeId s)
getVar v =
  do vars <- getVars
     vs   <- lift (readSTRef vars)
     case M.lookup v vs of
       Just t  -> do return t
       Nothing -> do error "var not in scope"

(=:=) :: TypeId s -> TypeId s -> T s ()
MkTypeId i1 ref1 =:= MkTypeId i2 ref2 =
  lift (
    do unify i1 ref1 i2 ref2
       return ()
  )
 where
  unify i1 ref1 i2 ref2
    | ref1 == ref2 = return (i1,ref1)
    | otherwise    =
        do mref1 <- readSTRef ref1
           case mref1 of
             Left (n1,eq1) ->
               do mref2 <- readSTRef ref2
                  case mref2 of
                    Left (n2,eq2) | n1 < n2 ->
                      do writeSTRef ref1 (Right (MkTypeId i2 ref2))
                         writeSTRef ref2 (Left (n1+n2,(eq1 `max` eq2)))
                         return (i2,ref2)
                    
                                  | otherwise ->
                      do writeSTRef ref2 (Right (MkTypeId i1 ref1))
                         writeSTRef ref1 (Left (n1+n2,(eq1 `max` eq2)))
                         return (i1,ref1)
                    
                    Right (MkTypeId i2' ref2') ->
                      do (i,ref) <- unify i1 ref1 i2' ref2'
                         writeSTRef ref2 (Right (MkTypeId i ref))
                         return (i,ref)
                      
             Right (MkTypeId i1' ref1') ->
               do (i,ref) <- unify i1' ref1' i2 ref2
                  writeSTRef ref1 (Right (MkTypeId i ref))
                  return (i,ref)

unifyList :: [TypeId s] -> T s ()
unifyList []     = return ()
unifyList (t:ts) = sequence_ [ t' =:= t | t' <- ts ]

-------------------------------------------------------------------------
-- the end.
