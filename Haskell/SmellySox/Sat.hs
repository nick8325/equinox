module SmellySox.Sat where

import Sat
import SmellySox.Utils
import Control.Monad
import qualified Data.Map as Map

data Formula a = Var a
               | Formula a :&: Formula a
               | Formula a :|: Formula a
               | Not (Formula a)
               | Formula a :=: Formula a
               | FTrue
               | FFalse

(-->) :: Formula a -> Formula a -> Formula a
f --> g = Not f :|: g

conj,disj :: [Formula a] -> Formula a
conj = foldr (:&:) FTrue
disj = foldr (:|:) FFalse

solve :: Ord a => Formula a -> IO (Maybe (a -> Bool))
solve f = run $ do
  let vs = vars f
  lits <- replicateM (length vs) newLit
  let varMap = Map.fromList (zip vs lits)
  l <- solve' (\x -> Map.findWithDefault (error "solve: varMap") x varMap) f
  addClause [l]
  b <- Sat.solve []
  if b then fmap Just $ do
     vals <- mapM getModelValue lits
     let valMap = Map.fromList (zip vs vals)
     return (\x -> Map.findWithDefault (error "solve: valMap") x valMap)
    else return Nothing

solve' :: (a -> Lit) -> Formula a -> S Lit
solve' env (Var x) = return (env x)
solve' env (f :&: g) = join (liftM2 mkAnd (solve' env f) (solve' env g))
solve' env (f :|: g) = join (liftM2 mkOr (solve' env f) (solve' env g))
solve' env (Not f) = fmap neg (solve' env f)
solve' env (f :=: g) = join (liftM2 mkEqu (solve' env f) (solve' env g))
solve' _ FTrue  = return mkTrue
solve' _ FFalse = return mkFalse

vars :: Ord a => Formula a -> [a]
vars (Var x) = [x]
vars (f :&: g) = vars f `merge` vars g
vars (f :|: g) = vars f `merge` vars g
vars (Not f) = vars f
vars (f :=: g) = vars f `merge` vars g
vars _ = []
