module EquiParadox.Main where

{-
Paradox -- Copyright (c) 2003-2007, Koen Claessen, Niklas Sorensson

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

import qualified Main
import Flags

import Form
import Name
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import Data.Maybe( fromJust )

import Paradox.AnalysisTypes
import Paradox.Flatten( simplify, splitAll )

import Equinox.TermSat

import Output

import IO
  ( hFlush
  , stdout
  )

import List
  ( sortBy
  , partition
  )

import System
  ( exitWith
  , ExitCode(..)
  )

head' s [] = error ("head " ++ s)
head' _ xs = head xs

---------------------------------------------------------------------------
-- main

main :: IO ()
main =
  do putStrLn "EquiParadox, version 1.0, 2008-07."
     Main.main solveProblem

-------------------------------------------------------------------------
-- problem

solveProblem :: (?flags :: Flags) => [Clause] -> IO Answer
solveProblem csIn =
  run $
    do lift $ putStrLn "Start!"
       d1 <- newCon "!1"
       lift $ putStrLn "Calculating types..."
       lift $ putStrLn (show typs)
       lift $ putStrLn "Creating domain leq-literals..."
       leqs <- sequence
                 [ case tdomain t of
                     Just 1 -> return (Bool True)
                     _      -> newLit
                 | t <- typs
                 ]
       lift $ putStrLn "Instantiating for all domains {1}..."
       sequence_ [ instantiateDomains1 d1 c | c <- cs ]
       lift $ putStrLn "Iterating over domain sizes..."
       loopDomainSizes flags syms [ (t,1,[leq]) | (t,leq) <- typs `zip` leqs ] (1,[d1]) cs
 where
  flags = ?flags

  csSimp                     = concatMap Paradox.Flatten.simplify (splitAll csIn)
  mTypeResult                = types csSimp
  Right (typs,annotateTypes) = mTypeResult
  cs                         = map annotateTypes csSimp
  symsSet                    = symbols cs
  syms                       = [ f | f <- S.toList symsSet, not (isVarSymbol f) ]

-------------------------------------------------------------------------
-- instantiation

instantiateDomains1 :: Con -> Clause -> T ()
instantiateDomains1 d c =
  do instClauses [(x,[d]) | x <- S.toList (free c)] c

instantiateDomains :: [(Type,Int,[Lit])] -> Maybe (Type,Int) -> (Int,[Con]) -> Clause -> T ()
instantiateDomains tps mtk (n,ds) c =
  case mtk of
    Nothing    -> instClauses (map pair allVs) c
    Just (t,k) -> insts (map pair oldVs) newVs
     where
      (newVs,oldVs) = partition isNew allVs
      isNew v       = typ (Var v) == t

      ds'           = take k ds
      d'            = last ds'

      insts oldVs []     = do return ()
      insts oldVs (v:vs) = do instClauses (oldVs ++ [(v,[d'])] ++ [(v,init ds') | v <- vs]) c
                              insts ((v,ds'):oldVs) vs
 where
  allVs         = S.toList (free c)
  pair x        = (x,take (typeSize x) ds)
  typeSize x    = head' "112" [ k | (t,k,_) <- tps, typ (Var x) == t ]

instClauses :: [(Symbol,[Con])] -> Clause -> T ()
instClauses vars c = insts vars M.empty
 where
  insts []            mp = instClause mp c
  insts ((x,ds):vars) mp = sequence_ [ insts vars (M.insert x d mp) | d <- ds ]

instClause :: Map Symbol Con -> Clause -> T ()
instClause mp c =
  do ls <- sequence [ instLit mp l | l <- c ]
     addClause ls

instLit :: Map Symbol Con -> Signed Atom -> T Lit
instLit mp (Pos a) = instAtom mp a
instLit mp (Neg a) = neg `fmap` instAtom mp a

instAtom :: Map Symbol Con -> Atom -> T Lit
instAtom mp (s Form.:=: t) =
  do x <- instTerm mp s
     y <- instTerm mp t
     return (x Equinox.TermSat.:=: y)

instTerm :: Map Symbol Con -> Term -> T Con
instTerm mp (Var x) =
  do return (fromJust (M.lookup x mp))

instTerm mp (Fun f ts) =
  do xs <- sequence [ instTerm mp t | t <- ts ]
     f `app` xs

-------------------------------------------------------------------------
-- looping through domain sizes

loopDomainSizes :: Flags -> [Symbol] -> [(Type,Int,[Lit])] -> (Int,[Con]) -> [Clause] -> T Answer
loopDomainSizes flags syms tps (n,ds) cs =
  do lift$ putStrLn $
          "solving... ("
       ++ unwords [ show t ++ "=" ++ show k | (t,k,_) <- tps ]
       ++ ")"
     b <- solve flags [ leqk | (_,_,leqk:_) <- tps ]
     if b then
       do checkTotality flags syms tps (n,ds) cs
      else
       do cnf <- conflict
          if null cnf then
            do return Unsatisfiable
           else
            let tp =
                  head' "161" (sortBy cmp [ tp | tp@(_,_,leqk:_) <- tps, neg leqk `elem` cnf ])

                (_,k1,_) `cmp` (_,k2,_) =
                  k1 `compare` k2

             in increaseDomain flags syms tp tps (n,ds) cs

checkTotality :: Flags -> [Symbol] -> [(Type,Int,[Lit])] -> (Int,[Con]) -> [Clause] -> T Answer
checkTotality flags syms tps (n,ds) cs =
  do bs <- sequence [ checkTotalitySym f tps (n,ds) | f <- syms ]
     if and bs then
       do return Satisfiable
      else
       do loopDomainSizes flags syms tps (n,ds) cs

checkTotalitySym :: Symbol -> [(Type,Int,[Lit])] -> (Int,[Con]) -> T Bool
checkTotalitySym (f@(_ ::: (_ :-> t))) tps (n,ds) | t == bool =
  do return True

checkTotalitySym (f@(_ ::: (_ :-> t))) tps (n,ds) =
  do leqs' <- sequence [ getModelValue leq | leq <- leqs ]
     let (k,leq) = head' "179" [ (k,leq) | (k,(leq,True)) <- [1..] `zip` reverse (leqs `zip` leqs') ]
     ds' <- sequence [ getModelRep d | d <- take k ds ]
     tab <- getModelTable f
     bs  <- sequence [ do y <- f `app` xs
                          addClause (neg leq : [ y Equinox.TermSat.:=: d | d <- take k ds ])
                          {-
                          lift $ putStrLn $
                               show t ++ "<=" ++ show k ++ " ==> "
                            ++ show [ (f,xs,d) | d <- take k ds ]
                          -}
                          return False
                     | (xs,y) <- tab
                     , y `notElem` ds'
                     ]
     return (and bs)
 where
  leqs = head' "193" [ leqs | (t',k,leqs) <- tps, t == t' ]

increaseDomain :: Flags -> [Symbol] -> (Type,Int,[Lit]) -> [(Type,Int,[Lit])] -> (Int,[Con]) -> [Clause] -> T Answer
increaseDomain flags syms tp@(t,k,leqs@(leqk:_)) tps (n,ds) cs =
  do cnf <- conflict
     if null cnf then
       do return Unsatisfiable
      else
       do leqk' <- case tdomain t of
                     Just k' | k' <= k+1 -> return (Bool True)
                     _                   -> newLit
          addClause [neg leqk,leqk'] -- d<=k -> d<=k+1

          let tp' =
                (t,k+1,leqk':leqs)

              tps' =
                [ if t2 == t
                    then tp'
                    else tp2
                | tp2@(t2,_,_) <- tps
                ]

              n' | k >= n    = k+1
                 | otherwise = n

          ds' <- if n' > n
                   then do d' <- newCon (show n'); return (ds++[d'])
                   else do return ds

          lift $ putStrLn $
            "instantiating... (" ++ show t ++ "++)"
          sequence_ [ do lift $ print c
                         instantiateDomains tps' (Just (t,k+1)) (n',ds') c
                    | c <- cs
                    ]
          loopDomainSizes flags syms tps' (n',ds') cs

---------------------------------------------------------------------------
-- the end.
