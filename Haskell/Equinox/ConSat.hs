module Equinox.ConSat
  ( C             -- :: * -> *; Functor, Monad
  , Lit(..)       -- :: *; Eq, Ord, Show
  , Con           -- :: *; Eq, Ord, Show
  , Weight        -- :: *
  , wapp
  , weight
  
  , run           -- :: C a -> IO a
  , lift          -- :: IO a -> C a
  , contradiction -- :: C ()
  , newLit        -- :: C Sat.Lit
  , newCon        -- :: String -> Weight -> C Con
  , neg           -- :: Lit -> Lit
  , getValue      -- :: Lit -> C (Maybe Bool)
  , getRep        -- :: Con -> C Con
  , getModelValue -- :: Lit -> C Bool -- use only after model has been found!
  , getModelRep   -- :: Con -> C Con  -- use only after model has been found!
  , addClause     -- :: [Lit] -> C ()
  , solve         -- :: Flags -> [Lit] -> C Bool
  , simplify      -- :: C ()
  )
 where
 
import qualified Sat
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import IO
import Flags
import Control.Monad
import List( intersperse )

data Lit
  = Lit Sat.Lit
  | Con :=: Con
  | Con :/=: Con
  | Bool Bool

instance Eq Lit where
  l1 == l2 = l1 `compare` l2 == EQ

instance Ord Lit where
  Lit l1       `compare` Lit l2       = l1 `compare` l2
  (a1 :=: b1)  `compare` (a2 :=: b2)  = upair a1 b1 `compare` upair a2 b2
  (a1 :/=: b1) `compare` (a2 :/=: b2) = upair a1 b1 `compare` upair a2 b2
  Bool b1      `compare` Bool b2      = b1 `compare` b2
  
  Bool _    `compare` _         = LT
  _         `compare` Bool _    = GT
  Lit _     `compare` _         = LT
  _         `compare` Lit _     = GT
  (_ :=: _) `compare` _         = LT
  _         `compare` (_ :=: _) = GT

instance Show Lit where
  show (Lit x)      = show x
  show (s :=: t)    = show s ++ " = " ++ show t
  show (s :/=: t)   = show s ++ " != " ++ show t
  show (Bool True)  = "$true"
  show (Bool False) = "$false"

upair :: Ord a => a -> a -> (a,a)
upair x y | x <= y    = (x,y)
          | otherwise = (y,x)

neg :: Lit -> Lit
neg (Lit x)    = Lit (Sat.neg x)
neg (a :=: b)  = a :/=: b
neg (a :/=: b) = a :=: b
neg (Bool b)   = Bool (not b)

data Weight = MkWeight{ depth :: !Int, siz :: !Int }
 deriving ( Eq, Ord )
 
wapp :: [Weight] -> Weight
wapp ws = MkWeight (1 + maximum (0 : map depth ws)) (1 + sum (map siz ws))

-- Debugging ON

{-
data Con
  = Con !Weight !Int String

weight :: Con -> Weight
weight (Con w _ _) = w

con :: Int -> Weight -> String -> Con
con n w s = Con w n s

instance Eq Con where
  Con _ n1 _ == Con _ n2 _ = n1 == n2

instance Ord Con where
  Con w1 n1 _ `compare` Con w2 n2 _ = (w1,n1) `compare` (w2,n2)

instance Show Con where
  show (Con _ _ s) = s -- ++ "#" ++ show n
-}

-- Debugging OFF

data Con
  = Con !Weight !Int
 deriving ( Ord )

instance Eq Con where
  Con _ n1 == Con _ n2 = n1 == n2

weight :: Con -> Weight
weight (Con w _) = w

con :: Int -> Weight -> String -> Con
con n w s = Con w n

instance Show Con where
  show (Con _ n) = "#" ++ show n

data State
  = MkState
  { counter  :: Int
  , compares :: Map (Con,Con) Sat.Lit
  , reps     :: Map Con Con
  , model    :: Con -> Con
  }

state0 :: State
state0 = MkState
  { counter  = 0
  , compares = M.empty
  , reps     = M.empty
  , model    = error "model inspected before solve"
  }

newtype C a = MkC (State -> Sat.S (a, State))

instance Functor C where
  fmap f (MkC m) = MkC (fmap (\(x,s) -> (f x,s)) . m)

instance Monad C where
  return x = MkC (\s -> return (x,s))

  MkC m1 >>= k = MkC (\s0 ->
    do (x,s1) <- m1 s0
       let MkC m2 = k x
       m2 s1
    )

run :: C a -> IO a
run (MkC m) =
  do (x,_) <- Sat.run (m state0)
     return x

getState :: C State
getState = MkC (\s -> return (s,s))

setState :: State -> C ()
setState s = MkC (\_ -> return ((),s))

liftS :: Sat.S a -> C a
liftS m = MkC (\s -> do x <- m; return (x,s))  

lift :: IO a -> C a
lift io = liftS (Sat.lift io)

contradiction :: C ()
contradiction = liftS Sat.contradiction

newLit :: C Lit
newLit = Lit `fmap` liftS Sat.newLit

getEqLit :: Con -> Con -> C Lit
getEqLit a b =
  do a' <- getRep a
     b' <- getRep b
     case a' `compare` b' of
       LT -> getLit' a' b'
       EQ -> return (Bool True)
       GT -> getLit' b' a'
 where
  getLit' a b = MkC (\s ->
    case M.lookup (a,b) (compares s) of
      Just l  -> do return (Lit l, s)
      Nothing -> do l <- Sat.newLit
                    return ( Lit l
                           , s{ compares = M.insert (a,b) l (compares s) }
                           )
   )

newCon :: String -> Weight -> C Con
newCon x w = MkC (\s ->
  let n  = counter s
      n' = n+1
      c  = con n w x
   in n' `seq` c `seq` return (c, s{ counter = n' })
  )

getValue :: Lit -> C (Maybe Bool)
getValue (Lit x)    = liftS (Sat.getValue x)
getValue (a :=: b)  = checkEqual a b
getValue (a :/=: b) = fmap (fmap not) (checkEqual a b)
getValue (Bool b)   = return (Just b)

getModelValue :: Lit -> C Bool
getModelValue (Lit x)    = liftS (Sat.getModelValue x)
getModelValue (a :=: b)  = checkModelEqual a b
getModelValue (a :/=: b) = fmap not (checkModelEqual a b)
getModelValue (Bool b)   = return b

checkEqual = undefined

getRep :: Con -> C Con
getRep a =
  do s <- getState
     (a',s') <- rep s a
     setState s'
     return a'
 where
  rep s a =
    case M.lookup a (reps s) of
      Nothing -> do return (a,s)
      Just a' -> do (a'',s') <- rep s a'
                    return (a'', s{ reps = M.insert a a'' (reps s) })

setRep :: Con -> Con -> C ()
setRep a b =
  do a' <- getRep a
     b' <- getRep b
     s  <- getState
     case a' `compare` b' of
       LT -> setState s{ reps = M.insert b' a' (reps s) }
       EQ -> return ()
       GT -> setState s{ reps = M.insert a' b' (reps s) }

checkModelEqual :: Con -> Con -> C Bool
checkModelEqual a b =
  MkC (\s ->
    return (model s a == model s b, s)
  )

getModelRep :: Con -> C Con
getModelRep a =
  do a' <- getRep a
     MkC (\s -> return (model s a', s))

norm :: Lit -> C Lit
norm (a :=: b)  = getEqLit a b
norm (a :/=: b) = neg `fmap` getEqLit a b
norm x          = return x

addClause :: [Lit] -> C ()
addClause xs =
  do lift (putStr (showClause xs ++ "."))
     xs' <- (filter (/= Bool False)) `fmap` sequence [ simp x | x <- xs ]
     case xs' of
       _ | Bool True `elem` xs' ->
         do lift (putStrLn ("  [=> $true]"))
            lift (hFlush stdout)
            return ()
       
       [a :=: b] ->
         do lift (putStrLn ("  [=> " ++ show b ++ " := " ++ show a ++ "]"))
            lift (hFlush stdout)
            setRep a b

       _ ->
         do xs'' <- sequence [ norm x | x <- xs' ]
            lift (putStrLn "")
            lift (hFlush stdout)
            liftS (Sat.addClause [ x | Lit x <- xs'' ])
            return ()
 where
  simp (a :=: b) =
    do a' <- getRep a
       b' <- getRep b
       return $
         case a' `compare` b' of
           LT -> a' :=: b'
           EQ -> Bool True
           GT -> b' :=: a'
  
  simp (a :/=: b) = neg `fmap` simp (a :=: b)
  simp l          = return l
  
  showClause c =
      concat
    . intersperse " | "
    . map show
    $ c
  
solve :: Flags -> [Lit] -> C Bool
solve flags xs =
  do xs' <- sequence [ norm x | x <- xs ]
     if Bool False `elem` xs'
       then return False
       else sat [ x | Lit x <- xs' ]
 where
  put   v s = when (v <= verbose flags) $ lift $ do putStr s;   hFlush stdout
  putLn v s = when (v <= verbose flags) $ lift $ do putStrLn s; hFlush stdout
  
  sat xs =
    do putLn 4 "--> ConSat: solving..."
       b <- liftS (Sat.solve xs)
       if b
         then check xs
         else return False

  check xs =
    do putLn 4 "--> ConSat: checking..."
       
       -- gather & set permanent positive equalities
       s <- getState
       peqs <- getPeqs [] (M.toList (compares s))
       sequence_
         [ do putLn 4 ("[" ++ show b ++ " :~ " ++ show a ++ "]")
              setRep a b
         | (a,b) <- peqs
         ]
       
       -- gather & rebuild compares table info
       (eqs,neqs,comps) <- getEqNeq [] [] [] (M.toList (compares s))
       
       let compares' = M.toList $ M.fromListWith (++) [ (ab,[x]) | (ab,x) <- comps ]
       
       bs1 <- sequence
         [ or `fmap` if a /= b
             then sequence
                    [ do putLn 4 ( "T2: ("
                                ++ show a
                                ++ " :=: "
                                ++ show b
                                ++ ") <=> "
                                ++ show x
                                ++ " <=> "
                                ++ show y
                                 )
                         liftS $ Sat.addClause [Sat.neg x, y]
                         liftS $ Sat.addClause [x, Sat.neg y]
                         return True
                    | y <- ys
                    ]
             else sequence
                    [ do putLn 4 ( "T1: ("
                                ++ show a
                                ++ " :=: "
                                ++ show a
                                ++ ") <=> "
                                ++ show y
                                 )
                         liftS $ Sat.addClause [y]
                         return True
                    | y <- x:ys
                    ]
         | ((a,b),x:ys) <- compares'
         ]
       
       s <- getState
       setState s{ compares = M.fromList [ (ab,x)
                                         | (ab@(a,b),x:_) <- compares'
                                         , a /= b
                                         ]
                 }
       
       let eqTab      = classes M.empty eqs
           graph      = M.fromListWith S.union [ (x,S.singleton y) | (x,y) <- eqs ++ map swap eqs ]
           swap (x,y) = (y,x)
       bs2 <- sequence
                [ if x' /= y'
                    then do return False
                    else do put 1 "T: "
                            addClause ((x :=: y) : [ x :/=: y | (x,y) <- p ])
                            return True
                | (x,y) <- neqs
                , let x' = rep eqTab x
                      y' = rep eqTab y
                      p  = bfs graph x y
                ]
       if or bs1 || or bs2
         then do sat xs
         else do setState (s{ model = rep eqTab })
                 return True

  getPeqs peqs [] =
    do return peqs

  getPeqs peqs ((ab,x):abxs) =
    do mb <- liftS (Sat.getValue x)
       case mb of
         Just True -> getPeqs (ab:peqs) abxs
         _         -> getPeqs peqs abxs
       
  getEqNeq eqs neqs comps [] =
    do return (eqs,neqs,comps)

  getEqNeq eqs neqs comps (((a,b),x):abxs) =
    do a' <- getRep a
       b' <- getRep b
       let ab     | a' < b    = (a',b')
                  | otherwise = (b',a')
           comps' = (ab,x):comps
       bl <- liftS (Sat.getModelValue x)
       if bl
         then getEqNeq (ab:eqs) neqs comps' abxs
         else getEqNeq eqs (ab:neqs) comps' abxs
       
  rep eqTab x =
    case M.lookup x eqTab of
      Just x' -> x'
      Nothing -> x 

  classes eqTab [] = cut eqTab (M.keys eqTab)
   where
    cut eqTab0 []     = eqTab0
    cut eqTab0 (x:xs) = cut eqTab1 xs
     where
      (eqTab1,_) = find eqTab0 x

  classes eqTab0 ((x,y):eqs) =
    case x' `compare` y' of
      LT -> classes (M.insert y' x' eqTab2) eqs
      EQ -> classes eqTab2 eqs
      GT -> classes (M.insert x' y' eqTab2) eqs
   where
    (eqTab1,x') = find eqTab0 x
    (eqTab2,y') = find eqTab1 y

  find eqTab0 x0 =
    case M.lookup x0 eqTab0 of
      Just x1
        | x1 == x2  -> (eqTab0,x1)
        | otherwise -> (M.insert x0 x2 eqTab1,x2)
       where
        (eqTab1,x2) = find eqTab0 x1

      Nothing ->
        (eqTab0,x0)

  bfs :: Map Con (Set Con) -> Con -> Con -> [(Con,Con)]
  bfs graph x y = bfs' M.empty [(x,x)] []
   where
    bfs' backs ((x,z):xys) xys' | x == y =
      path (M.insert x z backs) [] y
    
    bfs' backs ((x,z):xys) xys' | M.lookup x backs == Nothing =
      bfs' (M.insert x z backs) xys ([(v,x) | v <- neighbors x] ++ xys')
      
    bfs' backs (_:xys) xys' =
      bfs' backs xys xys'
    
    bfs' backs [] [] =
      error "bfs: no path!"
    
    bfs' backs [] xys' =
      bfs' backs (reverse xys') []
    
    neighbors x =
      case M.lookup x graph of
        Just xs -> S.toList xs
        Nothing -> error "bfs: not a node!"
    
    path backs p y
      | x == y    = p
      | otherwise = case M.lookup y backs of
                      Just z  -> path backs ((z,y):p) z
                      Nothing -> error "bfs: no backwards path!"
                      
simplify :: Bool -> Bool -> C Bool
simplify a b = liftS (Sat.simplify a b)
