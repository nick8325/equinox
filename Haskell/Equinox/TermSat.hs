module Equinox.TermSat
  ( T             -- :: * -> *; Functor, Monad
  , Lit(..)       -- :: *; Eq, Ord, Show
  , Con           -- :: *
  
  , run           -- :: T a -> IO a
  , lift          -- :: IO a -> T a
  , contradiction -- :: T ()
  , newLit        -- :: T Lit
  , newCon        -- :: String -> T Con
  , app           -- :: Symbol -> [Con] -> T Con
  , neg           -- :: Lit -> Lit
  , getValue      -- :: Lit -> T (Maybe Bool)
  , getRep        -- :: Con -> T Con
  , getModelValue -- :: Lit -> T Bool -- use only after model has been found!
  , getModelRep   -- :: Con -> T Con  -- use only after model has been found!
  , getModelTable -- :: Symbol -> T [([Con],Con)]
  , addClause     -- :: [Lit] -> T ()
  , solve         -- :: Flags -> [Lit] -> T Bool
  , simplify      -- :: Bool -> Bool -> T Bool
  )
 where
 
import qualified Equinox.ConSat as C
import Equinox.ConSat
  ( Lit(..)
  , Con
  , neg
  )
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import List
import Maybe
import Form( Symbol )
import Flags
import IO
import Control.Monad

data State
  = MkState
  { funtable :: Map Symbol (Map [Con] Con)
  , model    :: Map Symbol [([Con],Con)]
  }

state0 :: State
state0 = MkState
  { funtable = M.empty
  , model    = error "model inspected before solve"
  }

newtype T a = MkT (State -> C.C (a, State))

instance Functor T where
  fmap f (MkT m) = MkT (fmap (\(x,s) -> (f x,s)) . m)

instance Monad T where
  return x = MkT (\s -> return (x,s))

  MkT m1 >>= k = MkT (\s0 ->
    do (x,s1) <- m1 s0
       let MkT m2 = k x
       m2 s1
    )

run :: T a -> IO a
run (MkT m) =
  do (x,_) <- C.run (m state0)
     return x

getState :: T State
getState = MkT (\s -> return (s,s))

setState :: State -> T ()
setState s = MkT (\_ -> return ((),s))

liftC :: C.C a -> T a
liftC m = MkT (\s -> do x <- m; return (x,s))  

lift :: IO a -> T a
lift io = liftC (C.lift io)

contradiction :: T ()
contradiction = liftC C.contradiction

newLit :: T Lit
newLit = liftC C.newLit

newCon :: String -> T Con
newCon s = liftC (C.newCon s (C.wapp []))

getValue :: Lit -> T (Maybe Bool)
getValue x = liftC (C.getValue x)

getModelValue :: Lit -> T Bool
getModelValue x = liftC (C.getModelValue x)

getRep :: Con -> T Con
getRep a = liftC (C.getRep a)

getModelRep :: Con -> T Con
getModelRep a = liftC (C.getModelRep a)

getModelTable :: Symbol -> T [([Con],Con)]
getModelTable f =
  do s <- getState
     return $
       case M.lookup f (model s) of
         Just tab -> tab
         Nothing  -> []

addClause :: [Lit] -> T ()
addClause xs = liftC (C.addClause xs)

app :: Symbol -> [Con] -> T Con
app f xs = MkT (\s ->
    case M.lookup f (funtable s) of
      Nothing   -> create f xs M.empty s
      Just args ->
        do xs' <- sequence [ C.getRep x | x <- xs ]
           case M.lookup xs' args of
             Nothing -> create f xs' args s
             Just y  -> return (y,s)
  )
 where
  create f xs args s =
    do a <- C.newCon (
              show f ++
                (if null xs
                   then ""
                   else "(" ++ concat (intersperse "," (map show xs)) ++ ")"
                )) (C.wapp (map C.weight xs))
       return (a, s{ funtable = M.insert f (M.insert xs a args) (funtable s) })

solve :: Flags -> [Lit] -> T Bool
solve flags xs = sat xs
 where
  put   v s = when (v <= verbose flags) $ lift $ do putStr s;   hFlush stdout
  putLn v s = when (v <= verbose flags) $ lift $ do putStrLn s; hFlush stdout
  
  sat xs =
    do putLn 3 "--> TermSat: solving..."
       b <- liftC (C.solve flags xs)
       if b
         then do putLn 3 "--> TermSat: checking..."
                 check xs
         else do return False
 
  check xs =
    do b <- rebuildFuntable
       s <- getState
       bs <- sequence
               [ checkFunArgs (M.toList args)
               | (_,args) <- M.toList (funtable s)
               ]
       if b || or bs
         then do sat xs
         else do buildModel
                 return True

  rebuildFuntable =
    do s <- getState
       bes <- sequence
                [ do args'  <- sequence
                                 [ do xs' <- sequence [ getRep x | x <- xs ]
                                      y'  <- getRep y
                                      return (xs',S.singleton y')
                                 | (xs,y) <- M.toList args
                                 ]
                     let combinedArgs' = M.toList (M.fromListWith S.union args')
                     args'' <- sequence
                                 [ do sequence_ [ do put 1 "C2: "
                                                     addClause [ y :=: y' ]
                                                | y' <- ys'
                                                ]
                                      return (xs,minimum (y:ys'))
                                 | (xs,ys) <- combinedArgs'
                                 , let y:ys' = S.toList ys
                                 ]
                     return (any ((>= 2) . S.size . snd) combinedArgs',(f,M.fromList args''))
                | (f,args) <- M.toList (funtable s)
                ]
       setState s{ funtable = M.fromList (map snd bes) }
       return (or (map fst bes))
    
  checkFunArgs args =
    do tab <- sequence
                [ do xs' <- sequence [ getModelRep x | x <- xs ]
                     y'  <- getModelRep y
                     return (xs',[(y',[(xs,y)])])
                | (xs,y) <- args
                ]
       xs <- sequence
               [ do put 1 "C: "
                    addClause ( (y1 :=: y2)
                              : [ x1 :/=: x2 | (x1,x2) <- xs1 `zip` xs2 ]
                              )
               | (_,tab) <- M.toList (M.fromListWith (++) tab)
               , ((_,xsys1),(_,xsys2)) <- pairs (M.toList (M.fromListWith (++) tab))
               , (xs1,y1) <- xsys1
               , (xs2,y2) <- xsys2
               ]
       return (not (null xs))
  
  buildModel =
    do s <- getState
       
       theModel <-
         sequence
         [ do args' <- sequence
                         [ do xs' <- sequence [ getModelRep x | x <- xs ]
                              y'  <- getModelRep y
                              return (xs',y')
                         | (xs,y) <- M.toList args
                         ]
              return (f, S.toList (S.fromList args'))
         | (f,args) <- M.toList (funtable s)
         ]

       setState (s{ model = M.fromList theModel })

  pairs :: [a] -> [(a,a)]
  pairs []     = [] 
  pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs   
  
simplify :: Bool -> Bool -> T Bool
simplify a b = liftC (C.simplify a b)
