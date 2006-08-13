module Flags
  ( Flags(..)
  , getFlags
  , getTimeLeft
  , getTimeSpent
  , getTimeSpentS
  )
 where

import System.Environment
  ( getArgs
  )

import System

import List
  ( groupBy
  , intersperse
  , (\\)
  )

import Char

import CPUTime

-------------------------------------------------------------------------
-- flags

data Flags
  = Flags
  { time         :: Maybe Int
  , roots        :: [FilePath]
  , printModel   :: Bool
  , mfile        :: Maybe FilePath
  , splitting    :: Bool
  , sat          :: Bool
  , onlyClausify :: Bool
  , strength     :: Int
  , verbose      :: Int
  
  -- primitive
  , files :: [FilePath]
  , start :: Integer
  }
 deriving (Eq, Show)

initFlags :: Flags
initFlags =
  Flags
  { time         = Nothing
  , roots        = []
  , printModel   = False
  , mfile        = Nothing
  , splitting    = False
  , sat          = False
  , onlyClausify = False
  , strength     = 3
  , verbose      = 0

  -- primitive
  , files = []
  , start = error "starting time not properly initialized"
  }

-------------------------------------------------------------------------
-- options

options :: [Option Flags]
options =
  [ Option
    { long    = "time"
    , meaning = (\n f -> f{ time = Just n }) <$> argNum
    , help    = [ "Maximum running time in seconds. Is a soft limit."
                , "Example: --time 300"
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "root"
    , meaning = (\r f -> f{ roots = roots f ++ [r] }) <$> argFile
    , help    = [ "A directory in which included problems will be sought."
                , "Example: --root TPTP-v3.0.0"
                , "Default: --root ."
                ]
    }

  , Option
    { long    = "split"
    , meaning = unit (\f -> f{ splitting = True })
    , help    = [ "Split the conjecture into several sub-conjectures."
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "model"
    , meaning = unit (\f -> f{ printModel = True })
    , help    = [ "Print the found model on the screen."
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "strength"
    , meaning = (\n f -> f{ strength = n }) <$> argNum
    , help    = [ "Maximum number of non-guessing quantifier instantations"
                , "before starting to guess."
                , "Example: --strength 7"
                , "Default: 3"
                ]
    }

  , Option
    { long    = "verbose"
    , meaning = (\n f -> f{ verbose = verbose f `max` n }) <$> argNum
    , help    = [ "Verbosity level."
                , "Example: --verbose 2"
                , "Default: --verbose 0"
                ]
    }

  , Option
    { long    = "help"
    , meaning = unit id
    , help    = [ "Displays this help message."
                ]
    }
  ]

-- data Option

data Option a
  = Option
  { long    :: String
  , meaning :: Arg (a -> a)
  , help    :: [String]
  }

-------------------------------------------------------------------------
-- getFlags

getFlags :: IO Flags
getFlags =
  do as    <- getArgs
     picoT <- getCPUTime
     case parseFlags initFlags as of
       Left [] ->
         do putStr (unlines helpMessage)
            exitWith ExitSuccess

       Left err ->
         do putStrLn "Error in arguments:"
            putStr (unlines err)
            putStrLn "Try --help."
            exitWith (ExitFailure (-1))
       
       Right f ->
         do return f{ start = unPico picoT }

getTimeLeft :: Flags -> IO Int
getTimeLeft flags =
  do t' <- getTimeSpent flags
     return (t - t')
 where
  t = maybe 300 id (time flags)

getTimeSpent :: Flags -> IO Int
getTimeSpent flags =
  do picoT <- getCPUTime
     return (fromInteger (unPico picoT - start flags))

getTimeSpentS :: Flags -> IO String
getTimeSpentS flags =
  do picoT <- getCPUTime
     let t = fromInteger (unPico' picoT - start flags)
         m = t `div` 600
         s = (t `div` 10) `mod` 60
         d = t `mod` 10
     return ( show m
           ++ ":"
           ++ let x = show s in replicate (2 - length x) '0' ++ x
           ++ "."
           ++ show d
            )

unPico :: Integer {- picoseconds -} -> Integer {- seconds -}
unPico = let c = 10^12 in (`div` c)

unPico' :: Integer {- picoseconds -} -> Integer {- 0.1 seconds -}
unPico' = let c = 10^11 in (`div` c)

-------------------------------------------------------------------------
-- arg

data Arg a = MkArg [String] ([String] -> Either [String] (a, [String]))

instance Functor (Either a) where
  fmap f (Left x)  = Left x
  fmap f (Right y) = Right (f y)

unit :: a -> Arg a
unit x = MkArg [] (\s -> Right (x,s))

(<*>) :: Arg (a -> b) -> Arg a -> Arg b
MkArg fs f <*> MkArg xs x =
  MkArg (fs++xs) (\s ->
    case f s of
      Left err     -> Left err
      Right (h,s') -> case x s' of
                        Left err      -> Left err
                        Right (a,s'') -> Right (h a,s'')
  )

(<$>) :: (a -> b) -> Arg a -> Arg b
f <$> x = unit f <*> x

args :: Arg a -> [String]
args (MkArg as _) = as

-------------------------------------------------------------------------
-- parsers

argNum :: (Read a, Num a) => Arg a
argNum = MkArg ["<num>"] $ \xs ->
  case xs of
    x:xs       | all isDigit x -> Right (read x, xs)
    ('-':x):xs | all isDigit x -> Right (-read x, xs)
    _                          -> Left ["expected a number"]
      
argFile :: Arg FilePath
argFile = MkArg ["<file>"] $ \xs ->
  case xs of
    x:xs -> Right (x, xs)
    _    -> Left ["expected a file"]
      
argNums :: Arg [Int]
argNums = MkArg ["<nums>"] $ \xs ->
  case xs of
    []   -> Left ["expected a number list"]
    x:xs -> ((\a -> (a,xs)) `fmap`) . nums . groupBy (\x y -> isDigit x == isDigit y) $ x ++ ","
     where
      nums []                = Right []
      nums (n:",":ns)        = (read n :) `fmap` nums ns
      nums (n:"..":m:",":ns) = ([read n .. read m] ++) `fmap` nums ns
      nums _                 = Left ["number list garbled"]

argOption :: [String] -> Arg String
argOption as = MkArg ["<" ++ concat (intersperse " | " as) ++ ">"] $ \xs ->
  case xs of
    []   -> Left ["expected an argument"]
    x:xs -> ((\a -> (a,xs)) `fmap`) . elts $ x
     where
      elts x | x `elem` as = Right x
             | otherwise   = Left ["argument garbled"]

argList :: [String] -> Arg [String]
argList as = MkArg ["<" ++ concat (intersperse " | " as) ++ ">*"] $ \xs ->
  case xs of
    []   -> Left ["expected a list"]
    x:xs -> ((\a -> (a,xs)) `fmap`) . elts $ x ++ ","
     where
      elts []              = Right []
      elts s | w `elem` as = (w:) `fmap` elts r
       where
        w = takeWhile (/= ',') s
        r = tail (dropWhile (/= ',') s)
    
      elts _ = Left ["argument list garbled"]

parseFlags :: Flags -> [String] -> Either [String] Flags
parseFlags f []               = Right f
parseFlags f ("--help":xs)    = Left []
parseFlags f (('-':'-':x):xs) =
  case [ opt | opt <- options, x == long opt ] of
    opt:_  -> case h xs of
                Left err      -> Left err
                Right (g,xs') -> parseFlags (g f) xs'
     where
      MkArg _ h = meaning opt
    []     -> Left ["Unrecognized option: '--" ++ x ++ "'"]

parseFlags f (x:xs)           = parseFlags (f{files = files f ++ [x]}) xs

-------------------------------------------------------------------------
-- help message

helpMessage :: [String]
helpMessage =
  [ "Usage: <option>* <file>*"
  , ""
  , "<file> should be in TPTP format."
  , ""
  , "<option> can be any of the following:"
  ] ++
  concat
  [ [ ""
    , "  --" ++ long opt ++ " " ++ unwords (args (meaning opt))
    ] ++ map ("    "++) (help opt)
  | opt <- options
  ]

-------------------------------------------------------------------------
-- the end.





