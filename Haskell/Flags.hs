module Flags
  ( Flags(..)
  , Tool(..)
  , Prover(..)
        , Method(InjNotSurj,SurjNotInj,Serial,Relation,Auto,Leo,Trans)
  , getFlags
  , getTimeLeft
  , getTimeSpent
  , getTimeSpentS
  )
 where

{-
Paradox/Equinox -- Copyright (c) 2003-2007, Koen Claessen, Niklas Sorensson

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

import System.Exit
  ( exitWith
  , ExitCode(..)
  )

import System.Environment
  ( getArgs
  )

import GHC.Environment
  ( getFullArgs
  )

import System.IO

import Data.List
  ( groupBy
  , intersperse
  , (\\)
  )

import Data.Char

import System.CPUTime

import Control.Applicative

-------------------------------------------------------------------------
-- flags

data Tool
  = Paradox
  | Equinox
  | Infinox
        | SatPlay
        | Zoomer
 deriving ( Eq, Show )

data Flags
  = Flags
  { time         :: Maybe Int
  , roots        :: [FilePath]
  , printModel   :: Bool
  , dot          :: Maybe String
  , mfile        :: Maybe FilePath
  , splitting    :: Bool
  , sat          :: Bool
  , onlyClausify :: Bool
  , strength     :: Int
  , verbose      :: Int
  , progress     :: Bool
  , tstp         :: Bool
  , temp         :: FilePath
  , filelist     :: Maybe FilePath
  , nrOfThreads  :: Int

  -- infinox
  , elimit       :: Int
  , plimit       :: Int
  , zoom         :: Bool
  , termdepth    :: Int
  , function     :: String
  , relation     :: Maybe String
  , subset       :: Maybe String
  , method       :: [Method]
        , outfile                        :: Maybe FilePath
  , prover       :: Prover
        , leo                                    :: Bool


  -- primitive
  , thisFile     :: FilePath
  , files        :: [FilePath]
  , start        :: Integer
  }
 deriving ( Eq, Show )

data Method
  = InjNotSurj
  | SurjNotInj
  | Serial
  | Trans
        | Bijection
        | Relation
        | Auto
        | Leo
 deriving ( Eq, Show, Read, Bounded, Enum )

data Prover = E | Equi
  deriving (Eq, Show)


read' "equinox" = Equi
read' "Equinox" = Equi
read' "Equi"    = Equi
read' "Eq"      = Equi
read' "e"       = E
read' "E"       = E
read' "Eprover" = E
read' "eprover" = E
read' s = error $ "read': " ++ s ++ " no parse"

initFlags :: Flags
initFlags =
  Flags
  { time         = Nothing
  , roots        = []
  , printModel   = False
  , dot          = Nothing
  , mfile        = Nothing
  , splitting    = False
  , sat          = False
  , onlyClausify = False
  , strength     = 5
  , verbose      = 0
  , progress     = True
  , tstp         = False
  , temp         = "temp"
  , nrOfThreads  = 1

  -- infinox
  , elimit       = 2
  , plimit       = 2
  , zoom         = False
  , termdepth    = 1
  , function     = "-"
  , relation     = Nothing --Just "-"
  , subset       = Nothing --Just "-"
  , method       = [InjNotSurj,SurjNotInj,Serial, Trans, Auto,Leo]
        , outfile                        = Nothing
        , filelist               = Nothing
  , leo                                  = False
  , prover       = E

  -- primitive
  , thisFile     = ""
  , files        = []
  , start        = error "starting time not properly initialized"
  }

-------------------------------------------------------------------------
-- options

options :: [Option Flags]
options =
  [ Option
    { long    = "time"
    , tools   = [Paradox, Equinox, Infinox]
    , meaning = (\n f -> f{ time = Just n }) <$> argNum
    , help    = [ "Maximum running time in seconds. Is a (very) soft limit."
                , "Example: --time 300"
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "root"
    , tools   = [Paradox, Equinox, Infinox]
    , meaning = (\r f -> f{ roots = roots f ++ [r] }) <$> argFile
    , help    = [ "A directory in which included problems will be sought."
                , "Example: --root TPTP-v3.0.0"
                , "Default: --root ."
                ]
    }

  , Option
    { long    = "split"
    , tools   = [Paradox, Equinox, Infinox]
    , meaning = unit (\f -> f{ splitting = True })
    , help    = [ "Split the conjecture into several sub-conjectures."
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "model"
    , tools   = [Paradox]
    , meaning = unit (\f -> f{ printModel = True })
    , help    = [ "Print the found model on the screen."
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "modelfile"
    , tools   = [Equinox]
    , meaning = (\m f -> f{ mfile = Just m }) <$> argFile
    , help    = [ "Print the found approximation model in the file."
                , "Default: (off)"
                ]
    }
{-
  , Option
    { long    = "dot"
    , meaning = (\d f -> f{ dot = Just d }) <$> argDots
    , help    = [ "Generate dot-files for each approximate model."
                , "<dot-spec> specifies what symbols to show and how."
                , "Default: (off)"
                ]
    }
-}
  , Option
    { long    = "strength"
    , tools   = [Equinox]
    , meaning = (\n f -> f{ strength = n }) <$> argNum
    , help    = [ "Maximum number of non-guessing quantifier instantations"
                , "before starting to guess."
                , "Example: --strength 7"
                , "Default: --strength " ++ show (strength initFlags)
                ]
    }

  , Option
    { long    = "verbose"
    , tools   = [Paradox, Equinox, Infinox]
    , meaning = (\n f -> f{ verbose = verbose f `max` n }) <$> argNum
    , help    = [ "Verbosity level."
                , "Example: --verbose 2"
                , "Default: --verbose 0"
                ]
    }

  , Option
    { long    = "no-progress"
    , tools   = [Paradox, Equinox, Infinox]
    , meaning = unit (\f -> f{ progress = False })
    , help    = [ "Do not show progress during solving."
                , "Default: (off)"
                ]
    }

        , Option
    { long    = "temp"
    , tools   = [Infinox]
    , meaning = (\s f -> f{ temp = s }) <$> argName
    , help    = [ "Directory for temporary files."
                , "Default: (/temp)"
                ]
    }

  , Option
    { long    = "elimit"
    , tools   = [Infinox]
    , meaning = (\n f -> f{ elimit = n }) <$> argNum
    , help    = [ "Time-out for E-prover (as a subprocedure) in seconds."
                , "Default: --elimit 2"
                ]
    }

  , Option
    { long    = "plimit"
    , tools   = [Infinox]
    , meaning = (\n f -> f{ plimit = n }) <$> argNum
    , help    = [ "Time-out for Paradox (as a subprocedure) in seconds."
                , "Default: --plimit 2"
                ]
    }

  , Option
    { long    = "zoom"
    , tools   = [Infinox]
    , meaning = unit (\f -> f{ zoom = True })
    , help    = [ "Use 'zooming' to reduce the size of the problem."
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "prover"
    , tools   = [Infinox]
    , meaning = (\p f -> f{ prover = read' p }) <$> argName
    , help    = [ ""
                , "Default: E"
                ]
    }

{-
        , Option
    { long    = "leo"
    , tools   = [Infinox]
    , meaning = unit (\f -> f{ leo = True })
    , help    = [ "Use Leo to search for injective and non-surjective functions"
                , "Default: (off)"
                ]
    }
-}
  , Option
    { long    = "termdepth"
    , tools   = [Infinox]
    , meaning = (\n f -> f{ termdepth = n }) <$> argNum
    , help    = [ "Maximum depth for terms."
                , "Default: --termdepth 1"
                ]
    }

  , Option
    { long    = "method"
    , tools   = [Infinox]
                , meaning = (\m f -> f{ method = map read m }) <$> argList (map show [(minBound :: Method) .. maxBound])
    , help    = [ "Method to use."
                , "Default: --method InjNotSurj"
                ]
    }

  , Option
    { long    = "function"
    , tools   = [Infinox]
    , meaning = (\s f -> f{ function = s }) <$> argName
    , help    = [ "Use a specified function; use - for any function."
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "relation"
    , tools   = [Infinox]
    , meaning = (\s f -> f{ relation = Just s }) <$> argName
    , help    = [ "Generalize the method to use a specified relation; use - for any relation."
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "subset"
    , tools   = [Infinox]
    , meaning = (\s f -> f{ subset = Just s }) <$> argName
    , help    = [ "Generalize the method to use a specified subset; use - for any subset."
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "verbose"
    , tools   = [Paradox, Equinox, Infinox]
    , meaning = (\n f -> f{ verbose = verbose f `max` n }) <$> argNum
    , help    = [ "Verbosity level."
                , "Example: --verbose 2"
                , "Default: --verbose 0"
                ]
    }

        , Option
    { long    = "outfile"
    , tools   = [Infinox]
    , meaning = (\file f -> f{ outfile = Just file }) <$> argName
    , help    = [ "Specify a file for output"
                , "Example: --outfile file"
                , "Default: --outfile (off)"
                ]
    }


        , Option
    { long    = "filelist"
    , tools   = [Paradox, Equinox, Infinox]
    , meaning = (\file f -> f{ filelist = Just file }) <$> argName
    , help    = [ "Specify a file containing a list of problems"
                , "Example: --filelist file"
                , "Default: --filelist (off)"
                ]
    }

  , Option
    { long    = "tstp"
    , tools   = [Paradox, Equinox, Infinox]
    , meaning = unit (\f -> f{ tstp = True })
    , help    = [ "Generate output in TSTP and SZS ontology format."
                , "Default: (off)"
                ]
    }

  , Option
    { long    = "help"
    , tools   = [Paradox, Equinox, Infinox]
    , meaning = unit id
    , help    = [ "Displays this help message."
                ]
    }
  ]

-- data Option

data Option a
  = Option
  { long    :: String
  , tools   :: [Tool]
  , meaning :: Arg (a -> a)
  , help    :: [String]
  }

-------------------------------------------------------------------------
-- getFlags

getFlags :: Tool -> IO Flags
getFlags tool =
  do as    <- getArgs
     picoT <- getCPUTime
     case parseFlags tool initFlags as of
       Left [] ->
         do putStr (unlines (helpMessage tool))
            exitWith ExitSuccess

       Left err ->
         do putStrLn "Error in arguments:"
            putStr (unlines err)
            putStrLn "Try --help."
            exitWith (ExitFailure (-1))

       Right f ->
         do t <- getNrOfThreads
            return f{ start       = unPico picoT
                    , nrOfThreads = t
                    }

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

-- bweeeuh, do I really have to do this?
getNrOfThreads :: IO Int
getNrOfThreads =
  do xs <- getFullArgs
     return (threads False 1 xs)
 where
  threads rts t []                                      = t
  threads rts t ("+RTS" :xs)                            = threads True t xs
  threads rts t ("-RTS" :xs)                            = threads False t xs
  threads rts t ("--RTS":xs)                            = t
  threads rts t (('-':'N':n):xs) | rts && all isDigit n = read n
  threads rts t (_:xs)                                  = threads rts t xs

-------------------------------------------------------------------------
-- arg

data Arg a = MkArg [String] ([String] -> Either [String] (a, [String]))

{- -- already defined in GHC 6.8
instance Functor (Either a) where
  fmap f (Left x)  = Left x
  fmap f (Right y) = Right (f y)
-}

unit :: a -> Arg a
unit x = MkArg [] (\s -> Right (x,s))

star :: Arg (a -> b) -> Arg a -> Arg b
MkArg fs f `star` MkArg xs x =
  MkArg (fs++xs) (\s ->
    case f s of
      Left err     -> Left err
      Right (h,s') -> case x s' of
                        Left err      -> Left err
                        Right (a,s'') -> Right (h a,s'')
  )

instance Functor Arg where fmap f x = pure f <*> x

instance Applicative Arg where
  pure = unit
  (<*>) = star

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

argName :: Arg FilePath
argName = MkArg ["<name>"] $ \xs ->
  case xs of
    x:xs -> Right (x, xs)
    _    -> Left ["expected a name"]

argDots :: Arg FilePath
argDots = MkArg ["<dot-spec>"] $ \xs ->
  case xs of
    x:xs -> Right (x, xs)
    _    -> Left ["expected a dot-spec"]

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

parseFlags :: Tool -> Flags -> [String] -> Either [String] Flags
parseFlags tool f []               = Right f
parseFlags tool f ("--help":xs)    = Left []
parseFlags tool f (('-':'-':x):xs) =
  case [ opt | opt <- options, tool `elem` tools opt, x == long opt ] of
    opt:_  -> case h xs of
                Left err      -> Left err
                Right (g,xs') -> parseFlags tool (g f) xs'
     where
      MkArg _ h = meaning opt
    []     -> Left ["Unrecognized option: '--" ++ x ++ "'"]

parseFlags tool f (x:xs)           = parseFlags tool (f{files = files f ++ [x]}) xs

-------------------------------------------------------------------------
-- help message

helpMessage :: Tool -> [String]
helpMessage tool =
  [ "Usage: " ++ small (show tool) ++ " <option>* <file>*"
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
  , tool `elem` tools opt
  ]
 where
  small (c:s) = toLower c : s
  small s     = s

-------------------------------------------------------------------------
-- the end.

