module ParseProblem where

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
  ( getEnv
  )

import Data.Char
  ( isSpace
  , isAlpha
  , isAlphaNum
  , isDigit
  , isUpper
  , isLower
  )

import Data.List
  ( intersperse
  , (\\)
  , tails
  , nub
  )

import System.IO
  ( hFlush
  , stdout
  )

import System.IO.Error as IO
  ( ioError
  , userError
  , try
  )

import Control.Monad
  ( guard
  )

import Form
import Name
import Output
import Data.Set( Set )
import qualified Data.Set as S
import Parsek as P

-------------------------------------------------------------------------
-- reading

readProblemWithRoots :: [FilePath] -> FilePath -> IO Problem
readProblemWithRoots roots name =
  do putStr ("Reading '" ++ name ++ "' ... ")
     hFlush stdout
     mtptp <- IO.try (getEnv "TPTP")
     mes <- findFile [ rt ++ nm
                     | rt <- roots
                          ++ [ case reverse tptp of
                                 '/':_ -> tptp
                                 _     -> tptp ++ "/"
                             | Right tptp <- [mtptp]
                             ]
                     , nm <- nub [ name, name_p ]
                          ++ [ "Problems/" ++ name_p
                             , "Problems/" ++ take 3 name ++ "/" ++ name_p
                             ]
                     ]
     case mes of
       Nothing ->
         do putStrLn "COULD NOT OPEN"
            putFailure "INPUT FILE ERROR"

       Just (name',s) ->
         do putStr (if name' /= name then "('" ++ name' ++ "') " else "")
            hFlush stdout
            case parseP s of
              Left err ->
                do putStrLn "PARSE ERROR:"
                   sequence [ putWarning s | s <- err ]
                   exitWith (ExitFailure 1)

              Right (includes,clauses) ->
                do putStrLn "OK"
                   hFlush stdout
                   sets <- sequence [ readProblemWithRoots roots incl | incl <- includes ]
                   return (concat sets ++ clauses)
 where
  name_p | '.' `elem` name = name
         | otherwise       = name ++ ".p"

  findFile [] =
    do return Nothing

  findFile (name:names) =
    do -- on Cygwin, the variable TPTP expects Windows paths!
       -- putStrLn ("(trying '" ++ name ++ "'...)")
       ees <- IO.try (readFile name)
       case ees of
         Left _  -> findFile names
         Right s -> return (Just (name,s))

readProblem :: FilePath -> IO [Input Form]
readProblem name = readProblemWithRoots [""] name

-------------------------------------------------------------------------
-- parsing

type P = Parser Char

-- white space

white :: P ()
white =
  do munch isSpace
     option () $
       do char '%' <?> ""
          many (satisfy (/= '\n'))
          char '\n'
          white
      <|>
       do char '/' <?> ""
          char '*'
          s <- P.look
          let body ('*':'/':s) =
                do anyChar
                   anyChar
                   return ()

              body (_:s) =
                do anyChar
                   body s

              body [] =
                do return ()
          body s
          white

token :: String -> P String
token s =
  do white
     string s
 <?> show s

avname :: String -> P String
avname s =
  do white
     string s
 <?> show s

pname :: (Char -> Bool) -> P String
pname p =
  do white
     stdName
 where
  stdName =
    do mc <- option [] ((:[]) `fmap` char '$')
       c  <- satisfy (\c -> p c && isIdfChar c)
       s  <- munch isIdfChar
       let f = mc ++ (c:s)
       if f `elem` ["$false", "$true"]
         then fail ""
         else return ()
       return (mc ++ (c:s))
   <|>
    do if not (p '\'') then fail "name" else return ()
       string "\'"
       s <- munch (/= '\'')
       string "\'"
       return ("\'" ++ s ++ "\'")

fname :: P Name
fname =
  do s <- pname (not . isUpper)
     if s == "equal" then fail "equal" else return ()
     let n = name s
     n `seq` return n
 <?> "lower-case name"

vname :: P String
vname = pname isUpper
 <?> "variable name"

isVarName :: Name -> Bool
isVarName n = not (null s) && isUpper (head s)
 where
  s = show n

isIdfChar :: Char -> Bool
isIdfChar c = isValid c

isValid :: Char -> Bool
isValid n = isAlphaNum n || n == '_'

parens :: P a -> P a
parens = between (token "(") (token ")")

bracks :: P a -> P a
bracks = between (token "[") (token "]")

-- terms

type Bnd = Maybe (Set String)

term :: Bnd -> P Term
term bnd =
  do s <- fname
     xs <- args bnd
     return (Fun (s ::: ([ top | x <- xs ] :-> top)) xs)
 <|>
  do s <- case bnd of
            Just vs -> do choice [ avname s <?> "bound variable" | s <- S.toList vs ]
            Nothing -> do vname
     return (Var (name s ::: V top))
 <|>
  do parens (term bnd)
 <?> "term"

args :: Bnd -> P [Term]
args bnd =
  do return []
 <|>
  do parens (term bnd `sepBy` token ",")
 <?> "arguments"

-- atoms

atom :: Bnd -> P Form
atom bnd =
  do token "$false"
     return false
 <|>
  do token "$true"
     return true
 <|>
  do s  <- fname
     xs <- args bnd
     return (Atom (prd (s ::: ([ top | x <- xs ] :-> bool)) xs))
 <|>
  do t1 <- term bnd
     op <- token "=" <|> token "!="
     t2 <- term bnd
     let a = Atom (t1 :=: t2)
     return (if op == "=" then a else nt a)
 <|>
  do avname "equal"
     token "("
     t1 <- term bnd
     token ","
     t2 <- term bnd
     token ")"
     return (Atom (t1 :=: t2))
 <?> "atom"

-- forms

form :: Bnd -> P Form
form bnd =
  do foper bnd ops
 <?> "formula"
 where
  ops = [ ("<=>", Equiv)
        , ("<~>", \x y -> nt (x `Equiv` y))
        , ("=>",  \x y -> nt x \/ y)
        , ("<=",  \x y -> x \/ nt y)
        , ("|",   (\/))
        , ("~|",  \x y -> nt (x \/ y))
        , ("&",   (/\))
        , ("~&",  \x y -> nt (x /\ y))
        ]

foper :: Bnd -> [(String, Form->Form->Form)] -> P Form
foper bnd []                   = funit bnd
foper bnd ops@((sym,fun):ops') =
  do a <- foper bnd ops'
     option a $
       do token sym
          b <- foper bnd ops
          return (a `fun` b)

funit :: Bnd -> P Form
funit bnd =
  do parens (form bnd)
 <|>
  do atom bnd
 <|>
  do token "~"
     f <- funit bnd
     return (nt f)
 <|>
  do q <- (do token "!"; return forAll) <|> (do token "?"; return exists)
     vs <- bracks (vname `sepBy` token ",")
     token ":"
     f <- funit ((`S.union` S.fromList vs) `fmap` bnd)
     return (foldr q f (map (\v -> name v ::: V top) vs))
 <?> "formula unit"

lit :: P Form
lit =
  do atom Nothing
 <|>
  do token "~"
     a <- atom Nothing
     return (nt a)
 <?> "literal"

claus :: P Form
claus =
  do ls <- lit `sepBy` token "|"
     let c = orl ls
     return (foldr forAll_ c (S.toList (free c)))
 <|>
  do parens claus
 where
  orl [a] = a
  orl as  = Or (S.fromList as)

exiForm :: P Form
exiForm =
  do parens exiForm
 <|>
  do token "?"
     vs <- bracks (vname `sepBy` token ",")
     token ":"
     f <- funit (Just (S.fromList vs))
     let xs  = map (\v -> name v ::: V top) vs
         ans = Atom (prd (name "$answer" ::: ([ top | x <- xs ] :-> bool)) (map Var xs))
     return (foldr exists (nt ans /\ f) xs)
 <?> "existential quantification"

-- formulas and clauses

formula :: P (Input Form)
formula =
  do lang <- token "fof" <|> token "cnf"
     x <- parens $
       do white
          s <- pname (const True) <|> (token (show "") >> return "")
          token ","
          white
          (st,t) <- ptype
          token ","
          let body
                | lang == "fof" && st == "question" = exiForm
                | lang == "fof"                     = form (Just S.empty)
                | otherwise                         = claus
          f <- body
          option () (do token ","
                        let junk =
                              do munch (`notElem` "()")
                                 option () (do token "("; junk; token ")"; junk)
                         in junk)
          return (Input t s f)
     token "."
     return x
 where
  ptype = choice
    [ do token s
         return (s,t)
    | (s,t) <- typeList
    ]

  typeList =
    [ ("axiom",              Fact)  -- ..
    , ("theorem",            Fact)  -- I see no reason to distinguish these
    , ("lemma",              Fact)  -- ..
    , ("hypothesis",         Fact)  -- ..
    , ("definition",         Fact)  -- TODO: treat this one specially
    , ("conjecture",         Conjecture)
    , ("question",           Conjecture)
    , ("negated_conjecture", NegatedConjecture)
    ]

-- includes

include :: P FilePath
include =
  do token "include"
     s <- parens (white >> filePath)
     token "."
     return s

filePath :: P FilePath
filePath =
  do q <- char '\'' <|> char '\"'
     s <- munch (\c -> c /= q && c /= '\n')
     char q
     return s
 <?> "file path"

prob :: P ([FilePath],[Input Form])
prob =
  do xs <- many ((Left `fmap` include) <|> (Right `fmap` formula))
     let incls = [ incl | Left incl <- xs ]
         infs  = [ inf  | Right inf <- xs ]
     white
     return (incls,infs)

parseP :: String -> Either [String] ([FilePath],[Input Form])
parseP s =
  case parse prob completeResultsWithLine s of
    Left (n, exp, unexp) ->
      Left $
        [ "On line:    " ++ show n ] ++
        [ "Unexpected: " ++ commas "and" unexp | not (null unexp) ] ++
        [ "Expected:   " ++ commas "or" exp    | not (null exp) ]

    Right [x] ->
      Right x

    Right _ ->
      Left $
        [ "Internal error: Ambiguous parse!"
        , "Please report this as a bug in the parser."
        ]
 where
  commas op = concat . intersperse (", " ++ op ++ " ")

-------------------------------------------------------------------------
-- the end.

