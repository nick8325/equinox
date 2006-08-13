{-# OPTIONS -fglasgow-exts #-}
------------------------------------------------------------------
-- Parsek, a Parser Combinator Library                          --
-- Copyright (c) 2003 Koen Claessen                             --
-- koen@cs.chalmers.se                                          --
--                                                              --
-- This file is part of Parsek.                                 --
--                                                              --
-- Parsek is free software; you can redistribute it and/or      --
-- modify it under the terms of the GNU General Public License  --
-- as published by the Free Software Foundation; either version --
-- 2 of the License, or (at your option) any later version.     --
--                                                              --
-- Parsek is distributed in the hope that it will be useful,    --
-- but WITHOUT ANY WARRANTY; without even the implied warranty  --
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See  --
-- the GNU General Public License for more details.             --
--                                                              --
-- You should have received a copy of the GNU General Public    --
-- License along with Parsek; if not, write to the Free         --
-- Software Foundation, Inc., 59 Temple Place, Suite 330,       --
-- Boston, MA 02111-1307 USA.                                   --
------------------------------------------------------------------
{-

module Parsek
-------------------------------------------------------------------
$Id: Parsek.hs,v 1.1 2006/08/13 08:36:28 Koen Claessen Exp $

Author:     Koen Claessen
Date:       2001-01-27
Compliance: hugs -98 (needs "forall" on types)
Licence:    GPL

Comments:

This module implements fast and space-efficient monadic parser
combinators. It is inspired by Daan Leijen's "Parsec" library.
The aim was to get a library that was equally fast, without
having to use the cumbersome "try" combinator. (That combinator
is still supported, but is defined to be the identity function.)
This aim is achieved by using a paralell choice combinator,
instead of using backtracking.

The result is a library that is nearly as fast as Daan's, and
is (almost) compatible with it. (The types in this module are
a bit more general than Daan's.)

A part of the code (the parser combinators like "many") is simply
taken from Daan's original code. I hope he doesn't mind :-)

-}

module Parsek
  -- basic parser type
  ( Parser         -- :: * -> * -> *; Functor, Monad, MonadPlus
  , Expect         -- :: *; = [String]
  , Unexpect       -- :: *; = [String]
  
  -- parsers
  , satisfy        -- :: Show s => (s -> Bool) -> Parser s s
  , look           -- :: Parser s [s]
  , succeeds       -- :: Parser s a -> Parser s (Maybe a)
  , string         -- :: (Eq s, Show s) => [s] -> Parser s [s]
  
  , char           -- :: Eq s => s -> Parser s s
  , noneOf         -- :: Eq s => [s] -> Parser s s
  , oneOf          -- :: Eq s => [s] -> Parser s s
 
  , spaces         -- :: Parser Char ()
  , space          -- :: Parser Char Char
  , newline        -- :: Parser Char Char
  , tab            -- :: Parser Char Char
  , upper          -- :: Parser Char Char
  , lower          -- :: Parser Char Char
  , alphaNum       -- :: Parser Char Char
  , letter         -- :: Parser Char Char
  , digit          -- :: Parser Char Char
  , hexDigit       -- :: Parser Char Char
  , octDigit       -- :: Parser Char Char
  , anyChar        -- :: Parser s s
  , anySymbol      -- :: Parser s s
  , munch, munch1  -- :: (s -> Bool) -> Parser s [s]

  -- parser combinators
  , label          -- :: String -> Parser s a -> Parser s a
  , (<?>)          -- :: Parser s a -> String -> Parser s a
  , pzero          -- :: Parser s a
  , (<|>)          -- :: Parser s a -> Parser s a -> Parser s a
  , (<<|>)         -- :: Parser s a -> Parser s a -> Parser s a
  , try            -- :: Parser s a -> Parser s a; = id
  , choice         -- :: [Parser s a] -> Parser s a
  , option         -- :: a -> Parser s a -> Parser s a
  , optional       -- :: Parser s a -> Parser s ()
  , between        -- :: Parser s open -> Parser s close -> Parser s a -> Parser s a
  , count          -- :: Int -> Parser s a -> Parser s [a]

  , chainl1        -- :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
  , chainl         -- :: Parser s a -> Parser s (a -> a -> a) -> a -> Parser s a
  , chainr1        -- :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
  , chainr         -- :: Parser s a -> Parser s (a -> a -> a) -> a -> Parser s a
 
  , skipMany1      -- :: Parser s a -> Parser s ()
  , skipMany       -- :: Parser s a -> Parser s ()
  , many1          -- :: Parser s a -> Parser s [a]
  , many           -- :: Parser s a -> Parser s [a]
  , sepBy1         -- :: Parser s a -> Parser s sep -> Parser s [a]
  , sepBy          -- :: Parser s a -> Parser s sep -> Parser s [a]
  
  -- parsing & parse methods
  , ParseMethod    -- :: * -> * -> * -> * -> *
  , ParseResult    -- :: * -> * -> *; = Either (e, Expect, Unexpect) r
  , parseFromFile  -- :: Parser Char a -> ParseMethod Char a e r -> FilePath -> IO (ParseResult e r)
  , parse          -- :: Parser s a -> ParseMethod s a e r -> [s] -> ParseResult e r

  , shortestResult             -- :: ParseMethod s a (Maybe s) a
  , longestResult              -- :: ParseMethod s a (Maybe s) a
  , longestResults             -- :: ParseMethod s a (Maybe s) [a]
  , allResults                 -- :: ParseMethod s a (Maybe s) [a]
  , allResultsStaged           -- :: ParseMethod s a (Maybe s) [[a]]
  , completeResults            -- :: ParseMethod s a (Maybe s) [a]
  
  , shortestResultWithLeftover -- :: ParseMethod s a (Maybe s) (a,[s])
  , longestResultWithLeftover  -- :: ParseMethod s a (Maybe s) (a,[s])
  , longestResultsWithLeftover -- :: ParseMethod s a (Maybe s) ([a],[s])
  , allResultsWithLeftover     -- :: ParseMethod s a (Maybe s) [(a,[s])]
  
  , completeResultsWithLine    -- :: ParseMethod Char a Int [a]
  )
 where
  
import Monad
  ( MonadPlus(..)
  , guard
  )

import List
  ( union
  , intersperse
  )

import Char

infix  0 <?>
infixr 1 <|>, <<|>

-------------------------------------------------------------------------
-- type Parser

newtype Parser s a
  = Parser (forall res . (a -> Expect -> P s res) -> Expect -> P s res)

-- type P; parsing processes

data P s res
  = Symbol (s -> P s res)
  | Look ([s] -> P s res)
  | Fail Expect Unexpect
  | Result res (P s res)

-- type Expect, Unexpect

type Expect
  = [String]

type Unexpect
  = [String]

-------------------------------------------------------------------------
-- instances: Functor, Monad, MonadPlus

instance Functor (Parser s) where
  fmap p (Parser f) =
    Parser (\fut -> f (fut . p))

instance Monad (Parser s) where
  return a =
    Parser (\fut -> fut a)
  
  Parser f >>= k =
    Parser (\fut -> f (\a -> let Parser g = k a in g fut))

  fail s =
    Parser (\fut exp -> Fail exp [s])

instance MonadPlus (Parser s) where
  mzero =
    Parser (\fut exp -> Fail exp [])
    
  mplus (Parser f) (Parser g) =
    Parser (\fut exp -> f fut exp `plus` g fut exp)

plus :: P s res -> P s res -> P s res
Symbol fut1    `plus` Symbol fut2    = Symbol (\s -> fut1 s `plus` fut2 s)
Fail exp1 err1 `plus` Fail exp2 err2 = Fail (exp1 `union` exp2) (err1 `union` err2)
p              `plus` Result res q   = Result res (p `plus` q)
Result res p   `plus` q              = Result res (p `plus` q)
Look fut1      `plus` Look fut2      = Look (\s -> fut1 s `plus` fut2 s)
Look fut1      `plus` q              = Look (\s -> fut1 s `plus` q)
p              `plus` Look fut2      = Look (\s -> p `plus` fut2 s)
p@(Symbol _)   `plus` _              = p
_              `plus` q@(Symbol _)   = q

-------------------------------------------------------------------------
-- primitive parsers

anySymbol :: Parser s s
anySymbol =
  Parser (\fut exp -> Symbol (\c ->
    fut c []
  ))

satisfy :: Show s => (s -> Bool) -> Parser s s
satisfy pred =
  Parser (\fut exp -> Symbol (\c ->
    if pred c
      then fut c []
      else Fail exp [show [c]]
  ))

label :: Parser s a -> String -> Parser s a
label (Parser f) s =
  Parser (\fut exp ->
    if null exp
      then f (\a _ -> fut a []) [s]
      else f fut exp
  )

look :: Parser s [s]
look =
  Parser (\fut exp ->
    Look (\s -> fut s exp)
  )

succeeds :: Parser s a -> Parser s (Maybe a)
succeeds (Parser f) =
  Parser (\fut exp ->
    Look (\xs ->
      let sim (Symbol f)     q (x:xs) = sim (f x) (\k -> Symbol (\_ -> q k)) xs
          sim (Look f)       q xs     = sim (f xs) q xs
          sim p@(Result _ _) q xs     = q (cont p)
          sim _              _ _      = fut Nothing []

          cont (Symbol f)       = Symbol (\x -> cont (f x))
          cont (Look f)         = Look (\s -> cont (f s))
          cont (Result a p)     = fut (Just a) [] `plus` cont p
          cont (Fail exp unexp) = Fail exp unexp

       in sim (f (\a _ -> Result a (Fail [] [])) exp) id xs
    )
  )

-- specialized

string :: (Eq s, Show s) => [s] -> Parser s [s]
string s =
  Parser (\fut exp ->
    let inputs []     = fut s []
        inputs (x:xs) =
          Symbol (\c ->
            if c == x
              then inputs xs
              else Fail (if null exp then [show s] else exp) [show [c]]
          )
     
     in inputs s
  )

-------------------------------------------------------------------------
-- derived parsers

char c    = satisfy (==c)         <?> show [c]
noneOf cs = satisfy (\c -> not (c `elem` cs))
oneOf cs  = satisfy (\c -> c `elem` cs)

spaces    = skipMany space        <?> "white space"
space     = satisfy (isSpace)     <?> "space"
newline   = char '\n'             <?> "new-line"
tab       = char '\t'             <?> "tab"
upper     = satisfy (isUpper)     <?> "uppercase letter"
lower     = satisfy (isLower)     <?> "lowercase letter"
alphaNum  = satisfy (isAlphaNum)  <?> "letter or digit"
letter    = satisfy (isAlpha)     <?> "letter"
digit     = satisfy (isDigit)     <?> "digit"
hexDigit  = satisfy (isHexDigit)  <?> "hexadecimal digit"
octDigit  = satisfy (isOctDigit)  <?> "octal digit"
anyChar   = anySymbol

munch :: (s -> Bool) -> Parser s [s]
munch p =
  do cs <- look
     scan cs
 where
  scan (c:cs) | p c = do anySymbol; as <- scan cs; return (c:as)
  scan _            = do return []

munch1 :: Show s => (s -> Bool) -> Parser s [s]
munch1 p =
  do c  <- satisfy p
     cs <- munch p
     return (c:cs)

-----------------------------------------------------------
-- parser combinators

(<?>) :: Parser s a -> String -> Parser s a
p <?> s = label p s

pzero :: Parser s a
pzero = mzero

(<|>) :: Parser s a -> Parser s a -> Parser s a
p <|> q = p `mplus` q

(<<|>) :: Parser s a -> Parser s a -> Parser s a
p <<|> q =
  do ma <- succeeds p
     case ma of
       Nothing -> q
       Just a  -> return a

try :: Parser s a -> Parser s a
try p = p -- backwards compatibility with Parsec

choice :: [Parser s a] -> Parser s a
choice ps = foldr (<|>) mzero ps

option :: a -> Parser s a -> Parser s a
option x p = p <|> return x

optional :: Parser s a -> Parser s ()
optional p = (do p; return ()) <|> return ()

between :: Parser s open -> Parser s close -> Parser s a -> Parser s a
between open close p = do open; x <- p; close; return x

-- repetition
                
skipMany1,skipMany :: Parser s a -> Parser s ()
skipMany1 p = do p; skipMany p
skipMany  p = let scan = (do p; scan) <|> return () in scan

many1,many :: Parser s a -> Parser s [a]
many1 p = do x <- p; xs <- many p; return (x:xs)
many  p = let scan f = (do x <- p; scan (f.(x:))) <|> return (f []) in scan id

sepBy1,sepBy :: Parser s a -> Parser s sep -> Parser s [a]
sepBy  p sep = sepBy1 p sep <|> return []
sepBy1 p sep = do x <- p; xs <- many (do sep; p); return (x:xs)

count :: Int -> Parser s a -> Parser s [a]
count n p = sequence (replicate n p)

chainr,chainl :: Parser s a -> Parser s (a -> a -> a) -> a -> Parser s a
chainr p op x = chainr1 p op <|> return x
chainl p op x = chainl1 p op <|> return x

chainr1,chainl1 :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainr1 p op = scan
 where
  scan   = do x <- p; rest x
  rest x = (do f <- op; y <- scan; return (f x y)) <|> return x

chainl1 p op = scan
 where
  scan   = do x <- p; rest x
  rest x = (do f <- op; y <- p; rest (f x y)) <|> return x
                              
-------------------------------------------------------------------------
-- type ParseMethod, ParseResult

type ParseMethod s a e r
  = P s a -> [s] -> ParseResult e r

type ParseResult e r
  = Either (e, Expect, Unexpect) r

-- parse functions

parseFromFile :: Parser Char a -> ParseMethod Char a e r -> FilePath -> IO (ParseResult e r)
parseFromFile p method file =
  do s <- readFile file
     return (parse p method s)

parse :: Parser s a -> ParseMethod s a e r -> [s] -> ParseResult e r
parse (Parser f) method xs =
  case method (f (\a exp -> Result a (Fail exp [])) []) xs of
    Left (err, exp, unexp) -> Left (err, [ s | s@(_:_) <- exp ], unexp)
    Right x                -> Right x

-- parse methods

shortestResult :: ParseMethod s a (Maybe s) a
shortestResult p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res _) _      = Right res
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

longestResult :: ParseMethod s a (Maybe s) a
longestResult p xs = scan p Nothing xs
 where
  scan (Symbol sym)   mres       (x:xs) = scan (sym x) mres xs
  scan (Symbol _)     mres       []     = scan (Fail [] []) mres []
  scan (Result res p) _          xs     = scan p (Just res) xs
  scan (Fail exp err) Nothing    (x:xs) = failSym x exp err
  scan (Fail exp err) Nothing    []     = failEof exp err
  scan (Fail _ _)     (Just res) _      = Right res
  scan (Look f)       mres       xs     = scan (f xs) mres xs

longestResults :: ParseMethod s a (Maybe s) [a]
longestResults p xs = scan p [] [] xs
 where
  scan (Symbol sym)   []  old (x:xs) = scan (sym x) [] old xs
  scan (Symbol sym)   new old (x:xs) = scan (sym x) [] new xs
  scan (Symbol _)     new old []     = scan (Fail [] []) new old []
  scan (Result res p) new old xs     = scan p (res:new) [] xs
  scan (Fail exp err) []  []  (x:xs) = failSym x exp err
  scan (Fail exp err) []  []  []     = failEof exp err
  scan (Fail _ _)     []  old _      = Right old
  scan (Fail _ _)     new _   _      = Right new
  scan (Look f)       new old xs     = scan (f xs) new old xs
 
allResultsStaged :: ParseMethod s a (Maybe s) [[a]]
allResultsStaged p xs = Right (scan p [] xs)
 where
  scan (Symbol sym)   ys (x:xs) = ys : scan (sym x) [] xs
  scan (Symbol _)     ys []     = [ys]
  scan (Result res p) ys xs     = scan p (res:ys) xs
  scan (Fail _ _)     ys _      = [ys]
  scan (Look f)       ys xs     = scan (f xs) ys xs
 
allResults :: ParseMethod s a (Maybe s) [a]
allResults p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res p) xs     = Right (res : scan' p xs)
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

completeResults :: ParseMethod s a (Maybe s) [a]
completeResults p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res p) []     = Right (res : scan' p [])
  scan (Result _ p)   xs     = scan p xs
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

-- with left overs

shortestResultWithLeftover :: ParseMethod s a (Maybe s) (a,[s])
shortestResultWithLeftover p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res _) xs     = Right (res,xs)
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

longestResultWithLeftover :: ParseMethod s a (Maybe s) (a,[s])
longestResultWithLeftover p xs = scan p Nothing xs
 where
  scan (Symbol sym)   mres         (x:xs) = scan (sym x) mres xs
  scan (Symbol _)     mres         []     = scan (Fail [] []) mres []
  scan (Result res p) _            xs     = scan p (Just (res,xs)) xs
  scan (Fail exp err) Nothing      (x:xs) = failSym x exp err
  scan (Fail exp err) Nothing      []     = failEof exp err
  scan (Fail _ _)     (Just resxs) _      = Right resxs
  scan (Look f)       mres         xs     = scan (f xs) mres xs

longestResultsWithLeftover :: ParseMethod s a (Maybe s) ([a],Maybe [s])
longestResultsWithLeftover p xs = scan p empty empty xs
 where
  scan (Symbol sym)   ([],_) old    (x:xs) = scan (sym x) empty old xs
  scan (Symbol sym)   new    old    (x:xs) = scan (sym x) empty new xs
  scan (Symbol _)     new    old    []     = scan (Fail [] []) new old []
  scan (Result res p) (as,_) old    xs     = scan p (res:as,Just xs) empty xs
  scan (Fail exp err) ([],_) ([],_) (x:xs) = failSym x exp err
  scan (Fail exp err) ([],_) ([],_) []     = failEof exp err
  scan (Fail _ _)     ([],_)  old _        = Right old
  scan (Fail _ _)     new _   _            = Right new
  scan (Look f)       new    old    xs     = scan (f xs) new old xs
 
  empty = ([],Nothing)
 
allResultsWithLeftover :: ParseMethod s a (Maybe s) [(a,[s])]
allResultsWithLeftover p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res p) xs     = Right ((res,xs) : scan' p xs)
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

completeResultsWithLine :: ParseMethod Char a Int [a]
completeResultsWithLine p xs = scan p 1 xs
 where
  scan (Symbol sym)   n (x:xs) = let n' = x |> n in n' `seq` scan (sym x) n' xs
  scan (Symbol _)     n []     = scan (Fail [] ["end of file"]) n []
  scan (Result res p) n []     = Right (res : scan' p n [])
  scan (Result _ p)   n xs     = scan p n xs
  scan (Fail exp err) n xs     = Left (n, exp, err)
  scan (Look f)       n xs     = scan (f xs) n xs

  scan' p n xs =
    case scan p n xs of
      Left  _    -> []
      Right ress -> ress
  
  '\n' |> n = n+1
  _    |> n = n

-- failing

failSym :: s -> Expect -> Unexpect -> ParseResult (Maybe s) r
failSym s exp err = Left (Just s, exp, err)

failEof :: Expect -> Unexpect -> ParseResult (Maybe s) r
failEof exp err = Left (Nothing, exp, err ++ ["end of file"])

-------------------------------------------------------------------------
-- the end.

