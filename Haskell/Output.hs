module Output where

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

import System
import Flags
import Form( Answer )

---------------------------------------------------------------------------
-- outputs

putInfo :: String -> IO ()
putInfo s = putStrLn s

putOfficial :: String -> IO ()
putOfficial s = putStrLn ("+++ " ++ s)

putResult :: (?flags :: Flags) => Answer -> IO ()
putResult ans =
  do putOfficial ( "RESULT: "
                ++ show ans
                ++ (case files ?flags of
                     _:_:_ -> " (" ++ thisFile ?flags ++ ")"
                     _     -> "")
                 )
     if tstp ?flags then
       putInfo ( "SZS status "
              ++ show ans
              ++ " for "
              ++ thisFile ?flags
               )
      else
       return ()

putWarning :: String -> IO ()
putWarning s = putStrLn ("*** " ++ s)

putFailure :: String -> IO a
putFailure s = do putWarning s; exitWith (ExitFailure 1)

putHeader :: String -> IO ()
putHeader s = putStrLn ("=== " ++ s)

putSubHeader :: String -> IO ()
putSubHeader s = putStrLn ("--- " ++ s)

---------------------------------------------------------------------------
-- the end.
