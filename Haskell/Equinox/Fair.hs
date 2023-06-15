module Equinox.Fair where

{-
Equinox -- Copyright (c) 2003-2007, Koen Claessen

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

fair :: Int -> [a] -> [[a]]
fair n xs = concat [ enumWith xs en | en <- enums n k ]
 where
  k = length xs

  enumWith xs ns | all (==0) ns = [ [] ]
  enumWith xs ns =
    [ x : en
    | (x,ns') <- poss xs ns
    , en <- enumWith xs ns'
    ]

  poss []     []     = []
  poss (x:xs) (n:ns) = [ (x,(n-1):ns) | n > 0 ]
                    ++ [ (x',n:ns') | (x',ns') <- poss xs ns ]

enums :: Int -> Int -> [[Int]]
enums n k = concat [ map (++ replicate (k-i) 0) (ens n i)  | i <- [0..k] ]
 where
  ens 0 0 = [[]]
  ens n 0 = []
  ens n i = [ n' : ns
            | n' <- [n,n-1..0]
            , ns <- ens (n-n') (i-1)
            , n' > 0 || not (null ns)
            ]

--main = print (fair 2 [1,2,3,4])
