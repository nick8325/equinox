module Equinox.Fair where

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
