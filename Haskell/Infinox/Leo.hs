module Infinox.Leo where

import System.IO
import Infinox.Util
import Output

classifyWithLeo axiomfile = do
                        b <- leoprove conjecture axiomfile
                        if b then return Some else return None



conjecture = "thf(c4,conjecture," ++

        -- exists (G : i -> i) : forall (X:i) : forall (Y:i) : ( G(X) = G(Y) ==> X = Y) &&

        "?[G:$i>$i] :(((![X:$i]:( ![Y:$i]:(~((G @ X) = (G @ Y))|(X = Y)))) & " ++

        -- exists (Y:i) : forall (X:i) : G(X) != Y
        "( ?[Y:$i] : ![X:$i] : ~((G@X) = Y))) " ++


        --exists (X:i) : exists (Y:i) : (X != Y &&
        " | ((?[X:$i] : ?[Y:$i] : ((X != Y) & " ++
        --G(X) = G(Y)) &&
                        "((G @ X) = (G @ Y)))) & " ++
        --forall(Y:i) : exists (X:i) : G(X) = Y
                                " (![Y:$i] : ?[X:$i] : ((G@X) = Y)))))."

