module SmellySox.Test where

import SmellySox.Formula

test = Formula { types = ["Obj", "Arr"],
                 constants = [compose, ident, source, target, badObj, badArr,
                              a, b, pair, p1, p2, paired],
                 forms = [
                  ("category", Axiom,
                   foldr1 (Binop And) [associativity, idLeft, idRight,
                                       idType, composeDefined, badCompose,
                                       badSource, badTarget ]),
                  ("product", Axiom,
                   foldr1 (Binop And) [pairType, pairNotBad, pType, p1pair,
                                       p2pair, uniqueness, pairedDef ]),
                  ("conjecture", NegatedConjecture, notUniversal)]}
  where compose = Fun "compose" ["Arr", "Arr"] "Arr"
        ident = Fun "ident" ["Obj"] "Arr"
        source = Fun "source" ["Arr"] "Obj"
        target = Fun "target" ["Arr"] "Obj"
        badObj = Fun "badObj" [] "Obj"
        badArr = Fun "badArr" [] "Arr"
        a = Fun "a" [] "Obj"
        b = Fun "b" [] "Obj"
        axb = Fun "axb" [] "Obj"
        pair = Fun "pair" ["Arr", "Arr"] "Arr"
        p1 = Fun "p1" [] "Arr"
        p2 = Fun "p2" [] "Arr"
        paired = Pred "paired" ["Arr", "Arr"]
        x = Var "X" "Obj"
        y = Var "Y" "Obj"
        z = Var "Z" "Obj"
        f = Var "F" "Arr"
        g = Var "G" "Arr"
        h = Var "H" "Arr"
        h' = Var "H'" "Arr"

        associativity =
          Quant ForAll f . Quant ForAll g . Quant ForAll h $
            compose :@: [f :@: [], compose :@: [g :@: [], h :@: []]] :=:
            compose :@: [compose :@: [f :@: [], g :@: []], h :@: []]

        idLeft =
          Quant ForAll f $
            compose :@: [ident :@: [target :@: [f :@: []]], f :@: []] :=:
            f :@: []

        idRight =
          Quant ForAll f $
            compose :@: [f :@: [], ident :@: [source :@: [f :@: []]]] :=:
            f :@: []

        idType =
          Quant ForAll x $
            Binop And (source :@: [ident :@: [x :@: []]] :=: x :@: [])
                      (target :@: [ident :@: [x :@: []]] :=: x :@: [])

        composeDefined =
          Quant ForAll f . Quant ForAll g $
            Binop Implies
              (target :@: [g :@: []] :=: source :@: [f :@: []])
              (Binop And
               (target :@: [composition] :=: target :@: [f :@: []])
               (source :@: [composition] :=: source :@: [g :@: []]))
          where composition = compose :@: [f :@: [], g :@: []]

        badCompose =
          Quant ForAll f . Quant ForAll g $
            Binop Implies
              (Not (target :@: [g :@: []] :=: source :@: [f :@: []]))
              (compose :@: [f :@: [], g :@: []] :=: badArr :@: [])

        badSource =
          Quant ForAll f $
             Binop Equiv
               (source :@: [f :@: []] :=: badObj :@: [])
               (f :@: [] :=: badArr :@: [])

        badTarget =
          Quant ForAll f $
             Binop Equiv
               (target :@: [f :@: []] :=: badObj :@: [])
               (f :@: [] :=: badArr :@: [])

        pairNotBad =
          foldr1 (Binop And) . map Not $
            [axb :@: [] :=: badObj :@: [],
             a :@: [] :=: badObj :@: [],
             b :@: [] :=: badObj :@: []]

        pairedDef =
          Quant ForAll f . Quant ForAll g . Quant ForAll x $
            Binop Equiv
              (Literal (paired :@: [f :@: [], g :@: []]))
              (foldr1 (Binop And)
                [source :@: [f :@: []] :=: source :@: [g :@: []],
                 target :@: [f :@: []] :=: a :@: [],
                 target :@: [g :@: []] :=: b :@: []])

        pairType =
          Quant ForAll f . Quant ForAll g $
             Binop Equiv
               (Literal (paired :@: [f :@: [], g :@: []]))
               (Binop And
                  (source :@: [pair :@: [f :@: [], g :@: []]] :=: source :@: [f :@: []])
                  (target :@: [pair :@: [f :@: [], g :@: []]] :=: axb :@: []))

        pType =
          Binop And (projection p1 a) (projection p2 b)
            where projection p t =
                    Binop And
                      (source :@: [p :@: []] :=: axb :@: [])
                      (target :@: [p :@: []] :=: t :@: [])

        p1pair =
          Quant ForAll f . Quant ForAll g $
             Binop Implies
               (Literal (paired :@: [f :@: [], g :@: []]))
               (p1 :@: [pair :@: [f :@: [], g :@: []]] :=: f :@: [])

        p2pair =
          Quant ForAll f . Quant ForAll g $
             Binop Implies
               (Literal (paired :@: [f :@: [], g :@: []]))
               (p2 :@: [pair :@: [f :@: [], g :@: []]] :=: g :@: [])

        uniqueness =
          Quant ForAll f . Quant ForAll g .
             Binop Implies
               (Literal (paired :@: [f :@: [], g :@: []])) $
             existsUnique h h' $ \h ->
               Binop And
                 (compose :@: [p1 :@: [], h :@: []] :=: f :@: [])
                 (compose :@: [p2 :@: [], h :@: []] :=: g :@: [])
            where existsUnique x y f =
                    Quant Exists x
                      (Binop And (f x)
                                 (Quant ForAll y
                                    (Binop Implies (f y) (x :@: [] :=: y :@: []))))

        notUniversal =
          Quant Exists f $
                Binop And
                  (target :@: [f :@: []] :=: axb :@: [])
                  (Not (f :@: [] :=:
                          pair :@: [compose :@: [p1 :@: [], f :@: []],
                                    compose :@: [p2 :@: [], f :@: []]]))
