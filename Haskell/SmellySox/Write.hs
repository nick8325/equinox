module SmellySox.Write where

import SmellySox.Formula
import Text.PrettyPrint.HughesPJ

prettyPrint :: Formula -> String
prettyPrint f = render (formula f)

formula f = vcat (map form (forms f))
form (name, kind, e) =
  sep [text "fof(",
       nest 2 (text (name ++ ",")),
       nest 2 (text (showKind kind ++ ",")),
       nest 2 (expr e),
       text ")."]
    where showKind Axiom = "axiom"
          showKind Hypothesis = "hypothesis"
          showKind Definition = "definition"
          showKind Conjecture = "conjecture"
          showKind NegatedConjecture = "negated_conjecture"

expr (Const True) = text "$true"
expr (Const False) = text "$false"
expr (Literal t) = term t
expr (t :=: u) = hsep [term t, text "=", term u]
expr (Binop op e1 e2) = sep [parenExpr e1, binop op <+> parenExpr e2]
expr (Not (t :=: u)) = hsep [term t, text "!=", term u]
expr (Not e) = text "~" <> parenExpr e
expr (Quant q x e) = hang (hcat [quant q, brackets (text (name x)), text ":"]) 2 (parenExpr e)

parenExpr e@Binop{} = parens (expr e)
parenExpr e = expr e

term (f :@: []) = text (name f)
term (f :@: xs) = text (name f) <> parens (sep (punctuate (text ",") (map term xs)))

binop And = text "&"
binop Or = text "|"
binop Implies = text "=>"
binop Equiv = text "<=>"

quant ForAll = text "!"
quant Exists = text "?"
