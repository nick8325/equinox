tff(foo, type, (a : $tType)).
tff(foo, type, (b : $tType)).
tff(foo, type, (p : a > $o)).
tff(foo, type, (f : b > a)).

tff(foo, axiom, ![A:a, B:b]: (~p(A) | A=f(B))).
tff(foo, conjecture, ?[B:b,B2:b]: (B!=B2 & f(B)!=f(B2))).
