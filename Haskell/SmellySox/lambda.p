tff(foo, type, (var: $tType)).
tff(foo, type, (term: $tType)).

tff(foo, type, (lambda : (var * term) > term)).
tff(foo, type, (app : (term * term) > term)).
tff(foo, type, (v : var > term)).
tff(foo, type, (s : term)).
tff(foo, type, (k : term)).
tff(foo, type, (i : term)).
tff(foo, type, (y : term)).

tff(foo, axiom, ![X:var]: (lambda(X, v(X)) = i)).
tff(foo, axiom, ![X:var, Y:var]: ((X != Y) => lambda(X, v(Y)) = app(k, v(Y)))).
tff(foo, axiom, ![X:var]: (lambda(X, s) = app(k, s))).
tff(foo, axiom, ![X:var]: (lambda(X, k) = app(k, k))).
tff(foo, axiom, ![X:var]: (lambda(X, i) = app(k, i))).
tff(foo, axiom, ![X:var]: (lambda(X, y) = app(k, y))).
tff(foo, axiom, ![X:var, T: term, U: term]: (lambda(X, app(T, U)) = app(app(s, lambda(X, T)), lambda(X, U)))).
tff(foo, axiom, ![T:term, U:term]: (app(app(k,T),U) = T)).
tff(foo, axiom, ![T:term]: (app(i,T) = T)).
tff(foo, axiom, ![T:term, U:term, V:term]: (app(app(app(s,T),U),V) = app(app(T,U),app(T,V)))).

tff(foo, definition, ![F:term,X:var]: (app(y,F) =
    app(lambda(X, app(F, app(v(X),v(X)))),
    lambda(X, app(F, app(v(X),v(X))))))).
tff(foo, conjecture, ![T:term]: (app(y,T) = app(T,app(y,T)))).
