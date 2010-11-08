%% Notice: the type 'set' has no function symbols; we ought to be able
%% to do something with it!
%%
%% If we added some functions on sets, we
%% maybe should be able to infer some constraints on the types: e.g.,
%% nat is infinite (since we don't have any inequalities on nat, maybe
%% we can get that nat needs only size one instead).

tff(foo, type, (nat: $tType)).
tff(foo, type, (elem: $tType)).
tff(foo, type, (set: $tType)).
tff(foo, type, (in: (elem * set) > $o)).
tff(foo, type, (size: set > nat)).
tff(foo, type, (succ: nat > nat)).
tff(foo, type, (pred: nat > nat)).
tff(foo, type, (leq: (nat * nat) > $o)).
tff(foo, type, (nonzero: nat > $o)).
tff(foo, type, (subset: (set * set) > $o)).
tff(foo, type, (zero : nat)).

tff(foo, definition, ![S: set, T: set]: (subset(S, T) <=> ![X: elem]: (in(X,S) => in(X,T)))).
tff(foo, axiom, ![S: set, T: set]: ((S = T) <=> (subset(S, T) & subset(T, S)))).
tff(foo, axiom, ![S: set, T: set]: (subset(S, T) => leq(size(S), size(T)))).
tff(foo, axiom, ![N: nat]: (nonzero(N) <=> ~leq(N, zero))).
tff(foo, axiom, ![N: nat]: (nonzero(N) => succ(pred(N)) = N)).
tff(foo, axiom, pred(zero) = zero).
