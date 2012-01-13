
cnf(in_interval,axiom,
    ( in_interval(Lower,X,Upper)
    | ~ less_than_or_equal(Lower,X)
    | ~ less_than_or_equal(X,Upper) )).

%----Inequality axioms
cnf(reflexivity_of_less,axiom,
    ( less_than_or_equal(X,X) )).

cnf(totality_of_less,axiom,
    ( less_than_or_equal(X,Y)
    | less_than_or_equal(Y,X) )).

cnf(transitivity_of_less,axiom,
    ( less_than_or_equal_(merge(P,Q))
    | ~ less_than_or_equal_(P)
    | ~ less_than_or_equal_(Q) )).

cnf(transitivity_of_less,axiom,
    ( ~less_than_or_equal_(t(X,Z))
    | less_than_or_equal(X,Z)
    ) ).

cnf(transitivity_of_less,axiom,
    ( less_than_or_equal_(t(X,Z))
    | ~less_than_or_equal(X,Z)
    ) ).

cnf(transitivity_of_less,axiom,
    ( merge(t(X,Y),t(Y,Z)) = t(X,Z)
    ) ).

%----Interpolation axioms
cnf(interpolation1,axiom,
    ( ~ less_than_or_equal(X,q(Y,X))
    | less_than_or_equal(X,Y) )).

cnf(interpolation2,axiom,
    ( ~ less_than_or_equal(q(X,Y),X)
    | less_than_or_equal(Y,X) )).

%----Continuity axioms
cnf(continuity1,axiom,
    ( less_than_or_equal(f(X),n0)
    | ~ less_than_or_equal(X,h(X))
    | ~ in_interval(lower_bound,X,upper_bound) )).

cnf(continuity2,axiom,
    ( less_than_or_equal(f(X),n0)
    | ~ less_than_or_equal(Y,X)
    | ~ less_than_or_equal(f(Y),n0)
    | less_than_or_equal(Y,h(X))
    | ~ in_interval(lower_bound,X,upper_bound) )).

cnf(continuity3,axiom,
    ( less_than_or_equal(n0,f(X))
    | ~ less_than_or_equal(k(X),X)
    | ~ in_interval(lower_bound,X,upper_bound) )).

cnf(continuity4,axiom,
    ( less_than_or_equal(n0,f(X))
    | ~ less_than_or_equal(X,Y)
    | ~ less_than_or_equal(n0,f(Y))
    | less_than_or_equal(k(X),Y)
    | ~ in_interval(lower_bound,X,upper_bound) )).

%----Least upper bound axioms
cnf(crossover1,axiom,
    ( less_than_or_equal(X,l)
    | ~ less_than_or_equal(X,upper_bound)
    | ~ less_than_or_equal(f(X),n0) )).

cnf(crossover2_and_g_function1,axiom,
    ( less_than_or_equal(g(X),upper_bound)
    | less_than_or_equal(l,X) )).

cnf(crossover3_and_g_function2,axiom,
    ( less_than_or_equal(f(g(X)),n0)
    | less_than_or_equal(l,X) )).

cnf(crossover4_and_g_function3,axiom,
    ( ~ less_than_or_equal(g(X),X)
    | less_than_or_equal(l,X) )).

%----Endpoints of the interval
cnf(the_interval,hypothesis,
    ( less_than_or_equal(lower_bound,upper_bound) )).

cnf(lower_mapping,hypothesis,
    ( less_than_or_equal(f(lower_bound),n0) )).

cnf(upper_mapping,hypothesis,
    ( less_than_or_equal(n0,f(upper_bound)) )).

cnf(prove_there_is_x_which_crosses,negated_conjecture,
    ( ~ in_interval(f(X),n0,f(X)) )).

%--------------------------------------------------------------------------
