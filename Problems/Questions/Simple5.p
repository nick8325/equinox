%----Using inequality 
% Answer p(k,lkj,xyz)
% Answer p(a,b,c)
% More answers are possible
%----Using UNA
% Answer p(k,lkj,xyz)
% Answer p(h(d),g(e,e),k)
% Answer p(a,b,c)
% Answer p(g(e,e),w,b)
% Answer p(h(d),g(a,c),g(b,b))
% Answer p(a,a,a)
% No more answers are possible
%----Using UNA with optimism
% Answer p(k,lkj,xyz)
% Answer p(h(d),g(e,e),k)
% Answer p(a,b,c)
% Answer p(g(e,e),w,b)
% Answer p(h(d),g(a,c),g(b,b))
% Answer p(a,a,a)
% No more answers are possible

fof(a1,axiom,(
    p(a,b,c) )).

fof(a2,axiom,(
    p(g(e,e),w,b) )).

fof(a3,axiom,(
    p(h(d),g(a,c),g(b,b)) )).

fof(a4,axiom,(
    p(h(d),g(e,e),k) )).

fof(a5,axiom,(
    p(k,lkj,xyz) )).

fof(a6,axiom,(
    p(a,a,a) )).

fof(a7,axiom,
    ( a != k
    & a != lkj
    & a != xyz )).

%fof(name,question,(
%    ? [X,Y,Z] : p(X,Y,Z) )).
fof(name,conjecture,(
    ? [X,Y,Z] : (~$answer(X,Y,Z) & p(X,Y,Z)) )).
