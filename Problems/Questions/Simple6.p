%----Using UNA
% Answer pi(a,a,a)
% Answer pi(g(e,e),w,b)
% No more answers are possible
%----Using UNA with optimism 
% Answer pi(a,a,a)
% Answer pi(g(e,e),w,b)
% Answer pi(h(d),g(a,c),g(b,b))
% No more answers are possible

fof(ab,axiom,(
    a != b )).

fof(ghgh,axiom,(
    pi(g(e,e),w,b) )).

fof(dsfsf,axiom,(
    pi(h(d),g(a,c),g(b,b)) )).

fof(fafa,axiom,(
    pi(a,a,a) )).

fof(ab,question,(
    ? [X,Y,Z] : pi(X,Y,Z) )).
%fof(ab,conjecture,(
%    ? [X,Y,Z] : (~$answer(X,Y,Z) & pi(X,Y,Z)) )).

