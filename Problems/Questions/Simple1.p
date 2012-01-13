%----Using inequality 
% Answer p(a,b)
% Answer p(b,X_1)
% Answer p(a,a)
% No more answers are possible
%----Using UNA
% Answer p(a,b)
% WARNING: Stopped by duplicate answer

fof(pab,axiom,(
    p(a,b) )).

fof(pafbc,axiom,(
    p(a,f(b,c)) )).

fof(pbZ,axiom,(
    ! [Z] : p(b,Z) )).

fof(pZc,axiom,(
    ! [Z] : p(Z,c) )).

fof(a_not_b,axiom,(
    a != b )).

fof(a_is_c,axiom,(
    a = c )).

%fof(pXY,question,(
%    ? [X,Y] : p(X,Y) )).
fof(pXY,conjecture,(
    ? [X,Y] : (~$answer(X,Y) & p(X,Y)) )).
