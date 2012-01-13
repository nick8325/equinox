%----Using inequality 
% Answer p(X_1,a)
% No more answers are possible
%----Using UNA
% Answer p(X_1,a)
% WARNING: Stopped by duplicate answer

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

