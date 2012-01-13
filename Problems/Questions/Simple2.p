%----Using UNA
% Answer p(c,d)
% Answer p(a,b)
% Answer p(e,X_1)
% Answer p(f,X_2)
% No more answers are possible

fof(pab,axiom,(
    p(a,b) )).

fof(pcd,axiom,(
    p(c,d) )).

fof(pcd,axiom,(
    ! [Z] : p(e,Z) )).

fof(pcd,axiom,(
    ! [Z] : p(f,Z) )).

fof(pXY,conjecture,(
    ? [X,Y] : (~$answer(X,Y) & p(X,Y)) )).

