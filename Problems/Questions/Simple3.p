%----Using UNA
% No more answers are possible

%fof(pXY,question,(
%    ? [X,Y] : p(X,Y) )).
fof(pXY,conjecture,(
    ? [X,Y] : (~$answer(X,Y) & p(X,Y)) )).

