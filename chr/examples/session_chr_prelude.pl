/*
orders.pl: Orders propagation rules

%% DESCRIPTION

%% HOW TO USE
Events are pairs of role x label:
e.g.  event(A,1), event(B2,a)

Happens-before relations are pairs of (event x event):
e.g.  hb(event(A,1), event(B2,a))

Communicates-before relations are pairs of (event x event):
e.g.  cb(event(A,a), event(B2,a))
  

%% SAMPLE QUERIES
% ?- hb(event(X,1),event(Y,2)), hb(event(Y,2),event(Z,3)).
% hb(event(X, 1), event(Z, 3)),
% hb(event(Y, 2), event(Z, 3)),
% hb(event(X, 1), event(Y, 2)).

?- hb(event(X,1),event(Y,2)), hb(event(Y,2),event(Z,3)), hb(event(Z,3),event(T,a)).
hb(event(X, 1), event(T, a)),
hb(event(Y, 2), event(T, a)),
hb(event(X, 1), event(T, a)),
hb(event(Z, 3), event(T, a)),
hb(event(X, 1), event(Z, 3)),
hb(event(Y, 2), event(Z, 3)),
hb(event(X, 1), event(Y, 2)).

?- cb(event(X,2),event(Y,2)), hb(event(Y,2),event(Z,3)), hb(event(Z,3),event(T2,a)).
hb(event(X, 2), event(T2, a)),
hb(event(Y, 2), event(T2, a)),
hb(event(X, 2), event(T2, a)),
hb(event(Z, 3), event(T2, a)),
hb(event(X, 2), event(Z, 3)),
hb(event(Y, 2), event(Z, 3)),
cb(event(X, 2), event(Y, 2)).

?- cb(event(X,7),event(Y,2)), hb(event(Y,2),event(Z,3)), hb(event(Z,3),event(T2,a)).
  false

?- hb(event(X,1),event(Y,2)), hb(event(Y,4),event(Z,3)).

*/

:- module(orders, [event/2,hb/2,cb/2,imp/2,and/2,eq/2,analyse_trail/0,added/1,removed/1]).
:- use_module(library(chr)).


%% Syntax for SWI / SICStus 4.x
:- chr_constraint event/2,hb/2,cb/2,imp/2,and/2,contains/2,eq/2,analyse_trail/0,added/1,removed/1.

% hbhb   @ hb(event(A,L1),event(B,L2)), hb(event(B,L3),event(C,L4)) ==> L2=L3, hb(event(A,L1),event(C,L4)).
% cbhb   @ cb(event(A,L1),event(B,L2)), hb(event(B,L3),event(C,L4)) ==> L1=L2,L2=L3, hb(event(A,L1),event(C,L4)).

% and(X,Y) <=> X,Y.

hbhb   @ hb(event(A,L1),event(B,L2)), hb(event(B,L2),event(C,L4)) ==> hb(event(A,L1),event(C,L4)).
cbhb   @ cb(event(A,L1),event(B,L1)), hb(event(B,L1),event(C,L4)) ==> hb(event(A,L1),event(C,L4)).

imp(X,Y) <=> eq(X,and(X,Y)) .

eq(X,and(Y,Z)) <=> eq(X,Y),eq(X,Z).
eq(and(Y,Z),X) <=> eq(Y,X),eq(Z,X).

% eq(event(A1,L1),event(A2,L2)) <=> A1 \= A2, L1 \= L2 | false.
% eq(event(A1,L1),event(A2,L2)) <=> A1 == A2, L1 \= L2 | false.
% eq(event(A1,L1),event(A2,L2)) <=> A1 \= A2, L1 == L2 | false.
eq(event(A1,L1),event(A2,L2)) <=> A1 == A2, L1 == L2 | true.

% eq(hb(event(A1,L1),event(B1,E1)), hb(event(A2,L2),event(B2,E2))) <=> not(eq(event(A1,L1),event(A2,L2))), not(eq(event(B1,E1),event(B2,E2))) | false .
% eq(hb(event(A1,L1),event(B1,E1)), hb(event(A2,L2),event(B2,E2))) <=> eq(event(A1,L1),event(A2,L2)), not(eq(event(B1,E1),event(B2,E2))) | false.
% eq(hb(event(A1,L1),event(B1,E1)), hb(event(A2,L2),event(B2,E2))) <=> not(eq(event(A1,L1),event(A2,L2))), eq(event(B1,E1),event(B2,E2)) | false.
eq(hb(event(A1,L1),event(B1,E1)), hb(event(A2,L2),event(B2,E2))) <=> eq(event(A1,L1),event(A2,L2)), eq(event(B1,E1),event(B2,E2)) | true.

reflexive @ eq(X,Y) <=> X == Y | true.
redundant @ eq(X1,Y1) \ eq(X2,Y2) <=> X1 == X2, Y1 == Y2 | true.
symmetric @ eq(X,Y) ==> eq(Y,X).
transitive @ eq(X1,Y1), eq(X2,Y2) ==> Y1 == X2 | eq(X1,Y2).

reflexive @ eq(X,Y) <=> X \= Y | false.


% well formedness
% cbw    @ cb(event(X,A),event(Y,B)) ==> A\=B , false.
