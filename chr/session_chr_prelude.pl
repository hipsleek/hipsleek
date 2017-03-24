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
?- hb(event(X,1),event(Y,2)), hb(event(Y,2),event(Z,3)).
hb(event(X, 1), event(Z, 3)),
hb(event(Y, 2), event(Z, 3)),
hb(event(X, 1), event(Y, 2)).

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

:- module(orders, [event/2,hb/2,cb/2]).
:- use_module(library(chr)).


%% Syntax for SWI / SICStus 4.x
:- chr_constraint event/2,hb/2,cb/2.

% hbhb   @ hb(event(A,L1),event(B,L2)), hb(event(B,L3),event(C,L4)) ==> L2=L3, hb(event(A,L1),event(C,L4)).
% cbhb   @ cb(event(A,L1),event(B,L2)), hb(event(B,L3),event(C,L4)) ==> L1=L2,L2=L3, hb(event(A,L1),event(C,L4)).

hbhb   @ hb(event(A,L1),event(B,L2)), hb(event(B,L3),event(C,L4)) ==> hb(event(A,L1),event(C,L4)).
cbhb   @ cb(event(A,L1),event(B,L2)), hb(event(B,L3),event(C,L4)) ==> hb(event(A,L1),event(C,L4)).


% well formedness
% cbw    @ cb(event(X,A),event(Y,B)) ==> A\=B , false.
