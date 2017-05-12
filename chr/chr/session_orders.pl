#!/usr/bin/swipl -q
:- module(orders, [ev/2,hb/4,cb/4,snot/1]).
:- use_module(library(chr)).

:- initialization start.
:- chr_constraint ev/2,hb/4,cb/4,snot/1.


% disable singleton warning
:- style_check(-singleton).


% %% HOW TO USE
% Evs are pairs of role x label:
% e.g.  ev(A,1), ev(B2,a)

% Happens-before relations are tuples of (ev x ev):
% e.g.  hb(A,1,B2,a)

% Communicates-before relations are pairs of (ev x ev):
% e.g.  cb(A,a,B2,a)

%% SAMPLE QUERIES
%Q: hb(X,1,Y,2),hb(X,0,Y,2),hb(Y,2,Z,3),hb(Z,3,Y,2).
%A: false

%Q: hb(X,1,Y,2),hb(X,0,Y,2),hb(Y,2,Z,3).
%A: true


%%%%%%%%%%
%%%% RULES
%%%%%%%%%%
%negation rules for hb and ev
neg0   @ snot(hb(A,L,A,L)) <=> true. %;(B=A,L2=L1).
neg1   @ snot(hb(A,L1,B,L2)) ==> hb(B,L2,A,L1). %;(B=A,L2=L1).
neg2   @ snot((A;B)) ==> snot(A),snot(B).
neg3   @ snot((A,B)) ==> snot(A);snot(B).
% neg4   @ snot(A) ==> \+(A).

asy1   @ ev(A,L1), snot(ev(A,L1))  ==> false.
% false when contradiction is detected : (a <_HB b && b <_HB a)
asy2   @ hb(A,L1,B,L2), hb(B,L2,A,L1) ==> false.
asy2   @ hb(A,L1,A,L1)  ==> false.
% HB transitivity 
hbhb   @ hb(A,L1,B,L2), hb(B,L2,C,L4) ==> hb(A,L1,C,L4).
% CB transitivity 
cbhb   @ cb(A,L1,B,L1), hb(B,L1,C,L4) ==> hb(A,L1,C,L4).

%%%%%%%%%%
%%%% UTILS
%%%%%%%%%%
writeln(T) :- write(T), nl.

checkff :-
        catch(read(user_input, Gl), E,
              ( print_message(error, E),
                halt
              ) ),
        (once((Gl)) -> writeln(true); writeln(false)).

start :-
    repeat,
    checkff,
    fail.
