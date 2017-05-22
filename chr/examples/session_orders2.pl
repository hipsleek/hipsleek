#!/usr/bin/swipl -q
:- module(orders, [ev/1,hb/2,hbp/2,cb/2,snot/1,snot_eq/2]).
:- use_module(library(chr)).

%:- initialization start.
:- chr_constraint ev/1,hb/2,hbp/2,cb/2,snot/1,snot_eq/2.


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
neg2   @ snot(A;B) <=> snot(A),snot(B).
neg3   @ snot((A,B)) <=> snot(A);snot(B).
neg4   @ ev(A),snot(ev(A))  <=> false.
neg5   @ hb(A,B),snot(hb(A,B)) <=> false.
neg5   @ hbp(A,B),snot(hbp(A,B)) <=> false.
neg5   @ snot(snot_eq(A,B)) <=> A=B.
neg6   @ snot_eq(A,A) <=> false.
% neg5   @ hb(A,A),snot(hb(A,A)) <=> false.
sym1   @ hb(A,B)\hb(A,B) <=> true .
asy2   @ hb(A,B),hb(B,A)   <=> A=B.
asy3   @ hbp(A,B),hbp(B,A) <=> false.
asy4   @ hbp(A,A) <=> false.
asy5   @ cb(A,B) ==>  snot_eq(A,B).
% HB transitivity 
% hbhb   @ hb(A,B), hb(B,C) ==> A\=B,B\=C | hb(A,C).
hbhb   @ hb(A,B), hb(B,C) ==>  hb(A,C).
hbplus @ hb(B,C), snot_eq(B,C) ==> hbp(B,C).
hbplus @ hbp(B,C) ==> hb(B,C).
hbhb   @ hb(A,B), hbp(B,C)  ==>  hbp(A,C).
hbhb   @ hbp(A,B), hb(B,C)  ==>  hbp(A,C).
hbhb   @ hbp(A,B), hbp(B,C) ==>  hbp(A,C).
cbhb   @ cb(A,B), hbp(B,C)  ==>  hbp(A,C).

% hb(A,L1,B,L2) :- hb(A,L1,C,L3),hb(C,L3,B,L2).
% hb(A,L1,B,L2) :- cb(A,L1,C,L1),hb(C,L1,B,L2).

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


%  hb(X,1,Y,2),hb(X,0,Y,2),hb(Y,2,Y,2),hb(X,1,Z,3).
% halt.
% ^C
% Action (h for help) ? abort
                                % % Execution Aborted

% hb(X,1,Z,3), ?? |- hb(X,1,Y,2)

% hb(X,1,Z,3), hb(Z,3,Y,2) |- hb(X,1,Y,2)

% hb(Z,3,X,1) ;  hb(X,1,Y,2)
 
% hb(A,L1,B,L2) :- hb(A,L1,C,L3),hb(C,L3,B,L2).
% hb(A,L1,B,L2) :- cb(A,L1,C,L1),hb(C,L1,B,L2).

% A , Q |- B.
