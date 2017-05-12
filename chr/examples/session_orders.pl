#!/usr/bin/swipl -q
:- module(orders, [ev/2,hb/4,cb/4,snot/1,test/0,infer/4,looplabel/4,looprole/4,inferhb/3,combroles/2,comblabels/2,allevents/2,allhb1/2,allhb2/2,allhb/1]).
:- use_module(library(chr)).

%:- initialization start.
:- chr_constraint ev/2,hb/4,cb/4,snot/1,test/0,infer/4,looplabel/4,looprole/4,inferhb/3,combroles/2,comblabels/2,allevents/2,allhb1/2,allhb2/2,allhb/1.


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
neg2   @ snot(A;B) ==> snot(A),snot(B).
neg3   @ snot((A,B)) ==> snot(A);snot(B).
% neg4   @ snot(A) ==> \+(A).

asy1   @ ev(A,L1), snot(ev(A,L1))  ==> false.
% false when contradiction is detected : (a <_HB b && b <_HB a)
asy2   @ hb(A,L1,B,L2), hb(B,L2,A,L1) ==> A=B,L1=L2.
asy2   @ hb(A,L1,A,L1)  <=> true.
% HB transitivity 
hbhb   @ hb(A,L1,B,L2), hb(B,L2,C,L4) ==> hb(A,L1,C,L4).
% CB transitivity 
cbhb   @ cb(A,L1,B,L1), hb(B,L1,C,L4) ==> B\=C,L1\=L4 | hb(A,L1,C,L4).
% cbhb   @ cb(A,L1,B,L1), hb(B,L1,C,L4) ==>  hb(A,L1,C,L4).

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
inferhb(hb(R1,L1,R2,L2),R3,L3):- hb(R1,L1,R3,L3),hb(R3,L3,R2,L2).
% inferhb(hb(R1,L1,R2,L2),R3,L3):- cb(R1,L1,R3,L3),hb(R3,L3,R2,L2).

looprole(A,T,[],L) :- false.
looprole(A,T,[R|Tail],L):-  % writeln((A,inferhb(T,R,L))),
        (writeln("START"),(A,inferhb(T,R,L)),writeln(inferhb(T,R,L)),writeln("STOP"))
        ; looprole(A,T,Tail,L),false.

looplabel(A,T,R,[]) :- false.
looplabel(A,T,R,[L|Tail]):- looprole(A,T,R,L);looplabel(A,T,R,Tail),false.

infer(A,B,Roles,Labels):-   looplabel(A,B,Roles,Labels),false.

% combinations([R|RTail],[L|LTail]):- hb(R,L,) 

comb1 @ combroles(Role,Labels)   <=> false.
comb2 @ comblabels(Roles,Labels) <=> false.
comb3 @ allevents(Roles,Labels)  <=> false.

combroles(R,[]).
combroles(R,[L|LTail]):- ev(R,L),combroles(R,LTail).

comblabels([],Labels).
comblabels([R|RTail],Labels):- combroles(R,Labels),comblabels(RTail,Labels).

allevents(Roles,Labels):- comblabels(Roles,Labels),!.

allhb @ allhb1(E1,E2) <=> false.
allhb @ allhb2(E1,E2) <=> false.

allhb1((ev(R1,L1)),[]).
allhb1((ev(R1,L1)),[(ev(R2,L2))|Events]):- writeln("HERE"),hb(R1,L1,R2,L2),allhb1(ev(R1,L1),Events).

allhb2([],Events2).
allhb2([(ev(R1,L1))|Events1],Events2):- allhb1(ev(R1,L1),Events2),allhb2(Events1,Events2).

allhb(Events):- allhb2(Events,Events).

        
% POSSIBLE QUERY
% infer(hb(X,1,Z,3),hb(X,1,Y,2),[X,Y,Z],[1,2,3]).

%  #ic@S <_CB #ic@R &
%  A^{i#A} <_HB A^{i#1} &
%  B^{i#B} <_HB B^{i#1} &
%  A^{i#1} <_CB B^{i#1} &
% |- 
%  ic^{S} <_HB A^{i#1} & 
%  ic^{R} <_HB B^{i#1}.

% cb(SC,IC,RC,IC),hb(A,IA,A,I1),hb(B,IB,B,I1),hb(A,I1,B,I1)
% |- hb(S,IC,A,I1), hb(R,IC,B,I1).