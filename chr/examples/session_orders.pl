#!/usr/bin/env swipl
:- module(orders, [event/2,hb/4,cb/4]).
:- use_module(library(chr)).
% :- [orders_predicates].

:- initialization main.

:- chr_constraint event/2,hb/4,cb/4.
:- style_check(-singleton).

asym   @ hb(A,L1,B,L2), hb(B,L2,A,L1) ==> false.
hbhb   @ hb(A,L1,B,L2), hb(B,L2,C,L4) ==> hb(A,L1,C,L4).
cbhb   @ cb(A,L1,B,L1), hb(B,L1,C,L4) ==> hb(A,L1,C,L4).

writeln(T) :- write(T), nl.

checkff :-
   open('ex1.pl',read,Str),
   read_goals(Str,Gl),
   close(Str).

read_goals(Stream,[]):-
   at_end_of_stream(Stream).

read_goals(Stream,[X|L]):-
   \+ at_end_of_stream(Stream),
   read(Stream,Gl),
   Gl.
   % read_houses(Stream,L).

main :-
        ((checkff,writeln(true)) ; (\+(checkff),writeln(false))),
        halt.
