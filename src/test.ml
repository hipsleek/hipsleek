#include "xdebug.cppo"
open VarGen
(*
 created 21-Feb-2006

  Formula
*)
open Globals

module Err = Error
module CP = Cpure

type ('a,'b,'c) f =  ('a list * 'b list * 'c )

(*
let r ((q1,q2,q3):f (int,int,bool)):f = (q1,[],q3)
*)

type 'a eq = {eq: 'a ->'a -> 'a; neq: 'a ->'a -> 'a}

type 'a numb = {add: 'a ->'a -> 'a; shw: 'a -> string}

let numb_i = {add =(+); shw = string_of_int}

let numb_l numb_e = {add = List.map2 numb_e.add;
                     shw = fun a ->
                       "[" ^ List.fold_right
                         (fun e z ->" " ^ numb_e.shw e ^ z) a "]" };;
(*
let summ numb (h::t) = List.fold_left numb.add h t
*)

let f ~x ~y = x - y;;

let bump ?(step=1) x = x + step


let g x = x

