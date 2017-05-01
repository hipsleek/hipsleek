#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module F = Iformula
  
type role = Globals.ident * VarGen.primed
type chan = Globals.ident * VarGen.primed
                              
(* boundary base element *)
type event = {
  role   : role;
  uid    : suid;
  channel: chan;
}

(* boundary base element *)
and transmission = {
  sender   : role;
  receiver : role;
  channel  : chan;
  uid      : suid;
}
let string_of_role = F.string_of_spec_var
let string_of_chan = F.string_of_spec_var
let string_of_event e = (string_of_role e.role) ^ "^" ^(string_of_suid e.uid)
let string_of_transmission e = (string_of_role e.sender) ^ "-" ^ (string_of_suid e.uid) ^ "->" ^ (string_of_role e.receiver)
                                                            
(* order relations - to be collected after analyzing the protocol *)
type orders  = HBe of (* hbe_type *) event * event
             | HBt of transmission * transmission
             | CBe of event * event
and assrt   = Event of event
             | NEvent of event
             | Transm of transmission
             | Order of orders
             | And of assrt * assrt
             | Or of assrt * assrt
             | Impl of event * assrt

and hbe_type = {
  hbe_event1 : event;
  hbe_event2 : event;
}

let string_of_assrt e1 =
  let rec helper e1 = 
    match e1 with
    | Event e  -> string_of_event e
    | NEvent e -> "not("^ (string_of_event e) ^ ")"
    | Transm t -> string_of_transmission t
    | Order (HBe (e1,e2)) -> (string_of_event e1) ^ " <_HB " ^ (string_of_event e2)
    | Order (HBt (e1,e2)) -> (string_of_transmission e1) ^ " <_HB " ^ (string_of_transmission e2)
    | Order (CBe (e1,e2)) -> (string_of_event e1) ^ " <_CB " ^ (string_of_event e2)
    | And (a1,a2) -> (helper a1) ^ "&&" ^ (helper a2)
    | Or  (a1,a2) -> (helper a1) ^ "||" ^ (helper a2)
    | Impl (e,a) -> (string_of_event e) ^ "=>" ^ (helper a)
  in helper e1
    
let mk_hbe e1 e2 = Order (HBe (e1,e2))
let mk_hbt e1 e2 = Order (HBt (e1,e2))



