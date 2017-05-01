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
type orders  = HBe of hbe_type
             | HBt of hbt_type
             | CBe of cbe_type
and assrt   = Event of event
             | NEvent of event
             | Transm of transmission
             | Order of orders
             | And of and_type
             | Or of or_type
             | Impl of impl_type

and hbe_type = {
  hbe_event1 : event;
  hbe_event2 : event;
}
and hbt_type = {
  hbt_transmission1 : transmission;
  hbt_transmission2 : transmission;
}
and cbe_type = {
  cbe_event1 : event;
  cbe_event2 : event;
}
and and_type = {
  and_assrt1 :  assrt;
  and_assrt2 :  assrt;
}
and or_type = {
  or_assrt1 :  assrt;
  or_assrt2 :  assrt;
}
and impl_type = {
  impl_event :  event;
  impl_assrt :  assrt;
}

let string_of_assrt e1 =
  let rec helper e1 = 
    match e1 with
    | Event e  -> string_of_event e
    | NEvent e -> "not("^ (string_of_event e) ^ ")"
    | Transm t -> string_of_transmission t
    | Order (HBe e) -> (string_of_event e.hbe_event1) ^ " <_HB " ^ (string_of_event e.hbe_event2)
    | Order (HBt t) -> (string_of_transmission t.hbt_transmission1) ^ " <_HB " ^ (string_of_transmission t.hbt_transmission2)
    | Order (CBe e) -> (string_of_event e.cbe_event1) ^ " <_CB " ^ (string_of_event e.cbe_event2)
    | And a -> (helper a.and_assrt1) ^ "&&" ^ (helper a.and_assrt2)
    | Or  a -> (helper a.or_assrt1) ^ "||" ^ (helper a.or_assrt2)
    | Impl a -> (string_of_event a.impl_event) ^ "=>" ^ (helper a.impl_assrt)
  in helper e1
    
let mk_hbe e1 e2 = Order (HBe {hbe_event1 = e1; hbe_event2 = e2})
let mk_hbt e1 e2 = Order (HBt {hbt_transmission1 = e1; hbt_transmission2 = e2})



