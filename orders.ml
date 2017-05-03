#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module type GORDERS_TYPE = 
sig
  type role
  type chan
  
  type event
  type transmission

  val string_of_role : role -> string
  val string_of_chan : chan -> string
  val string_of_event : event -> string
  val string_of_transmission : transmission -> string

  type orders
  type assrt

  val string_of : assrt -> string 

  val mk_hbe : event ->  event -> assrt
  val mk_hbt : transmission -> transmission -> assrt
  val mk_cbe : event -> event -> assrt 

  val mk_and : assrt -> assrt -> assrt 

  val mk_event : role -> suid -> chan -> event
  val mk_assrt_event : role -> suid -> chan -> assrt
  
  val mk_transmission : role -> role -> suid -> chan -> transmission
  val mk_assrt_transmission : role -> role -> suid -> chan -> assrt

  val get_NoAssrt : assrt
end;;

module type VAR_TYPE =
sig
  type t
  val string_of : t -> string
end;;

(* generic orders, where role and chan are polymorphic *)
module GOrders
    (Var : VAR_TYPE) =
struct
  (* boundary base element *)
  type role = Var.t
  type chan = Var.t
                                
  type event = {
    role   : role;
    uid    : suid;
    channel: chan;
  }

  (* boundary base element *)
  and transmission = {
    sender   : role;
    receiver : role;
    uid      : suid;
    channel  : chan;
  }
  
  let string_of_role = Var.string_of
  let string_of_chan = Var.string_of
  let string_of_event e = (string_of_role e.role) ^ "," ^(string_of_suid e.uid)
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
              | NoAssrt

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

  let string_of e1 =
    let rec helper e1 = 
      match e1 with
      | Event e  -> "(" ^ string_of_event e ^ ")"
      | NEvent e -> "not("^ (string_of_event e) ^ ")"
      | Transm t -> string_of_transmission t
      | Order (HBe e) -> "(" ^ (string_of_event e.hbe_event1) ^ " <_HB " ^ (string_of_event e.hbe_event2) ^ ")"
      | Order (HBt t) -> "(" ^(string_of_transmission t.hbt_transmission1) ^ " <_HB " ^ (string_of_transmission t.hbt_transmission2) ^ ")"
      | Order (CBe e) -> "(" ^ (string_of_event e.cbe_event1) ^ " <_CB " ^ (string_of_event e.cbe_event2) ^ ")"
      | And a -> (helper a.and_assrt1) ^ " & " ^ (helper a.and_assrt2)
      | Or  a -> (helper a.or_assrt1) ^ " or " ^ (helper a.or_assrt2)
      | Impl a -> (string_of_event a.impl_event) ^ "=>" ^ (helper a.impl_assrt)
      | NoAssrt -> ""
    in helper e1

  let mk_hbe e1 e2 = Order (HBe {hbe_event1 = e1; hbe_event2 = e2})
  let mk_hbt e1 e2 = Order (HBt {hbt_transmission1 = e1; hbt_transmission2 = e2})
  let mk_cbe e1 e2 = Order (CBe {cbe_event1 = e1; cbe_event2 = e2})

  let mk_and assrt1 assrt2 = And {and_assrt1 = assrt1; and_assrt2 = assrt2}
  
  let mk_event (r:role) (id:suid) (chan:chan) : event = {role = r; uid = id; channel = chan}
  let mk_assrt_event (r:role) (id:suid) (chan:chan) : assrt = Event (mk_event r id chan)

  let mk_transmission (sender:role) (receiver:role) (id:suid) (chan:chan) : transmission = {sender = sender; receiver = receiver; uid = id; channel = chan}
  let mk_assrt_transmission (sender:role) (receiver:role) (id:suid) (chan:chan) : assrt = Transm {sender = sender; receiver = receiver; uid = id; channel = chan}
  
  let get_NoAssrt = NoAssrt
end ;;

