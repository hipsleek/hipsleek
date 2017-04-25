#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module CP = Cpure
  
type 'a bform = BBase of 'a | BStar of ('a bform) * ('a bform)

and  'a eform = BOT | FBase of 'a bform | BOr of ('a eform) * ('a eform)

and event = {
  role : Session.IProtocol_base.role;
  uid  : suid;
}

and transmission = {
  sender   : Session.IProtocol_base.role;
  receiver : Session.IProtocol_base.role;
  channel  : Session.IProtocol_base.chan;
  uid      : suid;
}

let eq_event (e1:event) (e2:event) : bool =
  (eq_suid e1.uid e2.uid) && (Session.IProtocol_base.eq_role e1.role e2.role)

let eq_transmission (t1:transmission) (t2:transmission) : bool =
  (eq_suid t1.uid t2.uid)
  && (Session.IProtocol_base.eq_role t1.sender t2.sender)
  && (Session.IProtocol_base.eq_role t1.receiver t2.receiver)
  && (Session.IProtocol_base.eq_chan t1.channel t2.channel)


module type KEY_EQ_TYPE =
sig
  type t
  val eq : t -> t -> bool
  val string_of : t -> string   
end;;

module type ELEM_EQ_TYPE =
sig
  include KEY_EQ_TYPE
  val bot : t
  val is_bot : t -> bool
end;;

module IRole =
struct
  type t = Session.IProtocol_base.role
  let eq = Session.IProtocol_base.eq_role
  let string_of = Session.IProtocol_base.string_of_role
end;;

module IChan =
struct
  type t = Session.IProtocol_base.chan
  let eq = Session.IProtocol_base.eq_chan
  let string_of = Session.IProtocol_base.string_of_chan
end;;

module BEvent =
struct
  type t = event eform
  let bot = BOT
  let is_bot x =
    match x with
    | BOT -> true
    | _   -> false
  let eq = failwith x_tbi
  let string_of = failwith x_tbi
end;;

module BTransmission =
struct
  type t = transmission eform
  let bot = BOT
  let is_bot x =
    match x with
    | BOT -> true
    | _   -> false
  let eq = failwith x_tbi
  let string_of = failwith x_tbi
end;;

module SMap
    (Key  : KEY_EQ_TYPE)
    (Elem : ELEM_EQ_TYPE) =
struct
  type key  = Key.t
  type elem = Elem.t
  type emap = (key * elem) list
  type epart = (elem list) list
  type elist = (elem list) 

  let eq = Key.eq 
  let string_of_elem = Elem.string_of
  let string_of_key  = Key.string_of 

  let string_of (e: emap) : string =    
    "emap["^ (pr_lst "\n" (pr_pair string_of_key string_of_elem) e) ^"]"
    
  let mkEmpty : emap = []

  let is_empty (m:emap) = match m with | [] -> true | _ -> false

  let find_aux (s: emap) (k:key) (d:elem) : elem =
    try
      snd(List.find (fun (k0,_) -> eq k0 k) s)
    with
      _ -> d

  (* find element with key k in s *)
  let find (s : emap) (k: key) : elem  = find_aux s k Elem.bot

  end;;

module RMap = SMap(IRole)(BEvent) ;;
module CMap = SMap(IChan)(BTransmission) ;;

let collect prot = prot ;;

(* let collect prot = *)
(*   match prot with *)
(*   | Session.IProtocol.SSeq  seq  -> f1 (collect seq.Session.IProtocol.session_seq_formula_head) *)
(*                      (collect seq.Session.IProtocol.session_seq_formula_tail) *)
(*   | Session.IProtocol.SStar star -> f2 (collect seq.Session.IProtocol.session_star_formula_star1) *)
(*                      (collect seq.Session.IProtocol.session_star_formula_star2) *)
(*   | Session.IProtocol.SOr   sor  -> f3 (collect seq.Session.IProtocol.session_sor_formula_sor1) *)
(*                      (collect seq.Session.IProtocol.session_sor_formula_sor2) *)
(*   | Session.IProtocol.SExists se -> collect se.Session.IProtocol.session_exists_formula_session *)
(*   | Session.IProtocol.SBase (Base tr) ->     *)
(*     let rmap = .. in *)
(*     let cmap = .. in *)
(*     let aset = .. in *)
(*     let gset = .. in *)
(*     ((rmap,cmap),(rmap,cmap),aset,gset) *)
(*   | Session.IProtocol.SEmp -> () *)
