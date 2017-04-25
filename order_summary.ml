#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module CP = Cpure
module SProt  = Session.IProtocol
module SBProt = Session.IProtocol_base

type role = SBProt.role
type chan = SBProt.chan
              
(* elements of the boundaries *)
type 'a bform = BBase of 'a | BStar of ('a bform) * ('a bform)
and  'a eform = BOT | FBase of 'a bform | BOr of ('a eform) * ('a eform)

(* boundary base element *)
and event = {
  role : role;
  uid  : suid;
}

(* boundary base element *)
and transmission = {
  sender   : role;
  receiver : role;
  channel  : chan;
  uid      : suid;
}

(* ------------------------------ *)
(* --- boundary base elements --- *)
module type BOUNDARY_BASE_ELEMENT_TYPE =
sig
  type t
  type a

  val make : a -> t
  val eq : t -> t -> bool
  val string_of : t -> string
end;;

module BEvent =
struct
  type t = event
  type a = role * suid
           
  let make ((role,uid) : a) : t = {role = role; uid = uid}
                                         
  let eq (e1:t) (e2:t) : bool =
    (eq_suid e1.uid e2.uid) && (SBProt.eq_role e1.role e2.role)

  let string_of (e:t) : string = (SBProt.string_of_role e.role) ^ (string_of_suid e.uid)
    
end;;

module BTrans =
struct
  type t = transmission
  type a = role * role * chan * suid
           
  let make ((sender,receiver,chan,uid) :a) : t =
    {sender = sender; receiver = receiver; channel = chan; uid = uid}
    
  let eq (t1:t) (t2:t) : bool =
    (eq_suid t1.uid t2.uid)
    && (SBProt.eq_role t1.sender t2.sender)
    && (SBProt.eq_role t1.receiver t2.receiver)
    && (SBProt.eq_chan t1.channel t2.channel)
       
  let string_of (e:t) : string =
    (SBProt.string_of_role e.sender) ^ "-" ^ (string_of_suid e.uid) ^ "->" ^ (SBProt.string_of_role e.receiver)
    
end;;

(* ------------------------------ *)
(* ------ boundary elements ----- *)

module type BOUNDARY_ELEMENT_TYPE =
sig
  (* include BOUNDARY_BASE_ELEMENT_TYPE *)
  type t
  type base
  val bot :       t
  val is_bot :    t -> bool
  val string_of : t -> string
  val eq :        t -> t -> bool
  val mk_base :   base -> t    
end;;

module BOUNDARY_ELEMENT =
  functor (Base: BOUNDARY_BASE_ELEMENT_TYPE) ->
  struct
    type base = Base.t
    type t = base eform
    let bot = BOT
    let is_bot x =
      match x with
      | BOT -> true
      | _   -> false
    let eq = failwith x_tbi
    let string_of = failwith x_tbi
    let mk_base (base: base) : t = FBase (BBase base)
  end;;

(* order relations - to be collected after analyzing the protocol *)
module Orders =
struct
  type orders  = HBe of event * event
               | HBt of transmission * transmission
               | CBe of event * event
  type assrt   = Event of event
               | NEvent of event
               | Transm of transmission
               | Order of orders
               | And of assrt * assrt
               | Or of assrt * assrt
               | Impl of event * assrt
  type t = assrt
  type base = orders
  let bot = failwith x_tbi
  let is_bot x = failwith x_tbi
  let eq = failwith x_tbi
  let string_of = failwith x_tbi
  let mk_base (base: base) : t = failwith x_tbi

end;;

(* ------------------------------------------------ *)
(* singnature of the keys for the backtier/frontier *)
module type KEY_EQ_TYPE =
sig
  type t
  val eq : t -> t -> bool
  val string_of : t -> string   
end;;

(* key for RMap *)
module IRole =
struct
  type t = role
  let eq = SBProt.eq_role
  let string_of = SBProt.string_of_role
end;;

(* key for CMap *)
module IChan =
struct
  type t = chan
  let eq = SBProt.eq_chan
  let string_of = SBProt.string_of_chan
end;;

(* key for CMap *)
module UID =
struct
  type t = suid
  let eq = eq_suid
  let string_of = string_of_suid
end;;

(* ------------------------------------------------ *)
module type SMap_type =
sig

  type key
  type elem
  type emap
  type epart
  type elist

  val eq: key -> key -> bool

  val string_of_elem : elem -> string
  val string_of_key  : key -> string

  val string_of:  emap -> string
    
  val mkEmpty : emap
  val is_empty :emap -> bool

  val mkSingleton : key -> elem -> emap
  val init : (key * elem) list -> emap
    
  val add : emap-> key -> elem -> emap
  val find : emap -> key -> elem

end;;

module SMap
    (Key  : KEY_EQ_TYPE)
    (Elem : BOUNDARY_ELEMENT_TYPE) =
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
    
  let mkEmpty () : emap = []
  let is_empty (m:emap) = match m with | [] -> true | _ -> false

  let mkSingleton (key:key) (elem:elem) : emap = [(key,elem)]
  let init lst : emap = lst

  let find_aux (s: emap) (k:key) (d:elem) : elem =
    try
      snd(List.find (fun (k0,_) -> eq k0 k) s)
    with
      _ -> d

  (* find element with key k in s *)
  let find (s : emap) (k: key) : elem  = find_aux s k Elem.bot

end;;

(* ------------------------------------------------ *)
module Events = BOUNDARY_ELEMENT(BEvent) ;;
module Trans = BOUNDARY_ELEMENT(BTrans) ;;

module RMap = SMap(IRole)(Events) ;;
module CMap = SMap(IChan)(Trans) ;;
module ConstrMap = SMap(UID)(Orders) ;;

(* ------------------------------------------------ *)
type summary = {
  bborder : RMap.emap * CMap.emap;
  fborder : RMap.emap * CMap.emap;
  assumptions: ConstrMap.emap;
  guards     : ConstrMap.emap;
}

let mk_empty_summary () =
  let rmap     = RMap.mkEmpty () in
  let cmap     = CMap.mkEmpty () in
  let assum    = ConstrMap.mkEmpty () in
  let guards   = ConstrMap.mkEmpty () in
  {bborder = (rmap,cmap) ; fborder = (rmap,cmap) ; assumptions = assum ; guards = guards}

(* ------------------------------------------------ *)
(* ----- merging functions for prot constructs ---- *)
  
let merge_all_seq seq1 seq2 : summary = seq1

let merge_all_sor sor1 sor2 : summary = sor1

let merge_all_star star1 star2 : summary = star1 

(* ------------------------------------------------ *)
(* Collects order assumptions and proof obligations.*)
(* The retuned result is a summary of the form:     *)
(* BackBorder x FrontBorder x Assumptions x Guards  *)
(*                                                  *)
(* where                                            *)
(*                                                  *)
(* Border: RMap x CMap                              *)
(* Assumptions : ConstrMap                          *)
(* Guards : ConstrMap                               *)
(* RMap :      role -> event                        *)
(* CMap :      chan -> transm                       *)
(* ConstrMap : uid  -> order                        *)

let rec collect prot =
  match prot with
  | SProt.SSeq  seq  -> merge_all_seq (collect seq.SProt.session_seq_formula_head)
                     (collect seq.SProt.session_seq_formula_tail)
  | SProt.SStar star -> merge_all_star (collect star.SProt.session_star_formula_star1)
                     (collect star.SProt.session_star_formula_star2)
  | SProt.SOr   sor  -> merge_all_sor (collect sor.SProt.session_sor_formula_or1)
                     (collect sor.SProt.session_sor_formula_or2)
  | SProt.SExists se -> collect se.SProt.session_exists_formula_session
  | SProt.SBase (Base tr) ->
    let sender   = tr.SBProt.protocol_base_formula_sender in
    let receiver = tr.SBProt.protocol_base_formula_receiver in
    let suid     = tr.SBProt.protocol_base_formula_uid in
    let chan     = map_opt_def (failwith "expecting a specified channel" )
        idf tr.SBProt.protocol_base_formula_chan in
    let event1   = BEvent.make (sender,suid) in
    let event2   = BEvent.make (receiver,suid) in
    let trans    = BTrans.make (sender,receiver,chan,suid) in
    (* INIT MAPS  *)
    let rmap     = RMap.init [(sender, Events.mk_base event1) ; (receiver, Events.mk_base event2)] in
    let cmap     = CMap.init [(chan, Trans.mk_base trans)] in
    let assum    = ConstrMap.init [(suid,Orders.Transm trans)] in
    let guards   = ConstrMap.mkEmpty () in
    {bborder = (rmap,cmap) ; fborder = (rmap,cmap) ; assumptions = assum ; guards = guards}
  | SProt.SEmp 
  | _ -> mk_empty_summary ()
   


