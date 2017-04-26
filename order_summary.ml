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
  type t1
  type base
  val bot :       unit -> t
  val is_bot :    t -> bool
  val string_of : t -> string
  val eq :        t -> t -> bool
  val mk_base :   base -> t
  val mk_or :     t -> t -> t
  val mk_star :   t -> t -> t
  val merge_seq  : t -> t -> t
  val merge_sor  : t -> t -> t
  val merge_star : t -> t -> t
end;;

module BOUNDARY_ELEMENT =
  functor (Base: BOUNDARY_BASE_ELEMENT_TYPE) ->
  struct
    type base = Base.t
    type t = base eform
    type t1 = base bform
    let bot () = BOT
    let is_bot x =
      match x with
      | BOT -> true
      | _   -> false
    let eq e1 e2  = failwith x_tbi
    let string_of e = failwith x_tbi
    let mk_base (base: base) : t = FBase (BBase base)
    let mk_or   (or1:t) (or2:t) : t = BOr (or1,or2)
    let mk_star (star1:t) (star2:t) : t =
      match star1, star2 with
      | FBase f1, FBase f2 ->  FBase (BStar (f1,f2))
      | _, _ -> failwith "BStar only between base elements"
    let merge_seq (f1:t) (f2:t) : t  = if (is_bot f1) then f2 else f1
    let merge_sor (f1:t) (f2:t) : t  = mk_or f1 f2
    let merge_star (f1:t) (f2:t) : t = if (is_bot f1) then f2
      else if (is_bot f2) then f1 else mk_star f1 f2
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
  type t1 = orders
  type base = orders
  let bot () = failwith x_tbi
  let is_bot x = failwith x_tbi
  let eq e1 e2 = failwith x_tbi
  let string_of e1 = failwith x_tbi
  let mk_base (base: base) : t = failwith x_tbi
  let mk_or   (or1:t) (or2:t) : t = failwith x_tbi 
  let mk_star (star1:t) (star2:t) : t = failwith x_tbi 
  let merge_seq (f1:t) (f2:t) : t = failwith x_tbi
  let merge_sor (f1:t) (f2:t) : t = failwith x_tbi
  let merge_star (f1:t) (f2:t) : t = failwith x_tbi
        
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

  val update_elem    : emap -> key -> elem -> emap
  val add_elem_dupl  : emap -> key -> elem -> emap
  val add_elem       : emap -> key -> elem -> emap
  
  val union      : emap -> emap -> emap
  val merge_seq  : emap -> emap -> emap
  val merge_sor  : emap -> emap -> emap
  val merge_star : emap -> emap -> emap 
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
  let find (s : emap) (k: key) : elem  = find_aux s k (Elem.bot ())

  let update_elem (e1:emap) (k:key) (el:elem) : emap =
    List.map (fun (k0,e0) -> if Key.eq k0 k then (k0,el) else (k0,e0)) e1

  (* allow key duplicates *)
  let add_elem_dupl (e1:emap) (k:key) (el:elem) : emap =
    (k,el)::e1
    
  (* if key exists in emap, then replace its corresponding element *)
  let add_elem (e1:emap) (k:key) (el:elem) : emap =
    let update_f =  if (Elem.is_bot (find e1 k)) then add_elem_dupl  else update_elem in
    update_f e1 k el

  (* this merge allows duplicates *)
  let union (e1:emap) (e2:emap) :emap =
    e1 @ e2

  type op = SEQ | SOR | STAR

  (* generic merge emap function *)
  let merge_op op (e1:emap) (e2:emap) :emap =
    let merge_elem op =
      match op with
      | SEQ  -> Elem.merge_seq
      | SOR  -> Elem.merge_sor
      | STAR -> Elem.merge_star in
    List.fold_left (fun map (key,elem) ->
        let elem1 = find e1 key in (* \bot or some element *)
        let elem1 = (merge_elem op) elem1 elem in
        add_elem e1 key elem1) e1 e2 
    
  let merge_seq  (e1:emap) (e2:emap) :emap = merge_op SEQ e1 e2
      
  let merge_sor  (e1:emap) (e2:emap) :emap = merge_op SOR e1 e2
      
  let merge_star (e1:emap) (e2:emap) :emap = merge_op STAR e1 e2

end;;

(* ------------------------------------------------ *)
module Events = BOUNDARY_ELEMENT(BEvent) ;;
module Trans = BOUNDARY_ELEMENT(BTrans) ;;

module RMap = SMap(IRole)(Events) ;;
module CMap = SMap(IChan)(Trans) ;;
module ConstrMap = SMap(UID)(Orders) ;;

(* ------------------------------------------------ *)
(* ------------- summary related stuff ------------ *)
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

let init_summary bborder fborder assum guards = 
  {bborder = bborder ; fborder = fborder ; assumptions = assum ; guards = guards}
  
(* ------------------------------------------------ *)
(* ----- merging functions for prot constructs ---- *)

let merge_set (fborder:RMap.emap * CMap.emap) (bborder:RMap.emap * CMap.emap) : ConstrMap.emap * ConstrMap.emap =
  
  (ConstrMap.mkEmpty (), ConstrMap.mkEmpty ())

(* generic border merge *)
let merge_border (b1:RMap.emap * CMap.emap) (b2:RMap.emap * CMap.emap)
    rmap_merge cmap_merge : RMap.emap * CMap.emap =
  let rmap1, cmap1 = b1 in
  let rmap2, cmap2 = b2 in
  let rmap0 = rmap_merge rmap1 rmap2 in 
  let cmap0 = cmap_merge cmap1 cmap2 in
  (rmap0,cmap0)

(* [;] in paper *)
let merge_seq_border (seq1:RMap.emap * CMap.emap) (seq2:RMap.emap * CMap.emap) : RMap.emap * CMap.emap =
  merge_border seq1 seq2 RMap.merge_seq CMap.merge_seq

(* [\/] in paper *)
let merge_sor_border (b1:RMap.emap * CMap.emap) (b2:RMap.emap * CMap.emap) : RMap.emap * CMap.emap =
  merge_border b1 b2 RMap.merge_sor CMap.merge_sor

(* [*] in paper *)
let merge_star_border (b1:RMap.emap * CMap.emap) (b2:RMap.emap * CMap.emap) : RMap.emap * CMap.emap =
  merge_border b1 b2 RMap.merge_star CMap.merge_star
  
(* f1 in paper *)
let merge_all_seq (seq1:summary) (seq2:summary) : summary =
  let bborder0 = merge_seq_border seq1.bborder seq2.bborder in
  let fborder0 = merge_seq_border seq2.fborder seq1.fborder in
  let assum3, guards3 = merge_set seq1.fborder seq2.bborder in
  let assume0 = ConstrMap.union (ConstrMap.union seq1.assumptions seq2.assumptions) assum3 in
  let guards0 = ConstrMap.union (ConstrMap.union seq1.guards seq2.guards) guards3 in
  init_summary bborder0 fborder0 assume0 guards0

let merge_all_sor (sor1:summary) (sor2:summary) : summary =
  let bborder0 = merge_sor_border sor1.bborder sor2.bborder in
  let fborder0 = merge_sor_border sor2.fborder sor1.fborder in
  let assume0 = ConstrMap.union sor1.assumptions sor2.assumptions in
  let guards0 = ConstrMap.union sor1.guards sor2.guards in
  init_summary bborder0 fborder0 assume0 guards0

let merge_all_star (star1:summary) (star2:summary) : summary =
  let bborder0 = merge_star_border star1.bborder star2.bborder in
  let fborder0 = merge_star_border star2.fborder star1.fborder in
  let assume0 = ConstrMap.union star1.assumptions star2.assumptions in
  let guards0 = ConstrMap.union star1.guards star2.guards in
  init_summary bborder0 fborder0 assume0 guards0


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
   


