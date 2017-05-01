#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module CP = Cpure
module SProt  = Session.IProtocol
module SBProt = Session.IProtocol_base

type role = Orders.role
type chan = Orders.chan
              
(* elements of the boundaries *)
type 'a bform = BBase of 'a | BStar of ('a bform) * ('a bform)
and  'a eform = BOT | FBase of 'a bform | BOr of ('a eform) * ('a eform)

(* boundary base element *)
type event = Orders.event

(* boundary base element *)
and transmission = Orders.transmission

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
  type a = role * suid * chan
           
  let make ((role,uid,chan) : a) : t = {role = role; uid = uid; channel = chan }
                                         
  let eq (e1:t) (e2:t) : bool =
    (eq_suid e1.uid e2.uid) && (SBProt.eq_role e1.role e2.role)

  let string_of (e:t) : string = (SBProt.string_of_role e.role) ^ "^" ^(string_of_suid e.uid)

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
  val add_elem   : t ->t -> t
end;;

module BOUNDARY_ELEMENT =
  functor (Base: BOUNDARY_BASE_ELEMENT_TYPE) ->
  struct
    type base = Base.t
    type t = base eform
    let bot () = BOT
    let is_bot x =
      match x with
      | BOT -> true
      | _   -> false
    let eq e1 e2  = failwith x_tbi
    let rec string_of e = match e with
      | BOT -> "BOT"
      | FBase (BBase bs) -> Base.string_of bs
      | FBase (BStar (bs1,bs2)) -> (string_of (FBase bs1)) ^ "*" ^ (string_of (FBase bs2))
      | BOr (bs1,bs2) -> (string_of bs1) ^ "*" ^ (string_of bs2)
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
    let add_elem (old_e:t)(new_e:t) :t  = new_e
  end;;

module Orders_list  =
struct
  type t = Orders.assrt list
  type base = Orders.assrt

  let bot () = []
  let is_bot x = List.length x == 0
  let eq e1 e2 = failwith x_tbi
  let string_of e1 = (pr_list (Orders.string_of_assrt)) e1
  let mk_base (base: base) : t = failwith x_tbi
  let mk_or   (or1:t) (or2:t) : t = failwith x_tbi 
  let mk_star (star1:t) (star2:t) : t = failwith x_tbi 
  let merge_seq (f1:t) (f2:t) : t = failwith x_tbi
  let merge_sor (f1:t) (f2:t) : t = failwith x_tbi
  let merge_star (f1:t) (f2:t) : t = failwith x_tbi
  let mkSingleton (e:base) : t = [e]
  let add_elem (old_e:t) (new_e:t) :t  = old_e@new_e    
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
  type klist

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
  val get_keys : emap -> klist

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
  type klist = (key list) 

  let eq = Key.eq 
  let string_of_elem = Elem.string_of
  let string_of_key  = Key.string_of 

  let string_of (e: emap) : string =    
    "["^ (pr_lst "\n" (pr_pair string_of_key string_of_elem) e) ^"]"
    
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

  let remove_duplicate_keys (keys:klist) : klist =
    let keys = List.fold_left (fun acc key ->
        if List.exists (eq key) acc then acc
        else (key::acc)) [] keys in
    keys

  (* each key is returned only once *)
  let get_keys (s : emap) : klist =
    let all_keys = List.map fst s in
    remove_duplicate_keys all_keys

  (* each key is returned only once *)
  let union_keys (e1:klist) (e2:klist) : klist =
    remove_duplicate_keys (e1@e2)

  let update_elem (e1:emap) (k:key) (el:elem) : emap =
    List.map (fun (k0,e0) -> if Key.eq k0 k then (k0, Elem.add_elem e0 el) else (k0,e0)) e1

  (* allow key duplicates *)
  let add_elem_dupl (e1:emap) (k:key) (el:elem) : emap =
    (k,el)::e1
    
  (* if key exists in emap, then replace its corresponding element *)
  let add_elem (e1:emap) (k:key) (el:elem) : emap =
    let update_f =  if (Elem.is_bot (find e1 k)) then add_elem_dupl else update_elem in
    update_f e1 k el

  (* this merge allows duplicates *)
  let union_dupl (e1:emap) (e2:emap) : emap =
    e1 @ e2

  (* TODO Andreea : debug below add/update_elem?*)
  (* this merge assumes e1 and e2 have no key duplicates *)
  let union (e1:emap) (e2:emap) : emap =
    List.fold_left (fun acc (key,elem) -> add_elem acc key elem) e1 e2

  let union (e1:emap) (e2:emap) : emap =
    let pr = string_of in
    Debug.no_2 "union" pr pr pr union e1 e2 
      
  (* this merge assumes e1 and e2 have no key duplicates *)
  let flatten (e0:emap list) : emap =    
    List.fold_left (fun acc e1 -> union acc e1) (mkEmpty ()) e0

  let flatten (e0:emap list) : emap =
    let pr = string_of in
    Debug.no_1 "flatten" (pr_list pr) pr flatten e0
  
  type op = SEQ | SOR | STAR

  (* generic merge emap function *)
  let merge_op op (e1:emap) (e2:emap) : emap =
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
module OL = Orders_list 
module Events = BOUNDARY_ELEMENT(BEvent) ;;
module Trans = BOUNDARY_ELEMENT(BTrans) ;;

module RMap = SMap(IRole)(Events) ;;
module CMap = SMap(IChan)(Trans) ;;
module ConstrMap = SMap(UID)(OL) ;;

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

let string_of_border = pr_pair (add_str "RMap:" RMap.string_of) (add_str "CMap:" CMap.string_of)
  
  
(* ------------------------------------------------ *)
(* ----- merging functions for prot constructs ---- *)

module type ORDERS_TYPE =
sig
  type t
  val mk_hb : t -> t -> Orders.assrt
  val get_uid : t -> suid
end;;

module Orders_hbe =
struct
  type t = event
  let mk_hb = Orders.mk_hbe
  let get_uid (e:t) = e.uid
end;;

module Orders_hbt =
struct
  type t = transmission
  let mk_hb = Orders.mk_hbt
  let get_uid (e:t) = e.uid
end;;


module Merger
    (Ord  : ORDERS_TYPE) =
struct
  type t = Ord.t eform

  let rec merge (e1:t) (e2:t) : ConstrMap.emap =
    match e1,e2 with
    | FBase (BBase e1) , FBase (BBase e2) ->
      let elem = OL.mkSingleton (Ord.mk_hb e1 e2) in (* hbe hbi  *)
      let key  = Ord.get_uid e2 in
      ConstrMap.init [(key, elem)]
    | FBase (BStar (s1,s2)) , _ ->
      let new_e1 = merge (FBase s1) e2 in
      let new_e2 = merge (FBase s2) e2 in
      ConstrMap.union new_e1 new_e2       (* TODO: upgrade to no duplicates *)
    | _, FBase (BStar (s1,s2)) ->
      let new_e1 = merge e1 (FBase s1) in
      let new_e2 = merge e1 (FBase s2) in
      ConstrMap.union new_e1 new_e2       (* TODO: upgrade to no duplicates *)
    | BOr (s1,s2) , _ ->
      let new_e1 = merge s1 e2 in
      let new_e2 = merge s2 e2 in
      ConstrMap.union new_e1 new_e2       (* TODO: upgrade to no duplicates *)
    | _, BOr (s1,s2) ->
      let new_e1 = merge e1 s1 in
      let new_e2 = merge e1 s2 in
      ConstrMap.union new_e1 new_e2       (* TODO: upgrade to no duplicates *)
    | BOT, _
    | _, BOT -> ConstrMap.mkEmpty ()
end;;

module RMerger = Merger(Orders_hbe)
module CMerger = Merger(Orders_hbt)

let merge_set (b1:RMap.emap * CMap.emap) (b2:RMap.emap * CMap.emap) : ConstrMap.emap * ConstrMap.emap =
  let rmap1, cmap1 = b1 in
  let rmap2, cmap2 = b2 in
  let keys = RMap.union_keys (RMap.get_keys rmap1) (RMap.get_keys rmap2) in
  let () = y_ninfo_hp (add_str "keys" (pr_list IRole.string_of)) keys in
  let assumpt = List.map (fun key -> RMerger.merge (RMap.find rmap1 key) (RMap.find rmap2 key) )  keys in
  let assumpt = x_add_1 ConstrMap.flatten assumpt in
  let keys = CMap.union_keys (CMap.get_keys cmap1) (CMap.get_keys cmap2) in
  let guards = List.map (fun key -> CMerger.merge (CMap.find cmap1 key) (CMap.find cmap2 key) )  keys in
  let guards = x_add_1 ConstrMap.flatten guards in
  (* flatten guards and assumptions  *)
  (assumpt, guards)

(* generic border merge *)
let merge_border (b1:RMap.emap * CMap.emap) (b2:RMap.emap * CMap.emap)
    rmap_merge cmap_merge : RMap.emap * CMap.emap =
  let rmap1, cmap1 = b1 in
  let rmap2, cmap2 = b2 in
  let rmap0 = rmap_merge rmap1 rmap2 in 
  let cmap0 = cmap_merge cmap1 cmap2 in
  (rmap0,cmap0)

let merge_border (b1:RMap.emap * CMap.emap) (b2:RMap.emap * CMap.emap)
    rmap_merge cmap_merge : RMap.emap * CMap.emap =
  let pr = string_of_border in
  Debug.no_2 "merge_border" pr pr pr (fun _ _ -> merge_border b1 b2 rmap_merge cmap_merge) b1 b2

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
  let assume0 = x_add_1 ConstrMap.flatten [seq1.assumptions; seq2.assumptions; assum3] in
  let guards0 = x_add_1 ConstrMap.flatten [seq1.guards; seq2.guards; guards3] in
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
    let fail str = failwith str in
    let chan     =
      match tr.SBProt.protocol_base_formula_chan with
      | None -> let () = y_binfo_pp "chan is none"  in failwith "expecting a specified channel"
      | Some chan -> chan in
      (* map_opt_def (fail "expecting a specified channel" ) *)
      (*   idf tr.SBProt.protocol_base_formula_chan in *)
    let event1   = BEvent.make (sender,suid,chan) in
    let event2   = BEvent.make (receiver,suid,chan) in
    let trans    = BTrans.make (sender,receiver,chan,suid) in
    (* INIT MAPS  *)
    let rmap     = RMap.init [(sender, Events.mk_base event1) ; (receiver, Events.mk_base event2)] in
    let cmap     = CMap.init [(chan, Trans.mk_base trans)] in
    let assum    = ConstrMap.init [(suid,OL.mkSingleton (Orders.Transm trans))] in
    let guards   = ConstrMap.mkEmpty () in
    {bborder = (rmap,cmap) ; fborder = (rmap,cmap) ; assumptions = assum ; guards = guards}
  | SProt.SEmp 
  | _ -> mk_empty_summary ()

let collect prot = 
  let res = collect prot in
  (res.assumptions, res.guards)

let collect prot =
  let pr_out = pr_pair (add_str "\nAssumptions:" ConstrMap.string_of) (add_str "\nGuards:" ConstrMap.string_of) in
  Debug.no_1 "OS.collect" pr_none pr_out collect prot

let insert_orders prot =
  let amap,gmap = collect prot in
  let () = y_binfo_hp (pr_pair (add_str "Assumptions:" ConstrMap.string_of) (add_str "\nGuards:" ConstrMap.string_of) ) (amap,gmap) in
  (* 
     prot <- add assumptions + guards
 *)
  prot

let insert_orders prot =
  let pr = Session.IProtocol.string_of_session in
  Debug.no_1 "OS.insert_orders" pr pr insert_orders prot
