#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module SProt  = Session.IProtocol
module SBProt = Session.IProtocol_base
module SIOrd = Session.IOrders
module OS = Order_summary
module SProj = Session.IProjection
module SBProj = Session.IProjection_base
module STProj = Session.ITPProjection
module SBTProj = Session.ITPProjection_base

type role = SIOrd.role
type chan = SIOrd.chan

module Projection_map = 
struct
  type t = SProj.session 
  type base = SProj.t

  let bot () = SProj.SEmp
  let is_bot x = match x with
    | SProj.SEmp -> true
    | _ -> false
  let eq e1 e2 = failwith x_tbi
  let string_of f = SProj.string_of_session f
  let mk_base (base: base) : t = failwith x_tbi
  let mk_or   (or1:t) (or2:t) : t = failwith x_tbi 
  let mk_star (star1:t) (star2:t) : t = failwith x_tbi 
  let merge_seq (f1:t) (f2:t) : t = failwith x_tbi
  let merge_sor (f1:t) (f2:t) : t = failwith x_tbi
  let merge_star (f1:t) (f2:t) : t = failwith x_tbi
  let mkSingleton (e:base) : t = failwith x_tbi
  let add_elem (old_e:t) (new_e:t) : t  = new_e
end;;

module TProjection_map =
struct
  type t = STProj.session
  type base = STProj.t

  let bot () = STProj.SEmp
  let is_bot x = match x with
    | STProj.SEmp -> true
    | _ -> false
  let eq e1 e2 = failwith x_tbi
  let string_of f = STProj.string_of_session f
  let mk_base (base: base) : t = failwith x_tbi
  let mk_or   (or1:t) (or2:t) : t = failwith x_tbi 
  let mk_star (star1:t) (star2:t) : t = failwith x_tbi 
  let merge_seq (f1:t) (f2:t) : t = failwith x_tbi
  let merge_sor (f1:t) (f2:t) : t = failwith x_tbi
  let merge_star (f1:t) (f2:t) : t = failwith x_tbi
  let mkSingleton (e:base) : t = failwith x_tbi
  let add_elem (old_e:t) (new_e:t) : t  = new_e
end;;

module PrjMap = OS.SMap(OS.IRole)(Projection_map)
module TPrjMap = OS.SMap(OS.IChan)(TProjection_map)

let create_session transmission chan msg_var pos heap_node msg =
  (* makes projection base *)
  let base = SBProj.mk_base (transmission, chan, msg_var, pos) ~node:heap_node msg in
  (* makes projection session *) 
  let session_formula = SProj.SBase (SProj.Base base) in
  session_formula

(* Makes projection per party for assumptions *)
let rec mk_prj_assume pred_orders role =
  match pred_orders with
   | SIOrd.And and_type -> 
       let and_head = and_type.and_assrt1 in
       let and_tail = and_type.and_assrt2 in
       let prj1 = mk_prj_assume and_head role in
       let prj2 = mk_prj_assume and_tail role in
       SIOrd.mk_and prj1 prj2 
   | SIOrd.Or or_type ->
       let or_head = or_type.or_assrt1 in
       let or_tail = or_type.or_assrt2 in
       let prj1 = mk_prj_assume or_head role in
       let prj2 = mk_prj_assume or_tail role in
       SIOrd.mk_or prj1 prj2
   | SIOrd.Event e ->
       if SBProt.eq_role role e.role then
         SIOrd.Event e
       else
         SIOrd.Bot
   | SIOrd.Order order -> SIOrd.Bot
   | _ -> SIOrd.Bot
   
(* Makes projection per party for proof obligations *)
(* Returns a pair of SIOrd.assrt *)
let rec mk_prj_guard pred_orders role =
  match pred_orders with
   | SIOrd.And and_type -> 
       let and_head = and_type.and_assrt1 in
       let and_tail = and_type.and_assrt2 in
       let (prj_assume1, prj_guard1) = mk_prj_guard and_head role in
       let (prj_assume2, prj_guard2) = mk_prj_guard and_tail role in
       (SIOrd.mk_and prj_assume1 prj_assume2, SIOrd.mk_and prj_guard1 prj_guard2)
   | SIOrd.Or or_type ->
       let or_head = or_type.or_assrt1 in
       let or_tail = or_type.or_assrt2 in
       let (prj_assume1, prj_guard1) = mk_prj_guard or_head role in
       let (prj_assume2, prj_guard2) = mk_prj_guard or_tail role in
       (SIOrd.mk_or prj_assume1 prj_assume2, SIOrd.mk_or prj_guard1 prj_guard2)
   | SIOrd.Event e -> (SIOrd.Bot, SIOrd.Bot)
   | SIOrd.Order order ->
     begin
      match order with
      | SIOrd.HBe hbe -> 
          let hbe_role = hbe.hbe_event2.role in
          if (SBProt.eq_role role hbe_role) then
            (SIOrd.Bot, SIOrd.mk_order (SIOrd.HBe hbe))
          else 
            (SIOrd.mk_order (SIOrd.HBe hbe), SIOrd.Bot)
      | _ -> (SIOrd.Bot, SIOrd.Bot)
     end
   | _ -> (SIOrd.Bot, SIOrd.Bot)

(* Removes Bot assrt from session predicate orders *)
(* Examples: 
  * Bot & (A,id_55) & Bot -> (A,id_55)
  * Bot & Bot & Bot & Bot -> Bot *)
let norm_assrt prj =   
  let norm prj = match prj with
  | SProj.SBase sb ->  
    begin          
      match sb with
      | SProj.Predicate p -> 
        (* gets predicate info *)
        let orders = p.session_predicate_orders in
        let pred_kind = p.session_predicate_kind in
        (* removes Bot elem from assumptions and guards orders *)
        begin match pred_kind with
        | Assert Assume
        | Assert Guard ->
          let fixpt = ref true in 
          let rec norm_order assrt = begin match assrt with
            | SIOrd.And typ ->
              let assrt1 = typ.and_assrt1 in
              let assrt2 = typ.and_assrt2 in 
              begin match assrt1, assrt2 with
              | SIOrd.Bot, a 
              | a, SIOrd.Bot -> 
                  let () = fixpt := false in
                  norm_order a
              | a1, a2 -> SIOrd.mk_and (norm_order a1) (norm_order a2) 
              end
            | SIOrd.Or typ ->
              let assrt1 = typ.or_assrt1 in
              let assrt2 = typ.or_assrt2 in
              SIOrd.mk_or (norm_order assrt1) (norm_order assrt2)
            | _ -> assrt end in
          let rec helper norm =
            let norm = norm_order norm in
            if not(!fixpt) then let () = fixpt := true in helper norm
            else norm in
          let norm = helper orders in
          (* updates the predicate with normalized orders *)
          let pred = SProj.update_session_predicate ~orders:norm p in 
          let sbase = SProj.SBase pred in
          Some sbase
        | _ -> None
        end
      | _ -> None             
     end                       
   | _ -> None                 
   in                          
   let fnc = (norm, (nonef, nonef)) in
   let res = SProj.trans_session_formula fnc prj in
   res

let norm_assrt prj =   
  let pr = SProj.string_of_session in 
  Debug.no_1 "SP.norm_assrt" pr pr norm_assrt prj

(* Removes assumptions and guards that have orders only with Bot *)
(* Example: Assume{Bot} -> emp *)
let norm_sess_pred prj =
  let norm prj = match prj with
  | SProj.SBase sb ->
      begin match sb with
      | SProj.Predicate p ->
          let assrt = p.session_predicate_orders in
          let pred_kind = p.session_predicate_kind in
          begin match pred_kind with
          | Assert Assume
          | Assert Guard ->
            begin match assrt with
            | SIOrd.Bot -> Some SProj.SEmp
            | _ -> None
            end
          | _ -> None
          end
      | _ -> None
      end
  | _ -> None
  in
  let fnc = (norm, (nonef, nonef)) in
  let res = SProj.trans_session_formula fnc prj in
  res

let norm_sess_pred prj=
  let pr = SProj.string_of_session in
  Debug.no_1 "SP.norm_sess_pred" pr pr norm_sess_pred prj

(* Projection per party *)
let mk_projection_per_party prot role =
  let rec deconstruct_prot prot = match prot with
    | SProt.SSeq seq -> 
        let head = seq.session_seq_formula_head in
        let tail = seq.session_seq_formula_tail in
        let pos = seq.session_seq_formula_pos in
        let session_head = deconstruct_prot head in
        let session_tail = deconstruct_prot tail in
        SProj.mk_session_seq_formula session_head session_tail pos
    | SProt.SOr sor ->
        let session1 = sor.session_sor_formula_or1 in
        let session2 = sor.session_sor_formula_or2 in
        let pos = sor.session_sor_formula_pos in
        let sess_prj1 = deconstruct_prot session1 in
        let sess_prj2 = deconstruct_prot session2 in
        SProj.mk_session_or_formula sess_prj1 sess_prj2 pos
    | SProt.SStar star ->
        let session1 = star.session_star_formula_star1 in 
        let session2 = star.session_star_formula_star2 in 
        let pos = star.session_star_formula_pos in
        let sess_prj1 = deconstruct_prot session1 in
        let sess_prj2 = deconstruct_prot session2 in
        SProj.mk_session_star_formula sess_prj1 sess_prj2 pos
    | SProt.SBase sb -> 
        begin
          match sb with
          | SProt.Base base ->
            (* gets information nedeed for projection *)
            let pos = SBProt.get_base_pos base in
            let msg_var = SBProt.get_message_var base in
            let msg = SBProt.get_message base in
            let chan =  SBProt.get_chan base in
            let chan_ident = match chan with
              | Some ch -> SBProt.string_of_chan ch
              | None -> "" in
            let sender = SBProt.get_sender base in
            let receiver = SBProt.get_receiver base in
            let heap_node = SBProt.get_session_heap_node base in
            (* creates session_formula based on transmission role *) 
            if (SBProt.eq_role sender role) then 
              let session_formula = create_session Session.TSend chan_ident msg_var pos heap_node msg in
              session_formula
            else if (SBProt.eq_role receiver role) then
              let session_formula = create_session Session.TReceive chan_ident msg_var pos heap_node msg in
              session_formula
            else
              SProj.SEmp
          | SProt.Predicate sp ->
            (* gets information nedeed for projection *)
            let pred_name = sp.session_predicate_name in
            let pred_ho_vars = sp.session_predicate_ho_vars in
            let pred_params = sp.session_predicate_params in
            let pred_pos = sp.session_predicate_pos in
            let pred_orders = sp.session_predicate_orders in
            let pred_kind = sp.session_predicate_kind in
            (* makes projection per Predicate kind *)
            (* only Assert Assume and Assert Guard are taken into consideration *)
            begin match pred_kind with
            | Assert a -> 
              begin
                match a with
                | Assume ->
                    let assrt = mk_prj_assume pred_orders role in
                    SProj.SBase (SProj.mk_session_predicate pred_name pred_ho_vars pred_params ~orders:assrt ~sess_pred_kind:pred_kind pred_pos)
                | Guard -> 
                    let (assrt_assume, assrt_guard) = mk_prj_guard pred_orders role in
                    let pred_assume = SProj.SBase (SProj.mk_session_predicate "Assume" pred_ho_vars pred_params ~orders:assrt_assume ~sess_pred_kind:(Assert Assume) pred_pos) in
                    let pred_guard = SProj.SBase (SProj.mk_session_predicate pred_name pred_ho_vars pred_params ~orders:assrt_guard ~sess_pred_kind:pred_kind pred_pos) in
                    SProj.mk_session_seq_formula pred_assume pred_guard pred_pos
                | _ -> SProj.SEmp
              end
            | _ -> SProj.SEmp 
            end
          | _ -> SProj.SEmp
        end
    | _ -> SProj.SEmp
  in
  let session = deconstruct_prot prot in
  (* removes assrt Bot *)
  let norm_sess = norm_assrt session in
  (* removes assertions and guards that contain orders with only one Bot *)
  let norm_sess = norm_sess_pred norm_sess in
  let norm_sess = SProj.remove_emps norm_sess in
  norm_sess

let mk_projection_per_party prot role =
  let pr1 = SProt.string_of_session in
  let pr2 = Session.IMessage.print_var in
  let pr_out = SProj.string_of_session in
  Debug.no_2 "SP.mk_projection_per_party" pr1 pr2 pr_out (fun _ _ -> mk_projection_per_party prot role) prot role

(* Collects projections into the Map *)
let save_prj_into_map map prj_elem role =
  match PrjMap.is_empty map with
    | true -> PrjMap.init [(role, prj_elem)]
    | false -> PrjMap.add_elem_dupl map role prj_elem

let save_prj_into_map map prj_elem role =
  let pr = PrjMap.string_of in
  Debug.no_1 "SP.save_prj_into_map" pr pr (fun _ -> save_prj_into_map map prj_elem role) map




