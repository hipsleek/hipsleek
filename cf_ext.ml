 
#include "xdebug.cppo"
(*
  Created 21-Feb-2006

  Formula
*)

module DD = Debug
open Globals
open VarGen
open Gen
open Exc.GTable
open Perm
open Label_only
open Label
open Cpure
open Mcpure_D
open Mcpure

module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CVP = CvpermUtils

open Cformula

let process_heap_prop_extn p_tab (* pname vns *) (* mutual-rec *) (* nnn_sv *) hf =
  let f hf = match hf with
    | HTrue | HFalse | HEmp | Hole _ | HRel _ | HVar _ -> Some hf
    | DataNode dl ->
      begin
        let name = dl.h_formula_data_name in
        let ptr = dl.h_formula_data_node in
        let args = dl.h_formula_data_arguments in
        let () = p_tab # proc_data ptr name args in
        Some hf
      end
    | ViewNode vl ->
      begin
        let name = vl.h_formula_view_name in
        let ptr = vl.h_formula_view_node in
        let vs = vl.h_formula_view_arguments in
        let n_hf = 
          try 
            let (new_vn,new_sv) = p_tab # proc_view (Some ptr) name  in
            (ViewNode {vl with h_formula_view_name = new_vn; 
                               h_formula_view_arguments = vs@[new_sv]})
          with _ -> hf
        in Some n_hf
      end
    | _ -> None
  in map_h_formula hf f

class data_table =
  object (self)
    val mutable lst = [] (* (ptr,value) list *)
    method logging s =
      (* let m = "**data_table** " in *)
      (* let () = print_endline_quiet (m^s) in *)
      ()
    method reset =
      self # logging "reset";
      lst <- []
    method add_field_tags dn param =
      let () = self # logging ((add_str "Add tag of" (pr_pair pr_id (pr_list (pr_list pr_id)))) (dn,param)) in
      lst <- (dn,param)::lst
    method find_tags dn =
      try
        snd(List.find (fun (n,_) -> n=dn) lst)
      with _ -> failwith (x_loc^"does not exist :"^dn)
    method get_tag_mask dn (t:string) = 
      try 
        let tags = self # find_tags dn in
        List.map (fun ls -> List.mem t ls) tags
      with _ -> 
        failwith (x_loc^"tag cannot be found")
        (*   if dn="node" then [false;true] *)
        (* else [false;true;true] *)
  end

let data_decl_obj = new data_table

let add_data_tags_to_obj cdata =
  let () = y_tinfo_pp "add_data_tags_to_obj" in
  data_decl_obj # reset;
  List.iter (fun cd ->
      let dn = cd.Cast.data_name in
      let fields = cd.Cast.data_fields in
      let tags = List.map snd fields in
      data_decl_obj # add_field_tags dn tags
    ) cdata
  
let compute_raw_base_case is_prim_v n_un_str =
  (* let is_prim_v = vdef.I.view_is_prim in *)
  let rec f_tr_base f = 
    let mf f h fl pos = if (CF.is_complex_heap h) then (CF.mkFalse fl pos)  else f in
    match f with
    | CF.Base b -> mf f b.CF.formula_base_heap b.CF.formula_base_flow b.CF.formula_base_pos
    | CF.Exists b -> mf f b.CF.formula_exists_heap b.CF.formula_exists_flow b.CF.formula_exists_pos
    | CF.Or b -> CF.mkOr (f_tr_base b.CF.formula_or_f1) (f_tr_base b.CF.formula_or_f2) no_pos in
  let rbc = 
    if is_prim_v then None
    else List.fold_left (fun a (c,l)-> 
        let fc = f_tr_base c in
        if (CF.isAnyConstFalse fc) then a 
        else match a with 
          | Some f1  -> Some (CF.mkOr f1 fc no_pos)
          | None -> Some fc) None n_un_str 
  in rbc

(* type: Excore.EPureI.epure list option -> *)
(*   Excore.EPureI.epure list option -> *)
(*   Excore.EPureI.epure list option -> *)
(*   Cformula.CP.formula -> *)
(*   VarGen.loc -> *)
(*   Excore.EPureI.epure list option * Excore.EPureI.epure list option * *)
(*   Cformula.MCP.mix_formula * Cformula.MCP.mix_formula *)
let compute_baga_invs (* t_v t_pf n_tl *) vbc_i vbc_o vbc_u new_pf pos =
  (* let vbi_i = vdef.I.view_baga_inv in *)
  (* let vbi_o = vdef.I.view_baga_over_inv in *)
  (* let vbi_u = vdef.I.view_baga_under_inv in *)
  (* let trans_var = t_v in *)
  (* let trans_pure_formula = t_pf in *)
  (* let vbc_i = conv_baga_inv vbi_i (\* vdef.I.view_baga_inv *\) in *)
  (* let vbc_o = conv_baga_inv vbi_o in *)
  (* let vbc_u = conv_baga_inv vbi_u in *)
  (* let conv_baga_inv baga_inv = *)
  (*   match baga_inv with *)
  (*   | None -> None *)
  (*   | Some lst -> *)
  (*     let rr = List.map (fun (idl,pf) -> *)
  (*         let svl = List.map (fun c -> x_add trans_var (c,Unprimed) n_tl pos) idl in *)
  (*         let cpf = x_add trans_pure_formula pf n_tl in *)
  (*         let cpf = x_add Cpure.arith_simplify 1 cpf in *)
  (*         (svl,cpf) *)
  (*       ) lst in *)
  (*     Some rr *)
  (* in *)
  let vbc_o = match vbc_o with
    | None -> Some (Excore.EPureI.mk_epure new_pf) 
    | Some _ -> vbc_o in
  let memo_pf_P = MCP.memoise_add_pure_P (MCP.mkMTrue pos) new_pf in
  let memo_pf_N = MCP.memoise_add_pure_N (MCP.mkMTrue pos) new_pf in
  let unfold_once baga =
    match baga with
    | None -> None
    | Some lst ->
      if List.length lst == 1 then
        Some lst (* unfold once *)
      else baga in
  let (vboi,vbui,user_inv,user_x_inv) = match vbc_i with
    | Some ef ->
      let new_f = Excore.EPureI.ef_conv_disj ef in
      let new_mix_f = x_add_1 Mcpure.mix_of_pure new_f in
      (vbc_i,vbc_i,new_mix_f,new_mix_f)
    | _ -> (vbc_o (* vdef.I.view_baga_over_inv *),
            vbc_u (* conv_baga_inv vbi_u *) (* vdef.I.view_baga_under_inv *),memo_pf_N,memo_pf_P) in
  let vboi = match vboi with
    | None ->
      begin
        x_dinfo_hp (add_str "pure to_be added" Cprinter.string_of_pure_formula) new_pf no_pos;
        (Some [([],new_pf)])
        (* Debug.ninfo_hprint (add_str ("baga inv("^vn^")") (fun x -> x)) "None" no_pos *)
      end
    | Some vbi -> vboi
    (* x_dinfo_hp (add_str ("baga over inv("^vn^")") (Cprinter.string_of_ef_pure_disj)) vbi no_pos  *)
  in (vboi,vbui,user_inv,user_x_inv)

(* type: Excore.EPureI.epure list option -> *)
(*   Excore.EPureI.epure list option -> *)
(*   Excore.EPureI.epure list option -> *)
(*   Cformula.CP.formula -> *)
(*   VarGen.loc -> *)
(*   Excore.EPureI.epure list option * Excore.EPureI.epure list option * *)
(*   Cformula.MCP.mix_formula * Cformula.MCP.mix_formula *)
let compute_baga_invs (* t_v t_pf n_tl *) vbc_i vbc_o vbc_u new_pf pos =
  let pr = pr_option (fun x -> Excore.EPureI.string_of_disj x) in
  let pr1 = pr_triple pr pr pr in
  let pr2 = !CP.print_formula in
  let pr2a f = pr2 (MCP.pure_of_mix f) in
  let pr3 = pr_quad pr pr pr2a pr2a in
  Debug.no_2 "compute_baga_invs" pr1 pr2 pr3 (fun _ _ -> compute_baga_invs vbc_i vbc_o vbc_u new_pf pos) (vbc_i,vbc_o,vbc_u) new_pf


