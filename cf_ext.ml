 
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
    method add_field_tags dn param = 
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
        if dn="node" then [false;true]
        else [false;true;true]
  end

let data_decl_obj = new data_table

let add_data_tags_to_obj cdata =
  List.iter (fun cd ->
      let dn = cd.Cast.data_name in
      let fields = cd.Cast.data_fields_new in
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
