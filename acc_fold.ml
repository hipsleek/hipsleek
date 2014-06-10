open Globals
open Gen.Basic


module C = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher

module LO = Label_only.LOne


(* 
 * split maximum chain of a h_formula
 *   - return a list of (possible heap chain * the rest of h_formula)
 *)
(* TRUNG TODO: implement the below function  *)
(* and split_heap_chain (hf: h_formula) *)
(*     : (h_formula * h_formula) list = *)



(* let find_begin_end_point_of_heap_chain (hf: CF.h_formula) (aux_pf: MCP.mix_formula) *)
(*     : (CP.spec_var * CP.spec_var) =                                                 *)
      

(* formula of heap chain, entry point, exit point *) 
type heap_chain = CF.h_formula * CP.spec_var * CP.spec_var

(* (*                                                                            *)
(*  * each heap chain is a tuple of (h_formula, begin point, end point of chain) *)
(*  * return a merged heap formula if chain1 and chain2 are consecutive          *)
(*  * otherwise, return None                                                     *)
(*  *)                                                                           *)
(* let merge_heap_chains (chain1: heap_chain) (chain2: heap_chain)               *)
(*     (aux_info: MCP.mix_formula) pos                                           *)
(*     : heap_chain option =                                                     *)
(*   let (hf1, start1, end1) = chain1 in                                         *)
(*   let (hf2, start2, end2) = chain2 in                                         *)
(*   let aux_pf = MCP.pure_of_mix aux_info in                                    *)
(*   let chain1_cond = CP.mkEqExp end1 start2 no_pos in                          *)
(*   let chain2_cond = CP.mkEqExp end2 start1 no_pos in                          *)
(*   (* check if chain2 follows chain1 *)                                        *)
(*   if (TP.imply_raw aux_info chain1_cond) then (                               *)
(*     let new_hf = CF.mkStarH hf1 hf2 pos in                                    *)
(*     Some (new_hf, start1, end2)                                               *)
(*   )                                                                           *)
(*   (* check if chain1 follows chain1 *)                                        *)
(*   else if (TP.imply_raw aux_info chain1_cond) then (                          *)
(*     let new_hf = CF.mkStarH hf2 hf1 pos in                                    *)
(*     Some (new_hf, start2, end1)                                               *)
(*   )                                                                           *)
(*   else None                                                                   *)


(* (* collect all view names from a h_formula *)                                    *)
(* let rec collect_view_from_hformula (hf: CF.h_formula) : ident list =             *)
(*   let eq_id x y = (String.compare x y = 0) in                                    *)
(*   let views = ref [] in                                                          *)
(*   let f_hf hf = match hf with                                                    *)
(*     | ViewNode vn ->                                                             *)
(*         views := Gen.BList.remove_dups_eq eq_id (h_formula_view_name :: !views); *)
(*         (Some hf)                                                                *)
(*     | _ -> None in                                                               *)
(*   let _ = CF.transform_h_formula f_hf hf in                                      *)
(*   !views                                                                         *)

let collect_atomic_heap_chain_x (f: CF.formula) (root_view: C.view_decl) (prog: C.prog_decl)
    : (heap_chain list) =
  if ((List.length root_view.C.view_forward_ptrs != 1) 
      || (List.length root_view.C.view_forward_fields != 1)) then []
  (* consider only the case the root view has 1 forward pointer and 1 forward field *)
  else (
    let pos = CF.pos_of_formula f in
    let fw_ptr = List.hd root_view.C.view_forward_ptrs in
    let fw_field = snd (List.hd root_view.C.view_forward_fields) in
    let root_dname = root_view.C.view_data_name in
    let root_vname = root_view.C.view_name in
    let heap_chains = ref [] in
    let (hf,_,_,_,_) = CF.split_components f in
    let f_hf hf = (match hf with
      | CF.DataNode dn ->
          if (String.compare dn.CF.h_formula_data_name root_dname = 0) then (
            try 
              let ddecl = C.look_up_data_def_raw prog.C.prog_data_decls root_dname in
              let entry_sv = dn.CF.h_formula_data_node in
              let exit_sv = (
                let svs = List.fold_left2 (fun res arg field ->
                  let ((_,fname),_) = field in
                  if (String.compare fname fw_field = 0) then res @ [arg]
                  else res
                ) [] dn.CF.h_formula_data_arguments ddecl.C.data_fields in
                if (List.length svs != 1) then
                  report_error pos "collect_atomic_heap_chain: expect 1 exit sv"
                else List.hd svs
              ) in
              heap_chains := !heap_chains @ [(hf, entry_sv, exit_sv)];
            with _ -> ()
          );
          None
      | CF.ViewNode vn ->
          if (String.compare vn.CF.h_formula_view_name root_vname = 0) then (
            try 
              let entry_sv = vn.CF.h_formula_view_node in
              let exit_sv = (
                let svs = List.fold_left2 (fun res arg var ->
                  if (CP.eq_spec_var var fw_ptr) then res @ [arg]
                  else res
                ) [] vn.CF.h_formula_view_arguments root_view.C.view_vars in
                if (List.length svs != 1) then
                  report_error pos "collect_atomic_heap_chain: expect 1 exit sv"
                else List.hd svs
              ) in
              heap_chains := !heap_chains @ [(hf, entry_sv, exit_sv)];
            with _ -> ()
          );
          None
      | CF.Star _ -> None
      | _ -> Some hf
    ) in
    let _ = CF.transform_h_formula f_hf hf in
    !heap_chains
  )

let collect_atomic_heap_chain (f: CF.formula) (root_view: C.view_decl) (prog: C.prog_decl)
    : (heap_chain list) =
  let pr_f = !CF.print_formula in
  let pr_vname vd = vd.C.view_name in
  let pr_chain heap_chain = (
    let (hf,entry_sv,exit_sv) = heap_chain in
    "(" ^ (!CF.print_h_formula hf) ^ ", " ^ (!CP.print_sv entry_sv)
    ^ ", " ^ (!CP.print_sv exit_sv) ^ ")"
  ) in
  let pr_out = pr_list pr_chain in
  Debug.no_2 "collect_atomic_heap_chain" pr_f pr_vname pr_out
    (fun _ _ -> collect_atomic_heap_chain_x f root_view prog) f root_view


  (* match hf with                                                                                                   *)
  (* | DataNode of h_formula_data                                                                                    *)
  (* | ViewNode of h_formula_view                                                                                    *)
  (* | ThreadNode of h_formula_thread                                                                                *)
  (* | Star star -                                                                                                   *)
  (* | StarMinus of h_formula_starminus                                                                              *)
  (* | Conj of h_formula_conj                                                                                        *)
  (* | ConjStar of h_formula_conjstar                                                                                *)
  (* | ConjConj of h_formula_conjconj                                                                                *)
  (* | Phase of h_formula_phase                                                                                      *)
  (* | Hole of int | FrmHole of int                                                                                  *)
  (* (* | TempHole of int * h_formula *)                                                                             *)
  (* | HRel of (CP.spec_var * ((CP.exp) list) * loc) (*placeh older for heap predicates*)                            *)
  (* (* | HRel of ((CP.spec_var * cond_path_type) * ((CP.exp) list) * loc) (\*placeh older for heap predicates*\) *) *)
  (* | HTrue                                                                                                         *)
  (* | HFalse                                                                                                        *)
  (* | HEmp (* emp for classical logic *)                                                                            *)


(*
 * - Segment a heap formula into heap chains,
 *   each heap chain is as long as possible.
 * - This segmentation is applicable only to conjunction of heap node
 *)
(* let segment_heap_conjunct_into_chains (hf: CF.h_formula) (aux_info: MCP.mix_formula) *)
     (* : (CF.h_formula list) = *)


(*
 * Find a list of heap chain starting from a root node
 * This list is ordered descendingly by the each heap chain length 
 *)
let collect_heap_chains_x (f: CF.formula) (root_sv: CP.spec_var)
    (root_view: C.view_decl) prog
    : heap_chain list =
  let (hf,mf,_,_,_) = CF.split_components f in
  let pf = MCP.pure_of_mix mf in
  let pos = CF.pos_of_formula f in
  let rec build_heap_chains built_chains atomic_chains = (
    let latest_chain = List.hd built_chains in
    let (latest_hf,latest_sv1,latest_sv2) = latest_chain in
    try
      let next_atomic_chain = List.find (fun (hf,sv1,sv2) ->
        (TP.imply_raw pf (CP.mkEqVar sv1 latest_sv2 pos))
      ) atomic_chains in
      let (next_hf, next_sv1, next_sv2) = next_atomic_chain in
      let new_hf = CF.mkStarH latest_hf next_hf pos in
      let new_chain = (new_hf, latest_sv1, next_sv2) in
      let built_chains = new_chain :: built_chains in
      build_heap_chains built_chains atomic_chains
    with Not_found -> built_chains
  ) in
  let atomic_chains = collect_atomic_heap_chain f root_view prog in
  try
    let root_chain = List.find (fun (hf,sv1,sv2) ->
      (TP.imply_raw pf (CP.mkEqVar sv1 root_sv pos))
    ) atomic_chains in
    let heap_chains = build_heap_chains [root_chain] atomic_chains in
    let heap_chains = List.rev heap_chains in
    heap_chains
  with Not_found -> []

let collect_heap_chains (f: CF.formula) (root_sv: CP.spec_var)
    (root_view: C.view_decl) prog
    : heap_chain list =
  let pr_f = !CF.print_formula in
  let pr_sv = !CP.print_sv in
  let pr_vname vd = vd.C.view_name in
  let pr_chain heap_chain = (
    let (hf,entry_sv,exit_sv) = heap_chain in
    "(" ^ (!CF.print_h_formula hf) ^ ", " ^ (!CP.print_sv entry_sv)
    ^ ", " ^ (!CP.print_sv exit_sv) ^ ")"
  ) in
  let pr_out = pr_list pr_chain in
  Debug.no_3 "collect_heap_chains" pr_f pr_sv pr_vname pr_out
      (fun _ _ _ -> collect_heap_chains_x f root_sv root_view prog)
      f root_sv root_view

(* let detect_fold_sequence (hc: heap_chain) (root_view: C.view_decl) = *)
  