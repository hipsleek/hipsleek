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
      

type heap_chain = CF.h_formula * CP.spec_var * CP.spec_var

(*
 * each heap chain is a tuple of (h_formula, begin point, end point of chain)
 * return a merged heap formula if chain1 and chain2 are consecutive
 * otherwise, return None
 *)
let merge_heap_chains (chain1: heap_chain) (chain2: heap_chain)
    (aux_info: CP.mix_formula) pos
    : heap_chain option =
  let (hf1, start1, end1) = chain1 in
  let (hf2, start2, end2) = chain2 in
  let aux_pf = MCP.pure_of_mix aux_info in
  let chain1_cond = CP.mkEqExp end1 start2 no_pos in
  let chain2_cond = CP.mkEqExp end2 start1 no_pos in
  (* check if chain2 follows chain1 *)
  if (TP.imply_raw aux_info chain1_cond) then (
    let new_hf = CF.mkStarH hf1 hf2 pos in
    Some (new_hf, start1, end2)
  )
  (* check if chain1 follows chain1 *)
  else if (TP.imply_raw aux_info chain1_cond) then (
    let new_hf = CF.mkStarH hf2 hf1 pos in
    Some (new_hf, start2, end1)
  )
  else None


(* collect all view names from a h_formula *)
let rec collect_view_from_hformula (hf: CF.h_formula) : ident list =
  let eq_id x y = (String.compare x y = 0) in
  let views = ref [] in
  let f_hf hf = match hf with
    | ViewNode vn ->
        views := Gen.BList.remove_dups_eq eq_id (h_formula_view_name :: !views);
        (Some hf)
    | _ -> None in
  let _ = CF.transform_h_formula f_hf hf in
  !views

let rec break_heap_conjunct (hf: CF.h_formula) (prog: CF.prog_decl)
    : (heap_chain list * CF.h_formula option) =
  let vnames = collect_view_from_hformula hf in
  let vdecls = List.map (fun vname ->
    try look_up_view_def_raw prog.CF.prog_view_decls vname
    with Not_found ->
      let msg = ("View_decl not found: " ^ vname) in
      report_error no_pos msg
  ) vnames
      
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
let segment_heap_conjunct_into_chains (hf: CF.h_formula) (aux_info: MCP.mix_formula)
     : (CF.h_formula list) =
    
  