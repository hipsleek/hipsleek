#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Others
open Label_only
module CP = Cpure
module IF = Iformula
module CF = Cformula
module CFU = Cfutil
module MCP = Mcpure
module CEQ = Checkeq

let mem = Gen.BList.mem_eq CP.eq_spec_var
let diff = Gen.BList.difference_eq CP.eq_spec_var

let rec partition_by_key key_of key_eq ls = 
  match ls with
  | [] -> []
  | e::es ->
    let ke = key_of e in 
    let same_es, other_es = List.partition (fun e -> key_eq ke (key_of e)) es in
    (ke, e::same_es)::(partition_by_key key_of key_eq other_es)

(***************************)
(***** ADDING DANGLING *****)
(***************************)

let dangling_view_name = "Dangling"

let mk_dangling_view_prim = 
  Cast.mk_view_prim dangling_view_name [] (MCP.mkMTrue no_pos) no_pos

let mk_dangling_view_node dangling_var = 
  CF.mkViewNode dangling_var dangling_view_name [] no_pos

let add_dangling_hprel (hpr: CF.hprel) =
  let _, lhs_p, _, _, _, _ = CF.split_components hpr.hprel_lhs in
  let lhs_aliases = MCP.ptr_equations_with_null lhs_p in
  let guard_aliases =
    match hpr.hprel_guard with
    | None -> []
    | Some g -> 
      let _, guard_p, _, _, _, _ = CF.split_components g in
      MCP.ptr_equations_with_null guard_p
  in
  let aliases = CP.find_all_closures (lhs_aliases @ guard_aliases) in
  let null_aliases =
    try List.find (fun svl -> List.exists CP.is_null_const svl) aliases
    with _ -> []
  in
  let lhs_args = CF.collect_feasible_heap_args_formula null_aliases hpr.hprel_lhs in
  let rhs_args = CF.collect_feasible_heap_args_formula null_aliases hpr.hprel_rhs in
  let rhs_args_w_aliases = List.concat (List.map (fun arg ->
    try List.find (fun svl -> mem arg svl) aliases
    with _ -> [arg]) rhs_args) in 
  let dangling_args = List.filter CP.is_node_typ (diff lhs_args rhs_args_w_aliases) in
  let () = x_binfo_hp (add_str "Dangling args" !CP.print_svl) dangling_args no_pos in
  let hpr_rhs = List.fold_left (fun hrp_rhs dangling_arg ->
      CF.mkStar_combine_heap hrp_rhs (mk_dangling_view_node dangling_arg) CF.Flow_combine no_pos
    ) hpr.hprel_rhs dangling_args in
  { hpr with hprel_rhs = hpr_rhs }, not (is_empty dangling_args)

let add_dangling_hprel (hpr: CF.hprel) = 
  let pr = Cprinter.string_of_hprel in
  Debug.no_1 "add_dangling_hprel" pr (pr_pair pr string_of_bool) add_dangling_hprel hpr

let add_dangling prog (is: CF.infer_state) = 
  let () = x_binfo_pp "Step 1: Adding dangling references" no_pos in
  let is_all_constrs, has_dangling_vars = List.split (List.map add_dangling_hprel is.CF.is_all_constrs) in
  let has_dangling_vars = or_list has_dangling_vars in
  let prog =
    if has_dangling_vars then
      { prog with Cast.prog_view_decls = prog.Cast.prog_view_decls @ [mk_dangling_view_prim]; }
    else prog
  in
  let () =
    if has_dangling_vars then
      x_binfo_hp (add_str "Detected dangling vars" (pr_list Cprinter.string_of_hprel_short)) is_all_constrs no_pos
    else x_binfo_pp "No dangling vars is detected" no_pos
  in
  { is with CF.is_all_constrs = is_all_constrs }

let add_dangling prog is = 
  let pr2 = Cprinter.string_of_infer_state_short in
  Debug.no_1 "add_dangling" pr2 pr2
    (fun _ -> add_dangling prog is) is

(*********************)
(***** UNFOLDING *****)
(*********************)
let key_of_hprel (hpr: CF.hprel) = 
  let hpr_lhs = hpr.hprel_lhs in
  let lhs_h, _, _, _, _, _ = CF.split_components hpr.hprel_lhs in
  match lhs_h with
  | HRel (hpr_sv, _, _) -> hpr_sv
  | _ -> failwith ("Unexpected formula in the LHS of a hprel " ^ (Cprinter.string_of_hprel_short hpr))

let paritition_hprel_list hprels = 
  partition_by_key key_of_hprel CP.eq_spec_var hprels
