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
  let pr = Cprinter.string_of_hprel_short in
  Debug.no_1 "add_dangling_hprel" pr (pr_pair pr string_of_bool) add_dangling_hprel hpr

(*********************)
(***** UNFOLDING *****)
(*********************)
let sig_of_hrel (h: CF.h_formula) =
  match h with
  | HRel (hpr_sv, hpr_args, _) -> (hpr_sv, CF.get_node_args h)
  | _ -> failwith ("Expected a HRel h_formula instead of " ^ (!CF.print_h_formula h))

let sig_of_hprel (hpr: CF.hprel) =
  let hpr_lhs = hpr.hprel_lhs in
  let lhs_h, _, _, _, _, _ = CF.split_components hpr.hprel_lhs in
  match lhs_h with
  | HRel (hpr_sv, hpr_args, _) -> (hpr_sv, CF.get_node_args lhs_h)
  | _ -> failwith ("Unexpected formula in the LHS of a hprel " ^ (Cprinter.string_of_hprel_short hpr))

let name_of_hprel (hpr: CF.hprel) = 
  fst (sig_of_hprel hpr) 

let args_of_hprel (hpr: CF.hprel) = 
  snd (sig_of_hprel hpr)

let partition_hprel_list hprels = 
  partition_by_key name_of_hprel CP.eq_spec_var hprels

let heap_entail_formula prog (ante: CF.formula) (conseq: CF.formula) =
  let empty_es = CF.empty_es (CF.mkNormalFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let ctx = CF.Ctx { empty_es with CF.es_formula = ante } in
  let rs, _ = x_add Solver.heap_entail_one_context 21 prog false ctx conseq None None None no_pos in
  let residue_f = CF.formula_of_list_context rs in
  match rs with
  | CF.FailCtx _ -> (false, residue_f)
  | CF.SuccCtx lst -> (true, residue_f) 

let heap_entail_formula prog (ante: CF.formula) (conseq: CF.formula) =
  let pr1 = !CF.print_formula in
  let pr2 = pr_pair string_of_bool pr1 in
  Debug.no_2 "Syn.heap_entail_formula" pr1 pr1 pr2 
    (fun _ _ -> heap_entail_formula prog ante conseq) ante conseq 

let is_sat f = Tpdispatcher.is_sat_raw f

let combine_Star f1 f2 = 
  CF.mkStar f1 f2 CF.Flow_combine no_pos

let add_back_hrel ctx hrel = 
  let hrel_f = CF.mkBase_simp hrel (MCP.mkMTrue no_pos) in
  combine_Star ctx hrel_f

let unfolding_one_hrel_def prog ctx (hrel_def: CF.hprel) =
  let pos = no_pos in
  let hrd_guard = hrel_def.hprel_guard in
  match hrd_guard with
  | None -> Some (combine_Star ctx hrel_def.hprel_rhs)
  | Some g ->
    let guard_h, guard_p, _, _, _, _ = CF.split_components g in
    let guard_h_f = CF.mkBase_simp guard_h (MCP.mkMTrue pos) in
    let rs, residue = heap_entail_formula prog ctx guard_h_f in
    if rs then
      let _, ctx_p, _, _, _, _ = CF.split_components ctx in
      if is_sat (MCP.merge_mems ctx_p guard_p true) then
        let comb_f = combine_Star g residue in
        Some (combine_Star comb_f hrel_def.hprel_rhs)
      else None
    else None

let unfolding_one_hrel_def prog ctx (hrel_def: CF.hprel) =
  let pr1 = !CF.print_formula in
  let pr2 = Cprinter.string_of_hprel_short in
  Debug.no_2 "unfolding_one_hrel_def" pr1 pr2 (pr_option pr1)
    (fun _ _ -> unfolding_one_hrel_def prog ctx hrel_def) ctx hrel_def

let unfolding_one_hrel prog ctx hprel_name hrel hprel_groups =
  let pos = no_pos in
  let hrel_name, hrel_args = sig_of_hrel hrel in
  if CP.eq_spec_var hprel_name hrel_name then
    [add_back_hrel ctx hrel]
  else
    let hrel_defs = List.filter (fun (hpr_sv, _) -> 
        CP.eq_spec_var hpr_sv hrel_name) hprel_groups in
    let hrel_defs = List.concat (List.map snd hrel_defs) in
    if is_empty hrel_defs then [add_back_hrel ctx hrel]
    else
      let subst_hrel_defs = List.map (
        fun hprel ->
          try
            let sst = List.combine (args_of_hprel hprel) hrel_args in
            CF.subst_hprel_constr sst hprel 
          with _ -> failwith ("Mismatch number of arguments of " ^ (!CP.print_sv hrel_name))
        ) hrel_defs
      in
      let unfolding_ctx_list = List.fold_left (fun acc hrel_def ->
          let unfolding_ctx = unfolding_one_hrel_def prog ctx hrel_def in
          match unfolding_ctx with
          | None -> acc
          | Some ctx -> acc @ [ctx]) [] subst_hrel_defs 
      in
      if is_empty unfolding_ctx_list then
        [add_back_hrel ctx hrel]
      else unfolding_ctx_list

let unfolding_one_hrel prog ctx hprel_name hrel hprel_groups =
  let pr1 = !CF.print_formula in
  let pr2 = !CF.print_h_formula in
  Debug.no_2 "unfolding_one_hrel" pr1 pr2 (pr_list pr1)
    (fun _ _ -> unfolding_one_hrel prog ctx hprel_name hrel hprel_groups) 
    ctx hrel

let rec unfolding_hrel_list prog ctx hprel_name hrel_list hprel_groups =
  match hrel_list with
  | [] -> [ctx]
  | hr::hrl ->
    let ctx_list = unfolding_one_hrel prog ctx hprel_name hr hprel_groups in
    List.concat (List.map (fun ctx -> 
        unfolding_hrel_list prog ctx hprel_name hrl hprel_groups) ctx_list)

let unfolding_hrel_list prog ctx hprel_name hrel_list hprel_groups =
  let pr1 = !CF.print_formula in
  let pr2 = pr_list !CF.print_h_formula in
  Debug.no_2 "unfolding_hrel_list" pr1 pr2 (pr_list pr1)
    (fun _ _ -> unfolding_hrel_list prog ctx hprel_name hrel_list hprel_groups) 
    ctx hrel_list

let rec unfolding_hprel prog hprel_groups (hpr: CF.hprel): CF.hprel list =
  let hpr_name, hpr_args = sig_of_hprel hpr in 
  let hpr_rhs = hpr.hprel_rhs in
  let rhs_h, rhs_p, _, _, _, _ = CF.split_components hpr_rhs in
  let rhs_hrels, rhs_hpreds = List.partition CF.is_hrel (CF.split_star_conjunctions rhs_h) in
  let ctx = CF.mkBase_simp (CF.join_star_conjunctions rhs_hpreds) rhs_p in
  let unfolding_ctx_list = unfolding_hrel_list prog ctx hpr_name rhs_hrels hprel_groups in
  let unfolding_hpr_list = List.map (fun unfolding_rhs -> 
      { hpr with hprel_rhs = unfolding_rhs }) unfolding_ctx_list in
  unfolding_hpr_list

let unfolding_hprel prog hprel_groups (hpr: CF.hprel): CF.hprel list =
  let pr = Cprinter.string_of_hprel_short in
  Debug.no_1 "unfolding_hprel" pr (pr_list pr)
    (fun _ -> unfolding_hprel prog hprel_groups hpr) hpr

let sort_hprel_list hprel_list = hprel_list

let unfolding_hprel_list prog hprel_list =
  let rec helper hprel_groups hprel_list =
    match hprel_list with
    | [] -> []
    | hpr::hprl ->
      (unfolding_hprel prog hprel_groups hpr) @ (helper hprel_groups hprl)
  in
  let hprel_groups = partition_hprel_list hprel_list in
  let sorted_hprel_list = sort_hprel_list hprel_list in
  helper hprel_groups sorted_hprel_list

let unfolding prog hprels = 
  unfolding_hprel_list prog hprels

let unfolding prog hprels = 
  let pr = pr_list Cprinter.string_of_hprel_short in
  Debug.no_1 "unfolding" pr pr (fun _ -> unfolding prog hprels) hprels

(****************)
(***** MAIN *****)
(****************)
let syn_preds prog (is: CF.infer_state) = 
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
  let () = x_binfo_pp "Step 2: Unfolding" no_pos in
  let is_all_constrs = unfolding prog is_all_constrs in
  { is with CF.is_all_constrs = is_all_constrs }

let syn_preds prog is = 
  let pr2 = Cprinter.string_of_infer_state_short in
  Debug.no_1 "syn_preds" pr2 pr2
    (fun _ -> syn_preds prog is) is