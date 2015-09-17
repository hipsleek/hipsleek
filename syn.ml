#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Others
open Label_only
open SynUtils
module CP = Cpure
module IF = Iformula
module CF = Cformula
(* module CFU = Cfutil *)
module MCP = Mcpure
(* module CEQ = Checkeq *)

(***************************)
(***** ADDING DANGLING *****)
(***************************)

let dangling_view_name = "Dangling"

let mk_dangling_view_prim = 
  Cast.mk_view_prim dangling_view_name [] (MCP.mkMTrue no_pos) no_pos

let mk_dangling_view_node dangling_var = 
  CF.mkViewNode dangling_var dangling_view_name [] no_pos

let add_dangling_hprel prog (hpr: CF.hprel) =
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
  let lhs_args = collect_feasible_heap_args_formula prog null_aliases hpr.hprel_lhs in
  let lhs_nodes = CF.collect_node_var_formula hpr.hprel_lhs in
  let rhs_args = collect_feasible_heap_args_formula prog null_aliases hpr.hprel_rhs in
  let rhs_args_w_aliases = List.concat (List.map (fun arg ->
    try List.find (fun svl -> mem arg svl) aliases
    with _ -> [arg]) rhs_args) in 
  let dangling_args = List.filter CP.is_node_typ (diff (* (diff lhs_args lhs_nodes) *) lhs_args rhs_args_w_aliases) in
  let () = x_binfo_hp (add_str "Dangling args" !CP.print_svl) dangling_args no_pos in
  let combine_dangling_args f = List.fold_left (fun acc_f dangling_arg ->
      CF.mkStar_combine_heap acc_f (mk_dangling_view_node dangling_arg) CF.Flow_combine no_pos
    ) f dangling_args in
  if is_empty dangling_args then hpr, false
  else
    (* let n_hpr =                                                                             *)
    (*   if is_pre_hprel hpr then { hpr with hprel_rhs = combine_dangling_args hpr.hprel_rhs } *)
    (*   else { hpr with hprel_lhs = combine_dangling_args hpr.hprel_lhs }                     *)
    (* in                                                                                      *)
    (* n_hpr, true                                                                             *)
    { hpr with hprel_rhs = combine_dangling_args hpr.hprel_rhs }, true

let add_dangling_hprel prog (hpr: CF.hprel) = 
  let pr = Cprinter.string_of_hprel_short in
  Debug.no_1 "add_dangling_hprel" pr (pr_pair pr string_of_bool) (add_dangling_hprel prog) hpr

let add_dangling_hprel_list prog (hpr_list: CF.hprel list) =
  fst (List.split (List.map (add_dangling_hprel prog) hpr_list))

(*********************)
(***** UNFOLDING *****)
(*********************)
module Ident = struct
  type t = ident
  let compare = String.compare
  let hash = Hashtbl.hash
  let equal i1 i2 = compare i1 i2 == 0 
end

module CG = Graph.Persistent.Digraph.Concrete(Ident)
module CGC = Graph.Components.Make(CG)

let hprel_num = ref 0

let fresh_hprel_num () =
  hprel_num := !hprel_num + 1;
  !hprel_num

type hprel_id = {
  hprel_constr: CF.hprel;
  hprel_id: int;
}

let mk_hprel_id hpr = 
  { hprel_constr = hpr; hprel_id = fresh_hprel_num (); }

let partition_hprel_list hprel_ids = 
  partition_by_key (fun hpri -> name_of_hprel hpri.hprel_constr) CP.eq_spec_var hprel_ids

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

let unfolding_one_hrel_def prog ctx hrel (hrel_def: CF.hprel) =
  let pos = no_pos in
  let hrd_lhs = hrel_def.hprel_lhs in
  let hrel_name, hrel_args = sig_of_hrel hrel in
  let _, lhs_p, _, _, _, _ = CF.split_components hrd_lhs in
  let lhs_p = MCP.pure_of_mix lhs_p in
  let ex_lhs_p = MCP.mix_of_pure (simplify lhs_p hrel_args) in
  let hrd_guard = hrel_def.hprel_guard in
  let guard_f = 
    match hrd_guard with
    | None -> CF.mkBase_simp HEmp (MCP.mkMTrue pos)
    | Some g -> g
  in
  let guard_h, guard_p, _, _, _, _ = CF.split_components guard_f in
  let guard_h_f = CF.mkBase_simp guard_h ex_lhs_p in
  let rs, residue = heap_entail_formula prog ctx guard_h_f in
  if rs then
    let _, ctx_p, _, _, _, _ = CF.split_components ctx in
    if is_sat (MCP.merge_mems ctx_p guard_p true) then
      (* Prevent self-recursive pred to avoid infinite unfolding *)
      let hprel_rhs_fv = CF.fv hrel_def.hprel_rhs in
      if mem hrel_name hprel_rhs_fv then
        failwith "Unfolding self-recursive predicate is not allowed to avoid possibly infinite unfolding!"
      else
        let comb_f = combine_Star guard_f residue in
        Some (combine_Star comb_f hrel_def.hprel_rhs)
    else None
  else None

let unfolding_one_hrel_def prog ctx hrel (hrel_def: CF.hprel) =
  let pr1 = !CF.print_formula in
  let pr2 = Cprinter.string_of_hprel_short in
  Debug.no_2 "unfolding_one_hrel_def" pr1 pr2 (pr_option pr1)
    (fun _ _ -> unfolding_one_hrel_def prog ctx hrel hrel_def) ctx hrel_def

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
      let guarded_hrel_defs, unguarded_hrel_defs = List.partition (fun hrel_def ->
          match hrel_def.CF.hprel_guard with Some _ -> true | None -> false) subst_hrel_defs in
      let non_inst_unguarded_hrel_defs, unguarded_hrel_defs = List.partition (is_non_inst_hprel prog) unguarded_hrel_defs in
      (* Only unfolding guarded hrel or non-inst hrel *)
      let unfolding_ctx_list = List.fold_left (fun acc hrel_def ->
          let unfolding_ctx = unfolding_one_hrel_def prog ctx hrel hrel_def in
          match unfolding_ctx with
          | None -> acc
          | Some ctx -> acc @ [ctx]) [] (guarded_hrel_defs @ non_inst_unguarded_hrel_defs)
      in
      let unfolding_ctx_list = 
        if is_empty unguarded_hrel_defs 
        then unfolding_ctx_list
        else unfolding_ctx_list @ [add_back_hrel ctx hrel]
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

let unfolding_hrel_list prog ctx hprel_name hrel_list hprel_groups =
  let rec helper ctx hrel_list = 
    match hrel_list with
    | [] -> [ctx]
    | hr::hrl ->
      let ctx_list = unfolding_one_hrel prog ctx hprel_name hr hprel_groups in
      List.concat (List.map (fun ctx -> helper ctx hrl) ctx_list)
  in
  let non_inst_hrel_list, norm_hrel_list = List.partition (is_non_inst_hrel prog) hrel_list in
  helper ctx (norm_hrel_list @ non_inst_hrel_list)

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

let dependent_graph_of_hprel dg hprel = 
  let hpr_name = CP.name_of_spec_var (name_of_hprel hprel) in 
  let hpr_rhs = hprel.hprel_rhs in
  let rhs_h, _, _, _, _, _ = CF.split_components hpr_rhs in
  let rhs_hrels = List.filter CF.is_hrel (CF.split_star_conjunctions rhs_h) in
  let rhs_hrels_name = List.map (fun hr -> CP.name_of_spec_var (name_of_hrel hr)) rhs_hrels in
  List.fold_left (fun dg hr_name -> CG.add_edge dg hpr_name hr_name) dg rhs_hrels_name

let dependent_graph_of_hprel_list hprel_list =
  let dg = CG.empty in
  List.fold_left (fun dg hprel -> dependent_graph_of_hprel dg hprel) dg hprel_list

let sort_hprel_list hprel_list = 
  let dg = dependent_graph_of_hprel_list hprel_list in
  let _, scc_f = CGC.scc dg in
  let compare hpr1 hpr2 =
    let hpr1_name = CP.name_of_spec_var (name_of_hprel hpr1) in
    let hpr2_name = CP.name_of_spec_var (name_of_hprel hpr2) in 
    (scc_f hpr1_name) - (scc_f hpr2_name)
  in
  List.sort compare hprel_list

let rec update_hprel_id_groups hprel_id hprel_sv hprel_id_list hprel_id_groups =
  match hprel_id_groups with
  | [] -> []
  | (hpr_sv, hpri_group)::hpri_groups ->
    if CP.eq_spec_var hpr_sv hprel_sv then
      let replaced_hpri_group = 
        hprel_id_list @ 
        (List.filter (fun hpri -> hpri.hprel_id != hprel_id) hpri_group) 
      in
      (hpr_sv, replaced_hpri_group)::hpri_groups
    else 
      (hpr_sv, hpri_group)::(update_hprel_id_groups hprel_id hprel_sv hprel_id_list hpri_groups)

let rec helper_unfolding_hprel_list_x prog hprel_id_groups hprel_id_list =
  match hprel_id_list with
  | [] -> []
  | hpri::hpril ->
    let hprel_groups = List.map (fun (hprel_sv, hprel_id_list) ->
        (hprel_sv, List.map (fun hpri -> hpri.hprel_constr) hprel_id_list)
      ) hprel_id_groups in
    let unfolding_hpr = unfolding_hprel prog hprel_groups hpri.hprel_constr in
    let unfolding_hpri = List.map mk_hprel_id unfolding_hpr in
    let updated_hprel_id_groups = update_hprel_id_groups 
      hpri.hprel_id (name_of_hprel hpri.hprel_constr) unfolding_hpri hprel_id_groups in
    unfolding_hpr @ (helper_unfolding_hprel_list prog updated_hprel_id_groups hpril)

and helper_unfolding_hprel_list prog hprel_id_groups hprel_id_list =
  let pr1 = Cprinter.string_of_hprel_list_short in
  let pr2 hpril = pr1 (List.map (fun hpri -> hpri.hprel_constr) hpril) in
  let pr3 = pr_list (pr_pair !CP.print_sv pr2) in
  Debug.no_2 "helper_unfolding_hprel_list" pr2 pr3 pr1
    (fun _ _ -> helper_unfolding_hprel_list_x prog hprel_id_groups hprel_id_list)
    hprel_id_list hprel_id_groups

let unfolding_hprel_list prog hprel_list =
  let sorted_hprel_list = sort_hprel_list hprel_list in
  let hprel_id_list = List.map mk_hprel_id sorted_hprel_list in
  let hprel_id_groups = partition_hprel_list hprel_id_list in
  helper_unfolding_hprel_list prog hprel_id_groups hprel_id_list

let selective_unfolding prog other_hprels hprels = 
  let pre_hprels, post_hprels = List.partition is_pre_hprel hprels in
  let sorted_hprel_list = sort_hprel_list pre_hprels in
  let hprel_id_list = List.map mk_hprel_id sorted_hprel_list in
  let other_hprel_id_list = List.map mk_hprel_id other_hprels in
  let hprel_id_groups = partition_hprel_list (hprel_id_list @ other_hprel_id_list) in 
  (helper_unfolding_hprel_list prog hprel_id_groups hprel_id_list) @ post_hprels

let selective_unfolding prog other_hprels hprels = 
  let pr = Cprinter.string_of_hprel_list_short in
  Debug.no_2 "selective_unfolding" pr pr pr 
    (fun _ _ -> selective_unfolding prog other_hprels hprels) other_hprels hprels

let unfolding prog hprels = 
  let pre_hprels, post_hprels = List.partition is_pre_hprel hprels in
  (unfolding_hprel_list prog pre_hprels) @ post_hprels

let unfolding prog hprels = 
  let pr = Cprinter.string_of_hprel_list_short in
  Debug.no_1 "unfolding" pr pr (fun _ -> unfolding prog hprels) hprels

(**************************)
(***** PARAMETERIZING *****)
(**************************)
let trans_heap_formula f_h_f (f: CF.formula) = 
  let somef2 _ f = Some (f, []) in
  let id2 f _ = (f, []) in
  let ida _ f = (f, []) in
  let f_arg = (voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2) in
  CF.trans_formula f () 
    (nonef2, nonef2, f_h_f, (somef2, somef2, somef2), (somef2, id2, ida, id2, id2)) 
    f_arg List.concat

let remove_dangling_heap_formula (f: CF.formula) = 
  let f_h_f _ hf = 
    match hf with
    | CF.ViewNode ({ 
        h_formula_view_node = view_node;
        h_formula_view_name = view_name; } as v) ->
      if eq_id view_name dangling_view_name then
        Some (CF.HEmp, [view_node])
      else Some (hf, [])
    | _ -> None
  in
  trans_heap_formula f_h_f f

let remove_dangling_heap_formula (f: CF.formula) = 
  let pr1 = !CF.print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_1 "remove_dangling_heap_formula" pr1 (pr_pair pr1 pr2)
    remove_dangling_heap_formula f
  
let add_dangling_params hrel_name dangling_params (f: CF.formula) = 
  let f_h_f _ hf = 
    match hf with
    | CF.HRel (hr_sv, hr_args, hr_pos) ->
      if CP.eq_spec_var hr_sv hrel_name then
        let parameterized_hrel = CF.HRel (hr_sv, hr_args @ dangling_params, hr_pos) in
        Some (parameterized_hrel, [])
      else Some (hf, [])
    | _ -> None
  in
  fst (trans_heap_formula f_h_f f)

let add_dangling_params hrel_name dangling_params (f: CF.formula) = 
  let pr1 = !CF.print_formula in
  let pr2 = !CP.print_sv in
  let pr3 = pr_list !CP.print_exp in
  Debug.no_3 "add_dangling_params" pr1 pr2 pr3 pr1
    (fun _ _ _ -> add_dangling_params hrel_name dangling_params f)
    f hrel_name dangling_params

let dangling_parameterizing_hprel (hpr: CF.hprel) =
  let is_pre = is_pre_hprel hpr in
  let param_f = if is_pre then hpr.hprel_rhs else hpr.hprel_lhs in 
  
  let n_param_f, dangling_vars = remove_dangling_heap_formula param_f in
  if is_empty dangling_vars then hpr, idf
  else
    let fresh_dangling_vars = CP.fresh_spec_vars dangling_vars in
    let dangling_params = List.map (fun dv -> CP.mkVar dv no_pos) fresh_dangling_vars in
    let n_param_f = CF.subst (List.combine dangling_vars fresh_dangling_vars) n_param_f in
    let hpr_name = name_of_hprel hpr in
    let f_update_params_hprel hpr =
      { hpr with
        CF.hprel_lhs = add_dangling_params hpr_name dangling_params hpr.CF.hprel_lhs;
        CF.hprel_rhs = add_dangling_params hpr_name dangling_params hpr.CF.hprel_rhs;
      }
    in
    let f_update_params_hprel hpr =
      let pr = Cprinter.string_of_hprel_short in
      Debug.no_1 "f_update_params_hprel" pr pr f_update_params_hprel hpr
    in
    let n_hpr = 
      if is_pre then { hpr with hprel_rhs = n_param_f }
      else { hpr with hprel_lhs = n_param_f }
    in 
    n_hpr, f_update_params_hprel

let dangling_parameterizing_hprel (hpr: CF.hprel) =
  let pr1 = Cprinter.string_of_hprel_short in
  let pr2 = fun (hpr, _) -> pr1 hpr in
  Debug.no_1 "dangling_parameterizing_hprel" pr1 pr2 dangling_parameterizing_hprel hpr

let rec dangling_parameterizing hprels =
  let rec helper_x acc hprels = 
    match hprels with
    | [] -> acc
    | hpr::hprl ->
      let hpr_wo_dangling, f_update_params = dangling_parameterizing_hprel hpr in
      let n_hpr = f_update_params hpr_wo_dangling in
      let n_hprl = List.map f_update_params hprl in
      let n_acc = List.map f_update_params acc in
      helper (n_acc @ [n_hpr]) n_hprl

  and helper acc hprels =
    let pr = Cprinter.string_of_hprel_list_short in
    Debug.no_2 "dangling_parameterizing_helper" pr pr pr
      helper_x acc hprels
  in
  
  helper [] hprels

let dangling_parameterizing hprels = 
  let pr = Cprinter.string_of_hprel_list_short in
  Debug.no_1 "parameterizing" pr pr 
    (fun _ -> dangling_parameterizing hprels) hprels

(****************)
(***** MAIN *****)
(****************)
let syn_preds prog (is: CF.infer_state) = 
  if !Globals.new_pred_syn then
    let () = x_binfo_pp ">>>>> Step 1: Adding dangling references <<<<<" no_pos in
    let is_all_constrs, has_dangling_vars = List.split (List.map (add_dangling_hprel prog) is.CF.is_all_constrs) in
    let has_dangling_vars = or_list has_dangling_vars in
    let prog =
      if has_dangling_vars then
        { prog with Cast.prog_view_decls = prog.Cast.prog_view_decls @ [mk_dangling_view_prim]; }
      else prog
    in
    let () =
      if has_dangling_vars then
        x_binfo_hp (add_str "Detected dangling vars" 
            Cprinter.string_of_hprel_list_short) is_all_constrs no_pos
      else x_binfo_pp "No dangling var is detected" no_pos
    in
  
    let () = x_binfo_pp ">>>>> Step 2: Unfolding <<<<<" no_pos in
    let is_all_constrs = unfolding prog is_all_constrs in
    let () = x_binfo_hp (add_str "Unfolding result" 
        Cprinter.string_of_hprel_list_short) is_all_constrs no_pos
    in
  
    let () = x_binfo_pp ">>>>> Step 3: Dangling Parameterizing <<<<<" no_pos in
    let is_all_constrs = dangling_parameterizing is_all_constrs in
    let () = x_binfo_hp (add_str "Parameterizing result" 
        Cprinter.string_of_hprel_list_short) is_all_constrs no_pos
    in
    { is with CF.is_all_constrs = is_all_constrs }
  else is

let syn_preds prog is = 
  let pr2 = Cprinter.string_of_infer_state_short in
  Debug.no_1 "syn_preds" pr2 pr2
    (fun _ -> syn_preds prog is) is