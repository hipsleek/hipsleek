#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Others
open Label_only
open SynUtils
open Wrapper
open Exc.GTable
module C = Cast
module I = Iast
module CP = Cpure
module IF = Iformula
module CF = Cformula
module CVU = Cvutil
module MCP = Mcpure
module CFU = Cfutil
(* module CEQ = Checkeq *)

(**************************)
(***** SIMPLIFICATION *****)
(**************************)

let pr_hprel_list = Cprinter.string_of_hprel_list_short

let simplify_hprel_list hprels = 
  List.map (x_add_1 simplify_hprel) hprels

(***************************)
(***** ADDING DANGLING *****)
(***************************)

let dangling_view_name = "Dangling"

let mk_dangling_view_prim = 
  Cast.mk_view_prim dangling_view_name [] (MCP.mkMTrue no_pos) no_pos

let mk_dangling_view_node dangling_var = 
  CF.mkViewNode dangling_var dangling_view_name [] no_pos

let add_dangling_hprel prog (hpr: CF.hprel) =
  if is_post_hprel hpr then
    let () = y_tinfo_pp ("Do not add dangling into the post-hprel " ^ (Cprinter.string_of_hprel_short hpr)) in
    hpr, false
  else
    let _, lhs_p, _, _, _, _ = x_add_1 CF.split_components hpr.hprel_lhs in
    let _, rhs_p, _, _, _, _ = x_add_1 CF.split_components hpr.hprel_rhs in
    let lhs_aliases = MCP.ptr_equations_with_null lhs_p in
    let rhs_aliases = MCP.ptr_equations_with_null rhs_p in
    let rhs_aset = CP.EMapSV.build_eset rhs_aliases in
    let guard_aliases =
      match hpr.hprel_guard with
      | None -> []
      | Some g -> 
        let _, guard_p, _, _, _, _ = x_add_1 CF.split_components g in
        MCP.ptr_equations_with_null guard_p
    in
    let aliases = CP.find_all_closures (lhs_aliases @ guard_aliases) in
    let () = y_tinfo_hp (add_str "aliases" (pr_list !CP.print_svl)) aliases in
    let null_aliases =
      try List.find (fun svl -> List.exists CP.is_null_const svl) aliases
      with _ -> []
    in
    let lhs_args = collect_feasible_heap_args_formula prog null_aliases hpr.hprel_lhs in
    (* let lhs_nodes = CF.collect_node_var_formula hpr.hprel_lhs in *)
    let rhs_args = collect_feasible_heap_args_formula prog null_aliases hpr.hprel_rhs in
    let rhs_args_w_aliases = List.concat (List.map (fun arg ->
      try List.find (fun svl -> mem arg svl) aliases
      with _ -> [arg]) rhs_args) in
    let lhs_def_vars = remove_dups (List.concat (List.map (fun (a, b) -> [a; b]) lhs_aliases)) in
    let () = y_tinfo_hp (add_str "lhs_def_vars" !CP.print_svl) lhs_def_vars in
    let () = y_tinfo_hp (add_str "lhs_args" !CP.print_svl) lhs_args in
    let () = y_tinfo_hp (add_str "rhs_args_w_aliases" !CP.print_svl) rhs_args_w_aliases in
    let dangling_args = List.filter CP.is_node_typ 
      (diff (* (diff lhs_args lhs_nodes) *) (diff lhs_args lhs_def_vars) rhs_args_w_aliases) in
    let () = y_tinfo_hp (add_str "dangling_args" !CP.print_svl) dangling_args in
    let strict_dangling_args = List.filter (fun dl ->
        let dl_aliases = CP.EMapSV.find_equiv_all_new dl rhs_aset in
        let dl_aliases = List.filter (fun dla -> not (CP.eq_spec_var dla dl)) dl_aliases in
        not (overlap dl_aliases lhs_args)
        (* if is_empty dl_aliases then true                                *)
        (* else not (List.exists (fun dla -> mem dla lhs_args) dl_aliases) *)
      ) dangling_args in
    let () = y_tinfo_hp (add_str "strict_dangling_args" !CP.print_svl) strict_dangling_args in
    let combine_dangling_args f = List.fold_left (fun acc_f dangling_arg ->
        CF.mkStar_combine_heap acc_f (mk_dangling_view_node dangling_arg) CF.Flow_combine no_pos
      ) f strict_dangling_args in
    if is_empty strict_dangling_args then hpr, false
    else
      { hpr with hprel_rhs = combine_dangling_args hpr.hprel_rhs }, true

let add_dangling_hprel prog (hpr: CF.hprel) =
  let pr = Cprinter.string_of_hprel_short in
  Debug.no_1 "Syn.add_dangling_hprel" pr (pr_pair pr string_of_bool) 
    (add_dangling_hprel prog) hpr

let add_dangling_hprel_list prog (hpr_list: CF.hprel list) =
  let n_hpr_list, has_dangling_vars = List.split (List.map (x_add add_dangling_hprel prog) hpr_list) in
  let has_dangling_vars = or_list has_dangling_vars in
  let () =
    if has_dangling_vars then
      (* { prog with Cast.prog_view_decls = prog.Cast.prog_view_decls @ [mk_dangling_view_prim]; } *)
      prog.Cast.prog_view_decls <- prog.Cast.prog_view_decls @ [mk_dangling_view_prim]
  in
  n_hpr_list

let add_dangling_hprel_list prog (hpr_list: CF.hprel list) =
  let pr = Cprinter.string_of_hprel_list_short in
  Debug.no_1 "Syn.add_dangling_hprel_list" pr pr (add_dangling_hprel_list prog) hpr_list

  
(*******************)
(***** MERGING *****)
(*******************)
let partition_hprel_list hprels = 
  partition_by_key (fun hpr -> name_of_hprel hpr) CP.eq_spec_var hprels

let rename_hprel_args n_args hprel =
  let hprel_name, hprel_args = sig_of_hprel hprel in
  try
    let sst = List.combine hprel_args n_args in
    CF.subst_hprel_constr sst hprel 
  with _ -> x_fail ("Mismatch number of arguments of " ^ (!CP.print_sv hprel_name))

let rename_hprel_list hprels = 
  match hprels with
  | [] -> []
  | hpr::hprs -> 
    let n_args = args_of_hprel hpr in
    hpr::(List.map (rename_hprel_args n_args) hprs)

let cond_of_pre_hprel (hprel: CF.hprel) = 
  let _, lhs_p, _, _, _, _ = x_add_1 CF.split_components hprel.hprel_lhs in
  match hprel.hprel_guard with
  | None -> MCP.pure_of_mix lhs_p
  | Some g -> 
    let _, g_p, _, _, _, _ = x_add_1 CF.split_components g in
    CP.mkAnd (MCP.pure_of_mix lhs_p) (MCP.pure_of_mix g_p) no_pos

let cond_guard_of_pre_hprel cond_list hprel_cond =
  let all_cond_guard = List.find_all (fun c -> imply hprel_cond c) cond_list in
  let cond_guard = CP.join_conjunctions all_cond_guard in
  cond_guard

let transform_pre_hprel_w_cond_guard cond_guard (hprel: CF.hprel) =
  let f_m_f m_f =
    let p_f = MCP.pure_of_mix m_f in
    let gist_p_f = Tpdispatcher.om_gist p_f cond_guard in
    MCP.mix_of_pure gist_p_f
  in
  { hprel with
    hprel_lhs = trans_pure_formula f_m_f hprel.hprel_lhs;
    hprel_guard = map_opt (trans_pure_formula f_m_f) hprel.hprel_guard; }

let transform_pre_hprel_w_cond_guard cond_guard (hprel: CF.hprel) =
  let pr1 = !CP.print_formula in
  let pr2 = Cprinter.string_of_hprel_short in
  Debug.no_2 "transform_pre_hprel_w_cond_guard" pr1 pr2 pr2 
    transform_pre_hprel_w_cond_guard cond_guard hprel

let should_merge_pre_hprels prog hprels = 
  match hprels with
  | []
  | _ ::[] -> false
  | hpr::hprs ->
    let args = args_of_hprel hpr in
    let ex_hpr_lhs = push_exists_for_args hpr.CF.hprel_lhs args in
    List.for_all (fun hp ->
      let ex_hp_lhs = push_exists_for_args hp.CF.hprel_lhs args in
      let equiv_lhs () = 
        (heap_entail_exact_formula prog ex_hpr_lhs ex_hp_lhs) &&
        (heap_entail_exact_formula prog ex_hp_lhs ex_hpr_lhs)
      in
      let equiv_guard () = 
        match hpr.CF.hprel_guard, hp.CF.hprel_guard with
        | None, None -> true
        | Some gr, Some g ->
          (heap_entail_exact_formula prog g gr) &&
          (heap_entail_exact_formula prog gr g)
        | _ -> false
      in (equiv_lhs ()) (* && (equiv_guard ()) *)) hprs

let should_merge_pre_hprels prog hprels = 
  let pr = pr_hprel_list in
  Debug.no_1 "should_merge_pre_hprels" pr string_of_bool
    (should_merge_pre_hprels prog) hprels
  
(* hprels have the same name *)
(* (A /\ a -> B) /\ (A /\ !a -> C) --> A -> (B /\ a) \/ (C /\ !a) *)
let merge_pre_hprel_list prog hprels =
  match hprels with
  | []
  | _::[] -> hprels
  | _ ->
    (* if List.exists (fun hpr -> is_None hpr.CF.hprel_guard) hprels then hprels *)
    (* else                                                                      *)
      let hprels = rename_hprel_list hprels in
      let conds = List.map cond_of_pre_hprel hprels in
      let sub_conds = List.concat (List.map CP.split_conjunctions conds) in
      let unsat_core = Smtsolver.get_unsat_core sub_conds in
      let () = y_binfo_hp (add_str "unsat_core" (pr_list !CP.print_formula)) unsat_core in
      if is_empty unsat_core then
        let msg = "Merging is not performed due to the set of pre-hprels does not have disjoint conditions" in
        let () = y_winfo_hp (add_str msg pr_hprel_list) hprels in
        hprels
      else
        let cond_guards = List.map (fun c -> cond_guard_of_pre_hprel unsat_core c) conds in
        let cond_guard_hprels = List.combine cond_guards hprels in
        let trans_hprels = List.map (fun (c, hpr) -> transform_pre_hprel_w_cond_guard c hpr) cond_guard_hprels in
        if not (should_merge_pre_hprels prog trans_hprels) then
          let msg = "Merging is not performed due to the set of pre-hprels does not have identical LHS and/or guards" in
          let () = y_winfo_hp (add_str msg pr_hprel_list) hprels in
          hprels
        else
          let disj_rhs_list = List.fold_left (fun acc (c, hprel) ->
            let rhs_w_cond = CF.add_pure_formula_to_formula c hprel.CF.hprel_rhs in
            acc @ [rhs_w_cond]) [] cond_guard_hprels in
          let disj_rhs = List.fold_left (fun acc f ->
            CF.mkOr acc f no_pos) (List.hd disj_rhs_list) (List.tl disj_rhs_list) in
          let comb_hpr = List.hd trans_hprels in
          let comb_hpr = { comb_hpr with hprel_rhs = disj_rhs } in
          [comb_hpr]

let merge_pre_hprel_list prog hprels =
  let pr = pr_hprel_list in
  Debug.no_1 "Syn.merge_pre_hprel_list" pr pr (merge_pre_hprel_list prog) hprels

(* (A -> C) /\ (B -> C) --> (A \/ B) -> C *)
let merge_post_hprel_list prog hprels =
  match hprels with
  | []
  | _::[] -> hprels
  | _ ->
    let hprels = rename_hprel_list hprels in
    let disj_lhs_list = List.map (fun hpr -> hpr.CF.hprel_lhs) hprels in
    let disj_lhs = List.fold_left (fun acc f ->
        CF.mkOr acc f no_pos) (List.hd disj_lhs_list) (List.tl disj_lhs_list) in
    let comb_hpr = List.hd hprels in
    let comb_hpr = { comb_hpr with hprel_lhs = disj_lhs } in
    [comb_hpr]

let merge_post_hprel_list prog hprels =
  let pr = pr_hprel_list in
  Debug.no_1 "Syn.merge_post_hprel_list" pr pr (merge_post_hprel_list prog) hprels

let merge_hprel_list prog hprels = 
  let pre_hprels, post_hprels = List.partition is_pre_hprel hprels in
  (merge_pre_hprel_list prog pre_hprels) @
  (merge_post_hprel_list prog post_hprels)

let merge_hprel_list prog hprels =
  let pr = pr_hprel_list in
  Debug.no_1 "Syn.merging" pr pr (merge_hprel_list prog) hprels

let merging prog hprels = 
  let hprel_lists = List.map snd (partition_hprel_list hprels) in
  List.concat (List.map (x_add merge_hprel_list prog) hprel_lists)

(*********************)
(***** UNFOLDING *****)
(*********************)
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

let partition_hprel_id_list hprel_ids = 
  partition_by_key (fun hpri -> name_of_hprel hpri.hprel_constr) CP.eq_spec_var hprel_ids

let add_back_hrel prog ctx hrel = 
  let hrel_f = CF.mkBase_simp hrel (MCP.mkMTrue no_pos) in
  combine_Star prog ctx hrel_f

let unfolding_one_hrel_def prog ctx hrel (hrel_def: CF.hprel) =
  let pos = no_pos in
  let hrel_name, hrel_args = sig_of_hrel hrel in
  let hprel_rhs_fv = CF.fv hrel_def.hprel_rhs in
  (* Prevent self-recursive pred to avoid infinite unfolding *)
  if mem hrel_name hprel_rhs_fv then
    let () = y_winfo_pp (
      "Unfolding self-recursive predicate " ^ 
      (!CF.print_h_formula hrel) ^ " is not allowed to avoid possibly infinite unfolding!")
    in
    None
  else
    let hrd_lhs = hrel_def.hprel_lhs in
    (* let _, lhs_p, _, _, _, _ = x_add_1 CF.split_components hrd_lhs in *)
    let lhs_p, _, _ = CVU.xpure_sym prog hrd_lhs in
    let lhs_p = MCP.pure_of_mix lhs_p in
    let ex_lhs_p = MCP.mix_of_pure (simplify lhs_p hrel_args) in
    let hrd_guard = hrel_def.hprel_guard in
    let guard_f = 
      match hrd_guard with
      | None -> CF.mkBase_simp HEmp (MCP.mkMTrue pos)
      | Some g -> g
    in
    let guard_h, guard_p, _, _, _, _ = x_add_1 CF.split_components guard_f in
    (* let guard_h_f = CF.mkBase_simp guard_h ex_lhs_p in *)
    let guard_h_f = CF.formula_of_heap guard_h no_pos in
    let rs, residue = x_add heap_entail_formula prog ctx guard_h_f in
    if rs then
      (* let _, ctx_p, _, _, _, _ = x_add_1 CF.split_components ctx in *)
      let ctx_p, _, _ = CVU.xpure_sym prog ctx in
      let p_cond = MCP.merge_mems ex_lhs_p guard_p true in
      if is_sat (MCP.merge_mems ctx_p p_cond true) then
        let comb_f = x_add combine_Star prog guard_h_f residue in
        Some (x_add combine_Star prog comb_f hrel_def.hprel_rhs, p_cond)
      else None (* not unfolding as it causes a contradiction *)
    else None (* guard_h is not satisfied by the current ctx *)

let unfolding_one_hrel_def prog ctx hrel (hrel_def: CF.hprel) =
  let pr1 = !CF.print_formula in
  let pr2 = Cprinter.string_of_hprel_short in
  let pr3 = pr_pair pr1 !MCP.print_mix_formula in
  Debug.no_2 "Syn.unfolding_one_hrel_def" pr1 pr2 (pr_option pr3)
    (fun _ _ -> unfolding_one_hrel_def prog ctx hrel hrel_def) ctx hrel_def

let unfolding_one_hrel prog ctx hrel hrel_defs = 
  let hrel_name, hrel_args = sig_of_hrel hrel in
  let merged_hrel_defs = (* x_add merge_hprel_list prog *) hrel_defs in
  let subst_hrel_defs = List.map (
    fun hprel ->
      try
        let sst = List.combine (args_of_hprel hprel) hrel_args in
        CF.subst_hprel_constr sst hprel 
      with _ -> x_fail ("Mismatch number of arguments of " ^ (!CP.print_sv hrel_name))
    ) merged_hrel_defs
  in
  (* let guarded_hrel_defs, unguarded_hrel_defs = List.partition (fun hrel_def ->                                           *)
  (*     match hrel_def.CF.hprel_guard with Some _ -> true | None -> false) subst_hrel_defs in                              *)
  (* let non_inst_unguarded_hrel_defs, unguarded_hrel_defs = List.partition (is_non_inst_hprel prog) unguarded_hrel_defs in *)
  (* (* Only unfolding guarded hrel or non-inst hrel *)                                                                     *)
  let unfolding_ctx_cond_list = List.fold_left (fun acc hrel_def ->
      let unfolding_ctx_cond = x_add unfolding_one_hrel_def prog ctx hrel hrel_def in
      match unfolding_ctx_cond with
      | None -> acc
      | Some (ctx, p) -> acc @ [(ctx, p)]) []
    (* (guarded_hrel_defs @ non_inst_unguarded_hrel_defs) *)
    subst_hrel_defs
  in
  (* let unfolding_ctx_list =                                  *)
  (*   if is_empty unguarded_hrel_defs                         *)
  (*   then unfolding_ctx_list                                 *)
  (*   else unfolding_ctx_list @ [add_back_hrel prog ctx hrel] *)
  (* in                                                        *)
  if is_empty unfolding_ctx_cond_list then
    [(add_back_hrel prog ctx hrel, MCP.mkMTrue no_pos)]
  else unfolding_ctx_cond_list

let folding_one_hrel_def prog ctx hrel (hrel_def: CF.hprel) =
  let pos = no_pos in
  let hrd_lhs = hrel_def.hprel_lhs in
  let hrel_name, hrel_args = sig_of_hrel hrel in
  (* Prevent self-recursive pred to avoid infinite folding *)
  let hprel_lhs_fv = CF.fv hrd_lhs in
  if mem hrel_name hprel_lhs_fv then
    let () = y_winfo_pp (
      "Folding self-recursive predicate " ^ (!CF.print_h_formula hrel) ^ 
      " is prohibited to avoid possibly infinite folding!")
    in
    None
  else
    (* let _, lhs_p, _, _, _, _ = x_add_1 CF.split_components hrd_lhs in *)
    let lhs_p, _, _ = x_add CVU.xpure_sym prog hrd_lhs in
    let lhs_p = MCP.pure_of_mix lhs_p in
    let ex_lhs_p = MCP.mix_of_pure (simplify lhs_p hrel_args) in
    (* let hrd_guard = hrel_def.hprel_guard in                          *)
    (* let guard_f =                                                    *)
    (*   let b = CF.mkBase_simp HEmp (MCP.mkMTrue pos) in               *)
    (*   match hrd_guard with                                           *)
    (*   | None -> b                                                    *)
    (*   | Some g -> b (* g *) (* Ignore guard in a post-hprel *)       *)
    (* in                                                               *)
    (* let guard_f = CF.add_pure_formula_to_formula ex_lhs_p guard_f in *)
    (* let rs, residue = x_add heap_entail_formula prog ctx guard_f in  *)
    (* if rs then                                                       *)
    let ctx_p, _, _ = CVU.xpure_sym prog ctx in
    if is_sat (MCP.merge_mems ctx_p ex_lhs_p true) then
      let comb_f = ctx (* x_add combine_Star prog guard_f residue *) in
      Some (x_add combine_Star prog comb_f hrel_def.hprel_lhs)
    else None

let folding_one_hrel_def prog ctx hrel (hrel_def: CF.hprel) =
  let pr1 = !CF.print_formula in
  let pr2 = Cprinter.string_of_hprel_short in
  Debug.no_2 "Syn.folding_one_hrel_def" pr1 pr2 (pr_option pr1)
    (fun _ _ -> folding_one_hrel_def prog ctx hrel hrel_def) ctx hrel_def

let folding_one_hrel prog ctx hrel hrel_defs = 
  let hrel_name, hrel_args = sig_of_hrel hrel in
  let subst_hrel_defs = List.map (
    fun hprel ->
      try
        let sst = List.combine (args_of_hprel hprel) hrel_args in
        CF.subst_hprel_constr sst hprel 
      with _ -> x_fail ("Mismatch number of arguments of " ^ (!CP.print_sv hrel_name))
    ) hrel_defs
  in
 let folding_ctx_list = List.fold_left (fun acc hrel_def ->
      let folding_ctx = x_add folding_one_hrel_def prog ctx hrel hrel_def in
      match folding_ctx with
      | None -> acc
      | Some ctx -> acc @ [ctx]) [] subst_hrel_defs
  in
  if is_empty folding_ctx_list then
    [add_back_hrel prog ctx hrel]
  else folding_ctx_list

let process_one_hrel prog is_unfolding ctx hprel_name hrel hprel_groups =
  let pos = no_pos in
  let hrel_name, hrel_args = sig_of_hrel hrel in
  if CP.eq_spec_var hprel_name hrel_name then
    [(add_back_hrel prog ctx hrel, MCP.mkMTrue no_pos)]
  else
    let hrel_defs = List.filter (fun (hpr_sv, _) -> 
        CP.eq_spec_var hpr_sv hrel_name) hprel_groups in
    let hrel_defs = List.concat (List.map snd hrel_defs) in
    if is_empty hrel_defs then [(add_back_hrel prog ctx hrel, MCP.mkMTrue no_pos)]
    else if is_unfolding then (* UNFOLDING FOR PRE-HPREL *)
      unfolding_one_hrel prog ctx hrel hrel_defs
    else (* FOLDING FOR POST-HPREL *)
      let folding_ctx_lst = folding_one_hrel prog ctx hrel hrel_defs in
      List.map (fun ctx -> (ctx, MCP.mkMTrue no_pos)) folding_ctx_lst

let process_one_hrel prog is_unfolding ctx hprel_name hrel hprel_groups =
  let pr1 = !CF.print_formula in
  let pr2 = !CF.print_h_formula in
  let pr3 = pr_pair pr1 !MCP.print_mix_formula in
  Debug.no_2 "Syn.process_one_hrel" pr1 pr2 (pr_list pr3)
    (fun _ _ -> process_one_hrel prog is_unfolding ctx hprel_name hrel hprel_groups) 
    ctx hrel

let unfolding_hrel_list prog is_unfolding ctx hprel_name hrel_list hprel_groups =
  let rec helper ctx hrel_list = 
    match hrel_list with
    | [] -> [(ctx, MCP.mkMTrue no_pos)]
    | hr::hrl ->
      let ctx_cond_list = x_add process_one_hrel prog is_unfolding ctx hprel_name hr hprel_groups in
      List.concat (List.map (fun (ctx, c) -> 
        let n_ctx_cond_list = helper ctx hrl in
        List.map (fun (n_ctx, n_c) -> n_ctx, MCP.merge_mems c n_c true) 
          n_ctx_cond_list) ctx_cond_list)
  in
  let non_inst_hrel_list, norm_hrel_list = List.partition (CFU.is_non_inst_hrel prog) hrel_list in
  helper ctx (norm_hrel_list @ non_inst_hrel_list)

let unfolding_hrel_list prog is_unfolding ctx hprel_name hrel_list hprel_groups =
  let pr1 = !CF.print_formula in
  let pr2 = pr_list !CF.print_h_formula in
  let pr3 = pr_pair pr1 !MCP.print_mix_formula in
  Debug.no_2 "Syn.unfolding_hrel_list" pr1 pr2 (pr_list pr3)
    (fun _ _ -> unfolding_hrel_list prog is_unfolding ctx hprel_name hrel_list hprel_groups) 
    ctx hrel_list

let unfolding_hprel_base prog is_unfolding hprel_groups hprel_name f_h f_p =
  let f_hrels, f_hpreds = List.partition CF.is_hrel (CF.split_star_conjunctions f_h) in
  let ctx = CF.mkBase_simp (CF.join_star_conjunctions f_hpreds) f_p in
  let unfolding_ctx_cond_list = x_add unfolding_hrel_list prog is_unfolding ctx hprel_name f_hrels hprel_groups in
  unfolding_ctx_cond_list

let rec unfolding_hprel_formula prog is_unfolding hprel_groups hprel_name (f: CF.formula) =
  match f with 
  | CF.Base { 
      formula_base_heap = h; 
      formula_base_pure = p; } ->
    unfolding_hprel_base prog is_unfolding hprel_groups hprel_name h p
  | CF.Exists { 
      formula_exists_qvars = svl;
      formula_exists_heap = h;
      formula_exists_pure = p } ->
    let unfolding_f_cond_list = unfolding_hprel_base prog is_unfolding hprel_groups hprel_name h p in
    List.map (fun (ctx, c) -> CF.push_exists svl ctx, MCP.mix_push_exists svl c) unfolding_f_cond_list
  | CF.Or {
      formula_or_f1 = f1;
      formula_or_f2 = f2;
      formula_or_pos = pos; } ->
    let unfolding_f1_cond_list = unfolding_hprel_formula prog is_unfolding hprel_groups hprel_name f1 in
    let unfolding_f2_cond_list = unfolding_hprel_formula prog is_unfolding hprel_groups hprel_name f2 in
    List.concat (List.map (fun (f1, c1) -> 
      List.map (fun (f2, c2) -> CF.mkOr f1 f2 pos, MCP.mkOr_mems c1 c2) unfolding_f2_cond_list) unfolding_f1_cond_list)

let unfolding_hprel_formula prog is_unfolding hprel_groups hprel_name (f: CF.formula) =
  let pr = !CF.print_formula in
  let pr1 = pr_pair pr !MCP.print_mix_formula in
  Debug.no_1 "Syn.unfolding_hprel_formula" pr (pr_list pr1)
    (fun _ -> unfolding_hprel_formula prog is_unfolding hprel_groups hprel_name f) f

let unfolding_hprel prog hprel_groups (hpr: CF.hprel): CF.hprel list =
  let hpr_name, hpr_args = sig_of_hprel hpr in
  let is_unfolding = is_pre_hprel hpr in
  let hpr_f = if is_unfolding then hpr.hprel_rhs else hpr.hprel_lhs in
  let unfolding_ctx_cond_list = x_add unfolding_hprel_formula prog is_unfolding hprel_groups hpr_name hpr_f in
  let unfolding_hpr_list = List.map (fun (unfolding_f, c) ->
      if is_unfolding then { hpr with 
          hprel_rhs = unfolding_f; 
          hprel_lhs = CF.add_pure_formula_to_formula (MCP.pure_of_mix c) hpr.hprel_lhs; }
      else { hpr with hprel_lhs = unfolding_f }) unfolding_ctx_cond_list in
  unfolding_hpr_list
    
let unfolding_hprel prog hprel_groups (hpr: CF.hprel): CF.hprel list =
  let pr = Cprinter.string_of_hprel_short in
  let pr1 = pr_list (fun (sv, _) -> !CP.print_sv sv) in
  Debug.no_2 "Syn.unfolding_hprel" pr pr1 (pr_list pr)
    (fun _ _ -> unfolding_hprel prog hprel_groups hpr) hpr hprel_groups

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

let rec helper_unfolding_hprel_list prog hprel_id_groups hprel_id_list =
  match hprel_id_list with
  | [] -> []
  | hpri::hpril ->
    let hpri_name = name_of_hprel hpri.hprel_constr in
    let dep_on_hpri = dg # depend_on (CP.name_of_spec_var hpri_name) in 
    let hprel_groups = List.fold_left (fun acc (hprel_sv, hprel_id_list) ->
        if mem_id (CP.name_of_spec_var hprel_sv) dep_on_hpri then acc
        else acc @ [(hprel_sv, List.map (fun hpri -> hpri.hprel_constr) hprel_id_list)]
      ) [] hprel_id_groups in
    let unfolding_hpr = x_add unfolding_hprel prog hprel_groups hpri.hprel_constr in
    let unfolding_hpri = List.map mk_hprel_id unfolding_hpr in
    let updated_hprel_id_groups = update_hprel_id_groups 
      hpri.hprel_id hpri_name unfolding_hpri hprel_id_groups in
    unfolding_hpr @ (helper_unfolding_hprel_list prog updated_hprel_id_groups hpril)

let helper_unfolding_hprel_list prog hprel_id_groups hprel_id_list =
  let pr1 = pr_hprel_list in
  let pr2 hpril = pr1 (List.map (fun hpri -> hpri.hprel_constr) hpril) in
  let pr3 = pr_list_ln (pr_pair !CP.print_sv pr2) in
  Debug.no_2 "Syn.helper_unfolding_hprel_list" pr2 (add_str "hprel_id_groups\n" pr3) pr1
    (fun _ _ -> helper_unfolding_hprel_list prog hprel_id_groups hprel_id_list)
    hprel_id_list hprel_id_groups

let unfolding_hprel_list prog hprel_list =
  let sorted_hprel_list = sort_hprel_list hprel_list in
  let hprel_id_list = List.map mk_hprel_id sorted_hprel_list in
  let hprel_id_groups = partition_hprel_id_list hprel_id_list in
  x_add helper_unfolding_hprel_list prog hprel_id_groups hprel_id_list

let aggr_selective_unfolding prog other_hprels sel_hprels =
  let all_hprels = sel_hprels @ other_hprels in
  let sel_hprels_id = List.map (fun hpr -> CP.name_of_spec_var (name_of_hprel hpr)) sel_hprels in
  let sorted_dep_sel_hprel_lst, other_hprel_lst = sort_dependent_hprel_list all_hprels sel_hprels_id in
  (* let sorted_hprel_list = sort_hprel_list (hprels @ other_hprels) in                            *)
  (* let sel_hprel_names = List.map name_of_hprel hprels in                                        *)
  (* (* Progressive selective unfolding: Unfolding the selective hprels and their dependants *)    *)
  (* let sorted_dep_sel_hprel_lst, other_hprel_lst, _ =                                            *)
  (*   List.fold_right (fun hpr (sacc, oacc, is_found) ->                                          *)
  (*     if is_found then (hpr::sacc, oacc, is_found)                                              *)
  (*     else if mem (name_of_hprel hpr) sel_hprel_names then (hpr::sacc, oacc, true)              *)
  (*     else (sacc, oacc, is_found)) sorted_hprel_list ([], [], false)                            *)
  (* in                                                                                            *)

  let dep_sel_hprel_id_lst = List.map mk_hprel_id sorted_dep_sel_hprel_lst in
  let other_hprel_id_lst = List.map mk_hprel_id other_hprel_lst in
  let hprel_id_groups = partition_hprel_id_list (dep_sel_hprel_id_lst @ other_hprel_id_lst) in
  x_add helper_unfolding_hprel_list prog hprel_id_groups dep_sel_hprel_id_lst,
  other_hprel_lst
  (* (* let sorted_selective_hprel_list = List.filter (fun s_hpr ->                             *) *)
  (* (*     mem (name_of_hprel s_hpr) hprel_names) sorted_hprel_list in                         *) *)
  (* (* let hprel_id_list = List.map mk_hprel_id sorted_selective_hprel_list in                 *) *)
  (* (* let other_hprel_id_list = List.map mk_hprel_id other_hprels in                          *) *)
  (* (* let hprel_id_groups = partition_hprel_id_list (hprel_id_list @ other_hprel_id_list) in  *) *)
  (* (* x_add helper_unfolding_hprel_list prog hprel_id_groups hprel_id_list                    *) *)

let comb_selective_unfolding prog other_hprels sel_hprels = 
  let sel_unfolding_hprels, others = aggr_selective_unfolding prog other_hprels sel_hprels in
  sel_unfolding_hprels @ others

let selective_unfolding prog other_hprels sel_hprels = 
  fst (aggr_selective_unfolding prog other_hprels sel_hprels)

let selective_unfolding prog other_hprels sel_hprels = 
  let pr = pr_hprel_list in
  Debug.no_2 "Syn.selective_unfolding" pr pr pr 
    (fun _ _ -> selective_unfolding prog other_hprels sel_hprels) other_hprels sel_hprels

let unfolding prog hprels = 
  unfolding_hprel_list prog hprels

let unfolding prog hprels = 
  let pr = pr_hprel_list in
  Debug.no_1 "Syn.unfolding" pr pr (fun _ -> unfolding prog hprels) hprels

(**************************)
(***** PARAMETERIZING *****)
(**************************)
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
  CF.trans_heap_formula f_h_f f

let remove_dangling_heap_formula (f: CF.formula) = 
  let pr1 = !CF.print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_1 "Syn.remove_dangling_heap_formula" pr1 (pr_pair pr1 pr2)
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
  fst (CF.trans_heap_formula f_h_f f)

let add_dangling_params hrel_name dangling_params (f: CF.formula) = 
  let pr1 = !CF.print_formula in
  let pr2 = !CP.print_sv in
  let pr3 = pr_list !CP.print_exp in
  Debug.no_3 "Syn.add_dangling_params" pr1 pr2 pr3 pr1
    (fun _ _ _ -> add_dangling_params hrel_name dangling_params f)
    f hrel_name dangling_params

let dangling_parameterizing_hprel (hpr: CF.hprel) =
  let is_pre = is_pre_hprel hpr in
  let f = if is_pre then hpr.hprel_rhs else hpr.hprel_lhs in 
  let f_disjs = CF.list_of_disjuncts f in
  let n_f_disjs_w_dangling_vars = List.fold_left (fun acc disj ->
    let n_disj, dangling_vars = x_add_1 remove_dangling_heap_formula disj in
    acc @ [(n_disj, dangling_vars)]) [] f_disjs
  in
  let all_dangling_vars = List.concat (List.map snd n_f_disjs_w_dangling_vars) in
  if is_empty all_dangling_vars then hpr, idf
  else
    let n_f_disjs, dangling_params_lists = List.split (List.map (fun (disj, dangling_vars) ->
      let fresh_dangling_vars = CP.fresh_spec_vars dangling_vars in
      let dangling_params = List.map (fun dv -> CP.mkVar dv no_pos) fresh_dangling_vars in
      (* Adding equality fresh_dangling_var = dangling_vars instead of renaming *)
      (* let n_disj = CF.subst (List.combine dangling_vars fresh_dangling_vars) disj in *)
      let n_disj = List.fold_left (fun f (dv, fdv) ->
          CF.add_pure_formula_to_formula (CP.mkEqVar fdv dv no_pos) f) 
        disj (List.combine dangling_vars fresh_dangling_vars) in
      (n_disj, dangling_params)) n_f_disjs_w_dangling_vars)
    in
    let n_f_opt = CF.join_conjunct_opt n_f_disjs in
    match n_f_opt with
    | None -> hpr, idf
    | Some n_f ->
      let dangling_params = List.concat dangling_params_lists in
      let hpr_name = name_of_hprel hpr in
      let f_update_params_hprel hpr =
        { hpr with
          CF.hprel_lhs = x_add add_dangling_params hpr_name dangling_params hpr.CF.hprel_lhs;
          CF.hprel_rhs = x_add add_dangling_params hpr_name dangling_params hpr.CF.hprel_rhs;
        }
      in
      let f_update_params_hprel hpr =
        let pr = Cprinter.string_of_hprel_short in
        Debug.no_1 "f_update_params_hprel" pr pr f_update_params_hprel hpr
      in
      let n_hpr = 
        if is_pre then { hpr with hprel_rhs = n_f }
        else { hpr with hprel_lhs = n_f }
      in 
      n_hpr, f_update_params_hprel

let dangling_parameterizing_hprel (hpr: CF.hprel) =
  let pr1 = Cprinter.string_of_hprel_short in
  let pr2 = fun (hpr, _) -> pr1 hpr in
  Debug.no_1 "Syn.dangling_parameterizing_hprel" pr1 pr2 dangling_parameterizing_hprel hpr

let rec dangling_parameterizing hprels =
  let rec helper_x acc hprels = 
    match hprels with
    | [] -> acc
    | hpr::hprl ->
      let hpr_wo_dangling, f_update_params = x_add_1 dangling_parameterizing_hprel hpr in
      let n_hpr = f_update_params hpr_wo_dangling in
      let n_hprl = List.map f_update_params hprl in
      let n_acc = List.map f_update_params acc in
      helper (n_acc @ [n_hpr]) n_hprl

  and helper acc hprels =
    let pr = pr_hprel_list in
    Debug.no_2 "dangling_parameterizing_helper" pr pr pr
      helper_x acc hprels
  in
  
  helper [] hprels

let dangling_parameterizing hprels = 
  let pr = pr_hprel_list in
  Debug.no_1 "Syn.parameterizing" pr pr 
    (fun _ -> dangling_parameterizing hprels) hprels

(***********************************)
(***** TRANSFORM HPREL TO VIEW *****)
(***********************************)
let trans_one_hprel_to_view iprog prog hv hprels = 
  let hid = CP.name_of_spec_var hv in
  let fail_msg = ("Cannot transform the hprels of " ^ hid ^ " into view declarations: ") in
  let unfold_hprels, fold_hprels = List.partition CFU.is_pre_hprel hprels in
  match unfold_hprels, fold_hprels with
  | hpr::[], others 
  | others, hpr::[] ->
    let vdecls =
      if !Globals.new_pred_syn then 
        let vdecl = view_decl_of_hprel iprog prog hpr in
        let () = y_binfo_hp (add_str ("other hprels of " ^ hid) Cprinter.string_of_hprel_list_short) others in
        let others_check = List.for_all (fun hpr ->
          let ante, _ = x_add trans_hrel_to_view_formula prog hpr.CF.hprel_lhs in
          let conseq, _ = x_add trans_hrel_to_view_formula prog hpr.CF.hprel_rhs in
          fst (x_add heap_entail_formula prog ante conseq)) others 
        in
        if others_check then [vdecl]
        else x_fail (fail_msg ^ "Other hprels are not satisfiable.")
      else Saout.view_decl_of_hprel iprog prog hpr
    in
    vdecls
  | _ -> x_fail (fail_msg ^ "Cannot find a single unfold/fold hprel.")

let trans_one_hprel_to_view iprog prog hv hprels = 
  let pr1 = Cprinter.string_of_hprel_list_short in
  let pr2 = pr_list_ln Cprinter.string_of_view_decl_short in
  Debug.no_2 "trans_one_hprel_to_view" !CP.print_sv pr1 pr2
    (fun _ _ -> trans_one_hprel_to_view iprog prog hv hprels) hv hprels

let trans_hprel_to_view iprog prog hprels = 
  let hprel_lists = partition_hprel_list hprels in
  let derived_views = List.concat (List.map (fun (hv, hprels) -> 
      trans_one_hprel_to_view iprog prog hv hprels) hprel_lists) in
  let () = y_tinfo_hp (add_str "derived_views" (pr_list_ln Cprinter.string_of_view_decl_short)) derived_views in
  (* prog_view_decls of iprog and cprog are updated by norm_derived_views *)
  let norm_derived_views = (* norm_derived_views iprog prog *) derived_views in
  let () = y_tinfo_hp (add_str "Derived Views" (pr_list_ln Cprinter.string_of_view_decl_short)) norm_derived_views in
  norm_derived_views

let trans_hprel_to_view iprog cprog hprels = 
  let pr1 = Cprinter.string_of_hprel_list_short in
  let pr2 = pr_list Cprinter.string_of_view_decl_short in
  Debug.no_1 "Syn.trans_hprel_to_view" pr1 pr2 
    (fun _ -> trans_hprel_to_view iprog cprog hprels) hprels

(**********************)
(***** PRED REUSE *****)
(**********************)
let aux_pred_reuse iprog cprog all_views =
  let ids = List.map (fun x -> x.Cast.view_name) all_views in 
  (* let vdefs = cprog.Cast.prog_view_decls in *)
  let vdefs = C.get_sorted_view_decls cprog in
  (* let () = Cast.cprog_obj # check_prog_upd x_loc cprog in *)
  let () = y_tinfo_pp "XXX Scheduling pred_elim_useless" in
  let vdefs = Norm.norm_elim_useless vdefs ids in
  (* let () = Cast.cprog_obj # check_prog_upd x_loc cprog in *)
  let v_ids = List.map (fun x -> x.Cast.view_name) vdefs in
  let () = y_tinfo_pp "XXX Scheduling pred_reuse" in
  let () = y_tinfo_hp (add_str "XXX derived_view names" (pr_list pr_id)) ids in
  let () = y_tinfo_hp (add_str "XXX derived views" 
      (pr_list Cprinter.string_of_view_decl_short)) all_views in
  let () = y_tinfo_hp (add_str "XXX existing view names" (pr_list pr_id)) v_ids in
  let lst = Norm.norm_reuse_rgx iprog cprog vdefs (REGEX_LIST ids) REGEX_STAR in
  let () = if lst!=[] then y_binfo_hp (add_str "XXX reuse found ..." (pr_list (pr_pair pr_id pr_id))) lst in
  let () = y_tinfo_pp "XXX Scheduling pred_reuse_subs" in
  let () = Norm.norm_reuse_subs iprog cprog vdefs ids in
  let () = y_tinfo_hp (add_str "XXX vdefs (after reuse)" 
      (pr_list Cprinter.string_of_view_decl_short)) vdefs in
  lst

let aux_pred_reuse iprog cprog all_views =
  let pr1 = pr_list (fun v -> v.Cast.view_name) in
  let pr2 = pr_list (pr_pair pr_id pr_id) in
  Debug.no_1 "aux_pred_reuse" pr1 pr2 
    (fun _ -> aux_pred_reuse iprog cprog all_views) all_views
  
(*************************)
(***** DERIVING VIEW *****)
(*************************)
let derive_view_norm prog other_hprels hprels = 
  (* PRE-PROCESSING *)
  let pre_hprels, post_hprels = List.partition is_pre_hprel hprels in
  let all_hprels = hprels @ other_hprels in
  (* WN : will other_hprels cause a problem later if it is neither unfold or fold? *)
  let () =
    if other_hprels != [] then
      let () = y_tinfo_hp (add_str "other_hprels is non-empty" pr_hprel_list) other_hprels in
      () 
  in
  (* SIMPLIFY *)
  let simplified_all_hprels = simplify_hprel_list all_hprels in
  (* ADD DANGLING *)
  let all_hprels_w_dangling = add_dangling_hprel_list prog simplified_all_hprels in
  let all_pre_hprels, all_post_hprels = List.partition is_pre_hprel all_hprels_w_dangling in
  (* DERIVING PRE: MERGE -> UNFOLD *)
  let all_merged_pre_hprels = merging prog all_pre_hprels in
  let selective_pre_hprel_ids = List.map (fun hpr -> name_of_hprel hpr) pre_hprels in
  let selective_merged_pre_hprels, other_merged_pre_hprels = List.partition 
    (fun hpr -> mem (name_of_hprel hpr) selective_pre_hprel_ids) all_merged_pre_hprels in
  let unfolding_pre_hprels = selective_unfolding prog other_merged_pre_hprels selective_merged_pre_hprels in
  (* DERIVING POST: FOLD -> MERGE *)
  let selective_post_hprel_ids = List.map (fun hpr -> name_of_hprel hpr) post_hprels in
  let selective_merged_post_hprels, other_merged_post_hprels = List.partition 
    (fun hpr -> mem (name_of_hprel hpr) selective_post_hprel_ids) all_post_hprels in
  let folding_post_hprels = selective_unfolding prog other_merged_post_hprels selective_merged_post_hprels in
  let merged_folding_post_hprels = merging prog folding_post_hprels in
  (* PARAM DANGLING *)
  let selective_merged_hprels = dangling_parameterizing (unfolding_pre_hprels @ merged_folding_post_hprels) in
  (* SIMPLIFY *)
  let simplified_selective_hprels = simplify_hprel_list selective_merged_hprels in
  simplified_selective_hprels

let derive_view_norm prog other_hprels hprels = 
  let pr = Cprinter.string_of_hprel_list_short in
  Debug.no_1 "Syn.derive_view_norm" pr pr
    (derive_view_norm prog other_hprels) hprels

let derive_view iprog cprog other_hprels hprels = 
  let hprels = Gen.BList.remove_dups_eq CF.eq_hprel_defn hprels in
  let other_hprels = Gen.BList.remove_dups_eq CF.eq_hprel_defn other_hprels in
  let pr = Cprinter.string_of_hprel_list_short in
  (* let () = y_binfo_hp (add_str "hprels" pr) hprels in *)
  (* let () = y_binfo_hp (add_str "other hprels" pr) other_hprels in *)
  let simplified_selective_hprels = derive_view_norm cprog other_hprels hprels in
  (* DERIVING VIEW *)
  let derived_views = trans_hprel_to_view iprog cprog (List.rev simplified_selective_hprels) in
  (* let derived_views = List.map (fun view -> unfolding_view iprog cprog view) derived_views in *)
  (derived_views, simplified_selective_hprels)

(* type: Saout.I.prog_decl -> *)
(*   Sautil.C.prog_decl -> *)
(*   SynUtils.CF.hprel list -> *)
(*   SynUtils.CF.hprel list -> Rev_ast.C.view_decl list * SynUtils.CF.hprel list *)
let derive_view iprog prog other_hprels hprels = 
  let pr1 = Cprinter.string_of_hprel_list_short in
  let pr2 = pr_list Cprinter.string_of_view_decl_short in
  Debug.no_2 "Syn.derive_view" pr1 pr1 (pr_pair pr2 pr1)
    (derive_view iprog prog) other_hprels hprels

(* type:                                                     *)
(*   Astsimp.I.prog_decl ->                                  *)
(*   Astsimp.C.prog_decl ->                                  *)
(*   C.view_decl ->                                          *)
(*   Globals.ident list ->                                   *)
(*   Rev_ast.CF.formula -> Rev_ast.CF.formula -> C.view_decl *)
let derive_equiv_view_by_lem ?(tmp_views=[]) iprog cprog view l_ivars l_head l_body =
  let l_name = "lem_inf_" ^ view.C.view_name in
  let l_ihead = Rev_ast.rev_trans_formula l_head in
  let l_ibody = Rev_ast.rev_trans_formula l_body in
  let llemma = I.mk_lemma l_name LEM_INFER LEM_GEN Left l_ivars l_ihead l_ibody in
  let () = llemma.I.coercion_infer_obj # set INF_CLASSIC in (* @classic *)
  let () = llemma.I.coercion_infer_obj # set INF_PURE_FIELD in (* @pure_field *)
  let () = y_tinfo_hp (add_str ("llemma " ^ l_name) Iprinter.string_of_coercion) llemma in 
  
  (* The below method updates CF.sleek_hprel_assumes via lemma proving *)
  let lres, _ = wrap_classic x_loc (Some true) (fun llemma -> x_add Lemma.manage_infer_lemmas [llemma] iprog cprog) llemma in
  if not lres then
    let () = y_binfo_pp "XXX fail infer ---> " in
    let () = restore_view iprog cprog view in
    [view]
  else
    let () = y_binfo_pp "XXX proven infer ---> " in
    let () = List.iter (fun v ->
      let () = C.update_un_struc_formula (fun f -> fst (trans_hrel_to_view_formula cprog f)) v in
      let () = C.update_view_formula (x_add_1 trans_hrel_to_view_struc_formula cprog) v in
      let () = x_add (C.update_view_decl ~caller:x_loc) cprog v in
      let () = x_add I.update_view_decl iprog (Rev_ast.rev_trans_view_decl v) in
      ()) tmp_views in
    (* derived_views have been added into prog_view_decls of iprog and cprog *)
    let derived_views, new_hprels = process_hprel_assumes_res "Deriving Segmented Views" 
        CF.sleek_hprel_assumes snd (REGEX_LIST l_ivars)
        (derive_view iprog cprog) 
    in
    (* let () = y_binfo_pp "XXX Scheduling pred_reuse_subs" in                                     *)
    let all_d_views = tmp_views@derived_views in
    (* let ids = List.map (fun x -> x.Cast.view_name) all_d_views in                               *)
    (* let vdefs = cprog.Cast.prog_view_decls in                                                   *)
    (* let v_ids = List.map (fun x -> x.Cast.view_name) vdefs in                                   *)
    (* let () = y_binfo_hp (add_str "XXX derived_view names" (pr_list pr_id)) ids in               *)
    (* let () = y_binfo_hp (add_str "XXX existing view names" (pr_list pr_id)) v_ids in            *)
    (* let lst = Norm.norm_reuse_rgx iprog cprog vdefs (REGEX_LIST ids) REGEX_STAR in              *)
    (* let () = y_binfo_hp (add_str "XXX reuse found .." (pr_list (pr_pair pr_id pr_id))) lst in   *)
    (* let () = y_tinfo_hp (add_str "derived views" (pr_list Cprinter.string_of_view_decl_short))  *)
    (*     all_d_views in                                                                          *)
    let lst = aux_pred_reuse iprog cprog all_d_views in
    (* Equiv test to form new pred *)
    let r_cbody, _ = x_add trans_hrel_to_view_formula cprog l_body in
    let r_ibody = Rev_ast.rev_trans_formula r_cbody in
    let r_name = l_name ^ "_rev" in
    let rlemma = I.mk_lemma r_name LEM_TEST LEM_GEN Right [] l_ihead r_ibody in
    let () = y_tinfo_hp (add_str ("rlemma " ^ r_name) Iprinter.string_of_coercion) rlemma in 
    let rres, _ = x_add Lemma.manage_infer_lemmas_x "test" [rlemma] iprog cprog in
    if not rres then 
      let () = y_binfo_pp "XXX fail <--- " in
      let () = y_tinfo_hp (add_str "rlemma" Iprinter.string_of_coercion) rlemma in
       let () = restore_view iprog cprog view in
      [view]
    else
      let () = y_binfo_pp "XXX proven equiv ..." in
      let vbody = CF.set_flow_in_formula_override 
          { CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link = None } 
          r_cbody 
      in
      let () = y_tinfo_hp (add_str "vbody" !CF.print_formula) vbody in
      let self_node = mk_self_node view.C.view_name vbody in
      let vbody = Typeinfer.case_normalize_renamed_formula iprog 
          (self_node::(elim_useless_vars view.C.view_vars)) [] vbody in
      (* let v_sf, v_un_str = norm_view_formula view.C.view_name vbody in *)
      (* let () =                                                                                                                 *)
      (*   view.C.view_formula <- v_sf;                                                                                           *)
      (*     (* CF.formula_to_struc_formula                                                                                    *) *)
      (*     (*   (Typeinfer.case_normalize_renamed_formula iprog (self_node::(elim_useless_vars view.C.view_vars)) [] vbody); *) *)
      (*   view.C.view_un_struc_formula <- v_un_str; (* [(vbody, (fresh_int (), ""))]; *)                                         *)
      (*   view.C.view_raw_base_case <- Cf_ext.compute_raw_base_case false v_un_str;                                              *)
      (*   view.C.view_base_case <- None                                                                                          *)
      (* in                                                                                                                       *)
      let norm_view = x_add update_view_content iprog cprog view vbody in
      (* let () = y_tinfo_hp (add_str "view" Cprinter.string_of_view_decl_short) view in *)
      (* let norm_view = norm_single_view iprog cprog view in                            *)
      let () = y_tinfo_hp (add_str "norm_view" Cprinter.string_of_view_decl_short) norm_view in
      norm_view::derived_views

(* type:                                                     *)
(*   Astsimp.I.prog_decl ->                                  *)
(*   Astsimp.C.prog_decl ->                                  *)
(*   C.view_decl ->                                          *)
(*   Globals.ident list ->                                   *)
(*   Rev_ast.CF.formula -> Rev_ast.CF.formula -> C.view_decl *)
let derive_equiv_view_by_lem ?(tmp_views=[]) iprog cprog view l_ivars l_head l_body =
  let pr1 = pr_list pr_id in
  let pr2 = !CF.print_formula in
  let pr3 = pr_list Cprinter.string_of_view_decl_short in
  Debug.no_3 "Syn.derive_equiv_view_by_lem" pr1 pr2 pr2 pr3
    (fun _ _ _ -> derive_equiv_view_by_lem ~tmp_views:tmp_views iprog cprog view l_ivars l_head l_body) l_ivars l_head l_body

(*******************************************)
(***** ELIM HEAD / TAIL / DISJ OF PRED *****)
(*******************************************)
let elim_head_pred iprog cprog pred = 
  let pred_f = C.formula_of_unstruc_view_f pred in
  let self_node = mk_self_node pred.C.view_name pred_f in
  let _, common_node_chain = find_common_node_chain self_node (CF.list_of_disjuncts pred_f) in
  let () = y_tinfo_hp (add_str "Common node chain" (pr_list !CF.print_h_formula)) common_node_chain in
  match common_node_chain with
  | [] -> [pred]
  | n::ns ->
    let common_heap = List.fold_left (fun acc f -> CF.mkStarH acc f no_pos) n ns in
    let common_f = CF.mkBase_simp common_heap (MCP.mkMTrue no_pos) in
    let args = collect_feasible_heap_args_formula cprog [] common_f in
    let nodes = CF.collect_node_var_formula common_f in
    let dangling_vars = List.filter CP.is_node_typ (diff args nodes) in
    let dangling_vars = remove_dups dangling_vars in
    let () = y_tinfo_hp (add_str "Unknown nodes" !CP.print_svl) dangling_vars in
    (* let fresh_pred_args = CP.fresh_spec_vars pred.C.view_vars in *)
    (* let fresh_pred_I_args = List.map (fun v -> (v, I)) (elim_useless_vars fresh_pred_args) in *)
    let pred_I_args = List.map (fun v -> (v, I)) (elim_useless_vars pred.C.view_vars) in
    let hrel_list, unknown_vars = List.split (List.map 
        (fun v -> x_add (C.add_raw_hp_rel ~caller:x_loc) cprog false true ((v, I)::pred_I_args (* fresh_pred_I_args *)) no_pos) dangling_vars) in
    let () =  iprog.I.prog_hp_decls <- (List.map Rev_ast.rev_trans_hp_decl cprog.C.prog_hp_decls) in
    let unknown_f = List.fold_left (fun f h -> CF.mkStar_combine_heap f h CF.Flow_combine no_pos) common_f hrel_list in
    let pred_h = CF.mkViewNode self_node pred.C.view_name pred.C.view_vars (* fresh_pred_args *) no_pos in
    (* let norm_flow = { CF.formula_flow_interval = exlist # get_hash n_flow; CF.formula_flow_link = None } in *)
    let norm_flow = CF.flow_formula_of_formula unknown_f in
    let pred_f = CF.set_flow_in_formula_override norm_flow (CF.formula_of_heap pred_h no_pos) in
    let pred_f_sv = CF.fv pred_f in
    let unknown_f_sv = CF.fv unknown_f in
    let ex_vars = List.filter (fun sv -> not (CP.is_hp_typ sv)) (diff unknown_f_sv pred_f_sv) in
    let unknown_f = CF.push_exists (remove_dups ex_vars) unknown_f in
    
    let ivars = List.map CP.name_of_spec_var unknown_vars in
    x_add derive_equiv_view_by_lem iprog cprog pred ivars pred_f unknown_f

let elim_head_pred iprog cprog pred = 
  let pr = Cprinter.string_of_view_decl_short in
  Debug.no_1 "Syn.elim_head_pred" pr (pr_list pr) 
    (fun _ -> elim_head_pred iprog cprog pred) pred

let elim_tail_pred iprog cprog pred = 
  (* let () =                                                                                        *)
  (*   try                                                                                           *)
  (*     let view_def = C.look_up_view_def_prog cprog pred.C.view_name in                            *)
  (*     ()                                                                                          *)
  (*   with _ -> y_winfo_pp ("Cannot find the definition of view " ^ pred.C.view_name ^ " in cprog") *)
  (* in                                                                                              *)
  let pred_f = C.formula_of_unstruc_view_f pred in
  let self_node =
    try
      List.find (fun sv -> eq_str (CP.name_of_spec_var sv) Globals.self) (CF.fv pred_f)
    with _ -> CP.SpecVar (Named pred.C.view_name, Globals.self, Unprimed)
  in
  let base_cases = find_pred_base_case pred in
  try
    let node_base_case = List.find (fun f -> 
        not (is_empty (snd (find_heap_node self_node f))) 
      ) base_cases in
    (* let fresh_pred_args = CP.fresh_spec_vars pred.C.view_vars in *)
    let fresh_self_node = CP.fresh_spec_var self_node in
    let pred_h = CF.mkViewNode self_node pred.C.view_name pred.C.view_vars (* fresh_pred_args *) no_pos in
    let unknown_h, unknown_hpred = x_add (C.add_raw_hp_rel ~caller:x_loc) cprog false true [(self_node, I); (fresh_self_node, I)] no_pos in
    let () =  iprog.I.prog_hp_decls <- (List.map Rev_ast.rev_trans_hp_decl cprog.C.prog_hp_decls) in
    let sst = [(self_node, fresh_self_node)] (* @ (List.combine pred.C.view_vars fresh_pred_args) *) in
    let unknown_f = 
      (* CF.mkStar_combine_heap (CF.subst sst node_base_case) unknown_h CF.Flow_combine no_pos in *)
      CF.mkStar_combine (CF.formula_of_heap unknown_h no_pos) (CF.subst sst node_base_case) CF.Flow_combine no_pos in
    let norm_flow = CF.flow_formula_of_formula unknown_f in
    let pred_f = CF.set_flow_in_formula_override norm_flow (CF.formula_of_heap pred_h no_pos) in
    let pred_f_sv = CF.fv pred_f in
    let unknown_f_sv = CF.fv unknown_f in
    let ex_vars = List.filter (fun sv -> not (CP.is_hp_typ sv)) (diff unknown_f_sv pred_f_sv) in
    let unknown_f = CF.push_exists (remove_dups ex_vars) unknown_f in
    x_add derive_equiv_view_by_lem iprog cprog pred [CP.name_of_spec_var unknown_hpred] pred_f unknown_f
  with _ -> [pred]

let elim_tail_pred iprog cprog pred = 
  let pr = Cprinter.string_of_view_decl_short in
  Debug.no_1 "Syn.elim_tail_pred" pr (pr_list pr) 
    (fun _ -> elim_tail_pred iprog cprog pred) pred

let elim_head_pred_list iprog cprog preds =
  norm_pred_list (elim_head_pred iprog cprog) preds

let elim_tail_pred_list iprog cprog preds =
  norm_pred_list (elim_tail_pred iprog cprog) preds

(*********************)
(***** PRED EXTN *****)
(*********************)

let extn_norm_pred iprog cprog extn_pred norm_pred =
  let equiv_pid = get_equiv_pred cprog norm_pred.C.view_name in 
  let norm_ipred = I.look_up_view_def_raw x_loc iprog.I.prog_view_decls equiv_pid in
  let extn_view_name = norm_ipred.I.view_name ^ "_" ^ extn_pred.C.view_name in
  let extn_view_var = extn_pred.C.view_name ^ "_prop" in
  let extn_iview = I.mk_iview_decl ~v_kind:View_DERV extn_view_name "" 
      (norm_ipred.I.view_vars @ [extn_view_var])
      (IF.mkETrue top_flow no_pos) no_pos
  in
  let orig_info = (norm_ipred.I.view_name, norm_ipred.I.view_vars) in
  (* DONE: Auto derive REC in typechecker (Norm.find_rec_data iprog prog REGEX_STAR) *)
  let extn_info = (extn_pred.C.view_name, [rec_field_id], [extn_view_var]) in
  let extn_iview = { extn_iview with 
    I.view_derv_from = Some (REGEX_LIST [(norm_ipred.I.view_name, true)]);
    I.view_derv_info = [(orig_info, extn_info)];
    I.view_derv_extns = [extn_info] } in
  let extn_cview_lst = x_add Derive.trans_view_dervs iprog 
    Rev_ast.rev_trans_formula Astsimp.trans_view [] 
    cprog.C.prog_view_decls extn_iview in
  let () = y_tinfo_hp (add_str "extn_cview_lst" 
      (pr_list Cprinter.string_of_view_decl_short)) extn_cview_lst in
  let extn_cview_aset = aux_pred_reuse iprog cprog extn_cview_lst in
  let comb_extn_name = Derive.retr_extn_pred_name norm_ipred.I.view_name extn_pred.C.view_name in
  let extn_cview = List.find (fun v -> eq_str v.C.view_name comb_extn_name) extn_cview_lst in
  (* let extn_cview = C.rename_view extn_cview equiv_pid in  *)
  let () = x_add (C.update_view_decl ~caller:x_loc) cprog extn_cview in
  let () = norm_pred.C.view_equiv_set # set ([], comb_extn_name) in
  let () = x_add Astsimp.compute_view_x_formula cprog extn_cview !Globals.n_xpure in
  extn_cview

let extn_norm_pred iprog cprog extn_pred norm_pred =
  let pr = Cprinter.string_of_view_decl_short in
  Debug.no_2 "Syn.extn_norm_pred" 
    (add_str "extn_pred" pr) (add_str "norm_pred" pr) pr
    (fun _ _ -> extn_norm_pred iprog cprog extn_pred norm_pred) extn_pred norm_pred

let extn_norm_pred_list iprog cprog extn_pred norm_preds = 
  List.map (fun pred -> extn_norm_pred iprog cprog extn_pred pred) norm_preds

(* Entry point of SLEEK cmd process_shape_extn_view *)
let extn_pred_list iprog cprog extn preds =
  try
    let extn_pred = C.look_up_view_def_raw x_loc cprog.C.prog_view_decls extn in
    match extn_pred.C.view_kind with
    | View_EXTN -> 
      let norm_preds = List.fold_left (fun acc pred ->
        match pred.C.view_kind with
        | View_NORM -> acc @ [pred]
        | k -> 
          let () = x_warn ("Cannot extend the " ^ (string_of_view_kind k) ^ " " ^ pred.C.view_name)
          in acc) [] preds 
      in
      extn_norm_pred_list iprog cprog extn_pred norm_preds
    | _ -> x_fail (extn ^ " is not a View_EXTN")
  with Not_found -> x_fail ("Cannot find the View_EXTN " ^ extn)

let extn_pred_id_list iprog cprog extn preds =
  let pred_decls = List.map (fun id ->
    try C.look_up_view_def_raw x_loc cprog.C.prog_view_decls id
    with _ -> x_fail ("Cannot find the view " ^ id)) preds in
  extn_pred_list iprog cprog extn pred_decls

let extn_pred_scc iprog cprog scc_proc_names = 
  let scc_procs = List.map (fun proc_name ->
    let proc = C.look_up_proc_def_raw cprog.C.new_proc_decls proc_name in
    proc) scc_proc_names in
  let scc_proc_specs = List.map (fun proc -> 
    proc.C.proc_stk_of_static_specs # top) scc_procs in
  let extn_lst = merge_infer_extn_lsts 
      (List.map get_inf_pred_extn_struc_formula scc_proc_specs) in
  let extn_pred_lst = partition_by_key 
    (fun (_, prop) -> prop) eq_str
    (expand_infer_extn_lst extn_lst) in
  List.map (fun (extn, extn_pred_lst) ->
    let preds = List.map (fun (id, _) -> id) extn_pred_lst in
    extn_pred_id_list iprog cprog extn preds) extn_pred_lst

(*********************************)
(***** COMBINE DISJ BRANCHES *****)
(*********************************)
let unify_disj_pred iprog cprog pred = 
  let pred_f = C.formula_of_unstruc_view_f pred in
  let self_node = mk_self_node pred.C.view_name pred_f in
  let common_node_chain, other_branches = find_common_node_chain_branches self_node (CF.list_of_disjuncts pred_f) in
  let () = y_tinfo_hp (add_str "Common node chain" (pr_list !CF.print_h_formula)) common_node_chain in
  match common_node_chain with
  | [] -> [pred]
  | n::ns ->
    let common_heap = List.fold_left (fun acc f -> CF.mkStarH acc f no_pos) n ns in
    let common_f = CF.mkBase_simp common_heap (MCP.mkMTrue no_pos) in
    let args = collect_feasible_heap_args_formula cprog [] common_f in
    let nodes = CF.collect_node_var_formula common_f in
    let dangling_vars = List.filter CP.is_node_typ (diff args nodes) in
    let dangling_vars = remove_dups dangling_vars in
    let () = y_tinfo_hp (add_str "Dangling nodes" !CP.print_svl) dangling_vars in
    let pred_I_args = List.map (fun v -> (v, I)) (elim_useless_vars pred.C.view_vars) in
    let hrel_list, unknown_vars = List.split (List.map 
        (fun v -> x_add (C.add_raw_hp_rel ~caller:x_loc) cprog false true ((v, I)::pred_I_args) no_pos) dangling_vars) in
    let () =  iprog.I.prog_hp_decls <- (List.map Rev_ast.rev_trans_hp_decl cprog.C.prog_hp_decls) in
    let unknown_branches = List.fold_left (fun f h -> CF.mkStar_combine_heap f h CF.Flow_combine no_pos) common_f hrel_list in
    let vbody = CF.formula_of_disjuncts (other_branches @ [unknown_branches]) in
    let vbody = CF.set_flow_in_formula_override 
        { CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link = None } 
        vbody 
    in
    let vbody = Typeinfer.case_normalize_renamed_formula iprog (self_node::(elim_useless_vars pred.C.view_vars)) [] vbody in
    
    (* Construct a new view with unknown HeapPred *)
    let tmp_name = "tmp_" ^ pred.C.view_name in
    (* let tmp_sf, tmp_un_str = norm_view_formula tmp_name vbody in *)
    let tmp_cpred = { pred with
        C.view_name = tmp_name;
        (* C.view_formula = tmp_sf; (* CF.formula_to_struc_formula vbody; *)           *)
        (* C.view_un_struc_formula = tmp_un_str; (* [(vbody, (fresh_int (), ""))]; *)  *)
      }  
    in
    let norm_tmp_cpred = x_add update_view_content iprog cprog tmp_cpred vbody in
    (* let tmp_ipred = Rev_ast.rev_trans_view_decl tmp_cpred in *)
    (* let () = C.update_view_decl cprog tmp_cpred in           *)
    (* let () = I.update_view_decl iprog tmp_ipred in           *)
    (* let norm_tmp_cpred = norm_single_view iprog cprog tmp_cpred in  *)
    let tmp_v = [norm_tmp_cpred] in
    let () = y_tinfo_hp (add_str "new view_decls" (pr_list Cprinter.string_of_view_decl_short)) tmp_v in
        (* cprog.C.prog_view_decls *) 
    let fresh_pred_args = CP.fresh_spec_vars pred.C.view_vars in
    let norm_flow = CF.flow_formula_of_formula unknown_branches in
    let pred_h = CF.mkViewNode self_node pred.C.view_name fresh_pred_args no_pos in
    let pred_f = CF.set_flow_in_formula_override norm_flow (CF.formula_of_heap pred_h no_pos) in
    let tmp_pred_h = CF.mkViewNode self_node tmp_name fresh_pred_args no_pos in
    let tmp_pred_f = CF.set_flow_in_formula_override norm_flow (CF.formula_of_heap tmp_pred_h no_pos) in
    let ivars = List.map CP.name_of_spec_var unknown_vars in
    x_add (derive_equiv_view_by_lem ~tmp_views:tmp_v) iprog cprog pred ivars pred_f tmp_pred_f

let unify_disj_pred_list iprog cprog preds =
  norm_pred_list (unify_disj_pred iprog cprog) preds

(****************)
(***** MAIN *****)
(****************)
let syn_pre_preds prog (is: CF.infer_state) = 
  if !Globals.new_pred_syn then
    let () = x_binfo_pp ">>>>> Step 0: Simplification <<<<<" no_pos in
    let is_all_constrs = CF.add_infer_type_to_hprel is.CF.is_all_constrs in
    let is_all_constrs = simplify_hprel_list is_all_constrs in
    let () = x_tinfo_hp (add_str "Simplified hprels" 
        pr_hprel_list) is_all_constrs no_pos
    in
  
    let () = x_binfo_pp ">>>>> Step 1: Adding dangling references <<<<<" no_pos in
    let is_all_constrs = x_add add_dangling_hprel_list prog is_all_constrs in
    (* let is_all_constrs, has_dangling_vars = List.split (List.map (x_add add_dangling_hprel prog) is_all_constrs) in *)
    (* let has_dangling_vars = or_list has_dangling_vars in                                                            *)
    (* let prog =                                                                                                      *)
    (*   if has_dangling_vars then                                                                                     *)
    (*     { prog with Cast.prog_view_decls = prog.Cast.prog_view_decls @ [mk_dangling_view_prim]; }                   *)
    (*   else prog                                                                                                     *)
    (* in                                                                                                              *)
    (* let () =                                                                                                        *)
    (*   if has_dangling_vars then                                                                                     *)
    (*     x_tinfo_hp (add_str "Detected dangling vars"                                                                *)
    (*         pr_hprel_list) is_all_constrs no_pos                                                                    *)
    (*   else x_tinfo_pp "No dangling var is detected" no_pos                                                          *)
    (* in                                                                                                              *)

    (* let () = x_binfo_pp ">>>>> Step 2A: Merging <<<<<" no_pos in   *)
    (* let is_all_constrs = x_add merging prog is_all_constrs in      *)
    (* let () = x_binfo_hp (add_str "Merging result"                  *)
    (*     pr_hprel_list) is_all_constrs no_pos *)
    (* in                                                             *)
  
    let () = x_binfo_pp ">>>>> Step 2: Unfolding <<<<<" no_pos in
    let is_all_constrs = x_add unfolding prog is_all_constrs in
    let () = x_tinfo_hp (add_str "Unfolding result" 
        pr_hprel_list) is_all_constrs no_pos
    in
  
    let () = x_binfo_pp ">>>>> Step 3: Dangling Parameterizing <<<<<" no_pos in
    let is_all_constrs = x_add_1 dangling_parameterizing is_all_constrs in
    let () = x_binfo_hp (add_str "Parameterizing result" 
        pr_hprel_list) is_all_constrs no_pos
    in

    let () = x_binfo_pp ">>>>> Step 4: Inferring Segment Predicates <<<<<" no_pos in
    
    { is with CF.is_all_constrs = is_all_constrs }
  else is

let syn_pre_preds prog is = 
  let pr2 = Cprinter.string_of_infer_state_short in
  Debug.no_1 "Syn.syn_pre_preds" pr2 pr2
    (fun _ -> syn_pre_preds prog is) is
