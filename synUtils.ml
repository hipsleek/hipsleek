#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Others
open Label_only
module CP = Cpure
module IF = Iformula
module CF = Cformula
module MCP = Mcpure

let mem = Gen.BList.mem_eq CP.eq_spec_var
let diff = Gen.BList.difference_eq CP.eq_spec_var
let remove_dups = Gen.BList.remove_dups_eq CP.eq_spec_var

let eq_id s1 s2 = String.compare s1 s2 == 0

let mem_id = Gen.BList.mem_eq eq_id

let rec partition_by_key key_of key_eq ls = 
  match ls with
  | [] -> []
  | e::es ->
    let ke = key_of e in 
    let same_es, other_es = List.partition (fun e -> key_eq ke (key_of e)) es in
    (ke, e::same_es)::(partition_by_key key_of key_eq other_es)

let bnd_vars_of_formula fv f args = 
  let bnd_vars = diff (fv f) args in
  let bnd_vars = List.filter (fun v ->
    match CP.type_of_spec_var v with
    | HpT -> false | _ -> true 
  ) bnd_vars in
  bnd_vars

let simplify f args = 
  let bnd_vars = bnd_vars_of_formula (CP.fv) f args in
  if bnd_vars == [] then f 
  else
    CP.mkExists_with_simpl Tpdispatcher.simplify_raw bnd_vars f None (CP.pos_of_formula f)

let simplify f args = 
  let pr1 = !CP.print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_2 "Syn.simplify" pr1 pr2 pr1 simplify f args

let imply a c = Tpdispatcher.imply_raw a c

let is_sat f = Tpdispatcher.is_sat_raw f

let push_exists_for_args f args =
  let bnd_vars = bnd_vars_of_formula (CF.fv) f args in
  CF.push_exists bnd_vars f

(*****************)
(***** UTILS *****)
(*****************)
let is_pre_hprel (hpr: CF.hprel) = 
  match hpr.hprel_type with
  | INFER_UNFOLD -> true
  | _ -> false
  
  
let is_post_hprel (hpr: CF.hprel) =
  match hpr.hprel_type with
  | INFER_FOLD -> true
  | _ -> false

let sig_of_hrel (h: CF.h_formula) =
  match h with
  | HRel (hr_sv, hr_args, _) -> (hr_sv, CF.get_node_args h)
  | _ -> failwith ("Expected a HRel h_formula instead of " ^ (!CF.print_h_formula h))

let name_of_hrel (h: CF.h_formula) = 
  fst (sig_of_hrel h) 

let args_of_hrel (h: CF.h_formula) = 
  snd (sig_of_hrel h)

let sig_of_hprel (hpr: CF.hprel) =
  let is_pre = is_pre_hprel hpr in
  let hpr_f = if is_pre then hpr.hprel_lhs else hpr.hprel_rhs in
  let f_h, _, _, _, _, _ = x_add_1 CF.split_components hpr_f in
  match f_h with
  | HRel (hr_sv, hr_args, _) -> (hr_sv, CF.get_node_args f_h)
  | _ -> failwith ("Unexpected formula in the " ^ 
                   (if is_pre then "LHS" else "RHS") ^ " of a " ^
                   (if is_pre then "pre-" else "post-") ^ "hprel " ^ 
                   (Cprinter.string_of_hprel_short hpr))

let name_of_hprel (hpr: CF.hprel) = 
  fst (sig_of_hprel hpr) 

let args_of_hprel (hpr: CF.hprel) = 
  snd (sig_of_hprel hpr)

(**********************)
(* UTILS OVER FORMULA *)
(**********************)
let combine_Star f1 f2 = 
  let comb_base f1 f2 = CF.mkStar f1 f2 CF.Flow_combine no_pos in
  let rec comb_base_f1 f1 f2 =
    match f2 with
    | CF.Base _
    | CF.Exists _ -> comb_base f1 f2
    | CF.Or { 
        formula_or_f1 = f2_1;
        formula_or_f2 = f2_2;
        formula_or_pos = pos; } ->
      let comb_f1 = comb_base_f1 f1 f2_1 in
      let comb_f2 = comb_base_f1 f1 f2_2 in
      CF.mkOr comb_f1 comb_f2 pos
  in
  let rec comb_formula f1 f2 =
    match f1 with
    | CF.Base _
    | CF.Exists _ -> comb_base_f1 f1 f2
    | CF.Or { 
        formula_or_f1 = f1_1;
        formula_or_f2 = f1_2;
        formula_or_pos = pos; } ->
      let comb_f1 = comb_formula f1_1 f2 in
      let comb_f2 = comb_formula f1_2 f2 in
      CF.mkOr comb_f1 comb_f2 pos
  in
  comb_formula f1 f2

let combine_Star f1 f2 = 
  let pr = !CF.print_formula in
  Debug.no_2 "combine_Star" pr pr pr combine_Star f1 f2

let trans_heap_formula f_h_f (f: CF.formula) = 
  let somef2 _ f = Some (f, []) in
  let id2 f _ = (f, []) in
  let ida _ f = (f, []) in
  let f_arg = (voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2) in
  CF.trans_formula f () 
    (nonef2, nonef2, f_h_f, (somef2, somef2, somef2), (somef2, id2, ida, id2, id2)) 
    f_arg List.concat

let rec trans_pure_formula f_m_f (f: CF.formula) = 
  match f with
  | CF.Base b ->
    let n_pure = f_m_f b.formula_base_pure in
    CF.Base { b with formula_base_pure = n_pure; }
  | CF.Or o ->
    let n_f1 = trans_pure_formula f_m_f o.formula_or_f1 in
    let n_f2 = trans_pure_formula f_m_f o.formula_or_f2 in
    CF.Or { o with formula_or_f1 = n_f1; formula_or_f2 = n_f2; }
  | CF.Exists e ->
    let n_pure = f_m_f e.formula_exists_pure in
    CF.Exists { e with formula_exists_pure = n_pure; }

let simplify_hprel (hprel: CF.hprel) =
  (* let args = args_of_hprel hprel in *)
  let h_fv_lhs = 
    (CF.fv_heap_of hprel.hprel_lhs) @
    (if is_post_hprel hprel then args_of_hprel hprel else []) 
  in
  let h_fv_lhs = remove_dups h_fv_lhs in
  let h_fv_guard = match hprel.hprel_guard with None -> [] | Some g -> CF.fv_heap_of g in
  let f_m_f args m_f =
    let p_f = MCP.pure_of_mix m_f in
    let simpl_p_f = simplify p_f args in
    MCP.mix_of_pure simpl_p_f 
  in
  { hprel with
    hprel_lhs = trans_pure_formula (f_m_f h_fv_lhs) hprel.hprel_lhs;
    hprel_guard = map_opt (trans_pure_formula (f_m_f h_fv_guard)) hprel.hprel_guard; }

let simplify_hprel (hprel: CF.hprel) =
  let pr = Cprinter.string_of_hprel_short in
  Debug.no_1 "simplify_hprel" pr pr simplify_hprel hprel

let is_non_inst_hprel prog (hprel: CF.hprel) =
  let hprel_name = CP.name_of_spec_var (name_of_hprel hprel) in
  let hprel_def = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls hprel_name in
  let hprel_inst = hprel_def.Cast.hp_vars_inst in
  List.for_all (fun (_, i) -> i = Globals.NI) hprel_inst

let is_non_inst_hrel prog (hrel: CF.h_formula) =
  let hrel_name = CP.name_of_spec_var (name_of_hrel hrel) in
  let hrel_def = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls hrel_name in
  let hrel_inst = hrel_def.Cast.hp_vars_inst in
  List.for_all (fun (_, i) -> i = Globals.NI) hrel_inst

let get_feasible_node_args prog (hf: CF.h_formula) =
  match hf with
  | HRel (hrel, el, _) ->
    let hrel_name = CP.name_of_spec_var hrel in
    let hprel_def = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls hrel_name in
    let el_inst = 
      try List.combine el (List.map snd hprel_def.Cast.hp_vars_inst)
      with Invalid_argument _ -> failwith ("SynUtils: Number of arguments of HRel " ^ hrel_name ^ " mismatched.")
    in
    List.fold_left (fun acc (e, i) ->
        match e with
        | CP.Var (sv, _) -> if i = Globals.NI then acc else acc @ [sv]
        | _ -> failwith ("Unexpected exp (not CP.Var) in HRel " ^ hrel_name ^ "'s arguments.")) 
      [] el_inst
  | _ -> CF.get_node_args hf

let collect_feasible_heap_args_formula prog null_aliases (f: CF.formula) : CP.spec_var list = 
  let rec helper f = 
    match f with
    | CF.Base ({ formula_base_heap = h; formula_base_pure = p; })
    | CF.Exists ({ formula_exists_heap = h; formula_exists_pure = p; }) ->
      let heaps = CF.split_star_conjunctions h in
      let heaps = List.filter (fun h ->
          match h with | CF.HEmp | CF.HTrue -> false | _ -> true) heaps
      in
      let heap_args = Gen.BList.remove_dups_eq CP.eq_spec_var 
          (List.concat (List.map (fun h ->
            let heap_node = try [CF.get_node_var h] with _ -> []
            in heap_node @ (get_feasible_node_args prog h)) heaps)) in
      if is_empty null_aliases then heap_args
      else
        List.filter (fun arg -> Gen.BList.mem_eq CP.eq_spec_var arg null_aliases) heap_args
    | CF.Or ({ formula_or_f1 = f1; formula_or_f2 = f2; }) ->
      (helper f1) @ (helper f2)
  in helper f

let collect_feasible_heap_args_formula prog null_aliases (f: CF.formula) : CP.spec_var list = 
  Debug.no_2 "collect_feasible_heap_args_formula" !CP.print_svl !CF.print_formula !CP.print_svl
    (collect_feasible_heap_args_formula prog) null_aliases f

let rec ctx_of_formula (f: CF.formula) = 
  let empty_es = CF.empty_es (CF.mkNormalFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let empty_ctx = CF.Ctx empty_es in
  CF.build_context empty_ctx f no_pos

let heap_entail_formula prog (ante: CF.formula) (conseq: CF.formula) =
  let ctx = ctx_of_formula ante in
  let rs, _ = x_add Solver.heap_entail_one_context 21 prog false ctx conseq None None None no_pos in
  let residue_f = CF.formula_of_list_context rs in
  match rs with
  | CF.FailCtx _ -> (false, residue_f)
  | CF.SuccCtx lst -> (true, residue_f) 

let heap_entail_formula prog (ante: CF.formula) (conseq: CF.formula) =
  let pr1 = !CF.print_formula in
  let pr2 = pr_pair string_of_bool pr1 in
  Debug.no_2 "Syn:heap_entail_formula" pr1 pr1 pr2 
    (fun _ _ -> heap_entail_formula prog ante conseq) ante conseq

let heap_entail_exact_formula prog (ante: CF.formula) (conseq: CF.formula) =
  fst (Wrapper.wrap_classic (Some true) (heap_entail_formula prog ante) conseq)

let heap_entail_exact_formula prog (ante: CF.formula) (conseq: CF.formula) =
  let pr1 = !CF.print_formula in
  let pr2 = string_of_bool in
  Debug.no_2 "Syn:heap_entail_exact_formula" pr1 pr1 pr2 
    (fun _ _ -> heap_entail_exact_formula prog ante conseq) ante conseq