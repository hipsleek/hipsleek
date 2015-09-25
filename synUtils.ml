#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Others
open Label_only
open Exc.GTable
module C = Cast
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
  let simplify_f = Tpdispatcher.simplify_raw in
  let bnd_vars = bnd_vars_of_formula (CP.fv) f args in
  if bnd_vars == [] then simplify_f f 
  else
    CP.mkExists_with_simpl simplify_f bnd_vars f None (CP.pos_of_formula f)

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

let select_obj name_of obj_list obj_id_list = 
  List.partition (fun obj -> mem_id (name_of obj) obj_id_list) obj_list

let select_hprel_assume hprel_list hprel_id_list = 
  select_obj (fun hpr -> CP.name_of_spec_var (name_of_hprel hpr)) hprel_list hprel_id_list

let process_hprel_assumes_others s hprel_assume_stk (ids: regex_id_list) f_proc = 
  let () = print_endline_quiet "\n========================" in
  let () = print_endline_quiet (" Performing "^s) in
  let () = print_endline_quiet "========================" in
  let () = hprel_assume_stk # set (CF.add_infer_type_to_hprel (hprel_assume_stk # get)) in
  let sel_hprel_assume_list, others =
    match ids with
    | REGEX_STAR -> hprel_assume_stk # get, []
    | REGEX_LIST hps -> select_hprel_assume (hprel_assume_stk # get) hps
  in
  let res = f_proc others sel_hprel_assume_list in
  hprel_assume_stk # set (res @ others)

let process_hprel_assumes_res s hprel_assume_stk hprel_assume_of_res (ids: regex_id_list) f_proc = 
  let () = print_endline_quiet "\n========================" in
  let () = print_endline_quiet (" Performing "^s) in
  let () = print_endline_quiet "========================" in
  let () = hprel_assume_stk # set (CF.add_infer_type_to_hprel (hprel_assume_stk # get)) in
  let sel_hprel_assume_list, others =
    match ids with
    | REGEX_STAR -> hprel_assume_stk # get, []
    | REGEX_LIST hps -> select_hprel_assume (hprel_assume_stk # get) hps
  in
  let res = f_proc others sel_hprel_assume_list in
  let () = hprel_assume_stk # set ((hprel_assume_of_res res) @ others) in
  res

(*********************)
(* UTILS FOR FORMULA *)
(*********************)
let combine_Star prog f1 f2 = 
  let comb_base f1 f2 =
    let comb_f = CF.mkStar f1 f2 CF.Flow_combine no_pos in
    Solver.elim_unsat_all prog comb_f in
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

let combine_Star prog f1 f2 = 
  let pr = !CF.print_formula in
  Debug.no_2 "combine_Star" pr pr pr (combine_Star prog) f1 f2

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
  let h_fv_guard = remove_dups h_fv_guard in
  let h_fv_rhs = (CF.fv_heap_of hprel.hprel_rhs) @ (CF.fv hprel.hprel_lhs) in
  let h_fv_rhs = remove_dups h_fv_rhs in
  let f_m_f args m_f =
    let p_f = MCP.pure_of_mix m_f in
    let simpl_p_f = simplify p_f args in
    MCP.mix_of_pure simpl_p_f 
  in
  { hprel with
    hprel_lhs = trans_pure_formula (f_m_f h_fv_lhs) hprel.hprel_lhs;
    hprel_guard = map_opt (trans_pure_formula (f_m_f h_fv_guard)) hprel.hprel_guard; 
    hprel_rhs = trans_pure_formula (f_m_f h_fv_rhs) hprel.hprel_rhs; }

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
  Debug.no_2 "Syn.heap_entail_formula" pr1 pr1 pr2 
    (fun _ _ -> heap_entail_formula prog ante conseq) ante conseq

let heap_entail_exact_formula prog (ante: CF.formula) (conseq: CF.formula) =
  fst (Wrapper.wrap_classic (Some true) (heap_entail_formula prog ante) conseq)

let heap_entail_exact_formula prog (ante: CF.formula) (conseq: CF.formula) =
  let pr1 = !CF.print_formula in
  let pr2 = string_of_bool in
  Debug.no_2 "Syn.heap_entail_exact_formula" pr1 pr1 pr2 
    (fun _ _ -> heap_entail_exact_formula prog ante conseq) ante conseq

let trans_hrel_to_view_formula (f: CF.formula) = 
  let f_h_f _ hf = 
    match hf with
    | CF.HRel _ ->
      let hrel_name, hrel_args = sig_of_hrel hf in
      Some (CF.mk_HRel_as_view hrel_name hrel_args no_pos, [])
    | _ -> None
  in
  fst (trans_heap_formula f_h_f f)

let view_decl_of_hprel prog (hprel: CF.hprel) =
  let hprel_name, hprel_args = sig_of_hprel hprel in
  let pos = no_pos in
  let hprel_self = CP.to_unprimed (List.hd hprel_args) in
  let vself = match hprel_self with CP.SpecVar (t, _, p) -> CP.SpecVar (t, Globals.self, p) in
  let vargs = List.map (fun sv -> (sv, NI)) (List.tl hprel_args) in
  let vbody = if is_pre_hprel hprel then hprel.hprel_rhs else hprel.hprel_lhs in
  let vbody = CF.elim_prm vbody in
  let vbody = trans_hrel_to_view_formula vbody in
  let vbody = CF.subst [(hprel_self, vself)] vbody in
  (* Set flow for view *)
  let vbody = CF.set_flow_in_formula_override 
      { CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link = None } 
      vbody in
  let vdecl = Cast.mk_view_decl_for_hp_rel (CP.name_of_spec_var hprel_name) vargs false pos in
  let vdecl_w_def = { vdecl with 
      Cast.view_formula = CF.formula_to_struc_formula vbody;
      Cast.view_un_struc_formula = [(vbody, (fresh_int (), ""))];
      Cast.view_kind = View_NORM; } in
  let () = Cast.add_view_decl prog vdecl_w_def in
  vdecl_w_def

let view_decl_of_hprel prog (hprel: CF.hprel) =
  let pr1 = Cprinter.string_of_hprel_short in
  let pr2 = Cprinter.string_of_view_decl in
  Debug.no_1 "Syn.view_decl_of_hprel" pr1 pr2 (view_decl_of_hprel prog) hprel

let find_heap_node root (f: CF.formula) =
  let _, f_p, _, _, _, _ = CF.split_components f in
  let aliases = MCP.ptr_equations_without_null f_p in
  let aset = CP.EMapSV.build_eset aliases in
  let root_aliases = CP.EMapSV.find_equiv_all_new root aset in
  let f_h_f _ h_f =
    match h_f with
    | CF.DataNode ({ h_formula_data_node = pt; } as h_data) ->
      if mem pt root_aliases then Some (CF.HEmp, [h_data])
      else None
    | _ -> None
  in
  let n_f, root_node = trans_heap_formula f_h_f f in
  n_f, root_node

let is_consistent_node_list nodes = 
  match nodes with
  | [] -> true
  | n::ns -> List.for_all (fun d -> 
      (eq_str d.CF.h_formula_data_name n.CF.h_formula_data_name) &&
      (List.length n.CF.h_formula_data_arguments == List.length d.CF.h_formula_data_arguments)) ns

let norm_node_list nodes =
  match nodes with
  | [] -> failwith "Unexpected empty node list."
  | n::_ ->
    let n_args = CP.fresh_spec_vars n.CF.h_formula_data_arguments in
    let sst_list = List.map (fun n -> List.combine n.CF.h_formula_data_arguments n_args) nodes in
    let norm_root = { n with CF.h_formula_data_arguments = n_args; } in
    norm_root, sst_list
  
let rec find_common_node_chain root (fs: CF.formula list) =
  let residue_fs, root_node_list = List.split (List.map (find_heap_node root) fs) in
  if List.exists is_empty root_node_list then (fs, [])
  else if List.exists (fun ns -> List.length ns > 1) root_node_list then
    failwith "There is a formula which has more than one root nodes."
  else 
    let root_node_list = List.map List.hd root_node_list in
    if not (is_consistent_node_list root_node_list) then
      failwith "The list of root nodes is not consistent."
    else
      let root_node, sst_list = norm_node_list root_node_list in
      let root_node = { root_node with CF.h_formula_data_node = root } in
      let norm_fs = List.map (fun (f, sst) -> CF.subst_all sst f) (List.combine residue_fs sst_list) in
      List.fold_left (fun (fs, node_chain) arg -> 
          let n_fs, arg_node_chain = find_common_node_chain arg fs in
          n_fs, (node_chain @ arg_node_chain)) 
        (norm_fs, [CF.DataNode root_node]) (List.filter CP.is_node_typ root_node.CF.h_formula_data_arguments)

let find_common_node_chain root (fs: CF.formula list) =
  let pr1 = !CP.print_sv in
  let pr2 = pr_list !CF.print_formula in
  let pr3 = pr_list !CF.print_h_formula in
  let pr4 = fun (_, h_l) -> pr3 h_l in
  Debug.no_2 "find_common_node_chain" pr1 pr2 (* (pr_pair pr2 pr3) *) pr4
    find_common_node_chain root fs

(*******************)
(* UTILS FOR LEMMA *)
(*******************)
let is_not_global_hp_def prog i =
  try
    let todo_unk = C.look_up_hp_def_raw prog.C.prog_hp_decls i 
    in false
  with _ -> true

let is_not_global_rel prog i =
  try
    let todo_unk = C.look_up_rel_def_raw (prog.C.prog_rel_decls # get_stk) i 
    in false
  with _ -> true

let univ_vars_of_lemma l_head = 
  let h, p, vp, _, _,_ = CF.split_components l_head in
  let pvars = MCP.mfv p in
  let pvars = List.filter (fun (CP.SpecVar (_,id,_)) -> 
    not (id = Globals.cyclic_name || 
         id = Globals.acyclic_name || 
         id = Globals.concrete_name || 
         id = Globals.set_comp_name)) pvars in (* ignore cyclic & acyclic rels *)
  let hvars = CF.h_fv h in
  let univ_vars = Gen.BList.difference_eq CP.eq_spec_var pvars hvars in 
  Gen.BList.remove_dups_eq CP.eq_spec_var univ_vars

let mater_vars_of_lemma prog l_head l_body = 
  let args = CF.fv_simple_formula l_head in 
  let m_vars = Astsimp.find_materialized_prop args [] l_body in
  let m_vars = List.map (fun m -> 
    let vs = m.C.mater_target_view in
    let vs2 = List.filter (fun v -> (is_not_global_rel prog v) && (is_not_global_hp_def prog v)) vs in
    (m, vs, vs2)) m_vars in
  let m_vars = List.filter (fun (m, vs, vs2) -> vs == [] || vs2 != []) m_vars in
  let m_vars = List.map (fun (m, vs, vs2) -> { m with C.mater_target_view = vs2 }) m_vars in
  m_vars

(* Adapted from Astsimp.trans_one_coercion_x *)
let mk_lemma prog l_name l_is_classic l_ivars l_itypes l_kind l_type l_head l_body pos =
  let iobj = new Globals.inf_obj_sub in
  let () = iobj # set_list l_itypes in
  { C.coercion_type = l_type;
    C.coercion_exact = l_is_classic;
    C.coercion_name = l_name;
    C.coercion_head = l_head;
    C.coercion_head_norm = l_head (* CF.mkTrue (CF.mkNormalFlow ()) pos *);
    C.coercion_body = l_body; 
    C.coercion_body_norm = CF.struc_formula_of_formula l_body (* (CF.mkTrue (CF.mkNormalFlow ()) pos) *) pos;
    C.coercion_impl_vars = [];
    C.coercion_univ_vars = univ_vars_of_lemma l_head;
    C.coercion_infer_vars = l_ivars;
    C.coercion_infer_obj = iobj;
    C.coercion_fold_def = new Gen.mut_option;
    C.coercion_head_view = Astsimp.find_view_name l_head Globals.self pos;
    C.coercion_body_view = Astsimp.find_view_name l_body Globals.self pos;
    C.coercion_body_pred_list = CF.extr_pred_list l_body;
    C.coercion_mater_vars = mater_vars_of_lemma prog l_head l_body;
    C.coercion_case = C.case_of_coercion l_head l_body;
    C.coercion_type_orig = None;
    C.coercion_kind = l_kind;
    C.coercion_origin = LEM_GEN; }
