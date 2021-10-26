#include "xdebug.cppo"
module CP = Cpure
module CF = Cformula
module MCP = Mcpure

open Globals
open VarGen
open Tid
open Cast
open Cprinter
open Gen

let eq_str s1 s2 = (String.compare s1 s2) = 0

(* Auxiliary methods *)
let diff = Gen.BList.difference_eq CP.eq_spec_var
let subset = Gen.BList.subset_eq CP.eq_spec_var
let remove_dups = Gen.BList.remove_dups_eq CP.eq_spec_var
let mem = Gen.BList.mem_eq CP.eq_spec_var

let rec partition_by_key key_of key_eq ls = 
  match ls with
  | [] -> []
  | e::es ->
    let ke = key_of e in 
    let same_es, other_es = List.partition (fun e -> key_eq ke (key_of e)) es in
    (ke, e::same_es)::(partition_by_key key_of key_eq other_es)

let rec partition_eq eq ls = 
  match ls with
  | [] -> []
  | e::es -> 
    let eq_es, neq_es = List.partition (eq e) es in
    (e::eq_es)::(partition_eq eq neq_es)

(* Stack of nondet vars *)
let nondet_vars_stk: CP.spec_var Gen.stack = new Gen.stack

let is_nondet_cond f =
  (* let svf = CP.fv f in *)
  (* Gen.BList.overlap_eq CP.eq_spec_var svf (nondet_vars_stk # get_stk) *)
  CP.has_nondet_cond f
  
let is_nondet_cond f =
  let pr = !CP.print_formula in
  Debug.no_1 "is_nondet_cond" pr string_of_bool is_nondet_cond f

let is_nondet_var sv = 
  Gen.BList.mem_eq CP.eq_spec_var sv (nondet_vars_stk # get_stk)

let print_ret_trel rel = 
  string_of_trrel_assume (rel.ret_ctx, rel.termr_lhs, rel.termr_rhs)

let print_call_trel_debug rel = 
  string_of_turel_debug (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)

let print_call_trel rel = 
  string_of_turel_assume (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)

let compare_trel r1 r2 = compare r1.trel_id r2.trel_id

let eq_trel r1 r2 = r1.trel_id == r2.trel_id

let update_call_trel rel ilhs irhs = 
  { rel with
    termu_lhs = ilhs;  
    termu_rhs = irhs; }

(* let string_of_tntrel = function                     *)
(*   | Ret rrel -> "@Return: " ^ (print_ret_trel rrel) *)
(*   | Call crel -> "@Call: " ^ (print_call_trel crel) *)

let subst_cond_with_ann params ann cond =
  match ann with
  | CP.TermU uid
  | CP.TermR uid ->
    let args = uid.CP.tu_args in
    CP.subst_term_avoid_capture (List.combine params args) cond
  | _ -> cond

(* TNT Case Spec *)
type tnt_case_spec = 
  | Sol of (CP.term_ann * CP.exp list)
  | Unknown of CP.term_cex option
  | Cases of (CP.formula * tnt_case_spec) list

let is_Loop sp = 
  match sp with
  | Sol (CP.Loop _, _) -> true
  | _ -> false

let is_cex_MayLoop sp = 
  match sp with
  | Sol (CP.MayLoop cex, _) -> not (is_None cex)
  | _ -> false

let is_emp_MayLoop sp = 
  match sp with
  | Sol (CP.MayLoop cex, _) -> is_None cex
  | _ -> false

let is_Term sp = 
  match sp with
  | Sol (CP.Term, _) -> true
  | _ -> false

let rec pr_tnt_case_spec (spec: tnt_case_spec) = 
  match spec with
  | Cases cl ->
    pr_args (Some("V",1)) (Some "A") "case " "{" "}" "" 
      (
        fun (c, s) -> wrap_box ("B",0) (pr_op_adhoc 
                                          (fun () -> pr_pure_formula c) " -> " )
            (fun () -> pr_tnt_case_spec s; fmt_string ";")
      ) cl 
  | Unknown cex -> 
    (* fmt_string "Unk" *) 
    (* fmt_string "requires MayLoop ensures true" *)
    fmt_string "requires ";
    pr_var_measures (MayLoop cex, [], []);
    fmt_string " ensures true"
  | Sol (ann, rnk) ->
    match ann with
    | CP.Loop _ -> 
      (* fmt_string "requires Loop ensures false" *)
      fmt_string "requires ";
      pr_var_measures (ann, [], []);
      fmt_string " ensures false"
    | _ -> 
      fmt_string "requires ";
      pr_var_measures (ann, rnk, []);
      fmt_string " ensures true"

let print_tnt_case_spec = poly_string_of_pr pr_tnt_case_spec

let is_base_rank rnk =
  match rnk with
  | [] -> true
  | c::[] -> CP.is_nat c
  | c::p::[] -> (CP.is_nat c) && (CP.is_nat p)
  | _ -> false

let eq_base_rank rnk1 rnk2 =
  match rnk1, rnk2 with
  | [], [] -> true
  | c1::[], c2::[] -> CP.eq_num_exp c1 c2
  | c1::_::[], c2::_::[] -> CP.eq_num_exp c1 c2
  | _ -> false

let eq_tnt_case_spec sp1 sp2 =
  match sp1, sp2 with
  (* Do not merge MayLoop with cex *)
  | Unknown None, Unknown None -> true
  | Unknown None, Sol (CP.MayLoop None, _) -> true
  | Sol (CP.MayLoop None, _), Unknown None -> true
  | Sol (ann1, rnk1), Sol (ann2, rnk2) ->
    begin match ann1, ann2 with
      | CP.Loop _, CP.Loop _ -> true
      | CP.MayLoop None, CP.MayLoop None -> true
      (* | CP.Term, CP.Term ->                          *)
      (*   (* is_base_rank rnk1 && is_base_rank rnk2 *) *)
      (*   eq_base_rank rnk1 rnk2                       *)
      | _ -> false
    end
  | _ -> false

(* Utilities for Path Traces *)
type path_trace = (CP.spec_var * bool) list

type and_or_tree = 
  | TSgl of path_trace
  | TSeq of and_or_tree list
  | TPar of and_or_tree list

let print_path_trace pt =
  pr_list (fun (v, b) -> if b then (!CP.print_sv v) else "!" ^ (!CP.print_sv v)) pt

let rec print_and_or_tree t =
  match t with 
  | TSgl pt -> "TSgl " ^ (print_path_trace pt)
  | TSeq seq -> "TSeq {" ^ (pr_list print_and_or_tree seq) ^ "}"
  | TPar par -> "TPar [" ^ (pr_list print_and_or_tree par) ^ "]"

(* Tracking path of a formula *)
let path_of_formula f =
  let ls = CP.split_conjunctions f in
  let bvs = List.concat (List.map (fun f -> opt_to_list (CP.getBVar f)) ls) in
  let bvs = Gen.BList.remove_dups_eq (fun (v1, _) (v2, _) -> CP.eq_spec_var v1 v2) bvs in
  bvs

let eq_path_elem (v1, s1) (v2, s2) =
  (CP.eq_spec_var v1 v2) && (s1 == s2)  

(* p1 and p2 are in the same sequence *)   
let eq_path p1 p2 =
  Gen.BList.list_setequal_eq eq_path_elem p1 p2

(* p1 is sub-path of p2 *)  
let is_sub_path p1 p2 = 
  (Gen.BList.subset_eq eq_path_elem p2 p1) &&
  (List.length p1 > List.length p2)

let rec eq_path_formula f1 f2 =
  let p1 = path_of_formula f1 in
  let p2 = path_of_formula f2 in
  eq_path p1 p2

(* This method assumes that the path_traces is sorted by length *)     
let rec and_or_tree_of_path_traces path_traces =
  match path_traces with
  | [] -> TSgl []
  | p::ps ->
    let p_len = List.length p in
    let same_len_p, others = List.partition (fun q -> (List.length q) == p_len) ps in
    let eq_path_grps = partition_eq eq_path (p::same_len_p) in 
    (* Group of same path traces *)
    match eq_path_grps with
    | [] -> and_or_tree_of_path_traces others
    | grp::[] -> and_tree_of_path_traces grp others
    | _ -> TPar (List.map (fun grp -> and_tree_of_path_traces grp others) eq_path_grps)

and and_tree_of_path_traces same_path_grp other_traces = 
  match same_path_grp with
  | [] -> and_or_tree_of_path_traces other_traces
  | s::_ -> 
    let sub_path_traces = List.filter (fun p -> is_sub_path p s) other_traces in
    let sgl_path_grp = List.map (fun p -> TSgl p) same_path_grp in
    match sub_path_traces with
    | [] -> begin match sgl_path_grp with
        | [] -> TSgl []
        | s::[] -> s
        | _ -> TSeq sgl_path_grp end
    | _ -> TSeq (sgl_path_grp @ [and_or_tree_of_path_traces sub_path_traces])

let and_or_tree_of_path_traces path_traces =
  let sorted_path_traces = List.sort (fun p1 p2 -> 
      compare (List.length p1) (List.length p2)) path_traces in
  and_or_tree_of_path_traces sorted_path_traces

(* Specification-related stuffs *)  
let rec is_infer_term sf = match sf with
  | CF.EList el -> List.exists (fun (lbl, sf) -> x_add_1 is_infer_term sf) el
  | CF.EInfer ei -> ei.CF.formula_inf_obj # is_term
  | _ -> false

let is_infer_term sf =
  let pr = string_of_struc_formula in
  Debug.no_1 "is_infer_term" pr string_of_bool is_infer_term sf

let is_infer_term_scc scc =
  List.exists (fun proc -> x_add_1 is_infer_term (proc.proc_stk_of_static_specs # top)) scc

let is_infer_term_scc scc = 
  let pr = pr_list (fun proc -> proc.proc_name) in
  Debug.no_1 "is_infer_term_scc" pr string_of_bool
    is_infer_term_scc scc

let is_prim_type sv = 
  let typ = CP.type_of_spec_var sv in
  match typ with
  | Int | Bool -> true
  | _ -> false

let collect_prim_args_base_formula ptr_vars h p =
  let aliases = MCP.ptr_equations_without_null p in
  let aset = CP.EMapSV.build_eset aliases in
  let f_h_f _ h_f =
    match h_f with
    | CF.DataNode ({ CF.h_formula_data_node = pt; CF.h_formula_data_arguments = args;})
    | CF.ViewNode ({ CF.h_formula_view_node = pt; CF.h_formula_view_arguments = args;}) ->
      let is_mem_ptr_vars = 
        if mem pt ptr_vars then true
        else
          let pt_aliases = CP.EMapSV.find_equiv_all_new pt aset in
          List.exists (fun pta -> mem pta ptr_vars) pt_aliases
      in
      if is_mem_ptr_vars then 
        let prim_args = List.filter is_prim_type args in 
        Some (h_f, args)
      else Some (h_f, [])
    | _ -> None
  in
  let prim_v = snd (CF.trans_h_formula h () f_h_f voidf2 (List.concat)) in
  remove_dups prim_v

let rec collect_prim_args_formula ptr_vars (f: CF.formula) =
  match f with
  | CF.Base { CF.formula_base_heap = h; CF.formula_base_pure = p } ->
    let prim_v = collect_prim_args_base_formula ptr_vars h p in
    f, prim_v
  | CF.Exists ({ CF.formula_exists_heap = h; CF.formula_exists_pure = p } as fe) -> 
    let prim_v = collect_prim_args_base_formula ptr_vars h p in
    (* prim_v will be moved to formula_struc_implicit_inst  *)
    (* to visible in both pre- and post-condition           *)
    (* CF.Exists { fe with CF.formula_exists_qvars = diff fe.CF.formula_exists_qvars prim_v }, *)
    (* prim_v                                                                                  *)
    let bnd_prim_v, free_prim_v = List.partition (fun v -> mem v fe.CF.formula_exists_qvars) prim_v in
    if is_empty bnd_prim_v then f, prim_v
    else
      let fresh_bnd_prim_v = CP.fresh_spec_vars bnd_prim_v in
      let n_f = CF.Exists { fe with CF.formula_exists_qvars = diff fe.CF.formula_exists_qvars bnd_prim_v } in
      let n_f = CF.subst_avoid_capture bnd_prim_v fresh_bnd_prim_v n_f in
      n_f, fresh_bnd_prim_v @ free_prim_v
  | CF.Or ({ CF.formula_or_f1 = f1; CF.formula_or_f2 = f2 } as fo ) ->
    let n_f1, prim_v1 = collect_prim_args_formula ptr_vars f1 in
    let n_f2, prim_v2 = collect_prim_args_formula ptr_vars f2 in
    CF.Or { fo with CF.formula_or_f1 = n_f1; CF.formula_or_f2 = n_f2; },
    remove_dups (prim_v1 @ prim_v2)

let rec collect_prim_args_struc_formula ptr_vars f =
  let rec_f = collect_prim_args_struc_formula ptr_vars in
  match f with
  | CF.EList el ->
    let n_el, prim_v_lst = List.split (List.map (fun (sld, sf) ->
      let n_sf, prim_v = rec_f sf in ((sld, n_sf), prim_v)) el) in
    CF.EList n_el, remove_dups (List.concat prim_v_lst)
  | CF.ECase ec ->
    let n_fcb, prim_v_lst = List.split (List.map (fun (c, sf) -> 
      let n_sf, prim_v = rec_f sf in ((c, n_sf), prim_v)) ec.CF.formula_case_branches)
    in
    CF.ECase { ec with CF.formula_case_branches = n_fcb }, 
    remove_dups (List.concat prim_v_lst)
  | CF.EInfer ei ->
    let n_cont, prim_v = rec_f ei.CF.formula_inf_continuation in
    CF.EInfer { ei with CF.formula_inf_continuation = n_cont }, prim_v
  | CF.EAssume _ ->
    (* To avoid clashing with the implicit primitive args *) 
    CF.rename_struc_bound_vars f, []
  | CF.EBase eb ->
    let n_base, prim_v_base = collect_prim_args_formula ptr_vars eb.CF.formula_struc_base in
    let n_cont, prim_v_cont =
      match eb.CF.formula_struc_continuation with
      | None -> None, []
      | Some sf -> let n_sf, prim_v = rec_f sf in Some n_sf, prim_v
    in
    CF.EBase { eb with
        CF.formula_struc_base = n_base;
        CF.formula_struc_continuation = n_cont;
        CF.formula_struc_implicit_inst = remove_dups (eb.CF.formula_struc_implicit_inst @ prim_v_base);
        CF.formula_struc_exists = diff eb.CF.formula_struc_exists prim_v_base; }, 
    remove_dups (prim_v_base @ prim_v_cont)

let collect_prim_args_struc_formula ptr_vars f =
  let pr1 = !CF.print_struc_formula in
  let pr2 = !CP.print_svl in
  Debug.no_2 "collect_prim_args_struc_formula" pr1 pr2 (pr_pair pr1 pr2)
    (fun _ _ -> collect_prim_args_struc_formula ptr_vars f) f ptr_vars

let add_term_relation_proc prog proc = 
  let is_primitive = not (proc.proc_is_main) in
  if is_primitive then ()
  else
    let spec = proc.proc_stk_of_static_specs # top in
    let fname = unmingle_name proc.proc_name in
    let args = List.map (fun (t, v) -> CP.SpecVar (t, v, Unprimed)) proc.proc_args in
    let prim_params, ptr_params = List.partition is_prim_type args in
    let n_spec, impl_params = collect_prim_args_struc_formula ptr_params spec in
    let params = prim_params @ impl_params in
    (* (* NOTE: We should not rely on collect_important_vars_in_spec *)   *)
    (* let imp_spec_vars = CF.collect_important_vars_in_spec true spec in *)
    (* let params = imp_spec_vars @ params  in                            *)
    (* let params = List.filter (fun sv ->                                *)
    (*     match sv with                                                  *)
    (*     | CP.SpecVar(t, _, _) -> (match t with                         *)
    (*         | Int | Bool -> true                                       *)
    (*         | _ -> false)) params in                                   *)
    let pos = proc.proc_loc in

    let utpre_name = fname ^ "pre" in
    let utpost_name = fname ^ "post" in

    let utpre_decl = {
      ut_name = utpre_name;
      ut_params = params;
      ut_is_pre = true;
      ut_pos = pos } in
    let utpost_decl = { utpre_decl with
                        ut_name = utpost_name;
                        ut_is_pre = false; } in

    let () = Debug.ninfo_hprint (add_str "added to UT_decls" (pr_list pr_id)) [utpre_name; utpost_name] no_pos in
    (* let () = ut_decls # push_list [utpre_decl; utpost_decl] in *)
    let () = prog.prog_ut_decls <- ([utpre_decl; utpost_decl] @ prog.prog_ut_decls) in

    let uid = {
      CP.tu_id = 0;
      CP.tu_sid = fname;
      CP.tu_fname = fname;
      CP.tu_call_num = proc.proc_call_order;
      CP.tu_args = List.map (fun v -> CP.mkVar v pos) params;
      CP.tu_cond = CP.mkTrue pos;
      CP.tu_icond = CP.mkTrue pos;
      CP.tu_sol = None;
      CP.tu_pos = pos; } in
    let n_spec = CF.norm_struc_with_lexvar is_primitive true (Some uid) n_spec in
    proc.proc_stk_of_static_specs # push_pr x_loc n_spec

let add_term_relation_scc prog scc =
  List.iter (fun proc -> add_term_relation_proc prog proc) scc

let partition_trels_by_proc trrels turels =
  let fn_trrels = 
    let key_of r = (r.termr_fname, r.termr_rhs_params) in
    let key_eq (k1, _) (k2, _) = String.compare k1 k2 == 0 in  
    partition_by_key key_of key_eq trrels 
  in
  (* let fn_cond_w_ids = List.map (fun (fn, trrels) ->                                                        *)
  (*   let fn_turels = List.find_all (fun r -> String.compare (fst fn) r.termu_fname == 0) turels in          *)
  (*   let params = snd fn in                                                                                 *)
  (*   (fn, List.map (fun c -> tnt_fresh_int (), c) (solve_trrel_list params trrels fn_turels))) fn_trrels in *)
  let fn_turels = 
    let key_of r = (r.termu_fname, List.concat (List.map CP.afv (CP.args_of_term_ann r.termu_lhs))) in
    let key_eq (k1, _) (k2, _) = String.compare k1 k2 == 0 in  
    partition_by_key key_of key_eq turels 
  in
  let fn_rels, rem_fn_turels = List.fold_left (fun (fn_rels, rem_fn_turels) (rfn, trrels) ->
      let turels, rem_fn_turels = List.partition (fun (ufn, _) -> eq_str (fst rfn) (fst ufn)) rem_fn_turels in
      let turels = List.concat (List.map snd turels) in
      fn_rels @ [(rfn, trrels, turels)], rem_fn_turels) ([], fn_turels) fn_trrels in
  let fn_rels = fn_rels @ (List.map (fun (fn, turels) -> (fn, [], turels)) rem_fn_turels) in
  fn_rels

(* For Nondet handling *)
let collect_nondet_rel_trrels trrels = 
  let nondet_rels = List.concat (List.map (fun tr -> CP.collect_nondet_rel tr.ret_ctx) trrels) in
  Gen.BList.remove_dups_eq CP.eq_nondet_rel nondet_rels

let string_of_nondet_pos p = 
  (string_of_int p.start_pos.Lexing.pos_lnum) ^ "_" ^
  (string_of_int (p.start_pos.Lexing.pos_cnum - p.start_pos.Lexing.pos_bol))

let trans_nondet_formula prog f = 
  let f_bf () bf =
    let (pf, il) = bf in
    match pf with
    | CP.RelForm (sv, args, pos) -> 
      if CP.is_nondet_sv sv then
        let svn = CP.name_of_spec_var sv in
        match args with
        | e::[] ->
          let nd_rel_def = look_up_rel_def_raw (prog.prog_rel_decls # get_stk) svn in
          (try
             let param = List.hd nd_rel_def.rel_vars in
             let svp = CP.SpecVar (CP.type_of_spec_var param, svn ^ (string_of_nondet_pos pos), Unprimed) in
             let nd_eq = CP.Eq ((CP.Var (svp, pos)), e, pos) in
             Some ((nd_eq, il), [(svp, pos)])
           with _ -> report_error pos ("Mismatch number of arguments in the nondet relation " ^ svn))
        | _ -> report_error pos ("Mismatch number of arguments in the nondet relation " ^ svn)
      else Some (bf, [])
    | _ -> Some (bf, [])
  in
  let f_arg () _ = () in
  CP.trans_formula f () (nonef2, f_bf, nonef2) (f_arg, f_arg, f_arg) List.concat

let trans_nondet_ctx prog ctx pos = 
  (* nondet_int__pos(v) --> nondet_int__pos = v & nondet_int__pos = nondet_int__pos' *)
  let trans_ctx, nd_vars = trans_nondet_formula prog ctx in
  let nd_vars = Gen.BList.remove_dups_eq 
      (fun (v1, _) (v2, _) -> CP.eq_spec_var v1 v2) nd_vars in
  let trans_ctx = List.fold_left (fun ctx (nd, ndp) ->
      let primed_nd = CP.to_primed nd in
      let eqf = CP.BForm ((CP.mkEq_b (CP.Var (nd, ndp)) (CP.Var (primed_nd, ndp)) pos, None)) in
      CP.mkAnd ctx eqf pos
    ) trans_ctx nd_vars in
  trans_ctx, nd_vars

let trans_nondet_ctx_trrel prog trrel =
  let pos = trrel.termr_pos in
  let ctx = trrel.ret_ctx in
  let trans_ctx, nd_vars = trans_nondet_ctx prog ctx pos in
  { trrel with ret_ctx = trans_ctx; }, nd_vars

let trans_nondet_trels_proc prog trrels turels = 
  let trans_trrels, nd_vars_lst = List.split (List.map (trans_nondet_ctx_trrel prog) trrels) in
  let nd_vars = Gen.BList.remove_dups_eq (fun (v1, _) (v2, _) -> CP.eq_spec_var v1 v2) 
      (List.concat nd_vars_lst) in
  let nd_sv_lst = List.map fst nd_vars in
  let nd_args = List.map (fun (nd, ndp) -> CP.Var (nd, ndp)) nd_vars in
  let primed_nd_args = List.map (fun (nd, ndp) -> CP.Var (CP.to_primed nd, ndp)) nd_vars in

  let trans_trrels_w_rname = List.map (
      fun tr -> { tr with
                  termr_lhs = List.map (fun ann -> CP.add_args_term_ann ann primed_nd_args) tr.termr_lhs;
                  termr_rhs = CP.add_args_term_ann tr.termr_rhs nd_args; 
                  termr_rhs_params = tr.termr_rhs_params @ nd_sv_lst; }, tr.termr_fname) trans_trrels
  in
  let trans_trrels, rname = List.split trans_trrels_w_rname in

  let trans_turels_w_uname = List.map (
      fun tu -> { tu with
                  call_ctx = fst (trans_nondet_ctx prog tu.call_ctx tu.termu_pos);
                  termu_lhs = CP.add_args_term_ann tu.termu_lhs nd_args;
                  termu_rhs = CP.add_args_term_ann tu.termu_rhs primed_nd_args;
                  termu_rhs_params = tu.termu_rhs_params @ nd_sv_lst;
                  termu_rhs_args = tu.termu_rhs_args @ primed_nd_args; }, tu.termu_fname) turels 
  in
  let trans_turels, uname = List.split trans_turels_w_uname in

  let ut_names = List.concat (List.map (fun id -> [id ^ "pre"; id ^ "post"])
                                (Gen.BList.remove_dups_eq eq_str (rname @ uname))) in

  let trans_ut_decls = List.fold_left (fun acc ut_decl ->
      let trans_ut_decl = 
        if (Gen.BList.mem_eq eq_str ut_decl.ut_name ut_names) then
          { ut_decl with ut_params = ut_decl.ut_params @ nd_sv_lst; }
        else ut_decl
      in acc @ [trans_ut_decl]
    ) [] prog.prog_ut_decls in
  let () = prog.prog_ut_decls <- trans_ut_decls in
  let () = nondet_vars_stk # push_list (nd_sv_lst @ (List.map CP.to_primed nd_sv_lst)) in
  trans_trrels, trans_turels

let trans_nondet_trels prog trrels turels =
  let trel_lst = List.map (fun (_, tr, tu) -> trans_nondet_trels_proc prog trrels turels) 
      (partition_trels_by_proc trrels turels) in
  let trrel_lst, turel_lst = List.split trel_lst in
  List.concat trrel_lst, List.concat turel_lst

