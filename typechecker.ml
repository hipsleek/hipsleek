#include "xdebug.cppo"
open VarGen
module DD = Debug
open Globals
open Wrapper
open Others
open Stat_global
open Global_var
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Cast
open Gen.Basic
open Perm
(* open Label_only *)
open Label
module CF = Cformula
module MCP = Mcpure
module SV = Solver
module CP = Cpure
module CVP = CvpermUtils
module VP = Vperm
module TP = Tpdispatcher
module PTracer = Prooftracer
module I = Iast
(* module LP = Lemproving *)
(* module Inf = Infer *)
(* module AS = Astsimp *)
module CEQ = Checkeq
module M = Lexer.Make(Token.Token)
module H = Hashtbl
module Synt = Synthesis
module LO2 = Label_only.Lab2_List
module SB = Songbird
(* module FP = Fixpoint *)

let pr_sv = Cprinter.string_of_spec_var
let pr_context = Cprinter.string_of_context
let pr_pf = Cprinter.string_of_pure_formula
let pr_failesc_ctx = Cprinter.string_of_list_failesc_context

let store_label = new store LO2.unlabelled LO2.string_of
let save_flags = ref (fun ()->()) ;;
let restore_flags = ref (fun ()->());;
let parse_flags = ref (fun (s:(string*(flags option)) list)-> ());;

let phase_infer_ind = ref false
let repair_proc = ref None

let log_spec = ref ""
(* checking expression *)
let flow_store = ref ([] : CF.flow_store list)

let num_para = ref (1)
let sort_input = ref false
let webserver = ref false
let proc_used_names = ref ([]:ident list)

let pr_ctx = Cprinter.string_of_list_failesc_context
let pr_formula = Cprinter.string_of_formula

let update_iprog_exp_defns iprog cprog_exp_defns =
  let iprog_exp_defns = iprog.Iast.prog_exp_decls in
  let n_iprog_exp_dfs i_exp_defn =
      try
        let c_exp_defn = List.find (fun c_exp_defn ->
            String.compare c_exp_defn.Cast.exp_name i_exp_defn.Iast.exp_name == 0)
            cprog_exp_defns in
        let exp_body = c_exp_defn.exp_body in
        let () = x_tinfo_hp (add_str "exp: " Cprinter.string_of_formula_exp)
            exp_body no_pos in
        let exp_body = Cpure.norm_exp exp_body in
        let () = x_tinfo_hp (add_str "exp: " Cprinter.string_of_formula_exp)
            exp_body no_pos in
        let n_exp = Cpure.translate_exp_to_ipure exp_body in
        {i_exp_defn with Iast.exp_body = Iast.ExpForm n_exp}
      with Not_found -> i_exp_defn
  in
  let n_iprog_exp_dfs = List.map n_iprog_exp_dfs iprog_exp_defns in
  {iprog with prog_exp_decls = n_iprog_exp_dfs}

(* global option to switch on/off the simplification of context after symbolic execution *)
let simplify_context = ref false

let scc_proc_sel_hps = ref ([]: CP.spec_var list)
let scc_proc_sel_post_hps = ref ([]: CP.spec_var list)

let parallelize num =
  num_para := num

let check_varperm (prog : prog_decl) (proc : proc_decl) (spec: CF.struc_formula) (ctx : CF.context) (pre_f:CF.formula) pos =
  x_dinfo_zp (lazy ("\ncheck_specs: EBase: checking VarPerm in the precondition:  \n" ^ (Cprinter.string_of_struc_formula spec) ^ "\n")) pos;
  let zero_vars = [] in
  let () = if (zero_vars!=[]) then
      report_error pos ("\ncheck_specs: EBase: unexpected @zero VarPerm in the pre-condition")
  in
  let val_vars = [] in
  let full_vars = [] in
  let tmp = Gen.BList.intersect_eq CP.eq_spec_var_ident val_vars full_vars in
  let () = if (tmp!=[]) then
      report_error pos ("\ncheck_specs: EBase: duplicated VarPerm: " ^ (Cprinter.string_of_spec_var_list tmp))
  in
  (*Ensure that all arguments have corresponding varialbe permissions*)
  let farg_types, farg_names = List.split proc.proc_args in
  let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
  let val_vars2 = [] in
  let full_vars2 = [] in
  let all_vars2 = full_vars2@val_vars2 in
  (*@zero of the main thread*)
  let zero_vars = Gen.BList.difference_eq CP.eq_spec_var_ident farg_spec_vars all_vars2 in
  let ctx = CF.transform_context (fun es -> CF.Ctx {es with CF.es_var_zero_perm = zero_vars}) ctx in
  (*drop VarPerm in the main thread*)
  (* let ext_base = CF.drop_varperm_formula pre_f in *)
  let ext_base = pre_f in
  x_dinfo_zp (lazy ("\n check_specs: EBase: checking VarPerm in the precondition: Done. " ^ "\n ### zero_vars = " ^ (Cprinter.string_of_spec_var_list zero_vars) ^ "\n")) pos;
  (ctx,ext_base)

let pre_ctr = new Gen.counter 0
let post_ctr = new Gen.counter 0
let prepost_ctr = new Gen.counter 0

let check_var_read_perm_type msg prog ctx pos v t perm_ty =
  if !ann_vp then
    let sv = (CP.SpecVar (t, v, Unprimed)) in
    (* let sv = CP.sp_rm_prime sv in *)
    (* let v = CP.ident_of_spec_var sv in *)
    let lend_f = VP.formula_of_vperm_anns [(perm_ty, [sv])] in
    let lend_f = CF.set_flow_in_formula_override
        { CF.formula_flow_interval = !norm_flow_int; CF.formula_flow_link = None } lend_f
    in
    let vperm_res, _ = SV.heap_entail_list_failesc_context_init prog false ctx lend_f None None None pos None in
    if not (CF.isSuccessListFailescCtx_new vperm_res) then
      let msg = (v ^ " does not have @lend/@full permission to read "^msg) in
      (Debug.print_info ("(" ^ (Cprinter.string_of_label_list_failesc_context vperm_res) ^ ") ") msg pos;
       Debug.print_info ("(Cause of ParCase Failure)") (Cprinter.string_of_failure_list_failesc_context vperm_res) pos;
       Err.report_error { Err.error_loc = pos; Err.error_text = msg })

let check_var_read_perm ?(msg="") prog ctx pos v t =
  check_var_read_perm_type msg prog ctx pos v t VP_Lend

let check_var_read_perm_frac f ?(msg="") prog ctx pos v t =
  check_var_read_perm_type msg prog ctx pos v t (VP_Frac f)

(* WN : need to trace check_specs_infer with Debug.no_; can we add and later check infer[@classic] etc with wrap_ *)

let rec check_specs_infer (prog : prog_decl) (proc : proc_decl)
    (ctx : CF.context) (spec_list:CF.struc_formula) e0 do_infer:
  CF.struc_formula * (CF.formula list)
     * ((CP.rel_cat * CP.formula * CP.formula) list) * (CF.hprel list)
     * (CP.spec_var list) * (CP.spec_var list)
     * ((CP.spec_var * int list) * CP.xpure_view) list * bool =
  let () = pre_ctr # reset in
  let () = post_ctr # reset in
  let f = wrap_proving_kind PK_Check_Specs
      (x_add check_specs_infer_a0 prog proc ctx e0 do_infer) in
  (fun _ -> f spec_list) spec_list

(* Termination *)
(* This procedure to check that Term[x1,x2,...,xn] are bounded by x1,x2,...,xn>=0 *)
(* In case of failure, please put message into term_msg stack *)
(* The resulting ctx may contain inferred constraint *)
and check_bounded_term_x prog ctx post_pos =
  let check_bounded_one_measures m es =
    (* Termination: filter the exp of phase variables
     * (their value non-negative numbers in default) *)
    let m = List.filter (fun e ->
        not (Gen.BList.overlap_eq CP.eq_spec_var (CP.afv e) prog.prog_logical_vars)) m in
    if m == [] then (es, CF.SuccCtx [(CF.Ctx es)])
    else begin
      let m_pos = match m with
        | [] -> no_pos
        | e::_ -> CP.pos_of_exp e
      in
      let ctx = CF.Ctx es in
      let bnd_formula_l = List.map (fun e ->
          CP.mkPure (CP.mkGte e (CP.mkIConst 0 m_pos) m_pos)) m in
      let bnd_formula = CF.formula_of_pure_formula
          (CP.join_conjunctions bnd_formula_l) m_pos in
      let rs, _ = SV.heap_entail_one_context 12 prog false ctx bnd_formula None None None post_pos in
      let () = x_tinfo_hp (add_str "Result context" !CF.print_list_context) rs no_pos in
      let term_pos = (m_pos, no_pos) in
      let term_res, n_es =
        let f_ctx = CF.formula_of_context ctx in
        if (CF.isFailCtx rs) then
          let tr = (term_pos, None, Some f_ctx, Term.MayTerm_S (Term.Not_Bounded_Measure m)) in
          let err_msg = Term.string_of_term_res tr in
          let () = Term.add_term_err_stk err_msg in
          tr, { es with CF.es_term_err = Some err_msg }
        else
          (term_pos, None, Some f_ctx, Term.Term_S Term.Bounded_Measure),
          es
      in
      let () = x_tinfo_hp (add_str "New es" !CF.print_entail_state) n_es no_pos in
      let () = Term.add_term_res_stk term_res in
      n_es, rs
    end
  in
  let check_bounded_one_measures m es =
    Debug.no_1 "check_bounded_one_measures"
      (pr_list !CP.print_exp) (fun _ -> "")
      (fun _ -> check_bounded_one_measures m es) m
  in

  (* need to perform boundedness check at recursive call *)
  if (!Globals.dis_term_chk || !Globals.dis_bnd_chk || !Globals.term_bnd_pre_flag)
  then (ctx, [])
  else
    let ctx = x_add_1 TermUtils.strip_lexvar_lhs ctx in
    match ctx with
    | CF.Ctx es ->
      let m = match es.CF.es_var_measures with
        | None -> []
        | Some (_, ml, _) -> ml
      in
      let () = x_tinfo_hp (add_str "Measures"
                             (pr_list !CP.print_exp)) m no_pos in
      let () = x_tinfo_hp (add_str "Orig context"
                             !CF.print_context) ctx no_pos in
      let n_es, rs = check_bounded_one_measures m es in
      (CF.Ctx n_es, Infer.collect_rel_list_context rs)
    | CF.OCtx (ctx1, ctx2) ->
      let n_ctx1, rl1 = check_bounded_term prog ctx1 post_pos in
      let n_ctx2, rl2 = check_bounded_term prog ctx2 post_pos in
      (CF.OCtx (n_ctx1, n_ctx2), rl1 @ rl2)

and check_bounded_term prog ctx post_pos =
  let pr = !CF.print_context in
  let pr1 = pr_pair !CF.print_context (pr_list Cprinter.string_of_lhs_rhs) in
  let f = wrap_proving_kind PK_Term_Bnd (check_bounded_term_x prog ctx) in
  Debug.no_1 "check_bounded_term" pr pr1 (fun _ -> f post_pos) ctx

and check_specs_infer_a0 (prog : prog_decl) (proc : proc_decl)
    (ctx : CF.context) e0 do_infer (sp:CF.struc_formula):
  CF.struc_formula * (CF.formula list) *
  ((CP.rel_cat * CP.formula * CP.formula) list) * (CF.hprel list) *
  (CP.spec_var list)* (CP.spec_var list) *
  ((CP.spec_var * int list)  *CP.xpure_view ) list * bool =
  let pr0 = Cprinter.string_of_context in
  let pr1 = Cprinter.string_of_struc_formula in
  let pr1n s = Cprinter.string_of_struc_formula (CF.norm_specs s) in
  let pr2 = add_str "inferred rels" (fun l -> string_of_int (List.length l)) in
  let pr2a = add_str "formulae" (pr_list Cprinter.string_of_formula) in
  let pr2b = add_str "inferred hp rels" (fun l -> string_of_int (List.length l)) in
  let pr4 = Cprinter.string_of_spec_var_list in
  let pr5 = pr_list (pr_pair (pr_pair pr_sv (pr_list string_of_int))
                       Cprinter.string_of_xpure_view) in
  let pr3 = pr_octa pr1 pr2a pr2 pr2b pr4 pr4 pr5 string_of_bool in
  let pr_exp = Cprinter.string_of_exp in
  let arr_as_var_flag = CF.determine_infer_type sp INF_ARR_AS_VAR in
  let field_imm_flag = CF.determine_infer_type sp INF_FIELD_IMM in
  let classic_flag = CF.determine_infer_classic sp in
  let ck_sp x = (check_specs_infer_a prog proc ctx e0 do_infer) x in
  (* CLASSIC: Set classic reasoning for hip with infer[@classic] spec *)
  let fn x = if classic_flag
    then wrap_classic x_loc (Some true) ck_sp x else ck_sp x in
  let fn x =
    if field_imm_flag then wrap_field_imm (Some true) fn x
    else fn x in
  let fn x =
    if arr_as_var_flag then wrap_arr_as_var fn x
    else fn x in
  Debug.no_3 "check_specs_infer" pr0 pr1 pr_exp pr3
    (fun _ _ _ -> fn sp) ctx sp e0

and check_specs_infer_a (prog : prog_decl) (proc : proc_decl) (ctx : CF.context)
    (e0:exp) (do_infer:bool) (spec: CF.struc_formula) :
  CF.struc_formula * (CF.formula list) *
  ((CP.rel_cat * CP.formula * CP.formula) list) *(CF.hprel list) *
  (CP.spec_var list)* (CP.spec_var list) *
  ((CP.spec_var * int list)  *CP.xpure_view ) list * bool =
  let rec helper (ctx : CF.context) (spec: CF.struc_formula):
    CF.struc_formula * (CF.formula list) *
    ((CP.rel_cat * CP.formula * CP.formula) list) *(CF.hprel list) *
    (CP.spec_var list)* (CP.spec_var list) *
    ((CP.spec_var * int list)  *CP.xpure_view) list * bool =
    let pos_spec = CF.pos_of_struc_formula spec in
    let _ = proving_loc # set pos_spec in
    log_spec := (Cprinter.string_of_struc_formula spec) ^ ", Line "
                ^ (string_of_int pos_spec.start_pos.Lexing.pos_lnum);
    let () = x_tinfo_hp (add_str "spec: " Cprinter.string_of_struc_formula) spec no_pos in
    match spec with
    | CF.ECase b ->
      let r =
        List.map (fun (c1, c2) ->
            let nctx = CF.transform_context (SV.combine_es_and prog (MCP.mix_of_pure c1) true) ctx in
            let (new_c2,pre,rel,hprel, sel_hps,sel_post_hps, unk_map,f) = helper nctx c2 in
            (* Thai: Need to generate EBase from pre if necessary *)
            let new_c2 =  if pre !=[] then
                (pre_ctr # inc ; CF.merge_struc_pre new_c2 pre)
              else new_c2 in
            ((c1,new_c2),(rel,f),((hprel, sel_hps),(sel_post_hps,unk_map))))
          b.CF.formula_case_branches in
      let (cbl,fl,hprel_ls) = split3 r in
      let (rel_ls,fl) = List.split fl in
      let rel = List.concat rel_ls in
      let hp_pairs1,hp_pairs2 = List.split hprel_ls in
      let hprels,sel_hps = List.split hp_pairs1 in
      let sel_post_hps,ls_unk_map = List.split hp_pairs2 in
      let hprel = List.concat hprels in
      let sel_hps = List.hd sel_hps in
      let unk_map = List.concat ls_unk_map in
      let br = List.for_all pr_id fl in
      let new_spec = CF.ECase {b with CF.formula_case_branches=cbl} in
      (new_spec,[],rel,hprel, sel_hps, List.concat sel_post_hps, unk_map,br)

    | CF.EBase b ->
      let vs = b.CF.formula_struc_explicit_inst @ b.CF.formula_struc_implicit_inst in
      let () = stk_vars # push_list vs in
      let () = x_tinfo_hp (add_str "Ebase" pr_id) (stk_vars # string_of_no_ln) no_pos in
      x_tinfo_hp (add_str "check_specs: EBase: " pr_context) ctx no_pos;
      (*************************************************************)
      (********* Check permissions variables in pre-condition ******)
      (*************************************************************)
      let has_lexvar = CF.has_lexvar_formula b.CF.formula_struc_base in
      let ctx,ext_base = if (!Globals.ann_vp) && (not has_lexvar) then
          check_varperm prog proc spec ctx b.CF.formula_struc_base pos_spec
        else (ctx,b.CF.formula_struc_base) in
      (*************************************************************)
      (*****<<<< Check permissions variables in pre-condition ******)
      (*************************************************************)
      let nctx =
        if !Globals.max_renaming
        then (CF.transform_context (CF.normalize_es ext_base b.CF.formula_struc_pos false) ctx)
        else (CF.transform_context (CF.normalize_clash_es ext_base
                                      b.CF.formula_struc_pos false) ctx) in
      x_tinfo_zp (lazy ("nctx: " ^ (Cprinter.string_of_context nctx) ^ "\n")) no_pos;
      (* Termination: Move lexvar to es_var_measures *)
      let (c,pre,rels,hprels, sel_hps,sel_post_hps, unk_map,r) =
        match b.CF.formula_struc_continuation with
        | None ->
          (None,[],[],[],[], [], [],true)
        | Some l ->
          let r1,r2,r3,r4,r5,r6,r7,r8 = helper nctx l in (Some r1,r2,r3,r4,r5,r6,r7,r8)
      in stk_vars # pop_list vs;
      let () = x_tinfo_zp (lazy ("\nProving done... Result: "
                                 ^ (string_of_bool r) ^ "\n")) pos_spec in
      let new_base = match pre with
        | [] -> b.CF.formula_struc_base
        | [p] -> (pre_ctr # inc; Fixpoint.simplify_pre
                    (x_add CF.normalize 1 b.CF.formula_struc_base p pos_spec) []
                 )
        | _ -> report_error pos_spec ("Spec has more than 2 pres but only 1 post") in
      x_tinfo_hp (add_str "Base" !CF.print_formula) b.CF.formula_struc_base no_pos;
      x_tinfo_hp (add_str "New Base" !CF.print_formula) new_base no_pos;
      let () = if (rels) ==[] && hprels == [] then () else pre_ctr#inc  in
      (CF.EBase {b with CF.formula_struc_base = new_base;
                        CF.formula_struc_continuation = c}, [], rels,hprels,
       sel_hps,sel_post_hps,unk_map, r)

    | CF.EInfer b ->
      x_binfo_zp (lazy ("check_specs: EInfer: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos;
      let inf_o = b.CF.formula_inf_obj in
      let inf_o_lst = inf_o # get_lst in
      let is_ana_ni = List.exists (fun x -> x==Globals.INF_ANA_NI) inf_o_lst in
      let wrap_ana_ni f x =
        if is_ana_ni then  Wrapper.wrap_ana_ni (Some true) f x else f x in
      let () = y_binfo_hp (add_str "inf_o_lst" (pr_list string_of_inf_const)) inf_o_lst in
      let postf = b.CF.formula_inf_post in
      let postxf = b.CF.formula_inf_xpost in
      let old_vars = if do_infer then b.CF.formula_inf_vars else [] in
      let new_formula_inf_continuation,new_args =
        begin
          match b.CF.formula_inf_transpec with
          | None -> b.CF.formula_inf_continuation,[]
          | Some (old_view_name, new_view_name) ->
            let () = x_binfo_pp "looking view_def here" no_pos in
            let old_view = look_up_view_def b.CF.formula_inf_pos
                prog.prog_view_decls old_view_name in
            let new_view = look_up_view_def b.CF.formula_inf_pos
                prog.prog_view_decls new_view_name in
            let () = x_binfo_pp "after looking view_def" no_pos in
            let sub_pair = ((old_view_name,old_view.view_vars),(new_view_name,new_view.view_vars)) in
            let new_spec,new_args = CF.tran_spec b.CF.formula_inf_continuation sub_pair in
            x_tinfo_hp (add_str "TEMP SPECS" pr_spec) new_spec no_pos;
            new_spec,new_args
        end
      in
      let pre_vars,post_vars = CF.get_pre_post_vars_simp [] new_formula_inf_continuation in
      let pargs = List.concat (List.map (fun (t,n) ->
          if t==Int then [CP.SpecVar (t,n,Unprimed)] else []) proc.proc_args) in
      let vars, new_formula_inf_continuation =
        if old_vars = [] then
          begin
            match postxf with
            | None ->
              if new_args = [] then [],new_formula_inf_continuation
              else
                let pre_args, _ = List.partition (fun x -> List.mem x pre_vars) new_args in
                let new_rel_pre = CP.fresh_spec_var_rel () in
                let new_rel_post = CP.fresh_spec_var_rel () in
                let new_rel_fml_pre =
                  let tmp = List.map (fun v -> CP.mkVar v no_pos) (pre_args@pargs) in
                  CP.BForm ((CP.RelForm (new_rel_pre, tmp, no_pos),None),None) in
                let new_rel_fml_post =
                  let tmp = List.map (fun v -> CP.mkVar v no_pos) (new_args@pargs) in
                  CP.BForm ((CP.RelForm (new_rel_post, tmp, no_pos),None),None) in
                let new_spec = CF.add_pure new_formula_inf_continuation
                    (Some new_rel_fml_pre) (Some new_rel_fml_post) in
                x_tinfo_hp (add_str "TEMP SPECS1" pr_spec) new_spec no_pos;
                [new_rel_pre;new_rel_post],new_spec
            | Some pflag ->
              if not(pflag) then
                if new_args = [] then
                  pre_vars@pargs,new_formula_inf_continuation
                else
                  let new_rel = CP.fresh_spec_var_rel () in
                  let tmp = List.map (fun v -> CP.mkVar v no_pos) (new_args@pargs) in
                  let new_rel_fml = CP.BForm ((CP.RelForm (new_rel, tmp, no_pos),None),None) in
                  let new_spec = CF.add_pure new_formula_inf_continuation (Some new_rel_fml) None in
                  x_tinfo_hp (add_str "TEMP SPECS2" pr_spec) new_spec no_pos;
                  [new_rel],new_spec
              else
              if pflag then
                let new_rel = CP.fresh_spec_var_rel () in
                let tmp = List.map (fun v -> CP.mkVar v no_pos) (new_args@pargs) in
                let new_rel_fml = CP.BForm ((CP.RelForm (new_rel, tmp, no_pos),None),None) in
                let new_spec = CF.add_pure new_formula_inf_continuation None (Some new_rel_fml) in
                x_tinfo_hp (add_str "TEMP SPECS3" pr_spec) new_spec no_pos;
                [new_rel],new_spec
              else
                [],new_formula_inf_continuation
          end
        else old_vars,new_formula_inf_continuation
      in
      let einfer = CF.EInfer {b with
                              CF.formula_inf_vars = vars;
                              CF.formula_inf_continuation = new_formula_inf_continuation}
      in
      let () = proc.proc_stk_of_static_specs # push_pr "typechecker:629" einfer in
      let new_fml_fv = CF.struc_fv new_formula_inf_continuation in
      let () = x_tinfo_hp (add_str "vars" !print_svl) vars no_pos in
      let vars_rel, vars_templ, vars_inf = List.fold_left (fun (vr, vt, vi) v ->
          let typ = CP.type_of_spec_var v in
          if is_RelT typ then (vr@[v], vt, vi)
          else if is_UtT typ then (vr@[v], vt, vi)
          else if is_FuncT typ then (vr, vt@[v], vi)
          else (vr, vt, vi@[v])) ([], [], []) vars in
      let () = x_binfo_hp (add_str "vars_rel" !print_svl) vars_rel no_pos in
      let _ =
        let proc_args_vars = List.map (fun (t,i) -> CP.SpecVar(t,i,Unprimed) ) proc.proc_args in
        let pre_post_vars = CP.remove_dups_svl (pre_vars @ post_vars
                                                @ new_fml_fv @ proc_args_vars)
        in
        let () = Debug.ninfo_hprint (add_str "all vars" !print_svl) pre_post_vars no_pos in
        let () = Debug.ninfo_hprint (add_str "inf vars" !print_svl) vars no_pos in
        let classify_rel v =
          let rel_decl = Cast.look_up_rel_def_raw (prog.Cast.prog_rel_decls #
                                                     get_stk)
              (CP.name_of_spec_var v) in
          if not (is_primitive_rel rel_decl)
          && (CP.isConstTrue rel_decl.rel_formula) then true else false in
        let (unknown_rel,known_rel) = List.partition classify_rel
            (CP.remove_dups_svl ((List.filter CP.is_rel_var pre_post_vars)@vars_rel)) in
        let () = Debug.ninfo_hprint (add_str "unknown_rel" !print_svl) unknown_rel no_pos in
        let () = Debug.ninfo_hprint (add_str "known_rel" !print_svl) known_rel no_pos in
        let inf_pos = b.CF.formula_inf_pos in
        let pr_vars = Cprinter.string_of_spec_var_list in
        let _ =
          if not(CP.subset vars pre_post_vars) then
            let v1 = (add_str "vars" pr_vars) vars in
            let v2 = (add_str "pre_post_vars" pr_vars) pre_post_vars in
            let v = ("\n"^v1^" "^v2^"\n") in
            if not(!Globals.print_min) then
              DD.info_pprint
                ("WARNING : Inferable vars include some external variables!"^v) inf_pos
          else if not(CP.subset unknown_rel vars_rel) then
            let v1 = (add_str "unknown_rel" pr_vars) unknown_rel in
            let v2 = (add_str "vars_rel" pr_vars) vars_rel in
            let v = ("\n"^v1^" "^v2^"\n") in
            report_error inf_pos ("Inferable vars do not include some unknown relation!"^v)
          else if CP.intersect known_rel vars_rel<>[] then
            let v1 = (add_str "known_rel" pr_vars) known_rel in
            let v2 = (add_str "vars_rel" pr_vars) vars_rel in
            let v = ("\n"^v1^" "^v2^"\n") in
            report_error inf_pos ("Inferable vars include some known relation!"^v)
          else () in
        () in
      let (vars_hp_rel,vars_inf) =
        List.partition (fun v -> CP.type_of_spec_var v == HpT ) vars_inf in
      let new_vars = vars_inf @ (List.filter (fun r -> List.mem r new_fml_fv) vars_rel) in
      let new_vars = new_vars @ (List.filter (fun r -> List.mem r new_fml_fv) vars_hp_rel) in
      (if new_vars!=[] || postf then pre_ctr # inc) ;
      let nctx = CF.transform_context (fun es ->
          CF.Ctx {es with CF.es_infer_vars = es.CF.es_infer_vars@vars_inf;
                          CF.es_infer_vars_rel = es.CF.es_infer_vars_rel@vars_rel;
                          CF.es_infer_vars_templ = es.CF.es_infer_vars_templ@vars_templ;
                          (* CF.es_infer_tnt = es.CF.es_infer_tnt || itnt; *)
                          CF.es_infer_obj = es.CF.es_infer_obj # mk_or_lst (inf_o_lst);
                          CF.es_infer_vars_hp_rel = es.CF.es_infer_vars_hp_rel@vars_hp_rel;
                          CF.es_infer_vars_sel_hp_rel = es.CF.es_infer_vars_sel_hp_rel@vars_hp_rel;
                          CF.es_infer_vars_sel_post_hp_rel = es.CF.es_infer_vars_sel_post_hp_rel;
                          CF.es_infer_post = es.CF.es_infer_post || postf}) ctx in
      let (c,pre,rel,hprel, _, post_hps ,unk_map,f) =
        wrap_ana_ni (helper nctx) new_formula_inf_continuation in
      let new_c = if pre=[] then c else
          match c with
          | CF.EAssume _ -> CF.EBase {
              CF.formula_struc_explicit_inst = [];
              CF.formula_struc_implicit_inst = [];
              CF.formula_struc_exists = [];
              CF.formula_struc_base = (match pre with
                  | [a] -> a
                  | _ -> report_error pos_spec ("Spec has more than 2 pres but only 1 post"));
              CF.formula_struc_is_requires = true;
              CF.formula_struc_continuation = Some c;
              CF.formula_struc_pos = pos_spec;}
          | _ -> c in
      (* Template: Restore template vars in specs *)
      let new_c =
        if vars_templ = [] then new_c
        else CF.EInfer { b with
                         CF.formula_inf_vars = vars_templ;
                         CF.formula_inf_continuation = new_c; }
      in
      (new_c,[],rel,hprel,vars_hp_rel,post_hps,unk_map,f)
    | CF.EList b ->
      let (sl,pl,rl,hprl,selhps,sel_posthps,unk_map,bl) =
        List.fold_left (fun (a1,a2,a3,a4,a5,a6,a7,a8) (l,c) ->
          let (b1,b2,b3,b4,b5,b6,b7,b8) =
            store_label # set l;
            helper (CF.update_ctx_label ctx l) c in
          (a1@[(l,b1)],a2@b2,a3@b3,a4@b4,a5@b5,a6@b6,a7@b7,a8@[b8])) ([],[],[],[],[],[],[],[]) b in
      x_tinfo_hp (add_str "SPECS (before norm_specs)" pr_spec) (CF.EList sl) no_pos;
      (CF.norm_specs (CF.EList sl), pl, rl, hprl,selhps,sel_posthps, unk_map,List.for_all pr_id bl)
    | CF.EAssume {
        CF.formula_assume_vars = var_ref;
        CF.formula_assume_simpl = post_cond;
        CF.formula_assume_lbl = post_label;
        CF.formula_assume_ensures_type = etype0; (* duplicate??? *)
        CF.formula_assume_struc = post_struc} ->
      let ctx = CF.add_path_id ctx (None,0) 0 in
      let etype = if (check_is_classic ()) then Some ((check_is_classic ())) else
          (* run-fast-test: classic2, classic2a *)
          etype0 in
      let curr_vars = stk_vars # get_stk in
      in_vars # set curr_vars ;
      x_tinfo_hp (add_str "curr vars" !CP.print_svl) curr_vars no_pos;
      let () = x_tinfo_hp (add_str "var_ref" !CP.print_svl) var_ref no_pos in
      if ((Immutable.is_lend post_cond) && not(!Globals.allow_field_ann))||
         (!Globals.allow_field_ann && Mem.is_lend post_cond) then
        Error.report_error {
          Error.error_loc = pos_spec;
          Error.error_text = ("The postcondition cannot contain @L heap
      predicates/data nodes/field annotations\n")}
      else
        let pos_post = CF.pos_of_formula post_cond in
        let () = post_pos#set (pos_post) in
        x_tinfo_zp (lazy ("check_specs: EAssume: "
                          ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos;
        let ctx1 = if !Globals.disable_pre_sat then ctx
          else CF.transform_context (SV.elim_unsat_es 2 prog (ref 1)) ctx in
        if (CF.isAnyFalseCtx ctx1) then
          let () = x_ninfo_zp
              (lazy ("\nFalse precondition detected in procedure "
                     ^proc.proc_name^"\n with context: "^
                     (Cprinter.string_of_context_short ctx))) no_pos in
          let () = x_binfo_hp (add_str "pos_post" Cprinter.string_of_pos) pos_post no_pos in
          let () = Globals.add_false_ctx pos_post in
          let () = print_endline_quiet
              ("\n\nWarning: False precondition detected in procedure "
               ^proc.proc_name^"\n with context: "
               ^ (Cprinter.string_of_context_short ctx)) in
          (spec,[],[],[], [], [],[],true)
        else
          let () = Gen.Profiling.push_time ("method "^proc.proc_name) in
          try
            let spec_and_inferred_post, inferred_pre, inferred_rel,
                inferred_hp_rel, sel_hps,sel_post_hps, unk_map, r =
              flow_store := [];
              let ctx1 = CF.set_flow_in_context_override
                  { CF.formula_flow_interval = !norm_flow_int; CF.formula_flow_link = None} ctx1 in
              let ctx1 = CF.add_path_id ctx1 (Some post_label,-1) (-1) in
              (* need to add initial esc_stack *)
              let init_esc = [((0,""),[])] in
              let lfe = [CF.mk_failesc_context ctx1 [] init_esc] in
              x_tinfo_hp (add_str "lfe" (Cprinter.string_of_list_failesc_context)) lfe no_pos;
              (* Termination: Check boundedness of the measures
               * before going into the function body *)
              let (_, rankbnds) = check_bounded_term prog ctx1 (CF.pos_of_formula post_cond) in
              let () = if !Globals.tc_drop_unused then
                  let spec_names = List.map CP.name_of_spec_var
                      ((CF.context_fv ctx1)@(CF.struc_fv post_struc)) in
                  proc_used_names := Gen.BList.remove_dups_eq (=)
                      ((exp_fv e0)@spec_names@(List.map snd proc.proc_args));
                  print_string_quiet ("bai-used:   "^(String.concat "," !proc_used_names)^"\n")
                else () in
              let () = x_tinfo_hp (add_str "e0: "
                                     (Cprinter.string_of_exp))
                  e0 no_pos in
              let res_ctx = x_add check_exp prog proc lfe e0 post_label in
              let () = x_tinfo_hp (add_str "res_ctx 0: "
                                     (Cprinter.string_of_list_failesc_context))
                  res_ctx no_pos in
              let res_ctx =  CF.transform_list_failesc_context
                  (idf,idf, (fun es -> CF.Ctx (CF.clear_entailment_es_pure es)))
                  res_ctx in
              let res_ctx = CF.list_failesc_to_partial res_ctx in
              let res_ctx = CF.change_ret_flow_partial_ctx res_ctx in
              let pos = CF.pos_of_formula post_cond in
              let () = x_tinfo_pp ("\n WN 2 : "
                                   ^(Cprinter.string_of_list_partial_context
                                       res_ctx)) pos in
              if (CF.isFailListPartialCtx_new res_ctx)
              then (spec, [], [],[], [],[],[], false)
              else
                let lh = Infer.collect_pre_heap_list_partial_context res_ctx in
                let lp = Infer.collect_pre_pure_list_partial_context res_ctx in
                let lr = x_add_1 Infer.collect_rel_list_partial_context res_ctx in
                if lr!=[] then
                  begin
                    x_winfo_pp "if important : need to add to estate.es_infer_rel" no_pos;
                    x_binfo_hp
                      (add_str "WARNING : Spurious RelInferred (not collected)"
                         (pr_list CP.print_lhs_rhs)) lr pos;
                    (* lr seems to be spurious RelInferred which have already been collected? *)
                    let () = Infer.infer_rel_stk # push_list_pr x_loc lr in
                    ()
                  end;
                let post_iv = Infer.collect_infer_vars_list_partial_context res_ctx in
                (* Why? Bug cll-count-base.ss *)
                (* no abductive inference for post-condition *)
                let postf = CF.collect_infer_post ctx in
                let (impl_vs,post_cond,post_struc) =
                  (* below seems to cause problem for verification *)
                  (* see bug-sort-ll.ss *)
                  if  pre_ctr # get > 0 then
                    let (impl_vs,new_post) =
                      if !Globals.old_post_conv_impl then CF.lax_impl_of_post post_cond
                      else ([],post_cond) in
                    let new_post_struc, impl_struc =
                      if !Globals.old_post_conv_impl then F.lax_impl_of_struc_post post_struc
                      else (post_struc,[]) in
                    if impl_vs!=[] then
                      begin
                        (* TODO:WN this could be a loss of completeness *)
                        (* In astsmpl.ml : seems impl --> exists *)
                        (* Here astsmpl.ml : seems impl --> exists *)
                        (* It seems impl --> exists by astsimpl.ml *)
                        x_binfo_pp ">>>>>> Convert Exists to Implicit Vars for Post-Cond <<<<<<" pos;
                        x_binfo_pp ("New Impl Vars :"
                                    ^(Cprinter.string_of_spec_var_list impl_vs))
                          pos;
                        x_dinfo_pp ("Post Struc Vars :"
                                    ^(Cprinter.string_of_spec_var_list
                                        impl_struc)) pos;
                        x_dinfo_pp ("New Post Cond :"^(Cprinter.string_of_formula new_post)) pos
                      end;
                    if (Gen.BList.list_setequal_eq CP.eq_spec_var_ident impl_struc impl_vs) then
                      (impl_vs,new_post,new_post_struc)
                    else (*temp fixing*)
                    if not (!Globals.pred_syn_flag) then report_error pos "Assume struc impl error"
                    else
                      let pr = Cprinter.string_of_spec_var_list in
                      let () = Debug.ninfo_hprint (add_str "impl_struc" pr) impl_struc no_pos in
                      let () = Debug.ninfo_hprint (add_str "impl_vs" pr) impl_vs no_pos in
                      let () = Debug.ninfo_hprint (add_str "new_post_struc"
                                                     Cprinter.string_of_struc_formula)
                          new_post_struc no_pos in
                      let () = Debug.ninfo_hprint
                          (add_str "new_post" Cprinter.string_of_formula)
                          new_post no_pos in
                      let sst = try List.combine impl_struc impl_vs
                        with _ -> []
                      in
                      let new_post_struc = CF.subst_struc sst new_post_struc in
                      let () = Debug.ninfo_hprint (add_str "new_post_struc"
                                                     Cprinter.string_of_struc_formula)
                          new_post_struc no_pos in
                      (impl_vs,new_post,new_post_struc)
                  else ([],post_cond,post_struc) in
                stk_evars # push_list impl_vs;
                (* TODO: Timing *)
                let pres, posts = CF.get_pre_post_vars_simp []
                    (proc.proc_stk_of_static_specs # top) in
                let pre_vars = CP.remove_dups_svl
                    (pres @ (List.map
                               (fun (t,id) -> CP.SpecVar (t,id,Unprimed)) proc.proc_args)) in
                let impl_vs, expl_vs =
                  List.partition (fun v -> CP.mem_svl v (pre_vars@posts))
                    impl_vs in
                DD.ninfo_pprint ("Pre Vars :"^(Cprinter.string_of_spec_var_list pre_vars)) pos;
                x_dinfo_pp ("Post Vars :"^(Cprinter.string_of_spec_var_list posts)) pos;
                x_dinfo_pp ("Extra Implicit Vars :"^(Cprinter.string_of_spec_var_list impl_vs)) pos;
                x_dinfo_pp ("Extra Explicit Vars :"^(Cprinter.string_of_spec_var_list expl_vs)) pos;
                x_dinfo_pp ("Res ctx:" ^ (Cprinter.string_of_list_partial_context res_ctx)) pos;
                (* TODO: Timing *)
                let res_ctx = Infer.add_impl_expl_vars_list_partial_context
                    impl_vs expl_vs res_ctx in
                let pos_post = (CF.pos_of_formula post_cond) in
                (* Termination: Collect the constraints of
                 * phase transitions inferred by inference
                 * Need to filter the constraints and normalize
                 * them - We only interest constraints related
                 * to logical variables *)
                let () = if !Globals.dis_term_chk then () else
                    let log_vars = prog.Cast.prog_logical_vars in
                    let cl = List.filter (fun f ->
                        Gen.BList.overlap_eq CP.eq_spec_var (CP.fv f) log_vars) lp in
                    let () = if not (Gen.is_empty lp) then
                        DD.info_hprint (add_str "Inferred constraints"
                                          (pr_list !CP.print_formula)) lp pos in

                    let () = x_add_1 Term.add_phase_constr_by_scc proc
                        (List.map TP.simplify_raw cl) in ()
                in
                let tmp_false_cnt  = new Gen.counter 0 in
                let elim_unsat e =
                  let already_unsat_flag = e.CF.es_unsat_flag in
                  if already_unsat_flag then e
                  else
                    let () = x_ninfo_hp (add_str "es_unsat_flag" string_of_bool)
                        already_unsat_flag no_pos in
                    let (b,_,e) = SV.elim_unsat_estate prog e in
                    if b then tmp_false_cnt # inc;
                    let () = x_ninfo_hp (add_str "elim_unsat(b)" string_of_bool) b no_pos in
                    e
                in
                let res_ctx = CF.map_list_partial_context res_ctx elim_unsat  in
                let new_false_cnt = tmp_false_cnt # get in
                let () = x_dinfo_hp (add_str "new_false_cnt" string_of_int) new_false_cnt no_pos in
                let tmp_ctx = x_add_1 check_post prog proc res_ctx
                    (post_cond,post_struc) pos_post post_label etype in
                let () = x_ninfo_pp "After check_post. It fail, will not show this" no_pos in
                let () =
                  if not(!Globals.old_infer_hp_collect) then
                    begin
                      let hp_rel_list = Infer.collect_hp_rel_list_partial_context tmp_ctx in
                      let () = Infer.rel_ass_stk # push_list (hp_rel_list) in
                      let () = Log.current_hprel_ass_stk # push_list (hp_rel_list) in
                      ()
                    end
                in
                let cnt_before = CF.count_sat_pc_list res_ctx in
                let cnt_after = CF.count_sat_pc_list tmp_ctx + new_false_cnt in
                if cnt_before>cnt_after && not(!Globals.old_collect_false) then
                  begin
                    (* need to do the same for pre-condition proving ? *)
                    (* detected new False from post-condition proving *)
                    (* potential unsoundness *)
                    (* to count false detected in elim_unsat_estate *)
                    let () = x_tinfo_pp ("\n Before CheckPost : "
                                         ^(Cprinter.string_of_list_partial_context
                        res_ctx)) no_pos in
                    let () = x_tinfo_pp ("\n After CheckPost : "
                                         ^(Cprinter.string_of_list_partial_context
                        tmp_ctx)) no_pos in
                    let () = x_binfo_pp ("\n Before CheckPost : "
                                         ^(string_of_int cnt_before)) no_pos in
                    (* inside cnt_after *)
                    let () = x_binfo_pp ("\n After CheckPost : "^(string_of_int cnt_after)) no_pos in
                    let () = add_false_ctx (post_pos # get) in
                    let () = print_endline_quiet
                        ("\n[UNSOUNDNESS] WARNING : possible new unsatisfiable
                        state from post-proving of "^(post_pos # string_of)) in
                    if !Globals.assert_unsound_false then failwith "Unsound false in SLEEK?"
                    else ()
                  end;
                (* Termination: collect error messages from successful states *)
                let term_err_msg = CF.collect_term_err_list_partial_context tmp_ctx in
                let () = List.iter (fun m -> Term.add_term_err_stk m) term_err_msg in
                let rels = Gen.BList.remove_dups_eq (=)
                    (Infer.collect_rel_list_partial_context tmp_ctx) in
                let hp_rels = Gen.BList.remove_dups_eq (=)
                    (Infer.collect_hp_rel_list_partial_context tmp_ctx) in
                let sel_hps= CP.remove_dups_svl
                    (CF.get_infer_vars_sel_hp_partial_ctx_list tmp_ctx) in
                let sel_post_hps= CP.remove_dups_svl
                    (CF.get_infer_vars_sel_post_hp_partial_ctx_list tmp_ctx) in
                let unk_map = Infer.collect_hp_unk_map_list_partial_context tmp_ctx in
                let res = CF.isSuccessListPartialCtx tmp_ctx in
                let lp = (* if not !do_abd_from_post then lp else ( *)
                  x_dinfo_zp (lazy ("TMP CTX: "
                                    ^ (Cprinter.string_of_list_partial_context
                                         tmp_ctx) ^ "\n")) no_pos;
                  let lp_new = Infer.collect_pre_pure_list_partial_context tmp_ctx in
                  Gen.BList.remove_dups_eq (CP.equalFormula) (lp@lp_new)
                in
                let infer_pre_flag = (List.length lh)+(List.length lp) > 0 in
                (* Fail with some tests *)
                let infer_post_flag = postf in
                let new_spec_post, pre =
                  if res then
                    let flist = Infer.collect_formula_list_partial_context tmp_ctx in
                    let i_pre =
                      if infer_pre_flag then (
                        prepost_ctr # inc;
                        x_tinfo_pp ">>>>>> HIP gather infer pre <<<<<<" pos;
                        x_tinfo_zp (lazy (("Inferred Heap: " ^
                                           (pr_list Cprinter.string_of_h_formula lh))
                          )) pos;
                        x_tinfo_zp (lazy (("Inferred Pure: " ^(pr_list pr_pf lp)))) pos;
                        let fml = if (!Globals.pa) then
                            CF.formula_of_disjuncts
                              (List.map (fun h ->
                                   CF.formula_of_heap h no_pos) lh)
                          else
                            List.fold_left CF.normalize_combine_heap
                              (CF.formula_of_heap CF.HEmp no_pos) lh in
                        let fml = x_add CF.normalize 1 fml
                            (CF.formula_of_pure_formula
                               (CP.arith_simplify_new
                                  (CP.conj_of_list lp no_pos)) no_pos) no_pos in
                        let check_sat = Solver.verify_pre_is_sat prog fml in
                        if check_sat then [fml] else [])
                      else [] in
                    let i_post =
                      if not(infer_post_flag) then spec
                      else
                      if rels!=[] then let () = post_ctr # inc in spec
                      else
                        begin
                          let () = post_ctr # inc in
                          let pre_vars = CF.context_fv ctx in
                          (* filter out is_prime *)
                          let pre_vars = List.filter (fun v -> not(CP.is_primed v)) pre_vars in
                          (* add vars of pre *)
                          let pre_vars = pre_vars @ (if i_pre = [] then []
                                                     else CF.fv (List.hd i_pre))
                          in
                          (* (\* add infer_vars *\) *)
                          let pre_vars = CP.remove_dups_svl (pre_vars @ post_iv) in
                          (* drop @L heap nodes from flist *)
                          let flist = List.map CF.remove_lend flist in
                          let flist = Gen.BList.remove_dups_eq (=) (flist) in
                          (* TODO: flist denotes a disjunction! see ll-b.ss *)
                          let post_vars = List.concat (List.map CF.fv flist) in
                          let heap_vars = List.concat (List.map (fun f -> CF.fv_heap_of f) flist) in
                          let heap_vars_init = CF.fv_heap_of post_cond in
                          (* ref parameters *)
                          let vr = List.map CP.to_primed var_ref in
                          let post_vars = CP.diff_svl post_vars
                              (pre_vars@heap_vars@heap_vars_init@vr) in
                          (* filter out res *)
                          let post_vars = List.filter (fun v ->
                              not(CP.is_res_spec_var v)) post_vars in
                          let post_vars = CP.remove_dups_svl post_vars in
                          let post_fml = if flist!=[] then
                              let tmp = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 no_pos)
                                  (List.hd flist) (List.tl flist) in
                              CF.normalize 1 tmp post_cond no_pos
                            else post_cond in
                          (* TODO : What if we have multiple ensures in a spec? *)
                          (* It may be too early to compute a fix-point. *)
                          let post_fml,_ = Fixpoint.simplify_post
                              post_fml post_vars prog None [] true [] [] in
                          x_dinfo_pp ">>>>>> HIP gather inferred post <<<<<<" pos;
                          x_dinfo_pp ("Initial Residual post :"
                                      ^(pr_list Cprinter.string_of_formula flist
                                       )) pos;
                          x_dinfo_pp ("Final Post :"^(Cprinter.string_of_formula post_fml)) pos;
                          let inferred_post =
                            let vars = CP.remove_dups_svl (var_ref(* @post_vars *)) in
                            let post_struc = CF.mkEBase post_fml None pos in
                            CF.mkEAssume vars post_fml post_struc post_label etype in
                          inferred_post
                        end in
                    (i_post, i_pre)
                  else (spec,[]) in
                (new_spec_post, pre, rankbnds@rels, hp_rels,sel_hps,
                 sel_post_hps, unk_map, res) in
            let () = Gen.Profiling.pop_time ("method "^proc.proc_name) in
            (spec_and_inferred_post,inferred_pre,inferred_rel,inferred_hp_rel,
             sel_hps, sel_post_hps, unk_map, r)
          with | Err.Ppf (e, ifk, error_type) ->
            (match ifk with
             | 1 ->
               if x_add_1 CF.is_error_flow post_cond  then
                 (spec, [],[],[],[],[], [], true) else
                 let () = Gen.Profiling.pop_time ("method "^proc.proc_name) in
                 (Err.report_error1 e (Err.get_error_type_str error_type)
                 (*"bind failure exception"*))
             | 2 -> if x_add_1 CF.is_error_flow post_cond  then
                 (spec, [],[],[],[],[], [], true) else
                 let () = Gen.Profiling.pop_time ("method "^proc.proc_name) in
                 (Err.report_error1 e (Err.get_error_type_str error_type)
                 (*"assert/assume failure exception"*)
                 )
             | 3 ->
               if CF.is_top_flow post_cond then
                 (spec, [],[],[],[],[],[], true) else
                 let () = Gen.Profiling.pop_time ("method "^proc.proc_name) in
                 (Err.report_error1 e (Err.get_error_type_str error_type))
             | _ -> let () = Gen.Profiling.pop_time ("method "^proc.proc_name) in
               (Err.report_error1 e (Err.get_error_type_str error_type))
            )
          |_ as e ->
            let () = Gen.Profiling.pop_time ("method "^proc.proc_name) in raise e
  in
  Wrapper.wrap_ana_ni (Some false) (helper ctx) spec

(*we infer automatically from ctx*)
and infer_lock_invariant_x lock_var ctx pos =
  try
    let found_args,found_name = CF.collect_heap_args_list_failesc_context ctx lock_var in
    let found_arg_names = List.map (fun v -> CP.name_of_spec_var v) found_args in
    if (found_name = "") then
      report_error pos "Scall : could not infer invariant name"
    else if (found_name = lock_name) then
      report_error pos "Scall : lock has not been initialized"
    else
      (found_name,found_arg_names)
  with _ -> report_error pos ("Scall : could not find heap node for lock " ^ (Cprinter.string_of_spec_var lock_var))

(*
  transform l1=l2 into l1=l2 & level(l1)=level(l2)
  This is to maintain information about locklevels in the presence
  of elim_exists
*)
and trans_level_eqn_list_failesc_context (ctx: CF.list_failesc_context)
  : CF.list_failesc_context =
  let translate_level_es es =
    let new_f = CF.translate_level_eqn_formula es.CF.es_formula in
    let new_es = {es with CF.es_formula = new_f} in (*trigger unsat_check*)
    CF.Ctx new_es
  in
  let ctx = CF.transform_list_failesc_context (idf,idf,translate_level_es) ctx in
  ctx

(*
  transform level(l1) into l1_mu
*)
and trans_level_list_partial_context (ctx:CF.list_partial_context)
  : CF.list_partial_context =
  let translate_level_es es =
    let new_f = CF.translate_level_formula es.CF.es_formula in
    let new_es = {es with CF.es_formula = new_f} in (*trigger unsat_check*)
    CF.Ctx new_es
  in
  let ctx = CF.transform_list_partial_context (translate_level_es, (fun c -> c)) ctx in
  ctx

and infer_lock_invariant lock_var ctx pos =
  let pr_out = pr_pair Cprinter.string_of_ident (pr_list Cprinter.string_of_ident) in
  Debug.no_2 "infer_lock_invariant"
    Cprinter.string_of_spec_var Cprinter.string_of_list_failesc_context pr_out
    (fun _ _ -> infer_lock_invariant_x lock_var ctx pos) lock_var ctx
(*
   Important arugments:
   ctx,e0 : current ctx and exp
   mn : mingled procedure name
   lock: lockset (if any)
   vs: arguments of the corresponding call
*)
and check_scall_fork prog ctx e0 (post_start_label:formula_label) ret_t mn lock
  vs ir pid pos =
  (*=========================*)
  (*=== id=FORK(fn,args) ====*)
  (*=========================*)
  if (CF.isFailListFailescCtx ctx) then
    let () = Debug.print_info "procedure call"
        ("\nempty/false context: Proving precondition in method " ^ mn
         ^ " has failed \n") pos in
    ctx
  else
    let fn = List.hd vs in
    let fargs = List.tl vs in
    let proc = look_up_proc_def pos prog.new_proc_decls fn in
    let farg_types, farg_names = List.split proc.proc_args in
    let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
    let actual_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) fargs farg_types in
    (*=======check_pre_post========*)
    (* Internal function to check pre/post condition of the fork call. *)
    let check_pre_post org_spec (sctx:CF.list_failesc_context)
        should_output_html : CF.list_failesc_context =
      (* Termination: Stripping the "variance" feature from org_spec
         if the call is not a recursive call *)
      (*TO CHECK: neccessary -> YES*)
      (*fork is not a recursive call*)
      let stripped_spec = org_spec in
      (* org_spec -> stripped_spec *)
      (* free vars = linking vars that appear both in pre and are not formal arguments *)
      let pre_free_vars = Gen.BList.difference_eq CP.eq_spec_var
          (Gen.BList.difference_eq CP.eq_spec_var (Cformula.struc_fv stripped_spec(*org_spec*))
             (Cformula.struc_post_fv stripped_spec(*org_spec*))) farg_spec_vars in
      (*LOCKSET: ls is not free var, it is a ghost argument in proc_args*)
      let ls_var = [(CP.mkLsVar Unprimed)] in
      let lsmu_var = [(CP.mkLsmuVar Unprimed)] in
      let waitlevel_var = [(CP.mkWaitlevelVar Unprimed)] in
      (*added for consistency, later waitlevel constraints are removed*)
      (*when fork, do not consider waitlevel because it is not used
        for delayed checking*)
      let pre_free_vars = List.filter (fun v -> CP.name_of_spec_var v
                                                <> Globals.ls_name
                                                && CP.name_of_spec_var v
                                                   <> Globals.lsmu_name
                                                && CP.name_of_spec_var v
                                                   <> Globals.waitlevel_name)
          pre_free_vars in
      (* free vars get to be substituted by fresh vars *)
      let pre_free_vars_fresh = CP.fresh_spec_vars pre_free_vars in
      let renamed_spec =
        if !Globals.max_renaming then (Cformula.rename_struc_bound_vars stripped_spec(*org_spec*))
        else (Cformula.rename_struc_clash_bound_vars stripped_spec(*org_spec*) (
            CF.formula_of_list_failesc_context sctx))
      in
      let st1 = List.combine pre_free_vars pre_free_vars_fresh in
      let fr_vars = farg_spec_vars @ (List.map CP.to_primed farg_spec_vars) in
      let to_vars = actual_spec_vars @ (List.map CP.to_primed actual_spec_vars) in
      (* Termination: Cache the subst for output pretty printing *)
      (* Assume: fork is not a recursive call*)
      let renamed_spec = CF.subst_struc st1 renamed_spec in
      let renamed_spec = CF.subst_struc_avoid_capture fr_vars to_vars renamed_spec in
      let st2 = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) actual_spec_vars in
      (*ALSO rename ls to ls'*)
      (*ALSO rename ls to ls', lsmu to lsmu'*)
      let st_ls = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) ls_var in
      let st_lsmu = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) lsmu_var in
      let st_waitlevel = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) waitlevel_var in
      let st3= st2@st_ls@st_lsmu@st_waitlevel in
      let pre2 = CF.subst_struc_pre st3 renamed_spec in
      let new_spec = (Cprinter.string_of_struc_formula pre2) in
      (*Termination checking *) (*TO CHECK: neccessary ???*)
      (* TODO: call the entailment checking function in solver.ml *)
      let to_print = "\nProving precondition in forked method " ^ proc.proc_name
                     ^ " for spec:\n" ^ new_spec (*!log_spec*) in
      let to_print = ("\nVerification Context:"^(post_pos#string_of_pos)^to_print) in
      x_dinfo_pp (to_print^"\n") pos;
      (* An Hoa : output the context and new spec before checking pre-condition *)
      let () = if !print_proof && should_output_html
        then Prooftracer.push_list_failesc_context_struct_entailment sctx pre2
      in

      (*Call heap_entail... to prove the precondition and add the post condition into thread id*)
      let tid = CP.fresh_thread_var () in
      let rs, prf = x_add SV.heap_entail_struc_list_failesc_context_init 1 prog
          false true sctx pre2 (Some tid) None None pos pid in
      let () = if !print_proof && should_output_html then Prooftracer.pop_div () in
      let () = PTracer.log_proof prf in
      if (CF.isSuccessListFailescCtx sctx) && (CF.isFailListFailescCtx rs) then
        if (!Globals.web_compile_flag) then
          Debug.print_info "procedure call"
            ("\nProving precondition in forked method " ^ proc.proc_name
             ^ " has failed \n") pos
        else
          Debug.print_info "procedure call" (to_print^" has failed \n") pos
      else () ;
      rs
    in
    (*=======check_pre_post - END ========*)
    (* Call check_pre_post with debug information *)
    let check_pre_post org_spec (sctx:CF.list_failesc_context)
        should_output_html : CF.list_failesc_context =
      let pr2 = Cprinter.summary_list_failesc_context in
      let pr3 = Cprinter.string_of_struc_formula in
      Debug.no_2 "check_pre_post" pr3 pr2 pr2 (fun _ _ ->
          check_pre_post org_spec sctx should_output_html) org_spec sctx in
    let () = if !print_proof then Prooftracer.start_compound_object () in
    let scall_pre_cond_pushed = if !print_proof then
        begin
          Tpdispatcher.push_suppress_imply_output_state ();
          Tpdispatcher.unsuppress_imply_output ();
          Prooftracer.push_pre e0;
        end else false in
    let res = if (CF.isFailListFailescCtx ctx) then
        let () = if !print_proof && scall_pre_cond_pushed
          then Prooftracer.append_html "Program state is unreachable." in
        ctx
      else
        check_pre_post (proc.proc_stk_of_static_specs#top) ctx scall_pre_cond_pushed
    in
    let () = if !print_proof then Prooftracer.add_pre e0 in
    let () = if !print_proof && scall_pre_cond_pushed then
        begin
          Prooftracer.pop_div ();
          Tpdispatcher.restore_suppress_imply_output_state ();
        end in
    res
(*=========================*)
(*===== <<< FORK ==========*)
(*=========================*)

(*
   Important arugments:
   ctx,e0 : current ctx and exp
   mn : mingled procedure name
   lock: lockset (if any)
   vs: arguments of the corresponding call
*)
and check_scall_join prog ctx e0 (post_start_label:formula_label) ret_t mn lock
    vs ir pid pos =
  (*=========================*)
  (*========= JOIN ==========*)
  (*=========================*)
  if (CF.isFailListFailescCtx ctx) then
    let () = Debug.print_info "procedure call"
        ("\nempty/false context: Proving precondition in method " ^ mn
         ^ " has failed \n") pos in
    ctx
  else
    (*=======check_pre_post - START ========*)
    (*=======check_pre_post - END ========*)
    (*Find the thread and compose (or merge???) it with the main formula*)
    (*Currently, we assume pass-by-value -> merge is ok.
      Otherwise, we have to compose*)
    let tid = List.hd vs in
    let tid =  CP.SpecVar (thread_typ, tid, Primed) in (*TO CHECK: Primed or Unprimed*)
    let () = x_dinfo_pp ("\ncheck_exp: SCall : join : before join("
                         ^ (Cprinter.string_of_spec_var tid) ^") \n ### ctx: "
                         ^ (Cprinter.string_of_list_failesc_context ctx)) pos
    in
    let empty_struc = CF.mkETrue (CF.mkTrueFlow ()) pos in
    (*Perform Delay lockset checking and join at Solver.heap_entail_conjunct_lhs_struc*)
    let rs, prf = x_add SV.heap_entail_struc_list_failesc_context_init 2 prog false
        true ctx empty_struc None None (Some tid) pos pid in
    (*This is done after join inside Solver.ml*)
    if (CF.isSuccessListFailescCtx ctx) && (CF.isFailListFailescCtx rs) then
      Debug.print_info "procedure call"
        ("join("^ (CF.string_of_spec_var tid)
         ^") has failed.\n" ^
         (Cprinter.string_of_list_failesc_context rs)^ " \n") pos else ();
    rs
(*=========================*)
(*===<<<<<= JOIN ==========*)
(*=========================*)

(*
   Important arugments:
   ctx,e0 : current ctx and exp
   mn : mingled procedure name
   lock: lockset (if any)
   vs: arguments of the corresponding call
*)

(*========================================================*)
(*==========lock operations ==============================*)
(*== init/finalize/acquires/release[LOCK](lock,args) =====*)
(*========================================================*)
and check_scall_lock_op prog ctx e0 (post_start_label:formula_label) ret_t mn
    lock vs ir pid pos =
  let mn_str = Cast.unmingle_name mn in
  if (not (CF.isNonFalseListFailescCtx ctx)) then
    ctx
  else
  if (CF.isFailListFailescCtx ctx) then
    let () = Debug.print_info "procedure call"
        ("\nempty/false context: Proving precondition in method " ^ mn
         ^ " has failed \n") pos in
    ctx
  else
    let l = List.hd vs in
    let lock_args = List.tl vs in
    let lock_var =  CP.SpecVar (lock_typ, l, Primed) in
    let lock_sort = match lock with
      | None ->
        if (mn_str=Globals.init_name) then
          Err.report_error { Err.error_loc = pos;
                             Err.error_text
                             = ("SCall :: init requires an associated lock");}
        else ""
      | Some v -> v
    in
    let lock_sort,lock_args = if lock_sort <> "" then
        (*user provides annotations*)
        (lock_sort,lock_args)
      else
        (*we infer automatically from ctx*)
        infer_lock_invariant lock_var ctx pos in
    let vdef = look_up_view_def_raw x_loc prog.prog_view_decls lock_sort in

    let types = List.map (fun v -> CP.type_of_spec_var v) vdef.view_vars in
    let new_args = List.map2 (fun arg typ ->  CP.SpecVar (typ, arg, Primed) ) lock_args types in
    let self_var =  CP.SpecVar (Named vdef.view_data_name, self, Unprimed) in
    let fr_vars = self_var::vdef.view_vars in
    let to_vars = lock_var::new_args in
    (*init/finalize does not need invariant*)
    let inv_lock = match vdef.view_inv_lock with
      | None ->
        (CF.mkTrue (CF.mkTrueFlow ()) pos)
      | Some f -> f
    in
    let renamed_inv = CF.subst_avoid_capture fr_vars to_vars inv_lock in
    let prepost =
      if (mn_str=Globals.acquire_name)
      then
        (***generating spec for acquire***)
        CF.prepost_of_acquire lock_var lock_sort new_args renamed_inv post_start_label pos
      else if (mn_str=Globals.release_name) then
        (***generating spec for release***)
        CF.prepost_of_release lock_var lock_sort new_args renamed_inv post_start_label pos
      else if (mn_str=Globals.finalize_name) then
        (***generating spec for finalize***)
        CF.prepost_of_finalize lock_var lock_sort new_args post_start_label pos
      else
        (***generating spec for init***)
        CF.prepost_of_init lock_var lock_sort new_args post_start_label pos
    in
    let () = x_ninfo_hp (add_str "prepost" Cprinter.string_of_struc_formula) prepost no_pos in
    let prepost = x_add Cvutil.prune_pred_struc prog true prepost in (* specialise --eps *)
    let () = x_ninfo_hp (add_str "prepost" Cprinter.string_of_struc_formula) prepost no_pos in
    let ctx =
      if (mn_str=Globals.finalize_name) then
        (*try to combine fractional permission before finalize*)
        SV.normalize_list_failesc_context_w_lemma prog ctx
      else ctx
    in
    let to_print = "\nProving precondition in method " ^ mn ^ " for spec:\n"
                   ^ (Cprinter.string_of_struc_formula prepost)  in
    let to_print = ("\nVerification Context:"^(post_pos#string_of_pos)^to_print) in
    x_dinfo_zp (lazy (to_print^"\n")) pos;
    (*TO CHECK: clear_entailment can effect reasoning??? *)
    let ctx = CF.clear_entailment_history_failesc_list (fun x -> None) ctx in
    let rs, prf = x_add SV.heap_entail_struc_list_failesc_context_init 3 prog false
        true ctx prepost None None None pos pid in
    if (CF.isSuccessListFailescCtx ctx) && (CF.isFailListFailescCtx rs) then
      if (!Globals.web_compile_flag) then
        Debug.print_info "procedure call" ("\nProving precondition in method "
                                           ^ mn ^ " has failed \n") pos
      else
        Debug.print_info "procedure call" (to_print^" has failed \n") pos else () ;
    (*NORMALIZE after acquiring some new states*)
    let tmp_res = SV.normalize_list_failesc_context_w_lemma prog rs in
    let tmp_res2 =
      if (mn_str=Globals.acquire_name) then
        (*acquire() an invariant may cause UNSAT*)
        let unsat_check_fct es =
          let new_es = {es with CF.es_unsat_flag = false} in (*trigger unsat_check*)
          SV.elim_unsat_es 12 prog (ref 1) new_es
        in
        let tmp_res2 = CF.transform_list_failesc_context (idf,idf,unsat_check_fct) tmp_res in
        tmp_res2
      else if (mn_str=Globals.release_name) then
        (*release: Those variables whose @full[] have been captured in the variant
          won't exist in pure constraint after release*)
        (* TODO: VPerm *)
        let full_vars = [] in
        let fresh_vars = CP.fresh_spec_vars full_vars in
        let fct (es:CF.entail_state) =
          let new_f = CF.subst_avoid_capture_pure full_vars fresh_vars es.CF.es_formula in
          CF.Ctx {es with CF.es_formula = new_f;}
        in
        if (full_vars!=[]) then
          CF.transform_list_failesc_context (idf,idf,fct) tmp_res
        else tmp_res
      else
        (*init/finalize: do nothing*)
        tmp_res
    in
    tmp_res2
(*============================================================*)
(*== <<< init/finalize/acquires/release[LOCK](lock,args) =====*)
(*============================================================*)

and check_exp prog proc ctx (e0:exp) label =
  let pr = Cprinter.string_of_list_failesc_context in
  Debug.no_2 "check_exp" pr (Cprinter.string_of_exp) pr (fun _ _ ->
      Gen.Profiling.push_time "check_exp_a";
      try
        let res = check_exp_a prog proc ctx e0 label in
        Gen.Profiling.pop_time "check_exp_a"; res
      with ex -> Gen.Profiling.pop_time "check_exp_a"; raise ex
    ) ctx e0

(* WN_2_Loc : to be implemented by returing xpure of asserted f formula*)
and get_xpure_of_formula f = 1

and check_exp_a (prog : prog_decl) (proc : proc_decl)
    (ctx : CF.list_failesc_context) (e0:exp) (post_start_label:formula_label):
  CF.list_failesc_context =
  let () = Synt.repair_proc := Some proc in
  let ctx = if !Globals.tc_drop_unused then
      let f es = CF.Ctx{
          es with
          CF.es_formula = CF.elim_e_var !proc_used_names es.CF.es_formula
        } in
      List.map (CF.transform_failesc_context (idf,idf,f)) ctx
    else ctx in
  if (exp_to_check e0) then CF.find_false_list_failesc_ctx ctx (Cast.pos_of_exp e0)
  else ();
  let check_exp1 (ctx : CF.list_failesc_context) : CF.list_failesc_context =
    match e0 with
    | Label e ->
      begin
        let ctx = CF.add_path_id_ctx_failesc_list ctx e.exp_label_path_id (-1) in
        let ctx = CF.add_cond_label_list_failesc_context (fst e.exp_label_path_id)
            (snd e.exp_label_path_id) ctx in
        (x_add check_exp prog proc ctx e.exp_label_exp post_start_label)
      end
    | Unfold ({exp_unfold_var = sv;
               exp_unfold_pos = pos}) ->
      SV.unfold_failesc_context (prog,None) ctx sv true pos
    (* for code *)
    | Assert ({ exp_assert_asserted_formula = c_assert_opt;
                exp_assert_assumed_formula = c_assume_opt;
                exp_assert_infer_vars = ivars;
                exp_assert_path_id = (pidi,s);
                exp_assert_type = atype;
                exp_assert_pos = pos}) ->
      let assert_assume_msg = match c_assert_opt with
        | None -> ""
        | Some f -> (
            match c_assume_opt with
            | None -> !CF.print_struc_formula f
            | Some post -> !CF.print_struc_formula
                             (CF.add_post
                                (CF.mkE_ensures_f post (CF. mkTrueFlow ()) no_pos) f)
          )
      in
      let assert_op ()=
        let () = if !print_proof && (match c_assert_opt with | None -> false | Some _ -> true) then
            begin
              Prooftracer.push_assert_assume e0;
              Prooftracer.add_assert_assume e0;
              Prooftracer.start_compound_object ();
              Tpdispatcher.push_suppress_imply_output_state ();
              Tpdispatcher.unsuppress_imply_output ();
            end in
        begin
          if !Globals.dis_ass_chk then ctx else
            let () = proving_loc#set pos in
            let s1 = snd post_start_label in
            if (String.length s)>0 && (String.compare s s1 <> 0) then ctx
            else
              let (ts,ps) = List.partition (fun (fl,el,sl)-> (List.length fl) = 0) ctx in
              let new_ctx,pure_info,assert_failed_msg = match c_assert_opt with
                | None -> ts,None, None
                | Some c1 ->
                  let c1 = x_add Cvutil.prune_pred_struc prog true c1 in
                  (* specialise asserted formula *)
                  let c1 = match c_assume_opt with
                    | None ->
                      (* WN_2_Loc: clear c1 of inferred info first *)
                      let pr2 = Cprinter.string_of_struc_formula in
                      let c1a = CF.clear_infer_from_context c1 in
                      let () = x_tinfo_hp (add_str "c1(before clear)" pr2) c1 no_pos in
                      let () = x_tinfo_hp (add_str "c1(after clear)" pr2) c1a no_pos in
                      c1a
                    | Some _ -> c1
                  in
                  let to_print = "Proving assert/assume in method "
                                 ^ proc.proc_name ^ " for spec: \n"
                                 ^ assert_assume_msg ^ "\n" in
                  x_binfo_pp (*print_info "assert"*) to_print pos;
                  let rs,prf = x_add SV.heap_entail_struc_list_failesc_context_init
                      4 prog false false ts c1 None None None pos None in
                  let () = PTracer.log_proof prf in

                  (*do not display the context if deploy in website*)
                  if not !Globals.web_compile_flag then
                    begin
                      Debug.pprint(*print_info "assert"*) (
                        "assert condition:\n"
                        ^ (Cprinter.string_of_struc_formula c1)) pos;
                      x_tinfo_hp (add_str "assert(inp-formula)"
                                    Cprinter.string_of_struc_formula) c1 pos;
                      x_tinfo_hp (add_str "assert(res-failesc)"
                                    Cprinter.string_of_list_failesc_context) rs
                        pos
                    end;
                  if CF.isSuccessListFailescCtx_new rs then
                    begin
                      Debug.print_info "assert"
                        (s ^(if (CF.isNonFalseListFailescCtx ts) then " : ok\n"
                             else ": unreachable\n")) pos;
                      x_tinfo_pp ("Residual:\n"
                                  ^ (Cprinter.string_of_list_failesc_context rs)) pos;
                      (* WN_2_Loc: put xpure of asserted by fn below  *)
                      let xp = get_xpure_of_formula c_assert_opt in
                      (rs,Some xp,None)
                    end
                  else
                    (*L2: todo: should not warning if post is must error*)
                    let _,fk,_= CF.get_failure_list_failesc_context_ext rs in
                    let fk_msg = match fk with
                      | CF.Failure_Must _ -> " (must)"
                      | CF.Failure_May _ -> " (may)"
                      | _ -> ""
                    in
                    let msg =  (s ^" : failed"^fk_msg ^ "\n") in
                    (Debug.print_info
                       "assert/assume" msg pos;
                     (rs,None, Some (msg,fk_msg)))
              in
              let () = if !print_proof  && (match c_assert_opt
                                            with | None -> false |
                                              Some _ -> true) then
                  begin
                    Prooftracer.add_assert_assume e0;
                    (* Prooftracer.end_object (); *)
                    Prooftracer.pop_div ();
                    Prooftracer.pop_div ();
                    Tpdispatcher.restore_suppress_imply_output_state ();
                  end in
              let res = match c_assume_opt with
                | None ->
                  begin
                    match pure_info with
                    | None ->
                      let () = x_tinfo_pp ("WN : place to act on infer_assume") no_pos in
                      let () = if ivars!=[]
                        then x_tinfo_hp (add_str "infer_assume"
                                           Cprinter.string_of_spec_var_list)
                            ivars pos in
                      if ivars==[] then ts
                      else (* failwith "to impl" *)
                        List.map (fun (bf,es,bl) ->
                            (bf,es,List.map (fun (pt,c,fopt) ->
                                 (pt,Infer.add_infer_vars_ctx ivars c,fopt)) bl)) ts
                    | Some p ->
                      (* WN_2_Loc: add p to ts; add new_infer from new_ctx into ts *)
                      CF.add_pure_and_infer_from_asserted p new_ctx ts
                  end
                | Some c ->
                  let c = if (!Globals.allow_locklevel) then
                      (*Some assumption may contain waitlevel,
                        translate before adding them into current state*)
                      CF.translate_waitlevel_formula c
                    else c
                  in
                  let c = x_add Cvutil.prune_preds prog false c in (* specialise assumed formula *)
                  let () = Debug.ninfo_hprint
                      (add_str "new_ctx" Cprinter.string_of_list_failesc_context
                      ) new_ctx pos in
                  let assumed_ctx =
                    CF.normalize_max_renaming_list_failesc_context c pos false
                      new_ctx in
                  let () = Debug.ninfo_hprint (add_str "assumed_ctx"
                                                 Cprinter.string_of_list_failesc_context)
                      assumed_ctx pos in
                  let r =if !Globals.disable_assume_cmd_sat then assumed_ctx
                    else
                      CF.transform_list_failesc_context
                        (idf,idf,(SV.elim_unsat_es 4 prog (ref 1))) assumed_ctx in
                  let res = List.map (x_add_1 CF.remove_dupl_false_fe) r in
                  match assert_failed_msg with
                  | None -> res
                  | Some (s,fk_msg) -> begin
                      let () = Debug.ninfo_hprint
                          (add_str "!Globals.enable_error_as_exc" string_of_bool
                          ) !Globals.enable_error_as_exc pos in
                      if (infer_const_obj # is_err_must
                          || !Globals.enable_error_as_exc
                          || (CF.isSuccessListFailescCtx_new res)) then
                        let idf = (fun c -> c) in
                        let to_print = "Proving assert/assume in method "
                                       ^ proc.proc_name ^ " ("
                                       ^ (string_of_loc pos) ^ ") Failed"
                                       ^ fk_msg in
                        CF.transform_list_failesc_context
                          (idf,idf,
                           (fun es -> CF.Ctx{es with CF.es_final_error
                                                     = CF.acc_error_msg
                                                         es.CF.es_final_error
                                                         to_print})) res
                      else
                        begin
                          (*L2: this code fragment may never be reached since we
                            set is_err_must in the wrapper*)
                          if not !Globals.disable_failure_explaining then
                            let s,fk,_= CF.get_failure_list_failesc_context new_ctx in
                            raise (Err.Ppf ({
                                Err.error_loc = pos;
                                Err.error_text = s
                              },(match fk with
                                | CF.Failure_Bot _ -> 0
                                | CF.Failure_Must _ -> 1
                                | CF.Failure_Valid -> 2
                                | CF.Failure_May _ -> 3), 2))
                          else
                            begin
                              Debug.print_info
                                ("(" ^
                                 (Cprinter.string_of_label_list_failesc_context
                                    new_ctx)^") "
                                ) ("Proving assert/assume in method failed\n") pos;
                              Debug.print_info ("(Cause of Assert Failure)")
                                (Cprinter.string_of_failure_list_failesc_context  new_ctx) pos;
                              Err.report_error {
                                Err.error_loc = pos;
                                Err.error_text = Printf.sprintf
                                    "Proving Assert/Assume in method failed."
                              }
                            end
                        end
                    end
              in
              let () = Debug.ninfo_hprint
                  (add_str "res" Cprinter.string_of_list_failesc_context) res
                  pos in
              (ps@res)
        end
      in
      (* assert/assume, efa-exc is turned on by default*)
      let assert_op_wrapper ()=
        (match c_assume_opt with
         | Some _ ->
           wrap_err_assert_assume (* efa_exc (Some true) *) assert_op ()
         | None -> (assert_op ())
        )
      in
      (* why is wrap classic needed for assert/assume? *)
      (* Ans : classic or not is based on atype *)
      (wrap_proving_kind
         (match c_assume_opt with
            None -> if ivars==[] then PK_Assert else PK_Infer_Assume
          | _ -> PK_Assert_Assume)
         (wrap_classic x_loc atype (assert_op_wrapper))) ()

    | Assign {
        exp_assign_lhs = v;
        exp_assign_rhs = rhs;
        exp_assign_pos = pos
      } ->
      let pr = Cprinter.string_of_exp in
      let () = x_tinfo_hp (add_str "ctx before rhs: "
                             Cprinter.string_of_list_failesc_context) ctx no_pos in
      let check_rhs_exp rhs = Debug.no_1 "check Assign (rhs)" pr
          (Cprinter.string_of_list_failesc_context) (fun rhs ->
              x_add check_exp prog proc ctx rhs post_start_label) rhs in
      let assign_op () =
        begin
          let () = proving_loc # set pos in
          let b =
            if !ann_vp then
              let tv = Gen.unsome (type_of_exp rhs) in
              let sv = (CP.SpecVar (tv, v, Unprimed)) in
              let full_f = VP.formula_of_vperm_anns [(VP_Full, [sv])] in
              let full_f = CF.set_flow_in_formula_override
                  { CF.formula_flow_interval = !norm_flow_int;
                    CF.formula_flow_link = None } full_f in
              let vperm_res, _ = SV.heap_entail_list_failesc_context_init prog
                  false ctx full_f None None None pos None in
              if not (CF.isSuccessListFailescCtx_new vperm_res) then
                let msg = (v ^ " does not have @full permission to write.") in
                (Debug.print_info
                   ("(" ^ (Cprinter.string_of_label_list_failesc_context
                             vperm_res) ^ ") ") msg pos;
                 Debug.print_info ("(Cause of ParCase Failure)")
                   (Cprinter.string_of_failure_list_failesc_context vperm_res)
                   pos;
                 Err.report_error { Err.error_loc = pos; Err.error_text = msg })
              else true
            else true in
          if not b then ctx
          else
            let ctx1 = check_rhs_exp rhs in
            let () = CF.must_consistent_list_failesc_context "assign 1" ctx1  in
            let fct c1 =
              let res = if (CF.subsume_flow_f !norm_flow_int
                              (CF.flow_formula_of_formula c1.CF.es_formula))
                then
                  let t0 = Gen.unsome (type_of_exp rhs) in
                  (* Loc: find an appropriate type of v instead of null_type (swl example).
                     it is better for shape inference *)
                  let t = if is_null_type t0 then
                      let svl = CF.fv c1.CF.es_formula in
                      try
                        let orig_sv = List.find (fun sv ->
                            String.compare (CP.name_of_spec_var sv) v = 0) svl in
                        CP.type_of_spec_var orig_sv
                      with _ -> t0
                    else t0 in
                  let vsv = CP.SpecVar (t, v, Primed) in (* rhs must be non-void *)
                  let tmp_vsv = CP.fresh_spec_var vsv in
                  let compose_es =
                    x_add CF.subst [(vsv, tmp_vsv); ((P.mkRes t), vsv)]
                      c1.CF.es_formula in
                  let compose_ctx = (CF.Ctx ({c1 with CF.es_formula = compose_es})) in
                  compose_ctx
                else (CF.Ctx c1) in
              res in
            let () = x_tinfo_hp (add_str "ctx Assign before: "
                             Cprinter.string_of_list_failesc_context) ctx1 no_pos in
            let () = x_tinfo_hp (add_str "rhs: "
                                     (Cprinter.string_of_exp))
                  rhs no_pos in
            let res = CF.transform_list_failesc_context (idf,idf,fct) ctx1 in
            let () = CF.must_consistent_list_failesc_context "assign final" res in
            let () = x_tinfo_hp (add_str "ctx Assign final: "
                             Cprinter.string_of_list_failesc_context) res no_pos in
            res
        end in
      Gen.Profiling.push_time "[check_exp] Assign";
      let res = wrap_proving_kind PK_Assign_Stmt assign_op () in
      Gen.Profiling.pop_time "[check_exp] Assign";
      res
    | Barrier {exp_barrier_recv = b; exp_barrier_pos = pos} ->
      let mkprf prf_l = PTracer.ContextList
          {PTracer.context_list_ante = [];
           PTracer.context_list_conseq = CF.mkETrue (CF.mkTrueFlow ()) pos;
           PTracer.context_list_proofs = prf_l; } in
      let rec process_ctx ctx = match ctx with
        | CF.OCtx (c1, c2) ->
          let r1, p1  = process_ctx c1 in
          let r2, p2  = process_ctx c2 in
          (CF.or_list_context r1 r2),
          (PTracer.mkOrStrucLeft ctx (CF.mkETrue (CF.mkTrueFlow ()) pos) [p1;p2])
        | CF.Ctx c ->
          match CF.find_barr (List.map (fun c-> c.barrier_name)
                                prog.prog_barrier_decls) (snd b) c.CF.es_formula
          with
          | None -> report_error pos ("context does not contain any info on barrier "^(snd b))
          | Some bar_dn ->
            let bn,args,branches = bar_dn.CF.h_formula_data_name,
                                   bar_dn.CF.h_formula_data_node
                                   ::bar_dn.CF.h_formula_data_arguments,
                                   bar_dn.CF.h_formula_data_remaining_branches
            in
            let bd = try List.find (fun c-> bn=c.barrier_name)
                           prog.prog_barrier_decls
              with | _ -> failwith "error in barr find " in
            let from_v = CP.SpecVar(Named bn,self, Unprimed)::bd.barrier_shared_vars in
            let bd_spec = CF.subst_struc (List.combine from_v args)
                (CF.filter_bar_branches branches bd.barrier_def) in
            let helper c bd_spec =
              let pr1 c = Cprinter.string_of_context (CF.Ctx c) in
              let pr2 f = Cprinter.string_of_struc_formula f in
              Debug.no_2 "barrier entail" pr1 pr2 (fun c-> "")
                (fun _ _ -> x_add SV.heap_entail_struc_init prog false true
                    (CF.SuccCtx [CF.Ctx c]) bd_spec pos None) c bd_spec
            in
            helper c bd_spec in

      let barr_failesc_context (f,e,n) =
        let esc_skeletal = List.map (fun (l,_) -> (l,[])) e in
        let res = List.map (fun (lbl,c2, oft)->
            let list_context_res,prf =process_ctx c2 in
            match list_context_res with
            | CF.FailCtx (t,c,_) -> begin
                let lc = if Globals.global_efa_exc () then
                    ([([],esc_skeletal, [((lbl, c ,Some t))])])
                  else [([(lbl,t)],esc_skeletal,[])]
                in
                lc,prf
              end
            | CF.SuccCtx ls -> List.map ( fun c-> ([],esc_skeletal,[(lbl,c, oft)])) ls,prf) n in
        let res_l,prf_l =List.split res in
        let res = List.fold_left (CF.list_failesc_context_or
                                    Cprinter.string_of_esc_stack) [(f,e,[])]
            res_l in
        (res, mkprf prf_l)  in

      let barr_failesc_context (f,e,n) =
        let pr1 (_,_,n) = pr_list (fun (_,c,_)-> Cprinter.string_of_context c) n in
        let pr2 (l,_) = String.concat "\n result: "
            (List.map (fun (_,_,c)-> pr_list (fun (_,ctx,_)->
                 Cprinter.string_of_context ctx) c) l) in
        Debug.no_1 "barrier_failesc_context" pr1 pr2 barr_failesc_context (f,e,n
                                                                          ) in

      let to_print = ("\nVerification Context:"^(post_pos#string_of_pos)^"\nBarrier call \n") in
      x_dinfo_zp (lazy (to_print^"\n")) pos;

      if (ctx==[]) then []
      else
        let r = List.map barr_failesc_context ctx in
        let r_ctx , prf_r = List.split r in
        let rs = List.fold_left CF.list_failesc_context_union (List.hd r_ctx) (List.tl r_ctx) in
        let () = PTracer.log_proof (mkprf prf_r) in
        if (CF.isSuccessListFailescCtx ctx) && (CF.isFailListFailescCtx rs)
        then Debug.print_info "barrier call" (to_print^" has failed \n") pos
        else () ;
        rs

    | BConst ({exp_bconst_val = b;
               exp_bconst_pos = pos}) -> begin
        Gen.Profiling.push_time "[check_exp] BConst";
        try
          let res_v = CP.mkRes bool_type in
          let tmp1 = CP.BForm ((CP.BVar (res_v, pos), None), None) in
          let tmp2 =
            if b then tmp1
            else CP.Not (tmp1, None, pos) in
          let f = CF.formula_of_pure_N tmp2 pos in
          let res = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
          Gen.Profiling.push_time "[check_exp] BConst";
          res
        with ex -> Gen.Profiling.pop_time "[check_exp] BConst"; raise ex
      end

    | Bind ({
        exp_bind_type = body_t;
        exp_bind_bound_var = (v_t, v); (* node to bind *)
        exp_bind_fields = lvars; (* fields of bound node *)
        exp_bind_body = body;
        exp_bind_imm = imm_node; (* imm annotation for the node *)
        exp_bind_param_imm = pimm; (* imm annotation for each field *)
        exp_bind_read_only = read_only;
        exp_bind_path_id = pid;
        exp_bind_pos = pos }) ->
      (* this creates a new esc_level for the bind construct to capture all
         exceptions from this construct *)
      let () = x_tinfo_hp (add_str "ctx bind start: "
                             Cprinter.string_of_list_failesc_context) ctx no_pos  in
      let ctx = CF.transform_list_failesc_context
          (idf,(fun c-> CF.push_esc_level c pid),(fun x-> CF.Ctx x)) ctx in
      let bind_op () =
        begin
          x_tinfo_pp ">>>>>> bind type-checker <<<<<<" pos;
          x_tinfo_hp (add_str "node" (fun x -> x)) v pos;
          x_tinfo_hp (add_str "fields" (pr_list (fun (_,x) -> x))) lvars pos;
          x_tinfo_hp (add_str "imm_node" Cprinter.string_of_imm) imm_node pos;
          x_tinfo_hp (add_str "fields ann" (pr_list Cprinter.string_of_imm)) pimm pos;
          x_tinfo_hp (add_str "read-only" string_of_bool) read_only pos;
          (* yes below is safe *)
          check_var_read_perm ~msg:"(inside bind)" prog ctx pos v v_t;
          let ctx =
            if !ann_vp then
              let vperm_fields =
                CVP.vperm_sets_of_anns [(VP_Full,
                  List.map (fun (t, i) -> CP.SpecVar (t, i, Unprimed)) lvars)] in
              VP.add_vperm_sets_list_failesc_ctx vperm_fields ctx
            else ctx in
          let () = proving_loc#set pos in
          let lsv = List.map (fun (t,i) -> CP.SpecVar(t,i,Unprimed)) lvars in
          let field_types, vs = List.split lvars in
          let v_prim = CP.SpecVar (v_t, v, Primed) in
          let vs_prim = List.map2 (fun v -> fun t -> CP.SpecVar (t, v, Primed)) vs field_types in
          let p = CP.fresh_spec_var v_prim in
          let link_pv = CF.formula_of_pure_N
              (CP.mkAnd (CP.mkEqVar v_prim p pos)
                 (CP.BForm ((CP.mkNeq (CP.Var (p, pos)) (CP.Null pos) pos, None)
                           , None)) pos) pos in
          let tmp_ctx =
            if !Globals.large_bind then
              CF.normalize_max_renaming_list_failesc_context link_pv pos false ctx
            else ctx in
          let () = CF.must_consistent_list_failesc_context "bind 1" ctx  in
          let unfolded = SV.unfold_failesc_context (prog,None) tmp_ctx v_prim true pos in
          let unfolded =  CF.transform_list_failesc_context
              (idf,idf, (fun es -> CF.Ctx (CF.clear_entailment_es_pure es)))
              unfolded in
          let () = CF.must_consistent_list_failesc_context "bind 2" unfolded  in
          let () = x_dinfo_zp (lazy ("bind: unfolded context:\n"
                                     ^ (Cprinter.string_of_list_failesc_context
                                          unfolded)
                                     ^ "\n")) pos in
          let unfolded =
            let idf = (fun c -> c) in
            CF.transform_list_failesc_context
              (idf,idf,
               (fun es -> CF.Ctx{es with CF.es_formula = Norm.imm_norm_formula
                                             prog es.CF.es_formula
                                             Solver.unfold_for_abs_merge pos;}))
              unfolded in
          let c = string_of_typ v_t in
          let fresh_perm_exp,perm_vars =
            (match !Globals.perm with
             | Bperm ->
               let c_name = x_add_1 Cpure.fresh_old_name "cbperm" in
               let t_name = x_add_1 Cpure.fresh_old_name "tbperm" in
               let a_name = x_add_1 Cpure.fresh_old_name "abperm" in
               let c_var = Cpure.SpecVar (Globals.Int,c_name, Unprimed) in
               let t_var = Cpure.SpecVar (Globals.Int,t_name, Unprimed) in
               let a_var = Cpure.SpecVar (Globals.Int,a_name, Unprimed) in
               Cpure.Bptriple ((c_var,t_var,a_var),pos), [c_var;t_var;a_var]
             | _ ->
               let fresh_perm_name = x_add_1 Cpure.fresh_old_name "f" in
               let perm_t = cperm_typ () in
               let perm_var = Cpure.SpecVar (perm_t,fresh_perm_name, Unprimed) in (*LDK TO CHECK*)
               Cpure.Var (perm_var,no_pos),[perm_var]) in
          let bind_ptr = if !Globals.large_bind then p else v_prim in
          let vdatanode = CF.DataNode ({
              CF.h_formula_data_node = bind_ptr;
              CF.h_formula_data_name = c;
              CF.h_formula_data_derv = false; (*TO CHECK: assume false*)
              CF.h_formula_data_split = SPLIT0; (*TO CHECK: assume false*)
              CF.h_formula_data_imm = imm_node;
              CF.h_formula_data_param_imm = pimm;
              CF.h_formula_data_perm = if (Perm.allow_perm ())
                then Some fresh_perm_exp else None;
              (*LDK: belong to HIP, deal later ???*)
              CF.h_formula_data_origins = []; (*deal later ???*)
              CF.h_formula_data_original = true; (*deal later ???*)
              CF.h_formula_data_arguments = (*t_var :: ext_var ::*) vs_prim;
              CF.h_formula_data_holes = []; (* An Hoa : Don't know what to do *)
              CF.h_formula_data_label = None;
              CF.h_formula_data_remaining_branches = None;
              CF.h_formula_data_pruning_conditions = [];
              CF.h_formula_data_pos = pos}) in
          let vheap = CF.formula_of_heap vdatanode pos in
          let vheap =
            if Globals.infer_const_obj # is_ana_ni
            then CF.mk_bind_ptr_f bind_ptr else vheap in
          let () = x_tinfo_hp (add_str "bind_ptr" (!CP.print_sv)) bind_ptr pos in
          let () = x_tinfo_hp (add_str "vs_prim" (!CP.print_svl)) vs_prim pos in
          let () = x_tinfo_hp (add_str "vheap(0)" (Cprinter.string_of_formula)) vheap pos in
          let vheap =
            if (Perm.allow_perm ()) then
              (*there exists fresh_perm_exp statisfy ... *)
              if (read_only)
              then
                let read_f = mkPermInv () fresh_perm_exp in
                CF.mkBase vdatanode (MCP.memoise_add_pure_N (MCP.mkMTrue pos)
                                       read_f) CVP.empty_vperm_sets CF.TypeTrue
                  (CF.mkTrueFlow ()) [] pos
              else
                let write_f = mkPermWrite () fresh_perm_exp in
                CF.mkBase vdatanode (MCP.memoise_add_pure_N (MCP.mkMTrue pos)
                                       write_f) CVP.empty_vperm_sets CF.TypeTrue
                  (CF.mkTrueFlow ()) [] pos
            else
              vheap in
          let () = x_tinfo_hp (add_str "vheap 2" Cprinter.string_of_formula) vheap no_pos in
          let vheap = x_add_1 Immutable.normalize_field_ann_formula vheap in
          let vheap = x_add Cvutil.prune_preds prog false vheap in
          let () = x_tinfo_hp (add_str "vheap 3" (Cprinter.string_of_formula)) vheap pos in
          (* WN : provided implicit instantation to vs_prim *)
          let struc_vheap = CF.EBase {
              CF.formula_struc_explicit_inst = [];
              CF.formula_struc_implicit_inst =
                (if (Perm.allow_perm ()) then perm_vars else [])@vs_prim;
              (*need to instantiate f*)
              CF.formula_struc_exists = [] ;
              CF.formula_struc_base = vheap;
              CF.formula_struc_is_requires = false;
              CF.formula_struc_continuation = None;
              CF.formula_struc_pos = pos} in
          let to_print = "Proving binding in method " ^ proc.proc_name
                         ^ " for spec " ^ !log_spec ^ "\n" in
          x_tinfo_pp to_print pos;
          let () = repair_proc := Some (proc.Cast.proc_name) in
          if (Gen.is_empty unfolded) then
            let () = y_tinfo_pp "unfolded body is empty" in
            unfolded
          else
            let () = consume_all := true in
            let () = y_tinfo_pp "need to use local version of infer_const_obj" in
            let () = x_tinfo_hp (add_str "struc_vheap"
                                   Cprinter.string_of_struc_formula) struc_vheap
                no_pos in
            let fn = SV.heap_entail_struc_list_failesc_context_init 5 prog false
                true unfolded struc_vheap None None None pos in
            let rs_prim, prf = x_add Wrapper.wrap_classic x_loc (Some false) fn (Some pid) in
            (* recover classic_frame for mem leak detection at post proving*)
            let () = consume_all := false in
            let () = CF.must_consistent_list_failesc_context "bind 3" rs_prim  in
            let () = PTracer.log_proof prf in
            let rs = CF.clear_entailment_history_failesc_list (fun x -> None) rs_prim in
            let () = CF.must_consistent_list_failesc_context "bind 4" rs  in
            if (CF.isSuccessListFailescCtx_new unfolded) &&
               (not(CF.isSuccessListFailescCtx_new rs))
            then
              begin
                if Globals.is_en_efa_exc () && (Globals.global_efa_exc ())
                then
                  let to_print = ("bind 3: node " ^ (Cprinter.string_of_formula
                                                       vheap ) ^
                                  " cannot be derived from context (")
                                 ^ (string_of_loc pos) ^ ")" in
                  let idf = (fun c -> c) in
                  CF.transform_list_failesc_context
                    (idf,idf,
                     (fun es -> CF.Ctx{es with CF.es_final_error
                                               = CF.acc_error_msg
                                                   es.CF.es_final_error to_print
                                      }))
                    rs
                else
                  let () = repair_loc := Some VarGen.proving_loc#get in
                  let s =  ("\n("^(Cprinter.string_of_label_list_failesc_context rs)^") ")^
                           ("bindxxx: node " ^ (Cprinter.string_of_formula vheap) ^
                            " cannot be derived from context\n") ^ (string_of_loc pos) ^"\n\n"
                           (* add branch info *)
                           ^ ("(Cause of Bind Failure)") ^
                           (Cprinter.string_of_failure_list_failesc_context rs )
                           ^ (string_of_loc pos) in
                  raise (Err.Ppf ({
                      Err.error_loc = pos;
                      Err.error_text = (to_print ^ s)
                    }, 1, 0))
                  raise (Err.Ppf ({
                      Err.error_loc = pos;
                      Err.error_text = (to_print ^ s)
                    }, 1, 0))
              end
            else
              begin
                stk_vars # push_list lsv;
                let () = x_tinfo_hp (add_str "inside bind" pr_id)
                    (stk_vars # string_of_no_ln) no_pos in
                let tmp_res1 = x_add check_exp prog proc rs body post_start_label in
                stk_vars # pop_list lsv;
                let () = CF.must_consistent_list_failesc_context "bind 5" tmp_res1  in
                let tmp_res2 =
                  if not(CP.isLend imm_node) && not(CP.isAccs imm_node)
                  (* asankhs: Do not change this please&& not(!Globals.allow_field_ann)*) then
                    CF.normalize_max_renaming_list_failesc_context_4_bind pid
                      vheap pos true tmp_res1
                      (* for Lend, Accs it should not be added back and
                         field level annotations should be added back and compacted *)
                  else tmp_res1
                in
                x_tinfo_pp "WN : adding vheap to exception too" no_pos;
                x_tinfo_hp (add_str "bind:vheap" Cprinter.string_of_formula) vheap no_pos;
                x_tinfo_hp (add_str "bind:tmp_res1"
                              (pr_list Cprinter.string_of_failesc_context))
                  tmp_res1 no_pos;
                let () = CF.must_consistent_list_failesc_context "bind 6" tmp_res2  in
                let bind_field = CF.mk_bind_fields_struc vs_prim in
                let tmp_res2 =
                  let idf = (fun c -> c) in
                  CF.transform_list_failesc_context
                    (idf,idf,
                     (fun es ->
                        let es_f = if Globals.infer_const_obj # is_ana_ni then
                            CF.mkAnd_pure es.CF.es_formula (MCP.mix_of_pure bind_field) no_pos
                          else es.CF.es_formula in
                        CF.Ctx{es with CF.es_formula = Norm.imm_norm_formula
                                           prog es_f Solver.unfold_for_abs_merge
                                           pos;}))
                    tmp_res2
                in
                let tmp_res2 = SV.prune_ctx_failesc_list prog tmp_res2 in
                x_tinfo_hp (add_str "bind:tmp_res2"
                              (pr_list Cprinter.string_of_failesc_context))
                  tmp_res2 no_pos;
                let tmp_res3 = x_add CF.push_exists_list_failesc_context vs_prim tmp_res2 in
                x_tinfo_hp (add_str "bind:tmp_res3"
                              (pr_list Cprinter.string_of_failesc_context))
                  tmp_res3 no_pos;
                let () = CF.must_consistent_list_failesc_context "bind 7" tmp_res3  in
                let res = if !Globals.elim_exists_ff
                  then SV.elim_exists_failesc_ctx_list tmp_res3 else tmp_res3 in
                let () = CF.must_consistent_list_failesc_context "bind 8" res  in
                x_tinfo_hp (add_str "bind:tmp_res2"
                              (pr_list Cprinter.string_of_failesc_context))
                  res no_pos;
                (* normalize_list_failesc_context_w_lemma prog res *)
                CF.pop_esc_level_list res pid
              end
        end  (*end Bind*)
      in
      (* bind, efa-exc is turned on by default*)
      let bind_op_wrapper () =
        wrap_err_bind bind_op ()
      in
      wrap_proving_kind PK_BIND bind_op_wrapper ()

    | Block ({
        exp_block_type = t;
        exp_block_body = e;
        exp_block_local_vars = local_vars;
        exp_block_pos = pos }) ->
      begin
        Gen.Profiling.push_time "[check_exp] Block";
        try
          let vss = List.map (fun (t,i) -> CP.SpecVar (t, i, Unprimed)) local_vars in
          stk_vars # push_list vss;
          let () = x_tinfo_hp (add_str "block" pr_id) (stk_vars # string_of_no_ln) no_pos in
          let ctx1 = x_add check_exp prog proc ctx e post_start_label in
          let () = x_tinfo_hp (add_str "CTX1: "
                                 Cprinter.string_of_list_failesc_context) ctx1
              no_pos in
          stk_vars # pop_list vss;
          let ctx1 = VP.clear_vperm_sets_list_failesc_ctx [(VP_Full, vss)] ctx1 in
          let svars = List.map (fun (t, n) -> CP.SpecVar (t, n, Primed)) local_vars in
          (* Do not push exists on nondet local vars *)
          let nd_vars = CF.collect_nondet_vars_list_failesc_context ctx1 in
          let svars = Gen.BList.difference_eq CP.eq_spec_var svars nd_vars in
          let ctx2 = x_add CF.push_exists_list_failesc_context svars ctx1 in
          let () = x_tinfo_hp (add_str "CTX2: "
                                 Cprinter.string_of_list_failesc_context) ctx2
              no_pos in
          let res = if !Globals.elim_exists_ff then SV.elim_exists_failesc_ctx_list ctx2 else ctx2 in
          Gen.Profiling.pop_time "[check_exp] Block";
          let () = x_tinfo_hp (add_str "check_exp block res: "
                                 Cprinter.string_of_list_failesc_context) res
              no_pos in
          res
        with ex -> Gen.Profiling.pop_time "[check_exp] Block"; raise ex
      end
    | Cast ({ exp_cast_target_type = target_typ;
              exp_cast_body = org_exp;
              exp_cast_pos = pos}) -> (
        let check_cast_body body = (
          let pr = Cprinter.string_of_exp in
          Debug.no_1 "check_cast_body" pr (fun _ -> "void")
            (fun rhs -> x_add check_exp prog proc ctx body post_start_label) body
        ) in
        let casting_op () = (
          let () = proving_loc#set pos in
          let ctx1 = check_cast_body org_exp in
          let () = CF.must_consistent_list_failesc_context "assign 1" ctx1  in
          let org_typ = Gen.unsome (type_of_exp org_exp) in
          let tempvar = CP.SpecVar (org_typ, Globals.fresh_name (), Primed) in
          let fct c1 =
            if (CF.subsume_flow_f !norm_flow_int (CF.flow_formula_of_formula c1.CF.es_formula)) then
              let compose_es = x_add CF.subst [((P.mkRes org_typ), tempvar)] c1.CF.es_formula in
              let compose_ctx = (CF.Ctx ({c1 with CF.es_formula = compose_es})) in
              compose_ctx
            else (CF.Ctx c1) in
          let res = CF.transform_list_failesc_context (idf,idf,fct) ctx1 in
          let res_v = CP.Var (CP.mkRes target_typ, pos) in
          let tempvar_exp = CP.Var (tempvar, pos) in
          let typcast_exp = CP.TypeCast (target_typ, tempvar_exp, pos) in
          let target_exp = CP.mkEqExp res_v typcast_exp pos in
          let f = CF.formula_of_mix_formula (MCP.mix_of_pure target_exp) pos in
          let res_ctx = CF.normalize_max_renaming_list_failesc_context f pos true res in
          let () = CF.must_consistent_list_failesc_context "assign final" res_ctx  in
          res_ctx
        ) in
        Gen.Profiling.push_time "[check_exp] Cast";
        let res = wrap_proving_kind PK_Cast casting_op () in
        Gen.Profiling.pop_time "[check_exp] Cast";
        res
      )
    | Catch b -> Error.report_error {
        Err.error_loc = b.exp_catch_pos;
        Err.error_text = "[typechecker.ml]: malformed cast, unexpected catch clause"
      }
    | Cond ({ exp_cond_type = t;
              exp_cond_condition = v;
              exp_cond_then_arm = e1;
              exp_cond_else_arm = e2;
              exp_cond_path_id = pid;
              exp_cond_pos = pos}) ->
      let () = x_tinfo_hp (add_str "ctx cond start: "
                             Cprinter.string_of_list_failesc_context) ctx no_pos  in
      let cond_op () =
        begin
          let () = proving_loc#set pos in
          let pure_cond = (CP.BForm ((CP.mkBVar v Primed pos, None), None)) in
          let then_cond_prim = MCP.mix_of_pure pure_cond in
          let else_cond_prim = MCP.mix_of_pure (CP.mkNot pure_cond None pos) in
          let then_ctx = if !Globals.delay_if_sat
            then SV.combine_list_failesc_context prog ctx then_cond_prim
            else  SV.combine_list_failesc_context_and_unsat_now prog ctx
                then_cond_prim in
          let () = x_tinfo_hp (add_str "then ctx: "
                                 Cprinter.string_of_list_failesc_context) then_ctx no_pos  in
          x_dinfo_zp (lazy ("conditional: then_delta:\n"
                            ^ (Cprinter.string_of_list_failesc_context then_ctx)
                           )) pos;
          let else_ctx =
            if !Globals.delay_if_sat then SV.combine_list_failesc_context prog ctx else_cond_prim
            else SV.combine_list_failesc_context_and_unsat_now prog ctx else_cond_prim in
          x_dinfo_zp (lazy ("conditional: else_delta:\n"
                            ^ (Cprinter.string_of_list_failesc_context else_ctx)
                           )) pos;
          let then_ctx1 = CF.add_cond_label_strict_list_failesc_context pid 1 then_ctx in
          let () = x_tinfo_hp (add_str "then ctx: "
                             Cprinter.string_of_list_failesc_context) then_ctx1 no_pos  in
          let else_ctx1 = CF.add_cond_label_strict_list_failesc_context pid 2 else_ctx in
          let then_ctx1 = CF.add_path_id_ctx_failesc_list then_ctx1 (None,-1) 1 in
          let else_ctx1 = CF.add_path_id_ctx_failesc_list else_ctx1 (None,-1) 2 in
          let then_ctx2 = if not(!disproof) then
              (x_add check_exp prog proc then_ctx1 e1) post_start_label
            else
              try
                let res = (x_add check_exp prog proc then_ctx1 e1) post_start_label in
                res
              with _ as e ->
                let () = x_binfo_hp (add_str "invalid_ent" string_of_int) !invalid_num no_pos in
                let () = x_binfo_hp (add_str "unkn_ent" string_of_int) !unkn_num no_pos in
                x_binfo_hp (add_str "valid_ent" string_of_int) !valid_num no_pos;
                (x_add check_exp prog proc else_ctx1 e2) post_start_label;
                raise e in
          let else_ctx2 = (x_add check_exp prog proc else_ctx1 e2) post_start_label in
          let res = CF.list_failesc_context_or (Cprinter.string_of_esc_stack) then_ctx2 else_ctx2 in
          res
        end in
      Gen.Profiling.push_time "[check_exp] Cond";
      let res = wrap_proving_kind PK_If_Stmt cond_op () in
      Gen.Profiling.pop_time "[check_exp] Cond";
      res
    | Dprint ({exp_dprint_string = str;
               exp_dprint_visible_names = visib_names;
               exp_dprint_pos = pos}) -> begin
        let pr1 = Cprinter.string_of_list_failesc_context in
        let () = x_tinfo_hp (add_str "ctx: " pr1) ctx no_pos in
        let curr_svl = stk_vars # get_stk in
        let () = x_tinfo_hp (add_str "Dprint" !Cpure.print_svl) curr_svl no_pos in
        let ctx2 = SV.list_failesc_context_and_unsat_now prog ctx in
        let ctx = ctx2 in
        let ctx_simp =
          if !Globals.simplify_dprint
          then x_add_1 (Cfout.simplify_failesc_context_list ~prog_vs:
                          (Some curr_svl)) ctx
          else ctx
        in
        if str = "" then begin
          let str1 = (Cprinter.string_of_list_failesc_context ctx) in
          let str2 = (Cprinter.string_of_list_failesc_context ctx_simp) in
          (if (Gen.is_empty ctx) then
             (print_string_quiet ("\ndprint:"^pos.start_pos.Lexing.pos_fname
                                  ^ ":" ^ (string_of_int
                                             pos.start_pos.Lexing.pos_lnum)
                                  ^" empty context"))
           else
             let tmp1 =
               if !Globals.simplify_dprint then ""
               else "\ndprint(orig): " ^ pos.start_pos.Lexing.pos_fname
                    ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum)
                    ^ ": ctx: " ^ str1 ^ "\n" in
             let tmp1 = if (SV.previous_failure()) then ("failesc context: "^tmp1) else tmp1 in
             let tmp2 =
               if !Globals.simplify_dprint then
                 "\ndprint(simpl): " ^ pos.start_pos.Lexing.pos_fname
                 ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^ ": ctx: " ^ str2 ^ "\n"
               else ""
             in
             let tmp2 = if (SV.previous_failure()) then ("failesc context: "^tmp2) else tmp2 in
             print_string_quiet (tmp1 ^ tmp2));
          ctx
        end else begin
          ignore (Drawing.dot_of_partial_context_file prog ctx visib_names str);
          ctx
        end
      end;
    | Debug ({exp_debug_flag = flag;
              exp_debug_pos = pos}) -> begin
        (if flag then Omega.log_mark "debug on"
         else Omega.log_mark "debug off");
        Debug.devel_debug_on := flag;
        ctx
      end;
    | ICall ({exp_icall_receiver = recv;
              exp_icall_receiver_type = recv_t; (* this is the type of the receiver *)
              exp_icall_type = ret_t; (* this is the return type *)
              exp_icall_method_name = mn;
              exp_icall_arguments = vs_prim;
              exp_icall_pos = pos}) ->
      Err.report_error {Err.error_loc = pos;
                        Err.error_text = "[typechecker.ml]: We do not support instant calls"}
    | IConst ({exp_iconst_val = i;
               exp_iconst_pos = pos}) ->
      Gen.Profiling.push_time "[check_exp] IConst";
      let c_e = CP.IConst (i, pos) in
      let res_v = CP.Var (CP.mkRes int_type, pos) in
      let c = CP.mkEqExp res_v c_e pos in
      let c =
        if !Globals.infer_lvar_slicing then
          CP.set_il_formula c (Some (false, fresh_int(), [res_v]))
        else c in
      let f = CF.formula_of_mix_formula (MCP.mix_of_pure c) pos in
      let res_ctx = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
      Gen.Profiling.pop_time "[check_exp] IConst";
      res_ctx
    | FConst {exp_fconst_val = f; exp_fconst_pos = pos} ->
      let c_e = CP.FConst (f, pos) in
      let res_v = CP.Var (CP.mkRes float_type, pos) in
      let c = CP.mkEqExp res_v c_e pos in
      let c =
        if !Globals.infer_lvar_slicing then
          CP.set_il_formula c (Some (false, fresh_int(), [res_v]))
        else c
      in
      let f = CF.formula_of_mix_formula (MCP.mix_of_pure c) pos in
      let res_ctx = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
      res_ctx
    | New ({exp_new_class_name = c;
            exp_new_parent_name = pname;
            exp_new_arguments = args;
            exp_new_pos = pos}) -> begin
        let field_types, vs = List.split args in
        let heap_args = List.map2 (fun n -> fun t -> CP.SpecVar (t, n, Primed))
            vs field_types in
        let heap_args,perm,perm_vars,perm_f = if (!Globals.perm == Globals.Bperm) then
            let bound_var = List.hd heap_args in
            let c_name = x_add_1 Cpure.fresh_old_name "cbperm" in
            let t_name = x_add_1 Cpure.fresh_old_name "tbperm" in
            let a_name = x_add_1 Cpure.fresh_old_name "abperm" in
            let c_var = Cpure.SpecVar (Globals.Int,c_name, Unprimed) in
            let t_var = Cpure.SpecVar (Globals.Int,t_name, Unprimed) in
            let a_var = Cpure.SpecVar (Globals.Int,a_name, Unprimed) in
            let perm = Some (Cpure.Bptriple ((c_var,t_var,a_var),pos)) in
            let perm_vars = [c_var;t_var;a_var] in
            let nheap_args = List.tl heap_args in
            let c_f = Cpure.mkEqVar c_var bound_var pos in
            let t_f = Cpure.mkEqVar t_var bound_var pos in
            let a_f = Cpure.mkEqVarInt a_var 0 pos in (*c=t=bound & a=0*)
            let ct_f = Cpure.mkAnd c_f t_f pos in
            let cta_f = Cpure.mkAnd ct_f a_f pos in
            nheap_args,perm,perm_vars,cta_f
          else heap_args,None,[],(Cpure.mkTrue pos)
        in
        let res_var =  CP.SpecVar (Named c, res_name, Unprimed) in
        let new_heap_args,level_f = if (!Globals.allow_locklevel && c=lock_name) then
            (*If this is a lock, astsimpl ensures that it has a single argument*)
            (*Bring locklevel out to form a new expression*)
            (* res = new lock(args) *)
            let arg_var = List.hd heap_args in (*|args| = 1*)
            let arg_var_exp = CP.Var (arg_var,pos) in
            let level = CP.mkLevel res_var pos in
            let eqn = CP.mkEqExp level arg_var_exp pos in (*  arg_var=level(res) *)
            let gt_f = CP.mkGtExp arg_var_exp (CP.IConst (0,pos)) pos in (* arg_var >0 *)
            let ls_pvar = CP.mkLsVar Primed in
            let ls_pvar_exp = CP.Var (ls_pvar,pos) in
            let notin_ls_f = CP.BForm (((CP.mkBagNotIn res_var ls_pvar_exp pos),
                                        None),None) in
            (* res notin ls' *)
            let lsmu_exp = CP.Var (CP.mkLsmuVar Primed,pos) in (*LSMU'*)
            let notin_lsmu_f = CP.mkBagNotInExp arg_var lsmu_exp pos in (*arg_var notin LSMU'*)
            let f1 = CP.And (eqn,gt_f,pos) in
            let f2 = CP.And (f1,notin_ls_f,pos) in
            let f = CP.And (f2,notin_lsmu_f,pos) in
            let nf = MCP.mix_of_pure f in
            ([],nf)
          else (heap_args,MCP.mkMTrue pos)
        in
        let heap_node = CF.DataNode ({
            CF.h_formula_data_node = CP.SpecVar (Named c, res_name, Unprimed);
            CF.h_formula_data_name = c;
            CF.h_formula_data_derv = false;
            CF.h_formula_data_split = SPLIT0;
            CF.h_formula_data_imm = CP.ConstAnn(Mutable);
            CF.h_formula_data_param_imm = List.map (fun _ -> CP.ConstAnn(Mutable)) heap_args;
            (* (andreeac) to check: too weak *)
            CF.h_formula_data_perm = perm;
            CF.h_formula_data_origins = [];
            CF.h_formula_data_original = true;
            CF.h_formula_data_arguments =(*type_var :: ext_var :: *) new_heap_args;
            CF.h_formula_data_holes = []; (* An Hoa : Don't know what to do *)
            CF.h_formula_data_remaining_branches = None;
            CF.h_formula_data_pruning_conditions = [];
            CF.h_formula_data_label = None;
            CF.h_formula_data_pos = pos}) in
        (*If this is not a lock, level_f = true*)
        let aux_f = MCP.memoise_add_pure_N level_f perm_f in
        let heap_form = if (perm_vars!=[]) then
            CF.mkExists perm_vars heap_node aux_f CVP.empty_vperm_sets
              CF.TypeTrue (CF.mkTrueFlow ()) [] pos
          else
            CF.mkBase heap_node aux_f CVP.empty_vperm_sets CF.TypeTrue (CF.mkTrueFlow ()) [] pos
        in
        let heap_form = x_add Cvutil.prune_preds prog false heap_form in
        let res = CF.normalize_max_renaming_list_failesc_context heap_form pos true ctx in
        res
      end;
    | Null pos ->
      let p = CP.mkEqExp (CP.mkVar (CP.SpecVar (Globals.null_type, res_name,
                                                Unprimed)) pos) (CP.Null pos)
          pos in
      let f = CF.formula_of_mix_formula (MCP.mix_of_pure p) pos in
      let res = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
      res
    | EmptyArray _ -> ctx (* An Hoa : no change in context for empty array *)
    | SCall ({
        exp_scall_type = ret_t;
        exp_scall_method_name = mn; (* mn is mingled name of the method *)
        exp_scall_lock = lock;
        exp_scall_arguments = vs;
        exp_scall_ho_arg = ha;
        exp_scall_is_rec = is_rec_flag;
        exp_scall_path_id = pid;
        exp_scall_pos = pos}) ->
      begin
        Gen.Profiling.push_time "[check_exp] SCall";
        let () = if Cast.unmingle_name mn = "fcode" then
            Synt.tmpl_proc_name := Some proc.Cast.proc_name;
            Synt.repair_pos := Some pos; in
        let () = x_tinfo_hp (add_str "scall name" pr_id) mn no_pos in
        let () = proving_loc#set pos in
        let mn_str = Cast.unmingle_name mn in
        let proc0 = proc in
        (*clear history*)
        let farg_types, _ (* farg_names *) = List.split proc.proc_args in
        let () = x_tinfo_hp (add_str "mn: " pr_id) mn no_pos in
        let () = x_tinfo_hp (add_str "ctx scall start: "
                               Cprinter.string_of_list_failesc_context) ctx no_pos
        in
        let ctx = CF.clear_entailment_history_failesc_list (fun x -> None) ctx
        in
        (*=========================*)
        (*======= CONCURRENCY======*)
        (*=========================*)
        if (mn_str=Globals.fork_name) then
          (*FORK*)
          check_scall_fork prog ctx e0 post_start_label ret_t mn lock vs is_rec_flag pid pos
        else if (mn_str=Globals.join_name) then
          (*JOIN*)
          check_scall_join prog ctx e0 post_start_label ret_t mn lock vs is_rec_flag pid pos
        else if (mn_str=Globals.acquire_name || mn_str=Globals.release_name
                 || mn_str=Globals.finalize_name || mn_str=Globals.init_name)
        then
          (*Lock operations: init/finalize/acquire/release*)
          check_scall_lock_op prog ctx e0 post_start_label ret_t mn lock vs is_rec_flag pid pos
          (*=========================*)
          (*===<<<<= CONCURRENCY=====*)
        else
          (*=========================*)
          (*=== NORMAL METHOD CALL ==*)
          let proc = look_up_proc_def pos prog.new_proc_decls mn in
          let () = Debug.ninfo_zprint (lazy (("   " ^ proc.Cast.proc_name))) no_pos in
          let () = Debug.tinfo_zprint
              (lazy (("stk spec: " ^(Cprinter.string_of_struc_formula
                                       (proc.Cast.proc_stk_of_static_specs #top)
                                    )))) no_pos in
          let farg_types, farg_names = List.split proc.proc_args in
          let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)
                                         ) farg_names farg_types in
          let actual_spec_vars =
            List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) vs farg_types in
          let () = x_tinfo_hp (add_str "actual_svs:"
                                 Cprinter.string_of_spec_var_list)
              actual_spec_vars no_pos in
          let b = true
          in
          if not b then ctx
          else
            let check_pre_post_orig org_spec (sctx:CF.list_failesc_context)
                should_output_html : CF.list_failesc_context =
              (* Termination: Stripping the "variance" feature from
               * org_spec if the call is not a recursive call *)
              let () = x_dinfo_hp (add_str "actual_svs:"
                                     Cprinter.string_of_list_failesc_context)
                  sctx no_pos in
              let () = x_tinfo_hp (add_str "org_spec:"
                                     Cprinter.string_of_struc_formula)
                  (org_spec) no_pos in
              let org_spec = if !Globals.change_flow
                then CF.change_spec_flow org_spec else org_spec in
              let lbl_ctx = store_label # get in
              let org_spec2 =
                if is_rec_flag && !auto_number then match org_spec with
                  | CF.EList b ->
                    let l = CF.Label_Spec.filter_label_rec lbl_ctx b in
                    CF.EList l
                  | _ -> org_spec
                else org_spec in
              let stripped_spec = org_spec2 in
              (* org_spec -> stripped_spec *)
              (* free vars = linking vars that appear both in pre and are not formal arguments *)
              (* Termination: The logical vars should not be renamed *)
              let pre_free_vars = Gen.BList.difference_eq CP.eq_spec_var
                  (Gen.BList.difference_eq CP.eq_spec_var (CF.struc_fv stripped_spec)
                     (CF.struc_post_fv stripped_spec))
                  (farg_spec_vars@prog.Cast.prog_logical_vars) in
              (* free vars get to be substituted by fresh vars *)
              (* removing ranking var and unknown predicate from renaming *)
              let pre_free_vars =
                List.filter (fun v -> let t = CP.type_of_spec_var v
                              in not(is_RelT t) && t != HpT) pre_free_vars in
              (*LOCKSET: ls is not free var*)
              let ls_var = [(CP.mkLsVar Unprimed)] in
              let lsmu_var = [(CP.mkLsmuVar Unprimed)] in
              let waitlevel_var = [(CP.mkWaitlevelVar Unprimed)] in
              let pre_free_vars = List.filter (fun v -> CP.name_of_spec_var v
                                                        <> Globals.ls_name
                                                        && CP.name_of_spec_var v
                                                           <> Globals.lsmu_name
                                                        && CP.name_of_spec_var v
                                                           <>
                                                           Globals.waitlevel_name)
                  pre_free_vars in
              let pre_free_vars_fresh = CP.fresh_spec_vars pre_free_vars in
              let () = x_tinfo_hp (add_str "stripped_spec"
                                     Cprinter.string_of_struc_formula)
                  (stripped_spec) no_pos in
              let renamed_spec =
                if !Globals.max_renaming then (CF.rename_struc_bound_vars stripped_spec)
                else (CF.rename_struc_clash_bound_vars stripped_spec
                        (CF.formula_of_list_failesc_context sctx)) in
              let () = x_tinfo_hp (add_str "renamed_spec"
                                     Cprinter.string_of_struc_formula)
                  renamed_spec no_pos in
              let st1 = List.combine pre_free_vars pre_free_vars_fresh in
              let fr_vars = farg_spec_vars @ (List.map CP.to_primed farg_spec_vars) in
              let to_vars = actual_spec_vars @ (List.map CP.to_primed actual_spec_vars) in
              let renamed_spec = CF.subst_struc st1 renamed_spec in
              let renamed_spec = CF.subst_struc_avoid_capture fr_vars to_vars renamed_spec in
              let renamed_spec =
                match proc.proc_ho_arg, ha with
                | Some hv, Some ha ->
                  let ht, hn = hv in
                  let hsv = CP.SpecVar (ht, hn, Unprimed) in
                  CF.subst_hvar_struc renamed_spec [(hsv, ha)]
                | _ -> renamed_spec
              in

              let st2 = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) actual_spec_vars in
              (*ALSO rename ls to ls',lsmu to lsmu'*)
              let st_ls = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) ls_var in
              let st_lsmu = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) lsmu_var in
              let st_waitlevel =
                waitlevel_var |> List.map (fun v -> (CP.to_unprimed v,
                                                     CP.to_primed v)) in
              let st3= st2@st_ls@st_lsmu@st_waitlevel in
              let () = x_tinfo_hp (add_str "renamed_spec"
                                     Cprinter.string_of_struc_formula)
                  renamed_spec no_pos in
              let pre2 = CF.subst_struc_pre st3 renamed_spec in
              let () = x_tinfo_hp (add_str "pre2" Cprinter.string_of_struc_formula) pre2 no_pos in
              let new_spec = (Cprinter.string_of_struc_formula pre2) in
              (* Termination: Store unreachable state *)
              let _ =
                if is_rec_flag then (* Only check termination of a recursive call *)
                  let () = x_dinfo_zp
                      (lazy (">>>>>>> Termination Checking: " ^ mn ^ " <<<<<<<")) pos in
                  if not (CF.isNonFalseListFailescCtx sctx) then
                    let todo_unk = Term.add_unreachable_res sctx pos in ()
                  else ()
                else ()
              in

              (* TODO: call the entailment checking function in solver.ml *)
              let to_print = "\nProving precondition in method "
                             ^ proc.proc_name ^ " for spec:\n" ^ new_spec  in
              let to_print = ("\nVerification Context:"^(post_pos#string_of_pos)
                              ^to_print) in
              x_dinfo_zp (lazy (to_print^"\n")) pos;
              (* An Hoa : output the context and new spec before checking pre-condition *)
              let () = if !print_proof && should_output_html
                then Prooftracer.push_list_failesc_context_struct_entailment
                    sctx pre2 in
              (*we use new rules to judge the spec*)
              let () = x_dinfo_hp (add_str "old rs:"
                                     Cprinter.string_of_list_failesc_context)
                  sctx no_pos in
              let rs, prf = x_add SV.heap_entail_struc_list_failesc_context_init 6
                  prog false true sctx pre2 None None None pos pid in
              let () = if !print_proof && should_output_html then Prooftracer.pop_div () in
              let () = PTracer.log_proof prf in
              let () = x_tinfo_hp (add_str "new rs:"
                                     Cprinter.string_of_list_failesc_context)
                  rs no_pos in
              rs
            in
            (*****************END_CHECK_PRE_POST********************************)
            (* Call check_pre_post with debug information *)
            (*******************************************************************)
            let check_pre_post ir org_spec (sctx:CF.list_failesc_context)
                should_output_html : CF.list_failesc_context =
              let pr2 = Cprinter.string_of_list_failesc_context in
              let pr3 = Cprinter.string_of_struc_formula in
              let () = Debug.dinfo_hprint (add_str  "org_spec"
                                             Cprinter.string_of_struc_formula)
                  org_spec no_pos in
              let wrap_fnc = if CF.is_infer_pre_must org_spec then wrap_err_must
                else wrap_err_pre in
              let pre_post_op_wrapper a b c = wrap_fnc (check_pre_post_orig a b) c in
              let pk = if ir then PK_PRE_REC else PK_PRE in
              let f = wrap_proving_kind pk (pre_post_op_wrapper org_spec sctx) in
              let is_post_false = CF.is_struc_false_post org_spec in
              let f x =
                if is_post_false then
                  if !Globals.new_trace_classic then
                    wrap_msg "check pre/post classic" (wrap_classic x_loc (Some true) f) x
                  else (wrap_classic x_loc (Some true) f) x
                else f x in
              Debug.no_2 "check_pre_post(2)" pr3 pr2 pr2 (fun _ _ ->
                  f should_output_html) org_spec sctx in
            let check_pre_post ir org_spec (sctx:CF.list_failesc_context)
                should_output_html : CF.list_failesc_context =
              Gen.Profiling.do_1 "check_pre_post"
                (check_pre_post ir org_spec sctx) should_output_html
            in
            let () = if !print_proof then Prooftracer.start_compound_object () in
            let scall_pre_cond_pushed = if !print_proof then
                begin
                  Tpdispatcher.push_suppress_imply_output_state ();
                  Tpdispatcher.unsuppress_imply_output ();
                  Prooftracer.push_pre e0;
                  (* print_endline ("CHECKING PRE-CONDITION OF FUNCTION CALL " ^
                     (Cprinter.string_of_exp e0)) *)
                end else false in

            let res = if (CF.isFailListFailescCtx_new ctx) then
                let _ = if !print_proof && scall_pre_cond_pushed
                  then Prooftracer.append_html "Program state is unreachable."
                in
                ctx
              else
                let pre_with_new_pos = CF.subst_pos_struc_formula pos
                    (proc.proc_stk_of_static_specs#top) in
                let () = x_tinfo_hp (add_str "specs#top: "
                                       Cprinter.string_of_struc_formula)
                    (proc.proc_stk_of_static_specs#top) no_pos in
                check_pre_post is_rec_flag pre_with_new_pos ctx scall_pre_cond_pushed
            in
            let () = x_tinfo_hp (add_str "res " Cprinter.string_of_list_failesc_context)
                res no_pos in
            let () = if !print_proof then Prooftracer.add_pre e0 in
            let () = if !print_proof && scall_pre_cond_pushed then
                begin
                  Prooftracer.pop_div ();
                  Tpdispatcher.restore_suppress_imply_output_state ();
                  (* print_endline "OK.\n" *)
                end in
            Gen.Profiling.pop_time "[check_exp] SCall";
            (*Loc: error as exception *)
            (* move must, may flow into esc_stack *)
            if (Globals.global_efa_exc () || (CF.isSuccessListFailescCtx_new res)) then
              let res =
                let () = update_callee_hpdefs_proc prog.Cast.new_proc_decls proc0.proc_name mn in
                let idf = (fun c -> c) in
                let err_kind_msg = if CF.is_infer_pre_must
                    (proc.proc_stk_of_static_specs#top) then "must" else "may"
                in
                let to_print = "Proving precondition in method "
                               ^ proc.proc_name ^ "(" ^ (string_of_loc pos) ^
                               ") Failed (" ^  err_kind_msg ^ ")" in
                CF.transform_list_failesc_context (
                  idf,idf,
                  (fun es -> CF.Ctx{es with
                                    CF.es_formula
                                    = Norm.imm_norm_formula prog
                                        es.CF.es_formula
                                        Solver.unfold_for_abs_merge pos;
                                    CF.es_final_error
                                    = CF.acc_error_msg es.CF.es_final_error to_print})) res
              in
              let () = x_tinfo_hp (add_str "res: " Cprinter.string_of_list_failesc_context)
                res no_pos in

              (*Exhausively apply normalization lemma after each SCall.
                Need to devise a smart way since
                this will incur overhead if we have many
                normalization lemmas in the programs*)
              (* Already did in EAssume *)
              res
            else begin
              (* get source code position of failed branches *)
              (
                if (!Globals.web_compile_flag) then
                  let to_print = "\nProving precondition in method "
                                 ^ proc.proc_name ^ " Failedss.\n" in
                  let s,_,_= CF.get_failure_list_failesc_context res in
                  let () = print_string_quiet (to_print ^s^"\n") in
                  res
                else
                  (*FAILURE explaining*)
                  let to_print = "\nProving precondition in method "
                                 ^ proc.proc_name ^ " Failed88.\n" in
                  let () = repair_loc := Some VarGen.proving_loc#get in
                  let _ =
                    if not !Globals.disable_failure_explaining then
                      let s,fk,_= CF.get_failure_list_failesc_context res
                      (*should check bot with is_bot_status*)
                      in
                      let () = Debug.ninfo_hprint
                          (add_str "res" Cprinter.string_of_list_failesc_context
                          ) res no_pos in
                      let () = Debug.ninfo_hprint (add_str "s" pr_id) s no_pos in
                      if (String.length s) >  0 then
                        let pr = pr_list_ln Cprinter.string_of_hprel_short in
                        if not(Infer.rel_ass_stk# is_empty) then
                          begin
                            if (* !VarGen.sap *) true then begin
                              print_endline_quiet "";
                              print_endline_quiet "*************************************";
                              print_endline_quiet "*******relational assumptions 2 ********";
                              print_endline_quiet "*************************************";
                            end;
                            let ras = Infer.rel_ass_stk # get_stk in
                            let () = Infer.scc_rel_ass_stk # push_list ras in
                            let () = Infer.rel_ass_stk # reset in
                            let () = Infer.scc_rel_ass_stk # reset in
                            if (* !VarGen.sap *) true then begin
                              let ras = List.rev(ras) in
                              let ras1 = if !Globals.print_en_tidy
                                then List.map Cfout.rearrange_rel ras else ras
                              in
                              if !Globals.testing_flag
                              then print_endline_quiet
                                  ("<rstart>"^(string_of_int (List.length ras)))
                              ;
                              let pr = pr_list_ln (fun x ->
                                  Cprinter.string_of_hprel_short_inst prog [] x)
                              in
                              let pr_len x = string_of_int (List.length x) in
                              print_endline_quiet (pr (ras1));
                              print_endline_quiet "*************************************";
                              if !Globals.testing_flag
                              then print_endline_quiet
                                  "<rstop>*************************************"
                            end
                          end;
                        raise (Err.Ppf ({
                            Err.error_loc = pos;
                            Err.error_text = (to_print ^s (* ^ "\n" ^ (pr hprel_assumptions) *))
                          }, (match fk with
                            | CF.Failure_Bot _ -> 0
                            | CF.Failure_Must _ -> 1
                            | CF.Failure_Valid -> 2
                            | CF.Failure_May _ -> 3), 1))
                      else ()
                    else
                      begin
                        Debug.print_info
                          ("("^(Cprinter.string_of_label_list_failesc_context
                                  res)^") ")
                          ("Proving precondition in method failed\n") pos;
                        Debug.print_info ("(Cause of PreCond Failure)")
                          (Cprinter.string_of_failure_list_failesc_context res) pos;
                        Err.report_error {
                          Err.error_loc = pos;
                          Err.error_text = Printf.sprintf
                              "Proving precondition in method failed."
                        }
                      end
                  in
                  res)
            end
      end
    | Seq ({exp_seq_type = te2;
            exp_seq_exp1 = e1;
            exp_seq_exp2 = e2;
            exp_seq_pos = pos}) -> begin
        let ctx1 = x_add check_exp prog proc ctx e1 post_start_label (*flow_store*) in
        (* Astsimp ensures that e1 is of type void *)
        let ctx2= x_add check_exp prog proc ctx1 e2 post_start_label (*flow_store*) in
        Debug.ninfo_hprint (add_str "WN ctx1:" Cprinter.string_of_list_failesc_context) ctx1 pos;
        Debug.ninfo_hprint (add_str "WN ctx2:" Cprinter.string_of_list_failesc_context) ctx2 pos;
        ctx2
      end
    | Time (b,s,_) -> if b then Gen.Profiling.push_time s else Gen.Profiling.pop_time s; ctx
    | This ({exp_this_type = t;
             exp_this_pos = pos}) ->
      begin
        let tmp = CF.formula_of_mix_formula
            (MCP.mix_of_pure (CP.mkEqVar (CP.mkRes t)
                                (CP.SpecVar (t, "this", Unprimed)) pos)) pos in
        CF.normalize_max_renaming_list_failesc_context tmp pos true ctx
      end
    | Var ({
        exp_var_type = t;
        exp_var_name = v;
        exp_var_pos = pos}) ->
      begin
        Gen.Profiling.push_time "[check_exp] Var";
        (*********************************************)
        (* VPerm: Check @full/@lend permission for v *)
        (*********************************************)
        let b =
          let () = check_var_read_perm ~msg:"(var access)" prog ctx pos v t in
          true in
        let res =
          (* if (not b) then res (*do not have permission for variable v*) *)
          (* else                                                          *)
          if not b then ctx (* Unreachable branch *)
          else
            let tmp = CF.formula_of_mix_formula
                (MCP.mix_of_pure (CP.mkEqVar (CP.mkRes t)
                                    (CP.SpecVar (t, v, Primed)) pos)) pos in
            CF.normalize_max_renaming_list_failesc_context tmp pos true ctx in
        Gen.Profiling.pop_time "[check_exp] Var";
        res
      end

    | VarDecl {
        exp_var_decl_type = t;
        exp_var_decl_name = v; } ->
      (*************************************)
      (* VPerm: Set @full permission for v *)
      (*************************************)
      if !ann_vp then
        let sv = CP.SpecVar (t, v, Unprimed) in
        let vp = CVP.vperm_sets_of_anns [(VP_Full, [sv])] in
        VP.add_vperm_sets_list_failesc_ctx vp ctx
      else ctx
    | Unit pos -> ctx
    | Sharp {exp_sharp_type =t;
              exp_sharp_flow_type = ft;(*P.flow_typ*)
              exp_sharp_val = v; (*maybe none*)
              exp_sharp_unpack = un;
              (*true if it must get the new flow from the second element of the current flow pair*)
              exp_sharp_path_id = pid;
              exp_sharp_pos = pos}	->
      (**********INTERNAL************)
      let () = x_tinfo_hp (add_str "sharp start: " pr_failesc_ctx) ctx no_pos in
      let look_up_typ_first_fld obj_name =
        let dclr = x_add Cast.look_up_data_def_raw prog.Cast.prog_data_decls obj_name in
        let (t,_),_ = (List.hd dclr.Cast.data_fields) in
        t in
      let nctx = match v with
        | Sharp_var (t,v) ->
          let t1 = (get_sharp_flow ft) in
          let () = x_tinfo_pp ("Sharp Flow:"^(string_of_flow t1) ^" Exc:"
                               ^(string_of_flow !raisable_flow_int)) no_pos in
          let ctx, vr,vf =
            let sharp_val = CP.SpecVar (t, v, Primed) in
            let eres_var = CP.mkeRes t in
            let res_var = CP.mkRes t in
            if is_subset_flow t1 !raisable_flow_int || is_subset_flow t1 !loop_ret_flow_int then
              let () = x_tinfo_pp ("inside sharp flow capture") no_pos in
              match t with
              | Named objn -> (
                  let ft = (look_up_typ_first_fld objn) in
                  let res_inside_exc = (CP.mkRes ft) in
                  try
                    let dnode =Cfutil.look_up_first_field prog ctx objn in
                    let v_exc = (List.find (fun sv ->
                        (Cpure.type_of_spec_var sv)== ft)
                        dnode.Cformula.h_formula_data_arguments) in
                    let fr_v_exc = CP.fresh_spec_var v_exc in
                    let p = CP.mkEqVar v_exc res_inside_exc pos in
                    let ctx_w_pure = CF.combine_pure_list_failesc_context
                        (MCP.mix_of_pure p) pos true ctx in
                    let () = x_tinfo_hp (add_str "ctx_w_pure" pr_failesc_ctx)
                        ctx_w_pure no_pos in
                    let () = x_tinfo_hp (add_str "res_inside_exc" pr_sv)
                        res_inside_exc no_pos in
                    let () = x_tinfo_hp (add_str "fr_v_exc" pr_sv) fr_v_exc
                        no_pos in
                    let () = x_tinfo_hp (add_str "sharp_val" pr_sv) sharp_val no_pos in
                    (ctx_w_pure,eres_var,sharp_val)
                  with _ -> (ctx,eres_var,sharp_val))
              | _ -> ctx,eres_var, sharp_val
            else ctx, res_var, sharp_val in
          let tmp = CF.formula_of_mix_formula  (MCP.mix_of_pure (CP.mkEqVar vr vf pos)) pos in
          let ctx1 = CF.normalize_max_renaming_list_failesc_context tmp pos true ctx in
          ctx1
        | Sharp_flow v ->
          let fct es =
            let rest, b_rez = CF.get_var_type v es.CF.es_formula in
            if b_rez then
              let vsv_f = CF.formula_of_mix_formula
                  (MCP.mix_of_pure (CP.mkEqVar (CP.SpecVar (rest, v, Primed))
                                      (P.mkRes rest) pos)) pos in
              if !Globals.max_renaming then CF.normalize_es vsv_f pos true es
              else CF.normalize_clash_es vsv_f pos true es
            else CF.Ctx es
          in
          CF.transform_list_failesc_context (idf,idf,fct) ctx
        | Sharp_no_val -> ctx in

      let r = match ft with
        | Sharp_ct nf ->
          if not un then
            CF.transform_list_failesc_context
              (idf,idf,
               (fun es -> CF.Ctx
                   {es with CF.es_formula =
                              CF.set_flow_in_formula nf es.CF.es_formula})) nctx
          else CF.transform_list_failesc_context
              (idf,idf,
               (fun es ->
                  CF.Ctx
                    {es
                     with CF.es_formula =
                            CF.set_flow_to_link_f !flow_store es.CF.es_formula no_pos})) nctx
        | Sharp_id v ->
          CF.transform_list_failesc_context
            (idf,idf,
             (fun es -> CF.Ctx
                 {es with
                  CF.es_formula =
                    CF.set_flow_in_formula (CF.get_flow_from_stack v !flow_store
                                              pos)
                      es.CF.es_formula})) nctx in
      let res = CF.add_path_id_ctx_failesc_list r (pid,0) (-1) in
      let () = x_tinfo_hp (add_str "ctx sharp after: " pr_failesc_ctx) res no_pos in
      res
    | Try ({exp_try_body = body;
            exp_catch_clause = cc;
            exp_try_path_id = pid;
            exp_try_pos = pos })->
      let cc = get_catch_of_exp cc in
      let ctx = CF.push_esc_level_list ctx idf pid in
      let ctx1 = x_add check_exp prog proc ctx body post_start_label in
      (* WN : ctx2,ctx3 appears to be redundant *)
      let ctx2 = CF.pop_esc_level_list ctx1 pid in
      let ctx3 = CF.push_esc_level_list ctx2 idf pid in
      (*Decide which to escape, and which to be caught.
        Caught exceptions become normal flows*)
      let ctx4 = x_add CF.splitter_failesc_context (cc.exp_catch_flow_type) (cc.exp_catch_var)
          (fun c -> CF.add_path_id c (Some pid,0) (-1)) SV.elim_exists_ctx ctx3 in
      let ctx5 = x_add check_exp prog proc ctx4 cc.exp_catch_body post_start_label in
      CF.pop_esc_level_list ctx5 pid

    | UnkExp {
        unk_exp_name = id;
        unk_exp_arguments = args;
        unk_exp_pos = pos;
      } ->
      let () = x_tinfo_hp (add_str "old ctx:" Cprinter.string_of_list_failesc_context) ctx no_pos in
      let exp_defs = prog.prog_exp_decls in
      begin
        try
          let exp_def = List.find (fun exp_decl -> String.compare exp_decl.Cast.exp_name id == 0)
              exp_defs in
          let res_exp = CP.mk_exp_var (CP.mkRes exp_def.exp_ret_typ) in
          let arg_exps = List.map (fun x -> CP.to_primed (CP.mk_spec_var x)) args in
          let unk_coes = List.map
              (fun var -> CP.SpecVar (CP.int_type,
                                      id ^ "_" ^ (CP.name_of_spec_var var), Unprimed))
              arg_exps in
          let unk_const = CP.SpecVar (Int, id ^ "_" ^ (string_of_int 0), Unprimed) in
          let templ = CP.Template {
              templ_id = CP.mk_spec_var exp_def.exp_name;
              templ_args = List.map CP.mk_exp_var arg_exps;
              templ_unks = List.map (fun x -> CP.mkVar x pos) (unk_const::unk_coes);
              templ_body = None;
              templ_pos = pos;
            }
          in
          let pure_f = CP.mkEqExp res_exp templ pos in
          let tmp = CF.formula_of_mix_formula (MCP.mix_of_pure pure_f) pos in
          let n_ctx =
            CF.normalize_max_renaming_list_failesc_context tmp pos true ctx in
          let () = x_binfo_hp (add_str "n_ctx:"
                                 Cprinter.string_of_list_failesc_context) n_ctx
              no_pos in
          n_ctx
        with Not_found ->
          Err.report_error { Err.error_loc = pos;
                             Err.error_text = "No expression declaration found." }
      end
    | Par { exp_par_vperm = vp; exp_par_lend_heap = lh; exp_par_cases = cl; exp_par_pos = pos; } ->
      if not !ann_vp then
        (DD.info_pprint
           ("WARNING: Skip reasoning PAR construct because --ann-vp is not
        enabled.") pos;
         ctx)
      else
        let f_ent ctx f = SV.heap_entail_list_failesc_context_init prog false ctx f
            None None None pos None in
        let par_pre_ctx, rem_ctx = VP.prepare_list_failesc_ctx_for_par f_ent vp lh ctx pos in
        let no_vp_par_pre_ctx =
          let pre_ctx = TermUtils.strip_lexvar_list_failesc_ctx par_pre_ctx in
          VP.set_vperm_sets_list_failesc_ctx CVP.empty_vperm_sets pre_ctx
        in
        let par_label = (1, "par") in
        let par_rem_ctx, case_post_ctx_list =
          List.fold_left (fun (par_rem_ctx, case_post_ctx_acc) c ->
              let par_rem_ctx, case_post_ctx =
                check_par_case_wrapper prog proc no_vp_par_pre_ctx par_rem_ctx c
                  par_label in
              (par_rem_ctx, case_post_ctx_acc @ [case_post_ctx])) (par_pre_ctx, []) cl in
        let res_ctx = List.fold_left (fun compose_ctx post_ctx ->
            VP.compose_list_failesc_contexts_for_par false post_ctx compose_ctx pos)
            rem_ctx (par_rem_ctx::case_post_ctx_list)
        in
        let lem = Lem_store.all_lemma # get_left_coercion in
        (* Norm CNT *)
        let norm_prop_es es =
          { es with
            CF.es_formula = x_add Solver.prop_formula_w_coers 20 prog es es.CF.es_formula lem}
        in
        let res_ctx = VP.norm_list_failesc_context_for_par norm_prop_es res_ctx in
        (* Norm ERR *)
        let norm_lem_es es = Solver.normalize_estate_w_coers prog es lem pos in
        VP.norm_list_failesc_context_for_par norm_lem_es res_ctx

    | _ ->
      failwith ((Cprinter.string_of_exp e0) ^ " is not supported yet")  in

  let check_exp1_a (ctx : CF.list_failesc_context) : CF.list_failesc_context =
    let pr = Cprinter.string_of_list_failesc_context in
    Debug.no_1 "check_exp1" pr pr check_exp1 ctx in

  let check_exp1_x (ctx : CF.list_failesc_context) : CF.list_failesc_context =
    Gen.Profiling.do_1 "check_exp1" (x_add_1 check_exp1_a) ctx in

  let ctx = if (not !Globals.failure_analysis)
    then List.filter (fun (f,s,c)-> Gen.is_empty f ) ctx
    else ctx in
  (* An Hoa : Simplify the context before checking *)
  let ctx = if (!simplify_context) then
      CF.simplify_list_failesc_context ctx proc.Cast.proc_important_vars
    else ctx in
  (* fl denote all failed states *)
  let (fl,cl) = List.partition (fun (_,s,c) -> Gen.is_empty c && CF.is_empty_esc_stack s) ctx in
  let failesc = x_add CF.splitter_failesc_context !norm_flow_int None (fun x->x)(fun x -> x) cl in
  x_dinfo_hp (add_str "check_exp1:failed?(fl):"Cprinter.string_of_list_failesc_context) fl no_pos;
  x_dinfo_hp (add_str "check_exp1:inp(cl):"Cprinter.string_of_list_failesc_context) cl no_pos;
  x_dinfo_hp (add_str "check_exp1:out(failesc):"
                Cprinter.string_of_list_failesc_context_short) failesc no_pos;
  ((check_exp1_x failesc) @ fl)

(* PAR: Check pre-state and compute post-state of a par_case *)
and norm_par_case_pre (vp: CVP.vperm_sets) (f: CF.formula) =
  VP.add_vperm_sets_formula vp f

and check_par_case_wrapper (prog: prog_decl) (proc: proc_decl) par_init_ctx
    (ctx: CF.list_failesc_context) (par_case: exp_par_case) par_label:
  CF.list_failesc_context * CF.list_failesc_context =
  wrap_par_case_check (fun c -> check_par_case prog proc par_init_ctx ctx c
                          par_label) par_case

and check_par_case_x (prog: prog_decl) (proc: proc_decl) par_init_ctx
    (ctx:CF.list_failesc_context) (par_case: exp_par_case)
    par_label:CF.list_failesc_context * CF.list_failesc_context =
  let pos = par_case.exp_par_case_pos in
  let rem_ctx, pre_ctx =
    if par_case.exp_par_case_else then
      CF.mkEmp_list_failesc_context pos, ctx
    else
      (* Construct pre-condition of the current par's case *)
      let vp = par_case.exp_par_case_vperm in
      let pre =
        match par_case.exp_par_case_cond with
        | None ->
          let b = CF.mkTrue_b (CF.mkTrueFlow ()) pos in
          CF.Base { b with CF.formula_base_vperm = vp; }
        | Some f -> norm_par_case_pre vp f in
      (* Remaining context for the other cases *)
      let rem_ctx =
        let ctx = VP.set_inf_par_list_failesc_ctx ctx in
        let res, _ = SV.heap_entail_list_failesc_context_init prog false ctx pre
            None None None pos None in
        if (CF.isSuccessListFailescCtx_new res) then
          VP.clear_inf_par_list_failesc_ctx res
        else
          let msg = "Proving condition of a par's case failed." in
          (Debug.print_info
             ("(" ^ (Cprinter.string_of_label_list_failesc_context res) ^ ") ")
             msg pos;
           Debug.print_info ("(Cause of ParCase Failure)")
             (Cprinter.string_of_failure_list_failesc_context res) pos;
           Err.report_error { Err.error_loc = pos; Err.error_text = msg }) in
      let init_ctx = CF.empty_ctx (CF.mkTrueFlow ()) LO2.unlabelled pos in
      let pre_ctx = CF.build_context init_ctx pre pos in
      let pre_ctx = CF.add_path_id pre_ctx (None, 0) 0 in
      let pre_ctx =
        if !Globals.disable_pre_sat then pre_ctx
        else CF.transform_context (SV.elim_unsat_es 10 prog (ref 1)) pre_ctx in
      let () = flow_store := [] in
      let pre_ctx = CF.set_flow_in_context_override
          { CF.formula_flow_interval = !norm_flow_int; CF.formula_flow_link = None } pre_ctx in
      (* Add initial esc_stack *)
      let init_esc = [((0, ""), [])] in
      rem_ctx, ([CF.mk_failesc_context pre_ctx [] init_esc]) in
  let pre_ctx = VP.compose_list_failesc_contexts_for_par true pre_ctx rem_ctx pos in
  let pre_ctx = VP.compose_list_failesc_contexts_for_par true pre_ctx par_init_ctx pos in

  let pr = !CF.print_list_failesc_context in
  let () = Debug.ninfo_hprint (add_str "check_par_case: rem_ctx:" pr) rem_ctx pos in
  let () = Debug.ninfo_hprint (add_str "check_par_case: par_init_ctx:" pr) par_init_ctx pos in
  let () = x_binfo_hp (add_str "check_par_case: pre_ctx:" pr) pre_ctx pos in
  let post_ctx = x_add check_exp prog proc pre_ctx par_case.exp_par_case_body par_label in
  let post_ctx = TermUtils.strip_lexvar_list_failesc_ctx post_ctx in
  (* Norm post_ctx *)
  let norm_prop_es es =
    {es with
     CF.es_formula = x_add Solver.prop_formula_w_coers 21 prog es
         es.CF.es_formula (Lem_store.all_lemma # get_left_coercion)
    } in
  let post_ctx = VP.norm_list_failesc_context_for_par norm_prop_es post_ctx in
  (rem_ctx, post_ctx)

and check_par_case (prog: prog_decl) (proc: proc_decl) par_init_ctx (ctx: CF.list_failesc_context)
    (par_case: exp_par_case) par_label: CF.list_failesc_context * CF.list_failesc_context =
  let pr1 = Cprinter.string_of_list_failesc_context in
  let pr2 = pr_pair (fun c -> "\nREM: " ^ (pr1 c))
      (fun c -> "\nPOST: " ^ (pr1 c)) in
  let pr3 = string_of_full_loc in
  Debug.no_2 "check_par_case" pr1 pr3 pr2
    (fun _ _ -> check_par_case_x prog proc par_init_ctx ctx par_case par_label)
    ctx (par_case.exp_par_case_pos)

and check_post (prog : prog_decl) (proc : proc_decl)
    (ctx : CF.list_partial_context) (posts : CF.formula*CF.struc_formula)
    pos (pid:formula_label) (etype: ensures_type) : CF.list_partial_context =
  let pr = Cprinter.string_of_list_partial_context in
  let pr1 = pr_pair Cprinter.string_of_formula Cprinter.string_of_struc_formula in
  (* WN : why do we have wrap_ad_flow here *)
  let () = Globals.check_post := true in
  let post_op_wrapper f a =
    wrap_err_post f a
  in
  let f = wrap_ver_post (wrap_add_flow (wrap_proving_kind PK_POST (
      post_op_wrapper (check_post_x prog proc ctx posts pos) pid) )) in
  Debug.no_2 "check_post" pr pr1 pr (fun _ _ -> f etype) ctx posts

and check_post_x (prog : prog_decl) (proc : proc_decl)
    (ctx : CF.list_partial_context) (posts : CF.formula*CF.struc_formula)
    pos (pid:formula_label) (etype: ensures_type) : CF.list_partial_context  =
  (wrap_classic x_loc etype (check_post_x_x prog proc ctx posts pos)) pid

and pr_spec = Cprinter.string_of_struc_formula

and pr_spec2 = Cprinter.string_of_struc_formula_for_spec

and check_post_x_x (prog : prog_decl) (proc : proc_decl)
    (ctx0 : CF.list_partial_context) (posts : CF.formula*CF.struc_formula)
    pos (pid:formula_label):  CF.list_partial_context  =
  let _ = x_binfo_pp ">>>>>>>>> begin prove post-cond >>>>>>>" no_pos in
  let _ = SB.enable_export_entailments () in
  let ctx = CF.fresh_view_list_partial_context ctx0 in
  let () = if !print_proof then
      begin
        Prooftracer.push_post ();
        Prooftracer.start_compound_object ();
        Prooftracer.push_list_partial_context_formula_entailment ctx (fst posts);
        Tpdispatcher.push_suppress_imply_output_state ();
        Tpdispatcher.unsuppress_imply_output ();
      end in
  (* Termination: Poststate of Loop must be unreachable (soundness) *)
  let todo_unk =
    if !Globals.dis_term_chk || !Globals.dis_post_chk then true
    else
      let check_falsify ctx = SV.heap_entail_one_context 17 prog false ctx
          (CF.mkFalse_nf pos) None None None pos in
      Term.check_loop_safety prog proc check_falsify ctx (fst posts) pos pid in

  (* Rho: print conc err, if any *)
  let _ =
    let conc_errs = CF.collect_conc_err_list_partial_context ctx in
    if is_empty conc_errs then ()
    else
      let str_conc_err = pr_list
          (fun (msg, pos) -> msg ^ ":" ^ (string_of_loc pos)) conc_errs in
      print_string_quiet ("\n!!! WARNING: " ^ str_conc_err ^ "\n") in
  let fn_state = ctx in
  let pr = Cprinter.string_of_list_partial_context in
  let () = x_tinfo_hp (add_str "ctx" pr) ctx no_pos in
  let all_traces = ctx |> List.map snd |> List.concat
                    |> List.map (fun (x, _, _) -> x) in
  let pr_paths = pr_list Cprinter.string_of_path_trace in
  let () = x_binfo_hp (add_str "paths" pr_paths) all_traces no_pos in
  let f1 = CF.formula_is_eq_flow (fst posts) !error_flow_int in
  let rs, prf =
    if f1 then
      begin
        let flat_post = (CF.formula_subst_flow (fst posts) (CF.mkNormalFlow())) in
        let _ = (CF.struc_formula_subst_flow (snd posts) (CF.mkNormalFlow())) in
        (*possibly change to flat post here as well??*)
        let ans, prf = SV.heap_entail_list_partial_context_init prog false
            fn_state flat_post None None None pos (Some pid) in
        let () = DD.ninfo_hprint
            (add_str "ans" Cprinter.string_of_list_partial_context) ans no_pos in
        let ans1 = if !mem_leak_detect then
            Soutil.detect_mem_leak prog proc ans
          else ans in
        (CF.invert_list_partial_context_outcome CF.invert_ctx_branch_must_fail
           CF.invert_fail_branch_must_fail ans1, prf)
      end
    else
      let rs_struc , prf = x_add SV.heap_entail_struc_list_partial_context_init
            prog false false fn_state (snd posts) None None None pos (Some pid) in
      rs_struc, prf in
  let _ = x_tinfo_pp "<<<<<<<<<< finish prove post-cond <<<<<<" no_pos in
  let _ = SB.disable_export_entailments () in
  let () = PTracer.log_proof prf in
  let () = if !print_proof then
      begin
        Tpdispatcher.restore_suppress_imply_output_state ();
        Prooftracer.add_post ();
        Prooftracer.pop_div ();
        Prooftracer.pop_div ();
        (* print_endline "DONE!" *)
      end in
  let is_succ = CF.isSuccessListPartialCtx_new rs in
  let is_reachable_succ = if not f1 then
      is_succ
    else
      is_succ && (CF.exist_reachable_states rs) in
  let () =  DD.ninfo_hprint (add_str "is_succ" string_of_bool) is_succ no_pos in
  let () =  DD.ninfo_hprint (add_str "is_reachable_succ" string_of_bool) is_reachable_succ no_pos in
  let pr = Cprinter.string_of_list_partial_context in
  let () = x_tinfo_hp (add_str "rs" pr) rs no_pos in
  if (is_reachable_succ) then
    rs
  else begin
    let fail_traces = rs |> List.map fst |> List.concat |> List.map fst in
    let pr_paths = pr_list Cprinter.string_of_path_trace in
    let aux fail_traces trace =
      let eq_trace t1 = t1 = trace in
      List.exists eq_trace fail_traces in
    let () = x_binfo_hp (add_str "paths" pr_paths) fail_traces no_pos in
    let check_post = List.map (aux fail_traces) all_traces in
    let () = Synt.check_post_list := check_post in
    let _ =
      if not !Globals.disable_failure_explaining then
        let s,fk,ets= CF.get_failure_list_partial_context rs in
        let failure_str = if List.exists (fun et -> et = Mem 1) ets then
            "memory leak failure" else
            "Post condition cannot be derived" in
        let () = x_tinfo_hp (add_str "failure_str: " (pr_id)) s pos in
        Err.report_error {
          Err.error_loc = pos;
          Err.error_text = (failure_str ^".")
        }
      else if not (!Globals.enable_repair) then
        begin
          Debug.print_info ("("^(Cprinter.string_of_label_list_partial_context rs)^") ")
            ("Postcondition cannot be derived from context\n")
            pos;
          Debug.print_info ("(Cause of PostCond Failure)")
            (Cprinter.string_of_failure_list_partial_context rs) pos;
          Err.report_error {
            Err.error_loc = pos;
            Err.error_text = Printf.sprintf
                "Post condition cannot be derived by the system."
          }
        end
      else
        Err.report_error {
          Err.error_loc = pos;
          Err.error_text = Printf.sprintf
              "Post condition cannot be derived by the system."
        } in
    rs
  end

(* process each scc set of mutual-rec procedures *)
(* to be used for inferring phase constraints *)
(* replacing each spec with new spec with phase numbering *)
and proc_mutual_scc (prog: prog_decl) (proc_lst : proc_decl list)
    (fn:prog_decl -> proc_decl -> bool) =
  let rec helper tot_r lst =
    match lst with
    | [] -> tot_r (*()*)
    | p::ps ->
      let nres =
        try
          let () =  DD.ninfo_hprint
              (add_str "proc_mutual_scc: proc_lst" Cprinter.string_of_struc_formula)
              (p.proc_stk_of_static_specs # top) no_pos in
          let cur_r = (fn prog p) in
          let () = if not cur_r then
              let () = if not !Globals.web_compile_flag
                then Debug.ninfo_hprint (add_str "proc.proc_name" pr_id)
                    (p.proc_name) no_pos in
              ()
            else () in
          tot_r && cur_r
        with _ as e -> raise e
      in
      helper nres ps
  in
  (*verify one scc - collect assumptions if applicable*)
  let res = helper true proc_lst in
  res

let proc_mutual_scc_shape_infer iprog prog pure_infer ini_hp_defs scc_procs =
  let _ =  Debug.ninfo_hprint (add_str "proc_mutual_scc_shape_infer: STARTING" (
      let pr proc = Cprinter.string_of_struc_formula_for_spec_inst prog
          (proc.proc_stk_of_static_specs # top) in
      pr_list_ln  pr)) scc_procs no_pos in
  if not(!Globals.pred_infer_flag) then ()
  else
    (*solve the set of assumptions for scc*)
    let scc_hprel_ass = Infer.scc_rel_ass_stk # get_stk in
    let scc_hprel_unkmap =  List.fold_left (fun r_map proc ->
        r_map@proc.Cast.proc_hprel_unkmap) [] scc_procs in
    let scc_sel_hps = !scc_proc_sel_hps in
    let scc_sel_post_hps = CP.remove_dups_svl (!scc_proc_sel_post_hps
                                               @Iincr.get_post_preds_scc
                                                 scc_procs) in
    let () = Debug.ninfo_hprint
        (add_str "proc_mutual_scc_shape_infer: List.length scc_hprel_ass"
           string_of_int) (List.length scc_hprel_ass) no_pos in
    let proc = List.hd scc_procs in
    (* ************************************ *)
    (* *************INTENAL********************* *)
    (* inter form *)
    let print_hp_defs_one_flow hp_defs flow_int=
      begin
        let defs0 = List.sort CF.hp_def_cmp hp_defs in
        let pre_preds,post_pred,rem = List.fold_left ( fun (r1,r2,r3) d ->
            match d.CF.def_cat with
            | CP.HPRelDefn (hp,_,_) -> if (CP.mem_svl hp scc_sel_post_hps) then (r1,r2@[d],r3) else
              if (CP.mem_svl hp scc_sel_hps) then (r1@[d],r2,r3) else (r1,r2,r3@[d])
            | _ -> (r1,r2,r3@[d]) ) ([],[],[]) defs0 in
        let defs1 = pre_preds@post_pred@rem in
        let defs = if !Globals.print_en_tidy then List.map Cfout.rearrange_hp_def defs1 else defs1 in
        print_endline_quiet "\n*********************************************************";
        let () = if !Globals.sae then print_endline_quiet
              ("*******relational definition (flow = "
               ^(!Cformula.print_flow flow_int) ^")********")
          else print_endline_quiet ("*******relational definition ********")
        in
        print_endline_quiet "*********************************************************";
        if !Globals.testing_flag then print_endline_quiet "<dstart>";
        let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def_short in
        let old_print_imm = !print_ann in
        let _= if !print_html then let () = print_ann:= false in () else () in
        print_endline_quiet (pr1 defs);
        let () = print_ann:=  old_print_imm in
        if !Globals.testing_flag then print_endline_quiet "<dstop>";
        print_endline_quiet "*************************************";
        ()
      end;
    in
    (* final form *)
    let print_hpdefs_one_flow flow_int=
      if not !Globals.new_pred_syn then
        begin
          let hpdefs = List.filter (fun hpdef ->
              match hpdef.CF.hprel_def_flow with
              | Some ifl -> CF.equal_flow_interval flow_int ifl
              | None -> false
            ) CF.rel_def_stk# get_stk in
          let defs0 = List.sort CF.hpdef_cmp hpdefs in
          let pre_preds,post_pred,rem = List.fold_left ( fun (r1,r2,r3) d ->
              match d.CF.hprel_def_kind with
              | CP.HPRelDefn (hp,_,_) -> if (CP.mem_svl hp scc_sel_post_hps) then (r1,r2@[d],r3) else
                if (CP.mem_svl hp scc_sel_hps) then (r1@[d],r2,r3) else (r1,r2,r3@[d])
              | _ -> (r1,r2,r3@[d]) ) ([],[],[]) defs0 in
          let defs1 = pre_preds@post_pred@rem in
          let defs = if !Globals.print_en_tidy then List.map Cfout.rearrange_def defs1 else defs1 in
          print_endline_quiet "\n************************************";
          let () = if !Globals.sae then print_endline_quiet
                ("*******relational definition (flow= "
                 ^(!Cformula.print_flow flow_int) ^")********")
            else
              print_endline_quiet ("*******relational definition" ^"********")
          in
          print_endline_quiet "*********************************************************";
          if !Globals.testing_flag then print_endline_quiet "<dstart>";
          let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
          let old_print_imm = !print_ann in
          let _= if !print_html then let () = print_ann:= false in () else () in
          print_endline_quiet (pr1 defs);
          let () = print_ann:=  old_print_imm in
          if !Globals.testing_flag then print_endline_quiet"<dstop>";
          print_endline_quiet "*************************************";
          ()
        end;
    in
    let do_infer_one_flow hprels scc_sel_hps0 flow_int=
      let () = if !Globals.sae
        then Debug.info_hprint (add_str "shape inference for flow" !
                                  Cformula.print_flow) flow_int  no_pos
        else ()
      in
      let (a, hp_defs,c) =
        if not (!Globals.pred_syn_modular) then
          if not (!Globals.sa_dnc) then
            let r1,r2,r3 = x_add (* Sa2. *)Sa3.infer_shapes iprog prog "" hprels
                scc_sel_hps scc_sel_post_hps (Gen.BList.remove_dups_eq
                                                (fun ((hp1,_),_) ((hp2, _),_) ->
                                                   (CP.eq_spec_var hp1 hp2 ))
                                                scc_hprel_unkmap) [] [] true
                true flow_int
            in
            (r1,r2,r3)
          else
            let todo_unk = x_add Sa3.infer_shapes iprog prog "" hprels
                scc_sel_hps scc_sel_post_hps (Gen.BList.remove_dups_eq
                                                (fun ((hp1,_),_) ((hp2, _),_) ->
                                                   (CP.eq_spec_var hp1 hp2 ))
                                                scc_hprel_unkmap) [] [] true
                true flow_int in
            ([],[], [])
        else
          let r = Sa3.infer_shapes iprog prog proc.proc_name (* "" *) hprels
              scc_sel_hps0 scc_sel_post_hps (Gen.BList.remove_dups_eq
                                               (fun ((hp1,_),_) ((hp2, _),_) ->
                                                  (CP.eq_spec_var hp1 hp2 ))
                                               scc_hprel_unkmap) [] [] true true
              flow_int
          in
          r
      in
      let sel_hps = List.map (fun hp_def -> Cformula.get_hpdef_name
                                 hp_def.Cformula.def_cat) hp_defs in
      (a, hp_defs,c, sel_hps)
    in
    (* ************************************ *)
    (* *************END INTENAL********************* *)
    let scc_hprel, scc_inferred_hps, dang_hps =
      if !Globals.pred_syn_flag && List.length scc_sel_hps> 0 then
        if is_empty scc_hprel_ass then
          let () = report_warning no_pos
              ("Shape inference is not performed due to empty hprel set") in
          [], [], []
        else
          let (a,b,c,_) =
            let hprels_flows = x_add_1 Cformula.partition_hprel_flow scc_hprel_ass in
            List.fold_left (fun (r1,r2,r3,scc_sel_hps1) (hprels, flow_n) ->
                let l1,l2,l3, new_sel_hps = do_infer_one_flow hprels scc_sel_hps1 flow_n in
                let () = print_hpdefs_one_flow (* l2 *) flow_n in
                r1@l1,r2@l2,r3@l3, CP.remove_dups_svl (scc_sel_hps1@new_sel_hps)
              ) ([],[],[],scc_sel_hps) hprels_flows
          in
          (a,b,c)
      else [],[],[]
    in
    (* update hpdefs for func call *)
    let () =
      if not !Globals.new_pred_syn then (* --old-pred-synthesis *)
        List.iter (fun proc ->
            let () = Cast.update_hpdefs_proc prog.Cast.new_proc_decls
                scc_inferred_hps proc.proc_name in
            ()) scc_procs
      else
        let () = y_tinfo_hp (add_str "cviews"
                               (pr_list Cprinter.string_of_view_decl_short))
            prog.prog_view_decls in
        let () = y_tinfo_hp (add_str "iviews"
                               (pr_list Iprinter.string_of_view_decl))
            iprog.prog_view_decls in
        ()
    in
    let rel_defs = if not (!Globals.pred_syn_modular) then CF.rel_def_stk (* Sa2.rel_def_stk *)
      else CF.rel_def_stk
    in
    let inferred_hpdefs = (rel_defs# get_stk) in
    if (* !Globals.sae *) false && not(rel_defs# is_empty) (* && !VarGen.sap *) then
      begin
        let defs0 = List.sort CF.hpdef_cmp (rel_defs # get_stk) in
        (* combine predicate based on flows *)
        let pre_preds,post_pred,rem = List.fold_left ( fun (r1,r2,r3) d ->
            match d.CF.hprel_def_kind with
            | CP.HPRelDefn (hp,_,_) -> if (CP.mem_svl hp scc_sel_post_hps) then (r1,r2@[d],r3) else
              if (CP.mem_svl hp scc_sel_hps) then (r1@[d],r2,r3) else (r1,r2,r3@[d])
            | _ -> (r1,r2,r3@[d]) ) ([],[],[]) defs0 in
        let defs1 = pre_preds@post_pred@rem in
        let defs = if !Globals.print_en_tidy then List.map Cfout.rearrange_def defs1 else defs1 in
        print_endline_quiet "\n*************************************";
        print_endline_quiet "*******relational definition ********";
        print_endline_quiet "*************************************";
        if !Globals.testing_flag then print_endline_quiet "<dstart>";
        let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
        let old_print_imm = !print_ann in
        let _= if !print_html then let () = print_ann:= false in () else () in
        print_endline_quiet (pr1 defs);
        let () = print_ann:=  old_print_imm in
        if !Globals.testing_flag then print_endline_quiet "<dstop>";
        print_endline_quiet "*************************************";
        let () = CF.rel_def_stk # reset in
        ()
      end;
    (*transform the result: hpdef --> views and transform specs*)
    (*   scc_inferred_hps  *)
    let scc_procs_names = (Gen.BList.remove_dups_eq (fun s1 s2 ->
        String.compare s1 s2 ==0) (List.map (fun proc -> proc.proc_name)
                                     scc_procs)) in
    let new_scc_procs =
      if !Globals.pred_trans_view then
        let nprog, is_print_inferred_spec =
          if not !Globals.new_pred_syn then (* --old-pred-synthesis *)
            match scc_procs with
            | [] -> prog,false
            | [p] -> if p.Cast.proc_sel_hps != [] then
                let nprog = x_add Saout.plug_shape_into_specs prog iprog
                    dang_hps scc_procs_names
                    (CP.diff_svl scc_sel_hps scc_sel_post_hps) scc_sel_post_hps
                    scc_inferred_hps in
                let new_scc_procs =
                  List.map (fun pn -> Cast.look_up_proc_def_raw
                               nprog.new_proc_decls pn) scc_procs_names in
                nprog,true
              else prog,false
            | _ ->
              let nprog = x_add Saout.plug_shape_into_specs prog iprog dang_hps
                  scc_procs_names (CP.diff_svl scc_sel_hps scc_sel_post_hps)
                  scc_sel_post_hps scc_inferred_hps in
              let new_scc_procs = List.map (fun pn -> Cast.look_up_proc_def_raw
                                               nprog.new_proc_decls pn)
                  scc_procs_names in
              nprog,true
          else
          if is_empty scc_sel_hps || is_empty scc_hprel_ass then prog, false
          else
            let () = Norm.find_rec_data iprog prog REGEX_STAR in
            let extn_pred_lsts = Syn.extn_pred_scc iprog prog scc_procs_names in
            let prog = SynUtils.trans_hrel_to_view_spec_scc prog scc_procs_names in
            let prog = SynUtils.remove_inf_vars_spec_scc prog scc_procs_names scc_sel_hps in
            prog, true
        in
        let new_scc_procs = List.map (fun pn -> Cast.look_up_proc_def_raw
                                         nprog.new_proc_decls pn)
            scc_procs_names in
        let () = List.iter (fun proc ->
            if is_print_inferred_spec then
              let () = x_binfo_hp (add_str "INFERRED SHAPE SPEC"
                                     (Cprinter.string_of_struc_formula))
                  (proc.proc_stk_of_static_specs#top) no_pos in
              ()
            else ()
          ) new_scc_procs in
        new_scc_procs
      else scc_procs
    in
    (**************regression check _ gen_regression file******************)
    (*to revise the check for scc*)
    let proc = List.hd scc_procs in
    let () = if(!Globals.validate || !Globals.cp_prefile) then
        (*update lib def*)
        let scc_inferred_hps1 = CEQ.update_lib inferred_hpdefs
            (scc_inferred_hps@ini_hp_defs)  scc_sel_hps in
        CEQ.validate proc scc_hprel_ass scc_inferred_hps1 scc_sel_hps in
    (**************end cp_test _ gen_cpfile******************)
    ()

(* checking procedure: (PROC p61) *)
and check_proc iprog (prog : prog_decl) (proc0 : proc_decl) cout_option
    (mutual_grp : proc_decl list) : bool =
  Debug.vv_debug ("check_proc:"^proc0.proc_name);
  let unmin_name = unmingle_name proc0.proc_name in
  let () = Globals.check_post := false in
  let () =  Debug.tinfo_hprint (add_str "in check_proc proc0"
                                  (Cprinter.string_of_struc_formula_for_spec_inst prog))
      (proc0.Cast.proc_stk_of_static_specs # top) no_pos in
  let proc = find_proc prog proc0.proc_name in
  let () = Synt.syn_iprog := Some iprog in
  let () = Synt.syn_cprog := Some prog in
  let () = x_tinfo_hp (add_str "in check_proc proc"
                         (Cprinter.string_of_struc_formula_for_spec_inst prog))
      (proc.Cast.proc_stk_of_static_specs # top) no_pos in
  let check_flag = ((Gen.is_empty !procs_verified)
                    || List.mem unmin_name !procs_verified)
                   && not (List.mem unmin_name !Inliner.inlined_procs) in
  let () = if !Globals.enable_repair then
      Globals.verified_procs := (!Globals.verified_procs) @ ["fcode"] in
  if List.mem proc0.proc_name (!Globals.verified_procs) then true
  else if check_flag then
    begin
      match proc.proc_body with
      | None -> true (* sanity checks have been done by the translation *)
      | Some body ->
        begin
          stk_vars # reset;
          let () = Excore.UnCa.reset_cache () in
          (* push proc.proc_args *)
          let args = List.map (fun (t,i) -> CP.SpecVar(t,i,Unprimed) ) proc.proc_args in
          stk_vars # push_list args;
          let () = x_dinfo_hp (add_str "start check_proc" pr_id)
              (stk_vars # string_of_no_ln) no_pos in
          let pr_flag = not(!phase_infer_ind) in
          let sel_hps = CF.get_hp_rel_name_struc (proc0.Cast.proc_stk_of_static_specs # top) in
          let () =  x_tinfo_hp (add_str "sel_hps" (!CP.print_svl) ) sel_hps no_pos in
          let () =
            if sel_hps = [] then () else
              begin
                print_endline_quiet "";
                print_endline_quiet "\n\n*******************************";
                print_endline_quiet     "******* SPECIFICATION 1 *******";
                print_endline_quiet     "*******************************";
                print_endline_quiet
                  (Cprinter.string_of_struc_formula_for_spec_inst prog
                     (proc0.proc_stk_of_static_specs # top));
                flush stdout
                (* proc0.Cast.proc_static_specs *)
              end in
          (*****LOCKSET variable: ls'=ls *********)
          let args =
            if (!allow_ls) then
              let lsmu_var = (lsmu_typ,lsmu_name) in
              let ls_var = (ls_typ,ls_name) in
              if (!Globals.allow_locklevel) then
                (*LS and LSMU are ghost variables*)
                lsmu_var::ls_var::proc.proc_args
              else
                ls_var::proc.proc_args
            else
              proc.proc_args in
          (******************************)
          let ftypes, fnames = List.split args in
          (* fsvars are the spec vars corresponding to the parameters *)
          let fsvars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in
          let pf = (CF.no_change fsvars proc.proc_loc) in (*init(V) := v'=v*)
          let nox = CF.formula_of_pure_N pf proc.proc_loc in
          let init_form = nox in
          let init_ctx1 = CF.empty_ctx (CF.mkTrueFlow ()) LO2.unlabelled  proc.proc_loc in
          let init_ctx = CF.build_context init_ctx1 init_form proc.proc_loc in
          (* Termination: Add the set of logical variables into the initial context *)
          let init_ctx =
            if !Globals.dis_term_chk then init_ctx
            else Infer.restore_infer_vars_ctx proc.proc_logical_vars [] init_ctx in
          let () = x_tinfo_hp (add_str "Init Ctx" !CF.print_context) init_ctx no_pos in
          let () = if !print_proof then begin
              Prooftracer.push_proc proc;
              Prooftracer.start_compound_object ();
            end in
          let pp, exc =
            try
              (* catch exception to close the section appropriately *)
              let spec = proc0.proc_stk_of_static_specs # top in
              let () = x_tinfo_hp (add_str "in check_proc proc spec:"
                                     (Cprinter.string_of_struc_formula_for_spec_inst
                                        prog)) spec no_pos in
              let (new_spec,fm,rels,hprels,sel_hp_rels,sel_post_hp_rels,
                   hp_rel_unkmap,f) = check_specs_infer prog proc init_ctx spec
                  body true in
              x_tinfo_hp (add_str "SPECS (after specs_infer)" pr_spec) new_spec no_pos;
              x_dinfo_hp (add_str "fm formula " (pr_list !CF.print_formula)) fm no_pos;
              (* let new_spec = x_add_1 CF.simplify_ann new_spec in *)
              let (rels,rest) =
                (List.partition (fun (a1,a2,a3) -> match a1 with
                     | CP.RelDefn _ -> true
                     | _ -> false) rels) in
              let (lst_assume,lst_rank) = (List.partition
                                             (fun (a1,a2,a3) -> match a1 with
                                                | CP.RelAssume _ -> true
                                                | _ -> false) rest) in
              let (hprels,hp_rest) = (List.partition
                                        (fun hp -> match hp.CF.hprel_kind with
                                           | CP.RelDefn _ -> true
                                           | _ -> false) hprels) in
              let (hp_lst_assume,hp_rest) =
                (List.partition (fun hp -> match hp.CF.hprel_kind with
                     | CP.RelAssume _ -> true | _ -> false) hp_rest) in
              let rels = List.map (fun (_,a2,a3)-> (a2,a3)) rels in
              (****************************************************************)
              (********************SHAPE INFER*****************************)
              (****************************************************************)
              (*store assumption. solve it when we finish analyse its scc*)
              let flow_hp_rel_ass = x_add_1 Cformula.partition_hprel_flow hp_lst_assume in
              let () = Debug.ninfo_hprint
                  (add_str "flow_hp_rel_ass"
                     (pr_list_ln (pr_pair
                                    ( pr_list_ln Cprinter.string_of_hprel_short)
                                    !Cformula.print_flow)) ) (flow_hp_rel_ass)  no_pos in
              let () = proc0.Cast.proc_hprel_ass <- proc.Cast.proc_hprel_ass@flow_hp_rel_ass in
              let () = proc0.Cast.proc_hprel_unkmap <- proc.Cast.proc_hprel_unkmap@hp_rel_unkmap in
              let () = proc0.Cast.proc_sel_hps <- proc.Cast.proc_sel_hps@sel_hp_rels in
              let () = scc_proc_sel_hps := !scc_proc_sel_hps@sel_hp_rels in
              let () = proc0.Cast.proc_sel_post_hps
                <- proc.Cast.proc_sel_post_hps@sel_post_hp_rels in
              let () = scc_proc_sel_post_hps := !scc_proc_sel_post_hps@sel_post_hp_rels in
              if not(Infer.rel_ass_stk# is_empty) then
                begin
                  if (* !VarGen.sap *) true then begin
                    print_endline_quiet "";
                    print_endline_quiet "********************************************";
                    print_endline_quiet "******* shape relational assumptions *******";
                    print_endline_quiet "********************************************";
                  end;
                  let ras = Infer.rel_ass_stk # get_stk in
                  let () = Infer.scc_rel_ass_stk # push_list ras in
                  let () = Infer.rel_ass_stk # reset in
                  if (* !VarGen.sap *) true then begin
                    let ras = List.rev(ras) in
                    let ras1 = if !Globals.print_en_tidy
                      then List.map Cfout.rearrange_rel ras else ras in
                    if !Globals.testing_flag
                    then print_endline_quiet
                        ("<rstart>"^(string_of_int (List.length ras)));
                    let pr = pr_list_ln (fun x ->
                        Cprinter.string_of_hprel_short_inst prog
                          sel_post_hp_rels x) in
                    let pr_len x = string_of_int (List.length x) in
                    let old_print_imm = !print_ann in
                    let _= if !print_html then let () = print_ann:= false in () else () in
                    let _  = print_endline_quiet (pr (ras1)) in
                    let () = print_ann:=  old_print_imm in
                    if !Globals.testing_flag
                    then print_endline_quiet
                        "<rstop>*************************************"
                  end
                end;
              (**************end cp_test _ gen_cpfile******************)
              let lst_rank = List.map (fun (_,a2,a3)-> (a2,a3)) lst_rank in
              (* TODO:WN : add_pre may be redundant here *)
              x_tinfo_hp (add_str "SPECS (after simplify_ann)" pr_spec) new_spec no_pos;
              x_tinfo_hp (add_str "SPECS (before add_pre)" pr_spec) new_spec no_pos;
              x_tinfo_hp (add_str "NEW SPECS(B4)" pr_spec) new_spec no_pos;
              let new_spec = x_add_1 Astsimp.add_pre prog new_spec in
              x_tinfo_hp (add_str "NEW SPECS(AF)" pr_spec) new_spec no_pos;

              if (pre_ctr # get> 0)
              then
                begin
                  let new_spec = if rels=[] then proc.proc_stk_of_static_specs # top else
                      proc.proc_stk_of_static_specs # top in
                  if !dis_post_chk then
                    (f,None)
                  else
                    begin
                      let () = if prepost_ctr # get > 0 then
                          Debug.info_ihprint (add_str "NEW SPECS" pr_spec)
                            new_spec no_pos else () in
                      let () = prepost_ctr # reset in
                      Debug.ninfo_hprint
                        (add_str "NEW RELS"
                           (pr_list_ln Cprinter.string_of_only_lhs_rhs)) rels
                        no_pos;
                      Debug.ninfo_hprint (add_str "NEW ASSUME"
                                            (pr_list_ln
                                               Cprinter.string_of_lhs_rhs))
                        lst_assume no_pos;
                      Debug.ninfo_hprint (add_str "NEW HP RELS"
                                            (pr_list_ln Cprinter.string_of_hprel
                                            )) hprels no_pos;
                      Debug.ninfo_hprint (add_str "NEW HP ASSUME"
                                            (pr_list_ln Cprinter.string_of_hprel
                                            )) hp_lst_assume no_pos;
                      x_tinfo_hp (add_str "NEW RANK"
                                    (pr_list_ln Cprinter.string_of_only_lhs_rhs)
                                 ) lst_rank no_pos;
                      stk_evars # reset;
                      let () = if not (!do_infer_inc) then ()
                        else Infer.print_spec (" " ^ (Infer.get_proc_name proc.proc_name) ^ "\n" ^
                                               (pr_spec2 (CF.struc_to_prepost new_spec)))
                            (Infer.get_file_name Sys.argv.(1)) in
                      (f, None)
                    end
                end
              else (f, None)
            with | _ as e -> (false, Some e) in
          let () = if !print_proof then begin
              Prooftracer.pop_div ();
              Prooftracer.add_proc proc pp;
            end
          in
          let () = match exc with
            | Some e -> raise e
            | None -> () in
          if pr_flag then
            begin
              if pp then
                let () = if (!Globals.enable_repair) then
                    let () = verified_procs := [proc0.proc_name] @(!verified_procs) in
                    () else () in
                if !Globals.web_compile_flag then
                  print_string_quiet ("\nProcedure <b>"^proc.proc_name
                                      ^"</b> <font
              color=\"blue\">SUCCESS</font>.\n")
                else
                  print_web_mode ("\nProcedure "^proc.proc_name^" SUCCESS333.\n")
              else
                let () = Log.last_cmd # dumping (proc.proc_name^" FAIL-1") in
                if !Globals.web_compile_flag then
                  begin
                    print_string_quiet ("\nProcedure <b>"^proc.proc_name
                                        ^"</b> result <font
              color=\"red\">FAIL</font>.\n");
                    (if proving_loc#is_avail then
                       Printf.printf "\nLast PPProving Locationnnnnnnnnnnnnnnndfff: %s\n"
                         proving_loc#string_of
                     else ())
                  end
                else
                  print_web_mode ("\nProcedure "^proc.proc_name^" result FAIL.(1)\n")
            end;
          pp
        end
    end else true

let check_proc iprog (prog : prog_decl) (proc : proc_decl) cout_option (mutual_grp : proc_decl list) : bool =
  let pr p = pr_id (name_of_proc p)  in
  let pr p = !Cast.print_proc_decl_no_body p in
  Debug.no_1_opt (fun _ -> not(is_primitive_proc proc))
    "check_proc" pr string_of_bool (fun _ -> check_proc iprog prog proc cout_option mutual_grp) proc

let reverify_proc prog proc do_infer =
  if !reverify_flag then
    match proc.proc_body with
    | None -> ()
    | Some body ->
      stk_vars # reset;
      (* push proc.proc_args *)
      let args = List.map (fun (t,i) -> CP.SpecVar(t,i,Unprimed) ) proc.proc_args in
      stk_vars # push_list args;
      let () = x_tinfo_hp (add_str "inside reverify" pr_id) (stk_vars # string_of_no_ln) no_pos in
      let pr_flag = not(!phase_infer_ind) in
      let new_spec = proc.proc_stk_of_static_specs # top in
      (* Do not remove inf_cmd when do_infer *)
      let new_spec = if not do_infer then CF.remove_inf_cmd_spec new_spec else new_spec in
      if !Globals.print_proc && pr_flag && (not !Globals.web_compile_flag) then
        print_string_quiet ("Procedure " ^ proc.proc_name ^ ":\n"
                            ^ (Cprinter.string_of_proc_decl 3 proc) ^ "\n\n");
      if pr_flag then
        begin
          print_string_quiet (("\nChecking procedure ") ^ proc.proc_name
                              ^ " (re-verifying ...)"); flush stdout;
          x_dinfo_zp (lazy (("Checking procedure ") ^ proc.proc_name ^ "... ")) proc.proc_loc;
          x_dinfo_zp (lazy ("Specs :\n" ^ (Cprinter.string_of_struc_formula
                                             new_spec))) proc.proc_loc;
        end;
      let () =
        begin
          if (not !Globals.web_compile_flag) then
            print_endline_quiet "";
          print_endline_quiet "\n\n*******************************";
          print_endline_quiet     "******* SPECIFICATION 2 *******";
          print_endline_quiet     "*******************************";
          print_endline_quiet (Cprinter.string_of_struc_formula(*_for_spec_inst prog*) new_spec);
        end
      in
      (*****LOCKSET variable: ls'=ls *********)
      let args =
        if (!allow_ls) then
          let lsmu_var = (lsmu_typ,lsmu_name) in
          let ls_var = (ls_typ,ls_name) in
          if (!Globals.allow_locklevel) then
            (*LS and LSMU are ghost variables*)
            lsmu_var::ls_var::proc.proc_args
          else
            ls_var::proc.proc_args
        else
          proc.proc_args in
      (******************************)
      (* fsvars are the spec vars corresponding to the parameters *)
      let fsvars = List.map (fun (t, v) -> CP.mk_typed_sv t v) args in
      let pf = (CF.no_change fsvars proc.proc_loc) in
      let nox = CF.formula_of_pure_N pf proc.proc_loc in
      let init_form = nox in
      let init_ctx1 = CF.empty_ctx (CF.mkTrueFlow ()) LO2.unlabelled  proc.proc_loc in
      (*add default full permission = 1.0 to ante;
        need to add type of full perm to stab
      *)
      let init_form =
        if (Perm.allow_perm ()) then
          CF.add_mix_formula_to_formula (full_perm_constraint ()) init_form
        else
          init_form in
      let init_ctx = CF.build_context init_ctx1 init_form proc.proc_loc in
      (* Termination: Add the set of logical variables into the initial context *)
      let init_ctx =
        if !Globals.dis_term_chk then init_ctx
        else Infer.restore_infer_vars_ctx proc.proc_logical_vars [] init_ctx in
      let () = x_tinfo_hp (add_str "Init Ctx" !CF.print_context) init_ctx no_pos in
      let _,_,_,_,_,_,_,is_valid = check_specs_infer prog proc init_ctx new_spec body do_infer in
      x_ninfo_hp (add_str "Performing a Re-verification, Valid?" string_of_bool) is_valid no_pos;
      ()
  else ()

let reverify_scc prog scc do_infer =
  List.iter (fun proc -> reverify_proc prog proc do_infer) scc

let reverify_scc prog scc do_infer =
  let pr_scc = pr_list (fun proc -> proc.proc_name) in
  let pr_dummy = fun _ -> "" in
  Debug.no_2 "reverify_scc" pr_scc string_of_bool pr_dummy
    (fun _ _ -> reverify_scc prog scc do_infer) scc do_infer

let check_phase_only iprog prog proc =
  (* check_proc prog proc *)
  try
    let _ = check_proc iprog prog proc in ()
  with _ as e -> (
      print_string_quiet ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      print_string_quiet ("\nException "^(Printexc.to_string e)^" during check_phase_only!\n");
      print_backtrace_quiet ();
    )

(* check entire program *)
let check_proc_wrapper iprog prog proc cout_option mutual_grp =
  try
    let () = Debug.ninfo_hprint
        (add_str "check_proc_wrapper"
           (Cprinter.string_of_struc_formula_for_spec_inst prog))
        proc.Cast.proc_stk_of_static_specs # top  no_pos in
    let res = check_proc iprog prog proc cout_option mutual_grp in
    res
  with _ as e ->
    raise e

let check_data iprog (prog : prog_decl) (cdef : data_decl) =
  try
    List.map (check_proc_wrapper iprog prog) cdef.data_methods
  with e ->
    raise e

let check_coercion (prog : prog_decl) =
  let find_coerc coercs name =
    try
      [(List.find (fun coerc -> coerc.coercion_name = name) coercs)]
    with _ -> []
  in

  (* combine the 2 lists of coercions into one list of lemmas:
     - coercions that have the same name in the left and right list of coercions -> (Some c1,Some c2)
     - left coercion c -> (Some c, one)
     - right coercion c -> (None, Some c)
  *)
  let left_coercs  =  List.filter (fun c -> c.Cast.coercion_kind != LEM_UNSAFE )
      (Lem_store.all_lemma # get_left_coercion) in
  let right_coercs = List.filter (fun c -> c.Cast.coercion_kind != LEM_UNSAFE )
      ( Lem_store.all_lemma # get_right_coercion) in
  let lemmas = List.map (fun l2r_coerc ->
      ([l2r_coerc], find_coerc right_coercs
         l2r_coerc.coercion_name) ) left_coercs in

  (* add to lemmas the coercions from prog.prog_right_coercions that do not have
     a corresponding pair in prog.prog_left_coercions *)
  let lemmas = lemmas @ List.map (fun r2l_coerc -> ([], [r2l_coerc]))
                 (List.filter
                    (fun r2l_coerc -> List.for_all
                        (fun l2r_coerc -> r2l_coerc.coercion_name
                                          <> l2r_coerc.coercion_name)
                        left_coercs)
                    right_coercs) in
  List.iter (fun (l2r, r2l) ->
      let (coerc_type, coerc_name) =
        let coercs = l2r @ r2l in
        match coercs with
        | [c] ->
          let typ = (match c.coercion_type_orig with
              | None -> c.coercion_type
              | Some t -> t
            ) in
          (typ, c.coercion_name)
        | c1::c2::[] -> (I.Equiv, c1.coercion_name)
        | _ ->  Error.report_error {Err.error_loc = no_pos;
                                    Err.error_text =
                                      "[typechecker.ml]: Lemma must contain only
  1 or 2 coercions."}
      in
      (* Andrea : why is hip not using process_lemma in sleekengine.ml *)
      let todo_unk = x_add (Lemproving.verify_lemma ~force_pr:true) 1 l2r r2l
          prog coerc_name coerc_type in ()
    ) lemmas

let init_files () =
  begin
    Omega.init_files ();
    Setmona.init_files ();
  end

let check_proc_wrapper_map iprog prog (proc,num) cout_option =
  Debug.vv_debug ("check_proc_wrapper_map:"^proc.proc_name) ;
  if !Tpdispatcher.external_prover then
    Tpdispatcher.Netprover.set_use_socket_map
      (List.nth !Tpdispatcher.external_host_ports
         (num mod (List.length !Tpdispatcher.external_host_ports)));
  (* make this dynamic according to availability of server machines*)
  try
    check_proc iprog prog proc cout_option []
  with _ as e ->
    if !Globals.check_all then begin
      print_web_mode ("\nProcedure "^proc.proc_name^" FAIL.(3)\n");
      print_string_quiet ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      false
    end else
      raise e

let check_proc_wrapper_map_net iprog prog  (proc,num) cout_option =
  try
    check_proc iprog prog proc cout_option []
  with _ as e ->
    if !Globals.check_all then begin
      print_web_mode ("\nProcedure "^proc.proc_name^" FAIL.(4)\n");
      print_string_quiet ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      false
    end else
      raise e

let stk_tmp_checks = new Gen.stack


let drop_phase_infer_checks() =
  stk_tmp_checks # push !dis_bnd_chk;
  stk_tmp_checks # push !dis_term_msg;
  stk_tmp_checks # push !dis_post_chk;
  stk_tmp_checks # push !dis_ass_chk;
  dis_bnd_chk := true;
  dis_term_msg := true;
  dis_post_chk := true;
  dis_ass_chk := true;
  phase_infer_ind := true

let restore_phase_infer_checks() =
  phase_infer_ind := false;
  dis_ass_chk := stk_tmp_checks # pop_top;
  dis_post_chk := stk_tmp_checks # pop_top;
  dis_term_msg := stk_tmp_checks # pop_top;
  dis_bnd_chk := stk_tmp_checks # pop_top

let lookup_called_procs_x iprog prog root_scc verified_sccs=
  let called_procs = List.fold_left (fun r p ->
      let procs = Cast.callees_of_proc prog (Cast.unmingle_name p.Cast.proc_name) in
      r@procs
    ) [] root_scc in
  let () = Debug.ninfo_hprint (add_str "called_procs" (pr_list pr_id)) called_procs no_pos in
  List.fold_left (fun r scc ->
      let called_scc = List.filter (fun p ->
          let pn = Cast.unmingle_name p.proc_name in
          List.exists (fun called_proc -> String.compare pn called_proc =0 ) called_procs) scc
      in
      if called_scc = [] then r else r@[called_scc]
    ) [] verified_sccs

let lookup_called_procs iprog prog root_scc verified_sccs=
  let pr1 p = pr_id p.proc_name in
  let pr2 = pr_list pr1 in
  Debug.no_2 "lookup_called_procs" pr2 (pr_list_ln pr2) (pr_list_ln pr2)
    (fun _ _ -> lookup_called_procs_x iprog prog root_scc verified_sccs)
    root_scc verified_sccs

let print_infer_scc loc scc =
  let rec collect s =
    match s with
    | CF.EList lst -> List.concat (List.map (fun (_,s) -> collect s) lst)
    | CF.EInfer s -> (s.CF.formula_inf_vars,s.CF.formula_inf_obj)
                     ::(collect s.CF.formula_inf_continuation)
    | _ -> [] in
  let head = "XXXX" in
  let () = y_dinfo_zp (lazy ("\n"^head^"Current SCC EInfer :"^loc)) in
  let () = y_dinfo_zp (lazy (
      let lst = List.map (fun p ->
          let lst = p.proc_stk_of_static_specs # get_stk in
          (p.proc_name, List.map collect lst)) scc in
      head^((pr_list (pr_pair pr_id
                        (pr_list_num
                           (pr_list_n (pr_pair !CP.print_svl (fun o -> o#string_of)))))) lst))) in
  let () = y_dinfo_zp (lazy (pr_list_ln
                               (fun p -> Cprinter.string_of_struc_formula
                                   (p.proc_stk_of_static_specs # top)) scc)) in
  ()

let ext_pure_check_procs iprog prog proc_names error_traces=
  let  todo_unk = Sap.extend_specs_views_pure_ext iprog prog proc_names error_traces in
  []

let rec check_prog (iprog: Iast.prog_decl) (prog : Cast.prog_decl) =
  let cout_option = None in
  let () = I.set_iprog iprog in
  ignore(List.map (check_data iprog prog) prog.prog_data_decls);
  let l_proc = Cast.list_of_procs prog in
  let proc_prim, proc_main = List.partition Cast.is_primitive_proc l_proc in
  let () = x_tinfo_hp (add_str "prog"
                         (pr_list (Cprinter.string_of_proc_decl 1))
                      ) proc_main no_pos in
  let sorted_proc_main = Cast.sort_proc_decls proc_main in
  let () = x_tinfo_hp (add_str "sorted_proc_main"
                         (pr_list Astsimp.pr_proc_call_order)
                      ) sorted_proc_main no_pos in
  (* this computes a list of scc mutual-recursive methods for processing *)
  let proc_scc = List.fold_left (fun a x -> match a with
      | [] -> [[x]]
      | xs::xss ->
        let i=(List.hd xs).proc_call_order in
        if i==x.proc_call_order then (x::xs)::xss
        else [x]::a
    ) [] sorted_proc_main in
  let proc_scc0 = List.rev proc_scc in
  let proc_scc = Cast.update_mut_vars_bu iprog prog proc_scc0 in
  let () = x_tinfo_hp (add_str "SCC"
                         (pr_list (pr_list (Astsimp.pr_proc_call_order))))
      proc_scc no_pos in
  (* flag to determine if can skip phase inference step *)
  (*************************** INTERNAL ***************************)
  let verify_scc_helper prog verified_sccs scc =
    let skip_pre_phase = (!Globals.dis_phase_num || !Globals.dis_term_chk) in
    let () = Cast.cprog_obj # check_prog_warning x_loc prog in
    let () = print_infer_scc (x_loc^" Beginning") scc in
    let scc, ini_hpdefs = if !Globals.sa_part then
        Da.find_rel_args_groups_scc prog scc
      else (scc,[])
    in
    let has_infer_shape_pre_proc = x_add Iincr.is_infer_const_scc scc INF_SHAPE_PRE in
    let has_infer_shape_post_proc = x_add Iincr.is_infer_const_scc scc INF_SHAPE_POST in
    let has_infer_shape_proc = (x_add_1 Pi.is_infer_shape_scc scc) in
    let has_infer_pre_proc = Pi.is_infer_pre_scc scc in
    let () = x_dinfo_hp (add_str "has_infer_shape_proc" string_of_bool)
        has_infer_shape_proc no_pos in
    let () = x_dinfo_hp (add_str "has_infer_pre_proc" string_of_bool) has_infer_pre_proc no_pos in
    let () = if (not(has_infer_shape_proc) && has_infer_pre_proc)
      then Pi.add_pre_relation_scc prog scc in
    let has_infer_post_proc = Pi.is_infer_post_scc scc in
    let () = if (not(has_infer_shape_proc)) then x_add Pi.add_post_relation_scc prog scc in
    let () = print_infer_scc (x_loc^" After add_pre/post relation") scc in
    (* Only infer post *)
    let (scc,old_specs) =
      if (has_infer_shape_proc || has_infer_post_proc || has_infer_pre_proc)
      then List.split (Pi.filter_infer_pure_scc scc) (* Remove INF_SHAPE *)
      else (scc,[]) in
    let () = print_infer_scc (x_loc^" After Remove INF_SHAPE") scc in
    let () = y_tinfo_hp (add_str "old_specs" (pr_list_ln !CF.print_struc_formula)) old_specs in
    let () = List.iter (fun proc ->
        x_tinfo_hp
          (add_str "spec before phase inference for mutual-recursive groups"
             Cprinter.string_of_struc_formula)
          (proc.proc_stk_of_static_specs # top) no_pos) scc in
    let is_all_verified1, prog =
      let call_order = (List.hd scc).proc_call_order in
      (* perform phase inference for mutual-recursive groups captured by stk_scc_with_phases *)
      if not(skip_pre_phase) && (stk_scc_with_phases # mem call_order) then
        begin
          Debug.ninfo_pprint ">>>>>> Perform Phase Inference for a Mutual Recursive Group
  <<<<<<" no_pos;
          Debug.ninfo_hprint (add_str "SCC 1"  (pr_list (fun p -> p.proc_name))) scc no_pos;
          drop_phase_infer_checks();
          let b = proc_mutual_scc prog scc (fun prog proc ->
              (check_proc iprog prog proc cout_option [])) in
          restore_phase_infer_checks();
          (* the message here should be empty *)
          (* Term.term_check_output Term.term_res_stk; *)
          b, Term.phase_num_infer_whole_scc prog scc
        end
      else true,prog
    in
    let () = print_infer_scc (x_loc^" After Phase Numbering") scc in
    let mutual_grp = ref scc in
    x_tinfo_hp (add_str "MG"  (pr_list (fun p -> p.proc_name))) !mutual_grp no_pos;
    let _ = x_tinfo_pp "imm infer end20" no_pos in
    let tmp_fun prog proc1 =
      begin
        mutual_grp := List.filter (fun x -> x.proc_name != proc1.proc_name) !mutual_grp;
        Debug.ninfo_hprint (add_str "SCC"  (pr_list (fun p -> p.proc_name))) scc no_pos;
        Debug.ninfo_hprint (add_str "MG_new"  (pr_list (fun p -> p.proc_name))) !mutual_grp no_pos;
        let () = Debug.ninfo_hprint
            (add_str "before check_proc_wrapper"
               (Cprinter.string_of_struc_formula_for_spec_inst prog))
            proc1.Cast.proc_stk_of_static_specs # top  no_pos in
        let r =
          try
            check_proc_wrapper iprog prog proc1 cout_option !mutual_grp
          with _ as e -> raise e
        in
        r
      end
    in
    let is_all_verified2 =
      try
        proc_mutual_scc prog scc tmp_fun
      with _ as e ->
        raise e
    in
    let () = print_infer_scc (x_loc^" After check_proc") scc in

    let should_print_term_res = List.fold_left (fun acc proc ->
        if not acc then CF.has_known_pre_lexvar_struc (proc.Cast.proc_stk_of_static_specs # top)
        else acc) false scc in
    let () = if should_print_term_res then Term.term_check_output_scc () else () in

    let scc =
      if is_all_verified2 || not !Globals.sa_ex then scc
      else
        let rele_sccs = lookup_called_procs iprog prog scc verified_sccs in
        (*extn rele views and specs*)
        let error_traces = [] in
        let n_scc = ext_pure_check_procs iprog prog (scc::rele_sccs) error_traces in
        (*do analysis on the new domain*)
        (*if fail, give up; if succ, move fwd*)
        let () = print_infer_scc (x_loc^" After ext_pure_check") n_scc in
        n_scc
    in

    let () = Debug.ninfo_hprint (add_str "is_all_verified2" string_of_bool)
        is_all_verified2 no_pos in
    let () = if is_all_verified2 then
        let () = Infer.scc_rel_ass_stk # reverse in
        let () = List.iter (fun hp_def -> CF.rel_def_stk # push hp_def) ini_hpdefs in
        let ini_hp_defs = List.map (fun def ->
            let fs = List.fold_left (fun r (_, f_opt,_) -> match f_opt with
                | Some f -> r@[f]
                | None -> r
              ) [] def.CF.hprel_def_body in
            { CF.def_cat = def.CF.hprel_def_kind;
              CF.def_lhs = def.CF.hprel_def_hrel;
              CF.def_rhs = [(CF.disj_of_list fs no_pos, None)];
              CF.def_flow = def.CF.hprel_def_flow;
            }) ini_hpdefs in
        let () = proc_mutual_scc_shape_infer iprog prog
            (has_infer_pre_proc || has_infer_post_proc) ini_hp_defs scc in
        let () = print_infer_scc (x_loc^" After shape_infer..") scc in
        let () = Infer.rel_ass_stk # reset in
        let () = Infer.scc_rel_ass_stk # reset in
        let () = scc_proc_sel_hps := [] in
        let () = scc_proc_sel_post_hps := [] in
        ()
      else ()
    in

    (* Pure inference *)
    let () = if (has_infer_shape_proc && has_infer_pre_proc)
      then Pi.add_pre_relation_scc prog scc in
    let () = if (has_infer_shape_proc && has_infer_post_proc)
      then x_add Pi.add_post_relation_scc prog scc in
    let () =
      if (has_infer_shape_proc && (has_infer_pre_proc || has_infer_post_proc))
      then wrap_reverify_scc (x_add reverify_scc) prog scc true in
    let () = if (has_infer_pre_proc || has_infer_post_proc)
      then Pi.infer_pure prog scc in
    let () = x_tinfo_hp (add_str "stk_of_static_specs (pure)"
                           (pr_list (fun p ->
                                (Cprinter.string_of_struc_formula
                                   p.proc_stk_of_static_specs #top))))
        scc no_pos in
    let rem_pure_inf_prog_rel_decls = List.filter (fun rel_decl ->
        let r1 = Str.regexp "post_" in
        let r2 = Str.regexp "pre_" in
        not(Str.string_match r1 rel_decl.rel_name 0) && not(Str.string_match r2 rel_decl.rel_name 0)
      ) (prog.prog_rel_decls # get_stk) in
    (* QUICK FIX : why did we remove pre/post? *)
    let () = DD.ninfo_hprint (add_str "has_infer_post_proc" string_of_bool)
        has_infer_post_proc no_pos in
    (* Resume other infer. *)
    let () = print_infer_scc (x_loc^" After infer_pure..") scc in
    let scc = if (has_infer_shape_proc || has_infer_post_proc || has_infer_pre_proc) &&
                 not (has_infer_shape_pre_proc || has_infer_shape_post_proc)
      then Pi.resume_infer_obj_scc scc old_specs
      else scc in
    let () = x_dinfo_hp (add_str "stk_of_static_specs (resume)"
                           (pr_list (fun p ->
                                (Cprinter.string_of_struc_formula
                                   p.proc_stk_of_static_specs #top)))) scc
        no_pos in
    let () = print_infer_scc (x_loc^" After remove shape/pre/post..") scc in
    let () =
      let inf_templs = List.map (fun tdef -> tdef.Cast.templ_name) prog.Cast.prog_templ_decls in
      if inf_templs = [] then ()
      else if !Globals.templ_term_inf then
        Terminf.infer_rank_template_init prog inf_templs
      else Template.collect_and_solve_templ_assumes prog inf_templs
    in
    let () = print_infer_scc (x_loc^" After term infer result..") scc in
    let scc_ids = List.map (fun proc -> proc.Cast.proc_name) scc in
    let updated_scc = List.fold_left (fun r proc_id ->
        try
          let proc = Cast.look_up_proc_def_raw prog.Cast.new_proc_decls proc_id in
          r@[proc]
        with _ -> r
      ) [] scc_ids in
    let () = Term.term_res_stk # reset in
    let () = x_dinfo_hp (add_str "updated_scc" (pr_list (fun p ->
        (Cprinter.string_of_struc_formula (p.Cast.proc_stk_of_static_specs # top
                                          ))))) updated_scc no_pos in
    let n_verified_sccs = verified_sccs@[updated_scc] in
    (prog,n_verified_sccs)
  in

  let verify_scc_helper prog verified_sccs scc =
    Imminfer.wrapper_infer_imm_pre_post Infer.infer_rel_stk verify_scc_helper
      prog verified_sccs scc in

  let rec verify_scc_incr prog verified_sccs scc=
    let old_infer_err_flag = !Globals.sae in
    let () = Globals.sae := (Pi.is_infer_error_scc scc || infer_const_obj # is_error) in
    let r =
      try
        verify_scc_helper prog verified_sccs scc
      with e ->
        raise e
    in
    let () = Globals.sae := old_infer_err_flag in
    r
  in
  let rec process_cmd iprog cprog verified_sccs scc (icmd: Icmd.icmd) =
    match icmd with
    | Icmd.I_Norm {cmd_res_infs = infs} ->
      let is_inf_size = List.exists (fun it -> it = INF_SIZE) infs in
      let iscc,_ = List.split (Iincr.set_infer_const_scc infs scc) in
      let () = if List.exists (fun it -> it = INF_SHAPE_PRE) infs then
          let () = Iincr.add_prepost_shape_relation_scc cprog
              (Iincr.add_pre_shape_relation ~trans_size_to_extn:
                 (is_inf_size && not !Globals.old_pred_extn)) iscc in
          ()
        else if List.exists (fun it -> it = INF_SHAPE_POST) infs then
          let () = Iincr.add_prepost_shape_relation_scc cprog Iincr.add_post_shape_relation scc in
          ()
        else if is_inf_size then
          let niscc = Iincr.reset_infer_const_scc [INF_SIZE] iscc in
          ()
        else () in
      let res = verify_scc_incr cprog verified_sccs iscc in
      res
    | Icmd.I_Seq cmds
    | Icmd.I_Search cmds ->
      List.fold_left (fun (acc_cprog, _) (_, cmd) ->
          process_cmd iprog acc_cprog verified_sccs scc cmd)
        (cprog, verified_sccs) cmds
  in
  (********************************************************)
  let prog, _ = List.fold_left (fun (prog, verified_sccs) scc ->
      let prog, n_verified_sccs =
        let icmd = Icmd.compute_cmd prog scc in
        process_cmd iprog prog verified_sccs scc icmd
      in
      let no_verified_sccs = List.map (fun scc -> List.map (fun proc ->
          let spec = proc.proc_stk_of_static_specs # top in
          let () = x_tinfo_hp (add_str "spec: "
                                 Cprinter.string_of_struc_formula
                              ) spec no_pos in
          let new_spec = CF.remove_inf_cmd_spec spec in
          let () = x_tinfo_hp (add_str "new spec: "
                                 Cprinter.string_of_struc_formula
                              ) new_spec no_pos in
          let () = proc.proc_stk_of_static_specs # push_pr (x_loc ^ "after_cmd") new_spec in
          proc
        ) scc ) n_verified_sccs in
      prog, no_verified_sccs
    ) (prog,[]) proc_scc
  in
  ignore (List.map (fun proc -> check_proc_wrapper iprog prog proc cout_option []) (proc_prim));
  let () =  match cout_option with
    | Some cout -> close_out cout
    | _ -> ()
  in ()

let check_prog iprog (prog : prog_decl) =
  Debug.no_1 "check_prog" (fun _ -> "?") (fun _ -> "?") check_prog iprog prog

let check_prog_wrapper iprog prog =
  try
    check_prog iprog prog
  with _ as e -> raise e
