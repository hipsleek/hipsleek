(*
  the wrapper of sleek implementation
*)

open Globals
open Wrapper
open Others
open Sleekcommons
open Gen.Basic
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Perm
open Label_only

module H = Hashtbl
module I = Iast
module Inf = Infer
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure
module LP = Lemproving
module AS = Astsimp
module DD = Debug
module XF = Xmlfront
module NF = Nativefront
module CEQ = Checkeq
module TI = Typeinfer
module MCP = Mcpure
module SY_CEQ = Syn_checkeq


let generate_lemma = ref (fun (iprog: I.prog_decl) n t (ihps: ident list) iante iconseq -> [],[])

let sleek_entail_check_x isvl (cprog: C.prog_decl) proof_traces ante conseq=
  let pr = Cprinter.string_of_struc_formula in
  let conseq = Solver.prune_pred_struc cprog true conseq in
  let _ = DD.tinfo_hprint (add_str "conseq(after prune)" pr) conseq no_pos in 
  (* let _ = DD.info_pprint "Andreea : false introduced by add_param_ann_constraints_struc" no_pos in *)
  (* let _ = DD.info_pprint "=============================================================" no_pos in *)
  let conseq = AS.add_param_ann_constraints_struc conseq in
  let _ = DD.tinfo_hprint (add_str "conseq(after add param)" pr) conseq no_pos in 
  (* let conseq = AS.add_param_ann_constraints_struc conseq in  *)
  let _ = Debug.devel_zprint (lazy ("\nrun_entail_check 2:"
                        ^"\n ### ivars = "^(pr_list !CP.print_sv isvl)
                        ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                        ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq)
                        ^"\n\n")) no_pos in
  let es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  (* let es = {es0 with CF.es_proof_traces = proof_traces} in *)
  let lem = Lem_store.all_lemma # get_left_coercion in
  let ante = Solver.normalize_formula_w_coers 11 cprog es ante lem (* cprog.C.prog_left_coercions *) in
  let _ = if (!Globals.print_core || !Globals.print_core_all) then print_endline ("INPUT: \n ### ante = " ^ (Cprinter.string_of_formula ante) ^"\n ### conseq = " ^ (Cprinter.string_of_struc_formula conseq)) else () in
  let _ = Debug.devel_zprint (lazy ("\nrun_entail_check 3: after normalization"
                        ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                        ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq)
                        ^"\n\n")) no_pos in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let ctx0 = Solver.elim_exists_ctx ctx in
  let ctx = CF.add_proof_traces_ctx ctx0 proof_traces in
  (* List of vars appearing in original formula *)
  let orig_vars = CF.fv ante @ CF.struc_fv conseq in
  (* (\* List of vars needed for abduction process *\) *)
  (* let vars = List.map (fun v -> TI.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) ivars in *)
  (* Init context with infer_vars and orig_vars *)
  let (vrel,iv) = List.partition (fun v -> is_RelT (CP.type_of_spec_var v)(*  ||  *)
              (* CP.type_of_spec_var v == FuncT *)) isvl in
  let (v_hp_rel,iv) = List.partition (fun v -> CP.type_of_spec_var v == HpT(*  ||  *)
              (* CP.type_of_spec_var v == FuncT *)) iv in
  (* let _ = print_endline ("WN: vars rel"^(Cprinter.string_of_spec_var_list vrel)) in *)
  (* let _ = print_endline ("WN: vars hp rel"^(Cprinter.string_of_spec_var_list v_hp_rel)) in *)
  (* let _ = print_endline ("WN: vars inf"^(Cprinter.string_of_spec_var_list iv)) in *)
  let ctx = Inf.init_vars ctx iv vrel v_hp_rel orig_vars in
  (* let _ = print_string ((pr_list_ln Cprinter.string_of_view_decl) !cprog.Cast.prog_view_decls)  in *)
  let _ = if !Globals.print_core || !Globals.print_core_all
    then print_string ("\nrun_infer:\n"^(Cprinter.string_of_formula ante)
        ^" "^(pr_list !CP.print_sv isvl)
      ^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") 
    else () 
  in
  let ctx = 
    if !Globals.delay_proving_sat then ctx
    else CF.transform_context (Solver.elim_unsat_es 9 cprog (ref 1)) ctx in
  let _ = if (CF.isAnyFalseCtx ctx) then
        print_endline ("[Warning] False ctx")
  in
  (* let _ = print_endline ("ctx: "^(Cprinter.string_of_context ctx)) in *)
  let rs1, _ = 
    if not !Globals.disable_failure_explaining then
      Solver.heap_entail_struc_init_bug_inv cprog false false 
        (CF.SuccCtx[ctx]) conseq no_pos None
    else
      Solver.heap_entail_struc_init cprog false false 
        (CF.SuccCtx[ctx]) conseq no_pos None
  in
  (* let _ = print_endline ("WN# 1:"^(Cprinter.string_of_list_context rs1)) in *)
  let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in
  (* let _ = print_endline ("WN# 2:"^(Cprinter.string_of_list_context rs)) in *)
  (* flush stdout; *)
  let res =
    if not !Globals.disable_failure_explaining then ((not (CF.isFailCtx_gen rs)))
    else ((not (CF.isFailCtx rs))) in
  (* residues := Some (rs, res); *)
  (res, rs,v_hp_rel)

(*
proof_traces: (formula*formula) list===> for cyclic proofs
*)
let sleek_entail_check isvl (cprog: C.prog_decl) proof_traces ante conseq=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = Cprinter.string_of_struc_formula in
  let pr3 = pr_triple string_of_bool Cprinter.string_of_list_context !CP.print_svl in
  let pr4 = pr_list_ln (pr_pair pr1 pr1) in
  Debug.no_4 "sleek_entail_check" !CP.print_svl pr1 pr2 pr4 pr3
      (fun _ _ _ _ -> sleek_entail_check_x isvl cprog proof_traces ante conseq)
      isvl ante conseq proof_traces

let sleek_sat_check isvl cprog f=
  true

(*
- guiding_svl is used to guide the syntatic checking.
- guiding_svl is common variables between f1 and f2
*)
let check_equiv iprog cprog guiding_svl proof_traces need_lemma f1 f2=
  let gen_lemma (r_left, r_right) (ante,conseq)=
    let iante = Astsimp.rev_trans_formula ante in
    let iconseq = Astsimp.rev_trans_formula conseq in
    let l2r,r2l = !generate_lemma iprog "temp" I.Equiv [] iante iconseq in
    (r_left@l2r, r_right@r2l)
  in
  if not (!Globals.syntatic_mode) then
    let old_l, old_r = if need_lemma then
      let n_l, n_r = List.fold_left gen_lemma ([],[]) proof_traces in
      let old_l = Lem_store.all_lemma # get_left_coercion  in
      let old_r = Lem_store.all_lemma # get_right_coercion  in
      let _ = Lem_store.all_lemma # add_left_coercion n_l in
      let _ = Lem_store.all_lemma # add_right_coercion n_r in
      (old_l, old_r)
    else ([],[])
    in
    let r =
      let b1, _, _ = (sleek_entail_check [] cprog proof_traces f1 (CF.struc_formula_of_formula f2 no_pos)) in
      if b1 then
        let b2,_,_ = (sleek_entail_check [] cprog (List.map (fun (f1,f2) -> (f2,f1)) proof_traces)
            f2 (CF.struc_formula_of_formula f1 no_pos)) in
        b2
      else
        b1
    in
    let _ = if need_lemma then
      let _ = Lem_store.all_lemma # set_left_coercion old_l in
      let _ = Lem_store.all_lemma # set_right_coercion old_r in
      ()
    else ()
    in
    r
  else
    SY_CEQ.check_relaxeq_formula guiding_svl f1 f2

let rec check_equiv_list_x iprog prog guiding_svl proof_traces need_lemma fs1 fs2=
  let rec look_up_f f fs fs1=
    match fs with
      | [] -> (false, fs1)
      | f1::fss -> if (check_equiv iprog prog guiding_svl proof_traces need_lemma f f1) then
            (true,fs1@fss)
          else look_up_f f fss (fs1@[f1])
  in
  if List.length fs1 = List.length fs2 then
    match fs1 with
      | [] -> true
      | f1::fss1 ->
          begin
              let r,fss2 = look_up_f f1 fs2 [] in
              if r then
                check_equiv_list iprog prog guiding_svl proof_traces need_lemma fss1 fss2
              else false
          end
  else false

and check_equiv_list iprog prog guiding_svl proof_traces need_lemma fs1 fs2: bool=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "check_equiv_list" pr1 pr1 string_of_bool
      (fun _ _ -> check_equiv_list_x iprog prog guiding_svl proof_traces need_lemma fs1 fs2) fs1 fs2


(* let _ = Sautility.check_equiv := check_equiv *)
(* let _ = Sautility.check_equiv_list := check_equiv_list *)

let validate_x ls_ex_es0 ls_act_es0=
  (*********INTERNAL********)
  let validate_one (guide_vars, es_f, ls_ass) es=
    (*compare es_formula*)
    let b1 = SY_CEQ.check_relaxeq_formula guide_vars es_f es.CF.es_formula in
    (*compare constrs*)
    if b1 then
      let b2= if ls_ass = [] then true else
        true
      in
      b2
    else
      b1
  in
  let rec find_2_validate_helper ls_act_es ex_es done_act_es=
    match ls_act_es with
      | [] -> (false,[])
      | act_es::rest ->
            let b= validate_one ex_es act_es in
            if b then (true,done_act_es@rest) else
              find_2_validate_helper rest ex_es (done_act_es@[act_es])
  in
  let rec find_2_validate ls_ex_es ls_act_es=
    match ls_ex_es with
      | [] -> true
      | ex_es::exp_rest ->
            let b, act_rest = find_2_validate_helper ls_act_es ex_es [] in
            if not b then
              (*diff*)
              false
            else
              find_2_validate exp_rest act_rest
  in
  (*********END INTERNAL********)
  let b = find_2_validate ls_ex_es0 ls_act_es0 in
  (b, None, [])

let validate ls_ex_es ls_act_es=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr2a = (pr_list_ln (pr_pair pr2 pr2)) in
  let pr3 = pr_list_ln (pr_triple pr1 pr2 pr2a) in
  let pr4 = pr_list_ln Cprinter.string_of_entail_state_short in
  let pr5 f_opt = match f_opt with
    | None -> "None"
    | Some f -> pr2 f
  in
  Debug.no_2 "SC.validate" pr3 pr4 (pr_triple string_of_bool pr5 pr2a)
      (fun _ _ -> validate_x ls_ex_es ls_act_es)
      ls_ex_es ls_act_es
