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
  Debug.no_3 "sleek_entail_check" pr1 pr2 pr4 pr3
      (fun _ _ _ -> sleek_entail_check_x isvl cprog proof_traces ante conseq)
      ante conseq proof_traces

let sleek_sat_check isvl cprog f=
  true
