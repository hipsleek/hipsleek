#include "xdebug.cppo"

open VarGen
(*
26.11.2008
todo: disable the default logging for omega
*)

open Globals
open Others
open Stat_global
module DD = Debug
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Cast
open Cformula
open Prooftracer
open Gen.Basic

open Immutable
open Perm
open Mcpure_D
open Mcpure
(* open Stat_global *)
open Cvutil

(* module Inf = Infer *)
module CP = Cpure
module CF = Cformula
(* module PR = Cprinter *)
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher
module VP = Vperm
module CVP = CvpermUtils

(* module LO = Label_only.Lab_List *)
module LO = Label_only.LOne
(* module ME = Musterr *)

let return_out_of_inst estate lhs_b extended_hps =
  let n_estate = {estate with
      CF.es_infer_vars_hp_rel = estate.CF.es_infer_vars_hp_rel@extended_hps;
  } in
  (true, n_estate,lhs_b)

(* the inst is currently guided by RHS eqset *)
let gen_inst prog estate lhds lhvs sst =
  let rec aux sst acc_p =
    match sst with
    | [] -> true,acc_p
    | (sv1,sv2)::rest ->
      let sv2_orig = CP.subs_one estate.CF.es_rhs_eqset sv2 in
      if CP.eq_spec_var sv1 sv2_orig then
        aux (* gen_inst *) (* prog estate lhds lhvs *) rest acc_p
      else
        (*str-inf/ex16c3d(8). exists free vars -> fail*)
        let reach_vs = CF.look_up_reachable_ptr_args prog lhds lhvs [sv1] in
        if CP.mem_svl sv2_orig reach_vs then
          if !Globals.old_infer_complex_lhs then
            aux (* gen_inst *) (* prog estate lhds lhvs *) rest acc_p
          else false, acc_p
        else
          let p = CP.mkEqVar sv1 sv2 no_pos in
          let new_acc = CP.mkAnd acc_p p no_pos in
          aux (* gen_inst *) (* prog estate lhds lhvs *) rest new_acc
  in aux sst (CP.mkTrue no_pos)

(* type: 'a -> *)
(*   CF.entail_state -> *)
(*   CF.h_formula_data list -> *)
(*   CF.h_formula_view list -> *)
(*   (CP.spec_var * CP.spec_var) list -> CP.formula -> bool * CP.formula *)
let gen_inst prog estate lhds lhvs sst =
  let pr2 =(pr_list (pr_pair pr_sv pr_sv)) in
  let pr_sv = !CP.print_sv in
  let pr3 = pr_pair string_of_bool !CP.print_formula in
  Debug.no_2 "gen_inst" (add_str "es_rhs_eqset" pr2)  (add_str "sst" pr2) pr3 (fun _ _ -> gen_inst prog estate lhds lhvs sst) estate.es_rhs_eqset sst


let do_inst prog estate lhs_b largs rargs extended_hps=
  (* let lhs_vs = CF.fv (Base lhs_b) in *)
  (* (\* only vars not already in LHS can be instantiated *\) *)
  (* let rargs = List.filter (fun v -> not(CP.mem_svl v lhs_vs)) rargs in *)
  try
    if rargs = [] then return_out_of_inst estate lhs_b extended_hps
    else
      let p = (MCP.pure_of_mix lhs_b.CF.formula_base_pure) in
      let fvp = CP.fv p in
      let () = Debug.ninfo_hprint (add_str  "fvp" !CP.print_svl) fvp no_pos in
      let () = Debug.ninfo_hprint (add_str  "rargs" !CP.print_svl) rargs no_pos in
      if CP.intersect_svl rargs fvp != [] then
        let is_succ=
          let ps_eqs = List.filter (fun p -> (CP.is_eq_exp_ptrs rargs p)) (CP.list_of_conjs p) in
          if ps_eqs = [] then false else true
        in
        is_succ,estate, lhs_b
      else
        let sst = List.combine largs rargs in
        let lhds, lhvs, _ = CF.get_hp_rel_bformula lhs_b in
        let is_succ, p = gen_inst prog estate lhds lhvs sst  in
        if not is_succ then
          is_succ, estate, lhs_b
        else
          let () = Debug.ninfo_hprint (add_str  "p" !CP.print_formula) p no_pos in
          let mf = (MCP.mix_of_pure p) in
          let () = Debug.ninfo_hprint (add_str  "lhs_b" !CF.print_formula_base) lhs_b no_pos in
          (true,
           {estate with CF.es_formula = CF.mkAnd_pure estate.CF.es_formula mf no_pos;
                        CF.es_infer_vars_hp_rel = estate.CF.es_infer_vars_hp_rel@extended_hps;
           },
           CF.mkAnd_base_pure lhs_b mf no_pos)
  with _ -> return_out_of_inst estate lhs_b extended_hps

(* type: 'a -> *)
(*   CF.entail_state -> *)
(*   CF.formula_base -> *)
(*   CP.spec_var list -> *)
(*   CP.spec_var list -> *)
(*   CF.CP.spec_var list -> bool * CF.entail_state * CF.formula_base *)
let do_inst prog estate lhs_b largs rargs extended_hps =
  let pr_svl = !CP.print_svl in
  let pr_bf bf = !print_formula (Base bf) in
  let pr_r (b,_,eb) = (pr_pair string_of_bool pr_bf) (b,eb) in
  Debug.no_4 "do_inst" (add_str "lhs_b" pr_bf) (add_str "largs" pr_svl) (add_str "rargs" pr_svl) (add_str "hps" pr_svl) pr_r (fun _ _ _ _ -> do_inst prog estate lhs_b largs rargs extended_hps) lhs_b largs rargs extended_hps 

(*
type: (CF.entail_state ->
   CF.formula_base ->
   Context.action -> Cformula.list_context * Prooftracer.proof) ->
  Context.match_res ->
  'a ->
  'b ->
  CF.entail_state ->
  'c ->
  CF.formula_base ->
  Cformula.formula_base ->
  'd ->
  CP.spec_var list ->
  'e -> VarGen.loc -> Cformula.list_context * Prooftracer.proof
*)
let infer_unfold pm_aux action (* caller prog *) estate (* conseq *) lhs_b rhs_b (* a *) (rhs_h_matched_set: CP.spec_var list) (* is_folding *) pos
  : (Cformula.list_context * Prooftracer.proof) =
  let prog = () in
  let r = action in
  let lhs_node = r.Context.match_res_lhs_node in
  let rhs_node = r.Context.match_res_rhs_node in
  let rhs_rest = r.Context.match_res_rhs_rest in
  let rhs_inst = r.Context.match_res_compatible in
  let is_succ_inst, n_estate, n_lhs_b = match lhs_node,rhs_node with
    | HRel (lhp,leargs,_),HRel (rhp,reargs,_) ->
      if CP.mem_svl lhp estate.es_infer_vars_hp_rel (* && not (CP.mem_svl rhp estate.es_infer_vars_hp_rel) *) then
        match leargs, reargs with
        | er::rest1,_::rest2 -> begin
            let largs = (List.map CP.exp_to_sv rest1) in
            let rargs = (List.map CP.exp_to_sv rest2) in
            let () = Debug.binfo_hprint (add_str  "unfold:rhs_inst"  (pr_list (pr_pair !CP.print_sv !CP.print_sv))) rhs_inst no_pos in
            if (* List.length rargs < List.length largs &&  *)rhs_inst != [] then
              (* let r = (CP.exp_to_sv er) in *)
              (* let sst = Cfutil.exam_homo_arguments prog lhs_b rhs_b lhp rhp r rargs largs in *)
              let lhds, lhvs, _ = CF.get_hp_rel_bformula lhs_b in
              let is_succ, p = gen_inst prog estate lhds lhvs rhs_inst  in
              if not is_succ then
                true, estate, lhs_b
              else
                (* WN : why do we add rhp to es_infer_hp_rel? *)
                (* WN : this may make the behaviour less predictable.. *)
                let mf = (MCP.mix_of_pure p) in
                (true,
                 {estate with CF.es_formula = CF.mkAnd_pure estate.CF.es_formula mf no_pos;
                              CF.es_infer_vars_hp_rel = estate.CF.es_infer_vars_hp_rel@[rhp];
                 },
                 CF.mkAnd_base_pure lhs_b mf no_pos)
            else
              do_inst prog estate lhs_b largs rargs [rhp]
          end
        | _ -> return_out_of_inst estate lhs_b [rhp]
      else
        return_out_of_inst estate lhs_b []
    | HRel (lhp,leargs,_),ViewNode vn -> begin
        if CP.mem_svl lhp estate.es_infer_vars_hp_rel then
          match leargs with
          | _::rest1 ->
            let largs = (List.map CP.exp_to_sv rest1) in
            let rargs = vn.CF.h_formula_view_arguments in
            do_inst prog estate lhs_b largs rargs []
          | _ -> return_out_of_inst estate lhs_b []
        else
          return_out_of_inst estate lhs_b []
      end
    | _ -> return_out_of_inst estate lhs_b []
  in
  if not is_succ_inst then
    let err_msg = "infer_unfold" in
    let conseq = Some (Base rhs_b) in
    (Errctx.mkFailCtx_may ~conseq:conseq (x_loc^"Can not instantiate") err_msg estate pos,NoAlias)
  else
    let () = Debug.ninfo_hprint (add_str  "n_estate.es_formula" !CF.print_formula) n_estate.es_formula no_pos in
    pm_aux n_estate n_lhs_b (Context.M_infer_heap (1, lhs_node, rhs_node,rhs_rest))


let infer_fold prog pm_aux action (* caller prog *) estate (* conseq *) lhs_b rhs_b (* a *) (rhs_h_matched_set: CP.spec_var list) (* is_folding *) pos
  : (Cformula.list_context * Prooftracer.proof) =
  let r = action in
  (* let prog = () in *)
  let r = action in
  let lhs_node = r.Context.match_res_lhs_node  in
  let rhs_node = r.Context.match_res_rhs_node  in
  let rhs_rest = r.Context.match_res_rhs_rest  in
  let rhs_inst = r.Context.match_res_compatible in
  let () = Debug.binfo_hprint (add_str  "fold:rhs_inst"  (pr_list (pr_pair !CP.print_sv !CP.print_sv))) rhs_inst no_pos in
  let is_succ_inst, n_estate, n_lhs_b = match lhs_node,rhs_node with
    | HRel (lhp,leargs,_),HRel (rhp,reargs,_) -> begin
        if CP.mem_svl rhp estate.es_infer_vars_hp_rel then
          match leargs, reargs with
          | er::rest1,_::rest2 -> begin
              let largs = (List.map CP.exp_to_sv rest1) in
              let rargs = (List.map CP.exp_to_sv rest2) in
              if rhs_inst != [] then
                let lhds, lhvs, _ = CF.get_hp_rel_bformula lhs_b in
                let is_succ, p = gen_inst prog estate lhds lhvs rhs_inst in
                if not is_succ then
                  true, estate, lhs_b
                else
                  let mf = (MCP.mix_of_pure p) in
                  (true,
                   {estate with CF.es_formula = CF.mkAnd_pure estate.CF.es_formula mf no_pos;
                                CF.es_infer_vars_hp_rel = estate.CF.es_infer_vars_hp_rel;
                   },
                   CF.mkAnd_base_pure lhs_b mf no_pos)
              else
                do_inst prog estate lhs_b largs rargs []
            end
          | _ -> return_out_of_inst estate lhs_b []
        else
          return_out_of_inst estate lhs_b []
      end
    | _ -> return_out_of_inst estate lhs_b []
  in
  if not is_succ_inst then
    let err_msg = "infer_fold" in
    let conseq = Some (Base rhs_b) in
    (Errctx.mkFailCtx_may ~conseq:conseq (x_loc^"Can not inst") err_msg estate pos,NoAlias)
  else
    let () = Debug.ninfo_hprint (add_str  "n_estate.es_formula" !CF.print_formula) n_estate.es_formula no_pos in
    pm_aux n_estate n_lhs_b (Context.M_infer_heap (2, lhs_node, rhs_node,rhs_rest))


