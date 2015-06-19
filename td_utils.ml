#include "xdebug.cppo"

open Globals
open VarGen
open Gen.Basic
open Wrapper
open Others
open Exc.GTable
open Printf
open Gen.Basic
open Gen.BList
open Mcpure_D
open Mcpure
open Label_only
open Typeinfer

module CA = Cast
module CF = Cformula
module CP = Cpure

let dump_self = CP.SpecVar (null_type, "Anon_"^(fresh_trailer()), Unprimed)

let symex_td_method_call prog proc ctx ecall=
  let move_br2err (fbrs, es, brs)=
    let err_brs = List.map (fun (pt,c, oft) -> (pt, CF.transform_context (fun es -> CF.Ctx {es with CF.es_formula = CF.substitute_flow_in_f !error_flow_int !norm_flow_int es.CF.es_formula;}) c, oft)) brs in
    (fbrs, es@[((-1,"-1"), err_brs)], [])
  in
  let clone_br2err is_clone_err safe_fl err_fl (fbrs, es, brs)=
    let safe_brs = List.map (fun (pt,c, oft) -> (pt, CF.transform_context (fun es -> CF.Ctx {es with CF.es_formula = CF.mkAnd_pure es.CF.es_formula safe_fl no_pos;}) c, oft)) brs in
    let es_errs = if is_clone_err then
      let err_brs = List.map (fun (pt,c, oft) -> (pt, CF.transform_context (fun es ->
        let cmb_f = CF.mkAnd_pure es.CF.es_formula err_fl no_pos in
        CF.Ctx {es with CF.es_formula = CF.substitute_flow_in_f !error_flow_int !norm_flow_int cmb_f;}
      ) c, oft)) brs in
      [((-1,"-1"), err_brs)]
    else [] in
    (fbrs, es@es_errs, safe_brs)
  in
  (****************************************)
  (****************************************)
  (* ecall = assert_error *)
  let mn = CA.unmingle_name ecall.CA.exp_scall_method_name in
  if String.compare mn assert_err_fn = 0 then
    List.map move_br2err ctx
  else
    (*otherwise*)
    (* generate a pred wrt. method call *)
    let mdecl = CA.look_up_proc_def_raw prog.Cast.new_proc_decls ecall.CA.exp_scall_method_name in
    let view_args =
      let sst= List.combine ecall.exp_scall_arguments mdecl.CA.proc_args in
      List.map (fun (act, (t, form)) -> CP.SpecVar (t, act, Primed)) sst
    in
    let res = CP.SpecVar (mdecl.CA.proc_return, res_name^(fresh_trailer()), Unprimed) in
    let e = CP.SpecVar (Int, err_var^(fresh_trailer()), Unprimed) in
    let view_args_extra = view_args@[res; e] in
    let hv = CF.mkViewNode dump_self (method2pred mn) view_args_extra ecall.CA.exp_scall_pos in
    let hv_f = CF.formula_of_heap hv ecall.CA.exp_scall_pos in
    let ctx1 = CF.transform_list_failesc_context 
    (idf,idf,(fun es -> Ctx{es with es_formula = CF.mkStar es.es_formula hv_f CF.Flow_combine ecall.CA.exp_scall_pos;})) ctx in
    (* ecall contain assert_error *)
    let is_clone = mdecl.CA.proc_has_assert_err in
    let e_exp = CP.Var (e, no_pos) in
    let safe_fl = MCP.mix_of_pure (CP.mkEqExp e_exp (CP.IConst (0, no_pos)) no_pos) in
    let err_fl = (CP.mkEqExp e_exp (CP.IConst (1, no_pos)) no_pos) in
    let err_fl = MCP.mix_of_pure (err_fl) in
    List.map (clone_br2err is_clone safe_fl err_fl) ctx1

let symex_td_method_call prog proc ctx ecall=
  let pr1 = Cprinter.string_of_list_failesc_context_short in
  let pr2 ecall = !CA.print_prog_exp (C.SCall ecall) in
  Debug.no_2 "symex_td_method_call" pr1 pr2 pr1
      (fun _ _ -> symex_td_method_call prog proc ctx ecall)
      ctx ecall
