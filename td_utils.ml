open Globals
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

module C = Cast
module CF = Cformula
module CP = Cpure

let symex_td_method_call prog proc ctx ecall=
  (* ecall = assert_error *)
  let mn = C.unmingle_name ecall.C.exp_scall_method_name in
  if String.compare mn assert_err_fn = 0 then
    CF.transform_list_failesc_context 
    (idf,idf,(fun es -> CF.Ctx{es with CF.es_formula = CF.substitute_flow_in_f !error_flow_int !norm_flow_int es.CF.es_formula;})) ctx

    else
      (*otherwise*)
      (* ecall contain assert_error *)
      ctx

let symex_td_method_call prog proc ctx ecall=
  let pr1 = Cprinter.string_of_list_failesc_context_short in
  let pr2 ecall = !C.print_prog_exp (C.SCall ecall) in
  Debug.no_2 "symex_td_method_call" pr1 pr2 pr1
      (fun _ _ -> symex_td_method_call prog proc ctx ecall)
      ctx ecall
