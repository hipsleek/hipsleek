#include "xdebug.cppo"
open VarGen
open Globals
open Others
open Stat_global

open Exc.GTable
open Cast
open Cformula
open Prooftracer
open Gen.Basic

open Immutable
open Perm
open Mcpure_D
open Mcpure
open Cvutil

let exist_invisible_cells f vars=
  let (hf,mf,_,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mf) in
  let dnodes = get_datas f in
  List.exists (fun dn ->
      let cl_ptrs = find_close [dn.h_formula_data_node] eqs in
      let () =  DD.ninfo_hprint (add_str "cl_ptrs" !CP.print_svl) cl_ptrs no_pos in
      not (List.exists (fun (CP.SpecVar (_,id,prm)) ->
          prm = Primed && List.exists (fun ((_,id1)) -> string_compare id id1) vars
      ) cl_ptrs)
  ) dnodes

let detect_mem_leak_partial_ctx_x prog proc ((pt, ctx,_) as br_ctx)=
  let rec detect_mem_leak_ctx c vars=
    match c with
      | Ctx es -> exist_invisible_cells es.es_formula vars,es
      | OCtx (c1, c2) ->
            let b1,e1 = detect_mem_leak_ctx c1 vars in
            if not b1 then
              detect_mem_leak_ctx c2 vars
            else b1,e1
  in
  let is_leak,es = detect_mem_leak_ctx ctx proc.Cast.proc_args in
  if is_leak then
    let err_msg = "mem leak" in
    let fe = mk_failure_must err_msg "mem leak" in
    let pos = no_pos in
    let ft = (Basic_Reason 
        ({fc_message =err_msg;
        fc_current_lhs = es;
        fc_orig_conseq = struc_formula_of_heap HTrue pos;
        fc_prior_steps = es.es_prior_steps;
        fc_current_conseq = CF.mkTrue (mkTrueFlow ()) pos;
        fc_failure_pts =[];}, fe, es.es_trace)) in
    ([(pt,ft)],[])
  else
    ([],[br_ctx])

let detect_mem_leak_partial_ctx prog proc br_ctx=
  let pr1 (_,ctx,_) = Cprinter.string_of_context_short ctx in
  let pr2 p = pr_id p.Cast.proc_name in
  let pr3 (_,ls2) = (pr_list pr1) ls2 in
  Debug.no_2 "detect_mem_leak_partial_ctx" pr2 pr1 pr3
      (fun _ _ -> detect_mem_leak_partial_ctx_x prog proc br_ctx)
      proc br_ctx

let detect_mem_leak_x prog proc ls_p_ctx=
  List.fold_left (fun r (brfs, br_ctx) ->
      let new_br_fail, new_br_ctx = List.fold_left ( fun (r1,r2) (br_ctx:branch_ctx) ->
          let n_fail, n_partial = detect_mem_leak_partial_ctx prog proc br_ctx in
          (r1@n_fail, r2@n_partial)
      ) ([],[]) br_ctx in
      r@[(brfs@new_br_fail, new_br_ctx)]
  ) [] ls_p_ctx


let detect_mem_leak prog proc ls_p_ctx=
  let pr1 = Cprinter.string_of_list_partial_context in
  let pr2 p = pr_id p.Cast.proc_name in
  Debug.no_2 "detect_mem_leak" pr2 pr1 pr1
      (fun _ _ -> detect_mem_leak_x prog proc ls_p_ctx)
      proc ls_p_ctx
