#include "xdebug.cppo"
open VarGen


(*
this module tranform an cast to pred
*)

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

module E = Env
module Err = Error
module C = Cast
module CF = Cformula
module CP = Cpure
module LO = Label_only.LOne



type assert_err=
  | VTD_Safe
  | VTD_Unsafe
  | VTD_Unk
  | VTD_NotApp

let string_of_assert_err res= match res with
    | VTD_Safe -> "safe"
    | VTD_Unsafe -> "unsafe"
    | VTD_Unk -> "unknown"
    | VTD_NotApp -> "not applicable"

let exists_assert_error_x prog e0=
  let rec helper e=
    (* let () = Debug.info_zprint (lazy  (" helper: " ^ (!print_exp e)  )) no_pos in *)
    match e with
      | C.SCall sc -> begin
            let mn = C.unmingle_name sc.C.exp_scall_method_name in
            let () = Debug.ninfo_hprint (add_str "SCall"
                                 (pr_id)
                              ) sc.C.exp_scall_method_name no_pos in
            if String.compare mn assert_err_fn = 0 then
              Some true
            else
              let mn_decl = C.look_up_proc_def_raw prog.C.new_proc_decls sc.exp_scall_method_name in
              let is_assert= mn_decl.C.proc_has_assert_err in
              Some is_assert
              end
      | _ -> None
  in
  helper e0

let exists_assert_error prog e0=
  let pr1 = !C.print_prog_exp in
  Debug.no_1 "exists_assert_error" pr1 (pr_opt string_of_bool)
    (fun _ -> exists_assert_error_x prog e0) e0


let exam_ass_error_proc prog proc=
  let exist_ass_err = match proc.C.proc_body with
    | Some e -> C.fold_exp e (exists_assert_error prog) (List.exists (fun b -> b)) false
    | None -> false
  in
  let () = proc.C.proc_has_assert_err <- exist_ass_err in
  exist_ass_err

let exam_ass_error_proc prog proc=
  let pr1 p = pr_id p.C.proc_name in
  Debug.no_1 "exam_ass_error_proc" pr1 string_of_bool
      (fun _ -> exam_ass_error_proc prog proc) proc

let exam_ass_error_scc iprog scc=
  (*func call error*)
  List.exists (exam_ass_error_proc iprog) scc


let symex_gen_view iprog prog proc body=
  let ctx0 = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled proc.C.proc_loc in
  let ctx1 = CF.set_flow_in_context_override
    { CF.formula_flow_interval = !norm_flow_int; CF.formula_flow_link = None} ctx0 in
  let label = (fresh_formula_label "") in
  let ctx1 = CF.add_path_id ctx1 (Some label,-1) (-1) in
  (* need to add initial esc_stack *)
  let init_esc = [((0,""),[])] in
  let lfe = [CF.mk_failesc_context ctx1 [] init_esc] in
  let old_symex_td = !symex_td in
  let () = symex_td := true in
  let res_ctx = x_add Typechecker.check_exp prog proc lfe body label in
  let () = symex_td := old_symex_td in
  let () = x_binfo_hp (add_str ("symex_gen_view:" ^ proc.C.proc_name) (Cprinter.string_of_list_failesc_context_short)) res_ctx no_pos in
  let br_ctxs = List.fold_left (fun acc (_,esc, brs) -> acc@(List.fold_left (fun eacc (_, ebrs) -> eacc@ebrs) [] esc)@brs ) [] res_ctx in
  let rec collect_es c = match c with
    | CF.Ctx es -> [CF.substitute_flow_in_f !norm_flow_int !ret_flow_int es.CF.es_formula]
    | CF.OCtx (c1,c2) -> (collect_es c1)@(collect_es c2)
  in
  let brs = List.fold_left (fun acc (_,ctx,_) -> acc@(collect_es ctx)) [] br_ctxs in
  let () = x_binfo_hp (add_str ("brs") (pr_list !CF.print_formula)) brs no_pos in
  CP.mkTrue proc.C.proc_loc


let symex_gen_view_from_proc iprog prog proc=
  (*
    - pred name
    - parameter list = method.para + option res + #e
    - parse body
  *)
  let pred_name = (C.unmingle_name proc.C.proc_name) ^ "_v" in
  let r_args = match proc.C.proc_return with
    | Void -> []
    | _ -> let r_arg =  res_name in
      [r_arg]
  in
  let e_arg = err_var in
  let proc_args = (List.map (fun (_,arg) -> arg) proc.C.proc_args) in
  let pred_args = proc_args @ r_args @ [e_arg] in
  let f_body = match proc.C.proc_body with
    | Some body -> symex_gen_view iprog prog proc body
    | None -> CP.mkTrue proc.C.proc_loc
  in
  true

let symex_gen_view_from_scc iprog prog scc=
  let vdecls = List.map (symex_gen_view_from_proc iprog prog) scc in
  vdecls

let verify_td_scc iprog prog scc=
  VTD_Unk

let verify_td_sccs iprog prog fast_return scc_procs=
  let combine_res ls_res=
    if List.exists (fun r -> r == VTD_Unsafe) ls_res then VTD_Unsafe
    else if List.for_all (fun r -> r == VTD_Safe) ls_res then VTD_Safe
    else VTD_Unk
  in
  let rec recf ls_scc res=
    match ls_scc with
      | [] -> res,combine_res res
      | scc::rest ->
            let vdcls = symex_gen_view_from_scc iprog prog scc in
            let r = verify_td_scc iprog prog scc in
            let n_res = res@[r] in
            if fast_return && r == VTD_Unsafe then
              (n_res,VTD_Unsafe)
            else recf rest n_res
  in
  recf scc_procs []

(* O: safe, 1: unsafe, 2: unknown, 3: not applicaple (all method donot have assert error) *)
let verify_as_sat iprog prog=
  (* Sort the proc_decls by proc_call_order *)
  let l_proc = Cast.list_of_procs prog in
  let proc_prim, proc_main = List.partition Cast.is_primitive_proc l_proc in
  let sorted_proc_main = Cast.sort_proc_decls proc_main in
  let () = Debug.info_hprint (add_str "sorted_proc_main"
                                 (pr_list Astsimp.pr_proc_call_order)
                              ) sorted_proc_main no_pos in
  (* this computes a list of scc mutual-recursive methods for processing *)
  let proc_scc = List.fold_left (fun a x -> match a with
      | [] -> [[x]]
      | xs::xss ->
        let i=(List.hd xs).C.proc_call_order in
        if i==x.C.proc_call_order then (x::xs)::xss
        else [x]::a
    ) [] sorted_proc_main in
  let proc_scc0 = List.rev proc_scc in
  (* look up assert error location *)
  if List.for_all (exam_ass_error_scc prog)  proc_scc0 then
    (* transform *)
    let _,res = verify_td_sccs iprog prog true proc_scc0 in
    (* check sat *)
    VTD_NotApp
  else
    VTD_NotApp
