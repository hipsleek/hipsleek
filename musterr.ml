(*
 1. this file provides interfaces and implementations for
   - must/may errors
2. IMPORTANT (AVOID REDUNDANT): before implement new method, please go through
  interfaces and UNUSED module to check whether your need is there.
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
open Stat_global

module Inf = Infer
module CP = Cpure
module CF = Cformula
module PR = Cprinter
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher

(* module LO = Label_only.Lab_List *)
module LO = Label_only.LOne



(* type steps = string list *)

(* (\*implementation of must/may is moved to musterr.ml*\) *)
 
(* (\*      MAY *)

(*  VALID       MUST *)

(*         BOT *)
(* *\) *)

(* type fail_context = { *)
(*     fc_prior_steps : steps; (\* prior steps in reverse order *\) *)
(*     fc_message : string;          (\* error message *\) *)
(*     (\* fc_current_lhs : entail_state;     (\\* LHS context with success points *\\) *\) *)
(*     (\* fc_orig_conseq : struc_formula;     (\\* RHS conseq at the point of failure *\\) *\) *)
(*     fc_failure_pts : Globals.formula_label list;     (\* failure points in conseq *\) *)
(*     (\* fc_current_conseq : formula; *\) *)
(* } *)

(* and fail_type = *)
(*   | Basic_Reason of (fail_context * fail_explaining) *)
(*   | Trivial_Reason of fail_explaining *)
(*   | Or_Reason of (fail_type * fail_type) *)
(*   | And_Reason of (fail_type * fail_type) *)
(*   | Union_Reason of (fail_type * fail_type) *)
(*   | ContinuationErr of fail_context *)
(*   | Or_Continuation of (fail_type * fail_type) *)

(* and failure_kind = *)
(*   | Failure_May of string *)
(*   | Failure_Must of string *)
(*   | Failure_Bot of string *)
(*   | Failure_Valid *)

(* and fail_explaining = { *)
(*     fe_kind: failure_kind; (\*may/must*\) *)
(*     fe_name: string; *)
(*     fe_locs: Globals.loc list; *)
(*     (\* fe_explain: string;  *\) *)
(*     (\* string explaining must failure *\) *)
(*     (\*  fe_sugg = struc_formula *\) *)
(* } *)

(*maximising must bug with RAND (error information)*)
let check_maymust_failure_x (ante:CP.formula) (cons:CP.formula): (CF.failure_kind*((CP.formula*CP.formula) list * (CP.formula*CP.formula) list * (CP.formula*CP.formula) list))=
  if not !disable_failure_explaining then
    let r = ref (-9999) in
    let is_sat f = TP.is_sat_sub_no 9 f r in
    let find_all_failures a c = CP.find_all_failures is_sat a c in
    let find_all_failures a c =
      let pr1 = Cprinter.string_of_pure_formula in
      let pr2 = pr_list (pr_pair pr1 pr1) in
      let pr3 = pr_triple pr2 pr2 pr2 in
      Debug.no_2 "find_all_failures" pr1 pr1 pr3 find_all_failures a c in
    let filter_redundant a c = CP.simplify_filter_ante TP.simplify_always a c in
    (* Check MAY/MUST: if being invalid and (exists (ante & conseq)) = true then that's MAY failure,
       otherwise MUST failure *)
    let ante_filter = filter_redundant ante cons in
    let (r1, r2, r3) = find_all_failures ante_filter cons in
    if List.length (r1@r2) = 0 then
      begin
        (CF.mk_failure_may_raw "", (r1, r2, r3))
      end
    else
      begin
        (*compute lub of must bug and current fc_flow*)
        (CF.mk_failure_must_raw "", (r1, r2, r3))
      end
  else
    (CF.mk_failure_may_raw "", ([], [], [(ante, cons)]))

(*maximising must bug with RAND (error information)*)
let check_maymust_failure (ante:CP.formula) (cons:CP.formula): (CF.failure_kind*((CP.formula*CP.formula) list * (CP.formula*CP.formula) list * (CP.formula*CP.formula) list))=
  let pr1 = Cprinter.string_of_pure_formula in
  let pr3 = pr_list (pr_pair pr1 pr1) in
  let pr2 = pr_pair (Cprinter.string_of_failure_kind) (pr_triple pr3 pr3 pr3) in
  Debug.no_2 "check_maymust_failure" pr1 pr1 pr2 (fun _ _ -> check_maymust_failure_x ante cons) ante cons

(*maximising must bug with AND (error information)*)
(* to return fail_type with AND_reason *)
let build_and_failures_x (failure_code:string) (failure_name:string) ((contra_list, must_list, may_list)
    :((CP.formula*CP.formula) list * (CP.formula*CP.formula) list * (CP.formula*CP.formula) list)) (fail_ctx_template: fail_context): list_context=
  if not !disable_failure_explaining then
    let build_and_one_kind_failures (failure_string:string) (fk: CF.failure_kind) (failure_list:(CP.formula*CP.formula) list):CF.fail_type option=
      (*build must/may msg*)
      let build_failure_msg (ante, cons) =
        let ll = (CP.list_pos_of_formula ante []) @ (CP.list_pos_of_formula cons []) in
        (*let _ = print_endline (Cprinter.string_of_list_loc ll) in*)
        let lli = CF.get_lines ll in
        (*possible to eliminate unnecessary intermediate that are defined by equality.*)
        (*not sure it is better*)
        let ante = CP.elim_equi_ante ante cons in
        ((Cprinter.string_of_pure_formula ante) ^ " |- "^
            (Cprinter.string_of_pure_formula cons) ^ ". LOCS:[" ^ (Cprinter.string_of_list_int lli) ^ "]", ll) in
      match failure_list with
        | [] -> None
        | _ ->
              let strs,locs= List.split (List.map build_failure_msg failure_list) in
              (*get line number only*)
              (* let rec get_line_number ll rs= *)
              (*   match ll with *)
              (*     | [] -> rs *)
              (*     | l::ls -> get_line_number ls (rs @ [l.start_pos.Lexing.pos_lnum]) *)
              (* in *)

              (*shoudl use ll in future*)
              (* let ll = Gen.Basic.remove_dups (get_line_number (List.concat locs) []) in*)
              let msg =
                match strs with
                  | [] -> ""
                  | [s] -> s ^ " ("  ^ failure_string ^ ")"
                  | _ -> (* "(failure_code="^failure_code ^ ") AndR[" ^ *)
                        "AndR[" ^ (String.concat "; " strs) ^ " ("  ^ failure_string ^ ").]"
              in
              let fe = match fk with
                |  Failure_May _ -> mk_failure_may msg failure_name
                | Failure_Must _ -> (mk_failure_must msg failure_name)
                | _ -> {fe_kind = fk; fe_name = failure_name ;fe_locs=[]}
              in
              Some (Basic_Reason ({fail_ctx_template with fc_message = msg }, fe))
    in
    let contra_fail_type = build_and_one_kind_failures "RHS: contradiction" (Failure_Must "") contra_list in
    let must_fail_type = build_and_one_kind_failures "must-bug" (Failure_Must "") must_list in
    let may_fail_type = build_and_one_kind_failures "may-bug" (Failure_May "") may_list in
    (*
      let pr oft =
      match oft with
      | Some ft -> Cprinter.string_of_fail_type ft
      | None -> "None"
      in
      let _ = print_endline ("locle contrad:" ^ (pr contra_fail_type)) in
      let _ = print_endline ("locle must:" ^ (pr must_fail_type)) in
      let _ = print_endline ("locle may:" ^ (pr may_fail_type)) in
    *)
    let oft = List.fold_left CF.mkAnd_Reason contra_fail_type [must_fail_type; may_fail_type] in
    match oft with
      | Some ft -> FailCtx ft
      | None -> (*report_error no_pos "Solver.build_and_failures: should be a failure here"*)
            let msg =  "use different strategies in proof searching (slicing)" in
            let fe =  mk_failure_may msg failure_name in
            FailCtx (Basic_Reason ({fail_ctx_template with fc_message = msg }, fe))
  else
    let msg = "failed in entailing pure formula(s) in conseq" in
    CF.mkFailCtx_in (Basic_Reason ({fail_ctx_template with fc_message = msg }, mk_failure_may msg failure_name))


let build_and_failures i (failure_code:string) (failure_name:string) ((contra_list, must_list, may_list)
    :((CP.formula*CP.formula) list * (CP.formula*CP.formula) list * (CP.formula*CP.formula) list)) 
      (fail_ctx_template: fail_context): list_context=
  let pr1 = Cprinter.string_of_pure_formula in
  let pr3 = pr_list (pr_pair pr1 pr1) in
  let pr4 = pr_triple pr3 pr3 pr3 in
  let pr2 = (fun _ -> "OUT") in
  Debug.no_1_num i "build_and_failures" pr4 pr2 
      (fun triple_list -> build_and_failures_x failure_code failure_name triple_list fail_ctx_template)
      (contra_list, must_list, may_list)

