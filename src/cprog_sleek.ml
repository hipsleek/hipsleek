#include "xdebug.cppo"
(** pretty printing for formula and cast *)

open Format
open Globals
open VarGen
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Lexing
open Cast
open Cformula
open Mcpure_D
open Gen.Basic
(* open Label_only *)
open Printf

module LO = Label_only.LOne
module LO2 = Label_only.Lab2_List
module P = Cpure
module MP = Mcpure
module CVP = CvpermUtils

let cprog = Cast.cprog
(* ref {  *)
(*     Cast.prog_data_decls = []; *)
(*     Cast.prog_view_decls = []; *)
(*     Cast.prog_logical_vars = []; *)
(*     Cast.prog_rel_decls = (let s = new Gen.stack_pr "prog_rel_decls(CAST)" Cprinter.string_of_rel_decl (=) in s); *)
(*     Cast.prog_templ_decls = []; *)
(*     Cast.prog_ui_decls = []; *)
(*     Cast.prog_ut_decls = []; *)
(*     Cast.prog_hp_decls = []; *)
(*     Cast.prog_view_equiv = []; *)
(*     Cast.prog_axiom_decls = [];  *)
(*     (\* [4/10/2011] An Hoa *\) *)
(*     (\*Cast.old_proc_decls = [];*\) *)
(*     Cast.new_proc_decls = Hashtbl.create 1; (\* no need for proc *\) *)
(*     (\*Cast.prog_left_coercions = []; *)
(*       Cast.prog_right_coercions = [];*\) *)
(*     Cast. prog_barrier_decls = []} ;; *)

let () =
  let s = new Gen.stack_pr "prog_rel_decls(CAST)" Cprinter.string_of_rel_decl (=) in
  Cast.set_prog {!cprog with prog_rel_decls = s}

(* let get_sorted_view_decls () =                                   *)
(*   let vdefs = Cast.sort_view_list !cprog.Cast.prog_view_decls in *)
(*   !cprog.Cast.prog_view_decls <- vdefs;                          *)
(*   vdefs                                                          *)
let get_sorted_view_decls () = Cast.get_sorted_view_decls !cprog

let update_view_decl_cprog vdef =
  x_add (Cast.update_view_decl ~caller:x_loc) !cprog vdef

let update_view_decl_iprog_g update_scc upd_flag vdef =
  try
    let iprog = Iast.get_iprog () in
    let is_data c =
      try
        let _ = Iast.look_up_data_def_raw iprog.Iast.prog_data_decls c in
        true
      with _ -> false in
    if update_scc then
      begin
        let n = vdef.Iast.view_name in
        let view_decls = iprog.Iast.prog_view_decls in
        let lst = Iast.gen_name_pairs_struc view_decls n vdef.Iast.view_formula in
        let body = vdef.Iast.view_formula in
        let () = y_tinfo_hp (add_str "body" Iprinter.string_of_struc_formula) body in
        let () = y_tinfo_hp (add_str "view" Iprinter.string_of_view_decl) vdef in
        let fvars = Iformula.struc_hp_fv ~vartype:Vartypes.var_with_view_only body in
        let fvars = List.map fst fvars in
        let () = y_tinfo_hp (add_str "fvars(view)" (pr_list pr_id)) fvars in
        let fvars2 = List.filter (fun c -> not(is_data c)) fvars in
        let () = y_tinfo_hp (add_str "fvars2" (pr_list pr_id)) fvars2 in
        let () = y_tinfo_hp (add_str "view" pr_id) n in
        let () = y_tinfo_hp (add_str "lst(pairs)" (pr_list (pr_pair pr_id pr_id))) lst in
        HipUtil.view_scc_obj # replace x_loc n fvars2
      end;
    if upd_flag then x_add Iast.update_view_decl iprog vdef
  with _ -> failwith (x_loc^" iprog not found")

let update_view_decl_iprog_g update_scc upd_flag vdef =
  let pr = fun v -> v.Iast.view_name in
  let prr = fun () -> "" in
  Debug.no_1 "update_view_decl_iprog_g" pr prr
    (fun _ -> update_view_decl_iprog_g update_scc upd_flag vdef) vdef

let update_view_decl_iprog ?(update_scc=false) vdef =
  let upd_flag = true in
  x_add update_view_decl_iprog_g update_scc upd_flag vdef

let update_view_decl_iprog ?(update_scc=false) vdef =
  let pr = fun v -> v.Iast.view_name in
  let prr = fun () -> "" in
  Debug.no_1 "update_view_decl_iprog" pr prr
    (fun _ -> update_view_decl_iprog ~update_scc:update_scc vdef) vdef

let update_view_decl_scc_only vdef =
  let upd_flag = false in
  x_add update_view_decl_iprog_g true upd_flag (Rev_ast.rev_trans_view_decl vdef)

let update_view_decl_scc_only vdef =
  let pr = fun v -> v.Cast.view_name in
  let prr = fun () -> "" in
  Debug.no_1 "update_view_decl_scc_only" pr prr update_view_decl_scc_only vdef

let update_view_decl_both ?(update_scc=false) vdef =
  let () = update_view_decl_cprog vdef in
  let () = update_view_decl_iprog ~update_scc:update_scc
      (Rev_ast.rev_trans_view_decl vdef) in
  ()

let update_view_decl_both ?(update_scc=false) vdef =
  let pr = fun v -> v.Cast.view_name in
  let prr = fun () -> "" in
  Debug.no_1 "update_view_decl_both" pr prr
    (fun _ -> update_view_decl_both ~update_scc:update_scc vdef) vdef

