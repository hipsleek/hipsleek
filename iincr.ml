open Globals
open Wrapper
open Others
open Exc.GTable

open Cformula

module CP = Cpure


let extract_inf_props prog scc=
  [INF_SIZE]

(*
  for each view in scc: extd with ext_pred_name
  output: [old_vn, new_vn]
*)
let extend_views iprog prog ext_pred_name scc=
  let vns = List.fold_left (fun r proc ->
      r@(get_views_struc proc.Cast.proc_stk_of_static_specs # top)
  ) [] scc in
  let vns1 = Gen.BList.remove_dups_eq string_compare (List.map (fun vn -> vn.h_formula_view_name) vns) in
  let vdcls = List.map (Cast.look_up_view_def_raw 65 prog.Cast.prog_view_decls) vns1 in
  let pure_extn_view = Cast.look_up_view_def_raw 65 prog.Cast.prog_view_decls ext_pred_name in
  let n_views = Derive.expose_pure_extn  iprog prog vdcls [pure_extn_view] in
  []

let extend_inf iprog prog ext_pred_name proc=
  let vnames = get_views_struc proc.Cast.proc_stk_of_static_specs # top in
  proc
