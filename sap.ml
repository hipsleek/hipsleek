(*handle pure extension to spec inference*)

open Globals
open Gen
open Others
open Label_only

module Err = Error
(* module AS = Astsimp *)
module CP = Cpure
(* module CF = Cformula *)
module MCP = Mcpure

let get_pure_ext cprog error_traces=
  let ext_kind = Cfutil.analyse_error () in
  (*lookup view_ext*)
   match ext_kind with
     | (* iSIZE_PROP *) 0 ->
           Debug.info_hprint (add_str "extend size property"  pr_id) "" no_pos;
           let view_exts = Cast.look_up_view_def_ext_size cprog.Cast.prog_view_decls 1 1 in
           if view_exts = [] then None
           else
             let extn_arg = fresh_any_name Globals.size_rel_arg in
             let ext_sv = CP.SpecVar (Int , extn_arg ,Unprimed) in
             Some (List.hd view_exts, ext_sv)
     | _ -> None


let collect_rele_views cprog specs=
  List.fold_left (fun vnames sf ->
      let hvs = Cformula.get_views_struc sf in
      vnames@(List.map (fun v -> v.Cformula.h_formula_view_name ) hvs)
  ) [] specs

let view_pure_ext iprog cprog view_ext extn_sv view=
  (*extend view with view_ext*)
  let extn_view_name = view_ext.Cast.view_name in
  let data_name = view.Cast.view_data_name in
  let extn_props = Cast.look_up_extn_info_rec_field cprog.Cast.prog_data_decls data_name in
  let extn_info = ((view.Cast.view_name,
  List.map CP.name_of_spec_var view.Cast.view_vars),(extn_view_name, extn_props , [extn_sv] )) in
  let iview = Iast.look_up_view_def_raw 48 iprog.Iast.prog_view_decls view.Cast.view_name in
  let der_view = {iview with Iast.view_name = fresh_any_name view.Cast.view_name} in
  let der_view1 = Derive.trans_view_one_derv iprog cprog.Cast.prog_view_decls der_view extn_info in
  (view, der_view1)

let extend_specs_views_pure_ext iprog cprog sccs error_traces =
  let specs = List.fold_left (fun r scc ->
      r@(List.map (fun proc -> proc.Cast.proc_static_specs) scc)
  ) [] sccs in
  (*collect rele views in spec of procs*)
  let rele_vnames0 =  collect_rele_views cprog specs in
  let rele_vnames1 = Gen.BList.remove_dups_eq (fun s1 s2 ->
      String.compare s1 s2 = 0) rele_vnames0 in
  (*from ext_type, lookup view_prop_extn*)
  let view_prop_extn_opt = get_pure_ext cprog error_traces in
  match view_prop_extn_opt with
    | Some (view_extn, extn_sv) ->
          let rele_views = List.fold_left (fun r vn ->
              try
                let v = List.find (fun v -> String.compare v.Cast.view_name vn = 0)
                  cprog.Cast.prog_view_decls in
                r@[v]
              with _ -> r
          ) [] rele_vnames1 in
          (*for each view, do extn*)
          (*subst new der views into the specs*)
          let extn_id = CP.name_of_spec_var extn_sv in
          let _ = List.map (view_pure_ext iprog cprog view_extn extn_id) rele_views in
          sccs
    | None -> sccs

