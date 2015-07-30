#include "xdebug.cppo"
open VarGen
open Globals
open Wrapper
open Others
open Exc.GTable

open Cformula

module CP = Cpure


let get_infer_type its0 inf0=
  (* let rec look_up ifts inf rem= *)
  (*   match ifts with *)
  (*     | [] -> raise Not_found *)
  (*     | it::rest -> if it == inf then it,rem@rest else *)
  (*         look_up rest inf (rem@[it]) *)
  (* in *)
  (* look_up its0 inf0 [] *)
  List.find (fun inf1 -> inf0==inf1) its0

let extract_inf_props prog scc=
  let rec get_from_one_spec spec=
    match (spec) with
    | (   EList el) -> List.fold_left (fun acc (_,sf) ->
          acc@(get_from_one_spec sf)
      ) [] el
    |    EInfer ei -> let inf_obj = ei.formula_inf_obj # clone in
      if inf_obj # is_size then
        [INF_SIZE]
      else []
    | _ -> []
  in
  List.fold_left (fun acc spec -> acc@(get_from_one_spec spec)) [] scc

let proc_extract_inf_props prog proc_name=
  try
    let proc = Cast.look_up_proc_def_raw prog.Cast.new_proc_decls proc_name in
    extract_inf_props prog [proc.Cast.proc_static_specs]
  with _ -> []

(*
  for each view in scc: extd with ext_pred_name
  output: [old_vn, new_vn]
*)
let extend_views iprog prog rev_formula_fnc trans_view_fnc ext_pred_names proc=
  let vns = get_views_struc proc.Cast.proc_stk_of_static_specs # top in
  let vns1 = Gen.BList.remove_dups_eq string_compare (List.map (fun vn -> vn.h_formula_view_name) vns) in
  let vdcls = List.map (x_add Cast.look_up_view_def_raw 65 prog.Cast.prog_view_decls) vns1 in
  let pure_extn_views = List.map (Cast.look_up_view_def_raw 65 prog.Cast.prog_view_decls) ext_pred_names in
  (* (orig_view, der_view) list *)
  let map_ext_views = Derive.expose_pure_extn iprog prog rev_formula_fnc trans_view_fnc vdcls pure_extn_views in
  map_ext_views

(* subst original view_formual by the new ones with quantifiers *)
let extend_inf iprog prog ext_pred_name proc=
  let vnames = get_views_struc proc.Cast.proc_stk_of_static_specs # top in
  proc

let extend_pure_props_view iprog cprog rev_formula_fnc trans_view_fnc proc=
  let inf_props = proc_extract_inf_props cprog proc.Cast.proc_name in
  let props = List.fold_left (fun acc io ->
      begin
        match io with
          | INF_SIZE -> acc@["size"]
          | _ -> acc
      end
  ) [] inf_props in
  if props = [] then proc else
    let map_views = extend_views iprog cprog rev_formula_fnc trans_view_fnc props proc in
    let new_proc = (extend_inf iprog cprog props) proc in
    new_proc
