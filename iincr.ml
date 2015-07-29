#include "xdebug.cppo"
open VarGen
open Gen
open Globals
open Wrapper
open Others
open Exc.GTable

open Cformula

module CP = Cpure
module CF = Cformula

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
let extend_inf iprog prog  map_views proc=
  (***************INTERNAL****************)
  let rec refresh_der_args args orig_args res=
    match args with
      | [] -> res
      | sv::rest -> if CP.mem_svl sv orig_args then
          refresh_der_args rest orig_args res@[sv]
        else
          refresh_der_args rest orig_args res@[CP.fresh_spec_var sv]
  in
  let rec lookup_map map vn v_args=
    match map with
      | [] -> raise Not_found
      | ((orig_vn,orig_v_args),(der_vn,der_v_args))::rest ->
            if string_compare vn orig_vn then
              let sst = List.combine orig_v_args v_args in
              (der_vn, CP.subst_var_list sst (refresh_der_args der_v_args orig_v_args []))
            else lookup_map rest vn v_args
  in
  let hview_subst_trans hn = match hn with
    | CF.ViewNode vn -> begin
        try
          let der_vn,der_args = lookup_map map_views vn.CF.h_formula_view_name vn.CF.h_formula_view_arguments in
          let () =  Debug.ninfo_hprint (add_str "der_args" (!CP.print_svl)) der_args no_pos in
          let args_orig,_ = List.fold_left (fun (r,i) sv -> (r@[(CP.SVArg sv, i)], i+1)) ([],0) der_args in
          let args_annot,_ = List.fold_left (fun (r,i) sv -> (r@[(CP.ImmAnn (CP.ConstAnn Mutable),i)], i+1) ) ([],0) der_args in
          CF.ViewNode {vn with h_formula_view_name = der_vn;
          CF.h_formula_view_arguments = der_args ;
          CF.h_formula_view_annot_arg = args_annot;
          CF.h_formula_view_args_orig = args_orig;}
        with Not_found -> hn
      end
    | _ -> hn
  in
   (*************END**INTERNAL****************)
  (* let vnames = get_views_struc proc.Cast.proc_stk_of_static_specs # top in *)
  let t_spec = proc.Cast.proc_stk_of_static_specs # top in
  let new_t_spec = struc_formula_trans_heap_node [] (formula_map (hview_subst_trans)) t_spec in
  let () =  Debug.info_hprint (add_str "derived top spec" (Cprinter.string_of_struc_formula)) new_t_spec no_pos in
  (* let () = proc.Cast.proc_stk_of_static_specs # pop in *)
  let () = proc.Cast.proc_stk_of_static_specs # push new_t_spec in
  let n_static_spec = struc_formula_trans_heap_node [] (formula_map (hview_subst_trans)) proc.Cast.proc_static_specs in
  let () =  Debug.ninfo_hprint (add_str "derived static spec" (Cprinter.string_of_struc_formula)) n_static_spec no_pos in
  let proc0 = {proc with Cast.proc_static_specs = n_static_spec} in
  let n_dyn_spec = struc_formula_trans_heap_node [] (formula_map (hview_subst_trans)) proc0.Cast.proc_dynamic_specs in
  let () =  Debug.ninfo_hprint (add_str "derived dynamic spec" (Cprinter.string_of_struc_formula)) n_dyn_spec no_pos in
  let proc1 = {proc0 with Cast.proc_dynamic_specs = n_dyn_spec} in
  proc1

let extend_pure_props_view_x iprog cprog rev_formula_fnc trans_view_fnc proc=
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
    let new_proc = (extend_inf iprog cprog  map_views) proc in
    new_proc

let extend_pure_props_view iprog cprog rev_formula_fnc trans_view_fnc proc=
  let pr1 = Cprinter.string_of_struc_formula in
  let pr2 p= "top spec:" ^ (pr1 p.Cast.proc_stk_of_static_specs # top) ^ "\n" ^
    "static spec:"  ^ (pr1 p.Cast.proc_static_specs) ^ "\n" ^
     "dynamic spec:"  ^ (pr1 p.Cast.proc_dynamic_specs) ^ "\n"
  in
  Debug.no_1 "extend_pure_props_view" pr2 pr2
      (fun _ -> extend_pure_props_view_x iprog cprog rev_formula_fnc trans_view_fnc proc) proc
