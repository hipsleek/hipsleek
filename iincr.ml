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

(* INFERENCE CHECK: which kind of inference *)
let is_infer_const sf0 it =
  let rec recf sf= match sf with
    | CF.EList el -> List.exists (fun (lbl,sf) ->
          recf sf) el
    | CF.EInfer ei ->
          let inf_obj = ei.CF.formula_inf_obj in
          (inf_obj # get it)
  | _ -> false
  in
  recf sf0

let is_infer_const sf it =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_2 "is_infer_const" pr string_of_inf_const string_of_bool is_infer_const sf it

let is_infer_const_scc scc it=
  List.exists (fun proc -> is_infer_const (proc.Cast.proc_stk_of_static_specs # top) it) scc

let get_infer_const sf0 =
  let rec recf sf= match sf with
    | CF.EList el -> List.fold_left (fun acc (lbl,sf) ->
          acc@(recf sf)) [] el
    | CF.EInfer ei ->
          let inf_obj = ei.CF.formula_inf_obj in
          (inf_obj # get_lst)
  | _ -> []
  in
  recf sf0

let get_infer_const_scc scc =
  let infs = List.fold_left (fun acc proc -> acc@(get_infer_const proc.Cast.proc_stk_of_static_specs # top) ) [] scc in
  Gen.BList.remove_dups_eq (=) infs


let update_infer_const_struc_formula add_infs minus_infs sf0 =
  let rec recf sf= match sf with
    | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
          (lbl,recf sf)) el)
    | CF.EBase eb ->
          let cont = eb.CF.formula_struc_continuation in (
              match cont with
                | None -> sf
                | Some cont -> CF.EBase {eb with CF.formula_struc_continuation = Some (recf cont)} )
    | CF.EAssume ea -> sf
    | CF.EInfer ei ->
          let inf_obj = ei.CF.formula_inf_obj in
          let new_inf_obj = inf_obj # clone in
          let ()  = new_inf_obj # empty in
          let infs = inf_obj # get_lst in
          let infs1 = Gen.BList.difference_eq (=) infs minus_infs in
          let () =  new_inf_obj # set_list ( Gen.BList.remove_dups_eq (=) (infs1@add_infs)) in
          CF.EInfer {ei with
              CF.formula_inf_obj = new_inf_obj}
    | CF.ECase ec -> CF.ECase { ec with
          CF.formula_case_branches = List.map (fun (pf,sf) ->
              (pf,recf sf)
          ) ec.CF.formula_case_branches
      }
  in
  recf sf0

let update_infer_const_struc_formula add_infs minus_infs sf0 =
  let pr1 =  Cprinter.string_of_struc_formula in
  let pr2 = pr_list string_of_inf_const in
  Debug.no_3 "update_infer_const_struc_formula" pr2 pr2 pr1 pr1
      (fun _ _ _ -> update_infer_const_struc_formula add_infs minus_infs sf0)
      add_infs minus_infs sf0

let set_infer_const_struc_formula add_infs sf0 =
  let rec recf sf= match sf with
    | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
          (lbl,recf sf)) el)
    | CF.EBase eb ->
          let cont = eb.CF.formula_struc_continuation in (
              match cont with
                | None -> sf
                | Some cont -> CF.EBase {eb with CF.formula_struc_continuation = Some (recf cont)} )
    | CF.EAssume ea -> sf
    | CF.EInfer ei ->
          let inf_obj = ei.CF.formula_inf_obj in
          let new_inf_obj = inf_obj # clone in
          let ()  = new_inf_obj # empty in
          let () =  new_inf_obj # set_list ( Gen.BList.remove_dups_eq (=) (add_infs)) in
          CF.EInfer {ei with
              CF.formula_inf_obj = new_inf_obj}
    | CF.ECase ec -> CF.ECase { ec with
          CF.formula_case_branches = List.map (fun (pf,sf) ->
              (pf,recf sf)
          ) ec.CF.formula_case_branches
      }
  in
  recf sf0

let set_infer_const_struc_formula add_infs sf0 =
  let pr1 =  Cprinter.string_of_struc_formula in
  let pr2 = pr_list string_of_inf_const in
  Debug.no_2 "set_infer_const_struc_formula" pr2 pr1 pr1
      (fun _ _ -> set_infer_const_struc_formula add_infs sf0)
      add_infs sf0

let reset_infer_const_struc_formula removed_infs sf0 =
  let rec recf sf= match sf with
    | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
          (lbl,recf sf)) el)
    | CF.EBase eb ->
          let cont = eb.CF.formula_struc_continuation in (
              match cont with
                | None -> sf
                | Some cont -> CF.EBase {eb with CF.formula_struc_continuation = Some (recf cont)} )
    | CF.EAssume ea -> sf
    | CF.EInfer ei ->
          let inf_obj = ei.CF.formula_inf_obj in
          let new_inf_obj = inf_obj # clone in
          let () =  new_inf_obj # reset_list ( Gen.BList.remove_dups_eq (=) (removed_infs)) in
          CF.EInfer {ei with
              CF.formula_inf_obj = new_inf_obj}
    | CF.ECase ec -> CF.ECase { ec with
          CF.formula_case_branches = List.map (fun (pf,sf) ->
              (pf,recf sf)
          ) ec.CF.formula_case_branches
      }
  in
  recf sf0

let reset_infer_const_struc_formula removed_infs sf0 =
  let pr1 =  Cprinter.string_of_struc_formula in
  let pr2 = pr_list string_of_inf_const in
  Debug.no_2 "reset_infer_const_struc_formula" pr2 pr1 pr1
      (fun _ _ -> reset_infer_const_struc_formula removed_infs sf0)
      removed_infs sf0

let update_infer_const_proc add_infs minus_infs proc=
  let spec = proc.Cast.proc_stk_of_static_specs # top in
  let new_spec = update_infer_const_struc_formula add_infs minus_infs spec in
  let () = proc.Cast.proc_stk_of_static_specs # push_pr "pi:377" new_spec in
  let () = x_tinfo_hp (add_str "new_spec" Cprinter.string_of_struc_formula) new_spec no_pos in
  (proc,new_spec)                       (* spec or new_spec *)

let set_infer_const_proc add_infs proc=
  let spec = proc.Cast.proc_stk_of_static_specs # top in
  let new_spec = set_infer_const_struc_formula add_infs spec in
  let () = proc.Cast.proc_stk_of_static_specs # push_pr "pi:377" new_spec in
  let () = x_tinfo_hp (add_str "new_spec" Cprinter.string_of_struc_formula) new_spec no_pos in
  (proc,new_spec) 

let reset_infer_const_proc removed_infs proc=
  let spec = proc.Cast.proc_stk_of_static_specs # top in
  let new_spec = reset_infer_const_struc_formula removed_infs spec in
  let () = proc.Cast.proc_stk_of_static_specs # push_pr "pi:377" new_spec in
  let () = x_tinfo_hp (add_str "new_spec" Cprinter.string_of_struc_formula) new_spec no_pos in
  (proc,new_spec) 

let update_infer_const_scc add_infs minus_infs scc =
  List.map (update_infer_const_proc add_infs minus_infs ) scc

let set_infer_const_scc add_infs scc =
  List.map (set_infer_const_proc add_infs ) scc

let reset_infer_const_scc removed_infs scc =
  List.map (reset_infer_const_proc removed_infs ) scc


(**)
let rec htrue2emp hf= match hf with
  | CF.HTrue -> CF.HEmp
  | _ -> hf

let add_pre_shape_relation ?(trans_size_to_extn=false) prog proc spec=
  let pos = no_pos in
  let rec recf sf rel_name rel_vars=match sf with
    | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
          (lbl, recf sf rel_name rel_vars)) el)
    | CF.EBase eb ->
          let args = rel_vars in
          let pre_eargs = List.map (fun sv -> CP.Var (sv,pos)) args in
          let pre_simpl0 = (CF.formula_of_heap (CF.HRel (CP.SpecVar (HpT, rel_name, Unprimed), pre_eargs, pos)) pos) in
          let cur_pre1 = CF.formula_map htrue2emp eb.CF.formula_struc_base in
          let ipre_simpl = CF.mkStar cur_pre1 pre_simpl0 CF.Flow_combine pos in
          CF.EBase {eb with
              CF.formula_struc_base = ipre_simpl}
  | CF.EAssume ea -> sf
  | CF.EInfer ei ->
    let rel_name = Globals.hp_default_prefix_name ^ (string_of_int (Globals.fresh_int())) in
    let proc_args = List.map (fun (t,id) -> CP.mk_typed_spec_var t id) proc.Cast.proc_args in
    let rel_vars = List.filter CP.is_node_typ proc_args in
    if rel_vars = [] then sf else
      let rel_vars = CP.remove_dups_svl rel_vars in
      let hp_pre_decl = {
          Cast.hp_name = rel_name;
          Cast.hp_vars_inst = List.map (fun sv ->
              let in_info =  Globals.I in
              (sv, in_info)
            ) rel_vars;
          Cast.hp_part_vars = [];
          Cast.hp_root_pos = None;
          Cast.hp_is_pre = true;
          Cast.hp_view = None;
          Cast.hp_formula = CF.mkHTrue_nf pos;
          }
      in
      let () = x_tinfo_hp (add_str ("generate unknown predicate for Pre synthesis of " ^ proc.Cast.proc_name ^ ": ") pr_id)
        hp_pre_decl.Cast.hp_name no_pos in
      let pre_inf_sv = (CP.SpecVar (HpT, hp_pre_decl.Cast.hp_name, Unprimed)) in
      let () = if trans_size_to_extn then 
          ei.CF.formula_inf_obj # add_infer_extn_lst rel_name ["size"]
      in
      let () = DD.ninfo_hprint (add_str "rel_args" Cprinter.string_of_typed_spec_var_list) rel_vars no_pos in
      let new_cont = recf ei.CF.formula_inf_continuation rel_name rel_vars in
      let () = prog.Cast.prog_hp_decls <- prog.Cast.prog_hp_decls@[hp_pre_decl] in
      let () = proc.Cast.proc_sel_hps <- proc.Cast.proc_sel_hps@[pre_inf_sv] in
      CF.EInfer {ei with
          CF.formula_inf_vars = CP.remove_dups_svl (ei.CF.formula_inf_vars@[pre_inf_sv]);
          CF.formula_inf_continuation = new_cont}
  | CF.ECase ec -> CF.ECase { ec with
                              CF.formula_case_branches = List.map (fun (pf,sf) ->
                                  let rel_name = fresh_any_name rel_name in
                                  (pf, recf sf rel_name rel_vars)
                              ) ec.CF.formula_case_branches
    }
  in
  recf spec "" []

let add_pre_shape_relation ?(trans_size_to_extn=false) prog proc sf =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "add_pre_shape_relation" pr pr 
    (fun _ -> add_pre_shape_relation ~trans_size_to_extn:trans_size_to_extn prog proc sf) sf


let add_post_shape_relation_x prog proc spec=
   let pos = no_pos in
   let rec recf sf rel_name rel_vars=match sf with
    | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
          (lbl, recf sf rel_name rel_vars)) el)
    | CF.EBase eb -> begin
        match eb.CF.formula_struc_continuation with
          | None -> sf
          | Some cont -> CF.EBase {eb with CF.formula_struc_continuation = Some (recf cont rel_name rel_vars)}
      end
    | CF.EAssume ea ->
          let args = rel_vars in
          let post_eargs = List.map (fun sv -> CP.Var (sv,pos)) args in
          let post_simpl0 = (CF.formula_of_heap (CF.HRel (CP.SpecVar (HpT, rel_name, Unprimed), post_eargs, pos)) pos) in
          let cur_post = CF.formula_map htrue2emp  ea.CF.formula_assume_simpl in
          let new_post = CF.mkStar cur_post post_simpl0 CF.Flow_combine pos in
          let new_sf = CF.mkEBase new_post None pos in
          CF.EAssume {ea with
              CF.formula_assume_simpl = new_post;
              CF.formula_assume_struc = new_sf}
    | CF.EInfer ei ->
          let rel_name = Globals.hppost_default_prefix_name ^ (string_of_int (Globals.fresh_int())) in
          let proc_args = List.map (fun (t,id) -> CP.mk_typed_spec_var t id) proc.Cast.proc_args in
          let rel_vars = List.filter CP.is_node_typ proc_args in
          if rel_vars = [] &&  not (is_node_typ proc.Cast.proc_return) then sf else
            let rel_unprimed_vars = CP.remove_dups_svl rel_vars in
            let rel_primed_vars = List.map (fun  (CP.SpecVar (t,id,_))  ->
                CP.SpecVar (t,id,Primed))
              proc.Cast.proc_by_name_params in
            let rel_res_vars = if is_node_typ proc.Cast.proc_return then [ (CP.SpecVar (proc.Cast.proc_return, res_name, Unprimed))] else [] in
            let rel_vars = rel_unprimed_vars@rel_primed_vars@rel_res_vars in
            let hp_post_decl = {
                Cast.hp_name = rel_name;
                Cast.hp_vars_inst = List.map (fun sv ->
                    let in_info =  Globals.I in
                    (sv, in_info)
                ) rel_vars;
                Cast.hp_part_vars = [];
                Cast.hp_root_pos = None;
                Cast.hp_is_pre = true;
                Cast.hp_view = None;
                Cast.hp_formula = CF.mkHTrue_nf pos;
            }
            in
            let () = Debug.info_hprint (add_str ("generate unknown predicate for Post synthesis of " ^ proc.Cast.proc_name ^ ": ") pr_id)
              hp_post_decl.Cast.hp_name no_pos in
            let post_inf_sv = (CP.SpecVar (HpT, hp_post_decl.Cast.hp_name, Unprimed)) in
            let () = DD.ninfo_hprint (add_str "rel_args" Cprinter.string_of_typed_spec_var_list) rel_vars no_pos in
            let new_cont = recf ei.CF.formula_inf_continuation rel_name rel_vars in
            let () = prog.Cast.prog_hp_decls <- prog.Cast.prog_hp_decls@[hp_post_decl] in
            let () = proc.Cast.proc_sel_hps <- proc.Cast.proc_sel_hps@[post_inf_sv] in
            CF.EInfer {ei with
                CF.formula_inf_vars = CP.remove_dups_svl (ei.CF.formula_inf_vars@[post_inf_sv]);
                CF.formula_inf_continuation = new_cont}
    | CF.ECase ec -> CF.ECase { ec with
          CF.formula_case_branches = List.map (fun (pf,sf) ->
              let rel_name = fresh_any_name rel_name in
              (pf, recf sf rel_name rel_vars)
          ) ec.CF.formula_case_branches
      }
   in
   recf spec "" []

let add_post_shape_relation prog proc sf =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "add_post_shape_relation" pr pr (fun _ -> add_post_shape_relation_x prog proc sf) sf


let get_post_preds_x spec=
   let rec recf sf =match sf with
    | CF.EList el -> List.fold_left (fun acc (_,sf) ->
          acc@(recf sf)) [] el
    | CF.EBase eb -> begin
        match eb.CF.formula_struc_continuation with
          | None -> []
          | Some cont -> recf cont
      end
    | CF.EAssume ea ->
          (List.map fst (CF.get_HRels_f ea.CF.formula_assume_simpl))@(recf ea.CF.formula_assume_struc)
    | CF.EInfer ei ->
          CP.intersect_svl ei.CF.formula_inf_vars (recf ei.CF.formula_inf_continuation)
    | CF.ECase ec ->
          List.fold_left (fun acc (pf,sf) ->
              acc@(recf sf)
          ) [] ec.CF.formula_case_branches
   in
   recf spec

let get_post_preds sf =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "get_post_preds" pr (!CP.print_svl) (fun _ -> get_post_preds_x sf) sf


let get_post_preds_scc scc =
  List.fold_left (fun acc proc ->
      let spec = proc.Cast.proc_stk_of_static_specs # top in
      acc@(get_post_preds spec)
  ) [] scc

(*
  add_fnc:
    - add_pre_shape_relation
    - add_post_shape_relation
*)
let add_prepost_shape_relation_scc prog add_fnc scc =
  let () = List.iter (fun proc ->
      let spec = proc.Cast.proc_stk_of_static_specs # top in
      let new_spec = add_fnc prog proc spec in
      proc.Cast.proc_stk_of_static_specs # push_pr "ii:275" new_spec
    ) scc in
  let () = if List.length scc > 1 then
      let infer_vars = List.fold_left (fun acc proc ->
          let spec = proc.Cast.proc_stk_of_static_specs # top in
          acc@(CF.struc_infer_relation spec)
        ) [] scc in
      List.iter (fun proc ->
          let spec = proc.Cast.proc_stk_of_static_specs # top in
          let new_spec = Pi.modify_infer_vars spec infer_vars in
          proc.Cast.proc_stk_of_static_specs # push_pr "ii:285" new_spec
        ) scc
  in ()

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
    extract_inf_props prog [proc.Cast.proc_stk_of_static_specs # top] (* [proc.Cast.proc_static_specs] *)
  with _ -> []


(*
  for each view in scc: extd with ext_pred_name
  output: [old_vn, new_vn]
*)
let extend_views iprog prog rev_formula_fnc trans_view_fnc ext_pred_names proc=
  let vns = get_views_struc proc.Cast.proc_stk_of_static_specs # top in
  let vns1 = Gen.BList.remove_dups_eq string_eq (List.map (fun vn -> vn.h_formula_view_name) vns) in
  let () =  Debug.ninfo_hprint (add_str "vns1" (pr_list pr_id)) vns1 no_pos in
  let cl_vns1 = Cfutil.get_closed_view prog vns1 in
  let rev_cl_vns1 = List.rev cl_vns1 in
  let () =  Debug.ninfo_hprint (add_str "rev_cl_vns1" (pr_list pr_id)) rev_cl_vns1 no_pos in
  let vdcls = List.map (x_add Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls) ( rev_cl_vns1) in
  let pure_extn_views = List.map (Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls) ext_pred_names in
  (* (orig_view, der_view) list *)
  let old_view_scc = !Astsimp.view_scc in
  let () = Astsimp.view_scc := [] in
  let map_ext_views = x_add Derive.expose_pure_extn iprog prog rev_formula_fnc trans_view_fnc vdcls pure_extn_views in
  let () = Astsimp.view_scc := old_view_scc in
  let new_vns = List.map (fun (_,(vn,_)) -> vn)  map_ext_views in
  let new_vdclrs = List.map (Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls) new_vns in
  let todo_unk =  (List.map (fun vdef -> x_add Astsimp.compute_view_x_formula prog vdef !Globals.n_xpure) new_vdclrs) in
  let todo_unk = (List.map (fun vdef -> Astsimp.set_materialized_prop vdef) prog.Cast.prog_view_decls) in
  let prog = Astsimp.fill_base_case prog in
  let () = List.iter (fun vdef -> x_binfo_hp (add_str "new view" Cprinter.string_of_view_decl) vdef no_pos) new_vdclrs in
  map_ext_views

(* subst original view_formual by the new ones with quantifiers *)
let extend_inf iprog prog map_views proc=
  (* let vnames = get_views_struc proc.Cast.proc_stk_of_static_specs # top in *)
  let t_spec = proc.Cast.proc_stk_of_static_specs # top in
  let new_t_spec = Cfutil.subst_views_struc map_views (* struc_formula_trans_heap_node [] (formula_map (hview_subst_trans)) *) t_spec in
  let () =  Debug.ninfo_hprint (add_str "derived top spec" (Cprinter.string_of_struc_formula)) new_t_spec no_pos in
  (* let () = proc.Cast.proc_stk_of_static_specs # pop in *)
  let () = proc.Cast.proc_stk_of_static_specs # push new_t_spec in
  let n_static_spec = new_t_spec (* Cfutil.subst_views_struc map_views (\* struc_formula_trans_heap_node [] (formula_map (hview_subst_trans)) *\) proc.Cast.proc_static_specs *) in
  let () =  Debug.ninfo_hprint (add_str "derived static spec" (Cprinter.string_of_struc_formula)) n_static_spec no_pos in
  (* let proc0 = {proc with Cast.proc_static_specs = n_static_spec} in *)
  let proc0 = proc in
  let n_dyn_spec = Cfutil.subst_views_struc map_views (* struc_formula_trans_heap_node [] (formula_map (hview_subst_trans)) *) proc0.Cast.proc_dynamic_specs in
  let () =  Debug.ninfo_hprint (add_str "derived dynamic spec" (Cprinter.string_of_struc_formula)) n_dyn_spec no_pos in
  let proc1 = {proc0 with Cast.proc_dynamic_specs = n_dyn_spec} in
  proc1

let extend_pure_props_view iprog cprog rev_formula_fnc trans_view_fnc proc=
  (* let inf_props = proc_extract_inf_props cprog proc.Cast.proc_name in *)
  let inf_props = get_infer_const proc.Cast.proc_stk_of_static_specs # top in
  let props = List.fold_left (fun acc io ->
      begin
        match io with
          | INF_SIZE -> acc@["size"]
          | _ -> acc
      end
  ) [] inf_props in
   let () =  Debug.ninfo_hprint (add_str "props" (pr_list pr_id)) props no_pos in
  if props = [] then proc else
    let map_views = extend_views iprog cprog rev_formula_fnc trans_view_fnc props proc in
    let () =  Debug.ninfo_hprint (add_str "extend" pr_id) "3" no_pos in
    let new_proc = (extend_inf iprog cprog  map_views) proc in
    new_proc

let extend_pure_props_view iprog cprog rev_formula_fnc trans_view_fnc proc=
  let pr1 = Cprinter.string_of_struc_formula in
  let pr2 p= "top spec:" ^ (pr1 p.Cast.proc_stk_of_static_specs # top) ^ "\n" ^
    (* "static spec:"  ^ (pr1 p.Cast.proc_static_specs) ^ "\n" ^ *)
     "dynamic spec:"  ^ (pr1 p.Cast.proc_dynamic_specs) ^ "\n"
  in
  Debug.no_1 "extend_pure_props_view" pr2 pr2
      (fun _ -> extend_pure_props_view iprog cprog rev_formula_fnc trans_view_fnc proc) proc
