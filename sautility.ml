(*this file contains all unitilise for shape analysis.
it is used mainly by infer.infer_collect_hp and sa.infer_hp
*)

open Globals
open Gen

module DD = Debug
module CF=Cformula
module CP=Cpure
module MCP=Mcpure
module C = Cast


let close_def defs (v1,v2)=
  if (CP.is_null_const v1) || (CP.is_null_const v2) then defs
  else if CP.mem_svl v1 defs then (CP.remove_dups_svl defs@[v2])
  else if CP.mem_svl v2 defs then (CP.remove_dups_svl defs@[v1])
  else (defs)

let rec get_data_view_hrel_vars_bformula bf=
  get_data_view_hrel_vars_h_formula bf.CF.formula_base_heap

and get_data_view_hrel_vars_h_formula hf=
  let rec helper h=
 match h with
    | CF.Star { CF.h_formula_star_h1 = hf1;
                CF.h_formula_star_h2 = hf2}
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;}
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;} ->
        let ls1 = helper hf1 in
        let ls2 = helper hf2 in
        (ls1@ls2)
    | CF.DataNode hd -> [hd.CF.h_formula_data_node]
    | CF.ViewNode hv -> [hv.CF.h_formula_view_node]
    | CF.HRel (hp,_,_) -> [hp]
    | CF.Hole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp -> []
  in
  helper hf

(*==============*)
(*for drop non-selective subformulas*)
(*check a data node does not belong to a set of data node name*)
let check_nbelongsto_dnode dn dn_names=
      List.for_all (fun dn_name -> not(CP.eq_spec_var dn.CF.h_formula_data_node dn_name)) dn_names

(*check a view node does not belong to a set of view node name*)
let check_nbelongsto_vnode vn vn_names=
      List.for_all (fun vn_name -> not(CP.eq_spec_var vn.CF.h_formula_view_node vn_name)) vn_names

let check_neq_hrelnode id ls=
      not (CP.mem_svl id ls)

(*check a data node belongs to a list of data node names*)
let select_dnode dn1 dn_names=
  List.exists (CP.eq_spec_var dn1.CF.h_formula_data_node) dn_names

(*check a view node belongs to a list of view node names*)
let select_vnode vn1 vn_names=
    (*return subst of args and add in lhs*)
  List.exists (CP.eq_spec_var vn1.CF.h_formula_view_node) vn_names

let select_hrel =  CP.mem_svl

let rec loop_up_ptr_args_data_node_x prog hd=
  (*data nodes*)
  let data_def =  C.look_up_data_def no_pos prog.C.prog_data_decls hd.CF.h_formula_data_name in
  (*get prototype of a node declaration*)
  let args = List.map (fun (t,_) -> t) data_def.C.data_fields in
  (*combine with actual areg*)
  let targs = List.combine args hd.CF.h_formula_data_arguments in
  (*get pointer*)
  snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs))

and loop_up_ptr_args_data_node prog hd=
  let pr1 = fun dn -> dn.CF.h_formula_data_name in
Debug.no_1 " loop_up_ptr_args_data_node" pr1 !CP.print_svl
    (fun _ ->  loop_up_ptr_args_data_node_x  prog hd) hd

(* let loop_up_ptr_args_view_node prog hv= *)
(*   (\*view node*\) *)
(*   let view_def =  Cast.look_up_view_def no_pos prog.Cast.prog_view_decls hv.CF.h_formula_view_name in *)
(*   (\*get prototype of a node declaration*\) *)
(*   let args = List.map (fun (t,_) -> t) view_def.Cast.view_fields in *)
(*   (\*combine with actual areg*\) *)
(*   let targs = List.combine args hd.CF.h_formula_view_arguments in *)
(*   (\*get pointer*\) *)
(*   snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs)) *)

and loop_up_ptr_args_one_node prog hd_nodes hv_nodes node_name=
  let rec look_up_data_node ls=
    match ls with
      | [] -> []
      | dn::ds -> if CP.eq_spec_var node_name dn.CF.h_formula_data_node then
            loop_up_ptr_args_data_node prog dn
          else look_up_data_node ds
  in
  (* let rec look_up_view_node ls= *)
  (*   match ls with *)
  (*     | [] -> [] *)
  (*     | dn::ds -> if CP.eq_spec_var node_name dn.CF.h_formula_view_node then *)
  (*           loop_up_ptr_args_view_node prog hd *)
  (*         else look_up_view_node ds *)
  (* in *)
  let ptrs = look_up_data_node hd_nodes in
  (* if ptrs = [] then look_up_view_node hv_nodes *)
  (* else *) ptrs

let loop_up_closed_ptr_args prog hd_nodes hv_nodes node_names=
  let rec helper old_ptrs inc_ptrs=
    let new_ptrs = List.concat
      (List.map (loop_up_ptr_args_one_node prog hd_nodes hv_nodes) inc_ptrs) in
    let diff_ptrs = List.filter (fun id -> not (CP.mem_svl id old_ptrs)) new_ptrs in
    let diff_ptrs = Gen.BList.remove_dups_eq CP.eq_spec_var diff_ptrs in
    if diff_ptrs = [] then old_ptrs
    else (helper (old_ptrs@diff_ptrs) diff_ptrs)
  in
  helper node_names node_names

let keep_data_view_hrel_nodes prog f hd_nodes hv_nodes keep_rootvars keep_hrels=
  let keep_ptrs = loop_up_closed_ptr_args prog hd_nodes hv_nodes keep_rootvars in
  CF.drop_data_view_hrel_nodes f check_nbelongsto_dnode check_nbelongsto_vnode
    check_neq_hrelnode keep_ptrs keep_ptrs keep_hrels

let keep_data_view_hrel_nodes_two_f prog f1 f2 hd_nodes hv_nodes keep_rootvars keep_hrels=
  let keep_ptrs = loop_up_closed_ptr_args prog hd_nodes hv_nodes keep_rootvars in
  let nf1 = CF.drop_data_view_hrel_nodes f2 check_nbelongsto_dnode check_nbelongsto_vnode check_neq_hrelnode keep_ptrs keep_ptrs keep_hrels in
  let nf2 = CF.drop_data_view_hrel_nodes f2 check_nbelongsto_dnode check_nbelongsto_vnode check_neq_hrelnode keep_ptrs keep_ptrs keep_hrels in
  (nf1,nf2)

let keep_data_view_hrel_nodes_two_fbs prog f1 f2 hd_nodes hv_nodes eqs keep_rootvars lrootvars keep_hrels=
  let _ = Debug.ninfo_pprint ("keep_vars root: " ^ (!CP.print_svl keep_rootvars)) no_pos in
  let keep_closed_rootvars = CP.remove_dups_svl (List.fold_left close_def keep_rootvars eqs) in
  let _ = Debug.ninfo_pprint ("keep_vars 1: " ^ (!CP.print_svl keep_closed_rootvars)) no_pos in
  let keep_vars = loop_up_closed_ptr_args prog hd_nodes hv_nodes keep_closed_rootvars in
  let lhs_keep_closed_rootvars = CP.remove_dups_svl (List.fold_left close_def lrootvars eqs) in
  let _ = Debug.ninfo_pprint ("keep_vars 1: " ^ (!CP.print_svl keep_closed_rootvars)) no_pos in
  let lkeep_vars = loop_up_closed_ptr_args prog hd_nodes hv_nodes lhs_keep_closed_rootvars in
  (*may be alisas between lhs and rhs*)
  let _ = Debug.ninfo_pprint ("keep_vars: " ^ (!CP.print_svl keep_vars)) no_pos in
  let _ = Debug.ninfo_pprint ("lhs keep_vars: " ^ (!CP.print_svl lkeep_vars)) no_pos in
  let nf1 = CF.drop_data_view_hrel_nodes_fb f1 check_nbelongsto_dnode check_nbelongsto_vnode check_neq_hrelnode keep_vars keep_vars keep_hrels (keep_vars@lkeep_vars) in
  let nf2 = CF.drop_data_view_hrel_nodes_fb f2 check_nbelongsto_dnode check_nbelongsto_vnode check_neq_hrelnode keep_vars keep_vars keep_hrels keep_vars in
  let _ = Debug.ninfo_pprint ("nf1: " ^ (Cprinter.string_of_formula_base nf1)) no_pos in
  let _ = Debug.ninfo_pprint ("nf2: " ^ (Cprinter.string_of_formula_base nf2)) no_pos in
  (nf1,nf2)

let rec drop_data_view_hrel_nodes_from_root prog f hd_nodes hv_nodes eqs drop_rootvars=
   match f with
    | CF.Base fb ->
       CF.Base { fb with CF.formula_base_heap = drop_data_view_hrel_nodes_hf_from_root
               prog fb.CF.formula_base_heap
               hd_nodes hv_nodes eqs drop_rootvars}
    | _ -> report_error no_pos "cformula.drop_data_view_hrel_nodes"


and drop_data_view_hrel_nodes_hf_from_root prog hf hd_nodes hv_nodes eqs drop_rootvars=
  let _ = Debug.ninfo_pprint ("drop_vars root: " ^ (!CP.print_svl drop_rootvars)) no_pos in
  (* let drop_closed_rootvars = CP.remove_dups_svl (List.fold_left close_def drop_rootvars eqs) in *)
  let _ = Debug.ninfo_pprint ("close drop_rootvars: " ^ (!CP.print_svl drop_rootvars)) no_pos in
  let drop_vars = loop_up_closed_ptr_args prog hd_nodes hv_nodes drop_rootvars in
  (*may be alisas between lhs and rhs*)
  let _ = Debug.ninfo_pprint ("drop_vars: " ^ (!CP.print_svl drop_vars)) no_pos in
  let nhf = CF.drop_data_view_hrel_nodes_hf hf select_dnode select_vnode select_hrel drop_vars drop_vars drop_vars in
  let _ = Debug.ninfo_pprint ("nhf: " ^ (Cprinter.string_of_h_formula nhf)) no_pos in
  nhf

(*END for drop non-selective subformulas*)
