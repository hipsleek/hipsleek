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
module CEQ = Checkeq


let close_def defs (v1,v2)=
  if (CP.is_null_const v1) || (CP.is_null_const v2) then defs
  else if CP.mem_svl v1 defs then (CP.remove_dups_svl defs@[v2])
  else if CP.mem_svl v2 defs then (CP.remove_dups_svl defs@[v1])
  else (defs)

let is_empty_f f=
   match f with
    | CF.Base fb ->
        (CF.is_empty_heap fb.CF.formula_base_heap) &&
            (CP.isConstTrue (MCP.pure_of_mix fb.CF.formula_base_pure))
    | _ -> report_error no_pos "SAU.is_empty_f: not handle yet"

let is_empty_wop opf=
  match opf with
    | None -> false
    | Some f ->  is_empty_f f

let is_unk_f f=
   match f with
    | CF.Base fb ->
        (CF.is_unkown_heap fb.CF.formula_base_heap) &&
            (CP.isConstTrue (MCP.pure_of_mix fb.CF.formula_base_pure))
    | _ -> report_error no_pos "SAU.is_empty_f: not handle yet"

(*for drop hp args*)
let rec retrieve_args_from_locs args locs index res=
  match args with
    | [] -> res
    | a::ss -> if List.mem index locs then
          retrieve_args_from_locs ss locs (index+1) (res@[a])
        else retrieve_args_from_locs ss locs (index+1) res

let rec eq_spec_var_order_list l1 l2=
  match l1,l2 with
    |[],[] -> true
    | v1::ls1,v2::ls2 ->
        if CP.eq_spec_var v1 v2 then
          eq_spec_var_order_list ls1 ls2
        else false
    | _ -> false

let check_hp_arg_eq (hp1, args1) (hp2, args2)=
  ((CP.eq_spec_var hp1 hp2) && (eq_spec_var_order_list args1 args2))

let mkHRel hp args pos=
  let eargs = List.map (fun x -> CP.mkVar x pos) args in
   ( CF.HRel (hp, eargs, pos))

let rec get_hdnodes (f: CF.formula)=
  match f with
    | CF.Base fb ->
        get_hdnodes_hf fb.CF.formula_base_heap
    | _ -> report_error no_pos "SAU.is_empty_f: not handle yet"

and get_hdnodes_hf (hf: CF.h_formula) = match hf with
  | CF.DataNode hd -> [hd]
  | CF.Conj {CF.h_formula_conj_h1 = h1; CF.h_formula_conj_h2 = h2} 
  | CF.Star {CF.h_formula_star_h1 = h1; CF.h_formula_star_h2 = h2} 
  | CF.Phase {CF.h_formula_phase_rd = h1; CF.h_formula_phase_rw = h2} 
      -> (get_hdnodes_hf h1)@(get_hdnodes_hf h2)
  | _ -> []

let check_simp_hp_eq (hp1, _) (hp2, _)=
   (CP.eq_spec_var hp1 hp2)

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

let rec drop_get_hrel f=
  match f with
    | CF.Base fb ->
        let new_hf, hrels = drop_get_hrel_h_formula fb.CF.formula_base_heap in
        (CF.Base {fb with CF.formula_base_heap= new_hf}, hrels)
    | _ -> report_error no_pos "SAU.drop_get_hrel: not handle yet"

(* and drop_get_hrel_bformula bf= *)
(*   drop_get_hrel_h_formula bf.CF.formula_base_heap *)

and drop_get_hrel_h_formula hf=
  let rec helper hf0=
    match hf0 with
      | CF.Star {CF.h_formula_star_h1 = hf1;
                 CF.h_formula_star_h2 = hf2;
                 CF.h_formula_star_pos = pos} ->
          let n_hf1,hrels1 = helper hf1 in
          let n_hf2,hrels2 = helper hf2 in
          (match n_hf1,n_hf2 with
            | (CF.HEmp,CF.HEmp) -> (CF.HEmp,hrels1@hrels2)
            | (CF.HEmp,_) -> (n_hf2,hrels1@hrels2)
            | (_,CF.HEmp) -> (n_hf1,hrels1@hrels2)
            | _ -> (CF.Star {CF.h_formula_star_h1 = n_hf1;
			                CF.h_formula_star_h2 = n_hf2;
			                CF.h_formula_star_pos = pos},
                    hrels1@hrels2)
          )
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
		          CF.h_formula_conj_h2 = hf2;
		          CF.h_formula_conj_pos = pos} ->
          let n_hf1,hrels1 = helper hf1 in
          let n_hf2,hrels2 = helper hf2 in
          (CF.Conj { CF.h_formula_conj_h1 = n_hf1;
		            CF.h_formula_conj_h2 = n_hf2;
		            CF.h_formula_conj_pos = pos},
           hrels1@hrels2)
      | CF.Phase { CF.h_formula_phase_rd = hf1;
		           CF.h_formula_phase_rw = hf2;
		           CF.h_formula_phase_pos = pos} ->
          let n_hf1,hrels1 = helper hf1 in
          let n_hf2,hrels2 = helper hf2 in
          (CF.Phase { CF.h_formula_phase_rd = n_hf1;
		             CF.h_formula_phase_rw = n_hf2;
		             CF.h_formula_phase_pos = pos},
          hrels1@hrels2)
      | CF.DataNode hd -> (hf0,[])
      | CF.ViewNode hv -> (hf0,[])
      | CF.HRel (sv, eargs, _) -> (CF.HEmp,
                                   [(sv,List.concat (List.map CP.afv eargs))])
      | CF.Hole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp -> (hf0,[])
  in
  helper hf

let get_ptrs hf0=
  let rec helper hf=
    match hf with
      | CF.Star {CF.h_formula_star_h1 = hf1;
                 CF.h_formula_star_h2 = hf2;}
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
		          CF.h_formula_conj_h2 = hf2;}
      | CF.Phase { CF.h_formula_phase_rd = hf1;
		           CF.h_formula_phase_rw = hf2;} ->
          (helper hf1)@(helper hf2)
      | CF.DataNode hd ->([hd.CF.h_formula_data_node]@
                                 (List.filter (fun (CP.SpecVar (t,_,_)) -> is_pointer t) hd.CF.h_formula_data_arguments))
      | CF.ViewNode hv -> ([hv.CF.h_formula_view_node]@
               (List.filter (fun (CP.SpecVar (t,_,_)) -> is_pointer t) hv.CF.h_formula_view_arguments))
      | CF.HRel (sv, eargs, _) -> List.concat (List.map CP.afv eargs)
      | _ -> []
  in
  helper hf0
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

(*should improve: should take care hrel also*)
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

(*=======utilities for infer_collect_hp_rel=======*)
(*defined pointers list *
  for recursive constraint(HP name *
 parameter name list)*)
(*todo: how about null? is it defined?*)
let rec find_defined_pointers_raw prog f=
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
  let ( _,mix_f,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mix_f) in
  let eqNulls = CP.remove_dups_svl ( MCP.get_null_ptrs mix_f) in
  (*defined vars=  + null + data + view*)
  let def_vs = (eqNulls) @ (List.map (fun hd -> hd.CF.h_formula_data_node) hds)
   @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) in
  (*find closed defined pointers set*)
  (* let def_vs0 = CP.remove_dups_svl def_vs in *)
  let def_vs_wo_args = CP.remove_dups_svl ((List.fold_left close_def def_vs eqs)) in
  (def_vs_wo_args, hds, hvs, hrs, eqs)

and check_node_args_defined prog def_svl hd_nodes hv_nodes dn_name=
  let arg_svl = loop_up_ptr_args_one_node prog hd_nodes hv_nodes dn_name in
  (* DD.info_pprint ("  arg_svl" ^ (!CP.print_svl arg_svl)) no_pos; *)
  let diff_svl = Gen.BList.difference_eq CP.eq_spec_var arg_svl def_svl in
  (* DD.info_pprint ("  diff_svl" ^ (!CP.print_svl diff_svl)) no_pos; *)
  if diff_svl = [] then true
  else false

and find_defined_pointers_after_preprocess prog def_vs_wo_args hds hvs hrs eqs predef_ptrs=
  let tmp = def_vs_wo_args in
  (* DD.info_pprint ("   defined raw " ^(!CP.print_svl tmp)) no_pos; *)
  let def_vs = List.filter (check_node_args_defined prog (def_vs_wo_args@predef_ptrs) hds hvs) tmp in
  (*(HP name * parameter name list)*)
  let hp_paras = List.map
                (fun (id, exps, _) -> (id, List.concat (List.map CP.afv exps)))
                hrs in
  (def_vs, hp_paras, hds, hvs, eqs)

and find_defined_pointers_x prog f predef_ptrs=
  let (def_vs, hds, hvs, hrs, eqs) = find_defined_pointers_raw prog f in
  find_defined_pointers_after_preprocess prog def_vs hds hvs hrs eqs predef_ptrs

and find_defined_pointers prog f predef_ptrs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv pr1) in
  (* let pr3 = fun x -> Cprinter.string_of_h_formula (CF.HRel x) in *)
  let pr4 = fun (a1, a2, _, _, _) ->
      let pr = pr_pair pr1 pr2 in pr (a1,a2)
  in
  Debug.no_2 "find_defined_pointers" Cprinter.prtt_string_of_formula pr1 pr4
      (fun _ _ -> find_defined_pointers_x prog f predef_ptrs) f predef_ptrs


let keep_data_view_hrel_nodes prog f hd_nodes hv_nodes keep_rootvars keep_hrels=
  let keep_ptrs = loop_up_closed_ptr_args prog hd_nodes hv_nodes keep_rootvars in
  CF.drop_data_view_hrel_nodes f check_nbelongsto_dnode check_nbelongsto_vnode
    check_neq_hrelnode keep_ptrs keep_ptrs keep_hrels

let keep_data_view_hrel_nodes_fb prog fb hd_nodes hv_nodes keep_rootvars keep_hrels=
  let keep_ptrs = loop_up_closed_ptr_args prog hd_nodes hv_nodes keep_rootvars in
  CF.drop_data_view_hrel_nodes_fb fb check_nbelongsto_dnode check_nbelongsto_vnode
    check_neq_hrelnode keep_ptrs keep_ptrs keep_hrels keep_ptrs

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
    | _ -> report_error no_pos "sau.drop_data_view_hrel_nodes"


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
(*fro infer_collect_hp*)
let update_hp_args hf renamed_hps=
  let rec look_up_helper hp0 ls_hp_args=
    match ls_hp_args with
      | [] -> false,[]
      | (hp1,args1)::hs ->
          if CP.eq_spec_var hp0 hp1 then (true, args1)
          else look_up_helper hp0 hs
  in
  let rec helper hf0=
    match hf0 with
      | CF.HRel (hp, eargs, p ) ->
          let r,args1= look_up_helper hp renamed_hps in
          if r then (CF.HRel (hp,List.map (fun sv -> CP.mkVar sv p) args1, p))
          else hf0
      | CF.Conj hfc ->
          CF.Conj {hfc with CF.h_formula_conj_h1=helper hfc.CF.h_formula_conj_h1;
              CF.h_formula_conj_h2=helper hfc.CF.h_formula_conj_h2;}
      | CF.Star hfs ->
          CF.Star {hfs with CF.h_formula_star_h1=helper hfs.CF.h_formula_star_h1;
              CF.h_formula_star_h2=helper hfs.CF.h_formula_star_h2;}
      | CF.Phase hfp->
           CF.Phase{hfp with CF.h_formula_phase_rd=helper hfp.CF.h_formula_phase_rd;
              CF.h_formula_phase_rw=helper hfp.CF.h_formula_phase_rw;}
      | _ -> hf0
  in
  helper hf

let test_and_update fb renamed_hps ls_new_p pos=
  if ls_new_p = [] then fb
    else
    begin
        {fb with CF.formula_base_heap =
                update_hp_args fb.CF.formula_base_heap renamed_hps;
            CF.formula_base_pure = MCP.mix_of_pure (List.fold_left
               (fun p1 p2-> CP.mkAnd p1 p2 pos)(List.hd ls_new_p)
               (List.tl ls_new_p))}
    end

let rename_hp_args_x lfb rfb=
  let lp = MCP.pure_of_mix lfb.CF.formula_base_pure in
  let lpos = (CP.pos_of_formula lp) in
  let lhf = lfb.CF.formula_base_heap in
  let lls_hp_args = CF.get_HRels lhf in
  (*rhs*)
  let rp = MCP.pure_of_mix rfb.CF.formula_base_pure in
  let rpos = (CP.pos_of_formula rp) in
  let rhf = rfb.CF.formula_base_heap in
  let rls_hp_args = CF.get_HRels rhf in
  let rec lhelper args1 args2 p r=
    match args2 with
      | [] -> r,p,args1
      | a1::ass -> if CP.mem_svl a1 args1 then
            let new_v = CP.SpecVar (CP.type_of_spec_var a1,
                  "v_" ^ (string_of_int (Globals.fresh_int())),Unprimed)  in
            let p1 =
              (* if CP.isConstTrue p then *)
                CP.mkPtrEqn a1 new_v lpos
              (* else *)
              (*   let ss = List.combine [a1] [new_v] in *)
              (*   let p0 = CP.filter_var_new p [a1] in *)
              (*   CP.subst ss p0 *)
            in
            let p2 = CP.mkAnd p p1 lpos in
            lhelper (args1@[new_v]) ass p2 true
          else lhelper (args1@[a1]) ass p r
  in
  let rec rhelper args1 args2 lp rp r=
    match args2 with
      | [] -> r,lp,rp,args1
      | a1::ass -> if CP.mem_svl a1 args1 then
            let new_v = CP.SpecVar (CP.type_of_spec_var a1,
                  "v_" ^ (string_of_int (Globals.fresh_int())),Unprimed)  in
            let ss = List.combine [a1] [new_v] in
            (*lhs*)
            (* let lp1 = *)
            (*   (\* if CP.isConstTrue lp then *\) *)
            (*     CP.mkPtrEqn a1 new_v lpos *)
            (*   (\* else *\) *)
            (*   (\*   let lp0 = CP.filter_var_new lp [a1] in *\) *)
            (*   (\*   CP.subst ss lp0 *\) *)
            (* in *)
            (* let lp2 = CP.mkAnd lp lp1 lpos in *)
            (*rhs*)
            let rp1 =
              (* if CP.isConstTrue rp then *)
                CP.mkPtrEqn a1 new_v rpos
              (* else *)
              (*   let rp0 = CP.filter_var_new rp [a1] in *)
              (*   CP.subst ss rp0 *)
            in
            let rp2 = CP.mkAnd rp rp1 rpos in
            rhelper (args1@[new_v]) ass lp rp2 true
          else rhelper (args1@[a1]) ass lp rp r
  in
  let rename_one_lhp (hp,args)=
    let r,np,new_args= lhelper [] args lp false in
    if r then [((hp,new_args),np)] else []
  in
  let rename_one_rhp (hp,args)=
    let r,nlp,nrp,new_args= rhelper [] args lp rp false in
    if r then [((hp,new_args),(nlp,nrp))] else []
  in
  let lpair = List.concat (List.map rename_one_lhp lls_hp_args) in
  let rpair = List.concat (List.map rename_one_rhp rls_hp_args) in
  let lrenamed_hps,lls_p= List.split lpair in
  let rrenamed_hps,rls_p= List.split rpair in
  let lrls_p,rrls_p = List.split rls_p in
  let l_new_hps = lrenamed_hps@rrenamed_hps in
  let l_new_p = lls_p@lrls_p in
  let new_lb= test_and_update lfb l_new_hps l_new_p lpos in
  let new_rb = test_and_update rfb rrenamed_hps rrls_p rpos in
  (new_lb,new_rb)

let rename_hp_args lfb rfb=
  let pr=Cprinter.prtt_string_of_formula_base in
  Debug.no_2 "rename_hp_args" pr pr (pr_pair pr pr)
      (fun _ _ -> rename_hp_args_x lfb rfb) lfb rfb


let get_raw_defined_w_pure prog f=
  match f with
    | CF.Base fb ->
        let def_raw,_,_,_,_ = find_defined_pointers_raw prog f in
        (*LOCLE: should get closed + eqnull in pure*)
        let p_svl = CP.fv (MCP.pure_of_mix fb.CF.formula_base_pure) in
        (def_raw@p_svl)
    | _ -> report_error no_pos "sau.get_raw_defined_w_pure: not handle yet"


(*for unk hps*)
(*check whether args of an unk hp is in keep_ptrs*)
let get_intersect_unk_hps keep_ptrs (hp, args)=
  (*may need closed*)
  let diff = Gen.BList.difference_eq CP.eq_spec_var args keep_ptrs in
  if diff = [] then [hp]
  else []


let rec subst_view_hp_formula view_name hp (f: CF.formula) =
  match f with
    | CF.Base fb -> CF.Base {fb with CF.formula_base_heap = subst_view_hp_h_formula view_name hp fb.CF.formula_base_heap }
    | CF.Exists fe -> CF.Exists {fe with CF.formula_exists_heap = subst_view_hp_h_formula view_name hp fe.CF.formula_exists_heap }
    | CF.Or orf  -> CF.Or { orf with
      CF.formula_or_f1 = subst_view_hp_formula view_name hp orf.CF.formula_or_f1;
      CF.formula_or_f2= subst_view_hp_formula view_name hp orf.CF.formula_or_f2;
    }

and subst_view_hp_h_formula view_name (hp_name, _, p) hf =
  let rec helper hf0=
    match hf0 with
      | CF.Star hfs -> CF.Star {hfs with
          CF.h_formula_star_h1 = helper hfs.CF.h_formula_star_h1;
          CF.h_formula_star_h2 = helper hfs.CF.h_formula_star_h2;}
      | CF.Conj hfc -> CF.Conj {hfc with
          CF.h_formula_conj_h1 = helper hfc.CF.h_formula_conj_h1;
          CF.h_formula_conj_h2 = helper hfc.CF.h_formula_conj_h2;}
      | CF.Phase hfp -> CF.Phase {hfp with
          CF.h_formula_phase_rd = helper hfp.CF.h_formula_phase_rd;
          CF.h_formula_phase_rw = helper hfp.CF.h_formula_phase_rw;}
      | CF.ViewNode hv -> if hv.CF.h_formula_view_name = view_name then
            let n_args = [hv.CF.h_formula_view_node]@hv.CF.h_formula_view_arguments in
            (CF.HRel (hp_name,  List.map (fun x -> CP.mkVar x p) n_args,p))
          else hf0
      | _ -> hf0
  in
  helper hf

(*==========check_relaxeq=============*)
(*currently we do not submit exists*)
let check_stricteq_hnodes stricted_eq hns1 hns2=
  let check_stricteq_hnode hn1 hn2=
    let arg_ptrs1 = List.filter (fun (CP.SpecVar (t,_,_)) -> is_pointer t) hn1.CF.h_formula_data_arguments in
    let arg_ptrs2 = List.filter (fun (CP.SpecVar (t,_,_)) -> is_pointer t)  hn2.CF.h_formula_data_arguments in
    (hn1.CF.h_formula_data_name = hn2.CF.h_formula_data_name) &&
        (hn1.CF.h_formula_data_node = hn2.CF.h_formula_data_node) &&
        ((Gen.BList.difference_eq CP.eq_spec_var arg_ptrs1 arg_ptrs2)=[])
  in
  let rec helper hn hns2 rest2=
    match hns2 with
      | [] -> (false,rest2)
      | hn1::hss ->
          if check_stricteq_hnode hn hn1 then
            (true,rest2@hss)
          else helper hn hss (rest2@[hn1])
  in
  let rec helper2 hns1 hns2=
    match hns1 with
      | [] -> if hns2 = [] then true else (not stricted_eq)
      | hn1::rest1 ->
          let r,rest2 = helper hn1 hns2 [] in
          if r then
            helper2 rest1 rest2
          else false
  in
  if (List.length hns1) <= (List.length hns2) then
    helper2 hns1 hns2
  else false

let check_stricteq_hrels hrels1 hrels2=
   let check_stricteq_hr (hp1, eargs1, _) (hp2, eargs2, _)=
     let r = (CP.eq_spec_var hp1 hp2) in
     (* ((Gen.BList.difference_eq CP.eq_exp_no_aset *)
        (*     eargs1 eargs2)=[]) *)
     if r then
       let ls1 = List.concat (List.map CP.afv eargs1) in
       let ls2 = List.concat (List.map CP.afv eargs2) in
       (true, List.combine ls1 ls2)
     else (false,[])
  in
  let rec helper hr hrs2 rest2=
    match hrs2 with
      | [] -> (false,[],rest2)
      | hr1::hss ->
          let r,ss1= check_stricteq_hr hr hr1 in
          if r then
            (true,ss1,rest2@hss)
          else helper hr hss (rest2@[hr1])
  in
  let rec helper2 hrs1 hrs2 ss0=
    match hrs1 with
      | [] -> true,ss0
      | hr1::rest1 ->
          let r,ss, rest2 = helper hr1 hrs2 [] in
          if r then
            helper2 rest1 rest2 (ss0@ss)
          else (false,ss0)
  in
  if (List.length hrels1) = (List.length hrels2) then
    helper2 hrels1 hrels2 []
  else (false,[])

let check_stricteq_h_fomula_x stricted_eq hf1 hf2=
  let hnodes1, _, hrels1 = CF.get_hp_rel_h_formula hf1 in
  let hnodes2, _, hrels2 = CF.get_hp_rel_h_formula hf2 in
  let r,ss = check_stricteq_hrels hrels1 hrels2 in
  let helper hn=
    let n_hn = CF.h_subst ss (CF.DataNode hn) in
    match n_hn with
      | CF.DataNode hn -> hn
      | _ -> report_error no_pos "sau.check_stricteq_h_fomula"
  in
  if r then begin
      let n_hnodes1 = List.map helper hnodes1 in
      let n_hnodes2 = List.map helper hnodes2 in
      if (List.length n_hnodes1) <= (List.length n_hnodes2) then
        check_stricteq_hnodes stricted_eq n_hnodes1 n_hnodes2
      else
        check_stricteq_hnodes stricted_eq n_hnodes2 n_hnodes1
    end
  else false

let check_stricteq_h_fomula stricted_eq hf1 hf2=
  let pr1 = Cprinter.string_of_h_formula in
  Debug.no_3 " check_stricteq_h_fomula" string_of_bool pr1 pr1 string_of_bool
      (fun _ _ _ ->  check_stricteq_h_fomula_x stricted_eq hf1 hf2) stricted_eq hf1 hf2

let check_relaxeq_formula_x f1 f2=
  let hf1,mf1,_,_,_ = CF.split_components f1 in
  let hf2,mf2,_,_,_ = CF.split_components f2 in
  DD.ninfo_pprint ("   mf1: " ^(Cprinter.string_of_mix_formula mf1)) no_pos;
  DD.ninfo_pprint ("   mf2: " ^ (Cprinter.string_of_mix_formula mf2)) no_pos;
  (* let r1,mts = CEQ.checkeq_h_formulas [] hf1 hf2 [] in *)
  let r1 = check_stricteq_h_fomula true hf1 hf2 in
  if r1 then
    (* let new_mf1 = xpure_for_hnodes hf1 in *)
    (* let cmb_mf1 = MCP.merge_mems mf1 new_mf1 true in *)
    (* let new_mf2 = xpure_for_hnodes hf2 in *)
    (* let cmb_mf2 = MCP.merge_mems mf2 new_mf2 true in *)
    (* (\*remove dups*\) *)
    (* let np1 = CP.remove_redundant (MCP.pure_of_mix cmb_mf1) in *)
    (* let np2 = CP.remove_redundant (MCP.pure_of_mix cmb_mf2) in *)
    let np1 = CF.remove_neqNull_redundant_hnodes_hf hf1 (MCP.pure_of_mix mf1) in
    let np2 = CF.remove_neqNull_redundant_hnodes_hf hf2 (MCP.pure_of_mix mf2) in
    (* DD.info_pprint ("   f1: " ^(!CP.print_formula np1)) no_pos; *)
    (* DD.info_pprint ("   f2: " ^ (!CP.print_formula np2)) no_pos; *)
    (* let r2,_ = CEQ.checkeq_p_formula [] np1 np2 mts in *)
    let r2 = CP.equalFormula np1 np2 in
    let _ = DD.ninfo_pprint ("   eq: " ^ (string_of_bool r2)) no_pos in
    r2
  else
    false

let check_relaxeq_formula f1 f2=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "check_relaxeq_formula" pr1 pr1 string_of_bool
      (fun _ _ -> check_relaxeq_formula_x f1 f2) f1 f2

(*exactly eq*)
let checkeq_pair_formula (f11,f12) (f21,f22)=
  (check_relaxeq_formula f11 f21)&&(check_relaxeq_formula f12 f22)

let rec checkeq_formula_list_x fs1 fs2=
  let rec look_up_f f fs fs1=
    match fs with
      | [] -> (false, fs1)
      | f1::fss -> if (check_relaxeq_formula f f1) then
            (true,fs1@fss)
          else look_up_f f fss (fs1@[f1])
  in
  match fs1 with
    | [] -> true
    | f1::fss1 ->
        begin
            let r,fss2 = look_up_f f1 fs2 [] in
            if r then
              checkeq_formula_list fss1 fss2
            else false
        end

and checkeq_formula_list fs1 fs2=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "checkeq_formula_list" pr1 pr1 string_of_bool
      (fun _ _ -> checkeq_formula_list_x fs1 fs2) fs1 fs2

(*=============common prefix equal=========*)
let check_com_pre_eq_formula_x f1 f2=
  let hf1,mf1,_,_,_ = CF.split_components f1 in
  let hf2,mf2,_,_,_ = CF.split_components f2 in
  DD.ninfo_pprint ("   mf1: " ^(Cprinter.string_of_mix_formula mf1)) no_pos;
  DD.ninfo_pprint ("   mf2: " ^ (Cprinter.string_of_mix_formula mf2)) no_pos;
  (* let r1,mts = CEQ.checkeq_h_formulas [] hf1 hf2 [] in *)
  let r1 = check_stricteq_h_fomula false hf1 hf2 in
  if r1 then
    (*remove dups*)
    let np1 = CP.remove_redundant (MCP.pure_of_mix mf1) in
    let np2 = CP.remove_redundant (MCP.pure_of_mix mf2) in
    DD.ninfo_pprint ("   p1: " ^(!CP.print_formula np1)) no_pos;
    DD.ninfo_pprint ("   p2: " ^ (!CP.print_formula np2)) no_pos;
    (* let r2,_ = CEQ.checkeq_p_formula [] np1 np2 mts in *)
    let r2 = CP.equalFormula np1 np2 in
    let _ = DD.ninfo_pprint ("   eq: " ^ (string_of_bool r2)) no_pos in
    r2
  else
    false

let check_com_pre_eq_formula f1 f2=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "check_com_pre_eq_formula" pr1 pr1 string_of_bool
      (fun _ _ -> check_com_pre_eq_formula_x f1 f2) f1 f2

let get_longest_common_hnodes_two args shortes_ldns ldns2=
  let rec get_subst_svl svl1 svl2 ss=
    match svl1,svl2 with
	 | [],[] -> ss
	 | v1::sl1,v2::sl2 -> if CP.eq_spec_var v1 v2 then
		get_subst_svl sl1 sl2 ss
	    else get_subst_svl sl1 sl2 (ss@[(v1,v2)])
	 | _ -> report_error no_pos "sau.get_longest_common_hnodes_two 1"
  in
  let rec look_up_one_hd hn lnds matched2 rest2=
    match lnds with
      | [] ->  report_error no_pos "sau.get_longest_common_hnodes_two" (*(false,[],matched2, rest2)*)
      | hn1::ls ->
          if hn.CF.h_formula_data_name = hn1.CF.h_formula_data_name &&
            CP.eq_spec_var hn.CF.h_formula_data_node hn1.CF.h_formula_data_node
          then
		    (*return last args and remain*)
            (get_subst_svl hn1.CF.h_formula_data_arguments hn.CF.h_formula_data_arguments [], matched2@[hn1.CF.h_formula_data_node],rest2@ls)
		  else look_up_one_hd hn ls matched2 (rest2@[hn1])
  in
  let helper hn lnds matched2 rest2=
    let last_ss,matched,rest= look_up_one_hd hn lnds matched2 rest2 in
    (*let last_ss,n_matched,n_rest=
      if ss=[] then *)
       (* (ss,List.combine args2 hn.CF.h_formula_data_arguments, matched, rest)*)
    (*  else
        let hn21 = List.hd rest in
        (List.combine hn21.CF.h_formula_data_arguments hn.CF.h_formula_data_arguments,[], matched2@[hn21.CF.h_formula_data_node],List.tl rest)
    in *)
    ([],last_ss,matched,rest)
  in
  let rec look_up_min_hds sh_dns matched2 rest_dns2 ss last_ss=
    match sh_dns with
      | [] -> (matched2, rest_dns2, ss, last_ss)
          (* report_error no_pos "sau.get_longest_common_hnodes_two" *)
          (* if length rest_dns2: mk pure equality all ss*)
      (*| [hn] ->
          let last_ss, n_matcheds2,n_rest2 =  helper hn rest_dns2 matched2 [] in
          (n_matcheds2, n_rest2, ss, last_ss)*)
      |  hn::sh_ls ->
          let new_ss, new_last_ss, n_matcheds2,n_rest2 =  helper hn rest_dns2 matched2 [] in
            look_up_min_hds sh_ls n_matcheds2 n_rest2 (ss@new_ss) (new_last_ss@last_ss)
  in
  (*remove all dnodes in tail of args*)
  
  (* let _ =  DD.info_pprint ("       args: " ^ (!CP.print_svl args)) no_pos in *)
  look_up_min_hds shortes_ldns [] ldns2 [] []

let process_one_f org_args args hp_subst sh_ldns com_eqNulls (ldns, f)=
  (* let _ =  DD.info_pprint ("       new args: " ^ (!CP.print_svl args)) no_pos in *)
  (* let pr2 = pr_list Cprinter.string_of_h_formula in *)
  (* let _ = DD.info_pprint ("      sh_ldns:" ^ (pr2 (List.map (fun hd -> CF.DataNode hd) sh_ldns))) no_pos in *)
  
  let (matcheds2, rest2, ss, last_ss) = get_longest_common_hnodes_two org_args sh_ldns ldns in
  (*drop all matcheds*)
  (* let _ =  DD.info_pprint ("       matched 1: " ^ (!CP.print_svl matcheds2)) no_pos in *)
  (* let _ =  DD.info_pprint ("       eqNulls: " ^ (!CP.print_svl com_eqNulls)) no_pos in *)
  (* let _ =  DD.info_pprint ("       f: " ^ (Cprinter.prtt_string_of_formula f)) no_pos in *)
  let nf1 = CF.drop_hnodes_f f matcheds2 in
  (*let _ =  DD.info_pprint ("       nf1: " ^ (Cprinter.prtt_string_of_formula nf1)) no_pos in*)
  (* let _ =  DD.info_pprint ("       args: " ^ (!CP.print_svl args)) no_pos in *)
  (* let _ =  DD.info_pprint ("       last_ss: " ^ (let pr = pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) in pr last_ss)) no_pos in *)
  (*apply susbt ss*)
  let nf2 = CF.remove_eqNulls nf1 com_eqNulls in
  (* let _ =  DD.info_pprint ("       nf2: " ^ (Cprinter.prtt_string_of_formula nf2)) no_pos in *)
  let nf3 = CF.subst ss nf2 in
  (*if rest = [] then add pure equality all last_ss*)
  let nf5,last_ss=
    (*partition last_ss into two groups: one for subst another not*)
    let last_ss1,last_ss2 = List.partition
      (fun (v1,v2) -> Gen.BList.difference_eq CP.eq_spec_var [v1;v2] args = [])
      last_ss
    in
    (* if (rest2 = [] && (CF.get_hp_rel_name_formula nf2) <> [] *)
 (* (\*and <> current hp*\)) || is_empty_f nf2 then *)
    (*mk eq for last_ss1*)
    let ps = List.concat (List.map (fun ((CP.SpecVar (t,v,p)) ,v2) ->
        if (is_pointer t)
        then [CP.mkPtrEqn v2 (CP.SpecVar (t,v,p)) no_pos]
        else []) last_ss1) in
    let p = CP.conj_of_list ps no_pos in
   (*apply subst last_ss2*)
    let nf4 = CF.subst last_ss2 nf3 in
    (*should remove x!=null if x is in matched2s*)
    (*combine them*)
    CF.mkAnd_pure nf4 (MCP.mix_of_pure p) no_pos,last_ss2
  in
  (* let _ =  DD.info_pprint ("       nf5: " ^ (Cprinter.prtt_string_of_formula nf5)) no_pos in *)
  (*subst hp rel by its new definition if applicable*)
  let hprel,hf = hp_subst in
  (* let _ =  DD.info_pprint ("       hf: " ^ (Cprinter.prtt_string_of_h_formula hf)) no_pos in*)
  let slv_root = get_ptrs hprel in
  (* let _ = DD.info_pprint ("       svl_roots: " ^ (Cprinter.string_of_spec_var_list slv_root)) no_pos in *)
  let old_svl = get_ptrs hf in
  (*rename everything except root*)
  let old_svl1 = Gen.BList.difference_eq CP.eq_spec_var old_svl slv_root in
  let fresh_svl = CP.fresh_spec_vars old_svl1 in
  let ss = List.combine old_svl1 fresh_svl in
  let n_hf = CF.h_subst (ss) hf in
  (* let _ =  DD.info_pprint ("       n_hf: " ^ (Cprinter.prtt_string_of_h_formula n_hf)) no_pos in *)
  let nf6 = CF.subst_hrel_f nf5 [(hprel, n_hf)] in
  (* let _ =  DD.info_pprint ("       nf6: " ^ (Cprinter.prtt_string_of_formula nf6)) no_pos in *)
  nf6

let get_shortest_lnds ll_ldns min=
  let rec helper ll=
  match ll with
    | [] -> report_error no_pos "sau.get_shortest_lnds"
    | (ldns,f)::lls -> if List.length ldns = min then
          (ldns,f)
        else helper lls
  in
  helper ll_ldns

(*(hds,f) list*)
let get_min_number ll_ldns=
  let rec helper ll min=
  match ll with
    | [] -> min
    | (lnds,f)::lls ->
        let ns = List.length lnds in
        if ns < min then
          helper lls ns
        else helper lls min
  in
  (*start with length of the first one*)
  let fmin = List.length (fst (List.hd ll_ldns)) in
  helper (List.tl ll_ldns) fmin

let get_min_number_new prog args ll_ldns=
  let helper1 dns=
    let closed_args = (loop_up_closed_ptr_args prog dns [] args) in
    let dns1 = List.filter (fun dn -> CP.mem_svl dn.CF.h_formula_data_node closed_args) dns in
    (List.length dns1, dns1)
  in
  (*todo: should check eqFormula*)
  let helper_pure f =
    let ( _,mix_f,_,_,_) = CF.split_components f in
    let eqNulls = CP.remove_dups_svl ( MCP.get_null_ptrs mix_f) in
	eqNulls
  in
  let rec helper ll r_min r_hns r_eqNulls=
  match ll with
    | [] -> r_min,r_hns,r_eqNulls
    | (lnds,f)::lls ->
        let ns,nhds = helper1 lnds in
		let eqNulls = helper_pure f in
		let new_eqNulls = CP.intersect_svl r_eqNulls eqNulls in
        if ns < r_min then
          helper lls ns nhds new_eqNulls
        else helper lls r_min r_hns new_eqNulls
  in
  (*start with length of the first one*)
  let fmin, fdns = helper1 (fst (List.hd ll_ldns)) in
  let eqNull = helper_pure (snd (List.hd ll_ldns)) in
  helper (List.tl ll_ldns) fmin fdns eqNull

let move_root_to_top root ldns=
  let rec helper lss res=
    match lss with
      | [] -> res
      | dn::dnss -> if CP.eq_spec_var root dn.CF.h_formula_data_node then
            ([dn]@res@dnss)
          else helper dnss (res@[dn])
  in
  let rec rename_last ldns ldone=
    match ldns with
      | [] -> ldone
      | [dn] ->
          let ptrs = dn.CF.h_formula_data_arguments in
          let fresh_ptrs = CP.fresh_spec_vars ptrs in
          (* let fresh_dn = {dn with CF.h_formula_data_arguments = fresh_ptrs} in *)
          let new_ldns = (ldone@[dn]) in
          let ss = List.combine ptrs fresh_ptrs in
          let new_ldns1 = (List.map
                               (fun dn -> let hf = CF.h_subst ss (CF.DataNode dn) in
                                          match hf with
                                            | CF.DataNode hd1 -> hd1
                                            | _ -> report_error no_pos "sau.move_root_to_top"
                               ) new_ldns)
          in
          new_ldns1
      | dn::dnss -> rename_last dnss (ldone@[dn])
  in
  let nldns1 = helper ldns [] in
  (* nldns1 *)
  rename_last nldns1 []

let add_raw_hp_rel_x prog unknown_ptrs pos=
  if (List.length unknown_ptrs > 0) then
    let hp_decl =
      { Cast.hp_name = Globals.hp_default_prefix_name ^ (string_of_int (Globals.fresh_int()));
        Cast.hp_vars =  CP.remove_dups_svl unknown_ptrs;
        Cast.hp_formula = CF.mkBase CF.HEmp (MCP.mkMTrue pos) CF.TypeTrue (CF.mkTrueFlow()) [] pos;}
    in
    prog.Cast.prog_hp_decls <- (hp_decl :: prog.Cast.prog_hp_decls);
    Smtsolver.add_hp_relation hp_decl.Cast.hp_name hp_decl.Cast.hp_vars hp_decl.Cast.hp_formula;
    let hf =
      CF.HRel (CP.SpecVar (HpT,hp_decl.Cast.hp_name, Unprimed), 
               List.map (fun sv -> CP.mkVar sv pos) hp_decl.Cast.hp_vars,
      pos)
    in
    DD.ninfo_pprint ("       gen hp_rel: " ^ (Cprinter.string_of_h_formula hf)) pos;
    (hf, [CP.SpecVar (HpT,hp_decl.Cast.hp_name, Unprimed)])
  else report_error pos "sau.add_raw_hp_rel: args should be not empty"

let add_raw_hp_rel prog unknown_args pos=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.string_of_h_formula in
  let pr4 (hf,_) = pr2 hf in
  Debug.no_1 "add_raw_hp_rel" pr1 pr4
      (fun _ -> add_raw_hp_rel_x prog unknown_args pos) unknown_args

let mk_hprel_def hp args defs pos=
  DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")") pos;
  (*make disjunction*)
  (*remove neqNUll redundant*)
  let defs1 = List.map CF.remove_neqNull_redundant_hnodes_f defs in
  let def = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 (CF.pos_of_formula f1))
    (List.hd defs1) (List.tl defs1) in
  DD.ninfo_pprint (" =: " ^ (Cprinter.prtt_string_of_formula def) ) pos;
  let def = (hp, (CP.HPRelDefn hp, (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, pos)), def)) in
  def

(*because root is moved to top*)
let mk_orig_hprel_def prog hp args sh_ldns eqNulls=
  let rec get_last_ptrs ls_lnds=
    match ls_lnds with
      | [] -> report_error no_pos "sau.mk_orig_hprel_def: sth wrong"
      | [nd] -> List.concat (List.map ((fun (CP.SpecVar (t,v,p)) ->
          if (is_pointer t)
          then [CP.SpecVar (t,v,p)]
          else [])) nd.CF.h_formula_data_arguments)
      | nd::ndss -> get_last_ptrs ndss
  in
  let other_args = List.tl args in
  let get_connected_helper ((CP.SpecVar (t,v,p)) as r)=
    if CP.mem_svl r other_args then
      let new_v = CP.SpecVar (t,
                  (v) ^ "_" ^ (string_of_int (Globals.fresh_int())),Unprimed)  in
	  [(r,new_v)]
	else []
  in
  let rec look_up_next_ptrs hds r res=
    (*r_nexts may be other args, we should remove them*)
    (*if CP.mem_svl r other_args then
      let new_v = CP.SpecVar (CP.type_of_spec_var r,
                  (CP.name_of_spec_var r) ^ (string_of_int (Globals.fresh_int())),Unprimed)  in
      ([new_v],hds, [(r,new_v)])
    else *)
      match hds with
        | [] -> ([],res,[],[])
        | hd::hss -> if CP.eq_spec_var r hd.CF.h_formula_data_node then
              let r_nexts,ssl = List.split (List.concat (List.map ((fun (CP.SpecVar (t,v,p)) ->
                  if (is_pointer t)
                  then 
				    let ss = get_connected_helper (CP.SpecVar (t,v,p)) in
					let new_v = CP.subs_one ss (CP.SpecVar (t,v,p)) in
					([new_v,ss])
                  else [])) hd.CF.h_formula_data_arguments)) in
			  let ss = List.concat ssl in
			  let matched_hn =
				if ss <> [] then 
				  let r =(CF.h_subst ss (CF.DataNode hd)) in
					  match r with
					   | CF.DataNode hd -> hd
					   | _ -> report_error no_pos "sau.look_up_next_ptrs"
				else hd
			  in
              (r_nexts, res@hss,[matched_hn],ss)
            else look_up_next_ptrs hss r (res@[hd])
  in
  let rec helper hds roots r_nexts r_done r_ss=
    match roots with
      | [] -> (r_nexts,hds,r_done,r_ss)
      | r::rs -> let nptrs,nhds,hn_done,ss = look_up_next_ptrs hds r [] in
                 helper nhds rs (r_nexts@nptrs) (r_done@hn_done) (r_ss@ss)
  in
  let rec get_last_ptrs_new ls_lnds roots root_nexts r_done r_ss=
    match root_nexts with
      | [] -> roots,r_done,r_ss,ls_lnds
      | _ -> let nptrs,nhds,hn_done,ss = helper ls_lnds root_nexts [] [] [] in
             get_last_ptrs_new nhds root_nexts nptrs (r_done@hn_done) (r_ss@ss)
  in
  let next_roots,new_sh_dns,ss,rem_dns = get_last_ptrs_new sh_ldns [(List.hd args)] [(List.hd args)] [] [] in
  let dnss = (new_sh_dns@rem_dns) in
  let hdss = List.map (fun hd -> (CF.DataNode hd)) dnss in
  (*subst*)
  let pr2 = pr_list Cprinter.string_of_h_formula in
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let _ = DD.ninfo_pprint ("      subst:" ^ (pr1 ss)) no_pos in 
  (*let hdss = List.map (CF.h_subst ss) hdss in *)
  let _ = DD.ninfo_pprint ("      old sh_hdss:" ^ (pr2 (List.map (fun hd -> CF.DataNode hd) sh_ldns))) no_pos in
  let _ = DD.ninfo_pprint ("      new sh_hdss:" ^ (pr2 (hdss))) no_pos in
  let _ = DD.ninfo_pprint ("      eqNulls:" ^ (!CP.print_svl eqNulls)) no_pos in
  (*currently we just support one next root. should improve when support tree*)
  match next_roots with
     | [] -> report_error no_pos "sa.generalize_one_hp: sth wrong"
     | [a] ->  let _ = DD.ninfo_pprint ("      last root:" ^ (Cprinter.string_of_spec_var a)) no_pos in
         (*generate new hp*)
         let n_hprel,n_hp =  add_raw_hp_rel prog ([a]@(List.tl args)) no_pos in
              (*first rel def for the orig*)
         let rest =  (hdss@[n_hprel]) in
         let orig_defs_h = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 no_pos) (List.hd rest) (List.tl rest) in
         let orig_def = CF.formula_of_heap orig_defs_h no_pos in
		 let orig_def1 =
		   match eqNulls with
		   | [] -> orig_def
		   | _ ->
			  (*let eqNulls1 = List.map (CP.subs_one ss) eqNulls in*)
			  let ps = List.map (fun v -> CP.mkNull v no_pos) eqNulls in
		      let p = CP.conj_of_list ps no_pos in
			  CF.mkAnd_pure orig_def (MCP.mix_of_pure p) no_pos
		 in
         let def = mk_hprel_def hp args [orig_def1] no_pos in
         (*subst*)
         let hprel = CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, no_pos) in
		 (*elim all except root*)
		 let n_orig_defs_h = CF.drop_hnodes_hf orig_defs_h (List.tl args) in
         (def, (hprel, n_orig_defs_h), n_hp, ([a]@(List.tl args)), dnss)
     | _ -> report_error no_pos "sa.generalize_one_hp: now we does not handle more than two ptr fields"


let get_longest_common_hnodes_list_x prog hp args fs=
 if List.length fs <= 1 then
   let hpdef = mk_hprel_def hp args fs no_pos in
   [hpdef] (* ([], fs, []) *)
 else begin
   let lldns = List.map (fun f -> (get_hdnodes f, f)) fs in
   let min,sh_ldns,eqNulls = get_min_number_new prog args lldns in
   (* let min = get_min_number lldns in *)
   (* let _ =  DD.info_pprint ("    min: " ^ (string_of_int min) ) no_pos in *)
   if min = 0 then
     (*mk_hprel_def*)
     let hpdef = mk_hprel_def hp args fs no_pos in
      [hpdef]
     (* ([],fs, []) *)
   else
     (*get shortest list of hnodes*)
     (* let sh_ldns, _ = get_shortest_lnds lldns min in *)
     (*assume root is the first arg*)
     let root = List.hd args in
     (*let sh_ldns1 = move_root_to_top root sh_ldns in*)
     let orig_hpdef, hp_subst, new_hp, n_args,sh_ldns2 = mk_orig_hprel_def prog hp args sh_ldns eqNulls in
     let n_fs = List.map (process_one_f args n_args hp_subst sh_ldns2 eqNulls) lldns in
     let new_hpdef =  mk_hprel_def (List.hd new_hp) n_args n_fs no_pos in
     (* (List.map (fun hd -> (CF.DataNode hd)) sh_ldns1, n_fs, []) *)
     [orig_hpdef;new_hpdef]
 end

let get_longest_common_hnodes_list prog hp args fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  let pr2 = fun (_, def) -> Cprinter.string_of_hp_rel_def def in
  let pr3 = !CP.print_sv in
  let pr4 = !CP.print_svl in
  Debug.no_3 "get_longest_common_hnodes_list" pr3 pr4 pr1 (pr_list_ln pr2)
      (fun _ _ _ -> get_longest_common_hnodes_list_x prog hp args fs) hp args fs

(*==========END check_relaxeq=============*)
let remove_longer_common_prefix fs=
  let rec helper cur res=
    match cur with
      | [] -> res
      | f::ss ->
          if List.exists
            (fun f2 ->
                check_com_pre_eq_formula f2 f)
            res then
            helper ss res
          else helper ss (res@[f])
  in
  helper fs []

(*fix subst*)
let rec look_up_subst_group hp args nrec_grps=
  let rec susbt_group fs pardefs=
    match pardefs with
      | [] -> fs
      | (_, args2, f)::pss->
          let ss = List.combine args2 args in
          let nf = CF.subst ss f in
          susbt_group (fs@[nf]) pss
  in
  match nrec_grps with
    | [] -> [](* report_error no_pos "sau.look_up_groups" *)
    | grp::gs -> begin
        let hp1,_,_ = (List.hd grp) in
        if CP.eq_spec_var hp hp1 then
           susbt_group [] grp
        else
          look_up_subst_group hp args gs
    end

let succ_susbt nrec_grps (hp,args,f)=
  (* DD.info_pprint ("       succ_susbt hp: " ^ (!CP.print_sv hp)) no_pos; *)
  let pos = no_pos in
  (*l1 x l2*)
  let helper ls1 ls2=
    List.concat (List.map (fun f1 ->
        List.map (fun f2 ->
             CF.mkStar f1 f2 CF.Flow_combine pos
    ) ls2) ls1)
  in
  let succ_hp_args = CF.get_HRels_f f in
  (*filter hp out*)
  let succ_hp_args = List.filter (fun (hp1,_) -> not (CP.eq_spec_var hp hp1)) succ_hp_args in
  (* DD.info_pprint ("       succ_hp_args:" ^ (let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) *)
  (*                                           in pr succ_hp_args)) no_pos; *)
  match succ_hp_args with
    | [] -> (false,[(hp,args,f)])
    | _ -> begin
        let fs_list = List.map (fun (hp0,arg0) -> look_up_subst_group hp0 arg0 nrec_grps)  succ_hp_args in
        if List.length (List.concat fs_list) = 0 then (false,[(hp,args,f)]) else
        (*create template from f*)
          let nf,_ = CF.drop_hrel_f f (fst (List.split succ_hp_args)) in
        (*combine fs_list*)
          let lsf_cmb = List.fold_left helper [nf] fs_list in
          (* DD.info_pprint ("       succ_susbt lsf_cmb:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula) *)
          (*                                                 in pr lsf_cmb)) no_pos; *)
        (*remove f which has common prefix*)
          let lsf_cmb1 = remove_longer_common_prefix lsf_cmb in
          (* DD.info_pprint ("       succ_susbt lsf_cmb 1:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula) *)
          (*                                                   in pr lsf_cmb1)) no_pos; *)
          let fss = List.map (fun f1 -> (hp,args,f1)) lsf_cmb1 in
          (true,fss)
    end

let remove_longer_common_prefix_w_unk unk_hps fs=
  let rec helper cur res=
    match cur with
      | [] -> res
      | f::ss ->
          let f1 = CF.subst_unk_hps_f f unk_hps in
          if List.exists
            (fun f2 ->
                let f21 = CF.subst_unk_hps_f f2 unk_hps in
                check_com_pre_eq_formula f1 f21)
            res then
            helper ss res
          else helper ss (res@[f])
  in
  helper fs []


let rec look_up_subst_hpdef hp args nrec_hpdefs=
  match nrec_hpdefs with
    | [] -> [](* report_error no_pos "sau.look_up_groups" *)
    | (CP.HPRelDefn hp1,hprel1,f1)::gs -> begin
        if CP.eq_spec_var hp hp1 then
           let args1 = get_ptrs hprel1 in
           let ss = List.combine args1 args in
           let nf1 = CF.subst ss f1 in
           (CF.list_of_disjs nf1)
        else
          look_up_subst_hpdef hp args gs
    end

let succ_susbt_hpdef nrec_hpdefs all_succ_hp (hp,args,f)=
  (* DD.info_pprint ("       succ_susbt_def hp: " ^ (!CP.print_sv hp)) no_pos; *)
  let pos = no_pos in
  (*l1 x l2*)
  let helper ls1 ls2=
    List.concat (List.map (fun f1 ->
        List.map (fun f2 ->
             CF.mkStar f1 f2 CF.Flow_combine pos
    ) ls2) ls1)
  in
  let succ_hp_args = CF.get_HRels_f f in
  (*filter hp out*)
  let succ_hp_args = List.filter (fun (hp1,_) -> not (CP.eq_spec_var hp hp1) &&
      (CP.mem_svl hp1 all_succ_hp)) succ_hp_args in
  (* DD.info_pprint ("       succ_hp_args:" ^ (let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) *)
  (*                                           in pr succ_hp_args)) no_pos; *)
  match succ_hp_args with
    | [] -> (false,[f])
    | _ -> begin
        let fs_list = (List.map (fun (hp0,arg0) -> look_up_subst_hpdef hp0 arg0 nrec_hpdefs) succ_hp_args) in
        if List.length (List.concat fs_list) = 0 then (false,[f]) else
        (*create template from f*)
          let nf,_ = CF.drop_hrel_f f (fst (List.split succ_hp_args)) in
        (*combine fs_list*)
          let lsf_cmb = List.fold_left helper [nf] fs_list in
          (* DD.info_pprint ("       succ_susbt lsf_cmb:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula) *)
          (*                                                 in pr lsf_cmb)) no_pos; *)
        (*remove f which has common prefix*)
          let lsf_cmb1 = (remove_longer_common_prefix lsf_cmb) in
          (* DD.info_pprint ("       succ_susbt lsf_cmb 1:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula) *)
          (*                                                   in pr lsf_cmb1)) no_pos; *)
          (true,lsf_cmb1)
    end
