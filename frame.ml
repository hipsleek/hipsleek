#include "xdebug.cppo"
open VarGen
(*This file supports for framing specification*)

module DD = Debug
open Globals
open Gen
open Exc.GTable
open Perm
open Label_only
open Label

module C = Cast
module Err = Error
module CP = Cpure
module CPG = Cpgraph
module MCP = Mcpure
module CF = Cformula


let seg_opz = ref false

let look_up_ptr_args_one_node hd_nodes hv_nodes node_name=
  let rec look_up_data_node ls=
    match ls with
    | [] -> []
    | dn::ds ->
      if CP.eq_spec_var node_name dn.CF.h_formula_data_node then
        (* loop_up_ptr_args_data_node prog dn *)
        List.filter CP.is_node_typ dn.CF.h_formula_data_arguments
      else
        look_up_data_node ds
  in
  let rec look_up_view_node ls=
    match ls with
    | [] -> []
    | vn::ds -> if CP.eq_spec_var node_name vn.CF.h_formula_view_node then
        List.filter CP.is_node_typ vn.CF.h_formula_view_arguments
      else look_up_view_node ds
  in
  let ptrs = look_up_data_node hd_nodes in
  if ptrs = [] then look_up_view_node hv_nodes
  else ptrs


let look_up_closed_ptr_args hd_nodes hv_nodes node_names=
  let rec helper old_ptrs inc_ptrs=
    let new_ptrs = List.concat
        (List.map (look_up_ptr_args_one_node hd_nodes hv_nodes)
           inc_ptrs) in
    let diff_ptrs = List.filter (fun id -> not (CP.mem_svl id old_ptrs)) new_ptrs in
    let diff_ptrs = Gen.BList.remove_dups_eq CP.eq_spec_var diff_ptrs in
    if diff_ptrs = [] then old_ptrs
    else (helper (old_ptrs@diff_ptrs) diff_ptrs)
  in
  helper node_names node_names

let find_close svl0 eqs0=
  let rec find_match svl ls_eqs rem_eqs=
    match ls_eqs with
    | [] -> svl,rem_eqs
    | (sv1,sv2)::ss->
      let b1 = CP.mem_svl sv1 svl in
      let b2 = CP.mem_svl sv2 svl in
      let new_m,new_rem_eqs=
        match b1,b2 with
        | false,false -> [],[(sv1,sv2)]
        | true,false -> ([sv2],[])
        | false,true -> ([sv1],[])
        | true,true -> ([],[])
      in
      find_match (svl@new_m) ss (rem_eqs@new_rem_eqs)
  in
  let rec loop_helper svl eqs=
    let new_svl,rem_eqs = find_match svl eqs [] in
    if List.length new_svl > List.length svl then
      loop_helper new_svl rem_eqs
    else new_svl
  in
  loop_helper svl0 eqs0

let get_frame ante conseq=
  let (lh,lmf,_,_,_,_) = CF.split_components ante in
  let (rh,rmf,_,_,_,_) = CF.split_components conseq in
  let frm_svl1 = CPG.get_frame (MCP.pure_of_mix lmf) in
  let frm_svl2 = CPG.get_frame (MCP.pure_of_mix rmf) in
  let leqs = (MCP.ptr_equations_without_null lmf) in
  let frm_svl = CP.remove_dups_svl (frm_svl1@frm_svl2) in
  let frm_svl = find_close frm_svl leqs in
  let lhds,lhvs,_ = CF.get_hp_rel_formula ante in
  let cl1 = look_up_closed_ptr_args lhds lhvs frm_svl in
  let rhds,rhvs,_ = CF.get_hp_rel_formula conseq in
  let cl2 = look_up_closed_ptr_args rhds rhvs frm_svl in
  CP.remove_dups_svl (cl1@cl2)

let generate_framing_holes_x hf0 framing_svl =
  let rec helper hf=
    match hf with
    | CF.Star {CF.h_formula_star_h1 = hf1;
               CF.h_formula_star_h2 = hf2;
               CF.h_formula_star_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      (
        (* match n_hf1,n_hf2 with *)
        (*   | (CF.HEmp,CF.HEmp) -> CF.HEmp,frm1@frm2 *)
        (*   | (CF.HEmp,_) -> n_hf2,frm1@frm2 *)
        (*   | (_,CF.HEmp) -> n_hf1,frm1@frm2 *)
        (*   | _ -> *)
        CF.Star {CF.h_formula_star_h1 = n_hf1;
                 CF.h_formula_star_h2 = n_hf2;
                 CF.h_formula_star_pos = pos}, frm1@frm2
      )
    | CF.StarMinus { CF.h_formula_starminus_h1 = hf1;
                     CF.h_formula_starminus_h2 = hf2;
                     CF.h_formula_starminus_aliasing = a;
                     CF.h_formula_starminus_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.StarMinus { CF.h_formula_starminus_h1 = n_hf1;
                     CF.h_formula_starminus_h2 = n_hf2;
                     CF.h_formula_starminus_aliasing = a;
                     CF.h_formula_starminus_pos = pos},frm1@frm2
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;
                CF.h_formula_conj_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.Conj { CF.h_formula_conj_h1 = n_hf1;
                CF.h_formula_conj_h2 = n_hf2;
                CF.h_formula_conj_pos = pos},frm1@frm2
    | CF.ConjStar { CF.h_formula_conjstar_h1 = hf1;
                    CF.h_formula_conjstar_h2 = hf2;
                    CF.h_formula_conjstar_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.ConjStar { CF.h_formula_conjstar_h1 = n_hf1;
                    CF.h_formula_conjstar_h2 = n_hf2;
                    CF.h_formula_conjstar_pos = pos},frm1@frm2
    | CF.ConjConj { CF.h_formula_conjconj_h1 = hf1;
                    CF.h_formula_conjconj_h2 = hf2;
                    CF.h_formula_conjconj_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.ConjConj { CF.h_formula_conjconj_h1 = n_hf1;
                    CF.h_formula_conjconj_h2 = n_hf2;
                    CF.h_formula_conjconj_pos = pos},frm1@frm2
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;
                 CF.h_formula_phase_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.Phase { CF.h_formula_phase_rd = n_hf1;
                 CF.h_formula_phase_rw = n_hf2;
                 CF.h_formula_phase_pos = pos},frm1@frm2
    | CF.DataNode hd -> if CP.mem_svl hd.CF.h_formula_data_node framing_svl then
        let fr_int = Globals.fresh_int() in
        (CF.FrmHole fr_int,[(hf, fr_int)])
        (* (CF.HEmp,[hf]) *)
      else (hf,[])
    | CF.ViewNode hv -> if CP.mem_svl hv.CF.h_formula_view_node framing_svl then
        let fr_int = Globals.fresh_int() in
        (CF.FrmHole fr_int,[(hf, fr_int)])
        (* (CF.HEmp,[hf]) *)
      else (hf,[])
    | CF.HRel _
    | CF.Hole _ | CF.FrmHole _ | CF.ThreadNode _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp | CF.HVar _ -> (hf,[])
  in
  if framing_svl = [] then (hf0,[]) else
    helper hf0

let generate_framing_holes hf0 framing_svl =
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = !CP.print_svl in
  let pr3 = (* pr_list pr1 *)
    (pr_list (pr_pair pr1 string_of_int)) in
  Debug.no_2 "generate_framing_holes" pr1 pr2 (pr_pair pr1 pr3)
    (fun _ _ -> generate_framing_holes_x hf0 framing_svl) hf0 framing_svl

let prune_framing_heaps_x hf0 framing_svl =
  let rec helper hf=
    match hf with
    | CF.Star {CF.h_formula_star_h1 = hf1;
               CF.h_formula_star_h2 = hf2;
               CF.h_formula_star_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      (match n_hf1,n_hf2 with
       | (CF.HEmp,CF.HEmp) -> CF.HEmp,frm1@frm2
       | (CF.HEmp,_) -> n_hf2,frm1@frm2
       | (_,CF.HEmp) -> n_hf1,frm1@frm2
       | _ -> CF.Star {CF.h_formula_star_h1 = n_hf1;
                       CF.h_formula_star_h2 = n_hf2;
                       CF.h_formula_star_pos = pos}, frm1@frm2
      )
    | CF.StarMinus { CF.h_formula_starminus_h1 = hf1;
                     CF.h_formula_starminus_h2 = hf2;
                     CF.h_formula_starminus_aliasing =a;
                     CF.h_formula_starminus_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.StarMinus { CF.h_formula_starminus_h1 = n_hf1;
                     CF.h_formula_starminus_h2 = n_hf2;
                     CF.h_formula_starminus_aliasing =a;
                     CF.h_formula_starminus_pos = pos},frm1@frm2
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;
                CF.h_formula_conj_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.Conj { CF.h_formula_conj_h1 = n_hf1;
                CF.h_formula_conj_h2 = n_hf2;
                CF.h_formula_conj_pos = pos},frm1@frm2
    | CF.ConjStar { CF.h_formula_conjstar_h1 = hf1;
                    CF.h_formula_conjstar_h2 = hf2;
                    CF.h_formula_conjstar_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.ConjStar { CF.h_formula_conjstar_h1 = n_hf1;
                    CF.h_formula_conjstar_h2 = n_hf2;
                    CF.h_formula_conjstar_pos = pos},frm1@frm2
    | CF.ConjConj { CF.h_formula_conjconj_h1 = hf1;
                    CF.h_formula_conjconj_h2 = hf2;
                    CF.h_formula_conjconj_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.ConjConj { CF.h_formula_conjconj_h1 = n_hf1;
                    CF.h_formula_conjconj_h2 = n_hf2;
                    CF.h_formula_conjconj_pos = pos},frm1@frm2
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;
                 CF.h_formula_phase_pos = pos} ->
      let n_hf1,frm1 = helper hf1 in
      let n_hf2,frm2 = helper hf2 in
      CF.Phase { CF.h_formula_phase_rd = n_hf1;
                 CF.h_formula_phase_rw = n_hf2;
                 CF.h_formula_phase_pos = pos},frm1@frm2
    | CF.DataNode hd -> if CP.mem_svl hd.CF.h_formula_data_node framing_svl then
        (* let fr_int = Globals.fresh_int() in *)
        (* (CF.FrmHole fr_int,[(hf, fr_int)]) *)
        (CF.HEmp,[hf])
      else (hf,[])
    | CF.ViewNode hv -> if CP.mem_svl hv.CF.h_formula_view_node framing_svl then
        (* let fr_int = Globals.fresh_int() in *)
        (* (CF.FrmHole fr_int,[(hf, fr_int)]) *)
        (CF.HEmp,[hf])
      else (hf,[])
    | CF.HRel _
    | CF.Hole _ | CF.FrmHole _ | CF.ThreadNode _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp | CF.HVar _ -> (hf,[])
  in
  helper hf0

let prune_framing_heaps hf0 framing_svl =
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list pr1
  (* (pr_list (pr_pair pr1 string_of_int)) *) in
  Debug.no_2 "prune_framing_heaps" pr1 pr2 (pr_pair pr1 pr3)
    (fun _ _ -> prune_framing_heaps_x hf0 framing_svl) hf0 framing_svl

let subst_framing_heaps hf0 framing_map =
  let transform (hf,n)= (CF.get_ptr_from_data hf, n) in
  let frm_map = List.map transform framing_map in
  let rec helper hf=
    match hf with
    | CF.Star {CF.h_formula_star_h1 = hf1;
               CF.h_formula_star_h2 = hf2;
               CF.h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      (CF.Star {CF.h_formula_star_h1 = n_hf1;
                CF.h_formula_star_h2 = n_hf2;
                CF.h_formula_star_pos = pos}
      )
    | CF.StarMinus { CF.h_formula_starminus_h1 = hf1;
                     CF.h_formula_starminus_h2 = hf2;
                     CF.h_formula_starminus_aliasing=a;
                     CF.h_formula_starminus_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.StarMinus { CF.h_formula_starminus_h1 = n_hf1;
                     CF.h_formula_starminus_h2 = n_hf2;
                     CF.h_formula_starminus_aliasing =a;
                     CF.h_formula_starminus_pos = pos}
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;
                CF.h_formula_conj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.Conj { CF.h_formula_conj_h1 = n_hf1;
                CF.h_formula_conj_h2 = n_hf2;
                CF.h_formula_conj_pos = pos}
    | CF.ConjStar { CF.h_formula_conjstar_h1 = hf1;
                    CF.h_formula_conjstar_h2 = hf2;
                    CF.h_formula_conjstar_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.ConjStar { CF.h_formula_conjstar_h1 = n_hf1;
                    CF.h_formula_conjstar_h2 = n_hf2;
                    CF.h_formula_conjstar_pos = pos}
    | CF.ConjConj { CF.h_formula_conjconj_h1 = hf1;
                    CF.h_formula_conjconj_h2 = hf2;
                    CF.h_formula_conjconj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.ConjConj { CF.h_formula_conjconj_h1 = n_hf1;
                    CF.h_formula_conjconj_h2 = n_hf2;
                    CF.h_formula_conjconj_pos = pos}
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;
                 CF.h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.Phase { CF.h_formula_phase_rd = n_hf1;
                 CF.h_formula_phase_rw = n_hf2;
                 CF.h_formula_phase_pos = pos}
    | CF.DataNode hd -> begin
        try
          let fr_int = List.assoc hd.CF.h_formula_data_node frm_map in
          (CF.FrmHole fr_int)
        with Not_found -> hf
      end
    | CF.ViewNode hv -> begin
        try
          let fr_int = List.assoc hv.CF.h_formula_view_node frm_map in
          (CF.FrmHole fr_int)
        with Not_found -> hf
      end
    | CF.HRel _
    | CF.Hole _ | CF.FrmHole _ | CF.ThreadNode _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp | CF.HVar _  -> hf
  in
  helper hf0

let recover_framing_heaps hf0 framing_map =
  let rec look_up maps n=
    match maps with
    | [] -> report_error no_pos "frame.recover_framing_heaps: should exist"
    | (hf,m)::rest -> if m=n then hf else
        look_up rest n
  in
  let rec helper hf=
    match hf with
    | CF.Star {CF.h_formula_star_h1 = hf1;
               CF.h_formula_star_h2 = hf2;
               CF.h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      (CF.Star {CF.h_formula_star_h1 = n_hf1;
                CF.h_formula_star_h2 = n_hf2;
                CF.h_formula_star_pos = pos}
      )
    | CF.StarMinus { CF.h_formula_starminus_h1 = hf1;
                     CF.h_formula_starminus_h2 = hf2;
                     CF. h_formula_starminus_aliasing =a;
                     CF.h_formula_starminus_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.StarMinus { CF.h_formula_starminus_h1 = n_hf1;
                     CF.h_formula_starminus_h2 = n_hf2;
                     CF. h_formula_starminus_aliasing =a;
                     CF.h_formula_starminus_pos = pos}
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;
                CF.h_formula_conj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.Conj { CF.h_formula_conj_h1 = n_hf1;
                CF.h_formula_conj_h2 = n_hf2;
                CF.h_formula_conj_pos = pos}
    | CF.ConjStar { CF.h_formula_conjstar_h1 = hf1;
                    CF.h_formula_conjstar_h2 = hf2;
                    CF.h_formula_conjstar_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.ConjStar { CF.h_formula_conjstar_h1 = n_hf1;
                    CF.h_formula_conjstar_h2 = n_hf2;
                    CF.h_formula_conjstar_pos = pos}
    | CF.ConjConj { CF.h_formula_conjconj_h1 = hf1;
                    CF.h_formula_conjconj_h2 = hf2;
                    CF.h_formula_conjconj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.ConjConj { CF.h_formula_conjconj_h1 = n_hf1;
                    CF.h_formula_conjconj_h2 = n_hf2;
                    CF.h_formula_conjconj_pos = pos}
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;
                 CF.h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      CF.Phase { CF.h_formula_phase_rd = n_hf1;
                 CF.h_formula_phase_rw = n_hf2;
                 CF.h_formula_phase_pos = pos}
    | CF.DataNode _
    | CF.ViewNode _
    | CF.HRel _ | CF.ThreadNode _
    | CF.Hole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp | CF.HVar _ -> hf
    | CF.FrmHole n -> look_up framing_map n
  in
  helper hf0

let prune_framing_heaps_formula_x f0 framing_svl =
  let rec helper f=
    match f with
    | CF.Base fb -> let nfb,frm_hs =  prune_framing_heaps fb.CF.formula_base_heap framing_svl in
      (CF.Base {fb with CF.formula_base_heap =  nfb;
                        CF.formula_base_pure = MCP.mix_of_pure (fst (CPG.get_prune_frame (MCP.pure_of_mix fb.CF.formula_base_pure)));
               }, frm_hs)
    | CF.Or orf -> report_error no_pos "frm.prune_framing_heaps_formula: should use holes-like to mark framing positions"
    (* let nf1 = helper orf.formula_or_f1 in *)
    (*          let nf2 =  helper orf.formula_or_f2 in *)
    (* ( Or {orf with formula_or_f1 = nf1; *)
    (*          formula_or_f2 = nf2;}) *)
    | CF.Exists fe -> let nfe,frm_hs = prune_framing_heaps fe.CF.formula_exists_heap framing_svl in
      (CF.Exists {fe with CF.formula_exists_heap = nfe ;
                          CF.formula_exists_pure = MCP.mix_of_pure (fst (CPG.get_prune_frame (MCP.pure_of_mix fe.CF.formula_exists_pure)));
                 },frm_hs)
  in
  helper f0

let prune_framing_heaps_formula f0 framing_svl =
  let pr1 = Cprinter.string_of_formula in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list Cprinter.string_of_h_formula
  (* (pr_list (pr_pair Cprinter.string_of_h_formula string_of_int)) *) in
  Debug.no_2 "prune_framing_heaps_formula" pr1 pr2 (pr_pair pr1 pr3)
    (fun _ _ -> prune_framing_heaps_formula_x f0 framing_svl) f0 framing_svl

let subst_framing_heaps_formula_x f0 framing_map =
  let rec helper f=
    match f with
    | CF.Base fb -> let nfb =  subst_framing_heaps fb.CF.formula_base_heap framing_map in
      (CF.Base {fb with CF.formula_base_heap =  nfb;
                        CF.formula_base_pure = MCP.mix_of_pure (fst (CPG.get_prune_frame (MCP.pure_of_mix fb.CF.formula_base_pure)));
               })
    | CF.Or orf -> report_error no_pos "frm.subst_framing_heaps_formula: should use holes-like to mark framing positions"
    (* let nf1 = helper orf.formula_or_f1 in *)
    (*          let nf2 =  helper orf.formula_or_f2 in *)
    (* ( Or {orf with formula_or_f1 = nf1; *)
    (*          formula_or_f2 = nf2;}) *)
    | CF.Exists fe -> let nfe = subst_framing_heaps fe.CF.formula_exists_heap framing_map in
      (CF.Exists {fe with CF.formula_exists_heap = nfe ;
                          CF.formula_exists_pure = MCP.mix_of_pure (fst (CPG.get_prune_frame (MCP.pure_of_mix fe.CF.formula_exists_pure)));
                 })
  in
  helper f0


let subst_framing_heaps_formula f0 framing_map =
  let pr1 = Cprinter.string_of_formula in
  let pr2 =  (pr_list (pr_pair Cprinter.string_of_h_formula string_of_int)) in
  Debug.no_2 "subst_framing_heaps_formula" pr1 pr2 pr1
    (fun _ _ -> subst_framing_heaps_formula_x f0 framing_map) f0 framing_map

let subst_framing_heaps_es es framing_map=
  let n_es_f =  subst_framing_heaps_formula es.CF.es_formula framing_map in
  {es with CF.es_formula = n_es_f}

let prune_irr_neq_formula f0 =
  let rec helper f=
    match f with
    | CF.Base fb ->
      let np=
        if !Globals.allow_frame then
          let ptrs = Cfutil.get_ptrs_connected_w_args fb.CF.formula_base_heap in
          let _,np2 = CPG.prune_irr_neq_ll (MCP.pure_of_mix fb.CF.formula_base_pure) ptrs in
          MCP.mix_of_pure np2
        else fb.CF.formula_base_pure
      in
      (CF.Base {fb with
                CF.formula_base_pure =  np;
               })
    | CF.Or orf -> report_error no_pos "frm.generate_framing_heaps_formula: should use holes-like to mark framing positions"
    (* let nf1 = helper orf.formula_or_f1 in *)
    (*          let nf2 =  helper orf.formula_or_f2 in *)
    (* ( Or {orf with formula_or_f1 = nf1; *)
    (*          formula_or_f2 = nf2;}) *)
    | CF.Exists fe -> let qvars, base_f = CF.split_quantifiers f in
      let nf= helper base_f in
      (CF.add_quantifiers qvars nf )
  in
  helper f0

let prune_irr_neq_es es=
  let n_es_f = prune_irr_neq_formula es.CF.es_formula in
  CF.Ctx {es with CF.es_formula = n_es_f}


let generate_framing_heaps_formula f0 framing_svl =
  let rec helper f=
    match f with
    | CF.Base fb -> let nhf,map =  generate_framing_holes fb.CF.formula_base_heap framing_svl in
      let np1 = if framing_svl = [] then
          (MCP.pure_of_mix fb.CF.formula_base_pure)
        else
          (fst (CPG.get_prune_frame (MCP.pure_of_mix fb.CF.formula_base_pure)))
      in
      (* let np1= *)
      (*       if !Globals.allow_frame then *)
      (*         let ptrs = CF.get_ptrs_w_args nhf in *)
      (*         let _,np2 = CP.prune_irr_neq np1 [ptrs] in *)
      (*         np2 *)
      (*       else np1 *)
      (* in *)
      (CF.Base {fb with CF.formula_base_heap =  nhf;
                        CF.formula_base_pure = MCP.mix_of_pure np1;
               }, map)
    | CF.Or orf -> report_error no_pos "frm.generate_framing_heaps_formula: should use holes-like to mark framing positions"
    (* let nf1 = helper orf.formula_or_f1 in *)
    (*          let nf2 =  helper orf.formula_or_f2 in *)
    (* ( Or {orf with formula_or_f1 = nf1; *)
    (*          formula_or_f2 = nf2;}) *)
    | CF.Exists fe -> let qvars, base_f = CF.split_quantifiers f in
      let nf, m = helper base_f in
      (CF.add_quantifiers qvars nf, m )
  in
  helper f0

let generate_framing_heaps_es_x es framing_svl=
  let n_es_f,map_hs = generate_framing_heaps_formula es.CF.es_formula framing_svl in
  {es with CF.es_formula = n_es_f},map_hs

let generate_framing_heaps_es es framing_svl=
  let pr1 = Cprinter.string_of_entail_state in
  let pr2 = pr_list (pr_pair Cprinter.string_of_h_formula string_of_int) in
  Debug.no_2 "generate_framing_heaps_es" pr1 !CP.print_svl (pr_pair pr1 pr2)
    (fun _ _ -> generate_framing_heaps_es_x es framing_svl)
    es framing_svl

let subst_framing_heaps_ctx_x ctx0 framing_map=
  match ctx0 with
  | CF.Ctx estate -> let n_es = subst_framing_heaps_es estate framing_map in
    (CF.Ctx  n_es)
  | CF.OCtx _ -> report_error no_pos ("frm.subst_framing_heaps_ctx: context is disjunctive or fail!!!")

let subst_framing_heaps_ctx ctx framing_map =
  let pr1 = Cprinter.string_of_context in
  let pr2 = pr_list (pr_pair Cprinter.string_of_h_formula string_of_int) in
  (* let pr3 = pr_pair pr1 pr2 pr1 in *)
  Debug.no_2 "subst_framing_heaps_ctx" pr1 pr2 pr1
    (fun _ _ -> subst_framing_heaps_ctx_x ctx framing_map) ctx framing_map

(*cur_frm_svl: can come from lhs if h and mf is of rhs*)
let extract_frame_heap_x h cur_frm_svl=
  (* let np,frm_svl = CP.get_prune_frame (MCP.pure_of_mix mf) in *)
  let nh,frm_hs = generate_framing_holes h cur_frm_svl in
  (nh,frm_hs)

let extract_frame_heap h frm_svl=
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = pr_pair pr1 (pr_list (pr_pair pr1 string_of_int )) in
  Debug.no_2 "extract_frame_heap" pr1 !CP.print_svl pr2
    (fun _  _ ->  extract_frame_heap_x h frm_svl) h frm_svl

let recover_framing_heaps_formula_x f0 framing_map =
  let rec helper f=
    match f with
    | CF.Base fb -> let nh = recover_framing_heaps fb.CF.formula_base_heap framing_map in
      (CF.Base {fb with CF.formula_base_heap =  nh;
               })
    | CF.Or orf -> report_error no_pos "frm.recover_framing_heaps_formula: should use holes-like to mark framing positions"
    (* let nf1 = helper orf.formula_or_f1 in *)
    (*          let nf2 =  helper orf.formula_or_f2 in *)
    (* ( Or {orf with formula_or_f1 = nf1; *)
    (*          formula_or_f2 = nf2;}) *)
    | CF.Exists fe -> let nh = recover_framing_heaps fe.CF.formula_exists_heap framing_map in
      (CF.Exists {fe with CF.formula_exists_heap = nh ;
                 })
  in
  helper f0

let recover_framing_heaps_formula f0 framing_map =
  let pr1 = Cprinter.string_of_formula in
  let pr2 = (pr_list (pr_pair Cprinter.string_of_h_formula string_of_int)) in
  Debug.no_2 "recover_framing_heaps_formula" pr1 pr2 pr1
    (fun _ _ -> recover_framing_heaps_formula_x f0 framing_map) f0 framing_map

let recover_framing_heaps_es es framing_map=
  let n_es_f = recover_framing_heaps_formula es.CF.es_formula framing_map in
  {es with CF.es_formula = n_es_f}

let recover_framing_heaps_ctx_x ctx0 framing_hs=
  let rec helper ctx=
    match ctx with
    | CF.Ctx estate -> let n_es = recover_framing_heaps_es estate framing_hs in
      (CF.Ctx n_es)
    | CF.OCtx (ctx1,ctx2) -> CF.OCtx (helper ctx1, helper ctx2)
  in
  helper ctx0

let recover_framing_heaps_ctx ctx framing_hs =
  let pr1 = Cprinter.string_of_context in
  let pr2 = pr_list (pr_pair Cprinter.string_of_h_formula string_of_int) in
  Debug.no_2 "recover_framing_heaps_ctx" pr1 pr2 pr1
    (fun _ _ -> recover_framing_heaps_ctx_x ctx framing_hs) ctx framing_hs

let recover_framing_heaps_list_ctx ls framing_hs=
  match ls with
  | CF.FailCtx _ -> ls
  | CF.SuccCtx ctxs -> CF.SuccCtx (List.map (fun ctx -> recover_framing_heaps_ctx ctx framing_hs) ctxs)

(*data nodes, view nodes*)
let get_p_view_data_h_formula hf0=
  let rec helper hf=
    match hf with
    | CF.Star { CF.h_formula_star_h1 = hf1;
                CF.h_formula_star_h2 = hf2}
    | CF.StarMinus { CF.h_formula_starminus_h1 = hf1;
                     CF.h_formula_starminus_h2 = hf2} ->
      let hd1,hv1 = helper hf1 in
      let hd2,hv2 = (helper hf2) in
      (hd1@hd2,hv1@hv2)
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;}
    | CF.ConjStar { CF.h_formula_conjstar_h1 = hf1;
                    CF.h_formula_conjstar_h2 = hf2;}
    | CF.ConjConj { CF.h_formula_conjconj_h1 = hf1;
                    CF.h_formula_conjconj_h2 = hf2;} ->
      let hd1,hv1 = (helper hf1)in
      let hd2,hv2 = (helper hf2) in
      (hd1@hd2,hv1@hv2)
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;} ->
      let hd1,hv1 = (helper hf1) in
      let hd2,hv2 = (helper hf2) in
      (hd1@hd2,hv1@hv2)
    | CF.DataNode hd -> ([hd],[])
    | CF.ViewNode hv -> ([],[hv])
    | CF.HRel _
    | CF.Hole _ | CF.FrmHole _| CF.ThreadNode _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp | CF.HVar _ -> ([],[])
  in
  helper hf0

let get_p_view_data (f:CF.formula) =
  match f with
  | CF.Base  ({CF.formula_base_heap = h1;
               CF.formula_base_pure = p1})
  | CF.Exists ({CF.formula_exists_heap = h1;
                CF.formula_exists_pure = p1}) -> (
      let hds,hvs = get_p_view_data_h_formula h1 in
      (MCP.pure_of_mix p1,hvs,hds)
    )
  | CF.Or _  -> report_error no_pos "Frame.get_p_view_data: not handle yet"


(******************************)
(*emp analysis*)
(******************************)
(* symbolic heap node
*)
(******************************)
type sym_node = CP.spec_var list

let print_sym_node = !CP.print_svl

let intersect_sym_svl sym_node svl=
  CP.intersect_svl sym_node svl

let eq_sym_nodes n1 n2=
  (List.length n1 = List.length n2) &&
  CP.diff_svl n1 n2 = []

let eq_sym_node_svl n1 svl=
  (List.length n1 = List.length svl) &&
  CP.diff_svl n1 svl = []

let sym_add_alias (sym_n:sym_node) (sv1,sv2):sym_node =
  if CP.mem_svl sv1 sym_n then
    sym_n@[sv2]
  else if CP.mem_svl sv2 sym_n then
    sym_n@[sv1]
  else sym_n

let svl_add_alias svl (sv1,sv2) =
  if CP.mem_svl sv1 svl then
    svl@[sv2]
  else if CP.mem_svl sv2 svl then
    svl@[sv1]
  else svl

let svl_add_list_alias svl ls =
  List.fold_left (fun ls pr-> svl_add_alias ls pr) svl ls

let combine_sym n sv= List.map (fun sv1 -> (sv1,sv)) n

(******************************)
(******************************)

let rec look_up_view_name sv maps=
  match maps with
  | [] -> None
  | (view_name, svl)::rest ->
    if CP.mem_svl sv svl then (Some view_name)
    else
      look_up_view_name sv rest

let rec look_up_emp_cond_x vname svl ls_map=
  match ls_map with
  | [] -> report_error no_pos "Frame.get_non_emp_x: 1"
  | (vname1, args1, ocond)::rest -> begin
      if String.compare vname vname1 = 0 && (List.length svl = List.length args1) then
        match ocond with
        | Some cond ->
          (* let () = Debug.info_hprint (add_str " cond: " (!CP.print_formula )) cond no_pos in *)
          let ss = List.combine args1 svl in
          let cond1 =  (CP.subst ss cond) in
          (* let () = Debug.info_hprint (add_str " cond1: " (!CP.print_formula )) cond1 no_pos in *)
          (* let () = Debug.info_hprint (add_str " neq: " (!CP.print_formula )) neq no_pos in *)
          [cond1]
        | None -> []
      else
        look_up_emp_cond_x vname svl rest

    end

let look_up_emp_cond vname svl ls_map=
  let pr1 op = match op with
    | None -> "None"
    | Some p -> !CP.print_formula p
  in
  let pr2 = pr_list (pr_triple pr_id !CP.print_svl pr1) in
  Debug.no_3 "look_up_emp_cond" pr_id !CP.print_svl pr2 (pr_list !CP.print_formula) (fun _ _ _ -> look_up_emp_cond_x vname svl ls_map) vname svl ls_map

let get_non_emp_x p view_ptrs_map view_emp_map=
  let list_to_pair ls =
    match ls with
    | [sv1;sv2] -> (sv1,sv2)
    | _ -> report_error no_pos "Frame.get_non_emp_x: 2"
  in
  let process_neq neq=
    let svl = CP.fv neq in
    let ov_name = look_up_view_name (List.hd svl) view_ptrs_map in
    match ov_name with
    | None -> []
    | Some v_name -> begin
        let cond = look_up_emp_cond v_name svl view_emp_map in
        if cond = [] then [] else
        if CPG.is_neg_equality neq (List.hd cond) then [svl] else []
      end
  in
  let ps = CP.list_of_conjs p in
  (*eq and neq*)
  let eqs, rest = List.partition CP.is_eq_exp ps in
  let neqs = List.filter CP.is_neq_exp rest in
  (*todo: neqNulls is red node*)
  let neqNulls, neqs1 = List.partition CP.is_neq_null_exp neqs in
  let non_emps = List.fold_left (fun ls neq -> ls@(process_neq neq)) [] neqs1 in
  (List.map list_to_pair (List.map CP.fv eqs),List.map list_to_pair non_emps)

let get_non_emp p view_ptrs_map view_emp_map=
  let pr1 = !CP.print_formula in
  let pr2 = pr_pair !CP.print_sv !CP.print_sv in
  let pr3 = pr_pair (pr_list  pr2) (pr_list pr2) in
  Debug.no_1 "get_non_emp" pr1 pr3
    (fun _ -> get_non_emp_x p view_ptrs_map view_emp_map) p
(******************************)

let revert_emp_abs_x emps view_ptrs_map view_emp_map=
  let process_emp (sv1,sv2)=
    let ov_name = look_up_view_name sv1 view_ptrs_map in
    match ov_name with
    | None -> []
    | Some v_name -> begin
        look_up_emp_cond v_name [sv1;sv2] view_emp_map
      end
  in
  List.fold_left (fun ls emp -> ls@(process_emp emp)) [] emps

let revert_emp_abs emps view_ptrs_map view_emp_map=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_list !CP.print_formula in
  Debug.no_1 "revert_emp_abs" pr1 pr2
    (fun _ -> revert_emp_abs_x emps view_ptrs_map view_emp_map) emps

(*xpure base cases for one predicate*)


(*xpure base cases for list of predicates*)

let rec filter_out inter_elinks0 chains res=
  match chains with
  | [] -> res
  | (sym_r_n, b,c):: rest ->
    if eq_sym_node_svl sym_r_n inter_elinks0 then
      filter_out inter_elinks0 rest res
    else filter_out inter_elinks0 rest (res@[(sym_r_n, b,c)])
(*emp calculus*)
(*
- emp(x,y,dont know) & emp (y,z, YES) ==> emp (x,z,dont know)
- emp(x,y,dont know) & emp (y,z,NO) ==> emp (x,z,NO)
- emp(x,y,dont know) & emp (y,z,dont know) ==> emp (x,z,dont know)
*)

(*rule 2*)
(*root r: a chain has a node or a non-base case between two nodes of the chain
  ==> other chains of root r must be base cases
  r --> w1
  r ---> w2

  if not emp(r,w1) then emp(r,w2)
*)
let rec intersect_fast ls ls1=
  match ls with
  | [] -> true
  | sv::rest ->
    if CP.mem_svl sv ls1 then intersect_fast rest ls1
    else false

let rec find_non_empty_one_chain l_non_emps ptrs=
  match l_non_emps with
  | [] -> false
  | (sv1,sv2)::rest -> if intersect_fast [sv1;sv2] ptrs then true
    else
      find_non_empty_one_chain rest ptrs

(*all sv1, sv2 \in svl: emp (sv1,sv2) *)
let build_emp svl maybe_emps=
  let inter_emp = List.filter (fun (sv1,sv2) -> (CP.mem_svl sv1 svl) && (CP.mem_svl sv2 svl)) maybe_emps in
  inter_emp

let force_spatial_no_dups_x maybe_emps non_emps (r,chains)=
  let rec find_non_emp cur_ls done_ls=
    match cur_ls with
    | [] -> []
    | (r_n,ptrs,end_ptrs)::rest ->
      if find_non_empty_one_chain non_emps ptrs then
        (* List.map (fun (r_n,_,_) -> (r,r_n)) (done_ls@rest) *)
        let ptr_other_chains = List.fold_left (fun ls (_,svl,_) -> ls@svl) [] (done_ls@rest) in
        build_emp (CP.remove_dups_svl ptr_other_chains) maybe_emps
      else
        find_non_emp rest (done_ls@[(r_n,ptrs,end_ptrs)])
  in
  let emps = find_non_emp chains [] in
  (* let end_links = List.map snd emps in *)
  (emps,(r,(* filter_out end_links chains [] *) chains))

let force_spatial_no_dups maybe_emps non_emps (r,chains)=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_pair print_sym_node (pr_list (pr_triple print_sym_node !CP.print_svl !CP.print_svl)) in
  Debug.no_1 "force_spatial_no_dups" pr2 (pr_pair pr1 pr2)
    (fun _ -> force_spatial_no_dups_x maybe_emps non_emps (r,chains)) (r,chains)

(*rule 3*)
(*
r --> w
r --> w'
r---> w''
and if not emp(w, w') then emp(r, w'')
*)
let force_spatial_transitive_x maybe_emps non_emps (r,chains)=
  let rec find_non_emp_from_2_chains ptrs rem_chains done_chains=
    match rem_chains with
    | [] -> []
    | (r_n,ptrs1,end_links)::rest ->
      if find_non_empty_one_chain non_emps (ptrs@ptrs1) then
        (rest@done_chains)
      else find_non_emp_from_2_chains ptrs rest (done_chains@[(r_n,ptrs1,end_links)])
  in
  let rec find_non_emp_trans cur_ls done_ls=
    match cur_ls with
    | [] -> []
    | (r_n,ptrs,end_ptrs)::rest ->
      let emp_chains = find_non_emp_from_2_chains ptrs rest [] in
      if emp_chains = [] then
        find_non_emp_trans rest (done_ls@[(r_n,ptrs,end_ptrs)])
      else
        (* List.map (fun (r_n,_,_) -> (r,r_n)) (done_ls@emp_chains) *)
        let ptr_other_chains = List.fold_left (fun ls (_,svl,_) -> ls@svl) [] (done_ls@emp_chains) in
        build_emp (CP.remove_dups_svl ptr_other_chains) maybe_emps
  in
  if List.length chains < 3 then []
  else find_non_emp_trans chains []

let force_spatial_transitive maybe_emps non_emps (r,chains)=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_pair print_sym_node (pr_list (pr_triple print_sym_node !CP.print_svl !CP.print_svl)) in
  Debug.no_1 "force_spatial_transitive" pr2 pr1
    (fun _ -> force_spatial_transitive_x maybe_emps non_emps (r,chains)) (r,chains)

let force_spatial maybe_emps non_emps chains_grp =
  let emp2, chains_grp1 = force_spatial_no_dups maybe_emps non_emps chains_grp in
  let emp3 = force_spatial_transitive maybe_emps non_emps chains_grp1 in
  (emp2@emp3, chains_grp1)

(*rule 4 - apply one*)
(*check no distinct loop-free for paths*)
(*root r:
  check NO distinct loop-free for one path r-w1
  r --u1--> w1
  r --u2--> w1
  ========> create loop: w1=r (w1 != null:: elim null at the intersection of chains)

*)
(*chain = nt, ptrs, end*)
(*return eqs of r end intersected end_links*)
let force_no_disctinct_loop_free_x maybe_emps (sym_r,chains) =
  let rec find_loop (sym_n_r0, svl0, end_links0) is_one_step elim_cur_chain rest0 done_chains res=
    match rest0 with
    | [] -> elim_cur_chain,done_chains,res
    | (sym_n_r1, svl1, end_links1)::rest1 ->
      let inter_svl = CP.remove_dups_svl (CP.intersect_svl svl0 svl1) in
      let inter_svl0 = CP.diff_svl inter_svl sym_r in
      let () = Debug.ninfo_hprint (add_str " inter_svl0: " (!CP.print_svl )) inter_svl0 no_pos in
      let () = Debug.ninfo_hprint (add_str " sym_n_r1: " (!CP.print_svl )) sym_n_r1 no_pos in
      let () = Debug.ninfo_hprint (add_str " end_links1: " (!CP.print_svl )) end_links1 no_pos in
      if inter_svl0 = [] || List.length inter_svl0 > 1 then
        (*do not have loop*)
        find_loop (sym_n_r0, svl0, end_links0) is_one_step elim_cur_chain rest1 (done_chains@[(sym_n_r1, svl1, end_links1)]) res
      else
        (*has loop*)
        let inter_svl1 = CP.diff_svl inter_svl0 end_links1 in
        if inter_svl1 = [] then
          (*loop that the intersection is the end*)
          let () = Debug.ninfo_hprint (add_str " ****1**** is_one_step " (string_of_bool )) is_one_step no_pos in
          if is_one_step then
            (* ([(\*(sym_n_r0, svl0, end_links0)*\)],(done_chains@rest0),res@inter_svl0) *)
            find_loop (sym_n_r0, svl0, end_links0) is_one_step true rest1 (done_chains@[(sym_n_r1, svl1, end_links1)]) (res@inter_svl0)
          else if (eq_sym_node_svl sym_n_r1 end_links1) then
            find_loop (sym_n_r0, svl0, end_links0) is_one_step elim_cur_chain rest1 (done_chains) (res@inter_svl0)
          else
            find_loop (sym_n_r0, svl0, end_links0) is_one_step elim_cur_chain  rest1 (done_chains@[(sym_n_r1, svl1, end_links1)]) (res@inter_svl0)
        else
          (*loop that the intersection is the middle*)
          let () = Debug.ninfo_hprint (add_str " ****2****" pr_id)"" no_pos in
          let inter_svl2 = ( CP.diff_svl inter_svl0 end_links0) in
          if eq_sym_node_svl sym_n_r0 inter_svl2 then
            (* ([(sym_n_r0, svl0, end_links0) ],(done_chains@((sym_n_r1, sym_r@sym_n_r1@inter_svl2, inter_svl2)::rest1)),res@inter_svl2) *)
            let () = Debug.ninfo_hprint (add_str " ****3****: " pr_id) "" no_pos in
            (true,(done_chains@((sym_n_r1, sym_r@sym_n_r1@inter_svl2, inter_svl2)::rest1)),res@inter_svl2)
          else if (eq_sym_node_svl sym_n_r1 inter_svl1) then
            let () = Debug.ninfo_hprint (add_str " ****4****: " pr_id) "" no_pos in
            find_loop (sym_n_r0, svl0, end_links0) is_one_step elim_cur_chain rest1 (done_chains) (res@inter_svl1)
          else
            find_loop (sym_n_r0, svl0, end_links0) is_one_step (elim_cur_chain) rest1 (done_chains@[(sym_n_r1, svl1, end_links1)]) (res@inter_svl1)
  in
  let rec find_loops ls done_chains res=
    match ls with
    | [] -> (CP.remove_dups_svl res, done_chains)
    | (sym_r_n, svl,end_links)::rest ->
      (* let () = Debug.info_hprint (add_str " sym_r: " (!CP.print_svl )) sym_r no_pos in *)
      (*check have a self loop*)
      if CP.intersect_svl sym_r end_links = [] then
        let elim_cur,rest1,n_inter = find_loop (sym_r_n, svl,end_links) (eq_sym_node_svl sym_r_n end_links) false
            rest [] [] in
        let n_done_chains = if elim_cur then done_chains else done_chains@[(sym_r_n, svl,end_links)] in
        find_loops rest1 n_done_chains (res@n_inter)
      else
        find_loops rest (done_chains@[(sym_r_n, svl,end_links)]) (res)
  in
  let inter_elinks,rems = find_loops chains [] [] in
  (* (List.fold_left (fun ls sv -> ls@(combine_sym sym_r sv)) [] inter_elinks, (sym_r@inter_elinks, rems)) *)
  (List.fold_left (fun ls sv -> ls@(combine_sym sym_r sv)) [] inter_elinks,(sym_r,rems))

let force_no_disctinct_loop_free maybe_emps (r,chains)=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_pair print_sym_node (pr_list (pr_triple print_sym_node !CP.print_svl !CP.print_svl)) in
  Debug.no_1 "force_no_disctinct_loop_free" pr2 (pr_pair pr1 pr2)
    (fun _ -> force_no_disctinct_loop_free_x maybe_emps (r,chains)) (r,chains)

(*note: sefl recursive and mutex recursive*)
let combine_dependent_components_x comps=
  let classify_helper (l_indep_comps, l_depen_comps) (r,chains)=
    let dep_rs = List.fold_left (fun ls (_,_,_, ls1) -> ls@ls1) [] chains in
    (*remove self recursive for loop scenarios*)
    let dep_rs1 = CP.remove_dups_svl (List.filter (fun sv -> not (CP.eq_spec_var sv r)) dep_rs) in
    if dep_rs1 = [] then
      (*indepen_coms, remove empty depent list of chains*)
      (*c is endlink, now support multiple endlinks wit [c]*)
      let n_chains = List.map (fun (a,b,c,_) -> ([a],b,[c])) chains in
      (l_indep_comps@[([r], n_chains)], l_depen_comps)
    else
      let n_chains = List.map (fun (a,b,c,d) -> (a,b,[c],d)) chains in
      (l_indep_comps, l_depen_comps@[(r, n_chains, dep_rs1,  0)])
  in
  (*sort order of nrec_grps to subst*)
  let topo_sort_x comps=
    let update_order_from_comps updated_roots incr (r,chains, dep_rs1, old_n)=
      if CP.mem_svl r updated_roots then
        (r,chains, dep_rs1,old_n+incr)
      else (r,chains, dep_rs1,old_n)
    in
    let process_one_dep_comps topo (r, chains, dep_rs,  n)=
      List.map (update_order_from_comps dep_rs 1) topo
    in
    let topo1 = List.fold_left process_one_dep_comps comps comps in
    (*sort decreasing and return the topo list*)
    let topo2 = List.sort (fun (_,_,_,n1) (_,_,_,n2) -> n2-n1) topo1 in
    topo2
  in
  (*for debugging*)
  let topo_sort comps=
    let pr1 = pr_quad !CP.print_sv (pr_list (pr_quad !CP.print_sv !CP.print_svl !CP.print_svl !CP.print_svl))
        !CP.print_svl string_of_int in
    let pr2 = pr_list_ln pr1 in
    Debug.no_1 "topo_sort" pr2 pr2
      (fun _ -> topo_sort_x comps) comps
  in
  let rec look_up_indep comps deps=
    match comps with
    | [] -> []
    | (sym_r,chains)::rest ->
      if CP.intersect_svl sym_r deps <> [] then
        List.map (fun (_,svl,el) -> (svl,el)) chains
      else look_up_indep rest deps
  in
  let rec look_up_dep comps deps=
    match comps with
    | [] -> []
    | (r,chains,_,_)::rest ->
      if CP.mem_svl r deps then
        List.map(fun (_,svl,el,_) -> (svl,el)) chains
      else look_up_dep rest deps
  in
  let rec combine chains indep_comps comps res=
    match chains with
    | [] -> res
    | (r_n, svl, els, deps)::rest ->
      let svl1 = look_up_indep indep_comps deps in
      let svl2 = look_up_dep comps deps in
      let n_svl,endlinks =  if List.length svl1 > 0 || List.length svl2 > 0 then
          let ls1,ls2 = List.fold_left (fun (svl,endlinks) (n_svl, n_ends) -> svl@n_svl,endlinks@n_ends) (svl,[]) (svl1@svl2) in
          (CP.remove_dups_svl ls1,ls2)
          (* let new_chains = *)
          (*   List.map (fun (svl1,el1) ->  (r_n, CP.remove_dups_svl (svl@svl1), el1, deps)) (svl1@svl2) *)
        else
          (svl, els)
      in
      (*make use of endlinks when support multiple endlinks*)
      let new_chains = [(r_n, n_svl, endlinks, deps)] in
      combine rest indep_comps comps (res@new_chains)
  in
  let rec combine_comps l_comps indep_comps res=
    match l_comps with
    | [] -> res
    | (r, chains, dep_rs1,  n)::rest ->
      (*if dep_rs1 = [] then chains else*)
      let n_chains = combine chains indep_comps (res@rest) [] in
      combine_comps rest indep_comps (res@[(r, n_chains, dep_rs1,  n)])
  in
  let indep_comps, dep_coms = List.fold_left classify_helper ([],[]) comps in
  (*build topo - dependent graph among components*)
  let sorted_dep_coms = topo_sort dep_coms in
  (*combine: bottom-up*)
  let combined_dep_coms = combine_comps sorted_dep_coms indep_comps [] in
  let combined_dep_coms1 = List.map (fun (r,chains,_,_) ->
      let n_chains = List.map (fun (a,b,c,_) -> ([a],b,c)) chains in
      ([r],n_chains)
    ) combined_dep_coms in
  (*should recombine for mutex dependence*)
  (indep_comps@combined_dep_coms1)


let combine_dependent_components comps=
  let pr2 = pr_pair !CP.print_sv (pr_list (pr_quad !CP.print_sv !CP.print_svl !CP.print_sv !CP.print_svl)) in
  let pr3 = pr_pair  print_sym_node (pr_list (pr_triple print_sym_node !CP.print_svl !CP.print_svl)) in
  Debug.no_1 "combine_dependent_components" (pr_list_ln pr2) (pr_list_ln pr3)
    (fun _ -> combine_dependent_components_x comps) comps

(****************************************************************************************)
(************AUX*************************)
(***************************************************************************************)
let rec part_grp ls_map res=
  match ls_map with
  | [] -> res
  | (vname1, svl1)::rest ->
    let part,rem = List.partition (fun (vname2,_) -> String.compare vname1 vname2 = 0) rest in
    let svl = List.fold_left (fun ls (_, svl2) -> ls@svl2) svl1 part in
    part_grp rem (res@[(vname1, svl)])

let get_ptr_view_map vns=
  let ls_view_ptrs_map = List.map (fun vn ->
      (vn.CF.h_formula_view_name, vn.CF.h_formula_view_node::(List.filter (fun sv ->
           CP.is_node_typ sv) vn.CF.h_formula_view_arguments)
      )
    ) vns in
  let maps = part_grp ls_view_ptrs_map [] in
  maps
(*should improve for more precise*)
let abs_maybe intial_emps vn=
  List.fold_left (fun ls sv ->
      let sv1,sv2 = (vn.CF.h_formula_view_node, sv) in
      if ( List.exists (fun (sv3,sv4) ->
          (CP.eq_spec_var sv1 sv3 && CP.eq_spec_var sv2 sv4) ||
          (CP.eq_spec_var sv1 sv4 && CP.eq_spec_var sv2 sv3))
          intial_emps) then ls else ls@[(sv1,sv2)]
    )
    [] (List.filter (fun sv ->
        CP.is_node_typ sv && not (CP.eq_spec_var sv vn.CF.h_formula_view_node)) vn.CF.h_formula_view_arguments)
(****************************************************************************************)
(************END AUX*************************)
(***************************************************************************************)
(*
goal: classify as many as maybe emp ---> emp
*)
let norm_dups_pred_x cprog f=
  let rec get_dups_hv eqs ls_maybe_emp res=
    match ls_maybe_emp with
    | [] -> List.filter (fun (_,ls) -> List.length ls > 1) res
    | (sv1,sv2)::rest ->
      let part,rem = List.partition (fun (sv,_) ->
          let svl = find_close [sv] eqs in
          CP.mem_svl sv1 svl
        )
          rest in
      get_dups_hv eqs rem (res@[(sv1,(sv1,sv2)::part)])
  in
  let rec find_chain all_dups_roots cur res links=
    try
      (* let () = Debug.info_pprint (" XXXXXXXXXX 3: " ^ (!CP.print_sv cur)) no_pos in *)
      if CP.mem_svl cur all_dups_roots then
        (*this chain points to anothe2r root*)
        (cur,res,[cur])
      else
        let n = List.assoc cur links in
        (* let () = Debug.info_pprint (" XXXXXXXXXX 4: " ^ (!CP.print_sv n)) no_pos in *)
        if CP.mem_svl n res then (n,res,[]) else
          find_chain all_dups_roots n (res@[n]) links
    with Not_found ->
      (cur,res,[])
  in
  let build_chains all_dups_roots all_maybe_emps hds (r,maybe_rdups_group)=
    (*list of (maybe emp-next ptr,ptrs in the chain, last ptrs)*)
    (*now only work with view -- should support data node also - a chain has a dn --> non emp*)
    let process_one_chain (r,r_n) =
      (* let () = Debug.info_pprint (" XXXXXXXXXX 5 - root: " ^ (!CP.print_sv r)) no_pos in *)
      let end_link, chains, deps = find_chain all_dups_roots r_n [r;r_n] all_maybe_emps in
      (r_n, chains,end_link,deps)
    in
    (r,List.map process_one_chain maybe_rdups_group)
  in
  (*each find emp branch - now assume emp branches are base cases*)
  (*return = (view name, view arguments, emp condition)*)
  let view_emp_map = Cast.get_emp_map cprog in
  let p,vns,dns = get_p_view_data f in
  let view_ptrs_map = get_ptr_view_map vns in
  (*return = (list of non-emp (v1,v2), list of eq )*)
  (*find initial non-emp constraints from pure*)
  let eqs0,non_emps0 = get_non_emp p view_ptrs_map view_emp_map in
  (*find chains from duplicate pred roots*)
  let maybe_emps = List.fold_left (fun ls vn -> ls@(abs_maybe eqs0 vn)) [] vns in
  (* TODO:WN : code below not executed *)
  (*          bool -> *)
  (*          bool -> *)
  (*          bool * (Hgraph.CP.spec_var * Hgraph.CP.spec_var) list * *)
  (*          Hgraph.heap_graph *)
  (*        but an expression was expected of type unit *)
  let () = x_winfo_pp "(TO FIX) norm_graph (in frame.ml) not executed!" no_pos in
  (* let todo_unk_bug_here = Hgraph.norm_graph maybe_emps eqs0 non_emps0 in *)
  let maybe_rdups_groups = get_dups_hv eqs0 maybe_emps [] in
  let all_dups_roots = List.map fst maybe_rdups_groups in
  (* let () = Debug.info_pprint (" XXXXXXXXXX 1") no_pos in *)
  let rdups_chains_grps = List.map (build_chains all_dups_roots maybe_emps dns) maybe_rdups_groups in
  let rdups_chains_grps0 = combine_dependent_components rdups_chains_grps in
  let rdups_chains_grps1 = List.map (fun (r,chains) -> (svl_add_list_alias r eqs0,chains)) rdups_chains_grps0 in
  (* let () = Debug.info_pprint (" XXXXXXXXXX 2") no_pos in *)
  (*rule 4*)
  (*detect dictinct loop*)
  let rec collect chains res_svl res_els=
    match chains with
    | [] -> res_svl,res_els
    | (_,svl,els)::rest ->
      collect rest (res_svl@svl) (res_els@els)
  in
  let rec look_up_next_roots grps new_roots res_svl res_els=
    match grps with
    | [] -> (*this root is not among duplicate ones*)
      res_svl,res_els
    | (rs,chains)::rest ->
      (*rs is the original graph*)
      let inter,rems = List.partition (fun sv -> List.mem sv rs) new_roots in
      if inter = [] then
        look_up_next_roots rest rems res_svl res_els
      else
        (*look up*)
        let n_svl,new_els = if eq_sym_nodes rs inter then
            collect chains [] []
          else report_error no_pos "frame.look_up_next_roots"
        in
        if rems = [] then
          (*no more new roots, return*)
          (res_svl@n_svl),(res_els@new_els)
        else
          look_up_next_roots rest rems (res_svl@n_svl) (res_els@new_els)
  in
  let rec to_combine sym_r sym_n eqs=
    match eqs with
    | [] -> false
    | (sv1,sv2)::rest ->
      if (CP.mem_svl sv1 sym_r && CP.mem_svl sv2 sym_n) ||
         (CP.mem_svl sv2 sym_r && CP.mem_svl sv1 sym_n) then true
      else to_combine sym_r sym_n rest
  in
  let rec get_new_next cur_sym_n eqs new_n1 new_n2 =
    (*(sv1,sv2): if cur_next is sv1: need update chains from sv2. otherwise dont need*)
    match eqs with
    | [] -> new_n1,new_n2
    | (sv1,sv2)::rest -> begin
        let b1 = CP.mem_svl sv1 cur_sym_n in
        let b2 = CP.mem_svl sv2 cur_sym_n in
        match b1,b2 with
        | false,false -> get_new_next cur_sym_n rest new_n1 new_n2
        | false,true -> get_new_next cur_sym_n rest new_n1 (new_n2@[sv1])
        | true,false -> get_new_next cur_sym_n rest (new_n1@[sv2]) new_n2
        | _ -> get_new_next cur_sym_n rest new_n1 new_n2
      end
  in
  let update_alias_chain sym_r eqs (sym_n,svl,els)=
    if to_combine sym_r sym_n eqs then [] else
      let n_sym_n = CP.remove_dups_svl (svl_add_list_alias sym_n eqs) in
      let n_els = (svl_add_list_alias els eqs) in
      let n_svl = List.fold_left (fun ls pr-> svl_add_alias ls pr) svl eqs in
      let diff_n1,diff_n2 = (* (CP.diff_svl n_sym_n sym_n) in *) get_new_next sym_n eqs [] [] in
      let () = Debug.ninfo_hprint (add_str " diff_n1: " (!CP.print_svl)) diff_n1 no_pos in
      let () = Debug.ninfo_hprint (add_str " diff_n2: " (!CP.print_svl )) diff_n2 no_pos in
      let n_svl_from_new_roots,els_from_new_roots = if diff_n1 = [] then [],[] else
          look_up_next_roots rdups_chains_grps0 diff_n1 [] []
      in
      [(n_sym_n,CP.remove_dups_svl (n_svl@n_svl_from_new_roots), CP.remove_dups_svl (n_els@els_from_new_roots))]
  in
  let update_alias_comps_x eqs (r,chains)=
    let n_r = svl_add_list_alias r eqs in
    (n_r,List.fold_left (fun ls chain -> ls@(update_alias_chain n_r eqs chain)) [] chains)
  in
  let update_alias_comps eqs (r,chains)=
    let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
    let pr2 = pr_pair print_sym_node (pr_list (pr_triple print_sym_node !CP.print_svl !CP.print_svl)) in
    Debug.no_2 "update_alias_comps" pr1 pr2 pr2
      (fun _ _ -> update_alias_comps_x eqs (r,chains)) eqs (r,chains)
  in
  let rec find_loops_helper grps done_grps emps=
    match grps with
    | [] -> emps,done_grps
    | grp::rest ->
      let eqs, (r,n_grp) = (force_no_disctinct_loop_free maybe_emps grp) in
      let n_grp1 = if List.length n_grp > 1 then [(r,n_grp)] else [] in
      (*update symbolic nodes + svl*)
      (* let rest1, done_grps2= *)
      (*   (\* if eqs= [] then *\) (rest,(done_grps@n_grp1)) (\* else *\) *)
      (*     (\* let rest1 = List.map (update_alias_comps eqs) rest in *\) *)
      (*     (\* let done_grps2 = List.map (update_alias_comps eqs) (done_grps@n_grp1) in *\) *)
      (*     (\* (rest1,done_grps2) *\) *)
      (* in *)
      (*move to next*)
      find_loops_helper rest (done_grps@n_grp1) (emps@eqs)
  in
  (* let emps4,rdups_chains_grps1 = List.fold_left (fun (ls1,ls2) grp -> *)
  (*     let eqs, (r,n_grp) = (force_no_disctinct_loop_free maybe_emps grp) in *)
  (*     let n_grp1 = if List.length n_grp > 1 then [(r,n_grp)] else [] in *)
  (*     (ls1@eqs, ls2@n_grp1) *)
  (* ) *)
  (*   ([],[]) rdups_chains_grps0 in *)
  (*should loop*)
  let rec fix_helper1 orig_grps rdups_chains_grps cur_emps=
    let new_emps,rdups_chains_grps1 = find_loops_helper rdups_chains_grps [] [] in
    let new_emps1 = Gen.BList.difference_eq (fun (sv1,sv2) (sv3,sv4) ->
        (CP.eq_spec_var sv1 sv3 && CP.eq_spec_var sv2 sv4) ||
        (CP.eq_spec_var sv1 sv4 && CP.eq_spec_var sv2 sv3)
      ) new_emps cur_emps in
    if new_emps = [] then (cur_emps,rdups_chains_grps1) else
      (*remove self loop*)
      let rdups_chains_grps2 = List.map (update_alias_comps new_emps) orig_grps in
      fix_helper1 orig_grps rdups_chains_grps2 (cur_emps@new_emps1)
  in
  let emps4,rdups_chains_grps2 =  (* find_loops_helper rdups_chains_grps0 [] [] *)
    fix_helper1 rdups_chains_grps1 rdups_chains_grps1 []
  in
  let rec loop_helper cur_emps grps=
    let new_emps,new_grps =
      List.fold_left (fun (ls1,ls2) grp ->
          let eqs, (r,n_grp) = (force_spatial maybe_emps non_emps0 grp) in
          let n_grp1 = if List.length n_grp > 1 then [(r,n_grp)] else [] in
          (ls1@eqs, ls2@n_grp1)
        )
        ([],[]) grps in
    let new_emps1 = Gen.BList.difference_eq (fun (sv1,sv2) (sv3,sv4) ->
        (CP.eq_spec_var sv1 sv3 && CP.eq_spec_var sv2 sv4) ||
        (CP.eq_spec_var sv1 sv4 && CP.eq_spec_var sv2 sv3)
      ) new_emps cur_emps in (new_emps1@cur_emps)
    (*dont need to loop*)
    (* if new_emps1 = [] then *)
    (*     (\*quick check conflict on emp abs*\) *)
    (*     cur_emps *)
    (*   else loop_helper (cur_emps@new_emps1) new_grps *)
  in
  let emps = loop_helper [] rdups_chains_grps2 in
  let emps1 = Gen.BList.remove_dups_eq (fun (sv1,sv2) (sv3,sv4) ->
      ((CP.eq_spec_var sv1 sv3) && (CP.eq_spec_var sv2 sv4))
    ) (emps@emps4) in

  let ps = revert_emp_abs emps1 view_ptrs_map view_emp_map in
  (*remove hvns in non emp*)
  let drop_hvns = CP.remove_dups_svl (List.map fst emps1) in
  let f1 = Cfutil.update_f f drop_hvns ps in
  f1

let norm_dups_pred_new_x cprog ante_non_emps f set_ptos build_graph do_case_split=
  (*each find emp branch - now assume emp branches are base cases*)
  (*return = (view name, view arguments, emp condition)*)
  let view_emp_map = Cast.get_emp_map cprog in
  let p,vns,dns = get_p_view_data f in
  let view_ptrs_map = get_ptr_view_map vns in
  (*return = (list of non-emp (v1,v2), list of eq )*)
  (*find initial non-emp constraints from pure*)
  let eqs0,non_emps0a = get_non_emp p view_ptrs_map view_emp_map in
  let non_emps0 = ante_non_emps@non_emps0a in
  (*10-06*)
  if not build_graph && eqs0 =[] && non_emps0 = [] then (false, f, Hgraph.mk_empty_hgraph()) else
    (*find chains from duplicate pred roots*)
    let maybe_emps = List.fold_left (fun ls vn -> ls@(abs_maybe eqs0 vn)) [] vns in
    let (is_conflict,emps1,graph) = Hgraph.norm_graph maybe_emps eqs0 non_emps0 set_ptos do_case_split in
    if is_conflict then (true,f,graph) else
      let ps = revert_emp_abs emps1 view_ptrs_map view_emp_map in
      (*remove hvns in non emp*)
      let drop_hvns = CP.remove_dups_svl (List.map fst emps1) in
      let f1 = Cfutil.update_f f drop_hvns ps in
      (false,f1,graph)

let norm_dups_pred_new_a cprog ante_non_emps f set_ptos build_graph do_case_split=
  if not (Cfutil.is_empty_heap_f f) && !seg_opz then
    norm_dups_pred_new_x cprog ante_non_emps f set_ptos build_graph do_case_split
  else false,f,(Hgraph.mk_empty_hgraph ())

let norm_dups_pred prog ante_non_emps f set_ptos build_graph do_case_split=
  let pr1 = Cprinter.string_of_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 = Hgraph.print_hgraph in
  Debug.no_2 "norm_dups_pred" pr1 pr2 (pr_triple string_of_bool pr1 pr3)
    (fun _ _ -> norm_dups_pred_new_a prog ante_non_emps f set_ptos
        build_graph do_case_split) f ante_non_emps

(*
min_grp_size
check sat = 3
check ent = 2
*)
let heap_normal_form_x prog f0 min_grp_size=
  let f = CF.elim_exists f0 in
  let comps = Cfutil.get_ptrs_connected_w_args_f f in
  let _ =
    if List.length comps <= 1 then
      let () = Globals.slice_one := !Globals.slice_one + 1 in
      ()
    else ()
  in
  let comps1 = List.filter (fun ls -> ( List.length ls) >= min_grp_size ) comps in
  let fs =
    (* if List.length comps1 > 1 then *)
    Cfutil.slice_frame f comps1
    (* else *)
    (*   [f] *)
  in
  (* List.map (norm_dups_pred prog) *) fs

let heap_normal_form cprog f min_grp_size=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_1 "heap_normal_form" pr1 (pr_list pr1)
    (fun _ -> heap_normal_form_x cprog f min_grp_size) f

let heap_normal_form_es prog min_grp_size es=
  let form_ctx f = CF.Ctx {es with CF.es_formula = f} in
  let n_es_fs = heap_normal_form prog es.CF.es_formula min_grp_size in
  let n_es_fs1 = List.map (norm_dups_pred prog []) n_es_fs in
  match n_es_fs1 with
  | [] -> [form_ctx (CF.mkTrue_nf no_pos)]
  | _ -> List.map (fun f -> form_ctx f) n_es_fs

let heap_normal_form_ctx prog min_grp_size c=
  match c with
  | CF.Ctx e -> (heap_normal_form_es prog min_grp_size e)
  | CF.OCtx (c1,c2) -> report_error no_pos "frame.slice_frame_ectx: not handle yet"


let check_unsat_w_norm prog f0 set_ptos=
  let helper f=
    let is_heap_conflict,_,_ = norm_dups_pred prog [] (CF.elim_exists f) set_ptos false true in
    is_heap_conflict
  in
  if not !seg_opz then false,None else
    let fs = (heap_normal_form prog f0 Hgraph.hgraph_grp_min_size_unsat) in
    let rec loop_helper fs=
      match fs with
      | [] -> false, None
      | f::rest ->
        let res1 = helper f in
        if res1 then (true,Some f) else
          loop_helper rest
    in
    let r,fail_of =
      match fs with
      | [] -> (* report_error no_pos "sleekengine.check_unsat" *) false, None
      | _ -> loop_helper fs
    in
    r,fail_of


let check_imply_w_norm prog non_tough_check ante_hg conseq_hg=
  let is_implied, vertex_map = Hgraph.check_homomorphism non_tough_check conseq_hg ante_hg in
  is_implied


(*
  find the residue syntactically
*)
let prune_match ante=
  ante
