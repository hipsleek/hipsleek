#include "xdebug.cppo"
open VarGen
(*this file contains all unitilise for shape analysis.
it is used mainly by infer.infer_collect_hp and sa.infer_hp
*)

open Globals
open Gen

module DD = Debug
module CF = Cformula
module CFU = Cfutil
module CP = Cpure
module MCP = Mcpure
module C = Cast
module I = Iast
module CEQ = Checkeq
module TP = Tpdispatcher
module SY_CEQ = Syn_checkeq

exception SA_NO_BASE_CASE of (CP.spec_var * (CP.spec_var list) * (CF.formula list)) (*hp without base case*)

(*hp_name * args * unk_args * condition * lhs * guard* rhs *)
type par_def_w_name =  CP.spec_var * CP.spec_var list * CP.spec_var list * CP.formula * (CF.formula option) * (CF.formula option) *
      (CF.formula option)

let check_stricteq_h_fomula = SY_CEQ.check_stricteq_h_fomula
let check_relaxeq_formula = SY_CEQ.check_relaxeq_formula
let checkeq_pair_formula = SY_CEQ.checkeq_pair_formula
let checkeq_formula_list = SY_CEQ.checkeq_formula_list
let checkeq_formula_list_w_args = SY_CEQ.checkeq_formula_list_w_args

(* let check_equiv = ref (fun (iprog: I.prog_decl) (prog: C.prog_decl) (svl: CP.spec_var list) (proof_traces: (CF.formula * CF.formula) list) (need_lemma:bool) *)
(*   (fs1: CF.formula) (fs2: CF.formula) -> *)
(*     let () = print_endline "sau printer has not been initialize 1" in *)
(* false ) *)

(* let check_equiv_list = ref (fun (iprog: I.prog_decl) (prog: C.prog_decl) (svl: CP.spec_var list) (pr_proof_traces: (CF.formula * CF.formula) list) *)
(*   (need_lemma:bool) (fs1: CF.formula list) (fs2: CF.formula list) -> *)
(*     let () = print_endline "sau printer has not been initialize" in *)
(* false ) *)

let is_rec_pardef (hp,_,f,_)=
  let hps = CF.get_hp_rel_name_formula f in
  (CP.mem_svl hp hps)

let string_of_hp_rel_def = Cprinter.string_of_hp_rel_def 
 
let string_of_par_def_w_name pd=
  let pr1 = !CP.print_sv in
  let pr4 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr5 = !CP.print_formula in
  let pr3 = fun x -> match x with
    | None -> "None"
    | Some f -> pr2 f
  in
  let pr = pr_hepta pr1 pr4 pr4 pr5 pr3 Cprinter.prtt_string_of_formula_opt pr3 in
  pr pd


let string_of_par_def_w_name_short pd=
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = Cprinter.prtt_string_of_formula in
  let pr4 og = match og with
    | None -> ""
    | Some hf -> Cprinter.prtt_string_of_formula hf
  in
  let pr = pr_penta pr1 pr2 pr4 pr3 pr2 in
  pr pd

(**=================================**)

let close_def defs (v1,v2)=
  if (CP.is_null_const v1) || (CP.is_null_const v2) then defs
  else if CP.mem_svl v1 defs then (CP.remove_dups_svl defs@[v2])
  else if CP.mem_svl v2 defs then (CP.remove_dups_svl defs@[v1])
  else (defs)

let close_def defs (v1,v2) =
  let pr = !CP.print_sv in
  let pr_pair = pr_pair pr pr in
  let p_svl = !CP.print_svl in
  Debug.no_2 "SAU:close_def" p_svl pr_pair p_svl close_def defs (v1,v2) 

  (* else *)
  (*   let b1 = CP.mem_svl v1 defs in *)
  (*   let b2 = CP.mem_svl v2 defs in *)
  (*   match b1,b2 with *)
  (*     | false,false *)
  (*     | true,false -> (defs@[v2]) *)

(*close_def is not precise if eqs= x=y & y=z and x=t, svl0=[t], and first examine x=y*)

(* let find_close svl0 eqs0= *)
(*   let rec find_match svl ls_eqs rem_eqs= *)
(*     match ls_eqs with *)
(*       | [] -> svl,rem_eqs *)
(*       | (sv1,sv2)::ss-> *)
(*             let b1 = CP.mem_svl sv1 svl in *)
(*             let b2 = CP.mem_svl sv2 svl in *)
(*             let new_m,new_rem_eqs= *)
(*               match b1,b2 with *)
(*                 | false,false -> [],[(sv1,sv2)] *)
(*                 | true,false -> ([sv2],[]) *)
(*                 | false,true -> ([sv1],[]) *)
(*                 | true,true -> ([],[]) *)
(*             in *)
(*             find_match (svl@new_m) ss (rem_eqs@new_rem_eqs) *)
(*   in *)
(*   let rec loop_helper svl eqs= *)
(*     let new_svl,rem_eqs = find_match svl eqs [] in *)
(*     if List.length new_svl > List.length svl then *)
(*       loop_helper new_svl rem_eqs *)
(*     else new_svl *)
(*   in *)
(*   loop_helper svl0 eqs0 *)

let find_close_f svl0 f=
  let ( _,mf,_,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mf)in
  CF.find_close svl0 eqs

let rec partition_subst_hprel ss r=
  match ss with
    | [] -> r
    | (sv1,sv2)::tl ->
          let part,rem = List.partition (fun (_, sv4) -> CP.eq_spec_var sv2 sv4) tl in
          let part_svl = fst (List.split part) in
          partition_subst_hprel rem r@[(sv1::part_svl, sv2)]

(*List.combine but ls2 >= ls1*)
let rec combine_length_neq_x ls1 ls2 res=
  match ls1,ls2 with
    | [],[] -> res
    | [],sv2::_ -> res
    | sv1::tl1,sv2::tl2 -> combine_length_neq_x tl1 tl2 (res@[sv1,sv2])
    | _ -> report_error no_pos "sau.combine_length_neq"

let combine_length_neq ls1 ls2 res=
  let pr1= !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_2 "combine_length_neq" pr1 pr1 pr2
      (fun _ _ -> combine_length_neq_x ls1 ls2 res) ls1 ls2


let rec combine_multiple_length ls1 orig_args=
  let rec helper ls1 ls2 res=
    match ls1,ls2 with
      | [],[] -> res
      | [],sv2::_ -> res
      | sv1::tl1,sv2::tl2 -> helper tl1 tl2 (res@[sv1,sv2])
      | sv::_,[] -> helper ls1 orig_args res
  in
  helper ls1 orig_args []

let rec is_empty_f f0= CF.is_empty_f f0
  (* let rec helper f= *)
  (*   match f with *)
  (*     | CF.Base fb -> *)
  (*           (CF.is_empty_heap fb.CF.formula_base_heap) && *)
  (*               (CP.isConstTrue (MCP.pure_of_mix fb.CF.formula_base_pure)) *)
  (*     | CF.Exists _ -> let _, base_f = CF.split_quantifiers f in *)
  (*       is_empty_f base_f *)
  (*     | CF.Or orf -> (helper orf.CF.formula_or_f1) && (helper orf.CF.formula_or_f2) *)
  (* in *)
  (* helper f0 *)

let is_empty_base fb=
  (CF.is_empty_heap fb.CF.formula_base_heap) &&
            (CP.isConstTrue (MCP.pure_of_mix fb.CF.formula_base_pure))


let is_empty_wop opf=
  match opf with
    | None -> false
    | Some f ->  is_empty_f f

let rec is_only_xpure_f f=
   match f with
    | CF.Base fb ->
          let p = (MCP.pure_of_mix fb.CF.formula_base_pure) in
          let ps =CP.split_conjunctions p in
          (CF.is_emp_heap fb.CF.formula_base_heap) &&
            (CP.isConstTrue p || (List.for_all CP.is_xpure ps))
    | CF.Exists _ -> let _, base1 = CF.split_quantifiers f in
                     CF.is_unknown_f base1
    | _ -> report_error no_pos "SAU.is_only_xpure_f: not handle yet"

(* let rec get_pos_x ls n sv= *)
(*   match ls with *)
(*     | [] -> report_error no_pos "sau.get_pos: impossible 1" *)
(*     | sv1::rest -> if CP.eq_spec_var sv sv1 then n *)
(*       else get_pos_x rest (n+1) sv *)

(* let get_pos ls n sv= *)
(*   let pr1 = !CP.print_svl in *)
(*   Debug.no_3 "sau.get_pos" pr1 string_of_int !CP.print_sv string_of_int *)
(*       (fun _ _ _ -> get_pos_x ls n sv) *)
(*       ls n sv *)

let get_pos ls n sv= Cfutil.get_pos ls n sv

let rec get_all_locs_helper ls n svl res=
  match ls with
    | [] -> res
    | sv1::rest ->
          let n_res = if CP.mem_svl sv1 svl then (res@[n]) else res in
          get_all_locs_helper rest (n+1) svl n_res

let get_all_locs ls need_svl = get_all_locs_helper ls 0 need_svl []

(*for drop hp args*)
(* let rec retrieve_args_from_locs_helper args locs index res= *)
(*   match args with *)
(*     | [] -> res *)
(*     | a::ss -> if List.mem index locs then *)
(*           retrieve_args_from_locs_helper ss locs (index+1) (res@[a]) *)
(*         else retrieve_args_from_locs_helper ss locs (index+1) res *)

let retrieve_args_from_locs args locs= Cfutil.retrieve_args_from_locs args locs
  (* retrieve_args_from_locs_helper args locs 0 [] *)

let eq_spec_var_order_list = CP.eq_spec_var_order_list
  (* match l1,l2 with *)
  (*   |[],[] -> true *)
  (*   | v1::ls1,v2::ls2 -> *)
  (*       if CP.eq_spec_var v1 v2 then *)
  (*         eq_spec_var_order_list ls1 ls2 *)
  (*       else false *)
  (*   | _ -> false *)

let select_dnode = CF.select_dnode

let select_vnode = CF.select_vnode

let check_hp_arg_eq (hp1, args1) (hp2, args2)= CF.check_hp_arg_eq (hp1, args1) (hp2, args2)

let check_neq_hpargs id ls= CF.check_neq_hpargs id ls

let check_nbelongsto_dnode = CF.check_nbelongsto_dnode

let check_nbelongsto_vnode = CF.check_nbelongsto_vnode

let eq_two_int_order_list l10 l20=
  let rec helper l1 l2=
    match l1,l2 with
      |[],[] -> true
    | v1::ls1,v2::ls2 ->
        if v1 = v2 then
          helper ls1 ls2
        else false
    | _ -> false
  in
  helper l10 l20

let check_hp_locs_eq (hp1, locs1) (hp2, locs2)=
  ((CP.eq_spec_var hp1 hp2) && (eq_two_int_order_list locs1 locs2))

let check_simp_hp_eq (hp1, _) (hp2, _)=
   (CP.eq_spec_var hp1 hp2)

(* let add_raw_hp_rel_x prog is_pre is_unknown unknown_ptrs pos= *)
(*   if (List.length unknown_ptrs > 0) then *)
(*     let hp_decl = *)
(*       { Cast.hp_name = (if is_unknown then Globals.unkhp_default_prefix_name else *)
(*         if is_pre then Globals.hp_default_prefix_name else hppost_default_prefix_name) *)
(*         ^ (string_of_int (Globals.fresh_int())); *)
(*       Cast.hp_part_vars = []; *)
(*       Cast.hp_root_pos = 0; (\*default, reset when def is inferred*\) *)
(*       Cast.hp_vars_inst = unknown_ptrs; *)
(*       Cast.hp_is_pre = is_pre; *)
(*       Cast.hp_formula = CF.mkBase CF.HEmp (MCP.mkMTrue pos) CF.TypeTrue (CF.mkTrueFlow()) [] pos;} *)
(*     in *)
(*     let unk_args = (fst (List.split hp_decl.Cast.hp_vars_inst)) in *)
(*     prog.Cast.prog_hp_decls <- (hp_decl :: prog.Cast.prog_hp_decls); *)
(*     (\* PURE_RELATION_OF_HEAP_PRED *\) *)
(*     let p_hp_decl = Predicate.generate_pure_rel hp_decl in *)
(*     let () = prog.C.prog_rel_decls <- (p_hp_decl::prog.C.prog_rel_decls) in *)
(*     Smtsolver.add_hp_relation hp_decl.Cast.hp_name unk_args hp_decl.Cast.hp_formula; *)
(*     let hf = *)
(*       CF.HRel (CP.SpecVar (HpT,hp_decl.Cast.hp_name, Unprimed),  *)
(*                List.map (fun sv -> CP.mkVar sv pos) unk_args, *)
(*       pos) *)
(*     in *)
(*     let () = x_tinfo_hp (add_str "define: " Cprinter.string_of_hp_decl) hp_decl pos in *)
(*     DD.ninfo_zprint (lazy (("       gen hp_rel: " ^ (Cprinter.string_of_h_formula hf)))) pos; *)
(*     (hf, CP.SpecVar (HpT,hp_decl.Cast.hp_name, Unprimed)) *)
(*   else report_error pos "sau.add_raw_hp_rel: args should be not empty" *)

let add_raw_hp_rel prog is_pre is_unknown unknown_args pos= Cast.add_raw_hp_rel prog is_pre is_unknown unknown_args pos
(*   let pr1 = pr_list (pr_pair !CP.print_sv print_arg_kind) in *)
(*   let pr2 = Cprinter.string_of_h_formula in *)
(*   let pr4 (hf,_) = pr2 hf in *)
(*   Debug.no_1 "add_raw_hp_rel" pr1 pr4 *)
(*       (fun _ -> add_raw_hp_rel_x prog is_pre is_unknown unknown_args pos) unknown_args *)

let add_raw_rel prog args pos=
  let rel_decl =
    { Cast.rel_name = Globals.rel_default_prefix_name  ^ (string_of_int (Globals.fresh_int()));
    Cast.rel_vars = args;
    Cast.rel_formula =(CP.mkTrue pos);}
  in
  let () = prog.Cast.prog_rel_decls <- (rel_decl :: prog.Cast.prog_rel_decls) in
  let _= Smtsolver.add_relation rel_decl.Cast.rel_name rel_decl.Cast.rel_vars rel_decl.Cast.rel_formula in
  let _= Z3.add_relation rel_decl.Cast.rel_name rel_decl.Cast.rel_vars rel_decl.Cast.rel_formula in
  CP.mkRel_sv rel_decl.Cast.rel_name

let fresh_raw_hp_rel prog is_pre is_unk hp pos =
  try
    let hp_decl = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
    let args_w_i = hp_decl.Cast.hp_vars_inst in
    let nhf, nhp = add_raw_hp_rel prog is_pre is_unk args_w_i pos in
    nhp
  with _ -> report_error pos "SAU.fresh_raw_hp_rel: where r u?"

let find_close_hpargs_x hpargs eqs0=
  let rec assoc_l ls hp=
    match ls with
      | [] -> []
      | (hp1,args1)::tl -> if CP.eq_spec_var hp hp1 then args1
          else assoc_l tl hp
  in
  let rec helper rem_eqs hpargs0=
    match rem_eqs with
      | [] -> hpargs0
      | (hp1,hp2)::tl -> begin
          let args1 = assoc_l hpargs0 hp1 in
          let args2 = assoc_l hpargs0 hp2 in
          let new_hpargs=
            match args1, args2 with
              | [],[] -> []
              | [],_ -> [(hp1,args2)]
              | _,[] -> [(hp2,args1)]
              | _ -> []
          in
          helper tl (hpargs0@new_hpargs)
      end
  in
  let close_hpargs = helper eqs0 hpargs in
  (Gen.BList.remove_dups_eq check_simp_hp_eq close_hpargs)

let find_close_hpargs hpargs eqs0=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_2 "find_close_hpargs" pr1 pr2 pr1
      (fun _ _ -> find_close_hpargs_x hpargs eqs0) hpargs eqs0

let check_hp_args_imply (hp1, args1) (hp2, args2)=
  ((CP.eq_spec_var hp1 hp2) && (CP.diff_svl args1 args2 = []))

let elim_eq_shorter_hpargs_x ls=
  let rec loop_helper cur_ls res=
    match cur_ls with
      | [] -> res
      | hpargs::ss ->
          if List.exists (check_hp_args_imply hpargs) res then
            loop_helper ss res
          else loop_helper ss (res@[hpargs])
  in
  let sort_fn (_,args1) (_,args2)=
    (List.length args2) - (List.length args1)
  in
  let sorted_ls = List.sort sort_fn ls in
  let filterd_ls = loop_helper sorted_ls [] in
  (Gen.BList.remove_dups_eq check_simp_hp_eq filterd_ls)

let elim_eq_shorter_hpargs ls=
  let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_1 "elim_eq_shorter_hpargs" pr pr
      (fun _ -> elim_eq_shorter_hpargs_x ls) ls

let refine_full_unk partial_hp_args_locs poss_full_hp_args_locs=
  let partial_hp_locs = List.map (fun (a,_,c) -> (a,c)) partial_hp_args_locs in
  let rec helper poss_full_ls res=
    match poss_full_ls with
      |[] -> res
      | (hp,args,locs)::lss ->
          try
              let locs1 = List.assoc hp partial_hp_locs in
              if (List.length locs1) = (List.length locs) then
                helper lss (res@[(hp,args,locs)])
              else helper lss res
          with Not_found ->
              report_error no_pos "sau.refine_full_unk"
  in
  helper poss_full_hp_args_locs []

(*OLD: todo remove*)
let refine_full_unk2 partial_hp_locs poss_full_hp_args_locs=
  let rec helper poss_full_ls res=
    match poss_full_ls with
      |[] -> res
      | (hp,args,locs)::lss ->
          try
              let locs1 = List.assoc hp partial_hp_locs in
              if (List.length locs1) = (List.length locs) then
                helper lss (res@[(hp,args,locs)])
              else helper lss res
          with Not_found ->
              report_error no_pos "sau.refine_full_unk"
  in
  helper poss_full_hp_args_locs []
(***********************************)

let mkHRel hp args pos=
  let eargs = List.map (fun x -> (CP.mkVar x pos)) args in
   ( CF.HRel (hp, eargs, pos))

let mkHRel_f hp args pos=
  let hf = mkHRel hp args pos in
  CF.formula_of_heap hf pos

let rec get_hdnodes (f: CF.formula)=
  match f with
    | CF.Base fb ->
        get_hdnodes_hf fb.CF.formula_base_heap
    | CF.Exists fe ->
        get_hdnodes_hf fe.CF.formula_exists_heap
    | _ -> report_error no_pos "SAU. get_hdnodes: not handle yet"

and get_hdnodes_hf (hf: CF.h_formula) =
  let pr = Cprinter.string_of_h_formula in 
  Debug.no_1 "get_hdnodes_hf" pr (pr_list pr_none) get_hdnodes_hf_x hf

and get_hdnodes_hf_x (hf: CF.h_formula) = match hf with
  | CF.DataNode hd -> [hd]
  | CF.Conj {CF.h_formula_conj_h1 = h1; CF.h_formula_conj_h2 = h2} 
  | CF.Star {CF.h_formula_star_h1 = h1; CF.h_formula_star_h2 = h2} 
  | CF.Phase {CF.h_formula_phase_rd = h1; CF.h_formula_phase_rw = h2} 
      -> (get_hdnodes_hf h1)@(get_hdnodes_hf h2)
  | _ -> []

let get_hdnodes_basef fb=
  get_hdnodes_hf fb.CF.formula_base_heap

let rec get_h_node_args (f: CF.formula)=
  match f with
    | CF.Base fb ->
        get_h_node_args_hf fb.CF.formula_base_heap
    | CF.Exists fe ->
        get_h_node_args_hf fe.CF.formula_exists_heap
    | _ -> report_error no_pos "SAU. get_hdnodes: not handle yet"

and get_h_node_args_hf (hf: CF.h_formula) = match hf with
  | CF.DataNode hd -> hd.CF.h_formula_data_node, hd.CF.h_formula_data_arguments
  | CF.ViewNode hv -> hv.CF.h_formula_view_node, hv.CF.h_formula_view_arguments
  | _ -> report_error no_pos "get_h_node_args_hf: unmatch rhs should be a node or a view only"

and get_h_node_cont_args_hf cprog (hf: CF.h_formula) = match hf with
  | CF.DataNode hd -> hd.CF.h_formula_data_node, hd.CF.h_formula_data_arguments
  | CF.ViewNode hv ->
        hv.CF.h_formula_view_node, List.filter (fun sv -> not (CP.eq_spec_var sv hv.CF.h_formula_view_node)) (Cast.look_up_cont_args hv.CF.h_formula_view_arguments hv.CF.h_formula_view_name
            cprog.Cast.prog_view_decls)
  | _ -> report_error no_pos "get_h_node_args_hf: unmatch rhs should be a node or a view only"

let rec get_data_view_hrel_vars_formula f=
  let rec helper f0=
    match f0 with
      | CF.Base fb -> get_data_view_hrel_vars_bformula fb
      | CF.Exists fe -> get_data_view_hrel_vars_h_formula fe.CF.formula_exists_heap
      | CF.Or orf  -> (helper orf.CF.formula_or_f1)@ (helper orf.CF.formula_or_f2)
  in
  helper f

and get_data_view_hrel_vars_bformula bf=
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
      | CF.ThreadNode ht -> [ht.CF.h_formula_thread_node] (*TOCHECK*)
      | CF.Hole _ | CF.FrmHole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp | CF.HVar _ -> []
      | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> Error.report_no_pattern()
  in
  helper hf

let rec drop_get_hrel_x f=
  match f with
    | CF.Base fb ->
        let new_hf, hrels = drop_get_hrel_h_formula fb.CF.formula_base_heap in
        (CF.Base {fb with CF.formula_base_heap= new_hf}, hrels)
    | CF.Exists fe ->
          let qvars, base1 = CF.split_quantifiers f in
          let nf,r = drop_get_hrel_x base1 in
          (CF.add_quantifiers qvars nf,r)
    | _ -> report_error no_pos "SAU.drop_get_hrel: SHOULD NOT OR"

and drop_get_hrel f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_1 "drop_get_hrel" pr1 (pr_pair pr1 pr2)
      (fun _ -> drop_get_hrel_x f) f

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
      | CF.ThreadNode ht -> (hf0,[])
      | CF.HRel (sv, eargs, _) -> (CF.HEmp,
                                   [(sv,List.concat (List.map CP.afv eargs))])
      | CF.Hole _ | CF.FrmHole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp | CF.HVar _ -> (hf0,[])
      | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> Error.report_no_pattern()
  in
  helper hf


let rec drop_data_hrel_except_x dn_names hpargs f=
  match f with
    | CF.Base fb ->
        let new_hf = drop_data_hrel_except_hf dn_names hpargs fb.CF.formula_base_heap in
        let new_p = CP.filter_var_new (MCP.pure_of_mix fb.CF.formula_base_pure) (dn_names@hpargs) in
        (CF.Base {fb with
            CF.formula_base_heap= new_hf;
            CF.formula_base_pure = MCP.mix_of_pure new_p;
        })
    | _ -> report_error no_pos "SAU.drop_get_hrel: not handle yet"

and drop_data_hrel_except dn_names hpargs f=
  let pr1=Cprinter.prtt_string_of_formula in
  Debug.no_3 "drop_data_hrel_except" !CP.print_svl !CP.print_svl pr1 pr1
      (fun _ _ _ -> drop_data_hrel_except_x dn_names hpargs f) dn_names hpargs f

and drop_data_hrel_except_hf dn_names hpargs hf=
  let rec helper hf0=
    match hf0 with
      | CF.Star {CF.h_formula_star_h1 = hf1;
                 CF.h_formula_star_h2 = hf2;
                 CF.h_formula_star_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          (match n_hf1,n_hf2 with
            | (CF.HEmp,CF.HEmp) -> (CF.HEmp)
            | (CF.HEmp,_) -> (n_hf2)
            | (_,CF.HEmp) -> (n_hf1)
            | _ -> (CF.Star {CF.h_formula_star_h1 = n_hf1;
			                CF.h_formula_star_h2 = n_hf2;
			                CF.h_formula_star_pos = pos})
          )
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
		          CF.h_formula_conj_h2 = hf2;
		          CF.h_formula_conj_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          CF.Conj { CF.h_formula_conj_h1 = n_hf1;
		            CF.h_formula_conj_h2 = n_hf2;
		            CF.h_formula_conj_pos = pos}
      | CF.Phase { CF.h_formula_phase_rd = hf1;
		           CF.h_formula_phase_rw = hf2;
		           CF.h_formula_phase_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          CF.Phase { CF.h_formula_phase_rd = n_hf1;
		             CF.h_formula_phase_rw = n_hf2;
		             CF.h_formula_phase_pos = pos}
      | CF.DataNode hd -> if CP.mem_svl hd.CF.h_formula_data_node dn_names then
            hf0 else CF.HEmp
      | CF.ViewNode hv -> hf0
      | CF.ThreadNode ht -> if CP.mem_svl ht.CF.h_formula_thread_node dn_names then
            hf0 else CF.HEmp
      | CF.HRel (_, eargs, _) ->
          let args1 = List.concat (List.map CP.afv eargs) in
          if CP.diff_svl args1 hpargs = [] then hf0 else CF.HEmp
      | CF.Hole _ | CF.FrmHole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp  | CF.HVar _ -> hf0
      | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> report_error no_pos "CF.drop_data_hrel_except_hf: not handle yet"
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

let get_root_ptrs prog hf0=
  let rec helper hf=
    match hf with
      | CF.Star {CF.h_formula_star_h1 = hf1;
                 CF.h_formula_star_h2 = hf2;}
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
		          CF.h_formula_conj_h2 = hf2;}
      | CF.Phase { CF.h_formula_phase_rd = hf1;
		           CF.h_formula_phase_rw = hf2;} ->
          (helper hf1)@(helper hf2)
      | CF.DataNode hd ->[hd.CF.h_formula_data_node]
      | CF.ViewNode hv -> [hv.CF.h_formula_view_node]
      | CF.HRel (hp, eargs, _) ->
            let hp_name= CP.name_of_spec_var hp in
            let hprel = Cast.look_up_hp_def_raw prog.C.prog_hp_decls hp_name in
            let ss = List.combine eargs hprel.C.hp_vars_inst in
            let root_eargs = List.fold_left (fun ls (e,(_,i)) -> if i = I then ls@[e] else ls ) [] ss in
            List.fold_left (fun ls e -> ls@(CP.afv e)) [] root_eargs
      | _ -> []
  in
  helper hf0

let partition_hp_args_x prog hp args=
  let hp_name= CP.name_of_spec_var hp in
  let hprel = Cast.look_up_hp_def_raw prog.C.prog_hp_decls hp_name in
  let ss = List.combine args hprel.C.hp_vars_inst in
  let i_args, ni_args = List.fold_left (fun (ls1,ls2) (sv,(_,i)) ->
      if i = I then (ls1@[(sv,I)],ls2) else (ls1,ls2@[(sv,NI)])
  ) ([],[]) ss
  in
  (i_args, ni_args)

let partition_hp_args prog hp args=
  let pr1 = (pr_list (pr_pair !CP.print_sv print_arg_kind)) in
  Debug.no_2 "partition_hp_args" !CP.print_sv !CP.print_svl (pr_pair pr1 pr1)
      (fun _ _ -> partition_hp_args_x prog hp args) hp args

let get_hp_args_inst prog hp args=
  let hp_name= CP.name_of_spec_var hp in
  let hprel = Cast.look_up_hp_def_raw prog.C.prog_hp_decls hp_name in
  let ss = List.combine args hprel.C.hp_vars_inst in
  let args_inst = List.fold_left (fun ls (e,(_,i)) -> if i = I then ls@[e] else ls ) [] ss in
  args_inst

let get_pos_of_hp_args_inst prog hp=
  let rec get_pos rem_args n res=
    match rem_args with
      | [] -> res
      | (sv,i)::rest -> let n_res = if i=I then (res@[n]) else res in
        get_pos rest (n+1) n_res
  in
  let hp_name= CP.name_of_spec_var hp in
  let hprel = Cast.look_up_hp_def_raw prog.C.prog_hp_decls hp_name in
  get_pos hprel.C.hp_vars_inst 0 []

let rec cmp_inst ls1 ls2 =
  match ls1,ls2 with
    | [], [] -> true
    | i1::rest1,i2::rest2 -> if i1=i2 then cmp_inst rest1 rest2
      else false
    | _ -> false

let rec cmp_subsume_inst ls1 ls2 =
  match ls1,ls2 with
    | [], _ -> true
    | i1::rest1,i2::rest2 -> if i1=i2 then cmp_inst rest1 rest2
      else false
    | _ -> false

let get_inst_hp_args prog hp=
  let hp_name= CP.name_of_spec_var hp in
  let hprel = Cast.look_up_hp_def_raw prog.C.prog_hp_decls hp_name in
  snd (List.split hprel.C.hp_vars_inst)

let rec drop_hrel_match_args f args=
  match f with
    | CF.Base fb -> let nfb = drop_hrel_match_args_hf fb.CF.formula_base_heap args in
        (CF.Base {fb with CF.formula_base_heap =  nfb;})
    | CF.Or orf -> let nf1 =  drop_hrel_match_args orf.CF.formula_or_f1 args in
                let nf2 =  drop_hrel_match_args orf.CF.formula_or_f2 args in
       ( CF.Or {orf with CF.formula_or_f1 = nf1;
                CF.formula_or_f2 = nf2;})
    | CF.Exists fe ->
        let qvars, base1 = CF.split_quantifiers f in
        let nf = drop_hrel_match_args base1 args in
        CF.add_quantifiers qvars nf
        (* (CF.Exists {fe with CF.formula_exists_heap = nfe ;}) *)

and drop_hrel_match_args_hf hf0 args=
  let rec helper hf=
    match hf with
      | CF.Star {CF.h_formula_star_h1 = hf1;
              CF.h_formula_star_h2 = hf2;
              CF.h_formula_star_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          let newf =
            (match n_hf1,n_hf2 with
              | (CF.HEmp,CF.HEmp) -> CF.HEmp
              | (CF.HEmp,_) -> n_hf2
              | (_,CF.HEmp) -> n_hf1
              | _ -> (CF.Star {CF.h_formula_star_h1 = n_hf1;
                            CF.h_formula_star_h2 = n_hf2;
                            CF.h_formula_star_pos = pos})
            ) in
          (newf)
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
               CF.h_formula_conj_h2 = hf2;
               CF.h_formula_conj_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          (CF.Conj { CF.h_formula_conj_h1 = n_hf1;
                  CF.h_formula_conj_h2 = n_hf2;
                  CF.h_formula_conj_pos = pos})
      | CF.Phase { CF.h_formula_phase_rd = hf1;
                CF.h_formula_phase_rw = hf2;
                CF.h_formula_phase_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          (CF.Phase { CF.h_formula_phase_rd = n_hf1;
                   CF.h_formula_phase_rw = n_hf2;
                   CF.h_formula_phase_pos = pos})
      | CF.DataNode hd -> (hf)
      | CF.ViewNode hv -> (hf)
      | CF.ThreadNode ht -> (hf)
      | CF.HRel (_,eargs1,_) ->
          let args1 = List.fold_left List.append [] (List.map CP.afv eargs1) in
          if eq_spec_var_order_list args args1 then (CF.HEmp)
          else (hf)
      | CF.Hole _ | CF.FrmHole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp | CF.HVar _ -> (hf)
      | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> report_error no_pos "SAU.drop_hrel_match_args_hf: not handle yet"
  in
  helper hf0

(*==============*)
(*for unk hps*)
(*check whether args of an is in keep_ptrs*)
let get_intersect_hps keep_ptrs (hp, args)=
  (*may need closed*)
  Debug.ninfo_zprint (lazy ((" keep_ptrs: "^ (!CP.print_svl keep_ptrs)))) no_pos;
  Debug.ninfo_zprint (lazy ((" args: "^ (!CP.print_svl args)))) no_pos;
  let interse = CP.intersect_svl args keep_ptrs in
  if interse = [] then [] else [hp]

let check_neq_hrelnode id ls= CF.check_neq_hrelnode id ls

let select_hrel =  CP.mem_svl

let select_hpargs id ls= (Gen.BList.mem_eq check_hp_arg_eq id ls)

let select_subsumehpargs (hp0,args0) ls= (List.exists (fun (hp1,args1) ->
    CP.eq_spec_var hp0 hp1 && CP.diff_svl args0 args1 = [])
    ls)

let look_up_dups_node_x prog hd_nodes hv_nodes lhs_args all_keep_svl r_keep_svl=
  let get_rel_lsvl sv=
    let ptrs = CF.look_up_ptr_args_one_node prog hd_nodes hv_nodes sv in
    (sv, CP.intersect_svl (sv::ptrs) lhs_args, ptrs<>[])
  in
  let rec group_dups rem_pars grps=
    match rem_pars with
      | [] -> grps
      | (sv, lhs_svl, is_node)::rest ->
            let grp,rest1 = List.partition (fun (_,lhs_svl1,_) -> CP.intersect_svl lhs_svl lhs_svl1 <> []) rest in
            group_dups rest1 (grps@[(sv, lhs_svl, is_node)::grp])
  in
  let prs = List.map get_rel_lsvl r_keep_svl in
  let prs1 = List.filter (fun (_,svl,_) -> svl <> []) prs in
  let grps = group_dups prs1 [] in
  let dups_svl = List.fold_left (fun res grp ->
      if List.length grp <=1 then res else
        List.fold_left (fun res1 (sv,_, is_node) -> if is_node then (res1@[sv]) else res1) [] grp
  ) [] grps
  in
  CP.diff_svl all_keep_svl dups_svl

(*remove sv in rhs: its arguments exists both in LHS pred and RHS pred*)
let look_up_dups_node prog hd_nodes hv_nodes lhs_args all_keep_svl r_keep_svl=
  let pr1 = !CP.print_svl in
  Debug.no_2 "look_up_dups_node" pr1 pr1 pr1
      (fun _ _ -> look_up_dups_node_x prog hd_nodes hv_nodes lhs_args all_keep_svl r_keep_svl)
      lhs_args r_keep_svl

let rec lookup_undef_args args undef_args def_ptrs=
  match args with
    | [] -> undef_args
    | a::ax -> if CP.mem_svl a def_ptrs then (*defined: omit*)
          lookup_undef_args ax undef_args def_ptrs
        else (*undefined *)
          lookup_undef_args ax (undef_args@[a]) def_ptrs

(*=======utilities for infer_collect_hp_rel=======*)
(*defined pointers list *
  for recursive constraint(HP name *
 parameter name list)*)
(* todo: how about null? is it defined? *)
let rec find_defined_pointers_raw prog f=
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
  let ( _,mix_f,_,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mix_f) in
  let eqNulls = CP.remove_dups_svl ( MCP.get_null_ptrs mix_f) in
  (*defined vars=  + null + data + view*)
  let def_vs = (* (eqNulls) @ *) (List.map (fun hd -> hd.CF.h_formula_data_node) hds)
   @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) in
  (*find closed defined pointers set*)
  (* let def_vs0 = CP.remove_dups_svl def_vs in *)
  let def_vs_wo_args = CP.remove_dups_svl ((List.fold_left close_def def_vs eqs)) in
  (def_vs_wo_args, hds, hvs, hrs, eqs,eqNulls)

and check_node_args_defined prog def_svl hd_nodes hv_nodes dn_name=
  let arg_svl = CF.look_up_ptr_args_one_node prog hd_nodes hv_nodes dn_name in
  (* DD.info_zprint (lazy (("  arg_svl" ^ (!CP.print_svl arg_svl)))) no_pos; *)
  (* DD.info_zprint (lazy (("  def_svl" ^ (!CP.print_svl def_svl)))) no_pos; *)
  if arg_svl = [] then false else
    let diff_svl = Gen.BList.difference_eq CP.eq_spec_var arg_svl def_svl in
  (* DD.info_zprint (lazy (("  diff_svl" ^ (!CP.print_svl diff_svl)))) no_pos; *)
    if diff_svl = [] then true
    else false

and find_defined_pointers_after_preprocess prog def_vs_wo_args hds hvs hrs eqs eqNulls predef_ptrs=
  let tmp = def_vs_wo_args in
  let predef = CF.find_close (def_vs_wo_args@predef_ptrs) eqs in
  (* DD.info_zprint (lazy (("   defined raw " ^(!CP.print_svl tmp)))) no_pos; *)
  let def_vs = List.filter (check_node_args_defined prog predef hds hvs) tmp in
  (*(HP name * parameter name list)*)
  let hp_paras = List.map
                (fun (id, exps, _) -> (id, List.concat (List.map CP.afv exps)))
                hrs in
  (def_vs@eqNulls, hp_paras, hds, hvs, eqs)

and find_defined_pointers_x prog f predef_ptrs=
  let (def_vs, hds, hvs, hrs, eqs,eqNulls) = find_defined_pointers_raw prog f in
  find_defined_pointers_after_preprocess prog def_vs hds hvs hrs eqs eqNulls predef_ptrs

and find_defined_pointers prog f predef_ptrs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv pr1) in
  (* let pr3 = fun x -> Cprinter.string_of_h_formula (CF.HRel x) in *)
  let pr4 = fun (a1, a2, _, _, _) ->
      let pr = pr_pair pr1 pr2 in pr (a1,a2)
  in
  Debug.no_2 "find_defined_pointers" Cprinter.prtt_string_of_formula pr1 pr4
      (fun _ _ -> find_defined_pointers_x prog f predef_ptrs) f predef_ptrs

let get_defined_eqs_x f=
  (*******INTERNAL******)
   let rec look_up eqs args r=
    match eqs with
      | [] -> (CP.remove_dups_svl  r)
      | (sv1,sv2)::rest -> if CP.diff_svl [sv1;sv2] args = [] then
          look_up rest args (r@[sv1;sv2])
        else look_up rest args r
  in
  (*smart_subst always gives explicit eqs for args*)
  let extract_defined_eq r (_,args) eqs=
    (* if List.length args = 2 then *)
      r@(look_up eqs args [])
    (* else r *)
  in
  (****END*********)
  let ( _,mix_f,_,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mix_f) in
  let hpargs = CF.get_HRels_f f in
  let def_eqs = List.fold_left (fun r hp_args -> extract_defined_eq r hp_args eqs) [] hpargs in
  def_eqs

let get_defined_eqs f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = !CP.print_svl in
  Debug.no_1 "get_defined_eqs" pr1 pr2
      (fun _ -> get_defined_eqs_x f) f

let get_raw_defined_w_pure_x prog predef lhs rhs=
  let rec helper f eqs=
    match f with
      | CF.Base fb ->
          let def_raw,_,_,_,leqs,eqNulls = find_defined_pointers_raw prog f in
          let def_raw1 = CP.remove_dups_svl (def_raw@eqNulls) in
          (def_raw1,leqs)
      | CF.Exists _ ->
            let qvars, base1 = CF.split_quantifiers f in
            let svl = helper base1 [] in
            (* (CF.add_quantifiers qvars nf) *)
            svl
      | _ -> report_error no_pos "sau.get_raw_defined_w_pure: not handle yet"
  in
  let lsvl,leqs = helper lhs [] in
  let rsvl,reqs = helper rhs leqs in
  let eqs = (leqs@reqs) in
  let svl = lsvl@rsvl@predef in
  let svl1 = if eqs = [] then svl else
    (List.fold_left close_def svl eqs)
  in
  let svl2 = (CP.remove_dups_svl svl1) in
  svl2

let get_raw_defined_w_pure prog predef lhs rhs=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = !CP.print_svl in
  Debug.no_3 "get_raw_defined_w_pure" pr2 pr1 pr1 pr2
      (fun _ _ _ -> get_raw_defined_w_pure_x prog predef lhs rhs) predef lhs rhs

let filter_var_x prog svl0 f=
  (* let (def_vs_wo_args, hd_nodes, hv_nodes, hrels, eqs) = find_defined_pointers_raw prog f in *)
  let hd_nodes,hv_nodes,hrels = CF.get_hp_rel_formula f in
  let ls_hpargs = List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs))) hrels in
  let svl1 = List.fold_left (fun r (_,args) -> r@args) svl0 ls_hpargs in
  let keep_ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes (svl0@svl1) in
  let keep_ptrs1 = CP.remove_dups_svl (keep_ptrs@svl1) in
  let keep_hps = List.concat (List.map (get_intersect_hps keep_ptrs1) ls_hpargs) in
  CF.drop_data_view_hrel_nodes f CF.check_nbelongsto_dnode CF.check_nbelongsto_vnode
      CF.check_neq_hrelnode keep_ptrs1 keep_ptrs1 keep_hps

let filter_var prog svl f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = !CP.print_svl in
  Debug.no_2 "CF.filter_var" pr2 pr1 pr1
      (fun _ _ -> filter_var_x prog svl f)
      svl f

(*todo: merge three following functions in a higher-order function*)
let keep_data_view_hrel_nodes prog f hd_nodes hv_nodes keep_rootvars keep_hrels=
  let keep_ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes keep_rootvars in
  CF.drop_data_view_hrel_nodes f CF.check_nbelongsto_dnode CF.check_nbelongsto_vnode
    CF.check_neq_hrelnode keep_ptrs keep_ptrs keep_hrels

let keep_data_view_hrel_nodes prog f hd_nodes hv_nodes keep_rootvars keep_hrels=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = !CP.print_svl in
  Debug.no_3 "keep_data_view_hrel_nodes" pr1 pr2 pr2 pr1
      (fun _ _ _ -> keep_data_view_hrel_nodes prog f hd_nodes hv_nodes keep_rootvars keep_hrels)
      f keep_rootvars keep_hrels

let keep_data_view_hpargs_nodes prog f hd_nodes hv_nodes keep_rootvars keep_hpargs=
  CFU.keep_data_view_hpargs_nodes prog f hd_nodes hv_nodes keep_rootvars keep_hpargs

let keep_data_view_hrel_nodes_fb prog fb hd_nodes hv_nodes keep_rootvars keep_hrels=
  let keep_ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes keep_rootvars in
  CF.drop_data_view_hpargs_nodes_fb fb CF.check_nbelongsto_dnode CF.check_nbelongsto_vnode
    check_neq_hpargs keep_ptrs keep_ptrs keep_hrels keep_ptrs

let keep_data_view_hrel_nodes_two_f prog lhs rhs hd_nodes hv_nodes eqs lhs_hpargs rhs_keep_rootvars rhs_keep_hrels=
  let keep_ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes rhs_keep_rootvars in
  let closed_keep_ptrs = CF.find_close (keep_ptrs) eqs in
  let lhs_keep_hrels = List.concat (List.map (get_intersect_hps closed_keep_ptrs) lhs_hpargs) in
  let nf1 = CF.drop_data_view_hrel_nodes lhs CF.check_nbelongsto_dnode CF.check_nbelongsto_vnode check_neq_hrelnode keep_ptrs closed_keep_ptrs lhs_keep_hrels in
  let nf2 = CF.drop_data_view_hrel_nodes rhs CF.check_nbelongsto_dnode CF.check_nbelongsto_vnode check_neq_hrelnode keep_ptrs closed_keep_ptrs rhs_keep_hrels in
  (nf1,nf2)

let filter_eqs keep_svl prog_vars eqs0=
  let all_keel_svl = keep_svl@prog_vars in
  let rec helper eqs res=
    match eqs with
      | [] -> res
      | (sv1,sv2)::ss ->
            let b1 = CP.mem_svl sv1 all_keel_svl in
            let b2 = CP.mem_svl sv2 all_keel_svl in
            let new_eq=
              match b1,b2 with
                | true,false -> if CP.is_res_spec_var sv2 then [] else
                    [((* CP.subs_one res *) sv2, (* CP.subs_one res *) sv1)] (*m_apply_par*)
                | true,true -> begin
                    let c1 = CP.mem_svl sv1 prog_vars in
                    let c2 = CP.mem_svl sv2 prog_vars in
                    match c1,c2 with
                      | true,false -> [((* CP.subs_one res *) sv2, (* CP.subs_one res *) sv1)]
                      | _ -> [((* CP.subs_one res *) sv1, (* CP.subs_one res *) sv2)]
                end
                | false,true -> if CP.is_res_spec_var sv1 then [] else
                      [((* CP.subs_one res *) sv1, (* CP.subs_one res *) sv2)]
                | _ -> []
            in
            helper ss (res@new_eq)
  in
  helper eqs0 []

let filter_fn null_svl p=
  if CP.is_eq_exp p then
      let p_svl = CP.fv p in
      (CP.diff_svl p_svl null_svl) <> []
  else true

let filter_eq_in_one_hp_x unk_svl eqs hpargs=
  let helper l_eqs (_,args)=
    List.filter (fun (sv1,sv2) -> not (CP.mem_svl sv1 args && CP.mem_svl sv2 args) &&
        not (CP.mem_svl sv1 unk_svl || CP.mem_svl sv2 unk_svl)) l_eqs
  in
  List.fold_left helper eqs hpargs

let filter_eq_in_one_hp unk_svl eqs hpargs=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_2 "filter_eq_in_one_hp" pr1 pr2 pr1
      (fun _ _ -> filter_eq_in_one_hp_x unk_svl eqs hpargs) eqs hpargs

let rec keep_prog_vars_helper prog_vars eqs res=
  match eqs with
    | [] -> res
    | (sv1,sv2)::tl ->
          let new_eq=
            let c1 = CP.mem_svl sv1 prog_vars in
            let c2 = CP.mem_svl sv2 prog_vars in
            match c1,c2 with
              | true,false -> [(sv2, sv1)]
              | _ -> [(sv1, sv2)]
          in
          keep_prog_vars_helper prog_vars tl (res@new_eq)

let rec get_uniqe_eq_svl svl res=
  match svl with
    | [] -> res
    | sv::rest -> let grp,rem = List.partition (CP.eq_spec_var sv) rest in
      let new_res = if grp = [] then (res@[sv]) else res in
       get_uniqe_eq_svl rem new_res

let get_uniqe_eq eqs=
  let eq_svl = List.fold_left (fun ls (sv1,sv2)-> ls@[sv1;sv2]) [] eqs in
  let uniqe_eq_svl = get_uniqe_eq_svl eq_svl [] in
  uniqe_eq_svl

let filter_uniqe_eq eqs=
  let uniqe_eq_svl = get_uniqe_eq eqs in
  let eqs1 = List.filter (fun (sv1,sv2) -> not (CP.mem sv1 uniqe_eq_svl || CP.mem_svl sv2 uniqe_eq_svl)) eqs in
  let () = DD.ninfo_zprint (lazy (("      eqs1: " ^ (let pr = pr_list(pr_pair !CP.print_sv !CP.print_sv) in pr eqs1)))) no_pos in
  eqs1

let generate_closure_eq_null args eqNulls cur_eqs=
  let rec find_exists ls_eqs sv res=
    match ls_eqs with
      | [] -> res
      | (sv1,sv2)::rest -> let new_res =
          if CP.eq_spec_var sv1 sv then
            (res@[sv2])
          else if CP.eq_spec_var sv2 sv then
            (res@[sv1])
          else res
        in
        find_exists rest sv new_res
  in
  let rec helper rem res=
    match rem with
      | [] -> res
      | sv::rest ->
            let eq_exist = find_exists cur_eqs sv [] in
            let rest_eq_null1 = CP.diff_svl rest eq_exist in
            let eqs = List.map (fun sv1 -> CP.mkEqVar sv sv1 no_pos) rest_eq_null1 in
            helper rest (res@eqs)
  in
  let new_eq_ps = helper (CP.intersect_svl args eqNulls) [] in
  CP.join_conjunctions new_eq_ps

let re_arrange eqs0=
  let rec helper eqs res=
  match eqs with
    | [] -> res
    | (sv1, sv2)::rest ->
          try
            let sv3 = List.assoc sv1 res in
            helper rest (res@[(sv2,sv3)])
          with _ ->
              helper rest (res@[(sv1,sv2)])
  in
  helper eqs0 []

let smart_subst_x nf1 nf2 hpargs eqs0 reqs unk_svl prog_vars=
  let largs= CF.h_fv nf1.CF.formula_base_heap in
  let rargs= CF.h_fv nf2.CF.formula_base_heap in
  let all_args = CP.remove_dups_svl (largs@rargs) in
  (*lhs - nf1*)
  (* let eqs0 = (MCP.ptr_equations_without_null nf1.CF.formula_base_pure) in *)
  (*cycle nodes: DO NOT subst*)
  let ptrs_group = (CF.get_ptrs_group_hf nf1.CF.formula_base_heap)@(CF.get_ptrs_group_hf nf2.CF.formula_base_heap) in
  let eqs = List.filter (fun (sv1,sv2) -> not (List.exists (fun svl -> CP.mem sv1 svl && CP.mem_svl sv2 svl) ptrs_group)) eqs0 in
  let () = DD.ninfo_zprint (lazy (("      eqs 1: " ^ (let pr = pr_list(pr_pair !CP.print_sv !CP.print_sv) in pr eqs)))) no_pos in
  (*******************)
  let eqNulls = CP.remove_dups_svl (MCP.get_null_ptrs nf1.CF.formula_base_pure) in
  let eqNulls1 = CF.find_close eqNulls eqs in
  (* let () = DD.info_zprint (lazy (("      eqNulls1: " ^ (!CP.print_svl eqNulls1)))) no_pos in *)
  let eqNulls2 = List.filter (fun sv -> CP.mem_svl sv all_args) eqNulls1 in
  (* let () = DD.info_zprint (lazy (("      eqNulls2: " ^ (!CP.print_svl eqNulls2)))) no_pos in *)
  let null_ps = List.map (fun sv -> CP.mkNull sv no_pos) eqNulls2 in
  let new_eqs = filter_eqs all_args prog_vars eqs in
  let new_eqs1 = List.filter (fun (sv1,sv2) -> not (CP.mem_svl sv1 eqNulls2 && CP.mem_svl sv2 eqNulls2)) new_eqs in
  let new_eqs1 = filter_eq_in_one_hp unk_svl new_eqs1 hpargs in
  let new_eqs2 = re_arrange new_eqs1 in
  let () = DD.ninfo_zprint (lazy (("      new_eqs2: " ^ (let pr = pr_list(pr_pair !CP.print_sv !CP.print_sv) in pr new_eqs2)))) no_pos in
  let nf1a = CF.subst_b new_eqs2 nf1 in
  let () = Debug.ninfo_zprint (lazy (("nf1a: " ^ (Cprinter.string_of_formula_base nf1a)))) no_pos in
  let ps10 = CP.list_of_conjs (MCP.pure_of_mix nf1a.CF.formula_base_pure) in
  let eqNulls3 = List.filter (fun sv -> not (CP.mem_svl sv rargs)) eqNulls2 in
  let new_ps11 = List.filter (filter_fn eqNulls3) ps10 in
  let new_p = generate_closure_eq_null (List.filter CP.is_node_typ rargs) eqNulls2 eqs in
  let new_ps12 = new_ps11@null_ps@[new_p]  in
  let new_ps13 = CP.remove_redundant_helper new_ps12 [] in
  let () = Debug.ninfo_zprint (lazy (("new_ps13: " ^ (let pr = pr_list !CP.print_formula in pr new_ps13)))) no_pos in
  let new_p13 = CP.conj_of_list new_ps13 no_pos in
  let nf11 = {nf1a with CF.formula_base_pure = MCP.mix_of_pure new_p13} in
  let () = Debug.ninfo_zprint (lazy (("nf11: " ^ (Cprinter.string_of_formula_base nf11)))) no_pos in
  (*rhs*)
  (* let reqs1 = re_arrange reqs in *)
  let new_nf2 = CF.subst_b (new_eqs2@reqs) nf2 in
  (*subst again*)
  let nleqs0 = (MCP.ptr_equations_without_null nf11.CF.formula_base_pure) in
  let ptrs_group1 = (CF.get_ptrs_group_hf nf1.CF.formula_base_heap)@(CF.get_ptrs_group_hf nf11.CF.formula_base_heap) in
  let nleqs = List.filter (fun (sv1,sv2) -> not (List.exists (fun svl -> CP.mem sv1 svl && CP.mem_svl sv2 svl) ptrs_group1)) nleqs0 in
  let () = DD.ninfo_zprint (lazy (("      nleqs: " ^ (let pr = pr_list(pr_pair !CP.print_sv !CP.print_sv) in pr nleqs)))) no_pos in
  let nreqs = (MCP.ptr_equations_without_null new_nf2.CF.formula_base_pure) in
  let nleqs1 = List.filter (fun (sv1,sv2) -> not (CP.mem_svl sv1 eqNulls2 && CP.mem_svl sv2 eqNulls2)) nleqs in
  let nleqs2 = filter_eq_in_one_hp unk_svl nleqs1 hpargs in
  let nreqs1 = List.filter (fun (sv1,sv2) -> not (CP.mem_svl sv1 eqNulls2 && CP.mem_svl sv2 eqNulls2)) nreqs in
  let nreqs2 = filter_eq_in_one_hp unk_svl nreqs1 hpargs in
  let nleqs3 =  keep_prog_vars_helper prog_vars nleqs2 [] in
  let nleqs4 = filter_uniqe_eq nleqs3 in
  let lhs_b2 = CF.subst_b (nleqs4) nf11 in (*m_apply_par*)
  let () = DD.ninfo_zprint (lazy (("      nreqs2: " ^ (let pr = pr_list(pr_pair !CP.print_sv !CP.print_sv) in pr nreqs2)))) no_pos in
  let rhs_b2 = CF.subst_b (nleqs4@nreqs2) new_nf2 in
  (*prog_vars*)
  let n_prog_vars = CP.subst_var_list (nleqs4@nreqs2) prog_vars in
  (lhs_b2,rhs_b2,n_prog_vars)

let smart_subst nf1 nf2 hpargs eqs reqs unk_svl prog_vars=
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv)  in
  Debug.no_5 "smart_subst" pr1 pr1 pr2 pr3 pr3 (pr_triple pr1 pr1 pr2)
      (fun _ _ _ _ _ -> smart_subst_x nf1 nf2 hpargs eqs reqs unk_svl prog_vars) nf1 nf2 prog_vars eqs reqs

(*moved to CFU*)
(*
(i) build emap for LHS/RHS 
  - eqnull -> make closure. do not subst
  - cycle nodes: DO NOT subst
  - inside one preds, do not subst
(ii) common free vars for both LHS/RHS
(iii) subs both sides to use smallest common vars
        lhs     |- P(v* )
*)
(* let cmp_fn sv1 sv2 = let n= String.compare (CP.name_of_spec_var sv1) (CP.name_of_spec_var sv2) in *)
(*   if n=0 then *)
(*     if CP.primed_of_spec_var sv1 = Unprimed then -1 else 1 *)
(*   else n *)
(* let build_subst_comm_x args prog_vars emap comm_svl= *)
(*   (\* let find_comm_eq ls_eq sv= *\) *)
(*   (\*   if List.exists (fun svl -> CP.mem_svl sv svl) ls_eq then ls_eq else *\) *)
(*   (\*     let com_eq_svl = CP.EMapSV.find_equiv_all sv emap in *\) *)
(*   (\*     if com_eq_svl = [] then ls_eq else *\) *)
(*   (\*       ls_eq@[com_eq_svl] *\) *)
(*   (\* in *\) *)
(*   let build_subst subst evars= *)
(*     let inter1 = CP.intersect_svl evars prog_vars in *)
(*     let keep_sv = if inter1 <> [] then *)
(*       List.hd (List.sort cmp_fn inter1) *)
(*     else *)
(*       let inter2 = CP.intersect_svl evars args in *)
(*       if inter2 <> [] then *)
(*         List.hd (List.sort cmp_fn inter2) *)
(*       else *)
(*         let evars1 = List.sort cmp_fn evars in *)
(*         List.hd evars1 *)
(*     in *)
(*     let new_ss = List.fold_left (fun r sv -> if CP.eq_spec_var keep_sv sv then r else r@[(sv, keep_sv)]) [] evars in *)
(*     subst@new_ss *)
(*   in *)
(*   let epart0 = CP.EMapSV.partition emap in *)
(*   (\* let ls_com_eq_svl = List.fold_left find_comm_eq [] comm_svl in *\) *)
(*   let ls_com_eq_svl, ls_non_com_eq_svl = List.partition (fun svl -> *)
(*       CP.intersect_svl svl comm_svl <> [] *)
(*   ) epart0 in *)
(*   let ss1 =  if ls_com_eq_svl = [] then [] else *)
(*     List.fold_left build_subst [] ls_com_eq_svl *)
(*   in *)
(*   let ss2 = if ls_non_com_eq_svl = [] then [] else *)
(*     List.fold_left build_subst [] ls_non_com_eq_svl *)
(*   in *)
(*   (ss1@ss2) *)

(* let build_subst_comm args prog_vars emap comm_svl= *)
(*   let pr1 = CP.EMapSV.string_of in *)
(*   let pr2 =  !CP.print_svl in *)
(*   let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv ) in *)
(*   Debug.no_4 "SAU.build_subst_comm" pr2 pr2 pr1 pr2 pr3 *)
(*       (fun _ _ _ _ ->  build_subst_comm_x args prog_vars emap comm_svl) *)
(*       args prog_vars emap comm_svl *)

(* let expose_expl_closure_eq_null_x lhs_b lhs_args emap0= *)
(*   let rec find_equiv_all eparts sv all_parts= *)
(*     match eparts with *)
(*       | [] -> [],all_parts *)
(*       | ls::rest -> if CP.mem_svl sv ls then (ls,all_parts@rest) else *)
(*           find_equiv_all rest sv (all_parts@[ls]) *)
(*   in *)
(*   let look_up_eq_null (epart, ls_null_args, ls_expl_eqs, ss) sv= *)
(*     (\* let eq_nulls,rem_parts = find_equiv_all epart sv [] in *\) *)
(*     let eq_nulls,rem_parts = find_equiv_all epart sv [] in *)
(*     let eq_null_args = CP.intersect_svl eq_nulls lhs_args in *)
(*     if List.length eq_null_args > 1 then *)
(*       let eq_null_args1 = (List.sort cmp_fn eq_null_args) in *)
(*       let keep_sv = List.hd eq_null_args1 in *)
(*       let ss2 = List.fold_left (fun ss1 sv -> *)
(*           if CP.eq_spec_var keep_sv sv then ss1 *)
(*           else ss1@[(sv, keep_sv)] *)
(*       ) [] eq_nulls *)
(*       in *)
(*       let ss3 = List.map (fun sv -> (sv, keep_sv) ) (List.tl eq_null_args1) in *)
(*       (rem_parts, ls_null_args@eq_null_args, ls_expl_eqs@ss3,ss@ss2) *)
(*     else (epart, ls_null_args, ls_expl_eqs, ss) *)
(*   in *)
(*   let eq_null_svl = CP.remove_dups_svl (MCP.get_null_ptrs lhs_b.CF.formula_base_pure) in *)
(*   let epart0 = CP.EMapSV.partition emap0 in *)
(*   let rem_parts, eq_null_args, expl_eq_args, ss = List.fold_left look_up_eq_null (epart0, [],[],[]) eq_null_svl in *)
(*   let cls_e_null = List.map (fun sv -> CP.mkNull sv no_pos) eq_null_args in *)
(*   (\* let expl_eq_ps = List.map (fun (sv1,sv2) -> CP.mkEqVar sv1 sv2 no_pos) expl_eq_args in *\) *)
(*   (CP.EMapSV.un_partition rem_parts, (\* expl_eq_ps@ *\)cls_e_null, ss) *)


(* let expose_expl_closure_eq_null lhs_b lhs_args emap= *)
(*   let pr1 = CP.EMapSV.string_of in *)
(*   let pr2 = pr_list !CP.print_formula in *)
(*   let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv ) in *)
(*   Debug.no_1 "SAU.expose_expl_closure_eq_null" pr1 (pr_triple pr1 pr2 pr3) *)
(*       (fun _ -> expose_expl_closure_eq_null_x lhs_b lhs_args emap) emap *)
(* (\* *)
(*   - cycle nodes: DO NOT subst *)
(*   - inside one preds, do not subst *)

(* for each ls_eqs, if it contains at least two vars of the same group, *)
(*   - we remove this ls_eqs *)
(*   - add equality in lhs *)
(*  input: *)
(*   - emap: global emap (no r_qemap) *)
(*   - groups of args of unknown preds + args + data nodes *)
(*  output: *)
(*   - triple of (remain emap, equalifty formula to be added to lhs, ss for pure of lhs *)
(*   rhs *)
(* *\) *)
(* let expose_expl_eqs_x emap0 prog_vars vars_grps0= *)
(*   (\*move root to behind, donot loss it*\) *)
(*   let roots = List.fold_left (fun roots0 args -> match args with *)
(*     | r::_ -> roots0@[r] *)
(*     | _ -> roots0 *)
(*   ) [] vars_grps0 in *)
(*   let all_vars = List.concat vars_grps0 in *)
(*   let process_one_ls_eq ls_eqs = *)
(*     let ls_eq_args = List.fold_left (fun r args -> *)
(*         let inter = CP.intersect_svl args ls_eqs in *)
(*         if List.length inter > 1 then r@[inter] else r *)
(*         ) [] vars_grps0 in *)
(*     let ls_eq_args1 = List.sort (fun ls1 ls2 -> List.length ls2 - List.length ls1) ls_eq_args in *)
(*     let ls_eq_args2 = Gen.BList.remove_dups_eq (Gen.BList.subset_eq CP.eq_spec_var) ls_eq_args1 in *)
(*     if ls_eq_args2=[] then (false,[],[]) *)
(*     else *)
(*       (\* let () = Debug.info_hprint (add_str  "ls_eq_args2 " (pr_list !CP.print_svl)) ls_eq_args2 no_pos in *\) *)
(*       (\*explicit equalities*\) *)
(*       let expl_eqs, link_svl = List.fold_left (fun (r, keep_svl) ls -> *)
(*           let ls1 = List.sort cmp_fn ls in *)
(*           (\* let inter = CP.intersect_svl roots ls1 in *\) *)
(*           let keep_sv = (\* if inter <> [] then List.hd inter else *\) List.hd ls1 in *)
(*           (r@(List.map (fun sv -> (sv, keep_sv)) (List.tl ls1)), keep_svl@[keep_sv]) *)
(*       ) ([],[]) ls_eq_args2 *)
(*       in *)
(*       (\*link among grps*\) *)
(*       let link_expl_eqs = if link_svl = [] then [] else *)
(*         let link_svl1 = List.sort cmp_fn link_svl in *)
(*         let fst_sv = List.hd link_svl1 in *)
(*         List.map (fun sv -> (sv, fst_sv)) (List.tl link_svl1) *)
(*       in *)
(*       (\*subst for others*\) *)
(*       let keep_sv = *)
(*         let () = Debug.ninfo_hprint (add_str  "link_svl" !CP.print_svl) link_svl no_pos in *)
(*         let inters1 = CP.intersect_svl (prog_vars) link_svl in *)
(*         let () = Debug.ninfo_hprint (add_str  "inters1" !CP.print_svl) inters1 no_pos in *)
(*         if inters1 != [] then List.hd inters1 else *)
(*           (\* let inters0 = CP.intersect_svl roots link_svl in *\) *)
(*           (\* let () = Debug.info_hprint (add_str  "inters0" !CP.print_svl) inters0 no_pos in *\) *)
(*           (\* if inters0 != [] then List.hd (inters0) else *\) *)
(*             let inters = CP.intersect_svl all_vars link_svl in *)
(*             let () = Debug.ninfo_hprint (add_str  "inters" !CP.print_svl) inters no_pos in *)
(*           if inters = [] then List.hd (List.sort cmp_fn link_svl) *)
(*           else List.hd inters *)
(*       in *)
(*       (\* let () = Debug.info_hprint (add_str  "keep_sv " !CP.print_sv) keep_sv no_pos in *\) *)
(*       (\* let () = Debug.info_hprint (add_str  "ls_eqs " !CP.print_svl) ls_eqs no_pos in *\) *)
(*       let ss2 = List.fold_left (fun ss1 sv -> *)
(*           if CP.eq_spec_var keep_sv sv then ss1 *)
(*           else ss1@[(sv, keep_sv)] *)
(*       ) [] ls_eqs *)
(*       in *)
(*       (true, expl_eqs@link_expl_eqs,ss2) *)
(*   in *)
(*   let epart0 = CP.EMapSV.partition emap0 in *)
(*   let rem_eparts, ls_eq_args, expl_eq_args,sst = List.fold_left (fun (r_eparts, r_eq_args, r_eqs, r_ss) ls_eqs-> *)
(*       let b, n_eqs, n_ss = process_one_ls_eq ls_eqs in *)
(*       if b then *)
(*         (r_eparts, r_eq_args@[ls_eqs], r_eqs@n_eqs, r_ss@n_ss) *)
(*       else (r_eparts@[ls_eqs], r_eq_args, r_eqs, r_ss) *)
(*   ) ([],[],[],[]) epart0 in *)
(*   let expl_eq_ps = List.map (fun (sv1,sv2) -> CP.mkEqVar sv1 sv2 no_pos) expl_eq_args in *)
(*   (CP.EMapSV.un_partition rem_eparts, ls_eq_args, expl_eq_ps ,sst) *)

(* let expose_expl_eqs emap prog_vars vars_grps= *)
(*   let pr1 = pr_list_ln !CP.print_svl in *)
(*   let pr2 = CP.EMapSV.string_of in *)
(*   let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv ) in *)
(*   let pr4 = pr_quad pr2 pr1 (pr_list !CP.print_formula) pr3 in *)
(*   Debug.no_2 "SAU.expose_expl_eqs" pr2 pr1 pr4 *)
(*       (fun _ _ -> expose_expl_eqs_x emap prog_vars vars_grps) *)
(*       emap vars_grps *)

(* let h_subst ss ls_eq_args0 hf0= *)
(*   let rec is_expl_eqs ls_eq_args svl = *)
(*     match ls_eq_args with *)
(*       | [] -> false *)
(*       | eqs::rest -> *)
(*             if List.length (CP.intersect_svl eqs svl) > 1 then true else *)
(*               is_expl_eqs rest svl *)
(*   in *)
(*   match hf0 with *)
(*     | CF.DataNode dn -> *)
(*           let svl = dn.CF.h_formula_data_node::dn.CF.h_formula_data_arguments in *)
(*           if is_expl_eqs ls_eq_args0 svl then hf0 else *)
(*             let hf1 = CF.h_subst ss hf0 in *)
(*             hf1 *)
(*     | CF.ViewNode vn -> *)
(*           let svl = vn.CF.h_formula_view_node::vn.CF.h_formula_view_arguments in *)
(*           if is_expl_eqs ls_eq_args0 svl then hf0 else *)
(*             let hf1 = CF.h_subst ss hf0 in *)
(*             hf1 *)
(*     | CF.HRel (hp, eargs, pos) -> *)
(*           let svl = List.fold_left List.append [] (List.map CP.afv eargs) in *)
(*           let () = Debug.ninfo_hprint (add_str  "svl " !CP.print_svl) svl no_pos in *)
(*           if is_expl_eqs ls_eq_args0 svl then hf0 else *)
(*             let hf1 = CF.h_subst ss hf0 in *)
(*             hf1 *)
(*     | _ -> hf0 *)

(*moved to CFU*)
(* let smart_subst_new_x lhs_b rhs_b hpargs l_emap r_emap r_qemap unk_svl prog_vars= *)
(*   let largs= CF.h_fv lhs_b.CF.formula_base_heap in *)
(*   let rargs= CF.h_fv rhs_b.CF.formula_base_heap in *)
(*   let all_args = CP.remove_dups_svl (largs@rargs) in *)
(*   (\*---------------------------------------*\) *)
(*   let lsvl = CF.fv (CF.Base lhs_b) in *)
(*   let rsvl = (CF.fv (CF.Base rhs_b))@(CP.EMapSV.get_elems r_emap)@(CP.EMapSV.get_elems r_qemap) in *)
(*   let comm_svl = CP.intersect_svl lsvl rsvl in *)
(*   let lhs_b1, rhs_b1, prog_vars = *)
(*     if comm_svl = [] then *)
(*       (lhs_b, rhs_b, prog_vars) *)
(*     else *)
(*       let l_emap1, null_ps, null_sst = expose_expl_closure_eq_null lhs_b all_args l_emap in *)
(*       let emap0 = CP.EMapSV.merge_eset l_emap r_emap in *)
(*       let vars_grps = (CF.get_data_node_ptrs_group_hf lhs_b.CF.formula_base_heap)@(CF.get_data_node_ptrs_group_hf rhs_b.CF.formula_base_heap)@ *)
(*         (List.map snd hpargs) *)
(*       in *)
(*       let emap0a, ls_eq_args, expl_eqs_ps, eq_sst = expose_expl_eqs emap0 prog_vars vars_grps in *)
(*       (\* let () = Debug.info_hprint (add_str  "ls_eq_args " (pr_list !CP.print_svl)) ls_eq_args no_pos in *\) *)
(*       let emap1 = CP.EMapSV.merge_eset emap0a r_qemap in *)
(*       let ss = build_subst_comm all_args prog_vars emap1 comm_svl in *)
(*       let pr_ss = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
(*       (\* let () = Debug.info_hprint (add_str  "ss " (pr_ss)) ss no_pos in *\) *)
(*       (\*LHS*\) *)
(*       let lhs_b1 = CF.subst_b ss lhs_b in *)
(*       let lhs_pure1 = MCP.pure_of_mix lhs_b1.CF.formula_base_pure in *)
(*       let lhs_pure2 = CP.subst (null_sst@eq_sst) lhs_pure1 in *)
(*       let lpos = CF.pos_of_formula (CF.Base lhs_b1) in *)
(*       let lhs_pure_w_expl = CP.conj_of_list (lhs_pure2::(null_ps@expl_eqs_ps)) lpos in *)
(*       let lhs_b2 = {lhs_b1 with CF.formula_base_pure = MCP.mix_of_pure *)
(*               (CP.remove_redundant lhs_pure_w_expl); *)
(*           CF.formula_base_heap = CF.trans_heap_hf (h_subst (null_sst@eq_sst) ls_eq_args) lhs_b1.CF.formula_base_heap; *)
(*       } in *)
(*       (\*RHS*\) *)
(*       let rhs_b1 = CF.subst_b ss rhs_b in *)
(*       (\* let () = Debug.info_hprint (add_str  "rhs_b1 " Cprinter.prtt_string_of_formula) (CF.Base rhs_b1) no_pos in *\) *)
(*       let rhs_b2 = {rhs_b1 with CF.formula_base_pure = MCP.mix_of_pure *)
(*               (CP.remove_redundant (MCP.pure_of_mix rhs_b1.CF.formula_base_pure)); *)
(*           CF.formula_base_heap = CF.trans_heap_hf (h_subst (null_sst@eq_sst) ls_eq_args) rhs_b1.CF.formula_base_heap; *)
(*       } in *)
(*       (lhs_b2, rhs_b2, CP.subst_var_list (ss@null_sst@eq_sst) prog_vars) *)
(*   in *)
(*   (lhs_b1, rhs_b1, prog_vars) *)

(* let smart_subst_new lhs_b rhs_b hpargs l_emap r_emap r_qemap unk_svl prog_vars= *)
(*   let pr1 = Cprinter.string_of_formula_base in *)
(*   let pr2 = !CP.print_svl in *)
(*   let pr3 = CP.EMapSV.string_of in *)
(*   let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in *)
(*   Debug.no_7 "smart_subst_new" pr1 pr1 pr4 pr2 pr3 pr3 pr3 (pr_triple pr1 pr1 pr2) *)
(*       (fun _ _ _ _ _ _ _-> smart_subst_new_x lhs_b rhs_b hpargs l_emap r_emap r_qemap unk_svl prog_vars) *)
(*       lhs_b rhs_b hpargs prog_vars l_emap r_emap r_qemap *)

let smart_subst_lhs f lhpargs leqs infer_vars=
  match f with
    | CF.Base fb ->
          let nfb,_,_ = smart_subst fb (CF.formula_base_of_heap CF.HEmp no_pos) lhpargs
            leqs [] [] infer_vars in
          nfb
    | _ -> report_error no_pos "SAU.smart_subst_lhs"

let keep_data_view_hrel_nodes_two_fbs prog f1 f2 hd_nodes hv_nodes hpargs
      leqs reqs his_ss keep_rootvars
      lhs_hpargs lkeep_hpargs lhs_args_ni rkeep_hps rhs_svl rhs_args_ni unk_svl prog_vars =
  let eqs = (leqs@reqs@his_ss) in
  let () = Debug.ninfo_zprint (lazy (("keep_vars root: " ^ (!CP.print_svl keep_rootvars)))) no_pos in
  let () = Debug.ninfo_zprint (lazy (("lhs_hpargs: " ^ (!CP.print_svl lhs_hpargs)))) no_pos in
  let keep_closed_rootvars =  (List.fold_left close_def keep_rootvars eqs) in
  let () = Debug.ninfo_zprint (lazy (("keep_vars 1: " ^ (!CP.print_svl keep_closed_rootvars)))) no_pos in
  let keep_vars = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes (CP.remove_dups_svl (keep_closed_rootvars)) in
  let c_lhs_hpargs = CP.remove_dups_svl (List.fold_left close_def lhs_hpargs eqs) in
  let () = Debug.ninfo_zprint (lazy (("c_lhs_hpargs: " ^ (!CP.print_svl c_lhs_hpargs)))) no_pos in
  (* let lkeep_vars = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes lhs_keep_closed_rootvars in *)
  (*may be alisas between lhs and rhs*)
  let () = Debug.ninfo_zprint (lazy (("keep_vars: " ^ (!CP.print_svl keep_vars)))) no_pos in
  (* let () = Debug.info_zprint (lazy (("lkeep_vars: " ^ (!CP.print_svl lkeep_vars)))) no_pos in *)
  (* let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let () = Debug.info_zprint (lazy (("lkeep_hpargs: " ^ (pr1 lkeep_hpargs)))) no_pos in *)
  (*remove dups*)
  (* let lkeep_nodes = look_up_dups_node prog hd_nodes hv_nodes c_lhs_hpargs keep_vars  *)
  (*  (List.fold_left close_def rhs_svl eqs ) in *)
  let () = Debug.ninfo_zprint (lazy (("f1: " ^ (Cprinter.string_of_formula_base f1)))) no_pos in
  let () = Debug.ninfo_zprint (lazy (("f2: " ^ (Cprinter.string_of_formula_base f2)))) no_pos in
  (*demo/cyc-lseg-3.ss*)
  let nf1 = CF.drop_data_view_hpargs_nodes_fb f1 CF.check_nbelongsto_dnode CF.check_nbelongsto_vnode check_neq_hpargs
    (* lkeep_nodes *) keep_vars (* lkeep_nodes *) keep_vars lkeep_hpargs (keep_vars@c_lhs_hpargs@
        (( List.filter (fun sv -> not (CP.is_node_typ sv)) lhs_args_ni)@rhs_args_ni)) in
  let nf2 = CF.drop_data_view_hrel_nodes_fb f2 CF.check_nbelongsto_dnode CF.check_nbelongsto_vnode check_neq_hrelnode
    keep_vars keep_vars rkeep_hps (keep_vars@rhs_args_ni) in
  let () = Debug.ninfo_zprint (lazy (("nf1: " ^ (Cprinter.string_of_formula_base nf1)))) no_pos in
  let () = Debug.ninfo_zprint (lazy (("nf2: " ^ (Cprinter.string_of_formula_base nf2)))) no_pos in
  let lhs_b2,rhs_b2 =  ( nf1, nf2)(* smart_subst nf1 nf2 hpargs eqs reqs unk_svl prog_vars *) in
  (lhs_b2,rhs_b2)

let rec drop_data_view_hrel_nodes_from_root prog f0 hd_nodes hv_nodes eqs drop_rootvars well_defined_svl rhs_svl defined_hps=
  let rec helper f =
  match f with
    | CF.Base fb ->
        let hd_names = List.fold_left (fun ls hd -> ls@[hd.CF.h_formula_data_node]) [] hd_nodes in
        let keep_hds = CP.diff_svl hd_names (drop_rootvars) in
        let closed_keep_svl = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes keep_hds in
        let well_defined_svl1 = CP.diff_svl well_defined_svl closed_keep_svl in
        let new_p=
          if well_defined_svl1 = [] then fb.CF.formula_base_pure else
            let pure_keep_svl = CP.diff_svl (CF.fv f) well_defined_svl1 in
            MCP.mix_of_pure (CP.filter_var_new
                  (MCP.pure_of_mix fb.CF.formula_base_pure) (CP.remove_dups_svl (pure_keep_svl@rhs_svl)))
        in
        CF.Base { fb with
            CF.formula_base_heap = drop_data_view_hrel_nodes_hf_from_root
                prog fb.CF.formula_base_heap
                hd_nodes hv_nodes eqs (drop_rootvars@well_defined_svl1(* @rhs_svl *)) defined_hps;
            CF.formula_base_pure = new_p
    }
    | CF.Exists fe ->
        let qvars, base1 = CF.split_quantifiers f in
        let nf = helper base1 in
        CF.add_quantifiers qvars nf
    | _ -> report_error no_pos "sau.drop_data_view_hrel_nodes"
  in
  helper f0

and drop_data_view_hrel_nodes_hf_from_root prog hf hd_nodes hv_nodes eqs drop_rootvars drop_hps=
  let () = Debug.ninfo_zprint (lazy (("drop_vars root: " ^ (!CP.print_svl drop_rootvars)))) no_pos in
  (* let drop_closed_rootvars = CP.remove_dups_svl (List.fold_left close_def drop_rootvars eqs) in *)
  let () = Debug.ninfo_zprint (lazy (("close drop_rootvars: " ^ (!CP.print_svl drop_rootvars)))) no_pos in
  let drop_vars = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes drop_rootvars in
  (*may be alisas between lhs and rhs*)
  (* let () = Debug.info_zprint (lazy (("drop_vars: " ^ (!CP.print_svl drop_vars)))) no_pos in *)
  (* let () = Debug.info_pprint ("drop_hps: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* pr drop_hps)) no_pos in *)
  (* let () = Debug.info_zprint (lazy (("hf: " ^ (Cprinter.string_of_h_formula hf)))) no_pos in *)
  let nhf = CF.drop_data_view_hpargs_nodes_hf hf CF.select_dnode CF.select_vnode select_subsumehpargs
    drop_vars drop_vars drop_hps in
  (* let () = Debug.info_zprint (lazy (("nhf: " ^ (Cprinter.string_of_h_formula nhf)))) no_pos in *)
  nhf


(***************************************************************)
           (*========SIMPLIFICATION============*)
(***************************************************************)
(*
  this function is diff to simp_match_partial_unknown.
 apply for pre-assumptions
  - this makes swl-i.ss failed
  - sa/hip/ll-append5.ss
*)
let simp_match_unknown_x unk_hps link_hps cs=
  let lhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_lhs in
  let rhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_rhs in
  let inter_hps = CP.intersect_svl lhs_hps rhs_hps in
  let inter_unk_hps = CP.intersect_svl inter_hps (unk_hps@link_hps) in
  CF.drop_hprel_constr cs inter_unk_hps

let simp_match_unknown unk_hps link_hps cs=
  let pr1 = Cprinter.string_of_hprel_short in
  let pr2 = !CP.print_svl in
  Debug.no_3 "simp_match_unknown" pr2 pr2 pr1 pr1
      (fun _ _ _ -> simp_match_unknown_x unk_hps link_hps cs)
      unk_hps link_hps cs

(*****************)
(* copied from sa
x::node<a,b> .... ===> x::node<c,d> === ss={a/c;b/d} and
subst into rhs
*)
let do_simpl_nodes_match_x lhs rhs =
  let check_eq_data_node dn1 dn2=
    CP.eq_spec_var dn1.CF.h_formula_data_node dn2.CF.h_formula_data_node
  in
  let sort_data_node_by_name dn1 dn2=
    String.compare (CP.name_of_spec_var dn1.CF.h_formula_data_node)
        (CP.name_of_spec_var dn2.CF.h_formula_data_node)
  in
  let rec get_subst lhds rhds res=
    match rhds,lhds with
      | [],_ -> res
      | _, [] -> res
      | dn2::rest2,dn1::rest1 ->
          let ss=
            if CP.eq_spec_var dn1.CF.h_formula_data_node dn2.CF.h_formula_data_node then
              List.combine dn2.CF.h_formula_data_arguments dn1.CF.h_formula_data_arguments
            else []
          in
          get_subst rest1 rest2 (res@ss)
  in
  let hn_drop_matched matched_svl hf=
    match hf with
      | CF.DataNode hn -> if CP.mem_svl hn.CF.h_formula_data_node matched_svl then CF.HEmp else hf
      | _ -> hf
  in
  let l_hds, _, _ = CF.get_hp_rel_formula lhs in
  let r_hds, _, _ = CF.get_hp_rel_formula rhs in
  let matched_data_nodes = Gen.BList.intersect_eq check_eq_data_node l_hds r_hds in
  let l_hds = Gen.BList.intersect_eq check_eq_data_node l_hds matched_data_nodes in
  let r_hds = Gen.BList.intersect_eq check_eq_data_node r_hds matched_data_nodes in
  let sl_hds = List.sort sort_data_node_by_name l_hds in
  let sr_hds = List.sort sort_data_node_by_name r_hds in
  let ss = get_subst sl_hds sr_hds [] in
  let matched_svl = (List.map (fun hn -> hn.CF.h_formula_data_node) matched_data_nodes) in
  let n_lhs, n_rhs =
    if matched_svl = [] then (lhs, rhs)
    else
      let rhs1 = CF.subst ss rhs in
      (CF.formula_trans_heap_node (hn_drop_matched matched_svl) lhs, 

      CF.formula_trans_heap_node (hn_drop_matched matched_svl) rhs1)
  in
  n_lhs, n_rhs

let do_simpl_nodes_match lhs rhs =
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "do_simpl_nodes_match" pr1 pr1 (pr_pair pr1 pr1)
      (fun _ _ -> do_simpl_nodes_match_x lhs rhs) lhs rhs
(*
 - sa/demo/dll-pap-1.slk
*)
let simp_match_hp_w_unknown_x prog unk_hps link_hps cs=
  let tot_unk_hps = unk_hps@link_hps in
  (* let ignored_hps = unk_hps@link_hps in *)
  let l_hds, l_hvs,lhrels =CF.get_hp_rel_formula cs.CF.hprel_lhs in
  let r_hds, r_hvs,rhrels =CF.get_hp_rel_formula cs.CF.hprel_rhs in
  let lhps,lhp_args = List.fold_left (fun (r_hps, r_hpargs) (hp, eargs, _) ->
      let args = (List.fold_left List.append [] (List.map CP.afv eargs)) in
      ((r_hps@[hp]), (r_hpargs@[(hp,args)]) )
  ) ([],[]) lhrels
  in
  let rhps,rhp_args = List.fold_left (fun (r_hps, r_hpargs) (hp, eargs, _) ->
      let args = (List.fold_left List.append [] (List.map CP.afv eargs)) in
      ((r_hps@[hp]), (r_hpargs@[(hp,args)]) )
  ) ([],[]) rhrels
  in
  let rec_hps0 = CP.intersect_svl lhps rhps in
  let rec_hps = CP.diff_svl rec_hps0 tot_unk_hps in
  (* let rec_hps = List.filter (fun hp -> not (CP.mem_svl hp ignored_hps)) rec_hps0 in *)
  if (List.length rec_hps <= 1)
    (* check-dll: recusrsive do not check*)
    || ( (List.length l_hds > 0 || List.length l_hvs > 0) && List.length lhrels > 0 &&
        (* (List.length r_hds > 0 || List.length r_hvs > 0) && *) List.length rhrels > 0) (*swl-i.ss*)
  then
    (*sll-append*)
    (*remove irr unknown hpreds*)
    let lhs_wo_hps = fst (CF.drop_hrel_f cs.CF.hprel_lhs lhps) in
    let rhs_wo_hps = fst (CF.drop_hrel_f cs.CF.hprel_rhs rhps) in
    let svl_wo_args = CP.remove_dups_svl ((CF.fv lhs_wo_hps)@(CF.fv rhs_wo_hps)) in
    let () = Debug.ninfo_zprint (lazy (("    svl_wo_args: " ^ (!CP.print_svl svl_wo_args)))) no_pos in
    let elim_irr_unk_helper f hpargs=
      let drop_unk_hps = List.fold_left (fun r_hps (hp,args) ->
          let () = Debug.ninfo_zprint (lazy (("    hp: " ^ (!CP.print_sv hp) ^ " args: "^ (!CP.print_svl args)))) no_pos in
          if (CP.mem_svl hp tot_unk_hps) then
            let _, args_ni = partition_hp_args prog hp args in
            if (CP.diff_svl (List.map fst args_ni) svl_wo_args) <> [] then
              r_hps@[hp]
            else
              r_hps
          else
            r_hps
      ) [] hpargs
      in
      fst (CF.drop_hrel_f f drop_unk_hps)
    in
    {cs with CF.hprel_lhs = elim_irr_unk_helper cs.CF.hprel_lhs lhp_args ;
        CF.hprel_rhs =  (* elim_irr_unk_helper *) cs.CF.hprel_rhs (* rhp_args *) ;
    }
  else
    let tot_unk_hps = unk_hps@link_hps in
    let part_helper = (fun (unk_svl,rem) (hp,args)->
        if CP.mem_svl hp tot_unk_hps then
          (unk_svl@args, rem)
        else (unk_svl, rem@[(hp,args)])
    ) in
    let rec order_eq_w_unk l_args r_args unk_svl args_violate_ni =
      match l_args,r_args with
        | [],[] -> true
        | sv1::rest1,sv2::rest2 ->
              if CP.eq_spec_var sv1 sv2 || (CP.mem_svl sv1 unk_svl && CP.mem_svl sv2 unk_svl) ||
                (CP.mem_svl sv2 args_violate_ni) || CP.mem_svl sv1 args_violate_ni
              then
                order_eq_w_unk rest1 rest2 unk_svl args_violate_ni
              else false
        | _ -> false
    in
    (* let lhp_args = CF.get_HRels_f cs.CF.hprel_lhs in *)
    (* let rhp_args = CF.get_HRels_f cs.CF.hprel_rhs in *)
    (*get_all ptrs initiated*)
    let l_ptrs = CF.get_ptrs_f cs.CF.hprel_lhs in
    let r_ptrs = CF.get_ptrs_f cs.CF.hprel_rhs in
    let ptrs = (l_ptrs@r_ptrs) in
    let lunk_svl,lrem_hpargs = List.fold_left part_helper ([],[]) (lhp_args) in
    let runk_svl,rrem_hpargs = List.fold_left part_helper ([],[]) (rhp_args) in
    let unk_svl = CP.remove_dups_svl (lunk_svl@runk_svl) in
    let  _ = DD.ninfo_zprint (lazy (("unk_svl: " ^ (!CP.print_svl unk_svl)))) no_pos in
    let drop_hps = List.fold_left (fun ls (r_hp,r_args) ->
        ls@(List.fold_left (fun ls_inn (l_hp, l_args) ->
            if CP.eq_spec_var l_hp r_hp then
              let _, l_arg_ni = partition_hp_args prog l_hp l_args in
              let _, r_arg_ni = partition_hp_args prog r_hp r_args in
              let violate_ni = CP.intersect_svl (List.map fst (l_arg_ni@r_arg_ni)) ptrs in
              if order_eq_w_unk l_args r_args unk_svl violate_ni then (ls_inn@[l_hp]) else ls_inn
            else ls_inn
        ) [] lrem_hpargs)
    ) [] rrem_hpargs in
    CF.drop_hprel_constr cs drop_hps

let simp_match_hp_w_unknown prog unk_hps link_hps cs=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.string_of_hprel_short_inst prog [] in
  Debug.no_3 "simp_match_hp_w_unknown" pr1 pr1 pr2 pr2
      (fun _ _ _ -> simp_match_hp_w_unknown_x prog unk_hps link_hps cs)
      unk_hps link_hps cs

let simplify_one_constr_b_x prog unk_hps lhs_b rhs_b=
  (*return subst of args and add in lhs*)
  let rec look_up_eq_dn ldn rdns r_rem=
    match rdns with
      | [] -> ([],r_rem,[])
      | rdn::rest ->
          if CP.eq_spec_var ldn.CF.h_formula_data_node rdn.CF.h_formula_data_node then
            let ss=
              let lsvl = List.filter CP.is_node_typ ldn.CF.h_formula_data_arguments in
              let rsvl = List.filter CP.is_node_typ rdn.CF.h_formula_data_arguments in
              let ss1 = List.combine rsvl lsvl in
              List.filter (fun (sv1,sv2) -> not (CP.eq_spec_var sv1 sv2)) ss1
            in
            ([ldn.CF.h_formula_data_node],r_rem@rest,ss)
          else look_up_eq_dn ldn rest (r_rem@[rdn])
  in
  let rec get_eq_dnodes ldns rdns res ss=
    match ldns with
      | [] -> (res,ss)
      | ldn::rest ->
          let r,rdns_rem, r_ss = look_up_eq_dn ldn rdns [] in
          get_eq_dnodes rest rdns_rem (res@r) (ss@r_ss)
  in
  (* let check_eq_data_node dn1 dn2= *)
  (*   CP.eq_spec_var dn1.CF.h_formula_data_node dn2.CF.h_formula_data_node *)
  (* in *)
  let check_eq_view_node vn1 vn2=
    (*return subst of args and add in lhs*)
    CP.eq_spec_var vn1.CF.h_formula_view_node vn2.CF.h_formula_view_node
  in
  let l_hds, l_hvs, l_hrs = CF.get_hp_rel_bformula lhs_b in
  let r_hds, r_hvs, r_hrs = CF.get_hp_rel_bformula rhs_b in
  DD.ninfo_pprint (" input: " ^(Cprinter.prtt_string_of_formula_base lhs_b) ^ " ==> " ^
  (Cprinter.prtt_string_of_formula_base rhs_b)) no_pos;
  (*drop unused pointers in LHS*)
  DD.ninfo_zprint (lazy ("  drop not-in-used pointers")) no_pos;
  let keep_hrels,keep_ptrs = List.split (List.map
    (fun (hrel, eargs, _) ->
        let args = List.concat (List.map CP.afv eargs) in
        ((hrel, args), args))
    (l_hrs@r_hrs) )
  in
  let lhs_b1 = keep_data_view_hrel_nodes_fb prog lhs_b (l_hds@r_hds) (l_hvs@r_hvs)
    (List.concat keep_ptrs) keep_hrels in
  (*pointers/hps matching LHS-RHS*)
  (*data nodes, view nodes, rel*)
  DD.ninfo_pprint "  matching LHS-RHS" no_pos;
  (* let matched_data_nodes = Gen.BList.intersect_eq check_eq_data_node l_hds r_hds in *)
  let matched_data_nodes, ss = get_eq_dnodes l_hds r_hds [] [] in
  let matched_view_nodes = Gen.BList.intersect_eq check_eq_view_node l_hvs r_hvs in
  let matched_hrel_nodes = Gen.BList.intersect_eq CF.check_eq_hrel_node l_hrs r_hrs in
  let hrels = List.map (fun (id,_,_) -> id) matched_hrel_nodes in
  let dnode_names = (* List.map (fun hd -> hd.CF.h_formula_data_node) *) matched_data_nodes in
  let vnode_names = List.map (fun hv -> hv.CF.h_formula_view_node) matched_view_nodes in
   Debug.ninfo_zprint (lazy (("    Matching found: " ^ (!CP.print_svl (dnode_names@vnode_names@hrels))))) no_pos;
  let lhs_nhf2,rhs_nhf2=
    if (dnode_names@vnode_names@hrels)=[] then lhs_b1.CF.formula_base_heap,rhs_b.CF.formula_base_heap
    else
      (*omit: not remove unk_hps in lhs*)
      (* let hrels1 = (List.filter (fun hp -> not(CP.mem_svl hp unk_hps)) hrels) in *)
      let lhs_nhf = CF.drop_data_view_hrel_nodes_hf lhs_b1.CF.formula_base_heap
        CF.select_dnode CF.select_vnode select_hrel dnode_names vnode_names hrels in
      let rhs_nhf = CF.drop_data_view_hrel_nodes_hf rhs_b.CF.formula_base_heap
        CF.select_dnode CF.select_vnode select_hrel dnode_names vnode_names hrels in
      let rhs_nhf2 = if ss= [] then rhs_nhf else CF.h_subst ss rhs_nhf in
      (lhs_nhf,rhs_nhf2)
  in
  (*remove duplicate pure formulas and remove x!= null if x::node*)
  let lsvl = List.map (fun hd -> hd.CF.h_formula_data_node) l_hds in
  let rsvl = List.map (fun hd -> hd.CF.h_formula_data_node) r_hds in
  let lhs_nmf2 = CF.remove_neqNull_redundant_hnodes lsvl (MCP.pure_of_mix lhs_b1.CF.formula_base_pure) in
  let rhs_nmf2 = CF.remove_neqNull_redundant_hnodes (lsvl@rsvl)(MCP.pure_of_mix rhs_b.CF.formula_base_pure) in
  let rhs_nmf3 = if ss=[] then rhs_nmf2 else CP.subst ss rhs_nmf2 in
  (* Debug.info_zprint (lazy (("    lmf: " ^ (!CP.print_formula lhs_nmf2)))) no_pos; *)
  let lhs_b2 = {lhs_b1 with CF.formula_base_heap = lhs_nhf2;
      CF.formula_base_pure = MCP.mix_of_pure lhs_nmf2
               } in
  let rhs_b2 = {rhs_b with CF.formula_base_heap = rhs_nhf2;
               CF.formula_base_pure = MCP.mix_of_pure rhs_nmf3} in
 (*pure subformulas matching LHS-RHS: drop RHS*)
  DD.ninfo_pprint (" output: " ^(Cprinter.prtt_string_of_formula_base lhs_b2) ^ " ==> " ^
  (Cprinter.prtt_string_of_formula_base rhs_b2)) no_pos;
(lhs_b2, rhs_b2, dnode_names@vnode_names@hrels)

let simplify_one_constr_b prog unk_hps lhs_b rhs_b=
  let pr = Cprinter.prtt_string_of_formula_base in
  Debug.no_2 "simplify_one_constr_b" pr pr (pr_triple pr pr !CP.print_svl)
      (fun _ _ -> simplify_one_constr_b_x prog unk_hps lhs_b rhs_b) lhs_b rhs_b


let rec simplify_one_constr prog unk_hps constr=
  begin
      let (lhs, rhs) = constr.CF.hprel_lhs,constr.CF.hprel_rhs in
      match lhs,rhs with
        | CF.Base lhs_b, CF.Base rhs_b ->
            begin
                let l,r,matched = simplify_one_constr_b prog unk_hps lhs_b rhs_b in
                 (* if l.CF.formula_base_heap = CF.HEmp && *)
                 (*   (MCP.isConstMTrue l.CF.formula_base_pure) then *)
                if CF.is_unknown_f (CF.Base l) || CF.is_unknown_f (CF.Base r) ||
                (is_empty_f (CF.Base l) && is_empty_f (CF.Base r)) then
                  let () = DD.ninfo_pprint (" input: " ^(Cprinter.prtt_string_of_formula_base lhs_b) ^ " ==> " ^
                                                  (Cprinter.prtt_string_of_formula_base rhs_b)) no_pos in
                  let () =  DD.ninfo_pprint (" output: drop") no_pos in
                   []
                else
                  (*it may subst into some unk_hps, should detect it*)
                  let hp_args = (CF.get_HRels l.CF.formula_base_heap)@
                    (CF.get_HRels r.CF.formula_base_heap) in
                  let hp_args1 = Gen.BList.remove_dups_eq check_simp_hp_eq
                    hp_args in
                  (*get hp that all args are unk*)
                  let unk_hp_args = List.filter (fun (hp,args) ->
                  (Gen.BList.difference_eq CP.eq_spec_var args constr.CF.unk_svl) = []) hp_args1 in
                  let new_constr = {constr with CF.predef_svl = constr.CF.predef_svl@matched;
                      CF.unk_hps = Gen.BList.remove_dups_eq check_simp_hp_eq
                          (constr.CF.unk_hps@unk_hp_args);
                       CF.hprel_lhs = CF.Base l;
                       CF.hprel_rhs = CF.Base r;
                                   }
                  in
                  let () =  DD.ninfo_zprint (lazy ((" simplify: new cs:" ^ ( Cprinter.string_of_hprel new_constr)))) no_pos in
                  [new_constr]
              end
        | _ -> report_error no_pos "sa.simplify_one_constr"
  end

let simplify_constrs_x prog unk_hps constrs=
  List.concat (List.map (simplify_one_constr prog unk_hps) constrs)

let simplify_constrs prog unk_hps constrs=
   let pr = pr_list_ln (Cprinter.string_of_hprel) in
  Debug.no_1 "simplify_constrs" pr pr
      (fun _ -> simplify_constrs_x prog unk_hps constrs) constrs

(***************************************************************)
           (*===========END SIMPLIFICATION===========*)
(***************************************************************)

(*
TODO: should remove split_spatial, now it always be true
*)
let find_well_defined_hp_x prog hds hvs r_hps prog_vars post_hps (hp,args) def_ptrs lhsb split_spatial pos=
  let do_spit fb rhs new_hps=
    let f = keep_data_view_hrel_nodes_fb prog fb hds hvs args [(hp,args)] in
    (*we do NOT want to keep heap in LHS*)
    let hf1 = CF.drop_hnodes_hf f.CF.formula_base_heap args in
    let p = MCP.pure_of_mix f.CF.formula_base_pure in
    let diff_svl = CP.diff_svl (CP.fv p) args in
    let p_w_quan = CP.mkExists_with_simpl TP.simplify diff_svl p None no_pos in
    let f1 = {f with CF.formula_base_pure = MCP.mix_of_pure p_w_quan;
        CF.formula_base_heap = hf1;} in
    let leqs = (MCP.ptr_equations_without_null f1.CF.formula_base_pure) in
    let f3 = if leqs =[] then f1 else
      let svl = prog_vars@args in
      let new_leqs = List.filter (fun (sv1,sv2) -> not (CP.mem sv1 svl && CP.mem_svl sv2 svl) ) leqs in
      (* let new_leqs = filter_eqs args prog_vars leqs in *)
      let f2 = CF.subst_b new_leqs f1 in
      {f2 with CF.formula_base_pure = MCP.mix_of_pure
              (CP.remove_redundant (MCP.pure_of_mix f2.CF.formula_base_pure))}
    in
    let p = MCP.pure_of_mix f3.CF.formula_base_pure in
    if CF.is_only_neqNull_pure p args ||
      List.for_all (CP.is_neq_exp) (CP.list_of_conjs p)
    then (fb, [],[(hp,args)], [])
    else
    (fb, [(hp,args,f3, rhs)],[], new_hps)
  in
  (*check hp is recursive or post_hp?*)
  if (CP.mem_svl hp r_hps || CP.mem_svl hp post_hps) then (lhsb, [], [(hp,args)], []) else
    let closed_args = CF.look_up_reachable_ptr_args prog hds hvs args in
    let undef_args = lookup_undef_args closed_args [] def_ptrs in
    if undef_args<> [] then
      (*not all args are well defined and in HIP. do not split*)
      let args_inst,args_ni =  partition_hp_args prog hp args in
      let wdef_svl = CP.diff_svl args undef_args in
      let wdef_ni_svl =  List.filter (fun (sv,_) -> CP.mem_svl sv wdef_svl
      ) args_ni in
      (*
        wdef_ni_svl: if not empty, do not split.
        TODO: forward hp defs to post-preds
      *)
      if wdef_ni_svl <> [] then
        (lhsb, [],[(hp,args)], [])
      else begin
        (*not all args are well defined and in SHAPE INFER. do split*)
        let undef_args_inst = List.filter (fun (sv,_) -> CP.mem_svl sv undef_args) args_inst in
        if undef_args_inst <> [] then
          (*hip or shape infer*)
          if not split_spatial then (lhsb, [],[(hp,args)], []) else
            let n_lhsb, new_ass, wdf_hpargs, ls_rhs=
              if !Globals.sa_sp_split_base then
                (*generate new hp decl for pre-preds*)
                let new_hf, new_hp = add_raw_hp_rel prog true true undef_args_inst pos in
                let nlhsb = CF.mkAnd_fb_hf lhsb new_hf pos in
                do_spit nlhsb (CF.formula_of_heap new_hf pos) [(new_hf,(new_hp, List.map fst undef_args_inst))]
              else
                do_spit lhsb (CF.mkTrue (CF.mkTrueFlow()) pos) []
            in
            match new_ass with
              | [(hp1,args1,n_lhsb1, rhs)] -> begin
                  let n_lhs1 = (CF.Base n_lhsb1) in
                    match CF.extract_hrel_head n_lhs1 with
                      | Some _ ->
                            (lhsb, [],[(hp,args)], [])
                      | None ->
                            (* let () = Debug.info_hprint (add_str "    n_lhs1" Cprinter.string_of_formula) n_lhs1 no_pos in *)
                            let p = (CF.get_pure n_lhs1) in
                            if CF.is_only_neqNull_pure p args1 ||
                              List.for_all (CP.is_neq_exp) (CP.list_of_conjs p)
                            then
                          (lhsb, [],[(hp,args)], [])
                        else (n_lhsb, new_ass, wdf_hpargs, ls_rhs)
                end
              | [] -> (lhsb, [],[(hp,args)], [])
              | _ -> report_error no_pos "sau.find_well_defined_hp"
        else
          do_spit lhsb (CF.mkTrue (CF.mkTrueFlow()) pos) []
      end
    else
      (*all args are well defined*)
      do_spit lhsb (CF.mkTrue (CF.mkTrueFlow()) pos) []

(*
  split_spatial: during assumption generating,
 do not do split_spatial, we need capture link_hps
*)
let find_well_defined_hp prog hds hvs ls_r_hpargs prog_vars post_hps 
      (hp,args) def_ptrs lhsb split_spatial pos=
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = pr_quad pr1 pr2 Cprinter.string_of_formula_base  Cprinter.prtt_string_of_formula in
  let pr4 = (pr_pair pr1 pr2) in
  let pr5 = pr_list (pr_pair Cprinter.prtt_string_of_h_formula pr4) in
  Debug.no_4 "find_well_defined_hp" Cprinter.string_of_formula_base pr4 pr2 pr2
      (pr_quad Cprinter.string_of_formula_base (pr_list_ln pr3) (pr_list pr4) pr5)
      (fun _ _  _ _ -> find_well_defined_hp_x prog hds hvs ls_r_hpargs
          prog_vars post_hps (hp,args) def_ptrs lhsb split_spatial pos)
      lhsb (hp,args) def_ptrs prog_vars

(*
  - case2: H(args) & p ==> G(args)
       H(args) & p ==> U(args)
       U(args) & p ==> G(args)
  -case 2: H(args) * z::node<args> & p ==> G(....) if p != true
   to capture path-sensitive unknown
*)
let split_guard_constrs_x prog is_guarded lhds lhvs post_hps ls_rhp_args (hp,args) lhsb pos=
  let keep_hds = List.filter (fun hd ->
      let svl = hd.CF.h_formula_data_node::hd.CF.h_formula_data_arguments in
      CP.intersect_svl svl args <> []
  ) lhds in
  let keep_hvs = List.filter (fun hv ->
      let svl = hv.CF.h_formula_view_node::hv.CF.h_formula_view_arguments in
      CP.intersect_svl svl args <> []
  ) lhvs in
  if keep_hds = [] && keep_hvs = [] then
    (*err-1b-split: split for guard*)
    if is_guarded then None else
      let ps = List.filter (fun p -> CP.intersect_svl (CP.fv p) args != [])
        (CP.split_conjunctions (MCP.pure_of_mix lhsb.CF.formula_base_pure)) in
      if ps = [] then
        None
      else
        let args_i =  get_hp_args_inst prog hp args in
        let ls_rhp_args1 = List.filter (fun (hp,_) -> CP.mem_svl hp post_hps) ls_rhp_args in
        if not (List.exists (fun (r_hp,r_args) ->
            let r_args_i = get_hp_args_inst prog r_hp r_args in
            (CP.intersect args_i r_args_i != [])
        ) ls_rhp_args1) then None
        else
          (*drop the lhs*)
          let n_orig_lhs_hf,_ = CF.drop_hrel_hf lhsb.CF.formula_base_heap [hp] in
          (*add new unk preds*)
          let hpdcl = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
          let new_hf, new_hp = add_raw_hp_rel prog true true hpdcl.Cast.hp_vars_inst pos in
          let _,args1 = CF.extract_HRel new_hf in
          let ss = List.combine args1 args in
          let n_constr_rhs_hf = (CF.h_subst ss new_hf) in
          let n_constr_rhs = CF.formula_of_heap n_constr_rhs_hf pos in
          let n_orig_lhs_hf2 = CF.mkStarH n_orig_lhs_hf n_constr_rhs_hf pos in
          let n_orig_lhsb = {lhsb with CF.formula_base_heap = n_orig_lhs_hf2} in
          let n_constr_lhf = CF.HRel (hp, List.map (fun sv -> CP.mkVar sv pos) args, pos) in
          let n_constr_lhs = CF.mkBase n_constr_lhf (MCP.mix_of_pure (CP.conj_of_list ps pos)) CvpermUtils.empty_vperm_sets CF.TypeTrue (CF.mkTrueFlow()) [] pos in
           (Some (n_orig_lhsb, (hp, n_constr_lhs,  n_constr_rhs, None), new_hp))
  else
    let g_hfs = (List.map (fun hd -> CF.DataNode hd) keep_hds)@
      (List.map (fun hv -> CF.ViewNode hv) keep_hvs) in
    let g_h = CF.join_star_conjunctions g_hfs in
    let all_svl = (List.fold_left (fun r hd -> r@hd.CF.h_formula_data_arguments) [] keep_hds)@
      (List.fold_left (fun r hv -> r@hv.CF.h_formula_view_arguments) [] keep_hvs) @args  in
    let p = CP.filter_var (MCP.pure_of_mix lhsb.CF.formula_base_pure) all_svl in
    let p1 = CP.prune_irr_eq p all_svl in
    let svl_p1 = CP.fv p1 in
    if CP.isConstTrue p1 || not (List.exists CP.is_node_typ svl_p1) then None else
      let g = CF.Base {lhsb with CF.formula_base_heap = g_h;
          CF.formula_base_pure = (MCP.mix_of_pure p1)} in
      let lhs = CF.formula_of_heap (CF.HRel (hp, List.map (fun sv -> CP.Var (sv, pos)) args, pos)) pos in
      (*generate new hp decl for top guard of pre-preds*)
      let hpdcl = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
      let new_hf, new_hp = add_raw_hp_rel prog true true hpdcl.Cast.hp_vars_inst pos in
      let _,args1 = CF.extract_HRel new_hf in
      let ss = List.combine args1 args in
      let rhs = CF.formula_of_heap (CF.h_subst ss new_hf) pos in
      Some (lhsb, (hp, lhs, rhs, Some g), new_hp)

let split_guard_constrs prog is_guarded lhds lhvs post_hps ls_rhp_args (hp,args) lhsb  pos=
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = Cprinter.prtt_string_of_formula in
  let pr4 = Cprinter.string_of_formula_base in
  Debug.no_2 "split_guard_constrs" pr4 (pr_pair pr1 pr2) (pr_opt (pr_triple pr4 (pr_quad pr1 pr3 pr3 (pr_opt pr3)) pr1))
      (fun _ _ -> split_guard_constrs_x prog is_guarded lhds lhvs post_hps ls_rhp_args (hp,args) lhsb  pos)
      lhsb (hp,args)

let detect_link_hp_x prog hds hvs r_hp r_args post_hps lhs_hpargs def_ptrs=
  let rec process_helper ls_hpargs=
    match ls_hpargs with
      | [] -> []
      | (hp,args)::rest ->
            if CP.eq_spec_var hp r_hp then process_helper rest else
              let closed_args = CF.look_up_reachable_ptr_args prog hds hvs args in
              let undef_args = lookup_undef_args closed_args [] def_ptrs in
              if undef_args <> [] && List.length undef_args < List.length args then
                let args_inst,_ =  partition_hp_args prog hp args in
                let undef_args_inst = List.filter (fun (sv,_) -> CP.mem_svl sv undef_args) args_inst in
                if undef_args_inst<>[] then
                  let undef_args1 = List.map fst undef_args_inst in
                  (*undef ini in lhs = rhs*)
                  if List.length undef_args1 = List.length r_args && CP.diff_svl undef_args1 r_args = [] then
                    [(r_hp,r_args)]
                  else process_helper rest
                else process_helper rest
              else process_helper rest
  in
  process_helper lhs_hpargs

let detect_link_hp prog hds hvs r_hp r_args post_hps lhs_hpargs def_ptrs=
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list (pr_pair pr1 pr2) in
  Debug.no_4 " detect_link_hp" pr1 pr2 pr3 pr2 pr3
      (fun _ _ _ _ -> detect_link_hp_x prog hds hvs r_hp r_args post_hps lhs_hpargs def_ptrs)
      r_hp r_args lhs_hpargs def_ptrs

let split_base_x prog hds hvs r_hps prog_vars post_hps (hp,args) def_ptrs lhsb=
  (*check hp is recursive?*)
  if (CP.mem_svl hp r_hps || CP.mem_svl hp post_hps) then ([],[(hp,args)]) else
    (* let closed_args = CF.look_up_reachable_ptr_args prog hds hvs args in *)
    (* let undef_args = lookup_undef_args closed_args [] def_ptrs in *)
    let f = keep_data_view_hrel_nodes_fb prog lhsb hds hvs args [(hp,args)] in
    (*we do NOT want to keep heap in LHS*)
    let hf1 = CF.drop_hnodes_hf f.CF.formula_base_heap args in
    let f1 = {f with CF.formula_base_heap = hf1;} in
    let p = MCP.pure_of_mix f1.CF.formula_base_pure in
    let diff_svl = CP.diff_svl (CP.fv p) args in
    let p_w_quan = CP.mkExists_with_simpl TP.simplify (*Omega.simplify*) diff_svl p None no_pos in
    let f3 = {f1 with CF.formula_base_pure = MCP.mix_of_pure p_w_quan} in
    (* let leqs = (MCP.ptr_equations_without_null f1.CF.formula_base_pure) in *)
    (* let f3 = if leqs =[] then f1 else *)
    (*   let svl = prog_vars@args in *)
    (*   let new_leqs = List.filter (fun (sv1,sv2) -> not (CP.mem sv1 svl && CP.mem_svl sv2 svl) ) leqs in *)
    (*   (\* let new_leqs = filter_eqs args prog_vars leqs in *\) *)
    (*   let f2 = CF.subst_b new_leqs f1 in *)
    (*   {f2 with CF.formula_base_pure = MCP.mix_of_pure *)
    (*           (CP.remove_redundant (MCP.pure_of_mix f2.CF.formula_base_pure))} *)
    (* in *)
    ([(hp,args,f3)],[])

let split_base prog hds hvs ls_r_hpargs prog_vars post_hps (hp,args) def_ptrs lhsb=
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = pr_triple pr1 pr2 Cprinter.string_of_formula_base in
  let pr4 = (pr_pair pr1 pr2) in
  Debug.no_4 "split_base" Cprinter.string_of_formula_base pr4 pr2 pr2 (pr_pair (pr_list_ln pr3) (pr_list pr4))
      (fun _ _  _ _ -> split_base_x prog hds hvs ls_r_hpargs prog_vars post_hps (hp,args) def_ptrs lhsb)
      lhsb (hp,args) def_ptrs prog_vars


let find_well_eq_defined_hp_x prog hds hvs lhsb eqs (hp,args)=
  let rec loop_helper rem_eqs=
    match rem_eqs with
      | [] -> ([], [(hp,args)])
      | (sv1,sv2)::rest -> if CP.mem_svl sv1 args && CP.mem_svl sv2 args then
          let f = keep_data_view_hrel_nodes_fb prog lhsb hds hvs args [(hp,args)] in
          ([(hp,args, f)],[])
        else loop_helper rest
  in
  if List.length args = 2 then
    let cmp_form = CP.get_cmp_form (MCP.pure_of_mix lhsb.CF.formula_base_pure) in
    loop_helper (eqs@cmp_form)
  else ([], [(hp,args)])

let find_well_eq_defined_hp prog hds hvs lhsb eqs (hp,args)=
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = pr_triple pr1 pr2 Cprinter.string_of_formula_base in
  let pr4 = (pr_pair pr1 pr2) in
  Debug.no_3 "find_well_eq_defined_hp" Cprinter.string_of_formula_base pr4 
      (pr_list (pr_pair pr1 pr1)) (pr_pair (pr_list_ln pr3) (pr_list pr4))
      (fun _ _ _ -> find_well_eq_defined_hp_x prog hds hvs lhsb eqs (hp,args))
      lhsb (hp,args) eqs

let generate_hp_ass unk_svl cond_p (hp,args,lfb,rf) =
  let knd = CP.RelAssume [hp] in
  let lhs = CF.Base lfb in
  let new_cs =  CF.mkHprel knd unk_svl [] [] lhs None rf cond_p in
  (* { *)
  (*     CF.hprel_kind = CP.RelAssume [hp]; *)
  (*     unk_svl = unk_svl;(\*inferred from norm*\) *)
  (*     unk_hps = []; *)
  (*     predef_svl = []; *)
  (*     hprel_lhs = CF.Base lfb; *)
  (*     hprel_guard = None; (\*guard exists with post-proving*\) *)
  (*     hprel_rhs = rf; *)
  (*     hprel_path = cond_p; *)
  (*     hprel_proving_kind = Others.proving_kind # top_no_exc; *)
  (* } *)
  (* in *)
  let () = x_dinfo_zp (lazy (("  new hp_ass " ^ (Cprinter.string_of_hprel_short new_cs)))) no_pos in
  new_cs

let generate_hp_ass i unk_svl cond_p (hp,args,lfb,rf) =
  Debug.no_1_num i "generate_hp_ass" pr_none pr_none (fun _ -> generate_hp_ass unk_svl cond_p (hp,args,lfb,rf)) 1


(************************************************)
(**aux2.slk**)
let simp_matching_x prog lhs rhs=
  let (_,mix_lf,_,_,_,_) = CF.split_components lhs in
  let (_,mix_rf,_,_,_,_) = CF.split_components rhs in
  let leqs = (MCP.ptr_equations_without_null mix_lf) in
  let reqs = (MCP.ptr_equations_with_null mix_rf) in
  let leqNulls = CP.remove_dups_svl ((MCP.get_null_ptrs mix_lf) ) in
  let reqNulls = CP.remove_dups_svl ( (MCP.get_null_ptrs mix_rf)) in
  let leqNull_ss = (List.map (fun (CP.SpecVar (t,id,p)) -> (CP.SpecVar (t,id,p), CP.SpecVar (t,"null", p))) leqNulls) in
  let reqNull_ss = (List.map (fun (CP.SpecVar (t,id,p)) -> (CP.SpecVar (t,id,p), CP.SpecVar (t,"null", p))) reqNulls) in
  let nlhs = CF.subst (leqs@leqNull_ss) lhs in
  let nrhs = CF.subst (leqs@reqs@leqNull_ss@reqNull_ss) rhs in
  match nlhs,nrhs with
    | CF.Base lhs_b, CF.Base rhs_b ->
        begin
            let l,r,matched = simplify_one_constr_b prog [] lhs_b rhs_b in
            if is_empty_f (CF.Base r) then
              let lps = List.map (fun (sv1,sv2) -> CP.mkPtrEqn sv1 sv2 no_pos) leqs in
              let lnull_ps =  List.map (fun sv-> CP.mkNull sv no_pos) leqNulls in
              let p = CP.conj_of_list (lps@lnull_ps) no_pos in
              let new_lhs = CF.mkAnd_pure (CF.simplify_pure_f_old (CF.Base l)) (MCP.mix_of_pure p) no_pos in
              (true,new_lhs)
            else
              (false,lhs)
        end
    | _ -> report_error no_pos "sa.simplify_one_constr"

let simp_matching prog lhs rhs=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_pair string_of_bool pr1 in
  Debug.no_2 "simp_matching" pr1 pr1 pr2
      (fun _ _ -> simp_matching_x prog lhs rhs) lhs rhs

(*END for drop non-selective subformulas*)
(************************************************************)
 (****************(*for infer_collect_hp*)*****************)
(************************************************************)
let update_hp_args hf renamed_hps=
  let rec look_up_helper hp0 args0 ls_hp_args=
    match ls_hp_args with
      | [] -> false,[]
      | (hp1,old_args1,new_args1)::hs ->
            if CP.eq_spec_var hp0 hp1 && (eq_spec_var_order_list args0 old_args1)  then (true, new_args1)
            else look_up_helper hp0 args0 hs
  in
  let rec helper hf0=
    match hf0 with
      | CF.HRel (hp, eargs, p ) ->
          let args0 = (List.fold_left List.append [] (List.map CP.afv eargs)) in
          let r,args1= look_up_helper hp args0 renamed_hps in
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
    if r then [((hp,args,new_args),np)] else []
  in
  let rename_one_rhp (hp,args)=
    let r,nlp,nrp,new_args= rhelper [] args lp rp false in
    if r then [((hp,args,new_args),(nlp,nrp))] else []
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

(************************************************************)
      (*******************END**************************)
(************************************************************)

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

(* (\************************************************************\) *)
(*       (\******************CHECKEQ************************\) *)
(* (\************************************************************\) *)
(* (\*==========check_relaxeq=============*\) *)
(* (\*currently we do not submit exists*\) *)
(* let check_stricteq_hnodes_x stricted_eq hns1 hns2= *)
(*   (\*allow dangl ptrs have diff names*\) *)
(*   let all_ptrs = *)
(*     if stricted_eq then [] else *)
(*     let ptrs1 = List.map (fun hd -> hd.CF.h_formula_data_node) hns1 in *)
(*     let ptrs2 = List.map (fun hd -> hd.CF.h_formula_data_node) hns2 in *)
(*     CP.remove_dups_svl (ptrs1@ptrs2) *)
(*   in *)
(*   let check_stricteq_hnode hn1 hn2= *)
(*     let arg_ptrs1 = (\* List.filter CP.is_node_typ *\) hn1.CF.h_formula_data_arguments in *)
(*     let arg_ptrs2 = (\* List.filter CP.is_node_typ *\)  hn2.CF.h_formula_data_arguments in *)
(*     if (hn1.CF.h_formula_data_name = hn2.CF.h_formula_data_name) && *)
(*         (CP.eq_spec_var hn1.CF.h_formula_data_node hn2.CF.h_formula_data_node) then *)
(*       let b = eq_spec_var_order_list arg_ptrs1 arg_ptrs2 in *)
(*       (\*bt-left2: may false if we check set eq as below*\) *)
(*       let diff1 = (Gen.BList.difference_eq CP.eq_spec_var arg_ptrs1 arg_ptrs2) in *)
(*       (\* (\\*for debugging*\\) *\) *)
(*       (\* let () = Debug.info_zprint (lazy (("     arg_ptrs1: " ^ (!CP.print_svl arg_ptrs1)))) no_pos in *\) *)
(*       (\* let () = Debug.info_zprint (lazy (("     arg_ptrs2: " ^ (!CP.print_svl arg_ptrs2)))) no_pos in *\) *)
(*       (\* let () = Debug.info_zprint (lazy (("     diff1: " ^ (!CP.print_svl diff1)))) no_pos in *\) *)
(*       (\*END for debugging*\) *)
(*       if stricted_eq then (\* (diff1=[]) *\)(b,[]) else *)
(*           (\*allow dangl ptrs have diff names*\) *)
(*         let diff2 = CP.intersect_svl diff1 all_ptrs in *)
(*         let ss = List.combine arg_ptrs1 arg_ptrs2 in *)
(*         (diff2 = [], (\* List.filter (fun (sv1, sv2) -> not(CP.eq_spec_var sv1 sv2)) *\) ss) *)
(*     else *)
(*       (false,[]) *)
(*   in *)
(*   let rec helper hn hns2 rest2= *)
(*     match hns2 with *)
(*       | [] -> (false,[], rest2) *)
(*       | hn1::hss -> *)
(*             let r,ss1 =  check_stricteq_hnode hn hn1 in *)
(*           if r then *)
(*             (true, ss1, rest2@hss) *)
(*           else helper hn hss (rest2@[hn1]) *)
(*   in *)
(*   let rec helper2 hns1 hns2 ss0= *)
(*     match hns1 with *)
(*       | [] -> if hns2 = [] then (true,ss0) else (false,ss0) *)
(*       | hn1::rest1 -> *)
(*           let r,ss1, rest2 = helper hn1 hns2 [] in *)
(*           if r then *)
(*             let n_rest1 = if ss1 = [] then rest1 else List.map (fun dn -> CF.dn_subst ss1 dn) rest1 in *)
(*             helper2 n_rest1 rest2 (ss0@ss1) *)
(*           else (false,ss0) *)
(*   in *)
(*   if (List.length hns1) <= (List.length hns2) then *)
(*     helper2 hns1 hns2 [] *)
(*   else (false,[]) *)

(* let check_stricteq_hnodes stricted_eq hns1 hns2= *)
(*   let pr1 hd = Cprinter.prtt_string_of_h_formula (CF.DataNode hd) in *)
(*   let pr2 = pr_list_ln pr1 in *)
(*   let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
(*   Debug.no_3 "check_stricteq_hnodes" string_of_bool pr2 pr2 (pr_pair string_of_bool pr3) *)
(*       (fun _ _ _ -> check_stricteq_hnodes_x stricted_eq hns1 hns2)  stricted_eq hns1 hns2 *)


(* let check_stricteq_hrels hrels1 hrels2= *)
(*    let check_stricteq_hr (hp1, eargs1, _) (hp2, eargs2, _)= *)
(*      let r = (CP.eq_spec_var hp1 hp2) in *)
(*      (\* ((Gen.BList.difference_eq CP.eq_exp_no_aset *\) *)
(*         (\*     eargs1 eargs2)=[]) *\) *)
(*      if r then *)
(*        let ls1 = List.concat (List.map CP.afv eargs1) in *)
(*        let ls2 = List.concat (List.map CP.afv eargs2) in *)
(*        (true, List.combine ls1 ls2) *)
(*      else (false,[]) *)
(*   in *)
(*   let rec helper hr hrs2 rest2= *)
(*     match hrs2 with *)
(*       | [] -> (false,[],rest2) *)
(*       | hr1::hss -> *)
(*           let r,ss1= check_stricteq_hr hr hr1 in *)
(*           if r then *)
(*             (true,ss1,rest2@hss) *)
(*           else helper hr hss (rest2@[hr1]) *)
(*   in *)
(*   let rec helper2 hrs1 hrs2 ss0= *)
(*     match hrs1 with *)
(*       | [] -> if hrs2 = [] then (true,ss0) else (false,ss0) *)
(*       | hr1::rest1 -> *)
(*           let r,ss, rest2 = helper hr1 hrs2 [] in *)
(*           if r then *)
(*             helper2 rest1 rest2 (ss0@ss) *)
(*           else (false,ss0) *)
(*   in *)
(*   if (List.length hrels1) = (List.length hrels2) then *)
(*     helper2 hrels1 hrels2 [] *)
(*   else (false,[]) *)

(* let check_stricteq_h_fomula_x stricted_eq hf1 hf2= *)
(*   let hnodes1, _, hrels1 = CF.get_hp_rel_h_formula hf1 in *)
(*   let hnodes2, _, hrels2 = CF.get_hp_rel_h_formula hf2 in *)
(*   let r,ss = check_stricteq_hrels hrels1 hrels2 in *)
(*   let helper hn= *)
(*     let n_hn = CF.h_subst ss (CF.DataNode hn) in *)
(*     match n_hn with *)
(*       | CF.DataNode hn -> hn *)
(*       | _ -> report_error no_pos "sau.check_stricteq_h_fomula" *)
(*   in *)
(*   if r then begin *)
(*       let n_hnodes1 = List.map helper hnodes1 in *)
(*       let n_hnodes2 = List.map helper hnodes2 in *)
(*       let r,ss1 = *)
(*         if (List.length n_hnodes1) <= (List.length n_hnodes2) then *)
(*           check_stricteq_hnodes stricted_eq n_hnodes1 n_hnodes2 *)
(*         else *)
(*           check_stricteq_hnodes stricted_eq n_hnodes2 n_hnodes1 *)
(*       in *)
(*       (r,ss@ss1) *)
(*     end *)
(*   else (false,[]) *)

(* let check_stricteq_h_fomula stricted_eq hf1 hf2= *)
(*   let pr1 = Cprinter.string_of_h_formula in *)
(*   let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
(*   Debug.no_3 " check_stricteq_h_fomula" string_of_bool pr1 pr1 (pr_pair string_of_bool pr2) *)
(*       (fun _ _ _ ->  check_stricteq_h_fomula_x stricted_eq hf1 hf2) stricted_eq hf1 hf2 *)

(* let checkeq_pure_x qvars1 qvars2 p1 p2= *)
(*   if CP.equalFormula p1 p2 then true else *)
(*      let p2 = CP.mkExists qvars2 p2 None no_pos in *)
(*      let b1,_,_ = x_add TP.imply_one 3 p1 p2 "sa:checkeq_pure" true None in *)
(*     if b1 then *)
(*       let p1 = CP.mkExists qvars1 p1 None no_pos in *)
(*       let b2,_,_ = x_add TP.imply_one 4 p2 p1 "sa:checkeq_pure" true None in *)
(*       b2 *)
(*     else false *)

(* let checkeq_pure qvars1 qvars2 p1 p2= *)
(*   let pr1 = !CP.print_formula in *)
(*   Debug.no_2 "checkeq_pure" pr1 pr1 string_of_bool *)
(*       (fun _ _ -> checkeq_pure_x qvars1 qvars2 p1 p2) p1 p2 *)

(* let check_relaxeq_formula_x args f1 f2= *)
(*   let qvars1, base_f1 = CF.split_quantifiers f1 in *)
(*   let qvars2, base_f2 = CF.split_quantifiers f2 in *)
(*   let hf1,mf1,_,_,_ = CF.split_components base_f1 in *)
(*   let hf2,mf2,_,_,_ = CF.split_components base_f2 in *)
(*   DD.ninfo_zprint (lazy (("   mf1: " ^(Cprinter.string_of_mix_formula mf1)))) no_pos; *)
(*   DD.ninfo_zprint (lazy (("   mf2: " ^ (Cprinter.string_of_mix_formula mf2)))) no_pos; *)
(*   (\* let r1,mts = CEQ.checkeq_h_formulas [] hf1 hf2 [] in *\) *)
(*   let r1,ss = check_stricteq_h_fomula false hf1 hf2 in *)
(*   if r1 then *)
(*     (\* let new_mf1 = xpure_for_hnodes hf1 in *\) *)
(*     (\* let cmb_mf1 = MCP.merge_mems mf1 new_mf1 true in *\) *)
(*     (\* let new_mf2 = xpure_for_hnodes hf2 in *\) *)
(*     (\* let cmb_mf2 = MCP.merge_mems mf2 new_mf2 true in *\) *)
(*     (\* (\\*remove dups*\\) *\) *)
(*     (\* let np1 = CP.remove_redundant (MCP.pure_of_mix cmb_mf1) in *\) *)
(*     (\* let np2 = CP.remove_redundant (MCP.pure_of_mix cmb_mf2) in *\) *)
(*     let np1 = CF.remove_neqNull_redundant_hnodes_hf hf1 (MCP.pure_of_mix mf1) in *)
(*     let np2 = CF.remove_neqNull_redundant_hnodes_hf hf2 (MCP.pure_of_mix mf2) in *)
(*     (\* DD.info_zprint (lazy (("   f1: " ^(!CP.print_formula np1)))) no_pos; *\) *)
(*     (\* DD.info_zprint (lazy (("   f2: " ^ (!CP.print_formula np2)))) no_pos; *\) *)
(*     (\* let r2,_ = CEQ.checkeq_p_formula [] np1 np2 mts in *\) *)
(*     let diff2 = List.map snd ss in *)
(*     let () = DD.ninfo_zprint (lazy (("   diff: " ^ (!CP.print_svl diff2)))) no_pos in *)
(*     let np11 = (\* CP.mkExists qvars1 np1 None no_pos *\) np1 in *)
(*     let np21 = (\* CP.mkExists qvars2 np2 None no_pos *\) np2 in *)
(*     let np12 = CP.subst ss np11 in *)
(*     (\* let _, bare_f2 = CP.split_ex_quantifiers np2 in *\) *)
(*     let svl1 = CP.fv np12 in *)
(*     let svl2 = CP.fv np21 in *)
(*     DD.ninfo_zprint (lazy (("   np12: " ^(!CP.print_formula np12)))) no_pos; *)
(*     DD.ninfo_zprint (lazy (("   np21: " ^ (!CP.print_formula np21)))) no_pos; *)
(*     let qvars1 = CP.remove_dups_svl ((CP.diff_svl svl1 (args@diff2))) in *)
(*     let qvars2 = CP.remove_dups_svl ((CP.diff_svl svl2 (args@diff2))) in *)
(*     let r2 = checkeq_pure qvars1 qvars2 np12 np21 in *)
(*     let () = DD.ninfo_zprint (lazy (("   eq: " ^ (string_of_bool r2)))) no_pos in *)
(*     r2 *)
(*   else *)
(*     false *)

(* let check_relaxeq_formula args f1 f2= *)
(*   let pr1 = Cprinter.string_of_formula in *)
(*   Debug.no_2 "check_relaxeq_formula" pr1 pr1 string_of_bool *)
(*       (fun _ _ -> check_relaxeq_formula_x args f1 f2) f1 f2 *)

(* (\*exactly eq*\) *)
(* let checkeq_pair_formula (f11,f12) (f21,f22)= *)
(*   (check_relaxeq_formula [] f11 f21)&&(check_relaxeq_formula [] f12 f22) *)

(* let rec checkeq_formula_list_x fs1 fs2= *)
(*   let rec look_up_f f fs fs1= *)
(*     match fs with *)
(*       | [] -> (false, fs1) *)
(*       | f1::fss -> if (check_relaxeq_formula [] f f1) then *)
(*             (true,fs1@fss) *)
(*           else look_up_f f fss (fs1@[f1]) *)
(*   in *)
(*   if List.length fs1 = List.length fs2 then *)
(*     match fs1 with *)
(*       | [] -> true *)
(*       | f1::fss1 -> *)
(*           begin *)
(*               let r,fss2 = look_up_f f1 fs2 [] in *)
(*               if r then *)
(*                 checkeq_formula_list fss1 fss2 *)
(*               else false *)
(*           end *)
(*   else false *)

(* and checkeq_formula_list fs1 fs2= *)
(*   let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in *)
(*   Debug.no_2 "checkeq_formula_list" pr1 pr1 string_of_bool *)
(*       (fun _ _ -> checkeq_formula_list_x fs1 fs2) fs1 fs2 *)

(*for post-preds*)
 let remove_pure_or_redundant_wg_x fs_wg=
   let drop_redundant conjs neg_of_disj =
     match neg_of_disj with
       | CP.Not (p, b,pos) ->
             let ps = CP.list_of_conjs p in
             let ps1 = List.filter (fun p1 -> not (List.exists (CP.equalFormula p1) conjs)) ps in
             if ps1 = [] then
               (false, CP.mkFalse pos)
             else (true, CP.Not (CP.conj_of_list ps1 pos, b,pos))
       | _ -> (true, neg_of_disj)
   in
   let drop_redundant_neg conjs neg_of_disj =
     match neg_of_disj with
       | CP.Not (p, b,pos) -> begin
             let ps = CP.list_of_conjs p in
             let ps1 = List.filter (fun p1 ->
                 let neg_p1 = CP.neg_eq_neq p1 in
                 let () = DD.ninfo_hprint (add_str "neg_p1: " (!CP.print_formula)) neg_p1 no_pos in
                 not (List.exists (CP.equalFormula neg_p1) conjs)
             ) ps in
              CP.disj_of_list (List.map CP.neg_eq_neq ps1) pos
         end
       | _ -> neg_of_disj
   in
   let rec helper f=
     match f with
       | CF.Base fb ->
             let ps = CP.list_of_conjs (MCP.pure_of_mix fb.CF.formula_base_pure) in
             let neg_of_disjs, conjs = List.partition ( CP.is_neg_of_consj) ps in
             let b,neg_of_disjs1 = List.fold_left (fun (rb,rps) orp ->
                 let b,norp = drop_redundant conjs orp in
                 (rb&&b, rps@[norp])
             ) (true,[]) neg_of_disjs in
             if not b then
               (false, CF.mkFalse_nf no_pos)
             else
               let neg_of_disjs2 = List.map (drop_redundant_neg conjs) neg_of_disjs1 in
               (* let () = DD.info_hprint (add_str "conjs: " (pr_list_ln !CP.print_formula)) conjs no_pos in *)
               (* let () = DD.info_hprint (add_str "neg_of_disjs2: " (pr_list_ln !CP.print_formula)) neg_of_disjs2 no_pos in *)
               (* let () = DD.info_hprint (add_str "neg_of_disjs: " (pr_list_ln !CP.print_formula)) neg_of_disjs no_pos in *)
               let np = CP.conj_of_list (conjs@neg_of_disjs2) fb.CF.formula_base_pos in
               (true, CF.Base {fb with CF.formula_base_pure = MCP.mix_of_pure np})
       | CF.Exists _ ->
             let qvars, base1 = CF.split_quantifiers f in
             let b,nf = helper base1 in
             if not b then (b,nf) else
               (true, CF.add_quantifiers qvars nf)
       | CF.Or orf -> begin
             let b1, nf1 = helper orf.CF.formula_or_f1 in
             let b2, nf2 = helper orf.CF.formula_or_f2 in
             match b1,b2 with
               | false, false -> false, nf1
               | false, true ->  b2, nf2
               | true, false -> b1,nf1
               | _ -> (true,
                     CF.Or {orf with
                         CF.formula_or_f1 = nf1;
                         CF.formula_or_f2 = nf2;
                     })
         end
   in
   List.fold_left (fun r (f,og) -> let b,nf= helper f in
     if b then r@[(nf,og)] else r
   ) [] fs_wg

let remove_pure_or_redundant_wg fs_wg=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln (pr_pair pr1 (pr_option pr1)) in
  Debug.no_1 "remove_pure_or_redundant_wg" pr2 pr2
      (fun _ -> remove_pure_or_redundant_wg_x fs_wg) fs_wg

let equiv_unify_x args fs=
  let fs1 = Gen.BList.remove_dups_eq (fun f1 f2 -> check_relaxeq_formula args f1 f2) fs in
  fs1

let equiv_unify args fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "equiv_unify" !CP.print_svl pr1 pr1
      (fun _ _ -> equiv_unify_x args fs) args fs

let equiv_unify_wg_x args fs_wg=
  let fs1_wg = Gen.BList.remove_dups_eq (fun (f1,_) (f2,_) -> check_relaxeq_formula args f1 f2) fs_wg in
  fs1_wg

let equiv_unify_wg args fs_wg=
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
  Debug.no_2 "equiv_unify_wg" !CP.print_svl pr1 pr1
      (fun _ _ -> equiv_unify_wg_x args fs_wg) args fs_wg

let remove_subsumed_pure_formula_x args ps=
  (*check ps01 <<= ps02*)
  let check_subsume (ps01,null_svl1) (ps02,null_svl2)=
    (List.length null_svl1 = List.length null_svl2) &&
        (CP.diff_svl null_svl1 null_svl2 = []) &&
        CP.equalFormula (CP.filter_var ps01 (CP.diff_svl args null_svl1))
        (CP.filter_var ps02 (CP.diff_svl args null_svl1))
  in
  let sort_fn (ps01,null_svl1) (ps02,null_svl2)=
    (* (List.length ps01) - (List.length ps02) *)
    (List.length null_svl1) - (List.length null_svl2)
  in
  (* let ls_ps = List.map CP.list_of_conjs ps in *)
  let ls_ps1 = List.sort sort_fn ps in
  let ls_ps2 = Gen.BList.remove_dups_eq check_subsume ls_ps1 in
  (* List.map (fun (ps,_) -> CP.join_conjunctions ps) ls_ps2 *)
  List.map fst ls_ps2

let remove_subsumed_pure_formula args ps=
  let pr1=pr_list_ln (pr_pair !CP.print_formula !CP.print_svl) in
  let pr2= pr_list_ln (!CP.print_formula) in
  Debug.no_1 "remove_subsumed_pure_formula" pr1 pr2
      (fun _ -> remove_subsumed_pure_formula_x args ps) ps

let remove_subsumed_pure_formula args fs=
  let helper f pos p=
    CF.mkAnd_pure f (MCP.mix_of_pure p) pos
  in
  if fs = [] then [] else
    let ps = List.map
      (fun f ->
          let p = CF.get_pure f in
          let mf = MCP.mix_of_pure p in
          let eqs = (MCP.ptr_equations_without_null mf) in
          let null_svl = MCP.get_null_ptrs (mf) in
          let null_svl1 = CF.find_close null_svl eqs in
          (p, null_svl1)
      ) fs
    in
    let ps1= remove_subsumed_pure_formula args ps in
    let emp_f = CF.mkTrue_nf no_pos in
    List.map (helper emp_f no_pos) ps1

(*=============common prefix equal=========*)
let check_com_pre_eq_formula_x f1 f2=
  let hf1,mf1,_,_,_,_ = CF.split_components f1 in
  let hf2,mf2,_,_,_,_ = CF.split_components f2 in
  DD.ninfo_zprint (lazy (("   mf1: " ^(Cprinter.string_of_mix_formula mf1)))) no_pos;
  DD.ninfo_zprint (lazy (("   mf2: " ^ (Cprinter.string_of_mix_formula mf2)))) no_pos;
  (* let r1,mts = CEQ.checkeq_h_formulas [] hf1 hf2 [] in *)
  let r1,ss = SY_CEQ.check_stricteq_h_fomula false hf1 hf2 in
  if r1 then
    (*remove dups*)
    let np1 = CP.remove_redundant (MCP.pure_of_mix mf1) in
    let np2 = CP.remove_redundant (MCP.pure_of_mix mf2) in
    DD.ninfo_zprint (lazy (("   p1: " ^(!CP.print_formula np1)))) no_pos;
    DD.ninfo_zprint (lazy (("   p2: " ^ (!CP.print_formula np2)))) no_pos;
    (* let r2,_ = CEQ.checkeq_p_formula [] np1 np2 mts in *)
    (*TODO: revise like checkeq_formula*)
    let r2 = CP.equalFormula np1 np2 in
    let () = DD.ninfo_zprint (lazy (("   eq: " ^ (string_of_bool r2)))) no_pos in
    r2
  else
    false

let check_com_pre_eq_formula f1 f2=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "check_com_pre_eq_formula" pr1 pr1 string_of_bool
      (fun _ _ -> check_com_pre_eq_formula_x f1 f2) f1 f2


let check_inconsistency hf mixf= CFU.check_inconsistency hf mixf
  (* let new_mf = CF.xpure_for_hnodes hf in *)
  (* let cmb_mf = MCP.merge_mems new_mf mixf true in *)
  (* not (TP.is_sat_raw cmb_mf) *)

let check_inconsistency_f f0 pure_f= CFU.check_inconsistency_f f0 pure_f
  (* let p = MCP.mix_of_pure (CF.get_pure pure_f) in *)
  (* let rec helper f= *)
  (*   match f with *)
  (*     | CF.Base fb -> check_inconsistency fb.CF.formula_base_heap p *)
  (*     | CF.Or orf -> (helper orf.CF.formula_or_f1) && (helper orf.CF.formula_or_f2) *)
  (*     | CF.Exists fe -> *)
  (*       (\*may not correct*\) *)
  (*         check_inconsistency fe.CF.formula_exists_heap p *)
  (* in *)
  (* helper f0 *)

(* let rec is_unsat_x f0= *)
(*   let rec helper f= *)
(*     match f with *)
(*       | CF.Base fb -> check_inconsistency fb.CF.formula_base_heap fb.CF.formula_base_pure *)
(*       | CF.Or orf -> (helper orf.CF.formula_or_f1) || (helper orf.CF.formula_or_f2) *)
(*       | CF.Exists fe -> *)
(*         (\*may not correct*\) *)
(*           check_inconsistency fe.CF.formula_exists_heap fe.CF.formula_exists_pure *)
(*   in *)
(*   helper f0 *)

let is_unsat f= CFU.is_unsat f
  (* let pr1 = Cprinter.prtt_string_of_formula in *)
  (* let pr2 = string_of_bool in *)
  (* Debug.no_1 "is_unsat" pr1 pr2 *)
  (*     (fun _ -> is_unsat_x f) f *)

let check_heap_inconsistency unk_hpargs f0=
  let do_check hf=
    let hpargs = CF.get_HRels hf in
    (*remove dangling*)
    let hpargs1 = List.filter
      (fun (hp0,args0) ->
          not(Gen.BList.mem_eq check_hp_arg_eq (hp0,args0) unk_hpargs))
      hpargs
    in
    Gen.BList.check_dups_eq eq_spec_var_order_list (List.map snd hpargs1)
  in
  let rec helper f=
    match f with
      | CF.Base fb -> do_check fb.CF.formula_base_heap
      | CF.Or orf -> (helper orf.CF.formula_or_f1) || (helper orf.CF.formula_or_f2)
      | CF.Exists fe ->
        (*may not correct*)
          do_check fe.CF.formula_exists_heap
  in
  helper f0
(************************************************************)
      (******************END CHECKEQ**********************)
(************************************************************)
let rec get_closed_ptrs_one rdn ldns rdns rcur_match ss=
  (* let () =  DD.info_zprint (lazy (("    rdn: " ^ (!CP.print_sv rdn) ))) no_pos in *)
  let rec find_args_subst largs rargs lm rm=
    match largs, rargs with
      | [],[] -> (lm,rm)
      | la::ls,ra::rs -> if CP.mem_svl ra rcur_match then
            (*find all matched previously. one lhs can match many rhs*)
            let l_ss = fst (List.split (List.filter (fun (_,r) -> CP.eq_spec_var r ra) ss)) in
            let () =  DD.ninfo_zprint (lazy (("    l_ss: " ^ (!CP.print_svl l_ss) ))) no_pos in
            if CP.mem_svl la l_ss then
               let () =  DD.ninfo_zprint (lazy (("    la: " ^ (!CP.print_sv la) ))) no_pos in
               let () =  DD.ninfo_zprint (lazy (("    ra: " ^ (!CP.print_sv ra) ))) no_pos in
              find_args_subst ls rs lm rm (*matched already*)
            else find_args_subst ls rs (lm@[la]) (rm@[ra])
          else find_args_subst ls rs (lm@[la]) (rm@[ra])
      | _ -> report_error no_pos "sa.get_closed_ptrs: 1"
  in
  let rec look_up_rdn m_dn rdns res=
    match rdns with
      | [] -> res
      | (data_name,node_name,args)::rest ->
          let r=
            if CP.mem_svl m_dn (node_name::args) then
              [(data_name,node_name,args)]
            else []
          in
          look_up_rdn m_dn rest (res@r)
  in
  if ldns = [] || rdns = [] then
    ([],[]) (*either lhs1 or rhs2 does not have any node*)
  else
    begin
        (* let (ld_name, lsv, largs) = List.hd ldn_match in *)
        (* let (rd_name, rsv, rargs) = List.hd rdn_match in *)
        let rec helper1 (ld_name, lsv, largs) rdn_m =
          match rdn_m with
            | [] -> []
            | (rd_name, rsv, rargs)::rs ->
                let () =  DD.ninfo_zprint (lazy (("    lsv: " ^ (!CP.print_sv lsv)))) no_pos in
                let () =  DD.ninfo_zprint (lazy (("    rsv: " ^ (!CP.print_sv rsv)))) no_pos in
                if (String.compare ld_name rd_name=0) && ((CP.eq_spec_var lsv rsv) || CP.intersect_svl rargs largs <> [])then
                  rsv::rargs
                else helper1 (ld_name, lsv, largs) rs
        in
        let rec helper2 ldn_m=
          match ldn_m with
            | [] -> ([],[]) (*all node intersected are diff in type*)
            | (ld_name, lsv, largs):: ls ->
                let lsv1 = CP.subs_one ss lsv in
                (* if CP.mem_svl lsv1 rcur_match then helper2 ls *)
                (* else *)
                begin
                  (* let () =  DD.info_zprint (lazy (("    largs: " ^ (!CP.print_svl (lsv::largs))))) no_pos in *)
                  let largs1 = List.map (CP.subs_one ss) largs in
                  (* let () =  DD.info_zprint (lazy (("    largs1: " ^ (!CP.print_svl (lsv1::largs1))))) no_pos in *)
                  (*look_up rdn in rdns*)
                  let cur_rdns = look_up_rdn rdn rdns [] in
                  let rargs = helper1 (ld_name, lsv1, largs1) cur_rdns in
                  (* let () =  DD.info_zprint (lazy (("    rargs: " ^ (!CP.print_svl (rargs))))) no_pos in *)
                  if rargs = [] then helper2 ls
                  else
                    find_args_subst (lsv::largs) rargs [] []
                end
        in
        let lm,rm = helper2 ldns in
        (* let () =  DD.info_zprint (lazy (("    lm " ^ (!CP.print_svl (lm))))) no_pos in *)
        (* let () =  DD.info_zprint (lazy (("    rm " ^ (!CP.print_svl (rm))))) no_pos in *)
        if lm = [] then ([],[]) (*all node intersected are diff in type*)
        else (rm, List.combine lm rm)
    end

(*check match node: rdns |- ldns *)
and get_closed_matched_ptrs ldns rdns rcur_match ss=
  let rec helper old_m old_ss inc_m=
    (* let () =  DD.info_zprint (lazy (("    old_m " ^ (!CP.print_svl old_m)))) no_pos in *)
    (* let () =  DD.info_zprint (lazy (("    inc_m " ^ (!CP.print_svl inc_m)))) no_pos in *)
    (*find matching ldns and rdns*)
    let r = List.map (fun m -> get_closed_ptrs_one m ldns rdns old_m old_ss) inc_m in
    let incr_match, incr_ss = List.split r in
    if incr_match = [] then
      old_m, old_ss
    else
      let n_incr_m = (List.concat incr_match) in
      helper (CP.remove_dups_svl (old_m@n_incr_m)) (old_ss@(List.concat incr_ss)) n_incr_m
  in
  if List.length ldns > List.length rdns then (false, rcur_match, ss) else
    let all_matched_svl1,subst1 = helper rcur_match ss rcur_match in
    (* let pr_ss = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
    (* let () =  Debug.info_zprint (lazy (("     subst1: " ^ (pr_ss subst1)))) no_pos in *)
    (*TODO: after match, check res_ldns > res_rdns --> false*)
    (true, all_matched_svl1,subst1)

(*
  - find the pattern of rhs1 in guard
  - apply the pattern in rhs2 to get the subsst
  - apply subst in rhs1. return the new rhs1
assume pattern is ONE datanode. enhance later
check-dll.ss: YES
swl-i.ss: NO
*)
let pattern_matching_with_guard_x rhs1 rhs2 guard match_svl check_pure=
  (************ INTERNAL ***********)
  let find_pattern ptr_node ptr_args pure_svl f=
    let hp_args = List.map (fun (_,args) -> args) (CF.get_HRels_f rhs1) in
    let v_args = List.map (fun vn -> vn.CF.h_formula_view_node::vn.CF.h_formula_view_arguments) (CF.get_views rhs1) in
    let sel_args = List.fold_left (fun ls (args) ->
        if CP.intersect_svl args match_svl = [] then ls
        else ls@args
    ) [] (hp_args@v_args) in
    let hd_args = ptr_node::ptr_args in
    let inter = CP.intersect_svl hd_args (sel_args@pure_svl) in
    let locs_pattern = get_all_locs hd_args inter in
    (inter, locs_pattern)
  in
  let apply_parttern_x locs hd_name f=
    let hds = get_hdnodes f in
    let sel_pats = List.fold_left (fun ls hd ->
        if String.compare hd_name hd.CF.h_formula_data_name = 0 then
          let hd_args = hd.CF.h_formula_data_node::hd.CF.h_formula_data_arguments in
          let () = x_tinfo_hp (add_str " hd_args:"  !CP.print_svl) hd_args no_pos in
          let () = x_tinfo_hp (add_str " match_svl:"  !CP.print_svl) match_svl no_pos in
          if CP.intersect_svl hd_args match_svl != [] then
            let sel_args = retrieve_args_from_locs hd_args locs in
            ls@[sel_args]
          else
            ls
        else ls
    ) [] hds
    in
    let () = x_tinfo_hp (add_str " sel_pats:" (pr_list !CP.print_svl)) sel_pats no_pos in
    match sel_pats with
      | [args] -> args
      | [] -> []
      | _ -> report_error no_pos "sau.pattern_matching_with_guard 1"
  in
  let apply_parttern locs hd_name f=
    let pr1 = Cprinter.prtt_string_of_formula in
    Debug.no_3 "apply_parttern" (pr_list string_of_int) pr_id pr1 !CP.print_svl
        (fun _ _ _ -> apply_parttern_x locs hd_name f)
        locs hd_name f
  in
  let rec combine_remove_eq ls1 ls2 res=
    match ls1,ls2 with
      | [], [] -> res
      | sv1::rest1, sv2::rest2 ->
            let new_res =
              if CP.eq_spec_var sv1 sv2 then
                res
              else (res@[(sv1,sv2)])
            in
            combine_remove_eq rest1 rest2 new_res
      | _ -> report_error no_pos "sau.pattern_matching_with_guard 2"
  in
  let process_pattern g_pure_svl hf=
    match hf with
      | CF.DataNode hd ->
            let inter_rhs1, hd_locs = find_pattern hd.CF.h_formula_data_node
              hd.CF.h_formula_data_arguments g_pure_svl rhs1 in
            let hd_name = hd.CF.h_formula_data_name in
            let inter_rhs2 =  apply_parttern hd_locs hd_name rhs2 in
            ( inter_rhs1, inter_rhs2, hd.CF.h_formula_data_node)
                (* | CF.ViewNode vd -> *)
      | _ -> report_error no_pos "sau. pattern_matching_with_guard 3"
  in
  (************END INTERNAL ***********)
  match guard with
    | None -> (false, rhs1, guard)
    | Some f -> begin
        let hf = match (CF.heap_of f) with
          | [a] -> a
          | _ -> report_error no_pos "SAU.pattern_matching_with_guard 3"
        in
        match hf with
          | CF.DataNode hd ->
                let g_pure_svl = CP.fv (CF.get_pure f) in
                (* let inter_rhs1, hd_locs, hd_name = find_pattern hd g_pure_svl rhs1 in *)
                (* let inter_rhs2 =  apply_parttern hd_locs hd_name rhs2 in *)
                let inter_rhs1, inter_rhs2, sv_node = process_pattern g_pure_svl hf in
                if inter_rhs2 = [] then (false,rhs1, guard) else
                  let ss = combine_remove_eq inter_rhs1 inter_rhs2 [] in
                  let () = DD.ninfo_hprint (add_str " ss:" (pr_list (pr_pair !CP.print_sv !CP.print_sv))) ss no_pos in
                  let nrhs1 = CF.subst ss rhs1 in
                  let nf = CF.drop_hnodes_f (CF.subst ss f) [sv_node] in
                  let n_lguard = CF.drop_dups nrhs1 nf in
                  if check_pure then
                    let np= CP.subst ss (CF.get_pure f) in
                    if is_unsat (CF.mkAnd_pure nrhs1 (MCP.mix_of_pure np) no_pos) then
                      (false, rhs1, guard)
                    else (true, nrhs1, (Some n_lguard))
                  else
                    (true, nrhs1, (Some n_lguard))
          | _ -> (false,rhs1, guard)
      end

let pattern_matching_with_guard rhs1 rhs2 (guard: CF.formula option)
      match_svl1 check_pure=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 ohf= match ohf with
    | None -> "None"
    | Some hf -> Cprinter.prtt_string_of_formula hf
  in
  let pr3 = !CP.print_svl in
  Debug.no_5 "pattern_matching_with_guard" pr1 pr1 pr2 pr3 string_of_bool (pr_triple string_of_bool pr1 pr2)
      (fun _ _ _ _ _ -> pattern_matching_with_guard_x rhs1 rhs2 guard
          match_svl1 check_pure)
      rhs1 rhs2 guard match_svl1 check_pure

(*
step 1: apply transitive implication
        B |= C ---> E
  ---------------------------------
  c1 = A |- B ;c2 = C |- D ===> c3=A |- D * E

Note: subst if the lhs is equal (frozen) and not complex
*)
let rec find_imply prog lunk_hps runk_hps lhs1 rhs1 lhs2 rhs2 (lguard1: CF.formula option) equal_hps complex_hps=
  let sort_hps_x hps = List.sort (fun (CP.SpecVar (_, id1,_),_)
      (CP.SpecVar (_, id2, _),_)-> String.compare id1 id2) hps
  in
  let sort_hps hps=
    let pr1 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
    Debug.no_1 "sort_hps" pr1 pr1
        (fun _ ->  sort_hps_x hps) hps
  in
 (*precondition: ls1 and ls2 are sorted*)
  (*we may enhance here, ls1, ls2 are not necessary the same: ls2 >= ls1*)
  let rec check_hrels_imply ls1 ls2 ldns rdns lhs_hps subst matched args res_rename=
    match ls1,ls2 with
      | [],[] -> (subst,matched,args,res_rename)
      | (id1, args1)::ss1,(id2, args2)::ss2 ->
          if CP.eq_spec_var id1 id2 then
            begin
                (* if CP.mem_svl id1 lunk_hps && CP.mem_svl id2 runk_hps && *)
                (*   !Globals.sa_equiv_chain && not(check_equiv_chains args1 args2 ldns rdns) then *)
                (*   check_hrels_imply ls1 ss2 ldns rdns lhs_hps *)
                (*     (subst) (matched) (args) res_rename *)
                (* else *)
                  check_hrels_imply ss1 ss2 ldns rdns lhs_hps
                    (subst@(List.combine args1 args2)) (matched@[id2]) (args@args2) res_rename
            end
          else (* begin *)
              (* (\*unk hps*\) *)
              (* if CP.mem_svl id1 lunk_hps && CP.mem_svl id2 runk_hps && *)
              (*   List.length args1 = List.length args2 && not (List.mem id2 lhs_hps) then *)
              (*   check_hrels_imply ss1 ss2 lhs_hps (subst@(List.combine args1 args2)) *)
              (*       (matched@[id1]) (args@args2) (res_rename@[(id1,(id2,args2))]) *)
              (* else *)
            check_hrels_imply ls1 ss2 ldns rdns lhs_hps subst matched args res_rename
          (* end *)
      | [], _ -> (subst,matched,args,res_rename)
      | _ -> ([],[],[],[])
  in
  let transform_hrel (hp,eargs,_)= (hp, List.concat (List.map CP.afv eargs)) in
  let transform_dn dn= (dn.CF.h_formula_data_name, dn.CF.h_formula_data_node,
                        List.filter (fun (CP.SpecVar (t,_,_)) -> is_pointer t ) dn.CF.h_formula_data_arguments) in
  let rec is_inconsistent_x ss done_ss=
    match ss with
      | [] -> false
      | (sv1,sv2)::rest->
          try
              let sv22 = List.assoc sv1 (rest@done_ss) in
              if CP.eq_spec_var sv2 sv22 then
                is_inconsistent_x rest (done_ss@[(sv1,sv2)])
              else true
          with Not_found -> is_inconsistent_x rest (done_ss@[(sv1,sv2)])
  in
  let rec is_inconsistent ss done_ss=
    let pr1= pr_list (pr_pair !CP.print_sv !CP.print_sv) in
    Debug.no_1 "is_inconsistent" pr1 string_of_bool
        (fun _ -> is_inconsistent_x ss done_ss) ss
  in
  (*matching hprels and return subst*)
  (*renaming vars of the second constraint*)
  let rsvl2 = CF.fv (CF.Base rhs2) in
  let lsvl2 = CF.fv lhs2 in
  let svl2 = CP.remove_dups_svl (rsvl2@lsvl2) in
  let hp_names = CP.remove_dups_svl ((CF.get_hp_rel_name_formula lhs2)@(CF.get_hp_rel_name_bformula rhs2)) in
  (*remove hp name*)
  let svl21 = CP.diff_svl svl2 hp_names in
  let fr_svl2 = CP.fresh_spec_vars svl21 in
  let sst = List.combine svl21 fr_svl2 in
  let rhs2 = CF.subst_b sst rhs2 in
  let lhs2 = CF.subst sst lhs2 in
  (*END*)
  let ldns,lvns,lhrels = CF.get_hp_rel_bformula lhs1 in
  let () = Debug.ninfo_zprint (lazy (("    rhs after subst: " ^ (Cprinter.prtt_string_of_formula_base rhs2)))) no_pos in
  let rdns,_,rhrels = CF.get_hp_rel_bformula rhs2 in
  let l_rhrels = sort_hps (List.map transform_hrel lhrels) in
  let r_rhrels = sort_hps (List.map transform_hrel rhrels) in
  (*m_args2: matched svl of rhs2*)
  let subst,matched_hps, m_args2,rhs_hps_rename = check_hrels_imply l_rhrels r_rhrels ldns rdns (List.map fst l_rhrels) [] [] [] [] in
  let () = Debug.ninfo_zprint (lazy (("    matched_hps: " ^ (!CP.print_svl matched_hps)))) no_pos in
  let () = Debug.ninfo_zprint (lazy (("    complex_hps: " ^ (!CP.print_svl complex_hps)))) no_pos in
  let r=
    if matched_hps = [] || ((CP.intersect_svl matched_hps complex_hps <> []) (* || CP.intersect_svl matched_hps equal_hps = [] *)) then None
    else
      begin
        (*for debugging*)
        (* let () = Debug.info_zprint (lazy (("     m_args2: " ^ (!CP.print_svl  m_args2)))) no_pos in *)
        (* let pr_ss = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
        (* let () =  Debug.info_zprint (lazy (("     subst: " ^ (pr_ss subst)))) no_pos in *)
        (*END for debugging*)
        (*matching hnodes (in matched_hps) and return subst*)
        let lhns1 = List.map transform_dn ldns in
        let rhns1 = List.map transform_dn rdns in
        (*all_matched_svl2: all matched slv of rhs2*)
        let is_node_match, all_matched_svl1,subst1 = get_closed_matched_ptrs lhns1 rhns1 (* cur_node_match  *)m_args2 subst in
        if not is_node_match then None else
          let all_matched_svl2 = all_matched_svl1 @ m_args2 in
          (* let () = Debug.info_zprint (lazy (("    all matched 1: " ^ (!CP.print_svl all_matched_svl1)))) no_pos in *)
          let () = Debug.ninfo_zprint (lazy (("    all matched 2: " ^ (!CP.print_svl all_matched_svl2)))) no_pos in
          (* let () =  Debug.info_zprint (lazy (("     subst1: " ^ (pr_ss subst1)))) no_pos in *)
          if (is_inconsistent subst1 []) then None else
            let n_lhs1 = CF.subst_b subst1 lhs1 in
            (*check pure implication*)
            (* let  nldns ,nlvns,_ = CF.get_hp_rel_bformula n_lhs1 in *)
            (*loc-1b1.slk*)
            (* let lmf = CP.filter_var_new (MCP.pure_of_mix n_lhs1.CF.formula_base_pure)
               (CF.look_up_reachable_ptr_args prog nldns nlvns all_matched_svl2) in *)
            let lmf = (MCP.pure_of_mix n_lhs1.CF.formula_base_pure) in
            let rmf = (MCP.pure_of_mix rhs2.CF.formula_base_pure) in
            let lmf, subst1, n_lhs1=
              let b, n_subst1 = CP.checkeq lmf rmf subst1 in
              if b then
                (CP.subst n_subst1 lmf, n_subst1, CF.subst_b n_subst1 lhs1)
              else
                (lmf, subst1,n_lhs1)
            in
            (*get rele pure of lhs2*)
            let rmf1 = CP.mkAnd rmf (CF.get_pure lhs2) no_pos in
            (* let () = Debug.ninfo_zprint (lazy (("    n_lhs1: " ^ (Cprinter.string_of_formula_base n_lhs1)))) no_pos in *)
            (*ptrs: cmpare node. pure --> quantifiers*)
            let () = Debug.ninfo_zprint (lazy (("    lmf: " ^ (!CP.print_formula lmf)))) no_pos in
            let () = Debug.ninfo_zprint (lazy (("    rmf1: " ^ (!CP.print_formula rmf1)))) no_pos in
            let b,_,_ = x_add TP.imply_one 5 rmf1 lmf "sa:check_hrels_imply" true None in
            let lpos = (CF.pos_of_formula lhs2) in
            if b then
              (*node match *)
              let r_nodes = List.map (fun (_,sv,_) -> sv) rhns1 in
              let lnodes_match, rnodes_match = List.fold_left
                (fun (l_match,r_match) (_,sv,_) ->
                  let sv1 = CP.subs_one subst1 sv in
                  if CP.mem_svl sv1 r_nodes then (l_match@[sv1],r_match@[sv1])
                  else (l_match,r_match)
              ) ([],[]) lhns1
              in
              (* let () = Debug.info_zprint (lazy (("    lnodes_match: " ^ (!CP.print_svl lnodes_match)))) no_pos in *)
              (* let () = Debug.info_zprint (lazy (("    rnodes_match: " ^ (!CP.print_svl rnodes_match)))) no_pos in *)
              (* let () = Debug.info_zprint (lazy (("    n_lhs1: " ^ (Cprinter.prtt_string_of_formula_base n_lhs1)))) no_pos in *)
              (* let () = Debug.info_zprint (lazy (("    rhs2: " ^ (Cprinter.prtt_string_of_formula_base rhs2)))) no_pos in *)
              let l_res = {n_lhs1 with
                  CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf
                      n_lhs1.CF.formula_base_heap CF.select_dnode
                      CF.select_vnode select_hrel lnodes_match lnodes_match matched_hps}
              in
              (*drop hps and matched svl in n_rhs2*)
              let r_res = {rhs2 with
                  CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf
                      rhs2.CF.formula_base_heap CF.select_dnode
                      CF.select_vnode select_hrel rnodes_match rnodes_match matched_hps;
                  CF.formula_base_pure = MCP.mix_of_pure
                      (CP.filter_var_new
                          (MCP.pure_of_mix rhs2.CF.formula_base_pure) (CP.diff_svl (CF.fv (CF.Base rhs2)) all_matched_svl2))}
              in
              let n_lhs2 = (* CF.subst ss2 *) lhs2 in
              (*end refresh*)
              (*combine l_res into lhs2*)
              let l =  CF.mkStar n_lhs2 (CF.Base l_res) CF.Flow_combine lpos in
              let n_rhs1a = CF.subst subst1 rhs1 in
              (*avoid clashing --> should refresh remain svl of r_res*)
              let r_res1 = (* CF.subst ss2 *) (CF.Base r_res) in
              (* let () = Debug.info_zprint (lazy (("    r_res1: " ^ (Cprinter.prtt_string_of_formula r_res1)))) no_pos in *)
              (* let () = Debug.info_zprint (lazy (("    n_rhs1a: " ^ (Cprinter.string_of_formula n_rhs1a)))) no_pos in *)
              let _, n_rhs1, n_lguard1 = pattern_matching_with_guard n_rhs1a r_res1 lguard1
                m_args2 true in
              let () = Debug.ninfo_zprint (lazy (("    n_rhs1: " ^ (Cprinter.string_of_formula n_rhs1)))) no_pos in
              (*elim duplicate hprel in r_res1 and n_rhs1*)
              let nr_hprel = CF.get_HRels_f n_rhs1 in
              let nrest_hprel = CF.get_HRels_f r_res1 in
              let diff3 = Gen.BList.intersect_eq check_hp_arg_eq nr_hprel nrest_hprel in
              (* let () = Debug.info_zprint (lazy (("    diff3: " ^ ((pr_list (pr_pair !CP.print_sv !CP.print_svl)) diff3)))) no_pos in *)
              let r_res2,_ = CF.drop_hrel_f r_res1 (List.map (fun (hp,_) -> hp) diff3) in
              let r = CF.mkStar n_rhs1 r_res2 CF.Flow_combine (CF.pos_of_formula n_rhs1) in
              (* let () = Debug.info_zprint (lazy (("    l: " ^ (Cprinter.string_of_formula l)))) no_pos in *)
              (* let () = Debug.info_zprint (lazy (("    r: " ^ (Cprinter.string_of_formula r)))) no_pos in *)
              (Some (l, r,subst1, sst,n_lguard1))
            else None
      end
  in
  r


(******************************************************************)
   (****************SIMPL HP PARDEF/CF.formula*****************)
(******************************************************************)

(*root = p && p:: node<_,_> ==> root = p& root::node<_,_> & *)
let mk_expl_root r f0=
  let rec find_r_subst ss res=
    match ss with
      | [] -> res
      | (sv1,sv2)::tl->
          if CP.eq_spec_var r sv1 then
            find_r_subst tl (res@[(sv2,sv1)])
          else if CP.eq_spec_var r sv2 then
            find_r_subst tl (res@[(sv1,sv2)])
          else find_r_subst tl (res)
  in
  let rec helper f=
    match f with
    | CF.Base fb ->
        let eqs = (MCP.ptr_equations_without_null fb.CF.formula_base_pure) in
        let r_ss = find_r_subst eqs [] in
        let new_h1 =
          if r_ss= [] then fb.CF.formula_base_heap else
            CF.h_subst r_ss fb.CF.formula_base_heap
        in
        CF.Base {fb with CF.formula_base_heap = new_h1}
    | CF.Exists _ ->
          let qvars, base1 = CF.split_quantifiers f in
          let nf = helper base1 in
          CF.add_quantifiers qvars nf
    | _ -> report_error no_pos "sau.mk_expl_root: not handle yet"
  in
  helper f0

(*fix subst*)
let filter_unconnected_hf args hf=
  let hds =  get_hdnodes_hf hf in
  let ptrs = List.map (fun hd -> hd.CF.h_formula_data_node) hds in
  let tail_ptrs = List.concat (List.map (fun hd ->
      List.filter CP.is_node_typ hd.CF.h_formula_data_arguments) hds) in
  let unconnected_ptr = CP.diff_svl ptrs (tail_ptrs@args) in
  CF.drop_hnodes_hf hf unconnected_ptr

let filter_fn h_svl p=
  if CP.is_eq_exp p then
    let p_svl = CP.fv p in
    (CP.diff_svl p_svl h_svl) = []
  else true

let remove_irr_eqs_x keep_svl p=
  let rec rearrang_eq ls res=
    match ls with
      | [] -> res
      | (sv1,sv2)::ss -> begin
          let b1= CP.mem_svl sv1 keep_svl in
          let b2 = CP.mem_svl sv2 keep_svl in
          match b1,b2 with
            | true,true -> rearrang_eq ss res
            | true,false -> rearrang_eq ss (res@[(sv2,sv1)])
            | false,true -> rearrang_eq ss (res@[(sv1,sv2)])
            | _ -> rearrang_eq ss res
      end
  in
  let eqs = (MCP.ptr_equations_without_null (MCP.mix_of_pure p)) in
  let eqs1 = rearrang_eq eqs [] in
  let eqs2 = Gen.BList.remove_dups_eq
    (fun (sv11,_) (sv21,_) -> CP.eq_spec_var sv11 sv21) eqs1
  in
  let p1 = CP.subst eqs2 p in
  let cons = CP.list_of_conjs p1 in
  let cons1 = CP.remove_redundant_helper cons [] in
  let cons2 = List.filter (filter_fn keep_svl) cons1 in
  let new_p = (CP.conj_of_list cons2 no_pos) in
  new_p,eqs2

let remove_irr_eqs keep_svl p=
  let pr1 = !CP.print_formula in
  let pr2 = fun (a,_) -> pr1 a in
  Debug.no_2 "remove_irr_eqs" !CP.print_svl pr1 pr2
      (fun _ _ -> remove_irr_eqs_x keep_svl p)  keep_svl p

let rec elim_irr_eq_exps prog args f=
  match f with
    | CF.Base fb ->
          let hd_nodes,hv_nodes,hrels = CF.get_hp_rel_formula f in
          let keep_ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes args in
          let largs = List.fold_left (fun r (_,eargs,_) -> let svl= List.concat (List.map CP.afv eargs) in
          if CP.intersect_svl svl keep_ptrs != [] then r@svl else r
          ) [] hrels in
          let keep_ptrs1 = CP.remove_dups_svl (keep_ptrs@largs) in
          let new_p,ss = remove_irr_eqs keep_ptrs1 (MCP.pure_of_mix fb.CF.formula_base_pure) in
          let _,new_p1 =  CP.prune_irr_neq new_p keep_ptrs1 in
          let new_h1 = CF.h_subst ss fb.CF.formula_base_heap in
          let new_h2 = filter_unconnected_hf args new_h1 in
          let eqNulls = MCP.get_null_ptrs (MCP.mix_of_pure new_p1) in
          let ps2 = List.filter (fun p ->
              if CP.is_eq_between_vars p then
                CP.diff_svl (CP.fv p) eqNulls != []
              else true
          ) (CP.list_of_conjs new_p1) in
          let new_p2 = CP.conj_of_list ps2 (CP.pos_of_formula new_p1) in
          CF.Base {fb with CF.formula_base_pure = MCP.mix_of_pure new_p2;
              CF.formula_base_heap = new_h2}
    | CF.Exists fe ->
        let qvars, base1 = CF.split_quantifiers f in
        let nf = elim_irr_eq_exps prog args base1 in
        CF.add_quantifiers qvars nf
    | _ -> report_error no_pos "sau. elim_irr_eq_exps: not handle yet"

let remove_dups_pardefs_x grp=
  let eq_pardefs (_,args1,_,f1,_) (_,args2,_,f2,_)=
    let ss = List.combine args1 args2 in
    let nf1 = CF.subst ss f1 in
    SY_CEQ.check_relaxeq_formula args1 nf1 f2
  in
  Gen.BList.remove_dups_eq eq_pardefs grp

let remove_dups_pardefs grp=
  let pr1 = (pr_list_ln string_of_par_def_w_name_short) in
  Debug.no_1 "remove_dups_pardefs" pr1 pr1
      (fun _ -> remove_dups_pardefs_x grp) grp

let remove_dups_pardefs_w_neqNull_x grp=
  let norm args0 (a1,args1,og,f1,a4)=
    let ss = List.combine args1 args0 in
    let nf1 = CF.subst ss f1 in
    (a1,args1,og,f1,a4,nf1)
  in
  let get_expl_svl f=
    let hds = get_hdnodes f in
    List.map (fun hd -> hd.CF.h_formula_data_node) hds
  in
  let process_one args0 expl_svl (a11,args1,og1,a13,a14,f1) rem=
    let neqNull_svl1 = CF.get_neqNull f1 in
    let rec helper l_rem=
    match l_rem with
      | [] ->
          let ss = List.combine args0 args1 in
          let neqNull_svl12 = List.map (CP.subs_one ss) neqNull_svl1 in
          let expl_svl1 = List.map (CP.subs_one ss) expl_svl in
          let hpargs = List.concat (snd (List.split (CF.get_HRels_f a13))) in
          (* let () = Debug.info_zprint (lazy (("    hpargs:" ^ (!CP.print_svl hpargs)))) no_pos in *)
          (* let () = Debug.info_zprint (lazy (("    neqNull_svl12:" ^ (!CP.print_svl neqNull_svl12)))) no_pos in *)
          let neq_svl = CP.intersect_svl neqNull_svl12 (expl_svl1@a14@hpargs) in
          let newf = CF.remove_neqNull_svl neq_svl a13 in
          if is_empty_f newf then [] else
            [(a11,args1,og1,newf,a14,f1)]
      | (a21,args2,og2,a23,a24,f2)::tl ->
          let neqNull_svl2 = CF.get_neqNull f2 in
          let () = Debug.ninfo_zprint (lazy (("    neqNull_svl1:" ^ (!CP.print_svl neqNull_svl1)))) no_pos in
          let () = Debug.ninfo_zprint (lazy (("    neqNull_svl2:" ^ (!CP.print_svl neqNull_svl2)))) no_pos in
          let neqNull_svl11 = CP.diff_svl neqNull_svl1 neqNull_svl2 in
          if neqNull_svl11 = [] then
            let b = SY_CEQ.check_relaxeq_formula args2 f1 f2 in
            if b then [] else helper tl
          else
            if CP.diff_svl neqNull_svl11 expl_svl = [] then
              let new_f1 = CF.remove_neqNull_svl neqNull_svl11 f1 in
              let new_f2 = CF.drop_hnodes_f f2 neqNull_svl11 in
              let b = check_relaxeq_formula args2 new_f1 new_f2 in
              if b then [] else helper tl
            else helper tl
    in
    helper rem
  in
  let rec loop_helper args0 expl_svl ls res=
    match ls with
      | [] -> res
      | pdef_ex::tl ->
          let new_pdef = process_one args0 expl_svl pdef_ex (res@tl) in
          loop_helper args0 expl_svl tl (res@new_pdef)
  in
  (*to add the normalized f*)
  let args0,new_grp=
    match grp with
      | [] -> [],[]
      | (a1,args0,og0,f0,a4)::tl ->
          let new_tl = List.map (norm args0) tl in
          (args0,(a1,args0,og0,f0,a4,f0)::new_tl)
  in
  let expl_svl = CP.remove_dups_svl (List.concat (List.map (fun (_,_,_,_,_,f0) -> get_expl_svl f0) new_grp)) in
  let res_ex = loop_helper args0 expl_svl new_grp [] in
  (*to remove the normalized f*)
  List.map (fun (a1,a2,og,a3,a4,a5) -> (a1,a2,og,a3,a4)) res_ex

let remove_dups_pardefs_w_neqNull grp=
  let pr1 = (pr_list_ln string_of_par_def_w_name_short) in
  Debug.no_1 "remove_dups_pardefs_w_neqNull" pr1 pr1
      (fun _ -> remove_dups_pardefs_w_neqNull_x grp) grp

let remove_longer_common_prefix fs=
  let sort_fn (s1,_) (s2,_)=
    s1-s2
  in
  let sort_formula fs1=
    let fs_w_size = List.map (fun f -> (CF.get_h_size_f f, f)) fs1 in
    let sorted_fs_w_size = List.sort sort_fn fs_w_size in
    let fs2 = List.map snd sorted_fs_w_size in
    (* let pr = pr_list_ln Cprinter.prtt_string_of_formula in *)
    (*  let () = DD.info_zprint (lazy (( "sorted-increasing size: " ^ (pr fs2)))) no_pos in *)
    fs2
  in
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
  let fs1 = sort_formula fs in
  helper fs1 []

let remove_longer_common_prefix_wg fs_wg=
  let sort_fn (s1,_,_) (s2,_,_)=
    s1-s2
  in
  let sort_formula fs1_wg=
    let fs_w_size = List.map (fun (f,og) -> (CF.get_h_size_f f, f,og)) fs1_wg in
    let sorted_fs_w_size = List.sort sort_fn fs_w_size in
    let fs2_wg = List.map (fun (_,f,og) -> (f,og)) sorted_fs_w_size in
    (* let pr = pr_list_ln Cprinter.prtt_string_of_formula in *)
    (*  let () = DD.info_zprint (lazy (( "sorted-increasing size: " ^ (pr fs2)))) no_pos in *)
    fs2_wg
  in
  let rec helper cur res=
    match cur with
      | [] -> res
      | (f,og)::ss ->
          if List.exists
            (fun (f2,og2) ->
                check_com_pre_eq_formula f2 f)
            res then
            helper ss res
          else helper ss (res@[(f,og)])
  in
  let fs1_wg = sort_formula fs_wg in
  helper fs1_wg []

let remove_longer_common_prefix_w_unk unk_hps fs=
  let rec helper cur res=
    match cur with
      | [] -> res
      | f::ss ->
          let f1,_ = CF.drop_unk_hrel (*CF.subst_unk_hps_f*) f unk_hps in
          if List.exists
            (fun f2 ->
                let f21,_ = CF.drop_unk_hrel (*CF.subst_unk_hps_f*) f2 unk_hps in
                check_com_pre_eq_formula f1 f21)
            res then
            helper ss res
          else helper ss (res@[f])
  in
  helper fs []

let remove_longer_common_prefix_w_unk_g unk_hps fs=
  let rec helper cur res=
    match cur with
      | [] -> res
      | (f,g)::ss ->
          let f1,_ = CF.drop_unk_hrel (*CF.subst_unk_hps_f*) f unk_hps in
          if List.exists
            (fun (f2,g2) ->
                let f21,_ = CF.drop_unk_hrel (*CF.subst_unk_hps_f*) f2 unk_hps in
                check_com_pre_eq_formula f1 f21)
            res then
            helper ss res
          else helper ss (res@[(f,g)])
  in
  helper fs []

let remove_equiv_wo_unkhps_wg_x hp args0 unk_hps fs_wg=
  let rec partition_helper cur res_unkhp_fs res_elim_unkhp_fs rems=
    match cur with
      | [] -> res_unkhp_fs,res_elim_unkhp_fs,rems
      | (f,og)::ss -> begin
            match CF.extract_hrel_head f with
              | Some _ -> partition_helper ss res_unkhp_fs res_elim_unkhp_fs (rems@[(f,og)])
              | None -> let newf,b = CF.drop_unk_hrel f unk_hps in
                if not b then
                  partition_helper ss res_unkhp_fs res_elim_unkhp_fs (rems@[(f,og)])
                else
                  begin
                    let newf2,_ = CF.drop_hrel_f newf [hp] in
                    if is_empty_f newf2 then
                      partition_helper ss res_unkhp_fs res_elim_unkhp_fs rems
                    else
                      partition_helper ss (res_unkhp_fs@[(f,og)]) (res_elim_unkhp_fs@[(newf,og)]) rems
                  end
        end
  in
  let check_dups elim_unkhp_fs non_unkhp_fs=
    let rec helper1 fs r=
      match fs with
        | [] -> r
        | (f,og)::fss ->
            (*check duplicate or not ll-append5*)
            if List.exists (fun (f1,og1) -> check_relaxeq_formula args0 f f1) elim_unkhp_fs then
              helper1 fss r
            else helper1 fss (r@[(f,og)])
    in
    helper1 non_unkhp_fs []
  in
  let unkhp_fs,elim_unkhp_fs,rems= partition_helper fs_wg [] [] [] in
  let rems1 = check_dups elim_unkhp_fs rems in
  (unkhp_fs@rems1)

let remove_equiv_wo_unkhps_wg hp args0 unk_hps fs_wg=
  let pr = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
  Debug.no_2 "remove_equiv_wo_unkhps_wg" !CP.print_svl pr pr
      (fun _ _ -> remove_equiv_wo_unkhps_wg_x hp args0 unk_hps fs_wg)
      unk_hps fs_wg

(************************************)
(*check hf2 is subset of hf1*)
let check_subset_h_fomula_x hf1 hf2=
  let helper1 hn=
    (hn.CF.h_formula_data_node, hn.CF.h_formula_data_arguments)
  in
  let helper2 (hp, eargs,_)=
    (hp, List.concat (List.map CP.afv eargs))
  in
  let hnodes1, _, hrels1 = CF.get_hp_rel_h_formula hf1 in
  let hnodes2, _, hrels2 = CF.get_hp_rel_h_formula hf2 in
  (*quick check first*)
  if (List.length hnodes2) < (List.length hnodes1) &&
    (List.length hrels2) < (List.length hrels1) then
    let hnargs1 = List.map helper1 hnodes1 in
    let hnargs2 = List.map helper1 hnodes2 in
    let hpargs1 = List.map helper2 hrels1 in
    let hpargs2 = List.map helper2 hrels2 in
    if (Gen.BList.difference_eq check_hp_arg_eq hnargs2 hnargs1) = [] then
      ((Gen.BList.difference_eq check_hp_arg_eq hpargs2 hpargs1) = [])
    else
      false
  else
    false

let check_subset_h_fomula hf1 hf2=
  let pr1 = Cprinter.string_of_h_formula in
  Debug.no_2 " check_subset_h_fomula"  pr1 pr1 string_of_bool
      (fun _ _ ->  check_subset_h_fomula_x hf1 hf2) hf1 hf2

let remove_subset_x fs0=
  let size_compare f1 f2=
    let s1 = get_data_view_hrel_vars_formula f1 in
    let s2 = get_data_view_hrel_vars_formula f2 in
    (List.length s2) - (List.length s1)
  in
  let check_subset f1 f2=
    let (hf1,mf1,_,_,_,_) = CF.split_components f1 in
    let (hf2,mf2,_,_,_,_) = CF.split_components f2 in
    let np1 = CF.remove_neqNull_redundant_hnodes_hf hf1 (MCP.pure_of_mix mf1) in
    let np2 = CF.remove_neqNull_redundant_hnodes_hf hf2 (MCP.pure_of_mix mf2) in
    (* DD.info_zprint (lazy (("   p1: " ^(!CP.print_formula np1)))) no_pos; *)
    (* DD.info_zprint (lazy (("   p2: " ^ (!CP.print_formula np2)))) no_pos; *)
    let r2 = CP.equalFormula np1 np2 in
    if r2 then
      check_subset_h_fomula hf1 hf2
    else false
  in
  let rec helper fs res=
    match fs with
      | [] -> res
      | f::fss ->
          if List.exists
            (fun f2 -> check_subset f2 f) res then
            helper fss res
          else helper fss (res@[f])
  in
  let fs1 = List.sort size_compare fs0 in
  helper fs1 []

let remove_subset fs0=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_1 "remove_subset" pr1 pr1
      (fun _ -> remove_subset_x fs0) fs0
(************************************)

let is_trivial f (hp,args)=
  let hpargs = CF.get_HRels_f f in
  let b1 = List.exists (fun hpargs1 -> check_hp_arg_eq (hp,args) hpargs1) hpargs in
  b1||(is_empty_f f)

let is_trivial_constr cs=
  let l_ohp = CF.extract_hrel_head cs.CF.hprel_lhs in
  let r_ohp = CF.extract_hrel_head cs.CF.hprel_rhs in
  match l_ohp,r_ohp with
    | Some (hp1), Some (hp2) -> (* if *) CP.eq_spec_var hp1 hp2 (* then *)
        (* let _,largs = CF.extract_HRel_f cs.CF.hprel_lhs in *)
        (* let _,rargs = CF.extract_HRel_f cs.CF.hprel_rhs in *)
        (* eq_spec_var_order_list largs rargs *)
      (* else false *)
    | _ -> false

let is_not_left_rec_constr cs=
  let r_ohp = CF.check_and_get_one_hpargs cs.CF.hprel_rhs in
  match r_ohp with
    | [(rhp,r_args,_)] -> begin
        let lhds, _, lhpargs = CF.get_hp_rel_formula cs.CF.hprel_lhs in
        match lhpargs with
          | [(lhp,eargs,_)] -> if CP.eq_spec_var rhp lhp then
              (* let args = List.fold_left (fun acc e -> acc@(CP.afv e)) [] eargs in *)
              List.for_all (fun hd -> not (CP.mem_svl hd.CF.h_formula_data_node r_args) ) lhds
            else false
          | _ -> false
      end
    | _ -> false

let collect_post_preds prog constrs=
  let collect_one r_post_hps cs=
    let hps = (CF.get_hp_rel_name_formula cs.CF.hprel_lhs)@(CF.get_hp_rel_name_formula cs.CF.hprel_rhs) in
    let hps1 = CP.remove_dups_svl hps in
    let post_hps = List.filter (fun hp -> not (Cast.check_pre_post_hp prog.Cast.prog_hp_decls (CP.name_of_spec_var hp)))
      hps1 in
    (r_post_hps@post_hps)
  in
  let post_hps = List.fold_left collect_one [] constrs in
  CP.remove_dups_svl (post_hps)

let classify_post_fix_x constrs=
  let helper r_post_fix_hps cs=
    let lhds, lhvs, _ = CF.get_hp_rel_formula cs.CF.hprel_lhs in
    if lhds != [] || lhvs != [] then r_post_fix_hps else
      let l_hpargs =  CF.get_HRels_f cs.CF.hprel_lhs in
      let r_hpargs =  CF.get_HRels_f cs.CF.hprel_rhs in
      let inter_hpargs = List.filter (fun (r_hp,r_args) ->
          List.exists (fun (l_hp,l_args) -> CP.eq_spec_var l_hp r_hp &&
              not (eq_spec_var_order_list l_args r_args) ) l_hpargs
      ) r_hpargs in
      match inter_hpargs with
        | [] -> (r_post_fix_hps)
        | (hp,_)::_ -> (r_post_fix_hps@[hp])
  in
  let part_helper post_fix_hps (r_post, r_post_fix) cs=
    let rhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_rhs in
    if CP.intersect_svl rhs_hps post_fix_hps <> [] then
      (r_post, r_post_fix@[cs])
    else
      (r_post@[cs], r_post_fix)
  in
  let post_fix_hps = List.fold_left helper [] constrs in
  let post_constrs, post_fix_constrs = List.fold_left (part_helper post_fix_hps) ([],[]) constrs in
  (post_constrs, post_fix_hps, post_fix_constrs)

let classify_post_fix constrs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = !CP.print_svl in
  Debug.no_1 " classify_post_fix" pr1 (pr_triple pr1 pr2 pr1)
      (fun _ -> classify_post_fix_x constrs) constrs

 let weaken_strengthen_special_constr_pre_x is_pre cs=
  if is_trivial_constr cs then
    if is_pre then
    {cs with CF.hprel_rhs = CF.mkHTrue (CF. mkTrueFlow ()) (CF.pos_of_formula cs.CF.hprel_rhs)}
    else
      {cs with CF.hprel_lhs = CF.mkFalse (CF.flow_formula_of_formula cs.CF.hprel_rhs) (CF.pos_of_formula cs.CF.hprel_rhs)}
  else
    if not is_pre && is_not_left_rec_constr cs then
      {cs with CF.hprel_lhs = CF.mkFalse (CF.flow_formula_of_formula cs.CF.hprel_rhs) (CF.pos_of_formula cs.CF.hprel_rhs)}
    else
      cs

let weaken_strengthen_special_constr_pre is_pre cs=
  let pr1 = Cprinter.string_of_hprel_short in
  Debug.no_2 "weaken_strengthen_special_constr_pre" string_of_bool pr1 pr1
      (fun _ _ -> weaken_strengthen_special_constr_pre_x is_pre cs)
      is_pre cs

let convert_HTrue_2_None hpdefs=
  let do_convert (res_link_hps, res_hpdefs) ( orig)=
    let f = CF.disj_of_list (List.map fst orig.CF.def_rhs) no_pos in
    if CF.isStrictConstHTrue f then
      try
        let hpargs = CF.extract_HRel orig.CF.def_lhs in
        (res_link_hps@[hpargs], res_hpdefs)
      with _ -> (res_link_hps, res_hpdefs@[orig])
    else (res_link_hps, res_hpdefs@[orig])
  in
  List.fold_left do_convert ([],[]) hpdefs

let constr_cmp cs1 cs2=
    checkeq_pair_formula (cs1.CF.hprel_lhs,cs1.CF.hprel_rhs)
        (cs2.CF.hprel_lhs,cs2.CF.hprel_rhs)

let remove_dups_constr constrs=
  Gen.BList.remove_dups_eq constr_cmp constrs

let subst_equiv_hprel equivs constrs=
  let subst_one parts cs=
    let nlhs = List.fold_left (fun f0 (from_hps, to_hp) ->
        CF.subst_hprel f0 from_hps to_hp
    ) cs.CF.hprel_lhs parts
    in
    let nrhs = List.fold_left (fun f0 (from_hps, to_hp) ->
        CF.subst_hprel f0 from_hps to_hp
    ) cs.CF.hprel_rhs parts
    in
    {cs with CF.hprel_lhs = nlhs;
        CF.hprel_rhs = nrhs;}
  in
  if equivs = [] then constrs else
    let parts = partition_subst_hprel equivs [] in
    List.map (subst_one parts) constrs

let is_inconsistent_heap f =
  let ( hf,mix_f,_,_,_,_) = CF.split_components f in
  let eqNulls = CP.remove_dups_svl (MCP.get_null_ptrs mix_f) in
  let neqNull_svl = CP.get_neq_null_svl (MCP.pure_of_mix mix_f) in
  let ptrs = CF.get_ptrs hf in
  if CP.intersect_svl eqNulls (neqNull_svl@ptrs) <> [] then true else false

let simplify_one_formula_x prog args f=
  let f1 = elim_irr_eq_exps prog args f in
  (* let f1 = filter_var prog args f in *)
  f1

let simplify_one_formula prog args f=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  Debug.no_2 "simplify_one_formula" pr1 pr2 pr2
      (fun _ _ ->simplify_one_formula_x prog args f)
      args f

let elim_useless_rec_preds_x prog hp args fs_wg=
  let process_one (f,og)=
    let hpargs = CF.get_HRels_f f in
    let rec_hpargs = List.filter (fun (hp0,args1) -> (CP.eq_spec_var hp hp0)
        && CP.diff_svl args args1 != []
    ) hpargs in
    if rec_hpargs = [] then [(f,og)] else
      let hds, hvs,_ = CF.get_hp_rel_formula f in
      let args_i = get_hp_args_inst prog hp args in
      (* let cl_args = CF.look_up_reachable_ptr_args prog hds hvs args_i in *)
      (* if CP.intersect_svl cl_args (List.fold_left (fun ls (_,rec_args) -> *)
      (*     let rec_args_i = get_hp_args_inst prog hp rec_args in *)
      (*     ls@rec_args_i) [] rec_hpargs) = [] then *)
      if args_i = [] || (hds = [] && hvs = []) then
        let nf,_ = CF.drop_hrel_f f [hp] in
        let nf1 = simplify_one_formula prog args nf in
        if is_empty_f nf1 then [] else [(nf1,og)]
      else [(f,og)]
  in
  List.fold_left (fun r (f,og) -> r@(process_one (f, og))) [] fs_wg

let elim_useless_rec_preds prog hp args fs_wg=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
  Debug.no_3 "elim_useless_rec_preds" !CP.print_sv pr1 pr2 pr2
      (fun _ _ _ -> elim_useless_rec_preds_x prog hp args fs_wg)
      hp args fs_wg

(************************************************************)
    (****************END SIMPL HP PARDEF/CF.formula************)
(************************************************************)
let move_root args ldns=
  let rec move_root_to_top arg lldns rest=
    match lldns with
      | [] -> (false,rest)
      | hd::hds ->
            if CP.eq_spec_var arg hd.CF.h_formula_data_node then
              (true,lldns@rest)
            else move_root_to_top arg hds (rest@[hd])
  in
  let rec sel_root largs=
    match largs with
      | [] -> ldns
      | a::ass ->
            let b,res= move_root_to_top a ldns [] in
            if b then res
            else sel_root ass
  in
  sel_root args

let norm_two_hnodes_wrapper args sh_dns0 matched0 rest_dns2 ss0 =
  let rec get_subst_svl matcheds svl1 svl2 ss=
    match svl1,svl2 with
	 | [],[] -> ss
	 | v1::sl1,v2::sl2 ->
         if CP.eq_spec_var v1 v2 || CP.mem_svl v2 matcheds ||
           CP.mem_svl v2 args || CP.mem_svl v1 args
         then
		   get_subst_svl matcheds sl1 sl2 ss
	     else get_subst_svl matcheds sl1 sl2 (ss@[(v2,v1)])
	 | _ -> report_error no_pos "sau.norm_hnodes_x 1"
  in
  let rec look_up_one_hd hn1 lnds matched2 rest2=
    match lnds with
      | [] ->  ([],matched2, rest2)
      | hn2::ls ->
          if hn1.CF.h_formula_data_name = hn2.CF.h_formula_data_name &&
            CP.eq_spec_var hn1.CF.h_formula_data_node hn2.CF.h_formula_data_node
          then
		    (*return last args and remain*)
            (* let () = DD.info_zprint (lazy (("  svl1: " ^ (!CP.print_svl hn1.CF.h_formula_data_arguments)))) no_pos in *)
            (* let () = DD.info_zprint (lazy (("  svl2: " ^ (!CP.print_svl hn.CF.h_formula_data_arguments)))) no_pos in *)
            (get_subst_svl matched2 hn1.CF.h_formula_data_arguments
                 hn2.CF.h_formula_data_arguments [],
             matched2@[hn2.CF.h_formula_data_node],rest2@ls)
		  else look_up_one_hd hn1 ls matched2 (rest2@[hn2])
  in
  let helper hn lnds matched2 rest2=
    let last_ss,matched,rest= look_up_one_hd hn lnds matched2 rest2 in
    let fresh_rest = List.map (fun hd -> CF.h_subst last_ss (CF.DataNode hd)) rest in
    let fresh_rest1 = List.concat (List.map get_hdnodes_hf fresh_rest) in
    (last_ss,matched,fresh_rest1)
  in
  let rec norm_hnodes_two_hns sh_dns matched2 rest_dns2 ss=
    match sh_dns with
      | [] -> (matched2, rest_dns2, ss)
      |  hn::sh_ls ->
          let new_ss, n_matcheds2,n_rest2 = helper hn rest_dns2 matched2 [] in
             norm_hnodes_two_hns sh_ls n_matcheds2 n_rest2 (ss@new_ss)
  in 
  norm_hnodes_two_hns sh_dns0 matched0 rest_dns2 ss0

let norm_hnodes_wg_x args fs_wg=
  (* let rec get_subst_svl matcheds svl1 svl2 ss= *)
  (*   match svl1,svl2 with *)
  (*        | [],[] -> ss *)
  (*        | v1::sl1,v2::sl2 -> *)
  (*        if CP.eq_spec_var v1 v2 || CP.mem_svl v2 matcheds || *)
  (*          CP.mem_svl v2 args || CP.mem_svl v1 args *)
  (*        then *)
  (*       	   get_subst_svl matcheds sl1 sl2 ss *)
  (*            else get_subst_svl matcheds sl1 sl2 (ss@[(v2,v1)]) *)
  (*        | _ -> report_error no_pos "sau.norm_hnodes_x 1" *)
  (* in *)
  (* let rec look_up_one_hd hn1 lnds matched2 rest2= *)
  (*   match lnds with *)
  (*     | [] ->  ([],matched2, rest2) *)
  (*     | hn2::ls -> *)
  (*         if hn1.CF.h_formula_data_name = hn2.CF.h_formula_data_name && *)
  (*           CP.eq_spec_var hn1.CF.h_formula_data_node hn2.CF.h_formula_data_node *)
  (*         then *)
  (*       	    (\*return last args and remain*\) *)
  (*           (\* let () = DD.info_zprint (lazy (("  svl1: " ^ (!CP.print_svl hn1.CF.h_formula_data_arguments)))) no_pos in *\) *)
  (*           (\* let () = DD.info_zprint (lazy (("  svl2: " ^ (!CP.print_svl hn.CF.h_formula_data_arguments)))) no_pos in *\) *)
  (*           (get_subst_svl matched2 hn1.CF.h_formula_data_arguments *)
  (*                hn2.CF.h_formula_data_arguments [], *)
  (*            matched2@[hn2.CF.h_formula_data_node],rest2@ls) *)
  (*       	  else look_up_one_hd hn1 ls matched2 (rest2@[hn2]) *)
  (* in *)
  (* let helper hn lnds matched2 rest2= *)
  (*   let last_ss,matched,rest= look_up_one_hd hn lnds matched2 rest2 in *)
  (*   let fresh_rest = List.map (fun hd -> CF.h_subst last_ss (CF.DataNode hd)) rest in *)
  (*   let fresh_rest1 = List.concat (List.map get_hdnodes_hf fresh_rest) in *)
  (*   (last_ss,matched,fresh_rest1) *)
  (* in *)
  (* let rec norm_hnodes_two_hns sh_dns matched2 rest_dns2 ss= *)
  (*   match sh_dns with *)
  (*     | [] -> (matched2, rest_dns2, ss) *)
  (*     |  hn::sh_ls -> *)
  (*         let new_ss, n_matcheds2,n_rest2 = helper hn rest_dns2 matched2 [] in *)
  (*            norm_hnodes_two_hns sh_ls n_matcheds2 n_rest2 (ss@new_ss) *)
  (* in *)
  let norm_one_f base_ldns (f,og)=
    let hnds = get_hdnodes f in
    let _,_, ss = (* norm_hnodes_two_hns *) norm_two_hnodes_wrapper args base_ldns [] hnds [] in
    let cur_svl = CF.fv f in
    let to_subst = List.map snd ss in
    let inter= CP.intersect_svl (CP.remove_dups_svl cur_svl)
      (CP.remove_dups_svl to_subst) in
    let f1, og1=
      if inter = [] then (f,og) else
        let fr_inter = CP.fresh_spec_vars inter in
        let ss1 = List.combine inter fr_inter in
        (CF.subst ss1 f, CF.subst_opt ss1 og)
    in
    (CF.subst ss f1, CF.subst_opt ss og1)
  in
  if fs_wg = [] then fs_wg else
    let base_f, base_og = List.hd fs_wg in
    let base_ldns = get_hdnodes base_f in
    if base_ldns = [] then fs_wg else
      let base_ldns1 = move_root args base_ldns in
      let tl_fs_wg = List.map (fun (f,og) ->  norm_one_f base_ldns1 (f, og)) (List.tl fs_wg) in
      ((base_f,base_og)::tl_fs_wg)

let norm_hnodes_wg args fs_wg=
  let pr0 = Cprinter.prtt_string_of_formula in
  let pr1 = pr_list_ln (pr_pair pr0 (pr_option pr0)) in
  Debug.no_2 "norm_hnodes_wg" !CP.print_svl pr1 pr1
      (fun _ _ -> norm_hnodes_wg_x args fs_wg) args fs_wg

(*norm trg_g ===> src_g*)
let norm_guard_x args src_f trg_f trg_g=
  (********INTERNAL*********)
  let norm_one_f src_ldns trg_f=
    let hnds = get_hdnodes trg_f in
    let _,_, ss = (* norm_hnodes_two_hns *)norm_two_hnodes_wrapper args src_ldns [] hnds [] in
    ss
  in
  (********END INTERNAL*********)
  let src_ldns = get_hdnodes src_f in
  if src_ldns = [] then trg_g else
    let src_ldns1 = move_root args src_ldns in
    let ss =  norm_one_f src_ldns1 trg_f in
    let src_g = CF.subst ss trg_g in
    src_g

let norm_guard args src_f trg_f trg_g=
  let pr1 = Cprinter.prtt_string_of_formula in
  Debug.no_4 "norm_guard" !CP.print_svl pr1 pr1 pr1 pr1
      (fun _ _ _ _ -> norm_guard_x args src_f trg_f trg_g)
      args src_f trg_f trg_g

let generate_equiv_pdefs_x unk_hps pdef_grps=
  let get_succ_hps_pardef (_,_,f,_)=
    (CF.get_HRels_f f)
  in
  let rec lookup_succ_hps_grp rem_grps hp done_grps=
    match rem_grps with
      | [] -> (false,[],done_grps,[])
      | grp::tl -> begin
          match grp with
            | [] -> lookup_succ_hps_grp tl hp done_grps
            | (hp1,_,_,_)::_ ->
                if CP.eq_spec_var hp1 hp then
                  let succ_hpargs = List.concat (List.map get_succ_hps_pardef grp) in
                  let hps = CP.remove_dups_svl (List.map fst succ_hpargs) in
                   (true,hps, done_grps@tl,grp)
                else
                  lookup_succ_hps_grp tl hp (done_grps@[grp])
      end
  in
  let subst_equiv_hp_one_pdef from_hp to_hp (hp,args,f,unk_svl)=
    let new_f = CF.subst_hprel f [from_hp] to_hp in
    if is_trivial new_f (hp,args) then [] else
      [(hp,args,new_f,unk_svl)]
  in
  let subst_equiv_hp_one_grp from_hp to_hp grp=
    match grp with
      | [] -> []
      | (hp,_,_,_)::tl ->
          if CP.eq_spec_var from_hp hp then grp
          else
            List.concat (List.map (subst_equiv_hp_one_pdef from_hp to_hp) grp)
  in
  (*hp0 --> hp_equiv*)
  let gen_equiv_hps_one_hp equiv_hps pdef_grps0 (hp0,args0,p0)=
    let size0 =  List.length args0 in
    (*remove invalid equivs*)
    let equivs_hps = List.concat (List.map (fun (hp1,args1,_) ->
        if CP.eq_spec_var hp0 hp1 || List.length args1 <> size0 then []
        else [hp1])  equiv_hps)
    in
    if equivs_hps = [] then pdef_grps0 else
      let is_pdefined,succ_hps,other_grps,cur_grp = lookup_succ_hps_grp pdef_grps0 hp0 [] in
      let not_process = succ_hps@unk_hps in
      let real_equivs_hps = List.filter (fun hp1 -> not (CP.mem_svl hp1 not_process)) equivs_hps in
      let new_pdef_grps0=
        (* if real_equivs_hps = [] then pdef_grps0 else *)
        if is_pdefined  then pdef_grps0 else
      (*build new pdefs*)
          (* let new_pdefs = List.map (fun hp2 -> (hp0,args0, mkHRel_f hp2 args0 p0)) real_equivs_hps in *)
          (* other_grps@[(cur_grp@new_pdefs)] *)
          match real_equivs_hps with
            | [hp2] -> List.map (subst_equiv_hp_one_grp hp0 hp2) pdef_grps0
            | _ -> pdef_grps0
      in
      new_pdef_grps0
  in
  let gen_equiv_hps_one pdef_grps1 grp=
    let equiv_hps = List.concat (List.map (fun (_,_,f,_) ->
        CF.check_and_get_one_hpargs f) grp) in
    List.fold_left (gen_equiv_hps_one_hp equiv_hps) pdef_grps1 equiv_hps
  in
  let rec loop_helper pdef_grps2 done_hps=
    let rec helper ls=
      match ls with
        | [] -> pdef_grps2
        | grp::tl -> begin
            match grp with
              | (hp1,_,_,_)::_ ->
                  if CP.mem_svl hp1 done_hps then
                    helper tl
                  else
                    let new_grps = gen_equiv_hps_one pdef_grps2 grp in
                    loop_helper new_grps (done_hps@[hp1])
              | [] -> helper tl
        end
    in
    helper pdef_grps2
  in
  loop_helper pdef_grps []

let generate_equiv_pdefs unk_hps pdef_grps=
  let pr1 =  Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln (pr_list_ln (pr_quad !CP.print_sv !CP.print_svl pr1 !CP.print_svl)) in
  Debug.no_2 "generate_equiv_pdefs" !CP.print_svl pr2 pr2
      (fun _ _ -> generate_equiv_pdefs_x unk_hps pdef_grps) unk_hps pdef_grps


(************************************************************)
      (******************FORM HP DEF*********************)
(************************************************************)

(*check which parameters of a hp can be dropped*)
(*fs is a set of formulae of hp's definition*)
let drop_hp_arguments_x prog hp args0 fs_wg=
  let rec helper raw_defined_svl args res index=
    match args with
      | [] -> res
      | a::ass -> if (CP.mem_svl a raw_defined_svl) then
            helper raw_defined_svl ass (res) (index+1)
          else helper raw_defined_svl ass (res@[index]) (index+1)
  in
  let intersect_cand cands=
    let () = Debug.ninfo_zprint (lazy (("     cands: " ^ (let pr = pr_list Cprinter.string_of_list_int in pr cands)))) no_pos in
    if cands = [] then [] else
      let locs = List.fold_left (fun ls1 ls2 -> Gen.BList.intersect_eq (=) ls1 ls2) (List.hd cands) (List.tl cands) in
      locs
  in
  let rename_drop_args args1 locs0=
    let rec loop_helper args index res=
      match args with
        | [] -> res
        | a::ass ->
            if List.mem index locs0 then
              let new_a = CP.fresh_spec_var a in
              loop_helper ass (index+1) (res@[new_a])
            else loop_helper ass (index+1) (res@[a])
    in
    loop_helper args1 0 []
  in
  let process_one_f (f,g)=
    let def_vs_wo_args, hd_nodes, hv_nodes, hrs, eqs,eqNulls = find_defined_pointers_raw prog f in
    let used_svl = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes (def_vs_wo_args@eqNulls@args0) in
    let hpargs = (List.map (fun (hp1,eargs,_)-> hp1,(List.concat (List.map CP.afv eargs))) hrs) in
    let rec_hpargs, rem_hpargs = List.partition (fun (hp1, _) -> CP.eq_spec_var hp1 hp) hpargs in
    let rec_args = CP.remove_dups_svl (List.concat (List.map snd rec_hpargs)) in
     (*  match rec_hpargs with *)
    (*     | [] -> [] *)
    (*     | [(_,args)] -> args *)
    (*     | _ -> report_error no_pos "sau.drop_hp_arguments" *)
    (* in *)
    if rec_args = [] then [] else
      let res = helper (CP.remove_dups_svl
                            ((List.concat (List.map snd rem_hpargs))@
                                    used_svl@args0)) rec_args [] 0 in
      res
  in
  let cands = List.map process_one_f fs_wg in
  let cands1 = (List.filter (fun x -> x<>[]) cands) in
  let drops = intersect_cand cands1 in
  (*rename dropped args*)
  let new_args,new_fs_wg=
    if drops = [] then args0,fs_wg
    else
      (*simplify-remove irr things from fs*)
      let n_args = rename_drop_args args0 drops in
      let simplify_helper args2 (f,g)=
        let f1 = elim_irr_eq_exps prog args2 f in
        if (is_empty_f f1) then []
        else [(f1,g)]
      in
      if List.length n_args = List.length args0 then
        (args0, fs_wg)
      else
        let fs1_wg = List.fold_left (fun r f_og-> r@(simplify_helper n_args f_og)) [] fs_wg in
        (n_args,fs1_wg)
  in
  (new_args,new_fs_wg)

let drop_hp_arguments prog hp args0 fs_wg=
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
  let pr2 = !CP.print_svl in
  let pr3 = pr_pair pr2 pr1 in
  Debug.no_3 "drop_hp_arguments" !CP.print_sv pr2 pr1 pr3
      (fun _ _ _ -> drop_hp_arguments_x prog hp args0 fs_wg) hp args0 fs_wg


let get_longest_common_hnodes_two args shortes_ldns ldns2 eqs=
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
      | [] ->  ([],[],matched2, rest2)
      | hn1::ls ->
          (* let eq_svl = CF.find_close [hn1.CF.h_formula_data_node] eqs in *)
          if hn.CF.h_formula_data_name = hn1.CF.h_formula_data_name &&
            CP.eq_spec_var hn.CF.h_formula_data_node hn1.CF.h_formula_data_node
            (* CP.mem_svl hn.CF.h_formula_data_node eq_svl *)
          then
		    (*return last args and remain*)
            (* let () = DD.info_zprint (lazy (("  svl1: " ^ (!CP.print_svl hn1.CF.h_formula_data_arguments)))) no_pos in *)
            (* let () = DD.info_zprint (lazy (("  svl2: " ^ (!CP.print_svl hn.CF.h_formula_data_arguments)))) no_pos in *)
            (hn1.CF.h_formula_data_arguments,get_subst_svl hn1.CF.h_formula_data_arguments hn.CF.h_formula_data_arguments [],
             matched2@[hn1.CF.h_formula_data_node],rest2@ls)
		  else look_up_one_hd hn ls matched2 (rest2@[hn1])
  in
  let helper hn lnds matched2 rest2=
    let last_svl,last_ss,matched,rest= look_up_one_hd hn lnds matched2 rest2 in
    (* let fresh_rest = List.map (fun hd -> CF.h_subst last_ss (CF.DataNode hd)) rest in *)
    (* let fresh_rest1 = List.concat (List.map get_hdnodes_hf fresh_rest) in *)
    (last_svl,[],last_ss,matched,rest)
  in
  let rec look_up_min_hds sh_dns matched2 rest_dns2 ss last_ss last_svl=
    match sh_dns with
      | [] -> (matched2, rest_dns2, ss, last_ss,last_svl)
          (* report_error no_pos "sau.get_longest_common_hnodes_two" *)
          (* if length rest_dns2: mk pure equality all ss*)
      (*| [hn] ->
          let last_ss, n_matcheds2,n_rest2 =  helper hn rest_dns2 matched2 [] in
          (n_matcheds2, n_rest2, ss, last_ss)*)
      |  hn::sh_ls ->
          let new_last_svl,new_ss, new_last_ss, n_matcheds2,n_rest2 =  helper hn rest_dns2 matched2 [] in
            look_up_min_hds sh_ls n_matcheds2 n_rest2 (ss@new_ss) (new_last_ss@last_ss) new_last_svl
  in
  (*remove all dnodes in tail of args*)

  (* let () =  DD.info_zprint (lazy (("       args: " ^ (!CP.print_svl args)))) no_pos in *)
  look_up_min_hds shortes_ldns [] ldns2 [] [] []

let get_longest_common_vnodes_two args shortes_lvns lvns2 eqs=
  let rec get_subst_svl svl1 svl2 ss=
    match svl1,svl2 with
	 | [],[] -> ss
	 | v1::sl1,v2::sl2 -> if CP.eq_spec_var v1 v2 then
		get_subst_svl sl1 sl2 ss
	    else get_subst_svl sl1 sl2 (ss@[(v1,v2)])
	 | _ -> report_error no_pos "sau.get_longest_common_hnodes_two 1"
  in
  let rec look_up_one_hd hn lvns matched2 rest2=
    match lvns with
      | [] ->  ([],[],matched2, rest2)
      | hn1::ls ->
            if hn.CF.h_formula_view_name = hn1.CF.h_formula_view_name &&
              CP.eq_spec_var hn.CF.h_formula_view_node hn1.CF.h_formula_view_node
            then
	      (*return last args and remain*)
              (* let () = DD.info_zprint (lazy (("  svl1: " ^ (!CP.print_svl hn1.CF.h_formula_data_arguments)))) no_pos in *)
              (* let () = DD.info_zprint (lazy (("  svl2: " ^ (!CP.print_svl hn.CF.h_formula_data_arguments)))) no_pos in *)
              (hn1.CF.h_formula_view_arguments,get_subst_svl hn1.CF.h_formula_view_arguments hn.CF.h_formula_view_arguments [],
             matched2@[hn1.CF.h_formula_view_node],rest2@ls)
		  else look_up_one_hd hn ls matched2 (rest2@[hn1])
  in
  let helper hn lnds matched2 rest2=
    let last_svl,last_ss,matched,rest= look_up_one_hd hn lnds matched2 rest2 in
    (last_svl,[],last_ss,matched,rest)
  in
  let rec look_up_min_hvs sh_vns matched2 rest_vns2 ss last_ss last_svl=
    match sh_vns with
      | [] -> (matched2, rest_vns2, ss, last_ss,last_svl)
      |  hn::sh_ls ->
          let new_last_svl,new_ss, new_last_ss, n_matcheds2,n_rest2 =  helper hn rest_vns2 matched2 [] in
            look_up_min_hvs sh_ls n_matcheds2 n_rest2 (ss@new_ss) (new_last_ss@last_ss) new_last_svl
  in
  (*remove all dnodes in tail of args*)
  (* let () =  DD.info_zprint (lazy (("       args: " ^ (!CP.print_svl args)))) no_pos in *)
  look_up_min_hvs shortes_lvns [] lvns2 [] [] []

let process_one_f_x prog org_args args next_roots hp_subst sh_ldns com_eqNulls com_eqPures com_hps (ldns, f)=
  (* let () =  DD.info_zprint (lazy (("       new args: " ^ (!CP.print_svl args)))) no_pos in *)
  (* let pr2 = pr_list Cprinter.string_of_h_formula in *)
  (* let () = DD.info_zprint (lazy (("      sh_ldns:" ^ (pr2 (List.map (fun hd -> CF.DataNode hd) sh_ldns))))) no_pos in *)
  let ( _,mix_f,_,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mix_f) in
  let (matcheds2, rest2, ss, last_ss0,_) = get_longest_common_hnodes_two org_args sh_ldns ldns eqs in
  (*drop all matcheds*)
  let () =  DD.ninfo_zprint (lazy (("       matched 1: " ^ (!CP.print_svl matcheds2)))) no_pos in
  (* let () =  DD.info_zprint (lazy (("       eqNulls: " ^ (!CP.print_svl com_eqNulls)))) no_pos in *)
  (* let () =  DD.info_zprint (lazy (("       f: " ^ (Cprinter.prtt_string_of_formula f)))) no_pos in *)
  let nf1 = CF.drop_hnodes_f f matcheds2 in
  let () =  DD.ninfo_zprint (lazy (("       nf1: " ^ (Cprinter.prtt_string_of_formula nf1)))) no_pos in
  (* let () =  DD.info_zprint (lazy (("       args: " ^ (!CP.print_svl args)))) no_pos in *)
  let () =  DD.ninfo_zprint (lazy (("       last_ss0: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_sv) in pr last_ss0)))) no_pos in
  (*apply susbt ss*)
  let nf2 = CF.remove_com_pures nf1 com_eqNulls com_eqPures in
  (* let () =  DD.info_zprint (lazy (("       nf2: " ^ (Cprinter.prtt_string_of_formula nf2)))) no_pos in *)
  let nf3 = (* CF.subst *)CF.ins ss nf2 in
  let () =  DD.ninfo_zprint (lazy (("       nf3: " ^ (Cprinter.prtt_string_of_formula nf3)))) no_pos in
  (*if rest = [] then add pure equality all last_ss*)
  let nf5,last_ss=
    (*partition last_ss into two groups: one for subst another not*)
    (* let pr = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
    let last_ss1,last_ss2 = List.partition
      (fun (v1,v2) -> Gen.BList.difference_eq CP.eq_spec_var [v1;v2] args = [])
      last_ss0
    in
    (*mk eq for last_ss1*)
    let ps = List.concat (List.map (fun ((CP.SpecVar (t,v,p)) ,v2) ->
        if (is_pointer t)
        then [CP.mkPtrEqn v2 (CP.SpecVar (t,v,p)) no_pos]
        else []) last_ss1) in
    let p = CP.conj_of_list ps no_pos in
   (*apply subst last_ss2*)
    (* let () =  DD.ninfo_zprint (lazy (("       last_ss2: " ^ (pr last_ss2)))) no_pos in *)
    let nf4 = CF.ins last_ss2 nf3 in
    (*should remove x!=null if x is in matched2s*)
    (*combine them*)
    CF.mkAnd_pure nf4 (MCP.mix_of_pure p) no_pos,last_ss2
  in
  let () =  DD.ninfo_zprint (lazy (("       nf5: " ^ (Cprinter.prtt_string_of_formula nf5)))) no_pos in
  (*subst hp rel by its new definition if applicable*)
  let hprel,hf = hp_subst in
  let hp2,args2= CF.extract_HRel hprel in
  let hpargs = CF.get_HRels_f nf5 in
  let nf6 =
    try
      let args3 = List.assoc hp2 hpargs in
      (* let () =  DD.info_zprint (lazy (("       hf: " ^ (Cprinter.prtt_string_of_h_formula hf)))) no_pos in*)
      let slv_root = get_ptrs hprel in
      (* let () = DD.info_zprint (lazy (("       svl_roots: " ^ (Cprinter.string_of_spec_var_list slv_root)))) no_pos in *)
      let old_svl = get_ptrs hf in
      (*rename everything except root*)
      let old_svl1 = Gen.BList.difference_eq CP.eq_spec_var old_svl slv_root in
      let fresh_svl = CP.fresh_spec_vars old_svl1 in
      let ss = List.combine old_svl1 fresh_svl in
      let n_hf = CF.h_subst (ss) hf in
      let nf5a,n_hf2=
        (*base case has at least one node?*)
        let hds= get_hdnodes_hf n_hf in
        if hds=[] then (nf5,n_hf) else
          let () = DD.ninfo_zprint (lazy (("       next_roots: " ^ (Cprinter.string_of_spec_var_list next_roots)))) no_pos in
          let hds1= get_hdnodes nf5 in
          let last_svl = CF.look_up_reachable_ptr_args prog hds1 [] next_roots in
          let () = DD.ninfo_zprint (lazy (("      last_svl: " ^ (Cprinter.string_of_spec_var_list last_svl)))) no_pos in
          let () = DD.ninfo_zprint (lazy (("      args3: " ^ (Cprinter.string_of_spec_var_list args3)))) no_pos in
          (*is recursive?*)
          let inter = CP.intersect_svl last_svl args3 in
          let () = DD.ninfo_zprint (lazy (("       inter: " ^ (Cprinter.string_of_spec_var_list inter)))) no_pos in
          if  inter <> [] then
            (*find commond pattern: even/odd. testcase: sll-del*)
            (*todo: should have better refinement*)
            let hds2 = get_hdnodes_hf n_hf in
            let n1 = List.length hds1 in
            if (n1 = 0) || ((List.length hds2) mod 2 = n1 mod 2) then
              let nf5b = CF.drop_hnodes_f nf5 last_svl in
              (* let ss1 = List.combine inter next_roots in *)
              let nf5b0 = (* CF.subst ss1 *) nf5b in
              (nf5b0,n_hf)
            else
              (* let nf5b0 = CF.subst ss1 nf5 in *)
              let n_hf1 =  CF.drop_hnodes_hf n_hf (List.map (fun hn -> hn.CF.h_formula_data_node) hds) in
              let hp_args = CF.get_HRels n_hf1 in
              let fst_args = match hp_args with
                | [(_,args0)] -> args0
                | _ -> report_error no_pos "sau.process_one_f: sth wrong 1"
              in
              let ss2 = List.combine fst_args inter in
              let n_hf2 = CF.h_subst ss2 n_hf1 in
              let () =  DD.info_zprint (lazy (("       n_hf2 1: " ^ (Cprinter.prtt_string_of_h_formula n_hf2)))) no_pos in
              (nf5, n_hf2)
          else (nf5,n_hf)
      in
      let () =  DD.ninfo_zprint (lazy (("       n_hf2: " ^ (Cprinter.prtt_string_of_h_formula n_hf2)))) no_pos in
      let () =  DD.ninfo_zprint (lazy (("       nf5a: " ^ (Cprinter.prtt_string_of_formula nf5a)))) no_pos in
      let nf6 = CF.subst_hrel_f nf5a [(hprel, n_hf2)] in
      nf6
    with Not_found -> nf5
  in
  let nf7 = CF.drop_exact_hrel_f nf6 com_hps com_eqPures in
  let () =  DD.ninfo_zprint (lazy (("       nf6: " ^ (Cprinter.prtt_string_of_formula nf6)))) no_pos in
  let () =  DD.ninfo_zprint (lazy (("       nf7: " ^ (Cprinter.prtt_string_of_formula nf7)))) no_pos in
  nf7

let process_one_f prog org_args args next_roots hp_subst sh_ldns com_eqNulls com_eqPures com_hps (ldns, f)=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 (a,b,_) = let pr = pr_pair !CP.print_sv (pr_list !CP.print_exp) in
  pr (a,b)
  in
  Debug.no_5 "process_one_f" pr1 pr1 pr2 (pr_list !CP.print_formula) (pr_list pr3) pr2
      (fun _ _ _ _ _-> process_one_f_x prog org_args args next_roots hp_subst sh_ldns com_eqNulls
          com_eqPures com_hps (ldns, f))
      org_args args f com_eqPures com_hps


(* let get_shortest_lnds ll_ldns min= *)
(*   let rec helper ll= *)
(*   match ll with *)
(*     | [] -> report_error no_pos "sau.get_shortest_lnds" *)
(*     | (ldns,f)::lls -> if List.length ldns = min then *)
(*           (ldns,f) *)
(*         else helper lls *)
(*   in *)
(*   helper ll_ldns *)

let get_min_common_x prog args unk_hps ll_ldns_lvns=
  let datanode_helper dns=
    let closed_args = (CF.look_up_reachable_ptr_args prog dns [] args) in
    let dns1 = List.filter (fun dn -> CP.mem_svl dn.CF.h_formula_data_node closed_args) dns in
    (List.length dns1, dns1)
  in
  let viewnode_helper vns=
    let closed_args = (CF.look_up_reachable_ptr_args prog [] vns args) in
    let vns1 = List.filter (fun vn -> CP.mem_svl vn.CF.h_formula_view_node closed_args) vns in
    (List.length vns1, vns1)
  in
  (*todo: should check eqFormula*)
  let helper_pure_hprels f =
    let ( hf,mix_f,_,_,_,_) = CF.split_components f in
    let eqNulls = CP.remove_dups_svl (MCP.get_null_ptrs mix_f) in
    let ps = CP.list_of_conjs (MCP.pure_of_mix mix_f) in
    let hprels = CF.get_hprel_h_formula hf in
	eqNulls,ps,hprels
  in
  let rec helper ll r_min r_hns r_hvs r_eqNulls r_ps r_hprels=
  match ll with
    | [] -> r_min,r_hns,r_hvs,r_eqNulls,r_ps,r_hprels
    | (lnds,lvds, f)::lls ->
          let ns,nhds = datanode_helper lnds in
          let vs,vhds = viewnode_helper lvds in
          let eqNulls,ps,hprels = helper_pure_hprels f in
	  let new_eqNulls = CP.intersect_svl r_eqNulls eqNulls in
          let new_ps = Gen.BList.intersect_eq CP.equalFormula ps r_ps in
          let new_hprels =
            let keep_unk_hpargs = List.filter (fun (hp,_,_) -> CP.mem_svl hp unk_hps) (r_hprels@hprels) in
            let r1 = Gen.BList.intersect_eq CF.eq_hprel r_hprels hprels in
            Gen.BList.remove_dups_eq (fun (hp1,_,_) (hp2,_,_) ->
                CP.eq_spec_var hp1 hp2) (keep_unk_hpargs@r1)
          in
          let new_min = (ns+vs) in
          if new_min < r_min then
            helper lls new_min nhds vhds new_eqNulls new_ps new_hprels
          else helper lls r_min r_hns r_hvs new_eqNulls new_ps new_hprels
  in
  (*start with length of the first one*)
  if ll_ldns_lvns = [] then (0,[],[],[],[],[]) else
    let f_dns, f_vns,ff = List.hd ll_ldns_lvns in
    let f_node_min, fdns = datanode_helper f_dns in
    let f_view_min, fvns = viewnode_helper  f_vns in
    let eqNull,eqPures, hprels = helper_pure_hprels ff in
    helper (List.tl ll_ldns_lvns) (f_node_min+f_view_min) fdns fvns eqNull eqPures hprels

let get_min_common prog args unk_hps ll_ldns_lvns=
  let pr1 = !CP.print_svl in
  let pr2 hd= Cprinter.prtt_string_of_h_formula (CF.DataNode hd) in
  let pr2a hv= Cprinter.prtt_string_of_h_formula (CF.ViewNode hv) in
  let pr3 = pr_list pr2 in
  let pr4 = pr_list !CP.print_formula in
  let pr5 hrel = Cprinter.prtt_string_of_h_formula (CF.HRel hrel) in
  let pr6 = pr_hexa string_of_int pr3 (pr_list pr2a) pr1 pr4 (pr_list pr5) in
  let pr7 = fun (_,_,f) -> Cprinter.prtt_string_of_formula f in
  Debug.no_3 "get_min_common" pr1 pr1 (pr_list_ln pr7) pr6
      (fun  _ _ _ -> get_min_common_x prog args unk_hps ll_ldns_lvns)
      args unk_hps ll_ldns_lvns


(*
  x::node<_,p> ===> p can not be a root
*)

let closer_ranking prog unk_hps fs root_cand args0=
  let build_conf f=
    let hds, hvs, hrs = CF.get_hp_rel_formula f in
    (* let hpargs = List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs))) hrs in *)
    let (_ ,mix_lf,_,_,_,_) = CF.split_components f in
    let eqNulls = MCP.get_null_ptrs mix_lf in
    let eqs = (MCP.ptr_equations_without_null mix_lf) in
    let def_vs = eqNulls @ (List.map (fun hd -> hd.CF.h_formula_data_node) hds)
      @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) in
    let unk_svl = List.fold_left (fun r (hp,eargs,_) -> if CP.mem_svl hp unk_hps then r@(List.fold_left List.append [] (List.map CP.afv eargs)) else r
    ) [] hrs in
    let xpure_hpargs = CF.get_xpure_view f in
    let xpure_svl = List.fold_left (fun r (hp,args) -> if CP.mem_svl hp unk_hps then r@args else r) [] xpure_hpargs in
    let def_ptrs = CP.remove_dups_svl (CF.find_close (CP.remove_dups_svl (def_vs@unk_svl@eqNulls@xpure_svl)) (eqs)) in
    (hds, hvs, def_ptrs, eqNulls)
  in
  let fs_config4 = List.map build_conf fs in
  let fs_config,ls_eqNulls = List.fold_left (fun (r1,r2) (a,b,c,d) -> (r1@[(a,b,c)],r2@[d])) ([],[]) fs_config4 in
  let exam_conf r (hds,hvs,def_ptrs0)=
    let () = DD.ninfo_hprint (add_str "        r:" !CP.print_sv) r no_pos in
    let def_ptrs = CP.remove_dups_svl (def_ptrs0@(List.filter (fun sv -> not (CP.eq_spec_var sv r)) args0)) in
    let closed_args = List.filter (CP.is_node_typ) (CF.look_up_reachable_ptr_args prog hds hvs [r]) in
    let () = DD.ninfo_hprint (add_str "        closed_args:" !CP.print_svl) closed_args no_pos in
    let () = DD.ninfo_hprint (add_str "        def_ptrs:" !CP.print_svl) def_ptrs no_pos in
    let undef_args = lookup_undef_args closed_args [] def_ptrs in
    let () = DD.ninfo_hprint (add_str "        undef_args:" !CP.print_svl) undef_args no_pos in
    undef_args = []
  in
  (* let args = r::(List.filter (fun sv -> not (CP.eq_spec_var r sv)) args0) in *)
  let eqNulls = if ls_eqNulls = [] then [] else
    List.fold_left (fun r ls -> CP.intersect_svl r ls) (List.hd ls_eqNulls) (List.tl ls_eqNulls) in
  let new_cand0 = List.filter (fun r -> (CP.is_node_typ r) &&
     List.for_all (exam_conf r) fs_config) root_cand
  in
  let () = DD.ninfo_zprint (lazy (("  new_cands0: " ^ (!CP.print_svl new_cand0) ))) no_pos in
  let new_cand =
    match unk_hps with
      | hp::_ -> (
            try
              let ins_args = get_hp_args_inst prog hp args0 in
              let ins_cand, rem = List.partition (fun sv -> CP.mem_svl sv ins_args) new_cand0  in
              let node_svl,non_node_svl = List.partition (CP.is_node_typ) ins_cand in
              (node_svl@non_node_svl@rem)
            with _ -> new_cand0
        )
      | _ -> let node_svl, non_node_svl = List.partition (CP.is_node_typ) new_cand0 in
        (node_svl@non_node_svl)
  in
  let () = DD.ninfo_zprint (lazy (("  new_cands: " ^ (!CP.print_svl new_cand) ))) no_pos in
  let () = DD.ninfo_zprint (lazy (("  eqNulls: " ^ (!CP.print_svl eqNulls) ))) no_pos in
  let root=
    match new_cand with
      | [] -> (* List.hd root_cand *)
            begin
              match unk_hps with
                | hp::_ -> (try
                   let ins_args = get_hp_args_inst prog hp args0 in
                   let ins_cand, rem = List.partition (fun sv -> CP.mem_svl sv ins_args) args0 in
                   List.hd (ins_cand@rem)
                 with _ -> List.hd root_cand)
                | _ -> List.hd root_cand
            end
      | r::_ ->
            if eqNulls = [] then
              (*swl*)
              let prmroots =  List.filter (fun sv -> let p = CP.primed_of_spec_var sv in p = Primed) new_cand in
              if prmroots = [] then
                r
              else List.hd prmroots
        else
          let eqNulls,rem =
            List.partition (fun sv -> CP.mem_svl sv eqNulls) new_cand in
          List.hd (rem@eqNulls)
  in
  (root, List.filter (fun sv -> not (CP.eq_spec_var root sv)) args0)

(*
if applicable, fst of unk_hps is the pred we are finding the root
*)
let find_root_x prog unk_hps args fs=
  let rec examine_one_arg fs a=
    match fs with
      | [] -> true
      | f::fs_tl ->
          (*get ptos of all nodes*)
          let hds = get_hdnodes f in
          let ptos = List.concat (List.map (fun hd -> hd.CF.h_formula_data_arguments) hds) in
          if CP.mem_svl a ptos then false
          else examine_one_arg fs_tl a
  in
  (*tricky here. should have another better*)
  match args with
    | [a] -> (a,[])
    | _ -> begin
        let root_cands = List.filter (examine_one_arg fs) args in
        let () = DD.ninfo_zprint (lazy (("  root_cands: " ^ (!CP.print_svl root_cands)))) no_pos in
        match root_cands with
          | [] -> (List.hd args, List.tl args)
                (*circle: demo/dll-app-bug3.slk*)
                (*report_error no_pos "sau.find_root_x: dont have a root. what next?" *)
          | r::_ ->
                let res = if List.length root_cands> 1 then
                  closer_ranking prog unk_hps fs root_cands args
                else
                  (r,List.filter (fun sv -> not (CP.eq_spec_var r sv)) args)
                in
                res
    end

let find_root  prog unk_hps args fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  let pr2 = pr_pair !CP.print_sv !CP.print_svl in
  Debug.no_3 "find_root" !CP.print_svl !CP.print_svl pr1 pr2
      (fun _ _ _ -> find_root_x prog unk_hps args fs) unk_hps  args fs


let drop_dups_guard lhs rhs guard=
  match guard with
    | None -> None
    | Some f -> let nf = CF.drop_dups rhs f in
      if is_empty_f nf then None else (Some nf)

(**********************)
(*check root: is_dangling (root=), is_null,is_not_null*)
let check_root_accept_dang_x root0 f0=
  let check_root_accept_dang_helper root hf p=
    if CF.is_empty_heap hf then
      let cons = CP.list_of_conjs p in
      let is_dang,is_null = List.fold_left
        (fun (b1,b2) p -> let b11,b21= CP.check_dang_or_null_exp root p in
                          b1||b11,b2||b21) (false,false) cons in
      (is_dang,is_null,false)
    else
      let ptrs = CF.get_ptrs hf in
      let is_not_null = CP.mem_svl root ptrs in
    (false,false,is_not_null)
  in
  let helper f=
    match f with
    | CF.Base fb ->
        check_root_accept_dang_helper root0 fb.CF.formula_base_heap
            (MCP.pure_of_mix fb.CF.formula_base_pure)
    | CF.Exists fe ->
        check_root_accept_dang_helper root0 fe.CF.formula_exists_heap
            (MCP.pure_of_mix fe.CF.formula_exists_pure)
    | _ -> report_error no_pos "SAU.check_root_accept_dang: not handle yet"
  in
  helper f0

let check_root_accept_dang root0 f0=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = string_of_bool in
  Debug.no_2 "check_root_accept_dang" !CP.print_sv pr1 (pr_triple pr2 pr2 pr2)
      (fun _ _ -> check_root_accept_dang_x root0 f0) root0 f0

let check_root_accept_dang_fs_x root0 fs=
  let rec helper cur_fs cur_is_dang cur_is_null cur_is_not_null=
    match cur_fs with
      | [] -> (cur_is_dang) || (cur_is_null&&cur_is_not_null)
      | f::tl ->
          let is_dang,is_null,is_not_null = check_root_accept_dang root0 f in
          let n_is_dang = is_dang || cur_is_dang in
          if n_is_dang then true else
            let n_is_null = is_null || cur_is_null in
            let n_is_not_null = is_not_null || cur_is_not_null in
            if n_is_null && n_is_not_null then true
            else helper tl n_is_dang n_is_null n_is_not_null
  in
  helper fs false false false

let check_root_accept_dang_fs root0 fs=
  let pr1 = !CP.print_sv in
  let pr2 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "check_root_accept_dang_fs" pr1 pr2 string_of_bool
      (fun _ _ -> check_root_accept_dang_fs_x root0 fs) root0 fs

let refine_dang_x prog (hpdefs: (CP.spec_var *CF.hp_rel_def) list) unk_hps fs=
  let rec look_up_hpdefs hp defs=
    match defs with
      | [] -> report_error no_pos ((!CP.print_sv hp) ^ " hprels should be topo sorted")
      | (hp1, def)::rest ->
          if CP.eq_spec_var hp hp1 then
            let _,args = CF.extract_HRel def.CF.def_lhs in
            (List.map fst def.CF.def_rhs, args)
          else look_up_hpdefs hp rest
  in
  let part_hps_only (f_hps_only,hps_only,rems) f=
    if CF.is_HRel_f f then
      let hp,args= CF.extract_HRel_f f in
      if CP.mem_svl hp unk_hps then
        (f_hps_only,hps_only,rems@[f])
      else
        (f_hps_only@[f],hps_only@[(hp,args)], rems)
    else
      (f_hps_only,hps_only,rems@[f])
  in
  let rec is_acc_dangling ls_hpargs=
    match ls_hpargs with
      | [] -> false
      | (hp1,_)::rest ->
          let fs,args1 = look_up_hpdefs hp1 hpdefs in
          let root1,(* non_r_args *) _ = find_root prog (hp1::unk_hps) args1 fs in
          let accept_dang = check_root_accept_dang_fs root1 fs in
          if accept_dang then true else
            is_acc_dangling rest
  in
  let refine_dang_br cur_rems f=
    let hps,_= List.split (CF.get_HRels_f f) in
    if CP.diff_svl hps unk_hps = [] then
      cur_rems
    else (cur_rems@[f])
  in
  (*find all = hp only*)
  let fs_hp_only,hps_only,rems = List.fold_left part_hps_only ([],[],[]) fs in
  (*for each, lookup def and check dangling*)
  (* let pr0 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let () =  DD.info_zprint (lazy (("       hps_only: " ^ (pr0 hps_only)))) no_pos in *)
  if is_acc_dangling hps_only then
    (* let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in *)
    (* let () =  DD.info_zprint (lazy (("       rems: " ^ (pr1 rems)))) no_pos in *)
    (*for each remain: elim if all its hps are danling*)
    let new_rems= List.fold_left refine_dang_br [] rems in
    (fs_hp_only@new_rems)
  else
    fs

let refine_dang prog hpdefs unk_hps fs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "refine_dang" pr1 pr2 pr2
      (fun _ _ -> refine_dang_x prog hpdefs unk_hps fs) unk_hps fs

let remove_dups_recursive_x prog cdefs hp args unk_hps unk_svl defs_wg=
  let is_rec_f (f,_)=
    let hps = CF.get_hp_rel_name_formula f in
    (CP.mem_svl hp hps)
  in
  let is_independ_f (f,_) =
    let hps = CF.get_hp_rel_name_formula f in
    let hps1 = CP.remove_dups_svl hps in
    (* DD.ninfo_zprint (lazy (("       hp: " ^ (!CP.print_sv hp)))) no_pos; *)
    let rems = List.filter (fun hp1 -> not(CP.eq_spec_var hp hp1)
    && not (CP.mem_svl hp1 unk_hps) ) hps1 in
    (* DD.ninfo_zprint (lazy (("       rems: " ^ (!CP.print_svl rems)))) no_pos; *)
    (rems = [])
  in
  (*r_ss for recover las_svl after match*)
  let recover_subst r_ss n_matcheds2=
    let rec loop_helper key_sv ss res_ss=
      match ss with
        | [] -> key_sv,res_ss (*can not find*)
        | (sv1,sv2)::ls ->
            if CP.eq_spec_var key_sv sv2 then sv1,(res_ss@ls)
            else loop_helper key_sv ls (res_ss@[(sv1,sv2)])
    in
    let rec out_loop r_ss ls done_ls=
      match ls  with
        | [] -> done_ls,r_ss
        | sv::tl -> let new_sv,new_r_ss = loop_helper sv r_ss [] in
                    out_loop new_r_ss tl (done_ls@[new_sv])
    in
    out_loop r_ss n_matcheds2 []
  in
  let rec match_hds all_rec_dns rec_dns matched2 rest_dns2 last_svl r_ss r=
    match rec_dns with
      | [] -> (r, matched2,last_svl)
      |  hns::rec_ls ->
          (* let pr = pr_list_ln (fun hd -> Cprinter.prtt_string_of_h_formula (CF.DataNode hd)) in *)
          (* let () = DD.info_zprint (lazy (("       hns: " ^ (pr hns)))) no_pos in *)
           let (n_matcheds2, rest2, ss, last_ss,new_last_svl) = get_longest_common_hnodes_two args hns rest_dns2 [] in
           (* let () = DD.info_zprint (lazy (("       n_matcheds2: " ^ (!CP.print_svl n_matcheds2)))) no_pos in *)
           (* let () = DD.info_zprint (lazy (("       new_last_svl: " ^ (!CP.print_svl new_last_svl)))) no_pos in *)
           if (List.length n_matcheds2) = (List.length hns) then
             let last_svl1 = List.filter CP.is_node_typ new_last_svl in
             let last_svl2=
               if List.length last_svl1 > List.length args then
                 CP.diff_svl last_svl1 unk_svl
               else last_svl1
             in
             let () = DD.ninfo_pprint ("        unk_svl: " ^
                     (!CP.print_svl  unk_svl)) no_pos in
               let () = DD.ninfo_zprint (lazy (("       last_svl2: " ^ (!CP.print_svl last_svl2)))) no_pos in
               let () = DD.ninfo_zprint (lazy (("       args: " ^ (!CP.print_svl args)))) no_pos in
               (* let ss = combine_length_neq last_svl2 args [] in *)
               let ss = combine_multiple_length last_svl2 args in
               let n_rest2 = List.map (CF.dn_subst (ss)) rest2 in
               let n_matcheds21,r_ss1 = recover_subst r_ss n_matcheds2 in
             (* let () = DD.info_zprint (lazy (("       n_matcheds21: " ^ (!CP.print_svl n_matcheds21)))) no_pos in *)
               if rest2 = [] then (true,matched2@n_matcheds21,last_svl2) else
               (*continue, if applicable*)
                 match_hds all_rec_dns all_rec_dns (matched2@n_matcheds21) n_rest2 last_svl2 (r_ss1@ss) true
           else match_hds all_rec_dns rec_ls matched2 rest_dns2 last_svl r_ss r
  in
  let match_with_rec rec_ls_dns (f,og)=
    let () = DD.ninfo_pprint ("       f:" ^
                     (Cprinter.prtt_string_of_formula f)) no_pos in
    let hds = get_hdnodes f in
    let rec_ls_dns1 = List.filter (fun hds -> hds <> []) rec_ls_dns in
    let b,matched,last_svl = match_hds rec_ls_dns1 rec_ls_dns1 [] hds [] [] false in
    if not b then ([],[(f,og)])
    else
      let last_svl1 = List.filter CP.is_node_typ last_svl in
      let () = DD.ninfo_pprint ("       last_svl1: " ^
                     (!CP.print_svl last_svl1)) no_pos in
      let residue = CF.drop_hnodes_f f matched in
      let () = DD.ninfo_pprint ("       residue:" ^
                     (Cprinter.prtt_string_of_formula residue)) no_pos in
      let () = DD.ninfo_pprint ("       args: " ^
                     (!CP.print_svl args)) no_pos in
      (* let ss = combine_length_neq last_svl1 args [] in *)
      let ss = combine_multiple_length last_svl1 args in
      let new_residue = CF.subst ss residue in
      (* let () = DD.info_pprint ("       new_residue:" ^ *)
      (*                (Cprinter.prtt_string_of_formula new_residue)) no_pos in *)
      ([(f,og, new_residue)],[])
  in
  let match_with_base_x is_acc_dang poss_base_fs_wg base_fs_wg=
    (*remove unk hps and neqNull*)
    (* let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in *)
    (* let () = DD.info_zprint (lazy (("       base_fs:" ^ (pr1 base_fs)))) no_pos in *)
    let base_fs1_wg = List.map (fun (f,og) -> let new_f,_ = CF.drop_hrel_f f unk_hps in (new_f,og)) base_fs_wg in
    (* let () = DD.info_zprint (lazy (("       base_fs1:" ^ (pr1 base_fs1)))) no_pos in *)
    let process_helper (f,og, residue) =
      (* let () = DD.info_zprint (lazy (("       residue:" ^ (Cprinter.prtt_string_of_formula residue)))) no_pos in *)
      let residue1,_ = CF.drop_unk_hrel residue unk_hps in
      let residue2 = CF.remove_neqNulls_f residue1 in
      (* let () = DD.info_zprint (lazy (("       residue2:" ^ (Cprinter.prtt_string_of_formula residue2)))) no_pos in *)
      let drop = if is_empty_f residue2 then
            is_acc_dang
          else
            List.exists
                (fun (base_f,_) ->
                    check_relaxeq_formula args base_f residue2
                )
                base_fs1_wg
      in
      if drop then [] else [(f,og)]
    in
    let new_base_fs_wg = List.concat (List.map process_helper poss_base_fs_wg) in
    new_base_fs_wg
  in
  (*for debugging*)
  let match_with_base is_acc_dang poss_base_fs_wg base_fs_wg=
    let pr0 = Cprinter.prtt_string_of_formula in
    let pr1 = pr_list_ln (pr_pair pr0 (pr_option pr0)) in
    let pr2 = pr_list_ln (pr_triple pr0 (pr_option pr0) pr0) in
    Debug.no_3 "match_with_base" string_of_bool pr2 pr1 pr1
        (fun _ _ _ -> match_with_base_x is_acc_dang poss_base_fs_wg base_fs_wg) is_acc_dang poss_base_fs_wg base_fs_wg
  in
  (*END for debugging*)
  (*partition into 4 groups: rec, base, depend - not process,
    others-match with rec to find residue*)
  let rec_fs_wg,rem_fs_wg= List.partition is_rec_f defs_wg in
  let indep_fs_wg, dep_fs_wg = List.partition is_independ_f rem_fs_wg in
  (*base cases > 1*)
  if (List.length indep_fs_wg > 1) then
    let root,(* non_r_args *) _ = find_root prog (hp::unk_hps) args (List.map fst defs_wg) in
    (* let () = DD.info_zprint (lazy ((" root: " ^ (!CP.print_sv root) ))) no_pos in *)
    (* let root = *)
    (*   if args = [] then report_error no_pos "sau.remove_dups_recursive: hp should have at least one argument" *)
    (*   else (List.hd args) *)
    (* in *)
    let rec_fs1_wg = remove_longer_common_prefix_wg rec_fs_wg in
    let rec_ls_hds = List.map (fun (f,_) -> get_hdnodes f) rec_fs1_wg in
    let parts = List.map (match_with_rec rec_ls_hds) indep_fs_wg in
    let ls_poss_base_fs_wg,ls_base_fs_wg = List.split parts in
    let base_fs_wg = List.concat ls_base_fs_wg in
    let poss_base_fs_wg = List.concat ls_poss_base_fs_wg in
    let dep_fs1_wg = remove_longer_common_prefix_wg dep_fs_wg in
    let b,rec_fs_wg,other_fs_wg=
      if base_fs_wg = [] then
      (*residue list*)
        let poss_base_fs1_wg = List.map (fun (_,og, res) -> (res, og)) poss_base_fs_wg in
        let poss_base_fs2_wg = List.filter (fun (f,_) -> not(is_empty_f f)) poss_base_fs1_wg in
      (* Gen.BList.remove_dups_eq (fun f1 f2 -> check_relaxeq_formula f1 f2) defs *)
        (false,rec_fs1_wg,(dep_fs1_wg@poss_base_fs2_wg))
      else
        let accept_dang = check_root_accept_dang_fs root (List.map fst defs_wg) in
        let new_base_fs_wg = match_with_base accept_dang poss_base_fs_wg base_fs_wg in
        (true,rec_fs1_wg,(dep_fs1_wg@base_fs_wg@new_base_fs_wg))
    in
    let refined_fs= other_fs_wg in
     (*  if !Globals.sa_refine_dang then *)
    (*     refine_dang prog cdefs unk_hps other_fs *)
    (*   else other_fs *)
    (* in *)
    (b,rec_fs_wg@refined_fs)
  else
    (true,defs_wg)

(*return: (base_case_exist,defs)*)
let remove_dups_recursive_wg prog cdefs hp args unk_hps unk_svl defs_wg=
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
  let pr2 = pr_pair string_of_bool pr1 in
  Debug.no_3 "remove_dups_recursive" !CP.print_sv !CP.print_svl pr1 pr2
      (fun _ _ _ -> remove_dups_recursive_x prog cdefs hp args unk_hps unk_svl defs_wg) hp args defs_wg


let simplify_set_of_formulas_wg_x prog is_pre cdefs hp args unk_hps unk_svl defs_wg=
  let is_self_rec f=
    let hpargs = CF.check_and_get_one_hpargs f in
    match hpargs with
      | [(hp1,_,_)] -> if CP.eq_spec_var hp hp1 then true else false
      | _ -> false
  in
  let helper (f,og)=
    let f1 = filter_var prog args f in
    let f2 = elim_irr_eq_exps prog (args@unk_svl) f1 in
    let () = Debug.ninfo_zprint (lazy (("  f2: "^ (Cprinter.prtt_string_of_formula f)))) no_pos in
    if is_pre && ( (is_trivial f2 (hp,args)) || is_self_rec f2) then [] else [(f2,og)]
  in
  if List.length defs_wg < 2 then (false, defs_wg) else
    let base_case_exist,defs1 = remove_dups_recursive_wg prog cdefs hp args unk_hps unk_svl defs_wg in
    let defs2 = List.concat (List.map helper defs1) in
    let b_defs3,r_defs3=List.partition (fun (f,_) -> Cfutil.is_empty_heap_f f) defs2 in
    (*remove duplicate for base cases*)
    let b_defs4 = (* remove_subsumed_pure_formula args *) b_defs3 in
    (*remove duplicate for recursive cases*)
    let r_defs4 = (* Gen.BList.remove_dups_eq check_relaxeq_formula *) r_defs3 in
    (*  if base_case_exist then *)
    (*      List.concat (List.map helper defs1) *)
    (*    else defs1 *)
    (* in *)
    (base_case_exist,b_defs4@r_defs4)

let simplify_set_of_formulas_wg prog is_pre cdefs hp args unk_hps unk_svl defs_wg=
   let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
   let pr2 = pr_pair string_of_bool pr1 in
   Debug.no_3 "simplify_set_of_formulas_wg" !CP.print_sv !CP.print_svl pr1 pr2
       (fun _ _ _ -> simplify_set_of_formulas_wg_x prog is_pre cdefs hp args unk_hps unk_svl defs_wg) hp args defs_wg

let norm_fold_seg_x prog hp_defs hp0 r other_args unk_hps defs_wg=
  (**********INTERNAL************)
  let rec extract_def l_hp_defs hp=
    match l_hp_defs with
      | [] -> None
      | def::rest -> begin match def.CF.def_cat with
            | CP.HPRelDefn (hp1, r1, args1) ->
                  if List.length (r::other_args) == List.length (r1::args1) && CP.eq_spec_var hp hp1 then
                    let fs= List.fold_left (fun r (f, _) ->
                        let dep_hps = CF.get_hp_rel_name_formula f in
                        if List.length (List.filter (fun hp2 -> CP.eq_spec_var hp2 hp1) dep_hps) == 1 then
                          (r@[f])
                        else r
                    ) [] def.CF.def_rhs
                    in
                    if fs = [] then None else (Some (def.CF.def_lhs, r1, args1, fs))
                  else extract_def rest hp
            | _ -> extract_def rest hp
        end
  in
  let rec do_fold_compare_x f r2 poss_r poss_args poss_fold_fs=
     match poss_fold_fs with
      | [] -> (false)
      | fold_f::rest ->
            let ss = List.combine (r2::other_args) (poss_r::poss_args) in
            if check_relaxeq_formula [poss_r] (CF.subst ss f) fold_f then
              true
            else
              do_fold_compare_x f r2 poss_r poss_args rest
  in
  let do_fold_compare f r2 poss_r poss_args poss_fold_fs=
    let pr1 = Cprinter.prtt_string_of_formula in
    Debug.no_4 "do_fold_compare" pr1 !CP.print_sv !CP.print_sv (pr_list_ln pr1) string_of_bool
        (fun _ _ _ _ -> do_fold_compare_x f r2 poss_r poss_args poss_fold_fs)
        f r2 poss_r poss_fold_fs
  in
  let extract_next_root hds hvs r2=
    let rec extract_data_node rest_hds=
      match rest_hds with
        | [] -> None
        | dn::rest -> begin
            if CP.eq_spec_var dn.CF.h_formula_data_node r2 then
              let ptrs = List.filter CP.is_node_typ dn.CF.h_formula_data_arguments in
              match ptrs with
                | [nr] -> Some (nr, CF.DataNode dn)
                | _ -> None
            else extract_data_node rest
          end
    in
    let rec extract_view_node rest_vds=
      match rest_vds with
        | [] -> None
        | vn::rest -> begin
            if CP.eq_spec_var vn.CF.h_formula_view_node r2 then
              let ptrs = List.filter CP.is_node_typ vn.CF.h_formula_view_arguments in
              match ptrs with
                | [nr] -> Some (nr, CF.ViewNode vn)
                | _ -> None
            else extract_view_node rest
          end
    in
    let dn_opt = extract_data_node hds in
    if dn_opt = None then extract_view_node hvs else dn_opt
  in
  let rec do_fold f r0 (poss_hf, poss_r, poss_args, poss_fold_fs) res_hfs=
    let () = Debug.ninfo_hprint (add_str "   f: " Cprinter.prtt_string_of_formula) f no_pos in
    let reach_f = CFU.obtain_reachable_formula prog f [r0] in
    let hds, hvs, _ = CF.get_hp_rel_formula reach_f in
    if hds = [] && hvs = [] then false, reach_f else
      let is_folded= do_fold_compare reach_f r0 poss_r poss_args poss_fold_fs in
      if is_folded then
        let folded_pred = CF.h_subst [( poss_r,r0)] poss_hf in
        let n_hf = CF.join_star_conjunctions (res_hfs@[folded_pred]) in
        (true, CF.formula_of_heap n_hf no_pos)
      else
        let cur_root_hf_opt = extract_next_root hds hvs r0 in
        match cur_root_hf_opt with
          | Some (n_root, n_hf) ->
                do_fold reach_f n_root (poss_hf, poss_r, poss_args, poss_fold_fs) (res_hfs@[n_hf])
          | None -> false, reach_f
  in
  let process_one_branch (f,og)=
    let dep_hps = CF.get_hp_rel_name_formula f in
    match dep_hps with
      | [hp] -> begin
            if CP.mem_svl hp (hp0::unk_hps) then
              (f,og)
            else
              let fold_opt = extract_def hp_defs hp in
              match fold_opt with
                | Some (poss_hf, poss_r, poss_args, poss_fold_fs) ->
                  let is_folded, folded_f = do_fold f r (poss_hf, poss_r, poss_args, poss_fold_fs) [] in
                  if is_folded then
                    (folded_f,og)
                  else (f,og)
                | None -> (f,og)
        end
      | _ -> (f,og)
  in
  (*********END*INTERNAL************)
  let defs_wg1 = List.map process_one_branch defs_wg in
  defs_wg1

let norm_fold_seg prog hp_defs hp r other_args unk_hps defs_wg=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln (pr_pair pr1 (pr_option pr1)) in
  (* let pr3 = Cprinter.string_of_hp_rel_def in *)
  Debug.no_4 "SAU.norm_fold_seg" !CP.print_sv !CP.print_sv !CP.print_svl pr2 pr2
      (fun _ _ _ _ -> norm_fold_seg_x prog  hp_defs hp r other_args unk_hps defs_wg)
      hp r other_args defs_wg

let norm_unfold_seg_x prog hp0 r other_args unk_hps ofl defs_wg=
  (**************INTERNAL**********)
  let look_up_continuous_para non_root_args (f,_)=
    let ls_hpargs = CF.get_HRels_f f in
    let rec_hpargs, other_hpargs = List.partition (fun (hp,_) -> CP.eq_spec_var hp hp0) ls_hpargs in
      if other_hpargs != [] then [] else
        let ( _,mix_f,_,_,_,_) = CF.split_components f in
        let eqs = (MCP.ptr_equations_without_null mix_f) in
        (*cont paras are para not changed, just forwarded*)
        let cont_paras = List.fold_left (fun cur_cont_paras (hp,args1) ->
            let f_wo_rec_hps,_ = CF.drop_hrel_f f [hp0] in
            let all_svl = CF.fv f_wo_rec_hps in
            let all_svl1 = CP.diff_svl all_svl (CP.remove_dups_svl (
                List.fold_left (fun r (sv1,sv2) -> r@[sv1;sv2]) [] eqs)) in
            let cont_args = CP.diff_svl args1 all_svl1 in
            let closed_rec_args = CF.find_close cont_args eqs in
            CP.intersect_svl cur_cont_paras closed_rec_args
        ) non_root_args rec_hpargs
        in
        cont_paras
  in
  let exchange_nodes f hds hvs cont_vars eqs =
    (* let neqs = List.fold_left (fun r (sv1,sv2) -> *)
    (*     let b1 = CP.mem_svl sv1 cont_vars in *)
    (*     let b2 = CP.mem_svl sv2 cont_vars in *)
    (*     match b1,b2 with *)
    (*       | true,false -> r@[(sv2,sv1)] *)
    (*       | false,true -> r@[(sv1,sv2)] *)
    (*       | _ -> r *)
    (* ) [] eqs in *)
    (* let n_f = CF.subst neqs f in *)
    (* let cont_vars1 = CF.find_close cont_vars eqs in *)
    (* let drop_node_svl = List.fold_left (fun r hd -> *)
    (*     if CP.mem_svl hd.CF.h_formula_data_node cont_vars1 then r@[hd.CF.h_formula_data_node] else r *)
    (* ) [] hds in *)
    (* let n_hds = List.map (fun hd -> {hd with CF.h_formula_data_node = CP.subs_one neqs hd.CF.h_formula_data_node}) hds in *)
    (* let n_hvs = List.map (fun hv -> {hv with CF.h_formula_view_node = CP.subs_one neqs hv.CF.h_formula_view_node}) hvs in *)
    (* (drop_node_svl,n_f, n_hds, n_hvs, neqs) *)
    ([], f, hds, hvs, eqs)
  in
  (*partition f into: cont_args and remain*)
  let segmentation_on_base_cases rem_args cont_args n_root f=
    let () = Debug.ninfo_hprint (add_str "n_root: " !CP.print_sv) n_root no_pos in
    let () = Debug.ninfo_hprint (add_str "   f: " Cprinter.prtt_string_of_formula) f no_pos in
    let keep_svl = [n_root]@cont_args in
    let ( _,mix_f,_,_,_,_) = CF.split_components f in
    let eqs = (MCP.ptr_equations_without_null mix_f) in
    let hds, hvs, hrs = CF.get_hp_rel_formula f in
    let hpargs = List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs))) hrs in
    let sel_hpargs, rem_sel_hpargs = List.partition (fun (_,args) -> CP.diff_svl args keep_svl = []) hpargs in
    let drop_node_svl,n_f, n_hds, n_hvs, eqs1 = exchange_nodes f hds hvs cont_args eqs in
    let () = Debug.ninfo_hprint (add_str "   n_f: " Cprinter.prtt_string_of_formula) n_f no_pos in
    let cont_f = keep_data_view_hpargs_nodes prog n_f n_hds n_hvs keep_svl sel_hpargs in
    let rem_f = drop_data_view_hrel_nodes_from_root prog f hds hvs eqs (drop_node_svl@keep_svl)
       (CF.look_up_reachable_ptr_args prog hds hvs (drop_node_svl@keep_svl)) [] sel_hpargs in
    let () = Debug.ninfo_hprint (add_str "   cont_f: " Cprinter.prtt_string_of_formula) cont_f no_pos in
    let () = Debug.ninfo_hprint (add_str "   rem_f: " Cprinter.prtt_string_of_formula) rem_f no_pos in
    ( elim_irr_eq_exps prog (n_root::rem_args) rem_f, cont_f)
  in
  (********END INTERNAL*************)
  (*classify base vs. rec*)
  let rec_fs_wg,base_fs_wg = List.partition (fun (f,g) ->
      let hps = CF.get_hp_rel_name_formula f in
      (CP.mem_svl hp0 hps)
  ) defs_wg in
  (*in rec branches, one parameter is continuous*)
  let cont_args = List.fold_left (look_up_continuous_para) other_args rec_fs_wg in
  let () = Debug.ninfo_hprint (add_str "cont_args: " !CP.print_svl) cont_args no_pos in
  if rec_fs_wg = [] || List.length cont_args != 1 then
    None
  else
    (*in base branches, root is closed and continuos parameter is contant*)
    (*if there are > segments: need generalization. NOW: ASSUME one base case*)
    if base_fs_wg = [] || List.length base_fs_wg > 1 then
      None
    else
      let fr_root = CP.fresh_spec_var r in
      let sst = [(r, fr_root)] in
      let link_ps = List.map (fun (sv1,sv2) -> CP.mkEqVar sv1 sv2 no_pos) sst in
      let link_p = CP.conj_of_list link_ps no_pos in
      let rem_args = (CP.diff_svl other_args cont_args) in
      let seg_fs_wg,cont_fs  = List.fold_left (fun (segs, cont_fs) (base, og) ->
          let seg_f,cont_f = segmentation_on_base_cases rem_args cont_args fr_root (CF.subst sst base) in
          let seg_f1 =  CF.simplify_pure_f_old (CF.mkAnd_pure seg_f (MCP.mix_of_pure link_p) no_pos) in
          (segs@[((seg_f1,og))], cont_fs@[cont_f])
      ) ([],[]) base_fs_wg in
      if List.for_all (fun f -> not (CF.isConstTrueFormula f)) cont_fs then
        try
        (*generate another pred*)
          (*now: deal with one seg point (rec point)*)
          let fr_cont_args = [fr_root] in
          let sst1 = List.combine cont_args fr_cont_args in
          let n_lhs,n_hp =  add_raw_hp_rel prog false false ((r,I)::(List.map (fun sv -> (sv,NI)) fr_cont_args)) no_pos in
          (*subst hp -> new_hp*)
          let hp_ss = [(hp0, n_hp)] in
          let rec_fs_wg1 = List.map (fun (f,og) -> CF.subst sst1 (CF.subst hp_ss f), og) rec_fs_wg in
          let none_rhs,rem_rhs = List.fold_left (fun (r1,r2) (f,og) -> if og =None then (r1@[f],r2) else (r1,r2@[(f,og)])
          ) ([],[]) (seg_fs_wg@rec_fs_wg1) in
          let n_hp_def = CF.mk_hp_rel_def1 (CP.HPRelDefn (n_hp, r, cont_args)) n_lhs ([(CF.disj_of_list none_rhs no_pos , None)]@rem_rhs) ofl  in
          (*should generalize cont_fs*)
          let rhs1 = CF.disj_of_list cont_fs no_pos in
          let rhs2 = CF.mkAnd_f_hf rhs1 n_lhs no_pos in
          Some (rhs2, n_hp_def)
        with _ -> None
      else
        None

let norm_unfold_seg prog hp r other_args unk_hps ofl defs_wg=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln (pr_pair pr1 (pr_option pr1)) in
  let pr3 = Cprinter.string_of_hp_rel_def in
  Debug.no_4 "SAU.norm_unfold_seg" !CP.print_sv !CP.print_sv !CP.print_svl pr2 (pr_option (pr_pair pr1 pr3))
      (fun _ _ _ _ -> norm_unfold_seg_x prog hp r other_args unk_hps ofl defs_wg)
      hp r other_args defs_wg

(**********************)
(*
args = {r} \union paras
*)
let mk_hprel_def_wprocess_x prog is_pre (cdefs:(CP.spec_var *CF.hp_rel_def) list) unk_hps unk_svl hp (args, r, paras)
      defs_wg (*ogs*) pos=
  match defs_wg with
    | [] -> []
    | _ -> begin
        let new_args,defs1_wg =
          if CP.mem_svl hp unk_hps then (args,defs_wg) else (* (args,defs) *)
            drop_hp_arguments prog hp args defs_wg
        in
        let base_case_exist,defs2 = simplify_set_of_formulas_wg prog is_pre cdefs hp new_args unk_hps unk_svl defs1_wg in
        if defs2 = [] (* || not base_case_exist *) then [] else
          let defs1 = List.map CF.remove_neqNull_redundant_hnodes_f_wg defs2 in
          (*make disjunction*)
          (* let def = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 (CF.pos_of_formula f1)) *)
          (*   (List.hd defs1) (List.tl defs1) in *)
          let todo_unk = C.set_proot_hp_def_raw (get_pos new_args 0 r) prog.C.prog_hp_decls (CP.name_of_spec_var hp) in
          let n_id = C.get_root_typ_hprel prog.C.prog_hp_decls (CP.name_of_spec_var hp) in
          let () = DD.ninfo_hprint (add_str "n_id: " pr_id) n_id no_pos in
          let defs_wg = if String.compare n_id "" ==0 then defs1 else
            let ss = [(r,CP.SpecVar (Named n_id, CP.name_of_spec_var r, CP.primed_of_spec_var r))] in
            List.map (fun (f, og) -> (CF.subst ss f ,og)) defs1
          in
          let () = DD.ninfo_zprint (lazy (((!CP.print_sv hp)^"(" ^(!CP.print_svl new_args) ^ ")"))) pos in
          DD.ninfo_zprint (lazy ((" =: " ^ ((pr_list_ln Cprinter.prtt_string_of_formula) (List.map fst defs_wg)) ))) pos;
          let def = (hp, CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, r, paras)) (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) new_args, pos))  defs_wg None) in
          [def]
      end

let mk_hprel_def_wprocess prog is_pre (cdefs:(CP.spec_var *CF.hp_rel_def) list) unk_hps unk_svl hp (args, r, paras)
      defs_wg (*ogs*) pos=
  let pr1 (f,_) = Cprinter.prtt_string_of_formula f in
  let pr2 = pr_pair !CP.print_sv Cprinter.string_of_hp_rel_def in
  Debug.no_3 "mk_hprel_def_wprocess" !CP.print_sv !CP.print_svl (pr_list_ln pr1)
      (pr_list_ln pr2) (fun _ _ _ -> mk_hprel_def_wprocess_x prog is_pre (cdefs:(CP.spec_var *CF.hp_rel_def) list) unk_hps unk_svl hp (args, r, paras)
      defs_wg (*ogs*) pos)
      hp args defs_wg

let mk_unk_hprel_def hp args defs pos=
  let def = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 (CF.pos_of_formula f1))
    (List.hd defs) (List.tl defs) in
  DD.ninfo_zprint (lazy ((" ==: " ^ (Cprinter.prtt_string_of_formula def) ))) pos;
  let def = CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, List.hd args, List.tl args))
    (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, pos)) [(def, None)] None in
  let pr_def = (hp, def) in
  [pr_def]

let mk_link_hprel_def prog iflow cond_path (hp,_)=
  let hp_name= CP.name_of_spec_var hp in
  let hprel = Cast.look_up_hp_def_raw prog.C.prog_hp_decls hp_name in
  let args = fst (List.split hprel.C.hp_vars_inst) in
  let hf = (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, no_pos)) in
  DD.ninfo_zprint (lazy ((" ==: " ^ "NONE" ))) no_pos;
  let def= {
      CF.hprel_def_kind = CP.HPRelDefn (hp, List.hd args, List.tl args);
      CF.hprel_def_hrel = hf;
      CF.hprel_def_guard = None;
      CF.hprel_def_body = [(cond_path, None, Some iflow)];
      CF.hprel_def_body_lib = [];
      CF.hprel_def_flow = (Some iflow);
  } in
  def

(*because root is moved to top*)
let extract_common prog hp r other_args args sh_ldns com_hprels=
  let get_connected_helper ((CP.SpecVar (t,v,p)) as r)=
    if CP.mem_svl r other_args then
      let new_v = (* CP.SpecVar (t, *)
        (* (v) ^ "_" ^ (string_of_int (Globals.fresh_int())),Unprimed) *)
        CP.fresh_spec_var r
      in
      [(r,new_v)]
    else []
  in
  let rec look_up_next_ptrs hds r res=
      match hds with
        | [] -> ([],res,[],[])
        | hd::hss -> if CP.eq_spec_var r hd.CF.h_formula_data_node then
            let r_nexts,ssl = List.split (List.concat (List.map ((fun (CP.SpecVar (t,v,p)) ->
                if (is_pointer t)
                then
		  let ss = get_connected_helper (CP.SpecVar (t,v,p)) in
		  let new_v = CP.subs_one ss (CP.SpecVar (t,v,p)) in
		  ([new_v,ss])
                else [])) hd.CF.h_formula_data_arguments))
            in
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
  let next_roots,new_sh_dns,ss,rem_dns = get_last_ptrs_new sh_ldns [r] [r] [] [] in
  let dnss = (new_sh_dns@rem_dns) in
  let () = DD.info_zprint (lazy (("   next_roots:" ^ (Cprinter.string_of_spec_var_list  next_roots)))) no_pos in
  let comp_args = List.fold_left (fun ls (_, eargs, _) -> ls@(List.fold_left List.append [] (List.map CP.afv eargs))) [] com_hprels in
  let next_roots1 = CP.diff_svl next_roots comp_args in
  let () = DD.info_zprint (lazy (("   next_roots1:" ^ (Cprinter.string_of_spec_var_list  next_roots1)))) no_pos in
  (next_roots1, dnss)

(*new_h_preds: generated sub preds *)
let get_sharing_multiple new_h_preds dnss eqNulls eqPures hprels =
   let hdss = List.map (fun hd -> (CF.DataNode hd)) dnss in
   let rest =  (hdss@new_h_preds@(List.map (fun hprel -> CF.HRel hprel) hprels)) in
   let orig_defs_h = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 no_pos) (List.hd rest) (List.tl rest) in
   let orig_def = CF.formula_of_heap orig_defs_h no_pos in
   (*common null process*)
   let orig_def1 =
     match eqNulls with
       | [] -> orig_def
       | _ ->
	     (*let eqNulls1 = List.map (CP.subs_one ss) eqNulls in*)
	     let ps = List.map (fun v -> CP.mkNull v no_pos) eqNulls in
	     let p = CP.conj_of_list ps no_pos in
             CF.mkAnd_pure orig_def (MCP.mix_of_pure p) no_pos
   in
   (*common pure process*)
   let common_pures = CP.conj_of_list eqPures no_pos in
   let orig_def2 = CF.mkAnd_pure orig_def1 (MCP.mix_of_pure common_pures) no_pos in
   let orig_def3 = CF.simplify_pure_f_old orig_def2 in
   (orig_def3, orig_defs_h)

let mk_orig_hprel_def prog is_pre cdefs unk_hps hp r other_args args sh_ldns eqNulls eqPures hprels unk_svl quans=
  let next_roots, dnss = extract_common prog hp r other_args args sh_ldns hprels in
  match next_roots with
    | [] -> report_error no_pos "sau.mk_orig_hprel_def: sth wrong 2"
    | _ ->  let () = DD.ninfo_zprint (lazy (("      last root:" ^ (Cprinter.string_of_spec_var_list  next_roots)))) no_pos in
      (*generate new hp*)
      let other_args_inst = (List.map (fun sv -> (sv,NI)) other_args) in
      let ls_n_args_inst = (List.map (fun sv -> ((sv,I)::other_args_inst, sv)) next_roots) in
      (* let ls_n_args = List.map (fun sv -> sv::other_args) next_roots in *)
      (* let n_args_inst =  (List.map (fun sv -> (sv,I)) next_roots)@other_args_inst in *)
      (* let n_args =  next_roots@other_args in *)
      (* let n_hprel,n_hp =  add_raw_hp_rel prog n_args_inst no_pos in *)
      let n_hprels,ls_n_hpargs = List.fold_left
        ( fun (r_hprels,r_hpargs) (n_args_inst, r) ->
            let is_pre = Cast.check_pre_post_hp prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
            let n_hprel,n_hp =  add_raw_hp_rel prog is_pre false n_args_inst no_pos in
            (r_hprels@[n_hprel], r_hpargs@[(n_hp,(List.map fst n_args_inst, r, other_args))])
        ) ([],[]) ls_n_args_inst
      in
      (*synthesize the common*)
      let orig_def3,orig_defs_h = get_sharing_multiple n_hprels dnss eqNulls eqPures hprels in
      (* let orig_def4 = CF.add_quantifiers quans orig_def3 in *)
      let defs = mk_hprel_def_wprocess prog is_pre cdefs unk_hps unk_svl hp (args,r,other_args) [(orig_def3,None)]  no_pos in
      (*subst*)
      let hprel = CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, no_pos) in
      (*elim all except root*)
      let n_orig_defs_h = CF.drop_hnodes_hf orig_defs_h other_args in
      (defs, (hprel, n_orig_defs_h), ls_n_hpargs (* [(n_hp, n_args)] *), dnss,
      CP.diff_svl next_roots unk_svl)
          (* | _ -> report_error no_pos "sau.generalize_one_hp: now we does not handle more than two ptr fields" *)

(* let mk_orig_hprel_def prog is_pre defs unk_hps hp r other_args args sh_ldns eqNulls eqPures hprels unk_svl quans= *)
(*   let pr1 = !CP.print_sv in *)
(*   let pr2 = !CP.print_svl in *)
(*   let pr2a = pr_triple !CP.print_svl !CP.print_sv !CP.print_svl in *)
(*   let pr3 = fun hd -> Cprinter.prtt_string_of_h_formula (CF.DataNode hd) in *)
(*   let pr4 =  pr_list !CP.print_formula in *)
(*   let pr5 = pr_list (pr_pair pr1 string_of_hp_rel_def) in *)
(*   let pr7 = pr_list (pr_pair pr1 pr2a) in *)
(*   let pr6 (d,_,ls_n_hpargs,dns,_) = *)
(*     let pr = pr_triple pr5 pr7 (pr_list pr3) in *)
(*     pr (d, ls_n_hpargs, dns) *)
(*   in *)
(*   let pr7a hrel = Cprinter.string_of_hrel_formula (CF.HRel hrel) in *)
(*   let pr7 = pr_list pr7a in *)
(*   Debug.no_7 "mk_orig_hprel_def" pr2 pr1 pr2 (pr_list pr3) pr2 pr4 pr7 pr6 *)
(*       (fun _ _ _ _ _ _ _ -> mk_orig_hprel_def_x prog is_pre defs unk_hps hp r other_args args sh_ldns *)
(*            eqNulls eqPures hprels unk_svl quans) *)
(*       unk_hps hp args sh_ldns eqNulls eqPures hprels *)
(*
  args = {r} \union paras
*)
let elim_not_in_used_args_x prog unk_hps orig_fs_wg fs_wg hp (args, r, paras)=
  let drop_hps = hp::unk_hps in
  let helper svl (f,_)=
    let new_f,_ = CF.drop_hrel_f f drop_hps in
    svl@(CF.fv new_f)
  in
  let svl = List.fold_left helper [] fs_wg in
  let new_args = CP.intersect_svl args svl in
  let elimed, n_orig_fs_wg,new_fs_wg ,ss, link_defs, n_hp=
    if List.length args = List.length new_args || new_args = [] then (false, orig_fs_wg,fs_wg,[],[],hp)
    else
      let old_hrel = mkHRel hp args no_pos in
      let is_pre = Cast.check_pre_post_hp prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
      let new_hrel,n_hp = add_raw_hp_rel prog is_pre false (List.map (fun sv -> (sv,I)) new_args) no_pos in
      (*let new_hrel = mkHRel hp new_args no_pos in *)
      (*linking defs*)
      let link_f = CF.formula_of_heap old_hrel no_pos in
      let todo_unk = C.set_proot_hp_def_raw (get_pos args 0 r) prog.C.prog_hp_decls (CP.name_of_spec_var hp) in
      let link_def = (hp, CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, r, paras))  old_hrel [(link_f,None)] None) in
      (*end linking*)
      let subst = [(old_hrel,new_hrel)] in
      let new_fs_wg = List.map (fun (f,og) -> (CF.subst_hrel_f f subst, og)) fs_wg in
      (true, List.map (fun (f,og) -> (CF.subst_hrel_f f subst, og)) orig_fs_wg, new_fs_wg,subst,[link_def],n_hp)
  in
  let n_r, n_paras = if List.length args = List.length new_args || new_args = [] ||
    (CP.mem_svl r new_args) then r,(List.filter (fun sv -> not (CP.eq_spec_var sv r)) new_args)
  else
    let n_r,non_r_args = find_root prog drop_hps new_args (List.map fst new_fs_wg) in
    n_r,non_r_args
  in
  elimed, n_orig_fs_wg,(new_args, n_r, n_paras),new_fs_wg,ss,link_defs, n_hp

(*
  args = {r} \union paras
*)
let elim_not_in_used_args prog unk_hps orig_fs_wg fs_wg hp (args, r, paras)=
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr2a = pr_triple !CP.print_svl !CP.print_sv !CP.print_svl in
  let pr3 (elimed,_,b,_,_,link_defs,_)=
    let pra = pr_list_ln (pr_pair pr1 Cprinter.string_of_hp_rel_def) in
    (string_of_bool elimed) ^ ": " ^(pr2a b) ^ "\n" ^ (pra link_defs) in
  Debug.no_3 "elim_not_in_used_args" pr1 pr2 pr2 pr3
      (fun _ _ _ -> elim_not_in_used_args_x prog unk_hps orig_fs_wg fs_wg hp (args, r, paras))
      hp args unk_hps

let check_and_elim_not_in_used_args prog is_pre cdefs unk_hps unk_svl fs_wg (*ogs*) hp (args, r, paras)=
  let n_hp, (n_args, r, n_paras), n_fs_wg ,elim_ss, link_defs =
    if !Globals.pred_elim_useless then
      let elimed,_,n_args,n_fs,ss,link_defs,n_hp = elim_not_in_used_args prog unk_hps
        [((CF.mkHTrue_nf no_pos), None)] fs_wg hp (args, r, paras) in
      if elimed then
        (n_hp, n_args,n_fs,ss, link_defs)
      else (hp, (args, r, paras), fs_wg, [],[])
    else (hp, (args, r, paras), fs_wg, [],[])
  in
  let hpdef = mk_hprel_def_wprocess prog is_pre cdefs unk_hps unk_svl n_hp (n_args, r, n_paras) n_fs_wg (*ogs*) no_pos in
  (link_defs@hpdef,elim_ss)

let is_base_cases_only fs_wg=
  let is_non_root (f,_)=
    let hps = CF.get_hp_rel_name_formula f in
    (hps = [])
  in
  List.for_all is_non_root fs_wg

let mk_hprel_def_for_subs_x prog is_pre cdefs unk_hps unk_svl ls_n_hpargs1 n_fs3_wg pos =
  (*for each new hpargs, find well pdefs*)
  let build_conf (f,og)=
    let hds, hvs, hrs = CF.get_hp_rel_formula f in
    let hpargs = List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs))) hrs in
    (f, hds, hvs, hpargs,og)
  in
  let fs_config = List.map build_conf n_fs3_wg in
  let extract_wdf hp args (f, hds, hvs, hpargs, og)=
    let closed_args = CF.look_up_reachable_ptr_args prog hds hvs args in
    let keep_hpargs = List.filter (fun (hp1,args0) ->
        CP.diff_svl args0 closed_args = []
    ) hpargs in
    let nf =  keep_data_view_hpargs_nodes prog f hds hvs args keep_hpargs in
    (*we may want to do overapporximate go give and nice solution.
      however, it may lose the equiv
    *)
    (* if is_empty_f nf || CF.is_only_neqNull_pure (CF.get_pure nf) args then *)
    (*   [] *)
    (* else *)
      (* match CF.extract_hrel_head nf with *)
      (*   | Some hp1 -> if CP.eq_spec_var hp1 hp then [] else *)
      (*       [nf] *)
      (*   | None -> [nf] *)
    [(nf,og)]
  in
  let generate_one (hp,(args,r,paras))=
    let fs_wg = List.fold_left (fun r_fs fc ->
        r_fs@(extract_wdf hp args fc)
    ) [] fs_config
    in
    let fs1_wg = Gen.BList.remove_dups_eq (fun (f1,_) (f2,_) ->
        check_relaxeq_formula args f1 f2) fs_wg
    in
    let new_hpdef = mk_hprel_def_wprocess prog is_pre cdefs unk_hps unk_svl hp (args,r,paras) fs1_wg pos in
    new_hpdef
  in
  match ls_n_hpargs1 with
    | [(hp,args)] -> mk_hprel_def_wprocess prog is_pre cdefs unk_hps unk_svl hp args n_fs3_wg pos
    | [] -> []
    | _ ->
          List.fold_left (fun defs hpargs-> defs@(generate_one hpargs)) [] ls_n_hpargs1

let mk_hprel_def_for_subs prog is_pre cdefs unk_hps unk_svl ls_n_hpargs1 n_fs3_wg pos =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
  let pr2a (args, r, _) = (!CP.print_svl args) ^ " (root:" ^ (!CP.print_sv r) ^")" in
  let pr2 = pr_list (pr_pair !CP.print_sv pr2a) in
  let pr3a = fun (_, def) -> Cprinter.string_of_hp_rel_def def in
  let pr3 = (pr_list_ln pr3a) in
  Debug.no_2 "mk_hprel_def_for_subs" pr2 pr1 pr3
      (fun _ _ -> mk_hprel_def_for_subs_x prog is_pre cdefs unk_hps unk_svl ls_n_hpargs1 n_fs3_wg pos)
      ls_n_hpargs1 n_fs3_wg

let generate_extra_defs prog is_pre cdefs unk_hps unk_svl hp r non_r_args args fs0_wg (*ogs*)
      lldns sh_ldns eqNulls eqPures hprels1 quans=
  let orig_hpdefs, hp_subst, ls_n_hpargs,sh_ldns2,next_roots = mk_orig_hprel_def prog is_pre cdefs unk_hps hp
    r non_r_args args sh_ldns eqNulls eqPures hprels1 unk_svl quans in
  match orig_hpdefs with
    | [] -> ([],[])
    | [(hp01,orig_hpdef)] -> (*(new_hp, n_args)*)
          let n_hps,n_args = List.fold_left (fun (ls1,ls2) (hp,(args,_,_))-> (ls1@[hp], ls2@args)) ([],[]) ls_n_hpargs in
          (* let n_args = CP.remove_dups_svl n_args0 in *)
          let n_fs_wg = List.map (fun (a,f,og) ->
              (process_one_f prog args n_args next_roots hp_subst sh_ldns2 eqNulls eqPures hprels1 (a,f), og)) lldns in
          let n_fs1_wg = if is_pre then
            (*pre-preds: strengthen*)
            List.filter (fun (f,og) -> not ((is_empty_f f) || (CF.is_only_neqNull n_args [] f))) n_fs_wg
          else
            (*post-pred: do not strengthen*)
            n_fs_wg
          in
          (*for debugging*)
          (* let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in *)
          (* let () = Debug.info_zprint (lazy (("  n_args: "^ (!CP.print_svl n_args)))) no_pos in *)
          (* let () = Debug.info_zprint (lazy (("  n_fs1: "^ (pr1 n_fs1)))) no_pos in *)
          (*END for debugging*)
          let n_fs2_wg = Gen.BList.remove_dups_eq (fun (f1,_) (f2,_) -> check_relaxeq_formula n_args f1 f2) n_fs1_wg in
          (* let () = Debug.info_zprint (lazy (("  n_fs2: "^ (pr1 n_fs2)))) no_pos in *)
          let n_orig_hpdef, ls_n_hpargs1, n_fs3_wg, elim_ss, link_defs =
            if (!Globals.pred_elim_useless) then
              (*
              (*********************************************)
                currently, we dont elim useless args when we have more
                than one braches. TO IMPROVE
              (*********************************************)
              *)
              match ls_n_hpargs with
                | [(new_hp, (n_args, n_r,paras))] ->
                      (* let (a,b,g,orig_fs) = orig_hpdef in *)
                      (* let fs, gs = List.split orig_hpdef.CF.def_rhs in *)
                      (* let orig_fs = CF.disj_of_list fs no_pos in *)
                      let _,n_orig_fs_wg,(n_args,r,n_paras), n_fs_wg,ss, link_defs, n_hp1=
                        elim_not_in_used_args prog unk_hps orig_hpdef.CF.def_rhs n_fs2_wg new_hp (n_args, n_r,paras)  in
                      ( {orig_hpdef with CF.def_rhs = n_orig_fs_wg }, [(n_hp1, (n_args,r,n_paras))], n_fs_wg ,ss, link_defs)
                | _ -> (orig_hpdef, ls_n_hpargs, n_fs2_wg, [],[])
            else (orig_hpdef, ls_n_hpargs, n_fs2_wg, [],[])
          in
          (* let new_hpdef = mk_hprel_def prog cdefs unk_hps unk_svl n_hp1 n_args1 n_fs3 no_pos in *)
          let new_hpdef = mk_hprel_def_for_subs prog is_pre cdefs unk_hps unk_svl ls_n_hpargs1 n_fs3_wg (*ogs*) no_pos in
          if new_hpdef = [] then
            let hpdef = mk_hprel_def_wprocess prog is_pre cdefs unk_hps unk_svl hp (args,r, non_r_args)  fs0_wg no_pos in
            (hpdef,[])
          else
            (((hp01,n_orig_hpdef)::new_hpdef)@link_defs,elim_ss)
    | _ -> report_error no_pos "sau.get_longest_common_hnodes_list"

let get_longest_common_hnodes_list_x prog is_pre (cdefs:(CP.spec_var *CF.hp_rel_def) list) unk_hps unk_svl hp r non_r_args (args: CP.spec_var list) fs0_wg (*ogs*)=
  if List.length fs0_wg <= 1 then
    let hpdef = mk_hprel_def_wprocess prog is_pre cdefs unk_hps unk_svl hp (args, r, non_r_args) fs0_wg (*ogs*) no_pos in
    (hpdef,[])
  (* check_and_elim_not_in_used_args prog is_pre cdefs unk_hps unk_svl (CF.mkHTrue_nf no_pos) fs0 hp args *)
  else begin
    let f0,_ = (List.hd fs0_wg) in
   let quans, _ = CF.split_quantifiers f0 in
   let fs_wg = (* List.map (fun f -> snd (CF.split_quantifiers f)) *) fs0_wg in
   let lldns_vns = List.map (fun (f,og) ->
       let hds,hvs,_ = CF.get_hp_rel_formula f in
       (hds, hvs,f, og)
   ) fs_wg in
   let lldns = List.map (fun (a,_,f,g) -> (a,f,g)) lldns_vns in
   let min,sh_ldns,sh_lvns,eqNulls,eqPures,hprels = get_min_common prog args unk_hps
     (List.map (fun (a,b,c,_) -> (a,b,c)) lldns_vns) in
   (*remove hp itself*)
   let hprels1 = List.filter (fun (hp1,_,_) -> not(CP.eq_spec_var hp hp1)) hprels in
   if min = 0 && eqNulls = [] && eqPures= [] then
     (*mk_hprel_def*)
     check_and_elim_not_in_used_args prog is_pre cdefs unk_hps unk_svl fs_wg (*ogs*) hp (args, r, non_r_args)
   else
     try
       if (is_base_cases_only fs0_wg  && (List.for_all (fun (ls,_,_,_) ->
           let n = List.length ls in
           (* let () = Debug.info_zprint (lazy (("  n: "^ (string_of_int n)))) no_pos in *)
           n = min ) lldns_vns) ) then
         (*if they all are base cases, wedo not need generate a new hp*)
         let next_roots,sh_ldns2 = extract_common prog hp r non_r_args args sh_ldns hprels1 in
         let common_f,_ = get_sharing_multiple [] sh_ldns2 eqNulls eqPures hprels in
         let hprel = CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, no_pos) in
         let hp_subst0 = (hprel, hprel) in
         let n_fs_wg = List.map (fun (a,f,og) -> (process_one_f prog args args next_roots hp_subst0 sh_ldns2 eqNulls eqPures hprels1 (a,f), og)) lldns in
         (* let disj = CF.disj_of_list n_fs no_pos in *)
         if List.for_all (fun (f,_) -> Cfutil.is_empty_heap_f f) n_fs_wg then
           (* let disj_p = CF.get_pure disj in *)
           let nfs_wg = List.map (fun (f, og) -> (CF.mkAnd_pure common_f (MCP.mix_of_pure ( CF.get_pure f)) no_pos, og)) n_fs_wg in
           check_and_elim_not_in_used_args prog is_pre cdefs unk_hps unk_svl
                nfs_wg (*ogs*) hp (args, r, non_r_args)
         else
           (*currently, HIP has not supported formual STAR (OR heap)  *)
           raise Not_found
       else
         generate_extra_defs prog is_pre cdefs unk_hps unk_svl hp r non_r_args args fs0_wg (*ogs*)
             lldns sh_ldns eqNulls eqPures hprels1 quans
     with
         _ ->  generate_extra_defs prog is_pre cdefs unk_hps unk_svl hp r non_r_args args fs0_wg (* ogs *)
             lldns sh_ldns eqNulls eqPures hprels1 quans
  end

let get_longest_common_hnodes_list prog is_pre cdefs unk_hps unk_svl hp r non_r_args args fs_wg (* ogs *)=
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
  let pr2 = fun (_, def) -> Cprinter.string_of_hp_rel_def def in
  let pr3 = !CP.print_sv in
  let pr4 = !CP.print_svl in
  let pr5 = pr_list (pr_pair Cprinter.prtt_string_of_h_formula Cprinter.prtt_string_of_h_formula) in
  let pr6= (pr_list_ln pr2) in
  Debug.no_5 "get_longest_common_hnodes_list" pr3 pr4 pr4 pr4 pr1 (pr_pair pr6 pr5)
      (fun _ _ _ _ _-> get_longest_common_hnodes_list_x prog is_pre cdefs unk_hps unk_svl hp r non_r_args args fs_wg (*ogs*))
      hp args unk_hps unk_svl fs_wg


let find_closure_eq_null_x hp args f=
  let (_ ,mf,_,_,_,_) = CF.split_components f in
  let eqNulls = MCP.get_null_ptrs mf in
  let eqNulls1 = CP.intersect_svl args (CP.remove_dups_svl eqNulls) in
  if List.length eqNulls1 < 2 then f else
    let eqs = (MCP.ptr_equations_without_null mf) in
    let n_pure_eqs = generate_closure_eq_null args eqNulls1 eqs in
    CF.mkAnd_pure f (MCP.mix_of_pure n_pure_eqs) (CF.pos_of_formula f)

let find_closure_eq_null hp args f=
  let pr1 =  Cprinter.prtt_string_of_formula in
  Debug.no_3 "find_closure_eq_null" !CP.print_sv !CP.print_svl pr1 pr1
      (fun _ _ _ -> find_closure_eq_null_x hp args f)
      hp args f

let find_closure_eq_wg_x hp args fs_wg=
  let extract_eq_pos f=
    let (_ ,mf,_,_,_,_) = CF.split_components f in
    let eqs = (MCP.ptr_equations_without_null mf) in
    let eqs1 = List.filter (fun (sv1,sv2) -> CP.diff_svl [sv1;sv2] args = []) eqs in
    if eqs1 = [] then raise Not_found else
      let pos_eqs = List.map (fun (sv1,sv2) -> (get_pos args 0 sv1, get_pos args 0 sv2)) eqs1 in
      pos_eqs
  in
  let insert_closure pos_eqs_comm f=
    let hpargs = CF.get_HRels_f f in
    let rec_hpargs = List.filter (fun (hp1,_) -> CP.eq_spec_var hp hp1) hpargs in
    let ps = List.map (fun (_, r_args) ->
        let ss = List.map (fun (p1, p2) ->
            let svl = retrieve_args_from_locs r_args [p1;p2] in
            match svl with
              | [sv1;sv2] -> (sv1,sv2)
              | _ -> report_error no_pos "sau.find_closure_eq: impossible 2"
        ) pos_eqs_comm in
        let ps1 = List.map (fun (sv1, sv2) -> CP.mkEqVar sv1 sv2 no_pos) ss in
        CP.conj_of_list ps1 no_pos
    ) rec_hpargs in
    let n_p = CP.conj_of_list ps no_pos in
    CF.mkAnd_pure f (MCP.mix_of_pure n_p) no_pos
  in
  let get_common_eqs cur_comms pos_eqs=
    let new_comms = Gen.BList.intersect_eq (fun (p1,p2) (p3,p4) ->
    (p1=p3 && p2=p4) || (p1=p4 && p2=p3)) cur_comms pos_eqs
    in
    if new_comms = [] then raise Not_found else new_comms
  in
  if List.length args < 2 || List.length fs_wg < 2 then fs_wg else
    let fs1_wg = List.map (fun (f, og) -> (find_closure_eq_null hp args f, og)) fs_wg in
    try
      let ls_pos_eqs = List.map (fun (f, _) -> (extract_eq_pos f)) fs1_wg in
      let eq_comms = List.fold_left get_common_eqs (List.hd ls_pos_eqs) (List.tl ls_pos_eqs) in
      let fs2_wg = List.map (fun (f, og) -> (insert_closure eq_comms f, og)) fs1_wg in
      fs2_wg
    with Not_found -> fs1_wg

let find_closure_eq_wg hp args fs_wg=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln (pr_pair pr1 (pr_option pr1)) in
  Debug.no_3 "find_closure_eq_wg" !CP.print_sv !CP.print_svl pr2 pr2
      (fun _ _ _ -> find_closure_eq_wg_x hp args fs_wg)
      hp args fs_wg

let norm_conjH_f_x prog org_args args next_roots sh_ldns sh_lvns com_eqNulls com_eqPures com_hps (ldns, lvns, f)=
  (* let () =  DD.info_zprint (lazy (("       new args: " ^ (!CP.print_svl args)))) no_pos in *)
  (* let pr2 = pr_list Cprinter.string_of_h_formula in *)
  (* let () = DD.info_zprint (lazy (("      sh_ldns:" ^ (pr2 (List.map (fun hd -> CF.DataNode hd) sh_ldns))))) no_pos in *)
  let ( _,mix_f,_,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mix_f) in
  let (matcheds2, dn_rest2, vn_rest2, ss, last_ss0) =
    if sh_ldns <> [] then
      let matcheds2, dn_rest2, ss, last_ss0,_ = get_longest_common_hnodes_two org_args sh_ldns ldns eqs in
      (matcheds2, dn_rest2, [], ss, last_ss0)
    else
      let matcheds2, vn_rest2, ss, last_ss0,_ = get_longest_common_vnodes_two org_args sh_lvns lvns eqs in
      (matcheds2, [], vn_rest2, ss, last_ss0)
  in
  (*drop all matcheds*)
  let () =  DD.ninfo_zprint (lazy (("       matched 1: " ^ (!CP.print_svl matcheds2)))) no_pos in
  (* let () =  DD.info_zprint (lazy (("       eqNulls: " ^ (!CP.print_svl com_eqNulls)))) no_pos in *)
  (* let () =  DD.info_zprint (lazy (("       f: " ^ (Cprinter.prtt_string_of_formula f)))) no_pos in *)
  let nf1 = CF.drop_hnodes_f f matcheds2 in
  let () =  DD.ninfo_zprint (lazy (("       nf1: " ^ (Cprinter.prtt_string_of_formula nf1)))) no_pos in
  (* let () =  DD.info_zprint (lazy (("       args: " ^ (!CP.print_svl args)))) no_pos in *)
  let () =  DD.ninfo_zprint (lazy (("       last_ss0: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_sv) in pr last_ss0)))) no_pos in
  (*apply susbt ss*)
  let nf2 = CF.remove_com_pures nf1 com_eqNulls com_eqPures in
  (* let () =  DD.info_zprint (lazy (("       nf2: " ^ (Cprinter.prtt_string_of_formula nf2)))) no_pos in *)
  let nf3 = (* CF.subst *)CF.ins ss nf2 in
  let () =  DD.ninfo_zprint (lazy (("       nf3: " ^ (Cprinter.prtt_string_of_formula nf3)))) no_pos in
  (*if rest = [] then add pure equality all last_ss*)
  let nf5,last_ss=
    (*partition last_ss into two groups: one for subst another not*)
    (* let pr = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
    let last_ss1,last_ss2 = List.partition
      (fun (v1,v2) -> Gen.BList.difference_eq CP.eq_spec_var [v1;v2] args = [])
      last_ss0
    in
    (*mk eq for last_ss1*)
    let ps = List.concat (List.map (fun ((CP.SpecVar (t,v,p)) ,v2) ->
        if (is_pointer t)
        then [CP.mkPtrEqn v2 (CP.SpecVar (t,v,p)) no_pos]
        else []) last_ss1) in
    let p = CP.conj_of_list ps no_pos in
   (*apply subst last_ss2*)
    (* let () =  DD.ninfo_zprint (lazy (("       last_ss2: " ^ (pr last_ss2)))) no_pos in *)
    let nf4 = CF.ins last_ss2 nf3 in
    (*should remove x!=null if x is in matched2s*)
    (*combine them*)
    CF.mkAnd_pure nf4 (MCP.mix_of_pure p) no_pos,last_ss2
  in
  let () =  DD.ninfo_zprint (lazy (("       nf5: " ^ (Cprinter.prtt_string_of_formula nf5)))) no_pos in
  let nf6 = nf5 in
  let nf7 = CF.drop_exact_hrel_f nf6 com_hps com_eqPures in
  let () =  DD.ninfo_zprint (lazy (("       nf6: " ^ (Cprinter.prtt_string_of_formula nf6)))) no_pos in
  let () =  DD.ninfo_zprint (lazy (("       nf7: " ^ (Cprinter.prtt_string_of_formula nf7)))) no_pos in
  nf7

let norm_conjH_f prog org_args args next_roots sh_ldns sh_lvns com_eqNulls com_eqPures com_hps (ldns, lvns,f)=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 (a,b,_) = let pr = pr_pair !CP.print_sv (pr_list !CP.print_exp) in
  pr (a,b)
  in
  Debug.no_5 "norm_conjH_f" pr1 pr1 pr2 (pr_list !CP.print_formula) (pr_list pr3) pr2
      (fun _ _ _ _ _-> norm_conjH_f_x prog org_args args next_roots sh_ldns sh_lvns
          com_eqNulls com_eqPures com_hps (ldns, lvns, f))
      org_args args f com_eqPures com_hps

let get_sharing_x prog unk_hps r other_args args sh_ldns sh_lvns eqNulls eqPures hprels unk_svl=
  (* let other_args = List.tl args in *)
  (**********INTERNAL************)
  let get_connected_helper ((CP.SpecVar (t,v,p)) as r)=
    if CP.mem_svl r other_args then
      let new_v = CP.fresh_spec_var r in
      [(r,new_v)]
    else []
  in
  (***************DATA NODE****************)
  let rec look_up_next_ptrs_data nodes r res=
      match nodes with
        | [] -> ([],res,[],[])
        | node::nss -> if CP.eq_spec_var r node.CF.h_formula_data_node then
            let r_nexts,ssl = List.split (List.concat (List.map ((fun (CP.SpecVar (t,v,p)) ->
                if (is_pointer t) then
		  let ss = get_connected_helper (CP.SpecVar (t,v,p)) in
		  let new_v = CP.subs_one ss (CP.SpecVar (t,v,p)) in
		  ([new_v,ss])
                else [])) node.CF.h_formula_data_arguments))
            in
	    let ss = List.concat ssl in
	    let matched_hn =
	      if ss <> [] then 
		let r =(CF.h_subst ss (CF.DataNode node)) in
		match r with
		  | CF.DataNode hd -> hd
                  | _ -> report_error no_pos "sau.look_up_next_ptrs"
	      else node
	    in
            (r_nexts, res@nss,[matched_hn],ss)
          else look_up_next_ptrs_data nss r (res@[node])
  in
  let rec data_helper hds roots r_nexts r_done r_ss=
    match roots with
      | [] -> (r_nexts,hds,r_done,r_ss)
      | r::rs -> let nptrs,nhds,hn_done,ss = look_up_next_ptrs_data hds r [] in
                 data_helper nhds rs (r_nexts@nptrs) (r_done@hn_done) (r_ss@ss)
  in
  let rec data_get_last_ptrs_new ls_lnds roots root_nexts r_done r_ss=
    match root_nexts with
      | [] -> roots,r_done,r_ss,ls_lnds
      | _ -> let nptrs,nhds,hn_done,ss = data_helper ls_lnds root_nexts [] [] [] in
             data_get_last_ptrs_new nhds root_nexts nptrs (r_done@hn_done) (r_ss@ss)
  in
  (***************VIEW NODE****************)
  let rec look_up_next_ptrs_view nodes r res=
      match nodes with
        | [] -> ([],res,[],[])
        | node::nss -> if CP.eq_spec_var r node.CF.h_formula_view_node then
            let r_nexts,ssl = List.split (List.concat (List.map ((fun (CP.SpecVar (t,v,p)) ->
                if (is_pointer t) then
		  let ss = get_connected_helper (CP.SpecVar (t,v,p)) in
		  let new_v = CP.subs_one ss (CP.SpecVar (t,v,p)) in
		  ([new_v,ss])
                else [])) node.CF.h_formula_view_arguments))
            in
	    let ss = List.concat ssl in
	    let matched_hn =
	      if ss <> [] then
		let r =(CF.h_subst ss (CF.ViewNode node)) in
		match r with
		  | CF.ViewNode hd -> hd
                  | _ -> report_error no_pos "sau.look_up_next_ptrs"
	      else node
	    in
            (r_nexts, res@nss,[matched_hn],ss)
          else look_up_next_ptrs_view nss r (res@[node])
  in
  let rec view_helper hds roots r_nexts r_done r_ss=
    match roots with
      | [] -> (r_nexts,hds,r_done,r_ss)
      | r::rs -> let nptrs,nhds,hn_done,ss = look_up_next_ptrs_view hds r [] in
                 view_helper nhds rs (r_nexts@nptrs) (r_done@hn_done) (r_ss@ss)
  in
  let rec view_get_last_ptrs_new ls_lvds roots root_nexts r_done r_ss=
    match root_nexts with
      | [] -> roots,r_done,r_ss,ls_lvds
      | _ -> let nptrs,nhvs,hv_done,ss = view_helper ls_lvds root_nexts [] [] [] in
             view_get_last_ptrs_new nhvs root_nexts nptrs (r_done@hv_done) (r_ss@ss)
  in
  (**********INTERNAL************)
  let dnss, vnss, hdss, next_roots,ss=
    if sh_ldns <> [] then
      let next_roots,new_sh_dns,ss,rem_dns = data_get_last_ptrs_new sh_ldns [r] [r] [] [] in
      let dnss = (new_sh_dns@rem_dns) in
      let hdss = List.map (fun hd -> (CF.DataNode hd)) dnss in
      (dnss, [], hdss, next_roots,ss)
    else
      let next_roots,new_sh_vns,ss,rem_vns = view_get_last_ptrs_new sh_lvns [r] [r] [] [] in
      let vnss = (new_sh_vns@rem_vns) in
      let hvss = List.map (fun hd -> (CF.ViewNode hd)) vnss in
      ([], vnss, hvss, next_roots,ss)
  in
  let () = DD.ninfo_zprint (lazy (("      next_roots:" ^ (!CP.print_svl next_roots)))) no_pos in
  match next_roots with
    | [] -> report_error no_pos "sau.generalize_one_hp: sth wrong"
    | _ ->  let () = DD.ninfo_zprint (lazy (("      last root:" ^ (Cprinter.string_of_spec_var_list  next_roots)))) no_pos in
      (*generate new hp*)
      let n_args = (next_roots@other_args) in
      (*first rel def for the orig*)
      let rest =  (hdss@(List.map (fun hprel -> CF.HRel hprel) hprels)) in
      let orig_defs_h = match rest with
        | [] -> CF.HEmp
        | _ -> List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 no_pos) (List.hd rest) (List.tl rest)
      in
      let orig_def = CF.formula_of_heap orig_defs_h no_pos in
      (*common null process*)
      let orig_def1 =
	match eqNulls with
	  | [] -> orig_def
	  | _ ->
		let ps = List.map (fun v -> CP.mkNull v no_pos) eqNulls in
		let p = CP.conj_of_list ps no_pos in
		CF.mkAnd_pure orig_def (MCP.mix_of_pure p) no_pos
      in
      (*common pure process*)
      let common_pures = CP.conj_of_list eqPures no_pos in
      let orig_def2 = CF.mkAnd_pure orig_def1 (MCP.mix_of_pure common_pures) no_pos in
      (*subst*)
      (orig_def2, n_args , dnss, vnss, CP.diff_svl next_roots unk_svl)

let get_sharing prog unk_hps r other_args args sh_ldns sh_lvns eqNulls eqPures hprels unk_svl=
  (* let pr1 = !CP.print_sv in *)
  let pr2 = !CP.print_svl in
  let pr3 = fun hd -> Cprinter.prtt_string_of_h_formula (CF.DataNode hd) in
  let pr3a = fun hd -> Cprinter.prtt_string_of_h_formula (CF.ViewNode hd) in
  let pr4 =  pr_list !CP.print_formula in
  let pr6 = pr_penta (Cprinter.prtt_string_of_formula) pr2 (pr_list pr3) (pr_list pr3a) pr2 in
  let pr7a hrel = Cprinter.string_of_hrel_formula (CF.HRel hrel) in
  let pr7 = pr_list pr7a in
  Debug.no_7 "get_sharing " pr2  pr2 (pr_list pr3) (pr_list pr3a) pr2 pr4 pr7 pr6
      (fun _ _ _ _ _ _ _ -> get_sharing_x prog unk_hps r other_args args sh_ldns sh_lvns eqNulls eqPures hprels unk_svl)
      unk_hps args sh_ldns sh_lvns eqNulls eqPures hprels

let partition_common_diff_x prog hp args unk_hps unk_svl f1 f2 pos=
  let fs = [f1;f2] in
  let r,non_r_args = find_root prog (hp::unk_hps) args fs in
  (* let lldns = List.map (fun f -> (get_hdnodes f, f)) fs in *)
  let lldns_vns = List.map (fun f ->
       let hds,hvs,_ = CF.get_hp_rel_formula f in
       (hds, hvs,f)
   ) fs in
  let min,sh_ldns,sh_lvns,eqNulls,eqPures,hprels = get_min_common prog args unk_hps lldns_vns in
  if min = 0 (* && eqNulls = [] && eqPures= [] *) then
    (false,CF.mkTrue (CF.mkTrueFlow()) pos ,fs, [])
  else
    let sharing_f, n_args , sh_ldns2, sh_lvns2, next_roots = get_sharing prog unk_hps r non_r_args args sh_ldns sh_lvns eqNulls eqPures hprels unk_svl
    in
    let n_fs = List.map (norm_conjH_f prog args n_args next_roots sh_ldns2 sh_lvns2 eqNulls eqPures hprels) lldns_vns in
    (true, sharing_f,n_fs, next_roots)

let partition_common_diff prog hp args unk_hps unk_svl f1 f2 pos=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = !CP.print_svl in
  Debug.no_4 "partition_common_diff" pr2 pr2 pr1 pr1 (pr_quad string_of_bool pr1 (pr_list_ln pr1) pr2)
      (fun _ _ _ _ -> partition_common_diff_x prog hp args unk_hps unk_svl f1 f2 pos)
      args unk_hps f1 f2

let mkConjH_and_norm_x prog hp args unk_hps unk_svl f1 f2 pos=
  (*****INTERNAL*****)
  let get_view_info prog vn=
    let rec look_up_view vn0=
      let vdef = x_add C.look_up_view_def_raw 43 prog.C.prog_view_decls vn0.CF.h_formula_view_name in
      let fs = List.map fst vdef.C.view_un_struc_formula in
      let hv_opt = CF.is_only_viewnode false (CF.formula_of_disjuncts fs) in
      match hv_opt with
        | Some vn1 -> look_up_view vn1
        | None -> vdef
    in
    let vdef = look_up_view vn in
    ((vn.CF.h_formula_view_name,vdef.C.view_un_struc_formula, vdef.C.view_vars))
  in
  let try_unfold_view pure_f1 f2=
     let _,vns,_= CF.get_hp_rel_formula f2 in
     let need_unfold, pr_views=
       if vns = [] then false,[] else
       (true, List.map (fun vn -> get_view_info prog vn) vns)
     in
     if need_unfold then
       let nf = CF.do_unfold_view prog pr_views f2 in
       let fs = CF.list_of_disjs nf in
       let mp1 = MCP.mix_of_pure (CF.get_pure pure_f1) in
       let fs1 = List.filter (fun f ->
           let f1 = CF.mkAnd_pure f mp1 no_pos in
           not (is_inconsistent_heap f1)
       ) fs in
       (pure_f1, CF.formula_of_disjuncts fs1)
     else (pure_f1, f2)
  in
  let is_unsat f=
    CF.isAnyConstFalse f1 || is_unsat f
  in
  let b1 = is_unsat f1 in
  let b2 = is_unsat f2 in
  if b1 then f2 else
    if b2 then f1 else
  let is_common, sharing_f, n_fs,_ = partition_common_diff prog hp args unk_hps unk_svl f1 f2 pos in
  if not is_common then
    let b1 = Cfutil.is_empty_heap_f f1 in
    let b2 = Cfutil.is_empty_heap_f f2 in
    let nf1,nf2=
      match b1,b2 with
        | false,false
        | true,true -> (f1,f2)
        | false,true -> try_unfold_view f2 f1
        | true,false -> try_unfold_view f1 f2
    in
    (CF.mkConj_combine nf1 nf2 CF.Flow_combine pos)
  else
    match n_fs with
      | [] -> CF.mkFalse_nf pos
      | [f] -> CF.mkStar sharing_f f CF.Flow_combine pos
      | [nf1;nf2] -> begin
          (*check pure*)
          let b1 = Cfutil.is_empty_heap_f nf1 in
          let b2 = Cfutil.is_empty_heap_f nf2 in
          match b1,b2 with
            | true, true ->
                  CF.mkStar sharing_f (CF.mkStar nf1 nf2 CF.Flow_combine pos) CF.Flow_combine pos
            | true, false -> if check_inconsistency_f nf2 nf1 then
                CF.mkFalse_nf pos
              else
                CF.mkStar sharing_f (CF.mkStar nf1 nf2 CF.Flow_combine pos) CF.Flow_combine pos
            | false, true -> if check_inconsistency_f nf1 nf2 then
                CF.mkFalse_nf pos
              else
                CF.mkStar sharing_f (CF.mkStar nf1 nf2 CF.Flow_combine pos) CF.Flow_combine pos
            | false, false ->
                  (* let () = DD.info_zprint (lazy (("      xxx2-4: "  ))) no_pos in *)
                  CF.mkStar sharing_f (CF.mkConj_combine nf1 nf2 CF.Flow_combine pos) CF.Flow_combine pos
        end
      | _ -> report_error no_pos "sau.norm_and_heap: should be no more than two formulas"

let mkConjH_and_norm prog hp args unk_hps unk_svl f1 f2 pos=
  let pr1 = Cprinter.prtt_string_of_formula in
  Debug.no_3 "mkConjH_and_norm" pr1 pr1 !CP.print_svl pr1
      (fun _ _ _ -> mkConjH_and_norm_x prog hp args unk_hps unk_svl f1 f2 pos) f1 f2 unk_hps

let simplify_disj_x prog hp args unk_hps unk_svl f1 f2 pos=
  (*todo: revise partition_common_diff*)
  let helper f1 f2=
    let fs = [f1;f2] in
    let r,non_r_args = find_root prog (hp::unk_hps) args fs in
    (* let lldns = List.map (fun f -> (get_hdnodes f, f)) fs in *)
    let lldns_vns = List.fold_left (fun r2 f ->
       let hds,hvs,_ = CF.get_hp_rel_formula f in
       (r2@[hds,hvs,f])
   ) [] fs in
    let min,sh_ldns,sh_lvns,eqNulls,eqPures,hprels = get_min_common prog args unk_hps lldns_vns in
    if min = 0  && eqNulls = [] && eqPures= [] && hprels=[] then
      (false,CF.mkTrue (CF.mkTrueFlow()) pos ,fs)
    else
      let sharing_f, n_args , sh_ldns2,sh_lvns2, next_roots = get_sharing prog unk_hps r non_r_args args sh_ldns sh_lvns eqNulls eqPures hprels unk_svl in
      let n_fs = List.map (norm_conjH_f prog args n_args next_roots sh_ldns2 sh_lvns2 eqNulls eqPures hprels) lldns_vns in
      (true, sharing_f,n_fs)
  in
  let is_common, sharing_f, n_fs = helper f1 f2 in
  if not is_common then (false, [f1;f2]) else
    if List.for_all (fun f -> Cfutil.is_empty_heap_f f) n_fs then
      if List.exists is_empty_f n_fs then
        (true, [sharing_f])
      else (false, [f1;f2])
    else (false, [f1;f2])

let simplify_disj prog hp args unk_hps unk_svl f1 f2 pos=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln pr1 in
  Debug.no_2 "simplify_disj" pr1 pr1 (pr_pair string_of_bool pr2)
      (fun _ _ -> simplify_disj_x prog hp args unk_hps unk_svl f1 f2 pos) f1 f2

let perform_conj_unify_post_wg_x prog hp args unk_hps unk_svl fs_wg pos=
  match fs_wg with
    | [(f1,og1);(f2,og2)] ->
          let is_common, sharing_f, n_fs, _ = partition_common_diff prog hp args unk_hps unk_svl f1 f2 pos in
      if not is_common then fs_wg else
        if List.for_all (fun f ->  Cfutil.is_empty_heap_f f) n_fs then
          let ps = List.map (fun f -> CF.get_pure f) n_fs in
          let p = CP.disj_of_list ps pos in
          let neg_p = CP.mkNot p None pos in
          if not(TP.is_sat_raw (MCP.mix_of_pure neg_p)) then
            [(sharing_f, og1)]
          else fs_wg
        else fs_wg
    | _ -> fs_wg

let perform_conj_unify_post_wg prog hp args unk_hps unk_svl fs_wg pos=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln (pr_pair pr1 (pr_option pr1)) in
  Debug.no_1 "perform_conj_unify_post_wg" pr2 pr2
      (fun _ -> perform_conj_unify_post_wg_x prog hp args unk_hps unk_svl fs_wg pos) fs_wg

(*match hprel: with the same args: TODO: enhance with data node + view node*)
let norm_heap_consj_x h1 h2 equivs=
  let equiv_cmp (h1,h2) (h3,h4) = (CP.eq_spec_var h1 h3 && CP.eq_spec_var h2 h4) ||
    (CP.eq_spec_var h1 h4 && CP.eq_spec_var h2 h3)
  in
  let hp_cmp (_,args1) (_,args2) =
    let s1 = String.concat "" (List.map !CP.print_sv args1) in
    let s2 = String.concat "" (List.map !CP.print_sv args2) in
    String.compare s1 s2
  in
  let rec hp_match hpargs1 hpargs2 res=
    match hpargs1, hpargs2 with
      | [],[] -> true,res
      | (hp1,args1)::rest1,(hp2,args2)::rest2 ->
            if eq_spec_var_order_list args1 args2 then
              let nres=
                if CP.eq_spec_var hp1 hp2 then res else (res@[(hp1,hp2)])
              in
              hp_match rest1 rest2 nres
            else
              (false,res)
      | _ -> false,res
  in
  let hpargs1 = CF.get_HRels h1 in
  let hpargs2 = CF.get_HRels h2 in
  let hpargs11 = List.sort hp_cmp hpargs1 in
  let hpargs21 = List.sort hp_cmp hpargs2 in
  let is_matched, new_equiv =  hp_match hpargs11 hpargs21 [] in
  if is_matched then
    let new_equiv = Gen.BList.difference_eq equiv_cmp new_equiv equivs in
    let equivs1 =  equivs@new_equiv in
    let parts = partition_subst_hprel equivs1 [] in
    let new_h1 = List.fold_left (fun hf0 (from_hps, to_hp) -> CF.subst_hprel_hf hf0 from_hps to_hp) h1 parts in
    let new_h2 = List.fold_left (fun hf0 (from_hps, to_hp) -> CF.subst_hprel_hf hf0 from_hps to_hp) h2 parts in
    if fst (check_stricteq_h_fomula true new_h1 new_h2) then
      Some (new_h1, equivs1)
    else None
  else None


let norm_heap_consj h1 h2 equivs=
  let pr1 = Cprinter.prtt_string_of_h_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 ores= match ores with
    | None -> "NONE"
    | Some x -> (pr_pair pr1 pr2) x in
  Debug.no_2 "norm_heap_consj" pr1 pr1 pr3
      (fun _ _ -> norm_heap_consj_x h1 h2 equivs) h1 h2

let subst_equiv_hf equivs hf=
  let parts = partition_subst_hprel equivs [] in
  let new_hf = List.fold_left (fun hf0 (from_hps, to_hp) -> CF.subst_hprel_hf hf0 from_hps to_hp) hf parts in
  new_hf

let subst_equiv equivs f=
  let parts = partition_subst_hprel equivs [] in
  let new_f = List.fold_left (fun f0 (from_hps, to_hp) -> CF.subst_hprel f0 from_hps to_hp) f parts in
  new_f

let norm_heap_consj_formula_x prog args unk_hps unk_svl f0 equivs0=
  let rec unify_conj2 conj_hfs hf1 res_equivs=
    match conj_hfs with
      | [] -> Some (hf1, res_equivs)
      | hf2::rest -> begin
            let ores = norm_heap_consj hf1 hf2 res_equivs in
            match ores with
              | None -> None
              | Some (nhf1, n_equivs) -> unify_conj2 rest nhf1 n_equivs
        end
  in
  let rec unify_conj conj_hfs res_equivs=
    match conj_hfs with
      | [] -> None
      | [hf] -> Some (subst_equiv_hf res_equivs hf, res_equivs)
      | hf1::rest -> begin
          let ores = unify_conj2 rest hf1 res_equivs in
          match ores with
              | None -> None
              | Some (_, n_equiv) -> unify_conj rest n_equiv
        end
  in
  let process_one f equivs1=
    let conj_hfs, rem_f = CF.partition_heap_consj f in
    let ores = unify_conj conj_hfs equivs1 in
    match ores with
      | None -> (f, equivs1)
      | Some (hf, n_equivs) ->
            let nf = CF.mkAnd_f_hf rem_f hf (CF.pos_of_formula f) in
            (nf, n_equivs)
  in
  let fs = CF.list_of_disjs f0 in
  let n_fs, n_equiv = List.fold_left (fun (r_fs, r_equivs) f ->
      let nf, n_equivs =  process_one f r_equivs in
      (r_fs@[nf], n_equivs)
  ) ([],equivs0) fs
  in
  let nf0 = CF.join_conjunct_opt n_fs in
  match nf0 with
    | None -> (f0, equivs0)
    | Some f01 -> (f01, n_equiv)

let norm_heap_consj_formula prog args unk_hps unk_svl f equivs=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 = (pr_pair pr1 pr2) in
  Debug.no_1 "norm_heap_consj_formula" pr1 pr3
      (fun _ -> norm_heap_consj_formula_x prog args unk_hps unk_svl f equivs) f

let norm_formula_x prog hp args unk_hps unk_svl f1 f2 equivs=
  if Cfutil.is_empty_heap_f f1 && Cfutil.is_empty_heap_f f2 then
    let pos = CF.pos_of_formula f1 in
    let cmb_f = CF.mkStar f1 f2 CF.Flow_combine pos in
    let cmb_f1=
      if not (TP.is_sat_raw (MCP.mix_of_pure (CF.get_pure cmb_f))) then
        CF.mkFalse (CF.flow_formula_of_formula cmb_f) pos
      else cmb_f
    in
    Some (cmb_f1, equivs)
  else if CF.isStrictConstTrue f1 then Some (f2, equivs)
  else if CF.isStrictConstTrue f2 then Some (f1, equivs)
  else
    let is_common, sharing_f, n_fs,_ = partition_common_diff prog hp args unk_hps unk_svl f1 f2 no_pos in
    if not is_common then None else
      match n_fs with
        | [] -> None
        | [f] -> Some (f, equivs)
        | [nf1;nf2] -> begin
            let (hf1 ,mf1,_,_,_,_) = CF.split_components nf1 in
            let (hf2 ,mf2,_,_,_,_) = CF.split_components nf2 in
            if CP.equalFormula (MCP.pure_of_mix mf1) (MCP.pure_of_mix mf2) then
              let ores = norm_heap_consj hf1 hf2 equivs in
              match ores with
                | None -> None
                | Some (hf, n_equivs) ->
                      Some (CF.mkAnd_f_hf sharing_f hf no_pos, n_equivs)
            else
              None
          end
        | _ -> report_error no_pos "sau.norm_formula: should be no more than two formulas"

let norm_formula prog hp args unk_hps unk_svl f1 f2 equivs=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 ores= match ores with
    | None -> "NONE"
    | Some (f, equivs) -> (pr_pair pr1 pr2)  (f, equivs)
  in
  Debug.no_2 "norm_formula" pr1 pr1 pr3
      (fun _ _ -> norm_formula_x prog hp args unk_hps unk_svl f1 f2 equivs) f1 f2

(************************************************************)
      (******************END FORM HP DEF*********************)
(************************************************************)

(************************************************************)
    (****************SUBST HP PARDEF*****************)
(************************************************************)
let rec look_up_subst_group hp args nrec_grps=
  (*refresh all ptrs except ones in args2 which substed by args*)
  let rec refresh_ptrs args2 ptrs r_ss=
    match ptrs with
      | [] -> r_ss
      | sv::svl ->
          if CP.mem_svl sv args2 then
             refresh_ptrs args2 svl r_ss
          else
            let f_sv = CP.fresh_spec_var sv in
            refresh_ptrs args2 svl r_ss@[(sv,f_sv)]
  in
  let rec susbt_group fs pardefs=
    match pardefs with
      | [] -> fs
      | (_, args2,_, f,_)::pss->
          (*should refresh f*)
          let ptrs = CF.get_ptrs_w_args_f f in
          let ss1 = refresh_ptrs args2 (CP.remove_dups_svl ptrs) [] in
          let ss = List.combine args2 args in
          let nf1 = CF.subst (ss) f in
          let nf2 = CF.subst (ss1) nf1 in
          (* let svl = List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (CF.fv f)) in *)
          (* let fr_svl = CP.fresh_spec_vars svl in *)
          (* let ss = List.combine svl fr_svl in *)
          (* let nf1 = CF.subst (ss) f in *)
          (* let args21 = CP.subst_var_list ss args2 in *)
          (* let ss1 = List.combine args21 args in *)
          (* let nf2 = CF.subst ss1 nf1 in *)
          (* let () = DD.info_zprint (lazy (("       f:" ^ (Cprinter.prtt_string_of_formula f)))) no_pos in *)
          (* let () = DD.info_zprint (lazy (("       nf1:" ^ (Cprinter.prtt_string_of_formula nf1)))) no_pos in *)
          (* let () = DD.info_zprint (lazy (("       nf2:" ^ (Cprinter.prtt_string_of_formula nf2)))) no_pos in *)
          susbt_group (fs@[nf2]) pss
  in
  match nrec_grps with
    | [] -> [](* report_error no_pos "sau.look_up_groups" *)
    | grp::gs -> begin
        if grp = [] then look_up_subst_group hp args gs else
          let hp1,_,_,_,_ = (List.hd grp) in
          if CP.eq_spec_var hp hp1 then
            [(hp1,susbt_group [] grp)]
          else
            look_up_subst_group hp args gs
    end

let compose_subs_x f1 f2 pos=
  let ptrs = get_data_view_hrel_vars_formula f1 in
  let new_f2 = CF.drop_hnodes_f f2 ptrs in
  let ls_hpargs1 = CF.get_HRels_f f1 in
  let ls_hpargs2 = CF.get_HRels_f new_f2 in
  let ls_inter = Gen.BList.intersect_eq check_hp_arg_eq ls_hpargs2 ls_hpargs1 in
  let dups_hps = List.map fst ls_inter in
  let new_f21,_ = CF.drop_hrel_f new_f2 dups_hps in
  (* let () = DD.info_zprint (lazy (("       new_f21:" ^ (pr new_f21)))) no_pos in *)
  CF.mkStar f1 new_f21 CF.Flow_combine pos

let compose_subs f1 f2 pos=
  let pr1 = Cprinter.prtt_string_of_formula in
  Debug.no_2 "compose_subs" pr1 pr1 pr1
      (fun _ _ -> compose_subs_x f1 f2 pos) f1 f2

(*this function is used two times: succ subts with
 - first for nrec_grp and
 - at the end for rec_indp_grp
*)
let succ_subst_x prog nrec_grps unk_hps allow_rec_subst (hp,args,og,f,unk_svl)=
  DD.ninfo_zprint (lazy (("       succ_susbt hp: " ^ (!CP.print_sv hp)))) no_pos;
  let pos = no_pos in
  let simplify_and_empty_test args f=
    let f1 = simplify_one_formula prog args f in
    let r =
      if is_empty_f f1 then []
      else [(hp,args,og,f1,unk_svl)]
    in
    r
  in
  (*l1 x l2*)
  let helper ls1 ls2=
    (* let pr = (Cprinter.prtt_string_of_formula) in *)
    (* let pr1 = pr_list_ln pr in *)
    let res = List.concat (List.map (fun f1 ->
        List.map (fun f2 ->
            compose_subs f1 f2 pos
    ) ls2) ls1)
    in
    (* let () = DD.info_zprint (lazy (("       res:" ^ (pr1 res)))) no_pos in *)
    res
  in
  let succ_hp_args = CF.get_HRels_f f in
  (*filter hp out if not allow subst by itself*)
  let succ_hp_args =
    if allow_rec_subst then succ_hp_args else
      List.filter (fun (hp1,_) -> not (CP.eq_spec_var hp hp1)) succ_hp_args
  in
  DD.ninfo_pprint ("       succ_hp_args:" ^ (let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl)
                                            in pr succ_hp_args)) no_pos;
  match succ_hp_args with
    | [] -> (false, simplify_and_empty_test args f)
    | _ -> begin
        let r = List.concat (List.map (fun (hp0,arg0) -> look_up_subst_group hp0 arg0 nrec_grps)  succ_hp_args) in
        if List.length r = 0 then
          (false, simplify_and_empty_test args f)
        else
          let matched_hps, fs_list = List.split r in
        (*create template from f*)
          let nf,_ = CF.drop_hrel_f f matched_hps in
        (*combine fs_list*)
          let lsf_cmb = List.fold_left helper [nf]
            (List.filter (fun ls -> ls <>[]) fs_list) in
          DD.ninfo_pprint ("       succ_susbt lsf_cmb:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula)
                                                          in pr lsf_cmb)) no_pos;
          let lsf_cmb1 = List.map (simplify_one_formula prog args) lsf_cmb in
          let lsf_cmb2 = List.filter (fun f ->  not (is_trivial f (hp,args))
              && not (is_inconsistent_heap f)
          ) lsf_cmb1 in
        (*remove f which has common prefix*)
          let lsf_cmb3 = remove_longer_common_prefix lsf_cmb2 in
          DD.ninfo_pprint ("       succ_susbt lsf_cmb 1:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula)
               in pr lsf_cmb1)) no_pos;
          (* DD.info_pprint ("       succ_susbt lsf_cmb 2:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula) *)
          (*      in pr lsf_cmb2)) no_pos; *)
          let fss = List.map (fun f1 -> (hp,args,og, f1,unk_svl)) lsf_cmb3 in
          (true, fss)
    end

let succ_subst prog nrec_grps unk_hps allow_rec_subst (hp,args,og,f,unk_svl)=
   let pr1 = pr_list_ln (pr_list_ln string_of_par_def_w_name_short) in
   let pr2 = pr_penta !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula_opt Cprinter.prtt_string_of_formula !CP.print_svl in
   let pr3 = pr_pair string_of_bool (pr_list_ln pr2) in
   Debug.no_4 "succ_subst" pr1 string_of_bool !CP.print_svl pr2 pr3
       (fun _ _ _  _ -> succ_subst_x prog nrec_grps unk_hps allow_rec_subst (hp,args,og,f,unk_svl))
       nrec_grps allow_rec_subst unk_hps (hp,args,og,f,unk_svl)

let succ_subst_with_mutrec_x prog deps unk_hps=
  let find_succ_one_dep_grp dep_grp=
    let (hp,_,_,_,_) = List.hd dep_grp in
    let succ_hps = List.concat (List.map (fun (_,_,_,f,_) -> CF.get_hp_rel_name_formula f) dep_grp) in
    (*remove dups*)
    let succ_hps1 = Gen.BList.remove_dups_eq CP.eq_spec_var succ_hps in
    (* DD.ninfo_zprint (lazy (("       succ_hps: " ^ (!CP.print_svl succ_hps)))) no_pos; *)
      (*remove unk_hps*)
      (* let succ_hps2 = List.filter (fun hp1 -> not (CP.mem_svl hp1 unk_hps)) succ_hps1
      in *)
    (hp,succ_hps1)
  in
  let update_helper hp0 succ0 (hp1,succ1)=
    if CP.mem_svl hp0 succ1 then (hp1,CP.remove_dups_svl (succ0@succ1))
    else (hp1,succ1)
  in
  let check_mutrec ls_hp_succ=
    let rec subst_helper ls res=
      match ls with
        | [] -> res
        | (hp,succ_hps)::tl ->
            let indir_succ_hps = List.concat (List.map (fun (hp,succ1) -> if CP.mem_svl hp succ_hps
                then succ1 else []) (tl@res)) in
            let new_succ = CP.remove_dups_svl (succ_hps@indir_succ_hps) in
            let new_res = List.map (update_helper hp new_succ) res in
            let new_tl = List.map (update_helper hp new_succ) tl in
            subst_helper new_tl (new_res@[(hp,new_succ)])
    in
    let closed_ls_hp_succ = subst_helper ls_hp_succ [] in
    List.concat (List.map (fun (hp,succ) -> if CP.mem_svl hp succ then [hp] else []) closed_ls_hp_succ)
  in
  let check_subst_diverge ls_mut_rec_hp_succ=
    let rec rec_check_diverge hp last history=
      (*START debugging*)
      (* let () = DD.info_zprint (lazy (("       hp: " ^ (!CP.print_sv hp)))) no_pos in *)
      (* let () = DD.info_zprint (lazy (("       last: " ^ (!CP.print_svl last)))) no_pos in *)
      (* let () = DD.info_zprint (lazy (("       history: " ^ (let pr = pr_list !CP.print_svl in pr history)))) no_pos in *)
      (*END debugging*)
      let last1 = List.filter (fun hp0 -> not (CP.eq_spec_var hp0 hp)) last in
      if last1 = [] then false else
        if List.exists
          (fun prev_succ -> CP.diff_svl prev_succ last1 = []) history then true
        else
          let new_succ = List.concat (List.map (fun (hp0,succ0) -> if CP.mem_svl hp0 last1 then succ0 else []) ls_mut_rec_hp_succ) in
          let new_last = CP.remove_dups_svl (new_succ) in
          rec_check_diverge hp new_last (history@[last1])
    in
    let rec_diverge,rec_terminating = List.partition
      (fun (hp0,succ0) -> rec_check_diverge hp0 succ0 []) ls_mut_rec_hp_succ in
    (List.map fst rec_terminating, List.map fst rec_diverge)
  in
  let subst_one_mutrec_grp all_orig_mut_rec_grps terminating_mutrec_grp=
    let rec susbt_helper grp=
      let bs, ls_new_grp = List.split (List.map (succ_subst prog all_orig_mut_rec_grps unk_hps false) grp) in
      let b = List.fold_left (fun b1 b2 -> b1 || b2) false bs in
      let new_grp = List.concat ls_new_grp in
      if b then susbt_helper new_grp else new_grp
    in
    susbt_helper terminating_mutrec_grp
  in
  let ls_hp_succ = List.map find_succ_one_dep_grp deps in
  let mut_rec_hps = check_mutrec ls_hp_succ in
  (*START debugging*)
  (* let pr1 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let () = DD.info_zprint (lazy (("       ls_hp_succ: " ^ (pr1 ls_hp_succ)))) no_pos in *)
  (* let () = DD.info_zprint (lazy (("       mut_rec_hps: " ^ (!CP.print_svl mut_rec_hps)))) no_pos in *)
  (*END debugging*)
  if mut_rec_hps = [] then ([],[],deps,[]) else
  (*partition*)
    let mut_rec_deps,nmut_rec_deps= List.partition (fun grp ->
        let (hp,_,_,_,_) = List.hd grp in
        CP.mem_svl hp mut_rec_hps
    ) deps
    in
    (*check safe subst*)
    let ls_mut_rec_hp_succ = List.filter (fun (hp,_) -> CP.mem_svl hp mut_rec_hps) ls_hp_succ in
    let to_be_subst,to_be_not_subst = check_subst_diverge ls_mut_rec_hp_succ in
    (*START debugging*)
    (* let () = DD.info_zprint (lazy (("       to_be_subst: " ^ (!CP.print_svl to_be_subst)))) no_pos in *)
    (* let () = DD.info_zprint (lazy (("       to_be_not_subst: " ^ (!CP.print_svl to_be_not_subst)))) no_pos in *)
    (*END debugging*)
    let rem,to_be_subst_grps = List.partition
      (fun grp -> let (hp0,_,_,_,_) = List.hd grp in
                  CP.mem_svl hp0 to_be_not_subst
      ) mut_rec_deps
    in
    (*subst*)
    let substed_mit_rec_indp = List.map (subst_one_mutrec_grp mut_rec_deps) to_be_subst_grps in
  (substed_mit_rec_indp,rem,nmut_rec_deps,to_be_subst)

(*out: rec_indp,rec_dep,nrec_deps*)
let succ_subst_with_mutrec prog deps unk_hps=
  let pr1 = pr_list_ln (pr_list_ln string_of_par_def_w_name_short) in
  Debug.no_1 " succ_subst_with_mutrec" pr1 (pr_quad pr1 pr1 pr1 !CP.print_svl)
      (fun _ -> succ_subst_with_mutrec_x prog deps unk_hps) deps

let succ_subst_with_rec_indp_x prog rec_indp_grps unk_hps depend_grps=
  let is_independ_pardef (hp,_,_,f,_) =
    let hps = CF.get_hp_rel_name_formula f in
    let hps = CP.remove_dups_svl hps in
    (* DD.ninfo_zprint (lazy (("       rec hp: " ^ (!CP.print_sv hp)))) no_pos; *)
    let _,rems = List.partition (fun hp1 -> CP.eq_spec_var hp hp1) hps in
    (* DD.ninfo_zprint (lazy (("       rec rems: " ^ (!CP.print_svl rems)))) no_pos; *)
    (rems = [])
  in
  let is_independ_group grp =
    List.for_all is_independ_pardef grp
  in
  let get_hp_name_from_grp grp=
    match grp with
      | [] -> report_error no_pos "sau.succ_susbt_with_rec_indp: should not empty"
      | (hp,_,_,_,_)::_ -> hp
  in
  let refine_grp_helper_x hp0 args0 fss=
    let fss1 = remove_longer_common_prefix fss in
    (* let fss1 = Gen.BList.remove_dups_eq (fun f1 f2 -> check_relaxeq_formula f1 f2) fss in *)
    let fss2= List.filter (fun f ->  not (is_trivial f (hp0,args0)) ) fss1 in
    (*remove neqNull if fss>1 formula*)
    let fss3 =
      if List.length fss2 > 1 then
        (* List.filter (fun f -> not(CF.is_only_neqNull args0 [] f)) fss2 *)
        let helper f=
          let f1 = CF.remove_neqNulls_f f in
          if is_empty_f f1 then [] else [f1]
        in
        List.concat (List.map helper fss2)
      else fss2
    in
    fss3
  in
  let refine_grp_helper hp0 args0 fss=
    let pr1= pr_list_ln Cprinter.prtt_string_of_formula in
    Debug.no_3 "refine_grp_helper" !CP.print_sv !CP.print_svl pr1 pr1
        (fun _ _ _ -> refine_grp_helper_x hp0 args0 fss)
        hp0 args0 fss
  in
  (********************)
  (* preprocess rec_indps:
     subst rec branch by all base branches
  *)
(*
  let preprocess_rec_indp_x grp=
    let rec_branches,base_branches = List.partition is_rec_pardef grp in
    if rec_branches = [] || base_branches = [] then grp else
      begin
          (*each rec_branch, substed by base*)
          let new_rec_bracnhes = List.concat (snd (List.split (
              List.map (succ_susbt prog [base_branches] unk_hps true) rec_branches))) in
          match new_rec_bracnhes with
            | [] -> base_branches
            | (hp1,args1,_,unk_svl)::_ ->
                let new_rec_fss = refine_grp_helper hp1 args1 (List.map (fun (_,_,f,_)-> f) new_rec_bracnhes) in
                let new_rec_bracnhes1 =  List.map (fun f -> (hp1,args1,f,unk_svl)) new_rec_fss in
                (base_branches@new_rec_bracnhes1)
      end
  in
  (*for debugging**)
  let preprocess_rec_indp grp=
    let pr1 = (pr_list_ln string_of_par_def_w_name_short) in
    Debug.no_1 "preprocess_rec_indp" pr1 pr1
        (fun _ -> preprocess_rec_indp_x grp) grp
  in
*)
  (*END for debugging**)
  (* let rec_indp_grps1 = List.map preprocess_rec_indp rec_indp_grps in *)
  (*********************************)
        (*******END***************)
  (********************************)
  let rec get_last_ptr_x args0 hds=
    match hds with
      | [] -> args0
      | hd ::tl ->
          let args1 = List.filter (fun a -> not (CP.eq_spec_var hd.CF.h_formula_data_node a)) args0 in
          if List.length args1 < List.length args0 then
            let new_ptrs = List.filter CP.is_node_typ hd.CF.h_formula_data_arguments in
            get_last_ptr_x (CP.remove_dups_svl (args1@new_ptrs)) tl
          else
            get_last_ptr_x args0 tl
  in
  let rec get_last_ptr args0 hds=
    let pr1 = !CP.print_svl in
    let pr2 = !CP.print_svl in
    Debug.no_1 "get_last_ptr" pr1 pr2
        (fun _ -> get_last_ptr_x args0 hds) args0
  in
  let succ_subst_one_pardef rec_indp_hps (hp,args,og,f,unk_svl)=
    let () = DD.ninfo_zprint (lazy (("       hp: " ^ (!CP.print_sv hp)))) no_pos in
    let () = DD.ninfo_zprint (lazy (("       rec_indp_hps: " ^ (!CP.print_svl rec_indp_hps)))) no_pos in
    let succ_hprels = CF.get_hprel f in
    let succ_hps = (List.map (fun (hp,_,_) -> hp) succ_hprels) in
    let succ_hps1 = List.filter (fun hp1 -> not (CP.eq_spec_var hp1 hp)) succ_hps in
    (* let () = DD.info_zprint (lazy (("       succ_hps1: " ^ (!CP.print_svl succ_hps1)))) no_pos in *)
    let new_pardefs=
      if (succ_hps1 = []) || (CP.diff_svl succ_hps1 rec_indp_hps <> []) (* || *)
        (* not (CF.is_HRel_f f) *)
        (*currently we just support f without hnodes hns, should enhance:
          recursive branches: matching with hns first
        *)
      then
        [(hp,args,og,f,unk_svl)]
      else
        let _, fss = succ_subst prog rec_indp_grps unk_hps false (hp,args,og,f,unk_svl) in
        (* let pr1= Cprinter.prtt_string_of_formula in *)
        (* let pr2 (_,_,a,_)= pr1 a in *)
        (* let pr3 = pr_list_ln pr2 in *)
        (* let () = DD.info_zprint (lazy (("       fss: " ^ (pr3 fss)))) no_pos in *)
        (* let hprel = mkHRel hp args no_pos in *)
        (* let ss = List.map (fun hprel1 -> ((CF.HRel hprel1), hprel)) succ_hprels in *)
        (* let fss1 = List.map (fun (_,_,f,_) -> (CF.subst_hrel_f f ss)) fss in *)
        (*pair args*)
        let hds = get_hdnodes f in
        let pr_args = List.map (fun a -> let last_args=get_last_ptr [a] hds in (a,last_args)) args in
        let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
        let () = DD.ninfo_zprint (lazy (("       pr_args: " ^ (pr1 pr_args)))) no_pos in
        let subst_helper pr_args0 (hp1,eargs1,p)=
          let args1 = List.concat (List.map CP.afv eargs1) in
          let rec get_new_arg ls r=
            match ls with
              | [] -> r
              | (a,last_args)::tl ->
                  let inter= CP.intersect_svl last_args args1 in
                  let new_a=
                    match inter with
                      | [] -> a
                      | [na] -> na
                      | _ -> report_error no_pos "sau.subst_helper"
                  in
                  get_new_arg tl (r@[new_a])
          in
          let rec add_anon_args ls l_args1 r=
            match ls with
              | [] -> r
              | a::tl -> if CP.mem_svl a l_args1 then
                    add_anon_args tl l_args1 (r@[a])
                  else
                    let fr_a = CP.fresh_spec_var a in
                    add_anon_args tl l_args1 (r@[fr_a])
          in
          let new_args0 = if List.length args = List.length args1 then
            get_new_arg pr_args0 []
              else add_anon_args args args1 []
          in
          let hprel = mkHRel hp new_args0 no_pos in
          ((CF.HRel (hp1,eargs1,p)), hprel)
        in
        let ss = List.map (subst_helper pr_args) succ_hprels in
        let fss1 = List.map (fun (_,_,_,f,_) -> (CF.subst_hrel_f f ss)) fss in
        (* let fss1 = List.map (fun (_,_,f,_) -> (CF.subst_hprel f succ_hps1 hp)) fss in *)
        let fss2 = refine_grp_helper hp args (fss1) in
        let fss3 = List.map (fun f1 -> (hp,args,og,f1,unk_svl)) fss2 in
        fss3
    in
    new_pardefs
  in
  let succ_subst_one_grp rec_indp_hps grp=
    let pardefs =
      if List.length grp > 1 then
        List.concat (List.map (succ_subst_one_pardef rec_indp_hps) grp)
      else grp
    in
    pardefs
  in
  let rec susbt_fix rec_indp_grps0 depend_grps0 r=
  (*get all rec_indp hp names*)
    let rec_indp_hps = List.map get_hp_name_from_grp rec_indp_grps0 in
    let new_dep_grps = List.map (succ_subst_one_grp rec_indp_hps) depend_grps0 in
    let new_indp_grps,deps = List.partition is_independ_group new_dep_grps in
    if new_indp_grps = [] || deps = [] then
      (r@new_dep_grps)
    else susbt_fix (rec_indp_grps0@new_indp_grps) deps (r@new_indp_grps)
  in
  susbt_fix rec_indp_grps depend_grps []

let succ_subst_with_rec_indp prog rec_indp_grps unk_hps depend_grps=
  let pr1 = pr_list_ln (pr_list_ln string_of_par_def_w_name_short) in
  Debug.no_3 "succ_subst_with_rec_indp" pr1 !CP.print_svl pr1 pr1
      (fun _ _ _ -> succ_subst_with_rec_indp_x prog rec_indp_grps unk_hps depend_grps)
      rec_indp_grps unk_hps depend_grps

(************************************************************)
    (****************END SUBST HP PARDEF*****************)
(************************************************************)

(************************************************************)
    (****************SUBST HP DEF*****************)
(************************************************************)

let look_up_subst_hpdef_x link_hps hp args (nrec_hpdefs: CF.hp_rel_def list)=
  let rec helper grp=
    match grp with
      | [] -> ([],args,[])(* report_error no_pos "sau.look_up_groups" *)
      | d1::gs -> begin
          let a1 = d1.CF.def_cat in
          let hp1 = CF.get_hpdef_name a1 in
          (* DD.info_zprint (lazy (("       hp: " ^ (!CP.print_sv hp)))) no_pos; *)
          (* DD.info_zprint (lazy (("       succ_susbt_def hp1: " ^ (!CP.print_sv hp1)))) no_pos; *)
          if CP.eq_spec_var hp hp1 then
            let args1 = get_ptrs d1.CF.def_lhs in
            let ss = List.combine args1 args in
            let ls_f_og = List.map (fun (f1, og1) ->(CF.subst ss f1, CF.subst_opt ss og1)) d1.CF.def_rhs in
            (*get top_guard*)
            (* let guarded_tops, rem = List.fold_left (fun (r1,r2) (f, og) -> *)
            (*     match og with *)
            (*       | None ->  (r1,r2@[f,og]) *)
            (*       | Some f1 -> (\* if CF.isStrictConstHTrue f then *\) *)
            (*           if CF.is_top_guard f link_hps og then *)
            (*           (r1@[(f,og)],r2) *)
            (*         else (r1,r2@[f,og]) *)
            (* ) ([],[]) ls_f_og in *)
            let rem1 = List.fold_left (fun r (f, og) -> let fs = CF.list_of_disjs f in
            r@(List.map (fun f-> (f,og)) fs)
            ) [] ls_f_og in
            (rem1, args,[])
          else
            helper gs
        end
  in
  helper nrec_hpdefs

let rec look_up_subst_hpdef link_hps hp args (nrec_hpdefs: CF.hp_rel_def list)=
  let pr1 = !CP.print_sv in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = Cprinter.prtt_string_of_formula_opt in
  Debug.no_1 "look_up_subst_hpdef" pr1 (pr_triple (pr_list_ln (pr_pair pr2 pr3))
      !CP.print_svl (pr_list_ln (pr_pair pr2 (pr_opt pr2))))
      (fun _ -> look_up_subst_hpdef_x link_hps hp args nrec_hpdefs) hp

let succ_subst_hpdef_x prog link_hps (nrec_hpdefs: CF.hp_rel_def list) all_succ_hp (hp,args,g,f)=
  DD.ninfo_zprint (lazy (("       succ_subst_def hp: " ^ (!CP.print_sv hp)))) no_pos;
  DD.ninfo_zprint (lazy (("       all_succ_hp: " ^ (!CP.print_svl all_succ_hp)))) no_pos;
  let pos = no_pos in
  (*l1 x l2*)
  let is_guard_consistent f g=
     match g with
       | None -> true
       | Some g_f1 ->
             not( is_inconsistent_heap (CF.mkAnd_pure f (MCP.mix_of_pure (CF.get_pure g_f1)) no_pos ))
  in
  let drop_dups_guards f og=
    let nog =
      match og with
        | None -> None
        | Some fg -> let nf = CF.drop_dups f fg in
          if is_empty_f nf then None else (Some nf)
    in
    nog
  in
  let helper ls1 (ls_f_og, args, top_guard)=
    let n_ls1 = List.fold_left (fun r1 (f1,og1) ->
        (* let is_top, nf1 = List.fold_left (fun (cur_b,cur_f1) (f2, og) -> *)
        (*     let b, _,_ = pattern_matching_with_guard f1 f og args true in *)
        (*     if b then *)
        (*       (true, CF.mkStar cur_f1 f2 CF.Flow_combine no_pos) *)
        (*     else (cur_b, cur_f1) *)
        (* ) (false, f1) top_guard in *)
        (* if is_top then *)
        (*   do not inline *)
        (*   [(nf1, g1)] *)
        (* else *)
        let n_fs_wg = List.fold_left (fun r (f2, og2) ->
            let is_consis_guard1 =  is_guard_consistent f1 og2  in
            let is_consis_guard = if is_consis_guard1 then
              is_guard_consistent f2 og1
            else false in
            if is_consis_guard then
              let nf1 = compose_subs f1 f2 pos in
              let b, nf2, nog2 = pattern_matching_with_guard nf1 f og2 args true in
              if b then
                let nog2 = drop_dups_guards nf2 og2 in
                r@[(nf2, nog2)]
              else
                let nog1 = drop_dups_guards nf1 og1 in
                r@[(nf1,nog1)]
            else r
        ) [] ls_f_og in
        r1@n_fs_wg
    ) [] ls1
    in
    (* List.map (fun f2 ->
        let b, nf2 = pattern_matching_with_guard f2 f g_opt args in
        if b then nf2 else f2
    ) n_ls1
    *)
    n_ls1
  in
  let simplify_and_empty_test args (f,g)=
    let f1 = simplify_one_formula prog args f in
    (* let () = DD.info_zprint (lazy (("       f:" ^ (Cprinter.prtt_string_of_formula f)))) no_pos in *)
    (* let () = DD.info_zprint (lazy (("       f1:" ^ (Cprinter.prtt_string_of_formula f1)))) no_pos in *)
    let r =
      if is_empty_f f1 || is_unsat f then []
      else [(f1,g)]
    in
    r
  in
  let succ_hp_args = CF.get_HRels_f f in
  (*filter hp out*)
  let succ_hp_args = List.filter (fun (hp1,_) -> not (CP.eq_spec_var hp hp1) &&
      (CP.mem_svl hp1 all_succ_hp)) succ_hp_args in
  (* DD.info_pprint ("       succ_hp_args:" ^ (let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) *)
  (*                                           in pr succ_hp_args)) no_pos; *)
  match succ_hp_args with
    | [] ->
        (false, simplify_and_empty_test args (f,g))
    | _ -> begin
        let fs_list =  (List.map (fun (hp0,arg0) -> look_up_subst_hpdef link_hps hp0 arg0 nrec_hpdefs) succ_hp_args) in
        (* let r = (List.concat fs_list) in *)
        if fs_list = [] then
          (false, simplify_and_empty_test args (f,g))
        else
        (*create template from f*)
          let fs_list_w_top,fs_list_wo_top = List.partition (fun (_,_,ls) -> ls!= []) fs_list in
          let fs_list = fs_list_wo_top@fs_list_w_top in
          let nf,_ = CF.drop_hrel_f f (fst (List.split succ_hp_args)) in
        (*combine fs_list*)
          let lsf_cmb = List.fold_left helper [(nf,g)] fs_list in
          DD.ninfo_pprint ("       succ_susbt lsf_cmb:" ^ (let pr = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula
              (pr_option Cprinter.prtt_string_of_formula))
          in pr lsf_cmb)) no_pos;
          (*remove trivial def*)
          let lsf_cmb1 = List.filter (fun (f,_) -> not (is_trivial f (hp,args))) lsf_cmb in
          (*simpl pure*)
          let lsf_cmb2 = List.concat
            (List.map (fun (f,g) -> (simplify_and_empty_test args (f, g))) lsf_cmb1)
          in
        (*remove f which has common prefix*)
          (* let lsf_cmb3 = (remove_longer_common_prefix lsf_cmb2) in *)
          ((lsf_cmb2 <> []),lsf_cmb2)
    end

let succ_subst_hpdef prog link_hps (nrec_hpdefs: CF.hp_rel_def list) all_succ_hp (hp,args,g,f)=
  let pr1 = pr_list_ln (string_of_hp_rel_def) in
  let pr2 = !CP.print_svl in
  let pr3 = pr_quad !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula_opt Cprinter.prtt_string_of_formula in
  let pr4 = pr_pair string_of_bool (pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) ) in
  Debug.no_3 " succ_subst_hpdef" pr1 pr2 pr3 pr4
      (fun _ _ _ -> succ_subst_hpdef_x prog link_hps nrec_hpdefs all_succ_hp (hp,args,g,f))
      nrec_hpdefs all_succ_hp (hp,args,g,f)

let combine_hpdefs_x hpdefs=
  (*partition the set by hp_name*)
  let rec partition_hpdefs_by_hp_name defs parts=
    match defs with
      | [] -> parts
      | def1::xs -> begin
          let part,remains= List.partition (fun def2->
              let hp1 = CF.get_hpdef_name def1.CF.def_cat in
              let hp2 = CF.get_hpdef_name def2.CF.def_cat in
              CP.eq_spec_var hp1 hp2) xs
          in
          partition_hpdefs_by_hp_name remains (parts@([def1::part]))
        end
  in
  let extract_def args0 def=
    let _,args = CF.extract_HRel def.CF.def_lhs in
    let ss = List.combine args args0 in
    List.fold_left (fun fs (f,_) -> fs@(CF.list_of_disjs (CF.subst ss f))) [] def.CF.def_rhs
  in
  let combine_one_hpdef grp=
    match grp with
      | [] -> report_error no_pos "sau.combine_one_hpdef"
      | [def] -> def
      | def::tl ->
          let fs, ogs = List.split def.CF.def_rhs in
          let fs0 = List.fold_left (fun r f -> r@(CF.list_of_disjs f)) [] fs in
          let _,args0 = CF.extract_HRel def.CF.def_lhs in
          let fs = fs0@(List.concat (List.map (extract_def args0) tl)) in
          let fs1 = (remove_longer_common_prefix fs) in
          let fs2 = remove_subset fs1 in
          let p = (*(CF.pos_of_formula f0)*) no_pos in
          let f = List.fold_left (fun f1 f2 -> CF.mkOr_n f1 f2 p)
                      (List.hd fs2) (List.tl fs2)
          in
          {def with CF.def_rhs = [(f, CF.combine_guard ogs)]}
         (* (hp0,hprel0, og0, def) *)
  in
  let hpdefs1,tupled_defs = List.partition (fun def -> match def.CF.def_cat with
    | CP.HPRelDefn _ -> true
    | _ -> false
  ) hpdefs in
  let hp_groups = partition_hpdefs_by_hp_name hpdefs1 [] in
  let hpdefs2 = List.map combine_one_hpdef hp_groups in
  (hpdefs2@tupled_defs)

let combine_hpdefs hpdefs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_1 "combine_hpdefs" pr1 pr1
      (fun _ -> combine_hpdefs_x hpdefs) hpdefs

let is_top_guard_hp_def unk_hps hp_def=
  List.exists (fun (f,og) -> CF.is_top_guard f unk_hps og) hp_def.CF.def_rhs

let get_pre_fwd_x post_hps post_pdefs=
  let process_one_pdef cur_fwd_hps (hp, _, _,_,off,_, _)=
    match off with
      | Some f-> let hps = CF.get_hp_rel_name_formula f in
        (cur_fwd_hps@(CP.diff_svl hps (hp::post_hps)))
      | None -> cur_fwd_hps
  in
  let fwd_pre = List.fold_left process_one_pdef [] post_pdefs in
  (CP.remove_dups_svl fwd_pre)

let get_pre_fwd post_hps post_pdefs=
  let pr_f off= match off with
    | Some f -> Cprinter.prtt_string_of_formula f
    | None -> "None"
  in
  let pr0 (a, b, _,_, c,_,d) = (pr_quad !CP.print_sv !CP.print_svl pr_f pr_f) (a,b,c,d) in
  let pr1 = pr_list_ln pr0 in
  let pr2 = !CP.print_svl in
  Debug.no_2 "get_pre_fwd" pr2 pr1 pr2
      (fun _ _ -> get_pre_fwd_x post_hps post_pdefs)
      post_hps post_pdefs

let extract_fwd_pre_defs_x fwd_pre_hps defs=
  let get_pre_def (cur_grps,cur_hps) (* (def_kind,hf,og, def) *) def=
    match def.CF.def_cat with
      | CP.HPRelDefn (hp,_,_) ->
            (*do not subst rec*)
            if CP.mem_svl hp fwd_pre_hps && not (CP.mem_svl hp (List.fold_left (fun r f ->
                r@(CF.get_hp_rel_name_formula f)) [] (List.map fst def.CF.def_rhs))) then
              let _, args =  CF.extract_HRel def.CF.def_lhs in
              ((cur_grps@[(List.fold_left (fun r (f,og) ->
                  r@(List.map (fun f ->
                      (hp, args, og, f, []))
                          (CF.list_of_disjs f) ) )
                  [] def.CF.def_rhs)]), cur_hps@[hp])
            else (cur_grps,cur_hps)
      | _ -> (cur_grps,cur_hps)
  in
  if fwd_pre_hps = [] then ([],[]) else
    List.fold_left get_pre_def ([],[]) defs

let extract_fwd_pre_defs fwd_pre_hps defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln (pr_list_ln string_of_par_def_w_name_short) in
  Debug.no_2 "extract_fwd_pre_defs" !CP.print_svl pr1 (pr_pair pr2 !CP.print_svl)
      (fun _ _ -> extract_fwd_pre_defs_x fwd_pre_hps defs) fwd_pre_hps defs

(************************************************************)
    (****************END SUBST HP DEF*****************)
(************************************************************)

let recover_dropped_args drop_hp_args hp_defs=
  let helper hrel=
    match hrel with
      | CF.HRel (hp, eargs, p ) -> (hp, eargs, p )
      | _ -> report_error no_pos "SAU.recover_droped_args_x 1"
  in
  let recover_def drops def=
    let hpdef,hprel,hp_body = def in
    let hp1, eargs1, p = helper hprel in
    let rec helper2 ldrops r_drop=
      match ldrops with
        | [] -> r_drop,def
        | (hp, eargs, dropped_eargs)::ds ->
          if CP.eq_spec_var hp hp1 then
            let args = List.concat (List.map CP.afv dropped_eargs) in
            let args1 = List.concat (List.map CP.afv eargs1) in
            let ss = List.combine args args1 in
            let new_eargs = CP.e_apply_subs_list ss eargs in
            (r_drop@ds, (hpdef, (CF.HRel (hp1,new_eargs,p)),hp_body))
          else helper2 ds (r_drop@[(hp, eargs, dropped_eargs)])
    in
    helper2 drops []
  in
  let rec helper1 drops hpdefs res=
    match hpdefs with
      | [] -> res
      | def::ls ->
          let drops1,def1 = recover_def drops def in
          helper1 drops1 ls (res@[def1])
  in
  helper1 drop_hp_args hp_defs []

(* let recover_dropped_args drop_hp_args hp_defs= *)
(*   let pr0 = pr_list !CP.print_exp in *)
(*   let pr1 = pr_list (pr_triple !CP.print_sv pr0 pr0) in *)
(*   let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in *)
(*   Debug.no_2 "recover_dropped_args" pr1 pr2 pr2 *)
(*       (fun _ _ -> recover_dropped_args_x drop_hp_args hp_defs) drop_hp_args hp_defs *)

(************************************************************)
    (****************(*UNK HPS*)*****************)
(************************************************************)
let drop_non_node_unk_hps hp_defs ls_non_node_unk_hpargs =
  let drop_one_hpdef lnon_node_hp_names (rc, hf, f)=
    let f1,_ = CF.drop_hrel_f f lnon_node_hp_names in
    (rc, hf, f1)
  in
  let non_node_hp_names = List.map fst ls_non_node_unk_hpargs in
  List.map (drop_one_hpdef non_node_hp_names) hp_defs

(* let drop_non_node_unk_hps hp_defs non_node_unk_hps = *)
(*   let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in *)
(*   let pr2 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in *)
(*   Debug.no_2 "drop_non_node_unk_hps" pr1 pr2 pr1 *)
(*       (fun _ _ -> drop_non_node_unk_hps_x hp_defs non_node_unk_hps) hp_defs non_node_unk_hps *)

let generate_hp_def_from_unk_hps_x hpdefs unk_hpargs hp_defs post_hps gunk_rels=
  let mk_unkdef pos (hp,args)=
    let hp_name = dang_hp_default_prefix_name ^ "_" ^ CP.name_of_spec_var hp in
    let ps,fr_args =
      List.split (List.map (fun sv ->
          let fr_sv = CP.fresh_spec_var_prefix hp_name sv in
          (CP.mkPtrEqn sv fr_sv pos, fr_sv)
      ) args)
    in
    let p = CP.conj_of_list ps pos in
    let def = CF.formula_of_pure_formula p pos in
    let () = DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^
                                    (!CP.print_svl args) ^ ")=" ^
                                    (Cprinter.prtt_string_of_formula (* (CF.formula_of_heap h_def no_pos) *) def)) pos
    in
    let new_hpdef = CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, List.hd args, List.tl args))
      (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, pos)) [(def, None)] None in
    let new_unkmap = (hp,fr_args) in
    (new_hpdef,new_unkmap)
  in
  let generate_unk_hps_pre_post unk_hps_done unk_hpargs_all=
    let hps_done = (CP.remove_dups_svl unk_hps_done) in
    let rem = List.filter (fun (hp1,_) -> not (CP.mem_svl hp1 hps_done)) unk_hpargs_all  in
    List.split (List.map (mk_unkdef no_pos) rem)
  in
  let helper (hpdefs,unk_map) (hp, args)=
    let new_hpdefs,ls_new_unkmap =
      if (CP.mem_svl hp post_hps)then
        [],[]
      else
        let new_hpdef,new_unkmap = mk_unkdef no_pos (hp, args) in
        [new_hpdef],[new_unkmap]
    in
    (hpdefs@new_hpdefs,unk_map@ls_new_unkmap)
  in
  DD.ninfo_zprint (lazy (">>>>>> unknown hps: <<<<<<")) no_pos;
  (* let unk_hpargs,unk_with_rels = List.partition (fun (hp,_) -> not(CP.mem_svl hp hpdefs) )  unk_hpargs0 in *)
  let unk_hps = List.map fst unk_hpargs in
  (*classify unk_hpdefs and non-unk ones*)
  let ls_unk_rels,ls_rem_hpdefs,ls_unk_rel_hpdefs = split3 (List.map (fun (* (a, hrel, og, f) *) def ->
      let (hp,args) = CF.extract_HRel def.CF.def_lhs in
      if (CP.mem_svl hp unk_hps) (* && not(CP.mem_svl hp hpdefs) *) then
        let eq_hps = List.fold_left (fun r (f, _) -> r@(CF.get_hp_rel_name_formula f)) [] def.CF.def_rhs in
        let eq_hps =  CP.diff_svl eq_hps [hp] in
        (List.map (fun hp1 -> (hp,hp1,args)) eq_hps,[],
        [({def with CF.def_rhs = List.map (fun (f, og) -> (fst (CF.drop_hrel_f f unk_hps), og)) def.CF.def_rhs} )])
      else ([],[def],[])
  ) hp_defs)
  in
  let unk_rels3 = List.concat ls_unk_rels in
  let unk_rels2 = List.map (fun (a,b,c) -> (a,b)) unk_rels3 in
  let unk_hps1 = find_close_hpargs unk_hpargs unk_rels2 in
  (*generate def for unk in precondition*)
  let unk_hpdefs, unk_map = List.fold_left helper ([],[]) unk_hps1 in
  (* let unk_hps_done1,unk_hpdefs_from_rel = rel_helper unk_rels3 unk_map in *)
  let unk_hps_done1 = List.map fst unk_rels2 in
  let unk_hps_done2 = List.map fst unk_map in
  let rem_unkdefs,rem_map = generate_unk_hps_pre_post (unk_hps_done1@unk_hps_done2) unk_hpargs in
  (* let all_unk_hpdefs = SAU.combine_hpdefs (unk_hpdefs_from_rel@unk_hpdefs@rem_unkdefs) in *)
  let all_unk_hpdefs = combine_hpdefs (unk_hpdefs@rem_unkdefs) in
  let rem_hpdefs = List.concat ls_rem_hpdefs in
  (rem_hpdefs,List.concat ls_unk_rel_hpdefs,all_unk_hpdefs,unk_map@rem_map,unk_rels3)

(*old sa: to remove*)
let generate_hp_def_from_unk_hps hpdefs unk_hps hp_defs post_hps unk_rels=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 (a,b,c,d,_) = let pr = pr_quad pr1 pr1 pr1 pr2 in pr (a,b,c,d) in
  (* let pr5 = pr_list CP.string_of_xpure_view in *)
  Debug.no_3 "generate_hp_def_from_unk_hps" pr2 pr1 pr4 pr3
      (fun _ _ _ -> generate_hp_def_from_unk_hps_x hpdefs unk_hps hp_defs post_hps unk_rels) unk_hps hp_defs unk_rels

(*old sa: to remove*)
let transform_unk_hps_to_pure_x hp_defs unk_hp_frargs =
  (* let transform_hp_unk (hp,args)= *)
  (*   let hp_name = CP.name_of_spec_var hp in *)
  (*   let fr_args = List.map (fun sv -> CP.fresh_spec_var_prefix hp_name sv) args in *)
  (*   (hp,fr_args) *)
  (* in *)
  let rec lookup_hpdefs rem_hpdefs (hp0,args0)=
    match rem_hpdefs with
      | [] -> report_error no_pos "sau.lookup_hpdefs"
      | (_,hrel,_,f)::tl->
          let hp,args = CF.extract_HRel hrel in
          if CP.eq_spec_var hp hp0 then
            let ss = List.combine args args0 in
            CP.subst ss (CF.extract_pure f)
          else lookup_hpdefs tl (hp0,args0)
  in
  let subst_xpure lhpdefs xp_hpargs f0=
    let process_p_helper p=
      let xp_ps = (List.map (lookup_hpdefs lhpdefs) xp_hpargs) in
      (* let filtered_xp_ps = CP.filter_disj xp_ps rem_ps in *)
      let new_p = CP.conj_of_list (CP.remove_redundant_helper ((CP.list_of_conjs p)@ xp_ps) []) no_pos in
      new_p
    in
    let rec helper f=
      match f with
        | CF.Base fb ->
            let new_p =  process_p_helper (MCP.pure_of_mix fb.CF.formula_base_pure) in
            CF.Base{fb with CF.formula_base_pure = (MCP.mix_of_pure new_p)}
        | CF.Exists fe ->
            let new_p =  process_p_helper (MCP.pure_of_mix fe.CF.formula_exists_pure) in
            CF.Exists{fe with CF.formula_exists_pure = (MCP.mix_of_pure new_p)}
        | CF.Or orf -> CF.Or {orf with
            CF.formula_or_f1 = helper orf.CF.formula_or_f1;
            CF.formula_or_f2 = helper orf.CF.formula_or_f2;
        }
    in
    helper f0
  in
  let look_up_get_eqs_ss args0 ls_unk_hpargs_fr (used_hp,used_args)=
    try
        let _,fr_args = List.find (fun (hp,_) -> CP.eq_spec_var hp used_hp) ls_unk_hpargs_fr in
        let ss = List.combine used_args fr_args in
        let rs1,rs2 = List.partition (fun (sv1,_) -> CP.mem_svl sv1 args0) ss in
        if List.length rs1 = List.length args0 then
          ([used_hp],[([(used_hp,used_args)],[])],rs2)
        else
          ([used_hp],[([],rs1)],rs2)
    with
      | Not_found -> ([],[],[])
  in
  let subst_pure_hp_unk args0 ls_unk_hpargs_fr f=
    (* let () = DD.info_zprint (lazy (("       f: " ^ (!CF.print_formula f)))) no_pos in *)
    let ls_used_hp_args = CF.get_HRels_f f in
    let ls_xpures =  CF.get_xpure_view f in
    (* let ls_used_hp_args0 = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) (ls_used_hp_args@ls_xpures) in *)
    (*look up*)
    let r1 = List.map (look_up_get_eqs_ss args0 ls_unk_hpargs_fr) ls_used_hp_args in
    let r2 = List.map (look_up_get_eqs_ss args0 ls_unk_hpargs_fr) ls_xpures in
    let ls_used_unk_hps,ls_eqs, ls_ss = split3 (r1@r2) in
    let used_unk_hps = List.concat ls_used_unk_hps in
    let unk_need_subst, eqs = List.fold_left (fun (ls1,ls2) (a1,a2) -> (ls1@a1,ls2@a2)) ([],[]) (List.concat ls_eqs) in
    (* let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
    (* let () = DD.info_zprint (lazy (("       eqs: " ^ (pr1 eqs)))) no_pos in *)
    let ss = List.concat ls_ss in
    (*remove unkhps*)
    let f1,_ =  CF.drop_unk_hrel (* CF.drop_hrel_f*) f used_unk_hps in
    (*subst*)
    let f2 = CF.subst ss f1 in
    (*add pure eqs*)
    let pos = CF.pos_of_formula f2 in
    let p_eqs = List.map (fun (sv1,sv2) -> CP.mkPtrEqn sv1 sv2 pos) eqs in
    let p = CP.conj_of_list (CP.remove_redundant_helper p_eqs []) pos in
    let f3 = CF.mkAnd_pure f2 (MCP.mix_of_pure p) pos in
    (f3, unk_need_subst)
  in
  let subst_pure_hp_unk_hpdef ls_unk_hpargs_fr (* (rc, hf,og, def) *) def=
    let hp,args0 = CF.extract_HRel def.CF.def_lhs in
    (* let () = DD.info_zprint (lazy (("       hp: " ^ (!CP.print_sv hp)))) no_pos in *)
    let fs, ogs = List.split def.CF.def_rhs in
    let fs1 = List.map (subst_pure_hp_unk args0 ls_unk_hpargs_fr) fs in
    let def1 = CF.disj_of_list (fst (List.split fs1)) no_pos in
    (def.CF.def_cat, def.CF.def_lhs , CF.combine_guard ogs, def1, fs1)
  in
  let subst_and_combine new_hpdefs pr_fs=
    let fs = List.map (fun (f, xp_args) ->
        if xp_args = [] then f else
        subst_xpure new_hpdefs xp_args f
    ) pr_fs
    in
    CF.disj_of_list fs no_pos
  in
  let ls_unk_hpargs_fr = unk_hp_frargs in
  (* let ls_unk_hpargs_fr = List.map transform_hp_unk unk_hpargs in *)
  let new_hpdefs = List.map (subst_pure_hp_unk_hpdef ls_unk_hpargs_fr) hp_defs in
  let new_hpdefs1 = List.map (fun (a,b,g,f,_) -> (a,b,g, f)) new_hpdefs in
  let new_hpdefs2 = List.map (fun (a,b,g,_,pr_f) -> (a,b,g, pr_f)) new_hpdefs in
  (*subst XPURE*)
  List.map (fun (a,b,g,pr_f) -> CF.mk_hp_rel_def1 a b [(subst_and_combine (*subst_xpure*) new_hpdefs1 pr_f,g)] None) new_hpdefs2

let transform_unk_hps_to_pure hp_defs unk_hpargs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_2 "transform_unk_hps_to_pure" pr1 pr2 pr1
      (fun _ _ -> transform_unk_hps_to_pure_x hp_defs unk_hpargs) hp_defs unk_hpargs

(*old sa: to remove*)
let rel_helper post_hps unk_rels unk_map=
  let generate_p_formual args pos fr_args=
    let ss = List.combine args fr_args in
    let ps = List.map (fun (sv1,sv2) -> CP.mkPtrEqn sv1 sv2 pos) ss in
    CF.formula_of_pure_formula (CP.conj_of_list ps pos) pos
  in
  let mk_def (hp,args,ls_fr_args)=
    let fs = List.map (generate_p_formual args no_pos) ls_fr_args in
    let def = CF.disj_of_list fs no_pos in
    (CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, List.hd args, List.tl args))
        (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args,no_pos)) [(def,None)] None)
  in
  let rec list_lookup_map hp0 ls=
    match ls with
      | [] -> []
      | (hp1,ls_frargs)::tl -> if CP.eq_spec_var hp0 hp1 then ls_frargs
          else list_lookup_map hp0 tl
  in
  let rec list_lookup hp0 ls=
    match ls with
      | [] -> []
      | (hp1,_,ls_frargs)::tl -> if CP.eq_spec_var hp0 hp1 then ls_frargs
          else list_lookup hp0 tl
  in
  let rec list_update hp0 args0 ls_frargs ls ls_done=
    match ls with
      | [] -> ls_done@[(hp0,args0,ls_frargs)]
      | (hp1,args1,ls_frargs1)::tl ->
          if CP.eq_spec_var hp0 hp1 then
            let diff = Gen.BList.difference_eq eq_spec_var_order_list ls_frargs ls_frargs1 in
            ls_done@[(hp1,args1,ls_frargs1@diff)]@tl
          else
            list_update hp0 args0 ls_frargs tl (ls_done@[(hp1,args1,ls_frargs1)])
  in
  let rec subst_helper unk_rels unk_tmp_hpdefs=
    match unk_rels with
      | [] -> unk_tmp_hpdefs
      | (hp1,hp2,args)::tl ->
          let fr_args =
            let fr_args = list_lookup_map hp2 unk_map in
            if fr_args <> [] then [fr_args]
            else list_lookup hp2 unk_tmp_hpdefs
          in
          let new_unk_tmp_hpdefs = list_update hp1 args fr_args unk_tmp_hpdefs [] in
          subst_helper tl new_unk_tmp_hpdefs
  in
  let unk_tmp_hpdefs =  subst_helper unk_rels [] in
  (List.map mk_def unk_tmp_hpdefs)

let is_tupled_hpdef def=
  match def.CF.def_cat with
    | CP.HPRelLDefn hps -> true
    | _ -> false

let partition_tupled_x hpdefs=
  let get_tupled_hps res def=
    match def.CF.def_cat with
    | CP.HPRelLDefn hps -> res@hps
    | _ -> res
  in
  let is_dep_tupled tupled_hps def=
    let fs = List.map fst def.CF.def_rhs in
    let hps = List.fold_left (fun r f -> r@(CF.get_hp_rel_name_formula f)) [] fs in
    CP.intersect_svl hps tupled_hps <> []
  in
  let hpdefs1,tupled_defs = List.partition (fun def -> match def.CF.def_cat with
    | CP.HPRelDefn _ -> true
    | _ -> false
  ) hpdefs
  in
  let tupled_hps = List.fold_left get_tupled_hps [] tupled_defs in
  let hpdefs_tupled_dep,hpdefs2 = List.partition (is_dep_tupled tupled_hps) hpdefs1 in
  (hpdefs2,tupled_defs@hpdefs_tupled_dep)

let partition_tupled hpdefs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_1 "partition_tupled" pr1 (pr_pair pr1 pr1)
      (fun _ -> partition_tupled_x hpdefs) hpdefs

(************************************************************)
    (****************(*END UNK HPS*)*****************)
(************************************************************)

let split_rhs_x prog cs=
  let simpily_lhs_rhs cs rhs_grp_hpargs hd_nodes hv_nodes eqs lhs_hpargs lhs rhs=
    let rhs_hps,rhs_keep_svl = List.split rhs_grp_hpargs in
    let n_lhs,n_rhs= keep_data_view_hrel_nodes_two_f prog lhs rhs hd_nodes hv_nodes eqs lhs_hpargs (List.concat rhs_keep_svl) rhs_hps in
    {cs with CF.hprel_lhs = n_lhs;
        CF.hprel_rhs = n_rhs
    }
  in
  let belong_one_node lsargs args0 args1=
    let args1 = CP.remove_dups_svl (args0@args1) in
    List.exists (fun args -> CP.diff_svl args1 args = []) lsargs
  in
  let rec partition_intersect_hpargs ls_node_args hpargs parts=
    match hpargs with
      | [] -> parts
      | (hp,args0)::tl->
           let part,remains= List.partition (fun (_,args1) ->
               CP.intersect_svl args0 args1 <> [] ||
           belong_one_node ls_node_args args0 args1) tl in
          partition_intersect_hpargs ls_node_args remains (parts@[[(hp,args0)]@part])
  in
  if List.length cs.CF.unk_hps > 0 then [cs]
  else
    let rhs_hpargs = CF.get_HRels_f cs.CF.hprel_rhs in
    match rhs_hpargs with
      | [] -> [cs]
      | [a] -> [cs]
      | _ ->
           let lhs = cs.CF.hprel_lhs in
           let rhs = cs.CF.hprel_rhs in
           let ldns,lvns,lhrels = CF.get_hp_rel_formula lhs in
           let rdns,rvns,_ = CF.get_hp_rel_formula rhs in
           let hns = ldns@rdns in
           let hvs = lvns@rvns in
          let grps = partition_intersect_hpargs (List.map (fun hd -> hd.CF.h_formula_data_arguments) hns) rhs_hpargs [] in
          if List.length grps <= 1 then [cs] else
            let lhs_hpargs = List.map (fun (hp, eargs,_) -> (hp,(List.fold_left List.append [] (List.map CP.afv eargs)))) lhrels in
            let ( _,mix_lf,_,_,_,_) = CF.split_components cs.CF.hprel_lhs in
            let (_,mix_rf,_,_,_,_) = CF.split_components cs.CF.hprel_rhs in
            let leqs = MCP.ptr_equations_without_null mix_lf in
            let reqs = MCP.ptr_equations_without_null mix_rf  in
            let eqs = leqs@reqs in
            List.map (fun rhs_hpargs -> simpily_lhs_rhs cs rhs_hpargs hns hvs eqs lhs_hpargs lhs rhs) grps

let split_rhs prog cs=
  let pr1 = Cprinter.string_of_hprel in
  Debug.no_1 "split_rhs" pr1 (pr_list_ln pr1)
      (fun _ -> split_rhs_x prog cs) cs

(*like tree recursion PLDI07*)
let simp_tree_one_hp_x unk_hps hp args fs=
  let is_rec_f f=
    let hps = CF.get_hp_rel_name_formula f in
    (CP.mem_svl hp hps)
  in
  let is_independ_f f =
    let hps = CF.get_hp_rel_name_formula f in
    let hps1 = CP.remove_dups_svl hps in
    (* DD.ninfo_zprint (lazy (("       hp: " ^ (!CP.print_sv hp)))) no_pos; *)
    let rems = List.filter (fun hp1 -> not(CP.eq_spec_var hp hp1)
    && not (CP.mem_svl hp1 unk_hps) ) hps1 in
    (* DD.ninfo_zprint (lazy (("       rems: " ^ (!CP.print_svl rems)))) no_pos; *)
    (rems = [])
  in
  let sort_fn (_,hds1) (_,hds2)=
    (List.length hds1)-(List.length hds2)
  in
  let rec check_exist f ls_f=
    match ls_f with
      | [] -> false
      | f1::tl_fs ->
           let r,_ (*map*) = CEQ.checkeq_formulas [] f f1 in
          if (* check_relaxeq_formula f f1 *) r then true else
            check_exist f tl_fs
  in
  let rec find_prec_point r (f,hds) rec_args done_fs done_hds=
    match hds with
      | [] -> f
      | hd::tl -> if CP.eq_spec_var hd.CF.h_formula_data_node r then
            let nf = CF.drop_hnodes_f f [r] in
            let n_roots = List.filter CP.is_node_typ hd.CF.h_formula_data_arguments in
            let rec_nrs,non_rec_nrs = List.partition (fun arg ->
                CP.mem_svl arg rec_args ) n_roots in
            if non_rec_nrs = [] then f else
              let nf1 = List.fold_left
                (fun f0 a -> drop_hrel_match_args f0 [a]) nf rec_nrs
              in
              let () = DD.ninfo_zprint (lazy (("non_rec_nrs: " ^ (!CP.print_svl non_rec_nrs) ))) no_pos in
              let nf2,a =
                match non_rec_nrs with
                  | [a] -> (find_prec_point a (nf1,done_hds@tl) rec_args done_fs
                      [],a)
                  | _ -> report_error no_pos "sau.find_prec_point"
              in
              let () = DD.ninfo_zprint (lazy ((" nf2: " ^ (Cprinter.prtt_string_of_formula nf2) ))) no_pos in
              let ss2 = List.combine [a] args in
              let nf2a = CF.subst ss2 nf2 in
              if check_exist nf2a done_fs then
                let hf4 = mkHRel hp [a] no_pos in
                let nf3 = drop_data_hrel_except [r] rec_nrs f in
                CF.mkAnd_f_hf nf3 hf4 no_pos
              else f
          else
            find_prec_point r (f,tl) rec_args done_fs (done_hds@[hd])
  in
  let process_one_rec_f args (f,hsa) done_fs=
    let () = DD.ninfo_zprint (lazy ((" f: " ^ (Cprinter.prtt_string_of_formula f) ))) no_pos in
    if check_exist f done_fs then [] else
      let hpargs = CF.get_HRels_f f in
      let rec_args = List.fold_left
        (fun args0 (hp1,args) -> if CP.eq_spec_var hp1 hp then (args0@args) else args0) [] hpargs in
      let newf=
        match args with
          | [a] -> find_prec_point a (f, hsa) rec_args done_fs []
          | _ -> report_error no_pos "sau. process_one_rec_f"
      in
      let () = DD.ninfo_zprint (lazy ((" newf: " ^ (Cprinter.prtt_string_of_formula newf) ))) no_pos in
      if check_exist newf done_fs then done_fs else (done_fs@[newf])
  in
  (*find base case*)
   let _, dep_fs = List.partition is_independ_f fs in
  if (List.length dep_fs >= 1) || (List.length args > 1) then fs else
    let rec_fs,base_fs= List.partition is_rec_f fs in
    (*sort all based on length of heaps*)
    let rec_ls_hds = List.map (fun f -> (f,get_hdnodes f)) rec_fs in
    let rec_ls_hds1 = List.sort sort_fn rec_ls_hds in
  (*for each of remain: find the next root, if it exists in base case, subst to become recursive one*)
    let fs1 = List.fold_left (fun done_fs (f,hds) -> process_one_rec_f args (f,hds) done_fs) base_fs rec_ls_hds1 in
    (* let fs2 = norm_hnodes args fs1 in *) fs1
    (* Gen.BList.remove_dups_eq check_relaxeq_formula fs2 *)

let simp_tree_one_hp unk_hps hp args fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_3 "simp_tree_one_hp" !CP.print_sv !CP.print_svl pr1 pr1
      (fun _ _ _ -> simp_tree_one_hp_x unk_hps hp args fs) hp args fs

(*old sa*)
let simp_tree_x unk_hps hpdefs=
  let process_one_hp (* (a,hprel,og,f) *)def=
    let hp,args = CF.extract_HRel def.CF.def_lhs in
    let fs,ogs = List.split def.CF.def_rhs in
    let nfs = simp_tree_one_hp unk_hps hp args fs in
    let nf = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 no_pos)
      (List.hd nfs) (List.tl nfs) in
    {def with CF.def_rhs = [(nf, CF.combine_guard ogs)]}
  in
  List.map process_one_hp hpdefs

let simp_tree unk_hps hpdefs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def_short in
  Debug.no_1 "simp_tree" pr1 pr1
      (fun _ -> simp_tree_x unk_hps hpdefs) hpdefs

(************************************************************)
    (****************(*MATCHING w view decls*)*****************)
(************************************************************)
(*syntactically equivalence checking*)
let match_one_hp_one_view_x iprog prog hp hp_name args def_fs (vdcl: C.view_decl): bool=
  let v_fl,_ = List.split vdcl.C.view_un_struc_formula in
  (*get root*)
  let (CP.SpecVar (t,_,_)) = List.hd args in
  (*assume self is always unprimed*)
  let v_args = [CP.SpecVar (t,self,Unprimed)]@vdcl.C.view_vars in
  let ss = List.combine (args) (v_args) in
  let def_fs1 = List.map (CF.subst ss) def_fs in
  let v_fl1 = List.map CF.elim_exists v_fl in
  if (List.length def_fs) = (List.length v_fl) then
    let v_fl2 =
      if vdcl.C.view_is_rec then
        List.map (subst_view_hp_formula vdcl.C.view_name hp) v_fl1
      else v_fl1
    in
    (*for debugging*)
    (* let pr = pr_list_ln Cprinter.prtt_string_of_formula in *)
    (* let () = Debug.info_zprint (lazy (("     def_fs: " ^ (pr def_fs)))) no_pos in *)
    (* let () = Debug.info_zprint (lazy (("     def_fs1: " ^ (pr def_fs1)))) no_pos in *)
    (* let () = Debug.info_zprint (lazy (("     v_fl1: " ^ (pr v_fl1)))) no_pos in *)
    (*END for debugging*)
    checkeq_formula_list def_fs1 v_fl2
  else
    false

let match_one_hp_one_view iprog prog hp hp_name args def_fs (vdcl: C.view_decl):bool=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  let pr2 = Cprinter.string_of_view_decl in
  Debug.no_2 "match_one_hp_one_view" pr1 pr2 string_of_bool
      (fun _ _ -> match_one_hp_one_view_x iprog prog hp hp_name args def_fs vdcl) def_fs vdcl

let match_one_hp_views iprog prog cur_m (vdcls: C.view_decl list) def:(CP.spec_var* CF.h_formula list)=
  let hf = def.CF.def_lhs in
  let orf = CF.disj_of_list (List.map fst def.CF.def_rhs) no_pos in
  match hf with
    | CF.HRel (hp, eargs, p) ->
        let def_fl = CF.list_of_disjs orf in
        let args = List.concat (List.map CP.afv eargs) in
        let helper vdcl=
          if (List.length args) = ((List.length vdcl.C.view_vars) + 1) then
            if (match_one_hp_one_view iprog prog (hp, eargs, p) hp args def_fl vdcl) then
              let vnode = CF.mkViewNode (List.hd args) vdcl.C.view_name
                (List.tl args) no_pos in
              [vnode]
            else []
          else []
        in
        let eq_views = List.concat (List.map helper vdcls) in
        (hp,eq_views)
    | _ -> report_error no_pos "sau.match_one_hp_views: should be a hp"


(************************************************************)
    (****************(*END MATCHING w view decls*)*****************)
(************************************************************)


(************************************************************)
    (****************(*currently we dont use*)*****************)
(************************************************************)
(*currently we dont use*)
let ann_unk_svl prog par_defs=
  (*partition the set by hp_name*)
  let rec partition_pdefs_by_hp_name pdefs parts=
    match pdefs with
      | [] -> parts
      | (a1,a2,a3,a4,a5,a6)::xs ->
          let part,remains= List.partition (fun (hp_name,_,_,_,_,_) -> CP.eq_spec_var a1 hp_name) xs in
          partition_pdefs_by_hp_name remains (parts@[[(a1,a2,a3,a4,a5,a6)]@part])
  in
  let add_unk_hp_f unk_hf opdef=
    match opdef with
      | None -> None
      | Some f ->
          let p = CF.pos_of_formula f in
          Some (CF.mkAnd_f_hf f unk_hf p)
  in
  let add_unk_hp_pdef unk_hf0 unk_args0 (hp,args,unk_args,cond,olhs,orhs)=
    let ss = List.combine unk_args0 unk_args in
    let unk_hf = CF.h_subst ss unk_hf0 in
    (hp,args,unk_args,cond,add_unk_hp_f unk_hf olhs, add_unk_hp_f unk_hf orhs)
  in
  let process_one_group par_defs=
    let (hp,args0,unk_args0,cond0,olhs0,orhs0) = List.hd par_defs in
    let () = Debug.ninfo_zprint (lazy (("     partial unk hp: " ^ (!CP.print_sv hp)))) no_pos in
    let unk_args0_w_inst = List.map (fun sv -> (sv, NI)) unk_args0 in
    let is_pre = Cast.check_pre_post_hp prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
    let unk_hf, unk_hps = add_raw_hp_rel prog is_pre true unk_args0_w_inst no_pos in
    let new_par_def0= (hp,args0,unk_args0,cond0,add_unk_hp_f unk_hf olhs0, add_unk_hp_f unk_hf orhs0) in
    let tl_par_defs = List.map (add_unk_hp_pdef unk_hf unk_args0) (List.tl par_defs) in
    ((unk_hps,unk_args0), new_par_def0::tl_par_defs)
  in
  let par_unk_defs,rems = List.partition (fun (_,_,unk_slv,_,_,_) -> unk_slv <> []) par_defs in
  let parunk_groups = partition_pdefs_by_hp_name par_unk_defs [] in
  let r = List.map process_one_group parunk_groups in
  let new_hpargs,new_unk_pardefs = List.split r in
  (new_hpargs, (List.concat new_unk_pardefs)@rems)

(*END currently we dont use*)
(************************************************************)
    (****************(*ENDcurrently we dont use*)*****************)
(************************************************************)

(*SLEEK*)
let get_pre_post_x pre_hps post_hps constrs=
  let get_hps all_hps ass = match ass.CF.hprel_kind with
    | CP.RelAssume hps ->
          let body_hps = (CF.get_hp_rel_name_formula ass.CF.hprel_lhs)@
            ( CF.get_hp_rel_name_formula ass.CF.hprel_rhs) in
          all_hps@hps@body_hps
    | _ -> all_hps
  in
  let filter_hp id_ls all_hps =List.filter (fun hp ->
      let hp_name = CP.name_of_spec_var hp in
      List.exists (fun id -> String.compare hp_name id = 0) id_ls
      ) all_hps in
  let hps2 = List.fold_left get_hps [] constrs in
  let hps20 = CP.remove_dups_svl hps2 in
  let sel_pre_hps = filter_hp pre_hps hps20 in
  let sel_post_hps = filter_hp post_hps hps20 in
  let sel_hps = sel_pre_hps@sel_post_hps in
  (sel_hps, sel_post_hps)

let get_pre_post pre_hps post_hps constrs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln Cprinter.string_of_hprel_short in
  Debug.no_1 "get_pre_post" pr2 (pr_pair pr1 pr1)
      (fun _ -> get_pre_post_x pre_hps post_hps constrs) constrs

(*SLEEK*)
(*=============**************************================*)
       (*=============COND PATH================*)
(*=============**************************================*)
let rec cmp_list_int ls1 ls2=
  match ls1,ls2 with
    | [],[] -> true
    | i1::rest1, i2::rest2 -> if i1=i2 then cmp_list_int rest1 rest2
      else false
    | _ -> false

let cmp_list_subsume_int_rev_x ls10 ls20=
  let rec helper ls1 ls2=
    match ls1,ls2 with
      | [],[] -> true
      | _, [] -> true
      | i1::rest1, i2::rest2 -> if i1=i2 then helper rest1 rest2
        else false
      | _ -> false
  in
  helper (List.rev ls10) (List.rev ls20)

let cmp_list_subsume_int_rev ls10 ls20=
  let pr1 = pr_list string_of_int in
  Debug.no_2 "cmp_list_subsume_int_rev" pr1 pr1 string_of_bool
      (fun _ _ -> cmp_list_subsume_int_rev_x ls10 ls20)
      ls10 ls20

let rec partition_helper pr_cond_hpargs grps=
  match pr_cond_hpargs with
    | [] -> grps
    | (cond1,hpargs1)::rest->
          let grp, rest1 = List.partition (fun (cond2, _) ->
              cmp_list_int cond1 cond2
          ) rest in
          let n_grps = grps@[(cond1,hpargs1::(List.map snd grp))] in
          partition_helper rest1 n_grps

let dang_partition pr_cond_hpargs0 =
  partition_helper pr_cond_hpargs0 []

let defn_partition pr_cond_defs=
  partition_helper pr_cond_defs []

let assumption_partition_x constrs0=
  (*********************************)
  (*        INTERNAL               *)
  (*********************************)
  let cmp_path_cs (path1, _,_) (path2, _,_) = (List.length path2) - (List.length path1) in
  let rec partition_helper constrs grps=
    match constrs with
      | [] -> grps
      | cs::rest->
            let grp, rest1 = List.partition (fun cs2 ->
                cmp_list_int cs.CF.hprel_path cs2.CF.hprel_path
            ) rest in
            let n_grps = grps@[(cs.CF.hprel_path,cs::grp, false)] in
            partition_helper rest1 n_grps
  in
  (*grps are sorted based on their path length*)
  let rec insert_subsumed rem_grps res=
    match rem_grps with
      | []-> res
      | (p1, grp1, is1)::rest ->
            let subsumed_constrs, n_rest = List.fold_left (fun (ls1,ls2) (p2, grp2, is2) ->
                if cmp_list_subsume_int_rev p1 p2 then
                  (ls1@grp2, ls2@[(p2, grp2, true)])
                else (ls1, ls2@[(p2, grp2, is2)])
            ) ([],[]) rest
            in
            insert_subsumed n_rest (res@[(p1, grp1@subsumed_constrs, is1)])
  in
  (*********************************)
  (*       END INTERNAL            *)
  (*********************************)
  (*group: path, constrs, is_subsumed (default: false) *)
  let grps = partition_helper constrs0 [] in
  (*sort (>) base on length of cond_path*)
  let grps1 = List.sort cmp_path_cs grps in
  (*insert grps that are subsumed.*)
  let grps2 = insert_subsumed grps1 [] in
  (*RETRUN: if one group is subsumed, it will not returned*)
  List.fold_left (fun ls (a,b,is)-> if not is then ls@[(a,b)] else ls) [] grps2
   (* List.map (fun (a,b,is)-> (a,b)) grps2 *)

let assumption_partition constrs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = CF.string_of_cond_path in
  let pr3 = pr_list_ln (pr_pair pr2 pr1) in
  Debug.no_1 "assumption_partition" pr1 pr3
      (fun _ -> assumption_partition_x constrs)
      constrs

let pair_dang_constr_path_x ls_constr_path ls_dang_path=
  let rec look_up ls p=
    match ls with
      | [] -> []
      | (p1, ls_hpargs)::rest -> if cmp_list_int p p1 then ls_hpargs
        else look_up rest p
  in
  let r = List.map (fun (p1, constrs) -> (p1, look_up ls_dang_path p1, constrs)
  ) ls_constr_path in
  r

let pair_dang_constr_path ls_constr_path ls_dang_path pr1=
  (* let pr1 = pr_list_ln Cprinter.string_of_hprel_short in *)
  (* let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def_short in *)
  let pr2 = CF.string_of_cond_path in
  let pr3 = pr_list_ln (pr_pair pr2 pr1) in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr5 = pr_list_ln (pr_pair pr2 pr4) in
  let pr6 = pr_list_ln (pr_triple pr2 pr4 pr1) in
  Debug.no_2 "pair_dang_constr_path" pr3 pr5 pr6
      (fun _ _ -> pair_dang_constr_path_x ls_constr_path ls_dang_path)
      ls_constr_path ls_dang_path

(*=============**************************================*)
       (*=============END COND PATH================*)
(*=============**************************================*)
let find_closed_sel_hp_def_x defs sel_hps dang_hps equivs=
  let look_up_depend cur_hp_sel fs=
    let hps = List.fold_left (fun r f -> r@(CF.get_hp_rel_name_formula f)) [] fs in
    let dep_hps =CP.diff_svl hps (cur_hp_sel) in
    (CP.remove_dups_svl dep_hps)
  in
  let look_up_hp_def new_sel_hps non_sel_hp_def=
    List.partition (fun (hp,_) -> CP.mem_svl hp new_sel_hps) non_sel_hp_def
  in
  let rec find_closed_sel cur_sel cur_sel_hpdef non_sel_hp_def incr=
    let rec helper1 ls res=
      match ls with
        | [] -> res
        | (hp,def)::lss ->
            let incr =
              if CP.mem_svl hp (cur_sel) then
                []
              else
                [hp]
            in
            let new_hp_dep = look_up_depend cur_sel (List.map fst def.CF.def_rhs) in
            helper1 lss (CP.remove_dups_svl (res@incr@new_hp_dep))
    in
    let incr_sel_hps = helper1 incr [] in
    (*nothing new*)
    if incr_sel_hps = [] then cur_sel_hpdef else
      let incr_sel_hp_def,remain_hp_defs = look_up_hp_def incr_sel_hps non_sel_hp_def in
      find_closed_sel (cur_sel@incr_sel_hps) (cur_sel_hpdef@incr_sel_hp_def) remain_hp_defs incr_sel_hp_def
  in
  (**********END INTERNAL********************)
  let defsw = List.map (fun def ->
      (List.hd (CF.get_hp_rel_name_h_formula def.CF.def_lhs), def)) defs in
  let sel_defw,remain_hp_defs = List.partition (fun (hp,_) -> CP.mem_svl hp sel_hps) defsw in
  let closed_sel_defw = find_closed_sel sel_hps sel_defw remain_hp_defs sel_defw in
  List.split closed_sel_defw

let find_closed_sel_hp_def defs sel_hps dang_hps equivs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = !CP.print_svl in
  let pr4 = pr_pair pr2 pr1 in
  Debug.no_2 "find_closed_sel_hp_def" pr1 pr2 pr4
      (fun _ _ -> find_closed_sel_hp_def_x defs sel_hps dang_hps equivs) defs sel_hps

let combine_path_defs_x sel_hps1 path_defs iflow=
  let rec look_up rem hp=
    match rem with
      | [] -> []
      | hpd::rest ->
            let hp1,args = CF.extract_HRel hpd.CF.hprel_def_hrel in
            if CP.eq_spec_var hp hp1 then
              [ (hpd.CF.hprel_def_kind, args, hpd.CF.hprel_def_guard, hpd.CF.hprel_def_body,
              hpd.CF.hprel_def_body_lib)]
            else look_up rest hp
  in
  let combine_path args0 args1 old_paths paths1 old_lib lib1=
    let ss = List.combine args1 args0 in
    let n_path (path1, ofs1, oflow) = (path1, (match ofs1 with
      | None -> None
      | Some f -> Some (CF.subst ss f))
    , oflow)
    in
    let n_lib = (* match old_lib, lib1 with *)
      (* | Some f1, Some f2 -> Some (CF.mkOr f1 f2 no_pos) *)
      (* | _ -> None *)
      old_lib@lib1
    in
    (old_paths@(List.map n_path paths1), n_lib)
  in
  let rec norm rem_path args0 paths lib=
    match rem_path with
      | [] -> (paths, lib)
      | (_, args1, g, path_fs1, lib1)::rest ->
            let n_paths, n_lib = combine_path args0 args1 paths path_fs1 lib lib1 in
            norm rest args0 n_paths n_lib
  in
  let rec combine_one_def hp=
    let settings= List.fold_left (fun ls path ->
        let res = look_up path hp in
        ls@res
    ) [] path_defs
    in
    match settings with
      | [] -> []
      | (k, args0, g, path_fs0, lib0)::rest ->
            let path_fs, lib = norm rest args0 path_fs0 lib0 in
            let path_fs1 = List.map (fun (a,b,_) -> (a,b)) path_fs in
            let lib1 = match lib with
              | [] -> None
              | (f0,_)::rest -> Some (List.fold_left (fun f1 (f2,_) -> CF.mkOr f1 f2 no_pos) f0 rest)
            in
            [(CF.mk_hprel_def k (mkHRel hp args0 no_pos) g path_fs1 lib1 (Some iflow))]
  in
  List.fold_left (fun ls hp -> ls@(combine_one_def hp)) [] sel_hps1

let combine_path_defs sel_hps1 path_defs iflow=
  let pr1 = !CP.print_svl in
  let pr2a = (pr_list_ln Cprinter.string_of_hprel_def) in
  let pr2 = pr_list_ln pr2a in
  Debug.no_2 "combine_path_defs" pr1 pr2 pr2a
      (fun _ _ ->  combine_path_defs_x sel_hps1 path_defs iflow)
      sel_hps1 path_defs

(*find def as the form H1 = H2, subst into views, hpdef, hp_defs*)
let reuse_equiv_hpdefs_x prog hpdefs hp_defs=
  let get_equiv_def (r_hp_defs, r_drop_hps, r_equivs) hp_def=
    let eq_hp_opt = match hp_def.CF.def_rhs with
      | [(f,_)] -> CF.extract_hrel_head f
      | _ -> None
    in
    match eq_hp_opt with
      | None -> (r_hp_defs@[hp_def], r_drop_hps, r_equivs)
      | Some (hp1) ->
            try
              let hp,_ = CF.extract_HRel hp_def.CF.def_lhs in
              (r_hp_defs, r_drop_hps@[hp], r_equivs@[(hp,hp1)])
            with _ -> (r_hp_defs@[hp_def], r_drop_hps, r_equivs)
  in
  let update_hpdef drop_hps equivs r hpdef=
    let hp,_ = CF.extract_HRel hpdef.CF.hprel_def_hrel in
    if CP.mem_svl hp drop_hps then
      r
    else
      let n_hpdef = CF.subst_hpdef equivs hpdef in
      (r@[n_hpdef])
  in
  let r_hp_defs, drop_hps, equivs = List.fold_left get_equiv_def ([],[],[]) hp_defs in
  if drop_hps = [] then (hpdefs, hp_defs) else
    (*update hpdefs: remove + subst*)
    let r_hpdefs = List.fold_left (update_hpdef drop_hps equivs) [] hpdefs in
    (*subst hp_defs*)
    let r_hp_defs1 = List.map (fun def -> {def with CF.def_rhs = List.map (fun (f,g) ->
        (CF.subst equivs f, CF.subst_opt equivs g)) def.CF.def_rhs}) r_hp_defs in
    (*subst cviews*)
    (* let n_cviews = List.map (fun v -> {v with }) prog.Cast.prog_view_decls in *)
    (r_hpdefs, r_hp_defs1)

let reuse_equiv_hpdefs prog hpdefs hp_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln Cprinter.string_of_hprel_def in
  Debug.no_2 "SAU.reuse_equiv_hpdefs" pr2 pr1 (pr_pair pr2 pr1)
      (fun _ _ -> reuse_equiv_hpdefs_x prog hpdefs hp_defs)
      hpdefs hp_defs

let pred_split_update_hpdefs iflow split_hps hpdefs hp_defs=
  let update_one hpdefs hp=
    try
      let hpdef,rem_hpdefs = CF.look_up_hpdef_with_remain hpdefs hp [] in
      let def = CF.look_up_hp_def hp_defs hp in
      let f = CF.disj_of_list (List.map fst def.CF.def_rhs) no_pos in
      (rem_hpdefs@[{hpdef with CF.hprel_def_body = [([], Some f, Some iflow)]}])
    with _ -> hpdefs
  in
  if split_hps = [] then hpdefs else
    List.fold_left update_one hpdefs split_hps


let filter_non_sel_x sel_hps0 hp_defs0 hpdefs0=
  let add_deps (cl_sel,rest_hpdefs) hpdef=
    match hpdef.CF.hprel_def_kind with
      | CP.HPRelDefn (hp,_,_) ->
            if CP.mem_svl hp cl_sel then
            let dep_hps = List.fold_left (fun ls (_,f_opt,_) ->
                match f_opt with
                  | Some f -> ls@(CF.get_hp_rel_name_formula f)
                  | None -> ls
            ) []  hpdef.CF.hprel_def_body
            in
             CP.remove_dups_svl (cl_sel@(List.filter (fun sv -> not (CP.eq_spec_var sv hp)) dep_hps)),rest_hpdefs
            else (cl_sel,rest_hpdefs@[hpdef])
      | _ -> (cl_sel,rest_hpdefs@[hpdef])
  in
  let rec find_close_sel sel_hps rest_defs=
    if rest_defs = [] then sel_hps else
      let sel_hps1, rest_defs1 =
        List.fold_left add_deps (sel_hps, []) rest_defs in
      if List.length sel_hps1 > List.length sel_hps then
         find_close_sel sel_hps1 rest_defs1
      else sel_hps
  in
  let cl_sel_hps = find_close_sel sel_hps0  hpdefs0 in
  let hp_defs1 = List.filter (fun def ->
      match def.CF.def_cat with
      | CP.HPRelDefn (hp,_,_) -> CP.mem_svl hp cl_sel_hps
      | _ -> false
  ) hp_defs0 in
  let hpdefs1 = List.filter (fun hpdef ->
      match hpdef.CF.hprel_def_kind with
      | CP.HPRelDefn (hp,_,_) -> CP.mem_svl hp cl_sel_hps
      | _ -> false
  ) hpdefs0 in
  hp_defs1,hpdefs1

let filter_non_sel sel_hps hp_defs hpdefs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln Cprinter.string_of_hprel_def in
  Debug.no_3 "filter_non_sel" !CP.print_svl pr1 pr2 (pr_pair pr1 pr2)
      (fun _ _ _ -> filter_non_sel_x sel_hps hp_defs hpdefs)
      sel_hps hp_defs hpdefs


let gen_slk_file is_proper prog file_name sel_pre_hps sel_post_hps rel_assumps unk_hps=
  let sel_pre_hps = CP.remove_dups_svl sel_pre_hps in
  let unk_hps = CP.remove_dups_svl unk_hps in
  let to_str_one_constr cs=
    "\nrelAssume \n" ^ (Cprinter.string_of_hprel_short cs)
  in
  let all_hps0, all_data_used0, all_view_used0 = List.fold_left (fun (r1,r2,r3) cs ->
      let ldns, lvns, lhps = CF.get_hp_rel_formula cs.CF.hprel_lhs in
      let rdns, rvns, rhps = CF.get_hp_rel_formula cs.CF.hprel_rhs in
      let ptrs = CP.remove_dups_svl ((CF.get_ptrs_w_args_f cs.CF.hprel_lhs)@(CF.get_ptrs_w_args_f cs.CF.hprel_rhs)) in
      let ptrs_node_used = List.fold_left (fun r t ->
          match t with
            | Named ot -> if ((String.compare ot "") ==0) then r else r@[ot]
            | _ -> r
      ) [] (List.map CP.type_of_spec_var ptrs) in
      let nr1 = r1@(List.map (fun (hp,_,_) -> hp) (lhps@rhps)) in
      let nr2 = r2@(List.map (fun dn -> dn.CF.h_formula_data_name) (ldns@rdns))@ptrs_node_used in
      let nr3 = r3@(List.map (fun vn -> vn.CF.h_formula_view_name) (lvns@rvns)) in
      (nr1,nr2,nr3)
  ) ([],[],[]) rel_assumps in
  (*data declare*)
  let all_data_used = Gen.BList.remove_dups_eq (fun s1 s2 -> String.compare s1 s2 = 0) all_data_used0 in
  let all_data_decls = List.fold_left (fun ls data_name ->
      try
        let data_decl = Cast.look_up_data_def no_pos prog.Cast.prog_data_decls data_name in
        ls@[data_decl]
      with _ -> ls
  ) [] all_data_used
  in

  let str_data_decls = List.fold_left (fun s s1 -> s^ s1 ^ ".\n") "" (List.map Cprinter.string_of_data_decl all_data_decls) in
  (*view declare*)
  let all_view_used = Gen.BList.remove_dups_eq (fun s1 s2 -> String.compare s1 s2 = 0) all_view_used0 in
  let all_view_decls = List.fold_left (fun ls view_name ->
      try
        let view_decl = x_add Cast.look_up_view_def_raw 42 prog.Cast.prog_view_decls view_name in
        ls@[view_decl]
      with _ -> ls
  ) [] all_view_used
  in
  let str_view_decls =   List.fold_left (fun s s1 -> s^ s1 ^ ".\n") "" (List.map Cprinter.string_of_view_decl all_view_decls) in
  (*preds decl*)
  let all_hps = CP.remove_dups_svl all_hps0 in
  let all_hp_decls = List.fold_left (fun ls hp ->
      try
        let hp_decl = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
        ls@[hp_decl]
      with _ -> ls
  ) [] all_hps
  in
  let str_hprel_decl = String.concat "\n" (List.map Cprinter.string_of_hp_decl all_hp_decls) in
  (*unknown decl*)
  let str_unk_decl = if unk_hps =[] then "" else "Declare_Unknown " ^ (!CP.print_svl unk_hps) ^"." in
  (*relational assumptions decl*)
  let str_constrs = List.fold_left (fun s s1 -> s ^ s1 ^ ".\n") "" (List.map to_str_one_constr rel_assumps) in

  (*infer command*)
  let str_infer_cmd = (if is_proper then "shape_infer_proper " else  "shape_infer ") ^
    (* (!CP.print_svl (CP.remove_dups_svl (CP.diff_svl all_hps (sel_post_hps@unk_hps)) ) (\* sel_pre_hps *\)) ^ *)
    (!CP.print_svl (CP.remove_dups_svl (CP.diff_svl sel_pre_hps (unk_hps)) ) (* sel_pre_hps *)) ^
    (!CP.print_svl sel_post_hps) ^"." in
  let out_chn =
    let reg = Str.regexp "\.ss" in
    let file_name1 = (if is_proper then "logs/gen_" else "logs/mod_") ^ (Str.global_replace reg ".slk" file_name) in
    (* let () = print_endline (file_name1 ^ ".slk") in *)
    let () = print_endline_quiet ("\n generating sleek file : " ^ file_name1) in
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    open_out (file_name1)
  in
  let str_slk = str_data_decls ^ "\n" ^ str_view_decls ^ "\n" ^ str_hprel_decl ^
    "\n" ^ str_unk_decl ^ "\n\n" ^ str_constrs ^ "\n\n" ^ str_infer_cmd in
  let () = output_string out_chn str_slk in
  let () = close_out out_chn in
  ()

(* combine all pred defs with the same name*)
let combine_hpdef_flow_x pre_hps post_hps hpdefs0=
  let get_args hpdef= match hpdef.Cformula.hprel_def_kind with
    | CP.HPRelDefn (_,r,args) -> r::args
    | _ -> report_error no_pos "sau.combine_hpdef_flow"
  in
  let do_combine hpdef0 hpdefs=
    let args0 = get_args hpdef0 in
    let bodys, libs = List.fold_left (fun (r1,r2) hpdef1 ->
        let args1 = get_args hpdef1 in
        let sst = List.combine args1 args0 in
        (r1@(List.map (fun (a, optf, oflow) -> (a, Cformula.subst_opt sst optf, oflow) ) hpdef1.Cformula.hprel_def_body),
        r2@(List.map (fun (f, oflow) -> (Cformula.subst sst f, oflow)) hpdef1.Cformula.hprel_def_body_lib))
    ) ([],[]) hpdefs in
    {hpdef0 with Cformula.hprel_def_body = hpdef0.Cformula.hprel_def_body@bodys;
        Cformula.hprel_def_body_lib = hpdef0.Cformula.hprel_def_body_lib@libs;
    }
  in
  let rec combine_helper hpdefs res=
    match hpdefs with
      | [] -> res
      | hpdef::rest ->
            let hp = Cformula.get_hpdef_name hpdef.Cformula.hprel_def_kind in
            let part,rest1 = List.partition (fun hpdef1 ->
                let hp1 = Cformula.get_hpdef_name hpdef1.Cformula.hprel_def_kind in
                CP.eq_spec_var hp hp1
            ) rest in
            let part1 = if part = [] then hpdef else
              do_combine hpdef part
            in
            combine_helper rest1 (res@[part1])
  in
  combine_helper hpdefs0 []


let combine_hpdef_flow pre_hps post_hps hpdefs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
  Debug.no_3 "combine_hpdef_flow" !CP.print_svl !CP.print_svl pr1 pr1
      (fun _ _ _ -> combine_hpdef_flow_x pre_hps post_hps hpdefs)
      pre_hps post_hps hpdefs
