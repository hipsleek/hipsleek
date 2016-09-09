#include "xdebug.cppo"

open VarGen
(*
26.11.2008
todo: disable the default logging for omega
*)

open Globals
open Others
open Stat_global
module DD = Debug
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Cast
open Cformula
open Prooftracer
open Gen.Basic

open Immutable
open Perm
open Mcpure_D
open Mcpure
(* open Stat_global *)
open Cvutil
(* open Infer *)

(* module Inf = Infer *)
module CP = Cpure
module CF = Cformula
(* module PR = Cprinter *)
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher
module VP = Vperm
module CVP = CvpermUtils

(* module LO = Label_only.Lab_List *)
module LO = Label_only.LOne
(* module ME = Musterr *)

(******************************************************************************)
(*=****************INFER REL HP ASS****************=*)
(*=*****************************************************************=*)

let generate_linking_svl drop_hpargs total_unk_map =
  let generate_linking_svl_one_hp pos (hp,args)=
    let hp_name = CP.name_of_spec_var hp in
    let ps,fr_svl,unk_map =
      try
        let fr_args = List.assoc hp total_unk_map in
        let ss = List.combine args fr_args in
        let ps = List.map (fun (sv,fr_sv) -> CP.mkPtrEqn sv fr_sv pos) ss in
        (ps,fr_args,[])
      with Not_found ->
        let ps,fr_svl = List.split (List.map (fun sv ->
            let fr_sv = CP.fresh_spec_var_prefix hp_name sv in
            (CP.mkPtrEqn sv fr_sv pos, fr_sv)
          ) args) in
        (ps,fr_svl,[(hp,fr_svl)])
    in
    let p = CP.conj_of_list ps pos in
    (p,fr_svl,unk_map)
  in
  let ps,ls_fr_svl,ls_unk_map = split3 (List.map (generate_linking_svl_one_hp no_pos) drop_hpargs) in
  (List.concat ls_fr_svl,CP.conj_of_list ps no_pos,List.concat ls_unk_map)

let generate_linking_svl drop_hpargs total_unk_map=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr2 = pr_triple !CP.print_svl !CP.print_formula
      (pr_list (pr_pair !CP.print_sv !CP.print_svl)) in
  Debug.no_1 "generate_linking_svl" pr1 pr2
    (fun _ -> generate_linking_svl drop_hpargs total_unk_map) drop_hpargs

let match_unk_preds prog lhs_hpargs rhs_hp rhs_args=
  let r_inst = Sautil.get_inst_hp_args prog rhs_hp in
  let rec helper lhs_rest=
    match lhs_rest with
    | [] -> None
    | (hp,args)::rest ->
      if List.length rhs_args = List.length args &&
        CP.eq_spec_var_order_list rhs_args args
        (* CP.diff_svl rhs_args args = [] *)
      then
        let l_inst = Sautil.get_inst_hp_args prog hp in
        if Sautil.cmp_inst l_inst r_inst then
          (Some (hp))
        else helper rest
      else helper rest
  in
  helper lhs_hpargs

(* find_guard@2@1 *)
(* find_guard inp1 :left heap:[ x::node<flted_12_16,p>@M] *)
(* find_guard inp2 leqs :[] *)
(* find_guard inp3 :[(H,[p])] *)
(* find_guard inp4 rhs_args :[p] *)
(* find_guard@2 EXIT:NONE *)
(* type: 'a -> *)
(*   CF.h_formula_data list -> *)
(*   'b -> *)
(*   (CF.CP.spec_var * CF.CP.spec_var) list -> *)
(*   ('c * CF.CP.spec_var list) list -> CP.spec_var list -> CF.h_formula option *)
let find_guard  prog lhds (* lhvs *) leqs null_ptrs l_selhpargs rhs_args =
  let l_args1 = List.fold_left (fun ls (hp,args) ->
      try
        let i_args, ni_args = x_add Sautil.partition_hp_args prog hp args in
        let sel_args = List.map fst i_args in
      ls@sel_args
      with _ -> ls@args
  ) [] l_selhpargs in
  let l_args2 = CF.find_close (l_args1@rhs_args) leqs in
  let cl_null_ptrs = CF.find_close null_ptrs leqs in
  let l_args3 = CP.diff_svl l_args2(* (CP.remove_dups_svl (l_args2@rhs_args)) *) cl_null_ptrs in
  let () = Debug.ninfo_hprint (add_str "l_args2"  !CP.print_svl) l_args2 no_pos in
  let () = Debug.ninfo_hprint (add_str "l_args3"  !CP.print_svl) l_args3 no_pos in
  let () = Debug.ninfo_hprint (add_str "rhs_args"  !CP.print_svl) rhs_args no_pos in
  (* let diff = CP.diff_svl rhs_args l_args1 in *)
  (* temporal fix for incr/ex15a/b. TODO *)
  (* if diff = [] then None else *) (*check-tll-1*)
    (*Now we keep heap + pure as pattern (env)*)
  let l_arg_cl = CF.look_up_rev_reachable_ptr_args prog lhds [] l_args3 in
  let () = DD.ninfo_hprint (add_str "l_arg_cl " !CP.print_svl) l_arg_cl no_pos in
    let guard_hds = List.filter (fun hd ->
         (*str-inf/ex16c3c requires root nodes in guard *)
        let svl =  hd.CF.h_formula_data_node::hd.CF.h_formula_data_arguments in
        CP.intersect_svl svl l_arg_cl <> []
      ) lhds
    in
    CF.join_star_conjunctions_opt (List.map (fun hd -> CF.DataNode hd) guard_hds)

(* type: 'a -> *)
(*   CF.h_formula_data list -> *)
(*   'b -> *)
(*   (CP.spec_var * CP.spec_var) list -> *)
(*   (CP.spec_var * CP.spec_var list) list -> *)
(*   CP.spec_var list -> CF.h_formula option *)
let find_guard  prog  lhds (* lhvs *) leqs null_ptrs l_selhpargs rhs_args=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
  let pr3 = pr_option Cprinter.prtt_string_of_h_formula
  in
  Debug.no_5 "find_guard" (add_str "left heap" (pr_list !CF.print_h_formula))
    (add_str "lhs_eqs" pr1) 
    (add_str "null_ptrs" !CP.print_svl)
    (add_str "left selected preds" pr2) 
    (add_str "rhs arg" !CP.print_svl) pr3
    (fun _ _ _ _ _ -> find_guard prog lhds (* lhvs *) leqs null_ptrs l_selhpargs rhs_args)
    (List.map (fun x -> CF.DataNode x) lhds) leqs null_ptrs l_selhpargs rhs_args

(* WN : new more generous find heap_guard condition *)
(* do we need to consider predicates? incomplete .. *)
let find_guard_new prog lhds lhvs leqs l_selhpargs rhs_args=
  let g = match lhds with
    | h::_ -> CF.DataNode h
    | [] -> failwith "XX"
  in Some g

(* type: 'a -> *)
(*   CF.h_formula_data list -> *)
(*   'b -> *)
(*   (CP.spec_var * CP.spec_var) list -> *)
(*   (CP.spec_var * CP.spec_var list) list -> *)
(*   CP.spec_var list -> CF.h_formula option *)

let find_guard_new prog lhds lhvs leqs l_selhpargs rhs_args=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
  let pr3 = (* match off with *)
    (* | None -> "NONE" *)
    (* | Some hf -> *) pr_option Cprinter.prtt_string_of_h_formula
  in
  Debug.no_4 "find_guard_new" (add_str "left heap" (pr_list !CF.print_h_formula)) 
    pr1 pr2 !CP.print_svl pr3
    (fun _ _ _ _ -> find_guard_new prog lhds lhvs leqs l_selhpargs rhs_args)
    (List.map (fun x -> CF.DataNode x) lhds) leqs l_selhpargs rhs_args

(*
  1.  H(x) --> x::node<_,p>: p is forwarded
  2.  H(x,y) --> x::node<_,p>: p and y are forwarded
  3.  x::<_,p> * H (p,p1) --> G(x): p and p1 are NOT forwarded
  3a. z::node2<_,l,r> * HP_577(l) * G1(r) --> G1(z) : l,r are NOT forwarded
*)

let find_undefined_selective_pointers prog es lfb lmix_f lhs_node unmatched rhs_rest (* rhs_h_matched_set *) leqs reqs pos
    (* total_unk_map *) post_hps prog_vars=
  let pr_sv_kind = pr_pair !CP.print_sv string_of_arg_kind in
  let get_rhs_unfold_fwd_svl lhds lhvs is_view h_node h_args def_svl leqNulls lhs_hpargs =
    let () = y_tinfo_hp (add_str "h_node" !CP.print_sv) h_node in
    let () = y_tinfo_hp (add_str "h_args" !CP.print_svl) h_args in
    let () = y_tinfo_hp (add_str "lhs_hpargs" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) lhs_hpargs in
    let rec parition_helper node_name hpargs=
      match hpargs with
      | [] -> (false, false, [],[], [])
      | (hp,args)::tl ->
        let i_args, ni_args = x_add Sautil.partition_hp_args prog hp args in
        let () = y_tinfo_hp (add_str "i_args" (pr_list pr_sv_kind)) i_args in
        let () = y_tinfo_hp (add_str "ni_args" (pr_list pr_sv_kind)) ni_args in
        let inter,rem = List.partition
            (fun (sv,_) ->
                let () = DD.ninfo_hprint (add_str  "sv" !CP.print_sv) sv pos in
                let cl = CF.find_close [sv] leqs in
                let () = DD.ninfo_hprint (add_str  "cl" !CP.print_svl) cl pos in
                CP.mem_svl node_name cl) i_args
        in
        let () = y_tinfo_hp (add_str "inter" (pr_list pr_sv_kind)) inter in
        let () = y_tinfo_hp (add_str "rem" (pr_list pr_sv_kind)) rem in
        let reachable_args = CF.look_up_reachable_ptr_args prog lhds lhvs
          (CP.diff_svl args h_args) in
        let () = y_tinfo_hp (add_str "reachable_args" !CP.print_svl) reachable_args in
        (* let flag = not !Globals.old_infer_complex_lhs in *)
        (* let flag = !Globals.new_infer_large_step in *)
        (* let flag = flag && (CP.intersect_svl reachable_args h_args !=[]) in *)
        (* let () = y_tinfo_hp (add_str "intersect_svl reachable_args h_args !=[]" string_of_bool) flag in *)
        (* let () = y_tinfo_hp (add_str "inter" !CP.print_svl) (List.map fst inter) in *)
        if inter = []  (* || flag *)
          (*str-inf/ex16c3d(8). exists free vars -> fail*)
           (* I suppose below is for new_infer_large_step ? *)
            then parition_helper node_name tl
        else
          let is_pre = Cast.check_pre_post_hp prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
          (true, is_pre,
          List.filter (fun (sv,_) -> if CP.mem_svl sv leqNulls || CP.mem_svl sv h_args then false
          else
            let reachable_vs = CF.look_up_reachable_ptr_args prog lhds lhvs [sv] in
            let reachable_vs_excl = CP.diff_svl reachable_vs [sv] in
            let () = y_tinfo_hp (add_str "reachable_vs_excl" !CP.print_svl) reachable_vs_excl in
            CP.intersect_svl reachable_vs_excl h_args = []
          ) rem,
          (ni_args), CP.diff_svl h_args reachable_args)
    in
    let res, is_pre, niu_svl_i, niu_svl_ni, h_args_rem = parition_helper h_node lhs_hpargs in
    if res then
      (*find arg pointers are going to be init in next stmts*)
      let args1 = CP.remove_dups_svl (CP.diff_svl h_args_rem (def_svl)) in
      let () = y_tinfo_hp (add_str "args1" !CP.print_svl) args1 in
      let () = y_tinfo_hp (add_str "     def_svl" !CP.print_svl) def_svl in
      let () = y_tinfo_hp (add_str "     h_args_rem" !CP.print_svl) args1 in
      let () = y_tinfo_hp (add_str "     niu_svl_i" (pr_list (pr_pair !CP.print_sv print_arg_kind))) niu_svl_i in
      let () = y_tinfo_hp (add_str "     niu_svl_ni" (pr_list (pr_pair !CP.print_sv print_arg_kind))) niu_svl_ni in
      (*old: args1@not_in_used_svl*)
      (*not_in_used_svl: NI*)
      let () = y_tinfo_hp (add_str "Globals.infer_const_obj # is_pure_field " string_of_bool) Globals.infer_const_obj # is_pure_field in
      let () = y_tinfo_hp (add_str " es.CF.es_infer_obj # is_pure_field_all" string_of_bool)  es.CF.es_infer_obj # is_pure_field_all in
      let args11 = if (* Globals.infer_const_obj # is_pure_field *)
        es.CF.es_infer_obj # is_pure_field_all
      (* !Globals.sa_pure_field *) then
          let args11 = List.map (fun sv ->
              if CP.is_node_typ sv then (sv, I)
              else (sv, NI)
            ) args1 in
          args11
        else
          let args10 = List.filter CP.is_node_typ args1 in
          let args11 = List.map (fun sv -> (sv, I)) args10 in
          args11
      in
      let niu_svl_i2 = List.map (fun (sv,n) ->
          if List.exists (fun dn -> CP.eq_spec_var dn.CF.h_formula_data_node sv) lhds then
            (sv, NI)
          else (sv, n) (* n = I *)
      ) niu_svl_i in
      let niu_svl_ni_total = niu_svl_i2@niu_svl_ni in
      (* for view, filter I var that is classified as NI in advance *)
      let args12 = List.filter (fun (sv,_) -> List.for_all (fun (sv1,_) -> not(CP.eq_spec_var sv1 sv)) niu_svl_ni_total) args11 in
      let () = y_tinfo_hp (add_str "args11" (pr_list (pr_pair !CP.print_sv string_of_arg_kind))) args11 in
      let () = y_tinfo_hp (add_str "args12" (pr_list (pr_pair !CP.print_sv string_of_arg_kind))) args12 in
      let () = y_tinfo_hp (add_str "niu_svl_ni_total" (pr_list (pr_pair !CP.print_sv string_of_arg_kind))) niu_svl_ni_total in
      let ls_fwd_svl =(*  if args12 =[] then *)
        (*   if is_view then *)
        (*     (\* if is view, we add root of view as NI to find precise constraints. duplicate with cicular data structure case?*\) *)
        (*     [(is_pre, niu_svl_i@[(h_node, NI)]@niu_svl_ni)] *)
        (*   else [] *)
        (* else *)
        let is_inf_pure_field = es.CF.es_infer_obj # is_pure_field_all in
        let () = y_tinfo_hp (add_str "is_inf_pure_field" string_of_bool) is_inf_pure_field in
        let i_svl, ni_svl = List.partition (fun (_, k) -> k = I) niu_svl_ni_total in
        if is_empty args12 then
          if is_empty i_svl && not is_inf_pure_field then []
          else [(is_pre, i_svl @ ni_svl @ [(h_node, NI)])]
        else
          if (* is_inf_pure_field && *) not !Globals.sep_pure_fields then
            let i_args12, ni_args12 = List.partition (fun (_, k) -> k = I) args12 in
            (* if not (is_empty i_args12) then *)
              List.map (fun ((arg, knd) as sv) ->
                let data_ni_svl = 
                  if is_view then []
                  else ni_args12
                in
                let fwd_svl = sv::niu_svl_ni_total @ data_ni_svl @ [(h_node, NI)] in
                (is_pre, fwd_svl)) i_args12
            (* else if is_empty i_svl && not is_inf_pure_field then []      *)
            (* else [(is_pre, i_svl @ ni_args12 @ ni_svl @ [(h_node, NI)])] *)
          else
            List.map (fun ((arg, knd) as sv) ->
              let data_ni_svl = 
                if is_view then []
                else 
                  match knd with
                  | NI -> []
                  | I ->
                    if is_empty niu_svl_ni_total then []
                    else List.filter (fun (a, k) -> 
                      k == NI && not (List.exists (fun (a1, _) -> CP.eq_spec_var a a1) niu_svl_ni_total)) args12
              in
              let fwd_svl = sv::niu_svl_ni_total@data_ni_svl@[(h_node, NI)] in
              (is_pre, fwd_svl)) args12
      in
      let () = y_tinfo_hp (add_str "ls_fwd_svl" (pr_list (pr_pair string_of_bool (pr_list (pr_pair !CP.print_sv string_of_arg_kind))))) ls_fwd_svl in
      (* str-inf/ex16c5b(8) do not need extra_clls *)
      (*generate extra hp for cll*)
      let extra_clls = [] in
      (* let extra_clls = if niu_svl_i = [] then *)
      (*   [] (\* [(is_pre, niu_svl_i@[(h_node, NI)]@niu_svl_ni)] *\) *)
      (*   else *)
      (*     [(is_pre, niu_svl_i@[(h_node, NI)]@niu_svl_ni)] *)
      (* in *)
      (true,ls_fwd_svl@extra_clls)
    else (false, [])
  in
  let get_lhs_fold_fwd_svl selected_hpargs def_vs rhs_args lhs_hds
      lhs_hvs ls_lhs_hpargs=
    let rec find_pt_new cur_hds svl res hd_rest=
      match cur_hds with
      | [] -> res,hd_rest
      | hd::tl ->
        let ptr_args = List.filter CP.is_node_typ hd.CF.h_formula_data_arguments in
        if (CP.intersect_svl ptr_args (svl@res) <> []) then
          find_pt_new tl svl (res@[hd.CF.h_formula_data_node]) hd_rest
        else find_pt_new tl svl res (hd_rest@[hd])
    in
    let rec loop_helper hds svl r=
      let r1,rest = find_pt_new hds svl r [] in
      if CP.diff_svl r1 r = [] || rest = [] then r1 else
        loop_helper rest svl r1
    in
    let process_one (hp,args)=
      let () = Debug.ninfo_zprint (lazy  ("  hp: " ^ (!CP.print_sv hp))) no_pos in
      if Gen.BList.mem_eq (fun (hp1,args1) (hp2,args2) ->
          CP.eq_spec_var hp1 hp2 && (CP.eq_spec_var_order_list args1 args2)
        ) (hp,args) selected_hpargs then
        let args_ins,_ = x_add Sautil.partition_hp_args prog hp args in
        let args_ins1 = fst (List.split args_ins) in
        let opto = loop_helper (*find_pt_new*) lhs_hds args_ins1 [] in
        (match opto with
         | [] -> let () = Debug.ninfo_zprint (lazy  ("    ptos: empty")) no_pos in []
         | ptos -> begin
             let () = Debug.ninfo_zprint (lazy  ("    ptos:" ^(!CP.print_svl ptos))) no_pos in
             let () = Debug.ninfo_zprint (lazy  ("    rhs_args:" ^(!CP.print_svl rhs_args))) no_pos in
             if CP.intersect_svl ptos rhs_args <> [] then [] else
               let fwd_svl = CP.remove_dups_svl (CP.diff_svl args_ins1 (def_vs@rhs_args)) in
               (* let is_pre = Cast.check_pre_post_hp prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in *)
               ((* is_pre, *) fwd_svl)
           end
        )
      else []
    in
    let ls_not_fwd_svl = List.map process_one ls_lhs_hpargs in
    (*should separate list of list *)
    (* let ls_not_fwd_svl1 = CP.remove_dups_svl (fun (_,svl1) (_,svl2) -> *)
    (*     List.length svl1 = List.length svl2 *)
    (*         && (CP.diff_svl svl1 slv2 = []) ) ls_not_fwd_svl in *)
    let ls_not_fwd_svl1 = CP.remove_dups_svl (List.concat ls_not_fwd_svl) in
    (*TODO: *)
    let ls_not_fwd_svl1_inst = List.map (fun sv -> (sv, I)) ls_not_fwd_svl1 in
    (true, ls_not_fwd_svl1_inst)
  in
  (* DD.info_pprint ">>>>>> find_undefined_selective_pointers <<<<<<" pos; *)
  (* let lfb = CF.subst_b leqs lfb in *)
  (* let rfb = CF.subst_b leqs rfb in *)
  let n_unmatched = (* CF.h_subst leqs *) unmatched in
  let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lfb in
  let leqNulls = MCP.get_null_ptrs lmix_f in
  let rhds, rhvs, rhrs = CF.get_hp_rel_h_formula n_unmatched in
  let reqNulls = [] (* MCP.get_null_ptrs rmix_f *) in
  (* let hrs = (lhrs @ rhrs) in *)
  let hds = (lhds @ rhds) in
  let hvs = (lhvs @ rhvs) in
  let eqs = (leqs@reqs) in
  let () = DD.ninfo_zprint (lazy  ("      eqs: " ^ (let pr = pr_list(pr_pair !CP.print_sv !CP.print_sv) in pr eqs))) no_pos in
  (*defined vars=  null + data + view + match nodes*)
  let r_def_vs = reqNulls @ (List.map (fun hd -> hd.CF.h_formula_data_node) rhds)
                 @ (List.map (fun hv -> hv.CF.h_formula_view_node) rhvs) in
  (*selective*)
  (*START debugging*)
  let () = y_tinfo_hp (add_str " lfb" Cprinter.string_of_formula_base) lfb in
  let () = y_tinfo_hp (add_str " n_unmatched" Cprinter.string_of_h_formula) n_unmatched in
  (*END debugging*)
  (* let n_lhds, _, n_lhrs = CF.get_hp_rel_bformula n_lfb in *)
  (**********get well-defined hp in lhs*)
  let helper (hp,eargs,_)=(hp,List.concat (List.map CP.afv eargs)) in
  let ls_lhp_args = (List.map helper lhrs) in
  let ls_rhp_args = (List.map helper rhrs) in
  let r_hps = List.map fst ls_rhp_args in
  let l_def_vs = leqNulls @ (List.map (fun hd -> hd.CF.h_formula_data_node) lhds)
                 @ (List.map (fun hv -> hv.CF.h_formula_view_node) lhvs) in
  let l_def_vs = CP.remove_dups_svl (CF.find_close l_def_vs (eqs)) in
  (*ll-append9-10: if not generate linking here, we can not obtain it later*)
  (* let unk_svl, unk_xpure, unk_map1 = (\* if !Globals.sa_split_base then *\) *)
  (*   SAC.generate_linking total_unk_map ls_lhp_args ls_rhp_args (\*eqs*\) post_hps pos *)
  (* (\* else ([], CP.mkTrue pos,total_unk_map) *\) *)
  (* in *)
  let unk_svl = [] in
  let unk_xpure = CP.mkTrue pos in
  let unk_map1 = [] in
  (* let lfb1 = CF.mkAnd_base_pure lfb (MCP.mix_of_pure unk_xpure) pos in *)
  let lfb, defined_hps,rem_lhpargs, new_lhs_hps =
    if r_hps = [] || CP.diff_svl r_hps post_hps <> [] then (lfb, [], ls_lhp_args, []) else
      List.fold_left (fun (lfb0,ls_defined,ls_rem, ls_new_hps) hpargs ->
          let lfb1, r_def,r_mem, new_hps = Sautil.find_well_defined_hp prog lhds lhvs r_hps
              prog_vars post_hps hpargs l_def_vs lfb0
              true  pos
          in
          (lfb1, ls_defined@r_def,ls_rem@r_mem, ls_new_hps@new_hps)
        ) (lfb, [],[], []) ls_lhp_args
  in
  (*END************get well-defined hp in lhs*)
  let def_vs = l_def_vs@r_def_vs in
  (*find closed defined pointers set*)
  let def_vs = CP.remove_dups_svl (CF.find_close def_vs (eqs)) in
  (*remove*)
  (* let unmatched_svl = (Sautil.get_ptrs unmatched) in *)
  let unmatched_svl = (Sautil.get_root_ptrs prog unmatched) in
  let unmatched_svl = (CF.find_close (unmatched_svl) (eqs)) in
  let closed_unmatched_svl0 = CF.look_up_reachable_ptr_args prog hds hvs unmatched_svl
  (* List.concat (List.map (Sautil.look_up_ptr_args_one_node prog hds hvs) unmatched_svl) *)
  in
  let closed_unmatched_svl = CP.remove_dups_svl
      (CF.find_close  (CP.remove_dups_svl (unmatched_svl@closed_unmatched_svl0)) (eqs)) in
  let () = Debug.ninfo_zprint (lazy  ("    closed_unmatched_svl:" ^(!CP.print_svl closed_unmatched_svl))) no_pos in
  (*END selective*)
  (*get all args of hp_rel to check whether they are fully embbed*)
  (* let unmatched_hp_args = CF.get_HRels n_unmatched in *)
  let () = Debug.ninfo_hprint (add_str "rem_lhpargs"  (pr_list (pr_pair !CP.print_sv !CP.print_svl))) rem_lhpargs no_pos in
  (* example incr/ex15c(3): we do not split base case here. unify the design *)
  let selected_hp_args0 = List.filter (fun (hp, args) ->
      let args_inst = Sautil.get_hp_args_inst prog hp args in
      (*SHOULD NOT traverse NULL ptr. this may cause some base-case split to be automatically
        done, but --classic will pick them up. sa/paper/last-obl3.slk
      *)
      let args_inst1 = (* CP.diff_svl args_inst leqNulls *) args_inst in
      (CP.intersect_svl args_inst1 closed_unmatched_svl) != []) rem_lhpargs in
  (* if lhs_node is an unknown preds. do simple step *)
  let selected_hp_args = match lhs_node with
    | CF.HRel (hp, eargs,_) -> begin
        try
          let args = (List.map CP.exp_to_sv eargs) in
          let hpargs = List.find (fun (hp1, args1) -> CP.eq_spec_var hp hp1 &&
              CP.eq_spec_var_order_list args args1
          ) selected_hp_args0 in
          [hpargs]
        with _ -> selected_hp_args0
          end
    | _ -> selected_hp_args0
  in
  let selected_hps0, hrel_args = List.split selected_hp_args in
  (*tricky here: do matching between two unk hps and we keep sth in rhs which not matched*)
  (* example incr/ex15c(3): still keep both unk preds in lhs and rhs *)
  let rest_svl = CF.get_hp_rel_vars_h_formula rhs_rest in
  let rest_svl1 = CF.find_close rest_svl leqs in
  let select_helper svl (hp,args)=
    if CP.diff_svl args svl = [] then [(hp,args)]
    else []
  in
  let drop_hpargs =  List.concat (List.map (select_helper rest_svl1) ls_lhp_args)in
  let drop_hps =  (List.map fst drop_hpargs) in
  (* let drop_hps = [] in *)
  (******************************************)
  (*TODO: test with sa/demo/sll-dll-2.ss*)
  (******************************************)
  (* find post_hps NI- cll case *)
  let post_svl_ni = List.fold_left (fun svl (hp, args) ->
      if CP.mem_svl hp post_hps then
        let args_i,_ = x_add Sautil.partition_hp_args prog hp args in
        svl@(List.map fst args_i)
      else svl
    ) [] ls_lhp_args in
  (* let vioated_ni_hps, vioated_ni_svl = List.fold_left (fun (ls1,ls2) (hp,args) -> *)
  (*     let _,args_ni = Sautil.partition_hp_args prog hp args in *)
  (*     (\*violate NI?*\) *)
  (*     let vs_ni = List.fold_left (fun ls (sv_ni, _) -> *)
  (*         if (List.exists (fun hd -> *)
  (*             CP.eq_spec_var sv_ni hd.CF.h_formula_data_node *)
  (*         ) lhds) then ls@[sv_ni] else ls *)
  (*     ) [] args_ni *)
  (*     in *)
  (*     let vs_ni1 = CP.diff_svl vs_ni post_svl_ni in *)
  (*     if vs_ni1 <> [] then *)
  (*       (ls1@[hp], ls2@vs_ni1) *)
  (*     else *)
  (*       (ls1,ls2) *)
  (* ) ([],[]) ls_lhp_args *)
  (* in *)
  let vioated_ni_hps(* , vioated_ni_svl *) = [] in
  (******************************************)
  let () = Debug.ninfo_hprint (add_str "selected_hp_args"  (pr_list (pr_pair !CP.print_sv !CP.print_svl))) selected_hp_args no_pos in
  let selected_hpargs =
    let drop_hps1 = drop_hps@vioated_ni_hps in
    List.filter (fun (hp,_) -> not (CP.mem_svl hp drop_hps1)) selected_hp_args
  in
  let () = Debug.ninfo_hprint (add_str "selected_hpargs"  (pr_list (pr_pair !CP.print_sv !CP.print_svl))) selected_hpargs no_pos in
  let selected_hpargs =
    let drop_hps1 = drop_hps@vioated_ni_hps in
    List.filter (fun (hp,_) -> not (CP.mem_svl hp drop_hps1)) selected_hp_args
  in
  let () = Debug.ninfo_hprint (add_str "selected_hpargs"  (pr_list (pr_pair !CP.print_sv !CP.print_svl))) selected_hpargs no_pos in
  (*========*)
  (*find undefined ptrs of all hrel args*)
  (*two cases: rhs unfold (mis-match is a node) and lhs fold (mis-match is a unk hp)*)
  let mis_match_found, ls_fwd_svl,rhs_sel_hpargs,lhs_selected_hpargs,ass_guard =
    if CF.is_HRel n_unmatched then
      let () = DD.ninfo_hprint (add_str  "Globals.infer_const_obj # is_pure_field " string_of_bool) Globals.infer_const_obj # is_pure_field pos in
      let rhs_hp, rhs_args= CF.extract_HRel n_unmatched in
      (*depend on the purpose of geting framing spec*)
      (*svl: framing heap*)
      let svl,selected_hpargs0, ass_guard0 = (* if proving_kind#string_of = "POST" then [] else *)
        (*since h_subst is not as expected we use closed set*)
        match match_unk_preds prog ls_lhp_args rhs_hp rhs_args with
        | Some hp ->
          let ass_guard1 = if CP.mem_svl rhs_hp post_hps then
              None
            else
              x_add find_guard(* _new *) prog lhds (* lhvs *) leqs leqNulls [(hp,rhs_args)] rhs_args
          in
          ([], [(hp,rhs_args)], ass_guard1)
        | None ->
          let closed_rhs_hpargs = CF.find_close rhs_args leqs in
          let () = Debug.ninfo_hprint (add_str "selected_hpargs"  (pr_list (pr_pair !CP.print_sv !CP.print_svl)))  selected_hpargs no_pos in
          let r1,r2 = (get_lhs_fold_fwd_svl selected_hpargs def_vs closed_rhs_hpargs lhds lhvs ls_lhp_args,
                       selected_hpargs) in
          let ass_guard1 = if CP.mem_svl rhs_hp post_hps then
              None
            else
              x_add find_guard prog lhds (* lhvs *) leqs leqNulls r2 rhs_args
          in
          ([r1],r2, ass_guard1)
      in
      (* let closed_svl = CF.find_close svl leqs in *)
      DD.ninfo_zprint (lazy  ("svl" ^ ((pr_list (pr_pair string_of_bool (pr_list (pr_pair !CP.print_sv print_arg_kind)))) svl))) pos;
      (*let unk_svl, unk_xpure, unk_map1 =*)
      (true (*TODO*), svl,[(rhs_hp, rhs_args)],selected_hpargs0,  ass_guard0)
    else
      let h_node, h_args = Sautil.get_h_node_cont_args_hf prog n_unmatched in
      let () = y_tinfo_hp (add_str " h_node" !CP.print_sv) h_node in
      let () = y_tinfo_hp (add_str " h_args" !CP.print_svl) h_args in
      (* let h_args1 = if List.filter CP.is_node_typ h_args in *)
      let hrel_args1 = List.concat hrel_args in
      (*should include their closed ptrs*)
      let hrel_args2 = CP.remove_dups_svl (CF.find_close hrel_args1 eqs) in
      let def_vs_w_unk_preds = CP.remove_dups_svl (def_vs@hrel_args2) in
      let () = DD.ninfo_zprint (lazy  ("def_vs@hrel_args2 " ^ (!CP.print_svl def_vs_w_unk_preds))) pos in
      let is_view = CF.is_view n_unmatched in
      (* match n_unmatched with *)
      (*   | CF.ViewNode vn -> true *)
      (*   | _ -> false *)
      (* in *)
      let def_vs1 = if is_view (* CF.is_view n_unmatched *) then CP.diff_svl def_vs_w_unk_preds h_args
        else def_vs_w_unk_preds (*(def_vs@hrel_args2)*)
      in
      let () = Debug.ninfo_hprint (add_str "def_vs1"  !CP.print_svl) def_vs1 no_pos in
      let mis_match_found, ls_unfold_fwd_svl = get_rhs_unfold_fwd_svl lhds lhvs is_view h_node h_args (def_vs1) leqNulls ls_lhp_args in
      let ass_guard1 = match n_unmatched with
        | CF.ViewNode vn ->
          x_add find_guard prog lhds (* lhvs *) leqs leqNulls selected_hpargs (vn.CF.h_formula_view_node::h_args)
        | CF.DataNode dn ->
          x_add find_guard prog lhds (* lhvs *) leqs leqNulls selected_hpargs (dn.CF.h_formula_data_node::h_args)
        | _ -> None
      in
      (mis_match_found, ls_unfold_fwd_svl(* @lundefs_args *),[],selected_hpargs, ass_guard1)
  in
  let ls_undef =  (* List.map CP.remove_dups_svl *) (ls_fwd_svl) in
  let () = y_tinfo_hp (add_str "ls_undef" 
      (pr_list (pr_pair string_of_bool (pr_list (pr_pair !CP.print_sv string_of_arg_kind))))) ls_undef in
  (* DD.info_zprint (lazy  ("selected_hpargs: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr (selected_hpargs)))) pos; *)
  (*special split_base*)
  let defined_hps0, lhs_selected_hpargs0 = if not !Globals.sa_sp_split_base then
      (*transfer all defined preds into selected lhs so that
        - they are consumed in ass (and removed from residue)
        - it will be split in shape _infer
      *)
      let lhs_selected_from_def = List.map (fun (hp,args,_,_) -> (hp,args)) defined_hps in
      ([], lhs_selected_hpargs@lhs_selected_from_def)
    else
      (defined_hps, lhs_selected_hpargs)
  in
  (*********CLASSIC************)
  let classic_defined, classic_lhs_sel_hpargs= if (check_is_classic ()) && (CF.is_empty_heap rhs_rest)  then
      (*/norm/sp-7b1: need compare pred name + pred args*)
      (* let lhs_sel_hps = List.map fst lhs_selected_hpargs in *)
      let truef = CF.mkTrue (CF.mkNormalFlow()) pos in
      let rem_lhpargs1 = List.filter (fun (hp,args) -> not (
          Gen.BList.mem_eq (fun (hp1,args1) (hp2,args2) ->
              CP.eq_spec_var hp1 hp2 && (CP.eq_spec_var_order_list args1 args2))
            (hp,args) lhs_selected_hpargs)) rem_lhpargs in
      List.fold_left (fun (ls,ls2) (hp,args) ->
          (* if CP.mem_svl hp sel_hps then *)
          let hf = (CF.HRel (hp, List.map (fun x -> CP.mkVar x pos) args, pos)) in
          let p = CP.filter_var (MCP.pure_of_mix lfb.CF.formula_base_pure) args in
          if CP.isConstTrue p then (ls,ls2@[hp,args]) else
            let lhs_ass = CF.mkAnd_base_pure (CF.formula_base_of_heap hf pos)
                (MCP.mix_of_pure p) pos in
            let new_defined = (hp, args, lhs_ass, truef) in
            (ls@[new_defined], ls2)
            (* else ls *)
        ) ([],[]) rem_lhpargs1
    else ([],[])
  in
  (****************************)
  let total_defined_hps = defined_hps0@classic_defined in
  let ls_defined_hpargs =  List.map (fun (hp,args,_,_) -> (hp,args)) total_defined_hps in
  let lhs_selected_hpargs1 = List.filter (fun (hp,args) ->
      not (Gen.BList.mem_eq Sautil.check_hp_arg_eq (hp,args) ls_defined_hpargs)
    ) lhs_selected_hpargs0
  (* lhs_selected_hpargs0@classic_lhs_sel_hpargs *)
  (*/norm/sp-7b1*)
  in
  (*********CLASSIC**sa/demo/xisa-remove2; bugs/bug-classic-4a**********)
  (* let classic_ptrs = if false (\* (check_is_classic ()) *\) && (CF.is_empty_heap rhs_rest) then *)
  (*     let acc_ptrs = List.fold_left (fun ls (_, args) -> ls@args) [] (lhs_selected_hpargs1@rhs_sel_hpargs@(List.map (fun (a,b,_,_) -> (a,b)) total_defined_hps)) in *)
  (*     let cl_acc_ptrs= CF.look_up_reachable_ptr_args prog hds hvs acc_ptrs in *)
  (*     List.fold_left (fun ls hd -> let sv = hd.CF.h_formula_data_node in *)
  (*                      if not (CP.mem_svl sv cl_acc_ptrs) then (ls@[sv]) else ls *)
  (*                    ) [] hds *)
  (*   else [] *)
  (* in *)
  (*********END CLASSIC************)
  (mis_match_found, (* undefs1@lundefs_args *) ls_undef,
  (* hds,hvs,lhrs,rhrs, *)leqNulls@reqNulls,
  lhs_selected_hpargs1,rhs_sel_hpargs, total_defined_hps,
   CP.remove_dups_svl (unk_svl),unk_xpure,unk_map1,new_lhs_hps,
  (* vioated_ni_svl, *)
  (* classic_ptrs, *) ass_guard)

(* type: Sautil.C.prog_decl -> *)
(*   CF.formula_base -> *)
(*   MCP.mix_formula -> *)
(*   CF.h_formula -> *)
(*   CF.h_formula -> *)
(*   'a -> *)
(*   (CP.spec_var * CP.spec_var) list -> *)
(*   (CP.spec_var * CP.spec_var) list -> *)
(*   VarGen.loc -> *)
(*   'b -> *)
(*   CP.spec_var list -> *)
(*   CF.CP.spec_var list -> *)
(*   bool * (bool * (CP.spec_var * Globals.hp_arg_kind) list) list * *)
(*   CF.h_formula_data list * CF.h_formula_view list * *)
(*   (CF.CP.spec_var * CF.CP.exp list * VarGen.loc) list * *)
(*   (CF.CP.spec_var * CF.CP.exp list * VarGen.loc) list * *)
(*   Slicing.CP.spec_var list * *)
(*   (Sautil.CF.CP.spec_var * CF.CP.spec_var list) list * *)
(*   (CF.CP.spec_var * CF.CP.spec_var list) list * *)
(*   (Sautil.CP.spec_var * CF.CP.spec_var list * Sautil.CF.formula_base * *)
(*    Sautil.CF.formula) *)
(*   list * CP.spec_var list * CP.formula * 'c list * *)
(*   (Cast.F.h_formula * (Sautil.CP.spec_var * CF.CP.spec_var list)) list * *)
(*   'd list * CF.CP.spec_var list * CF.h_formula option *)
let find_undefined_selective_pointers prog es lfb lmix_f lhs_node unmatched rhs_rest (* rhs_h_matched_set *) leqs reqs pos
    (* total_unk_map *) post_hps prog_vars=
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 = Cprinter.prtt_string_of_h_formula in
  let pr3 = pr_list (pr_pair !CP.print_sv !print_svl) in
  let pr4 = pr_list (pr_pair string_of_bool (pr_list (pr_pair !CP.print_sv print_arg_kind))) in
  let pr6 = pr_list_ln (pr_quad !CP.print_sv !CP.print_svl pr1 Cprinter.prtt_string_of_formula) in
  let pr8 ohf = match ohf with
    | None -> "None"
    | Some hf -> pr2 hf
  in
  let pr5 = fun (is_found, undefs,_,selected_hpargs, rhs_sel_hpargs,defined_hps,_,_,_,_,ass_guard) ->
    let pr = pr_hexa string_of_bool pr4 pr3 pr3 pr6 pr8 in
    pr (is_found, undefs,selected_hpargs,rhs_sel_hpargs,defined_hps,ass_guard)
  in
  Debug.no_2 "find_undefined_selective_pointers"
    (add_str "unmatched" pr2)
    (* (add_str "rhs_h_matched_set" !print_svl) *)
    (add_str "lfb" pr1)
    pr5
    ( fun _ _ -> find_undefined_selective_pointers prog es lfb lmix_f lhs_node unmatched rhs_rest
        (* rhs_h_matched_set *) leqs reqs pos (* total_unk_map *) post_hps prog_vars) unmatched (* rhs_h_matched_set *) lfb


(*
  out: list of program variables of mismatching node
*)
let get_prog_vars_x prog_hps rhs_unmatch proving_kind =
  match rhs_unmatch with
  | CF.HRel (hp, eargs,_) ->
    if proving_kind = PK_POST && CP.mem_svl hp prog_hps then
      ([hp],(List.fold_left List.append [] (List.map CP.afv eargs)))
    else [],[]
  | _ -> [],[]

let get_prog_vars prog_hps rhs_unmatch proving_kind =
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.string_of_h_formula in
  let pr3 =  Others.string_of_proving_kind in
  Debug.no_3 "get_prog_vars" pr1 pr2 pr3 (pr_pair pr1 pr1)
    (fun _ _ _ -> get_prog_vars_x prog_hps rhs_unmatch proving_kind) prog_hps rhs_unmatch proving_kind

(* let get_history_nodes_x root_svl hds history lfb done_args eqs lhs_hpargs= *)
(*   let hd_names = List.map (fun hd -> hd.CF.h_formula_data_node) hds in *)
(*   let hd_closed_names = (List.fold_left Sautil.close_def hd_names eqs) in *)
(*   let undefined_ptrs = Gen.BList.difference_eq CP.eq_spec_var root_svl hd_closed_names in *)
(*   (\* let () = Debug.info_zprint (lazy  ("      undefined_ptrs: " ^ (!CP.print_svl  undefined_ptrs))) no_pos in *\) *)
(*   let pos = CF.pos_of_formula (CF.Base lfb) in *)
(*   let rec look_up cur_hds dn0= *)
(*     match cur_hds with *)
(*     | [] -> [] *)
(*     | dn1::hdss -> if CP.eq_spec_var dn1.CF.h_formula_data_node dn0.CF.h_formula_data_node then *)
(*         List.combine dn0.CF.h_formula_data_arguments dn1.CF.h_formula_data_arguments *)
(*       else look_up hdss dn0 *)
(*   in *)
(*   let rec lookup_hrel ls_hpargs (hp0,args0)= *)
(*     match ls_hpargs with *)
(*     | [] -> false *)
(*     | (hp,args)::tl -> *)
(*       if CP.eq_spec_var hp0 hp then *)
(*         let args1 = List.map ((CP.subs_one eqs)) args in *)
(*         let args01 = List.map ((CP.subs_one eqs)) args0 in *)
(*         if Sautil.eq_spec_var_order_list args1 args01 then true else *)
(*           lookup_hrel tl (hp0,args0) *)
(*       else lookup_hrel tl (hp0,args0) *)
(*   in *)
(*   let helper (fb,hps,keep_svl,r_ss) hf= *)
(*     match hf with *)
(*     | CF.DataNode dn -> *)
(*       if CP.mem_svl dn.CF.h_formula_data_node undefined_ptrs then *)
(*         (mkAnd_fb_hf fb hf pos,hps,keep_svl,r_ss) *)
(*       else *)
(*         let ss = look_up hds dn in *)
(*         (fb,hps,keep_svl,r_ss@ss) *)
(*     | CF.HRel (hp,eargs,p) -> *)
(*       let args = List.concat (List.map CP.afv eargs) in *)
(*       if (Gen.BList.intersect_eq CP.eq_spec_var args undefined_ptrs) = [] || *)
(*          (Gen.BList.difference_eq CP.eq_spec_var args done_args) = [] || *)
(*          lookup_hrel lhs_hpargs (hp,args) *)
(*       then *)
(*         (fb,hps,keep_svl,r_ss) *)
(*       else *)
(*         (mkAnd_fb_hf fb hf p,hps@[hp], keep_svl@(Gen.BList.difference_eq CP.eq_spec_var args undefined_ptrs),r_ss) *)
(*     | HEmp -> (fb,hps,keep_svl,r_ss) *)
(*     | _ -> report_error pos "infer.get_history_nodes" *)
(*   in *)
(*   List.fold_left helper (lfb,[],[],[]) history *)

(* let get_history_nodes root_svl hds history lfb done_args eqs lhs_hpargs= *)
(*   let pr1 = pr_list_ln Cprinter.string_of_h_formula in *)
(*   let pr2 = Cprinter.string_of_formula_base in *)
(*   let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
(*   let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in *)
(*   Debug.no_4 "get_history_nodes" !CP.print_svl pr1 pr2 pr4 (fun (f,_,_,ss) ->(pr2 f) ^ " ;ss: " ^ (pr3 ss)) *)
(*     (fun _ _ _ _ -> get_history_nodes_x root_svl hds history lfb done_args eqs lhs_hpargs) root_svl history lfb lhs_hpargs *)

let get_h_formula_data_fr_hnode hn=
  match hn with
  | CF.DataNode hd -> [hd]
  | CF.HEmp -> []
  | CF.HRel _ -> []
  | _ -> report_error no_pos
           "infer.get_h_formula_data_fr_hnode: input must be a list of hnodes"

(* this caused problem with ex20e9a1.slk *)
(* how about ex20e9f5h.slk? *)
let is_match_pred lhs_selected_hpargs rhs_selected_hpargs =
  match lhs_selected_hpargs, rhs_selected_hpargs with
    | [(lhp,largs)], [(rhp,rargs)] -> 
      let () = y_tinfo_hp (add_str "largs" !CP.print_svl) largs in
      let () = y_tinfo_hp (add_str "rargs" !CP.print_svl) rargs in
      if true (* not(!Globals.adhoc_flag_3) *) then 
        CP.eq_spec_var_order_list largs rargs
      else 
        CP.diff_svl largs rargs = [] || CP.diff_svl rargs largs = [] 
    | _ -> false

let is_match_node lhs_selected_hpargs rhs_b =
  match lhs_selected_hpargs with
    | [(_,largs)] ->
          let rhds, rhvs, _ = CF.get_hp_rel_bformula rhs_b in
          let d_match = List.exists (fun dn ->
              let rargs = dn.CF.h_formula_data_node:: dn.CF.h_formula_data_arguments in
              CP.eq_spec_var_order_list largs rargs
          ) rhds in
          if d_match then true else
            List.exists (fun dn ->
              let rargs = dn.CF.h_formula_view_node:: dn.CF.h_formula_view_arguments in
              CP.eq_spec_var_order_list largs rargs
          ) rhvs
    | _ -> false

(*history from func calls*)
let simplify_lhs_rhs prog iact es lhs_b rhs_b rhs_rest leqs reqs hds hvs lhrs rhrs lhs_selected_hpargs rhs_selected_hpargs
    (* crt_holes  *)(* history *) unk_svl prog_vars (* lvi_ni_svl *) (* classic_nodes *)=
  (********************INTERNAL**************************)
  let  crt_holes = es.CF.es_crt_holes in
  let partition_i_ni_svl (hp,args)=
    (* let () = Debug.info_zprint (lazy  ("    args:" ^ (!CP.print_svl hd) ^ ": "^(!CP.print_svl args))) no_pos in *)
    let i_args_w_inst, i_args_w_ni = x_add Sautil.partition_hp_args prog hp args in
    (List.map fst i_args_w_inst, List.map fst i_args_w_ni)
  in
  let filter_non_selected_hp selected_hpargs (hp,args)= Gen.BList.mem_eq Sautil.check_hp_arg_eq (hp,args) selected_hpargs in
  let filter_non_selected_hp_rhs selected_hps (hp,_)= CP.mem_svl hp selected_hps in
  let lhs_hp = lhs_b.CF.formula_base_heap in
  let rhs_hp = rhs_b.CF.formula_base_heap in
  let () = y_tinfo_hp (add_str "lhs_hp" !CF.print_h_formula) lhs_hp in
  let () = y_tinfo_hp (add_str "rhs_hp" !CF.print_h_formula) rhs_hp in
  let () = y_tinfo_hp (add_str "rhs_rest" !CF.print_h_formula) rhs_rest in
  let is_match_flag = is_match_pred lhs_selected_hpargs rhs_selected_hpargs in
  let is_match = is_match_flag || is_match_node lhs_selected_hpargs rhs_b in
     (****************************************)
  (*****************INTERNAL********************)
  (*lhs*)
  let l_hpargs = List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs)) ) lhrs in
  let _,l_rem_hp_args = (List.partition (filter_non_selected_hp lhs_selected_hpargs) l_hpargs) in
  let lhp_args = lhs_selected_hpargs in
  let lkeep_hrels,lhs_keep_rootvars = List.split lhp_args in
  let lhs_keep_rootvars = List.concat lhs_keep_rootvars in
  let lhs_keep_i_rootvars, lhs_args_ni = List.fold_left (fun (i_svl, ni_svl) (hp,args) ->
      let args_i, args_ni = partition_i_ni_svl (hp,args) in
      (i_svl@args_i, ni_svl@args_ni)
    ) ([],[]) lhp_args in
  (*rhs*)
  let rhs_selected_hps = List.map fst rhs_selected_hpargs in
  let r_hpargs = CF.get_HRels rhs_b.CF.formula_base_heap in
  let rhp_args,r_rem_hp_args = (List.partition (filter_non_selected_hp_rhs rhs_selected_hps) r_hpargs) in
  (*root of hprel is the inst args; ni should be kept to preserve rele pure
  *)
  let rkeep_hrels, rhs_keep_rootvars, rhs_args_ni = List.fold_left (fun (hps,r_args, r_ni_svl) (hp,args) ->
      let args_i, args_ni = partition_i_ni_svl (hp,args) in
      (hps@[hp], r_args@(args_i), r_ni_svl@args_ni)
    ) ([],[], []) rhp_args in
  (*elim ptrs that violate NI rule in lhs*)
  (* let rhs_keep_rootvars =  CP.diff_svl rhs_keep_rootvars0 (lvi_ni_svl) in *)
  let () = Debug.ninfo_hprint (add_str  "    rhs_args_ni" !CP.print_svl) rhs_args_ni no_pos in
  (***************************)
  (*w history*)
  let rhs_svl0a = (CP.remove_dups_svl (lhs_keep_i_rootvars@rhs_keep_rootvars)) in
  let rhs_svl = (List.fold_left Sautil.close_def rhs_svl0a (leqs@reqs)) in
  let () = Debug.ninfo_hprint (add_str  " rhs_svl" !CP.print_svl) rhs_svl no_pos in
  (*elim ptrs that violate NI rule in lhs*)
  (* let svl = CP.diff_svl svl0 (lvi_ni_svl) in *)
  (*get args which already captures by other hprel*)
  (* let done_args = CP.remove_dups_svl (List.concat (List.map (fun (_,args) -> args) (lhp_args))) in *)

  let () = Debug.ninfo_hprint (add_str "    lhs_args_ni" !CP.print_svl) lhs_args_ni no_pos in
  let () = Debug.ninfo_hprint (add_str  "    rhs_args_ni" !CP.print_svl) rhs_args_ni no_pos in
  let () = Debug.ninfo_hprint (add_str  "    rhs_svl" !CP.print_svl) rhs_svl no_pos in
  (* let () = Debug.ninfo_hprint (add_str  "    keep_root_hrels" !CP.print_svl) keep_root_hrels no_pos in *)
  let () = DD.ninfo_hprint (add_str  "es.es_infer_obj # is_pure_field_all " string_of_bool) es.es_infer_obj # is_pure_field_all no_pos in
  let () = Debug.ninfo_hprint (add_str  "is_match" string_of_bool) is_match no_pos in

  let lhs_b0, new_hds, new_hvs = if is_match then
    let n_lhs_b = {lhs_b with CF.formula_base_heap= CF.drop_hnodes_hf lhs_b.CF.formula_base_heap (CF.get_ptrs lhs_b.CF.formula_base_heap) (* (rhs_svl@lhs_args_ni(* @keep_root_hrels@classic_nodes*)) *);} in
    n_lhs_b,[],[] (*matching unkown pred lhs vs. rhs*)
  else
    lhs_b,(hds(* @filter_his *)), hvs
  in
  let lhs_b = {lhs_b0 with CF.formula_base_heap= CF.drop_hnodes_hf lhs_b0.CF.formula_base_heap (CF.get_ptrs rhs_rest)} in

  (*******DROP*******)
  (*TOFIX*)
  let classic_local = check_is_classic () (* es.CF.es_infer_obj # is_classic *) in
  let () = Debug.ninfo_hprint (add_str  "check_is_classic ()" string_of_bool) (check_is_classic ()) no_pos in
  let () = Debug.ninfo_hprint (add_str  "es.CF.es_infer_obj # is_classic" string_of_bool) (es.CF.es_infer_obj # is_classic) no_pos in
  let classic_nodes = if classic_local (* && !Globals.adhoc_flag_2 *) then CF.get_ptrs lhs_b.CF.formula_base_heap else [] in
  let lhs_keep_root_svl = rhs_svl in
  let rhs_keep_root_svl = (rhs_svl(* @keep_root_hrels@classic_nodes*)) in
  let lhs_b1 = if classic_local (* check_is_classic () *) (* es.CF.es_infer_obj # is_classic_all *) || !Globals.old_infer_complex_lhs || iact != 1 (*infer_unfold*) 
    then lhs_b
    else
      {lhs_b with CF.formula_base_heap= CF.drop_hnodes_hf lhs_b.CF.formula_base_heap (CP.remove_dups_svl (lhs_keep_rootvars@rhs_args_ni));}
  in
  let lhs_b1a,rhs_b1a = Sautil.keep_data_view_hrel_nodes_two_fbs prog es.CF.es_infer_obj # is_pure_field_all
    (!Globals.old_infer_complex_lhs || iact != 1)
    lhs_b1 rhs_b
      (* (hds@filter_his) hvs *) new_hds new_hvs (* (lhp_args@rhp_args) *) leqs reqs (lhs_keep_root_svl@classic_nodes) rhs_keep_root_svl
      (lhs_keep_rootvars(* @keep_root_hrels *)) lhp_args lhs_args_ni
      rhs_selected_hps (* rhs_keep_rootvars *) rhs_args_ni
      (* unk_svl *) (* (CP.remove_dups_svl prog_vars) *) in
  (***************************)
  let () = y_tinfo_hp (add_str "lhs_b1" Cprinter.string_of_formula_base) lhs_b1 in
  let () = y_tinfo_hp (add_str  "lhs_b1a" Cprinter.string_of_formula_base) lhs_b1a in
  let () = y_tinfo_hp (add_str  "rhs_b1a" Cprinter.string_of_formula_base) rhs_b1a in
  let lhs_b1,rhs_b1 = if not (es.CF.es_infer_obj # is_pure_field_all) then
    let l_pure_fields =  CF.find_close (List.filter (fun sv -> not (CP.is_node_typ sv)) lhs_args_ni) (leqs@reqs) in
    let r_pure_fields =  CF.find_close (List.filter (fun sv -> not (CP.is_node_typ sv)) rhs_args_ni) (leqs@reqs) in
    let () = Debug.ninfo_hprint (add_str  "l_pure_fields" !CP.print_svl) l_pure_fields no_pos in
    let () = Debug.ninfo_hprint (add_str  "r_pure_fields" !CP.print_svl) r_pure_fields no_pos in
    (*lhs*)
    let new_lhs_b1 = if l_pure_fields=[] then lhs_b1a else
      let lhs_p = (MCP.pure_of_mix (lhs_b1a.CF.formula_base_pure)) in
      let l_keep_svl = CP.diff_svl (CP.fv lhs_p) l_pure_fields in
      {lhs_b1a with CF.formula_base_pure = MCP.mix_of_pure (CP.filter_var_new lhs_p l_keep_svl) } in
    (*rhs*)
    let new_rhs_b1 = if r_pure_fields=[] then rhs_b1a else
      let rhs_p = (MCP.pure_of_mix (rhs_b1a.CF.formula_base_pure)) in
      let r_keep_svl = CP.diff_svl (CP.fv rhs_p) r_pure_fields in
      {rhs_b1a with CF.formula_base_pure = MCP.mix_of_pure (CP.filter_var_new rhs_p r_keep_svl) } in
    (new_lhs_b1, new_rhs_b1)
  else lhs_b1a,rhs_b1a in
  let () = y_tinfo_hp (add_str "lhs_b1" Cprinter.string_of_formula_base) lhs_b1 in
  (*subst holes*)
  let lhs_b1 = {lhs_b1 with CF.formula_base_heap = Immutable.apply_subs_h_formula crt_holes lhs_b1.CF.formula_base_heap} in
  let rhs_b1 = {rhs_b1 with CF.formula_base_heap = Immutable.apply_subs_h_formula crt_holes rhs_b1.CF.formula_base_heap} in
  let lhs_b2 = (* CF.subst_b (leqs) *) lhs_b1 in (*m_apply_par*)
  let rhs_b2 = (* CF.subst_b (leqs@reqs) *) rhs_b1 in
  let () = Debug.ninfo_hprint (add_str  "lhs_b1" Cprinter.string_of_formula_base) lhs_b1 no_pos in
  let () = Debug.ninfo_hprint (add_str  "rhs_b2" Cprinter.string_of_formula_base) rhs_b2 no_pos in
  (*remove redundant: x=x*)
  let lhs_b3 = {lhs_b2 with CF.formula_base_pure = MCP.mix_of_pure
                                (CP.remove_redundant (MCP.pure_of_mix lhs_b2.CF.formula_base_pure))} in
  let rhs_b3 = {rhs_b2 with CF.formula_base_pure = MCP.mix_of_pure
                                (CP.remove_redundant (MCP.pure_of_mix rhs_b2.CF.formula_base_pure))} in
  (*args of one hp must be diff --
    inside Sautil.keep_data_view_hrel_nodes_two_fbs*)
  (* let lhs_b4,rhs_b4 = Sautil.rename_hp_args lhs_b3 rhs_b3 in *)
  (CF.prune_irr_neq_formula ~en_pure_field:es.CF.es_infer_obj # is_pure_field_all prog_vars lhs_b3 rhs_b3,rhs_b3)

let simplify_lhs_rhs prog iact es lhs_b rhs_b rhs_rest leqs reqs hds hvs lhrs rhrs
    lhs_selected_hpargs rhs_selected_hpargs (* crt_holes *) (* history *) unk_svl prog_vars
    (* lvi_ni_svl *) (* classic_nodes *)=
  let pr = Cprinter.string_of_formula_base in
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  DD.no_4 "simplify_lhs_rhs" (add_str "lhs preds" pr1)
      (add_str "rhs preds" pr1) pr pr (pr_pair pr pr)
    (fun _ _ _ _ -> simplify_lhs_rhs prog iact es lhs_b rhs_b rhs_rest
        leqs reqs hds hvs lhrs rhrs lhs_selected_hpargs rhs_selected_hpargs (* crt_holes *) (* history *)
        unk_svl prog_vars
        (* lvi_ni_svl *) (* classic_nodes *)
    )
      lhs_selected_hpargs rhs_selected_hpargs lhs_b rhs_b


let lookup_eq_hprel_ass_x hps hprel_ass lhs rhs=
  let lhs_svl = List.map (CP.name_of_spec_var) (CP.remove_dups_svl (CF.fv lhs)) in
  let rec checkeq_hprel hprels=
    match hprels with
    | [] -> false,[]
    | ass::tl ->
      let b1,_ = Checkeq.checkeq_formulas lhs_svl lhs ass.CF.hprel_lhs in
      if b1 then
        let b2,m = Checkeq.checkeq_formulas [] rhs ass.CF.hprel_rhs in
        if b2 then
          true,List.filter (fun (sv1,sv2) -> CP.mem sv1 hps) (List.hd m)
        else checkeq_hprel tl
      else
        checkeq_hprel tl
  in
  checkeq_hprel hprel_ass

(*example s3*)
let lookup_eq_hprel_ass hps hprel_ass lhs rhs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr4 = pr_pair string_of_bool pr3 in
  Debug.no_4 "lookup_eq_hprel_ass" !CP.print_svl pr1 pr2 pr2 pr4
    (fun _ _ _ _ -> lookup_eq_hprel_ass_x hps hprel_ass lhs rhs) hps hprel_ass lhs rhs

let constant_checking prog rhs lhs_b rhs_b es=
  let r,new_lhs = Sautil.simp_matching prog (CF.Base lhs_b) (CF.Base rhs_b) in
  if r then
    let new_es = {es with CF.es_formula = new_lhs} in
    (true, new_es, rhs, None, None, None)
  else
    (false, es, rhs, None, None, None)

let generate_error_constraints prog es lhs rhs_hf lhs_hps es_cond_path pos=
  if not !Globals.sae then
    None
  else
    (* to transform heap to pure formula, use baga *)
    let old_baga_flag = !use_baga (* !baga_xpure *) in
    let () = use_baga (* baga_xpure *) := true in
    let prhs_guard,_,_ = x_add Cvutil.xpure_heap_symbolic 10 prog rhs_hf (Mcpure.mkMTrue pos) 0 in
    let () = use_baga (* baga_xpure *) := old_baga_flag in
    let prhs_guard1 =  MCP.pure_of_mix prhs_guard in
    (* tranform pointers: x>0, x=1 -> x!=null *)
    let prhs_guard2 = Cputil.hloc_enum_to_symb prhs_guard1 in
    if CP.isConstTrue prhs_guard2 then None else
      (******************************************)
      let neg_prhs0 = (CP.neg_eq_neq prhs_guard2) in
      (* contradict with LHS? *)
      let () = use_baga (* baga_xpure *) := true in
      let lhs_p,_,_ = (x_add Cvutil.xpure_symbolic 10 prog es.es_formula) in
      let () = use_baga (* baga_xpure *) := old_baga_flag in
      let lhs_extra = CP.mkAnd (MCP.pure_of_mix lhs_p) neg_prhs0 no_pos in
      if not( TP.is_sat_raw (MCP.mix_of_pure lhs_extra)) then None else
        (******************************************)
        let neg_prhs = MCP.mix_of_pure neg_prhs0 in
        let ass_rhs = CF.mkBase HEmp neg_prhs CvpermUtils.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] pos in
        let knd = CP.RelAssume lhs_hps in
        let ehp_rel = CF.mkHprel_w_flow knd [] [] [] lhs None ass_rhs es_cond_path !error_flow_int in
        (* let hp_rel_list = Gen.BList.difference_eq Sautil.constr_cmp hp_rel_list0 ex_ass in *)
        let hp_rel_list = [ehp_rel] in
        (* postpone until heap_entail_after_sat *)
        if !Globals.old_infer_hp_collect then 
          begin
            x_tinfo_hp (add_str "HPRelInferred" (pr_list_ln Cprinter.string_of_hprel_short)) hp_rel_list pos;
            let () = Infer.rel_ass_stk # push_list hp_rel_list in
            let () = Log.current_hprel_ass_stk # push_list (hp_rel_list) in
            ()
          end;
        (* update es.formula *)
        let n_es_form = mkAnd_pure es.es_formula neg_prhs pos in
        let n_es_form_e = CF.substitute_flow_into_f !error_flow_int n_es_form in
        let new_es = {es with (* CF.es_infer_hp_rel = es.CF.es_infer_hp_rel # push_list hp_rel_list; *)
                              CF.es_formula = n_es_form_e} in
        let () =  new_es.CF.es_infer_hp_rel # push_list_loc x_loc hp_rel_list in
        Some new_es

let generate_error_constraints prog es lhs rhs_hf lhs_hps es_cond_path pos=
  let pr1 = Cprinter.string_of_formula in
  let pr2 es = Cprinter.prtt_string_of_formula es.CF.es_formula in
  Debug.no_3 " generate_error_constraints" pr2 pr1 Cprinter.string_of_h_formula (pr_option pr2)
    (fun  _ _ _ ->  generate_error_constraints prog (es:entail_state) lhs rhs_hf lhs_hps es_cond_path pos)
    es lhs rhs_hf


(*if guard exists in the lhs, remove it*)
let check_guard es guard_opt lhs_b_orig lhs_b rhs_b pos=
  let process_guard_old guard=
    let g_hds = Sautil.get_hdnodes_hf guard in
    let l_hds,_, l_hrels = CF.get_hp_rel_bformula lhs_b in
    let _,_, r_hrels = CF.get_hp_rel_bformula rhs_b in
    (* check useful guard:
       A guard is useful if
       vars(G) /\ (ws-vs) != []
    *)
    let largs = List.fold_left (fun ls (_,eargs,_)->
        ls@(List.fold_left List.append [] (List.map CP.afv eargs))) [] l_hrels in
    let rargs = List.fold_left (fun ls (_,eargs,_)->
        ls@(List.fold_left List.append [] (List.map CP.afv eargs))) [] r_hrels in
    if (CP.intersect_svl (CF.h_fv guard) (CP.diff_svl rargs largs) = []) then
      (*  None *)
      (* else if (CP.intersect_svl (CF.h_fv guard) (CP.intersect_svl (CF.fv (CF.Base lhs_b)) (CF.fv (CF.Base rhs_b))) = []) then *)
      None
    else
      let l_hd_svl = List.map (fun hd -> hd.CF.h_formula_data_node) l_hds in
      let inter_svl = List.fold_left (fun res hd ->
          if CP.mem_svl hd.CF.h_formula_data_node l_hd_svl then
            (res@[hd.CF.h_formula_data_node])
          else res
      ) [] g_hds in
      let new_guard = if inter_svl = [] then (Some guard) else
        let guard1 = CF.drop_hnodes_hf guard inter_svl in
        if guard1 = CF.HEmp then None else (Some guard1)
      in
      match new_guard with
        | None -> None
        | Some hf -> let g_svl = CF.h_fv hf in
          let () = DD.ninfo_hprint (add_str  "  g_svl" !CP.print_svl) g_svl pos in
          let p = (MCP.pure_of_mix lhs_b.CF.formula_base_pure) in
          let () = DD.ninfo_hprint (add_str  "  p" !CP.print_formula) p pos in
          let g_pure = CP.filter_var p g_svl in
          let () = DD.ninfo_hprint (add_str  "  g_pure" !CP.print_formula) g_pure pos in
          let p_orig = (MCP.pure_of_mix lhs_b_orig.CF.formula_base_pure) in
          let () = DD.ninfo_hprint (add_str  "  p_orig" !CP.print_formula) p_orig pos in
          let g_pure_orig = CP.filter_var p_orig g_svl in
          let () = DD.ninfo_hprint (add_str  "  g_pure_orig" !CP.print_formula) g_pure_orig pos in
          let g_pure_rem = Gen.BList.difference_eq (CP.equalFormula) (CP.split_conjunctions g_pure_orig)
              (CP.split_conjunctions g_pure) in
          Some (CF.Base {lhs_b with CF.formula_base_heap= hf;
                                    CF.formula_base_pure = (MCP.mix_of_pure (CP.join_disjunctions g_pure_rem));} )
    in
     (* - rose tree need to remove guard that captured in LHS already
       - tree-2: need handle pure of guard for path-sensitive
    *)
    let process_guard guard =
      let g_hds = Sautil.get_hdnodes_hf guard in
      let l_hds,_, l_hrels = CF.get_hp_rel_bformula lhs_b in
      let _,_, r_hrels = CF.get_hp_rel_bformula rhs_b in
      let l_hd_svl = List.map (fun hd -> hd.CF.h_formula_data_node) l_hds in
      let inter_svl = List.fold_left (fun res hd ->
          if CP.mem_svl hd.CF.h_formula_data_node l_hd_svl then
            (res@[hd.CF.h_formula_data_node])
          else res
        ) [] g_hds in
      let new_guard = if inter_svl = [] then (Some guard) else
          let guard1 = CF.drop_hnodes_hf guard inter_svl in
          if guard1 = CF.HEmp then None (* rose-tree *)
          else (Some guard1)
      in
      match new_guard with
      | None -> None
      | Some hf ->
        let g_svl0 = CF.get_node_args hf in
        let () = DD.ninfo_hprint (add_str  "  g_svl0" !CP.print_svl) g_svl0 pos in
        let g_svl = if es.CF.es_infer_obj # is_pure_field_all then g_svl0 else
          List.filter (CP.is_node_typ) g_svl0
        in
        let () = DD.ninfo_hprint (add_str  "  g_svl" !CP.print_svl) g_svl pos in
        let p = (MCP.pure_of_mix lhs_b.CF.formula_base_pure) in
        let () = DD.ninfo_hprint (add_str  "  p" !CP.print_formula) p pos in
        let g_pure = CP.filter_var p g_svl in
        let () = DD.ninfo_hprint (add_str  "  g_pure" !CP.print_formula) g_pure pos in
        let p_orig = (MCP.pure_of_mix lhs_b_orig.CF.formula_base_pure) in
        let () = DD.ninfo_hprint (add_str  "  p_orig" !CP.print_formula) p_orig pos in
        let g_pure_orig = CP.filter_var p_orig g_svl in
        let () = DD.ninfo_hprint (add_str  "  g_pure_orig" !CP.print_formula) g_pure_orig pos in
        let g_pure_rem = Gen.BList.difference_eq (CP.equalFormula) (CP.split_conjunctions g_pure_orig)
            (CP.split_conjunctions g_pure) in
        Some (CF.Base {lhs_b with CF.formula_base_heap= hf;
                                  CF.formula_base_pure = (MCP.mix_of_pure (CP.conj_of_list g_pure_rem no_pos));} )
    in
    (***************END****************)
    match guard_opt with
    | None -> None
    | Some hf -> process_guard hf

(* type: Sautil.CF.h_formula option -> *)
(*   CF.formula_base -> CF.formula_base -> CF.formula_base -> CF.formula option *)
let check_guard es guard_opt lhs_b_orig lhs_b rhs_b pos=
  let prh = pr_option !CF.print_h_formula in
  Debug.no_1 "check_guard" prh (pr_option !CF.print_formula)
      (fun _ -> check_guard es guard_opt lhs_b_orig lhs_b rhs_b pos) guard_opt

let hn_trans_field_mut hn =
  match hn with
    | CF.DataNode hn ->
          CF.DataNode {hn with CF.h_formula_data_param_imm = List.map (fun _ ->
              CP.ConstAnn Mutable
          ) hn.CF.h_formula_data_param_imm;
              CF.h_formula_data_imm = CP.ConstAnn Mutable;}
    |  CF.ViewNode hv ->
           CF.ViewNode {hv with h_formula_view_imm = CP.ConstAnn Mutable}
    | _ -> hn


let generate_constraints ?(caller="") prog iact es rhs lhs_b ass_guard rhs_b1 rhs_rest defined_hps
    ls_unknown_ptrs unk_pure unk_svl (* no_es_history *) lselected_hpargs rselected_hpargs
    (* hds hvs lhras *) lhrs (* rhras *) rhrs leqs reqs eqNull prog_vars (* lvi_ni_svl *) (* classic_nodes *)
    pos =
  let lhds, lhvs, lhras = CF.get_hp_rel_bformula lhs_b in
  let rhds, rhvs, rhras = CF.get_hp_rel_bformula rhs_b1 in
  let hds = lhds@rhds in
  let hvs = lhvs@rhvs in
  (*****************INTERNAL********************)
  let update_fb (fb,r_hprels,post_hps, hps,hfs) (is_pre, unknown_ptrs) =
    match unknown_ptrs with
    | [] -> (fb,r_hprels,post_hps,hps,hfs)
    | _ ->
      let (hf,vhp_rels) = x_add (Sautil.add_raw_hp_rel ~caller:(x_loc ^ ":" ^ caller)) prog is_pre false unknown_ptrs pos in
      begin
        match hf with
        | HRel hp ->
          let new_post_hps = if is_pre then post_hps else (post_hps@[vhp_rels]) in
          ((CF.mkAnd_fb_hf fb hf pos), r_hprels@[vhp_rels], new_post_hps,
           hps@[hp], hfs@[hf])
        | _ -> report_error pos "infer.generate_constraints: add_raw_hp_rel should return a hrel"
      end
  in
  (*change to @M for field-ann*)
  (* let hn_trans_field_mut hn = *)
  (*   match hn with *)
  (*   | CF.DataNode hn -> *)
  (*     CF.DataNode {hn with CF.h_formula_data_param_imm = List.map (fun _ -> *)
  (*         CP.ConstAnn Mutable *)
  (*       ) hn.CF.h_formula_data_param_imm; *)
  (*            CF.h_formula_data_imm = CP.ConstAnn Mutable;} *)
  (*   |  CF.ViewNode hv -> *)
  (*     CF.ViewNode {hv with h_formula_view_imm = CP.ConstAnn Mutable} *)
  (*   | _ -> hn *)
  (* in *)
  (*****************END INTERNAL********************)
  let new_rhs_b,rvhp_rels,new_post_hps, new_hrels,r_new_hfs =
    List.fold_left update_fb (rhs_b1,[],[],[],[]) ls_unknown_ptrs in
  let () = y_tinfo_hp (add_str "ls_unknown_ptrs" (pr_list (pr_pair string_of_bool (pr_list (pr_pair !CP.print_sv string_of_arg_kind))))) ls_unknown_ptrs in 
  let () = y_tinfo_hp (add_str "rhs_b1" !CF.print_formula) (CF.Base rhs_b1) in
  let () = y_tinfo_hp (add_str "new_rhs_b" !CF.print_formula) (CF.Base new_rhs_b) in
  (*add roots from history*)
  let matched_svl = CF.get_ptrs (*es.CF.es_heap*) lhs_b.CF.formula_base_heap in
  let matched_svl1 = (List.fold_left Sautil.close_def matched_svl (leqs@reqs)) in
  (* let sel_his = List.concat (List.map (fun hf -> match hf with *)
  (*     | CF.DataNode hd -> if CP.mem_svl hd.CF.h_formula_data_node matched_svl1 then [] else [hf] *)
  (*     | _ -> [hf] *)
  (*   ) no_es_history) in *)
  (* let sel_his = [] in *)
  DD.ninfo_hprint (add_str "new_rhs_b" Cprinter.string_of_formula_base) new_rhs_b pos;
  let lhs_b0 = CF.mkAnd_base_pure lhs_b (MCP.mix_of_pure unk_pure) pos in
  let group_unk_svl = List.concat (List.map (fun ass -> ass.CF.unk_svl) Log.current_hprel_ass_stk # get_stk) in
  let total_unk_svl = CP.remove_dups_svl (group_unk_svl@unk_svl) in
  let new_rselected_hpargs = (rselected_hpargs@(List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs)))
                                              new_hrels)) in
  let new_rhs_b0 = {new_rhs_b with 
                    CF.formula_base_heap =  CF.check_imm_mis rhs new_rhs_b.CF.formula_base_heap} in
  let () = y_tinfo_hp (add_str "new_rhs_b0" !CF.print_formula) (CF.Base new_rhs_b0) in
  let (new_lhs_b,new_rhs_b) = x_add simplify_lhs_rhs prog iact es lhs_b0 new_rhs_b0 rhs_rest leqs reqs hds hvs lhras (rhras@new_hrels)
      (lselected_hpargs) new_rselected_hpargs
      total_unk_svl prog_vars (* lvi_ni_svl *) (* classic_nodes *) in
  let () = y_tinfo_hp (add_str "new_rhs_b" !CF.print_formula) (CF.Base new_rhs_b) in
  (*simply add constraints: *)
  let hprel_def = List.concat (List.map CF.get_ptrs ((* no_es_history@ *)(CF.get_hnodes lhs_b.CF.formula_base_heap
  (* es.CF.es_heap *))))
  in
  (*split the constraints relating between pre- andxs post-preds*)
  let es_cond_path = CF.get_es_cond_path es in
  let defined_hprels = List.map (x_add Sautil.generate_hp_ass 0 [](* (closed_hprel_args_def@total_unk_svl) *) es_cond_path) defined_hps in
  let m = [] in
  let hp_rels, n_es_heap_opt, ass_lhs=
    (* if b && m <> [] then [] else *)
    let knd = CP.RelAssume (CP.remove_dups_svl (lhrs@rhrs@rvhp_rels)) in
    let before_lhs = CF.Base new_lhs_b in
    let before_rhs = CF.Base new_rhs_b in
    let lhs0,rhs = if !Globals.allow_field_ann then
        (CF.formula_trans_heap_node hn_trans_field_mut before_lhs,
         CF.formula_trans_heap_node hn_trans_field_mut before_rhs)
      else
        (before_lhs,before_rhs)
    in
    let vnodes = (* CF.get_views (CF.Base lhs_b) *) [] in
    let lhs =  CF.remove_neqNull_svl (CP.diff_svl matched_svl (List.map (fun vn -> vn.h_formula_view_node) vnodes)) lhs0 in
    let grd = x_add check_guard es ass_guard lhs_b new_lhs_b new_rhs_b pos in
    (* let rhs = CF.Base new_rhs_b in *)
    let () = x_tinfo_hp (add_str "before_lhs"  Cprinter.prtt_string_of_formula) before_lhs no_pos in
    let () = y_tinfo_hp (add_str "before_rhs"  Cprinter.prtt_string_of_formula) before_rhs in
    let () = x_tinfo_hp (add_str "lhs"  Cprinter.prtt_string_of_formula) lhs no_pos in
    let () = y_tinfo_hp (add_str "rhs"  Cprinter.prtt_string_of_formula) rhs in
    let hp_rel = CF.mkHprel knd [] [] matched_svl lhs grd rhs es_cond_path in
    let () = y_tinfo_hp (add_str "hp_rel" Cprinter.string_of_hprel_short) hp_rel in
    [hp_rel], Some (match lhs with
        | CF.Base fb -> fb.CF.formula_base_heap
        | _ -> report_error no_pos "INFER.generate_constrains: impossible"
      ), lhs
  in
  let hp_rel_list0a = hp_rels@defined_hprels in
  let hp_rel_list0 = 
    if !Globals.old_keep_triv_relass then hp_rel_list0a
    else List.filter (fun cs -> not (Sautil.is_trivial_constr ~en_arg:true cs)) hp_rel_list0a in
  let ex_ass = (Infer.rel_ass_stk # get_stk) in
  let hp_rel_list = Gen.BList.difference_eq Sautil.constr_cmp hp_rel_list0 ex_ass in
  (* postpone until heap_entail_after_sat *)
  if (!Globals.old_infer_hp_collect) then
    begin
      let () = Infer.rel_ass_stk # push_list (hp_rel_list) in
      let () = Log.current_hprel_ass_stk # push_list (hp_rel_list) in
      ()
    end;
  (* let () = DD.info_hprint (add_str  "  rvhp_rels" !CP.print_svl rvhp_rels) pos in *)
  (* let () = DD.info_hprint (add_str  "  new_post_hps" !CP.print_svl) new_post_hps pos in *)
  let () = x_tinfo_hp (add_str  "  hp_rels" (pr_list_ln Cprinter.string_of_hprel))  hp_rels pos in
  let () = x_tinfo_hp (add_str  "  hp_rel_list"  (pr_list_ln Cprinter.string_of_hprel)) hp_rel_list pos in
  r_new_hfs, new_lhs_b,m,rvhp_rels,new_post_hps, hp_rel_list, n_es_heap_opt, ass_lhs

let generate_constraints ?(caller="") prog iact es rhs lhs_b ass_guard rhs_b1 rhs_rest defined_hps
    ls_unknown_ptrs unk_pure unk_svl (* no_es_history *) lselected_hpargs rselected_hpargs
    (* hds hvs lhras *) lhrs (* rhras *) rhrs leqs reqs eqNull prog_vars (* lvi_ni_svl *) (* classic_nodes *)
    pos =
  let pr1 = !CF.print_formula in
  let pr2 = Cprinter.string_of_hprel_short in
  let prr = (fun (_, _, _, _, _, hps, _, _) -> pr_list_ln pr2 hps) in
  Debug.no_2 "generate_constraints"
    (add_str "lhs_b" pr1) (add_str "rhs_b1" pr1) prr
    (fun _ _ -> generate_constraints ~caller:caller prog iact es rhs lhs_b ass_guard rhs_b1 rhs_rest defined_hps
    ls_unknown_ptrs unk_pure unk_svl (* no_es_history *) lselected_hpargs rselected_hpargs
    (* hds hvs lhras *) lhrs (* rhras *) rhrs leqs reqs eqNull prog_vars (* lvi_ni_svl *) (* classic_nodes *) pos)
    (CF.Base lhs_b) (CF.Base rhs_b1)

let update_es prog es hds hvs ass_lhs_b rhs rhs_rest r_new_hfs defined_hps lselected_hpargs0
    new_hp_rels leqs all_aset m post_hps unk_map hp_rel_list pos=
  let update_es_f f new_hf=
    (CF.mkAnd_f_hf f (CF.h_subst leqs new_hf) pos)
  in
  begin
    let new_es_formula =  List.fold_left update_es_f es.CF.es_formula r_new_hfs in
    (*drop hp rel + nodes consumed in lhs of hp_rel in es_formula*)
    (* DD.info_hprint (add_str  "  before" Cprinter.string_of_formula) new_es_formula pos; *)
    let root_vars_ls = Sautil.get_data_view_hrel_vars_bformula ass_lhs_b in
    (*tricky here: since we dont have matching between two unk hps, we keep sth in rhs which not matched*)
    let rest_svl = CF.get_hp_rel_vars_h_formula rhs_rest in
    let rest_svl1 = CF.find_close rest_svl leqs in
    let ass_hp_args = CF.get_HRels ass_lhs_b.CF.formula_base_heap in
    let check_full_inter svl (hp,args)=
      if CP.diff_svl args svl = [] then [hp] else []
    in
    let keep_hps =  List.concat (List.map (check_full_inter rest_svl1) ass_hp_args) in
    let () = DD.ninfo_hprint (add_str  "  rest_svl"  !CP.print_svl) rest_svl pos in
    let () = x_tinfo_hp (add_str  "  keep_hps"  !CP.print_svl) keep_hps pos in
    let root_vars_ls1 = CP.diff_svl root_vars_ls keep_hps in
    let well_defined_svl = List.concat (List.map (fun (hp,args,_,_) -> hp:: args) defined_hps) in
    let root_vars_ls2 = CF.find_close root_vars_ls1 leqs in
    (*lhs should remove defined hps + selected hps*)
    let lselected_hpargs1 = lselected_hpargs0@(List.map (fun (a,b,_,_) -> (a,b)) defined_hps) in
    (*should consider closure of aliasing. since constraints are in normal form,
      but residue is not. and we want to drop exact matching of args*)
    (* let lselected_hpargs2 = List.map (fun (hp,args) -> (hp, CF.find_close args leqs)) lselected_hpargs1 in *)
    let () = DD.ninfo_hprint (add_str  "  lselected_hpargs: " (pr_list (pr_pair !CP.print_sv  !CP.print_svl))) lselected_hpargs1 pos
    in
    let () = DD.ninfo_hprint (add_str  "  all_aset: " (CP.EMapSV.string_of )) all_aset pos  in
    let lselected_hpargs2 = List.map (fun (hp,args) -> (hp, CP.find_eq_closure all_aset args)) lselected_hpargs1 in
    let () = DD.ninfo_hprint (add_str  "  lselected_hpargs2: " (pr_list (pr_pair !CP.print_sv  !CP.print_svl))) lselected_hpargs2 pos
    in
    let () = x_tinfo_hp (add_str  "  root_vars_ls2 " !CP.print_svl) root_vars_ls2 pos in
    let root_vars_ls3 = CP.remove_dups_svl ((List.fold_left (fun r sv ->
        r@(CP.EMapSV.find_equiv_all sv all_aset)
      ) [] root_vars_ls2)@root_vars_ls2) in

    let () = x_tinfo_hp (add_str  "  root_vars_ls3 " !CP.print_svl) root_vars_ls3 pos in
    let () = DD.ninfo_hprint (add_str  "  residue (before)" Cprinter.string_of_formula) new_es_formula pos in
    let new_es_formula = Sautil.drop_data_view_hrel_nodes_from_root prog new_es_formula hds hvs leqs root_vars_ls3
        well_defined_svl (CF.h_fv rhs) lselected_hpargs2 in
    let () = DD.ninfo_hprint (add_str  "  residue (after)" Cprinter.string_of_formula) new_es_formula pos in
    (*CF.drop_hrel_f new_es_formula lhrs in *)
    (*add mismatched heap into the entail states if @L*)
    let check_consumed_node h f=
      match h with
      | DataNode hd -> 
        (* if (!Globals.allow_field_ann) then *)
        (*   (f,h) *)
        (* else  *)
        (* if  not(CF.isLend (hd.CF.h_formula_data_imm)) then (f,h) else *)
        let n_param_imm = if (!Globals.allow_field_ann) then
            List.map (fun _ -> CP.ConstAnn Mutable) hd.CF.h_formula_data_param_imm
          else hd.CF.h_formula_data_param_imm
        in
        let new_h = DataNode {hd with CF.h_formula_data_imm = (CP.ConstAnn(Mutable));
                                      CF.h_formula_data_param_imm = n_param_imm} in
        (*generate new hole*)
        let nf, nholes = if (* not(!Globals.adhoc_flag_3) && *) Immutable.produces_hole (hd.CF.h_formula_data_imm) then
            let hole_no = Globals.fresh_int() in
            let h_hole = CF.Hole hole_no  in
            let () = y_tinfo_hp (add_str "adding new hole" (pr_pair Cprinter.string_of_h_formula string_of_int)) (new_h, hole_no) in
            (* (CF.mkAnd_f_hf f h_hole pos,[(new_h, hole_no)]) *)
            (f,[(new_h, hole_no)])
          else (f,[])
        in
        (nf , new_h, nholes)
      | _ ->
        (f, h, [])
    in
    let new_es_formula, new_lhs, new_holes = check_consumed_node rhs new_es_formula in
    let new_es_formula1 = x_add CF.subst m new_es_formula in
    (*if rhs_rest = Emp && . remove infer svl such that infer_pure_m is not invoked*)
    let n_ihvr = (es.CF.es_infer_vars_hp_rel@new_hp_rels)
    in
    (* let n_ivr = if CF.is_empty_heap rhs_rest then CP.diff_svl es.CF.es_infer_vars_rel (CF.h_fv rhs) else es.CF.es_infer_vars_rel in *)
    let new_es = {es with CF.es_infer_vars_hp_rel = n_ihvr;
                          (* CF.es_infer_vars_rel =  n_ivr; *)
                          (* CF.es_infer_hp_rel = es.CF.es_infer_hp_rel # push_list hp_rel_list; *)
                          CF.es_infer_hp_unk_map = (es.CF.es_infer_hp_unk_map@unk_map);
                          CF.es_infer_vars_sel_post_hp_rel = (es.CF.es_infer_vars_sel_post_hp_rel @ post_hps);
                          CF.es_crt_holes = es.CF.es_crt_holes@new_holes;
                          CF.es_formula = new_es_formula1} in
    let () = new_es.CF.es_infer_hp_rel # push_list_loc x_loc hp_rel_list in
    x_tinfo_hp (add_str "  residue before matching: " Cprinter.string_of_formula) new_es.CF.es_formula pos;
    x_tinfo_hp (add_str "  new_es_formula: "  Cprinter.string_of_formula) new_es_formula pos;
    x_tinfo_hp (add_str "  new_lhs: "  Cprinter.string_of_h_formula) new_lhs pos;
    (new_es, new_lhs)
  end

let update_es prog es hds hvs ass_lhs_b rhs rhs_rest r_new_hfs defined_hps lselected_hpargs0
    rvhp_rels leqs all_aset m post_hps unk_map hp_rel_list pos=
  let pr1 fb = Cprinter.string_of_formula (CF.Base fb) in
  let pr2 = Cprinter.prtt_string_of_h_formula in
  let pr3 es = Cprinter.prtt_string_of_formula es.CF.es_formula in
  let pr4 = CP.EMapSV.string_of in
  Debug.no_4 "INFER.update_es" pr3 pr1 pr2 pr4 (pr_pair pr3 pr2)
    (fun _ _ _ _ -> update_es prog es hds hvs ass_lhs_b rhs rhs_rest r_new_hfs defined_hps lselected_hpargs0
        rvhp_rels leqs all_aset m post_hps unk_map hp_rel_list pos)
    es ass_lhs_b rhs all_aset

let get_eqset puref =
  let (subs,_) = CP.get_all_vv_eqs puref in
  let eqset = CP.EMapSV.build_eset subs in
  eqset


let return_out_of_inst estate lhs_b extended_hps =
  let n_estate = {estate with
      CF.es_infer_vars_hp_rel = estate.CF.es_infer_vars_hp_rel@extended_hps;
  } in
  (true, n_estate,lhs_b)

let return_out_of_inst estate lhs_b extended_hps =
  let pr = Cprinter.string_of_entail_state in
  Debug.no_1 "return_out_of_inst" pr (fun (_, es, _) -> pr es)
    (fun _ -> return_out_of_inst estate lhs_b extended_hps) estate

(* the inst is currently guided by RHS eqset *)
let gen_inst prog estate lhds lhvs sst =
  let rec aux sst acc_p =
    match sst with
    | [] -> true,acc_p
    | (sv1,sv2)::rest ->
      let sv2_orig = CP.subs_one estate.CF.es_rhs_eqset sv2 in
      if CP.eq_spec_var sv1 sv2_orig then
        aux (* gen_inst *) (* prog estate lhds lhvs *) rest acc_p
      else
        (*str-inf/ex16c3d(8). exists free vars -> fail*)
        let reach_vs = CF.look_up_reachable_ptr_args prog lhds lhvs [sv1] in
        if CP.mem_svl sv2_orig reach_vs then
          if !Globals.old_infer_complex_lhs then
            aux (* gen_inst *) (* prog estate lhds lhvs *) rest acc_p
          else false, acc_p
        else
          let p = CP.mkEqVar sv1 sv2 no_pos in
          let new_acc = CP.mkAnd acc_p p no_pos in
          aux (* gen_inst *) (* prog estate lhds lhvs *) rest new_acc
  in aux sst (CP.mkTrue no_pos)

(* type: 'a -> *)
(*   CF.entail_state -> *)
(*   CF.h_formula_data list -> *)
(*   CF.h_formula_view list -> *)
(*   (CP.spec_var * CP.spec_var) list -> CP.formula -> bool * CP.formula *)
let gen_inst prog estate lhds lhvs sst =
  let pr2 =(pr_list (pr_pair pr_sv pr_sv)) in
  let pr_sv = !CP.print_sv in
  let pr3 = pr_pair string_of_bool !CP.print_formula in
  Debug.no_2 "gen_inst" (add_str "es_rhs_eqset" pr2)  (add_str "sst" pr2) pr3 (fun _ _ -> gen_inst prog estate lhds lhvs sst) estate.es_rhs_eqset sst


let do_inst prog estate lhs_b largs rargs extended_hps=
  (* let lhs_vs = CF.fv (Base lhs_b) in *)
  (* (\* only vars not already in LHS can be instantiated *\) *)
  (* let rargs = List.filter (fun v -> not(CP.mem_svl v lhs_vs)) rargs in *)
  try
    if rargs = [] then return_out_of_inst estate lhs_b extended_hps
    else
      let p = (MCP.pure_of_mix lhs_b.CF.formula_base_pure) in
      let fvp = CP.fv p in
      let () = Debug.tinfo_hprint (add_str  "fvp" !CP.print_svl) fvp no_pos in
      let () = Debug.tinfo_hprint (add_str  "rargs" !CP.print_svl) rargs no_pos in
      let sst = List.combine largs rargs in (* inst only for same number of parameters *)
      if CP.intersect_svl rargs fvp != [] then
        let is_succ=
          let ps_eqs = List.filter (fun p -> (CP.is_eq_exp_ptrs rargs p)) (CP.list_of_conjs p) in
          if ps_eqs = [] then false else true
        in
        is_succ,estate, lhs_b
      else
        let lhds, lhvs, _ = CF.get_hp_rel_bformula lhs_b in
        let is_succ, p = x_add gen_inst prog estate lhds lhvs sst  in
        if not is_succ then
          is_succ, estate, lhs_b
        else
          let () = Debug.tinfo_hprint (add_str  "p" !CP.print_formula) p no_pos in
          let mf = (MCP.mix_of_pure p) in
          let () = Debug.tinfo_hprint (add_str  "lhs_b" !CF.print_formula_base) lhs_b no_pos in
          (true,
           {estate with CF.es_formula = CF.mkAnd_pure estate.CF.es_formula mf no_pos;
                        CF.es_infer_vars_hp_rel = estate.CF.es_infer_vars_hp_rel@extended_hps;
           },
           CF.mkAnd_base_pure lhs_b mf no_pos)
  with _ -> return_out_of_inst estate lhs_b extended_hps

(* type: 'a -> *)
(*   CF.entail_state -> *)
(*   CF.formula_base -> *)
(*   CP.spec_var list -> *)
(*   CP.spec_var list -> *)
(*   CF.CP.spec_var list -> bool * CF.entail_state * CF.formula_base *)
let do_inst prog estate lhs_b largs rargs extended_hps =
  let pr_svl = !CP.print_svl in
  let pr_bf bf = !print_formula (Base bf) in
  let pr_r (b,_,eb) = (pr_pair string_of_bool pr_bf) (b,eb) in
  Debug.no_4 "do_inst" (add_str "lhs_b" pr_bf) (add_str "largs" pr_svl) (add_str "rargs" pr_svl) (add_str "hps" pr_svl) pr_r (fun _ _ _ _ -> do_inst prog estate lhs_b largs rargs extended_hps) lhs_b largs rargs extended_hps 

(* TODO : how about aliases *)
let set_root_unfold lhs rhs alias_set =
  match lhs with
  | HRel (hp, args, _) -> 
    begin
      try
        let ptr = CF.get_root_ptr rhs in
        let rec aux xs n = match xs with
          | [] -> 
            let () = y_winfo_hp (add_str "no match with args" !CF.print_h_formula) rhs in
            (-1)
          | x::xs -> let v = CP.exp_to_sv x in
            if List.exists (CP.eq_spec_var v) (ptr::alias_set) then n
            else aux xs (n+1) in
        let posn = aux args 0 in
        let () = y_tinfo_hp (add_str ("root posn (" ^ (!CP.print_sv hp) ^ ")") string_of_int) posn in
        let () = if posn>=0 then Cast.cprog_obj # set_hp_root hp posn in
        ()
      with _ -> 
        let () = y_winfo_hp (add_str "no ptr on rhs?" !CF.print_h_formula) rhs in
        ()
    end
  | _ -> 
    let () = y_winfo_hp (add_str "not a hp_rel?" !CF.print_h_formula) lhs in
    ()

let set_root_unfold lhs rhs alias_set =
  let pr = !CF.print_h_formula in
  Debug.no_3 "set_root_unfold" 
    (add_str "lhs" pr) (add_str "rhs" pr)
    (add_str "aset" !CP.print_svl) (fun _ -> "")
    set_root_unfold lhs rhs alias_set

(*
type: (CF.entail_state ->
   CF.formula_base ->
   Context.action -> Cformula.list_context * Prooftracer.proof) ->
  Context.match_res ->
  'a ->
  'b ->
  CF.entail_state ->
  'c ->
  CF.formula_base ->
  Cformula.formula_base ->
  'd ->
  CP.spec_var list ->
  'e -> VarGen.loc -> Cformula.list_context * Prooftracer.proof
*)
let infer_unfold prog pm_aux action (* caller prog *) estate (* conseq *) lhs_b rhs_b (* a *) (rhs_h_matched_set: CP.spec_var list) (* is_folding *) pos
  : (Cformula.list_context * Prooftracer.proof) =
  (* let prog = () in *)
  let r = action in
  let lhs_node = r.Context.match_res_lhs_node in
  let rhs_node = r.Context.match_res_rhs_node in
  let rhs_rest = r.Context.match_res_rhs_rest in
  let rhs_inst = r.Context.match_res_compatible in
  let alias_set = r.Context.match_res_alias_set in
  let () = y_tinfo_hp (add_str "(infer_unfold)lhs_node" !CF.print_h_formula) lhs_node in
  let () = y_tinfo_hp (add_str "(infer_unfold)rhs_node" !CF.print_h_formula) rhs_node in
  let () = y_tinfo_hp (add_str  "compatible"  (pr_list (pr_pair !CP.print_sv !CP.print_sv))) rhs_inst in
  let () = y_tinfo_hp (add_str "roots" pr_id) Cast.cprog_obj # show_roots in
  let () = set_root_unfold lhs_node rhs_node alias_set in
  let () = y_tinfo_hp (add_str "roots(updated)" pr_id) Cast.cprog_obj # show_roots in
  let () = y_tinfo_hp (add_str "estate" Cprinter.string_of_entail_state) estate in
  let is_succ_inst, n_estate, n_lhs_b = 
    match lhs_node,rhs_node with
    | HRel (lhp,leargs,_),HRel (rhp,reargs,_) ->
      let () = y_tinfo_pp "HRel vs HRel" in
      if CP.mem_svl lhp estate.es_infer_vars_hp_rel (* && not (CP.mem_svl rhp estate.es_infer_vars_hp_rel) *) then
        match leargs, reargs with
        | er::rest1,_::rest2 -> begin
            let largs = (List.map CP.exp_to_sv rest1) in
            let rargs = (List.map CP.exp_to_sv rest2) in
            let () = Debug.tinfo_hprint (add_str  "infer_unfold:rhs_inst"  (pr_list (pr_pair !CP.print_sv !CP.print_sv))) rhs_inst no_pos in
            if (* List.length rargs < List.length largs &&  *)rhs_inst != [] then
              (* let r = (CP.exp_to_sv er) in *)
              (* let sst = Cfutil.exam_homo_arguments prog lhs_b rhs_b lhp rhp r rargs largs in *)
              let lhds, lhvs, _ = CF.get_hp_rel_bformula lhs_b in
              let is_succ, p = x_add gen_inst prog estate lhds lhvs rhs_inst  in
              if not is_succ then
                true, estate, lhs_b
              else
                (* WN : why do we add rhp to es_infer_hp_rel? *)
                (* WN : this may make the behaviour less predictable.. *)
                let mf = (MCP.mix_of_pure p) in
                (true,
                 {estate with CF.es_formula = CF.mkAnd_pure estate.CF.es_formula mf no_pos;
                              CF.es_infer_vars_hp_rel = estate.CF.es_infer_vars_hp_rel@[rhp];
                 },
                 CF.mkAnd_base_pure lhs_b mf no_pos)
            else
              x_add do_inst prog estate lhs_b largs rargs [rhp]
          end
        | _ -> return_out_of_inst estate lhs_b [rhp]
      else
        return_out_of_inst estate lhs_b []
    | HRel (lhp,leargs,_),ViewNode vn -> 
      let () = y_tinfo_pp "HRel vs ViewNode" in
      begin
        if CP.mem_svl lhp estate.es_infer_vars_hp_rel then
          match leargs with
          | _::rest1 ->
            let largs = (List.map CP.exp_to_sv rest1) in
            let rargs = vn.CF.h_formula_view_arguments in
            x_add do_inst prog estate lhs_b largs rargs []
          | _ -> return_out_of_inst estate lhs_b []
        else
          return_out_of_inst estate lhs_b []
      end
    | _ ->
      let () = y_tinfo_pp "_" in 
      return_out_of_inst estate lhs_b []
  in
  let () = y_tinfo_hp (add_str "n_estate" Cprinter.string_of_entail_state) n_estate in
  if not is_succ_inst then
    let err_msg = "infer_unfold (cannot inst)" in
    let conseq = Some (Base rhs_b) in
    (Errctx.mkFailCtx_may ~conseq:conseq x_loc err_msg estate pos,NoAlias)
  else
    let () = Debug.ninfo_hprint (add_str "n_estate.es_formula" !CF.print_formula) n_estate.es_formula no_pos in
    pm_aux n_estate n_lhs_b (Context.M_infer_heap (1, lhs_node, rhs_node, rhs_rest))

let infer_unfold prog pm_aux action (* caller prog *) estate (* conseq *) lhs_b rhs_b (* a *) (rhs_h_matched_set: CP.spec_var list) (* is_folding *) pos
  : (Cformula.list_context * Prooftracer.proof) =
  let length_ctx ctx = match ctx with
    | CF.FailCtx _ -> 0
    | CF.SuccCtx ctx0 -> List.length ctx0 in
  let pr2 x = 
    "\nctx length:" ^ (string_of_int (length_ctx (fst x))) ^ 
    " \n Context:"^ Cprinter.string_of_list_context(* _short *) (fst x) in
  let pr3 = Cprinter.string_of_formula in
  Debug.no_4 "infer_unfold"
    (add_str "estate" Cprinter.string_of_entail_state(* _short *))
    (add_str "action" Context.string_of_match_res) 
    (add_str "lhs_b" pr3) 
    (add_str "rhs_b" pr3)
    pr2
    (fun _ _ _ _ -> infer_unfold prog pm_aux action estate lhs_b rhs_b rhs_h_matched_set pos) 
    estate action (Base lhs_b) (Base rhs_b) 

let infer_fold prog pm_aux action (* caller prog *) estate (* conseq *) lhs_b rhs_b (* a *) (rhs_h_matched_set: CP.spec_var list) (* is_folding *) pos
  : (Cformula.list_context * Prooftracer.proof) =
  let r = action in
  (* let prog = () in *)
  let r = action in
  let lhs_node = r.Context.match_res_lhs_node  in
  let rhs_node = r.Context.match_res_rhs_node  in
  let alias_set = r.Context.match_res_alias_set  in
  let () = y_tinfo_hp (add_str "infer_fold(lhs)" !CF.print_h_formula) lhs_node in
  let () = y_tinfo_hp (add_str "infer_fold(rhs)" !CF.print_h_formula) rhs_node in
  let () = y_tinfo_hp (add_str "alias_set" !CP.print_svl) alias_set in
  let () = y_tinfo_hp (add_str "rhs_matched" !CP.print_svl) rhs_h_matched_set in
  let rhs_rest = r.Context.match_res_rhs_rest  in
  let rhs_inst = r.Context.match_res_compatible in
  (* WN:TODO: need to improve res_compatible so that it really indicate comparable ptrs *)
  (* it seems mostly empty for now *)
  (* see ex21d1b2e *)
  let () = Debug.tinfo_hprint (add_str  "fold:rhs_inst"  (pr_list (pr_pair !CP.print_sv !CP.print_sv))) rhs_inst no_pos in
  let is_succ_inst, n_estate, n_lhs_b = match lhs_node,rhs_node with
    | HRel (lhp,leargs,_),HRel (rhp,reargs,_) -> begin
        if CP.mem_svl rhp estate.es_infer_vars_hp_rel then
          match leargs, reargs with
          | er::rest1,_::rest2 -> begin
              let largs = (List.map CP.exp_to_sv rest1) in
              let rargs = (List.map CP.exp_to_sv rest2) in
              if rhs_inst != [] then
                let lhds, lhvs, _ = CF.get_hp_rel_bformula lhs_b in
                let is_succ, p = x_add gen_inst prog estate lhds lhvs rhs_inst in
                if not is_succ then
                  true, estate, lhs_b
                else
                  let mf = (MCP.mix_of_pure p) in
                  (true,
                   {estate with CF.es_formula = CF.mkAnd_pure estate.CF.es_formula mf no_pos;
                                CF.es_infer_vars_hp_rel = estate.CF.es_infer_vars_hp_rel;
                   },
                   CF.mkAnd_base_pure lhs_b mf no_pos)
              else
                x_add do_inst prog estate lhs_b largs rargs []
            end
          | _ -> return_out_of_inst estate lhs_b []
        else
          return_out_of_inst estate lhs_b []
      end
    | _ -> return_out_of_inst estate lhs_b []
  in
  if not is_succ_inst then
    let err_msg = "infer_fold" in
    let conseq = Some (Base rhs_b) in
    (Errctx.mkFailCtx_may ~conseq:conseq (x_loc^"Can not inst") err_msg estate pos,NoAlias)
  else
    let () = Debug.ninfo_hprint (add_str  "n_estate.es_formula" !CF.print_formula) n_estate.es_formula no_pos in
    pm_aux n_estate n_lhs_b (Context.M_infer_heap (2, lhs_node, rhs_node,rhs_rest))


let infer_collect_hp_rel_empty_rhs prog (es0:entail_state) lhs_b (* rhs0 *) mix_rf pos =
  (*********INTERNAL**********)
  let get_eqset puref =
    let (subs,_) = CP.get_all_vv_eqs puref in
    let eqset = CP.EMapSV.build_eset subs in
    eqset
  in
  if CF.isStrictConstTrue_wo_flow es0.CF.es_formula then (false, es0, [], lhs_b) else
    let es_cond_path = CF.get_es_cond_path es0 in
    (* type: CF.formula_base -> *)
    (*   CF.formula_base -> *)
    (*   (Sautil.CP.spec_var * Sautil.CP.spec_var) list -> *)
    (*   (Sautil.CP.spec_var * Sautil.CP.spec_var) list -> *)
    (*   CF.h_formula_data list -> *)
    (*   Sautil.CF.h_formula_view list -> *)
    (*   (Sautil.CF.CP.spec_var * CP.exp list * 'a) list -> *)
    (*   CP.spec_var * CF.CP.spec_var list -> CF.hprel option *)
    let generate_constrs lhs_b rhs_b leqs reqs hds hvs lhras (hp,args)=
      (* WN : Why did this simplify_lhs_rhs has so many parameters? *)
      let (new_lhs_b,new_rhs_b) = x_add simplify_lhs_rhs prog 0 es0 lhs_b rhs_b (CF.HEmp) leqs reqs hds hvs lhras []
          [(hp,args)] [] [] [] in
      let lhs0 = (CF.Base new_lhs_b) in
      let () = y_tinfo_hp (add_str "lhs0" !CF.print_formula) lhs0 in
      (* WN : Why do we remove !=null? *)
      let lhs = (* CF.remove_neqNull_svl args *) lhs0 in
      (* let () = x_tinfo_hp (add_str "lhs0" !CF.print_formula) lhs0 no_pos in *)
      (* WN : Why do we extract hrel_head and then not use it? *)
      (* let extr_hd = x_add_1 CF.extract_hrel_head lhs in *)
      let extr_ans = x_add_1 CF.extract_hrel_head_list lhs in
      let pr_hr = pr_list (pr_triple !CP.print_sv (pr_list !CP.print_exp) !CP.print_formula) in
      let pr6 = pr_option (pr_pair pr_hr !CF.print_formula) in
      let () = x_tinfo_hp (add_str "extr_ans(list)" pr6) extr_ans no_pos in
      (* let () = x_tinfo_hp (add_str "extr_hd" (pr_option !CP.print_sv)) extr_hd no_pos in *)
      let rhs_f = (CF.Base new_rhs_b) in
      let () = x_tinfo_hp (add_str "lhs(after)" !CF.print_formula) lhs no_pos in
      let () = x_tinfo_hp (add_str "rhs" !CF.print_formula) rhs_f no_pos in
      let () = x_tinfo_hp (add_str "(hp,args)"  (pr_pair !CP.print_sv !CP.print_svl)) (hp,args) no_pos in
      let ( _,lmf,_,_,_,_) = CF.split_components lhs in
      let leqNulls = CF.find_close (MCP.get_null_ptrs lmf) leqs in
      let ass_guard = x_add find_guard prog hds leqs leqNulls [(hp,CP.diff_svl args leqNulls)] [] in
      let hprel_lst = match extr_ans with
        | None -> []
        | Some (lst,f) ->
          List.map (fun (hp,args,p) ->
              let knd = CP.RelAssume [hp] in
              let args2 = List.map (fun e -> 
                  match e with CP.Var (sv,_) -> sv
                             | _ -> failwith "Expecting vars only for hp_rel args") args in
              (* need to form new lhs from pure *)
              let new_h = CF.HRel (hp,args,no_pos) in 
              let lhs = CF.repl_heap_formula new_h lhs in
              let () = x_tinfo_pp "TODO : pure formula should be assumption filtered" no_pos in
              let lhs = CF.repl_pure_formula p lhs in
              let grd = x_add check_guard es0 ass_guard lhs_b new_lhs_b new_rhs_b pos in
              let hprel_ass = CF.mkHprel knd [] [] args2 lhs grd rhs_f es_cond_path in
              ((hp,args2,new_rhs_b.CF.formula_base_pure),hprel_ass)
            ) lst 
      in
      let () = x_tinfo_hp (add_str "hprel_lst"  (pr_list (pr_pair pr_none Cprinter.string_of_hprel_short))) hprel_lst no_pos in
      if  extr_ans (* extr_hd *) != None then
        (* let knd = CP.RelAssume [hp] in *)
        (* let hprel_ass = CF.mkHprel knd [] [] args lhs None rhs_f es_cond_path in *)
        (* let () = x_tinfo_hp (add_str "hprel_ass"  Cprinter.string_of_hprel_short) hprel_ass no_pos in *)
        (* (Some hprel_ass) *)
        Some hprel_lst
      else None
    in
    let generate_constrs lhs_b rhs_b leqs reqs hds hvs lhras p =
      let pr1 = Cprinter.string_of_formula_base in
      let pr2 = pr_list (fun (_, hpr) -> Cprinter.string_of_hprel_short hpr) in
      Debug.no_3 "generate_constrs" pr1 pr1 (pr_pair !CP.print_sv !CP.print_svl) (pr_option pr2)
        (fun _ _ _ -> generate_constrs lhs_b rhs_b leqs reqs hds hvs lhras p) lhs_b rhs_b p
    in
    let lhs0 = es0.CF.es_formula in
    (**********END INTERNAL***********)
    (*for debugging*)
    (* DD.info_hprint (add_str  ("  es: " ^ (Cprinter.string_of_formula es.CF.es_formula)) pos; *)
    let () = x_tinfo_hp (add_str  "es_infer_vars_hp_rel " !CP.print_svl) es0.es_infer_vars_hp_rel no_pos in
    let () = x_tinfo_hp (add_str  "es_infer_vars " !CP.print_svl) es0.es_infer_vars no_pos in
    let () = x_tinfo_hp (add_str  "es_infer_vars_rel " !CP.print_svl) es0.es_infer_vars_rel no_pos in
    let () = x_tinfo_hp (add_str  "es_infer_vars_sel_hp_rel " !CP.print_svl) es0.es_infer_vars_sel_hp_rel no_pos in
    (*end for debugging*)
    let pk =  try
        let ls = proving_kind# get_stk in
        match ls with
        | [] -> PK_Unknown
        | x::_ -> x
      with _ ->
        PK_Unknown in
    if no_infer_hp_rel es0 (* || MCP.isTrivMTerm mix_rf *) || ( pk != PK_POST && not (check_is_classic ())) then
      (false, es0, [], lhs_b)
    else
      let ivs = es0.es_infer_vars_hp_rel in
      (*check whether LHS/RHS contains hp_rel*)
      (*ll-del-1*)
      let lhrs = CF.get_hp_rel_name_formula lhs0 in
      if CP.intersect ivs (lhrs) = [] then
        begin
          (* DD.info_pprint ">>>>>> infer_hp_rel <<<<<<" pos; *)
          let () = x_tinfo_pp " no hp_rel found" pos in
          (false,es0,[], lhs_b)
        end
      else
        begin
          (* let pr = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
          let () = DD.ninfo_zprint (lazy (("  es0.CF.es_evars: " ^ (!CP.print_svl  es0.CF.es_evars)))) no_pos in
          (*which pointers are defined and which arguments of data nodes are pointer*)let lhs_b0 = match lhs0 with
            | Base fb -> fb
            | _ -> report_error pos "Infer.infer_collect_hp_rel_empty_rhs: impossible"
          in
          let ( _,mix_lf,_,_,_,_) = CF.split_components lhs0 in
          let l_emap0 = get_eqset (MCP.pure_of_mix mix_lf) in
          let r_emap0 = get_eqset (MCP.pure_of_mix mix_rf) in
          (* let () = DD.ninfo_hprint (add_str "   sst0: " pr) (sst0) pos in *)
          let _ =
            x_tinfo_pp ">>>>>> infer_hp_rel <<<<<<" pos;
            x_tinfo_hp (add_str  "  lhs " Cprinter.string_of_formula) lhs0 pos;
            x_tinfo_hp (add_str  "  classic " string_of_bool) (check_is_classic ()) pos
          in
          (*TOFIX: detect HEmp or HTrue *)
          let rhs_b0a = formula_base_of_heap (CF.HEmp) pos in
          let rhs_b0 = {rhs_b0a with formula_base_pure = mix_rf} in
          (* let rhs_htrue_b0 = formula_base_of_heap (CF.HTrue) pos in *)
          (********** BASIC INFO LHS, RHS **********)
          let l_hpargs = CF.get_HRels lhs_b0.CF.formula_base_heap in
          let l_non_infer_hps = CP.diff_svl lhrs ivs in
          (**smart subst**)
          let leqs0 = (MCP.ptr_equations_without_null mix_lf) in
          let post_hps,prog_vars =
            get_prog_vars es0.CF.es_infer_vars_sel_hp_rel rhs_b0.CF.formula_base_heap pk in
          let r_eqsetmap = CP.EMapSV.build_eset es0.CF.es_rhs_eqset in
          let lhs_b1, rhs_b1, subst_prog_vars, smart_sst = Cfutil.smart_subst_new lhs_b0 rhs_b0 (l_hpargs)
              l_emap0 r_emap0 r_eqsetmap [] (prog_vars@es0.es_infer_vars)
          in
          let () = y_tinfo_hp (add_str "lhs_b0" (fun b -> !CF.print_formula (CF.Base b))) lhs_b0 in
          let () = y_tinfo_hp (add_str "lhs_b1" (fun b -> !CF.print_formula (CF.Base b))) lhs_b1 in
          (* let lhs_b1 = Sautil.smart_subst_lhs lhs0 l_hpargs leqs0 es0.es_infer_vars in *)
          (* let rhs_b1 = rhs_b0 in *)
          let lhs_h = lhs_b1.CF.formula_base_heap in
          let ( _,mix_lf1,_,_,_,_) = CF.split_components (CF.Base lhs_b1) in
          let ( _,mix_rf1,_,_,_,_) = CF.split_components (CF.Base rhs_b1) in
          let leqs1 = (MCP.ptr_equations_without_null mix_lf1) in
          let reqs1 = (MCP.ptr_equations_without_null mix_rf1) in
          (********** END BASIC INFO LHS, RHS **********)
          let tmp = CF.get_HRels lhs_b1.CF.formula_base_heap in
          let pr_hp_lst = pr_list (pr_pair !CP.print_sv !CP.print_svl)in
          let () = x_tinfo_hp (add_str "tmp" pr_hp_lst) tmp no_pos in
          let () = x_tinfo_hp (add_str "ivs" !CP.print_svl) ivs no_pos in
          let sel_hprels = List.filter (fun (hp,_) -> CP.mem_svl hp ivs) tmp  in
          if sel_hprels = [] then
            (false, es0, [], lhs_b)
          else
            let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lhs_b1 in
            let leqNulls = MCP.get_null_ptrs mix_lf1 in
            let sel_hpargs, hprel_ass0, abd_mixs = List.fold_left (fun (ls1,ls2,ls3) (hp,args) ->
                let rhs_b2 =
                  (* if (rhs0 = CF.HTrue && List.exists (fun sv -> not (CP.mem_svl sv leqNulls)) args) then *)
                  (* (\* hp /\ p ==> htrue *\) rhs_htrue_b0 *)
                  (* else (\* hp /\ p ==> emp *\) *) rhs_b1
                in
                let r_opt = x_add generate_constrs lhs_b1 rhs_b2 leqs1 reqs1 lhds lhvs lhrs (hp,args) in
                match r_opt with
                | Some lst ->
                  let (hp_arg_lst_pure,ass_lst) = List.split lst in
                  let hp_arg_lst, abd_mps = List.fold_left (fun (ls1,ls2) (hp,args,mf) -> ls1@[(hp,args)],ls2@[mf]) ([],[]) hp_arg_lst_pure in
                  (ls1@hp_arg_lst (* [(hp,args)] *),ls2@ass_lst(* [ass] *), ls3@abd_mps)
                | None -> (ls1,ls2,ls3)
              ) ([],[],[]) sel_hprels in
            let ex_ass = (Infer.rel_ass_stk # get_stk) in
            let hprel_ass = Gen.BList.difference_eq Sautil.constr_cmp hprel_ass0 ex_ass in
            let () = y_tinfo_hp (add_str "hprel_ass0" (pr_list_ln Cprinter.string_of_hprel_short)) hprel_ass0 in
            let () = y_tinfo_hp (add_str "hprel_ass" (pr_list_ln Cprinter.string_of_hprel_short)) hprel_ass in
            let () = x_tinfo_hp (add_str "sel_hpargs" pr_hp_lst) sel_hpargs no_pos in
            if sel_hpargs = [] || hprel_ass = [] then (false,es0,[], lhs_b) else
              (*update residue*)
              let reqs0 = (MCP.ptr_equations_without_null mix_rf) in
              let empty_eqset = CP.EMapSV.mkEmpty in
              let all_aset = CP.add_equiv_list_eqs empty_eqset (leqs0@reqs0@es0.CF.es_rhs_eqset) in
              let sel_hpargs2 = List.map (fun (hp,args) -> (hp, CP.find_eq_closure all_aset args)) sel_hpargs in
              let nhf = CF.drop_data_view_hpargs_nodes_hf lhs_b0.CF.formula_base_heap CF.select_dnode CF.select_vnode Sautil.select_subsumehpargs [] [] sel_hpargs2 in
              let abd_ps = List.fold_left (fun acc mx ->
                  let ps = CP.list_of_conjs (MCP.pure_of_mix mx) in
                  acc@ps
              ) [] abd_mixs in
              let abd_ps1 = CP.remove_redundant_helper abd_ps [] in
              let abd_mf = MCP.mix_of_pure (CP.conj_of_list abd_ps1 no_pos) in
              let () = x_tinfo_hp (add_str "abd_mf" Cprinter.string_of_mix_formula) abd_mf no_pos in
              let new_es_formula = CF.Base {lhs_b0 with
                  CF.formula_base_pure = MCP.merge_mems lhs_b0.CF.formula_base_pure abd_mf true;
                  CF.formula_base_heap = nhf} in
              let es1 = {es0 with CF.es_formula = new_es_formula} in
              let n_lhs_b = {lhs_b with CF.formula_base_pure = MCP.merge_mems lhs_b.CF.formula_base_pure abd_mf true;} in
              (true, es1, hprel_ass, n_lhs_b)
        end


let infer_collect_hp_rel_empty_rhs i prog (es:entail_state) lhs_b (* rhs0 *) rhs_p pos =
  let pr1 =  Cprinter.string_of_estate_infer_hp (* Cprinter.string_of_formula *) in
  let pr2 = Cprinter.string_of_mix_formula in
  let pr3 =  (pr_quad (add_str "Res" string_of_bool) (add_str "Sel HP" Cprinter.string_of_estate_infer_hp)
      (add_str "Inferred Relations" (pr_list_ln Cprinter.string_of_hprel_short))
      (add_str "lhs base" Cprinter.string_of_formula_base)
  ) in
  let pr4 = Cprinter.string_of_h_formula in
  Debug.no_2_num i "infer_collect_hp_rel_empty_rhs" (add_str "estate" pr1) (* pr4 *) (add_str "rhs_p" pr2) pr3
    ( fun _ _ -> infer_collect_hp_rel_empty_rhs prog es lhs_b (* rhs0 *) rhs_p pos) es(* .CF.es_formula *) (* rhs0 *) rhs_p


let infer_collect_hp_rel_fold prog iact (es0:entail_state) lhs_node rhs_node rhs_rest (rhs_h_matched_set:CP.spec_var list) lhs_b1 rhs_b1 pos =
  (*********************INTERNAL*********************)
  (******************************************)
  let get_ptrs_ni hf = match hf with
    | CF.ViewNode {CF.h_formula_view_arguments = args}
    | CF.DataNode {CF.h_formula_data_arguments = args} ->
      List.fold_left (fun acc sv -> if CP.is_node_typ sv then acc@[(sv,I)] else
                       if es0.CF.es_infer_obj # is_pure_field_all then
                         acc@[(sv,NI)] else acc
                     ) [] args
    | CF.HRel (hp,eargs_w_r,_) -> begin
        match eargs_w_r with
        | er::_ ->
          let args = List.map CP.exp_to_sv eargs_w_r in
          let r = List.hd args in
          let i_args, ni_args = x_add Sautil.partition_hp_args prog hp args in
          let i_args_wo_r = List.filter (fun (sv,_) -> not(CP.eq_spec_var sv r)) i_args in
          let ni_args_wo_r = List.filter (fun (sv,_) -> not(CP.eq_spec_var sv r)) ni_args in
          (* let ni_args1 = List.fold_left (fun acc (sv,_) -> *)
          (*     if not (CP.is_node_typ sv) && not es0.CF.es_infer_obj # is_pure_field_all then acc else *)
          (*       acc@[(sv,NI)] *)
          (* ) [] ni_args in *)
          (* i_args_wo_r@ni_args_wo_r *)
          i_args@ni_args
        | _ -> []
      end
    | _ -> []
  in
  let get_root hf = match hf with
    | CF.ViewNode {CF.h_formula_view_node = sv}
    | CF.DataNode {CF.h_formula_data_node = sv} -> [(sv,NI)]
    | CF.HRel (hp,args (* eargs_w_r *),_) -> begin
        let args = List.map CP.exp_to_sv args in
        try
          [(Cast.cprog_obj # get_hp_root hp args,NI)]
        with _ -> 
          begin
            match args (* eargs_w_r *) with
            | r::_ ->
              [(r,NI)]
            | _ -> []
          end
      end
    | _ -> []
  in
  let get_undefined_back_ptrs lhs_node rhs_node=
    let lhs_ptrs = get_ptrs_ni lhs_node in
    let rhs_ptrs = get_ptrs_ni rhs_node in
    let root = get_root rhs_node in
    let res_lhs = Gen.BList.difference_eq (fun (sv1,_) (sv2,_) -> CP.eq_spec_var sv1 sv2) lhs_ptrs (root@rhs_ptrs) in
    let res_rhs = Gen.BList.difference_eq (fun (sv1,_) (sv2,_) -> CP.eq_spec_var sv1 sv2) rhs_ptrs (root@lhs_ptrs) in
    let i_svl, ni_svl = List.partition (fun (_,n) -> n=I) (res_lhs@res_rhs) in
    let pr = pr_list (pr_pair !CP.print_sv print_arg_kind) in
    let () = y_tinfo_hp (add_str "lhs_ptrs" pr) lhs_ptrs in
    let () = y_tinfo_hp (add_str "rhs_ptrs" pr) rhs_ptrs in
    let () = y_tinfo_hp (add_str "root" pr) root in
    let () = y_tinfo_hp (add_str "res_lhs" pr) res_lhs in
    let () = y_tinfo_hp (add_str "res_rhs" pr) res_rhs in
    i_svl@(root)@ni_svl
  in
  let get_undefined_back_ptrs lhs_node rhs_node =
    let pr = !CF.print_h_formula in
    let pr2 = pr_list (pr_pair !CP.print_sv print_arg_kind) in
    Debug.no_2 "get_undefined_back_ptrs" pr pr pr2 get_undefined_back_ptrs lhs_node rhs_node
  in
  let generate_rel es undef_lhs_ptrs =
    let (pred_hfs,new_hp_decls)=
      if undef_lhs_ptrs = [] || (List.filter (fun (_,n) -> n=I) undef_lhs_ptrs) = [] then
        [],[]
      else
        let (pred_hf,new_hp_rel) = x_add (Sautil.add_raw_hp_rel ~caller:x_loc) prog false false undef_lhs_ptrs pos in
        [pred_hf], [new_hp_rel]
    in
    let (lhf,lmf,_,_,_,_) = CF.split_components (CF.Base lhs_b1) in
    let lhds, lhvs, lhrs = CF.get_hp_rel_h_formula lhf in
    let leqs = (MCP.ptr_equations_without_null lmf) in
    let leqNulls = MCP.get_null_ptrs lmf in

    let es_cond_path = CF.get_es_cond_path es in
    let rhpargs = CF.get_HRels rhs_node in
    let rhps, r_args = List.fold_left (fun (acc1,acc2) (hp,args) -> acc1@[hp], acc2@args ) ([],[]) rhpargs in
    let knd = CP.RelAssume (CP.remove_dups_svl (rhps@new_hp_decls)) in
    let rel_lhs_hf = List.fold_left (fun acc pred_hf -> CF.mkStarH acc pred_hf pos) lhs_node pred_hfs in
    let rel_lhs_svl = (CP.remove_dups_svl (CF.h_fv rel_lhs_hf)) in
    let rel_lhs_pure = (CP.filter_var_new (MCP.pure_of_mix lhs_b1.CF.formula_base_pure) (if es.CF.es_infer_obj # is_pure_field_all then rel_lhs_svl else List.filter CP.is_node_typ rel_lhs_svl) ) in
    let rel_lhs_base = {lhs_b1 with formula_base_heap = rel_lhs_hf;
                                    formula_base_pure = MCP.mix_of_pure rel_lhs_pure} in
    let before_lhs = CF.Base rel_lhs_base in
    let before_rhs = CF.Base rhs_b1 in
    let rel_lhs,rel_rhs = if !Globals.allow_field_ann then
        (CF.formula_trans_heap_node hn_trans_field_mut before_lhs,
         CF.formula_trans_heap_node hn_trans_field_mut before_rhs)
      else
        (before_lhs,before_rhs)
    in
    let ass_guard = None in
    let hp_rel = CF.mkHprel knd [] [] (CF.get_ptrs lhs_node) rel_lhs ass_guard rel_rhs es_cond_path in

    let hp_rel_list0 =
      if !Globals.old_keep_triv_relass then [hp_rel]
      else List.filter (fun cs -> not (Sautil.is_trivial_constr ~en_arg:true cs)) [hp_rel] in
    let ex_ass = (Infer.rel_ass_stk # get_stk) in
    let hp_rel_list = Gen.BList.difference_eq Sautil.constr_cmp hp_rel_list0 ex_ass in
    (* postpone until heap_entail_after_sat *)
    if (!Globals.old_infer_hp_collect) then
      begin
        let () = Infer.rel_ass_stk # push_list (hp_rel_list) in
        let () = Log.current_hprel_ass_stk # push_list (hp_rel_list) in
        ()
      end;
    let n_ihvr = (es.CF.es_infer_vars_hp_rel@new_hp_decls) in
    let new_es = {es with CF.es_infer_vars_hp_rel = n_ihvr;
                 } in
    (* let hp_rel_list = CF.add_fold_flag hp_rel_list in *)
    let () = new_es.CF.es_infer_hp_rel # push_list_loc x_loc hp_rel_list in
    let heap_of_rel_lhs = match (CF.heap_of rel_lhs) with
      | [hf] -> hf
      | _ -> failwith "infer_collect_hp_rel_fold 2" in
    new_es, heap_of_rel_lhs
  in
  (******************************************)
  (*********************END*********************)
  (******************************************)
  let undef_lhs_ptrs_w_pure = x_add get_undefined_back_ptrs lhs_node rhs_node in
  let () = y_tinfo_hp (add_str "undef_lhs_ptrs_w_pure" ((pr_list (pr_pair !CP.print_sv print_arg_kind)))) undef_lhs_ptrs_w_pure in
  let undef_lhs_ptrs = List.filter (fun (sv,_) -> CP.is_node_typ sv) undef_lhs_ptrs_w_pure in
  (*generate constraint*)
  let new_es, heap_of_rel_lhs = generate_rel es0 undef_lhs_ptrs in
  (true, new_es, lhs_node, Some new_es.CF.es_heap, None, Some heap_of_rel_lhs)

let infer_collect_hp_rel_fold prog iact (es0:entail_state) lhs_node rhs_node rhs_rest (rhs_h_matched_set:CP.spec_var list) lhs_b1 rhs_b1 pos =
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 es = Cprinter.prtt_string_of_formula es.CF.es_formula in
  let pr4 = Cprinter.string_of_estate_infer_hp in
  let pr5 = pr_hexa string_of_bool pr4 (add_str "abd heap" Cprinter.string_of_h_formula)
    (pr_option Cprinter.string_of_h_formula) (pr_option pr2)
    (add_str "new rest" (pr_option Cprinter.string_of_h_formula))
  in
  Debug.no_5 "infer_collect_hp_rel_fold"
      (add_str "lhs_node" !CF.print_h_formula) (add_str "rhs_node" !CF.print_h_formula)
      (add_str "lhs" pr1) (add_str "rhs" pr1) (add_str "es" pr2) pr5
      ( fun _ _ _ _ _ -> infer_collect_hp_rel_fold prog iact (es0:entail_state) lhs_node rhs_node rhs_rest (rhs_h_matched_set:CP.spec_var list) lhs_b1 rhs_b1 pos)
      lhs_node rhs_node lhs_b1 rhs_b1 es0


(*
  type: Cast.prog_decl ->
  Cformula.entail_state ->
  Sautil.CF.h_formula ->
  CP.spec_var list ->
  CF.formula_base -> CF.formula_base -> VarGen.loc -> bool * CF.entail_st
*)
let infer_collect_hp_rel ?(caller="") prog iact (es0:entail_state) lhs_node rhs0 rhs_rest (rhs_h_matched_set:CP.spec_var list) lhs_b0 rhs_b0 pos =
  (*********INTERNAL**********)
  let exist_uncheck_rhs_null_ptrs l_emap r_emap l_null_ptrs r_null_ptrs rhs_args=
    let cl_lnull_ptrs = CP.find_eq_closure l_emap l_null_ptrs in
    let emap0 = CP.EMapSV.merge_eset l_emap r_emap in
    let cl_rnull_ptrs = CP.find_eq_closure emap0 r_null_ptrs in
    let () = Debug.ninfo_hprint (add_str  "cl_rnull_ptrs" !CP.print_svl) cl_rnull_ptrs no_pos in
    let rhs_uncheck_null_ptrs = CP.diff_svl cl_rnull_ptrs cl_lnull_ptrs in
    let () = Debug.ninfo_hprint (add_str  "rhs_uncheck_null_ptrs" !CP.print_svl) rhs_uncheck_null_ptrs no_pos in
    CP.intersect_svl rhs_uncheck_null_ptrs rhs_args != []
  in
  let exist_uncheck_rhs_null_ptrs l_emap r_emap l_null_ptrs r_null_ptrs rhs_args=
    let pr1 = !CP.print_svl in
    Debug.no_3 "exist_uncheck_rhs_null_ptrs" pr1 pr1 (add_str "SEL rhs args" pr1) string_of_bool
        (fun _ _ _ -> exist_uncheck_rhs_null_ptrs l_emap r_emap l_null_ptrs r_null_ptrs rhs_args)
        l_null_ptrs r_null_ptrs rhs_args
  in
  (**********END INTERNAL***********)
  if CF.isStrictConstTrue_wo_flow es0.CF.es_formula ||
     (CF.get_hp_rel_name_formula es0.CF.es_formula = [] && CF.get_hp_rel_name_h_formula rhs0 = [])
  then (false, es0, rhs0, None, None, None) else
    let pk = try if proving_kind # is_empty then PK_Unknown else proving_kind#top with _ -> PK_Unknown in
    (*for debugging*)
    (* DD.info_hprint (add_str  ("  es: " ^ (Cprinter.string_of_formula es.CF.es_formula)) pos; *)
    let () = Debug.ninfo_hprint (add_str  "es_infer_vars_hp_rel " !CP.print_svl) es0.es_infer_vars_hp_rel no_pos in
    let () = Debug.ninfo_hprint (add_str  "es_infer_vars " !CP.print_svl) es0.es_infer_vars no_pos in
    let () = Debug.ninfo_hprint (add_str  "es_infer_vars_sel_hp_rel " !CP.print_svl) es0.es_infer_vars_sel_hp_rel no_pos in
    (*end for debugging*)
    if no_infer_hp_rel es0 then
      constant_checking prog rhs0 lhs_b0 rhs_b0 es0
    else
      let ivs = es0.es_infer_vars_hp_rel in
      (*check whether LHS/RHS contains hp_rel*)
      (*ll-del-1*)
      let lhrs = CF.get_hp_rel_name_bformula lhs_b0 in
      let rhrs = CF.get_hp_rel_name_bformula rhs_b0 in
      if CP.intersect ivs (lhrs@rhrs) = [] then
        begin
          (* DD.info_pprint ">>>>>> infer_hp_rel <<<<<<" pos; *)
          let () = x_tinfo_pp " no hp_rel found" pos in
          constant_checking prog rhs0 lhs_b0 rhs_b0 es0
          (* (false,es) *)
        end
      else
        begin
          let pr = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
          let () = DD.ninfo_zprint (lazy (("  es0.CF.es_evars: " ^ (!CP.print_svl  es0.CF.es_evars)))) no_pos in
          (* freshing rhs if rhs is a data/view node. renaming: bug-app3.slk*)
          let rhs0b, rhs_b, es,  r_sst = match rhs0 with
            |  CF.DataNode _
            | CF.ViewNode _  ->
              let v_lhs = (CF.fv (CF.Base lhs_b0)) in
              let v_rhs = (CF.h_fv (rhs0)) in
              let v_hp_rel = es0.CF.es_infer_vars_hp_rel in
              (* let pr = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
              let () = DD.ninfo_hprint (add_str "   es0.CF.es_rhs_eqset: " pr) (es0.CF.es_rhs_eqset) pos in
              let r_evars0, l_ante_evars0  = List.split es0.CF.es_rhs_eqset in
              let r_evars, l_ante_evars = if !Globals.en_slc_ps then l_ante_evars0,r_evars0 else r_evars0, l_ante_evars0 in
              (* let r_evars = List.map fst es0.CF.es_rhs_eqset in *)
              let evars_match_lhs,evars_nmatch_lhs  = List.partition (fun sv -> CP.mem_svl sv r_evars
                                                                     ) es0.CF.es_evars in
              (* let evars_nmatch_lhs = CP.diff_svl evars_nmatch_lhs es0.CF.es_gen_impl_vars in *)
              let () = DD.ninfo_zprint (lazy ((" evars_match_lhs: " ^ (!CP.print_svl evars_match_lhs)))) no_pos in
              let v_2_rename = List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.diff_svl v_rhs (v_lhs@v_hp_rel@
                                                                                                    es0.CF.es_evars  (*evars_match_lhs*)  )) in
              let fr_svl = CP.fresh_spec_vars v_2_rename in
              let sst0 = (List.combine v_2_rename fr_svl) in
              let fr_evars = CP.fresh_spec_vars evars_nmatch_lhs in
              let sst1 = List.combine evars_nmatch_lhs fr_evars in
              let sst = sst0@ es0.CF.es_rhs_eqset@sst1 in
              let () = DD.ninfo_hprint (add_str "   sst: " pr) (sst) pos in
              let rhs = CF.h_subst sst rhs0 in
              let rhs_b = CF.subst_b sst0 rhs_b0 in
              (rhs, rhs_b, es0, List.map (fun (sv1,sv2) -> (sv2,sv1)) sst)
            | _ -> (rhs0, rhs_b0, es0, [])
          in
          (* DD.info_pprint "  hp_rel found" pos; *)
          (*which pointers are defined and which arguments of data nodes are pointer*)
          let ( _,mix_lf,_,_,_,_) = CF.split_components (CF.Base lhs_b0) in
          let leqs = (MCP.ptr_equations_without_null mix_lf) in

          let l_emap0 = get_eqset (MCP.pure_of_mix mix_lf) in
          let (_,mix_rf0,_,_,_,_) = CF.split_components (CF.Base rhs_b0) in
          let reqs_orig = (MCP.ptr_equations_without_null mix_rf0) in

          let r_emap0 = get_eqset (MCP.pure_of_mix mix_rf0) in
          let r_eqsetmap0 = CP.EMapSV.build_eset es0.CF.es_rhs_eqset in

          (* let () = DD.ninfo_hprint (add_str "   sst0: " pr) (sst0) pos in *)
          let () = x_tinfo_zp (lazy (("  es.CF.es_evars: " ^ (!CP.print_svl  es.CF.es_evars)))) no_pos in
          let () = x_tinfo_hp (add_str "   es.CF.es_rhs_eqset: " pr) (es.CF.es_rhs_eqset) pos in
          (* let () = DD.ninfo_hprint (add_str "   reqs_orig: " pr)  reqs_orig pos in *)
          (* let rls1,rls2  = List.split es.CF.es_rhs_eqset in *)
          (* let n_rhs_eqset = List.combine (CP.subst_var_list sst0 rls1) (CP.subst_var_list sst0 rls2) *)
          (* (MCP.ptr_equations_without_null mix_rf)  in *)
          let (_,mix_rf,_,_,_,_) = CF.split_components (CF.Base rhs_b) in
          let r_emap = get_eqset (MCP.pure_of_mix mix_rf) in
          let r_eqsetmap = CP.EMapSV.build_eset es.CF.es_rhs_eqset in

          (* let reqs = Gen.BList.remove_dups_eq (fun (sv1,sv2) (sv3, sv4) -> CP.eq_spec_var sv1 sv3 && CP.eq_spec_var sv2 sv4) n_rhs_eqset@reqs_orig in *)
          let _ =
            x_tinfo_pp ">>>>>> infer_hp_rel <<<<<<" pos;
            x_tinfo_hp (add_str  "  es_heap " Cprinter.string_of_h_formula) es.CF.es_heap pos;
            (* x_tinfo_hp (add_str  "  es_history " ^ (pr_list_ln Cprinter.string_of_h_formula)) es.CF.es_history pos; *)
            x_tinfo_hp (add_str  "  lhs " Cprinter.string_of_formula_base) lhs_b0 pos;
            (* x_tinfo_hp (add_str  "  rhs " Cprinter.prtt_string_of_h_formula) rhs0 pos; *)
            x_tinfo_hp (add_str  "  rhs_rest " Cprinter.prtt_string_of_h_formula) rhs_rest pos;
            x_tinfo_hp (add_str  "  unmatch " Cprinter.string_of_h_formula) rhs0b pos;
            x_tinfo_hp (add_str  "  classic " string_of_bool) (check_is_classic ()) pos
          in
          let post_hps,prog_vars =
            get_prog_vars es.CF.es_infer_vars_sel_hp_rel rhs0b pk in
          (********** BASIC INFO LHS, RHS **********)
          let l_hpargs = CF.get_HRels lhs_b0.CF.formula_base_heap in
          let l_non_infer_hps = CP.diff_svl lhrs ivs in
          let r_hpargs = CF.get_HRels rhs0b in
          (**smart subst**)
          (* let n_es_evars = CP.subst_var_list sst0 es.CF.es_evars in *)
          let lhs_b1, rhs_b1, subst_prog_vars, smart_sst = Cfutil.smart_subst_new lhs_b0 (formula_base_of_heap rhs0b pos) (l_hpargs@r_hpargs)
              l_emap0 r_emap r_eqsetmap [] (prog_vars@es.es_infer_vars)
          in
          (* let lhs_b1, rhs_b1, subst_prog_vars = Sautil.smart_subst lhs_b0 (formula_base_of_heap rhs pos) (l_hpargs@r_hpargs) *)
          (*   (leqs@reqs) (List.filter (fun (sv1,sv2) -> CP.intersect_svl [sv1;sv2] n_es_evars <> []) reqs) *)
          (*   [] (prog_vars@es.es_infer_vars) *)
          (* in *)
          let lhs_h = lhs_b1.CF.formula_base_heap in
          let rhs = rhs_b1.CF.formula_base_heap in
          let mis_nodes =  match rhs with
            | DataNode n -> [n.h_formula_data_node]
            | ViewNode n -> [n.h_formula_view_node]
            | HRel (_,eargs,_) -> CP.remove_dups_svl (List.concat (List.map CP.afv eargs))
            | _ -> report_error pos "Expect a node or a hrel"
            (* CF.get_ptr_from_data_w_hrel *)
          in
          (* let () = x_tinfo_pp "parameters for detecting mis_match" pos in *)
          (* let () = x_tinfo_hp (add_str "mis_nodes" !print_svl) mis_nodes pos in *)
          (* let () = x_tinfo_hp (add_str "leqs" pr) leqs pos in *)
          (* let () = x_tinfo_hp (add_str "reqs" pr) reqs pos in *)
          (* let () = x_tinfo_hp (add_str "subs_prog_vars" !print_svl) subst_prog_vars pos in *)
          let fv_lhs = CF.fv (CF.Base lhs_b1) in
          let fv_rhs = CF.h_fv rhs in
          let () = x_tinfo_hp (add_str "fv_lhs" !print_svl) fv_lhs pos in
          let () = x_tinfo_hp (add_str "fv_rhs" !print_svl) fv_rhs pos in
          let es_cond_path = CF.get_es_cond_path es in
          if (CP.intersect fv_lhs fv_rhs) == [] then
            begin
              let () = Debug.ninfo_pprint ">>>>>> mismatch ptr is not a selective variable <<<<<<" pos in
              (*bugs/bug-classic-4a.slk: comment the following stuff*)
              let rhs_hps = (List.map fst r_hpargs) in
              if rhs_hps <> [] then
                let truef = (CF.mkTrue (CF.mkNormalFlow()) pos) in
                let lhs, new_es =
                  if false (* (check_is_classic ()) *) then
                    let rest_args = CF.h_fv rhs_rest in
                    let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lhs_b1 in
                    let helper (hp,eargs,_)=(hp,List.concat (List.map CP.afv eargs)) in
                    let ls_lhp_args = (List.map helper lhrs) in
                    let ass_lhs1, lselected_hpargs1 =
                      if rest_args = [] then ( lhs_b1, ls_lhp_args) else
                        let lselected_hpargs0 =  List.filter (fun (_, args) ->
                            CP.intersect_svl args rest_args = []) ls_lhp_args
                        in
                        let ass_lhs0 = Sautil.keep_data_view_hrel_nodes_fb prog lhs_b1 lhds lhvs (CP.diff_svl (CF.fv (CF.Base lhs_b1))
                                                                                                    rest_args) lselected_hpargs0
                        in (ass_lhs0, lselected_hpargs0)
                    in
                    let l_aset = CP.EMapSV.mkEmpty in
                    let all_aset = CP.add_equiv_list_eqs l_aset (leqs@reqs_orig@es.CF.es_rhs_eqset) in
                    let new_es,_ = x_add update_es prog es lhds lhvs lhs_b1 rhs rhs_rest [] [] lselected_hpargs1
                        [] leqs all_aset [] post_hps [] [] pos in
                    (CF.Base ass_lhs1, new_es)
                  else
                    (truef, es)
                in
                let knd = CP.RelAssume rhs_hps in
                let lhs = lhs in
                let rhs = CF.Base rhs_b1 in
                let hprel_ass = [CF.mkHprel_1 knd lhs None rhs es_cond_path] in
                let () = y_tinfo_hp (add_str "hprel_ass" (pr_list Cprinter.string_of_hprel_short)) hprel_ass in
                (* postpone until heap_entail_after_sat? *)
                if !Globals.old_infer_hp_collect then 
                  begin
                    x_tinfo_hp (add_str "HPRelInferred" (pr_list_ln Cprinter.string_of_hprel_short))  hprel_ass pos;
                    let () = Infer.rel_ass_stk # push_list hprel_ass in
                    let () = Log.current_hprel_ass_stk # push_list hprel_ass in
                    ()
                  end;
                let new_es1 = {new_es with (* CF.es_infer_hp_rel = es.CF.es_infer_hp_rel # push_list  hprel_ass; *)
                    CF.es_infer_vars_sel_post_hp_rel = (es.CF.es_infer_vars_sel_post_hp_rel @ post_hps);} in
                let () = new_es1.CF.es_infer_hp_rel # push_list_loc x_loc hprel_ass in
                (true, new_es1, rhs0, None, None, None)
              else
                constant_checking prog rhs lhs_b0 rhs_b es
            end
          else
            let ( _,mix_lf1,_,_,_,_) = CF.split_components (CF.Base lhs_b1) in
            let leqs1 = (MCP.ptr_equations_without_null mix_lf1) in
            let reqs1 = [] in
            (********** END BASIC INFO LHS, RHS **********)
            if !Globals.infer_back_ptr && iact = 2 then
              let lhs_node1 = CF.h_subst smart_sst lhs_node in
              infer_collect_hp_rel_fold prog iact es lhs_node1 rhs rhs_rest rhs_h_matched_set lhs_b1 rhs_b1 pos
            else
            let is_found_mis, ls_unknown_ptrs,(* hds,hvs,lhras,rhras, *)eqNull,
                lselected_hpargs,rselected_hpargs,defined_hps, unk_svl,unk_pure,unk_map,new_lhs_hps,
              (* lvi_ni_svl, *) (* classic_nodes, *)
              ass_guard =
              x_add find_undefined_selective_pointers prog es lhs_b1 mix_lf1 lhs_node rhs rhs_rest
                (* (rhs_h_matched_set) *) leqs1 reqs1 pos (* es.CF.es_infer_hp_unk_map *) post_hps subst_prog_vars in
            let flag1 = (List.exists (fun (hp,args1) -> if not (CP.mem_svl hp ivs) then
                                         not (List.exists (fun (_,args2) -> x_add CP.sub_spec_var_list (* eq_spec_var_order_list *) args1 args2) lselected_hpargs)
                                       else false
                                     ) rselected_hpargs (*incr/ex15c(1)*) ) in
            let flag2 = exist_uncheck_rhs_null_ptrs l_emap0 (CP.EMapSV.merge_eset r_emap r_eqsetmap) 
                (MCP.get_null_ptrs mix_lf1) (MCP.get_null_ptrs mix_rf)
                (List.fold_left (fun acc (_, args) -> acc@args) [] rselected_hpargs) in
            let flag3 = not is_found_mis in
            let prb = string_of_bool in
            let () = y_tinfo_hp (add_str "mis-matched" (pr_triple prb prb prb)) (flag1,flag2,flag3) in
            if flag3 || flag1 || flag2 then
              let () = x_tinfo_hp (add_str ">>>>>> mismatch ptr" pr_id) ((Cprinter.prtt_string_of_h_formula rhs) ^" is not found (or inst) in the lhs <<<<<<") pos in
              (false, es, rhs, None, None, None)
            else
              (* let rhs_b1 = CF.formula_base_of_heap rhs pos in *)
              let lhs_new_hfs,lhs_new_hpargs = List.split new_lhs_hps in
              (*remove all non_infer_hps*)
              let lselected_hpargs1 = List.filter (fun (hp,_) -> not (CP.mem_svl hp l_non_infer_hps)) (lselected_hpargs) in
              let lselected_hpargs2 = lselected_hpargs1@lhs_new_hpargs in
              let defined_hps1 =  List.filter (fun (hp,_,_,_) -> not (CP.mem_svl hp l_non_infer_hps)) defined_hps in
              let n_lhs_b1 = match lhs_new_hfs with
                | [] -> lhs_b1
                | hf::rest -> CF.mkAnd_fb_hf lhs_b1 (List.fold_left(fun a c-> mkStarH a c pos ) hf rest) pos
              in
              let r_new_hfs,ass_lhs_b, m,rvhp_rels, r_post_hps,hp_rel_list,n_es_heap_opt, ass_lhs =
                x_add (generate_constraints ~caller:(x_loc ^ ":" ^ caller)) prog iact es rhs n_lhs_b1 ass_guard rhs_b1 rhs_rest
                  defined_hps1 ls_unknown_ptrs unk_pure unk_svl
                    lselected_hpargs2 rselected_hpargs
                  (* hds hvs lhras *) lhrs (* rhras *) rhrs leqs1 reqs1 eqNull subst_prog_vars
                    (* lvi_ni_svl *) (* classic_nodes *) pos in
              (* generate assumption for memory error *)
              let oerror_es = generate_error_constraints prog es ass_lhs rhs
                  (List.map fst lselected_hpargs2) es_cond_path pos in
              (*update residue*)
              (*the new hprel generate may be from post-preds, update them*)
              let new_post_hps = post_hps@r_post_hps in
              (*use leqs not leqs1: since res is not substed*)
              let () = DD.ninfo_zprint (lazy ((" leqs: " ^ (let pr = pr_list(pr_pair !CP.print_sv !CP.print_sv) in pr leqs)))) no_pos in
              let () = DD.ninfo_zprint (lazy ((" reqs_orig: " ^ (let pr = pr_list(pr_pair !CP.print_sv !CP.print_sv) in pr reqs_orig)))) no_pos in
              (*if a hpargs is either NI or cont*)
              (* let lselected_hpargs3 = lselected_hpargs2 in *)
              (* let l_aset = CP.EMapSV.mkEmpty in *)
              (* let all_aset = CP.add_equiv_list_eqs l_aset (leqs@reqs_orig@n_rhs_eqset) in *)
              let all_aset = CP.EMapSV.merge_eset (CP.EMapSV.merge_eset l_emap0 r_emap0) r_eqsetmap0 in
              let lhds, lhvs, _ = CF.get_hp_rel_bformula lhs_b1 in
              let rhds, rhvs, _ = CF.get_hp_rel_h_formula rhs in
              let hds = lhds@rhds in
              let hvs = lhvs@rhvs in
              let () = y_tinfo_hp (add_str "hp_rel_list" (pr_list Cprinter.string_of_hprel_short)) hp_rel_list in
              let new_es, new_lhs = x_add update_es prog es hds hvs ass_lhs_b rhs rhs_rest r_new_hfs defined_hps1 lselected_hpargs2
                  rvhp_rels (leqs) all_aset m new_post_hps unk_map hp_rel_list pos in
              let n_es_heap = match rhs with
                | CF.HRel _ ->  n_es_heap_opt
                | _ -> None
              in
              (true, new_es, new_lhs, n_es_heap, oerror_es, None)
        end
(*
  output:
   - res = true: succ
   - new_estate: new entailment state
   - n_lhs: if rhs_node is a data/heape ie. x::node<_> (and lhs_node is a unknown pred i.e. H(x)),
       this abduction method (infer_collect_hp_rel) genrates an abduction relation
         - H(x) ==> x::node<_>
       and implicitly unfolds H(x) into the entailment state by
        (i) returning (n_lhs = x::node<_>,  n_es_heap_opt = None)
        (ii) matching n_lhs and rhs_node
   - n_es_heap_opt: to do
   - oerror_es: for error inference
*)
let infer_collect_hp_rel ?(caller="") i prog iact (es:entail_state) lhs_node rhs rhs_rest (rhs_h_matched_set:CP.spec_var list) lhs_b rhs_b pos =
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 es = Cprinter.prtt_string_of_formula es.CF.es_formula in
  (* let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
  let pr4 = Cprinter.string_of_estate(*_infer_hp*) in
  let pr5 =  pr_hexa string_of_bool pr4 (add_str "abd heap" Cprinter.string_of_h_formula)
      (pr_option Cprinter.string_of_h_formula) (pr_option pr2)
      (add_str "new rest" (pr_option Cprinter.string_of_h_formula))
  in
  Debug.no_6_num i "infer_collect_hp_rel" (* pr2 *)
      (add_str "lhs_node" !CF.print_h_formula) (add_str "rhs_node" !CF.print_h_formula)
      (add_str "lhs" pr1) (add_str "rhs" pr1) (add_str "es" pr4) 
      (add_str "classic" string_of_bool) pr5
    ( fun _ _ _ _ _ _ -> infer_collect_hp_rel ~caller:caller prog iact es lhs_node rhs rhs_rest rhs_h_matched_set lhs_b rhs_b pos)
      (* es *) lhs_node rhs lhs_b rhs_b es (check_is_classic ())

(*
  assume
  - rhs node matching with rhs (body) of coersion
  - lhs_node is an unknown pred
*)
let infer_collect_hp_rel_unfold_lemma_guided prog iact estate lhs_node rhs_node rhs_rest rhs_h_matched_set
      lhs_b rhs_b conseq (lemma:Cast.coercion_decl option) pos =
  let default_ret () = estate in
  match lemma with
    | Some coer -> begin
        let coer_head_views = CF.get_views coer.Cast.coercion_head in
        let sel_head_views = List.filter (fun vn -> string_eq coer.Cast.coercion_head_view vn.CF.h_formula_view_name) coer_head_views in
        match rhs_node,sel_head_views with
          | CF.ViewNode rvn, [head_vn] -> begin
              let sst = List.combine (head_vn.CF.h_formula_view_node::head_vn.CF.h_formula_view_arguments)
                (rvn.CF.h_formula_view_node::rvn.CF.h_formula_view_arguments) in
              let coer_body_dns = CF.get_datas (CF.subst sst coer.Cast.coercion_body) in
              let self_body_dns = List.filter (fun dn -> CP.eq_spec_var rvn.CF.h_formula_view_node dn.CF.h_formula_data_node) coer_body_dns in
              match self_body_dns with
                | [self_body_dn] -> begin
                    let n_rhs_node = CF.DataNode (CF.fresh_data_arg self_body_dn) in
                    (* let iact = 2 in *)
                    let () = x_tinfo_hp (add_str  "n_rhs_node" Cprinter.string_of_h_formula) n_rhs_node  pos in
                    let () = x_tinfo_hp (add_str  "lhs_node" Cprinter.string_of_h_formula) lhs_node  pos in
                    let () = x_tinfo_hp (add_str  "rhs_rest" Cprinter.string_of_h_formula) rhs_rest  pos in
                    let () = x_tinfo_hp (add_str  "rhs_b" Cprinter.string_of_formula) (CF.Base rhs_b)  pos in
                    let () = x_tinfo_hp (add_str  "lhs_b" Cprinter.string_of_formula) (CF.Base lhs_b)  pos in
                    let (res,n_estate, n_lhs, n_es_heap_opt, oerror_es, rhs_rest_opt)=
                      x_add (infer_collect_hp_rel ~caller:x_loc) 3 prog iact estate lhs_node n_rhs_node rhs_rest rhs_h_matched_set
                          lhs_b rhs_b pos in
                    if res then
                       let () = x_tinfo_hp (add_str  "new estate" Cprinter.string_of_formula) n_estate.CF.es_formula  pos in
                       let () = x_tinfo_hp (add_str  "n lhs" Cprinter.string_of_h_formula) n_lhs  pos in
                       let n_estate1 = {n_estate with CF.es_formula = CF.mkStar_combine_heap n_estate.CF.es_formula n_lhs CF.Flow_combine pos} in
                       (n_estate1)
                    else
                      (estate)
                  end
                | _ -> default_ret ()
            end
          | _ ->  default_ret ()
      end
    | None -> default_ret ()

let infer_collect_hp_rel_unfold_lemma_guided prog iact es lhs_node rhs rhs_rest rhs_h_matched_set
      lhs_b rhs_b conseq lemma pos =
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 es = Cprinter.prtt_string_of_formula es.CF.es_formula in
  let pr4 = Cprinter.string_of_estate_infer_hp in
  let pr5 =  pr2 in
  Debug.no_7 "infer_collect_hp_rel_unfold_lemma_guided"
      (add_str "act" string_of_int) (add_str "lhs_node" !CF.print_h_formula) (add_str "rhs_node" !CF.print_h_formula)
      (add_str "lhs" pr1) (add_str "rhs" pr1) (add_str "es" pr2) (pr_option Cprinter.string_of_coercion) pr5
    ( fun _ _ _ _ _ _ _ -> infer_collect_hp_rel_unfold_lemma_guided prog iact es lhs_node rhs rhs_rest rhs_h_matched_set
        lhs_b rhs_b conseq lemma pos)
      iact lhs_node rhs lhs_b rhs_b es lemma


(*
  assume
  - lhs node matching with lhs of coersion
  - rhs_node is a unknown pred
*)
let infer_collect_hp_rel_fold_lemma_guided prog iact estate lhs_node rhs_node rhs_rest rhs_h_matched_set
      lhs_b rhs_b conseq (lemma:Cast.coercion_decl option) pos =
  match lemma with
    | Some coer -> begin
        let coer_head_views = CF.get_views coer.Cast.coercion_head in
        let sel_head_views = List.filter (fun vn -> string_eq coer.Cast.coercion_head_view vn.CF.h_formula_view_name) coer_head_views in
        match lhs_node,sel_head_views with
          | CF.ViewNode lvn, [head_vn] -> begin
              let sst = List.combine (head_vn.CF.h_formula_view_node::head_vn.CF.h_formula_view_arguments)
                (lvn.CF.h_formula_view_node::lvn.CF.h_formula_view_arguments) in
              let coer_body_dns = CF.get_datas (CF.subst sst coer.Cast.coercion_body) in
              let self_body_dns = List.filter (fun dn -> CP.eq_spec_var lvn.CF.h_formula_view_node dn.CF.h_formula_data_node) coer_body_dns in
              match self_body_dns with
                | [self_body_dn] -> begin
                    let n_lhs_node = CF.DataNode (CF.fresh_data_arg self_body_dn) in
                    (* let iact = 2 in *)
                    let () = x_tinfo_hp (add_str  "n_lhs_node" Cprinter.string_of_h_formula) n_lhs_node  pos in
                    let () = x_tinfo_hp (add_str  "rhs_node" Cprinter.string_of_h_formula) rhs_node  pos in
                    let () = x_tinfo_hp (add_str  "rhs_rest" Cprinter.string_of_h_formula) rhs_rest  pos in
                    let () = x_tinfo_hp (add_str  "rhs_b" Cprinter.string_of_formula) (CF.Base rhs_b)  pos in
                    let () = x_tinfo_hp (add_str  "lhs_b" Cprinter.string_of_formula) (CF.Base lhs_b)  pos in
                    let (res,n_estate, n_lhs, n_es_heap_opt, oerror_es, rhs_rest_opt)=
                      x_add (infer_collect_hp_rel ~caller:x_loc) 3 prog iact estate n_lhs_node rhs_node rhs_rest rhs_h_matched_set
                          lhs_b rhs_b pos in
                    if res then
                       let n_rhs_rest, n_rhs_node, n_conseq = match rhs_rest_opt with
                         | None -> rhs_rest,rhs_node, conseq
                         | Some hf ->
                               let rest_lhs_fold = CF.drop_hnodes_hf hf [self_body_dn.CF.h_formula_data_node] in
                               let n_conseq =  (Base {rhs_b with formula_base_heap = hf}) in
                               (CF.mkStarH rhs_rest rest_lhs_fold no_pos,n_lhs_node, n_conseq)
                       in
                       let n_rhs_b = {rhs_b with CF.formula_base_heap = n_lhs_node} in
                       let n_estate1 = match n_es_heap_opt with
                         | Some hf -> {n_estate with CF.es_heap = hf}
                         | None -> n_estate
                       in
                       (n_estate1,n_conseq,n_rhs_rest,n_rhs_node, n_rhs_b)
                    else
                      (estate,conseq,rhs_rest,rhs_node,rhs_b)
                  end
                | _ -> (estate,conseq,rhs_rest,rhs_node,rhs_b)
            end
          | _ ->  (estate,conseq,rhs_rest,rhs_node,rhs_b)
      end
    | None -> (estate,conseq,rhs_rest,rhs_node,rhs_b)

let infer_collect_hp_rel_fold_lemma_guided prog iact es lhs_node rhs rhs_rest rhs_h_matched_set
      lhs_b rhs_b conseq lemma pos =
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 es = Cprinter.prtt_string_of_formula es.CF.es_formula in
  let pr4 = Cprinter.string_of_estate_infer_hp in
  let pr5 =  pr_penta pr2 (add_str "conseq" Cprinter.string_of_formula)
    (add_str "rhs_rest" Cprinter.string_of_h_formula) (add_str "rhs_node" Cprinter.string_of_h_formula)
    pr1
  in
  Debug.no_7 "infer_collect_hp_rel_fold_lemma_guided"
      (add_str "act" string_of_int) (add_str "lhs_node" !CF.print_h_formula) (add_str "rhs_node" !CF.print_h_formula)
      (add_str "lhs" pr1) (add_str "rhs" pr1) (add_str "es" pr2) (pr_option Cprinter.string_of_coercion) pr5
    ( fun _ _ _ _ _ _ _ -> infer_collect_hp_rel_fold_lemma_guided prog iact es lhs_node rhs rhs_rest rhs_h_matched_set
        lhs_b rhs_b conseq lemma pos)
      iact lhs_node rhs lhs_b rhs_b es lemma

let collect_classic_assumption prog es lfb sel_hps infer_vars pos=
  let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lfb in
  let (_ ,mix_lf,_,_,_,_) = CF.split_components (CF.Base lfb) in
  let leqNulls = MCP.get_null_ptrs mix_lf in
  let leqs = (MCP.ptr_equations_without_null mix_lf) in
  let l_def_vs = leqNulls @ (List.map (fun hd -> hd.CF.h_formula_data_node) lhds)
                 @ (List.map (fun hv -> hv.CF.h_formula_view_node) lhvs) in
  let l_def_vs = CP.remove_dups_svl (CF.find_close l_def_vs (leqs)) in
  let helper (hp,eargs,_)=(hp,List.concat (List.map CP.afv eargs)) in
  let ls_lhp_args = (List.map helper lhrs) in
  let _, defined_preds,rems_hpargs,link_hps =
    List.fold_left (fun (lfb1, r_defined_preds, r_rems, r_link_hps) hpargs ->
        let n_lfb,def_hps, rem_hps, ls_link_hps=
          Sautil.find_well_defined_hp prog lhds lhvs []
            infer_vars [] hpargs (l_def_vs) lfb1 true pos
        in
        (n_lfb, r_defined_preds@def_hps, r_rems@rem_hps, r_link_hps@(snd (List.split ls_link_hps)))
      ) (lfb, [], [], []) ls_lhp_args
  in
  (* let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let () = Debug.info_hprint (add_str  " rems_hpargs" pr1) rems_hpargs no_pos in *)
  let truef = CF.mkTrue (CF.mkTrueFlow()) pos in
  let rem_defined= List.fold_left (fun ls (hp,args) ->
      if CP.mem_svl hp sel_hps then
        let hf = (CF.HRel (hp, List.map (fun x -> CP.mkVar x pos) args, pos)) in
        let p = CP.filter_var (MCP.pure_of_mix lfb.CF.formula_base_pure) args in
        let lhs_ass = CF.mkAnd_base_pure (CF.formula_base_of_heap hf pos)
            (MCP.mix_of_pure p) pos in
        let new_defined = (hp, args, lhs_ass, truef) in
        (ls@[new_defined])
      else ls
    ) [] rems_hpargs in
  let defined_preds0 = defined_preds@rem_defined in
  let new_constrs =
    match defined_preds0 with
    | [] -> []
    | _ -> let es_cond_path = CF.get_es_cond_path es in
      let defined_hprels = List.map (x_add Sautil.generate_hp_ass 1 [] es_cond_path) defined_preds0 in
      defined_hprels
  in
  (new_constrs, (List.map (fun (a, _, _,_) -> a) defined_preds0))

let infer_collect_hp_rel_classsic prog (es:entail_state) rhs pos =
  let () = Debug.ninfo_hprint (add_str  "es_infer_vars_hp_rel"  !CP.print_svl) es.es_infer_vars_hp_rel no_pos in
  let () = Debug.ninfo_hprint (add_str  "es_infer_vars" !CP.print_svl)  es.es_infer_vars no_pos in
  let () = Debug.ninfo_hprint (add_str  "es_infer_vars_sel_hp_rel" !CP.print_svl)  es.es_infer_vars_sel_hp_rel no_pos in
  if rhs<>HEmp || no_infer_hp_rel es then
    let () = Debug.ninfo_pprint ("no_infer_hp: " ) no_pos in
    (false, es)
  else
    let lhs = es.CF.es_formula in
    let ivs = es.es_infer_vars_hp_rel in
    (*check whether LHS contains hp_rel*)
    let lhrs = CF.get_hp_rel_name_formula lhs in
    (* Andreea: is below check ok? *)
    if CP.intersect ivs lhrs = [] then
      (false,es)
    else begin
      (*which pointers are defined and which arguments of data nodes are pointer*)
      let ( _,mix_lf,_,_,_,_) = CF.split_components lhs in
      let leqs = (MCP.ptr_equations_without_null mix_lf) in
      let _ =
        x_tinfo_pp ">>>>>> infer_hp_rel_classic <<<<<<" pos;
        x_tinfo_hp (add_str  "  es_heap " Cprinter.string_of_h_formula) es.CF.es_heap pos;
        x_tinfo_hp (add_str  "  lhs " Cprinter.string_of_formula) lhs pos;
        x_tinfo_hp (add_str  "  unmatch " Cprinter.string_of_h_formula) rhs pos;
        x_tinfo_hp (add_str  "  classic " string_of_bool) (check_is_classic ()) pos
      in
      let l_hpargs = CF.get_HRels_f lhs in
      let l_non_infer_hps = CP.diff_svl lhrs ivs in
      (**smart subst**)
      let lhsb1 = Sautil.smart_subst_lhs lhs l_hpargs leqs es.es_infer_vars in
      (**************COLLECT ASS*******************)
      let ls_ass, defined_hps = collect_classic_assumption prog es lhsb1
          (es.es_infer_vars_hp_rel@es.es_infer_vars_sel_hp_rel) es.es_infer_vars pos in
      if ls_ass = [] then (false, es) else
        (**************REFINE RES*******************)
        let n_es_formula, _ = CF.drop_hrel_f es.es_formula defined_hps in
        let new_es = {es with (* CF. es_infer_vars_hp_rel = es.CF.es_infer_vars_hp_rel@rvhp_rels; *)
                      (* CF.es_infer_hp_rel = es.CF.es_infer_hp_rel # pust_list ls_ass; *)
                      (* CF.es_infer_hp_unk_map = (es.CF.es_infer_hp_unk_map@unk_map); *)
                      (* CF.es_infer_vars_sel_post_hp_rel = (es.CF.es_infer_vars_sel_post_hp_rel @ post_hps); *)
                      CF.es_formula = n_es_formula}
        in
        (* let ls_ass = CF.add_unfold_flag ls_ass in *)
        let () = new_es.CF.es_infer_hp_rel # push_list_loc x_loc ls_ass in
        x_tinfo_hp (add_str  "  new residue " Cprinter.string_of_formula) new_es.CF.es_formula pos;
        (true, new_es)
    end

let infer_collect_hp_rel_classsic i prog (es:entail_state) rhs pos =
  let pr1 = Cprinter.string_of_formula in
  let pr2 = Cprinter.string_of_h_formula in
  let pr3 = Cprinter.string_of_estate_infer_hp in
  let pr4 =  pr_pair string_of_bool pr3 in
  Debug.no_2_num i "infer_collect_hp_rel_classsic" pr1 pr2 pr4
    ( fun _ _ -> infer_collect_hp_rel_classsic prog es rhs pos) es.CF.es_formula rhs
