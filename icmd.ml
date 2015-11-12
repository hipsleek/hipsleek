(* This module schedules properties need to be inferred *)
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

type cmd_res= {
    cmd_res_infs: infer_type list;
    (* cmd_res_scc: Cast.proc_decl list; *)
}

type icmd =
  | I_Norm of cmd_res
  | I_Seq of icmd_wt list
  | I_Search of icmd_wt list

and icmd_wt = (int * icmd)
(* -1 : unknown, 0 : mandatory; >0 : optional (lower value has higher priority) *)

let mk_norm_icmd infs= I_Norm {cmd_res_infs=infs(* ;cmd_res_scc = scc *)}

let mk_norm_icmd_wt i infs= (i, I_Norm {cmd_res_infs=infs(* ;cmd_res_scc = scc *)})

let mk_seq_icmd c1 c2 = I_Seq [c1;c2]

let rec string_of_icmd cmd =
  match cmd with
  | I_Norm infs -> "iNorm" ^ (pr_list string_of_inf_const infs.cmd_res_infs)
  | I_Seq iseq -> "iSeq" ^ (pr_list string_of_icmd_wt iseq)
  | I_Search isearch -> "iSearch" ^ (pr_list string_of_icmd_wt isearch)

and string_of_icmd_wt cmd = pr_pair string_of_int string_of_icmd cmd

let print_infer_scc scc =
  let rec collect_inf s = 
    match s with
    | CF.EList lst -> List.concat (List.map (fun (_,s) -> collect_inf s) lst)
    | CF.EInfer s -> (s.CF.formula_inf_vars, s.CF.formula_inf_obj)::(collect_inf s.CF.formula_inf_continuation)
    | _ -> [] 
  in
  let lst = List.map (fun p -> 
    let lst = p.Cast.proc_stk_of_static_specs # get_stk in
    (p.proc_name, List.map collect_inf lst)) scc 
  in
  pr_list (pr_pair pr_id (pr_list_num 
      (pr_list_n (pr_pair !CP.print_svl (fun iobj -> iobj # string_of))))) lst

let rec compute_cmd cprog scc: icmd =
  let infs = (Iincr.get_infer_const_scc scc) in
  let () = y_tinfo_hp (add_str "infs" (pr_list string_of_inf_const)) infs in
  let () = y_tinfo_hp (add_str "infer_const_obj" pr_id) (Globals.infer_const_obj # string_of) in
  let has_infer_shape_prepost_proc = 
    Globals.infer_const_obj # is_shape_pre_post ||
    List.exists (fun it -> it = INF_SHAPE_PRE_POST) infs 
  in
  let has_infer_pure_field =
    Globals.infer_const_obj # is_pure_field ||
    List.exists (fun it -> it = INF_PURE_FIELD) infs 
  in
  let has_infer_classic =
    Globals.infer_const_obj # is_classic ||
    List.exists (fun it -> it = INF_CLASSIC) infs 
  in
  let inf_shape_pre_cmd =
    mk_norm_icmd (
      [INF_SHAPE_PRE] @
      (if has_infer_pure_field then [INF_PURE_FIELD] else []) @
      (if has_infer_classic then [INF_CLASSIC] else []))
  in
  if has_infer_shape_prepost_proc then
    (* let scc_wo_shape,_ = List.split (Iincr.update_infer_const_scc [] [INF_SHAPE_PRE_POST] scc) in *)
    (* let scc_pre,_ = List.split (Iincr.update_infer_const_scc [INF_SHAPE_PRE;INF_CLASSIC] infs scc) in *)
    (* let pre_cmd = compute_cmd cprog [INF_SHAPE_PRE;INF_CLASSIC] in *)
    (* let scc_post,_ = List.split (Iincr.update_infer_const_scc [INF_SHAPE_POST] infs scc) in *)
    (* let post_cmd =  compute_cmd cprog [INF_SHAPE_POST] in *)
    (* let pre_cmd = mk_norm_icmd [INF_SHAPE_PRE] in *)
    let post_cmd = mk_norm_icmd [INF_SHAPE_POST] in
    let snd_cmd = 
      if Globals.infer_const_obj # is_shape_post || List.exists (fun it -> it != INF_SHAPE_PRE_POST) infs
      then mk_seq_icmd (1, post_cmd) (mk_norm_icmd_wt 1 (Gen.BList.difference_eq (=) infs [INF_SHAPE_PRE_POST]))
      else post_cmd
    in
    mk_seq_icmd (1, inf_shape_pre_cmd) (1, snd_cmd)
  else
    if (Globals.infer_const_obj # is_shape_pre || List.exists (fun it -> it = INF_SHAPE_PRE) infs) && 
       (Globals.infer_const_obj # is_shape_post || List.exists (fun it -> it = INF_SHAPE_POST) infs) 
    then
      (* let pre_cmd =                                                                               *)
      (*   if Globals.infer_const_obj # is_classic || List.exists (fun it -> it = INF_CLASSIC) infs  *)
      (*   then mk_norm_icmd [INF_SHAPE_PRE; INF_CLASSIC]                                            *)
      (*   else mk_norm_icmd [INF_SHAPE_PRE]                                                         *)
      (* in                                                                                          *)
      let post_cmd = mk_norm_icmd [INF_SHAPE_POST] in
      let rem = List.filter (fun it -> it!= INF_SHAPE_PRE && it != INF_SHAPE_POST && it != INF_CLASSIC) infs in
      let snd_cmd = 
        if rem != [] then mk_seq_icmd (1, post_cmd) (mk_norm_icmd_wt 1 rem)
        else post_cmd
      in
      mk_seq_icmd (1, inf_shape_pre_cmd) (1, snd_cmd)
    else
      (* let has_infer_shape_pre_proc =List.exists (fun it -> it = INF_SHAPE_PRE) infs in *)
      (* if has_infer_shape_pre_proc then *)
      (*   (\*TOFIX: care other infer consts*\) *)
      (*   let () = Iincr.add_prepost_shape_relation_scc cprog Iincr.add_pre_shape_relation scc in *)
      (*   mk_norm_icmd scc *)
      (* else *)
      (*   let has_infer_shape_post_proc = List.exists (fun it -> it = INF_SHAPE_POST) infs in *)
      (*   if has_infer_shape_post_proc then *)
      (*     (\*TOFIX: care other infer consts*\) *)
      (*     let () = Iincr.add_prepost_shape_relation_scc cprog Iincr.add_post_shape_relation scc in *)
      (*     mk_norm_icmd scc *)
      (*   else *)
      mk_norm_icmd infs

let compute_cmd cprog scc: icmd =
  let pr1 = print_infer_scc in
  let pr2 = string_of_icmd in
  Debug.no_2 "compute_cmd" (add_str "inf_scc" pr1) 
    (add_str "inf_obj" (fun _ -> Globals.infer_const_obj # string_of)) pr2 
    (fun _ _ -> compute_cmd cprog scc) scc ()
    

  
