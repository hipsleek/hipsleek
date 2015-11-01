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

let rec compute_cmd cprog scc: icmd =
  let infs = (Iincr.get_infer_const_scc scc) in
  let () = y_binfo_hp (add_str "infs" (pr_list string_of_inf_const)) infs in
  let () = y_binfo_hp (add_str "infer_const_obj" pr_id) (Globals.infer_const_obj # string_of) in
  let has_infer_shape_prepost_proc = Globals.infer_const_obj # is_shape_pre_post ||
    List.exists (fun it -> it = INF_SHAPE_PRE_POST) infs in
  if has_infer_shape_prepost_proc then
    (* let scc_wo_shape,_ = List.split (Iincr.update_infer_const_scc [] [INF_SHAPE_PRE_POST] scc) in *)
    (* let scc_pre,_ = List.split (Iincr.update_infer_const_scc [INF_SHAPE_PRE;INF_CLASSIC] infs scc) in *)
    (* let pre_cmd = compute_cmd cprog [INF_SHAPE_PRE;INF_CLASSIC] in *)
    (* let scc_post,_ = List.split (Iincr.update_infer_const_scc [INF_SHAPE_POST] infs scc) in *)
    (* let post_cmd =  compute_cmd cprog [INF_SHAPE_POST] in *)
    let pre_cmd = mk_norm_icmd [INF_SHAPE_PRE(* ;INF_CLASSIC *)] in
    let post_cmd = mk_norm_icmd [INF_SHAPE_POST] in
    let snd_cmd = if Globals.infer_const_obj # is_shape_post || List.exists (fun it -> it != INF_SHAPE_PRE_POST) infs then
      mk_seq_icmd (1,post_cmd) ( mk_norm_icmd_wt 1 (Gen.BList.difference_eq (=) infs [INF_SHAPE_PRE_POST]))
    else
      post_cmd
    in
    mk_seq_icmd (1,pre_cmd) (1,snd_cmd)
  else
    if (Globals.infer_const_obj # is_shape_pre || List.exists (fun it -> it = INF_SHAPE_PRE) infs)
      && (Globals.infer_const_obj # is_shape_post || List.exists (fun it -> it = INF_SHAPE_POST) infs) then
      let pre_cmd = if Globals.infer_const_obj # is_classic || List.exists (fun it -> it = INF_CLASSIC) infs then
         mk_norm_icmd [INF_SHAPE_PRE;INF_CLASSIC]
      else mk_norm_icmd [INF_SHAPE_PRE]
      in
      let post_cmd = mk_norm_icmd [INF_SHAPE_POST] in
      let rem = List.filter (fun it -> it!= INF_SHAPE_PRE && it != INF_SHAPE_POST && it != INF_CLASSIC) infs in
      let snd_cmd = if rem != [] then
        mk_seq_icmd (1,post_cmd) ( mk_norm_icmd_wt 1 rem )
      else
        post_cmd
      in
      mk_seq_icmd (1,pre_cmd) (1,snd_cmd)
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
