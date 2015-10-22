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

let rec compute_cmd cprog scc infs: icmd=
  if List.exists (fun it -> it = INF_ANA_NI) infs then
    let ni_cmd = mk_norm_icmd [INF_ANA_NI] in
    let rest_infs = (Gen.BList.difference_eq (=) infs [INF_ANA_NI]) in
    if rest_infs = [] then
      ni_cmd
    else
      let rest_cmd = compute_cmd cprog scc rest_infs in
      mk_seq_icmd (1,ni_cmd) (1,rest_cmd)
  else
    let has_infer_shape_prepost_proc = List.exists (fun it -> it = INF_SHAPE_PRE_POST) infs in
    if has_infer_shape_prepost_proc then
      (* let scc_wo_shape,_ = List.split (Iincr.update_infer_const_scc [] [INF_SHAPE_PRE_POST] scc) in *)
      (* let scc_pre,_ = List.split (Iincr.update_infer_const_scc [INF_SHAPE_PRE;INF_CLASSIC] infs scc) in *)
      (* let pre_cmd = compute_cmd cprog [INF_SHAPE_PRE;INF_CLASSIC] in *)
      (* let scc_post,_ = List.split (Iincr.update_infer_const_scc [INF_SHAPE_POST] infs scc) in *)
      (* let post_cmd =  compute_cmd cprog [INF_SHAPE_POST] in *)
      let pre_cmd = mk_norm_icmd [INF_SHAPE_PRE;INF_CLASSIC] in
      let post_cmd = mk_norm_icmd [INF_SHAPE_POST] in
      let snd_cmd = if List.exists (fun it -> it != INF_SHAPE_PRE_POST) infs then
        mk_seq_icmd (1,post_cmd) ( mk_norm_icmd_wt 1 (Gen.BList.difference_eq (=) infs [INF_SHAPE_PRE_POST]))
      else
        post_cmd
      in
      mk_seq_icmd (1,pre_cmd) (1,snd_cmd)
    else
      if List.exists (fun it -> it = INF_SHAPE_PRE) infs && List.exists (fun it -> it = INF_SHAPE_POST) infs then
        let pre_cmd = if List.exists (fun it -> it = INF_CLASSIC) infs then
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
