open Globals
open Others
open Gen
open Cformula

module DD = Debug
module Err = Error
module CA = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module TP = Tpdispatcher
module SAU = Sautility


type iaction =
  | I_infer_dang
  | I_pre_trans_closure
  | I_split_base
  | I_partition (* pre, pre-oblg, post, post-oblg *)
  | I_pre_synz (* of iaction_wt list *)
  | I_pre_oblg
  | I_post_synz
  | I_post_oblg
  | I_seq of iaction_wt list

and iaction_wt = (int * iaction)
(* -1 : unknown, 0 : mandatory; >0 : optional (lower value has higher priority) *)


let rec string_of_iaction act=
  match act with
    | I_infer_dang -> "analize dangling"
    | I_pre_trans_closure -> "find transitive closure"
    | I_split_base ->  "split base"
    | I_partition -> "pre, pre-oblg, post, post-oblg"
    | I_pre_synz -> "pre-preds synthesize"
    | I_pre_oblg -> "pre-oblg"
    | I_post_synz -> "post-preds synthesize"
    | I_post_oblg -> "post-oblg"
    | I_seq ls_act -> "seq:" ^ (String.concat ";" (List.map (pr_pair string_of_int string_of_iaction) ls_act))

let mk_is constrs link_hpargs dang_hpargs unk_map sel_hps post_hps cond_path
      hp_equivs hpdefs=
  {
      is_constrs = constrs;
      is_link_hpargs = link_hpargs;
      is_dang_hpargs = dang_hpargs; (*dangling hps == link hps = unknown. to remove one of them*)
      is_sel_hps = sel_hps;
      is_unk_map = unk_map;
      is_post_hps = post_hps;
      is_cond_path = cond_path;
      is_hp_equivs = hp_equivs;
      is_hp_defs = hpdefs;
  }

let icompute_action_init need_preprocess detect_dang=
  let pre_acts=
    if need_preprocess then
      let dang_act =
        if detect_dang then
          [(0, I_infer_dang)]
        else []
      in
      dang_act@[(0, I_split_base)]
    else
      []
  in
  I_seq (pre_acts@[(0, I_pre_trans_closure); (0, I_partition)])

let icompute_action_pre ()=
  I_pre_synz

let icompute_action_pre_oblg ()=
  I_pre_oblg

let icompute_action_post ()=
  I_post_synz

let icompute_action_post_oblg ()=
  I_post_oblg
