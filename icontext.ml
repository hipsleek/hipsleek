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


type infer_state = {
    is_assumption : hprel list;
    is_link_hps : CP.spec_var list;
    is_dang_hps : CP.spec_var list; (*dangling hps = link hps = unknown. to remove one of them*)
    is_sel_hps: CP.spec_var list;
    is_sel_post_hps: CP.spec_var list;
    is_hpdef: hp_rel_def list;
}


type iaction =
  | I_pre_trans
