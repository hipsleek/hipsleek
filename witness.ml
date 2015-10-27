#include "xdebug.cppo"
open VarGen
open Globals
open Others
open Gen

module CF = Cformula
module CP = Cpure



let rec witness_search iprog cprog call_stack inter_id intra_id cur_exp cur_proc_name cur_rest_path_ctls res_str=
  true, stack_alloc, inter_id, res_s_tr
