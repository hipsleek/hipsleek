#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Others
open Label_only
module CP = Cpure
module IF = Iformula
module CF = Cformula
module CFU = Cfutil
module MCP = Mcpure
module CEQ = Checkeq

let add_dangling prog (is:CF.infer_state) = 
  let () = x_binfo_pp "TODO : this proc is to add dangling references" no_pos in
  is

let add_dangling prog is = 
  let pr2 = Cprinter.string_of_infer_state_short in
  Debug.no_1 "add_dangling" pr2 pr2
    (fun _ -> add_dangling prog is) is
