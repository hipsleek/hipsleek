module CP = Cpure
module CF = Cformula
module MCP = Mcpure

open Globals
open Cprinter

(* Temporal Relation at Return *)
type ret_trel = {
  ret_ctx: MCP.mix_formula;
  (* Collect from RHS *)
  termr_fname: ident;
  termr_params: CP.spec_var list;
  termr_lhs: CP.term_ann list;
  termr_rhs: CP.term_ann;
}

let print_ret_trel rel = 
  string_of_trrel_assume (rel.ret_ctx, rel.termr_lhs, rel.termr_rhs)
  
(* Temporal Relation at Call *)
type call_trel = {
  call_ctx: MCP.mix_formula;
  trel_id: int;
  termu_lhs: CP.term_ann;
  termu_rhs: CP.term_ann;
}

let print_call_trel_debug rel = 
  string_of_turel_debug (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)

let print_call_trel rel = 
  string_of_turel_assume (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)
  
let compare_trel r1 r2 = compare r1.trel_id r2.trel_id
  
let eq_trel r1 r2 = r1.trel_id == r2.trel_id

let dummy_trel = {
  call_ctx = MCP.mix_of_pure (CP.mkTrue no_pos);
  trel_id = -1;
  termu_lhs = MayLoop;
  termu_rhs = MayLoop; 
}
  
let update_call_trel rel ilhs irhs = 
  { rel with
    termu_lhs = ilhs;  
    termu_rhs = irhs; }

type tntrel =
  | Ret of ret_trel
  | Call of call_trel

let string_of_tntrel = function
  | Ret rrel -> "@Return: " ^ (print_ret_trel rrel)
  | Call crel -> "@Call: " ^ (print_call_trel crel)
