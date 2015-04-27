open Globals
open VarGen

module CP = Cpure

(* Temporal Relation at Return *)
type ret_trel = {
  ret_ctx: CP.formula;
  termr_fname: ident; (* Collect from RHS *)
  termr_lhs: CP.term_ann list;
  termr_rhs: CP.term_ann;
  termr_rhs_params: CP.spec_var list; (* For simplification on condition *)
  termr_pos: loc;
}

let ret_trel_stk: ret_trel Gen.stack = new Gen.stack

(* Temporal Relation at Call *)
type call_trel = {
  trel_id: int;
  call_ctx: CP.formula;
  termu_fname: ident; (* Collect from LHS *)
  termu_lhs: CP.term_ann;
  termu_rhs: CP.term_ann;
  (* For TermU/TermR *)
  termu_rhs_params: CP.spec_var list; (* For substitution on condition *)
  (* For other term_ann *)
  termu_cle: ident; (* callee *)
  termu_rhs_args: CP.exp list;
  termu_pos: loc;
}

let call_trel_stk: call_trel Gen.stack = new Gen.stack

let dummy_trel = {
  trel_id = -1;
  call_ctx = CP.mkTrue no_pos;
  termu_fname = "";
  termu_lhs = CP.MayLoop None;
  termu_rhs = CP.MayLoop None; 
  termu_rhs_params = []; 
  termu_cle = "";
  termu_rhs_args = [];
  termu_pos = no_pos; }

type tntrel =
  | Ret of ret_trel
  | Call of call_trel
