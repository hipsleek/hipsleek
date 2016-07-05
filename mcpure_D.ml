#include "xdebug.cppo"
open VarGen
open Globals
open Cpure

(* Memoised structures *)
type memo_pure = memoised_group list

and memoised_group = {
  memo_group_fv           : spec_var list;
  memo_group_linking_vars : spec_var list;
  memo_group_changed      : bool;
  memo_group_unsat        : bool; (* false if the slice has been checked UNSAT *)
  memo_group_cons         : memoised_constraint list; (*used for pruning*)
  memo_group_slice        : formula list; (*constraints that can not be used for pruning but belong to the current slice non-the less*)
  memo_group_aset         : var_aset; (* alias set *)
}

and memoised_constraint = {
  memo_formula            : b_formula;
  memo_status             : prune_status 
}

and prune_status = 
  | Implied_R (* Redundant constraint - Need not be proven when present in conseq *)     
  | Implied_P (* Propagated constraint - Need not be proven when present in conseq *)
  | Implied_N (* Original constraint *)

and var_aset = Gen.EqMap(SV).emap 

let empty_var_aset = EMapSV.mkEmpty

let print_mg_f = ref (fun (c: memoised_group) -> "printing not initialized")
let print_mp_f = ref (fun (c: memo_pure) -> "printing not initialized")


