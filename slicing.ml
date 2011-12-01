(* Slicing Module *)
(*
module type FORMULA_TYPE = 
sig
  type t
end;;

module type SLICE_TYPE =
sig
  type t
  val sameSlice: t -> t -> bool
  val isRelevant: t -> t -> bool
end;;

(* Slicing Framework *)
module SlicingFramework = 
  functor (Formula: FORMULA_TYPE) -> 
  functor (Slice: SLICE_TYPE) -> 
sig
  open Slice
  open Formula
  type s = Slice.t
  type f = Formula.t
  val split: f -> s list   
  val getCtr: s -> s list -> s list
end;;

(* Automatic Slicing *)
module AutoSlicing = 
struct

end;;

(* Annotated Slicing *)
module AnnoSlicing = 
struct
end;;
*)

open Globals
open Cpure

let empty_var_aset = EMapSV.mkEmpty 

type memo_pure = memoised_group list

and memoised_group = {
  memo_group_fv : spec_var list;
  memo_group_linking_vars : spec_var list;
  memo_group_changed : bool;
  memo_group_cons : memoised_constraint list; (*used for pruning*)
  memo_group_slice: formula list; (*constraints that can not be used for pruning but belong to the current slice non-the less*)
  memo_group_aset : var_aset; (* alias set *)
}

and memoised_constraint = {
  memo_formula : b_formula;
  memo_status : prune_status 
}

and prune_status = 
  | Implied_R      (*constraint that is superseeded by other constraints in the current state*)
  | Implied_P
  | Implied_N

and var_aset = Gen.EqMap(SV).emap 

and atomic_constraint = 
  | Const_B of b_formula
  | Const_R of formula
  | Const_E of spec_var * spec_var (* For equality constraint *)

and constr = syn_label * atomic_constraint

and slice = syn_label * atomic_constraint list

and syn_label = spec_var list (* Syntactic label for automatic slicing *)

let fv_atom (c: atomic_constraint) =
  match c with
  | Const_B bf -> bfv bf
  | Const_R f -> fv f
  | Const_E (v1, v2) -> 
      match (is_const v1, is_const v2) with
      | (true, true) -> []
      | (true, false) -> [v2]
      | (false, true) -> [v1]
      | (false, false) -> [v1; v2]

(* SameSlice meta-predicate for automatic slicing mechanism *)
(* Using syntactic label for lower cost *)
let same_slice_auto (q1: constr) (q2: slice) : bool =
  let lq1, _ = q1 in
  let lq2, _ = q2 in
  Gen.BList.overlap_eq eq_spec_var lq1 lq2

(* Flatten a list of (memoised_group) slices into a list of formulas *)  
let flatten_memo_pure (mp : memo_pure) = 
  List.fold_left (fun a d -> 
	  let n_c = List.map (fun c -> ((bfv c.memo_formula), [(Some c, None, None)])) d.memo_group_cons in
	  let n_f = List.map (fun f -> ((fv f), [(None, Some f, None)])) d.memo_group_slice in
	  let n_a = (fun f -> ((get_elems_eq f), [(None, None, Some f)])) d.memo_group_aset in
    (a @ n_c @ n_f @ [n_a])) [] mp

let rec split (cl : atomic_constraint list) : slice list = 
  match cl with
  | [] -> []
  | a::p ->
      let pl = split p in
      let va = fv_atom a in
      let p1, p2 = List.partition (fun s -> same_slice_auto (va, a) s) pl in
      let vp1, fp1 = List.split p1 in
      (*let vp1 = Gen.BList.remove_dups_eq eq_spec_var (va @ (List.concat vp1)) in*)
      let vp1 = va @ (List.concat vp1) in
      let fp1 = a::(List.concat fp1) in
      (vp1, fp1)::p2

(* Transform each slice to a memoised group *)
let slice_to_memo_group (s : slice) (status : prune_status) filter_merged_cons : memoised_group = 
  let vs, fs = s in
  let vs = Gen.BList.remove_dups_eq eq_spec_var vs in
  let cons, slice, aset = List.fold_left (
    fun (c, s, a) ctr -> match ctr with
      | Const_B b -> (match get_bform_eq_args_with_const b with
        | Some (v1, v2) -> (c, s, add_equiv_eq_with_const a v1 v2)
        | _ -> let pos = { memo_formula = b; memo_status = status } in 
          (pos::c, s, a))
      | Const_R f -> (c, f::s, a)
      | Const_E (v1, v2) -> (c, s, add_equiv_eq_with_const a v1 v2)) 
    ([], [], empty_var_aset) fs in
  {
    memo_group_fv = vs;
    memo_group_linking_vars = [];
    memo_group_cons = filter_merged_cons aset [cons];
    memo_group_slice = slice;
    memo_group_changed = true;
    memo_group_aset = aset;
  }

let slice_list_to_memo_pure (sl : slice list) (status : prune_status) filter_merged_cons : memo_pure = 
  List.map (fun s -> slice_to_memo_group s status filter_merged_cons) sl 

