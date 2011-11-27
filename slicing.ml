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

and slice = syn_label * atomic_constraint list

and syn_label = spec_var list (* Syntactic label for automatic slicing *)

let fv_atom (c: atomic_constraint) =
  match c with
  | Const_B bf -> bfv bf
  | Const_R f -> fv f

(* SameSlice meta-predicate for automatic slicing mechanism *)
let same_slice_auto (q1: atomic_constraint) (q2: atomic_constraint) : bool =
  Gen.BList.overlap_eq eq_spec_var (fv_atom q1) (fv_atom q2)

(* Flatten a list of (memoised_group) slices into a list of formulas *)  
let flatten_memo_pure (mp : memo_pure) = 
  List.fold_left (fun a d -> 
	  let n_c = List.map (fun c -> ((bfv c.memo_formula), [(Some c, None, None)])) d.memo_group_cons in
	  let n_f = List.map (fun f -> ((fv f), [(None, Some f, None)])) d.memo_group_slice in
	  let n_a = (fun f -> ((get_elems_eq f), [(None, None, Some f)])) d.memo_group_aset in
    (a @ n_c @ n_f @ [n_a])) [] mp

(*
(* Expensive function - Need a syntactic label for each slice *)
let rec split (cl : atomic_constraint list) : slice list = 
  match cl with
  | [] -> []
  | a::p ->
      let p1, p2 = List.partition (fun al -> 
        List.exists (fun b -> same_slice_auto a b) al) (split p) in
      (a::(List.concat p1))::p2
*)
(*
let split (cl : atomic_constraint list) : slice list = 
  let rec helper cl = 
    match cl with
    | [] -> [([], [])]
    | a::p -> 
        let pl = helper p in
        let va = fv_atom a in
        let p1, p2 = List.partition (fun (vb, b) -> 
          Gen.BList.overlap_eq eq_spec_var va vb) pl in
        let vp1, fp1 = List.split p1 in
        let vp1 = Gen.BList.remove_dups_eq eq_spec_var (va @ (List.concat vp1)) in
        let fp1 = a::(List.concat fp1) in
        (vp1, fp1)::p2
  in List.map (fun (_, s) -> s) (helper cl)
*)
(*
let same_slice_auto (q : atomic_constraint) (s : slice) : bool =
  let s_label, _ = s in
  Gen.BList.overlap_eq eq_spec_var (fv_atom q) s_label
*)
let rec split (cl : atomic_constraint list) : slice list = 
  match cl with
  | [] -> []
  | a::p ->
      let pl = split p in
      let va = fv_atom a in
      let p1, p2 = List.partition (fun (vb, _) -> Gen.BList.overlap_eq eq_spec_var va vb) pl in
      let vp1, fp1 = List.split p1 in
      let vp1 = Gen.BList.remove_dups_eq eq_spec_var (va @ (List.concat vp1)) in
      let fp1 = a::(List.concat fp1) in
      (vp1, fp1)::p2

(* Transform each slice to a memoised group *)
let slice_to_memo_group (s : slice) (status : prune_status) filter_merged_cons : memoised_group = 
  let vs, fs = s in
  let cons, slice, aset = List.fold_left (
    fun (c, s, a) ctr -> match ctr with
      | Const_B b -> (match get_bform_eq_args_with_const b with
        | Some (v1, v2) -> (c, s, add_equiv_eq_with_const a v1 v2)
        | _ -> let pos = { memo_formula = b; memo_status = status } in 
          (pos::c, s, a))
      | Const_R f -> (c, f::s, a)) 
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

