open Globals
open Cpure

(* Memoised Formula *)
let empty_var_aset = EMapSV.mkEmpty

(* Memoised structures *)
type memo_pure = memoised_group list

and memoised_group = {
  memo_group_fv           : spec_var list;
  memo_group_linking_vars : spec_var list;
  memo_group_changed      : bool;
  memo_group_cons         : memoised_constraint list; (*used for pruning*)
  memo_group_slice        : formula list; (*constraints that can not be used for pruning but belong to the current slice non-the less*)
  memo_group_aset         : var_aset; (* alias set *)
}

and memoised_constraint = {
  memo_formula            : b_formula;
  memo_status             : prune_status 
}

and prune_status = 
  | Implied_R      (*constraint that is superseeded by other constraints in the current state*)
  | Implied_P
  | Implied_N

and var_aset = Gen.EqMap(SV).emap 


(************************************)
(* Signatures for Slicing Framework *)
(************************************)

(* Signature of Atomic Constraints *)
module type ATOM_TYPE = 
sig
  type t
  val fv: t -> spec_var list
end;;

(* Signature of Label *)
module type LABEL_TYPE =
  functor (Atom: ATOM_TYPE) ->
sig
  type t
  val empty: t
  val label_of:  Atom.t -> t
  val merge: t -> t -> t
  val merge_list: t list -> t
  val is_rel: t -> t -> bool
end;;

(* Atomic Constraint with Label *)
module CONSTR = 
  functor (Label: LABEL_TYPE) ->
  functor (Atom: ATOM_TYPE) ->
struct
  module ALabel = Label(Atom)
  type t = (ALabel.t option) * Atom.t
  
  let get_label (constr: t) : ALabel.t =
    match (fst constr) with
    | None -> ALabel.label_of (snd constr)
    | Some l -> l

  let constr_of_atom (a: Atom.t) : t =
    (Some (ALabel.label_of a), a)

  let constr_of_atom_list (al: Atom.t list) : t list =
    List.map constr_of_atom al
end;;

(* Slice - List of Atomic Constraints *)  
module SLICE = 
  functor (Label: LABEL_TYPE) ->
  functor (Atom: ATOM_TYPE) ->
struct
  module ALabel = Label(Atom)
  type t = (ALabel.t option) * (Atom.t list)
  
  let get_label (slice: t) : ALabel.t =
    match (fst slice) with
    | None -> List.fold_left (fun acc c -> 
        ALabel.merge acc (ALabel.label_of c)) (ALabel.empty) (snd slice)
    | Some l -> l
end;;

(* Signature of Slicing Framework *)  
module type S_FRAMEWORK =
  functor (Label: LABEL_TYPE) ->
  functor (Atom: ATOM_TYPE) ->
sig
  type constr = CONSTR(Label)(Atom).t
  type slice = SLICE(Label)(Atom).t
  val same_slice: constr -> slice -> bool
  val split: constr list -> slice list
end;;

(* Automatic Slicing 
 * An instance of Slicing Framework *)
module S_AUTO : S_FRAMEWORK =
  functor (Label: LABEL_TYPE) ->
  functor (Atom: ATOM_TYPE) ->
struct
  module Constr = CONSTR(Label)(Atom)
  module Slice = SLICE(Label)(Atom)
  module ALabel = Label(Atom)
  type constr = Constr.t
  type slice = Slice.t

  let same_slice (c: constr) (s: slice) : bool =
    let lc = Constr.get_label c in
	  let ls = Slice.get_label s in
	  ALabel.is_rel lc ls
    
  let merge_slice_by_constr (c: constr) (sl: slice list) : slice =  
    let _, fc = c in
    let _, fsl = List.split sl in
    let n_label = ALabel.merge_list ((Constr.get_label c)::(List.map Slice.get_label sl)) in
    (Some n_label, fc::(List.concat fsl))

  let rec split (cl: constr list) : slice list = 
    match cl with
    | [] -> []
    | a::p ->
      let pl = split p in
      let p1, p2 = List.partition (fun s -> same_slice a s) pl in
      let np1 = merge_slice_by_constr a p1 in 
      np1::p2
end;;

(* Syntactic Label for Automatic Slicing *)
module Syn_Label_AuS =
  functor (Atom: ATOM_TYPE) ->
struct
  type t = spec_var list
  let empty : t = []
  let label_of (a: Atom.t) : t = Atom.fv a
  let merge (l1: t) (l2: t) : t = l1@l2
  let merge_list (l: t list) : t = List.concat l
  let is_rel (l1: t) (l2: t) : bool =
    Gen.BList.overlap_eq eq_spec_var l1 l2
end;;

module Pure_Constr =
struct
  type t = 
    | Pure_B of b_formula
    | Pure_F of formula
  
  let fv (constr: t) : spec_var list = 
    match constr with
    | Pure_B b -> bfv b
    | Pure_F f -> fv f
  
  let atom_of_b_formula (b: b_formula) : t = Pure_B b

  let atom_of_formula (f: formula) : t = Pure_F f
end;;

module Pure_AuS = S_AUTO (Syn_Label_AuS) (Pure_Constr);;
module Pure_Constr_AuS = CONSTR (Syn_Label_AuS) (Pure_Constr);;
module Pure_Slice_AuS = SLICE (Syn_Label_AuS) (Pure_Constr);;


module Memo_Constr =
struct
  module P = Pure_Constr
  type t =
    | Memo_B of b_formula * prune_status
    | Memo_F of formula
    | Memo_E of spec_var * spec_var (* For equality constraints *)

  let fv (constr: t) : spec_var list = 
    match constr with
    | Memo_B (bf, _) -> bfv bf
    | Memo_F f -> fv f
    | Memo_E (v1, v2) -> 
        match (is_const v1, is_const v2) with
        | (true, true) -> []
        | (true, false) -> [v2]
        | (false, true) -> [v1]
        | (false, false) -> [v1; v2]

  let memo_constr_of_pure_constr (a: P.t) (status: prune_status) : t = 
    match a with
    | P.Pure_B b -> (match get_bform_eq_args_with_const b with
      | Some (v1, v2) -> Memo_E (v1, v2)
      | _ -> Memo_B (b, status))
    | P.Pure_F f -> Memo_F f

  let memo_constr_of_memo_group (mg: memoised_group) : t list =
    let l1 = List.map (fun c -> Memo_B (c.memo_formula, c.memo_status)) mg.memo_group_cons in
    let l2 = List.map (fun f -> Memo_F f) mg.memo_group_slice in
    let l3 = List.map (fun (v1, v2) -> Memo_E (v1, v2)) (get_equiv_eq_with_const mg.memo_group_aset) in
    l1@l2@l3

  let memo_constr_of_memo_pure (mp: memo_pure) : t list =
    List.concat (List.map memo_constr_of_memo_group mp) 
end;;

module Memo_AuS = S_AUTO (Syn_Label_AuS) (Memo_Constr);;
module Memo_Constr_AuS = CONSTR (Syn_Label_AuS) (Memo_Constr);;
module Memo_Slice_AuS = SLICE (Syn_Label_AuS) (Memo_Constr);;


module Memo_Group = 
struct
  type t = memoised_group
  let fv (mg: t) : spec_var list = mg.memo_group_fv
end;;
 
module MG_AuS = S_AUTO (Syn_Label_AuS) (Memo_Group);;
module MG_Constr_AuS = CONSTR (Syn_Label_AuS) (Memo_Group);;
module MG_Slice_AuS = SLICE (Syn_Label_AuS) (Memo_Group);;


module Memo_Formula =
struct
  module P = Pure_Constr
  module M = Memo_Constr
  module PS_AuS = SLICE (Syn_Label_AuS) (Pure_Constr)
  module MS_AuS = SLICE (Syn_Label_AuS) (Memo_Constr)
  module MGS_AuS = SLICE (Syn_Label_AuS) (Memo_Group)

  let memo_group_of_pure_slice (s: PS_AuS.t) (status: prune_status) f_opt : memoised_group =
    let vs = Gen.BList.remove_dups_eq eq_spec_var (PS_AuS.get_label s) in
    let cons, slice, aset = List.fold_left (
      fun (c, s, a) p_ctr -> match p_ctr with 
      | P.Pure_B b -> (match get_bform_eq_args_with_const b with
        | Some (v1, v2) -> (c, s, add_equiv_eq_with_const a v1 v2)
        | _ -> let mc = { memo_formula = b; memo_status = status } in
          (mc::c, s, a))
      | P.Pure_F f -> (c, f::s, a)
    ) ([], [], empty_var_aset) (snd s) in
    let cons = match f_opt with
      | None -> cons
      | Some f -> f aset [cons]
    in
    {
      memo_group_fv = vs;
      memo_group_linking_vars = [];
      memo_group_cons = cons;
      memo_group_slice = slice;
      memo_group_changed = true;
      memo_group_aset = aset;
    }

  let memo_pure_of_pure_slice (sl: PS_AuS.t list) (status: prune_status) f_opt : memo_pure = 
    List.map (fun s -> memo_group_of_pure_slice s status f_opt) sl

  let memo_group_of_memo_slice (s: MS_AuS.t) f_opt : memoised_group =
    let vs = Gen.BList.remove_dups_eq eq_spec_var (MS_AuS.get_label s) in
    let cons, slice, aset = List.fold_left (
      fun (c, s, a) m_ctr -> match m_ctr with 
      | M.Memo_B (b, status) -> 
          let mc = { memo_formula = b; memo_status = status } in
          (mc::c, s, a)
      | M.Memo_F f -> (c, f::s, a)
      | M.Memo_E (v1, v2) -> (c, s, add_equiv_eq_with_const a v1 v2)
    ) ([], [], empty_var_aset) (snd s) in
    let cons = match f_opt with
    | None -> cons
    | Some f -> f aset [cons]
    in
    {
      memo_group_fv = vs;
      memo_group_linking_vars = [];
      memo_group_cons = cons;
      memo_group_slice = slice;
      memo_group_changed = true;
      memo_group_aset = aset;
    }

  let memo_pure_of_memo_slice (sl: MS_AuS.t list) f_opt : memo_pure = 
    List.map (fun s -> memo_group_of_memo_slice s f_opt) sl

  let memo_group_of_mg_slice (s: MGS_AuS.t) f_opt : memoised_group =
    let vs = Gen.BList.remove_dups_eq eq_spec_var (MGS_AuS.get_label s) in
    let cons, slice, aset = List.fold_left (
      fun (c, s, a) mg -> 
        (c@mg.memo_group_cons, s@mg.memo_group_slice, EMapSV.merge_eset a mg.memo_group_aset)
    ) ([], [], empty_var_aset) (snd s)
    in
    let cons = match f_opt with
    | None -> cons
    | Some f -> f aset [cons]
    in
    {
      memo_group_fv = vs;
      memo_group_linking_vars = [];
      memo_group_cons = cons;
      memo_group_slice = slice;
      memo_group_changed = true;
      memo_group_aset = aset;
    }
    
  let memo_pure_of_mg_slice (sl: MGS_AuS.t list) f_opt : memo_pure = 
    List.map (fun s -> memo_group_of_mg_slice s f_opt) sl

end;;


(*
(* Transform a slice to a memoised group *)
let atom_constr_to_memo_constr (a: atom_constr) (status: prune_status) : memo_constr =
  match a with
  | Atom_B b -> (match get_bform_eq_args_with_const b with
    | Some (v1, v2) -> Memo_E (v1, v2)
    | _ -> Memo_B (b, status))
  | Atom_F f -> Memo_F f 

let slice_to_memo_slice (a: slice) (status: prune_status) : memo_slice =
  let _, fa = a in
  let fm = List.map (fun a -> atom_constr_to_memo_constr a status) fa in
  let lm = syn_label_of_slice a in
  (Some lm, fm)

(* Transform a slice into a memoised group 
 * To be used in the create_memo_group function *)  
let memo_slice_to_memo_group (m: memo_slice) filter_merged_cons_opt : memoised_group = 
  let vs = Gen.BList.remove_dups_eq eq_spec_var (syn_label_of_memo_slice m) in
  let cons, slice, aset = List.fold_left (
    fun (c, s, a) ctr -> match ctr with 
    | Memo_B (b, status) -> 
        let mc = { memo_formula = b; memo_status = status } in
        (mc::c, s, a)
    | Memo_F f -> (c, f::s, a)
    | Memo_E (v1, v2) -> (c, s, add_equiv_eq_with_const a v1 v2)
  ) ([], [], empty_var_aset) (snd m) in
  let cons = match filter_merged_cons_opt with
  | None -> cons
  | Some f -> f aset [cons]
  in
  {
    memo_group_fv = vs;
    memo_group_linking_vars = [];
    memo_group_cons = cons;
    memo_group_slice = slice;
    memo_group_changed = true;
    memo_group_aset = aset;
  }
(*
let memo_group_to_memo_slice (mg: memoised_group) : 

let memo_group_to_constrs (mg: memoised_group) : constr list * (b_formula, prune_status) Hashtbl.t =
  let ps_tab = Hashtbl.create 200 in
  let l1 = List.map (fun c -> 
    let _ = Hashtbl.add ps_tab c.memo_formula c.memo_status in
    atom_to_constr (Const_B c.memo_formula)) mg.memo_group_cons in
  let l2 = List.map (fun f -> atom_to_constr (Const_R f)) mg.memo_group_slice in
  let l3 = List.map (fun (v1, v2) -> atom_to_constr (Const_E (v1, v2))) (get_equiv_eq_with_const mg.memo_group_aset) in
  (l1@l2@l3, ps_tab)
*)

let slice_to_memo_group (a: slice) (status: prune_status) filter_merged_cons : memoised_group = 
  let m_slice = slice_to_memo_slice a status in
  memo_slice_to_memo_group m_slice (Some filter_merged_cons)

let slice_list_to_memo_pure (sl: slice list) (status: prune_status) filter_merged_cons : memo_pure = 
  List.map (fun s -> slice_to_memo_group s status filter_merged_cons) sl 

*)



(* Flatten a list of (memoised_group) slices into a list of formulas *)  
let flatten_memo_pure (mp: memo_pure) = 
  List.fold_left (fun a d -> 
	  let n_c = List.map (fun c -> ((bfv c.memo_formula), [(Some c, None, None)])) d.memo_group_cons in
	  let n_f = List.map (fun f -> ((fv f), [(None, Some f, None)])) d.memo_group_slice in
	  let n_a = (fun f -> ((get_elems_eq f), [(None, None, Some f)])) d.memo_group_aset in
    (a @ n_c @ n_f @ [n_a])) [] mp


(*
let overlap_by_fv (qv: spec_var list) (q: constr) : bool = 
  let lq = syn_label_of_constr q in
  Gen.BList.overlap_eq eq_spec_var qv lq


let get_rel_constr_by_fv (qv: spec_var list) (cl: constr list) : (constr list * constr list) = 
  List.partition (fun c -> overlap_by_fv qv c) cl    





(* Transform a memoised group to a slice *)
*)
(*
 let memo_group_of (s: t list) (vs: spec_var list) 
    (status: prune_status) filter_merged_cons_opt : memoised_group =
    let vs = Gen.BList.remove_dups_eq eq_spec_var vs in
    let cons, slice, aset = List.fold_left (
      fun (c, s, a) p_ctr -> match p_ctr with 
      | Pure_B b -> (match get_bform_eq_args_with_const b with
        | Some (v1, v2) -> (c, s, add_equiv_eq_with_const a v1 v2)
        | _ -> let mc = { memo_formula = b; memo_status = status } in
          (mc::c, s, a))
      | Pure_F f -> (c, f::s, a)
    ) ([], [], empty_var_aset) s in
    (*let cons = match filter_merged_cons_opt with
    | None -> cons
    | Some f -> f aset [cons]
    in*)
    {
      memo_group_fv = vs;
      memo_group_linking_vars = [];
      memo_group_cons = cons;
      memo_group_slice = slice;
      memo_group_changed = true;
      memo_group_aset = aset;
    }
*)
(*
let memo_group_of (s: t list) (vs: spec_var list) 
    (status: prune_status) filter_merged_cons_opt : memoised_group =
    let vs = Gen.BList.remove_dups_eq eq_spec_var vs in
    let cons, slice, aset = List.fold_left (
      fun (c, s, a) m_ctr -> match m_ctr with 
      | Memo_B (b, status) -> 
          let mc = { memo_formula = b; memo_status = status } in
          (mc::c, s, a)
      | Memo_F f -> (c, f::s, a)
      | Memo_E (v1, v2) -> (c, s, add_equiv_eq_with_const a v1 v2)
    ) ([], [], empty_var_aset) s in
    (*let cons = match filter_merged_cons_opt with
    | None -> cons
    | Some f -> f aset [cons]
    in*)
    {
      memo_group_fv = vs;
      memo_group_linking_vars = [];
      memo_group_cons = cons;
      memo_group_slice = slice;
      memo_group_changed = true;
      memo_group_aset = aset;
    }
*)
