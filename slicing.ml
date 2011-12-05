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
  (* afv (fv with annotation) returns the pair 
   * of strongly linking variables
   * and weakly linking variables of the input *)
  val afv: t -> (spec_var list * spec_var list)
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
  val fv_of_label: t -> (spec_var list * spec_var list)
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
module type S_FRAMEWORK_SIG =
  functor (Label: LABEL_TYPE) ->
  functor (Atom: ATOM_TYPE) ->
sig
  type constr = CONSTR(Label)(Atom).t
  type slice = SLICE(Label)(Atom).t
  val same_slice: constr -> slice -> bool
  val split: constr list -> slice list
end;;

(* Implementation of Slicing Framework *)
module S_FRAMEWORK : S_FRAMEWORK_SIG =
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

  let fv_of_label (l: t) : (spec_var list * spec_var list) = (l, [])
end;;

(* Syntatic Label for Annotated Slicing *
 * Suitable for weakly linking constraint and
 * weakly linking variable *) 

module Syn_Label_AnS =
  functor (Atom: ATOM_TYPE) ->
struct
  (* Pair of strongly and weakly linking variables *)
  type t = spec_var list * spec_var list

  let empty : t = ([], [])
  
  let label_of (a: Atom.t) : t = Atom.afv a 
  
  let merge (l1: t) (l2: t) : t =
    let (sv1, wv1) = l1 in
    let (sv2, wv2) = l2 in
    (sv1@sv2, wv1@wv2)
  
  let merge_list (l: t list) : t = 
    let (sl, wl) = List.split l in
    (List.concat sl, List.concat wl)
  
  let is_rel (l1: t) (l2: t) : bool =
    let (sv1, wv1) = l1 in
    let (sv2, wv2) = l2 in
    if (sv1 = [] && sv2 = []) then
      (* Keep the linking constraints separately *)
      (Gen.BList.list_equiv_eq eq_spec_var wv1 wv2)
    else 
      (Gen.BList.overlap_eq eq_spec_var sv1 sv2) && 
      (Gen.BList.list_equiv_eq eq_spec_var wv1 wv2)
	  
  let fv_of_label (l: t) : (spec_var list * spec_var list) = l
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

  let afv (constr: t) : (spec_var list * spec_var list) =
    match constr with
    | Pure_B b -> bfv_with_slicing_label b
    | Pure_F f -> fv_with_slicing_label f
  
  let atom_of_b_formula (b: b_formula) : t = Pure_B b

  let atom_of_formula (f: formula) : t = Pure_F f
end;;

module Pure_AuS         = S_FRAMEWORK (Syn_Label_AuS) (Pure_Constr);;
module Pure_Constr_AuS  = CONSTR      (Syn_Label_AuS) (Pure_Constr);;
module Pure_Slice_AuS   = SLICE       (Syn_Label_AuS) (Pure_Constr);;

module Pure_AnS         = S_FRAMEWORK (Syn_Label_AnS) (Pure_Constr);;
module Pure_Constr_AnS  = CONSTR      (Syn_Label_AnS) (Pure_Constr);;
module Pure_Slice_AnS   = SLICE       (Syn_Label_AnS) (Pure_Constr);;


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

  let afv (constr: t) : (spec_var list * spec_var list) =
    match constr with
    | Memo_B (bf, _) -> bfv_with_slicing_label bf
    | Memo_F f -> fv_with_slicing_label f
    | Memo_E _ -> (fv constr, []) 

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

module Memo_AuS         = S_FRAMEWORK (Syn_Label_AuS) (Memo_Constr);;
module Memo_Constr_AuS  = CONSTR      (Syn_Label_AuS) (Memo_Constr);;
module Memo_Slice_AuS   = SLICE       (Syn_Label_AuS) (Memo_Constr);;

module Memo_AnS         = S_FRAMEWORK (Syn_Label_AnS) (Memo_Constr);;
module Memo_Constr_AnS  = CONSTR      (Syn_Label_AnS) (Memo_Constr);;
module Memo_Slice_AnS   = SLICE       (Syn_Label_AnS) (Memo_Constr);;


module Memo_Group = 
struct
  type t = memoised_group
  
  let fv (mg: t) : spec_var list = mg.memo_group_fv
  
  let afv (mg: t) : (spec_var list * spec_var list) = 
    let wv = mg.memo_group_linking_vars in
    let sv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv wv in
    (sv, wv)
end;;
 
module MG_AuS         = S_FRAMEWORK (Syn_Label_AuS) (Memo_Group);;
module MG_Constr_AuS  = CONSTR      (Syn_Label_AuS) (Memo_Group);;
module MG_Slice_AuS   = SLICE       (Syn_Label_AuS) (Memo_Group);;

module MG_AnS         = S_FRAMEWORK (Syn_Label_AnS) (Memo_Group);;
module MG_Constr_AnS  = CONSTR      (Syn_Label_AnS) (Memo_Group);;
module MG_Slice_AnS   = SLICE       (Syn_Label_AnS) (Memo_Group);;

module Memo_Formula =
  functor (Label: LABEL_TYPE) -> 
struct
  module P = Pure_Constr
  module M = Memo_Constr

  module PS = SLICE (Label) (Pure_Constr)
  module MS = SLICE (Label) (Memo_Constr)
  module MGS = SLICE (Label) (Memo_Group)
  
  module PL = Label (Pure_Constr)
  module ML = Label (Memo_Constr)
  module MGL = Label (Memo_Group)
  
  (* Utilities of Automatic Slicing *)
  let memo_group_of_pure_slice (s: PS.t) (status: prune_status) f_opt : memoised_group =
    let sv, ws = PL.fv_of_label (PS.get_label s) in
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
      memo_group_fv = Gen.BList.remove_dups_eq eq_spec_var (sv@ws);
      memo_group_linking_vars = Gen.BList.remove_dups_eq eq_spec_var ws;
      memo_group_cons = cons;
      memo_group_slice = slice;
      memo_group_changed = true;
      memo_group_aset = aset;
    }

  let memo_pure_of_pure_slice (sl: PS.t list) (status: prune_status) f_opt : memo_pure = 
    List.map (fun s -> memo_group_of_pure_slice s status f_opt) sl

  let memo_group_of_memo_slice (s: MS.t) f_opt : memoised_group =
    let sv, wv = ML.fv_of_label (MS.get_label s) in
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
      memo_group_fv = Gen.BList.remove_dups_eq eq_spec_var (sv@wv);
      memo_group_linking_vars = Gen.BList.remove_dups_eq eq_spec_var wv;
      memo_group_cons = cons;
      memo_group_slice = slice;
      memo_group_changed = true;
      memo_group_aset = aset;
    }

  let memo_pure_of_memo_slice (sl: MS.t list) f_opt : memo_pure = 
    List.map (fun s -> memo_group_of_memo_slice s f_opt) sl

  let memo_group_of_mg_slice (s: MGS.t) f_opt : memoised_group =
    let sv, wv = MGL.fv_of_label (MGS.get_label s) in
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
      memo_group_fv = Gen.BList.remove_dups_eq eq_spec_var (sv@wv);
      memo_group_linking_vars = Gen.BList.remove_dups_eq eq_spec_var wv;
      memo_group_cons = cons;
      memo_group_slice = slice;
      memo_group_changed = true;
      memo_group_aset = aset;
    }
    
  let memo_pure_of_mg_slice (sl: MGS.t list) f_opt : memo_pure = 
    List.map (fun s -> memo_group_of_mg_slice s f_opt) sl
end;;

module PMF_AuS = Memo_Formula (Syn_Label_AuS);;
module PMF_AnS = Memo_Formula (Syn_Label_AnS);;


