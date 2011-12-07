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
  val atom_of_formula: formula -> t
end;;

(* Signature of Label *)
module type LABEL_TYPE =
  functor (Atom: ATOM_TYPE) ->
sig
  type t
  val empty: t
  val label_of_atom:  Atom.t -> t
  val merge: t -> t -> t
  val merge_list: t list -> t
  val cor_is_rel: t -> t -> bool
  val rel_is_rel: t -> t -> bool
  val is_rel_by_fv: spec_var list -> t -> t -> bool
  (* fv_of_label returns list of strongly and weakly linking variables *)
  val fv_of_label: t -> (spec_var list * spec_var list)
  val label_of_fv: spec_var list -> t
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
    | None -> ALabel.label_of_atom (snd constr)
    | Some l -> l

  let constr_of_atom (a: Atom.t) : t =
    (Some (ALabel.label_of_atom a), a)

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

  let empty: t = (None, [])

  let get_label (slice: t) : ALabel.t =
    match (fst slice) with
    | None -> List.fold_left (fun acc c -> 
        ALabel.merge acc (ALabel.label_of_atom c)) (ALabel.empty) (snd slice)
    | Some l -> l

  let merge (s1: t) (s2: t) = 
    let lbl = ALabel.merge (get_label s1) (get_label s2) in
    (Some lbl, (snd s1)@(snd s2))

  let slice_of_atom (a: Atom.t) : t =
    (Some (ALabel.label_of_atom a), [a])

  let atom_of_slice (s: t) : Atom.t list = snd s
end;;

(* Signature of Slicing Framework *)  
module type S_FRAMEWORK_SIG =
  functor (Label: LABEL_TYPE) ->
  functor (Atom: ATOM_TYPE) ->
sig
  type constr = CONSTR(Label)(Atom).t
  type slice = SLICE(Label)(Atom).t
  
  val split: constr list -> slice list
  (* split_by_fv is used in Quantifier pushing *)
  val split_by_fv: spec_var list -> constr list -> slice list

  val get_ctr: int -> slice -> constr list -> slice
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

  let merge_slice_by_constr (c: constr) (sl: slice list) : slice =  
    let _, fc = c in
    let _, fsl = List.split sl in
    let n_label = ALabel.merge_list ((Constr.get_label c)::(List.map Slice.get_label sl)) in
    (Some n_label, fc::(List.concat fsl))

  let same_slice (c: constr) (s: slice) : bool =
    let lc = Constr.get_label c in
	  let ls = Slice.get_label s in
	  ALabel.cor_is_rel lc ls

  let rec split (cl: constr list) : slice list = 
    match cl with
    | [] -> []
    | a::p ->
      let pl = split p in
      let p1, p2 = List.partition (fun s -> same_slice a s) pl in
      let np1 = merge_slice_by_constr a p1 in 
      np1::p2

  let same_slice_by_fv (vl: spec_var list) (c: constr) (s: slice) : bool =
    let lc = Constr.get_label c in
	  let ls = Slice.get_label s in
	  ALabel.is_rel_by_fv vl lc ls

  let rec split_by_fv (vl: spec_var list) (cl: constr list) : slice list = 
    match cl with
    | [] -> []
    | a::p ->
      let pl = split p in
      let p1, p2 = List.partition (fun s -> same_slice_by_fv vl a s) pl in
      let np1 = merge_slice_by_constr a p1 in 
      np1::p2

  (* Merge relevant constraints into one slice *)
  let merge_constr_by_slice (s: slice) (ps: constr list) : slice =
    let _, cl = List.split ps in
    let s_label = ALabel.merge_list (List.map Constr.get_label ps) in
    (Some s_label, cl)

  let is_relevant (f: slice) (s: constr) : bool = 
    let lf = Slice.get_label f in
    let ls = Constr.get_label s in
    ALabel.rel_is_rel lf ls
  
  let rec get_ctr (n: int) (f: slice) (ps: constr list) : slice =
    if (n = 0) then Slice.empty 
    else
      let rel_ctr, non_rel_ctr = List.partition (fun s -> is_relevant f s) ps in
      if rel_ctr = [] then Slice.empty
      else
        let r1 = merge_constr_by_slice f rel_ctr in
        let r2 = get_ctr (n-1) r1 non_rel_ctr in
        Slice.merge r1 r2
end;;

(* Syntactic Label for Automatic Slicing *)
module Syn_Label_AuS =
  functor (Atom: ATOM_TYPE) ->
struct
  type t = spec_var list
  
  let empty : t = []
  
  let label_of_atom (a: Atom.t) : t = Atom.fv a
  
  let merge (l1: t) (l2: t) : t = l1@l2
  
  let merge_list (l: t list) : t = List.concat l
 
  (* For SameSlice meta-predicate *)
  let cor_is_rel (l1: t) (l2: t) : bool =
    Gen.BList.overlap_eq eq_spec_var l1 l2

  (* For IsRelevant meta-predicate *)
  let rel_is_rel (l1: t) (l2: t) : bool =
    Gen.BList.overlap_eq eq_spec_var l1 l2

  (* With automatic slicing mechanism, two label 
   * are always relevant by fv.
   * So the function is not need,
   * it is just a dummy function *)
  let is_rel_by_fv (vl: spec_var list) (l1: t) (l2: t) : bool = false

  let fv_of_label (l: t) : (spec_var list * spec_var list) = (l, [])

  let label_of_fv (v: spec_var list) : t = v 
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
  
  let label_of_atom (a: Atom.t) : t = Atom.afv a 
  
  let merge (l1: t) (l2: t) : t =
    let (sv1, wv1) = l1 in
    let (sv2, wv2) = l2 in
    (sv1@sv2, wv1@wv2)
  
  let merge_list (l: t list) : t = 
    let (sl, wl) = List.split l in
    (List.concat sl, List.concat wl)
  
  (* For SameSlice meta-predicate *)
  let cor_is_rel (l1: t) (l2: t) : bool =
    let (sv1, wv1) = l1 in
    let (sv2, wv2) = l2 in
    if (sv1 = [] && sv2 = []) then
      (* Keep the linking constraints separately *)
      (Gen.BList.list_equiv_eq eq_spec_var wv1 wv2)
    else 
      (Gen.BList.overlap_eq eq_spec_var sv1 sv2) && 
      (Gen.BList.list_equiv_eq eq_spec_var wv1 wv2)

  (* For IsRelevant meta-predicate *)
  let rel_is_rel (l1: t) (l2: t) = true

  (* Two label are relevant with respect to vl 
   * if they share some common variables in vl *)
  let is_rel_by_fv (vl: spec_var list) (l1: t) (l2: t) : bool =
    let (sv1, wv1) = l1 in
    let (sv2, wv2) = l2 in
    let intersect = Gen.BList.intersect_eq eq_spec_var (sv1@wv1) (sv2@wv2) in
		Gen.BList.overlap_eq eq_spec_var vl intersect

  let fv_of_label (l: t) : (spec_var list * spec_var list) = l

  let label_of_fv (v: spec_var list) : t = (v, []) 
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

  let formula_of_memo_constr (c: t) : formula =
    match c with
    | Memo_B (bf, _) -> BForm (bf, None)
    | Memo_F f -> f
    | Memo_E (v1, v2) -> BForm (((form_bform_eq_with_const v1 v2), None), None)

  let atom_of_formula (f: formula) : t = Memo_F f
end;;

module Memo_Group = 
struct
  type t = memoised_group
  
  let fv (mg: t) : spec_var list = mg.memo_group_fv
  
  let afv (mg: t) : (spec_var list * spec_var list) = 
    let wv = mg.memo_group_linking_vars in
    let sv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv wv in
    (sv, wv)

  let atom_of_formula (f: formula) : t =
    let sv, wv = fv_with_slicing_label f in
    {
      memo_group_fv = sv@wv;
      memo_group_linking_vars = wv;
      memo_group_cons = [];
      memo_group_slice = [f];
      memo_group_changed = false;
      memo_group_aset = empty_var_aset;
    }

end;;
 
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

(* Utilities for Mcpure module
 * Using for both automatic slicing 
 * and annotated slicing *)  
module MCP_Util = 
  functor (Label: LABEL_TYPE) ->
struct
  module Pure_S         = S_FRAMEWORK (Label) (Pure_Constr)
  module Pure_Constr_S  = CONSTR      (Label) (Pure_Constr)
  module Pure_Slice_S   = SLICE       (Label) (Pure_Constr)
  module Pure_Label     = Label       (Pure_Constr)

  module Memo_S         = S_FRAMEWORK (Label) (Memo_Constr);;
  module Memo_Constr_S  = CONSTR      (Label) (Memo_Constr);;
  module Memo_Slice_S   = SLICE       (Label) (Memo_Constr);;

  module MG_S           = S_FRAMEWORK (Label) (Memo_Group)
  module MG_Constr_S    = CONSTR      (Label) (Memo_Group)
  module MG_Slice_S     = SLICE       (Label) (Memo_Group)
  
  module MF_S           = Memo_Formula(Label)

  let regroup_memo_group (lst: memo_pure) : memo_pure =
    if !f_1_slice then 
      (if (List.length lst)>1 then (print_string "multi slice problem"; failwith "multi slice problem"); lst)
    else 
      let l = MG_Constr_S.constr_of_atom_list lst in
      let sl = MG_S.split l in
      MF_S.memo_pure_of_mg_slice sl None

  let group_mem_by_fv (lst: memo_pure) : memo_pure =
    if !f_1_slice then
      (if (List.length lst)>1 then (print_string "multi slice problem "; failwith "multi slice problem"); lst)
    else 
      let l = MG_Constr_S.constr_of_atom_list lst in
      let sl = MG_S.split l in
      MF_S.memo_pure_of_mg_slice sl None

  let merge_mems_nx (l1: memo_pure) (l2: memo_pure) slice_check_dups filter_merged_cons : memo_pure = 
    let r = 
      if !f_1_slice then 
		    (if (List.length l1)>1 || (List.length l2)>1  then (print_string "multi slice problem"; failwith "multi slice problem");      
        let h1,h2 = (List.hd l1, List.hd l2) in
		    let na = EMapSV.merge_eset h1.memo_group_aset h2.memo_group_aset in
		    [{
          memo_group_fv = remove_dups_svl (h1.memo_group_fv @ h2.memo_group_fv);
		      memo_group_linking_vars = remove_dups_svl (h1.memo_group_linking_vars @ h2.memo_group_linking_vars);
		      memo_group_cons = filter_merged_cons na [h1.memo_group_cons; h2.memo_group_cons];
		      memo_group_changed = true;
		      memo_group_slice = h1.memo_group_slice @ h2.memo_group_slice;
		      memo_group_aset = na;
		    }])
      else
        let l = MG_Constr_S.constr_of_atom_list (l1@l2) in
        let sl = MG_S.split l in
        let merged_mp = MF_S.memo_pure_of_mg_slice sl (Some filter_merged_cons) in
        if (not slice_check_dups) then merged_mp
        else List.map (fun mg -> { mg with memo_group_slice =
          (Gen.Profiling.push_time "merge_mems_r_dups";
          let n_slice = Gen.BList.remove_dups_eq eq_pure_formula mg.memo_group_slice in
			    Gen.Profiling.pop_time "merge_mems_r_dups"; n_slice)
        }) merged_mp
    in r

  let create_memo_group (l1: b_formula list) (l2: formula list) 
    (status: prune_status) filter_merged_cons : memo_pure =
    (* Normalize l1 and l2 to lists of atomic constraints *)
    let l1 = List.map (fun b -> 
      let n_b = if !opt_ineq then trans_eq_bform b else b in
      Pure_Constr.atom_of_b_formula n_b) l1 in
    let l2 = List.map (fun f -> Pure_Constr.atom_of_formula f) l2 in
    let sl =
      let l = l1 @ l2 in
      if !f_1_slice then (* No slicing *)
        let v = List.fold_left (fun a s -> a @ (Pure_Constr.fv s)) [] l in
        let lbl = Pure_Label.label_of_fv (Gen.BList.remove_dups_eq eq_spec_var v) in
        [(Some lbl, l)] 
      else 
        (* List of atomic constraints with syntactic label *)
        let n_l = Pure_Constr_S.constr_of_atom_list l in
        Pure_S.split n_l 
    in
    MF_S.memo_pure_of_pure_slice sl status (Some filter_merged_cons)

  let split_mem_grp (g : memoised_group) : memo_pure = 
    if !f_1_slice then [g]
    else
      let l =  Memo_Constr.memo_constr_of_memo_group g in
      let n_l = Memo_Constr_S.constr_of_atom_list l in 
      let sl = Memo_S.split n_l in
      MF_S.memo_pure_of_memo_slice sl None 
end;;

module MG_AnS           = S_FRAMEWORK (Syn_Label_AnS) (Memo_Group)
module MG_Constr_AnS    = CONSTR      (Syn_Label_AnS) (Memo_Group)
module MG_Slice_AnS     = SLICE       (Syn_Label_AnS) (Memo_Group)
module MF_AnS           = Memo_Formula(Syn_Label_AnS)

module MG_AuS           = S_FRAMEWORK (Syn_Label_AuS) (Memo_Group)
module MG_Constr_AuS    = CONSTR      (Syn_Label_AuS) (Memo_Group)
module MG_Slice_AuS     = SLICE       (Syn_Label_AuS) (Memo_Group)
module MF_AuS           = Memo_Formula(Syn_Label_AuS)

module Memo_AnS         = S_FRAMEWORK (Syn_Label_AnS) (Memo_Constr);;
module Memo_Constr_AnS  = CONSTR      (Syn_Label_AnS) (Memo_Constr);;
module Memo_Slice_AnS   = SLICE       (Syn_Label_AnS) (Memo_Constr);;


