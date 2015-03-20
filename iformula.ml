#include "xdebug.cppo"
(*
  Created 19-Feb-2006

  Input formulae
*)

open Globals
open VarGen
open Exc.GTable
open Perm
open Label_only
open Gen.Basic

module P = Ipure
module VP = IvpermUtils

let top_flow = top_flow
let n_flow = n_flow

type mem_formula = {	mem_formula_exp : P.exp;
			mem_formula_exact : bool;
			mem_formula_field_values : (ident * (P.exp list)) list;
			mem_formula_field_layout : (ident * (P.ann list)) list;
			mem_formula_guards : P.formula list;
		}

and assume_formula =
	{
		formula_assume_simpl : formula;
		formula_assume_struc : struc_formula;
		formula_assume_lbl : formula_label;
		formula_assume_ensures_type : ensures_type;
	}

and struc_formula =
	| ECase of struc_case_formula
	| EBase of struc_base_formula
	| EAssume of assume_formula (*(formula*formula_label*ensures_type)*)
		(*could be generalized to have a struc_formula type instead of simple formula*)
		(* spec feature to induce inference *)
	| EInfer of struc_infer_formula
	| EList of (spec_label_def*struc_formula) list


and struc_infer_formula =
  {
    (* formula_inf_tnt: bool; (\* true if termination to be inferred *\) *)
    formula_inf_obj: Globals.inf_obj; (* local infer object *)
    formula_inf_post : bool; (* true if post to be inferred *)
    formula_inf_xpost : bool option; (* None -> no auto-var; Some _ -> true if post to be inferred *)
    formula_inf_transpec : (ident * ident) option;
    formula_inf_vars : (ident * primed) list;
    formula_inf_continuation : struc_formula;
    formula_inf_pos : loc
  }

and struc_case_formula =
	{
		formula_case_branches : (P.formula * struc_formula ) list;
		formula_case_pos : loc
	}

and struc_base_formula =
	{
		 formula_struc_explicit_inst : (ident * primed) list;
		 formula_struc_implicit_inst : (ident * primed) list;
		 formula_struc_exists :  (ident * primed) list;
		 formula_struc_base : formula;
                 formula_struc_is_requires: bool;
		 formula_struc_continuation : struc_formula option ;
		 formula_struc_pos : loc
	}

and formula =
  | Base of formula_base
  | Exists of formula_exists
  | Or of formula_or

and rflow_formula = {
  rflow_kind: ho_flow_kind;
  rflow_base: formula;
}

and formula_base = { 
  formula_base_heap : h_formula;
  formula_base_pure : P.formula;
  formula_base_vperm : VP.vperm_sets;
  formula_base_flow : flow_formula;
  formula_base_and: one_formula list;
  formula_base_pos : loc }

and formula_exists = { 
  formula_exists_qvars : (ident * primed) list;
  formula_exists_heap : h_formula;
  formula_exists_pure : P.formula;
  formula_exists_vperm : VP.vperm_sets;
  formula_exists_flow : flow_formula;
  formula_exists_and : one_formula list;
  formula_exists_pos : loc }

(*Note that one_formula and h_formula_thread
  are different ways of representing threads.
  Using one_formula, thread is a separate AND-conjunction,
  while using h_formula_thread, thread is a resource *)
and one_formula = {
    formula_heap : h_formula;
    formula_pure : P.formula;
    formula_delayed : P.formula;
    formula_thread : (ident*primed) option;
    formula_pos : loc
}

and flow_formula = constant_flow

and formula_or = { formula_or_f1 : formula;
		   formula_or_f2 : formula;
		   formula_or_pos : loc }

and h_formula = (* heap formula *)
  | Phase of h_formula_phase
  | Conj of h_formula_conj
  | ConjStar of h_formula_conjstar
  | ConjConj of h_formula_conjconj
  | Star of h_formula_star
  (* guard as magic wand? *)
  (* | Wand of h_formula * h_formula *)
  | StarMinus of h_formula_starminus
  | HeapNode of h_formula_heap
  | HeapNode2 of h_formula_heap2
	  (* Don't distinguish between view and data node for now, as that requires look up *)
	  (*  | ArrayNode of ((ident * primed) * ident * P.exp list * loc) *)
	  (* pointer * base type * list of dimensions *)

  (*Added in 2014-02-18: Thread node carrying a resource
    e.g. t::thread(0.5)<x::node<>> *)
  | ThreadNode of h_formula_thread
  | HRel of (ident * (P.exp list) * loc)
  | HTrue
  | HFalse
  | HEmp (* emp for classical logic *)
  | HVar of ident * (ident list)

and h_formula_star = { h_formula_star_h1 : h_formula;
		       h_formula_star_h2 : h_formula;
		       h_formula_star_pos : loc }

and h_formula_starminus = { h_formula_starminus_h1 : h_formula;
		       h_formula_starminus_h2 : h_formula;
		       h_formula_starminus_pos : loc }

and h_formula_conj = { h_formula_conj_h1 : h_formula;
		       h_formula_conj_h2 : h_formula;
		       h_formula_conj_pos : loc }

and h_formula_conjstar = { h_formula_conjstar_h1 : h_formula;
		       h_formula_conjstar_h2 : h_formula;
		       h_formula_conjstar_pos : loc }

and h_formula_conjconj = { h_formula_conjconj_h1 : h_formula;
		       h_formula_conjconj_h2 : h_formula;
		       h_formula_conjconj_pos : loc }

and h_formula_phase = { h_formula_phase_rd : h_formula;
			h_formula_phase_rw : h_formula;
			h_formula_phase_pos : loc }

and h_formula_heap = { h_formula_heap_node : (ident * primed);
                       h_formula_heap_name : ident;
                       h_formula_heap_deref : int;
                       h_formula_heap_derv : bool; 
                       h_formula_heap_split : split_ann; 
                       h_formula_heap_imm : P.ann;
                       h_formula_heap_imm_param : P.ann option list;
                       h_formula_heap_full : bool;
                       h_formula_heap_with_inv : bool;
                       h_formula_heap_perm : iperm; (*LDK: optional fractional permission*)
                       h_formula_heap_ho_arguments : rflow_formula list;
                       h_formula_heap_arguments : P.exp list;
                       h_formula_heap_pseudo_data : bool;
                       h_formula_heap_label : formula_label option;
                       h_formula_heap_pos : loc }

and h_formula_thread = { h_formula_thread_node : (ident * primed);
                       h_formula_thread_name : ident;
                       h_formula_thread_delayed : P.formula; (* for delayed lockset checking *)
                       h_formula_thread_resource : formula;
                       h_formula_thread_perm : iperm; (*LDK: optional fractional permission*)
                       h_formula_thread_label : formula_label option;
                       h_formula_thread_pos : loc }


and h_formula_heap2 = { h_formula_heap2_node : (ident * primed);
                        h_formula_heap2_name : ident;
                        h_formula_heap2_deref : int;
                        h_formula_heap2_derv : bool;
                        h_formula_heap2_split : split_ann;
                        h_formula_heap2_imm : P.ann;
                        h_formula_heap2_imm_param : P.ann option list;
                        h_formula_heap2_full : bool;
                        h_formula_heap2_with_inv : bool;
                        h_formula_heap2_perm : iperm; (*LDK: fractional permission*)
                        h_formula_heap2_arguments : (ident * P.exp) list;
                        h_formula_heap2_ho_arguments : rflow_formula list;
                        h_formula_heap2_pseudo_data : bool;
                        h_formula_heap2_label : formula_label option;
                        h_formula_heap2_pos : loc }

let mk_absent_ann = Ipure_D.ConstAnn Accs
let print_pure_formula = ref(fun (c:Ipure.formula) -> "printer not initialized")
(* Interactive command line *)
let cmd: (string * (bool * struc_formula option * string option)) ref = ref ("", (false, None, None))

let print_formula = ref(fun (c:formula) -> "printer not initialized")
let print_rflow_formula = ref(fun (c: rflow_formula) -> "printer not initialized")
let print_h_formula = ref(fun (c:h_formula) -> "printer not initialized")
let print_struc_formula = ref(fun (c:struc_formula) -> "printer not initialized")

(*move to ipure.ml*)
(* let linking_exp_list = ref (Hashtbl.create 100) *)
(* let () = let zero = P.IConst (0, no_pos) *)
(* 		in Hashtbl.add !linking_exp_list zero 0 *)

let apply_one_imm (fr,t) a = match a with
  | P.ConstAnn _ -> a
  | P.PolyAnn (sv, pos) -> P.PolyAnn ((if P.eq_var sv fr then t else sv), pos)

let apply_one_opt_imm (fr,t) a = match a with
  | Some annot -> Some (apply_one_imm (fr,t) annot)
  | None -> None
  
let rec string_of_spec_var_list l = match l with 
  | []               -> ""
  | h::[]            -> string_of_spec_var h 
  | h::t             -> (string_of_spec_var h) ^ "," ^ (string_of_spec_var_list t)

and string_of_spec_var = function 
  | (id, p) -> id ^ (match p with 
    | Primed   -> "'"
    | Unprimed -> "")

let print_one_formula = ref(fun (c:one_formula) -> "printer not initialized")
let print_formula = ref(fun (c:formula) -> "printer not initialized")
let print_struc_formula = ref(fun (c:struc_formula) -> "printer not initialized")

let rec string_of_spec_var_list l = match l with 
  | []               -> ""
  | h::[]            -> string_of_spec_var h 
  | h::t             -> (string_of_spec_var h) ^ "," ^ (string_of_spec_var_list t)

and string_of_spec_var = function 
  | (id, p) -> id ^ (match p with 
    | Primed   -> "'"
    | Unprimed -> "")

let rec is_param_ann_list_empty (anns:  P.ann option list) : bool =
  match anns with
    | [] -> true
    | (Some _)::t  -> false
    | (None)::t    -> true  && (is_param_ann_list_empty t)
	
(* constructors *)

let rec formula_of_heap_1 h pos = 
  mkBase h (P.mkTrue pos) VP.empty_vperm_sets top_flow [] pos

and formula_of_pure_1 p pos = mkBase HEmp p VP.empty_vperm_sets top_flow [] pos                (* pure formula has Empty heap *)

and formula_of_heap_with_flow h f pos = mkBase h (P.mkTrue pos) VP.empty_vperm_sets f [] pos

and formula_of_pure_with_flow p f a pos = mkBase HEmp p VP.empty_vperm_sets f a pos            (* pure formula has Empty heap *)

and formula_of_pure_with_flow_htrue p f a pos =
  let h = if Ipure.isConstTrue p then HTrue else HEmp in
  mkBase h p VP.empty_vperm_sets f a pos (* pure formula has HTRUE heap *)

and formula_of_pure_with_flow_emp p f a pos =
  let h = HEmp in
  mkBase h p VP.empty_vperm_sets f a pos (* pure formula has HTRUE heap *)

and formula_of_vperm_pure_with_flow_htrue p vp f a pos =
  let h = if Ipure.isConstTrue p then HTrue else HEmp in
  mkBase h p vp f a pos

and formula_of_vperm_pure_with_flow_emp p vp f a pos =
  let h = (* if Ipure.isConstTrue p then HTrue else *) HEmp in
  mkBase h p vp f a pos

and one_formula_of_formula f =
  match f with
    | Base b ->
        one_formula_of_formula_base b
    | Exists b ->
        one_formula_of_formula_exists b
    | _ ->
        Error.report_error	{Error.error_loc = no_pos; Error.error_text = "expected base formula, not found"} 

and one_formula_of_formula_base b =
  {formula_heap = b.formula_base_heap;
   formula_pure = b.formula_base_pure;
   formula_thread = None;
   formula_delayed = (P.mkTrue b.formula_base_pos);
   formula_pos = b.formula_base_pos}

and one_formula_of_formula_exists b =
  {formula_heap = b.formula_exists_heap;
   formula_pure = b.formula_exists_pure;
   formula_thread = None;
   formula_delayed = (P.mkTrue b.formula_exists_pos);
   formula_pos = b.formula_exists_pos}

and add_formula_and (a: one_formula list) (f:formula) : formula =
  match f with
    | Or o -> mkOr (add_formula_and a o.formula_or_f1) (add_formula_and a o.formula_or_f2) o.formula_or_pos
    | Base b -> Base { b with formula_base_and = a@b.formula_base_and}
    | Exists e -> Exists {e with formula_exists_and = a@e.formula_exists_and}

and isConstFalse f0 = match f0 with
  | Base f -> begin
	  let h, p = f.formula_base_heap, f.formula_base_pure in
		match h with
		  | HFalse -> true
		  | _ -> (P.isConstFalse p)
	end
  | _ -> false

(* TRUNG TODO: should change name to isConstEmp ? *)
and isConstTrue f0 = match f0 with
  | Base f -> begin
	  let h, p = f.formula_base_heap, f.formula_base_pure in
		match h with
		  | HEmp -> (P.isConstTrue p && VP.is_empty_vperm_sets f.formula_base_vperm)
		  | _ -> false
	end
  | _ -> false

and isEConstFalse f0 = match f0 with
  | EBase b -> isConstFalse b.formula_struc_base
  | EList b -> List.for_all (fun (_,c)->isEConstFalse c) b
  | _ -> false


and isEConstTrue f0 = match f0 with
  | EBase b -> isConstTrue b.formula_struc_base && b.formula_struc_continuation=None
  | EList b -> List.exists (fun (_,c)-> isEConstTrue c) b
  | _ -> false

and get_pre_post f0=
  let btrue =  mkTrue_nf no_pos in
  match f0 with
    | EBase b -> begin
        (* if isConstTrue b.formula_struc_base then *)
        match b.formula_struc_continuation with
          | Some post -> begin
              match post with
                | EAssume pb -> begin
                      match pb.formula_assume_struc with
                        | EBase p -> true,b.formula_struc_base,p.formula_struc_base
                        | _ -> false,  b.formula_struc_base, btrue
                  end
                | _ -> false,  b.formula_struc_base, btrue
            end
          | None -> false,  b.formula_struc_base, btrue
      (* else false,b.formula_struc_base, btrue *)
      end
    | _ -> false, btrue, btrue

and mkTrue_nf p =  mkTrue n_flow p

(* TRUNG TODO: should change name to mkEmp ? *)
and mkTrue flow pos = Base { 
  formula_base_heap = HEmp;
  formula_base_pure = P.mkTrue pos;
  formula_base_vperm = VP.empty_vperm_sets;
  formula_base_flow = flow;
  formula_base_and = [];
  formula_base_pos = pos }

and mkFalse flow pos = Base { 
  formula_base_heap = HFalse;
  formula_base_pure = P.mkFalse pos;
  formula_base_vperm = VP.empty_vperm_sets;
  formula_base_flow = flow;
  formula_base_and = [];
  formula_base_pos = pos }

and mkTrivAssume flow pos = EAssume {
		formula_assume_simpl = mkTrue flow pos; 
		formula_assume_struc = mkETrue flow pos;
		formula_assume_lbl = (-1,"");
		formula_assume_ensures_type = None;
	}

and mkETrueTrue flow flow2 pos = EBase {
		 formula_struc_explicit_inst = [];
		 formula_struc_implicit_inst = [];
		 formula_struc_exists = [];
		 formula_struc_base = mkTrue flow pos;
                 formula_struc_is_requires = true;
		 formula_struc_continuation = Some (mkTrivAssume flow2 pos) ;
		 formula_struc_pos = pos	}

and mkEAssume simp struc lbl ens = EAssume{
		formula_assume_simpl = simp;
		formula_assume_struc = struc;
		formula_assume_lbl = lbl;
		formula_assume_ensures_type = ens;
	}

and mkETrue flow pos = EBase {
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = mkTrue flow pos;
    formula_struc_is_requires = false;
    formula_struc_continuation = None;
    formula_struc_pos = pos	}

and mkEFalse flow pos = EBase {
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = mkFalse flow pos;
    formula_struc_is_requires = false;
    formula_struc_continuation = None;
    formula_struc_pos = pos	}

and mkEFalseF () = mkEFalse false_flow no_pos
and mkETrueF () = mkETrue n_flow no_pos
and mkETrueTrueF () = mkETrueTrue n_flow n_flow no_pos

(*and mkEOr (f1:struc_formula) (f2:struc_formula) pos :struc_formula= 
	if isEConstTrue f1 || isEConstTrue f2 then mkETrue top_flow pos
  else if isEConstFalse f1 then f2
  else if isEConstFalse f2 then f1
  else EOr { formula_struc_or_f1 = f1; formula_struc_or_f2 = f2; formula_struc_or_pos = pos}*)

and mkEBase ei ii e b (c:struc_formula option) l= EBase {
    formula_struc_explicit_inst = ei;
    formula_struc_implicit_inst = ii;
    formula_struc_exists = e;
    formula_struc_base = b;
    formula_struc_is_requires = c!=None;
    formula_struc_continuation = c;
    formula_struc_pos = l;}
  
and mkOr f1 f2 pos =
  let raw =  Or { formula_or_f1 = f1;
			formula_or_f2 = f2;
			formula_or_pos = pos } in
   if (formula_same_flow f1 f2) then
    (* if (isConstTrue f1) then f1 *)
    (* else if (isConstTrue f2) then f2 *)
    (* else *) if (isConstFalse f1) then f2
    else if (isConstFalse f2) then f1
    else raw
   else raw
   
and disj_of_list l default pos = match l with
	| [] -> if default then mkTrue n_flow pos else mkFalse false_flow pos
	| h::t -> List.fold_left (fun c1 c2-> mkOr c1 c2 pos) h t

and mkBase_wo_flow (h : h_formula) (p : P.formula) (vp: VP.vperm_sets) (a: one_formula list) pos =
  mkBase h p vp top_flow a pos

and mkBase (h : h_formula) (p : P.formula) (vp: VP.vperm_sets) flow (a: one_formula list) pos = 
  match h with
  | HFalse -> mkFalse flow pos
  | _ -> 
    if P.isConstFalse p then mkFalse flow pos
    else 
      Base { 
        formula_base_heap = h;
        formula_base_pure = p;
        formula_base_vperm = vp;
        formula_base_flow = flow;
        formula_base_and = a;
        formula_base_pos = pos }

and mkExists (qvars : (ident * primed) list) (h : h_formula) (p : P.formula) (vp: VP.vperm_sets) 
  flow (a: one_formula list) pos = 
  match h with
  | HFalse -> mkFalse flow pos
  | _ ->
    if P.isConstFalse p then mkFalse flow pos
    else
      Exists { 
        formula_exists_qvars = qvars;
        formula_exists_heap = h;
        formula_exists_pure = p;
        formula_exists_vperm = vp;
        formula_exists_flow = flow;
        formula_exists_and = a;
        formula_exists_pos = pos }

and mkOneFormula (h : h_formula) (p : P.formula) (dl : P.formula) id pos = 
  {formula_heap =h;
   formula_pure = p;
   formula_thread = id;
   formula_delayed = dl;
   formula_pos =pos}

and mkStar f1 f2 pos = match f1 with
  | HFalse -> HFalse
  | HEmp -> f2
  | _ -> match f2 with
    | HFalse -> HFalse
    | HEmp -> f1
    | _ -> if (f1 = HTrue) && (f2 = HTrue) then HTrue
           else Star { h_formula_star_h1 = f1;
                       h_formula_star_h2 = f2;
                       h_formula_star_pos = pos }
                       
and mkStarMinus f1 f2 pos = match f1 with
  | HFalse -> HFalse
  | HEmp -> f2
  | _ -> match f2 with
    | HFalse -> HFalse
    | HEmp -> f1
    | _ -> if (f1 = HTrue) && (f2 = HTrue) then HTrue
           else StarMinus { h_formula_starminus_h1 = f1;
                       h_formula_starminus_h2 = f2;
                       h_formula_starminus_pos = pos }

and mkConj f1 f2 pos =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else Conj { h_formula_conj_h1 = f1;
              h_formula_conj_h2 = f2;
              h_formula_conj_pos = pos }

and mkConjStar f1 f2 pos =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else ConjStar { h_formula_conjstar_h1 = f1;
              h_formula_conjstar_h2 = f2;
              h_formula_conjstar_pos = pos }

and mkConjConj f1 f2 pos =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else ConjConj { h_formula_conjconj_h1 = f1;
              h_formula_conjconj_h2 = f2;
              h_formula_conjconj_pos = pos }                            

and mkPhase f1 f2 pos =
  match f1 with
  | HFalse -> HFalse
  | _ -> match f2 with
    | HFalse -> HFalse
    | _ -> Phase { h_formula_phase_rd = f1;
                   h_formula_phase_rw = f2;
                   h_formula_phase_pos = pos }

and mkThreadNode c id rsr dl perm ofl l =
  ThreadNode { h_formula_thread_node = c;
             h_formula_thread_name = id;
             h_formula_thread_resource = rsr;
             h_formula_thread_perm = perm;
             h_formula_thread_delayed = dl;
             h_formula_thread_label = ofl;
             h_formula_thread_pos = l }

and mkHeapNode_x c id ho deref dr split i f inv pd perm hl hl_i ofl l=
  HeapNode { h_formula_heap_node = c;
             h_formula_heap_name = id;
             h_formula_heap_deref = deref;
             h_formula_heap_derv = dr;
             h_formula_heap_split = split;
             h_formula_heap_imm = i;
             h_formula_heap_imm_param = hl_i;
             h_formula_heap_full = f;
             h_formula_heap_with_inv = inv;
             h_formula_heap_pseudo_data = pd;
             h_formula_heap_perm = perm; 
             h_formula_heap_arguments = hl;
             h_formula_heap_ho_arguments = ho;
             h_formula_heap_label = ofl;
             h_formula_heap_pos = l }

and mkHeapNode  c id ho deref dr split i f inv pd perm hl hl_i ofl l=
  Debug.no_1 "mkHeapNode" (fun (name, _) -> name) !print_h_formula 
      (fun _ -> mkHeapNode_x c id ho deref dr split i f inv pd perm hl hl_i ofl l ) c

and mkHeapNode2 c id ho deref dr split i f inv pd perm ohl hl_i ofl l = 
  HeapNode2 { h_formula_heap2_node = c;
              h_formula_heap2_name = id;
              h_formula_heap2_deref = deref;
              h_formula_heap2_derv = dr;
              h_formula_heap2_split = split;
              h_formula_heap2_imm = i;
              h_formula_heap2_imm_param = hl_i;
              h_formula_heap2_full = f;
              h_formula_heap2_with_inv = inv;
              h_formula_heap2_pseudo_data = pd;
              h_formula_heap2_perm = perm;
              h_formula_heap2_arguments = ohl;
              h_formula_heap2_ho_arguments = ho;
              h_formula_heap2_label = ofl;
              h_formula_heap2_pos = l }

and pos_of_formula f0 = match f0 with
  | Base f -> f.formula_base_pos
  | Or f -> f.formula_or_pos
  | Exists f -> f.formula_exists_pos

and pos_of_struc_formula f0 = match f0 with 
	| ECase b -> b.formula_case_pos
	| EBase b -> b.formula_struc_pos
	| EAssume b -> pos_of_formula b.formula_assume_simpl
	| EInfer b -> b.formula_inf_pos
	| EList b -> try pos_of_struc_formula (snd (List.hd b))
                     with _ -> no_pos

and flow_of_formula f1 = match f1 with
  | Base b-> Some b.formula_base_flow
  | Exists b -> Some b.formula_exists_flow
  | Or o -> 
    let fl1 = flow_of_formula o.formula_or_f1 in
    let fl2 = flow_of_formula o.formula_or_f2 in
    match fl1,fl2 with
      | Some f1, Some f2 -> if (f1=f2) then Some f1 else None
      | _ -> None

and formula_same_flow f1 f2 = 
  let f1 = flow_of_formula f1 in
  let f2 = flow_of_formula f2 in
  match f1, f2 with
    | Some f1, Some f2 -> f1=f2
    | _ -> false
  
(**
 * An Hoa : function to extract the root of a quantified id.
 **)
and extract_var_from_id (id,p) =
	let ids = Str.split (Str.regexp "\\.") id in
	let var = List.hd ids in
		(var,p)
and ann_opt_to_ann_lst (ann_opt_lst: P.ann option list) (default_ann: P.ann): P.ann list = 
  match ann_opt_lst with
    | [] -> []
    | (Some ann0) :: t ->  ann0 :: (ann_opt_to_ann_lst t default_ann)
    | (None) :: t      ->  default_ann :: (ann_opt_to_ann_lst t default_ann) 

and fv_imm ann = match ann with
  | P.ConstAnn _ -> []
  | P.PolyAnn (id,_) -> [id]

and fv_imm_opt ann = 
  match ann with
    | Some ann -> fv_imm ann
    | None     -> [] 

and fv_imm_list ann_lst = 
  List.fold_left (fun acc a -> acc @ (fv_imm a)) [] ann_lst

and fv_imm_opt_list ann_lst = 
  List.fold_left (fun acc a -> acc @ (fv_imm_opt a)) [] ann_lst

and h_fv_ann (f:h_formula):(ident*primed) list = 
  let rec helper f = 
    match f with   
      | Conj ({h_formula_conj_h1 = h1; 
	h_formula_conj_h2 = h2; 
	h_formula_conj_pos = pos})
      | ConjStar ({h_formula_conjstar_h1 = h1; 
	h_formula_conjstar_h2 = h2; 
	h_formula_conjstar_pos = pos})
      | ConjConj ({h_formula_conjconj_h1 = h1; 
	h_formula_conjconj_h2 = h2; 
	h_formula_conjconj_pos = pos})	   	   
      | Phase ({h_formula_phase_rd = h1; 
	h_formula_phase_rw = h2; 
	h_formula_phase_pos = pos}) 
      | StarMinus ({h_formula_starminus_h1 = h1; 
	h_formula_starminus_h2 = h2; 
	h_formula_starminus_pos = pos})
      | Star ({h_formula_star_h1 = h1; 
	h_formula_star_h2 = h2; 
	h_formula_star_pos = pos}) ->  Gen.BList.remove_dups_eq (=) ((helper h1)@(helper h2))
      | HeapNode {h_formula_heap_imm = imm; 
        h_formula_heap_imm_param = imm_param; } 
      | HeapNode2 {h_formula_heap2_imm = imm;
        h_formula_heap2_imm_param = imm_param; } ->
            let imm_vars = fv_imm imm in
            let imm_param_vars = fv_imm_opt_list imm_param in
            Gen.BList.remove_dups_eq (=) imm_vars@imm_param_vars
      | ThreadNode _
      | HRel _
      | HTrue 
      | HFalse 
      | HEmp | HVar _ -> [] 
  in helper f

and heap_fv_ann_one_formula (f:one_formula):(ident*primed) list =  (h_fv_ann f.formula_heap)

and fv_ann_formula_x (f:formula):(ident*primed) list = 
  let rec helper f = 
    match f with
      | Base b-> 
            let avars = List.concat (List.map heap_fv_ann_one_formula  b.formula_base_and) in
            let hvars = (h_fv_ann b.formula_base_heap) in
            Gen.BList.remove_dups_eq (=) hvars@avars
      | Exists b-> 
            let avars = List.concat (List.map heap_fv_ann_one_formula  b.formula_exists_and) in
            let hvars = (h_fv_ann b.formula_exists_heap) in
	    Gen.BList.difference_eq (=) (hvars@avars) b.formula_exists_qvars
      | Or b-> Gen.BList.remove_dups_eq (=) ((helper b.formula_or_f1)@(helper b.formula_or_f2))
  in helper f 

and fv_ann_formula (f:formula):(ident*primed) list = 
  let pr = !print_formula in
  let pr_out = pr_list (pr_id fst) in
  Debug.no_1 "fv_ann_formula" pr pr_out fv_ann_formula_x f

and collect_annot_vars f  = fv_ann_formula f


and h_fv (f:h_formula):(ident*primed) list = match f with   
  | Conj ({h_formula_conj_h1 = h1; 
	   h_formula_conj_h2 = h2; 
	   h_formula_conj_pos = pos})
  | ConjStar ({h_formula_conjstar_h1 = h1; 
	   h_formula_conjstar_h2 = h2; 
	   h_formula_conjstar_pos = pos})
  | ConjConj ({h_formula_conjconj_h1 = h1; 
	   h_formula_conjconj_h2 = h2; 
	   h_formula_conjconj_pos = pos})	   	   
  | Phase ({h_formula_phase_rd = h1; 
	   h_formula_phase_rw = h2; 
	   h_formula_phase_pos = pos}) 
  | StarMinus ({h_formula_starminus_h1 = h1; 
	   h_formula_starminus_h2 = h2; 
	   h_formula_starminus_pos = pos})
  | Star ({h_formula_star_h1 = h1; 
	   h_formula_star_h2 = h2; 
	   h_formula_star_pos = pos}) ->  Gen.BList.remove_dups_eq (=) ((h_fv h1)@(h_fv h2))
(*WN:TODO:DONE*)
 | HeapNode {h_formula_heap_node = name ;
          (* An Hoa : problem detected and fix - name is a 
             quantified id so that we need to extract the 
             real information inside *)
              h_formula_heap_perm = perm; (*LDK*)
              h_formula_heap_imm = imm; 
              h_formula_heap_imm_param = ann_param;
              h_formula_heap_ho_arguments = ho_b;
              h_formula_heap_arguments = b} ->
     let perm_vars = (fv_iperm ()) perm in
     let imm_vars =  fv_imm imm in
     let prm_ann =  List.flatten (List.map fv_imm  (ann_opt_to_ann_lst ann_param imm)) in
     let imm_vars = if (!Globals.allow_field_ann) then imm_vars@prm_ann else imm_vars in
     let hvars = List.concat (List.map (fun ff -> heap_fv ff.rflow_base) ho_b) in
     Gen.BList.remove_dups_eq (=) (hvars@imm_vars@perm_vars@((extract_var_from_id name):: (List.concat (List.map Ipure.afv b))))
  | HeapNode2 { h_formula_heap2_node = name ;
                h_formula_heap2_perm = perm; (*LDK*)
                h_formula_heap2_imm = imm;
                h_formula_heap2_ho_arguments = ho_b;
		h_formula_heap2_arguments = b}-> 
     let perm_vars =  (fv_iperm ()) perm in
     let imm_vars =  fv_imm imm in
     let hvars = List.concat (List.map (fun ff -> heap_fv ff.rflow_base) ho_b) in
     Gen.BList.remove_dups_eq (=)  (hvars@imm_vars@perm_vars@((extract_var_from_id name):: (List.concat (List.map (fun c-> (Ipure.afv (snd c))) b) )))
 | ThreadNode {h_formula_thread_node = name ;
              h_formula_thread_perm = perm;
              h_formula_thread_delayed = dl;
              h_formula_thread_resource = rsr} ->
     let perm_vars = (fv_iperm ()) perm in
     let rsr_vars = heap_fv rsr in (*TOCHECK: currently recursively look into resource*)
     (*This is h_fv, hence, dl is not included*)
     Gen.BList.remove_dups_eq (=) (perm_vars@rsr_vars@([extract_var_from_id name]))
  | HRel (_, args, _)->
      let args_fv = List.concat (List.map Ipure.afv args) in
	  Gen.BList.remove_dups_eq (=) args_fv
  (* TODO:WN:HVar -*)
  | HVar (v,ls) -> [(v,Unprimed)]@(List.map (fun v -> (v,Unprimed)) ls) (* TODO:HO -prime? *)
  | HTrue -> []
  | HFalse -> [] 
  | HEmp -> [] 

and get_hprel_svl_hf (f0:h_formula):(ident*primed) list =
  let rec helper f =match f with
    | Conj ({h_formula_conj_h1 = h1; 
      h_formula_conj_h2 = h2; 
      h_formula_conj_pos = pos})
    | ConjStar ({h_formula_conjstar_h1 = h1; 
      h_formula_conjstar_h2 = h2; 
      h_formula_conjstar_pos = pos})
    | ConjConj ({h_formula_conjconj_h1 = h1; 
      h_formula_conjconj_h2 = h2;
      h_formula_conjconj_pos = pos})
    | Phase ({h_formula_phase_rd = h1;
      h_formula_phase_rw = h2;
      h_formula_phase_pos = pos}) 
    | StarMinus ({h_formula_starminus_h1 = h1; 
      h_formula_starminus_h2 = h2; 
      h_formula_starminus_pos = pos})
    | Star ({h_formula_star_h1 = h1; 
      h_formula_star_h2 = h2; 
      h_formula_star_pos = pos}) ->  Gen.BList.remove_dups_eq (=) ((helper h1)@(helper h2))
    | HRel (_, args, _)->
          let args_fv = List.concat (List.map Ipure.afv args) in
          Gen.BList.remove_dups_eq (=) args_fv
    | HeapNode _
    | HeapNode2 _
    | ThreadNode _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> []
  in
  helper f0

and heap_fv_one_formula (f:one_formula):(ident*primed) list =  (h_fv f.formula_heap)

(*TO CHECK: how about formula_and*)
and heap_fv (f:formula):(ident*primed) list = match f with
	| Base b-> 
        let avars = List.concat (List.map heap_fv_one_formula b.formula_base_and) in
        let hvars = (h_fv b.formula_base_heap) in
        Gen.BList.remove_dups_eq (=) hvars@avars
	| Exists b-> 
        let avars = List.concat (List.map heap_fv_one_formula b.formula_exists_and) in
        let hvars =  (h_fv b.formula_exists_heap) in
        Gen.BList.difference_eq (=) (Gen.BList.remove_dups_eq (=) hvars@avars)
             b.formula_exists_qvars 
	| Or b-> Gen.BList.remove_dups_eq (=) ((heap_fv b.formula_or_f1)@(heap_fv b.formula_or_f2))

and struc_hp_fv (f:struc_formula): (ident*primed) list =  match f with
	| EBase b-> Gen.BList.difference_eq (=) ((Gen.fold_opt struc_hp_fv b.formula_struc_continuation)@(heap_fv b.formula_struc_base)) 
					(b.formula_struc_explicit_inst@b.formula_struc_implicit_inst)
	| ECase b-> Gen.fold_l_snd struc_hp_fv b.formula_case_branches
	| EAssume b-> heap_fv b.formula_assume_simpl
        | EInfer b -> struc_hp_fv b.formula_inf_continuation
	| EList b -> Gen.BList.remove_dups_eq (=) (Gen.fold_l_snd struc_hp_fv b)

and struc_case_fv (f:struc_formula): (ident*primed) list =  match f with
	| EBase b-> Gen.BList.difference_eq (=)(Gen.fold_opt struc_case_fv b.formula_struc_continuation)
					(b.formula_struc_explicit_inst@b.formula_struc_implicit_inst)
	| ECase b-> List.fold_left (fun a (c1,c2)-> (P.fv c1)@(struc_case_fv c2)@a)
					[] b.formula_case_branches
	| EAssume b-> []
        | EInfer b -> struc_case_fv b.formula_inf_continuation
	| EList b -> Gen.BList.remove_dups_eq (=) (Gen.fold_l_snd struc_case_fv b)

(*TO CHECK: how about formula_and*)
and unbound_heap_fv (f:formula):(ident*primed) list = match f with
	| Base b-> 
        let avars = List.concat (List.map heap_fv_one_formula b.formula_base_and) in
        let hvars = Gen.BList.difference_eq (=) (h_fv b.formula_base_heap) (get_hprel_svl_hf b.formula_base_heap) in
        Gen.BList.remove_dups_eq (=) hvars@avars
	| Exists b-> 
        let avars = List.concat (List.map heap_fv_one_formula b.formula_exists_and) in
        let hvars = Gen.BList.difference_eq (=) (h_fv b.formula_exists_heap) (get_hprel_svl_hf b.formula_exists_heap) in
		Gen.BList.difference_eq (=) (hvars@avars) b.formula_exists_qvars
	| Or b-> Gen.BList.remove_dups_eq (=) ((unbound_heap_fv b.formula_or_f1)@(unbound_heap_fv b.formula_or_f2))

and struc_free_vars with_inst (f:struc_formula) :(ident*primed) list= match f with
	| EBase b -> Gen.BList.remove_dups_eq (=) (Gen.BList.difference_eq (=) 
					((all_fv b.formula_struc_base)@ (Gen.fold_opt (struc_free_vars with_inst) b.formula_struc_continuation))
           ( (if with_inst then [] else b.formula_struc_explicit_inst@ b.formula_struc_implicit_inst) @ b.formula_struc_exists))
	| ECase b -> 
				let fvc = List.fold_left (fun a (c1,c2)-> 
				a@(struc_free_vars with_inst c2 )@(Ipure.fv c1)) [] b.formula_case_branches in
				Gen.BList.remove_dups_eq (=) fvc		
	| EAssume b-> all_fv b.formula_assume_simpl
	| EInfer b -> Gen.BList.remove_dups_eq (=) ( struc_free_vars with_inst b.formula_inf_continuation)
	| EList b -> Gen.BList.remove_dups_eq (=) (Gen.fold_l_snd (struc_free_vars with_inst) b)
	
	
 
and struc_split_fv_debug f0 wi =
  Debug.no_2 "struc_split_fv" (!print_struc_formula) string_of_bool 
      (fun (l1,l2) -> (string_of_spec_var_list l1)^"|"^(string_of_spec_var_list l2)) struc_split_fv_a f0 wi

and struc_split_fv f0 wi =
  Debug.no_2 "struc_split_fv" (!print_struc_formula) string_of_bool 
      (fun (l1,l2) -> (string_of_spec_var_list l1)^"|"^(string_of_spec_var_list l2)) struc_split_fv_a f0 wi


and struc_split_fv_a (f0:struc_formula) with_inst:((ident*primed) list) * ((ident*primed) list)= 
  let rde = Gen.BList.remove_dups_eq (=)  in
  let diffe = Gen.BList.difference_eq (=)  in
  let rec helper f = match f with
    | EBase b ->
	  let fvb = all_fv b.formula_struc_base in
	  let prc,psc = match b.formula_struc_continuation with | None -> ([],[]) | Some l -> helper l in
	  let rm = (if with_inst then [] else b.formula_struc_explicit_inst@ b.formula_struc_implicit_inst) @ b.formula_struc_exists in
	  (rde (diffe (fvb@prc) rm),(diffe psc rm))
    | ECase b ->
	  let prl,psl = List.fold_left (fun (a1,a2) (c1,c2)-> 
	      let prc, psc = helper c2 in
	      ((a1@prc@(Ipure.fv c1)),psc@a2)) ([],[]) b.formula_case_branches in
	  (rde prl, rde psl)
    | EAssume b-> ([],all_fv b.formula_assume_simpl)
    | EInfer b -> helper b.formula_inf_continuation
    | EList b->
	  let prl, pcl = List.split (List.map (fun c-> helper (snd c)) b) in
	  (rde (List.concat prl), rde (List.concat pcl)) in
  helper f0


and all_fv_one_formula (f:one_formula):(ident*primed) list = 
  Gen.BList.remove_dups_eq (=) ((h_fv f.formula_heap)@(Ipure.fv f.formula_pure))

and all_fv (f:formula):(ident*primed) list = match f with
	| Base b->
        let avars= List.concat (List.map all_fv_one_formula b.formula_base_and) in
       Gen.BList.remove_dups_eq (=) ((h_fv b.formula_base_heap)@(Ipure.fv b.formula_base_pure)@avars)
	| Exists b-> 
        let avars= (List.concat (List.map all_fv_one_formula b.formula_exists_and)) @(h_fv b.formula_exists_heap)@(Ipure.fv b.formula_exists_pure) in
		Gen.BList.difference_eq (=) (Gen.BList.remove_dups_eq (=) avars) b.formula_exists_qvars 
	| Or b-> Gen.BList.remove_dups_eq (=) ((all_fv b.formula_or_f1)@(all_fv b.formula_or_f2))
	
and add_quantifiers (qvars : (ident*primed) list) (f : formula) : formula = match f with
  | Base ({ 
      formula_base_heap = h;
      formula_base_pure = p;
      formula_base_vperm = vp; 
      formula_base_flow = f;
      formula_base_and = a;
      formula_base_pos = pos }) -> 
    mkExists qvars h p vp f a pos (*TO CHECK*)
  | Exists ({
      formula_exists_qvars = qvs; 
      formula_exists_heap = h; 
      formula_exists_pure = p;
      formula_exists_vperm = vp;
      formula_exists_flow = f;
      formula_exists_and = a;
      formula_exists_pos = pos }) ->
    let new_qvars = Gen.BList.remove_dups_eq (=) (qvs @ qvars) in
    mkExists new_qvars h p vp f a pos (*TO CHECK*)
  | _ -> failwith ("add_quantifiers: invalid argument")

and push_exists (qvars : (ident*primed) list) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
	  let new_f1 = push_exists qvars f1 in
	  let new_f2 = push_exists qvars f2 in
	  let resform = mkOr new_f1 new_f2 pos in
		resform
  | _ -> add_quantifiers qvars f

and formula_to_struc_formula (f:formula):struc_formula =
  let rec helper (f:formula):struc_formula = match f with
    | Base b-> EBase {
	  formula_struc_explicit_inst =[];
	  formula_struc_implicit_inst = [];
	  formula_struc_exists = [];
	  formula_struc_base = f;
          formula_struc_is_requires = false;
	  formula_struc_continuation = None;
	  formula_struc_pos = b.formula_base_pos}
    | Exists b-> EBase {
	  formula_struc_explicit_inst =[];
	  formula_struc_implicit_inst = [];
	  formula_struc_exists = [];
	  formula_struc_base = f;
          formula_struc_is_requires = false;
	  formula_struc_continuation = None;
	  formula_struc_pos = b.formula_exists_pos}
    | Or b->  EList [(empty_spec_label_def,helper b.formula_or_f1);(empty_spec_label_def,helper b.formula_or_f2)] in
  Debug.no_1 "formula_to_struc_formula" !print_formula !print_struc_formula helper f

(* split a conjunction into heap constraints, pure pointer constraints, *)
(* and Presburger constraints *)
and split_components (f : formula) =  match f with
    | Base ({
        formula_base_heap = h; 
        formula_base_pure = p; 
        formula_base_vperm = vp;
        formula_base_and = a;
        formula_base_flow =fl }) -> (h, p, vp, fl, a)
    | Exists ({
        formula_exists_heap = h;
        formula_exists_pure = p;
        formula_exists_vperm = vp;
        formula_exists_and = a;
        formula_exists_flow = fl }) -> (h, p, vp, fl, a)
    | _ -> failwith ("split_components: don't expect OR")

and split_quantifiers (f : formula) : ( (ident * primed) list * formula) = match f with
  | Exists ({
      formula_exists_qvars = qvars; 
      formula_exists_heap =  h; 
      formula_exists_pure = p;
      formula_exists_vperm = vp; 
      formula_exists_flow = f;
      formula_exists_and = a;
      formula_exists_pos = pos}) -> (qvars, mkBase h p vp f a pos)
  | Base _ -> ([], f)
  | _ -> failwith ("split_quantifiers: invalid argument")

(*var substitution*)

and subst sst (f : formula) = match sst with
  | s :: rest -> subst rest (apply_one s f)
  | [] -> f 

(*subst all including existential variables*)
and subst_all sst (f : formula) = 
  let rec helper sst f =
    match sst with
      | s :: rest -> helper rest (apply_one_all s f)
      | [] -> f 
  in helper sst f

(*subst all including existential variables*)
and subst_pointer sst (f : formula) vars = 
  let rec helper sst f =
    match sst with
      | s :: rest -> helper rest (apply_one_pointer s f vars)
      | [] -> f 
  in helper sst f

and subst_var (fr, t) (o : (ident*primed)) = if (Ipure.eq_var fr o) then t else o
and subst_var_list ft (o : (ident*primed)) = 
  let r = List.filter (fun (c1,c2)-> (Ipure.eq_var c1 o) ) ft in
  match r with 
    | [] -> o
    | _ -> snd (List.hd r)

and split_one_formula (f : one_formula) = f.formula_heap, f.formula_pure, f.formula_delayed,f.formula_thread, f.formula_pos

and one_formula_apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : one_formula) =
  let h,p,dl,id,pos = split_one_formula f in
  {formula_heap = h_apply_one s h;
   formula_pure = Ipure.apply_one s p;
   formula_delayed = Ipure.apply_one s dl;
   formula_thread = (match id with 
     | None -> None
     | Some v -> Some (subst_var s v));
   formula_pos = pos} 



and one_formula_apply_one_pointer ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : one_formula) vars =
  let h,p,dl,id,pos = split_one_formula f in
  let closure = List.map (fun v -> Ipure.find_closure_pure v p) vars in
  let closure = List.concat closure in
  let new_h,ps = h_apply_one_pointer s h closure in
  let ps1,ps2 = Ipure.partition_pointer closure p in
  (*do not rename those in ps1*)
  let new_p = Ipure.conj_of_list ps2 in
  let new_p1 =  Ipure.apply_one s new_p in
  (*look for the special case where x'=x should be translated to x_new=x_old*)
  (*note that those formulas such as x'=x+1 are already captured in the new_p1*)
  let ps1 = List.map (fun p -> P.trans_special_formula s p vars) ps1 in
  (*after all, convert x' to x to represent the fact that the original
  node remain unchanged, only its value is changed*)
  let new_sst = List.fold_left (fun sst (id,p) ->
        let unprimed_param = (id,Unprimed) in
        let primed_param = (id,Primed) in
        let sub = (primed_param,unprimed_param) in
        (sub::sst)
  ) [] vars
  in
  let ps1 = List.map (fun p -> Ipure.subst new_sst p) ps1 in
  let new_p2 = Ipure.conj_of_list ((new_p1::ps1)@ps) in
  (***************)
  {formula_heap = new_h;
   formula_pure = new_p2;
   formula_delayed = dl; (*TO CHECK*)
   formula_thread = (match id with 
     | None -> None
     | Some v -> Some (subst_var s v));
   formula_pos = pos}

and apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : formula) = match f with
  | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos }) -> 
    Or ({ formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos })
  | Base ({
      formula_base_heap = h;
      formula_base_pure = p;
      formula_base_vperm = vp;
      formula_base_flow = fl;
      formula_base_and = a;
      formula_base_pos = pos }) ->
    Base ({
      formula_base_heap = h_apply_one s h;
      formula_base_pure = Ipure.apply_one s p;
      formula_base_vperm = VP.vp_apply_one s vp;
      formula_base_flow = fl;
      formula_base_and = List.map (one_formula_apply_one s) a;
      formula_base_pos = pos })
  | Exists ({
      formula_exists_qvars = qsv;
      formula_exists_heap = qh;
      formula_exists_pure = qp;
      formula_exists_vperm = vp;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_pos = pos }) ->
    if List.mem (fst fr) (List.map fst qsv) then f
    else Exists ({
      formula_exists_qvars = qsv;
      formula_exists_heap =  h_apply_one s qh;
      formula_exists_pure = Ipure.apply_one s qp;
      formula_exists_vperm = VP.vp_apply_one s vp;
      formula_exists_flow = fl;
      formula_exists_and = List.map (one_formula_apply_one s) a;
      formula_exists_pos = pos })

(*subst all including existential variables*)
and apply_one_all ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : formula) = 
  match f with
  | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos }) ->
    Or ({formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos})
  | Base ({
      formula_base_heap = h;
      formula_base_pure = p;
      formula_base_vperm = vp;
      formula_base_flow = fl;
      formula_base_and = a;
      formula_base_pos = pos }) ->
    Base ({
      formula_base_heap = h_apply_one s h;
      formula_base_pure = Ipure.apply_one s p;
      formula_base_vperm = VP.vp_apply_one s vp;
      formula_base_flow = fl;
      formula_base_and = List.map (one_formula_apply_one s) a;
      formula_base_pos = pos })
  | Exists ({
      formula_exists_qvars = qsv;
      formula_exists_heap = qh;
      formula_exists_vperm = vp;
      formula_exists_pure = qp;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_pos = pos }) ->
    (*also substitute exist vars*)
    let new_evars = List.map (subst_var s) qsv in
    Exists ({
      formula_exists_qvars = new_evars;
      formula_exists_heap =  h_apply_one s qh;
      formula_exists_vperm = VP.vp_apply_one s vp;
      formula_exists_pure = Ipure.apply_one s qp;
      formula_exists_flow = fl;
      formula_exists_and = List.map (one_formula_apply_one s) a;
      formula_exists_pos = pos })


and apply_one_pointer ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : formula) vars = 
  match f with
  | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos }) ->
    Or ({formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos})
  | Base ({
      formula_base_heap = h;
      formula_base_pure = p;
      formula_base_vperm = vp;
      formula_base_flow = fl;
      formula_base_and = a;
      formula_base_pos = pos }) ->
    (* let closure = List.map (fun v -> Ipure.find_closure_pure v p) vars in *)
    (* let closure = List.concat closure in *)
    let new_h,ps = h_apply_one_pointer s h [] (* closure *) in
    (* let ps1,ps2 = Ipure.partition_pointer [] (\* closure *\) p in *)
    (* (\*do not rename those in ps1*\) *)
    (* let new_p = Ipure.conj_of_list ps2 in *)
    (* let new_p1 =  Ipure.apply_one s new_p in *)
    (* let ps1 = List.map (fun p -> P.trans_special_formula s p vars) ps1 in *)
    (* let new_p2 = Ipure.conj_of_list ((new_p1::ps1)@ps) in *)
    (***************)
    Base ({
      formula_base_heap = new_h;
      formula_base_pure =  Ipure.apply_one s p (* new_p2 *);
      formula_base_vperm = VP.vp_apply_one s vp;
      formula_base_flow = fl;
      formula_base_and = List.map (fun f -> one_formula_apply_one_pointer s f vars) a;
      formula_base_pos = pos})
  | Exists ({
      formula_exists_qvars = qsv;
      formula_exists_heap = qh;
      formula_exists_pure = qp;
      formula_exists_vperm = vp;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_pos = pos }) ->
    let closure = List.map (fun v -> Ipure.find_closure_pure v qp) vars in
    let closure = List.concat closure in
    (* only need to consider existential variables that related to vars *)
    let closure = List.filter (fun v -> Gen.BList.mem_eq Ipure.eq_var v (qsv@vars)) closure in
    (* let closure = closure@vars in *)
    let new_h, ps = h_apply_one_pointer s qh closure in
    let ps1, ps2 = Ipure.partition_pointer closure qp in
    (* do not rename those in ps1 *)
    let new_p = Ipure.conj_of_list ps2 in
    let new_p1 =  Ipure.apply_one s new_p in
    let ps1 = List.map (fun p -> P.trans_special_formula s p vars) ps1 in
    (* after all, convert x' to x to represent the fact that the original
       node remain unchanged, only its value is changed *)
    let new_sst = List.fold_left (fun sst (id,p) ->
      let primed_param = (id, Primed) in
      let unprimed_param = (id, Unprimed) in
      let sub = (primed_param,unprimed_param) in
      (sub::sst)) [] vars
    in
    let ps1 = List.map (fun p -> Ipure.subst new_sst p) ps1 in
    (* let () = print_endline ("new_p1 = " ^ (!print_pure_formula new_p1)) in *)
    (* let () = print_endline ("ps1 = " ^ (pr_list !print_pure_formula ps1)) in *)
    let new_p2 = Ipure.conj_of_list ((new_p1::ps1)@ps) in
    (***************)
    (*also substitute exist vars*)
    let new_evars = List.map (subst_var s) qsv in
    Exists ({
      formula_exists_qvars = new_evars;
      formula_exists_heap = new_h;
      formula_exists_pure = new_p2;
      formula_exists_vperm = VP.vp_apply_one s vp;
      formula_exists_flow = fl;
      formula_exists_and = List.map (fun f -> one_formula_apply_one_pointer s f vars) a;
      formula_exists_pos = pos })

and h_apply_one_pointer ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : h_formula) vars : h_formula * (Ipure.formula list)= 
  let rec helper f =
    match f with
    | Conj ({h_formula_conj_h1 = h1; 
             h_formula_conj_h2 = h2; 
             h_formula_conj_pos = pos}) ->
        let new_h1,ps1 = helper h1 in
        let new_h2,ps2 = helper h2 in
        if (new_h1=HTrue) then new_h2,ps1@ps2 else
          if (new_h2=HTrue) then new_h1,ps1@ps2 else
            let node = Conj ({h_formula_conj_h1 = h1; 
                              h_formula_conj_h2 = h2; 
                              h_formula_conj_pos = pos})
            in (node,ps1@ps2)
    | Star ({h_formula_star_h1 = f1; 
             h_formula_star_h2 = f2; 
             h_formula_star_pos = pos}) ->
        let new_h1,ps1 = helper f1 in
        let new_h2,ps2 = helper f2 in
        if (new_h1=HTrue) then new_h2,ps1@ps2 else
          if (new_h2=HTrue) then new_h1,ps1@ps2 else
            let node = Star ({h_formula_star_h1 = h_apply_one s f1; 
                              h_formula_star_h2 = h_apply_one s f2; 
                              h_formula_star_pos = pos})
            in (node,ps1@ps2)
    | HeapNode ({h_formula_heap_node = x; 
                 h_formula_heap_name = c; 
                 h_formula_heap_arguments = args;
                 h_formula_heap_pos = pos} as h_node) ->
        let b,_ = Globals.is_program_pointer c in
        let node = HeapNode {h_node with h_formula_heap_node = subst_var s x; 
                             h_formula_heap_arguments = List.map (Ipure.e_apply_one s) args;
                             h_formula_heap_pos = pos}
        in
        if ((not b) || (List.length args != 1))  then
          (node,[])
        else
          (*convert pointer heap node to equality*)
          (*if is a pointer, expecting a single argument*)
          let arg = List.hd args in
          (match arg with
            | P.Var (v,_) ->
                if Gen.BList.mem_eq P.eq_var v vars then
                  let p = P.mkEqVarExp x v pos in
                  (HTrue,[p])
                else
                  (node,[])
            | _ ->
                (node,[]))
    | ThreadNode _ (*TOCHECK: _delayed*)
    | HeapNode2 _
    | Phase _
    | HRel _ (*TO CHECK*)
    | HEmp
    | HTrue
    | HFalse | HVar _ -> (f,[])
    | ConjStar _ | ConjConj _ | StarMinus _ -> Error.report_no_pattern ()
  in helper f


and h_apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : h_formula) = match f with
  | Conj ({h_formula_conj_h1 = h1; 
           h_formula_conj_h2 = h2; 
           h_formula_conj_pos = pos}) ->
      Conj ({h_formula_conj_h1 = h_apply_one s h1; 
             h_formula_conj_h2 = h_apply_one s h2; 
             h_formula_conj_pos = pos})
  | ConjStar ({h_formula_conjstar_h1 = h1; 
               h_formula_conjstar_h2 = h2; 
               h_formula_conjstar_pos = pos}) ->
      ConjStar ({h_formula_conjstar_h1 = h_apply_one s h1; 
                 h_formula_conjstar_h2 = h_apply_one s h2; 
                 h_formula_conjstar_pos = pos})
  | ConjConj ({h_formula_conjconj_h1 = h1; 
               h_formula_conjconj_h2 = h2; 
               h_formula_conjconj_pos = pos}) ->
      ConjConj ({h_formula_conjconj_h1 = h_apply_one s h1; 
                 h_formula_conjconj_h2 = h_apply_one s h2; 
                 h_formula_conjconj_pos = pos})
  | Phase ({h_formula_phase_rd = h1; 
            h_formula_phase_rw = h2; 
            h_formula_phase_pos = pos}) ->
      Phase ({h_formula_phase_rd = h_apply_one s h1; 
              h_formula_phase_rw = h_apply_one s h2; 
              h_formula_phase_pos = pos}) 
  | StarMinus ({h_formula_starminus_h1 = f1; 
                h_formula_starminus_h2 = f2; 
                h_formula_starminus_pos = pos}) -> 
      StarMinus ({h_formula_starminus_h1 = h_apply_one s f1; 
                  h_formula_starminus_h2 = h_apply_one s f2; 
                  h_formula_starminus_pos = pos})
  | Star ({h_formula_star_h1 = f1; 
           h_formula_star_h2 = f2; 
           h_formula_star_pos = pos}) -> 
      Star ({h_formula_star_h1 = h_apply_one s f1; 
             h_formula_star_h2 = h_apply_one s f2; 
             h_formula_star_pos = pos})
  | HeapNode ({h_formula_heap_node = x; 
               h_formula_heap_name = c; 
               h_formula_heap_deref = deref;
               h_formula_heap_derv = dr;
               h_formula_heap_split = split;
               h_formula_heap_imm = imm;
               h_formula_heap_imm_param = imm_p;
               h_formula_heap_full = full;
               h_formula_heap_with_inv = winv;
               h_formula_heap_perm = perm; (*LDK*)
               h_formula_heap_arguments = args;
               h_formula_heap_ho_arguments = ho_args;
               h_formula_heap_pseudo_data = ps_data;
               h_formula_heap_label = l;
               h_formula_heap_pos = pos}) ->
      let imm = apply_one_imm s imm in
      let imm_p = List.map (fun x -> apply_one_opt_imm s x) imm_p in
      let perm1 = ( match perm with
        | Some f -> Some (apply_one_iperm () s f)
        | None -> None
      ) in
      HeapNode ({h_formula_heap_node = subst_var s x;
                 h_formula_heap_name = c;
                 h_formula_heap_deref = deref;
                 h_formula_heap_derv = dr;
                 h_formula_heap_split = split;
                 h_formula_heap_imm = imm;
                 h_formula_heap_imm_param = imm_p;
                 h_formula_heap_full = full;
                 h_formula_heap_with_inv = winv;
                 h_formula_heap_perm = perm1 ; (*LDK*)
                 h_formula_heap_arguments = List.map (Ipure.e_apply_one s) args;
                 h_formula_heap_ho_arguments = List.map (fun ff -> 
                   {ff with rflow_base = apply_one s ff.rflow_base; }) ho_args;
                 h_formula_heap_pseudo_data = ps_data;
                 h_formula_heap_label = l;
                 h_formula_heap_pos = pos})
  | HeapNode2 ({h_formula_heap2_node = x;
                h_formula_heap2_name = c;
                h_formula_heap2_deref = deref;
                h_formula_heap2_derv = dr; 
                h_formula_heap2_split = split; 
                h_formula_heap2_imm = imm;
                h_formula_heap2_imm_param = imm_p; 
                h_formula_heap2_full = full;
                h_formula_heap2_with_inv = winv;
                h_formula_heap2_arguments = args;
                h_formula_heap2_ho_arguments = ho_args;
                h_formula_heap2_perm = perm; (*LDK*)
                h_formula_heap2_pseudo_data = ps_data;
                h_formula_heap2_label = l;
                h_formula_heap2_pos= pos}) -> 
      let imm = apply_one_imm s imm in
      let imm_p = List.map (fun x -> apply_one_opt_imm s x) imm_p in
      let perm1 = (
        match perm with
        | Some f -> Some (apply_one_iperm () s f)
        | None -> None
      ) in
      HeapNode2 ({h_formula_heap2_node = subst_var s x;
                  h_formula_heap2_name = c;
                  h_formula_heap2_deref = deref;
                  h_formula_heap2_derv = dr; 
                  h_formula_heap2_split = split; 
                  h_formula_heap2_imm = imm;
                  h_formula_heap2_imm_param = imm_p; 
                  h_formula_heap2_full = full;
                  h_formula_heap2_with_inv = winv;
                  h_formula_heap2_perm = perm1; (*LDK*)
                  h_formula_heap2_arguments = List.map (fun (c1,c2)-> (c1,(Ipure.e_apply_one s c2))) args;
                  h_formula_heap2_ho_arguments = List.map (fun ff -> 
                    {ff with rflow_base = apply_one s ff.rflow_base; }) ho_args;
                  h_formula_heap2_pseudo_data = ps_data;
                  h_formula_heap2_label = l;
                  h_formula_heap2_pos = pos})
  | ThreadNode ({ h_formula_thread_node = x;
                  h_formula_thread_name = c;
                  h_formula_thread_resource = rsr;
                  h_formula_thread_delayed = dl;
                  h_formula_thread_perm = perm;} as t) ->
      let rsr1 = apply_one s rsr in
      let dl1 = Ipure.apply_one s dl in
      let perm1 = ( match perm with
        | Some f -> Some (apply_one_iperm () s f)
        | None -> None)
      in ThreadNode {t with h_formula_thread_resource = rsr1;
                            h_formula_thread_delayed = dl1;
                            h_formula_thread_perm = perm1;}
  | HTrue -> f
  | HFalse -> f
  | HEmp  -> f
  (* URGENT:TODO:WN:HVar *)
  | HVar (v,ls) -> 
        let (v1, _) =  (subst_var s (v, Unprimed)) in
        let lsx =  List.map (fun v -> (subst_var s (v, Unprimed))) ls in
        HVar (v1,ls)
  | HRel (r, args, l) -> HRel (r, List.map (Ipure.e_apply_one s) args,l)

and rename_bound_vars_x (f : formula) = 
  let add_quantifiers (qvars : (ident*primed) list) (f : formula) : formula = 
    match f with
    | Base b -> 
      mkExists qvars 
        b.formula_base_heap b.formula_base_pure b.formula_base_vperm 
        b.formula_base_flow b.formula_base_and b.formula_base_pos
    | Exists b -> 
      let new_qvars = Gen.BList.remove_dups_eq (=) (b.formula_exists_qvars @ qvars) in
      mkExists new_qvars 
        b.formula_exists_heap b.formula_exists_pure b.formula_exists_vperm 
        b.formula_exists_flow b.formula_exists_and b.formula_exists_pos
    | _ -> failwith ("add_quantifiers: invalid argument") 
  in
  match f with
    | Or b -> mkOr (rename_bound_vars_x b.formula_or_f1) (rename_bound_vars_x b.formula_or_f2) b.formula_or_pos
    | Base _ -> f
    | Exists _ ->
      let qvars, base_f = split_quantifiers f in
      let new_qvars = Ipure.fresh_vars qvars in
      let rho = List.combine qvars new_qvars in
      let new_base_f = subst rho base_f in
      let resform = add_quantifiers new_qvars new_base_f in
      resform 

and rename_bound_vars (f : formula): formula = 
  let pr = !print_formula in
  Debug.no_1 "IF.rename_bound_vars" pr pr rename_bound_vars_x f
	          
and subst_struc (sst:((ident * primed)*(ident * primed)) list) (f:struc_formula):struc_formula = match f with
	| EAssume b -> 
		EAssume {b with 
			formula_assume_simpl = subst sst b.formula_assume_simpl; 
			formula_assume_struc = subst_struc sst b.formula_assume_struc;}
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> ((Ipure.subst sst c1),(subst_struc sst c2))) b.formula_case_branches}
	| EBase b->  EBase { b with
			  formula_struc_implicit_inst = List.map (subst_var_list sst) b.formula_struc_implicit_inst;
			  formula_struc_explicit_inst = List.map (subst_var_list sst) b.formula_struc_explicit_inst;
			  formula_struc_exists = List.map (subst_var_list sst) b.formula_struc_exists;
			  formula_struc_base = subst sst b.formula_struc_base;
			  formula_struc_continuation = Gen.map_opt (subst_struc sst) b.formula_struc_continuation;
			  formula_struc_pos = b.formula_struc_pos}
  | EInfer b -> EInfer {b with
      formula_inf_vars = List.map (subst_var_list sst) b.formula_inf_vars;
      formula_inf_continuation = subst_struc sst b.formula_inf_continuation;}
  | EList b -> EList (Gen.map_l_snd (subst_struc sst) b)
             (* formula_ext_complete = b.formula_ext_complete;*)

(*substitute all including existential variables*)
and subst_all_struc (sst:((ident * primed)*(ident * primed)) list) (f:struc_formula):struc_formula =
  let rec helper f =
  match f with
	| EAssume b -> 
		EAssume {b with 
			formula_assume_simpl = subst_all sst b.formula_assume_simpl; 
			formula_assume_struc = subst_all_struc sst b.formula_assume_struc;}
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> ((Ipure.subst sst c1),(helper c2))) b.formula_case_branches}
	| EBase b->  EBase { b with
			  formula_struc_implicit_inst = List.map (subst_var_list sst) b.formula_struc_implicit_inst;
			  formula_struc_explicit_inst = List.map (subst_var_list sst) b.formula_struc_explicit_inst;
			  formula_struc_exists = List.map (subst_var_list sst) b.formula_struc_exists;
			  formula_struc_base = subst_all sst b.formula_struc_base;
			  formula_struc_continuation = Gen.map_opt helper b.formula_struc_continuation;
			  formula_struc_pos = b.formula_struc_pos}
  | EInfer b -> EInfer {b with
      formula_inf_vars = List.map (subst_var_list sst) b.formula_inf_vars;
      formula_inf_continuation = helper b.formula_inf_continuation;}
  | EList b -> EList (Gen.map_l_snd (helper) b)
             (* formula_ext_complete = b.formula_ext_complete;*)
  in helper f

(*substitute all including existential variables*)
(*need to maintain point_to fact of a list of addressable vars *)
and subst_pointer_struc (sst:((ident * primed)*(ident * primed)) list) (f:struc_formula) (vars: (ident * primed) list):struc_formula =
  let rec helper f =
  match f with
	| EAssume b ->
        let pvars = List.map (fun (v,_) -> (v,Primed)) vars in
        let uvars = List.map (fun (v,_) -> (v,Unprimed)) vars in
		EAssume {b with 
			formula_assume_simpl = subst_pointer sst b.formula_assume_simpl (pvars@uvars); 
			formula_assume_struc = helper b.formula_assume_struc;}
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> ((Ipure.subst sst c1),(helper c2))) b.formula_case_branches}
	| EBase b->
        (*Preconditions do not contain primed notations*)
        let uvars = List.map (fun (v,_) -> (v,Unprimed)) vars in
        EBase { b with
	    formula_struc_implicit_inst = List.map (subst_var_list sst) b.formula_struc_implicit_inst;
	    formula_struc_explicit_inst = List.map (subst_var_list sst) b.formula_struc_explicit_inst;
	    formula_struc_exists = List.map (subst_var_list sst) b.formula_struc_exists;
	    formula_struc_base = subst_pointer sst b.formula_struc_base (uvars);
	    formula_struc_continuation = Gen.map_opt helper b.formula_struc_continuation;
	    formula_struc_pos = b.formula_struc_pos}
        | EInfer b -> EInfer {b with
              formula_inf_vars = List.map (subst_var_list sst) b.formula_inf_vars;
              formula_inf_continuation = helper b.formula_inf_continuation;}
        | EList b -> EList (Gen.map_l_snd (helper) b)
             (* formula_ext_complete = b.formula_ext_complete;*)
  in helper f

let get_heap_nodes (f0:h_formula) =
  let rec helper f =match f with
    | Conj ({h_formula_conj_h1 = h1; 
      h_formula_conj_h2 = h2; 
      h_formula_conj_pos = pos})
    | ConjStar ({h_formula_conjstar_h1 = h1; 
      h_formula_conjstar_h2 = h2; 
      h_formula_conjstar_pos = pos})
    | ConjConj ({h_formula_conjconj_h1 = h1; 
      h_formula_conjconj_h2 = h2;
      h_formula_conjconj_pos = pos})
    | Phase ({h_formula_phase_rd = h1;
      h_formula_phase_rw = h2;
      h_formula_phase_pos = pos}) 
    | StarMinus ({h_formula_starminus_h1 = h1; 
      h_formula_starminus_h2 = h2; 
      h_formula_starminus_pos = pos})
    | Star ({h_formula_star_h1 = h1; 
      h_formula_star_h2 = h2; 
      h_formula_star_pos = pos}) ->
          let r11, r12 = (helper h1) in
          let r21, r22 = (helper h2) in
          (r11@r21, r12@r22)
    | HeapNode hn -> [hn],[]
    | HeapNode2 hn2 -> [],[hn2]
    | ThreadNode _
    | HRel _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> [],[]
  in
  helper f0

let get_heaps (f0:h_formula) =
  let rec helper f =match f with
    | Conj ({h_formula_conj_h1 = h1; 
      h_formula_conj_h2 = h2; 
      h_formula_conj_pos = pos})
    | ConjStar ({h_formula_conjstar_h1 = h1; 
      h_formula_conjstar_h2 = h2; 
      h_formula_conjstar_pos = pos})
    | ConjConj ({h_formula_conjconj_h1 = h1; 
      h_formula_conjconj_h2 = h2;
      h_formula_conjconj_pos = pos})
    | Phase ({h_formula_phase_rd = h1;
      h_formula_phase_rw = h2;
      h_formula_phase_pos = pos}) 
    | StarMinus ({h_formula_starminus_h1 = h1; 
      h_formula_starminus_h2 = h2; 
      h_formula_starminus_pos = pos})
    | Star ({h_formula_star_h1 = h1; 
      h_formula_star_h2 = h2; 
      h_formula_star_pos = pos}) ->
         (helper h1)@(helper h2)
    | HeapNode _
    | HeapNode2 _
    | ThreadNode _
    | HRel _
    | HTrue
    | HFalse | HVar _ -> [f]
    | HEmp -> []
  in
  helper f0

(*======for generate tmp view=========*)
let rec one_formula_apply_one_w_data_name ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : one_formula) =
  let h,p,dl,id,pos = split_one_formula f in
  {formula_heap = h_apply_one_w_data_name s h;
   formula_pure = Ipure.apply_one s p;
   formula_delayed = Ipure.apply_one s dl;
   formula_thread = (match id with
     | None -> None
     | Some v -> Some (subst_var s v));
   formula_pos = pos}

and h_apply_one_w_data_name ((fr, t) as s : ((ident*primed) * (ident*primed))) (f0 : h_formula) =
  let subst_data_name ((c1,_),(c2,_)) c=
    if c = c1 then c2 else c
  in
  let rec helper f=
    match f with
    | Conj ({h_formula_conj_h1 = h1;
             h_formula_conj_h2 = h2;
             h_formula_conj_pos = pos}) ->
        Conj ({h_formula_conj_h1 = helper h1;
               h_formula_conj_h2 = helper h2;
               h_formula_conj_pos = pos})
    | Phase ({h_formula_phase_rd = h1;
              h_formula_phase_rw = h2;
              h_formula_phase_pos = pos}) ->
      Phase ({h_formula_phase_rd = helper h1;
              h_formula_phase_rw = helper h2;
              h_formula_phase_pos = pos})
    | Star ({h_formula_star_h1 = f1;
             h_formula_star_h2 = f2;
             h_formula_star_pos = pos}) ->
        Star ({h_formula_star_h1 = helper f1;
               h_formula_star_h2 = helper f2;
               h_formula_star_pos = pos})
    | ConjStar ({h_formula_conjstar_h1 = f1;
                 h_formula_conjstar_h2 = f2;
                 h_formula_conjstar_pos = pos}) ->
        ConjStar ({h_formula_conjstar_h1 = helper f1;
                   h_formula_conjstar_h2 = helper f2;
                   h_formula_conjstar_pos = pos})
    | ConjConj ({h_formula_conjconj_h1 = f1;
                 h_formula_conjconj_h2 = f2;
                 h_formula_conjconj_pos = pos}) ->
        ConjConj ({h_formula_conjconj_h1 = helper f1;
                   h_formula_conjconj_h2 = helper f2;
                   h_formula_conjconj_pos = pos})
    | StarMinus ({h_formula_starminus_h1 = f1;
                  h_formula_starminus_h2 = f2;
                  h_formula_starminus_pos = pos}) ->
        StarMinus ({h_formula_starminus_h1 = helper f1;
                    h_formula_starminus_h2 = helper f2;
                    h_formula_starminus_pos = pos})
    | HeapNode ({h_formula_heap_node = x;
                 h_formula_heap_name = c;
                 h_formula_heap_deref = deref;
                 h_formula_heap_derv = dr;
                 h_formula_heap_split = split;
                 h_formula_heap_imm = imm;
                 h_formula_heap_imm_param = imm_p; 
                 h_formula_heap_full = full;
                 h_formula_heap_with_inv = winv;
                 h_formula_heap_perm = perm; (*LDK*)
                 h_formula_heap_arguments = args;
                 h_formula_heap_ho_arguments = ho_args;
                 h_formula_heap_pseudo_data = ps_data;
                 h_formula_heap_label = l;
                 h_formula_heap_pos = pos}) ->
        let imm = apply_one_imm s imm in
        let perm1 = ( match perm with
          | Some f -> Some (apply_one_iperm () s f)
          | None -> None
        ) in 
        HeapNode ({h_formula_heap_node = subst_var s x;
                   h_formula_heap_name = subst_data_name s c;
                   h_formula_heap_deref = deref;
                   h_formula_heap_derv = dr;
                   h_formula_heap_split = split;
                   h_formula_heap_imm = imm;
                   h_formula_heap_imm_param = imm_p; 
                   h_formula_heap_full = full;
                   h_formula_heap_with_inv = winv;
                   h_formula_heap_perm = perm1 ; (*LDK*)
                   h_formula_heap_arguments = List.map (Ipure.e_apply_one s) args;
                   h_formula_heap_ho_arguments = List.map (fun ff -> 
                     { ff with rflow_base = apply_one_w_data_name s ff.rflow_base; }) ho_args; 
                   h_formula_heap_pseudo_data = ps_data;
                   h_formula_heap_label = l;
                   h_formula_heap_pos = pos})
    | HeapNode2 ({h_formula_heap2_node = x;
                  h_formula_heap2_name = c;
                  h_formula_heap2_deref = deref;
                  h_formula_heap2_derv = dr;
                  h_formula_heap2_split = split;
                  h_formula_heap2_imm = imm;
                  h_formula_heap2_imm_param = imm_p;
                  h_formula_heap2_full = full;
                  h_formula_heap2_with_inv = winv;
                  h_formula_heap2_arguments = args;
                  h_formula_heap2_ho_arguments = ho_args;
                  h_formula_heap2_perm = perm; (*LDK*)
                  h_formula_heap2_pseudo_data = ps_data;
                  h_formula_heap2_label = l;
                  h_formula_heap2_pos= pos}) ->
        let imm = apply_one_imm s imm in
        let perm1 = match perm with
          | Some f -> Some (apply_one_iperm () s f)
          | None -> None
        in
        HeapNode2 ({h_formula_heap2_node = subst_var s x;
                    h_formula_heap2_name = subst_data_name s c;
                    h_formula_heap2_deref = deref;
                    h_formula_heap2_derv = dr;
                    h_formula_heap2_split = split;
                    h_formula_heap2_imm = imm;
                    h_formula_heap2_imm_param = imm_p;
                    h_formula_heap2_full =full;
                    h_formula_heap2_with_inv = winv;
                    h_formula_heap2_perm = perm1; (*LDK*)
                    h_formula_heap2_arguments = List.map (fun (c1,c2)-> (c1,(Ipure.e_apply_one s c2))) args;
                    h_formula_heap2_ho_arguments = List.map (fun ff -> 
                      { ff with rflow_base = apply_one_w_data_name s ff.rflow_base; }) ho_args; 
                    h_formula_heap2_pseudo_data =ps_data;
                    h_formula_heap2_label = l;
                    h_formula_heap2_pos = pos})
  | ThreadNode ({ h_formula_thread_node = x;
                  h_formula_thread_name = c;
                  h_formula_thread_resource = rsr;
                  h_formula_thread_delayed = dl;
                  h_formula_thread_perm = perm;} as t) ->
      let rsr1 = apply_one_w_data_name s rsr in
      let dl1 =  Ipure.apply_one s dl in
      let perm1 = ( match perm with
        | Some f -> Some (apply_one_iperm () s f)
        | None -> None)
      in ThreadNode {t with h_formula_thread_resource = rsr1;
                            h_formula_thread_delayed = dl1;
                            h_formula_thread_perm = perm1;}
    | HTrue -> f
    | HFalse -> f
    | HEmp -> f
    (* URGENT:TODO:WN:HVar *)
    | HVar (v,hvar_vs) -> HVar (subst_data_name s v,hvar_vs) (* TODO:HO *)
    | HRel (r, args, l) -> HRel (r, List.map (Ipure.e_apply_one s) args,l)
  in
  helper f0

and apply_one_w_data_name ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : formula) = 
  match f with
  | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos }) ->
    Or ({ formula_or_f1 = apply_one_w_data_name s f1; formula_or_f2 =  apply_one_w_data_name s f2; formula_or_pos = pos })
  | Base ({
      formula_base_heap = h;
      formula_base_pure = p;
      formula_base_vperm = vp;
      formula_base_flow = fl;
      formula_base_and = a;
      formula_base_pos = pos }) ->
    Base ({
      formula_base_heap = h_apply_one_w_data_name s h;
      formula_base_pure = Ipure.apply_one s p;
      formula_base_vperm = VP.vp_apply_one s vp;
      formula_base_flow = fl;
      formula_base_and = List.map (one_formula_apply_one_w_data_name s) a;
      formula_base_pos = pos })
  | Exists ({
      formula_exists_qvars = qsv;
      formula_exists_heap = qh;
      formula_exists_pure = qp;
      formula_exists_vperm = vp;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_pos = pos }) ->
    if List.mem (fst fr) (List.map fst qsv) then f
    else Exists ({
      formula_exists_qvars = qsv;
      formula_exists_heap =  h_apply_one_w_data_name s qh;
      formula_exists_pure = Ipure.apply_one s qp;
      formula_exists_vperm = VP.vp_apply_one s vp;
      formula_exists_flow = fl;
      formula_exists_and = List.map (one_formula_apply_one_w_data_name s) a;
      formula_exists_pos = pos })

and subst_w_data_name sst (f : formula) = match sst with
  | s :: rest -> subst_w_data_name rest (apply_one_w_data_name s f)
  | [] -> f

and subst_w_data_name_struc (sst:((ident * primed)*(ident * primed)) list) (f:struc_formula):struc_formula = match f with
	| EAssume b -> 
		EAssume {b with 
			formula_assume_simpl = subst_w_data_name sst b.formula_assume_simpl; 
			formula_assume_struc = subst_w_data_name_struc sst b.formula_assume_struc;}
	| ECase b -> ECase {b with 
		formula_case_branches = 
			List.map (fun (c1,c2)-> ((Ipure.subst sst c1),(subst_w_data_name_struc sst c2)))
				b.formula_case_branches}
	| EBase b->  EBase {b with
			  formula_struc_implicit_inst = List.map (subst_var_list sst) b.formula_struc_implicit_inst;
			  formula_struc_explicit_inst = List.map (subst_var_list sst) b.formula_struc_explicit_inst;
			  formula_struc_exists = List.map (subst_var_list sst) b.formula_struc_exists;
			  formula_struc_base = subst_w_data_name sst b.formula_struc_base;
			  formula_struc_continuation = Gen.map_opt (subst_w_data_name_struc sst) b.formula_struc_continuation;
			  formula_struc_pos = b.formula_struc_pos}
  | EInfer b -> EInfer {b with
      formula_inf_vars = List.map (subst_var_list sst) b.formula_inf_vars;
      formula_inf_continuation = subst_w_data_name_struc sst b.formula_inf_continuation;}
  | EList b -> EList (Gen.map_l_snd (subst_w_data_name_struc sst) b)
             (* formula_ext_complete = b.formula_ext_complete;*)
(*======END for generate tmp view======*)

let rec rename_bound_var_struc_formula (f:struc_formula):struc_formula = match f with
	| EAssume b -> 
		EAssume {b with 
			formula_assume_simpl = x_add_1 rename_bound_vars b.formula_assume_simpl; 
			formula_assume_struc = rename_bound_var_struc_formula b.formula_assume_struc;}
	| ECase b-> ECase {b with formula_case_branches = Gen.map_l_snd rename_bound_var_struc_formula b.formula_case_branches}
	| EBase b-> 
			let sst2 = List.map (fun (c1,c2)-> ((c1,c2),((Ipure.fresh_old_name c1),c2))) b.formula_struc_implicit_inst in
			EBase {b with 
				formula_struc_explicit_inst = b.formula_struc_explicit_inst;
		 		formula_struc_implicit_inst = snd (List.split sst2);
				formula_struc_base= x_add_1 rename_bound_vars (subst sst2 b.formula_struc_base); 
				formula_struc_continuation= Gen.map_opt rename_bound_var_struc_formula (Gen.map_opt (subst_struc sst2) b.formula_struc_continuation) }			
	| EInfer b -> EInfer {b with (* Need to check again *)
					formula_inf_continuation = rename_bound_var_struc_formula b.formula_inf_continuation;}
	| EList b -> EList (Gen.map_l_snd rename_bound_var_struc_formula b)
	

and float_out_exps_from_heap n lbl_getter annot_getter (f:formula ) :formula = (* float_out_exps_from_heap_x f *)
let pr = !print_formula in
Debug.no_1_num n "float_out_exps_from_heap" pr pr (fun _ -> float_out_exps_from_heap_x lbl_getter annot_getter f) f

and float_out_exps_from_heap_x lbl_getter annot_getter (f:formula ) :formula = 
  let rec float_ann_var l c=
    match c with
      | Ipure.AConst _
      | Ipure.Var _ -> (c,[])
      | Ipure.Ann_Exp (e ,_,_) -> float_ann_var l e
      | _ ->
	    let nn = (("flted_"^(string_of_int l.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
	    let nv = Ipure.Var (nn,l) in
	    let npf = 
	      (* if !Globals.do_slicing then *)
              if not !Globals.dis_slc_ann then
                try
                  let lexp = P.find_lexp_exp c !Ipure.linking_exp_list in
                  (*let () = Hashtbl.remove !Ipure.linking_exp_list c in*)
		  Ipure.BForm ((Ipure.Eq (nv,c,l), (Some (false, fresh_int(), lexp))), None)
                with Not_found ->
		    Ipure.BForm ((Ipure.Eq (nv,c,l), None), None)
              else
                Ipure.BForm ((Ipure.Eq (nv,c,l), None), None) 
                    (* Slicing: TODO IL for linking exp *)
            in
	    (nv,[(nn,npf)])
  in
  let rec float_out_exps (f:h_formula):(h_formula * (((ident*primed)*Ipure.formula)list)) = match f with
    | Star b-> 
	let r11,r12 = float_out_exps b.h_formula_star_h1 in
	let r21,r22 = float_out_exps b.h_formula_star_h2 in
	  (Star ({h_formula_star_h1  =r11; h_formula_star_h2=r21;h_formula_star_pos = b.h_formula_star_pos}), 
	   (r12@r22))
    | StarMinus b-> 
	let r11,r12 = float_out_exps b.h_formula_starminus_h1 in
	let r21,r22 = float_out_exps b.h_formula_starminus_h2 in
	  (StarMinus ({h_formula_starminus_h1  =r11; h_formula_starminus_h2=r21;h_formula_starminus_pos = b.h_formula_starminus_pos}), 
	   (r12@r22))	   
    | Conj b-> 
	let r11,r12 = float_out_exps b.h_formula_conj_h1 in
	let r21,r22 = float_out_exps b.h_formula_conj_h2 in
	  (Conj ({h_formula_conj_h1  =r11; h_formula_conj_h2=r21;h_formula_conj_pos = b.h_formula_conj_pos}), 
	   (r12@r22))
    | ConjStar b-> 
	let r11,r12 = float_out_exps b.h_formula_conjstar_h1 in
	let r21,r22 = float_out_exps b.h_formula_conjstar_h2 in
	  (ConjStar ({h_formula_conjstar_h1  =r11; h_formula_conjstar_h2=r21;h_formula_conjstar_pos = b.h_formula_conjstar_pos}), 
	   (r12@r22))
    | ConjConj b-> 
	let r11,r12 = float_out_exps b.h_formula_conjconj_h1 in
	let r21,r22 = float_out_exps b.h_formula_conjconj_h2 in
	  (ConjConj ({h_formula_conjconj_h1  =r11; h_formula_conjconj_h2=r21;h_formula_conjconj_pos = b.h_formula_conjconj_pos}), 
	   (r12@r22))	   	   
    | Phase b-> 
	let r11,r12 = float_out_exps b.h_formula_phase_rd in
	let r21,r22 = float_out_exps b.h_formula_phase_rw in
	  (Phase ({h_formula_phase_rd  =r11; h_formula_phase_rw=r21;h_formula_phase_pos = b.h_formula_phase_pos}), 
	   (r12@r22))
    | HeapNode b->
        (*LDK*)
        let perm = b.h_formula_heap_perm in
        let na_perm, ls_perm = float_out_iperm () perm b.h_formula_heap_pos in
        let prep_one_arg_helper (id,c) =
          let nn = (("flted_"^(string_of_int b.h_formula_heap_pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
	  let nv = Ipure.Var (nn,b.h_formula_heap_pos) in
	  let npf = 
	    (* if !Globals.do_slicing then *)
	    if not !Globals.dis_slc_ann then
	      try
		let lexp = P.find_lexp_exp c !Ipure.linking_exp_list in
		(* let () = Hashtbl.remove !Ipure.linking_exp_list c in *)
		Ipure.BForm ((Ipure.Eq (nv,c,b.h_formula_heap_pos), (Some (false, fresh_int(), lexp))), None)
	      with Not_found -> Ipure.BForm ((Ipure.Eq (nv,c,b.h_formula_heap_pos), None), None)
            else 
              let pf = Ipure.Eq (nv,c,b.h_formula_heap_pos) in
	      (*if (*not(!Globals.allow_field_ann)*) (true) then Ipure.Eq (nv,c,b.h_formula_heap_pos) else 
                in*)
              let nf = Ipure.BForm ((pf, None), None) in
              match lbl_getter b.h_formula_heap_name id with 
		| None -> nf 
                | Some lb -> Ipure.mkAndList [(lb,nf)] 
                      (* Slicing: TODO IL for linking exp *)
          in
	  (nv,[(nn,npf)]) in
	let rec prep_one_arg (id,c) = match c with
          | Ipure.AConst _ ->
                if ( List.exists (fun (a,p) -> (id + 1) == p) (annot_getter b.h_formula_heap_name)) then (c,[])
                else prep_one_arg_helper (id,c)
	  | Ipure.Var _ -> (c,[])
          | Ipure.Ann_Exp (e ,_,_) -> prep_one_arg (id, e)
	  | _ ->  prep_one_arg_helper (id,c) in
        let na,ls = List.split (List.map prep_one_arg (Gen.BList.add_index b.h_formula_heap_arguments)) in
        let ho_na = List.map (fun ff -> { ff with 
          rflow_base = float_out_exps_from_heap 3 lbl_getter annot_getter ff.rflow_base }) b.h_formula_heap_ho_arguments in
        let () = x_dinfo_hp (add_str "ho_na" (pr_list !print_rflow_formula)) ho_na no_pos in
        (HeapNode ({b with h_formula_heap_arguments = na; h_formula_heap_ho_arguments = ho_na; h_formula_heap_perm = na_perm}),(List.concat (ls_perm ::ls)))
    | HeapNode2 b ->
        (*LDK*)
        let perm = b.h_formula_heap2_perm in
        let na_perm, ls_perm = float_out_iperm () perm b.h_formula_heap2_pos in
        let prep_one_arg_helper (id,c) =
	  let nn = (("flted_"^(string_of_int b.h_formula_heap2_pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
	  let nv = Ipure.Var (nn,b.h_formula_heap2_pos) in
	  let npf =
	    (* if !Globals.do_slicing then *)
	    if not !Globals.dis_slc_ann then
	      try
		let lexp = P.find_lexp_exp c !Ipure.linking_exp_list in
		(*let () = Hashtbl.remove !Ipure.linking_exp_list (snd c) in*)
		Ipure.BForm ((Ipure.Eq (nv, c,b.h_formula_heap2_pos), (Some (false, fresh_int(), lexp))), None)
	      with Not_found ->
		  Ipure.BForm ((Ipure.Eq (nv, c,b.h_formula_heap2_pos), None), None)
	    else Ipure.BForm ((Ipure.Eq (nv, c,b.h_formula_heap2_pos), None), None) in (* Slicing: TODO *)
	  ((id,nv),[(nn,npf)]) in
        let rec helper (id, c)=
          match c with
              | Ipure.AConst _ ->
                    (* if ( List.exists (fun (a,p) -> (id + 1) == p) (annot_getter b.h_formula_heap2_name)) then *) ((id,c),[])
                    (* else prep_one_arg_helper (id,c) *)
	      | Ipure.Var _ -> ((id,c),[])
              | Ipure.Ann_Exp (e ,_,_) -> helper (id, e)
	      | _ -> prep_one_arg_helper (id,c)
        in
        let na,ls = List.split (List.map helper b.h_formula_heap2_arguments) in
        let ho_na = List.map (fun ff -> { ff with rflow_base = 
          float_out_exps_from_heap 4 lbl_getter annot_getter ff.rflow_base; }) b.h_formula_heap2_ho_arguments in
        (HeapNode2 ({b with h_formula_heap2_ho_arguments = ho_na;
            h_formula_heap2_arguments = na;h_formula_heap2_perm = na_perm}),(List.concat (ls_perm :: ls)))
    | ThreadNode b->
        let perm = b.h_formula_thread_perm in
        let na_perm, ls_perm = float_out_iperm () perm b.h_formula_thread_pos in
        let rsr1 = float_out_exps_from_heap 5 lbl_getter annot_getter b.h_formula_thread_resource in (*TOCHECK*)
        let qvars, rsr2 = split_quantifiers rsr1 in
        let rl = if (List.length qvars) == 0 then
              ls_perm
            else
              let rl = List.map (fun v -> (v,P.mkTrue b.h_formula_thread_pos)) qvars in
              rl@ls_perm
        in
        (*TOCHECK: need to float our _delayed??? *)
        let new_node = ThreadNode ({b with h_formula_thread_resource = rsr2; h_formula_thread_perm = na_perm}) in
        (new_node,rl)
    | HRel (r, args, l) ->
        	(* let nargs = List.map Ipure.float_out_exp_min_max args in *)
			(* let nargse = List.map fst nargs in *)
            let na,ls = List.split (List.map (float_ann_var l)(* (fun c-> *)
		  (*       match c with *)
		  (*         | Ipure.Var _ -> (c,[]) *)
                  (*         | _ -> *)
		  (*       	  let nn = (("flted_"^(string_of_int l.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in *)
		  (*       	  let nv = Ipure.Var (nn,l) in *)
		  (*       	  let npf =  *)
		  (*       		(\* if !Globals.do_slicing then *\) *)
                  (*     if not !Globals.dis_slc_ann then *)
                  (*     try *)
                  (*         let lexp = P.find_lexp_exp c !Ipure.linking_exp_list in *)
                  (*               (\*let () = Hashtbl.remove !Ipure.linking_exp_list c in*\) *)
		  (*       			  Ipure.BForm ((Ipure.Eq (nv,c,l), (Some (false, fresh_int(), lexp))), None) *)
                  (*     with Not_found -> *)
		  (*       			  Ipure.BForm ((Ipure.Eq (nv,c,l), None), None) *)
                  (*   else *)
                  (*     Ipure.BForm ((Ipure.Eq (nv,c,l), None), None)  *)
                  (*       (\* Slicing: TODO IL for linking exp *\) *)
                  (* in *)
		  (*       	  (nv,[(nn,npf)])) *) args) in
            (HRel (r, na, l),List.concat ls)
    | HTrue -> (f,[])
    | HFalse -> (f,[]) 
    | HEmp | HVar _ -> (f,[]) in
  let float_out_exps i (f:h_formula):(h_formula * (((ident*primed)*Ipure.formula)list)) = 
    let pr1 = !print_h_formula in
    let pr2 = pr_pair pr1 (pr_list (pr_pair (fun (i,_) -> i) !print_pure_formula)) in
    Debug.no_1_num i "float_out_exps" pr1 pr2 float_out_exps f in
  let helper_one_formula (f:one_formula) =
    let rh,rl = float_out_exps 1 f.formula_heap in
    if (List.length rl) == 0 then ([],f)
    else
	  let r1,r2 = List.hd rl in
	  let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)-> ((c1::a1),(Ipure.mkAnd a2 c2 f.formula_pos)) ) ([r1],r2) (List.tl rl) in
      let new_p = Ipure.mkAnd r2 f.formula_pure f.formula_pos in
      (r1,mkOneFormula rh new_p f.formula_delayed f.formula_thread f.formula_pos)
  in
  let rec helper (f:formula):formula = 
    match f with
    | Base b -> 
      let rh,rl = float_out_exps 2 b.formula_base_heap in
      if (List.length rl) == 0 then 
        Base { b with formula_base_heap = rh; }
      else 
        let r1,r2 = List.hd rl in
        let r1,r2 = List.fold_left (fun (a1,a2) (c1,c2) -> 
          ((c1::a1),(Ipure.mkAnd a2 c2 b.formula_base_pos))) ([r1],r2) (List.tl rl) in
        let tmp = List.map helper_one_formula b.formula_base_and in
        let avars,afs = List.split tmp in
        let avars = List.concat avars in
        Exists ({
          formula_exists_qvars = avars@r1;
          formula_exists_heap = rh;
          formula_exists_vperm = b.formula_base_vperm;
          formula_exists_flow = b.formula_base_flow;
          formula_exists_pure = Ipure.mkAnd r2 b.formula_base_pure b.formula_base_pos;
          formula_exists_and = afs;
          formula_exists_pos = b.formula_base_pos })
    | Exists b ->
      let rh,rl = float_out_exps 3 b.formula_exists_heap in
      if (List.length rl)== 0 then
        Exists { b with formula_exists_heap = rh; }
      else
        let r1,r2 = List.hd rl in
        let r1,r2 = List.fold_left (fun (a1,a2) (c1,c2) -> 
          ((c1::a1),(Ipure.mkAnd a2 c2 b.formula_exists_pos))) ([r1],r2) (List.tl rl) in
        let tmp = List.map helper_one_formula b.formula_exists_and in
        let avars,afs = List.split tmp in
        let avars = List.concat avars in
        Exists ({
          formula_exists_qvars = avars@r1@b.formula_exists_qvars;
          formula_exists_heap = rh;
          formula_exists_pure = Ipure.mkAnd r2 b.formula_exists_pure b.formula_exists_pos;
          formula_exists_vperm = b.formula_exists_vperm;
          formula_exists_flow = b.formula_exists_flow;
          formula_exists_and = afs;
          formula_exists_pos = b.formula_exists_pos })
    | Or b -> Or ({
        formula_or_f1 = float_out_exps_from_heap 6 lbl_getter annot_getter b.formula_or_f1 ;
        formula_or_f2 = float_out_exps_from_heap 7 lbl_getter annot_getter b.formula_or_f2 ;
        formula_or_pos = b.formula_or_pos })
  in helper f
       
and float_out_exps_from_heap_struc lbl_getter annot_getter (f:struc_formula):struc_formula = match f with
  | EAssume b ->    
          EAssume {b with
			formula_assume_simpl = float_out_exps_from_heap 8 lbl_getter annot_getter b.formula_assume_simpl; 
			formula_assume_struc = float_out_exps_from_heap_struc lbl_getter annot_getter b.formula_assume_struc;}
    | ECase b -> ECase {b with formula_case_branches = Gen.map_l_snd (fun x -> float_out_exps_from_heap_struc lbl_getter annot_getter x) b.formula_case_branches}
    | EBase b -> EBase { b with
				 formula_struc_explicit_inst = b.formula_struc_explicit_inst;
				 formula_struc_implicit_inst = b.formula_struc_implicit_inst;
				 formula_struc_exists = b.formula_struc_exists ;
				 formula_struc_base = float_out_exps_from_heap 9 lbl_getter annot_getter b.formula_struc_base;
				 formula_struc_continuation = Gen.map_opt (fun x -> float_out_exps_from_heap_struc lbl_getter annot_getter x)  b.formula_struc_continuation;
				 formula_struc_pos = b.formula_struc_pos}
    | EInfer b -> EInfer ({b with formula_inf_continuation = float_out_exps_from_heap_struc lbl_getter annot_getter b.formula_inf_continuation;})
	| EList b -> EList (Gen.map_l_snd (fun x -> float_out_exps_from_heap_struc lbl_getter annot_getter x) b )

and float_out_one_formula_min_max (f :  one_formula) :  one_formula =
  let (nh, nhpf) = float_out_heap_min_max f.formula_heap in
  let np = Ipure.float_out_pure_min_max f.formula_pure in
  let new_p =  (match nhpf with
    | None -> np
    | Some e1 -> Ipure.And (np, e1, f.formula_pos)) in
  mkOneFormula nh new_p f.formula_delayed f.formula_thread f.formula_pos

and float_out_min_max (f :  formula) :  formula =
  match f with
  | Base {
      formula_base_pos = l;
      formula_base_heap = h0;
      formula_base_vperm = vp;
      formula_base_flow = fl;
      formula_base_and = a;
      formula_base_pure = p0 } as b ->
    let (nh, nhpf) = float_out_heap_min_max h0 in
    let np = Ipure.float_out_pure_min_max p0 in
    Base {
      formula_base_pos = l;
      formula_base_heap = nh;
      formula_base_vperm = vp;
      formula_base_flow = fl;
      formula_base_pure = (match nhpf with
        | None -> np
        | Some e1 -> Ipure.And (np, e1, l));
      formula_base_and = List.map float_out_one_formula_min_max a; }
  | Exists {
      formula_exists_qvars = qv;
      formula_exists_heap = h0;
      formula_exists_pure = p0;
      formula_exists_vperm = vp;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_pos = l } ->
    let (nh, nhpf) = float_out_heap_min_max h0 in
    let np = Ipure.float_out_pure_min_max p0 in
    Exists {
      formula_exists_qvars = qv;
      formula_exists_heap = nh;
      formula_exists_vperm = vp;
      formula_exists_flow =fl;
      formula_exists_pure = (match nhpf with
        | None -> np
        | Some e1 -> (Ipure.And (np, e1, l)));
      formula_exists_and = List.map float_out_one_formula_min_max a;
      formula_exists_pos = l; }
  |  Or b -> Or {
      formula_or_f1 = float_out_min_max b.formula_or_f1;
      formula_or_f2 = float_out_min_max b.formula_or_f2;
      formula_or_pos = b.formula_or_pos; }

and float_out_heap_min_max (h :  h_formula) :
  ( h_formula * (Ipure.formula option)) =
  (******INTERNAL******)
   let rec helper1 l (a, c) d =
    match d with
      | Ipure.Null _ 
      | Ipure.IConst _
      | Ipure.AConst _
      | Ipure.Var _ -> (d::a, c)
      | Ipure.Ann_Exp (e ,_,_) -> helper1 l (a, c) e
      | _ -> 
	    let new_name = fresh_var_name "ptr" l.start_pos.Lexing.pos_lnum in 
	    let nv = Ipure.Var((new_name, Unprimed), l) in
	    (nv::a, let lexp = P.find_lexp_exp d !Ipure.linking_exp_list 
	    in match c with
	      | None -> Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d, l), Some (false, fresh_int(), lexp)), None)))
	      | Some s -> Some (Ipure.And ((Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d, l), Some (false, fresh_int(), lexp)), None))), s, l)))
   in
   let rec helper2 l (a, c) (d1,d2)=
     match d2 with
       | Ipure.Null _ 
       | Ipure.IConst _
       | Ipure.AConst _
       | Ipure.Var _ -> ((d1,d2):: a, c)
       | Ipure.Ann_Exp (e ,_,_) -> helper2 l (a, c) (d1,e)
       | _ -> 
	     let new_name = fresh_var_name "ptr" l.start_pos.Lexing.pos_lnum in 
	     let nv = Ipure.Var((new_name, Unprimed), l) in
             ((d1,nv):: a, 
             let lexp = P.find_lexp_exp d2 !Ipure.linking_exp_list in 
             match c with
	       | None -> Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d2, l), Some (false, fresh_int(), lexp)), None)))
	       | Some s -> Some (Ipure.And ((Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d2, l), Some (false, fresh_int(), lexp)), None)) ), s, l)))
   in
   (*****END INTERNAL******)
   match h with
    |  Star
	{
          h_formula_star_h1 = f1;
          h_formula_star_h2 = f2;
          h_formula_star_pos = l
	} ->
	 let (nf1, np1) = float_out_heap_min_max f1 in
	 let (nf2, np2) = float_out_heap_min_max f2 in
	 let np =
           (match (np1, np2) with
              | (None, None) -> None
              | (Some _, None) -> np1
              | (None, Some _) -> np2
              | (Some e1, Some e2) -> Some (Ipure.And (e1, e2, l)))
	 in
           (( Star
		{
		  h_formula_star_h1 = nf1;
		  h_formula_star_h2 = nf2;
		  h_formula_star_pos = l;
		}),
            np)
    |  StarMinus
	{
          h_formula_starminus_h1 = f1;
          h_formula_starminus_h2 = f2;
          h_formula_starminus_pos = l
	} ->
	 let (nf1, np1) = float_out_heap_min_max f1 in
	 let (nf2, np2) = float_out_heap_min_max f2 in
	 let np =
           (match (np1, np2) with
              | (None, None) -> None
              | (Some _, None) -> np1
              | (None, Some _) -> np2
              | (Some e1, Some e2) -> Some (Ipure.And (e1, e2, l)))
	 in
           (( StarMinus
		{
		  h_formula_starminus_h1 = nf1;
		  h_formula_starminus_h2 = nf2;
		  h_formula_starminus_pos = l;
		}),
            np)            
    |  Conj
	{
          h_formula_conj_h1 = f1;
          h_formula_conj_h2 = f2;
          h_formula_conj_pos = l
	} ->
	 let (nf1, np1) = float_out_heap_min_max f1 in
	 let (nf2, np2) = float_out_heap_min_max f2 in
	 let np =
           (match (np1, np2) with
              | (None, None) -> None
              | (Some _, None) -> np1
              | (None, Some _) -> np2
              | (Some e1, Some e2) -> Some (Ipure.And (e1, e2, l)))
	 in
           (( Conj
		{
		  h_formula_conj_h1 = nf1;
		  h_formula_conj_h2 = nf2;
		  h_formula_conj_pos = l;
		}),
            np)
    |  ConjStar
	{
          h_formula_conjstar_h1 = f1;
          h_formula_conjstar_h2 = f2;
          h_formula_conjstar_pos = l
	} ->
	 let (nf1, np1) = float_out_heap_min_max f1 in
	 let (nf2, np2) = float_out_heap_min_max f2 in
	 let np =
           (match (np1, np2) with
              | (None, None) -> None
              | (Some _, None) -> np1
              | (None, Some _) -> np2
              | (Some e1, Some e2) -> Some (Ipure.And (e1, e2, l)))
	 in
           (( ConjStar
		{
		  h_formula_conjstar_h1 = nf1;
		  h_formula_conjstar_h2 = nf2;
		  h_formula_conjstar_pos = l;
		}),
            np)
    |  ConjConj
	{
          h_formula_conjconj_h1 = f1;
          h_formula_conjconj_h2 = f2;
          h_formula_conjconj_pos = l
	} ->
	 let (nf1, np1) = float_out_heap_min_max f1 in
	 let (nf2, np2) = float_out_heap_min_max f2 in
	 let np =
           (match (np1, np2) with
              | (None, None) -> None
              | (Some _, None) -> np1
              | (None, Some _) -> np2
              | (Some e1, Some e2) -> Some (Ipure.And (e1, e2, l)))
	 in
           (( ConjConj
		{
		  h_formula_conjconj_h1 = nf1;
		  h_formula_conjconj_h2 = nf2;
		  h_formula_conjconj_pos = l;
		}),
            np)                        
    |  Phase
	{
          h_formula_phase_rd = f1;
          h_formula_phase_rw = f2;
          h_formula_phase_pos = l
	} ->
	 let (nf1, np1) = float_out_heap_min_max f1 in
	 let (nf2, np2) = float_out_heap_min_max f2 in
	 let np =
           (match (np1, np2) with
              | (None, None) -> None
              | (Some _, None) -> np1
              | (None, Some _) -> np2
              | (Some e1, Some e2) -> Some (Ipure.And (e1, e2, l)))
	 in
           (( Phase
		{
		  h_formula_phase_rd = nf1;
		  h_formula_phase_rw = nf2;
		  h_formula_phase_pos = l;
		}),
            np)


    |  HeapNode h1->
	    let l = h1.h_formula_heap_pos in
	    let args = h1.h_formula_heap_arguments in
        (*LDK*)
	    let perm = h1.h_formula_heap_perm in
	    let nl_perm, new_p_perm = float_out_min_max_iperm () perm l in
	          let nl, new_p =
	            List.fold_left (helper1 l)
                    (* (fun (a, c) d ->  *)
	            (*         match d with *)
		    (*               | Ipure.Null _  *)
		    (*               | Ipure.IConst _ *)
		    (*               | Ipure.Var _ -> (d::a, c) *)
		    (*               | _ ->  *)
		    (*                   let new_name = fresh_var_name "ptr" l.start_pos.Lexing.pos_lnum in  *)
		    (*                   let nv = Ipure.Var((new_name, Unprimed), l) in *)
		    (*                   (nv::a, let lexp = P.find_lexp_exp d !Ipure.linking_exp_list  *)
		    (*     	                      in match c with *)
		    (*                             | None -> Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d, l), Some (false, fresh_int(), lexp)), None))) *)
		    (*                             | Some s -> Some (Ipure.And ((Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d, l), Some (false, fresh_int(), lexp)), None))), s, l)))) *) ([], new_p_perm) args in
              (( HeapNode { h1 with  h_formula_heap_arguments = (List.rev nl); h_formula_heap_perm = nl_perm}), new_p)
    |  HeapNode2 h1 ->
	    let l = h1. h_formula_heap2_pos in
	    let args = h1. h_formula_heap2_arguments in
	    let perm = h1. h_formula_heap2_perm in
	    let nl_perm, new_p_perm = float_out_min_max_iperm () perm l in
	    let nl, new_p =
	      List.fold_left (helper2 l)
              (* (fun (a, c) (d1,d2) -> *)
	      (*         match d2 with *)
	      (*               | Ipure.Null _  *)
	      (*               | Ipure.IConst _ *)
	      (*               | Ipure.Var _ -> ((d1,d2):: a, c) *)
	      (*               | _ ->  *)
	      (*                   let new_name = fresh_var_name "ptr" l.start_pos.Lexing.pos_lnum in  *)
	      (*                   let nv = Ipure.Var((new_name, Unprimed), l) in *)

	      (*   	            ((d1,nv):: a,  *)
              (*            let lexp = P.find_lexp_exp d2 !Ipure.linking_exp_list in  *)
              (*            match c with *)
	      (*   	               | None -> Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d2, l), Some (false, fresh_int(), lexp)), None))) *)
	      (*   	               | Some s -> Some (Ipure.And ((Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d2, l), Some (false, fresh_int(), lexp)), None)) ), s, l)))) *) ([], new_p_perm) args 
        in
        (( HeapNode2 { h1 with  h_formula_heap2_arguments = (List.rev nl);h_formula_heap2_perm = nl_perm;}), new_p)
    |  ThreadNode h1->
	    let l = h1.h_formula_thread_pos in
        let rsr = float_out_min_max h1.h_formula_thread_resource in
	    let perm = h1.h_formula_thread_perm in
        let dl = Ipure.float_out_pure_min_max h1.h_formula_thread_delayed in
	    let nl_perm, new_p_perm = float_out_min_max_iperm () perm l in
        ((ThreadNode { h1 with  h_formula_thread_resource = rsr; h_formula_thread_perm = nl_perm; h_formula_thread_delayed = dl;}), new_p_perm)

    | HRel (r, args, l) ->
        	let nargs = List.map Ipure.float_out_exp_min_max args in
			let nargse = List.map fst nargs in
            (HRel (r, nargse, l),None)
    |  HTrue -> (h, None)
    |  HFalse -> (h, None)
    |  HEmp | HVar _ -> (h, None)
	 
  
and float_out_struc_min_max (f0 : struc_formula): struc_formula = match f0 with
	| EAssume b -> 
	      EAssume {b with 
		  formula_assume_simpl = float_out_min_max b.formula_assume_simpl; 
		  formula_assume_struc = float_out_struc_min_max b.formula_assume_struc;}
	| ECase b-> ECase {b with 
	      formula_case_branches = (List.map (fun (c1,c2)->((Ipure.float_out_pure_min_max c1),(float_out_struc_min_max c2))) b.formula_case_branches)}
	| EBase b -> EBase {b with 
	      formula_struc_base = float_out_min_max b.formula_struc_base;
	      formula_struc_continuation = Gen.map_opt float_out_struc_min_max b.formula_struc_continuation}
	| EInfer b -> EInfer {b with formula_inf_continuation = float_out_struc_min_max b.formula_inf_continuation;}
	| EList b -> EList (Gen.map_l_snd float_out_struc_min_max b)

and view_node_types_struc (f:struc_formula):ident list = match f with
  | ECase b -> Gen.fold_l_snd view_node_types_struc b.formula_case_branches
  | EBase b -> (view_node_types b.formula_struc_base)@(Gen.fold_opt view_node_types_struc b.formula_struc_continuation)
  | EAssume b -> view_node_types b.formula_assume_simpl
  | EInfer b -> view_node_types_struc b.formula_inf_continuation
  | EList b -> Gen.BList.remove_dups_eq (=) (Gen.fold_l_snd view_node_types_struc b)

and view_node_types (f:formula):ident list = 
  let rec helper (f:h_formula):ident list =  match f with
    | Star b -> Gen.BList.remove_dups_eq (=) ((helper b.h_formula_star_h1)@(helper b.h_formula_star_h2))
    | HeapNode b -> [b.h_formula_heap_name]
    | HeapNode2 b -> [b.h_formula_heap2_name]
    | _ -> [] in
  match f with
    | Or b-> Gen.BList.remove_dups_eq (=) ((view_node_types b.formula_or_f1) @ (view_node_types b.formula_or_f2))
    | Base b -> helper b.formula_base_heap
    | Exists b -> helper b.formula_exists_heap

and has_top_flow_struc (f:struc_formula) =
  let compare_top_flow fl=
    (String.compare fl (top_flow))<>0 &&
        (String.compare fl (top_flow^"#E"))<>0
  in
  let rec has_top_flow (f:formula) = match f with
    | Base b-> if (* (String.compare b.formula_base_flow top_flow)<>0 *)
        compare_top_flow b.formula_base_flow
      then Error.report_error {
	  Error.error_loc = b.formula_base_pos;
	  Error.error_text = ("view formula can not have a non top flow( "^b.formula_base_flow^")")} else ()
    | Exists b-> if (* (String.compare b.formula_exists_flow top_flow)<>0 *)
        compare_top_flow b.formula_exists_flow
      then Error.report_error {
	  Error.error_loc = b.formula_exists_pos;
	  Error.error_text = ("view formula can not have a non top flow("^b.formula_exists_flow^")")} else ()
    | Or b -> (has_top_flow b.formula_or_f1);(has_top_flow b.formula_or_f2) in
  let rec helper f0 = match f0 with
    | EBase b->   has_top_flow b.formula_struc_base; (match  b.formula_struc_continuation with | None -> () | Some l-> helper l)
    | ECase b->   List.iter (fun (_,b1)-> (helper b1)) b.formula_case_branches
    | EAssume b-> has_top_flow b.formula_assume_simpl
    | EInfer b-> helper b.formula_inf_continuation
    | EList b-> List.iter (fun c-> helper (snd c)) b  in
  helper f


and subst_flow_of_formula fr t (f:formula):formula = match f with
	| Base b-> Base {b with formula_base_flow = 
		if (String.compare fr b.formula_base_flow)==0 then t else b.formula_base_flow;}
	| Exists b-> Exists {b with formula_exists_flow = 
		if (String.compare fr b.formula_exists_flow)==0 then t else b.formula_exists_flow;}
	| Or b -> Or {b with formula_or_f1 = (subst_flow_of_formula fr t b.formula_or_f1);
					  formula_or_f2 = (subst_flow_of_formula fr t b.formula_or_f2);}
	
and subst_stub_flow t f = subst_flow_of_formula stub_flow t f	

and subst_flow_of_struc_formula  fr t (f:struc_formula):struc_formula = match f with
	| EBase b ->EBase {b with 
						 formula_struc_base = subst_flow_of_formula fr t b.formula_struc_base;
						 formula_struc_continuation = Gen.map_opt (subst_flow_of_struc_formula fr t) b.formula_struc_continuation}
	| ECase b ->ECase {b with formula_case_branches = Gen.map_l_snd (subst_flow_of_struc_formula fr t) b.formula_case_branches}
	| EAssume b-> 
		EAssume {b with 
			formula_assume_simpl = subst_flow_of_formula fr t b.formula_assume_simpl; 
			formula_assume_struc = subst_flow_of_struc_formula fr t b.formula_assume_struc;}
	| EInfer b -> EInfer {b with formula_inf_continuation = subst_flow_of_struc_formula fr t b.formula_inf_continuation;}
	| EList b-> EList (Gen.map_l_snd (subst_flow_of_struc_formula fr t) b	)
	
and subst_stub_flow_struc (t:string) (f:struc_formula) : struc_formula = subst_flow_of_struc_formula stub_flow t f	
      
let rec break_formula (f : formula) : P.b_formula list list =
  match f with
	| Base bf -> [P.break_pure_formula bf.formula_base_pure]
	| Exists ef -> [P.break_pure_formula ef.formula_exists_pure]
	| Or orf -> (break_formula orf.formula_or_f1) @ (break_formula orf.formula_or_f2)

and break_struc_formula (f : struc_formula) : P.b_formula list list = match f with
	| ECase cf -> List.map (fun (cond, sf) -> List.concat ([P.break_pure_formula cond] @ (break_struc_formula sf))) cf.formula_case_branches
	| EBase bf -> [List.concat ((break_formula bf.formula_struc_base) @ (Gen.fold_opt break_struc_formula bf.formula_struc_continuation))]
	| EAssume b -> break_formula b.formula_assume_simpl
	| EInfer bf -> break_struc_formula bf.formula_inf_continuation
	| EList b-> Gen.fold_l_snd break_struc_formula b

let isAccs(a : P.ann) : bool = 
  match a with
    | P.ConstAnn(Accs) -> true
    | _ -> false

let isLend(a : P.ann) : bool = 
  match a with
    | P.ConstAnn(Lend) -> true
    | _ -> false

and isMutable(a : P.ann) : bool = 
  match a with
    | P.ConstAnn(Mutable) -> true
    | _ -> false

and isImm(a : P.ann) : bool = 
  match a with
    | P.ConstAnn(Imm) -> true
    | _ -> false

let eq_var (sv1 : (ident * primed)) (sv2 : (ident * primed)) = match (sv1, sv2) with
  | ((v1, p1), (v2, p2)) -> v1 = v2 && p1 = p2

let diff_svl vl rl = Gen.BList.difference_eq eq_var vl rl

let rec prune_exists fml infer_vars = match fml with
  | Base _ -> fml
  | Or { formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos} -> 
    mkOr (prune_exists f1 infer_vars) (prune_exists f2 infer_vars) pos
  | Exists fml_ex ->
    let new_vars = diff_svl fml_ex.formula_exists_qvars infer_vars in
    Exists {fml_ex with formula_exists_qvars = new_vars}
    

let rec prune_exists_struc infer_vars fml = match fml with
	| ECase b -> ECase {b with formula_case_branches = map_l_snd (prune_exists_struc infer_vars) b.formula_case_branches}
	| EBase b -> EBase {b with 
		formula_struc_base = prune_exists b.formula_struc_base infer_vars;
		formula_struc_continuation = map_opt (prune_exists_struc infer_vars) b.formula_struc_continuation;}
	| EAssume b -> EAssume {b with 
		formula_assume_simpl = prune_exists  b.formula_assume_simpl infer_vars;
		formula_assume_struc = prune_exists_struc infer_vars b.formula_assume_struc;}
	| EInfer b -> EInfer {b with formula_inf_continuation = prune_exists_struc infer_vars b.formula_inf_continuation}
	| EList b -> EList (map_l_snd (prune_exists_struc infer_vars) b) 
	
(*find thread id for each one_formula*)
(*remove thread = id and add id into  formula_thread*)
let float_out_thread_one_formula_x (f : one_formula) : one_formula =
  (*find thread id in formula_delayed*)
  let dl = f.formula_delayed in
  let ps = P.list_of_conjs dl in
  (*look for a formula with thread=id*)
  let helper (f:P.formula) =
    match f with
      | P.BForm (bf, _) ->
          let p,_ = bf in
          (match p with
            | P.Eq (e1,e2,pos) ->
                (match e1 with
                  | P.Var ((id,_),_) ->
                      (if ((String.compare id thread_name) == 0) then
                        (match e2 with
                          | P.Var ((tid,pr),pos_e2) ->
                              (Some (tid,pr),f)
                          | _ ->
                              Error.report_error {Error.error_loc = no_pos; Error.error_text = "Not found: expecting a thread id var"})
                       else (None,f))
                  | _ -> (None,f))
            | _ -> (None,f))
      | _ -> (None,f)
  in
  let has_thread (f:P.formula) : bool =
    let res1,res2 = helper f in
    match res1 with
      | None -> false
      | Some _ -> true
  in
  let ps1, ps2 = List.partition has_thread ps in
  let n = List.length ps1 in
  if (n==0) then
    Error.report_error {Error.error_loc = no_pos; Error.error_text = "could not find a thread id"}
 else if (n>1) then (*conservative. Do not check for their equalities*)
   Error.report_error {Error.error_loc = no_pos; Error.error_text = "more than one thread id found"}
 else (*n=1*)
  let new_p = P.conj_of_list ps2 in
  let thread_f = List.hd ps1 in
  let thread_id,_ = helper thread_f in
  {f with formula_delayed = new_p; formula_thread = thread_id}

let float_out_thread_one_formula (f : one_formula) : one_formula =
  Debug.no_1  "float_out_thread_one_formula"
      !print_one_formula !print_one_formula
      float_out_thread_one_formula_x f

(*find thread id for each one_formula*)  
let float_out_thread_x (f : formula) : formula =
  let rec helper f =
  match f with
  | Base b ->
      let new_a = List.map float_out_thread_one_formula b.formula_base_and in
      Base {b with formula_base_and = new_a}
  | Exists e ->
      let new_a = List.map float_out_thread_one_formula e.formula_exists_and in
      Exists {e with formula_exists_and = new_a}
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let new_f1 = helper f1 in
      let new_f2 = helper f2 in
      let res = mkOr new_f1 new_f2 pos in
      res
  in helper f

let float_out_thread (f : formula) : formula =
  Debug.no_1 "float_out_thread" 
      !print_formula !print_formula 
      float_out_thread_x f


let rec float_out_thread_struc_formula_x lbl_getter annot_getter (f:struc_formula) : struc_formula = match f with
    | EAssume b -> 
		EAssume {b with 
			formula_assume_simpl = float_out_thread b.formula_assume_simpl; 
			formula_assume_struc = float_out_thread_struc_formula_x lbl_getter annot_getter b.formula_assume_struc ;}
    | ECase b -> 
		ECase {
			formula_case_branches = List.map (fun (c1,c2)-> (c1,(float_out_exps_from_heap_struc lbl_getter annot_getter c2 ))) b.formula_case_branches ; 
			formula_case_pos=b.formula_case_pos}
    | EBase b-> EBase {b with
				 formula_struc_base = float_out_thread b.formula_struc_base;
				 formula_struc_continuation =  Gen.map_opt (fun x -> float_out_thread_struc_formula_x lbl_getter annot_getter x ) b.formula_struc_continuation;
				}
    | EInfer b -> EInfer ({b with formula_inf_continuation = float_out_thread_struc_formula_x lbl_getter annot_getter b.formula_inf_continuation ;})
	| EList b -> EList (Gen.map_l_snd (fun x -> float_out_thread_struc_formula_x lbl_getter annot_getter x ) b)

let float_out_thread_struc_formula lbl_getter annot_getter (f:struc_formula): struc_formula = 
  Debug.no_1 "float_out_thread_struc_formula"
      !print_struc_formula !print_struc_formula
      (fun _ -> float_out_thread_struc_formula_x lbl_getter annot_getter f) f 


let add_pure_formula_to_formula (p:P.formula) (f0 : formula): formula =
  let rec helper f0 =
    match f0 with
      | Base b -> Base {b with formula_base_pure = P.mkAnd p b.formula_base_pure no_pos}
      | Exists e -> Exists {e with formula_exists_pure = P.mkAnd p e.formula_exists_pure no_pos}
      | Or o ->
          let o1 = helper o.formula_or_f1 in
          let o2 = helper o.formula_or_f2 in
          (Or {o with formula_or_f1 = o1; formula_or_f2 = o2})
  in helper f0
	  
let add_h_formula_to_formula (h_f: h_formula) (f0 : formula): formula =
  let rec helper f0 =
    match f0 with
      | Base b ->
          let h = mkStar b.formula_base_heap h_f b.formula_base_pos in
          (Base {b with formula_base_heap =h})
      | Exists e ->
          let h = mkStar e.formula_exists_heap h_f e.formula_exists_pos in
          (Exists {e with formula_exists_heap =h})
      | Or o ->
          let o1 = helper o.formula_or_f1 in
          let o2 = helper o.formula_or_f2 in
          (Or {o with formula_or_f1 = o1; formula_or_f2 = o2})
  in helper f0

(* merge f1 into f2 *)
let mkStar_formula (f1 : formula) (f2 : formula) (pos : loc) = 
  let h1, p1, vp1, fl1, a1 = split_components f1 in
  let h2, p2, vp2, fl2, a2 = split_components f2 in
  (* assume no phase *)
  let h = mkStar h1 h2 pos in
  let p = Ipure.mkAnd p1 p2 pos in
  let vp = VP.merge_vperm_sets [vp1; vp2] in
  (* assume similar flow *)
  let fl = fl2 in (* or fl1 *)
  let a = a1@a2 in (* combine a1 and a2: assuming merging a1 and a2 *)
  mkBase h p vp fl a pos (* TO CHECK: how about a1,a2: DONE *)

(* merge f1 into f2 *)
let normalize_formula (f1 : formula) (f2 : formula) (pos : loc) = 
  let rec helper f1 f2 pos =
    match f1 with
    | Or ({ formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _ }) ->
      let eo1 = helper o11 f2 pos in
      let eo2 = helper o12 f2 pos in
      mkOr eo1 eo2 pos
    | _ -> begin
      match f2 with
      | Or ({ formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _ }) ->
        let eo1 = helper f1 o21 pos in
        let eo2 = helper f1 o22 pos in
        mkOr eo1 eo2 pos
      | _ -> begin
        let rf1 = x_add_1 rename_bound_vars f1 in
        let rf2 = x_add_1 rename_bound_vars f2 in
        let qvars1, base1 = split_quantifiers rf1 in
        let qvars2, base2 = split_quantifiers rf2 in
        let new_base = mkStar_formula base1 base2 pos in
        let new_h, new_p, new_vp, new_fl, new_a = split_components new_base in
        (* qvars[1|2] are fresh vars, hence no duplications *)
        let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_fl new_a pos in
        resform
      end
    end
  in helper f1 f2 pos

let add_h_formula_to_pre_x (h_f,impl_vars) (f0 : struc_formula): struc_formula =
  let rec helper (f0:struc_formula) =
    match f0 with
	  | EAssume _ -> f0
	  | ECase b-> ECase {b with 
		  formula_case_branches = (List.map (fun (c1,c2)->(c1,(helper c2))) b.formula_case_branches)}
	  | EBase b -> EBase {b with
          formula_struc_explicit_inst = b.formula_struc_explicit_inst@impl_vars;
		  formula_struc_base = add_h_formula_to_formula h_f  b.formula_struc_base;}
	  | EInfer b -> EInfer {b with
          formula_inf_continuation = helper b.formula_inf_continuation}
	  | EList b -> EList (Gen.map_l_snd helper b)
  in helper f0

let add_h_formula_to_pre (h_f,impl_vars) (f0 : struc_formula): struc_formula =
  let pr1 = pr_pair !print_h_formula string_of_spec_var_list in
  Debug.no_2 "add_h_formula_to_pre"
      pr1 !print_struc_formula !print_struc_formula
      add_h_formula_to_pre_x (h_f,impl_vars) f0

let add_formula_to_post_x (f,ex_vars) (f0 : struc_formula): struc_formula =
  let rec helper (f0:struc_formula) =
    match f0 with
      | EAssume b -> 
		  EAssume {b with 
			formula_assume_simpl = add_quantifiers ex_vars (normalize_formula f b.formula_assume_simpl no_pos);
			formula_assume_struc = match b.formula_assume_struc with
				| EBase b -> 
					EBase {b with 
						formula_struc_base = normalize_formula f b.formula_struc_base no_pos;
						formula_struc_exists = ex_vars@b.formula_struc_exists;}
				| _ -> mkEBase [] [] ex_vars f (Some b.formula_assume_struc) no_pos;}
      | ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> c1,helper c2) b.formula_case_branches}
      | EBase b -> EBase {b with formula_struc_continuation = Gen.map_opt helper b.formula_struc_continuation; }
      | EInfer b-> EInfer {b with formula_inf_continuation = helper b.formula_inf_continuation;}
	  | EList b -> EList (Gen.map_l_snd helper b)
  in helper f0

let add_formula_to_post (f,ex_vars) (f0 : struc_formula): struc_formula =
  let pr1 = pr_pair !print_formula string_of_spec_var_list in
  Debug.no_2 "add_formula_to_post"
      pr1 !print_struc_formula !print_struc_formula
      add_formula_to_post_x (f,ex_vars) f0

let mkEInfer xpost transpec pos = EInfer { 
    (* formula_inf_tnt = false; *)
    formula_inf_obj = new Globals.inf_obj; (* Globals.infer_const_obj # clone; *)
    formula_inf_post = true;
    formula_inf_xpost = xpost;
    formula_inf_transpec = transpec;
    formula_inf_vars = [];
    formula_inf_continuation = EList [];
    formula_inf_pos = pos}

let merge_cmd einfer spec = match einfer with
  | EInfer e -> EInfer {e with formula_inf_continuation = spec}
  | EBase _ -> einfer
  | _ -> Gen.report_error no_pos "Error in merge_cmd"


type find_bar_node = 
	| Bar_wrong_state 
	| Bar_state_var of (ident*primed)
	| Bar_state_ok
	| Bar_not_found
	  
let find_barr_node bname (f:int) (t:int) struc :bool= 
	let rec find_h_node x h = match h with 
		 | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
		 | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
		 | ConjStar {h_formula_conjstar_h1 = h1; h_formula_conjstar_h2 = h2}
		 | ConjConj {h_formula_conjconj_h1 = h1; h_formula_conjconj_h2 = h2}	
		 | StarMinus {h_formula_starminus_h1 = h1; h_formula_starminus_h2 = h2}	 		 
		 | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2} -> 
			(match find_h_node x h1 with 
				| Bar_not_found -> find_h_node x h2 
				| _ as x-> x)
		 | HeapNode h -> 
			if fst h.h_formula_heap_node = self && h.h_formula_heap_name=bname then 
				(match  h.h_formula_heap_arguments with 
					| [] -> Bar_wrong_state
					| (P.Var (v,_))::_-> Bar_state_var v
					| (P.IConst (v,_))::_ -> if x=v then Bar_state_ok else Bar_wrong_state
					| _ -> Bar_wrong_state)
			else Bar_not_found
	     | ThreadNode h -> Bar_not_found (*TOCHECK: inside thread_resource*)
		 | HeapNode2 h -> Gen.report_error no_pos "malfunction with convert to heap node"
		 | HRel _ | HTrue | HEmp | HFalse |HVar _ -> Bar_not_found in
	let rec find_node x f= match f with 
		| Base {formula_base_heap = h; formula_base_pure = p} 
		| Exists {formula_exists_heap = h; formula_exists_pure = p} -> 
		  (match find_h_node x h with 
			| Bar_wrong_state -> false
		    | Bar_state_var v -> P.find_p_val x v p
			| Bar_state_ok -> true
			| Bar_not_found -> false)
		| Or e -> find_node x e.formula_or_f1 && find_node x e.formula_or_f2 in
	let rec helper b f0 = match f0 with
		| EAssume e -> if b then find_node t e.formula_assume_simpl else false
		| ECase e -> Gen.Basic.all_l_snd (helper b) e.formula_case_branches
		| EBase e-> (match e.formula_struc_continuation with | None -> false | Some cont-> helper (if b then b else find_node f e.formula_struc_base) cont)
		| EInfer e -> helper b e.formula_inf_continuation
		| EList e -> Gen.Basic.all_l_snd (helper b) e in
	helper false struc 

	
let add_post_for_flow fl_names f = 
	let rec fct c = match c with
		| Or b -> Or { formula_or_f1 = fct b.formula_or_f1; formula_or_f2 = fct b.formula_or_f2; formula_or_pos = b.formula_or_pos}
		| Base b -> 
			if (String.compare b.formula_base_flow n_flow) == 0 then  
				let l = List.map (fun c-> Base {b with formula_base_flow = c}) fl_names in
				List.fold_left (fun a c-> mkOr a c b.formula_base_pos) c l 
			else c
		| Exists b ->
			if (String.compare b.formula_exists_flow n_flow) == 0 then  
				let l = List.map (fun c-> Exists {b with formula_exists_flow = c}) fl_names in
				List.fold_left (fun a c-> mkOr a c b.formula_exists_pos) c l 
			else c in	
	let rec helper is_post f =  match f with
		| ECase c -> ECase {c with formula_case_branches = List.map (fun (c1,c2)-> c1,helper is_post c2) c.formula_case_branches} 
		| EBase b -> 
			let new_base = if is_post then fct b.formula_struc_base else b.formula_struc_base in
			let new_cont = Gen.map_opt (helper is_post) b.formula_struc_continuation in
			EBase {b with formula_struc_continuation = new_cont; formula_struc_base = new_base}
		| EInfer b-> EInfer {b with formula_inf_continuation = helper is_post b.formula_inf_continuation;}
		| EList b -> EList (Gen.map_l_snd (helper is_post) b)
		| EAssume b -> EAssume {b with 
			formula_assume_simpl = fct b.formula_assume_simpl; 
			formula_assume_struc = helper true b.formula_assume_struc;} in
	helper false f
	

let rec flatten_post_struc f pos = match f with
	| EBase b -> 
		if b.formula_struc_explicit_inst!=[] || b.formula_struc_implicit_inst!=[] || b.formula_struc_exists!=[] then
			report_error  pos "EAssume does not perform instantiations"
		else (match b.formula_struc_continuation with
			| None -> b.formula_struc_base
			| Some c-> normalize_formula b.formula_struc_base (flatten_post_struc c pos) pos)
	| ECase b -> 
		disj_of_list (List.map (fun (c1,c2)-> add_pure_formula_to_formula c1 (flatten_post_struc c2 pos)) b.formula_case_branches) true pos
	| EList b -> 
		disj_of_list (List.map (fun(_,c)-> flatten_post_struc c pos) b) true pos
	| _ -> report_error pos "EAssume supports does not allow multiple assume or any infer stage"
	
	
let rec wrap_post_struc_ex fv f = match f with 
	| EBase b -> 
		let fvc,_ = map_opt_def ([],[])(fun c-> struc_split_fv c false) b.formula_struc_continuation in
		let ninst = Gen.BList.intersect_eq (=) b.formula_struc_implicit_inst fvc in
		let a_fv = fvc@fv@ninst in
		let bfv = all_fv b.formula_struc_base in
		let not_quant, to_quant  = List.partition (fun c-> List.mem c a_fv) bfv in
		EBase {b with 
			formula_struc_base = push_exists to_quant b.formula_struc_base;
			formula_struc_continuation = map_opt (wrap_post_struc_ex  (fv@not_quant)) b.formula_struc_continuation;
			formula_struc_explicit_inst = [];
			formula_struc_implicit_inst = ninst;}
	| ECase b -> ECase { b with 
		formula_case_branches = List.map (fun (c1,c2)-> c1, wrap_post_struc_ex (fv@ P.fv c1) c2) b.formula_case_branches}
	| _ -> f
	
let wrap_post_struc_ex fv f = 
	Debug.no_2 "wrap_post_struc_ex" (pr_list !P.print_id) !print_struc_formula !print_struc_formula
		wrap_post_struc_ex fv f 

let rec struc_formula_drop_infer f =
 let recf = struc_formula_drop_infer in
 match f with
    | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd recf b.formula_case_branches}
	| EBase b -> EBase {b with formula_struc_continuation = Gen.map_opt recf b.formula_struc_continuation}
	| EAssume _ -> f
	| EInfer b-> b.formula_inf_continuation
	| EList l-> EList (Gen.map_l_snd recf l)
	(* | EOr b-> mkEOr (recf b.formula_struc_or_f1) (recf b.formula_struc_or_f2) b.formula_struc_or_pos *)

let rec heap_trans_heap_node fct f =
 let recf = heap_trans_heap_node fct in
 match f with
  | HTrue | HRel _ -> fct f
  |  HFalse | HEmp | HVar _ | HeapNode _ | HeapNode2 _ -> f
  | ThreadNode h -> ThreadNode {h with h_formula_thread_resource = formula_trans_heap_node fct h.h_formula_thread_resource}
  | Phase b -> Phase {b with h_formula_phase_rd = recf b.h_formula_phase_rd; h_formula_phase_rw = recf b.h_formula_phase_rw}
  | Conj b -> Conj {b with h_formula_conj_h2 = recf b.h_formula_conj_h2; h_formula_conj_h1 = recf b.h_formula_conj_h1}
  | Star b -> Star {b with h_formula_star_h2 = recf b.h_formula_star_h2; h_formula_star_h1 = recf b.h_formula_star_h1}
  | ConjStar _|ConjConj _|StarMinus _ -> report_error no_pos "IF.heap_trans_heap_node: not handle yet"


and formula_trans_heap_node fct f =
  let recf = formula_trans_heap_node fct in
  match f with
	| Base b-> Base{b with  formula_base_heap = heap_trans_heap_node fct b.formula_base_heap}
	| Exists b-> Exists{b with  formula_exists_heap = heap_trans_heap_node fct b.formula_exists_heap}
	| Or b-> Or {b with formula_or_f1 = recf b.formula_or_f1;formula_or_f2 = recf b.formula_or_f2}
 
and struc_formula_trans_heap_node_x fct f =
 let recf = struc_formula_trans_heap_node fct in
  match f with
    | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd recf b.formula_case_branches}
	| EBase b -> EBase {b with
						formula_struc_continuation = Gen.map_opt recf b.formula_struc_continuation;
						formula_struc_base=formula_trans_heap_node fct b.formula_struc_base;}
	| EAssume ea-> EAssume {ea with  formula_assume_simpl = formula_trans_heap_node fct ea.formula_assume_simpl;
                           formula_assume_struc = recf ea.formula_assume_struc}
 (* (formula_trans_heap_node fct f, fl, et) *)
	| EInfer _ -> f
	| EList l -> EList (Gen.map_l_snd recf l)
	(* | EOr b-> mkEOr (recf b.formula_struc_or_f1) (recf b.formula_struc_or_f2) b.formula_struc_or_pos *)
	
and struc_formula_trans_heap_node fct f =
	let pr = !print_struc_formula in
	Debug.no_1 "struc_formula_trans_heap_node" pr pr (struc_formula_trans_heap_node_x fct) f


let rec heap_drop_heap_node f0 hns=
  let rec helper f=
 match f with
  | HRel b -> f
  | HTrue  | HFalse | HEmp | HVar _ -> f
  | HeapNode hn ->
      if List.exists (fun s1 -> String.compare s1 hn.h_formula_heap_name =0) hns then
        HEmp
      else f
  | HeapNode2 hn2 ->
      if List.exists (fun s1 -> String.compare s1 hn2.h_formula_heap2_name =0) hns then
        HEmp
      else f
  | ThreadNode hn ->
      if List.exists (fun s1 -> String.compare s1 hn.h_formula_thread_name =0) hns then
        HEmp
      else f
  | Phase b -> Phase {b with h_formula_phase_rd = helper b.h_formula_phase_rd; h_formula_phase_rw = helper b.h_formula_phase_rw}
  | Conj b -> Conj {b with h_formula_conj_h2 = helper b.h_formula_conj_h2; h_formula_conj_h1 = helper b.h_formula_conj_h1}
  | Star b -> begin
      let nh1 = helper b.h_formula_star_h1 in
      let nh2 = helper b.h_formula_star_h2 in
      match nh1,nh2 with
        | HEmp,HEmp -> HEmp
        | HEmp,_ -> nh2
        | _, HEmp -> nh1
        | _ ->
            Star {b with h_formula_star_h2 = nh2; h_formula_star_h1 = nh1}
  end
  | ConjStar _|ConjConj _|StarMinus _ -> report_error no_pos "IF.heap_drop_heap_node: not handle yet"
  in
  helper f0


let rec formula_drop_heap_node f0 hns=
  let rec helper f=
    match f with
      | Base b-> Base{b with formula_base_heap = heap_drop_heap_node b.formula_base_heap hns}
      | Exists b-> Exists{b with formula_exists_heap = heap_drop_heap_node b.formula_exists_heap hns}
      | Or b-> Or {b with formula_or_f1 = helper b.formula_or_f1;formula_or_f2 = helper b.formula_or_f2}
  in
  helper f0

let rec struc_formula_drop_heap_node f0 hns =
  let rec helper f=
    match f with
      | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd helper b.formula_case_branches}
      | EBase b -> EBase {b with
	    formula_struc_continuation = Gen.map_opt helper b.formula_struc_continuation;
	    formula_struc_base=formula_drop_heap_node b.formula_struc_base hns;}
      | EAssume ea -> EAssume {ea with formula_assume_simpl = formula_drop_heap_node ea.formula_assume_simpl hns;
            formula_assume_struc = helper ea.formula_assume_struc }
            (* (formula_drop_heap_node f hns, fl, et) *)
      | EInfer _ -> f
      | EList l -> EList (Gen.map_l_snd helper l)
	    (* | EOr b-> mkEOr (helper b.formula_struc_or_f1) (helper b.formula_struc_or_f2) b.formula_struc_or_pos *)
  in
  helper f0

let struc_formula_drop_heap_node f hns =
	let pr = !print_struc_formula in
	Debug.no_1 "struc_formula_drop_heap_node" pr pr (fun _ -> struc_formula_drop_heap_node f hns) f

let split_star_conjunctions (f:h_formula): (h_formula list) =
  let rec helper f = 
  match f with
  | Star({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos;}) ->
        let res1 = helper h1 in
        let res2 = helper h2 in
        (res1@res2)
    | _ -> [f]
  in
  helper f

let type_of_formula (f: formula) : formula_type =
  (* if (isAnyConstFalse f) then Simple *)
  (* else  *)
    match f with
    | Base b  ->
        let h = b.formula_base_heap in
        let hs = split_star_conjunctions h in
        if ((List.length hs)>1) then Complex 
        else Simple 
    | Exists e ->
        let h = e.formula_exists_heap in
        let hs = split_star_conjunctions h in
        if ((List.length hs)>1) then Complex 
        else Simple
    | _ -> Complex


let normal_formula view_nodes data_nodes f0=
  let sv_cmp (s1,p1) (s2,p2) = p1=p2 && String.compare s1 s2 = 0 in
  let extract_qvars hns hn2s=
    let ei1 = List.fold_left (fun r hn -> if Gen.BList.mem_eq sv_cmp hn.h_formula_heap_node data_nodes then
      r@hn.h_formula_heap_arguments else r) [] (hns) in
    let ei2 = List.fold_left (fun r hn -> if Gen.BList.mem_eq sv_cmp hn.h_formula_heap2_node data_nodes then
      r@hn.h_formula_heap2_arguments else r) [] (hn2s) in
    let ei = ei1@(snd (List.split ei2)) in
    List.fold_left (fun r e -> r@(Ipure.afv e)) [] ei
  in
  let extract_iis hns hn2s=
    let qvars1 = List.fold_left (fun r hn -> if Gen.BList.mem_eq sv_cmp hn.h_formula_heap_node view_nodes then
      r@hn.h_formula_heap_arguments else r) [] (hns) in
    let qvars2 = List.fold_left (fun r hn -> if Gen.BList.mem_eq sv_cmp hn.h_formula_heap2_node view_nodes then
      r@hn.h_formula_heap2_arguments else r) [] (hn2s) in
    let qvars = qvars1@(snd (List.split qvars2)) in
    List.fold_left (fun r e -> r@(Ipure.afv e)) [] qvars
  in
  let fresh_qvars qvars f=
    let fr_qvars = Ipure.fresh_vars qvars in
    let ss0 = List.combine qvars fr_qvars in
    let eq_ps = List.map (fun (sv1, sv2) -> Ipure.mkEqVarExp sv1 sv2 no_pos) ss0 in
    let p = Ipure.conj_of_list eq_ps in
    let f1 = subst ss0 f in
    (fr_qvars,add_pure_formula_to_formula p f1)
  in
  let rec helper f=
    match f with
      | Base fb ->
            let hns, hn2s = get_heap_nodes fb.formula_base_heap in
            (*data nodes*)
            let qvars0 = extract_qvars hns hn2s in
            (*view nodes*)
            let ii = extract_iis hns hn2s in
            let qvars = Gen.BList.difference_eq sv_cmp qvars0 ii in
            let nb = if qvars = [] then f else
              let fr_qvars, f1 = (fresh_qvars qvars f) in
              add_quantifiers fr_qvars f1 in
            mkEBase [] ii [] nb None fb.formula_base_pos
      | Exists fe ->
            let hns, hn2s = get_heap_nodes fe.formula_exists_heap in
            (*data nodes*)
            let qvars = extract_qvars hns hn2s in
            (*view nodes*)
            let ii = extract_iis hns hn2s in
            let qvars0, basef = split_quantifiers f in
            let qvars0a = Gen.BList.difference_eq sv_cmp qvars0 ii in
            let qvars1 = Gen.BList.difference_eq sv_cmp qvars (ii@qvars0) in
            let nb = if qvars1 = [] then add_quantifiers qvars0a basef else
              let fr_qvars, f1 = (fresh_qvars qvars1 basef) in
              add_quantifiers (qvars0a@fr_qvars) f1 in
            mkEBase [] ii [] nb None fe.formula_exists_pos
      | Or orf -> let sf1 = helper orf.formula_or_f1 in
        let sf2 = helper orf.formula_or_f2 in
        EList [(Label_only.empty_spec_label_def,sf1);(Label_only.empty_spec_label_def,sf2)]
  in
  helper f0


let normal_formula view_nodes data_nodes f0=
  let pr1 = !print_formula in
  let pr2 = !print_struc_formula in
  let pr_svl = pr_list (pr_id fst) in
  Debug.no_3 "normal_formula" pr_svl pr_svl pr1 pr2
      (fun _ _ _ -> normal_formula view_nodes data_nodes f0)
      view_nodes data_nodes f0

let h_formula_collect_hvar hf0 =
  let rec helper hf = match hf with
    |  Star{ h_formula_star_h1 = hf1;
          h_formula_star_h2 = hf2;}
    |  StarMinus{ h_formula_starminus_h1 = hf1;
          h_formula_starminus_h2 = hf2;}
    |  Conj { h_formula_conj_h1 = hf1;
          h_formula_conj_h2 = hf2;}
    |  ConjStar { h_formula_conjstar_h1 = hf1;
          h_formula_conjstar_h2 = hf2;}
    |  ConjConj { h_formula_conjconj_h1 = hf1;
          h_formula_conjconj_h2 = hf2;}
    |  Phase { h_formula_phase_rd = hf1;
          h_formula_phase_rw = hf2;} -> (helper hf1)@(helper hf2)
    | HVar (v,_) -> [v]
    | _ -> []
  in
  helper hf0

let formula_collect_hvar f0 =
  let rec helper f=
    match f with
      | Base {formula_base_heap = hf}
      | Exists {formula_exists_heap = hf} ->
            h_formula_collect_hvar hf
      | Or orf -> (helper orf.formula_or_f1)@(helper orf.formula_or_f2)
  in
  helper f0

let h_formula_collect_hprel hf0 =
  let rec helper hf = match hf with
    |  Star{ h_formula_star_h1 = hf1;
          h_formula_star_h2 = hf2;}
    |  StarMinus{ h_formula_starminus_h1 = hf1;
          h_formula_starminus_h2 = hf2;}
    |  Conj { h_formula_conj_h1 = hf1;
          h_formula_conj_h2 = hf2;}
    |  ConjStar { h_formula_conjstar_h1 = hf1;
          h_formula_conjstar_h2 = hf2;}
    |  ConjConj { h_formula_conjconj_h1 = hf1;
          h_formula_conjconj_h2 = hf2;}
    |  Phase { h_formula_phase_rd = hf1;
          h_formula_phase_rw = hf2;} -> (helper hf1)@(helper hf2)
    | HRel (id, es,_) -> [(id, List.fold_left (fun r e -> r@(List.map fst (Ipure.afv e))) [] es)]
    | _ -> []
  in
  helper hf0

let formula_collect_hprel f0 =
  let rec helper f=
    match f with
      | Base {formula_base_heap = hf}
      | Exists {formula_exists_heap = hf} ->
            h_formula_collect_hprel hf
      | Or orf -> (helper orf.formula_or_f1)@(helper orf.formula_or_f2)
  in
  helper f0

let struc_formula_collect_pre_hprel_x f0 =
  let rec helper f=
    match f with
      | ECase b-> List.fold_left (fun r (_,sc) -> r@(helper sc)) [] b.formula_case_branches
      | EBase b ->  formula_collect_hprel b.formula_struc_base
      | EAssume _ -> []
      | EInfer b -> helper b.formula_inf_continuation
      | EList l -> List.fold_left (fun r (_,sc) -> r@(helper sc)) [] l
  in
  helper f0

let struc_formula_collect_pre_hprel f0 =
  let pr1 = !print_struc_formula in
  let pr2 = pr_list (pr_pair pr_id (pr_list pr_id)) in
  Debug.no_1 "struc_formula_collect_pre_hprel" pr1 pr2
      (fun _ -> struc_formula_collect_pre_hprel_x f0) f0


let rec transform_h_formula_x (f: h_formula -> h_formula option) (e: h_formula)
    : h_formula = 
  let r =  f e in 
  match r with
  | Some e1 -> e1
  | None  -> (
      match e with  
      | Star s ->
          let new_h1 = transform_h_formula f s.h_formula_star_h1 in
          let new_h2 = transform_h_formula f s.h_formula_star_h2 in
          Star {s with h_formula_star_h1 = new_h1;
                       h_formula_star_h2 = new_h2;}
      | StarMinus s ->
          let new_h1 = transform_h_formula f s.h_formula_starminus_h1 in
          let new_h2 = transform_h_formula f s.h_formula_starminus_h2 in
          StarMinus {s with h_formula_starminus_h1 = new_h1;
                            h_formula_starminus_h2 = new_h2;}
      | Conj s ->
          let new_h1 = transform_h_formula f s.h_formula_conj_h1 in
          let new_h2 = transform_h_formula f s.h_formula_conj_h1 in
          Conj {s with h_formula_conj_h1 = new_h1;
                       h_formula_conj_h2 = new_h2;}
      | ConjStar s ->
          let new_h1 = transform_h_formula f s.h_formula_conjstar_h1 in
          let new_h2 = transform_h_formula f s.h_formula_conjstar_h2 in
          ConjStar {s with h_formula_conjstar_h1 = new_h1;
                           h_formula_conjstar_h2 = new_h2;}
      | ConjConj s ->
          let new_h1 = transform_h_formula f s.h_formula_conjconj_h1 in
          let new_h2 = transform_h_formula f s.h_formula_conjconj_h2 in
          ConjConj {s with h_formula_conjconj_h1 = new_h1;
                          h_formula_conjconj_h2 = new_h2;}
      | Phase s ->
          let new_rd = transform_h_formula f s.h_formula_phase_rd in
          let new_rw = transform_h_formula f s.h_formula_phase_rw in
          Phase {s with h_formula_phase_rd = new_rd;
                        h_formula_phase_rw = new_rw;}
      | HeapNode _ | HeapNode2 _ | ThreadNode _
      | HRel _ | HTrue | HFalse | HEmp | HVar _ -> e
    )

and transform_h_formula (f: h_formula -> h_formula option) (e: h_formula)
    : h_formula =
  let pr = !print_h_formula in
  Debug.no_1 "IF.transform_h_formula" pr pr (fun _ -> transform_h_formula_x f e) e

let drop_htrue hf=
  match hf with
    | HTrue -> HEmp
    | _ -> hf

let transform_formula_x f (e:formula):formula =
  let rec helper f e = (
    let (_, f_f, f_h_f, f_p_t) = f in
    let r =  f_f e in 
    match r with
    | Some e1 -> e1
    | None  -> (
        match e with     
        | Base b ->
            let new_heap = transform_h_formula f_h_f b.formula_base_heap in
            let new_pure = P.transform_formula f_p_t b.formula_base_pure in
            Base { b with formula_base_heap = new_heap;
                          formula_base_pure = new_pure; }
        | Or o -> 
            Or {o with formula_or_f1 = helper f o.formula_or_f1;
                       formula_or_f2 = helper f o.formula_or_f2;}
        | Exists e ->
            let new_heap = transform_h_formula f_h_f e.formula_exists_heap in
            let new_pure = P.transform_formula f_p_t e.formula_exists_pure in
            Exists { e with formula_exists_heap = new_heap;
                            formula_exists_pure = new_pure;}
      )
  ) in
  helper f e


let transform_formula f (e:formula):formula =
  let pr = !print_formula in
  Debug.no_1 "IF.transform_formula" pr pr (fun _ -> transform_formula_x f e) e

let transform_formula_simp trans_hf (e:formula):formula =
  let rec helper e =
    match e with     
      | Base b ->
            let new_heap = trans_hf b.formula_base_heap in
            Base { b with formula_base_heap = new_heap; }
        | Or o -> 
              Or {o with formula_or_f1 = helper o.formula_or_f1;
                  formula_or_f2 = helper o.formula_or_f2;}
        | Exists e ->
              let new_heap = trans_hf e.formula_exists_heap in
              Exists { e with formula_exists_heap = new_heap;}
  in
  helper  e

let rec transform_struc_formula_x f (e:struc_formula) : struc_formula = 
  let (f_e_f, f_f, f_h_f, f_p_t) = f in
  let r = f_e_f e in 
  match r with
  | Some e1 -> e1
  | None -> (
      match e with
      | ECase c -> 
          let br' = List.map (fun (c1,c2)->
            ((P.transform_formula f_p_t c1),(transform_struc_formula f c2))
          ) c.formula_case_branches in
          ECase {c with formula_case_branches = br';}
      | EBase b ->
          let new_base = transform_formula f b.formula_struc_base in
          let new_cont = map_opt (transform_struc_formula f) b.formula_struc_continuation in
          EBase{b with formula_struc_base = new_base;
                       formula_struc_continuation = new_cont;}
      | EAssume b->
          let new_simpl = transform_formula f b.formula_assume_simpl in
          let new_struc = transform_struc_formula f b.formula_assume_struc in
          EAssume {b with formula_assume_simpl = new_simpl;
                          formula_assume_struc = new_struc;}
      | EInfer b ->
          let new_cont = transform_struc_formula f b.formula_inf_continuation in
          EInfer {b with formula_inf_continuation = new_cont;}
      | EList b -> EList (map_l_snd (transform_struc_formula f) b)
    )

and transform_struc_formula f (e:struc_formula) : struc_formula =
  let pr = !print_struc_formula in
  Debug.no_1 "IF.transform_struc_formula" pr pr
      (fun _ -> transform_struc_formula_x f e) e

let transform_bexp_hf_x prog hf0=
  let trans_bexp_arg (eas, ps) ae= match ae with
    | Ipure.BExpr f -> let pos = Ipure.pos_of_exp ae in
      let be_id = Globals.fresh_any_name "be" in
      let e = Ipure.Var ((be_id, Unprimed), pos) in
      let p = Ipure.transform_bexp (Ipure.mkTrue pos) None None e f in
      (* let nae = Ipure.BVar ((be_id, Unprimed), pos) in *)
      (eas@[e], ps@[p])
    | _ -> (eas@[ae], ps)
  in
  let rec recf hf= match hf with
    | HeapNode hn ->
          let neargs, ps_bexp = List.fold_left trans_bexp_arg ([],[]) hn.h_formula_heap_arguments in
          (HeapNode {hn with h_formula_heap_arguments = neargs}, ps_bexp)
    | _ -> hf,[]
  in
  recf hf0

let transform_bexp_hf prog hf0=
  let pr1 = !print_h_formula in
  Debug.no_1 "transform_bexp_hf" pr1 (pr_pair pr1 (pr_list !Ipure.print_formula))
      (fun _ -> transform_bexp_hf_x prog hf0) hf0
