  
(*
  Created 21-Feb-2006

  Formula
*)

module DD = Debug
open Globals
open Gen
open Exc.GTable
open Perm
open Label_only
open Label 

module Err = Error
module CP = Cpure
module MCP = Mcpure

type ann = ConstAnn of heap_ann | PolyAnn of CP.spec_var

type typed_ident = (typ * ident)

and formula_type = 
  | Simple
  | Complex
(*later, type of formula, based on #nodes ....*)

type t_formula = (* type constraint *)
	(* commented out on 09.06.08 : we have decided to remove for now the type information related to the OO extension
  	   | TypeExact of t_formula_sub_type (* for t = C *)
	   | TypeSub of t_formula_sub_type (* for t <: C *)
	   | TypeSuper of t_formula_sub_type (* for t < C *)
	*)

  | TypeAnd of t_formula_and
  | TypeTrue
  | TypeFalse
  | TypeEmpty

and t_formula_sub_type = { t_formula_sub_type_var : Cpure.spec_var;
t_formula_sub_type_type : ident }

and t_formula_and = { t_formula_and_f1 : t_formula;
t_formula_and_f2 : t_formula }


(*and struc_formula = (formula_label*ext_formula) list*)

and struc_formula = 
  | EOr of  struc_or_formula
  | EList of (spec_label_def * struc_formula) list 
  | ECase of struc_case_formula
  | EBase of struc_base_formula
  | EAssume of ((Cpure.spec_var list) * formula * formula_label)
  | EInfer of struc_infer_formula
  

and struc_or_formula = 
  {
      formula_struc_or_f1 : struc_formula;
      formula_struc_or_f2 : struc_formula;
      formula_struc_or_pos: loc;
  }

and struc_infer_formula =
  {
    formula_inf_post : bool; (* true if post to be inferred *)
    formula_inf_xpost : bool option; (* None -> no auto-var; Some _ -> true if post to be inferred *)
    formula_inf_transpec : (ident * ident) option;
    formula_inf_vars : Cpure.spec_var list;
    formula_inf_continuation : struc_formula;
    (* TODO : can we change this to struc_formula instead *)
    (* formula_inf_continuation : struc_formula; *)
    formula_inf_pos : loc
  }

and struc_case_formula =
	{
		formula_case_branches : (Cpure.formula * struc_formula ) list;
		formula_case_exists : Cpure.spec_var list; (*should be absolete, to be removed *)
		formula_case_pos : loc 		
	}

and struc_base_formula =
	{
		formula_struc_explicit_inst : Cpure.spec_var list;
		formula_struc_implicit_inst : Cpure.spec_var list;
        (* 
           vars_free, vars_linking, vars_extracted 
        *)
		formula_struc_exists : Cpure.spec_var list;
		formula_struc_base : formula;
		formula_struc_continuation : struc_formula option;
		formula_struc_pos : loc
	}
	
and formula =
  | Base of formula_base
  | Or of formula_or
  | Exists of formula_exists

and list_formula = formula list

and formula_base = {  formula_base_heap : h_formula;
                      formula_base_pure : MCP.mix_formula;
                      formula_base_type : t_formula; (* a collection ot subtype information *)
                      formula_base_and : one_formula list; (*to capture concurrent flows*)
                      formula_base_flow : flow_formula;
                      formula_base_label : formula_label option;
                      formula_base_pos : loc }


and mem_formula = { 
  mem_formula_mset : CP.DisjSetSV.dpart ; (* list of disjoint vars *)
}

and formula_or = {  formula_or_f1 : formula;
                    formula_or_f2 : formula;
                    formula_or_pos : loc }

and formula_exists = {  formula_exists_qvars : CP.spec_var list;
                        formula_exists_heap : h_formula;
                        formula_exists_pure : MCP.mix_formula;
                        formula_exists_type : t_formula;
                        formula_exists_and : one_formula list;
                        formula_exists_flow : flow_formula;
                        formula_exists_label : formula_label option;
                        formula_exists_pos : loc }

and flow_formula = {  formula_flow_interval : nflow; 
                      formula_flow_link : (ident option)}
and flow_store = {
	formula_store_name : ident;
	formula_store_value : flow_formula;		
}

and one_formula = {
    formula_heap : h_formula;
    formula_pure : MCP.mix_formula;
    formula_thread : CP.spec_var;
    formula_ref_vars : CP.spec_var list; (*to update ref vars when join*)
    formula_label : formula_label option;
    formula_pos : loc
}
	
and flow_treatment = 
  | Flow_combine
  | Flow_replace
		  
and h_formula = (* heap formula *)
  | Star of h_formula_star
  | Conj of h_formula_conj
  | Phase of h_formula_phase
  | DataNode of h_formula_data
  | ViewNode of h_formula_view
  | Hole of int
  | HRel of (CP.spec_var * (CP.exp list) * loc)
  | HTrue
  | HFalse
  | HEmp (* emp for classical logic *)

          
and h_formula_star = {  h_formula_star_h1 : h_formula;
                        h_formula_star_h2 : h_formula;
                        h_formula_star_pos : loc }

and h_formula_conj = { h_formula_conj_h1 : h_formula;
h_formula_conj_h2 : h_formula;
h_formula_conj_pos : loc }

and h_formula_phase = { h_formula_phase_rd : h_formula;
h_formula_phase_rw : h_formula;
h_formula_phase_pos : loc }

and h_formula_data = {  h_formula_data_node : CP.spec_var;
                        h_formula_data_name : ident;
						h_formula_data_derv : bool;
                        h_formula_data_imm : ann;
                        h_formula_data_perm : cperm; (* option; *) (*LDK: permission*)
                        (*added to support fractional splitting of data nodes*)
                        h_formula_data_origins : ident list;
                        h_formula_data_original : bool;
                        h_formula_data_arguments : CP.spec_var list;
						h_formula_data_holes : int list; (* An Hoa : list of fields not to be considered for partial structures *) (*store positions*)
                        h_formula_data_label : formula_label option;
                        h_formula_data_remaining_branches :  (formula_label list) option;
                        h_formula_data_pruning_conditions :  (CP.b_formula * formula_label list ) list;
                        h_formula_data_pos : loc }

and h_formula_view = {  h_formula_view_node : CP.spec_var;
                        h_formula_view_name : ident;
                        h_formula_view_derv : bool;
                        h_formula_view_imm : ann;
                        h_formula_view_perm : cperm; (*LDK: permission*)
                        h_formula_view_arguments : CP.spec_var list;
                        h_formula_view_modes : mode list;
                        h_formula_view_coercible : bool;
                        (* if this view is generated by a coercion from another view c, 
                           then c is in h_formula_view_origins. Used to avoid loopy coercions *)
                        h_formula_view_origins : ident list;
                        h_formula_view_original : bool;
                        h_formula_view_lhs_case : bool; (* to allow LHS case analysis prior to unfolding and lemma *)
                        (* to allow LHS case analysis prior to unfolding and lemma *)
                        h_formula_view_unfold_num : int; (* to prevent infinite unfolding *)
                        (* h_formula_view_orig_fold_num : int; (\* depth of originality for folding *\) *)
                        (* used to indicate a specialised view *)
                        h_formula_view_remaining_branches :  (formula_label list) option;
                        h_formula_view_pruning_conditions :  (CP.b_formula * formula_label list ) list;
                        h_formula_view_label : formula_label option;
                        h_formula_view_pos : loc }
and approx_disj = 
  | ApproxBase of approx_disj_base
  | ApproxOr of approx_disj_or

and approx_formula =
  | ApproxCon of approx_disj
  | ApproxAnd of approx_formula_and
	    
and approx_disj_base = { approx_disj_base_vars : CP.spec_var list;
(* list of variables that _must_ point to objects *)
approx_disj_base_formula : CP.formula }
	
and approx_disj_or = { approx_disj_or_d1 : approx_disj;
approx_disj_or_d2 : approx_disj }

and approx_formula_and = { approx_formula_and_a1 : approx_formula;
approx_formula_and_a2 : approx_formula }


let print_formula = ref(fun (c:formula) -> "printer not initialized")
let print_pure_f = ref(fun (c:CP.formula) -> "printer not initialized")
let print_formula_base = ref(fun (c:formula_base) -> "printer not initialized")
let print_h_formula = ref(fun (c:h_formula) -> "printer not initialized")
let print_h_formula_for_spec = ref(fun (c:h_formula) -> "printer not initialized")
let print_mix_f = ref(fun (c:MCP.mix_formula) -> "printer not initialized")
let print_mix_formula = print_mix_f
let print_ident_list = ref(fun (c:ident list) -> "printer not initialized")
let print_svl = ref(fun (c:CP.spec_var list) -> "printer not initialized")
let print_sv = ref(fun (c:CP.spec_var) -> "printer not initialized")
let print_struc_formula = ref(fun (c:struc_formula) -> "printer not initialized")
let print_flow_formula = ref(fun (c:flow_formula) -> "printer not initialized")
let print_spec_var = print_sv
let print_spec_var_list = print_svl
let print_infer_rel(l,r) = (!print_pure_f l)^" --> "^(!print_pure_f r)
let print_mem_formula = ref (fun (c:mem_formula) -> "printer has not been initialized")

module Exp_Heap =
struct 
  type e = h_formula
  let comb x y = Star 
    { h_formula_star_h1 = x;
	  h_formula_star_h2 = y;
      h_formula_star_pos = no_pos
    }
  let string_of = !print_h_formula
end;;

module Exp_Spec =
struct 
  type e = struc_formula
  let comb x y = EOr 
    { formula_struc_or_f1 = x;
    formula_struc_or_f2 = y;
    formula_struc_or_pos = no_pos
    }
  let string_of = !print_struc_formula
end;;

module Label_Heap = LabelExpr(Lab_List)(Exp_Heap);;
module Label_Spec = LabelExpr(Lab2_List)(Exp_Spec);;


(* utility functions *)



let isLend(a : ann) : bool = 
  match a with
    | ConstAnn(Lend) -> true
    | _ -> false

and isMutable(a : ann) : bool = 
  match a with
    | ConstAnn(Mutable) -> true
    | _ -> false

and isImm(a : ann) : bool = 
  match a with
    | ConstAnn(Imm) -> true
    | _ -> false

let fv_ann (a:ann) = match a with
  | ConstAnn _ -> []
  | PolyAnn v -> [v]

let mkConstAnn i = match i with 
  | 0 -> ConstAnn Mutable
  | 1 -> ConstAnn Imm
  | 2 -> ConstAnn Lend
  | _ -> report_error no_pos "Const Ann is greater than 2"  

let mkPolyAnn v = PolyAnn v

(* generalized to data and view *)
let get_ptr_from_data h =
  match h with
    | DataNode f -> f.h_formula_data_node
    | ViewNode f -> f.h_formula_view_node
    | _ -> report_error no_pos "get_ptr_from_data : data expected" 

(*if is hrel: return true and its name
 if a node or a view: return false and its name
*)
let get_ptr_from_data_w_hrel h =
  match h with
    | DataNode f -> false,f.h_formula_data_node
    | ViewNode f -> false, f.h_formula_view_node
    | HRel (hp,_,_) -> true,hp
    | _ -> report_error no_pos "get_ptr_from_data : data expected" 

let print_path_trace = ref(fun (pt: path_trace) -> "printer not initialized")
let print_list_int = ref(fun (ll: int list) -> "printer not initialized")
(*--- 09.05.2000 *)
(* pretty printing for a spec_var list *)
let rec string_of_spec_var_list l = match l with 
  | []               -> ""
  | h::[]            -> string_of_spec_var h 
  | h::t             -> (string_of_spec_var h) ^ "," ^ (string_of_spec_var_list t)

and string_of_spec_var = function
  | CP.SpecVar (_, id, p) -> id ^ (match p with
    | Primed   -> "'"
    | Unprimed -> "")
(*09.05.2000 ---*)

let consistent_formula f : bool = 
  let rec helper f = match f with
    | Base {formula_base_pure = mf}
    | Exists {formula_exists_pure = mf} ->
          MCP.consistent_mix_formula mf
    | Or {formula_or_f1 = f1; formula_or_f2 =f2} ->
          (helper f1) && (helper f2)
  in helper f

let must_consistent_formula (s:string) (l:formula) : unit =
  if !consistency_checking then
    let b = consistent_formula l in
    if b then  print_endline ("\nSuccessfully Tested Consistency at "^s)
    else report_error no_pos ("ERROR at "^s^": formula inconsistent")

let extr_formula_base e = match e with
      {formula_base_heap = h;
      formula_base_pure = p; 
      formula_base_type = t;
      formula_base_flow = fl;
	  formula_base_and = a} -> (h,p,t,fl,a) 

let is_eq_node_name a b = (a=b)

let is_eq_data_name a b =
  match a,b with
    | {h_formula_data_name = c1;}, {h_formula_data_name = c2;}-> c1=c2

let is_eq_view_name a b =
  match a,b with
    | {h_formula_view_name = c1;}, {h_formula_view_name = c2;}-> c1=c2

let is_eq_view_name a b =
  Debug.no_2 "is_eq_view_name" (fun x->x) (fun x->x) string_of_bool (fun _ _ ->  is_eq_view_name a b) 
      a.h_formula_view_name b.h_formula_view_name

let is_eq_data_ann a b = (a = b)
let is_eq_view_ann a b =
  match a,b with
    | {h_formula_view_imm = c1;}, {h_formula_view_imm = c2;}-> c1=c2

let br_match br1 br2 = match br1,br2 with
      | None,None -> true
      | Some br1,Some br2 ->(Gen.BList.list_setequal_eq (=) br1 br2)
      | _ ->   Err.report_error { Err.error_loc = no_pos; Err.error_text ="mix of specialised and unspecialised view"}

let is_eq_view_spec a b =
  (is_eq_view_name a b) &&
  (match a,b with
    | {h_formula_view_remaining_branches = c1;}, {h_formula_view_remaining_branches = c2;}-> br_match c1 c2)

let is_eq_view_spec a b =
  Debug.no_2 "is_eq_view_spec" (fun x->x) (fun x->x) string_of_bool (fun _ _ ->  is_eq_view_spec a b) 
      a.h_formula_view_name b.h_formula_view_name

(* returns false if unsatisfiable *)
let is_sat_mem_formula (mf:mem_formula) : bool =
  let d = mf.mem_formula_mset in
  (CP.DisjSetSV.is_sat_dset d)

(* returns all the disjoint pairs from a mem formula *)
let generate_disj_pairs_from_memf (mf:mem_formula):(CP.spec_var * CP.spec_var) list  =
  let m = mf.mem_formula_mset in
  let rec helper l =
  match l with
    | h::r -> 
      if (r!=[]) then (List.fold_left (fun x y -> (h,y)::x) [] r) @ (helper r)
      else []
    | [] -> []
  in
  List.fold_left (fun x y -> x@(helper y)) [] m

let rec formula_of_heap h pos = mkBase h (MCP.mkMTrue pos) TypeTrue (mkTrueFlow ()) [] pos
and formula_of_heap_fl h fl pos = mkBase h (MCP.mkMTrue pos) TypeTrue fl [] pos

and struc_formula_of_heap h pos = EBase { 
	formula_struc_explicit_inst = [];	 
	formula_struc_implicit_inst = []; 
	formula_struc_exists = [];
	formula_struc_base = formula_of_heap h pos;
	formula_struc_continuation = None;
	formula_struc_pos = pos}

and struc_formula_of_formula f pos = EBase { 
	formula_struc_explicit_inst = [];	 
    formula_struc_implicit_inst = []; 
    formula_struc_exists = [];
	formula_struc_base = f;
	formula_struc_continuation = None;
	formula_struc_pos = pos}
  
and mkEOr f1 f2 pos = 
  if isConstETrue f1 || isConstETrue f2 then mkETrue (mkTrueFlow ()) pos
  else if isConstEFalse f1 then f2
  else if isConstEFalse f2 then f1
  else 	EOr ({formula_struc_or_f1 = f1; formula_struc_or_f2 = f2; formula_struc_or_pos = pos})

and mkEList l =
	if isConstETrue (EList l) then mkETrue (mkTrueFlow ()) no_pos 
	else if isConstEFalse (EList l) then mkEFalse (mkFalseFlow) no_pos
	else EList l
and mkTrueFlow () = 
  {formula_flow_interval = !top_flow_int; formula_flow_link = None;}
	  

and mkFalseFlow = {formula_flow_interval = false_flow_int; formula_flow_link = None;}

and mkNormalFlow () = { formula_flow_interval = !norm_flow_int; formula_flow_link = None;}

and mkErrorFlow () = { formula_flow_interval = !error_flow_int; formula_flow_link = None;}

and formula_of_mix_formula (p:MCP.mix_formula) (pos:loc) :formula= mkBase HEmp p TypeTrue (mkTrueFlow ()) [] pos

and formula_of_pure_formula (p:CP.formula) (pos:loc) :formula = 
  let mix_f = (*MCP.OnePF*) MCP.mix_of_pure p in
  formula_of_mix_formula mix_f pos 

and mkBase_simp (h : h_formula) (p : MCP.mix_formula) : formula=  mkBase_w_lbl h p TypeTrue (mkNormalFlow()) [] no_pos None

and mkEBase f ct pos = EBase {
      formula_struc_explicit_inst =[];
      formula_struc_implicit_inst =[];
      formula_struc_exists =[];
      formula_struc_base = f;
      formula_struc_continuation = ct;
      formula_struc_pos = pos;
  }

and mk_ebase_inferred_pre (h:h_formula) (p:CP.formula) ct = mkEBase (mkBase_simp h (MCP.mix_of_pure p)) ct no_pos 

and formula_of_pure_aux (p:CP.formula) (status:int) (pos:loc) :formula=
  let mp = if (status >0 ) then MCP.memoise_add_pure_N (MCP.mkMTrue pos) p 
  else  MCP.memoise_add_pure_P (MCP.mkMTrue pos) p  in
  mkBase HEmp mp TypeTrue (mkTrueFlow ()) [] pos

and formula_of_pure_P (p:CP.formula) (pos:loc) :formula= formula_of_pure_aux p (-1) pos
  
and formula_of_pure_N (p:CP.formula) (pos:loc) :formula= formula_of_pure_aux p 1 pos
  
(*and formula_of_pure_with_branches_aux p br status pos = 
  let mp = if status>0 then MCP.memoise_add_pure_N (MCP.mkMTrue pos) p
  else MCP.memoise_add_pure_P (MCP.mkMTrue pos) p in
  mkBase HTrue mp TypeTrue (mkTrueFlow ()) br [] pos

and formula_of_pure_with_branches_N p br pos = formula_of_pure_with_branches_aux p br 1 pos

and formula_of_pure_with_branches_P p br pos = formula_of_pure_with_branches_aux p br (-1) pos

and formula_of_mix_formula_with_branches p br pos = mkBase HTrue p TypeTrue (mkTrueFlow ()) br pos

and formula_of_pure_with_branches_fl_aux p br fl status pos = 
  let mp = if status>0 then MCP.memoise_add_pure_N (MCP.mkMTrue pos) p 
  else MCP.memoise_add_pure_P (MCP.mkMTrue pos) p in
  mkBase HTrue mp TypeTrue fl br [] pos

and formula_of_pure_with_branches_fl_N p br fl pos = formula_of_pure_with_branches_fl_aux p br fl 1 pos

and formula_of_pure_with_branches_fl_P p br fl pos = formula_of_pure_with_branches_fl_aux p br fl (-1) pos*)
  
and formula_of_mix_formula_with_fl (p:MCP.mix_formula) fl pos = mkBase HEmp p TypeTrue fl pos
and formula_of_base base = Base(base)

and data_of_h_formula h = match h with
  | DataNode d -> d
  | _ -> failwith ("data_of_h_formula: input is not a data node")

and isAnyConstFalse f = match f with
  | Exists ({formula_exists_heap = h;
    formula_exists_pure = p;
    formula_exists_flow = fl;})
  | Base ({formula_base_heap = h;
    formula_base_pure = p;
    formula_base_flow = fl;}) -> h = HFalse || MCP.isConstMFalse p||is_false_flow fl.formula_flow_interval
  | _ -> false


and isAllConstFalse f = match f with
  | Exists ({formula_exists_heap = h;
    formula_exists_pure = p;
    formula_exists_flow = fl;})
  | Base ({formula_base_heap = h;
    formula_base_pure = p;
    formula_base_flow = fl;}) -> (h = HFalse || MCP.isConstMFalse p)||(is_false_flow fl.formula_flow_interval)
  | _ -> false

and isConstDFalse f = 
  match f with
	| EBase b -> isAnyConstFalse b.formula_struc_base
    | EList x-> List.for_all (fun (_,c)-> isConstDFalse c) x
	| _ -> false

and isConstDTrue f = 
  match f with
	| EBase b -> (isStrictConstTrue b.formula_struc_base) &&(b.formula_struc_continuation==None)
    | EList x -> List.exists (fun (_,c)-> isConstDTrue c) x
	| _ -> false

and isConstETrue f = (*List.exists*) isConstDTrue f
          
and isConstEFalse f = (*List.for_all*) isConstDFalse f

(* TRUNG TODO: should change name to isConstEmpFormula ? *)
and isConstTrueFormula f =
    match f with
      | Base b -> (b.formula_base_heap==HEmp) &&
            (MCP.isConstMTrue b.formula_base_pure)
      | Exists _ -> false
      | Or b -> false

and isConstETrueSpecs f = match f with
	| EBase b 
    | EList ((_,EBase b)::[])-> isStrictConstTrue b.formula_struc_base && 
          (match b.formula_struc_continuation with
            | Some EAssume (_,f,_)-> isStrictConstTrue f
            | None -> true
            | _-> false)
	| _ -> false

(* TRUNG TODO: should change name to isStrictConstEmp_x ? *)
and isStrictConstTrue_x f = match f with
  | Exists ({ formula_exists_heap = HEmp;
    formula_exists_pure = p;
    formula_exists_flow = fl; })
  | Base ({formula_base_heap = HEmp;
    formula_base_pure = p;
    formula_base_flow = fl;}) -> 
        MCP.isConstMTrue p && is_top_flow fl.formula_flow_interval
	        (* don't need to care about formula_base_type  *)
  | _ -> false

and isStrictConstTrue (f:formula) = 
  Debug.no_1 "isStrictConstTrue" !print_formula string_of_bool isStrictConstTrue_x f

(* TRUNG TODO: should change name to isAnyConstEmp ? *)
and isAnyConstTrue f = match f with
  | Exists ({formula_exists_heap = HEmp;
    formula_exists_pure = p;
	formula_exists_flow = fl; })
  | Base ({formula_base_heap = HEmp;
	formula_base_pure = p;
	formula_base_flow = fl;}) -> 
        MCP.isConstMTrue p (* don't need to care about formula_base_type  *)
  | _ -> false

and is_complex_heap (h : h_formula) : bool = match h with
  | HFalse | HEmp-> false
  | _ -> true

and is_coercible_x (h : h_formula) : bool = match h with
  | ViewNode ({h_formula_view_coercible = c}) -> c
  | DataNode _ -> true (*LDK: assume that all data nodes are coercible*)
  | _ -> false

and is_coercible (h : h_formula) : bool =
  Debug.no_1 "is_coercible" !print_h_formula string_of_bool is_coercible_x h 


(*
  for immutability 
*)
and drop_read_phase (f : h_formula) : h_formula = match f with
  | Phase(f1) -> f1.h_formula_phase_rw
  | _ -> f

and drop_read_phase1 (f : h_formula) p : h_formula = match f with
  | Phase(f1) -> 
        if contains_spec_var f1.h_formula_phase_rw p 
        then f1.h_formula_phase_rw
        else f
  | Star({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos;}) -> 
        let new_f1 = drop_read_phase1 h1 p in
        let new_f2 = drop_read_phase1 h2 p in
	    mkStarH new_f1 new_f2 pos
  | Conj({h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;
	h_formula_conj_pos = pos;}) -> 
        let new_f1 = drop_read_phase1 h1 p in
        let new_f2 = drop_read_phase1 h2 p in
	    mkConjH new_f1 new_f2 pos
  | _ -> f

and contains_spec_var (f : h_formula) p : bool = match f with
  | DataNode (h1) -> Cpure.eq_spec_var p h1.h_formula_data_node
  | ViewNode (h1) -> Cpure.eq_spec_var p h1.h_formula_view_node
  | Phase ({h_formula_phase_rd = h1;
	h_formula_phase_rw = h2;}) ->
        (contains_spec_var h1 p) or (contains_spec_var h2 p)
  | Conj ({h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;}) ->
        (contains_spec_var h1 p) or (contains_spec_var h2 p)
  | Star ({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;}) ->
        (contains_spec_var h1 p) or (contains_spec_var h2 p)
  | _ -> false



(*
  perform simplification incrementally
*)

and mkAndType f1 f2 = match f1 with
  | TypeTrue -> f2
  | TypeFalse -> TypeFalse
  | _ -> begin
	  match f2 with
		| TypeTrue -> f1
		| TypeFalse -> TypeFalse
		| _ -> TypeAnd ({t_formula_and_f1 = f1; t_formula_and_f2 = f2})
	end
        
(*assume none is invalid*)
(* and non_overlapping (n1,n2) (p1,p2) : bool = n1>p2 || p1>n2 *)
and non_overlapping t1 t2 : bool = not(is_overlap_flow t1 t2)
  
and overlapping n p : bool = is_overlap_flow n p

(* and intersect_flow (n1,n2)(p1,p2) : (int*int)= ((if (n1<p1) then p1 else n1),(if (n2<p2) then n2 else p2)) *)

(* and is_false_flow (p1,p2) :bool = (p2==0)&&(p1==0) || p1>p2 *)
and is_top_flow p :bool = (equal_flow_interval !top_flow_int p)


and is_sleek_mustbug_flow p: bool = (equal_flow_interval !error_flow_int p)
and is_sleek_mustbug_flow_ff ff: bool = is_sleek_mustbug_flow ff.formula_flow_interval

(* and equal_flow_interval (t1:nflow) (t2:nflow) : bool =  *)
(*   is_eq_flow t1 t2 *)

and equal_flow_interval t1 t2 : bool = 
  is_eq_flow t1 t2

(*first subsumes the second*)
(* and subsume_flow_x (n1,n2)(p1,p2) : bool = *)
(* if (is_false_flow (p1,p2)) then true else (n1<=p1)&&(p2<=n2) *)

(* and subsume_flow (t1:nflow) (t2:nflow) : bool = *)
(*   is_subsume_flow t1 t2 *)

and subsume_flow t1 t2 : bool =
  is_subsume_flow t1 t2

(* and subsume_flow n p : bool =  *)
(*   let pr1 = pr_pair string_of_int  string_of_int in *)
(*   Debug.no_2 "subsume_flow" pr1 pr1 string_of_bool subsume_flow_x n p  *)

(* and overlap_flow t1 t2 : bool = (subsume_flow t1 t2) || (subsume_flow t2 t1) *)


and overlap_flow t1 t2 : bool = is_overlap_flow t1 t2

and subtract_flow_list t1 t2  (* : (nflow list) *) = 
   subtract_flow_l t1 t2
  (* if n1<p1 then (n1,p1-1)::(subtract_flow_list (p1,n2) (p1,p2)) *)
  (* else if n2>p2 then [(p2+1,n2)] *)
  (* else [] *)

and disjoint_flow t1 t2 : bool = not(overlap_flow t1 t2) 

and subsume_flow_f t1 f :bool = subsume_flow t1 f.formula_flow_interval

and subsume_flow_ff f1 f2 :bool = subsume_flow f1.formula_flow_interval f2.formula_flow_interval

(* and subsume_flow_ff i f1 f2 :bool =  *)
(*   let pr = !print_flow_formula in *)
(*   Debug.no_2_num i "subsume_flow_ff" pr pr string_of_bool subsume_flow_ff_x f1 f2 *)

and overlap_flow_ff f1 f2 :bool = overlap_flow f1.formula_flow_interval f2.formula_flow_interval

(* and overlap_flow_ff f1 f2 :bool =  *)
(*   let pr = !print_flow_formula in *)
(*   Debug.no_2 "subsume_flow_ff" pr pr string_of_bool overlap_flow_ff_x f1 f2 *)

and get_flow_from_stack c l pos = 
  try
	let r = List.find (fun h-> ((String.compare h.formula_store_name c)==0)) l in
	r.formula_store_value
  with Not_found -> Err.report_error { 
	  Err.error_loc = pos;
	  Err.error_text = "the flow var stack \n "^
		  (String.concat " " (List.map (fun h-> (h.formula_store_name^"= "^
			  (string_of_flow (h.formula_store_value.formula_flow_interval) ^" "))) l))^
		  "\n does not contain "^c
   }

and set_flow_in_formula_override (n:flow_formula) (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow = n}
  | Exists b-> Exists {b with formula_exists_flow = n}
  | Or b-> Or {formula_or_f1 = set_flow_in_formula_override n b.formula_or_f1;
	formula_or_f2 = set_flow_in_formula_override n b.formula_or_f2;
	formula_or_pos = b.formula_or_pos}
		
and set_flow_in_formula (n:flow_formula) (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow = if (subsume_flow_f !norm_flow_int b.formula_base_flow) then n else b.formula_base_flow}
  | Exists b-> Exists {b with formula_exists_flow = if (subsume_flow_f !norm_flow_int b.formula_exists_flow) then n else b.formula_exists_flow}
  | Or b-> Or {formula_or_f1 = set_flow_in_formula_override n b.formula_or_f1;
	formula_or_f2 = set_flow_in_formula_override n b.formula_or_f2;
	formula_or_pos = b.formula_or_pos}

		
and set_flow_to_link_f flow_store f pos = match f with
  | Base b-> Base {b with formula_base_flow = 
			if (equal_flow_interval b.formula_base_flow.formula_flow_interval false_flow_int) then b.formula_base_flow
			else
			  if (subsume_flow !norm_flow_int b.formula_base_flow.formula_flow_interval ) then
				match b.formula_base_flow.formula_flow_link with
				  | None -> Error.report_error { Error.error_loc = pos;Error.error_text = "simple flow where link required"}
				  | Some v -> get_flow_from_stack v flow_store pos
			  else b.formula_base_flow}
  | Exists b-> Exists {b with formula_exists_flow = 
			if (equal_flow_interval b.formula_exists_flow.formula_flow_interval false_flow_int) then b.formula_exists_flow
			else
			  if (subsume_flow !norm_flow_int b.formula_exists_flow.formula_flow_interval ) then 
				match b.formula_exists_flow.formula_flow_link with
				  | None -> Error.report_error { Error.error_loc = pos;Error.error_text = "simple flow where link required"}
				  | Some v -> get_flow_from_stack v flow_store pos
			  else b.formula_exists_flow}
  | Or b-> Or {formula_or_f1 = set_flow_to_link_f flow_store b.formula_or_f1 pos;
	formula_or_f2 = set_flow_to_link_f flow_store b.formula_or_f2 pos;
	formula_or_pos = b.formula_or_pos}


and formula_is_eq_flow  (f:formula) ff   : bool =
  let is_eq f = equal_flow_interval ff (f.formula_flow_interval) in
  match f with
  | Base b-> is_eq b.formula_base_flow
  | Exists b-> is_eq b.formula_exists_flow
  | Or b ->  (formula_is_eq_flow b.formula_or_f1 ff) &&  (formula_is_eq_flow b.formula_or_f2 ff)

and struc_formula_is_eq_flow (f:struc_formula) ff : bool = match f with
    | EOr b -> (struc_formula_is_eq_flow b.formula_struc_or_f1 ff)&& (struc_formula_is_eq_flow b.formula_struc_or_f2 ff)
    | EList l ->List.for_all (fun (_,c)-> struc_formula_is_eq_flow c ff)l 
	| EBase b -> (formula_is_eq_flow b.formula_struc_base ff) && (match b.formula_struc_continuation with Some f -> struc_formula_is_eq_flow f ff | None-> true)
	| ECase b -> List.for_all (fun (_,c) -> struc_formula_is_eq_flow c ff) b.formula_case_branches 
	| EAssume (x,b,y) -> formula_is_eq_flow b ff
    | EInfer b -> struc_formula_is_eq_flow b.formula_inf_continuation ff

and formula_subst_flow (f:formula) ff : formula =
  match f with
  | Base b-> Base {b with formula_base_flow = ff} 
  | Exists b-> Exists{b with formula_exists_flow = ff}
  | Or b -> Or {b with formula_or_f1 = formula_subst_flow b.formula_or_f1 ff;
	formula_or_f2 = formula_subst_flow b.formula_or_f2 ff}

and struc_formula_subst_flow (f:struc_formula) ff : struc_formula = match f with
    | EOr b -> EOr {b with 
                      formula_struc_or_f1 = struc_formula_subst_flow b.formula_struc_or_f1 ff; 
                      formula_struc_or_f2 = struc_formula_subst_flow b.formula_struc_or_f2 ff;
                   }
    | EList l -> EList (map_l_snd (fun c-> struc_formula_subst_flow c ff) l)
	| EBase b -> EBase {b with 
                     formula_struc_base = formula_subst_flow b.formula_struc_base ff ; 
		             formula_struc_continuation = map_opt (fun c-> struc_formula_subst_flow c ff) b.formula_struc_continuation
                       }
	| ECase b -> ECase {b with formula_case_branches = 
              List.map (fun (c1,c2) -> (c1,(struc_formula_subst_flow c2 ff))) b.formula_case_branches;}
	| EAssume (x,b,y) -> EAssume (x,(formula_subst_flow b ff),y)
    | EInfer b -> EInfer {b with formula_inf_continuation = struc_formula_subst_flow b.formula_inf_continuation ff} 

and split_one_formula (f : one_formula) = f.formula_heap, f.formula_pure,  f.formula_thread, f.formula_label, f.formula_pos

and one_formula_of_formula (f : formula) (tid: CP.spec_var): one_formula =
  (match f with
    | Base {formula_base_heap = h;
        formula_base_pure = p;
        formula_base_label = lbl;
        formula_base_pos = pos;
       } ->
        mkOneFormula h p tid lbl pos
    | Exists {
        formula_exists_heap = h;
        formula_exists_pure = p;
        formula_exists_label = lbl;
        formula_exists_pos = pos;
       } ->
        mkOneFormula h p tid lbl pos
    | _ -> Error.report_error {Error.error_loc = no_pos; Error.error_text = "one_formula_of_formula: disjunctive form"} )

and add_formula_and (a: one_formula list) (f:formula) : formula =
  match f with
    | Or o -> mkOr (add_formula_and a o.formula_or_f1) (add_formula_and a o.formula_or_f2) o.formula_or_pos
    | Base b -> Base { b with formula_base_and = b.formula_base_and@a}
    | Exists e -> Exists {e with formula_exists_and = e.formula_exists_and@a}

and replace_formula_and (a: one_formula list) (f:formula) : formula =
  match f with
    | Or o -> mkOr (add_formula_and a o.formula_or_f1) (add_formula_and a o.formula_or_f2) o.formula_or_pos
    | Base b -> Base { b with formula_base_and = a}
    | Exists e -> Exists {e with formula_exists_and = a}


and formula_of_one_formula (f : one_formula) : formula =
  Base {formula_base_heap = f.formula_heap;
        formula_base_pure = f.formula_pure;
        formula_base_type = TypeTrue;
        formula_base_and = [];
        formula_base_flow = mkTrueFlow ();
        formula_base_label = f.formula_label;
        formula_base_pos = f.formula_pos;
       }

and formula_and_of_formula (f:formula) : one_formula list = 
  match f with
  | Base b-> b.formula_base_and
  | Exists b-> b.formula_exists_and
  | Or b ->
      (*need normalization or error*)
	  Err.report_error { Err.error_loc = no_pos;
		                 Err.error_text = "formula_and_of_formula: disjunctive formula"}

and flow_formula_of_formula (f:formula) (*pos*) : flow_formula = 
  match f with
  | Base b-> b.formula_base_flow
  | Exists b-> b.formula_exists_flow
  | Or b -> 
		let fl1 = flow_formula_of_formula b.formula_or_f1 in
		let fl2 = flow_formula_of_formula b.formula_or_f2 in
		if (equal_flow_interval fl1.formula_flow_interval fl2.formula_flow_interval) then fl1
		else Err.report_error { Err.error_loc = no_pos;
		Err.error_text = "flow_formula_of_formula: disjunctive formula"}

and flow_formula_of_struc_formula (f:struc_formula):flow_formula=
  let compare_flow ffi1 ffi2 =
    if (equal_flow_interval ffi1.formula_flow_interval ffi2.formula_flow_interval) then ffi1
	else Err.report_error { Err.error_loc = no_pos;
		                    Err.error_text = "flow_formula_of_struc_formula: need to handle here"}
  in
  let fold_left_compare_flows flow_list=
    match flow_list with
      | [] -> report_error no_pos "Cformula.flow_formula_of_struc_formula"
      | fl::[] -> fl
      | _ ->  List.fold_left compare_flow (List.hd flow_list) (List.tl flow_list)
  in
  let rec helper (f:struc_formula) = match f with
	| EOr b -> compare_flow (helper b.formula_struc_or_f1) (helper b.formula_struc_or_f2)
    | EList b -> fold_left_compare_flows (List.map (fun (_,c)-> helper c) b)
    | EBase b -> flow_formula_of_formula b.formula_struc_base
	| ECase b -> fold_left_compare_flows (List.map (fun (_,c)-> helper c) b.formula_case_branches)
	| EAssume (x,b,y) -> flow_formula_of_formula b
    | EInfer b -> helper b.formula_inf_continuation
  in
   helper f

and substitute_flow_in_f to_flow from_flow (f:formula):formula = 
  Debug.no_3 "substitute_flow_in_f" string_of_flow string_of_flow !print_formula !print_formula (fun _ _ _ -> substitute_flow_in_f_x to_flow from_flow f) to_flow from_flow f

and substitute_flow_in_f_x to_flow from_flow (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow = 
		    if (equal_flow_interval from_flow b.formula_base_flow.formula_flow_interval) then 
		      {formula_flow_interval = to_flow; formula_flow_link = b.formula_base_flow.formula_flow_link}
		    else b.formula_base_flow;}
  | Exists b-> Exists{b with formula_exists_flow = 
		    if (equal_flow_interval from_flow b.formula_exists_flow.formula_flow_interval) then 
		      {formula_flow_interval = to_flow; formula_flow_link = b.formula_exists_flow.formula_flow_link}
		    else b.formula_exists_flow;}	
  | Or b-> Or {formula_or_f1 = substitute_flow_in_f_x to_flow from_flow b.formula_or_f1;
	formula_or_f2 = substitute_flow_in_f_x to_flow from_flow b.formula_or_f2;
	formula_or_pos = b.formula_or_pos}

and substitute_flow_into_f to_flow (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow = 
		    {formula_flow_interval = to_flow; formula_flow_link = b.formula_base_flow.formula_flow_link}}
  | Exists b-> Exists{b with formula_exists_flow = 
		    {formula_flow_interval = to_flow; formula_flow_link = b.formula_exists_flow.formula_flow_link}}
  | Or b-> Or {formula_or_f1 = substitute_flow_into_f to_flow b.formula_or_f1;
	formula_or_f2 = substitute_flow_into_f to_flow b.formula_or_f2;
	formula_or_pos = b.formula_or_pos}
		
and substitute_flow_in_struc_f to_flow from_flow (f:struc_formula):struc_formula = match f with
    | EOr b -> EOr {b with 
         formula_struc_or_f1 = substitute_flow_in_struc_f to_flow from_flow b.formula_struc_or_f1;
         formula_struc_or_f2 = substitute_flow_in_struc_f to_flow from_flow b.formula_struc_or_f2; }
    | EList b -> EList (map_l_snd (substitute_flow_in_struc_f to_flow from_flow) b)
	| EBase b -> EBase {b with formula_struc_base = substitute_flow_in_f to_flow from_flow b.formula_struc_base ; 
		  formula_struc_continuation = map_opt (substitute_flow_in_struc_f to_flow from_flow)  b.formula_struc_continuation}
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2) -> (c1,(substitute_flow_in_struc_f to_flow from_flow  c2))) b.formula_case_branches;}
	| EAssume (x,b,y) -> EAssume (x,(substitute_flow_in_f to_flow from_flow  b),y)
 | EInfer b -> EInfer {b with formula_inf_continuation =substitute_flow_in_struc_f to_flow from_flow b.formula_inf_continuation}

and mkAndFlow (fl1:flow_formula) (fl2:flow_formula) flow_tr :flow_formula = 
  let pr = !print_flow_formula in
  let pr2 x = match x with Flow_combine -> "Combine" | Flow_replace -> "Replace" in
  Debug.no_3 "mkAndFlow" pr pr pr2 pr (fun _ _ _ -> mkAndFlow_x fl1 fl2 flow_tr) fl1 fl2 flow_tr

(*this is used for adding formulas, links will be ignored since the only place where links can appear is in the context, the first one will be kept*)
and mkAndFlow_x (fl1:flow_formula) (fl2:flow_formula) flow_tr :flow_formula = 
  let int1 = fl1.formula_flow_interval in
  let int2 = fl2.formula_flow_interval in
  let r = if (is_top_flow int1) then fl2
  else if (is_top_flow int2) then fl1
  else 
    match flow_tr with
	| Flow_replace ->
		  {	formula_flow_interval = int2;
		  formula_flow_link = match (fl1.formula_flow_link,fl2.formula_flow_link)with
			| None,None -> None
			| Some s,None-> Some s
			| None, Some s -> Some s
			| Some _, Some s -> Some s
			(* | _ ->  Err.report_error { Err.error_loc = no_pos; Err.error_text = "mkAndFlow: cannot and two flows with two links"} *)
                  ;}
	| Flow_combine ->
		  if (overlapping int1 int2) then 
			{	formula_flow_interval = intersect_flow int1 int2;
			formula_flow_link = match (fl1.formula_flow_link,fl2.formula_flow_link)with
			  | None,None -> None
			  | Some s,None-> Some s
			  | None, Some s -> Some s
			  | Some s1, Some s2 -> Some (s1^"AND"^s2)
			  (* | _ ->  Err.report_error { Err.error_loc = no_pos; Err.error_text = "mkAndFlow: cannot and two flows with two links"} *)
                    ;}
		  else {formula_flow_interval = false_flow_int; formula_flow_link = None} in
	r

and get_case_guard_list lbl (lst:(Cpure.b_formula * formula_label list) list) :  CP.b_formula list= 
  List.fold_left (fun a (cond,lbl_lst) -> if (List.mem lbl lbl_lst) then cond::a else a) [] lst

(* TRUNG TODO: should change name to mkEmp_b ? *)
and mkTrue_b (flowt:flow_formula) pos = {
		formula_base_heap = HEmp; 
		formula_base_pure = MCP.mkMTrue pos; 
		formula_base_type = TypeTrue; 
formula_base_and = [];
		formula_base_flow = flowt (*(mkTrueFlow ())*);
		formula_base_label = None;
		formula_base_pos = pos}
	  
and mkTrue_b_nf pos = mkTrue_b (mkTrueFlow ()) pos
	  
and mkTrue (flowt: flow_formula) pos = Base (mkTrue_b flowt pos)

and mkTrue_nf pos = Base (mkTrue_b_nf pos)

and mkFalse_nf pos = mkFalse (mkTrueFlow ()) pos

and mkFalse (flowt: flow_formula) pos = Base ({
		formula_base_heap = HFalse; 
		formula_base_pure = MCP.mkMFalse pos; 
		formula_base_type = TypeFalse;
formula_base_and = [];
		formula_base_flow = flowt (*mkFalseFlow*); (*Cpure.flow_eqs any_flow pos;*)
		formula_base_label = None;
		formula_base_pos = pos})
  
and mkEFalse flowt pos = EBase({
	formula_struc_explicit_inst = [];
	formula_struc_implicit_inst = [];
	formula_struc_exists = [];
	formula_struc_base = mkFalse flowt pos;
	formula_struc_continuation = None;
	formula_struc_pos = pos})

and mkETrue flowt pos = EBase({
	formula_struc_explicit_inst = [];
	formula_struc_implicit_inst = [];
	formula_struc_exists = [];
	formula_struc_base = mkTrue flowt pos;
	formula_struc_continuation = None;
	formula_struc_pos = pos})
  
and mkOr f1 f2 pos =
  let rec liniarize_or c = match c with
	| Or f -> 
		  let p11,p12,p13 = liniarize_or f.formula_or_f1 in
		  let p21,p22,p23 = liniarize_or f.formula_or_f2 in
		  (p11@p21, p12@p22, p13@p23)
	| Exists _ -> ([],[],[c]) 
	| Base f -> 
		  if (isAnyConstFalse c) then ([],[c],[])
		  else if (isAnyConstTrue c) then ([c],[],[])
		  else ([],[],[c]) in
  if isStrictConstTrue f1 || isStrictConstTrue f2 then
	mkTrue (mkTrueFlow ()) pos
  else if isAnyConstFalse f1 then f2
  else if isAnyConstFalse f2 then f1
  else 	
	Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos})

and mkBase_w_lbl (h : h_formula) (p : MCP.mix_formula) (t : t_formula) (fl : flow_formula) (a : one_formula list)(pos : loc) lbl: formula= 
  if MCP.isConstMFalse p || h = HFalse || (is_false_flow fl.formula_flow_interval)  then  mkFalse fl pos
  else 
	Base ({formula_base_heap = h; 
	formula_base_pure = p; 
	formula_base_type = t;
	formula_base_flow = fl;
    formula_base_and = a;
    formula_base_label = lbl;
	formula_base_pos = pos})
and mkBase (h : h_formula) (p : MCP.mix_formula) (t : t_formula) (fl : flow_formula) (a: one_formula list)(pos : loc) : formula= 
  mkBase_w_lbl h p t fl a pos None

and mkOneFormula (h : h_formula) (p : MCP.mix_formula) (tid : CP.spec_var) lbl (pos : loc) : one_formula= 
  {formula_heap = h;
   formula_pure = p;
   formula_thread = tid;
   formula_ref_vars = [];
   formula_label = lbl;
   formula_pos = pos;
  }

and mkStarH (f1 : h_formula) (f2 : h_formula) (pos : loc) = match f1 with
  | HFalse -> HFalse
  | HEmp -> f2
  | _ -> match f2 with
    | HFalse -> HFalse
    | HEmp -> f1
    | _ -> if (f1 = HTrue) && (f2 = HTrue) then HTrue 
           else Star { h_formula_star_h1 = f1;
                       h_formula_star_h2 = f2;
                       h_formula_star_pos = pos }

and mkConjH (f1 : h_formula) (f2 : h_formula) (pos : loc) = 
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else Conj ({h_formula_conj_h1 = f1; 
              h_formula_conj_h2 = f2; 
              h_formula_conj_pos = pos})

and mkPhaseH (f1 : h_formula) (f2 : h_formula) (pos : loc) = 
  match f1 with
    | HFalse -> HFalse
    | _ -> match f2 with
        | HFalse -> HFalse
        | _ -> Phase ({h_formula_phase_rd = f1; 
                       h_formula_phase_rw = f2; 
                       h_formula_phase_pos = pos})

and is_simple_formula (f:formula) =
  let h, _, _, _, _ = split_components f in
  match h with
    | HTrue | HFalse 
    | HEmp
    | DataNode _ -> true
    | ViewNode _ -> true
    | _ -> false

(*TO CHECK: formula_*_and *)
and fv_simple_formula (f:formula) = 
  let h, _, _, _, _ = split_components f in
  match h with
    | HTrue -> []                       (*TRUNG TODO: should be [perm_of_htrue]*)
    | HFalse | HEmp -> []
    | DataNode h -> 
        let perm = h.h_formula_data_perm in
        let perm_vars = fv_cperm perm in
        let ann_vars = fv_ann (h.h_formula_data_imm)  in
        perm_vars@ann_vars@(h.h_formula_data_node::h.h_formula_data_arguments)
    | ViewNode h -> 
        let perm = h.h_formula_view_perm in
        let perm_vars = fv_cperm perm in
        let ann_vars = fv_ann (h.h_formula_view_imm)  in
        perm_vars@ann_vars@(h.h_formula_view_node::h.h_formula_view_arguments)
    | _ -> []

(*LDK: don't count perm var as free vars in a coercion*)
and fv_simple_formula_coerc (f:formula) = 
  let h, _, _, _, _ = split_components f in
  match h with
    | HTrue | HFalse | HEmp -> []
    | DataNode h ->  h.h_formula_data_node::h.h_formula_data_arguments
    | ViewNode h ->  h.h_formula_view_node::h.h_formula_view_arguments
    | _ -> []
and mkStar (f1 : formula) (f2 : formula) flow_tr (pos : loc) =
  let h1, p1, fl1, t1, a1 = split_components f1 in
  let h2, p2, fl2, t2, a2 = split_components f2 in
  let h = mkStarH h1 h2 pos in
  let p = MCP.merge_mems p1 p2 true in
  let t = mkAndType t1 t2 in
  let fl = mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*assuming merging a1 and a2*)
  mkBase h p t fl a pos (*TO CHECK: how about a1,a2: DONE*)

and combine_and_pure (f1:formula)(p:MCP.mix_formula)(f2:MCP.mix_formula):MCP.mix_formula*bool = 
  if (isAnyConstFalse f1) then (MCP.mkMFalse no_pos,false)
  else if (isAnyConstTrue f1) then (f2,true)
  else 
    let r = Gen.Profiling.no_1 "6_combine_mm" (MCP.merge_mems p f2) true in
    if (MCP.isConstMFalse r) then (r,false)
    else if (MCP.isConstMTrue r) then (r,false)
    else (r,true)     

and sintactic_search (f:formula)(p:Cpure.formula):bool = match f with
  | Or b-> false		
  | Base _					
  | Exists _-> 
		let _, pl, _,_, _ = split_components f in	
		(MCP.memo_is_member_pure p pl)

and mkStar_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
  Debug.no_2 "mkstar_combine"
      (!print_formula)
      (!print_formula)
      (!print_formula)
      (fun f1 f2 -> mkStar_combine_x f1 f2 flow_tr pos) f1 f2 
	  
and mkStar_combine_x (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
  let h1, p1, fl1, t1, a1 = split_components f1 in
  let h2, p2, fl2, t2, a2 = split_components f2 in

  (* i assume that at least one of the two formulae has only 1 phase *)
  let h = 
    if not(contains_phase h1) then
      mkStarH h1 h2 pos
    else
      if not(contains_phase h2) then
	    mkStarH h2 h1 pos
      else
	    report_error no_pos "[cformula.ml, mkstar_combine]: at least one of the formulae combined should not contain phases"
  in
  (* let h = mkStarH h1 h2 pos in *)
  let p,_ = combine_and_pure f1 p1 p2 in
  let t = mkAndType t1 t2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*combine a1 and a2: assuming merging a1 and a2*)
  mkBase h p t fl a pos (*TO CHECK: how about a1,a2: DONE*)

and contains_phase (f : h_formula) : bool =  match f with
  | DataNode (h1) -> false
  | ViewNode (h1) -> false 
  | Conj({h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;
	h_formula_conj_pos = pos})
  | Star({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos}) -> (contains_phase h1) or (contains_phase h2)
  | Phase({h_formula_phase_rd = h1;
	h_formula_phase_rw = h2;
	h_formula_phase_pos = pos}) -> true
  | _ -> false

	  
and mkConj_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
  let h1, p1, fl1, t1, a1 = split_components f1 in
  let h2, p2, fl2, t2, a2 = split_components f2 in
  let h = mkConjH h1 h2 pos in
  let p,_ = combine_and_pure f1 p1 p2 in
  let t = mkAndType t1 t2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*assume merging a1 and a2*)
  mkBase h p t fl a pos (*TO CHECK: how about a1,a2: DONE*)
	  
and mkPhase_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
  let h1, p1, fl1, t1, a1 = split_components f1 in
  let h2, p2, fl2, t2, a2 = split_components f2 in
  let h = mkPhaseH h1 h2 pos in
  let p,_ = combine_and_pure f1 p1 p2 in
  let t = mkAndType t1 t2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*assume merging a1 and a2*)
  mkBase h p t fl a pos (*TO CHECK: how about a1,a2: DONE*)
      
and mkAnd_pure (f1 : formula) (p2 : MCP.mix_formula) (pos : loc):formula = 
  if (isAnyConstFalse f1) then f1
  else 
	let h1, p1, fl1, t1, a1 = split_components f1 in		
    if (MCP.isConstMTrue p1) then mkBase h1 p2 t1 fl1 a1 pos
	else 
      mkBase h1 (MCP.merge_mems p1 p2 true) t1 fl1 a1 pos

          
and mkExists_w_lbl (svs : CP.spec_var list) (h : h_formula) (p : MCP.mix_formula) (t : t_formula) (fl:flow_formula) a (pos : loc) lbl=
  let tmp_b = {formula_base_heap = h;
  formula_base_pure = p;
  formula_base_type = t;
  formula_base_flow = fl;
  formula_base_and = a;
  formula_base_label = lbl;
  formula_base_pos = pos} in
  let fvars = fv (Base tmp_b) in
  let qvars = Gen.BList.intersect_eq (=) svs fvars in (* used only these for the quantified formula *)
  if Gen.is_empty qvars then Base tmp_b 
  else
	Exists ({formula_exists_qvars = qvars; 
	formula_exists_heap =  h; 
	formula_exists_pure = p;
	formula_exists_type = t;
    formula_exists_and = a;
	formula_exists_flow = fl;
    formula_exists_label = lbl;
	formula_exists_pos = pos})

and is_empty_heap (h : h_formula) = match h with
  | HEmp -> true
  | _ -> false

and mkExists (svs : CP.spec_var list) (h : h_formula) (p : MCP.mix_formula) (t : t_formula) (fl:flow_formula) a (pos : loc) = 
  mkExists_w_lbl svs h p t fl a pos None

and is_view (h : h_formula) = match h with
  | ViewNode _ -> true
  | _ -> false

and is_data (h : h_formula) = match h with
  | DataNode _ -> true
  | _ -> false

and is_hformula_contain_htrue (h: h_formula) : bool =
  match h with
  | Star { h_formula_star_h1 = h1;
           h_formula_star_h2 = h2; } -> (is_hformula_contain_htrue h1) || (is_hformula_contain_htrue h2)
  | Conj { h_formula_conj_h1 = h1;
           h_formula_conj_h2 = h2; } -> (is_hformula_contain_htrue h1) || (is_hformula_contain_htrue h2)
  | Phase { h_formula_phase_rd = h1;
            h_formula_phase_rw = h2; } -> (is_hformula_contain_htrue h1) || (is_hformula_contain_htrue h2)
  | HTrue -> true
  | HRel _
  | DataNode _
  | ViewNode _
  | Hole _
  | HFalse
  | HEmp -> false

and is_formula_contain_htrue (h: formula) : bool =
  match h with
  | Base { formula_base_heap = h1; } -> is_hformula_contain_htrue h1
  | Exists { formula_exists_heap = h1; } -> is_hformula_contain_htrue h1
  | Or { formula_or_f1 = f1; 
         formula_or_f2 = f2 } -> (is_formula_contain_htrue f1) || (is_formula_contain_htrue f2)

and get_node_name (h : h_formula) = match h with
  | ViewNode ({h_formula_view_name = c}) 
  | DataNode ({h_formula_data_name = c}) -> c
  | _ -> failwith ("get_node_name: invalid argument")

and get_node_perm (h : h_formula) = match h with
  | ViewNode ({h_formula_view_perm = c}) 
  | DataNode ({h_formula_data_perm = c}) -> c
  | _ -> failwith ("get_node_perm: invalid argument")

and set_node_perm (h : h_formula) p= match h with
  | ViewNode b -> ViewNode {b with h_formula_view_perm = p}
  | DataNode b -> DataNode {b with h_formula_data_perm = p}
  | _ -> failwith ("set_node_perm: invalid argument")
  
and get_node_args (h : h_formula) = match h with
  | ViewNode ({h_formula_view_arguments = c}) 
  | DataNode ({h_formula_data_arguments = c}) -> c
  | _ -> failwith ("get_node_args: invalid argument")
  
and get_node_label (h : h_formula) = match h with
  | ViewNode ({h_formula_view_label = c}) 
  | DataNode ({h_formula_data_label = c}) -> c
  | _ -> failwith ("get_node_args: invalid argument")
  
and get_node_var (h : h_formula) = match h with
  | ViewNode ({h_formula_view_node = c}) 
  | DataNode ({h_formula_data_node = c}) -> c
  | _ -> failwith ("get_node_var: invalid argument")
  
and set_node_var newc (h : h_formula) = match h with
  | ViewNode w -> ViewNode {w with h_formula_view_node = newc;}
  | DataNode w -> DataNode {w with h_formula_data_node = newc;}
  | _ -> failwith ("set_node_var: invalid argument")

and get_node_imm (h : h_formula) = match h with
  | ViewNode ({h_formula_view_imm = imm}) 
  | DataNode ({h_formula_data_imm = imm}) -> imm
  | _ -> failwith ("get_node_imm: invalid argument")

and get_view_origins (h : h_formula) = match h with
  | ViewNode ({h_formula_view_origins = origs}) -> origs
  | _ -> [] (* failwith ("get_view_origins: not a view") *)

and get_view_original (h : h_formula) = match h with
  | ViewNode ({h_formula_view_original = original}) -> original
  | _ -> true (* failwith ("get_view_original: not a view") *)

and get_view_unfold_num (h : h_formula) = match h with
  | ViewNode ({h_formula_view_unfold_num = i}) -> i
  | _ -> 0 

and get_view_modes_x (h : h_formula) = match h with
  | ViewNode ({h_formula_view_modes = modes}) -> modes
  | _ -> failwith ("get_view_modes: not a view")

and get_view_modes (h : h_formula) =
  let pr l = string_of_int (List.length l) in 
  Debug.no_1 "get_view_modes" !print_h_formula pr (fun _ -> get_view_modes_x h) h
  
and get_view_imm (h : h_formula) = match h with
  | ViewNode ({h_formula_view_imm = imm}) -> imm
  | _ -> failwith ("get_view_imm: not a view")

and get_view_derv (h : h_formula) = match h with
  | ViewNode ({h_formula_view_derv = dr}) -> dr
  | _ -> failwith ("get_view_derv: not a view")

and get_data_derv (h : h_formula) = match h with
  | DataNode ({h_formula_data_derv = dr}) -> dr
  | _ -> failwith ("get_data_derv not a data")

and h_add_origins (h : h_formula) origs = 
  let pr = !print_h_formula in
  let pr2 = !print_ident_list in
  Debug.no_2 "h_add_origins" pr pr2 pr h_add_origins_a h origs

and h_add_origins_a (h : h_formula) origs =
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
	      Star ({h_formula_star_h1 = helper h1;
		  h_formula_star_h2 = helper h2;
		  h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_origins = origs @ vn.h_formula_view_origins}
    | DataNode dn -> DataNode {dn with h_formula_data_origins = origs @ dn.h_formula_data_origins}
    | _ -> h
  in helper h

and h_add_perm (h : h_formula) (permvar:cperm_var) : h_formula = 
  let pr = !print_h_formula in
  let pr2 = !print_spec_var in
  Debug.no_2 "h_add_perm" pr pr2 pr h_add_perm_a h permvar

and h_add_perm_a (h : h_formula) (permvar:cperm_var) : h_formula=
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
	      Star ({h_formula_star_h1 = helper h1;
		  h_formula_star_h2 = helper h2;
		  h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_perm = Some permvar}
    | DataNode vn -> DataNode {vn with h_formula_data_perm = Some permvar}
    | _ -> h
  in helper h

and h_add_original (h : h_formula) original = 
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
	      Star ({h_formula_star_h1 = helper h1;
		  h_formula_star_h2 = helper h2;
		  h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_original = original}
    | DataNode dn -> DataNode {dn with h_formula_data_original = original}
    | _ -> h 
  in helper h

and h_set_lhs_case (h : h_formula) flag = 
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
	      Star ({h_formula_star_h1 = helper h1;
		  h_formula_star_h2 = helper h2;
		  h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_lhs_case = flag}
    | _ -> h 
  in helper h

and h_set_lhs_case_of_a_view (h : h_formula) (v_name:ident) flag: h_formula = 
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
	      Star ({h_formula_star_h1 = helper h1;
		  h_formula_star_h2 = helper h2;
		  h_formula_star_pos = pos})
    | ViewNode vn -> 
        let name = get_node_name h in
        if (name=v_name) then
          ViewNode {vn with h_formula_view_lhs_case = flag}
        else h
    | _ -> h 
  in helper h

and h_add_unfold_num (h : h_formula) i = 
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
	      Star ({h_formula_star_h1 = helper h1;
		  h_formula_star_h2 = helper h2;
		  h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_unfold_num = i}
    | _ -> h 
  in helper h

(* WN : below is marking node as @D? *)
and h_add_origs_to_node (v : string) (h : h_formula) origs = 
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
	         h_formula_star_h2 = h2;
	         h_formula_star_pos = pos}) ->
	    Star ({h_formula_star_h1 = helper h1;
		       h_formula_star_h2 = helper h2;
		       h_formula_star_pos = pos})
    | ViewNode vn -> if not((CP.name_of_spec_var vn.h_formula_view_node) = v) then
	      ViewNode {vn with 
	          h_formula_view_origins = origs @ vn.h_formula_view_origins;
	          h_formula_view_original = false}
        else
	      ViewNode {vn with 
	          h_formula_view_origins = origs @ vn.h_formula_view_origins;
	          (* set the view to be derived *)
	          h_formula_view_original = false}
    | DataNode dn -> if not((CP.name_of_spec_var dn.h_formula_data_node) = v) then
	      DataNode {dn with 
	          h_formula_data_origins = origs @ dn.h_formula_data_origins;
	          h_formula_data_original = false}
        else
	      DataNode {dn with 
	          h_formula_data_origins = origs @ dn.h_formula_data_origins;
	          (* set the view to be derived *)
	          h_formula_data_original = false}
    | _ -> h 
  in helper h  
  
and add_origs_to_node (v:string) (f : formula) origs = 
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or ({formula_or_f1 = helper f1;
		  formula_or_f2 = helper f2;
		  formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_origs_to_node v b.formula_base_heap origs})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_origs_to_node v e.formula_exists_heap origs})
  in helper f

(* the first matched node has orgins and its view_original=false *)
(* , other nodes have their view_original=false *)
(*ln: lhs name: name of heap node in the head of an coercion*)
and h_add_origs_to_first_node (v : string) (ln:string) (h : h_formula) origs =
  (*return a pair (is_first,h_formula), where is_first indicates
    whether the first matched node is in the h_formula*)
  let rec helper h found_first: (bool * h_formula)= match h with
    | Star ({h_formula_star_h1 = h1;
	         h_formula_star_h2 = h2;
	         h_formula_star_pos = pos}) ->
        let  (is_first1,star_h1) = helper h1 found_first in
        let is_first2,star_h2 =
          if ((not is_first1) && (not (found_first))) then
            let is_first2, star_h2 =  helper h2 false in
            (is_first2,star_h2)
          else
            (*first node found somewhere*)
            let _,star_h2 =  helper h2 true in
            (true,star_h2)
        in
        is_first2, Star ({
            h_formula_star_h1 = star_h1;
		    h_formula_star_h2 = star_h2;
		    h_formula_star_pos = pos})
    | ViewNode vn ->
        if (((CP.name_of_spec_var vn.h_formula_view_node) = v) && (not found_first) && vn.h_formula_view_name=ln) then
          (*if it is the first matched node (same pointer name, 
            same view name and first_node not found):
            - add origs to its view_origins
            - set view_original= false*)
	      (true,
           ViewNode {vn with
	           h_formula_view_origins = origs @ vn.h_formula_view_origins;
	           (* set the view to be derived *)
	           h_formula_view_original = false})

        else
          (*otherwise, its origins unchange but its view_original=false*)
	      (false, ViewNode {vn with h_formula_view_original = false})
	      (* (false, ViewNode {vn with *)
          (*     h_formula_view_origins = origs @ vn.h_formula_view_origins; *)
          (*     h_formula_view_original = true}) *)
    | DataNode dn ->
        if (((CP.name_of_spec_var dn.h_formula_data_node) = v) && (not found_first) && dn.h_formula_data_name=ln) then
          (*if it is the first matched node (same pointer name, 
            same view name and first_node not found):
            - add origs to its view_origins
            - set view_original= false*)
	      (true,
           DataNode {dn with
	           h_formula_data_origins = origs @ dn.h_formula_data_origins;
	           (* set the view to be derived *)
	           h_formula_data_original = false})

        else
          (*otherwise, its origins unchange but its view_original=false*)
	      (false, DataNode {dn with h_formula_data_original = false})
	      (* (false, DataNode {dn with  *)
	      (*     h_formula_data_origins = origs @ dn.h_formula_data_origins; *)
          (*     h_formula_data_original = true}) *)
    | _ -> (false,h)
  in
  let _, h1 = helper h false in
  h1

(*ln: lhs name: name of heap node in the head of an coercion*)
and add_origs_to_first_node (v:string) (ln:string)(f : formula) origs = 
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or ({formula_or_f1 = helper f1;
		  formula_or_f2 = helper f2;
		  formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_origs_to_first_node v ln b.formula_base_heap origs})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_origs_to_first_node v ln e.formula_exists_heap origs})
  in helper f
 
and add_origins (f : formula) origs = 
  let pr = !print_formula in
  let pr2 = !print_ident_list in
  Debug.no_2 "add_origins" pr pr2 pr add_origins_a f origs

and add_origins_a (f : formula) origs = 
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or ({formula_or_f1 = helper f1;
		  formula_or_f2 = helper f2;
		  formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_origins b.formula_base_heap origs})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_origins e.formula_exists_heap origs})
  in helper f

and add_perm (f : formula) (permvar:cperm_var):formula = 
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or ({formula_or_f1 = helper f1;
		  formula_or_f2 = helper f2;
		  formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_perm b.formula_base_heap permvar})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_perm e.formula_exists_heap permvar})
  in helper f

and h_reset_origins (h : h_formula) = 
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
	      Star ({h_formula_star_h1 = helper h1;
		  h_formula_star_h2 = helper h2;
		  h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_origins = []}
    | _ -> h 
  in helper h

and reset_origins (f : formula) = 
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or ({formula_or_f1 = helper f1;
		  formula_or_f2 = helper f2;
		  formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_reset_origins b.formula_base_heap})
    | Exists e -> Exists ({e with formula_exists_heap = h_reset_origins e.formula_exists_heap})
  in helper f

and reset_struc_origins (f : struc_formula) = match f with
      | EOr b -> EOr {b with formula_struc_or_f1 = reset_struc_origins b.formula_struc_or_f1;formula_struc_or_f2 = reset_struc_origins b.formula_struc_or_f2}
      | EList b-> EList (map_l_snd reset_struc_origins b)
	  | ECase b -> ECase {b with formula_case_branches = map_l_snd reset_struc_origins b.formula_case_branches;}
	  | EBase b -> EBase {b with formula_struc_base = reset_origins b.formula_struc_base ; 
          formula_struc_continuation = map_opt reset_struc_origins b.formula_struc_continuation}
	  | EAssume (x,b,y) ->  EAssume (x,(reset_origins b),y)
      | EInfer b -> EInfer {b with formula_inf_continuation = reset_struc_origins b.formula_inf_continuation}
	
and add_original (f : formula) original = 
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or ({formula_or_f1 = helper f1;
		  formula_or_f2 = helper f2;
		  formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_original b.formula_base_heap original})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_original e.formula_exists_heap original})
  in helper f

and add_struc_original original (f : struc_formula) = match f with
	  | ECase b -> ECase {b with formula_case_branches = map_l_snd (add_struc_original original) b.formula_case_branches;}
      | EOr b -> EOr {b with formula_struc_or_f1= add_struc_original original b.formula_struc_or_f1;
                             formula_struc_or_f2= add_struc_original original b.formula_struc_or_f2;
                     }
      | EList b -> EList (map_l_snd (add_struc_original original) b)
	  | EBase b -> EBase {b with formula_struc_base = add_original b.formula_struc_base original ; 
			formula_struc_continuation = map_opt (add_struc_original original) b.formula_struc_continuation}
	  | EAssume (x,b,y) ->  EAssume (x,(add_original b original),y)
	  (*| EVariance b -> EVariance {b with formula_var_continuation = ext_f b.formula_var_continuation}*)
   | EInfer b -> EInfer {b with formula_inf_continuation = add_struc_original original b.formula_inf_continuation}

and set_lhs_case (f : formula) flag = 
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or ({formula_or_f1 = helper f1;
		  formula_or_f2 = helper f2;
		  formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_set_lhs_case b.formula_base_heap flag})
    | Exists e -> Exists ({e with formula_exists_heap = h_set_lhs_case e.formula_exists_heap flag})
  in helper f

and set_lhs_case_of_a_view (f : formula) (v_name:ident) flag : formula = 
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or ({formula_or_f1 = helper f1;
		  formula_or_f2 = helper f2;
		  formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_set_lhs_case_of_a_view b.formula_base_heap v_name flag})
    | Exists e -> Exists ({e with formula_exists_heap = h_set_lhs_case_of_a_view e.formula_exists_heap v_name flag})
  in helper f

and struc_formula_set_lhs_case (flag:bool) (f:struc_formula) : struc_formula = match f with 
	| EBase b -> EBase {b with formula_struc_base = set_lhs_case b.formula_struc_base flag ; 
		                       formula_struc_continuation = map_opt (struc_formula_set_lhs_case flag) b.formula_struc_continuation}
    | EOr b-> EOr {b with 
        formula_struc_or_f1 = struc_formula_set_lhs_case flag b.formula_struc_or_f1;
        formula_struc_or_f2 = struc_formula_set_lhs_case flag b.formula_struc_or_f2;
    }
    | EList b -> EList (map_l_snd (struc_formula_set_lhs_case flag) b)
	| ECase b -> ECase {b with formula_case_branches = map_l_snd (struc_formula_set_lhs_case flag) b.formula_case_branches;}
	| EAssume (x,b,y) -> EAssume (x,(set_lhs_case b flag),y)
    | EInfer b -> EInfer {b with formula_inf_continuation = struc_formula_set_lhs_case flag b.formula_inf_continuation}

and add_unfold_num (f : formula) uf = 
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or ({formula_or_f1 = helper f1;
		  formula_or_f2 = helper f2;
		  formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_unfold_num b.formula_base_heap uf})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_unfold_num e.formula_exists_heap uf})
  in helper f

and add_struc_origins origs (f:struc_formula) = match f with
	  | ECase b -> ECase {b with formula_case_branches = map_l_snd (add_struc_origins origs) b.formula_case_branches;}
	  | EBase b -> EBase {b with formula_struc_base = add_origins b.formula_struc_base origs ; 
			formula_struc_continuation = map_opt (add_struc_origins origs) b.formula_struc_continuation}
	  | EAssume (x,b,y) ->  EAssume (x,(add_origins b origs),y)
      | EOr b-> EOr {b with 
                       formula_struc_or_f1 = add_struc_origins origs b.formula_struc_or_f1;
                       formula_struc_or_f2 = add_struc_origins origs b.formula_struc_or_f2;}
      | EList b -> EList (map_l_snd (add_struc_origins origs) b)
      | EInfer b -> EInfer {b with formula_inf_continuation = add_struc_origins origs b.formula_inf_continuation}

and no_change (svars : CP.spec_var list) (pos : loc) : CP.formula = match svars with
  | sv :: rest ->
	    let f = CP.mkEqVar (CP.to_primed sv) (CP.to_unprimed sv) pos in
	    let restf = no_change rest pos in
		CP.mkAnd f restf pos
  | [] -> CP.mkTrue pos
 
and pos_of_struc_formula (f:struc_formula): loc =match f with
	| ECase b -> b.formula_case_pos
	| EBase b -> b.formula_struc_pos
	| EAssume (x,b,_)-> pos_of_formula b
    | EInfer b -> b.formula_inf_pos
    | EOr b-> b.formula_struc_or_pos
    | EList b-> match b with | x::_ -> pos_of_struc_formula (snd x) |_-> no_pos

and pos_of_formula (f : formula) : loc = match f with
  | Base ({formula_base_pos = pos}) -> pos
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> pos_of_formula f1
  | Exists ({formula_exists_pos = pos}) -> pos

and list_pos_of_formula (f : formula) : (loc list)= match f with
    | Base ({formula_base_heap = h;
           formula_base_pure = mf;
           formula_base_pos = pos}) -> (list_pos_of_heap_formula h) @ (MCP.list_pos_of_mix_formula mf) @ [pos]
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> (list_pos_of_formula f1) @ (list_pos_of_formula f2) @ [pos]
    | Exists ({formula_exists_heap = h;
               formula_exists_pure = mf;
               formula_exists_pos = pos}) -> (list_pos_of_heap_formula h) @ (MCP.list_pos_of_mix_formula mf) @ [pos]

and list_pos_of_heap_formula (h: h_formula): (loc list)= match h with
  | Star {h_formula_star_pos = pos} -> [pos]
  | Conj {h_formula_conj_pos = pos} -> [pos]
  | _ -> []

and get_lines (ll: loc list): (int list)=
  Gen.Basic.remove_dups (List.map (fun x -> x.start_pos.Lexing.pos_lnum) ll)

and subst_pos_struc_formula (p:loc) (f:struc_formula): struc_formula=
  match f with
	| ECase b ->
        let helper (pre, post)= (CP.subst_pos_formula p pre, subst_pos_struc_formula p post) in
        ECase {b with formula_case_branches = List.map helper b.formula_case_branches; formula_case_pos = p}
	| EBase b-> EBase { b with formula_struc_base = subst_pos_formula p b.formula_struc_base;
						formula_struc_continuation = map_opt (subst_pos_struc_formula p) b.formula_struc_continuation;
						formula_struc_pos = p}
	| EAssume (x,b,l)-> EAssume (x, subst_pos_formula p b, l)
    | EInfer ei -> EInfer {ei with formula_inf_continuation = subst_pos_struc_formula p ei.formula_inf_continuation; formula_inf_pos=p}
	| EList b -> EList (map_l_snd (subst_pos_struc_formula p) b)
	| EOr b -> EOr { formula_struc_or_f1 = subst_pos_struc_formula p b.formula_struc_or_f1;
					 formula_struc_or_f2 = subst_pos_struc_formula p b.formula_struc_or_f2;
					 formula_struc_or_pos = p} 
    
  

and subst_pos_formula (p:loc) (f: formula): formula=
  match f with
    | Base b -> Base {b with formula_base_pure = MCP.subst_pos_mix_formula p b.formula_base_pure;formula_base_pos = p }
    | Or b -> Or {formula_or_f1 = subst_pos_formula p b.formula_or_f1;
	                                     formula_or_f2 = subst_pos_formula p b.formula_or_f2;
	                                     formula_or_pos = p}
    | Exists ef -> Exists {ef with formula_exists_pos =  p}

and struc_fv (f: struc_formula) : CP.spec_var list = 
  let rdv = Gen.BList.remove_dups_eq CP.eq_spec_var in
  let dsvl l1 l2 = Gen.BList.difference_eq CP.eq_spec_var (rdv l1) l2 in
  match f with
	| ECase b -> dsvl (List.concat (List.map (fun (c1,c2) -> (CP.fv c1)@(struc_fv c2) ) b.formula_case_branches)) b.formula_case_exists
	| EBase b -> dsvl ((fold_opt struc_fv b.formula_struc_continuation)@(fv b.formula_struc_base))
                      (b.formula_struc_explicit_inst @ b.formula_struc_implicit_inst@ b.formula_struc_exists)
	| EAssume (x,b,_) -> fv b
	| EInfer b -> Gen.BList.remove_dups_eq CP.eq_spec_var (struc_fv b.formula_inf_continuation)
    | EOr b -> rdv ((struc_fv b.formula_struc_or_f1)@(struc_fv b.formula_struc_or_f2))
    | EList b -> rdv (fold_l_snd struc_fv b)

and struc_fv_infer (f: struc_formula) : CP.spec_var list = 
  let rdv = Gen.BList.remove_dups_eq CP.eq_spec_var in
  let dsvl l1 l2 = Gen.BList.difference_eq CP.eq_spec_var (rdv l1) l2 in
  match f with
    | ECase b -> dsvl (List.concat (List.map (fun (c1,c2) -> (CP.fv c1)@(struc_fv_infer c2) ) b.formula_case_branches)) b.formula_case_exists
    | EBase b -> dsvl ((fold_opt struc_fv_infer b.formula_struc_continuation)@(fv b.formula_struc_base))
          (b.formula_struc_explicit_inst @ b.formula_struc_implicit_inst@ b.formula_struc_exists)
    | EAssume (x,b,_) -> fv b
    | EInfer b -> dsvl (struc_fv_infer b.formula_inf_continuation) b.formula_inf_vars
    | EOr b -> rdv ((struc_fv_infer b.formula_struc_or_f1)@(struc_fv_infer b.formula_struc_or_f2))
    | EList b -> rdv (fold_l_snd struc_fv_infer b)

and struc_post_fv (f:struc_formula):Cpure.spec_var list = 
  let rdv = Gen.BList.remove_dups_eq CP.eq_spec_var in  
  match f with
	| ECase b-> rdv (fold_l_snd struc_post_fv b.formula_case_branches)
	| EBase b->	fold_opt struc_post_fv b.formula_struc_continuation
	| EAssume (x,b,_)-> fv b
    | EInfer b -> struc_post_fv b.formula_inf_continuation
    | EOr b -> rdv((struc_post_fv b.formula_struc_or_f1)@(struc_post_fv b.formula_struc_or_f2))
    | EList b -> rdv (fold_l_snd struc_post_fv b)

and heap_of (f:formula) : h_formula list = match f with
  | Or ({formula_or_f1 = f1; 
	formula_or_f2 = f2}) -> (heap_of f1)@(heap_of f2)
  | Base b-> [b.formula_base_heap]
  | Exists b-> [b.formula_exists_heap]

and fv_heap_of (f:formula) = 
  let hl= heap_of f in
  List.concat (List.map h_fv hl)

and fv_heap_of_one_formula (f:one_formula) =  (h_fv f.formula_heap)

and mk_Star f1 f2 pos = match f1 with
  | HFalse -> HFalse
  | HEmp -> f2
  | _ -> match f2 with
    | HFalse -> HFalse
    | HEmp -> f1
    | _ -> if (f1 = HTrue) && (f2 = HTrue) then HTrue
           else Star { h_formula_star_h1 = f1;
                       h_formula_star_h2 = f2;
                       h_formula_star_pos = pos }

and mk_Conj f1 f2 p =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else Conj ({h_formula_conj_h1 = f1; 
              h_formula_conj_h2 = f2; 
              h_formula_conj_pos = p})

and remove_h_lend (f:h_formula) : h_formula = 
  match f with
    | Star b -> 
        let new_f1 = remove_h_lend b.h_formula_star_h1 in
        let new_f2 = remove_h_lend b.h_formula_star_h2 in
        let pos = b.h_formula_star_pos in
        mk_Star new_f1 new_f2 pos
    | Conj b -> 
        let new_f1 = remove_h_lend b.h_formula_conj_h1 in
        let new_f2 = remove_h_lend b.h_formula_conj_h2 in
        let pos = b.h_formula_conj_pos in
        mk_Conj new_f1 new_f2 pos
    | DataNode {h_formula_data_imm = i} 
    | ViewNode {h_formula_view_imm = i} ->
          if isLend i then HEmp else f
    | _ -> f

and remove_lend (f:formula) : formula = match f with
  | Or b -> 
        let new_f1 = remove_lend b.formula_or_f1 in
        let new_f2 = remove_lend b.formula_or_f2 in
        Or {b with formula_or_f1=new_f1; formula_or_f2=new_f2}
  | Base b -> 
        let old_h = b.formula_base_heap in
        Base {b with formula_base_heap = remove_h_lend old_h}
  | Exists b -> 
        let old_h = b.formula_exists_heap in
        Exists {b with formula_exists_heap = remove_h_lend old_h}

and one_formula_fv (f:one_formula) : CP.spec_var list =
  let base = formula_of_one_formula f in
  let vars = fv base in
  let tid=f.formula_thread in
  (tid::vars)

and fv (f : formula) : CP.spec_var list = match f with
  | Or ({formula_or_f1 = f1; 
	formula_or_f2 = f2}) -> CP.remove_dups_svl (fv f1 @ fv f2)
  | Base ({formula_base_heap = h; 
	formula_base_pure = p;
    formula_base_and = a;
	formula_base_type = t}) ->
      let vars = CP.remove_dups_svl (List.concat (List.map one_formula_fv a)) in
      CP.remove_dups_svl (h_fv h @ MCP.mfv p @ vars)
  | Exists ({formula_exists_qvars = qvars; 
	formula_exists_heap = h; 
	formula_exists_pure = p; 
	formula_exists_type = t;
    formula_exists_and = a;
	formula_exists_flow = fl;
    formula_exists_label = lbl;
	formula_exists_pos = pos}) -> 
	    let fvars = fv (Base ({formula_base_heap = h; 
		formula_base_pure = p; 
		formula_base_type = t;
        formula_base_and = a;
		formula_base_flow = fl;
        formula_base_label = lbl;
		formula_base_pos = pos})) in
        let vars = List.concat (List.map one_formula_fv a) in
        let fvars = CP.remove_dups_svl (vars@fvars) in
	    let res = Gen.BList.difference_eq CP.eq_spec_var fvars qvars in
		res
	
and f_h_fv (f : formula) : CP.spec_var list = 
	let rec helper h = match h with
	  | Star b ->  Gen.BList.remove_dups_eq (=) (helper b.h_formula_star_h1 @ helper b.h_formula_star_h2)
	  | Conj b ->  Gen.BList.remove_dups_eq (=) (helper b.h_formula_conj_h1 @ helper b.h_formula_conj_h2)
	  | Phase b ->  Gen.BList.remove_dups_eq (=) (helper b.h_formula_phase_rd @ helper b.h_formula_phase_rw)
	  | DataNode b -> [b.h_formula_data_node]
	  | ViewNode b -> [b.h_formula_view_node]
	  | HRel (r, args, pos) -> [r] (*vp*)
	  | HTrue | HFalse | HEmp | Hole _ -> [] in
	match f with
	  | Or b -> CP.remove_dups_svl (fv b.formula_or_f1 @ fv b.formula_or_f2)
	  | Base b -> h_fv b.formula_base_heap
	  | Exists b -> Gen.BList.difference_eq CP.eq_spec_var (h_fv b.formula_exists_heap) b.formula_exists_qvars 
	
and h_fv (h : h_formula) : CP.spec_var list = match h with
  | Star ({h_formula_star_h1 = h1; 
	h_formula_star_h2 = h2; 
	h_formula_star_pos = pos}) -> CP.remove_dups_svl (h_fv h1 @ h_fv h2)
  | Conj ({h_formula_conj_h1 = h1; 
	h_formula_conj_h2 = h2; 
	h_formula_conj_pos = pos}) -> Gen.BList.remove_dups_eq (=) (h_fv h1 @ h_fv h2)
  | Phase ({h_formula_phase_rd = h1; 
	h_formula_phase_rw = h2; 
	h_formula_phase_pos = pos}) -> Gen.BList.remove_dups_eq (=) (h_fv h1 @ h_fv h2)
  | DataNode ({h_formula_data_node = v;
               h_formula_data_perm = perm;
               h_formula_data_imm = ann;
               h_formula_data_arguments = vs})
  | ViewNode ({h_formula_view_node = v; 
               h_formula_view_perm = perm; 
               h_formula_view_imm = ann;
	           h_formula_view_arguments = vs}) -> 
      let pvars = fv_cperm perm in
      let avars = fv_ann ann in
      let pvars = 
        if pvars==[] then 
          pvars 
        else 
          let var = List.hd pvars in
          if (List.mem var vs) then [] else pvars
      in
      let vs=avars@pvars@vs in
      if List.mem v vs then vs else v :: vs
  | HRel (r, args, _) ->
      let vid = r in
	  vid::CP.remove_dups_svl (List.fold_left List.append [] (List.map CP.afv args))
  | HTrue | HFalse | HEmp | Hole _ -> []

(*and br_fv br init_l: CP.spec_var list =
  CP.remove_dups_svl (List.fold_left (fun a (c1,c2)-> (CP.fv c2)@a) init_l br)*)
  
and f_top_level_vars_struc (f:struc_formula) : CP.spec_var list =
  let pr1 = !print_struc_formula in
  let pr2 = !print_svl in
  Debug.no_1 "f_top_level_vars_struc" pr1 pr2 f_top_level_vars_struc_x f

and f_top_level_vars_struc_x (f:struc_formula) : CP.spec_var list = match f with
  | ECase c-> fold_l_snd f_top_level_vars_struc_x c.formula_case_branches
  | EBase b -> 	(f_top_level_vars b.formula_struc_base) @ (fold_opt f_top_level_vars_struc_x b.formula_struc_continuation)
  | EAssume _ -> []
  | EInfer b -> f_top_level_vars_struc_x b.formula_inf_continuation
  | EOr b-> (f_top_level_vars_struc_x b.formula_struc_or_f1)@(f_top_level_vars_struc_x b.formula_struc_or_f2)
  | EList b -> fold_l_snd f_top_level_vars_struc_x b
        
and f_top_level_vars_x (f : formula) : CP.spec_var list = match f with
  | Base ({formula_base_heap = h}) -> (top_level_vars h)
  | Or ({ formula_or_f1 = f1;
	formula_or_f2 = f2}) -> (f_top_level_vars_x f1) @ (f_top_level_vars_x f2)
  | Exists ({formula_exists_heap = h}) -> (top_level_vars h)

and f_top_level_vars (f : formula) : CP.spec_var list = 
  let pr1 = !print_formula in
  let pr2 = !print_svl in
  Debug.no_1 "f_top_level_vars" pr1 pr2 f_top_level_vars_x f 


and top_level_vars (h : h_formula) : CP.spec_var list = match h with
  | Star ({h_formula_star_h1 = h1; 
	h_formula_star_h2 = h2}) -> (top_level_vars h1) @ (top_level_vars h2)
  | Conj ({h_formula_conj_h1 = h1; 
	h_formula_conj_h2 = h2}) -> (top_level_vars h1) @ (top_level_vars h2)
  | Phase ({h_formula_phase_rd = h1; 
	h_formula_phase_rw = h2}) -> (top_level_vars h1) @ (top_level_vars h2)
  | DataNode ({h_formula_data_node = v}) 
  | ViewNode ({h_formula_view_node = v}) -> [v]
  | HRel (r, agrs,  pos) -> [r] (*vp*)
  | HTrue | HFalse | HEmp | Hole _ -> []

and get_formula_pos (f : formula) = match f with
  | Base ({formula_base_pos = p}) -> p
  | Or ({formula_or_pos = p}) -> p
  | Exists ({formula_exists_pos = p}) -> p 


(* substitution *)

and subst_avoid_capture (fr : CP.spec_var list) (t : CP.spec_var list) (f : formula) =
  Debug.no_3 "subst_avoid_capture" 
      (add_str "from vars:" !print_svl) 
      (add_str "to vars:" !print_svl)
      !print_formula 
      !print_formula
      (fun _ _ _ -> subst_avoid_capture_x fr t f) fr t f

and subst_avoid_capture_x (fr : CP.spec_var list) (t : CP.spec_var list) (f : formula) =
  let fresh_fr = CP.fresh_spec_vars fr in
  (*--- 09.05.2000 *)
  (*let _ = (print_string ("\n[cformula.ml, line 307]: fresh name = " ^ (string_of_spec_var_list fresh_fr) ^ "!!!!!!!!!!!\n")) in*)
  (*09.05.2000 ---*)
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst_one_by_one st1 f in
  let f2 = subst_one_by_one st2 f1 in
  f2
      
and subst_avoid_capture_h (fr : CP.spec_var list) (t : CP.spec_var list) (f : h_formula) : h_formula =
  Debug.no_3 "[cformula]subst_avoid_capture_h" !print_svl !print_svl !print_h_formula !print_h_formula
      (fun _ _ _ -> subst_avoid_capture_h_x fr t f) fr t f

and subst_avoid_capture_h_x (fr : CP.spec_var list) (t : CP.spec_var list) (f : h_formula) : h_formula =
  let fresh_fr = CP.fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst_one_by_one_h st1 f in
  let f2 = subst_one_by_one_h st2 f1 in
  f2

and subst_var_list sst (svs : Cpure.spec_var list) = match svs with
  | [] -> []
  | sv :: rest ->
        let new_vars = subst_var_list sst rest in
        let new_sv = match List.filter (fun st -> fst st = sv) sst with
		  | [(fr, t)] -> t
		  | _ -> sv in
		new_sv :: new_vars

and subst_struc_avoid_capture_varperm (fr : CP.spec_var list) (t : CP.spec_var list) (f : struc_formula):struc_formula =
  let fresh_fr = CP.fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst_struc_varperm st1 f in
  let f2 = subst_struc_varperm st2 f1 in
  f2


(*LDK: substitue variales (t) in formula (f) by variables (fr)*)
and subst_struc_avoid_capture (fr : CP.spec_var list) (t : CP.spec_var list) (f : struc_formula):struc_formula =
  let fresh_fr = CP.fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst_struc st1 f in
  let f2 = subst_struc st2 f1 in
  f2
and subst_struc sst (f : struc_formula) = match sst with
  | s :: rest -> subst_struc rest (apply_one_struc s f)
  | [] -> f

and subst_struc_varperm sst (f : struc_formula) = match sst with
  | s :: rest -> subst_struc_varperm rest (apply_one_struc_varperm s f)
  | [] -> f

and subst_struc_pre sst (f : struc_formula) = 
  (* apply_par_struc_pre s f *)
  match sst with
  | s :: rest -> subst_struc_pre rest (apply_one_struc_pre s f)
  | [] -> f

and apply_one_struc_pre  ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : struc_formula):struc_formula = match f with
	| ECase b -> ECase {b with 
              formula_case_branches = List.map (fun (c1,c2)-> ((CP.apply_one s c1),(apply_one_struc_pre s c2)) ) b.formula_case_branches;}
	| EBase b -> EBase {
			  formula_struc_explicit_inst = List.map (subst_var s)  b.formula_struc_explicit_inst;
			  formula_struc_implicit_inst = List.map (subst_var s)  b.formula_struc_implicit_inst;
			  formula_struc_exists = List.map (subst_var s)  b.formula_struc_exists;
			  formula_struc_base = apply_one s  b.formula_struc_base;
			  formula_struc_continuation = map_opt (apply_one_struc_pre s) b.formula_struc_continuation;
			  formula_struc_pos = b.formula_struc_pos	
		  }
	| EAssume (x,b,y)-> if (List.mem fr x) then f else EAssume (x, (apply_one s b),y)
    | EInfer b -> EInfer {b with formula_inf_continuation = apply_one_struc_pre s b.formula_inf_continuation}
    | EOr b -> EOr {b with formula_struc_or_f1 = apply_one_struc_pre s b.formula_struc_or_f1; 
                           formula_struc_or_f2 = apply_one_struc_pre s b.formula_struc_or_f2;}
    | EList b-> EList (map_l_snd (apply_one_struc_pre s) b)

and apply_one_struc_pre_varperm  ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : struc_formula):struc_formula =  match f with
	| ECase b -> 
		  ECase ({b with 
              formula_case_branches = List.map (fun (c1,c2)-> ((CP.apply_one_varperm s c1),(apply_one_struc_pre_varperm s c2)) ) b.formula_case_branches;})
	| EBase b ->
		  EBase ({
			  formula_struc_explicit_inst = List.map (subst_var s)  b.formula_struc_explicit_inst;
			  formula_struc_implicit_inst = List.map (subst_var s)  b.formula_struc_implicit_inst;
			  formula_struc_exists = List.map (subst_var s)  b.formula_struc_exists;
			  formula_struc_base = apply_one_varperm s  b.formula_struc_base;
			  formula_struc_continuation = map_opt (apply_one_struc_pre_varperm s) b.formula_struc_continuation;
			  formula_struc_pos = b.formula_struc_pos})
	| EAssume (x,b,y)-> if (List.mem fr x) then f else EAssume (x, (apply_one_varperm s b),y)
    | EInfer b -> EInfer {b with formula_inf_continuation = (apply_one_struc_pre_varperm s) b.formula_inf_continuation}
	| EOr b -> EOr {b with 
					formula_struc_or_f1 = apply_one_struc_pre_varperm s b.formula_struc_or_f1;
					formula_struc_or_f2 = apply_one_struc_pre_varperm s b.formula_struc_or_f2;}
	| EList b -> EList (map_l_snd (apply_one_struc_pre_varperm s) b)
	
and subst_struc_pre_varperm sst (f : struc_formula) = 
  (* apply_par_struc_pre s f *)
  match sst with
  | s :: rest -> subst_struc_pre_varperm rest (apply_one_struc_pre_varperm s f)
  | [] -> f 

and apply_one_struc  ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : struc_formula):struc_formula =  match f with
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> ((CP.apply_one s c1),(apply_one_struc s c2)) ) b.formula_case_branches;}
	| EBase b -> EBase {
			  formula_struc_explicit_inst = List.map (subst_var s)  b.formula_struc_explicit_inst;
			  formula_struc_implicit_inst = List.map (subst_var s)  b.formula_struc_implicit_inst;
			  formula_struc_exists = List.map (subst_var s)  b.formula_struc_exists;
			  formula_struc_base = apply_one s  b.formula_struc_base;
			  formula_struc_continuation = map_opt (apply_one_struc s) b.formula_struc_continuation;
			  formula_struc_pos = b.formula_struc_pos }
	| EAssume (x,b,y)-> EAssume((subst_var_list [s] x),(apply_one s b),y)
    | EInfer b -> EInfer {b with  formula_inf_continuation = apply_one_struc s b.formula_inf_continuation}
    | EOr b -> EOr {b with 
					formula_struc_or_f1 = apply_one_struc s b.formula_struc_or_f1; 
                    formula_struc_or_f2 = apply_one_struc s b.formula_struc_or_f2;}
    | EList b-> EList (map_l_snd (apply_one_struc s) b)

and apply_one_struc_varperm  ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : struc_formula):struc_formula = match f with
	| ECase b ->  ECase ({b with formula_case_branches = List.map (fun (c1,c2)-> ((CP.apply_one_varperm s c1),(apply_one_struc_varperm s c2)) ) b.formula_case_branches;})
	| EBase b ->  EBase ({
			  formula_struc_explicit_inst = List.map (subst_var s)  b.formula_struc_explicit_inst;
			  formula_struc_implicit_inst = List.map (subst_var s)  b.formula_struc_implicit_inst;
			  formula_struc_exists = List.map (subst_var s)  b.formula_struc_exists;
			  formula_struc_base = apply_one_varperm s  b.formula_struc_base;
			  formula_struc_continuation = map_opt (apply_one_struc_varperm s) b.formula_struc_continuation;
			  formula_struc_pos = b.formula_struc_pos })
	| EAssume (x,b,y)-> EAssume((subst_var_list [s] x),(apply_one_varperm s b),y)
    | EInfer b -> EInfer {b with formula_inf_continuation = (apply_one_struc_varperm s) b.formula_inf_continuation}
	| EOr b -> EOr {b with 
					  formula_struc_or_f1 = apply_one_struc_varperm s b.formula_struc_or_f1;
					  formula_struc_or_f2 = apply_one_struc_varperm s b.formula_struc_or_f2;}
	| EList b -> EList (map_l_snd (apply_one_struc_varperm s) b)

(*LDK: add a constraint formula between perm spec var of datanode to fresh spec var of a view decl  *)
and add_mix_formula_to_struc_formula  (rhs_p: MCP.mix_formula) (f : struc_formula): struc_formula =
  Debug.no_2 "add_mix_formula_to_struc_formula"
      !print_mix_formula !print_struc_formula !print_struc_formula
      add_mix_formula_to_struc_formula_x rhs_p f 

(*LDK: only heap need fractional permision spec var (perm) *)
and add_mix_formula_to_struc_formula_x (rhs_p: MCP.mix_formula) (f : struc_formula) : struc_formula = match f with
	| ECase b -> f
	| EBase b -> EBase {b with  formula_struc_base = add_mix_formula_to_formula rhs_p b.formula_struc_base ;
			  formula_struc_continuation = map_opt (add_mix_formula_to_struc_formula_x rhs_p) b.formula_struc_continuation;}
	| EAssume (x,b,y)-> f
	| EInfer b -> EInfer { b with formula_inf_continuation = add_mix_formula_to_struc_formula_x rhs_p b.formula_inf_continuation;}
    | EOr b -> EOr {b with 
						formula_struc_or_f1 = add_mix_formula_to_struc_formula_x rhs_p b.formula_struc_or_f1; 
						formula_struc_or_f2 = add_mix_formula_to_struc_formula_x rhs_p b.formula_struc_or_f2; }
	| EList b -> EList (map_l_snd (add_mix_formula_to_struc_formula_x rhs_p) b)

and add_pure_formula_to_formula (f1_pure: CP.formula) (f2_f:formula)  : formula = add_mix_formula_to_formula (MCP.mix_of_pure f1_pure) f2_f

(*LDK : add a constraint formula between perm spec var of datanode to fresh spec var of a view decl  *)
and add_mix_formula_to_formula  (f1_mix: MCP.mix_formula) (f2_f:formula) : formula =
  Debug.no_2 "add_mix_formula_to_formula_x" !print_mix_formula !print_formula
      !print_formula
      add_mix_formula_to_formula_x f1_mix f2_f

and add_mix_formula_to_formula_x (f1_mix: MCP.mix_formula) (f2_f:formula)  : formula=
  match f2_f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
        Or ({formula_or_f1 = add_mix_formula_to_formula_x f1_mix f1 ; formula_or_f2 =  add_mix_formula_to_formula_x f1_mix f2 ; formula_or_pos = pos})
    | Base b -> Base { b with formula_base_pure = add_mix_formula_to_mix_formula f1_mix b.formula_base_pure;}
    | Exists b -> Exists {b with  formula_exists_pure = add_mix_formula_to_mix_formula f1_mix b.formula_exists_pure;}

(*add f1 into p*)
and add_mix_formula_to_mix_formula (f1: MCP.mix_formula) (f2: MCP.mix_formula) :MCP.mix_formula =  (MCP.merge_mems f1 f2 true)

and add_formula_to_formula (f1: CP.formula) (f2:CP.formula) = (CP.And (f1,f2,no_pos))

and add_pure_formula_to_mix_formula (pure_f: CP.formula) (mix_f: MCP.mix_formula):MCP.mix_formula = 
  (match mix_f with
    | MCP.MemoF m1 -> 
        let _ = print_string ("[add_pure_formula_to_mix_formula] Warning: mix_f not added to MCP.MemoF \n") in
        mix_f
    | MCP.OnePF mix_f_pure ->  MCP.OnePF (add_formula_to_formula pure_f mix_f_pure) )

and one_formula_subst sst (f : one_formula) = 
  let base = formula_of_one_formula f in
  let rs = subst sst base in
  let ref_vars = (List.map (CP.subst_var_par sst) f.formula_ref_vars) in
  let tid = CP.subst_var_par sst f.formula_thread in
  let one_f = (one_formula_of_formula rs tid) in
  {one_f with formula_ref_vars = ref_vars}

and one_formula_subst_varperm sst (f : one_formula) = 
  let base = formula_of_one_formula f in
  let rs = subst_varperm sst base in
  let ref_vars = (List.map (CP.subst_var_par sst) f.formula_ref_vars) in
  let tid = CP.subst_var_par sst f.formula_thread in
  let one_f = (one_formula_of_formula rs tid) in
  {one_f with formula_ref_vars = ref_vars}

	
(** An Hoa : replace the function subst above by substituting f in parallel **)

and subst sst (f : formula) = 
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula in
  Debug.no_2 "subst_one_by_one" pr1 pr2 pr2 subst_x sst f 

and subst_x sst (f : formula) =
  let rec helper f =
	match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
    Or ({formula_or_f1 = helper f1; formula_or_f2 =  helper f2; formula_or_pos = pos})
  | Base b-> Base ({b with formula_base_heap = h_subst sst b.formula_base_heap; 
					formula_base_pure =MCP.regroup_memo_group (MCP.m_apply_par sst b.formula_base_pure); 
                    formula_base_and = (List.map (fun f -> one_formula_subst sst f) b.formula_base_and);})
  | Exists ({formula_exists_qvars = qsv; 
						formula_exists_heap = qh; 
						formula_exists_pure = qp; 
						formula_exists_type = tconstr;
                        formula_exists_and = a; (*TO CHECK*)
						formula_exists_flow = fl;
						formula_exists_label = lbl;
						formula_exists_pos = pos}) -> 
		(* Variable under this existential quantification should NOT be substituted! *)
		(* Thus, we need to filter out replacements (fr |-> t) in sst where fr is in qsv *)
		let qsvnames = (List.map CP.name_of_spec_var qsv) in
		let sst = List.filter (fun (fr,_) -> not (List.mem (CP.name_of_spec_var fr) qsvnames)) sst in
		if sst = [] then f
		else Exists ({formula_exists_qvars = qsv; 
									formula_exists_heap =  h_subst sst qh; 
									formula_exists_pure = MCP.regroup_memo_group (MCP.m_apply_par sst qp);
									formula_exists_type = tconstr;
                                    formula_exists_and = (List.map (fun f -> one_formula_subst sst f) a);
									formula_exists_flow = fl;
									formula_exists_label = lbl;
									formula_exists_pos = pos})
  in helper f

and subst_b sst (b:formula_base): formula_base =
  {b with formula_base_heap = h_subst sst b.formula_base_heap;
	  formula_base_pure =MCP.regroup_memo_group (MCP.m_apply_par sst b.formula_base_pure);
      formula_base_and = (List.map (fun f -> one_formula_subst sst f) b.formula_base_and);}

(** An Hoa : End of formula substitution **)

(*sub everything including VarPerm*)
and subst_varperm sst (f : formula) = 
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula in
  Debug.no_2 "subst_varperm" pr1 pr2 pr2 subst_varperm_x sst f 

and subst_varperm_x sst (f : formula) =
  let rec helper f =
	match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
    Or ({formula_or_f1 = helper f1; formula_or_f2 =  helper f2; formula_or_pos = pos})
  | Base b ->Base ({b with formula_base_heap = h_subst sst b.formula_base_heap; 
					formula_base_pure =MCP.regroup_memo_group (MCP.m_apply_par_varperm sst b.formula_base_pure);
                    formula_base_and = (List.map (fun f -> one_formula_subst_varperm sst f) b.formula_base_and);})
  | Exists b -> 
		(* Variable under this existential quantification should NOT be substituted! *)
		(* Thus, we need to filter out replacements (fr |-> t) in sst where fr is in b.formula_exists_qvars *)
		let qsvnames = (List.map CP.name_of_spec_var b.formula_exists_qvars) in
		let sst = List.filter (fun (fr,_) -> not (List.mem (CP.name_of_spec_var fr) qsvnames)) sst in
		if sst = [] then f
		else Exists ({b with formula_exists_heap =  h_subst sst b.formula_exists_heap; 
							 formula_exists_pure = MCP.regroup_memo_group (MCP.m_apply_par_varperm sst b.formula_exists_pure); 
							 formula_exists_and = (List.map (fun f -> one_formula_subst_varperm sst f) b.formula_exists_and);})
  in helper f
(** An Hoa : End of formula substitution **)


(** An Hoa: Function to substitute variables in a heap formula in parallel **)
and h_subst sst (f : h_formula) = 
	match f with
  | Star ({h_formula_star_h1 = f1; 
					h_formula_star_h2 = f2; 
					h_formula_star_pos = pos}) -> 
		Star ({h_formula_star_h1 = h_subst sst f1; 
		h_formula_star_h2 = h_subst sst f2; 
		h_formula_star_pos = pos})
  | Phase ({h_formula_phase_rd = f1; 
						h_formula_phase_rw = f2; 
						h_formula_phase_pos = pos}) -> 
		Phase ({h_formula_phase_rd = h_subst sst f1; 
		h_formula_phase_rw = h_subst sst f2; 
		h_formula_phase_pos = pos})
  | Conj ({h_formula_conj_h1 = f1; 
					h_formula_conj_h2 = f2; 
					h_formula_conj_pos = pos}) -> 
		Conj ({h_formula_conj_h1 = h_subst sst f1; 
		h_formula_conj_h2 = h_subst sst f2; 
		h_formula_conj_pos = pos})
  | ViewNode ({h_formula_view_node = x; 
							h_formula_view_name = c; 
							h_formula_view_imm = imm; 
							h_formula_view_perm = perm; (*LDK*)
							h_formula_view_arguments = svs; 
							h_formula_view_modes = modes;
							h_formula_view_coercible = coble;
							h_formula_view_origins = orgs;
							h_formula_view_original = original;
							h_formula_view_unfold_num = i;
							h_formula_view_label = lbl;
							h_formula_view_remaining_branches = ann;
							h_formula_view_pruning_conditions = pcond;
							h_formula_view_pos = pos} as g) -> 
		ViewNode { g with 
							h_formula_view_imm = subs_imm_par sst imm;  
							h_formula_view_node = CP.subst_var_par sst x; 
							h_formula_view_perm = map_opt (CP.subst_var_par sst) perm;
							h_formula_view_arguments = List.map (CP.subst_var_par sst) svs;
							h_formula_view_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_subs sst c,c2)) pcond
		}
  | DataNode ({h_formula_data_node = x; 
							h_formula_data_name = c; 
							h_formula_data_derv = dr; 
							h_formula_data_imm = imm; 
							h_formula_data_perm = perm; (*LDK*)
							h_formula_data_arguments = svs; 
							h_formula_data_origins = orgs;
							h_formula_data_original = original;
							h_formula_data_holes = hs; (* An Hoa 16/8/2011 Holes added *)
							h_formula_data_label = lbl;
							h_formula_data_remaining_branches = ann;
							h_formula_data_pruning_conditions = pcond;
							h_formula_data_pos = pos}) -> 
		DataNode ({h_formula_data_node = CP.subst_var_par sst x; 
							h_formula_data_name = c; 
							h_formula_data_derv = dr; 
							h_formula_data_imm = subs_imm_par sst imm;  
							h_formula_data_perm = map_opt (CP.subst_var_par sst) perm;   (*LDK*)
							h_formula_data_arguments = List.map (CP.subst_var_par sst) svs;
							h_formula_data_holes = hs; (* An Hoa 16/8/2011 Holes added *)
							h_formula_data_origins = orgs;
							h_formula_data_original = original;
							h_formula_data_label = lbl;
							h_formula_data_remaining_branches = ann;
							h_formula_data_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_subs sst c,c2)) pcond;
							h_formula_data_pos = pos})
  | HRel (r, args, pos) -> HRel (r, CP.e_apply_subs_list sst args, pos)
  | HTrue -> f
  | HFalse -> f
  | HEmp -> f
  | Hole _ -> f
(** An Hoa : End of heap formula substitution **) 

(* and subst_var_par sst v = try *)
(* 			List.assoc v sst *)
(* 	with Not_found -> v *)

and subst_one_by_one sst (f : formula) = 
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula in
  Debug.no_2 "subst_one_by_one" pr1 pr2 pr2 subst_one_by_one_x sst f 

and subst_one_by_one_x sst (f : formula) = match sst with
  | s :: rest -> subst_one_by_one_x rest (apply_one s f)
  | [] -> f

and subst_one_by_one_h sst (f : h_formula) = 
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_h_formula in
  Debug.no_2 "subst_one_by_one" pr1 pr2 pr2 subst_one_by_one_h_x sst f 

and subst_one_by_one_h_x sst (f : h_formula) = match sst with
  | s :: rest -> subst_one_by_one_h_x rest (h_apply_one s f)
  | [] -> f

and apply_one_imm (fr,t) a = match a with
  | ConstAnn _ -> a
  | PolyAnn sv ->  PolyAnn (if CP.eq_spec_var sv fr then t else sv)


and subs_imm_par sst a = match a with
  | ConstAnn _ -> a
  | PolyAnn sv ->  PolyAnn (CP.subst_var_par sst sv)

and subst_var (fr, t) (o : CP.spec_var) = if CP.eq_spec_var fr o then t else o

and apply_one_one_formula ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : one_formula) = 
  let base = formula_of_one_formula f in
  let rs = apply_one s base in
  let tid = subst_var s f.formula_thread in
  let ref_vars = List.map (subst_var s) f.formula_ref_vars in
  let one_f = (one_formula_of_formula rs tid) in
  {one_f with formula_ref_vars = ref_vars}

and apply_one_one_formula_varperm ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : one_formula) = 
  let base = formula_of_one_formula f in
  let rs = apply_one_varperm s base in
  let tid = subst_var s f.formula_thread in
  let ref_vars = List.map (subst_var s) f.formula_ref_vars in
  let one_f = (one_formula_of_formula rs tid) in
  {one_f with formula_ref_vars = ref_vars}

and apply_one ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
        Or ({formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h; 
	formula_base_pure = p; 
	formula_base_type = t;
    formula_base_and = a;
	formula_base_flow = fl;
    formula_base_label = lbl;
	formula_base_pos = pos}) -> 
        Base ({formula_base_heap = h_apply_one s h; 
		formula_base_pure =MCP.regroup_memo_group (MCP.m_apply_one s p); 
		formula_base_type = t;
        formula_base_and = List.map (apply_one_one_formula s) a;
		formula_base_flow = fl;
        formula_base_label = lbl;
		formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
	formula_exists_heap = qh; 
	formula_exists_pure = qp; 
	formula_exists_type = tconstr;
    formula_exists_and = a;
	formula_exists_flow = fl;
    formula_exists_label = lbl;
	formula_exists_pos = pos}) -> 
	    if List.mem (CP.name_of_spec_var fr) (List.map CP.name_of_spec_var qsv) then f 
	    else Exists ({formula_exists_qvars = qsv; 
		formula_exists_heap =  h_apply_one s qh; 
		formula_exists_pure = MCP.regroup_memo_group (MCP.m_apply_one s qp); 
		formula_exists_type = tconstr;
        formula_exists_and = List.map (apply_one_one_formula s) a;
		formula_exists_flow = fl;
        formula_exists_label = lbl;
		formula_exists_pos = pos})

(*apply subst to VarPerm only*)
and apply_one_varperm ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
        Or ({formula_or_f1 = apply_one_varperm s f1; formula_or_f2 =  apply_one_varperm s f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h; 
	formula_base_pure = p; 
	formula_base_type = t;
    formula_base_and = a;
	formula_base_flow = fl;
    formula_base_label = lbl;
	formula_base_pos = pos}) -> 
        Base ({formula_base_heap = h_apply_one s h;
		formula_base_pure =MCP.regroup_memo_group (MCP.m_apply_one_varperm s p); 
		formula_base_type = t;
        formula_base_and = List.map (apply_one_one_formula_varperm s) a;
		formula_base_flow = fl;
        formula_base_label = lbl;
		formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
	formula_exists_heap = qh; 
	formula_exists_pure = qp; 
	formula_exists_type = tconstr;
    formula_exists_and = a;
	formula_exists_flow = fl;
    formula_exists_label = lbl;
	formula_exists_pos = pos}) -> 
	    if List.mem (CP.name_of_spec_var fr) (List.map CP.name_of_spec_var qsv) then f 
	    else Exists ({formula_exists_qvars = qsv; 
		formula_exists_heap =  h_apply_one s qh;
		formula_exists_pure = MCP.regroup_memo_group (MCP.m_apply_one_varperm s qp); 
		formula_exists_type = tconstr;
        formula_exists_and = List.map (apply_one_one_formula_varperm s) a;
		formula_exists_flow = fl;
        formula_exists_label = lbl;
		formula_exists_pos = pos})


and h_apply_one ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : h_formula) = match f with
  | Star ({h_formula_star_h1 = f1; 
	h_formula_star_h2 = f2; 
	h_formula_star_pos = pos}) -> 
        Star ({h_formula_star_h1 = h_apply_one s f1; 
	    h_formula_star_h2 = h_apply_one s f2; 
	    h_formula_star_pos = pos})
  | Phase ({h_formula_phase_rd = f1; 
	h_formula_phase_rw = f2; 
	h_formula_phase_pos = pos}) -> 
        Phase ({h_formula_phase_rd = h_apply_one s f1; 
	    h_formula_phase_rw = h_apply_one s f2; 
	    h_formula_phase_pos = pos})
  | Conj ({h_formula_conj_h1 = f1; 
	h_formula_conj_h2 = f2; 
	h_formula_conj_pos = pos}) -> 
        Conj ({h_formula_conj_h1 = h_apply_one s f1; 
	    h_formula_conj_h2 = h_apply_one s f2; 
	    h_formula_conj_pos = pos})
  | ViewNode ({h_formula_view_node = x; 
	h_formula_view_name = c; 
    h_formula_view_imm = imm; 
	h_formula_view_perm = perm; (*LDK*)
	h_formula_view_arguments = svs; 
	h_formula_view_modes = modes;
	h_formula_view_coercible = coble;
	h_formula_view_origins = orgs;
	h_formula_view_original = original;
	h_formula_view_unfold_num = i;
	h_formula_view_label = lbl;
    h_formula_view_remaining_branches = ann;
    h_formula_view_pruning_conditions = pcond;
	h_formula_view_pos = pos} as g) -> 
        ViewNode {g with h_formula_view_node = subst_var s x; 
        h_formula_view_perm = subst_var_perm () s perm;  (*LDK*)
        h_formula_view_imm = apply_one_imm s imm;  
		h_formula_view_arguments = List.map (subst_var s) svs;
        h_formula_view_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_one s c,c2)) pcond
        }
  | DataNode ({h_formula_data_node = x; 
	h_formula_data_name = c; 
    h_formula_data_derv = dr;
    h_formula_data_imm = imm; 
    h_formula_data_perm = perm; (*LDK*)
	h_formula_data_origins = orgs;
	h_formula_data_original = original;
	h_formula_data_arguments = svs; 
	h_formula_data_holes = hs; (* An Hoa 16/8/2011 Holes added *)
	h_formula_data_label = lbl;
    h_formula_data_remaining_branches = ann;
    h_formula_data_pruning_conditions = pcond;
	h_formula_data_pos = pos}) -> 
        DataNode ({h_formula_data_node = subst_var s x; 
		h_formula_data_name = c; 
        h_formula_data_derv = dr;
    	h_formula_data_perm = subst_var_perm () s perm; (*LDK*)
        h_formula_data_imm = apply_one_imm s imm;  
	    h_formula_data_origins = orgs;
	    h_formula_data_original = original;
		h_formula_data_arguments = List.map (subst_var s) svs;
	    h_formula_data_holes = hs;
		h_formula_data_label = lbl;
        h_formula_data_remaining_branches = ann;
        h_formula_data_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_one s c,c2)) pcond;
		h_formula_data_pos = pos})
  | HRel (r, args, pos) -> HRel (r, List.map (CP.e_apply_one s) args, pos)
  | HTrue -> f
  | HFalse -> f
  | HEmp -> f
  | Hole _ -> f    

(* normalization *)
(* normalizes ( \/ (EX v* . /\ ) ) * ( \/ (EX v* . /\ ) ) *)
and normalize_keep_flow (f1 : formula) (f2 : formula) flow_tr (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
        let eo1 = normalize_x o11 f2 pos in
        let eo2 = normalize_x o12 f2 pos in
		mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
		| Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
			  let eo1 = normalize_x f1 o21 pos in
			  let eo2 = normalize_x f1 o22 pos in
			  mkOr eo1 eo2 pos
		| _ -> begin
			let rf1 = rename_bound_vars f1 in
			let rf2 = rename_bound_vars f2 in
			let qvars1, base1 = split_quantifiers rf1 in
			let qvars2, base2 = split_quantifiers rf2 in
			let new_base = mkStar_combine base1 base2 flow_tr pos in
			let new_h, new_p, new_fl, new_t, new_a = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end

and normalize i (f1 : formula) (f2 : formula) (pos : loc) = 
  Debug.no_1_num i "normalize" (!print_formula) (!print_formula) (fun _ -> normalize_x f1 f2 pos) f1
	    
and normalize_x (f1 : formula) (f2 : formula) (pos : loc) = 
  normalize_keep_flow f1 f2 Flow_combine pos

(*LDK*)
and normalize_replace (f1 : formula) (f2 : formula) (pos : loc) = 
  Debug.no_2 "normalize_replace" !print_formula !print_formula !print_formula
      (fun _ _ -> normalize_replace_x f1 f2 pos) f1 f2

and normalize_replace_x (f1 : formula) (f2 : formula) (pos : loc) = 
  normalize_keep_flow f1 f2 Flow_replace pos

and normalize_combine_heap (f1 : formula) (f2 : h_formula) 
      = normalize_combine_star f1 (formula_of_heap f2 no_pos) no_pos

and normalize_combine (f1 : formula) (f2 : formula) (pos : loc) = normalize_combine_star f1 f2 pos

and normalize_combine_star_x (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
        let eo1 = normalize_combine_star_x o11 f2 pos in
        let eo2 = normalize_combine_star_x o12 f2 pos in
		mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
		| Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
			  let eo1 = normalize_combine_star_x f1 o21 pos in
			  let eo2 = normalize_combine_star_x f1 o22 pos in
			  mkOr eo1 eo2 pos
		| _ -> begin
			let rf1 = Gen.Profiling.no_1 "7_ren_bound" rename_bound_vars f1 in
			let rf2 = Gen.Profiling.no_1 "7_ren_bound" rename_bound_vars f2 in
			let qvars1, base1 = split_quantifiers rf1 in
			let qvars2, base2 = split_quantifiers rf2 in
			let new_base = Gen.Profiling.no_1 "6_mkstar" (mkStar_combine base1 base2 Flow_combine) pos in
			let new_h, new_p, new_fl, new_t, new_a = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end

and normalize_combine_star (f1 : formula) (f2 : formula) (pos : loc) = 
  let pr = !print_formula in
  Debug.no_2 "normalize_combine_star" pr pr pr 
      (fun _ _ -> Gen.Profiling.no_1 "10_norm_comb_st"(normalize_combine_star_x f1 f2) pos) f1 f2

and normalize_combine_conj (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
        let eo1 = normalize_combine_conj o11 f2 pos in
        let eo2 = normalize_combine_conj o12 f2 pos in
		mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
		| Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
			  let eo1 = normalize_combine_conj f1 o21 pos in
			  let eo2 = normalize_combine_conj f1 o22 pos in
			  mkOr eo1 eo2 pos
		| _ -> begin
			let rf1 = rename_bound_vars f1 in
			let rf2 = rename_bound_vars f2 in
			let qvars1, base1 = split_quantifiers rf1 in
			let qvars2, base2 = split_quantifiers rf2 in
			let new_base = mkConj_combine base1 base2 Flow_combine pos in
			let new_h, new_p, new_fl, new_t, new_a = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end

and normalize_combine_phase (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
        let eo1 = normalize_combine_phase o11 f2 pos in
        let eo2 = normalize_combine_phase o12 f2 pos in
		mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
		| Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
			  let eo1 = normalize_combine_phase f1 o21 pos in
			  let eo2 = normalize_combine_phase f1 o22 pos in
			  mkOr eo1 eo2 pos
		| _ -> begin
			let rf1 = rename_bound_vars f1 in
			let rf2 = rename_bound_vars f2 in
			let qvars1, base1 = split_quantifiers rf1 in
			let qvars2, base2 = split_quantifiers rf2 in
			let new_base = mkPhase_combine base1 base2 Flow_combine pos in
			let new_h, new_p, new_fl, new_t, new_a = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end
	    
(* -- 13.05.2008 *)
(* normalizes but only renames the bound variables of f1 that clash with variables from fv(f2) *)

and normalize_only_clash_rename (f1 : formula) (f2 : formula) (pos : loc) = 
  Debug.no_2 "normalize_only_clash_rename" (!print_formula) (!print_formula) (!print_formula) (fun _ _ -> normalize_only_clash_rename_x f1 f2 pos) f1 f2

and normalize_only_clash_rename_x (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
        let eo1 = normalize_only_clash_rename_x o11 f2 pos in
        let eo2 = normalize_only_clash_rename_x o12 f2 pos in
		mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
		| Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
			  let eo1 = normalize_only_clash_rename_x f1 o21 pos in
			  let eo2 = normalize_only_clash_rename_x f1 o22 pos in
			  mkOr eo1 eo2 pos
		| _ -> begin
			let rf1 = (fst (rename_clash_bound_vars f1 f2)) in
			let rf2 = (*rename_bound_vars*) f2 in
			let qvars1, base1 = split_quantifiers rf1 in
			let qvars2, base2 = split_quantifiers rf2 in
			let new_base = mkStar_combine base1 base2 Flow_combine pos in
			let new_h, new_p, new_fl, new_t, new_a = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end
        (* 13.05.2008 -- *)

(* split a conjunction into heap constraints, pure pointer constraints, *)
(* and Presburger constraints *)
and split_components (f: formula) =
  Debug.no_1 "split_components" !print_formula (fun _ -> "")
  split_components_x f 

and split_components_x (f : formula) = 
  if (isAnyConstFalse f) then (HFalse,(MCP.mkMFalse no_pos),(flow_formula_of_formula f),TypeFalse, [])
  else match f with
    | Base ({formula_base_heap = h; 
	  formula_base_pure = p; 
	  formula_base_flow =fl;
	  formula_base_and =a; (*TO CHECK: omit at the moment*)
	  formula_base_type = t}) -> (h, p(*, imm*), fl, t, a)
    | Exists ({formula_exists_heap = h; 
	  formula_exists_pure = p; 
	  formula_exists_flow = fl;
	  formula_exists_and = a; (*TO CHECK: omit at the moment*)
	  formula_exists_type = t}) -> (h, p(*, imm*), fl, t, a)
    | Or ({formula_or_pos = pos}) -> 
          Err.report_error {Err.error_loc = pos;Err.error_text = "split_components: don't expect OR"}
			 

and all_components (f:formula) = (*the above misses some *)
	if (isAnyConstFalse f) then ([],HFalse,(MCP.mkMFalse no_pos),TypeFalse,(flow_formula_of_formula f),None,[],  no_pos)
	else match f with
	 | Base b -> ([], b.formula_base_heap, b.formula_base_pure, b.formula_base_type, b.formula_base_flow, b.formula_base_label, b.formula_base_and, b.formula_base_pos)
	 | Exists e -> (e.formula_exists_qvars, e.formula_exists_heap, e.formula_exists_pure, e.formula_exists_type,
						e.formula_exists_flow, e.formula_exists_label, e.formula_exists_and, e.formula_exists_pos)
	 | Or ({formula_or_pos = pos}) ->  Err.report_error {Err.error_loc = pos;Err.error_text = "all_components: don't expect OR"}
			 
and split_quantifiers (f : formula) : (CP.spec_var list * formula) = match f with
  | Exists ({formula_exists_qvars = qvars; 
	formula_exists_heap =  h; 
	formula_exists_pure = p; 
	formula_exists_type = t;
	formula_exists_flow = fl;
	formula_exists_and = a;
	formula_exists_pos = pos}) -> 
        (qvars, mkBase h p t fl a pos)
  | Base _ -> ([], f)
  | _ -> failwith ("split_quantifiers: invalid argument")

and add_quantifiers (qvars : CP.spec_var list) (f : formula) : formula = match f with
  | Base ({formula_base_heap = h; 
	formula_base_pure = p; 
	formula_base_type = t;
	formula_base_flow = fl;
        formula_base_and = a;
        formula_base_pos = pos}) -> mkExists qvars h p t fl a pos
  | Exists ({formula_exists_qvars = qvs; 
	formula_exists_heap = h; 
	formula_exists_pure = p; 
	formula_exists_type = t;
	formula_exists_flow = fl;
    formula_exists_and = a;
	formula_exists_pos = pos}) -> 
	    let new_qvars = CP.remove_dups_svl (qvs @ qvars) in
		mkExists new_qvars h p t fl a pos
  | _ -> failwith ("add_quantifiers: invalid argument")

(* 19.05.2008 *)
and remove_quantifiers (qvars : CP.spec_var list) (f : formula) : formula = match f with
  | Base _ -> f
  | Exists ({formula_exists_qvars = qvs; 
	formula_exists_heap = h; 
	formula_exists_pure = p; 
	formula_exists_type = t;
	formula_exists_flow = fl;
    formula_exists_and = a;
	formula_exists_pos = pos}) -> 
	    let new_qvars = (List.filter (fun x -> not(List.exists (fun y -> CP.eq_spec_var x y) qvars)) qvs) in
	  	if (List.length new_qvars == 0) then mkBase h p t fl a pos
	  	else mkExists new_qvars h p t fl a pos
  | _ -> failwith ("add_quantifiers: invalid argument")
        (* 19.05.2008 *)

and push_struc_exists (qvars : CP.spec_var list) (f : struc_formula) = match f with
	| EBase b -> EBase {b with formula_struc_exists = b.formula_struc_exists @ qvars}
	| ECase b -> ECase {b with formula_case_exists = b.formula_case_exists @ qvars}
	| EAssume (x,b,y) -> EAssume (x,(push_exists qvars b),y)
	| EInfer b -> EInfer b
	| EOr b -> EOr {b with formula_struc_or_f1 = push_struc_exists qvars b.formula_struc_or_f1;formula_struc_or_f2 = push_struc_exists qvars b.formula_struc_or_f2;}
	| EList b -> EList (map_l_snd (push_struc_exists qvars) b)

and push_exists (qvars : CP.spec_var list) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
	    let new_f1 = push_exists qvars f1 in
	    let new_f2 = push_exists qvars f2 in
	    let resform = mkOr new_f1 new_f2 pos in
		resform
  | _ -> add_quantifiers qvars f

(* 19.05.2008 *)
and pop_exists (qvars : CP.spec_var list) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
	    let new_f1 = pop_exists qvars f1 in
	    let new_f2 = pop_exists qvars f2 in
	    let resform = mkOr new_f1 new_f2 pos in
		resform
  | _ -> remove_quantifiers qvars f
        (* 19.05.2008 *)

and formula_of_disjuncts (f:formula list) : formula=
  match f with
    | [] -> (mkTrue (mkTrueFlow()) no_pos)
    | x::xs -> List.fold_left (fun a c-> mkOr a c no_pos) x xs

and rename_struc_bound_vars (f:struc_formula):struc_formula = match f with
	| ECase b-> 
		  let sst3 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_case_exists in
		  let f = ECase {b with formula_case_exists = (snd (List.split sst3));
			  formula_case_branches = List.map (fun (c1,c2)-> ((Cpure.rename_top_level_bound_vars c1),(rename_struc_bound_vars c2))) b.formula_case_branches;} in
		  subst_struc sst3 f
	| EBase b-> 
		  let sst1 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_struc_explicit_inst in
		  let sst2 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_struc_implicit_inst in
		  let sst3 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_struc_exists in
		  let sst = sst1@sst2@sst3 in
		  let f = EBase {b with 
			  formula_struc_implicit_inst = (snd (List.split sst2));
			  formula_struc_explicit_inst = (snd (List.split sst1));
			  formula_struc_exists = (snd (List.split sst3));
			  formula_struc_base = rename_bound_vars b.formula_struc_base;
			  formula_struc_continuation = map_opt rename_struc_bound_vars b.formula_struc_continuation; }in
		  subst_struc sst f
	| EAssume (x,b,y)-> EAssume (x,(rename_bound_vars b),y)
	| EInfer b -> EInfer { b with formula_inf_continuation = rename_struc_bound_vars b.formula_inf_continuation;}
	| EOr b -> EOr {b with 
			formula_struc_or_f1 = rename_struc_bound_vars b.formula_struc_or_f1; 
			formula_struc_or_f2 = rename_struc_bound_vars b.formula_struc_or_f2;}
	| EList b -> EList (map_l_snd rename_struc_bound_vars b)


and rename_bound_vars (f : formula) =
  let pr= !print_formula in
  Debug.no_1 "rename_bound_vars" pr pr
      (fun _ -> rename_bound_vars_x f) f

and rename_bound_vars_x (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	    let rf1 = rename_bound_vars_x f1 in
	    let rf2 = rename_bound_vars_x f2 in
	    let resform = mkOr rf1 rf2 pos in
		resform
  | Base _ -> f
  | Exists _ ->
	    let qvars, base_f = split_quantifiers f in
	    let new_qvars = CP.fresh_spec_vars qvars in
	    (*--- 09.05.2000 *)
		(*let _ = (print_string ("\n[cformula.ml, line 519]: fresh name = " ^ (string_of_spec_var_list new_qvars) ^ "!!!!!!!!!!!\n")) in*)
		(*09.05.2000 ---*)
	    let rho = List.combine qvars new_qvars in
	    let new_base_f = subst_varperm rho base_f in (*TO CHECK*)
	    let resform = add_quantifiers new_qvars new_base_f in
		resform

and propagate_perm_formula (f : formula) (permvar:cperm_var) : formula =
  Debug.no_2 "propagate_perm_formula"
      !print_formula
      !print_spec_var
      !print_formula
      propagate_perm_formula_x f permvar

(*LDK: propagate permvar into view formula during UNFOLDING*)
and propagate_perm_formula_x (f : formula) (permvar:cperm_var) : formula = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	    let rf1 = propagate_perm_formula_x f1 permvar in
	    let rf2 = propagate_perm_formula_x f2 permvar in
	    let resform = mkOr rf1 rf2 pos in
		resform
  | Base f1 ->
        let f1_heap,vars = propagate_perm_h_formula f1.formula_base_heap permvar in
        let base_p = f1.formula_base_pure in
        let mk_eq v = mkEq_cperm () v permvar no_pos in
        let mk_eqs = List.map mk_eq vars in
        let mk_BForm (b:CP.b_formula): CP.formula = CP.BForm (b,None) in
        let mk_eqs = List.map mk_BForm mk_eqs in
        let perm_p = List.fold_left (fun res v -> CP.mkAnd v res no_pos) (CP.mkTrue no_pos) mk_eqs in
        let perm_p = MCP.OnePF perm_p in
        let base_p = add_mix_formula_to_mix_formula perm_p base_p in
        Base({f1 with formula_base_heap = f1_heap; formula_base_pure = base_p})
  | Exists f1 ->
        let f1_heap,vars = propagate_perm_h_formula f1.formula_exists_heap permvar in
        let base_p = f1.formula_exists_pure in
        let mk_eq v = mkEq_cperm () v permvar no_pos in
        let mk_eqs = List.map mk_eq vars in
        let mk_BForm (b:CP.b_formula): CP.formula = CP.BForm (b,None) in
        let mk_eqs = List.map mk_BForm mk_eqs in
        let perm_p = List.fold_left (fun res v -> CP.mkAnd v res no_pos) (CP.mkTrue no_pos) mk_eqs in
        let perm_p = MCP.OnePF perm_p in
        let base_p = add_mix_formula_to_mix_formula perm_p base_p in
        Exists({f1 with 
            formula_exists_qvars = List.append vars f1.formula_exists_qvars;
            formula_exists_heap = f1_heap; 
            formula_exists_pure = base_p})

(*Spec_var list to creat pure constraints: freshvar = permvar*)
and propagate_perm_h_formula (f : h_formula) (permvar:cperm_var) : h_formula * (CP.spec_var list) = 
  match f with
    | ViewNode f1 -> 
        let fresh_var = fresh_cperm_var () permvar in
        let vn = ViewNode({f1 with h_formula_view_perm = Some fresh_var}) in
        (vn,[fresh_var])
    | DataNode f1 -> 
        let fresh_var = fresh_cperm_var () permvar in
        let dn = DataNode({f1 with h_formula_data_perm = Some fresh_var}) in
        (dn,[fresh_var])
    | Star f1 ->
	      let h1,xs1 = propagate_perm_h_formula f1.h_formula_star_h1 permvar in
	      let h2,xs2 = propagate_perm_h_formula f1.h_formula_star_h2 permvar in
	      let star = mkStarH h1 h2 f1.h_formula_star_pos in
          let xs = List.append xs1 xs2 in
          (star,xs)
    | Conj f1 ->
	      let h1,xs1 = propagate_perm_h_formula f1.h_formula_conj_h1 permvar in
	      let h2,xs2 = propagate_perm_h_formula f1.h_formula_conj_h2 permvar in
          let conj = mkConjH h1 h2 f1.h_formula_conj_pos in
          let xs = List.append xs1 xs2 in
          (conj,xs)

    | Phase f1 ->
	      let h1,xs1 = propagate_perm_h_formula f1.h_formula_phase_rd permvar in
	      let h2,xs2 = propagate_perm_h_formula f1.h_formula_phase_rw permvar in
          let phase = mkPhaseH h1 h2 f1.h_formula_phase_pos in
          let xs = List.append xs1 xs2 in
          (phase,xs)
    | _ -> (f,[])

(* -- 13.05.2008 *)
(* rename only those bound vars of f1 which clash with fv(f2) *)
(* return the new formula and the list of fresh names *)
and rename_struc_clash_bound_vars (f1 : struc_formula) (f2 : formula) : struc_formula  =  match f1 with
	| EAssume (x,b,y)-> EAssume (x,(fst(rename_clash_bound_vars b f2)),y)
	| ECase b ->  
		  let r1 = List.map (fun (c1,c2) -> (c1,(rename_struc_clash_bound_vars c2 f2))) b.formula_case_branches in
		  let new_exs = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_case_exists in
		  let rho = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2))) new_exs) in
		  ECase {formula_case_exists = (snd (List.split new_exs));
		  formula_case_branches = List.map (fun (c1,c2)-> ((Cpure.subst rho c1),(subst_struc rho c2))) r1;
		  formula_case_pos = b.formula_case_pos}
	| EBase b -> 
		  let new_imp = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_struc_implicit_inst in
		  let new_exp = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_struc_explicit_inst in
		  let new_exs = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_struc_exists in
		  (* fresh_qvars contains only the freshly generated names *)
		  let rho_imp = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2)))  new_imp) in
		  let rho_exp = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2)))  new_exp) in
		  let rho_exs = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2)))  new_exs) in
		  let rho = rho_imp@rho_exp@rho_exs in
		  EBase {b with 
			  formula_struc_implicit_inst = (snd (List.split new_imp));
			  formula_struc_explicit_inst = (snd (List.split new_exp));
			  formula_struc_exists = (snd (List.split new_exs));
			  formula_struc_base = subst rho (fst ( rename_clash_bound_vars b.formula_struc_base f2 ));
			  formula_struc_continuation = map_opt (fun c-> rename_struc_clash_bound_vars (subst_struc rho c) f2) b.formula_struc_continuation;
		  }
	| EInfer b -> EInfer {b with formula_inf_continuation = rename_struc_clash_bound_vars b.formula_inf_continuation f2}
	| EOr b -> EOr {b with 
					formula_struc_or_f1 = rename_struc_clash_bound_vars b.formula_struc_or_f1 f2; 
					formula_struc_or_f2 = rename_struc_clash_bound_vars b.formula_struc_or_f2 f2;}
	| EList b -> EList (map_l_snd (fun c->rename_struc_clash_bound_vars c f2) b)
  

and rename_clash_bound_vars (f1 : formula) (f2 : formula) : (formula * CP.spec_var list) = match f1 with
  | Or ({formula_or_f1 = or1; formula_or_f2 = or2; formula_or_pos = pos}) ->
	    let (rf1, fvar1) = (rename_clash_bound_vars or1 f2) in
	    let (rf2, fvar2) = (rename_clash_bound_vars or2 f2) in
	    let resform = mkOr rf1 rf2 pos in
		(resform, fvar1@fvar2)
  | Base _ -> (f1, [])
  | Exists _ ->
	    let qvars, base_f = split_quantifiers f1 in
	    let new_qvars = (List.map (fun v -> (if (check_name_clash v f2) then (CP.fresh_spec_var v) else v)) qvars) in
	    (* fresh_qvars contains only the freshly generated names *)
	    let fresh_qvars = (List.filter (fun v1 -> (not (List.exists (fun v2 -> CP.eq_spec_var v1 v2) qvars)))  new_qvars) in
	    let rho = List.combine qvars new_qvars in
	    let new_base_f = subst rho base_f in
	    let resform = add_quantifiers new_qvars new_base_f in
		(resform, fresh_qvars)

and check_name_clash (v : CP.spec_var) (f : formula) : bool =
  let spec_vars = fv f in
  (*let _ = print_string ("[cformula.ml, line 467]: Spec vars: " ^ (string_of_spec_var_list spec_vars) ^ "\n") in*)
  (List.exists (fun c -> (CP.eq_spec_var c v)) spec_vars)
      (* 13.05.2008 -- *)

(* composition operator: it suffices to define composition in terms of  *)
(* the * operator, as the & operator is just a special case when one of *)
(* the term is pure                                                     *)

(* x+x' o[x'->fx] x'=x+1 --> x+fx & x'=fx+1 *)

(*transform history also*)
and compose_formula_new (delta : formula) (phi : formula) (x : CP.spec_var list) flow_tr history (pos : loc) =
  let rs = CP.fresh_spec_vars x in
  (*--- 09.05.2000 *)
  (*let _ = (print_string ("\n[cformula.ml, line 533]: fresh name = " ^ (string_of_spec_var_list rs) ^ "!!!!!!!!!!!\n")) in*)
  (*09.05.2000 ---*)
  let rho1 = List.combine (List.map CP.to_unprimed x) rs in
  let rho2 = List.combine (List.map CP.to_primed x) rs in
  let new_delta = subst rho2 delta in
  let new_phi = subst rho1 phi in
  let new_history = List.map (h_subst rho2) history in
  let new_f = normalize_keep_flow new_delta new_phi flow_tr pos in
  let _ = must_consistent_formula "compose_formula 1" new_f in
  let resform = push_exists rs new_f in
  let _ = must_consistent_formula "compose_formula 2" resform in
  resform,new_history

and compose_formula_x (delta : formula) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) =
  let rs = CP.fresh_spec_vars x in
  (*--- 09.05.2000 *)
  (*let _ = (print_string ("\n[cformula.ml, line 533]: fresh name = " ^ (string_of_spec_var_list rs) ^ "!!!!!!!!!!!\n")) in*)
  (*09.05.2000 ---*)
  let rho1 = List.combine (List.map CP.to_unprimed x) rs in
  let rho2 = List.combine (List.map CP.to_primed x) rs in
  let new_delta = subst rho2 delta in
  let new_phi = subst rho1 phi in
  let new_f = normalize_keep_flow new_delta new_phi flow_tr pos in
  let _ = must_consistent_formula "compose_formula 1" new_f in
  let resform = push_exists rs new_f in
  let _ = must_consistent_formula "compose_formula 2" resform in
  resform

and compose_formula (delta : formula) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) =
  let pr1 = !print_formula in
  let pr3 = !print_svl in
   Debug.no_3 "compose_formula" pr1 pr1 pr3 pr1 (fun _ _ _ -> compose_formula_x delta phi x flow_tr pos) delta phi x
	  
and view_node_types (f:formula):ident list = 
  let rec helper (f:h_formula):ident list =  match f with
	| Star b -> Gen.BList.remove_dups_eq (=) ((helper b.h_formula_star_h1)@(helper b.h_formula_star_h2))
	| ViewNode b -> [b.h_formula_view_name]
	| _ -> [] in
  match f with
	| Or b-> Gen.BList.remove_dups_eq (=) ((view_node_types b.formula_or_f1) @ (view_node_types b.formula_or_f2))
	| Base b -> helper b.formula_base_heap
	| Exists b -> helper b.formula_exists_heap

(*
  Other utilities.
*)

and get_var_type_x v (f: formula): (typ * bool) = 
  let fv_list = fv f in
  let res_list = CP.remove_dups_svl (List.filter (fun c-> ((String.compare v (CP.name_of_spec_var c))==0)) fv_list) in
  match List.length res_list with
	| 0 -> (Void,false)
	| 1 -> (CP.type_of_spec_var (List.hd res_list),true)
	| _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = "could not find a coherent "^v^" type"}

and get_var_type v (f: formula): (typ * bool) = 
  let pr2 = pr_pair string_of_typ string_of_bool in
  Debug.no_2 "get_var_type" 
      pr_id !print_formula pr2
      (fun _ _ -> get_var_type_x v f) v f


and get_result_type (f: formula): (typ * bool) = get_var_type res_name f

and get_exc_result_type (f: formula): (typ * bool) = get_var_type eres_name f
  
and disj_count (f0 : formula) = match f0 with
  | Or ({formula_or_f1 = f1;
	formula_or_f2 = f2}) ->
	    let c1 = disj_count f1 in
	    let c2 = disj_count f2 in
		1 + c1 + c2

  | _ -> 1

(*=========for sa==========*)
let is_HRel hf=
  match hf with
    | HRel _ -> true
    | _ -> false

let get_HRel hf=
  match hf with
    | HRel (hp, eargs, _ ) -> Some (hp, List.concat (List.map CP.afv eargs))
    | _ -> None

let get_HRels hf=
  let rec helper h=
    match h with
      | HRel (hp, eargs, _ ) -> [(hp, List.concat (List.map CP.afv eargs))]
      | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2} 
      | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2} 
      | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2} 
          -> (helper h1)@(helper h2)
      | _ -> []
  in
  helper hf

let rec check_eq_hrel_node  (rl1, args1 ,_)  (rl2, args2,_)=
    let rec helper l1 l2=
      match l1,l2 with
        | [],[] -> true
        | v1::vs1,v2::vs2 ->
            if CP.eq_spec_var v1 v2 then helper vs1 vs2
            else false
        | _ -> false
    in
    (*hp1 = hp2 and args1 = arg2*)
    let svs1 = List.concat (List.map CP.afv args1) in
    let svs2 = List.concat (List.map CP.afv args2) in
    (CP.eq_spec_var rl1 rl2) && (helper svs1 svs2)

and h_node_list (f: h_formula): CP.spec_var list = match f with
  | DataNode {h_formula_data_node = c}
  | ViewNode {h_formula_view_node = c} -> [c]
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2} 
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2} 
  | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2} 
  -> (h_node_list h1)@(h_node_list h2)
  | _ -> []

and get_hnodes (f: h_formula) = match f with
  | DataNode _ -> [f]
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2} 
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2} 
  | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2} 
  -> (get_hnodes h1)@(get_hnodes h2)
  | _ -> []

and get_hp_rel_formula (f:formula) =
  match f with 
    | Base  ({formula_base_heap = h1;
		formula_base_pure = p1})
    | Exists ({formula_exists_heap = h1;
		 formula_exists_pure = p1}) -> (
      get_hp_rel_h_formula h1
    )
    | Or orf  ->
        let a1,b1,c1 = get_hp_rel_formula orf.formula_or_f1 in
        let a2,b2,c2 = get_hp_rel_formula orf.formula_or_f2 in
        (a1@a2,b1@b2,c1@c2)

and get_hp_rel_bformula bf=
  get_hp_rel_h_formula bf.formula_base_heap

(*data nodes, view nodes, rel*)
and get_hp_rel_h_formula hf=
  match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2} ->
        let hd1, hv1,hr1 = get_hp_rel_h_formula hf1 in
        let hd2,hv2,hr2 = (get_hp_rel_h_formula hf2) in
        (hd1@hd2,hv1@hv2,hr1@hr2)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;} ->
        let hd1,hv1,hr1 = (get_hp_rel_h_formula hf1)in
        let hd2,hv2,hr2 = (get_hp_rel_h_formula hf2) in
        (hd1@hd2,hv1@hv2,hr1@hr2)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
        let hd1,hv1,hr1 = (get_hp_rel_h_formula hf1) in
        let hd2,hv2,hr2 = (get_hp_rel_h_formula hf2) in
        (hd1@hd2,hv1@hv2,hr1@hr2)
    | DataNode hd -> ([hd],[],[])
    | ViewNode hv -> ([],[hv],[])
    | HRel hr -> ([],[],[hr])
    | Hole _
    | HTrue
    | HFalse
    | HEmp -> ([],[],[])


and get_hp_rel_name_formula (f: formula) =
  match f with
    | Base  ({formula_base_heap = h1;
		      formula_base_pure = p1})
    | Exists ({ formula_exists_heap = h1;
		        formula_exists_pure = p1}) -> get_hp_rel_name_h_formula h1
    | Or orf  -> (get_hp_rel_name_formula orf.formula_or_f1)@
        (get_hp_rel_name_formula orf.formula_or_f2)

and get_hp_rel_name_bformula bf=
  get_hp_rel_name_h_formula bf.formula_base_heap

and get_hp_rel_name_h_formula hf=
  match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2} ->
        (get_hp_rel_name_h_formula hf1)@(get_hp_rel_name_h_formula hf2)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;} ->
        (get_hp_rel_name_h_formula hf1)@(get_hp_rel_name_h_formula hf2)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
        (get_hp_rel_name_h_formula hf1)@(get_hp_rel_name_h_formula hf2)
    | DataNode hd -> []
    | ViewNode hv -> []
    | HRel (rl,_,_) -> [rl]
    | Hole _
    | HTrue
    | HFalse
    | HEmp -> []

and get_hp_rel_vars_bformula bf=
  get_hp_rel_vars_h_formula bf.formula_base_heap

and get_hp_rel_vars_h_formula_x hf=
  match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2} ->
        (get_hp_rel_vars_h_formula_x hf1)@(get_hp_rel_vars_h_formula_x hf2)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;} ->
        (get_hp_rel_vars_h_formula_x hf1)@(get_hp_rel_vars_h_formula_x hf2)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
        (get_hp_rel_vars_h_formula_x hf1)@(get_hp_rel_vars_h_formula_x hf2)
    | DataNode hd -> []
    | ViewNode hv -> []
    | HRel (rl,args,_) -> [rl]@(CP.remove_dups_svl (List.fold_left List.append [] (List.map CP.afv args)))
    | Hole _
    | HTrue
    | HFalse
    | HEmp -> []

and get_hp_rel_vars_h_formula hf=
  let pr1= !print_h_formula in
  let pr2 = !print_svl in
  Debug.no_1 "get_hp_rel_vars_h_formula" pr1 pr2
      ( fun _ -> get_hp_rel_vars_h_formula_x hf) hf

and filter_irr_hp_lhs_bf bf relevant_vars =
   {bf with formula_base_heap = filter_irr_hp_lhs_hf bf.formula_base_heap relevant_vars;}

and filter_irr_hp_lhs_hf hf relevant_vars=
  match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
        let n_hf1 = filter_irr_hp_lhs_hf hf1 relevant_vars in
        let n_hf2 = filter_irr_hp_lhs_hf hf2 relevant_vars in
        (match n_hf1,n_hf2 with
          | (HEmp,HEmp) -> HEmp
          | (HEmp,_) -> n_hf2
          | (_,HEmp) -> n_hf1
          | _ -> Star {h_formula_star_h1 = n_hf1;
                       h_formula_star_h2 = n_hf2;
                       h_formula_star_pos = pos}
        )
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
        let n_hf1 = filter_irr_hp_lhs_hf hf1 relevant_vars in
        let n_hf2 = filter_irr_hp_lhs_hf hf2 relevant_vars in
        Conj { h_formula_conj_h1 = n_hf1;
               h_formula_conj_h2 = n_hf2;
               h_formula_conj_pos = pos}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
        let n_hf1 = filter_irr_hp_lhs_hf hf1 relevant_vars in
        let n_hf2 = filter_irr_hp_lhs_hf hf2 relevant_vars in
        Phase { h_formula_phase_rd = n_hf1;
              h_formula_phase_rw = n_hf2;
              h_formula_phase_pos = pos} 
    | DataNode hd -> hf
    | ViewNode hv -> hf
    | HRel (_, args, _) -> let args_vars = (CP.remove_dups_svl (List.fold_left List.append [] (List.map CP.afv args))) in
                           if  CP.intersect args_vars relevant_vars = [] then HEmp
                           else hf
    | Hole _
    | HTrue
    | HFalse
    | HEmp -> hf

and filter_vars_hf hf rvs=
  match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
        let n_hf1 =  filter_vars_hf hf1 rvs in
        let n_hf2 = filter_vars_hf hf2 rvs in
        (match n_hf1,n_hf2 with
          | (HTrue,HTrue) -> HTrue
          | (HTrue,_) -> n_hf2
          | (_,HTrue) -> n_hf1
          | _ -> Star {h_formula_star_h1 = n_hf1;
                       h_formula_star_h2 = n_hf2;
                       h_formula_star_pos = pos}
        )
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
        let n_hf1 = filter_vars_hf hf1 rvs in
        let n_hf2 = filter_vars_hf hf2 rvs in
        Conj { h_formula_conj_h1 = n_hf1;
               h_formula_conj_h2 = n_hf2;
               h_formula_conj_pos = pos}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
        let n_hf1 = filter_vars_hf hf1 rvs in
        let n_hf2 = filter_vars_hf hf2 rvs in
        Phase { h_formula_phase_rd = n_hf1;
              h_formula_phase_rw = n_hf2;
              h_formula_phase_pos = pos} 
    | DataNode hd -> if CP.mem_svl hd.h_formula_data_node rvs then hf
        else HTrue
    | ViewNode hv -> if CP.mem_svl hv.h_formula_view_node rvs then hf
        else HTrue
    | HRel _ -> hf
    | Hole _
    | HTrue
    | HFalse
    | HEmp -> hf

(*drop HRel in the set hp_names and return corresponding subst of their args*)
and drop_hrel_f f hp_names=
  match f with
    | Base fb -> let nfb,argsl = drop_hrel_hf fb.formula_base_heap hp_names in
        (Base {fb with formula_base_heap =  nfb;}, argsl)
    | Or orf -> let nf1,argsl1 =  drop_hrel_f orf.formula_or_f1 hp_names in
                let nf2,argsl2 =  drop_hrel_f orf.formula_or_f2 hp_names in
       ( Or {orf with formula_or_f1 = nf1;
                formula_or_f2 = nf2;}, argsl1@argsl2)
    | Exists fe -> let nfe,argsl = drop_hrel_hf fe.formula_exists_heap hp_names in
        (Exists {fe with formula_exists_heap = nfe ;}, argsl)

and drop_hrel_hf hf hp_names=
  match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
        let n_hf1, argsl1 = drop_hrel_hf hf1 hp_names in
        let n_hf2, argsl2 = drop_hrel_hf hf2 hp_names in
        let newf =
        (match n_hf1,n_hf2 with
          | (HEmp,HEmp) -> HEmp
          | (HEmp,_) -> n_hf2
          | (_,HEmp) -> n_hf1
          | _ -> (Star {h_formula_star_h1 = n_hf1;
                       h_formula_star_h2 = n_hf2;
                       h_formula_star_pos = pos})
        ) in
        (newf, argsl1@argsl2)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
        let n_hf1,argsl1 = drop_hrel_hf hf1 hp_names in
        let n_hf2,argsl2 = drop_hrel_hf hf2 hp_names in
        (Conj { h_formula_conj_h1 = n_hf1;
               h_formula_conj_h2 = n_hf2;
               h_formula_conj_pos = pos}, argsl1@argsl2)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
        let n_hf1,argsl1 = drop_hrel_hf hf1 hp_names in
        let n_hf2,argsl2 = drop_hrel_hf hf2 hp_names in
        (Phase { h_formula_phase_rd = n_hf1;
              h_formula_phase_rw = n_hf2;
              h_formula_phase_pos = pos},argsl1@argsl2) 
    | DataNode hd -> (hf,[])
    | ViewNode hv -> (hf,[])
    | HRel (id,args,_) -> if CP.mem_svl id hp_names then (HEmp, [args])
        else (hf,[])
    | Hole _
    | HTrue
    | HFalse
    | HEmp -> (hf,[])

and drop_data_view_hrel_nodes f fn_data_select fn_view_select fn_hrel_select dnodes vnodes relnodes=
  match f with
    | Base fb ->
        let new_hf = drop_data_view_hrel_nodes_hf
          fb.formula_base_heap fn_data_select fn_view_select fn_hrel_select
          dnodes vnodes relnodes in
        (*assume keep vars = dnodes*)
        let new_p = CP.filter_var (MCP.pure_of_mix fb.formula_base_pure) dnodes in
        Base {fb with formula_base_heap = new_hf;
            formula_base_pure = MCP.mix_of_pure new_p;
                }
    | _ -> report_error no_pos "cformula.drop_data_view_hrel_nodes"

and drop_data_view_hrel_nodes_fb fb fn_data_select fn_view_select fn_hrel_select matched_data_nodes matched_view_nodes matched_hrel_nodes keep_pure_vars=
  let new_hf = drop_data_view_hrel_nodes_hf
          fb.formula_base_heap fn_data_select fn_view_select fn_hrel_select
          matched_data_nodes matched_view_nodes matched_hrel_nodes in
   (*assume keep vars = dnodes*)
  let new_p = CP.filter_var (MCP.pure_of_mix fb.formula_base_pure) keep_pure_vars in
  {fb with formula_base_heap = new_hf;
      formula_base_pure = MCP.mix_of_pure new_p;}

and drop_data_view_hrel_nodes_hf hf fn_data_select fn_view_select fn_hrel_select
      data_nodes view_nodes hrel_nodes=
  match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
        let n_hf1 = drop_data_view_hrel_nodes_hf hf1 fn_data_select fn_view_select fn_hrel_select data_nodes view_nodes hrel_nodes in
        let n_hf2 = drop_data_view_hrel_nodes_hf hf2 fn_data_select fn_view_select fn_hrel_select data_nodes view_nodes hrel_nodes in
        Debug.ninfo_hprint (add_str "nhf1: " !print_h_formula) n_hf1 no_pos;
        Debug.ninfo_hprint (add_str "nhf2: " !print_h_formula) n_hf2 no_pos;
        let res=
        if (n_hf1 = HEmp) then n_hf2
        else if (n_hf2 = HEmp) then n_hf1
        else
          Star {h_formula_star_h1 = n_hf1;
                h_formula_star_h2 = n_hf2;
                h_formula_star_pos = pos}
        in
        Debug.ninfo_hprint (add_str "nhf1*nhf2: " !print_h_formula) res no_pos;
        res
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
        let n_hf1 = drop_data_view_hrel_nodes_hf hf1 fn_data_select fn_view_select fn_hrel_select data_nodes view_nodes hrel_nodes in
        let n_hf2 = drop_data_view_hrel_nodes_hf hf2 fn_data_select fn_view_select fn_hrel_select data_nodes view_nodes hrel_nodes in
        Conj { h_formula_conj_h1 = n_hf1;
               h_formula_conj_h2 = n_hf2;
               h_formula_conj_pos = pos}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
        let n_hf1 = drop_data_view_hrel_nodes_hf hf1 fn_data_select fn_view_select fn_hrel_select data_nodes view_nodes hrel_nodes in
        let n_hf2 = drop_data_view_hrel_nodes_hf hf2 fn_data_select fn_view_select fn_hrel_select data_nodes view_nodes hrel_nodes in
        Phase { h_formula_phase_rd = n_hf1;
              h_formula_phase_rw = n_hf2;
              h_formula_phase_pos = pos}
    | DataNode hd -> if fn_data_select hd data_nodes then HEmp
        else hf
    | ViewNode hv -> if fn_view_select hv view_nodes then HEmp
        else hf
    | HRel (id,_,_) ->
        Debug.ninfo_hprint (add_str "HRel: " !CP.print_sv) id no_pos;
        if (*CP.mem_svl*)fn_hrel_select id hrel_nodes then HEmp
        else hf
    | Hole _
    | HTrue
    | HFalse
    | HEmp -> hf

and mkAnd_f_hf f hf pos=
  match f with
    | Base fb -> Base (mkAnd_fb_hf fb hf pos)
    | Or orf -> Or {orf with formula_or_f1 = mkAnd_f_hf orf.formula_or_f1 hf pos;
                formula_or_f2 = mkAnd_f_hf orf.formula_or_f2 hf pos;}
    | Exists fe ->
        let new_hf = Star { h_formula_star_h1 = fe.formula_exists_heap;
                            h_formula_star_h2 = hf;
                            h_formula_star_pos = pos
                          }
        in
        Exists {fe with formula_exists_heap =  new_hf;}

and mkAnd_fb_hf fb hf pos=
  let new_hf = Star { h_formula_star_h1 = fb.formula_base_heap ;
                         h_formula_star_h2 = hf;
                         h_formula_star_pos = pos
  } in
  {fb with formula_base_heap = new_hf}

let rec subst_hrel_f f hprel_subst=
  match f with
    | Base fb -> Base {fb with formula_base_heap =  subst_hrel_hf fb.formula_base_heap hprel_subst;}
    | Or orf -> Or {orf with formula_or_f1 = subst_hrel_f orf.formula_or_f1 hprel_subst;
                formula_or_f2 = subst_hrel_f orf.formula_or_f2 hprel_subst;}
    | Exists fe -> Exists {fe with formula_exists_heap =  subst_hrel_hf fe.formula_exists_heap hprel_subst;}

and subst_hrel_hf hf hprel_subst=
  let helper (HRel (id,el,p)) (HRel (id1,el1,_), hf)=
    if id == id1 then
      (*should specvar subst*)
      let svl1 = (List.fold_left List.append [] (List.map CP.afv el)) in
      let svl2 = (List.fold_left List.append [] (List.map CP.afv el1)) in
      let f = h_subst (List.combine svl2 svl1) hf in
      (true, f)
    else (false, HRel (id,el,p))
  in
  let rec find_and_subst (HRel (id,el,p)) subst =
    (* List.fold_left helper (HRel (id,el,p)) subst *)
    match subst with
      | [] -> (HRel (id,el,p))
      | (HRel (id1,el1,p1), hf)::ss ->
          let stop,f = helper (HRel (id,el,p)) (HRel (id1,el1,p1), hf) in
          if stop then f
          else find_and_subst (HRel (id,el,p)) ss
      | _ -> report_error no_pos "cformula.find_and_subst"
  in
  match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
        let n_hf1 = subst_hrel_hf hf1 hprel_subst in
        let n_hf2 = subst_hrel_hf hf2 hprel_subst in
        Star {h_formula_star_h1 = n_hf1;
              h_formula_star_h2 = n_hf2;
              h_formula_star_pos = pos}
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
        let n_hf1 = subst_hrel_hf hf1 hprel_subst in
        let n_hf2 = subst_hrel_hf hf2 hprel_subst in
        Conj { h_formula_conj_h1 = n_hf1;
               h_formula_conj_h2 = n_hf2;
               h_formula_conj_pos = pos}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
        let n_hf1 = subst_hrel_hf hf1 hprel_subst in
        let n_hf2 = subst_hrel_hf hf2 hprel_subst in
        Phase { h_formula_phase_rd = n_hf1;
              h_formula_phase_rw = n_hf2;
              h_formula_phase_pos = pos}
    | DataNode hd -> hf
    | ViewNode hv -> hf
    | HRel _ -> find_and_subst hf hprel_subst
    | Hole _
    | HTrue
    | HFalse
    | HEmp -> hf


(*end for sa*)
 (* context functions *)

(*type formula_cache_no = int

type formula_cache_no_list = formula_cache_no list*)
type formula_trace = string list

type list_formula_trace = formula_trace list

type entail_state = {
  es_formula : formula; (* can be any formula ; 
    !!!!!  make sure that for each change to this formula the es_cache_no_list is update apropriatedly*)
  es_heap : h_formula; (* consumed nodes *)
  es_history : h_formula list; (* for sa *)
  es_evars : CP.spec_var list; (* existential variables on RHS *)

  (* WN : What is es_pure for? *)
    (*  It is added into the residue in
the method "heap_entail_empty_rhs_heap" but only when we do folding. It
is the pure constraints of the RHS when there is no heap. This es_pure
will be split into to_ante and to_conseq when ~Sprocess_fold_result~T. I
think it is used to instantiate when folding.
    *)
  es_pure : MCP.mix_formula;

  (*used by universal LEMMAS for instantiation? *)
  es_ivars : CP.spec_var list; 
    (* ivars are the variables to be instantiated (for the universal lemma application)  *)
  (* es_expl_vars : CP.spec_var list; (\* vars to be explicit instantiated *\) *)
  es_ante_evars : CP.spec_var list;
  (* es_must_match : bool; *)
  (*used by late instantiation*)
  es_gen_expl_vars: CP.spec_var list; (* explicit instantiation var*)
  es_gen_impl_vars: CP.spec_var list; (* implicit instantiation var*)

  (* to indicate if unsat check has been done for current state *)
  es_unsat_flag : bool; (* true - unsat already performed; false - requires unsat test *)
  es_pp_subst : (CP.spec_var * CP.spec_var) list;
  es_arith_subst : (CP.spec_var * CP.exp) list;
  es_success_pts : (formula_label * formula_label)  list  ;(* successful pt from conseq *)
  es_residue_pts : formula_label  list  ;(* residue pts from antecedent *)
  es_id      : int              ; (* unique +ve id *)
  (* below is to store an antecedent prior to it becoming false *)
  es_orig_ante   : formula option       ;  (* original antecedent formula *) 
  es_orig_conseq : struc_formula ;
  es_path_label : path_trace;
  es_prior_steps : steps; (* prior steps in reverse order *)
  (*es_cache_no_list : formula_cache_no_list;*)

  (* For Termination checking *)
  (* Term ann with Lexical ordering *)
  es_var_measures : (term_ann * CP.exp list * CP.exp list) option; 
  es_var_stack :  string list; 
  (* this should store first termination error detected *)
  (* in case an error has already been detected *)
  (* we will not do any further termination checking *)
  (* from this context *)
  es_term_err: string option;


  (* for IMMUTABILITY *)
(* INPUT : this is an alias set for the RHS conseq *)
(* to be used by matching strategy for imm *)
  es_rhs_eqset : (CP.spec_var * CP.spec_var) list;
(*  es_frame : (h_formula * int) list; *)
  es_cont : h_formula list;
  es_crt_holes : (h_formula * int) list;
  es_hole_stk : ((h_formula * int) list) list;
  es_aux_xpure_1 : MCP.mix_formula;
  es_imm_last_phase : bool;
(* below are being used as OUTPUTS *)
  es_subst :  (CP.spec_var list *  CP.spec_var list) (* from * to *); 
  es_aux_conseq : CP.formula;
  (* es_imm_pure_stk : MCP.mix_formula list; *)
  es_must_error : (string * fail_type) option;
  (* es_must_error : string option *)
  es_trace : formula_trace; (*LDK: to keep track of past operations: match,fold...*) 
  (* WN : isn't above the same as prior steps? *)
  es_is_normalizing : bool; (*normalizing process*)

  (* to support permission of variables *)
  (* denotes stack variables with possibly zero permission *)
  es_var_zero_perm : CP.spec_var list;

  (* FOR INFERENCE *)
  (* input flag to indicate if post-condition is to be inferred *)
  es_infer_post : bool; 
  (*input vars where inference expected*)
  es_infer_vars : CP.spec_var list; 
  es_infer_vars_rel : CP.spec_var list;
  es_infer_vars_hp_rel : CP.spec_var list;
  (* input vars to denote vars already instantiated *)
  es_infer_vars_dead : CP.spec_var list; 
  (*  es_infer_init : bool; (* input : true : init, false : non-init *)                *)
  (*  es_infer_pre : (formula_label option * formula) list;  (* output heap inferred *)*)
  (* output : pre heap inferred *)
  es_infer_heap : h_formula list; 
  (* output : pre pure inferred *)
  es_infer_pure : CP.formula list; 
  (* output : post inferred relation lhs --> rhs *)

  (*  (i) defn for relation:
          lhs -> p(...); 
     (ii) proof obligation for unknown relation
          p(...) -> ctr
     (ii) term measures:
          lhs -> r(..)>=0
          lhs -> r(..)-r(..)>0
  RelCat = RelDef (rid) | RelAssume(rid) 
     | RankDec [rid] | RankBounded id
  *)
  (* es_infer_rel : (CP.formula * CP.formula) list; *)
  es_infer_rel : (CP.rel_cat * CP.formula * CP.formula) list;
  es_infer_hp_rel : (CP.rel_cat * formula * formula) list;
  (* output : pre pure assumed to infer relation *)
  (* es_infer_pures : CP.formula list; *)
  (* es_infer_invs : CP.formula list (\* WN : what is this? *\) *)
  (* input precondition inferred so far, for heap
     you may accumulate the xpure0 information;
     to be used by infer_lhs_contra to determine if
     a FALSE is being inferred
  *)
     es_infer_pure_thus : CP.formula; 
     es_group_lbl: spec_label_def;

     

  (* allow residue in lhs formula *)
  es_allow_residue: bool;
}

and context = 
  | Ctx of entail_state
  | OCtx of (context * context) (* disjunctive context *)
      (*| FailCtx of (fail_context list)*)

and steps = string list

(*      MAY

 VALID       MUST

        BOT
*)
 and failure_kind =
       | Failure_May of string
       | Failure_Must of string
       | Failure_Bot of string
       | Failure_Valid

 and fail_explaining = {
     fe_kind: failure_kind; (*may/must*)
     fe_name: string;
     fe_locs: (*Globals.loc*) int list; (*line number*)
(* fe_explain: string;  *)
(* string explaining must failure *)
(*  fe_sugg = struc_formula *)
 }

  and fail_context = {
      fc_prior_steps : steps; (* prior steps in reverse order *)
      fc_message : string;          (* error message *)
      fc_current_lhs : entail_state;     (* LHS context with success points *)
      fc_orig_conseq : struc_formula;     (* RHS conseq at the point of failure *)
      fc_failure_pts : Globals.formula_label list;     (* failure points in conseq *)
      fc_current_conseq : formula;
  }

  and fail_type =
        | Basic_Reason of (fail_context * fail_explaining)
        | Trivial_Reason of fail_explaining
        | Or_Reason of (fail_type * fail_type)
        | And_Reason of (fail_type * fail_type)
        | Union_Reason of (fail_type * fail_type)
        | ContinuationErr of fail_context
        | Or_Continuation of (fail_type * fail_type)

(* Fail | List of Successes *)
and list_context =
  | FailCtx of fail_type
  | SuccCtx of context list

and branch_fail = path_trace * fail_type

and branch_ctx =  path_trace * context

(* disjunction of state with failures and partial success *)
(* a state is successful if it has empty branch_fail *)
and partial_context = (branch_fail list) * (branch_ctx list)
    (* disjunct of failures and success *)

(* successful partial states that have escaped through exceptions *)
and esc_stack = ((control_path_id_strict * branch_ctx list) list)

and failesc_context = (branch_fail list) * esc_stack * (branch_ctx list)

(* conjunct of context in the form of /\(f1|f2 ..s1|s2|s3) *)
and list_partial_context = partial_context list
 
and list_failesc_context = failesc_context list 
    (* conjunct of contexts *)
  
and list_failesc_context_tag = failesc_context Gen.Stackable.tag_list

let print_list_context_short = ref(fun (c:list_context) -> "printer not initialized")
let print_list_context = ref(fun (c:list_context) -> "printer not initialized")
let print_context_list_short = ref(fun (c:context list) -> "printer not initialized")
let print_context_short = ref(fun (c:context) -> "printer not initialized")
let print_context = ref(fun (c:context) -> "printer not initialized")
let print_entail_state = ref(fun (c:entail_state) -> "printer not initialized")
let print_entail_state_short = ref(fun (c:entail_state) -> "printer not initialized")
let print_list_partial_context = ref(fun (c:list_partial_context) -> "printer not initialized")
let print_list_failesc_context = ref(fun (c:list_failesc_context) -> "printer not initialized")
(* let print_flow = ref(fun (c:nflow) -> "printer not initialized") *)
let print_flow = ref(fun (c:nflow) -> "printer not initialized")
let print_esc_stack = ref(fun (c:esc_stack) -> "printer not initialized")
let print_failesc_context = ref(fun (c:failesc_context) -> "printer not initialized")
let print_failure_kind_full = ref(fun (c:failure_kind) -> "printer not initialized")
let print_fail_type = ref(fun (c:fail_type) -> "printer not initialized")

let context_of_branch_ctx_list ls = 
  let rec helper ls = match ls with
    | [] -> report_error no_pos "Current Successful context should not be empty []"
    | [(_,c)] -> c
    | (_,c)::ts -> OCtx (c,helper ts) 
  in helper ls
 
let succ_context_of_failesc_context (_,_,sl) = (context_of_branch_ctx_list sl)

let succ_context_of_failesc_context ((_,_,sl) as x) =
  let pr = !print_failesc_context in
  let pr2 = !print_context_short in
  Debug.no_1 "succ_context_of_failesc_context" pr pr2
      succ_context_of_failesc_context x
			
let succ_context_of_list_failesc_context ctx = 
	List.map succ_context_of_failesc_context ctx

let es_fv (es:entail_state) : CP.spec_var list =
  (fv es.es_formula)@(h_fv es.es_heap)

let rec context_fv (c:context) : CP.spec_var list =
  match c with
    | Ctx es ->  es_fv es
    | OCtx (c1,c2) -> (context_fv c1)@(context_fv c2)

let empty_infer_rel () = new Gen.stack

let empty_es flowt grp_lbl pos = 
	let x = mkTrue flowt pos in
{
  es_formula = x;
  es_heap = HEmp;
  es_history = [];
  es_pure = MCP.mkMTrue pos;
  es_evars = [];
  (* es_must_match = false; *)
  es_ivars = [];
  (* es_expl_vars = []; *)
  es_ante_evars = [];
  es_gen_expl_vars = []; 
  es_gen_impl_vars = []; 
  es_pp_subst = [];
  es_unsat_flag = true;
  es_arith_subst = [];
  es_success_pts = [];
  es_residue_pts  = [];
  es_id = 0 ;
  es_orig_ante = None;
  es_orig_conseq = mkETrue flowt pos;
  es_rhs_eqset = [];
  es_path_label  =[];
  es_prior_steps  = [];
  es_var_measures = None;
  es_var_stack = [];
  (*es_cache_no_list = [];*)
  es_cont = [];
  es_crt_holes = [];
  es_hole_stk = [];
  es_aux_xpure_1 = MCP.mkMTrue pos;
  es_imm_last_phase = true;
  es_subst = ([], []);
  es_aux_conseq = CP.mkTrue pos;
   (* es_imm_pure_stk = []; *)
  es_must_error = None;
  es_trace = [];
  es_is_normalizing = false;
  es_infer_post = false;
  es_infer_vars = [];
  es_infer_vars_dead = [];
  es_infer_vars_rel = [];
  es_infer_vars_hp_rel = [];
  es_infer_heap = []; (* HTrue; *)
  es_infer_pure = []; (* (CP.mkTrue no_pos); *)
  es_infer_rel = [] ;
  es_infer_hp_rel = [] ;
  es_infer_pure_thus = CP.mkTrue no_pos ;
  es_var_zero_perm = [];
  es_group_lbl = grp_lbl;
  es_term_err = None;
  (*es_infer_invs = [];*)
  es_allow_residue = false;
}

let is_one_context (c:context) =
  match c with
    | Ctx _ -> true
    | OCtx _ -> false

let is_cont t = 
  match t with
    | ContinuationErr _ -> true
    | Or_Continuation _ -> true
    | _ -> false

let isFailCtx cl = match cl with 
	| FailCtx _ -> true
	| SuccCtx _ -> false

let isFailCtx cl = 
  Debug.no_1 "isFailCtx" 
      !print_list_context_short string_of_bool isFailCtx cl

let get_must_error_from_ctx cs = 
  match cs with 
    | [Ctx es] -> (match es.es_must_error with
        | None -> None
        | Some (msg,_) -> Some msg)
    | _ -> None

let get_bot_status_from_ctx cs=
  match cs with
    | [Ctx es] ->
        ( match formula_is_eq_flow es.es_formula false_flow_int with
          | true -> Some ""
          | false -> None
        )
    | _ -> None

let rec set_must_error_from_one_ctx ctx msg ft=
  match ctx with
    | Ctx es ->
        begin
            let instance_ft=
              (
                  match ft with
                    | Basic_Reason (fc, fe) ->
                        let instance_fc = {fc with fc_current_lhs = es;
                            fc_message = msg;
                            fc_prior_steps = es.es_prior_steps
                                          }
                        in Basic_Reason (instance_fc, fe)
                    | _ -> report_error no_pos "Cformula.set_must_error_from_one_ctx: should be basic reason here"
              )
            in
            Ctx {es with  es_formula = substitute_flow_into_f  !error_flow_int es.es_formula;
                es_must_error = Some (msg,instance_ft)}
        end
    | OCtx (ctx1, ctx2) -> OCtx (set_must_error_from_one_ctx ctx1 msg ft, set_must_error_from_one_ctx ctx2 msg ft)

let rec set_must_error_from_ctx cs msg ft=
  match cs with
    | [] -> []
    | es::ls -> (set_must_error_from_one_ctx es msg ft):: (set_must_error_from_ctx ls msg ft)

let isFailCtx_gen cl = match cl with
	| FailCtx _ -> true
	| SuccCtx cs -> (get_must_error_from_ctx cs) !=None
    (* | _ -> false *)

let mk_failure_bot_raw msg = Failure_Bot msg

let mk_failure_must_raw msg = Failure_Must msg

let mk_failure_may_raw msg = Failure_May msg

let mk_failure_may msg name = {fe_kind = Failure_May msg;fe_name = name ;fe_locs=[]}

let mk_failure_must msg name = {fe_kind = mk_failure_must_raw msg;fe_name = name ;fe_locs=[]}

let mk_failure_bot msg name= {fe_kind = mk_failure_bot_raw msg;fe_name = name ;fe_locs=[]}

let mk_failure_valid = {fe_kind = Failure_Valid;fe_name = "Valid" ;fe_locs=[]}

let mkAnd_Reason (ft1:fail_type option) (ft2:fail_type option): fail_type option=
  match ft1, ft2 with
    | None, ft2 -> ft2
    | _ , None -> ft1
    | Some ft1, Some ft2 -> Some (And_Reason (ft1, ft2))

let mkOr_Reason ft1 ft2=
  Or_Reason (ft1, ft2)

let comb_must m1 m2 = "["^m1^","^m2^"]"

let is_must_failure_fe (f:fail_explaining) =
  match f.fe_kind with
    | Failure_Must _ -> true 
    | _ -> false

let is_bot_failure_fe (f:fail_explaining) =
  match f.fe_kind with
    | Failure_Bot _ -> true 
    | _ -> false

let rec is_must_failure_ft (f:fail_type) =
  match f with
    | Basic_Reason (_,fe) -> is_must_failure_fe fe
    | Or_Reason (f1,f2) -> (((is_must_failure_ft f1) && (is_must_failure_ft f2)) ||
                                   ((is_bot_failure_ft f1) && (is_must_failure_ft f2)) ||
                                   ((is_must_failure_ft f1) && (is_bot_failure_ft f2)) )
    | And_Reason (f1,f2) -> (is_must_failure_ft f1) || (is_must_failure_ft f2)
    | Union_Reason (f1,f2) -> (is_must_failure_ft f1) && (is_must_failure_ft f2)
    | _ -> false

and is_bot_failure_ft (f:fail_type) =
  match f with
    | Basic_Reason (_,fe) -> is_bot_failure_fe fe
    | Or_Reason (f1,f2) -> (is_bot_failure_ft f1) && (is_bot_failure_ft f2)
    | And_Reason (f1,f2) -> (is_bot_failure_ft f1) || (is_bot_failure_ft f2)
    | Union_Reason (f1,f2) -> (is_bot_failure_ft f1) || (is_bot_failure_ft f2)
    | _ -> false


let is_must_failure (f:list_context) =
  match f with
    | FailCtx f -> is_must_failure_ft f
    | _ -> false

let get_must_failure_fe (f:fail_explaining) =
  match f.fe_kind with
    | Failure_Must m -> Some m 
    | _ -> None

let comb_or m1 m2 = match m1,m2 with
  | Some m1, Some m2 -> Some ("or["^m1^","^m2^"]")
  | _, _ -> None

let comb_and m1 m2 = match m1,m2 with
  | Some m1, Some m2 -> Some ("and["^m1^","^m2^"]")
  | Some m1, None -> Some (m1)
  | None, Some m2 -> Some (m2)
  | _, _ -> None

let rec context_is_eq_flow (f:context) (ff)  : bool=
  match f with
    | Ctx es -> formula_is_eq_flow es.es_formula ff
    | OCtx (c1,c2) -> (context_is_eq_flow c1 ff) && (context_is_eq_flow c2 ff)

let list_context_is_eq_flow (f:list_context) (ff)  : bool=
  match f with
    | FailCtx _ -> false
    | SuccCtx ls -> List.for_all (fun f -> context_is_eq_flow f ff) ls

(* let rec get_must_failure_ft (ft:fail_type) = *)
(*   match ft with *)
(*     | Basic_Reason (_,fe) -> get_must_failure_fe fe *)
(*     | Or_Reason (f1,f2) -> comb_or (get_must_failure_ft f1) (get_must_failure_ft f2) *)
(*     | And_Reason (f1,f2) -> comb_and (get_must_failure_ft f1) (get_must_failure_ft f2) *)
(*     | Union_Reason (f1,f2) -> comb_and (get_must_failure_ft f1) (get_must_failure_ft f2) *)
(*     | ContinuationErr _ -> None *)
(*     | Or_Continuation (f1,f2) -> comb_or (get_must_failure_ft f1) (get_must_failure_ft f2) *)
(*           (\* report_error no_pos "get_must_failure : or continuation encountered" *\) *)
(*     | _ -> None *)

let get_failure_fe (f:fail_explaining) = f.fe_kind

(*gen_land*)
let gen_land (m1,n1,e1) (m2,n2,e2) = match m1,m2 with
  | Failure_Bot _, _ -> m1, n1, e1
      (*report_error no_pos "Failure_None not expected in gen_and"*)
  | _, Failure_Bot _ -> m2, n2, e2
      (*report_error no_pos "Failure_None not expected in gen_and"*)
  | Failure_May m1, Failure_May m2 -> (Failure_May ("LAndR["^m1^","^m2^"]"),n1,None)
  | Failure_May m1, _ -> m2, n2, e2
  | _ , Failure_May m2 -> m1,n1, e1
  | Failure_Must m1, Failure_Must m2 ->
       if (n1==sl_error) then (Failure_Must m2, n2, e2)
        else if (n2==sl_error) then (Failure_Must m1, n1, e1)
        else Failure_Must ("LAndR["^m1^","^m2^"]"), n1, e1 (*combine state here?*)
  | Failure_Must m1, Failure_Valid -> Failure_May ("LAndR["^m1^",Valid]"), n1, None (*combine state here?*)
  | Failure_Valid, x  -> (m2, n2, e2)

(*gen_rand*)
let gen_rand_x (m1,n1,e1) (m2,n2,e2) = match m1,m2 with
  | Failure_Bot m, _ -> Failure_Bot m, n1,e1
      (*report_error no_pos "Failure_None not expected in gen_and"*)
  | _, Failure_Bot m -> Failure_Bot m, n2, e2
      (*report_error no_pos "Failure_None not expected in gen_and"*)
  | Failure_Must m1, Failure_Must m2 ->
      if (n1=sl_error) then (Failure_Must m2, n2, e2)
      else if (n2= sl_error) then (Failure_Must m1, n1, e1)
      else Failure_Must ("AndR["^m1^","^m2^"]"), n1, e1 (*combine state here?*)
  | Failure_Must m, _ -> Failure_Must m, n1, e1
  | _, Failure_Must m -> Failure_Must m, n2, e2
  | Failure_May m1, Failure_May m2 -> (Failure_May ("AndR["^m1^","^m2^"]"),n1,None)
  | Failure_May m, _ -> Failure_May m,n1,None
  | _, Failure_May m -> Failure_May m,n2,None
  | Failure_Valid, x  -> (m2,n2,e2)
  (* | x, Failure_Valid -> x *)

let gen_rand (m1,n1,e1) (m2,n2,e2)=
  let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
  let pr1 (m, n, e) = let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
                       match e with
                         | None -> tmp
                         | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Debug.no_2 "gen_rand" pr pr pr1 (fun x y -> gen_rand_x x y) (m1,n1,e1) (m2,n2,e2)

(* state to be refined to accurate one for must-bug *)
(*gen_lor*)
let gen_lor_x (m1,n1,e1) (m2,n2,e2) : (failure_kind * string * (entail_state option)) = match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("OrR["^m1^","^m2^"]"), n1, e1 (*combine state here?*)
(* report_error no_pos "Failure_None not expected in gen_or" *)
  | Failure_Bot _, _ ->  m2, n2,e2
      (* report_error no_pos "Failure_None not expected in gen_or" *)
  | _, Failure_Bot _ -> m1,n1,e1
      (*report_error no_pos "Failure_None not expected in gen_or"*)
  | Failure_May m1, Failure_May m2 -> Failure_May ("OrR["^m1^","^m2^"]"),n1, None
  | Failure_May m, _ -> Failure_May m, n1,None
  | _, Failure_May m -> Failure_May m,n2,None
  | Failure_Must m1, Failure_Must m2 ->
      if (n1=sl_error) then (Failure_Must m2, n2, e2)
      else if (n2= sl_error) then (Failure_Must m1, n1, e1)
      else (Failure_Must ("lor["^m1^","^m2^"]"), n1, e1)
  | Failure_Must m, Failure_Valid -> (Failure_May ("OrR["^m^",valid]"),n1,None)
  | Failure_Valid, Failure_Must m -> (Failure_May ("OrR["^m^",valid]"),n2,None)
  (* | _, Failure_Must m -> Failure_May ("or["^m^",unknown]") *)
  (* | Failure_Must m,_ -> Failure_May ("or["^m^",unknown]") *)
  | Failure_Valid, x  -> (m2,n2,e2)
  (* | x, Failure_Valid -> x *)

let gen_lor (m1,n1,e1) (m2,n2,e2)=
  let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
  let pr1 (m, n, e) = let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
                       match e with
                         | None -> tmp
                         | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Debug.no_2 "gen_lor" pr pr pr1 (fun x y -> gen_lor_x x y) (m1,n1,e1) (m2,n2,e2)

let cmb_lor m1 m2: failure_kind = match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("lor["^m1^","^m2^"]")
  | Failure_Bot _, _ ->  m2
  | _, Failure_Bot _ -> m1
  | Failure_May m1, Failure_May m2 -> Failure_May ("lor["^m1^","^m2^"]")
  | Failure_May m, _ -> Failure_May m
  | _, Failure_May m -> Failure_May m
  | Failure_Must m1, Failure_Must m2 ->
      Failure_Must ("lor["^m1^","^m2^"]")
  | Failure_Must m, Failure_Valid -> (Failure_May ("lor["^m^",valid]"))
  | Failure_Valid, Failure_Must m -> (Failure_May ("lor["^m^",valid]"))
  | Failure_Valid, x  -> m2

(*gen_ror*)
(*
  - m: failure_kind (must/may/bot/valid)
  - n: name of failure (logical/separation entailment). should reduce separation entailment
  - e: current entailment
*)
let gen_ror_x (m1, n1, e1) (m2, n2, e2) = match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("UnionR["^m1^","^m2^"]"), n1,e1 (*combine state here?*)
  | Failure_Bot _, x -> m1,n1,e1 (* (m2,e2) *)
  | x, Failure_Bot _ -> m2,n2,e2 (*(m1,e1)*)
  | Failure_Valid, _ -> (Failure_Valid,"",None)
  | _, Failure_Valid -> (Failure_Valid,"",None)
  | Failure_Must m1, Failure_Must m2 ->
      if (n1=sl_error && e2 != None) then (Failure_Must m2, n2, e2)
      else if (n2 =sl_error && e1 != None) then(Failure_Must m1, n1, e1)
      else (Failure_Must ("UnionR["^m1^","^m2^"]"),n1, e1)
  | Failure_May m1, Failure_May m2 -> (Failure_May ("UnionR["^m1^","^m2^"]"),n1,None)
  | Failure_May _,  _ -> (m1,n1,e1)
  | _, Failure_May _ -> (m2,n2,e2)

let gen_ror (m1,n1,e1) (m2,n2,e2)=
  let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
  let pr1 (m, n, e) = let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
                       match e with
                         | None -> tmp
                         | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Debug.no_2 "gen_ror" pr pr pr1 (fun x y -> gen_ror_x x y) (m1,n1,e1) (m2,n2,e2)


let rec get_failure_es_ft_x (ft:fail_type) : (failure_kind * (entail_state option)) =
  let rec helper ft = 
  match ft with
    | Basic_Reason (fc,fe) ->
        (*let _= print_endline ("fe_name: " ^ fe.fe_name) in*)
        let f = get_failure_fe fe in
        if (is_must_failure_fe fe) then (f,  fe.fe_name, Some fc.fc_current_lhs)
        else (f,fe.fe_name, None)
    | Or_Reason (f1,f2) -> gen_lor (helper f1) (helper f2)
    | And_Reason (f1,f2) -> gen_rand (helper f1) (helper f2)
    | Union_Reason (f1,f2) -> gen_ror (helper f1) (helper f2)
    | ContinuationErr _ -> (Failure_May "Continuation_Err", "Continuation", None)
    | Or_Continuation (f1,f2) -> gen_lor (helper f1) (helper f2)
    (* report_error no_pos "get_must_failure : or continuation encountered" *)
    | Trivial_Reason fe -> (fe.fe_kind, fe.fe_name, None)
  in
  let (f, _, oes) = helper ft in (f, oes)

let get_failure_es_ft (ft:fail_type) : (failure_kind * (entail_state option)) =
  let pr1 (m, e) = let tmp = (!print_failure_kind_full m) in
                       match e with
                         | None -> tmp
                         | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Debug.no_1 "get_failure_es_ft" !print_fail_type pr1 (fun x -> get_failure_es_ft_x x) ft

let get_failure_ft (ft:fail_type) : (failure_kind) =
  fst (get_failure_es_ft ft)

let get_must_failure_ft f =
  match (get_failure_ft f) with
    | Failure_Must m -> Some m
    | _ -> None

let get_bot_status_ft f =
  match (get_failure_ft f) with
    | Failure_Bot m -> Some m
    | _ -> None

let get_may_failure_fe (f:fail_explaining) =
  match f.fe_kind with
    | Failure_May m | Failure_Must m -> Some m 
    | Failure_Valid -> Some "proven valid here"
    | Failure_Bot _ -> None

(* let rec get_may_failure_ft (f:fail_type) = *)
(*   match f with *)
(*     | Basic_Reason (_,fe) -> get_may_failure_fe fe *)
(*     | Or_Reason (f1,f2) -> comb_or (get_may_failure_ft f1) (get_may_failure_ft f2) *)
(*     | Union_Reason (f1,f2) -> comb_or (get_may_failure_ft f1) (get_may_failure_ft f2) *)
(*     | And_Reason (f1,f2) -> comb_and (get_may_failure_ft f1) (get_may_failure_ft f2) *)
(*     | ContinuationErr _ -> Some "ContErr detected" *)
(*           (\* report_error no_pos "get_may_failure : continuation encountered" *\) *)
(*     | Or_Continuation (f1,f2) -> comb_or (get_may_failure_ft f1) (get_may_failure_ft f2) *)
(*           (\* report_error no_pos "get_may_failure : or continuation encountered" *\) *)
(*     | Trivial_Reason s -> Some s *)

let get_may_failure_ft f =
  match (get_failure_ft f) with
    | Failure_Must m -> Some ("must:"^m)
    | Failure_May m -> Some (m)
    | Failure_Valid -> Some ("Failure_Valid")
    | Failure_Bot m -> Some ("Failure_Bot"^m)

let get_may_failure (f:list_context) =
  match f with
    | FailCtx ft -> 
          let m = (get_may_failure_ft ft) in
          (match m with
            | Some s -> m
            | None -> 
                  let _ = print_flush (!print_list_context_short f) 
                  in report_error no_pos "Should be a may failure here")
    | _ -> None

(* returns Some es if it is a must failure *)
let rec get_must_es_from_ft ft = 
  match ft with
    | Basic_Reason (fc,fe) -> 
          if is_must_failure_fe fe then Some fc.fc_current_lhs
          else None
    | Or_Reason (f1,f2) -> 
          let r1=(get_must_es_from_ft f1) in
          let r2=(get_must_es_from_ft f2) in
          (match r1,r2 with
            | Some _,Some _ -> r1
            | _, _ -> None)
    | And_Reason (f1,f2) | Union_Reason (f1,f2) -> 
          let r1=(get_must_es_from_ft f1) in
          let r2=(get_must_es_from_ft f2) in
          (match r1,r2 with
            | Some _, _ -> r1
            | None, Some _ -> r2
            | None, None -> None)
    | _ -> None

let get_must_es_msg_ft ft = 
  let msg,es = get_failure_es_ft ft in
  (* let es = get_must_es_from_ft ft in *)
  (* let msg = get_must_failure_ft ft in *)
  match es,msg with
    | Some es, Failure_Must msg -> Some (es,msg)
    | None, Failure_Must msg -> Some (empty_es ( mkTrueFlow ()) Lab2_List.unlabelled no_pos,msg) (*may be Trivial fail*)
    (*report_error no_pos "INCONSISTENCY with get_must_es_msg_ft"*)
    | _, _ -> None
 
let get_must_failure (ft:list_context) =
  match ft with
    | FailCtx f -> get_must_failure_ft f
          (* (try get_must_failure_ft f *)
          (* with a ->   *)
          (*     let _ = print_flush (!print_list_context_short ft) in *)
          (*     raise a) *)
	| SuccCtx cs -> get_must_error_from_ctx cs
    (* | _ -> None *)

(*todo: revise, pretty printer*)
let rec get_must_failure_list_partial_context (ls:list_partial_context): (string option)=
    (*may use lor to combine the list first*)
    let los= List.map get_must_failure_partial_context ls in
    (*los contains mutilpe specs??*)
    ( match (combine_helper "UNIONR\n" los "") with
      | "" -> None
      | s -> Some s
    )

  and combine_helper op los rs=
    match los with
      | [] -> rs
      | [os] -> let tmp=
            ( match os with
              | None -> rs
              | Some s -> rs ^ s
            ) in tmp
      | os::ss ->
          (*os contains all failed of 1 path trace*)
          let tmp=
            ( match os with
              | None -> rs
              | Some s -> rs ^ s ^ "\n" ^ op
            ) in
          combine_helper op ss tmp

  and get_must_failure_partial_context ((bfl:branch_fail list), (bctxl: branch_ctx list)): (string option)=
    let helper (pt, ft)=
      let os = get_must_failure_ft ft in
      match os with
        | None -> None
        | Some (s) ->  (* let spt = !print_path_trace pt in *)
                    Some ((*"  path trace: " ^spt ^ "\nlocs: " ^ (!print_list_int ll) ^*) "cause: " ^s)
    in
    match bfl with
      | [] -> None
      | fl -> let los= List.map helper fl in
              ( match (combine_helper "OrR\n" los "") with
                | "" -> None
                | s -> Some s
              )

(*currently, we do not use lor to combine traces,
so just call get_may_falure_list_partial_context*)
let rec get_failure_list_partial_context (ls:list_partial_context): (string*failure_kind)=
    (*may use lor to combine the list first*)
  (*return failure of 1 lemma is enough*)
    let (los, fk)= List.split (List.map get_failure_partial_context [(List.hd ls)]) in
    (*los contains path traces*)
    (combine_helper "UNIONR\n" [List.hd los] "", List.hd fk)

and get_failure_branch bfl=
   let helper (pt, ft)=
     (* let spt = !print_path_trace pt in *)
      match  (get_failure_ft ft) with
        | Failure_Must m -> (Some ((*"  path trace: " ^spt (*^ "\nlocs: " ^ (!print_list_int ll)*) ^*) "  (must) cause: " ^m),  Failure_Must m)
        | Failure_May m -> (Some ((*"  path trace: " ^spt (*^ "\nlocs: " ^ (!print_list_int ll)*) ^*) "  (may) cause: " ^m),  Failure_May m)
        | Failure_Valid -> (None, Failure_Valid)
        | Failure_Bot m -> (Some ((*"  path trace: " ^spt^*)"  unreachable: "^m), Failure_Bot m)
    in
    match bfl with
      | [] -> (None, Failure_Valid)
      | fl -> let los, fks= List.split (List.map helper fl) in
              ( match (combine_helper "OrR\n" los "") with
                | "" -> None, Failure_Valid
                | s -> Some s, List.fold_left cmb_lor (List.hd fks) (List.tl fks)
              )

and get_failure_partial_context ((bfl:branch_fail list), _): (string option*failure_kind)=
   get_failure_branch bfl

let rec get_failure_list_failesc_context (ls:list_failesc_context): (string* failure_kind)=
    (*may use rand to combine the list first*)
    let los, fks= List.split (List.map get_failure_failesc_context [(List.hd ls)]) in
    (*los contains path traces*)
    (*combine_helper "UNION\n" los ""*)
     (*return failure of 1 lemma is enough*)
   (combine_helper "UNIONR\n" [(List.hd los)] "", List.hd fks)

and get_failure_failesc_context ((bfl:branch_fail list), _, _): (string option*failure_kind)=
  get_failure_branch bfl

let get_bot_status (ft:list_context) =
  match ft with
    | FailCtx f -> get_bot_status_ft f
	| SuccCtx cs -> get_bot_status_from_ctx cs

let extract_failure_msg rs=
 if not !Globals.disable_failure_explaining then
   match get_must_failure rs with
     | Some s -> "(must) cause:"^s 
     | _ -> (match get_may_failure rs with
           | Some s -> "(may) cause:"^s
           | None -> "INCONSISTENCY : expected failure but success instead"
     )
 else ""

let is_may_failure_fe (f:fail_explaining) = (get_may_failure_fe f) != None

let rec is_may_failure_ft (f:fail_type) = (get_may_failure_ft f) != None

let is_may_failure (f:list_context) = (get_may_failure f) != None

let is_bot_status (f:list_context) = (get_bot_status f) != None

let convert_must_failure_4_fail_type  (s:string) (ft:fail_type) : context option =
     match (get_must_es_msg_ft ft) with
          | Some (es,msg) -> Some (Ctx {es with es_must_error = Some (s^msg,ft) } ) 
          | _ ->  None

(* TRUNG WHY: purpose when converting a list_context from FailCtx type to SuccCtx type? *)
let convert_must_failure_to_value_orig (l:list_context) : list_context =
  match l with 
    | FailCtx ft ->
          (* (match (get_must_es_msg_ft ft) with *)
          (*   | Some (es,msg) -> SuccCtx [Ctx {es with es_must_error = Some (msg,ft) } ]  *)
          (*   | _ ->  l) *)
          (match (convert_must_failure_4_fail_type "" ft) with
            | Some ctx -> SuccCtx [ctx]
            | None -> l)
    | SuccCtx _ -> l

let convert_must_failure_to_value_orig (l:list_context) : list_context =
 let pr = !print_list_context_short in
  Debug.no_1 "convert_must_failure_to_value_orig" pr pr
  (fun _ -> convert_must_failure_to_value_orig l) l

(* let add_must_err (s:string) (fme:branch_ctx list) (e:esc_stack) : esc_stack = *)
(*   ((-1,"Must Err @"^s),fme) :: e *)

let add_must_err_to_pc (s:string) (fme:branch_ctx list) (e:branch_ctx list) : branch_ctx list =
  fme @ e

let convert_must_failure_4_branch_type  (s:string) ((pt,ft):branch_fail) : branch_ctx option =
  match (convert_must_failure_4_fail_type s ft) with
    | Some b -> Some (pt,b)
    | None -> None

let convert_must_failure_4_branch_fail_list  (s:string) (fl:branch_fail list) : (branch_ctx list * branch_fail list) =
  List.fold_left (fun (must_l,may_l) bf ->
      match (convert_must_failure_4_branch_type s bf) with
        | Some r -> (r::must_l, may_l)
        | None -> (must_l, bf::may_l)) ([],[]) fl

let convert_must_failure_4_failesc_context (s:string) ((fl,e,bl):failesc_context) : failesc_context =
  let (fme,fl) = convert_must_failure_4_branch_fail_list s fl in
  (fl,e,add_must_err_to_pc s fme bl)

let convert_must_failure_4_list_failesc_context (s:string) (l:list_failesc_context) : list_failesc_context =
  List.map (convert_must_failure_4_failesc_context s) l


let fold_context (f:'t -> entail_state -> 't) (a:'t) (c:context) : 't =
  let rec helper a c = match c with
    | Ctx es -> f a es
    | OCtx (c1,c2) -> helper (helper a c1) c2 in
  helper a c


let consistent_entail_state (es:entail_state) : bool = consistent_formula es.es_formula

let consistent_context (c:context) : bool = 
  fold_context (fun a es -> (consistent_entail_state es) && a) true c

let must_consistent_context (s:string) l : unit =
  if !consistency_checking then
    let b = consistent_context l in
    if b then  print_endline ("\nSuccessfully Tested Consistency at "^s)
    else report_error no_pos ("ERROR at "^s^": context inconsistent")

let consistent_branch_ctx ((_,c):branch_ctx) : bool = consistent_context c

let consistent_esc_stack (ls:esc_stack) : bool = 
  List.for_all (fun (_,b_ls) -> List.for_all consistent_branch_ctx b_ls) ls
 
let consistent_failesc_context ((_,es,b_ls):failesc_context) : bool =
  let b1 = List.for_all (consistent_branch_ctx) b_ls in
  let b2 = consistent_esc_stack es in
  b1 && b2

let consistent_list_failesc_context (l:list_failesc_context) : bool =
   List.for_all (consistent_failesc_context) l

let must_consistent_list_failesc_context (s:string) l : unit =
  if !consistency_checking then
    let b = consistent_list_failesc_context l in
    if b then  print_endline ("\nSuccessfully Tested Consistency at "^s)
    else report_error no_pos ("ERROR: "^s^" list_failesc context inconsistent")

(*let isStrictFalseCtx ctx = match ctx with
  | Ctx es -> isStrictConstFalse es.es_formula
  | _ -> false*)

let isAnyFalseCtx (ctx:context) : bool = match ctx with
  | Ctx es -> isAnyConstFalse es.es_formula
  | _ -> false  

(* let isAnyFalseBranchCtx (ctx:branch_ctx) : bool = match ctx with *)
(*   | _,Ctx es -> isAnyConstFalse es.es_formula *)
(*   | _ -> false *)

let isAnyFalsePartialCtx (fc,sc) = (fc=[]) &&
  List.for_all (fun (_,s) -> isAnyFalseCtx s) sc

let isAnyFalseFailescCtx (fc,ec,sc) = (fc=[]) &&
  List.for_all (fun (_,s) -> isAnyFalseCtx s) sc

let isAnyFalseListCtx ctx = match ctx with
  | SuccCtx lc ->List.exists isAnyFalseCtx lc
  | FailCtx _ -> false
  
let isStrictTrueCtx ctx = match ctx with
  | Ctx es -> isStrictConstTrue es.es_formula
  | _ -> false

let isAnyTrueCtx ctx = match ctx with
  | Ctx es -> isAnyConstTrue es.es_formula
  | _ -> false
  
let rec allFalseCtx ctx = match ctx with
	| Ctx es -> isAnyFalseCtx ctx
	| OCtx (c1,c2) -> (allFalseCtx c1) && (allFalseCtx c2)

let isFalseBranchCtxL (ss:branch_ctx list) = 
   (ss!=[]) && (List.for_all (fun (_,c) -> isAnyFalseCtx c) ss )

let remove_dupl_false (sl:branch_ctx list) = 
  let nl = (List.filter (fun (_,oc) -> not (isAnyFalseCtx oc) ) sl) in
  if nl==[] then 
    if (sl==[]) then []
    else [List.hd(sl)]
  else nl

let remove_dupl_false (sl:branch_ctx list) = 
  let pr n = string_of_int(List.length n) in
  Debug.no_1 "remove_dupl_false" pr pr remove_dupl_false sl

let remove_dupl_false_context_list (sl:context list) = 
  let nl = (List.filter (fun oc -> not (isAnyFalseCtx oc) ) sl) in
  if nl==[] then 
    if (sl==[]) then []
    else [List.hd(sl)]
  else nl

let remove_dupl_false_pc (fl,sl) = (fl,remove_dupl_false sl)

let remove_dupl_false_fe (fl,ec,sl) = (fl,ec,remove_dupl_false sl)


let remove_dupl_false_pc_list (fs_list:list_partial_context) = 
  let ns = List.filter (fun (fl,sl) -> not(fl==[] && isFalseBranchCtxL sl)) fs_list in
  if ns==[] then [List.hd fs_list]
  else ns
 
let remove_dupl_false_fe_list (fs_list:list_failesc_context) = 
  let ns = List.filter (fun (fl,_,sl) -> not(fl==[] && isFalseBranchCtxL sl)) fs_list in
  if ns==[] then [List.hd fs_list]
  else ns

let rec collect_term_err ctx =
  match ctx with
  | Ctx estate ->
    (match estate.es_term_err with
      | None -> []
      | Some msg -> [msg])
  | OCtx (ctx1, ctx2) -> (collect_term_err ctx1) @ (collect_term_err ctx2)

let collect_term_err_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c) ->
    collect_term_err c) cl)) ctx in
  List.concat r

let collect_term_err_list_partial_context (ctx:list_partial_context) =
  Debug.no_1 "collect_term_err_list_partial_context"
  !print_list_partial_context (pr_list (fun x -> x))
  collect_term_err_list_partial_context ctx

let rec collect_pre_pure ctx = 
  match ctx with
  | Ctx estate -> estate.es_infer_pure 
  | OCtx (ctx1, ctx2) -> (collect_pre_pure ctx1) @ (collect_pre_pure ctx2) 

let rec collect_pre_heap ctx = 
  match ctx with
  | Ctx estate -> estate.es_infer_heap 
  | OCtx (ctx1, ctx2) -> (collect_pre_heap ctx1) @ (collect_pre_heap ctx2) 

let rec collect_rel ctx = 
  match ctx with
  | Ctx estate -> estate.es_infer_rel 
  | OCtx (ctx1, ctx2) -> (collect_rel ctx1) @ (collect_rel ctx2) 

let rec collect_hp_rel ctx = 
  match ctx with
  | Ctx estate -> estate.es_infer_hp_rel 
  | OCtx (ctx1, ctx2) -> (collect_hp_rel ctx1) @ (collect_hp_rel ctx2) 

let rec collect_infer_vars ctx = 
  match ctx with
  | Ctx estate -> estate.es_infer_vars 
  | OCtx (ctx1, ctx2) -> (collect_infer_vars ctx1) @ (collect_infer_vars ctx2) 

let rec collect_infer_post ctx = 
  match ctx with
  | Ctx estate -> estate.es_infer_post 
  | OCtx (ctx1, ctx2) -> (collect_infer_post ctx1) || (collect_infer_post ctx2) 

let rec collect_formula ctx = 
  match ctx with
  | Ctx estate -> [estate.es_formula]
  | OCtx (ctx1, ctx2) -> (collect_formula ctx1) @ (collect_formula ctx2) 

let rec collect_orig_ante ctx =
	match ctx with
	| Ctx estate -> 
      (match estate.es_orig_ante with
      | None -> []
      | Some ante -> [ante])
	| OCtx (ctx1, ctx2) -> (collect_orig_ante ctx1) @ (collect_orig_ante ctx2)

let rec collect_term_ann_context ctx =
	match ctx with
	| Ctx es -> (match es.es_var_measures with
		| None -> []
		| Some (t_ann, _, _) -> [t_ann])
	| OCtx (ctx1, ctx2) -> (collect_term_ann_context ctx1) @ (collect_term_ann_context ctx2)

let collect_term_ann_list_context ctx =
	match ctx with
	| FailCtx _ -> []
	| SuccCtx l_ctx -> 
		List.concat (List.map (fun ctx -> collect_term_ann_context ctx) l_ctx) 

let rec collect_term_err_msg_context ctx =
  match ctx with
  | Ctx es -> es.es_var_stack
  | OCtx (ctx1, ctx2) -> 
      (collect_term_err_msg_context ctx1) @
      (collect_term_err_msg_context ctx2)

(* let collect_term_err_msg_list_context ctx = *)
(*   match ctx with *)
(*   | FailCtx _ -> [] *)
(*   | SuccCtx l_ctx -> *)
(*       List.concat (List.map (fun ctx -> collect_term_err_msg_context ctx) l_ctx) *)

let collect_term_ann_and_msg_list_context ctx =
	match ctx with
	| FailCtx _ -> []
	| SuccCtx l_ctx -> (List.map (fun ctx -> 
      (List.exists (fun a -> match a with Fail _ -> true | _ -> false) (collect_term_ann_context ctx), 
      (String.concat "\n" (collect_term_err_msg_context ctx)))) l_ctx) 
			
(* Termination: The term_measures of an OR context
 * should only be collected once *)  
let rec collect_term_measures_context ctx =
	match ctx with
	| Ctx es -> (match es.es_var_measures with
		| None -> []
    | Some (_, ml, _) -> [ml])
	| OCtx (ctx1, _) -> collect_term_measures_context ctx1

let collect_term_measures_branch_ctx_list br_ctx_l =
  List.concat (List.map (fun (_, ctx) -> 
    collect_term_measures_context ctx) br_ctx_l)

let collect_term_measures_list_partial_context p_ctx_l =
  List.concat (List.map (fun (_, br_ctx_l) -> 
    collect_term_measures_branch_ctx_list br_ctx_l) p_ctx_l)

let rec add_pre_heap ctx = 
  match ctx with
  | Ctx estate -> estate.es_infer_heap 
  | OCtx (ctx1, ctx2) -> (collect_pre_heap ctx1) @ (collect_pre_heap ctx2) 

let add_infer_pure_thus_estate cp es =
  {es with es_infer_pure_thus = CP.mkAnd es.es_infer_pure_thus cp no_pos;
  }

let add_infer_rel_to_estate_x cp es =
  let old_cp = es.es_infer_rel in
  let new_cp = cp@old_cp in
  {es with es_infer_rel = new_cp;}

let add_infer_rel_to_estate cp es =
  let pr = pr_list CP.print_lhs_rhs in
  let pr2 es = pr es.es_infer_rel in
 Debug.no_1 "add_infer_rel_to_estate" pr pr2 
  (fun _ -> add_infer_rel_to_estate_x cp es) cp

let add_infer_pure_to_estate cp es =
  let old_cp = es.es_infer_pure in
  let new_cp = List.concat (List.map CP.split_conjunctions cp) in
  let new_cp = List.fold_left (fun a n -> 
      (* let n = CP.norm_form n in *)
      let n = CP.arith_simplify_new n in
      if List.exists (CP.equalFormula_f CP.eq_spec_var n) a then a else n::a) old_cp new_cp 
  in  {es with es_infer_pure = new_cp;
      (* add inferred pre to pure_this too *)
               es_infer_pure_thus = CP.mkAnd es.es_infer_pure_thus (CP.join_conjunctions new_cp) no_pos;
  }

let add_infer_rel_to_ctx cp ctx =
  let rec helper ctx =
    match ctx with
      | Ctx es -> Ctx (add_infer_rel_to_estate cp es)
      | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

let add_infer_pure_to_ctx cp ctx =
  let rec helper ctx =
    match ctx with
      | Ctx es -> Ctx (add_infer_pure_to_estate cp es)
      | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

let add_infer_pure_to_ctx cp ctx =
  Debug.no_1 "add_infer_pure_to_ctx"
      (pr_list !print_pure_f) pr_no
      (fun _ -> add_infer_pure_to_ctx cp ctx) cp

let add_infer_heap_to_ctx cp ctx =
  let rec helper ctx =
    match ctx with
      | Ctx es -> 
        let new_cp = List.filter (fun c -> not (Gen.BList.mem_eq (*CP.equalFormula*) (=) c es.es_infer_heap)) cp in
        Ctx {es with es_infer_heap = new_cp@es.es_infer_heap;}
      | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

let add_infer_pure_to_list_context cp (l : list_context) : list_context  = 
  match l with
    | FailCtx _-> l
    | SuccCtx sc -> SuccCtx (List.map (add_infer_pure_to_ctx cp) sc)

let add_infer_pure_to_list_context cp (l : list_context) : list_context  = 
  let pr = !print_list_context_short in
  Debug.no_2 "add_infer_pure_to_list_context"
      (pr_list !print_pure_f) pr pr
      add_infer_pure_to_list_context cp l

let add_infer_heap_to_list_context cp (l : list_context) : list_context  = 
  match l with
    | FailCtx _-> l
    | SuccCtx sc -> SuccCtx (List.map (add_infer_heap_to_ctx cp) sc)

let add_infer_rel_to_list_context cp (l : list_context) : list_context  = 
  match l with
    | FailCtx _-> l
    | SuccCtx sc -> SuccCtx (List.map (add_infer_rel_to_ctx cp) sc)

(* f_ctx denotes false context *)
let add_infer_pre f_ctx ctx =
  let ch = collect_pre_heap f_ctx in
  if (ch!=[]) then
    let _ = print_endline "ERROR : non-pure heap inferred for false" in
    report_error no_pos ("add_infer_pre: non-pure inferred heap :"^(!print_context f_ctx))
  else
    let cp = collect_pre_pure f_ctx in
    if (cp!=[]) then add_infer_pure_to_ctx cp ctx
    else 
      let cr = collect_rel f_ctx in
      if (cr!=[]) then add_infer_rel_to_ctx cr ctx
      else ctx

let mkOCtx ctx1 ctx2 pos =
  (*if (isFailCtx ctx1) || (isFailCtx ctx2) then or_fail_ctx ctx1 ctx2
  else*)  (* if isStrictTrueCtx ctx1 || isStrictTrueCtx ctx2 then *)
  (* true_ctx (mkTrueFlow ()) pos *)  (* not much point in checking
                                         for true *)
  (* else *) 
  if isAnyFalseCtx ctx1 then add_infer_pre ctx1 ctx2
  else if isAnyFalseCtx ctx2 then add_infer_pre ctx2 ctx1
  else OCtx (ctx1,ctx2) 

let or_context c1 c2 = mkOCtx c1 c2 no_pos   

let failesc_context_simplify ((l,a,cs) : failesc_context) : failesc_context =  (l,a,remove_dupl_false cs)
  
let failesc_context_simplify (ctx: failesc_context) : failesc_context =
  let pr = !print_failesc_context in
  Debug.no_1 "failesc_context_simplify" pr pr
    failesc_context_simplify ctx

let list_failesc_context_simplify (l : list_failesc_context) : list_failesc_context = 
  List.map failesc_context_simplify l

let list_failesc_context_simplify (l : list_failesc_context) : list_failesc_context = 
  let pr = !print_list_failesc_context in
  Debug.no_1 "list_failesc_context_simplify" pr pr list_failesc_context_simplify l 


let mk_empty_frame () : (h_formula * int ) = 
  let hole_id = fresh_int () in
    (Hole(hole_id), hole_id)

let mk_not_a_failure =
  Basic_Reason ({
      fc_prior_steps = [];
      fc_message = "Success";
      fc_current_lhs =  empty_es (mkTrueFlow ()) Lab2_List.unlabelled  no_pos;
      fc_orig_conseq =  mkETrue  (mkTrueFlow ()) no_pos;
      fc_failure_pts = [];
      fc_current_conseq = mkTrue (mkTrueFlow ()) no_pos
  }, {
      fe_kind = Failure_Valid;
      fe_name = "" ;fe_locs=[]
  }
)

let invert ls = 
  let foo es =
            let fc_template = {
		        fc_message = "INCONSISTENCY : expected failure but success instead";
		        fc_current_lhs  =  empty_es (mkTrueFlow ()) Lab2_List.unlabelled  no_pos;
		        fc_prior_steps = [];
		        fc_orig_conseq  = es.es_orig_conseq;
		        fc_current_conseq = mkTrue (mkTrueFlow()) no_pos;
		        fc_failure_pts =  []} in
            (Basic_Reason (fc_template,
                 mk_failure_must "INCONSISTENCY : expected failure but success instead" "")) in
  let goo es ff = formula_subst_flow es.es_formula ff in
  let errmsg = "Expecting Failure but Success instead" in
  match ls with
  | [] -> []
  | [Ctx es] -> (match es.es_must_error with
      | None -> [Ctx {es with es_must_error = Some ("1 "^errmsg,foo es); es_formula = goo es (mkErrorFlow())}]
      | Some _ -> [Ctx {es with es_must_error = None; es_formula = goo es (mkNormalFlow())}])
  | (Ctx es)::_ -> [Ctx {es with es_must_error = Some ("2 "^errmsg,foo es); es_formula = goo es (mkErrorFlow())}]
  | _ -> report_error no_pos "not sure how to invert_outcome"


let invert_outcome (l:list_context) : list_context =
  match l with 
  | FailCtx ft -> l
  | SuccCtx ls -> SuccCtx (invert ls)

let invert_fail_branch_must_fail (pt, ft):(branch_fail list * branch_ctx list)=
  let fk,eso = get_failure_es_ft ft in
   match (fk) with
     | Failure_Must _ ->
         begin
             match eso with
               | Some es -> ([],[(pt, Ctx es)])
               | None -> failwith "Cformula.invert_branch_must_fail: something is wrong"
         end
     | _ -> ([(pt,ft)], [])

let invert_ctx_branch_must_fail (pt, ctx):(branch_fail)=
  let foo es =
    let fc_template = {
		fc_message = "INCONSISTENCY : expected failure but success instead";
		fc_current_lhs  =  empty_es (mkTrueFlow ()) Lab2_List.unlabelled no_pos;
		fc_prior_steps = [];
		fc_orig_conseq  = es.es_orig_conseq;
		fc_current_conseq = mkTrue (mkTrueFlow()) no_pos;
		fc_failure_pts =  []} in
    (Basic_Reason (fc_template,
                   mk_failure_must "INCONSISTENCY : expected failure but success instead" "")) in
  match ctx with
    | Ctx es -> (pt, foo es)
    | _ -> report_error no_pos "not sure how to invert_outcome"

let invert_partial_context_outcome fnc_ctx_invert fnc_fail_invert (fs, bctxs):(branch_fail list * branch_ctx list)=
  let rec helper fs rs ctxs=
    match fs with
      | [] -> rs, ctxs
      | bf::bs -> let r1,r2 = fnc_fail_invert bf in
                  helper bs (rs@r1) (ctxs@r2)
  in
  match fs with
    | [] ->(*if fs = empty ==> invert Valid => must failure*)
        (fs@(List.map fnc_ctx_invert bctxs),[])
    | _ -> (*otherwises*)
        let fb, cb = helper fs [] bctxs in (fb,cb)

let invert_list_partial_context_outcome fnc_ctx_invert fnc_fail_invert cl=
  List.map (invert_partial_context_outcome fnc_ctx_invert fnc_fail_invert) cl

let empty_ctx flowt lbl pos = Ctx (empty_es flowt lbl(*Lab2_List.unlabelled*) pos)


let false_es_with_flow_and_orig_ante es flowt f pos =
	let new_f = mkFalse flowt pos in
    {(empty_es flowt Lab2_List.unlabelled pos) with es_formula = new_f ; es_orig_ante = Some f; 
        es_infer_vars = es.es_infer_vars;
        es_infer_vars_rel = es.es_infer_vars_rel;
        es_infer_vars_hp_rel = es.es_infer_vars_hp_rel;
        es_infer_vars_dead = es.es_infer_vars_dead;
        es_infer_heap = es.es_infer_heap;
        es_infer_pure = es.es_infer_pure;
        es_infer_rel = es.es_infer_rel;
        es_infer_hp_rel = es.es_infer_hp_rel;
        es_infer_pure_thus = es.es_infer_pure_thus;
        es_var_measures = es.es_var_measures;
        es_group_lbl = es.es_group_lbl;
        es_term_err = es.es_term_err;
    }

let false_es_with_orig_ante es f pos =
    let flowt = flow_formula_of_formula f in
      false_es_with_flow_and_orig_ante es flowt f pos

let false_ctx_with_flow_and_orig_ante es flowt f pos = 
	Ctx (false_es_with_flow_and_orig_ante es flowt f pos)

let false_ctx_with_orig_ante es f pos = 
	Ctx (false_es_with_orig_ante es f pos)

let false_es flowt g_lbl pos = 
  let x =  mkFalse flowt pos in
    {(empty_es flowt g_lbl pos) with es_formula = x;}

and true_ctx flowt g_lbl pos = Ctx (empty_es flowt g_lbl pos)

(* let mkFalse_branch_ctx = ([],false_ctx mkFalseFlow no_pos) *)

let or_context_list (cl10 : context list) (cl20 : context list) : context list = 
  let rec helper cl1 = match cl1 with
	| c1 :: rest ->
		let tmp1 = helper rest in
		let tmp2 = List.map (or_context c1) cl20 in
		  tmp2 @ tmp1 
	| [] -> []
  in
	if Gen.is_empty cl20 then
	  []
	else helper cl10 

let or_context_list cl10 cl20 =
  let pr = !print_context_list_short in
  Debug.no_2 "or_context_list" pr pr pr (fun _ _ -> or_context_list cl10 cl20) cl10 cl20
  
let mkFailContext msg estate conseq pid pos = {
  fc_prior_steps = estate.es_prior_steps ;
  fc_message = msg ;
  fc_current_lhs = estate;
  fc_orig_conseq = estate.es_orig_conseq;
  fc_failure_pts = (match pid with | Some s-> [s] | _ -> []);
  fc_current_conseq = conseq;
}   
let mkFailCtx_in (ft:fail_type) = FailCtx ft

(*simple concurrency*)
let mkFailCtx_simple msg estate conseq pos = 
  let fail_ctx = {
	  fc_message = msg;
	  fc_current_lhs  = estate;
	  fc_prior_steps = estate.es_prior_steps;
	  fc_orig_conseq  = struc_formula_of_formula conseq pos;
	  fc_current_conseq = formula_of_heap HFalse pos;
	  fc_failure_pts = [];} 
  in
  let fail_ex = {fe_kind = Failure_Must msg; fe_name = Globals.logical_error ;fe_locs=[]} in
  (*temporary no failure explaining*)
  mkFailCtx_in (Basic_Reason (fail_ctx,fail_ex))

let mkFailCtx_vperm msg rhs_b estate conseq pos = 
  let s = "variable permission mismatch "^msg in
  let new_estate = {estate  with es_formula = substitute_flow_into_f
          !top_flow_int estate.es_formula} in
  mkFailCtx_in (Basic_Reason (mkFailContext s new_estate (Base rhs_b) None pos,mk_failure_may s logical_error))

let mk_fail_partial_context_label (ft:fail_type) (lab:path_trace) : (partial_context) = ([(lab,ft)], []) 

(* let mk_partial_context (c:context) : (partial_context) = ([], [ ([], c) ] )  *)

let mk_partial_context (c:context) (lab:path_trace) : (partial_context) = ([], [ (lab, c) ] ) 
let mk_failesc_context (c:context) (lab:path_trace) esc : (failesc_context) = ([], esc,[ (lab, c) ] ) 

let rec is_empty_esc_stack (e:esc_stack) : bool = match e with
  | [] -> false
  | (_,[])::t -> is_empty_esc_stack t
  | (_,h::t)::_ -> true
  
let colapse_esc_stack (e:esc_stack) : branch_ctx list = List.fold_left (fun a (_,c)-> a@c) [] e

let push_esc_elem  (e:esc_stack) (b:branch_ctx list): esc_stack = 
  match b with 
  | [] -> e
  | _ ->
    match e with
    | [] -> [((0,""),b)]
    | (lbl,h)::t-> (lbl,b@h)::t 
  
let push_esc_level (e:esc_stack) lbl : esc_stack = (lbl,[])::e

let pop_esc_level (e:esc_stack) lbl : (esc_stack * branch_ctx list) = match e with
  | (lbl,s)::t -> (t,s)
  | _ -> Error.report_error {Err.error_loc = no_pos;  
              Err.error_text = "error in popping exception contexts \n"}
       
let rec merge_success s1 s2 = match s1,s2 with
    | [],xs | xs,[] -> xs   
        (* List.filter (fun (l,_) -> not (List.mem l pt_fail_list)) xs *)
    | (l1,b1)::z1,(l2,b2)::z2 -> 
	if path_trace_eq l1 l2 then 
	  let res = merge_success z1 z2 in
	    ((l1,or_context b1 b2)::res)
	else if path_trace_lt l1 l2 then 
	  let res = merge_success z1 s2 in
	    (l1,b1)::res
	else let res = merge_success s1 z2 in
	  (l2,b2)::res
       
let pop_esc_level_list (l:list_failesc_context) lbl : list_failesc_context = 
  List.map (fun (fl,el,sl)-> 
    let ne,el = pop_esc_level el lbl in 
    (fl,ne, merge_success el sl)) l
 
let mk_list_partial_context_label (c:list_context) (lab:path_trace): (list_partial_context) =
  match c with
    | FailCtx fr ->  [( [(lab,fr)] ,[])]
    | SuccCtx cl -> List.map (fun c -> mk_partial_context c lab) cl

let mk_list_partial_context (c:list_context) : (list_partial_context) =
  mk_list_partial_context_label c []



let repl_label_list_partial_context (lab:path_trace) (cl:list_partial_context) : list_partial_context 
    = List.map (fun (fl,sl) -> (fl, List.map (fun (_,c) -> (lab,c)) sl)) cl

let is_inferred_pre estate = 
  not(estate.es_infer_heap==[] && estate.es_infer_pure==[])
  (* let r = (List.length (estate.es_infer_heap))+(List.length (estate.es_infer_pure)) in *)
  (* if r>0 then true else false *)

let rec is_inferred_pre_ctx ctx = 
  match ctx with
  | Ctx estate -> is_inferred_pre estate 
  | OCtx (ctx1, ctx2) -> (is_inferred_pre_ctx ctx1) || (is_inferred_pre_ctx ctx2)

(* let anyPreInCtx c = is_inferred_pre_ctx c *)

let proc_left t1 t2 =
    match t1 with
      | [] -> Some t2
      | [c1] -> 
            if isAnyFalseCtx c1 then
              if is_inferred_pre_ctx c1 then Some t2 (* drop FalseCtx with Pre *)
              else Some t1 (* keep FalseCtx wo Pre *)
            else None
      | _ -> None 

(* remove false with precondition *)
let simplify_ctx_elim_false_dupl t1 t2 =
  match proc_left t1 t2 with
    | Some r1 -> r1
    | None -> 
          (match proc_left t2 t1 with
            | Some r2 -> r2
            | None -> t1@t2)

let simplify_ctx_elim_false_dupl t1 t2 =
  let pr = !print_context_list_short in
  Debug.no_2 "simplify_ctx_elim_flse_dupl" pr pr pr simplify_ctx_elim_false_dupl t1 t2 

  (*context set union*)

let list_context_union_x c1 c2 = 
  let simplify x = (* context_list_simplify *) x in
match c1,c2 with
  | FailCtx t1 ,FailCtx t2 -> (*FailCtx (Or_Reason (t1,t2))*)
      if ((is_cont t1) && not(is_cont t2))
      then FailCtx(t1)
      else
	if ((is_cont t2) && not(is_cont t1))
	then FailCtx(t2)
	else
	  if (is_cont t1) && (is_cont t2) then
	    FailCtx (Or_Continuation (t1,t2))  
	  else
	    FailCtx (Union_Reason (t1,t2))  (* for UNION, we need to priorities MAY bug *)
	     (*FailCtx (And_Reason (t1,t2))   *)
  | FailCtx t1 ,SuccCtx t2 -> SuccCtx (simplify t2)
  | SuccCtx t1 ,FailCtx t2 -> SuccCtx (simplify t1)
  | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (simplify_ctx_elim_false_dupl t1 t2)

let list_context_union c1 c2 =
  let pr = !print_list_context_short in
  Debug.no_2_opt (fun _ -> not(isFailCtx c1 ||  isFailCtx c2) )  "list_context_union" 
      pr pr pr
      list_context_union_x c1 c2 

let rec union_context_left c_l = match (List.length c_l) with
  | 0 ->  Err.report_error {Err.error_loc = no_pos;  
              Err.error_text = "folding empty context list \n"}
  | 1 -> (List.hd c_l)
  | _ ->  List.fold_left list_context_union (List.hd c_l) (List.tl c_l)
 
(*should use union_context_left directly*)
and fold_context_left_x c_l = union_context_left c_l 

 (*list_context or*)
and get_explaining t =
  match t with
  | Basic_Reason (f, fe) -> Some fe
  | Trivial_Reason _ -> None
  | Or_Reason _ -> None
  | Union_Reason _ -> None
  | And_Reason (_,_) -> None
  | ContinuationErr _ -> None
  | Or_Continuation _ -> None

and isMustFail fc = is_must_failure_ft fc
 

and isMayFail fc = is_may_failure_ft fc
   
and isMustFailCtx cl = match cl with
  | FailCtx fc -> isMustFail fc
  | SuccCtx _ -> false

and isMayFailCtx cl = match cl with
  | FailCtx fc -> isMayFail fc
  | SuccCtx _ -> false

and fold_context_left c_l = 
  let pr = !print_list_context_short in
  let pr1 x = String.concat "\n" (List.map !print_list_context_short x) in
  Debug.no_1 "fold_context_left" pr1 pr fold_context_left_x c_l

(* Fail U Succ --> Succ *)
(* Fail m1 U Fail m2 --> And m1 m2 *)
(* Fail or Succ --> Fail *)
(* Fail m1 or Fail m2 --> Or m1 m2 *)
  (*list_context or*)

(*LOR*)
and or_list_context_x_new c1 c2 =
  match c1,c2 with
     | FailCtx t1 ,FailCtx t2 -> FailCtx (Or_Reason (t1,t2))
     | FailCtx t1 ,SuccCtx t2 ->
         if is_bot_failure_ft t1 then
           c2
         else
           let t = mk_not_a_failure in
           FailCtx (Or_Reason (t1,t))
     | SuccCtx t1 ,FailCtx t2 ->
         if is_bot_failure_ft t2 then
           c1
         else
           let t = mk_not_a_failure in
           FailCtx (Or_Reason (t,t2))
     | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (or_context_list t1 t2)

and or_list_context_x c1 c2 = match c1,c2 with
     | FailCtx t1 ,FailCtx t2 -> FailCtx (Or_Reason (t1,t2))
     | FailCtx t1 ,SuccCtx t2 ->
        let t = mk_not_a_failure 
        in
        FailCtx (Or_Reason (t1,t))
     | SuccCtx t1 ,FailCtx t2 ->
        let t = mk_not_a_failure 
        in
        FailCtx (Or_Reason (t,t2))
     | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (or_context_list t1 t2)

and and_list_context c1 c2= match c1,c2 with
  | FailCtx t1 ,FailCtx t2 -> FailCtx (And_Reason (t1,t2))
  | FailCtx t1 ,SuccCtx t2 ->
         c1
  | SuccCtx t1 ,FailCtx t2 ->
      c2
  | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (or_context_list t1 t2)

and or_list_context c1 c2 = 
  let pr = !print_list_context_short in
  Debug.no_2 "or_list_context" pr pr pr or_list_context_x_new c1 c2

(* can remove redundancy here? *)

let isFailPartialCtx (fs,ss) =
  if (Gen.is_empty fs) then false else true

let isFailFailescCtx (fs,es,ss) =
  if (Gen.is_empty fs) then false else true
(* if (Gen.is_empty ss)&&(Gen.is_empty (colapse_esc_stack es)) then true else false *)

let isFailBranchFail (_,ft) =
   match (get_failure_ft ft) with
        | Failure_Must _ -> true
        | Failure_May _ -> true
        | Failure_Valid -> false
        | Failure_Bot _ -> false

let isFailFailescCtx_new (fs,_,_) =
  List.exists isFailBranchFail fs

let isFailPartialCtx_new (fs,ss) =
  List.exists isFailBranchFail fs

let isFailListPartialCtx cl =
  List.for_all isFailPartialCtx cl 

let isFailListPartialCtx_new cl =
  List.for_all isFailPartialCtx_new cl 

let isFailListFailescCtx cl =
  List.for_all isFailFailescCtx cl 

let isFailListFailescCtx_new cl =
  List.for_all isFailFailescCtx_new cl

let isSuccessPartialCtx (fs,ss) =
if (Gen.is_empty fs) then true else false

let isSuccessBranchFail (_,ft) =
   match (get_failure_ft ft) with
     | Failure_Must _ -> false
     | Failure_May _ -> false
     | Failure_Valid -> true
     | Failure_Bot _ -> true

let isSuccessPartialCtx_new (fs,_) =
 List.for_all isSuccessBranchFail fs

let isSuccessFailescCtx (fs,_,_) =
if (Gen.is_empty fs) then true else false

let isSuccessFailescCtx_new (fs,_,_) =
  List.for_all isSuccessBranchFail fs

let isSuccessListPartialCtx cl =
  cl==[] || List.exists isSuccessPartialCtx cl 

let isSuccessListPartialCtx cl =
  let pr = !print_list_partial_context in
  Debug.no_1 "isSuccessListPartialCtx" pr string_of_bool isSuccessListPartialCtx cl

let isSuccessListPartialCtx_new cl =
  cl==[] || List.exists isSuccessPartialCtx_new cl

let isSuccessListFailescCtx cl =
  cl==[] || List.exists isSuccessFailescCtx cl 

let isSuccessListFailescCtx cl =
  (* let cl = list_failesc_context_simplify cl in *)
  let pr = !print_list_failesc_context in
  Debug.no_1 "isSuccessListFailescCtx" pr string_of_bool isSuccessListFailescCtx cl

let isSuccessListFailescCtx_new cl =
  cl==[] || List.exists isSuccessFailescCtx_new cl

let isNonFalseListPartialCtx cl = 
 List.exists (fun (_,ss)-> ((List.length ss) >0) && not (List.for_all (fun (_,c) -> isAnyFalseCtx c) ss )) cl

let isNonFalseListFailescCtx cl = 
 List.exists (fun (_,el,ss)-> 
  let ess = (colapse_esc_stack el)@ss in
  ((List.length ess) >0) && not (List.for_all (fun (_,c) -> isAnyFalseCtx c) ess )) cl

let keep_failure_failesc_context ((c,es,sc): failesc_context) : failesc_context =
  (c,[],[])

let keep_failure_list_failesc_context (lc: list_failesc_context) : list_failesc_context =
  List.map ( keep_failure_failesc_context) lc 

let keep_failure_partial_context ((c,es): partial_context) : partial_context =
  (c,[])

let keep_failure_list_partial_context (lc: list_partial_context) : list_partial_context =
  List.map ( keep_failure_partial_context) lc 



(* this should be applied to merging also and be improved *)
let count_false (sl:branch_ctx list) = List.fold_left (fun cnt (_,oc) -> if (isAnyFalseCtx oc) then cnt+1 else cnt) 0 sl

(*remove v=v from formula*)
let remove_true_conj_pure (p:CP.formula) =
  let ps = CP.split_conjunctions p in
  let ps1 = CP.remove_true_conj_eq ps in
  let ps2 = CP.join_conjunctions ps1 in 
  ps2

(*remove v=v from formula*)
let remove_true_conj_mix_formula_x (f:MCP.mix_formula):MCP.mix_formula = 
  (match f with
    | MCP.MemoF _ -> 
        let _ = print_string ("[cformula.ml][remove_true_conj_mix_formula] Warning: not yet support MCP.MemoF \n") in
        f
    | MCP.OnePF p_f -> (MCP.OnePF (remove_true_conj_pure p_f))
  )

(*remove v=v from formula*)
let remove_true_conj_mix_formula (f:MCP.mix_formula):MCP.mix_formula = 
  Debug.no_1 "remove_true_conj_mix_formula" !print_mix_formula !print_mix_formula 
      remove_true_conj_mix_formula_x f
(*remove v=v from formula*)
let remove_dupl_conj_eq_pure (p:CP.formula) =
  let ps = CP.split_conjunctions p in
  let ps1 = CP.remove_dupl_conj_eq ps in
  let ps2 = CP.join_conjunctions ps1 in 
  ps2
(*remove v=v from formula*)
let remove_dupl_conj_eq_mix_formula_x (f:MCP.mix_formula):MCP.mix_formula = 
  (match f with
    | MCP.MemoF _ -> 
        (*Todo: implement this*)
        (* let _ = print_string ("[cformula.ml][remove_dupl_conj_eq_mix_formula] Warning: not yet support MCP.MemoF \n") in *)
        f
    | MCP.OnePF p_f -> (MCP.OnePF (remove_dupl_conj_eq_pure p_f))
  )
(*remove v=v from formula*)
let remove_dupl_conj_eq_mix_formula (f:MCP.mix_formula):MCP.mix_formula = 
  Debug.no_1 "remove_dupl_conj_eq_mix_formula" !print_mix_formula !print_mix_formula 
      remove_dupl_conj_eq_mix_formula_x f

(*remove v=v from formula*)
let remove_dupl_conj_eq_formula_x (f:formula):formula = 
  let rec helper f = 
  match f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
        Or ({formula_or_f1 = helper f1; formula_or_f2 = helper f2; formula_or_pos = pos})
    | Base b ->
        let new_p = remove_dupl_conj_eq_mix_formula b.formula_base_pure in
        Base {b with formula_base_pure=new_p}
    | Exists b ->
         let new_p = remove_dupl_conj_eq_mix_formula b.formula_exists_pure in
        Exists {b with formula_exists_pure=new_p}
  in helper f
(*remove v=v from formula*)
let remove_dupl_conj_eq_formula (f:formula):formula = 
  Debug.no_1 "remove_dupl_conj_eq_formula" !print_formula !print_formula 
      remove_dupl_conj_eq_formula_x f

(*remove v=v from formula*)
let remove_dupl_conj_estate (estate:entail_state) : entail_state =  {estate with es_pure=remove_dupl_conj_eq_mix_formula estate.es_pure}

  (* Debug.no_1 "remove_dupl_false" pr pr remove_dupl_false sl *)

  

let rank (t:partial_context):float = match t with
  | ( [] ,[] ) -> Err.report_error {Err.error_loc = no_pos;  Err.error_text = " rank: recieved an empty partial_context\n"}
  | ( [] , _ ) -> 1.
  | ( _  ,[] ) -> 0.
  | ( l1 , l2) -> 
    let fn,sn =float (List.length(l1)), float(List.length(l2)) in
    sn /.(fn +. sn)
  
let list_partial_context_union (l1:list_partial_context) (l2:list_partial_context):list_partial_context = remove_dupl_false_pc_list (l1 @ l2)

let list_failesc_context_union (l1:list_failesc_context) (l2:list_failesc_context):list_failesc_context = remove_dupl_false_fe_list (l1 @ l2)

let list_partial_context_union (l1:list_partial_context) (l2:list_partial_context):list_partial_context = 
  let pr x = string_of_int(List.length x) in
  Debug.no_2 "list_partial_context_union" pr pr pr list_partial_context_union l1 l2

let list_failesc_context_union (l1:list_failesc_context) (l2:list_failesc_context):list_failesc_context = 
  let pr x = string_of_int(List.length x) in
  Debug.no_2 "list_failesc_context_union" pr pr pr list_failesc_context_union l1 l2


let select n l = 
  if n<=0 then l 
    else (Gen.BList.take n l) @(List.filter (fun c-> (rank c)==1.) (Gen.BList.drop n l))

let list_partial_context_union_n (l1:list_partial_context) (l2:list_partial_context) n :list_partial_context = 
    select n  (List.sort (fun a1 a2 -> truncate (((rank a2)-.(rank a1))*.1000.)) (l1 @ l2))

let rec merge_fail (f1:branch_fail list) (f2:branch_fail list) : (branch_fail list * path_trace list) =
  match f1,f2 with
    | [],xs -> xs, (List.map (fun (p,_)->p) xs)
    | xs,[] -> xs, (List.map (fun (p,_)->p) xs)
    | (l1,b1)::z1,(l2,b2)::z2 -> 
	if path_trace_eq l1 l2 then 
	  let res,pt = merge_fail z1 z2 in
      (* let fe = {fe_kind = Failure_Bot} in *)
	  ((l1,Or_Reason (b1,b2))::res, l1::pt)
	else if path_trace_lt l1 l2 then 
	  let res,pt = merge_fail z1 f2 in
	    ((l1,b1)::res, l1::pt)
	else let res,pt = merge_fail f1 z2 in
	  ((l2,b2)::res, l2::pt)
    
let merge_partial_context_or ((f1,s1):partial_context) ((f2,s2):partial_context) : partial_context =
  let s1 = remove_dupl_false s1 in
  let s2 = remove_dupl_false s2 in
  let (res_f,pt_fail_list) = merge_fail f1 f2 in  
  let res_s = merge_success s1 s2 in
    (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f1,s1))); *)
    (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f2,s2))); *)
    (* print_string ("\nAfter :"^(Cprinter.summary_partial_context (res_f,res_s))); *)
    (res_f,res_s)

(*
type: esc_stack ->
  esc_stack -> (control_path_id_strict * branch_ctx list) list

*)
let rec merge_esc f e1 e2 = 
  match e1,e2 with
    | [],[] -> []
    | (l1,b1)::z1,(l2,b2)::z2 ->
          let flag = not ((fst l1)==(fst l2)) in
          (if flag then 
            print_endline ("WARNING MISMATCH at merge_esc:\n"^(!print_esc_stack e1)^"\n"^(!print_esc_stack e2)))
          ; (l1,merge_success b1 b2)::(merge_esc f z1 z2)
              (* if not ((fst l1)==(fst l2)) then  *)
              (*   Err.report_error {Err.error_loc = no_pos;  Err.error_text = "malfunction in merge failesc context lbl mismatch\n"} *)
    | _ ->   
          print_string ("stack e1: "^ (f e1)^":"^" stack e2: "^(f e2)^":"^"\n");
          Err.report_error {Err.error_loc = no_pos;  Err.error_text = "mismatched number in merge_esc methd \n"} 

let merge_esc f e1 e2 =
  let pr1 x = "#"^(!print_esc_stack x)^"#" in
  Debug.no_2 "merge_esc" pr1 pr1 pr_no (fun _ _ -> merge_esc f e1 e2) e1 e2 

let merge_failesc_context_or f ((f1,e1,s1):failesc_context) ((f2,e2,s2):failesc_context) : failesc_context =
  let s1 = remove_dupl_false s1 in
  let s2 = remove_dupl_false s2 in
  let (res_f,pt_fail_list) = merge_fail f1 f2 in
  let res_s = merge_success s1 s2 in
  (* WN[((0,""),[])] : this should be added at the beginning of each proc, and not here *)
  (* let e1 = match e1 with | [] -> [((0,""),[])] | _-> e1 in *)
  (* let e2 = match e2 with | [] -> [((0,""),[])] | _-> e2 in *)
  let res_e = merge_esc f e1 e2 in  
  (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f1,s1))); *)
  (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f2,s2))); *)
  (* print_string ("\nAfter :"^(Cprinter.summary_partial_context (res_f,res_s))); *)
  (res_f,res_e,res_s)

let merge_failesc_context_or f (((f1,e1,s1):failesc_context) as x1) (((f2,e2,s2):failesc_context) as x2) : failesc_context =
  let pr = !print_failesc_context in
  Debug.no_2 "merge_failesc_context_or" pr pr pr
      (fun _ _ -> merge_failesc_context_or f (x1) (x2)) x1 x2


let simple_or pc1 pc2 =  ( (fst pc1)@(fst pc2),  remove_dupl_false ((snd pc1)@(snd pc2)) ) 

let list_partial_context_or_naive (l1:list_partial_context) (l2:list_partial_context) : list_partial_context = 
  List.concat (List.map (fun pc1-> (List.map (simple_or pc1) l2)) l1)
  (* List.concat (List.map (fun pc1-> (List.map (merge_partial_context_or pc1) l2)) l1) *)

let list_partial_context_or (l1:list_partial_context) (l2:list_partial_context) : list_partial_context = 
  (* List.concat (List.map (fun pc1-> (List.map (simple_or pc1) l2)) l1) *)
  List.concat (List.map (fun pc1-> (List.map (fun pc2 -> remove_dupl_false_pc (merge_partial_context_or pc1 pc2)) l2)) l1)

let list_partial_context_or (l1:list_partial_context) (l2:list_partial_context) : list_partial_context = 
  let pr x = string_of_int (List.length x) in 
  Debug.no_2_loop "list_partial_context_or" pr pr pr list_partial_context_or l1 l2 

let list_failesc_context_or f (l1:list_failesc_context) (l2:list_failesc_context) : list_failesc_context = 
  List.concat (List.map (fun pc1-> (List.map (fun pc2 -> remove_dupl_false_fe (merge_failesc_context_or f pc1 pc2)) l2)) l1)

let list_failesc_context_or f (l1:list_failesc_context) (l2:list_failesc_context) : list_failesc_context = 
  let pr = !print_list_failesc_context in
  Debug.no_2 "list_failesc_context_or" 
      pr pr pr
      (fun _ _ -> list_failesc_context_or f l1 l2) l1 l2


let add_cond_label_partial_context (c_pid: control_path_id_strict) (c_opt: path_label) ((fl,sl):partial_context) =
  let sl_1 = List.map (fun (pt,ctx) -> (((c_pid,c_opt)::pt),ctx) ) sl in
    (fl,sl_1)

let add_cond_label_failesc_context (c_pid: control_path_id_strict) (c_opt: path_label) ((fl,esc,sl):failesc_context) =
  let sl_1 = List.map (fun (pt,ctx) -> (((c_pid,c_opt)::pt),ctx) ) sl in
    (fl,esc,sl_1)


let add_cond_label_list_partial_context (c_pid: control_path_id) (c_opt: path_label) (lpc:list_partial_context) =
match c_pid with
  | None -> (print_string "empty c_pid here"; lpc)
  | Some pid -> List.map (add_cond_label_partial_context pid c_opt) lpc

  
let add_cond_label_list_failesc_context (c_pid: control_path_id) (c_opt: path_label) (lpc:list_failesc_context) =
match c_pid with
  | None -> (print_string "empty c_pid here"; lpc)
  | Some pid -> List.map (add_cond_label_failesc_context pid c_opt) lpc

let rec build_context ctx f pos = match f with
  | Base _ | Exists _ -> 
	  let es = estate_of_context ctx pos in
		Ctx ({es with es_formula = f;es_unsat_flag =false})
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = _}) -> 
	  let c1 = build_context ctx f1 pos in
	  let c2 = build_context ctx f2 pos in
		or_context c1 c2
	
(* 09.05.2008 ---*)		

and set_context_formula (ctx : context) (f : formula) : context = match ctx with
  | Ctx es -> begin
	  match f with
		| Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
			let cf1 = set_context_formula ctx f1 in
			let cf2 = set_context_formula ctx f2 in
			  mkOCtx  cf1 cf2 pos
		| _ -> Ctx {es with es_formula = f;es_unsat_flag =false;}
	end
  | OCtx (c1, c2) ->
	  let nc1 = set_context_formula c1 f in
	  let nc2 = set_context_formula c2 f in
		mkOCtx nc1 nc2 (pos_of_formula f) 

(* and get_estate_must_match (es : entail_state) : bool =  *)
(* 	es.es_must_match *)

(* and set_estate_must_match (es: entail_state) : entail_state = 	 *)
(* 	let es_new = {es with es_must_match = true} in *)
(* 		es_new *)

and moving_ivars_to_evars (estate:entail_state) (anode:h_formula) : entail_state =
    let arg_vars = h_fv anode in
    let (removed_ivars,remaining_ivars) = List.partition (fun v -> CP.mem v arg_vars) estate.es_ivars in
    {estate with es_evars = estate.es_evars@removed_ivars; es_ivars = remaining_ivars; } 

(* and set_context_must_match (ctx : context) : context = match ctx with  *)
(*   | Ctx (es) -> Ctx(set_estate_must_match es) *)
(*   | OCtx (ctx1, ctx2) -> OCtx((set_context_must_match ctx1), (set_context_must_match ctx2)) *)

(* and set_context_must_match (ctx : context) : context =  *)
(*   set_context (fun es -> {es with es_must_match = true}) ctx *)

and set_estate f (es: entail_state) : entail_state = 	
	f es 

and set_context f (ctx : context) : context = match ctx with 
  | Ctx (es) -> Ctx(set_estate f es)
  | OCtx (ctx1, ctx2) -> mkOCtx (set_context f ctx1)  (set_context f ctx2) no_pos

and set_list_context f (ctx : list_context) : list_context = match ctx with
  | FailCtx f -> ctx
  | SuccCtx l -> let nl = List.map (set_context f) l in SuccCtx nl

and estate_opt_of_list_context (ctx : list_context) : entail_state option = 
  match ctx with
  | SuccCtx (c::_) -> estate_opt_of_context c
  | _ -> None

and estate_opt_of_context (ctx : context) = match ctx with
  | Ctx es -> Some es
  | _ -> None

and estate_of_context (ctx : context) (pos : loc) = match ctx with
  | Ctx es -> es
  | _ -> Err.report_error {Err.error_loc = pos;
						   Err.error_text = "estate_of_context: disjunctive or fail context"}

and flow_formula_of_ctx (ctx : context) (pos : loc) = match ctx with
  | Ctx es -> flow_formula_of_formula es.es_formula
  | _ -> Err.report_error {Err.error_loc = pos;
						   Err.error_text = "flow_of_context: disjunctive or fail context"}

and set_flow_in_ctx_override (c:context) (f:flow_formula) :context = match c with
	| Ctx c1-> Ctx {c1 with es_formula = set_flow_in_formula_override f c1.es_formula}
	| OCtx (c1,c2) -> OCtx ((set_flow_in_ctx_override c1 f),(set_flow_in_ctx_override c2 f))
		
and change_flow_ctx from_fl to_fl ctx_list = 
	let rec helper c = match c with
		| Ctx c -> Ctx {c with es_formula = substitute_flow_in_f to_fl from_fl c.es_formula;}
		| OCtx (c1,c2)-> OCtx ((helper c1), (helper c2)) in
	List.map helper ctx_list

and change_flow_into_ctx to_fl ctx =
  match ctx with
	| Ctx c -> Ctx {c with es_formula = substitute_flow_into_f to_fl c.es_formula;}
	| OCtx (c1,c2)-> OCtx ((change_flow_into_ctx to_fl c1), (change_flow_into_ctx to_fl c2))

and change_flow_into_ctx_list to_fl ctx_list =
	List.map (change_flow_into_ctx to_fl) ctx_list


and convert_must_failure_to_value (l:list_context) ante_flow conseq (bug_verified:bool): list_context =
  match l with
  | FailCtx ft ->
        (match (get_must_es_msg_ft ft) with
          | Some (es,msg) ->
              begin
                  match bug_verified with
                    | true ->
                        (*change flow to the flow at the beginning*)
                        let new_ctx_lst = change_flow_into_ctx_list ante_flow [Ctx es] in
                        SuccCtx new_ctx_lst
                    | false ->
                        (*update es_must_error*)
                        SuccCtx [Ctx {es with es_must_error = Some (msg,ft) } ]
              end
          | _ ->  l)
  | SuccCtx ctx_lst -> if not bug_verified then l else
        begin
            let fc_template = {
		        fc_message = "INCONSISTENCY : expected failure but success instead";
		        fc_current_lhs  =  empty_es (mkTrueFlow ()) Lab2_List.unlabelled no_pos;
		        fc_prior_steps = [];
		        fc_orig_conseq  = conseq;
		        fc_current_conseq = mkTrue (mkTrueFlow()) no_pos;
		        fc_failure_pts =  []} in
            let ft_template = (Basic_Reason (fc_template,
                                             mk_failure_must "INCONSISTENCY : expected failure but success instead" "")) in
            let new_ctx_lst = set_must_error_from_ctx ctx_lst "INCONSISTENCY : expected failure but success instead"
              ft_template in
            SuccCtx new_ctx_lst
        end
(*23.10.2008*)

and compose_context_formula_x (ctx : context) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) : context = match ctx with
  | Ctx es -> begin
	  match phi with
		| Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
			let new_c1 = compose_context_formula_x ctx phi1 x flow_tr pos in
			let new_c2 = compose_context_formula_x ctx phi2 x flow_tr pos in
			let res = (mkOCtx new_c1 new_c2 pos ) in
			  res
		| _ -> let new_es_f,new_history = compose_formula_new es.es_formula phi x flow_tr es.es_history pos in
            Ctx {es with es_formula = new_es_f;
                es_history = new_history;
                es_unsat_flag =false;}
	end
  | OCtx (c1, c2) -> 
	  let new_c1 = compose_context_formula_x c1 phi x flow_tr pos in
	  let new_c2 = compose_context_formula_x c2 phi x flow_tr pos in
	  let res = (mkOCtx new_c1 new_c2 pos) in
		res

and compose_context_formula (ctx : context) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) : context = 
  let pr1 = !print_context_short in
  let pr2 = !print_formula in
  let pr3 = !print_svl in
  Debug.no_3 "compose_context_formula" pr1 pr2 pr3 pr1 (fun _ _ _ -> compose_context_formula_x ctx phi x flow_tr pos) ctx phi x

(*TODO: expand simplify_context to normalize by flow type *)
(* and simplify_context_0 (ctx:context):context =  *)
(* 	if (allFalseCtx ctx) then ctx (\* (false_ctx (mkFalseFlow) no_pos) *\) *)
(* 								else  ctx *)
		
and normalize_es (f : formula) (pos : loc) (result_is_sat:bool) (es : entail_state): context = 
	Ctx {es with es_formula = normalize 3 es.es_formula f pos; es_unsat_flag = es.es_unsat_flag&&result_is_sat} 

and normalize_es_combine (f : formula) (result_is_sat:bool)(pos : loc) (es : entail_state): context =
  (* let _ = print_string ("\nCformula.ml: normalize_es_combine") in *)
	Ctx {es with es_formula = normalize_combine es.es_formula f pos; es_unsat_flag = es.es_unsat_flag&&result_is_sat;} 
		
and combine_and (f1:formula) (f2:MCP.mix_formula) :formula*bool = match f1 with
	| Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = pos}) ->
	 print_string ("malfunction: inner or has not been converted to a CtxOr!");
      Error.report_error {
		Error.error_loc = pos;
		Error.error_text = ("malfunction: inner or has not been converted to a CtxOr!") }
	| Base ({ formula_base_pure = p;} as b) -> 
			let r1,r2 = (combine_and_pure f1 p f2) in
			(Base{b with formula_base_pure = r1;}, r2)					 
	| Exists ({formula_exists_qvars = evars;
			   formula_exists_pure = p ;} as b) -> 
			if (List.length (Gen.BList.intersect_eq (=) (MCP.mfv f2) evars))=0 then
				let r1,r2 = combine_and_pure f1 p f2 in
				(Exists {b with formula_exists_pure = r1;},r2)	  
				else 
					let rf1 = rename_bound_vars f1 in
					(combine_and rf1 f2)
		
and normalize_no_rename_context_formula (ctx : context) (p : MCP.mix_formula) : context = 
	let rec push_pure (f:formula):formula = match f with
		| Base b-> Base {b with formula_base_pure = MCP.merge_mems p b.formula_base_pure true;}
		| Exists b -> Exists {b with formula_exists_pure = MCP.merge_mems p b.formula_exists_pure true;}
		| Or b -> Or {
				   formula_or_f1 = push_pure b.formula_or_f1;
				   formula_or_f2 = push_pure b.formula_or_f2;
				   formula_or_pos = b.formula_or_pos
				}in
match ctx with
  | Ctx es -> Ctx {es with es_formula = push_pure es.es_formula;es_unsat_flag  =false;}
  | OCtx (c1, c2) ->
	  let nc1 = normalize_no_rename_context_formula c1 p in
	  let nc2 = normalize_no_rename_context_formula c2 p in
	  let res = mkOCtx nc1 nc2 no_pos in
		res
		
(* -- 17.05.2008 *)
and normalize_clash_es (f : formula) (pos : loc) (result_is_sat:bool)(es:entail_state): context =
  (* let _ = print_string ("\nCformula.ml: normalize_clash_es") in *)
  match f with
	| Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
		let new_c1 = normalize_clash_es phi1 pos result_is_sat es in
		let new_c2 = normalize_clash_es phi2 pos result_is_sat es in
		let res = (mkOCtx new_c1 new_c2 pos) in
		res
	| _ -> Ctx {es with es_formula = normalize_only_clash_rename es.es_formula f pos; es_unsat_flag =es.es_unsat_flag&&result_is_sat}
	
(* 17.05.2008 -- *)

(* and formula_of_context ctx0 = match ctx0 with *)
(*   | OCtx (c1, c2) -> *)
(* 	  let f1 = formula_of_context c1 in *)
(* 	  let f2 = formula_of_context c2 in *)
(* 		mkOr f1 f2 no_pos *)
(*   | Ctx es -> es.es_formula *)
 
(*LDK: add es_pure into residue*)
and formula_of_context_x ctx0 = match ctx0 with
  | OCtx (c1, c2) ->
	  let f1 = formula_of_context_x c1 in
	  let f2 = formula_of_context_x c2 in
		mkOr f1 f2 no_pos
  | Ctx es -> let m = CP.mk_varperm_zero es.es_var_zero_perm no_pos in
      let mix_f = MCP.merge_mems es.es_pure (MCP.mix_of_pure m) true in
      add_mix_formula_to_formula mix_f es.es_formula
	  	
and formula_of_context ctx0 = 
  let pr = !print_context_short in
    Debug.no_1 "formula_of_context" pr !print_formula formula_of_context_x ctx0

(*LDK: add es_pure into residue*)
and formula_trace_of_context_x ctx0 = match ctx0 with
  | OCtx (c1, c2) ->
	  let f1,trace1 = formula_trace_of_context_x c1 in
	  let f2,trace2  = formula_trace_of_context_x c2 in
	  let f = mkOr f1 f2 no_pos in
      let trace = trace1@["||OR||"]@trace2 in
      (f,trace)
  | Ctx es -> 
      let orig_f = es.es_formula in
      let esvm = es.es_var_measures in  (* (term_ann * CP.exp list * CP.exp list) option;  *)
	  let m = CP.mk_varperm_zero es.es_var_zero_perm no_pos in
	  let mix_f = MCP.merge_mems es.es_pure (MCP.mix_of_pure m) true in
      let mix_f = match esvm with
        | None -> mix_f
        | Some (ta,l1,l2) ->
            let m = CP.mkPure (CP.mkLexVar ta l1 l2 no_pos) in
            Debug.trace_hprint (add_str "es_var_measures:" !CP.print_formula) m no_pos;
            MCP.merge_mems mix_f (MCP.mix_of_pure m) true in
      (*TO CHECK*)
      let f = add_mix_formula_to_formula mix_f orig_f in
      let trace = es.es_trace in
      Debug.trace_hprint (add_str "es_formula:" !print_formula) orig_f no_pos;
      DD.trace_hprint (add_str "es_pure:" !print_mix_formula) es.es_pure no_pos;
      (f,trace)

and formula_trace_of_context ctx0 = 
  let pr = !print_context_short in
  let pr2 (f,_) = !print_formula f in
    Debug.no_1 "formula_trace_of_context" pr pr2 formula_trace_of_context_x ctx0

(* -- added 16.05.2008 *)  
and formula_of_list_context (ctx : list_context) : formula =  match ctx with
  | FailCtx _ -> mkTrue (mkTrueFlow()) no_pos
  | SuccCtx ls -> List.fold_left (fun a c-> mkOr (formula_of_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) ls
(* 16.05.2008 -- *)

and list_formula_of_list_context (ctx : list_context) : list_formula =  match ctx with
  | FailCtx _ -> []
  | SuccCtx ls -> List.map (formula_of_context) ls

and list_formula_trace_of_list_context (ctx : list_context) : (context * (formula*formula_trace)) list =  match ctx with
  | FailCtx _ -> []
  | SuccCtx ls -> List.map (fun c -> (c,formula_trace_of_context c)) ls

(* filter out partial failure first *)
and list_formula_of_list_partial_context (ls : list_partial_context) : list_formula =  
  let ls = List.filter (fun (f,s) -> Gen.is_empty f) ls in
  List.map (formula_of_partial_context) ls

(* assumes that all are successes, may need to filter *)
and list_formula_of_list_failesc_context (ls : list_failesc_context) : list_formula =  
  let ls = List.filter (fun (f,es,s) -> Gen.is_empty f) ls in
  List.map (formula_of_failesc_context) ls

and formula_of_list_partial_context (ls : list_partial_context) : formula =  
  List.fold_left (fun a c-> mkOr (formula_of_partial_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) ls

and formula_of_list_failesc_context (ls : list_failesc_context) : formula =  
  List.fold_left (fun a c-> mkOr (formula_of_failesc_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) ls

(* below ignored the escaping state! *)
and formula_of_failesc_context ((_,_,sl) : failesc_context) : formula =  
  List.fold_left (fun a (_,c)-> mkOr (formula_of_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) sl
          
and formula_of_partial_context ((fl,sl) : partial_context) : formula =  
  List.fold_left (fun a (_,c)-> mkOr (formula_of_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) sl

and disj_count_ctx (ctx0 : context) = match ctx0 with
  | OCtx (c1, c2) ->
	  let t1 = disj_count_ctx c1 in
	  let t2 = disj_count_ctx c2 in
		1 + t1 + t2
  | Ctx es -> disj_count es.es_formula

(*
and find_type_var (tc : h_formula) (v : ident) : CP.spec_var option = match tc with
  | Star ({h_formula_star_h1 = h1;
		   h_formula_star_h2 = h2}) -> begin
	  let tmp1 = find_type_var h1 v in
		match tmp1 with
		  | Some _ -> tmp1
		  | None -> find_type_var h2 v
	end
  | DataNode ({h_formula_data_arguments = args}) -> Some (List.hd args)
  | ViewNode _ | HTrue | HFalse -> None
*)

let rec set_flow_in_context_override f_f ctx = match ctx with
	| Ctx es -> Ctx {es with es_formula = (set_flow_in_formula_override f_f es.es_formula)}
	| OCtx (c1,c2) -> OCtx ((set_flow_in_context_override f_f c1),(set_flow_in_context_override f_f c2))



(* order nodes in topological order *)

module Node = struct
  type t = h_formula
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module NG = Graph.Imperative.Digraph.Concrete(Node)
module TopoNG = Graph.Topological.Make(NG)

(*
  return the same formula with nodes rearranged in topological
  order based on the points-to relation of the heap nodes.
*)
(*
let topologize_formula (h0 : h_formula) : h_formula =
  let g = NG.create () in
*)

(*************************************************************************************************************************
	05.06.2008:
	Utilities for existential quantifier elimination: 
	- before we were only searching for substitutions of k form v1 = v2 and then substitute ex v1. P(v1) --> P(v2)
	- now, we want to be more aggressive and search for substitutions of the form v1 = exp2; however, we can only apply these substitutions to the pure part 
	(due to the way shape predicates are recorded --> root pointer and args are suppose to be spec vars)
*************************************************************************************************************************)	 
let rec subst_exp sst (f : formula) = match sst with
  | s :: rest -> 
	  let new_f = subst_exp rest (apply_one_exp s f) in
	  (*let fv_new_f = fv new_f in
		 	if List.mem (fst s) fv_new_f then 
		 		let f = add_quantifiers [(fst s)] new_f in
		 		let qvars, base_f = split_quantifiers f in
		 		let h, p, t = split_components base_f in
		 	 		mkExists qvars h (CP.mkAnd p (CP.mkEqExp (CP.mkVar (fst s) no_pos) (snd s) no_pos) no_pos) t no_pos 
			else*) new_f
  | [] -> f 
  
and subst_var_exp (fr, t) (o : CP.spec_var) = if CP.eq_spec_var fr o then t else o

and apply_one_exp_one_formula ((fr, t) as s : (CP.spec_var * CP.exp)) (f : one_formula) = 
  let base = formula_of_one_formula f in
  let rs = apply_one_exp s base in (*TO CHECK: how about formula_thread*)
  let one_f = (one_formula_of_formula rs f.formula_thread) in
  {one_f with formula_ref_vars = f.formula_ref_vars}

and apply_one_exp ((fr, t) as s : (CP.spec_var * CP.exp)) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
      Or ({formula_or_f1 = apply_one_exp s f1; formula_or_f2 =  apply_one_exp s f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h; 
		   formula_base_pure = p; 
		   formula_base_type = t;
       formula_base_and = a;
		   formula_base_flow = fl;
		   formula_base_label = lbl;
		   formula_base_pos = pos}) -> 
    Base ({formula_base_heap = h; 
			formula_base_pure = MCP.memo_apply_one_exp s p;
            formula_base_and = List.map (apply_one_exp_one_formula s) a;
			formula_base_flow = fl;
		 	formula_base_type = t;
			formula_base_label = lbl;
		 	formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
			 formula_exists_heap = qh; 
			 formula_exists_pure = qp; 
			 formula_exists_type = tconstr;
       formula_exists_and = a;
			 formula_exists_flow = fl;
			 formula_exists_label = lbl;
			 formula_exists_pos = pos}) -> 
	  if List.mem (CP.name_of_spec_var fr) (List.map CP.name_of_spec_var qsv) then f 
	  else 
      Exists ({formula_exists_qvars = qsv; 
					formula_exists_heap =  qh; 
					formula_exists_pure = MCP.memo_apply_one_exp s qp; 
					formula_exists_type = tconstr;
                    formula_exists_and = List.map (apply_one_exp_one_formula s) a;
					formula_exists_flow = fl;
					formula_exists_label = lbl;
					formula_exists_pos = pos})

let rec struc_to_formula_gen (f:struc_formula):(formula*formula_label option list) list = 
	let rec get_label_f f = match f with
		| Or b-> (get_label_f b.formula_or_f1)@(get_label_f b.formula_or_f2)
		| Base{formula_base_label = l}| Exists{formula_exists_label = l} -> [l]in
	match f with
		| ECase b-> 
			  let r = List.concat (List.map 
				  (fun (c1,c2)-> 
					if (isConstEFalse c2) then []
					else
					let np = (MCP.memoise_add_pure_N (MCP.mkMTrue b.formula_case_pos) c1) in
					let npf = mkBase HEmp np TypeTrue (mkTrueFlow ()) [] b.formula_case_pos in
					let l = struc_to_formula_gen c2 in
					List.map (fun (c1,c2) -> (normalize_combine npf c1 no_pos,c2)) l) b.formula_case_branches) in
			  List.map (fun (c1,c2)-> ( push_exists b.formula_case_exists c1,c2)) r 
		| EBase b-> 
				let nf,nl = b.formula_struc_base,(get_label_f b.formula_struc_base) in
				let f c = push_exists b.formula_struc_exists (normalize_combine nf c b.formula_struc_pos) in
				let lc = fold_opt struc_to_formula_gen b.formula_struc_continuation in
				(match lc with
				  | [] -> [(f nf, nl)]
				  | _ -> List.map (fun (c1,c2)-> (f c1,nl@c2)) lc)
		| EAssume (_,b,_)-> [(b,[None])]
		| EInfer b -> struc_to_formula_gen b.formula_inf_continuation
		| EOr b  -> (struc_to_formula_gen b.formula_struc_or_f1)@(struc_to_formula_gen b.formula_struc_or_f2)
		| EList b -> fold_l_snd struc_to_formula_gen b 
	
(* let struc_to_formula f0 :formula = formula_of_disjuncts (fst (List.split (struc_to_formula_gen f0))) *)
(* TO-CHECK : why is above overridden *)

let list_of_disjs (f0 : formula) : formula list =
  let rec helper f disjs = match f with
    | Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos} ->
      let tmp1 = helper f2 disjs in
      let tmp2 = helper f1 tmp1 in
      tmp2
    | _ -> f :: disjs
  in
  helper f0 []

let disj_of_list (xs : formula list) pos : formula = 
  let rec helper xs r = match xs with
    | [] -> r
    | x::xs -> mkOr x (helper xs r) pos
  in
  match xs with
  | [] -> mkTrue (mkTrueFlow ()) pos
  | x::xs -> helper xs x

let rec split_conjuncts (f:formula):formula list = match f with 
  | Or b -> (split_conjuncts b.formula_or_f1)@(split_conjuncts b.formula_or_f2)
  | _ -> [f] 
  
let list_of_disjuncts f = split_conjuncts f

let join_conjunct_opt l = match l with
  | [] -> None
  | h::t -> Some (List.fold_left (fun a c-> mkOr c a no_pos) h t)

let join_star_conjunctions (hs : h_formula list) : h_formula  = 
  List.fold_left(fun a c-> mkStarH a c no_pos) HEmp hs

let join_star_conjunctions_opt_x (hs : h_formula list) : (h_formula option)  = 
  match hs with
    | [] -> None
    | x::xs -> Some (List.fold_left (fun a c -> mkStarH a c no_pos ) x xs)

	
let join_star_conjunctions_opt (hs : h_formula list) : (h_formula option)  =  
  let rec pr1 xs = 
    match xs with
      | [] -> ""
      | x::xs1 -> (!print_h_formula x) ^ "|*|" ^ pr1 xs1
  in
  let pr2 = pr_option !print_h_formula in
  Debug.no_1 "join_star_conjunctions_opt" pr1 pr2
  join_star_conjunctions_opt_x hs


let split_star_conjunctions_x (f:h_formula): (h_formula list) =
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

let split_star_conjunctions (f:h_formula): (h_formula list) = 
  let rec pr xs = 
    match xs with
      | [] -> ""
      | x::xs1 -> (!print_h_formula x) ^ "|*|" ^ pr xs1
  in
  Debug.no_1 "split_star_conjunctions" !print_h_formula pr
  split_star_conjunctions_x f

let type_of_formula (f: formula) : formula_type =
  if (isAnyConstFalse f) then Simple
  else match f with
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


let rec struc_to_view_un_s (f0:struc_formula):(formula*formula_label) list = 
  let ifo = (struc_to_formula_gen f0) in
  List.map (fun (c1,c2)-> 
	let c2 = List.fold_left (fun a c2-> match c2 with | None -> a | Some s-> s::a) [] c2 in
	match c2 with
	| [x] -> (c1,x)
	| _ ->  Err.report_error {Err.error_loc = no_pos;  Err.error_text = " mismatch in view labeling \n"} ) ifo

(* proc will convert implicit/explicit vars to existential *)
let rec struc_to_formula_x (f:struc_formula):formula = match f with
		| ECase b-> 
		   let r = 
			if (List.length b.formula_case_branches) >0 then
			  List.fold_left (fun a (c1,c2)->  
				if (isConstEFalse c2) then a
				else
					let c1 = MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) c1 in
					(mkOr a (normalize_combine (mkBase HEmp c1 TypeTrue (mkTrueFlow ()) [] b.formula_case_pos ) (struc_to_formula_x c2) b.formula_case_pos) 
						b.formula_case_pos) ) (mkFalse (mkFalseFlow) b.formula_case_pos) b.formula_case_branches 
			else mkTrue (mkTrueFlow ()) b.formula_case_pos in
		   push_exists b.formula_case_exists r 
		| EBase b-> 
				let e = match b.formula_struc_continuation with
					| Some e -> normalize_combine b.formula_struc_base (struc_to_formula_x e) b.formula_struc_pos 
					| None -> b.formula_struc_base in
                (* is it necessary to also push the implicit vars? *)
				push_exists (b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@b.formula_struc_exists) e 
		| EAssume (_,b,_)-> b 
		| EInfer b -> struc_to_formula_x b.formula_inf_continuation 
	    | EOr b -> mkOr (struc_to_formula_x b.formula_struc_or_f1) (struc_to_formula_x b.formula_struc_or_f2) b.formula_struc_or_pos
		| EList b -> formula_of_disjuncts (fold_l_snd (fun c-> [struc_to_formula_x c]) b)

and struc_to_formula f0 :formula = 
  let pr1 = !print_struc_formula in
  let pr2 = !print_formula in
  Debug.no_1 "struc_to_formula" pr1 pr2 struc_to_formula_x f0

let rec normalize_struc cont base: struc_formula = match cont with
  | ECase b -> 
    ECase {b with formula_case_branches = 
      List.map (fun (p,c) -> (p, normalize_struc c base)) b.formula_case_branches}
  | EBase b ->
    let new_base = normalize_combine base.formula_struc_base b.formula_struc_base base.formula_struc_pos in
    (match b.formula_struc_continuation with
      | None -> EBase base
      | Some c -> normalize_struc c {b with formula_struc_base = new_base})
  | EAssume _ -> EBase base
  | EInfer b -> 
    EInfer {b with formula_inf_continuation = normalize_struc b.formula_inf_continuation base}
  | EOr b -> EOr {b with formula_struc_or_f1 = normalize_struc b.formula_struc_or_f1 base;
                         formula_struc_or_f2 = normalize_struc b.formula_struc_or_f2 base}
  | EList b -> EList (List.map (fun (l,c) -> (l,normalize_struc c base)) b)

(* Convert struc_formula to pre/post structure *)
let rec struc_to_prepost_x (f:struc_formula): struc_formula = match f with
  | ECase b -> 
    ECase {b with formula_case_branches = 
      List.map (fun (p,c) -> (p, struc_to_prepost_x c)) b.formula_case_branches}
  | EBase b ->
    let new_b = match b.formula_struc_continuation with
      | None -> f
      | Some c -> normalize_struc c b
    in
    new_b
  | EAssume _ -> f 
  | EInfer b -> EInfer {b with formula_inf_continuation = struc_to_prepost b.formula_inf_continuation}
  | EOr b -> EOr {b with formula_struc_or_f1 = struc_to_prepost_x b.formula_struc_or_f1;
                         formula_struc_or_f2 = struc_to_prepost_x b.formula_struc_or_f2}
  | EList b -> EList (List.map (fun (l,c) -> (l,struc_to_prepost_x c)) b)

and struc_to_prepost f0 : struc_formula = 
  let pr = !print_struc_formula in
  Debug.no_1 "struc_to_prepost" pr pr struc_to_prepost_x f0

(* An Hoa : construct pre-condition from a structured spec formula *)
let rec struc_to_precond_formula (f : struc_formula) : formula = match f with
	| ECase b ->
		let fold_function a (c1, c2) = if (isConstEFalse c2) then a 
			else 
				let c1 = MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) c1 in 
					(mkOr a (normalize_combine (mkBase HEmp c1 TypeTrue (mkTrueFlow ()) [] b.formula_case_pos) (struc_to_precond_formula c2) b.formula_case_pos) 
					     b.formula_case_pos) in
		let r = if (List.length b.formula_case_branches) >0 then
			List.fold_left fold_function (mkFalse (mkFalseFlow) b.formula_case_pos) b.formula_case_branches 
		else mkTrue (mkTrueFlow ()) b.formula_case_pos in
			push_exists b.formula_case_exists r
	| EBase b -> 
		let e = match b.formula_struc_continuation with
			| None -> b.formula_struc_base 
			| Some e-> normalize_combine b.formula_struc_base (struc_to_precond_formula e) b.formula_struc_pos in
		push_exists (b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@b.formula_struc_exists) e 
	| EAssume (_,b,_) -> (* Eliminate assume by making it true *) formula_of_heap HEmp no_pos 
    | EInfer b -> struc_to_precond_formula b.formula_inf_continuation
	| EOr b -> mkOr (struc_to_precond_formula b.formula_struc_or_f1) (struc_to_precond_formula b.formula_struc_or_f2) b.formula_struc_or_pos
	| EList b -> formula_of_disjuncts (fold_l_snd (fun c-> [struc_to_precond_formula c]) b)
(* An Hoa : end of pre-condition construction *)

and formula_to_struc_formula (f:formula):struc_formula =
	let rec helper (f:formula):struc_formula = match f with
		| Base b-> EBase {
			 		formula_struc_explicit_inst =[];
		 			formula_struc_implicit_inst = [];
					formula_struc_exists = [];
		 			formula_struc_base = f;
					formula_struc_continuation = None;
		 			formula_struc_pos = b.formula_base_pos}
		| Exists b-> EBase {
			 		formula_struc_explicit_inst =[];
		 			formula_struc_implicit_inst = [];
					formula_struc_exists = [];
		 			formula_struc_base = f;
					formula_struc_continuation = None;
		 			formula_struc_pos = b.formula_exists_pos}
		| Or b->  EOr {formula_struc_or_f1 = helper b.formula_or_f1; formula_struc_or_f2 = helper b.formula_or_f2; formula_struc_or_pos = b.formula_or_pos} in			
	(helper f)

and plug_ref_vars (w:Cpure.spec_var list) (f:struc_formula) :struc_formula = 
	let rec filter_quantifiers w f = match f with
	| Base _ -> f
	| Exists b -> Exists {b with formula_exists_qvars = Gen.BList.difference_eq (=) b.formula_exists_qvars w;}
	| Or b -> Or {b with 
						formula_or_f1 = filter_quantifiers w b.formula_or_f1;
						formula_or_f2 = filter_quantifiers w b.formula_or_f2;}in
	match f with
	| EAssume (_,b,t)->  EAssume (w,(filter_quantifiers  w b),t)
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> (c1,(plug_ref_vars w c2))) b.formula_case_branches;}
	| EBase b -> EBase {b with formula_struc_continuation = map_opt (plug_ref_vars w) b.formula_struc_continuation}
    | EInfer b -> EInfer {b with formula_inf_continuation = plug_ref_vars w b.formula_inf_continuation}
	| EOr b -> EOr {b with formula_struc_or_f1 = plug_ref_vars w b.formula_struc_or_f1; formula_struc_or_f2 = plug_ref_vars w b.formula_struc_or_f2; }
	| EList b -> EList (map_l_snd (plug_ref_vars w) b)


and count_or c = match c with
			| Ctx _ -> 1
			| OCtx (c1,c2) -> (count_or c1)+(count_or c2)		
			
and find_false_ctx ctx pos =
  match ctx with
   | FailCtx _ -> ()
   | SuccCtx ctx ->
	if (List.exists isAnyFalseCtx ctx) then 
    false_ctx_line_list := Gen.BList.remove_dups_eq (=) (pos::!false_ctx_line_list) else ()

and find_false_list_failesc_ctx (ctx:list_failesc_context) pos =
    if (List.exists isAnyFalseFailescCtx ctx) then 
      false_ctx_line_list := Gen.BList.remove_dups_eq (=) (pos::!false_ctx_line_list) 
    else ()
  

and guard_vars (f:struc_formula) = 
	let rdv = Gen.BList.remove_dups_eq (=) in
	match f with
	| ECase b-> rdv (List.fold_left (fun a (c1,c2)-> a@(Cpure.fv c1)@(guard_vars c2)) [] b.formula_case_branches)
	| EBase b -> Gen.BList.difference_eq (=) (fold_opt guard_vars b.formula_struc_continuation) b.formula_struc_exists
	| EAssume b-> []
	| EInfer b -> guard_vars b.formula_inf_continuation
	| EOr b -> rdv ((guard_vars b.formula_struc_or_f1)@(guard_vars b.formula_struc_or_f2))
	| EList b-> rdv (fold_l_snd guard_vars b)
	
and set_unsat_flag (ctx:context) (nf:bool):context = match ctx with
| OCtx(c1,c2)-> OCtx ((set_unsat_flag c1 nf),(set_unsat_flag c2 nf))
| Ctx c-> Ctx {c with es_unsat_flag = nf}

and filter_heap (f:formula):formula option = match f with
  | Or b-> begin 
      match (filter_heap b.formula_or_f1) with
	| None -> None (*(filter_heap b.formula_or_f2)*)
	| Some d1-> match (filter_heap b.formula_or_f2) with
	    | None -> None
	    | Some d2 -> Some (mkOr d1 d2 b.formula_or_pos)
    end
  | Base b-> begin 
      match b.formula_base_heap with
	| Star _
	| Conj _
	| Phase _    
	| DataNode _ 
	| ViewNode _ 
	| HRel _ (*vp*)
	| Hole _ -> None
	| HTrue 
	| HFalse
  | HEmp -> Some f
    end
  | Exists b-> 
      begin
	match b.formula_exists_heap with
	  | Star _
	  | Conj _
	  | Phase _    
	  | DataNode _ 
	  | ViewNode _ 
	  | HRel _ (*vp*)
	  | Hole _ -> None
	  | HTrue 
	  | HFalse
    | HEmp -> Some f
      end

and set_es_evars (c:context)(v:Cpure.spec_var list):context = 
  match c with
	| OCtx (c1,c2)-> OCtx ((set_es_evars c1 v),(set_es_evars c2 v))
	| Ctx e -> Ctx {e with es_evars = v}

  
and case_to_disjunct f  =
  let pr = !print_struc_formula in
  Debug.no_1 "case_to_disjunct" pr pr case_to_disjunct_x f 

and case_to_disjunct_x (f:struc_formula):struc_formula  =
  let rec push_pure c (f:struc_formula):struc_formula =  match f with
    | ECase _ -> f (*this should never occur*) 
    | EBase b-> EBase {b with formula_struc_base = 
      normalize_combine 
        b.formula_struc_base 
          (formula_of_pure_N c no_pos) 
          no_pos}
    | _ -> EBase {
       formula_struc_explicit_inst = [];
       formula_struc_implicit_inst = [];
       formula_struc_exists = [];
       formula_struc_base = formula_of_pure_N c no_pos;
       formula_struc_continuation = Some f;
       formula_struc_pos = no_pos;
    }	 in
  match f with
    | ECase b-> 
		let l = List.map (fun (c1,c2)-> push_pure c1 (case_to_disjunct_x c2)) b.formula_case_branches in
		(match l with 
		  | [] -> failwith "unexpected empty case struc"
		  | h::t -> List.fold_left (fun a c-> EOr {formula_struc_or_f1 = a;formula_struc_or_f2=c; formula_struc_or_pos = no_pos}) h t)
    | EBase b-> EBase {b with formula_struc_continuation = map_opt case_to_disjunct_x b.formula_struc_continuation}
	| EOr b -> EOr {b with formula_struc_or_f1 = case_to_disjunct_x b.formula_struc_or_f1;
						formula_struc_or_f2 = case_to_disjunct_x b.formula_struc_or_f2;}
    | EList b -> EList (map_l_snd case_to_disjunct_x b)
	| _ -> f

(* start label - can be simplified *)	
let get_start_label ctx = match ctx with
  | FailCtx _ -> ""
  | SuccCtx sl -> 
    let rec helper c= match c with
      | Ctx e -> if (List.length e.es_path_label)==0 then "" else snd(fst (Gen.BList.list_last e.es_path_label))
      | OCtx (c1,c2) -> helper c1 in
	helper (List.hd sl)

let get_start_partial_label (ctx:list_partial_context) =
  let rec helper c= match c with
    | Ctx e -> if (List.length e.es_path_label)==0 then "" else snd(fst (Gen.BList.list_last e.es_path_label))
    | OCtx (c1,c2) -> helper c1 in
  let pc = List.hd ctx in
    if (rank pc) < 1. then ""
    else let (_,ls) = pc in
      helper (snd (List.hd ls))

	
let rec replace_heap_formula_label nl f = match f with
  | Star b -> Star {b with 
		      h_formula_star_h1 = replace_heap_formula_label nl b.h_formula_star_h1; 
		      h_formula_star_h2 = replace_heap_formula_label nl b.h_formula_star_h2; }
  | Phase b -> Phase {b with 
		      h_formula_phase_rd = replace_heap_formula_label nl b.h_formula_phase_rd; 
		      h_formula_phase_rw = replace_heap_formula_label nl b.h_formula_phase_rw; }
  | Conj b -> Conj {b with 
		      h_formula_conj_h1 = replace_heap_formula_label nl b.h_formula_conj_h1; 
		      h_formula_conj_h2 = replace_heap_formula_label nl b.h_formula_conj_h2; }
  | DataNode b -> DataNode {b with h_formula_data_label = (nl ())}
  | ViewNode b -> ViewNode {b with h_formula_view_label = (nl ())}
  | HRel (r, args, pos) -> HRel(r, args, pos) (*vp*)
  | HTrue 
  | HFalse 
  | HEmp 
  | Hole _ -> f
	
and replace_formula_label1 nl f = match f with
	| Base b->Base {b with 
			formula_base_heap = replace_heap_formula_label nl b.formula_base_heap ;
			formula_base_pure = MCP.replace_mix_formula_label nl b.formula_base_pure ;}
	| Exists b->Exists {b with 
			formula_exists_heap = replace_heap_formula_label nl b.formula_exists_heap ;
			formula_exists_pure = MCP.replace_mix_formula_label nl b.formula_exists_pure ;}
	| Or b -> Or {b with 
			formula_or_f1 = replace_formula_label1 nl b.formula_or_f1;
			formula_or_f2 = replace_formula_label1 nl b.formula_or_f2;	}
			
let rec replace_struc_formula_label1 nl f =  match f with
	| EBase b -> EBase {b with 
			formula_struc_base = replace_formula_label1 nl b.formula_struc_base;
			formula_struc_continuation = map_opt (replace_struc_formula_label1 nl) b.formula_struc_continuation}
	| ECase b -> 
      let new_br = List.map 
        (fun (c1,c2)-> 
          ((CP.replace_pure_formula_label nl c1), (replace_struc_formula_label1 nl c2))
        ) b.formula_case_branches in
      ECase { b with formula_case_branches = new_br;}
	| EAssume (b1,b2,b3)-> EAssume (b1,(replace_formula_label1 nl b2),b3)
    | EInfer b -> EInfer {b with formula_inf_continuation = replace_struc_formula_label1 nl b.formula_inf_continuation}
	| EList b -> EList (map_l_snd (replace_struc_formula_label1 nl) b)
	| EOr b -> EOr {b with formula_struc_or_f1 = replace_struc_formula_label1 nl b.formula_struc_or_f1; formula_struc_or_f2 = replace_struc_formula_label1 nl b.formula_struc_or_f2;}
 	
and replace_struc_formula_label nl f = replace_struc_formula_label1 (fun c -> nl) f
and replace_struc_formula_label_fresh f = replace_struc_formula_label1 (fun c -> (fresh_branch_point_id "")) f
and replace_formula_label nl f = replace_formula_label1 (fun c -> nl) f
and replace_formula_label_fresh f = replace_formula_label1 (fun c -> (fresh_branch_point_id "")) f

and residue_labels_in_formula f = 
  let rec residue_labels_in_heap f = match f with
    | Star b -> (residue_labels_in_heap b.h_formula_star_h1) @ (residue_labels_in_heap b.h_formula_star_h2)
    | Conj b -> (residue_labels_in_heap b.h_formula_conj_h1) @ (residue_labels_in_heap b.h_formula_conj_h2)
    | Phase b -> (residue_labels_in_heap b.h_formula_phase_rd) @ (residue_labels_in_heap b.h_formula_phase_rw)
    | DataNode b -> (match b.h_formula_data_label with Some s-> [s] | _ -> [])
    | ViewNode b -> (match b.h_formula_view_label with Some s-> [s] | _ -> [])
    | HRel _
    | HTrue 
    | HFalse 
    | HEmp
    | Hole _ -> [] 
        in match f with
	| Base b-> residue_labels_in_heap b.formula_base_heap 
	| Exists b->residue_labels_in_heap b.formula_exists_heap
	| Or b -> (residue_labels_in_formula b.formula_or_f1) @ (residue_labels_in_formula b.formula_or_f2)

let get_node_label n =  match n with
	| DataNode b -> b.h_formula_data_label
	| ViewNode b -> b.h_formula_view_label
	| _ -> None
	

(* generic transform for heap formula *)
let trans_h_formula (e:h_formula) (arg:'a) (f:'a->h_formula->(h_formula * 'b) option) 
      (f_args:'a->h_formula->'a)(f_comb:'b list -> 'b) :(h_formula * 'b) =
  let rec helper (e:h_formula) (arg:'a) =
    let r =  f arg e in 
    match r with
    | Some (e1,v) -> (e1,v)
    | None  -> let new_arg = f_args arg e in
        match e with
        | Star s -> 
            let (e1,r1)=helper s.h_formula_star_h1 new_arg in
            let (e2,r2)=helper s.h_formula_star_h2 new_arg in
            (Star {s with h_formula_star_h1 = e1;
                          h_formula_star_h2 = e2;},f_comb [r1;r2])
        | Conj s -> 
            let (e1,r1)=helper s.h_formula_conj_h1 new_arg in
            let (e2,r2)=helper s.h_formula_conj_h2 new_arg in
            (Conj {s with h_formula_conj_h1 = e1;
                          h_formula_conj_h2 = e2;},f_comb [r1;r2])
        | Phase s -> 
            let (e1,r1)=helper s.h_formula_phase_rd new_arg in
            let (e2,r2)=helper s.h_formula_phase_rw new_arg in
            (Phase {s with h_formula_phase_rd = e1;
                           h_formula_phase_rw = e2;},f_comb [r1;r2])
        | DataNode _
        | ViewNode _
        | HRel _
        | Hole _	  
        | HTrue
        | HFalse 
        | HEmp -> (e, f_comb []) 
  in (helper e arg)

let map_h_formula_args (e:h_formula) (arg:'a) (f:'a -> h_formula -> h_formula option) (f_args: 'a -> h_formula -> 'a) : h_formula =
  let f1 ac e = push_opt_void_pair (f ac e) in
  fst (trans_h_formula e arg f1 f_args voidf)
	
  (*this maps an expression without passing an argument*)
let map_h_formula (e:h_formula) (f:h_formula->h_formula option) : h_formula = 
  map_h_formula_args e () (fun _ e -> f e) idf2 

  (*this computes a result from expression passing an argument*)
let fold_h_formula_args (e:h_formula) (init_a:'a) (f:'a -> h_formula-> 'b option) (f_args: 'a -> h_formula -> 'a) (comb_f: 'b list->'b) : 'b =
  let f1 ac e = match (f ac e) with
    | Some r -> Some (e,r)
    | None ->  None in
  snd(trans_h_formula e init_a f1 f_args comb_f)
 
  (*this computes a result from expression without passing an argument*)
let fold_h_formula (e:h_formula) (f:h_formula-> 'b option) (comb_f: 'b list->'b) : 'b =
  fold_h_formula_args e () (fun _ e-> f e) voidf2 comb_f 

(* transform heap formula *)
let rec transform_h_formula (f:h_formula -> h_formula option) (e:h_formula):h_formula = 
  let r =  f e in 
  match r with
    | Some e1 -> e1
    | None  -> match e with	 
	      | Star s -> Star {s with 
			  h_formula_star_h1 = transform_h_formula f s.h_formula_star_h1;
			  h_formula_star_h2 = transform_h_formula f s.h_formula_star_h2;}
	      | Conj s -> Conj {s with 
			  h_formula_conj_h1 = transform_h_formula f s.h_formula_conj_h1;
			  h_formula_conj_h2 = transform_h_formula f s.h_formula_conj_h2;}
	      | Phase s -> Phase {s with 
			  h_formula_phase_rd = transform_h_formula f s.h_formula_phase_rd;
			  h_formula_phase_rw = transform_h_formula f s.h_formula_phase_rw;}
	      | DataNode _
	      | ViewNode _
          | HRel _
	      | Hole _
	      | HTrue
	      | HFalse 
        | HEmp -> e


let transform_formula_x f (e:formula):formula =
  let rec helper f e = 
	let (_, f_f, f_h_f, f_p_t) = f in
	let r =  f_f e in 
	match r with
	| Some e1 -> e1
	| None  -> 
        match e with	 
		| Base b -> 
      Base{b with 
              formula_base_heap = transform_h_formula f_h_f b.formula_base_heap;
              formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure;}
		| Or o -> 
			Or {o with 
                    formula_or_f1 = helper f o.formula_or_f1;
                    formula_or_f2 = helper f o.formula_or_f2;}
		| Exists e -> 
      Exists {e with
                formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap;
                formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure;}
  in helper f e



let transform_formula f (e:formula):formula =
  let pr = !print_formula in
  Debug.no_2 "transform_formula" (fun _ -> "f") pr pr transform_formula_x f e

let transform_formula_w_perm_x (f:formula -> formula option) (e:formula) (permvar:cperm):formula =
	let r =  f e in 
	match r with
	| Some e1 -> e1
	| None  -> e

let transform_formula_w_perm (f:formula -> formula option) (e:formula) (permvar:cperm):formula =
  let pr = !print_formula in
  Debug.no_3 "transform_formula_w_perm" 
      (fun _ -> "f") pr !print_spec_var pr 
      transform_formula_w_perm_x f e permvar

let transform_formula_w_perm_x (f:formula -> formula option) (e:formula) (permvar:cperm_var):formula =
	let r =  f e in 
	match r with
	| Some e1 -> e1
	| None  -> e


let transform_formula_w_perm (f:formula -> formula option) (e:formula) (permvar:cperm_var):formula =
  let pr = !print_formula in
  Debug.no_3 "transform_formula_w_perm" 
      (fun _ -> "f") pr !print_spec_var pr 
      transform_formula_w_perm_x f e permvar

let rec trans2_formula f (e:formula):formula =
	let (f_h_f, f_p_t) = f in
    match e with	 
		| Base b -> 
      Base{b with 
              formula_base_heap = transform_h_formula f_h_f b.formula_base_heap;
              formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure;}
		| Or o -> Or {o with 
                    formula_or_f1 = trans2_formula f o.formula_or_f1;
                    formula_or_f2 = trans2_formula f o.formula_or_f2;}
		| Exists e -> 
      Exists {e with
                formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap;
                formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure;}


let foldheap_formula (h:h_formula -> 'a) (f_comb: 'a list -> 'a)  (e:formula) : 'a =
  let rec helper e =
    match e with
      | Base {formula_base_heap = e} -> h e
      | Or { formula_or_f1 = e1; formula_or_f2 = e2} -> f_comb [helper e1;helper e2]
      | Exists {formula_exists_heap = e} -> h e
  in helper e


let rec foldheap_struc_formula (h:h_formula -> 'a) (f_comb: 'a list -> 'a)  (e:struc_formula): 'a =
  let h_f = fun c-> [foldheap_struc_formula h f_comb c] in
  match e with
      | ECase b -> f_comb(fold_l_snd h_f b.formula_case_branches)
      | EBase b -> f_comb ((foldheap_formula h f_comb b.formula_struc_base)::(fold_opt h_f b.formula_struc_continuation))
      | EAssume (_,e,_) -> foldheap_formula h f_comb e
	  | EOr b -> f_comb ((h_f b.formula_struc_or_f1)@ h_f b.formula_struc_or_f2)
      | EInfer b -> foldheap_struc_formula h f_comb b.formula_inf_continuation
	  | EList b ->  f_comb (fold_l_snd h_f b)

let trans_formula (e: formula) (arg: 'a) f f_arg f_comb: (formula * 'b) =
  let f_struc_f, f_f, f_heap_f, f_pure, f_memo = f in
  let f_struc_f_arg, f_f_arg, f_heap_f_arg, f_pure_arg, f_memo_arg = f_arg in
  let trans_heap (e: h_formula) (arg: 'a) : (h_formula * 'b) = trans_h_formula e arg f_heap_f f_heap_f_arg f_comb in
  let trans_mix (e: MCP.mix_formula) (arg: 'a) : (MCP.mix_formula * 'b) = 
      MCP.trans_mix_formula e arg (f_memo,f_pure) (f_memo_arg,f_pure_arg) f_comb in
  let rec trans_f (e: formula) (arg: 'a) : (formula * 'b) =
    let r = f_f arg e in
    match r with
    | Some e1 -> e1
    | None ->
        let new_arg = f_f_arg arg e in
        match e with
        | Base b ->
            let new_heap, v1 = trans_heap b.formula_base_heap new_arg in
            let new_pure, v2 = trans_mix b.formula_base_pure new_arg in
            let new_base = Base { b with
              formula_base_heap = new_heap;
              formula_base_pure = new_pure; }
            in
            (new_base, f_comb [v1; v2])
        | Or o ->
            let nf1, v1 = trans_f o.formula_or_f1 new_arg in
            let nf2, v2 = trans_f o.formula_or_f2 new_arg in
            let new_or = Or { o with
              formula_or_f1 = nf1;
              formula_or_f2 = nf2; }
            in
            (new_or, f_comb [v1; v2])
        | Exists e ->
            let new_heap, v1 = trans_heap e.formula_exists_heap new_arg in
            let new_pure, v2 = trans_mix e.formula_exists_pure new_arg in
            let new_exists = Exists { e with
              formula_exists_heap = new_heap;
              formula_exists_pure = new_pure;}
            in
            (new_exists, f_comb [v1; v2])
  in
  trans_f e arg

let rec transform_struc_formula f (e:struc_formula) :struc_formula = 
  let (f_e_f, f_f, f_h_f, f_p_t) = f in
	let r = f_e_f e in 
	match r with
	| Some e1 -> e1
	| None -> match e with
		| ECase c -> 
      let br' = 
        List.map (fun (c1,c2)-> ((CP.transform_formula f_p_t c1),(transform_struc_formula f c2))) c.formula_case_branches in
      ECase {c with formula_case_branches = br';}
		| EBase b -> EBase{b with 
				 formula_struc_base = transform_formula f b.formula_struc_base;
				 formula_struc_continuation = map_opt (transform_struc_formula f) b.formula_struc_continuation;
				}
		| EAssume (v,e,pid)-> EAssume (v,(transform_formula f e),pid)
		| EInfer b -> EInfer {b with formula_inf_continuation = transform_struc_formula f b.formula_inf_continuation;}
		| EList b -> EList (map_l_snd (transform_struc_formula f) b)
		| EOr b -> EOr {b with 
				formula_struc_or_f1 = transform_struc_formula f b.formula_struc_or_f1; 
				formula_struc_or_f2 = transform_struc_formula f b.formula_struc_or_f2;}


let rec transform_struc_formula_w_perm f (permvar:cperm_var) (e:struc_formula) :struc_formula = 
  let (f_e_f, f_f, f_h_f, f_p_t) = f in
	let r = f_e_f e in 
	match r with
	| Some e1 -> e1
	| None -> match e with
		| ECase c -> 
			let br' = 
				List.map (fun (c1,c2)-> ((CP.transform_formula f_p_t c1),(transform_struc_formula_w_perm f permvar c2))) c.formula_case_branches in
			ECase {c with formula_case_branches = br';}
		| EBase b -> EBase{b with 
				 formula_struc_base = transform_formula_w_perm f_f b.formula_struc_base permvar;
				 formula_struc_continuation = map_opt (transform_struc_formula_w_perm f permvar) b.formula_struc_continuation;
				}
		| EAssume (v,e,pid)-> EAssume (v,(transform_formula_w_perm f_f e permvar),pid)
		| EInfer b -> EInfer {b with formula_inf_continuation = transform_struc_formula_w_perm f permvar b.formula_inf_continuation;}
		| EList b -> mkEList (map_l_snd (transform_struc_formula_w_perm f permvar) b)
		| EOr b -> mkEOr (transform_struc_formula_w_perm f permvar b.formula_struc_or_f1) (transform_struc_formula_w_perm f permvar b.formula_struc_or_f2) b.formula_struc_or_pos


let rec trans_struc_formula (e: struc_formula) (arg: 'a) f f_arg f_comb : (struc_formula * 'b) =
  let f_struc_f, f_f, f_h_formula, f_pure, f_memo = f in
  let f_struc_f_arg, f_f_arg, f_h_f_arg, f_pure_arg, f_memo_arg = f_arg in
  let trans_pure (e: CP.formula) (arg: 'a) : (CP.formula * 'b) = CP.trans_formula e arg f_pure f_pure_arg f_comb in
  let trans_struc (arg: 'a) (e: struc_formula)  : (struc_formula * 'b) = trans_struc_formula e arg f f_arg f_comb in
  let trans_f (e: formula) (arg: 'a) : (formula * 'b) = trans_formula e arg f f_arg f_comb in
  
  match f_struc_f arg e with
    | Some e1 -> e1
    | None ->
        let new_arg = f_struc_f_arg arg e in
        match e with
        | ECase c ->
            let helper ((e1,e2): CP.formula * struc_formula): (CP.formula * struc_formula) * 'b =
              let ne1, v1 = trans_pure e1 new_arg in
              let ne2, v2 = trans_struc new_arg e2  in
              ((ne1, ne2), f_comb [v1; v2])in
            let new_case_branches, vals = List.split (List.map helper c.formula_case_branches) in
            (ECase {c with formula_case_branches = new_case_branches}, f_comb vals)
        | EBase b ->
            let new_base, v1 = trans_f b.formula_struc_base new_arg in
            let new_cont, l = match b.formula_struc_continuation with 
					| None -> (None,[v1]) 
					| Some b-> let r1,r2 = trans_struc new_arg b in (Some r1, [v1;r2]) in
            (EBase { b with formula_struc_base = new_base; formula_struc_continuation = new_cont; }, f_comb l)
        | EAssume (v, e, pid) ->
            let ne, r = trans_f e new_arg in
            (EAssume (v, ne, pid), f_comb [r])
        | EInfer b -> 
          let new_cont, val3 = trans_struc new_arg b.formula_inf_continuation  in
          (EInfer {b with formula_inf_continuation = new_cont}, f_comb [val3])
	    | EList b -> 
			let ne,vals = map_l_snd_res (trans_struc new_arg) b in
			(mkEList ne, f_comb vals)
		| EOr b ->
			let ne1, v1 = trans_struc new_arg b.formula_struc_or_f1 in
			let ne2, v2 = trans_struc new_arg b.formula_struc_or_f2 in
			(mkEOr ne1 ne2 b.formula_struc_or_pos, f_comb [v1;v2])
        
let rec transform_context f (c:context):context = 
	match c with
	| Ctx e -> 
        (f e)
	| OCtx (c1,c2) -> 
        mkOCtx (transform_context f c1)(transform_context f c2) no_pos
		
let trans_context (c: context) (arg: 'a) 
        (f: 'a -> context -> (context * 'b) option) 
        (f_arg: 'a -> context -> 'a)
        (f_comb: 'b list -> 'b)
        : (context * 'b) =
  let rec trans_c (c: context) (arg: 'a) : (context * 'b) =
    let r = f arg c in
    match r with
    | Some c1 -> c1
    | None ->
        let new_arg = f_arg arg c in
        match c with
        | Ctx _ -> (c, f_comb [])
        | OCtx (c1, c2) ->
            let nc1, v1 = trans_c c1 new_arg in
            let nc2, v2 = trans_c c2 new_arg in
            (mkOCtx nc1 nc2 no_pos, f_comb [v1; v2])
  in
  trans_c c arg

let rec transform_fail_ctx f (c:fail_type) : fail_type = 
  match c with
    | Trivial_Reason _ -> c
    | Basic_Reason (br,fe) -> Basic_Reason ((f br), fe)
    | ContinuationErr br -> ContinuationErr (f br)
    | Or_Reason (ft1,ft2) -> Or_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
    | Union_Reason (ft1,ft2) -> Union_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
    | Or_Continuation (ft1,ft2) -> Or_Continuation ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
    | And_Reason (ft1,ft2) -> And_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
  
let transform_list_context f (c:list_context):list_context = 
  let f_c,f_f = f in
  match c with
    | FailCtx fc -> FailCtx (transform_fail_ctx f_f fc)
    | SuccCtx sc -> SuccCtx ((List.map (transform_context f_c)) sc)
    
let transform_partial_context f ((fail_c, succ_c):partial_context) : partial_context = 
  let f_c,f_f = f in
  let f_res = List.map (fun (lbl, f_t) -> (lbl, transform_fail_ctx f_f f_t )) fail_c in
  let s_res = List.map (fun (lbl, ctx) -> (lbl, transform_context f_c ctx) ) succ_c in
    (f_res,s_res)
	
let transform_failesc_context f ((fail_c,esc_c, succ_c):failesc_context): failesc_context = 
  let ff,fe,fs = f in
  let rf = List.map (fun (lbl, ctx) -> (lbl, transform_fail_ctx ff ctx) ) fail_c in
  let re = fe esc_c in
  let rs = List.map (fun (lbl, ctx) -> (lbl, transform_context fs ctx) ) succ_c in
  (rf, re,rs)

let transform_list_partial_context f (c:list_partial_context):list_partial_context = 
  List.map (transform_partial_context f) c
    
let transform_list_failesc_context f (c:list_failesc_context): list_failesc_context = 
  List.map (transform_failesc_context f) c

  (*use with care, it destroyes the information about exception stacks , preferably do not use except in check specs*)
let list_failesc_to_partial (c:list_failesc_context): list_partial_context =
	List.map (fun (fl,el,sl) -> (fl,(colapse_esc_stack el)@sl)) c 
    
let rec fold_fail_context f (c:fail_type) = 
  (*let f_br,f_or,f_and = f in*)
  match c with
    | Trivial_Reason _ -> f c []
    | Basic_Reason br -> f c []
    | ContinuationErr br -> f c []
    | Or_Reason (ft1,ft2) | Union_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
    | Or_Continuation (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
    | And_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
    
    
let rename_labels transformer e =
	let n_l_f n_l = match n_l with
				| None -> (fresh_branch_point_id "")
				| Some (_,s) -> (fresh_branch_point_id s) in	
    let f_e_f e = None in
	let f_f e = None in
	let rec f_h_f e = match e with 
		| Star s -> None
		| Conj s -> None
		| Phase s -> None	
  	    | DataNode d -> Some (DataNode {d with h_formula_data_label = n_l_f d.h_formula_data_label})
	    | ViewNode v -> Some (ViewNode {v with h_formula_view_label = n_l_f v.h_formula_view_label})
        | HRel _
	    | Hole _
	    | HTrue
	    | HFalse 
        | HEmp -> Some e in
  let f_m e = None in
  let f_a e = None in
	let f_b e = Some e in
	let f_e e = Some e in
	let f_p_f e = 
		match e with
		| CP.BForm (b,f_l) -> Some (CP.BForm (b,(n_l_f f_l)))
		| CP.And _
		| CP. AndList _ -> None
		| CP.Or (e1,e2,f_l,l) -> (Some (CP.Or (e1,e2,(n_l_f f_l),l)))
		| CP.Not (e1,f_l, l) -> (Some (CP.Not (e1,(n_l_f f_l),l)))
		| CP.Forall (v,e1,f_l, l) -> (Some (CP.Forall (v,e1,(n_l_f f_l),l)))
		| CP.Exists (v,e1,f_l, l) -> (Some (CP.Exists (v,e1,(n_l_f f_l),l)))in
	 transformer (f_e_f,f_f,f_h_f,(f_m,f_a,f_p_f,f_b,f_e)) e

let rename_labels_struc (e:struc_formula):struc_formula = rename_labels transform_struc_formula e
let rename_labels_formula (e:formula):formula = rename_labels transform_formula e
		 		
let rename_labels_formula_ante  e=
	let n_l_f n_l = match n_l with
				| None -> (fresh_branch_point_id "")
				| Some (_,s) -> (fresh_branch_point_id s) in	
    let f_e_f e = None in
	let f_f e = None in
	let rec f_h_f e = match e with 
	    | Conj s -> None
	    | Phase s -> None
	    | Star s -> None
	    | DataNode d -> Some (DataNode {d with h_formula_data_label = n_l_f d.h_formula_data_label})
	    | ViewNode v -> Some (ViewNode {v with h_formula_view_label = n_l_f v.h_formula_view_label})
        | HRel _
	    | Hole _
	    | HTrue
	    | HFalse 
      | HEmp -> Some e in
  let f_m e = None in
  let f_a e = None in
	let f_b e = Some e in
	let f_e e = Some e in
	let f_p_f e = Some e in		
	
	transform_formula (f_e_f,f_f,f_h_f,(f_m,f_a,f_p_f,f_b,f_e)) e
			 
let erase_propagated f = 
  let f_e_f e = None in
	let f_f e = None in
	let rec f_h_f e =  None in
  let f_memo e =  Some (MCP.cons_filter e MCP.isImplT) in
  let f_aset e = Some e in
	let f_formula e = Some e in
	let f_b_formula e = Some e in
	let f_exp e = Some e in			
  transform_struc_formula (f_e_f,f_f,f_h_f,(f_memo,f_aset, f_formula, f_b_formula, f_exp)) f

and pop_expl_impl_context (expvars : CP.spec_var list) (impvars : CP.spec_var list) (ctx : list_context)  : list_context = 
  transform_list_context ((fun es -> Ctx{es with 
				es_gen_expl_vars = Gen.BList.difference_eq CP.eq_spec_var es.es_gen_expl_vars expvars; 
				es_gen_impl_vars = Gen.BList.difference_eq CP.eq_spec_var es.es_gen_impl_vars impvars;
				es_evars = Gen.BList.difference_eq (=) es.es_evars expvars;
				}), fun c->c) ctx

and push_exists_list_context (qvars : CP.spec_var list) (ctx : list_context) : list_context = 
  transform_list_context ((fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula}),(fun c->c)) ctx


and push_exists_list_partial_context (qvars : CP.spec_var list) (ctx : list_partial_context) : list_partial_context = 
  transform_list_partial_context ((fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula}),(fun c->c)) ctx

and push_exists_list_failesc_context (qvars : CP.spec_var list) (ctx : list_failesc_context) : list_failesc_context = 
  transform_list_failesc_context (idf,idf,(fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula})) ctx
  
and push_exists_context (qvars : CP.spec_var list) (ctx : context) : context = 
  transform_context (fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula}) ctx
        
and push_expl_impl_context (expvars : CP.spec_var list) (impvars : CP.spec_var list) (ctx : context)  : context = 
 transform_context (fun es -> Ctx{es with 
				es_gen_expl_vars = es.es_gen_expl_vars @ expvars; 
				es_gen_impl_vars = es.es_gen_impl_vars @ impvars;
				(*es_evars = es.es_evars@ expvars;*)}) ctx
        
and impl_to_expl es vl : entail_state = 
  let im, il = List.partition (fun c-> List.mem c vl) es.es_gen_impl_vars in
  {es with 
    es_gen_expl_vars = es.es_gen_expl_vars @ im; 
    es_gen_impl_vars = il;}
        
        
and pop_exists_context (qvars : CP.spec_var list) (ctx : list_context) : list_context = 
transform_list_context ((fun es -> Ctx{es with es_formula = pop_exists qvars es.es_formula}),(fun c->c)) ctx

and pop_exists_estate (qvars : CP.spec_var list) (es : entail_state) : entail_state = 
	let new_es = {es with 
		es_evars = (List.filter (fun x -> not (List.exists (fun y -> (CP.eq_spec_var x y)) qvars)) es.es_evars);
		es_formula = pop_exists qvars es.es_formula
	}
	in new_es
  
 (* add a list of existential vars, evars, to each context in the list ctx *)
and add_exist_vars_to_ctx_list (ctx : list_context) (evars	: CP.spec_var list) : list_context = 
  transform_list_context ((fun es-> Ctx{es with es_formula = (add_quantifiers evars es.es_formula)}),(fun c->c)) ctx


and change_ret_flow_ctx ctx_list =
  transform_list_context ((fun es -> Ctx{es with es_formula = substitute_flow_in_f !norm_flow_int !ret_flow_int es.es_formula;})
    ,(fun c->c)) ctx_list

and change_ret_flow_partial_ctx ctx_list = 
  transform_list_partial_context ((fun es -> Ctx{es with es_formula = substitute_flow_in_f !norm_flow_int !ret_flow_int es.es_formula;})
    ,(fun c->c)) ctx_list
    
and change_ret_flow_failesc_ctx ctx_list = 
  transform_list_failesc_context 
    (idf,idf,(fun es -> Ctx{es with es_formula = substitute_flow_in_f !norm_flow_int !ret_flow_int es.es_formula;})) ctx_list
    
let add_path_id ctx (pi1,pi2) = match pi1 with
	| None -> ctx
	| Some s -> 
    let fct e = Ctx{e with es_path_label = (s,pi2)::e.es_path_label} in    
    transform_context fct ctx
	
let add_path_id_ctx_list c (pi1,pi2)  = match pi1 with
	| None -> c
	| Some s ->	      
    let fct e = Ctx{e with es_path_label = (s,pi2)::e.es_path_label} in    
    transform_list_context (fct,(fun c-> c)) c
 
let add_path_id_ctx_partial_list (c:list_partial_context) (pi1,pi2) : list_partial_context = 
  match pi1 with
    | None -> c
    | Some s ->	      
	let fct e = Ctx{e with es_path_label = (s,pi2)::e.es_path_label} in    
	  transform_list_partial_context (fct,(fun c-> c)) c

let add_path_id_ctx_failesc_list (c:list_failesc_context) (pi1,pi2) : list_failesc_context = 
  match pi1 with
    | None -> c
    | Some s ->	      
	let fct e = Ctx{e with es_path_label = (s,pi2)::e.es_path_label} in    
	  transform_list_failesc_context (idf,idf,fct) c

	  
let normalize_max_renaming_list_partial_context f pos b ctx = 
    if !max_renaming then transform_list_partial_context ((normalize_es f pos b),(fun c->c)) ctx
      else transform_list_partial_context ((normalize_clash_es f pos b),(fun c->c)) ctx
let normalize_max_renaming_list_failesc_context f pos b ctx = 
    if !max_renaming then transform_list_failesc_context (idf,idf,(normalize_es f pos b)) ctx
      else transform_list_failesc_context (idf,idf,(normalize_clash_es f pos b)) ctx
let normalize_max_renaming_list_failesc_context f pos b ctx =
  Gen.Profiling.do_2 "normalize_max_renaming_list_failesc_context" (normalize_max_renaming_list_failesc_context f pos) b ctx
      
let normalize_max_renaming f pos b ctx = 
  if !max_renaming then transform_list_context ((normalize_es f pos b),(fun c->c)) ctx
  else transform_list_context ((normalize_clash_es f pos b),(fun c->c)) ctx

let normalize_max_renaming_s f pos b ctx = 
  if !max_renaming then transform_context (normalize_es f pos b) ctx
  else transform_context (normalize_clash_es f pos b) ctx

(*
  to be used in the type-checker. After every entailment, the history of vars
  must be cleared.
*)

let clear_entailment_vars (es :entail_state) : entail_state = 
  {es with es_history = es.es_history@[es.es_heap];
         es_heap = HEmp;
          es_evars = [];
      es_ivars = [];
      es_gen_expl_vars = [];
      es_gen_impl_vars = [];
      es_subst = ([],[]);
      }

let clear_entailment_history_es_es (es :entail_state) : entail_state = 
  {es with es_history = es.es_history@[es.es_heap];
      es_heap = HEmp;
  }

(*
  to be used in the type-checker. After every entailment, the history of consumed nodes
  must be cleared.
*)

let clear_entailment_history_es xp (es :entail_state) :context =
  (* TODO : this is clearing more than es_heap since qsort-tail.ss fails otherwise *)
  let hf = es.es_heap in
  let old_history =  if is_data hf then es.es_history@[hf] else es.es_history in
  (* adding xpure0 of es_heap into es_formula *)
  let es_f = match xp hf with
    | None -> es.es_formula
    | Some (mf,svl,mm)  -> mkAnd_pure es.es_formula mf no_pos
  in 
  Ctx {
      (* es with es_heap=HTrue;} *)
      (empty_es (mkTrueFlow ()) es.es_group_lbl no_pos) with
          es_formula = es_f;
          es_history = old_history;
          es_path_label = es.es_path_label;
          es_prior_steps = es.es_prior_steps;
          es_var_measures = es.es_var_measures;
      (* WN : what is the purpose of es_var_stack?*)
          es_var_stack = es.es_var_stack;
          es_infer_vars = es.es_infer_vars;
          es_infer_vars_rel = es.es_infer_vars_rel;
          es_infer_vars_hp_rel = es.es_infer_vars_hp_rel;
          es_infer_heap = es.es_infer_heap;
          es_infer_pure = es.es_infer_pure;
          es_infer_rel = es.es_infer_rel;
          es_infer_hp_rel = es.es_infer_hp_rel;
          es_group_lbl = es.es_group_lbl;
          es_term_err = es.es_term_err;
          es_var_zero_perm = es.es_var_zero_perm;
  }

let clear_entailment_history xp (ctx : context) : context =  
  transform_context (clear_entailment_history_es xp) ctx
  
let clear_entailment_history_list xp (ctx : list_context) : list_context = 
  transform_list_context (clear_entailment_history_es xp,(fun c->c)) ctx 

let clear_entailment_history_partial_list xp (ctx : list_partial_context) : list_partial_context = 
  transform_list_partial_context (clear_entailment_history_es xp,(fun c->c)) ctx 

let clear_entailment_history_failesc_list xp (ctx : list_failesc_context) : list_failesc_context = 
  transform_list_failesc_context (idf,idf,clear_entailment_history_es xp) ctx 
  
let fold_partial_context_left_or (c_l:(list_partial_context list)) = match (List.length c_l) with
  | 0 ->  Err.report_error {Err.error_loc = no_pos;  
              Err.error_text = "folding or empty partial context list \n"}
  | 1 -> (List.hd c_l)
  | _ -> List.fold_left (fun a c->  list_partial_context_or a c)
      (List.hd c_l) (List.tl c_l)

let fold_partial_context_left_union (c_l:(list_partial_context list)) = match (List.length c_l) with
  | 0 ->  Err.report_error {Err.error_loc = no_pos;  
              Err.error_text = "folding union empty partial context list \n"}
  | 1 -> (List.hd c_l)
  | _ -> List.fold_left (fun a c->  list_partial_context_union a c) (List.hd c_l) (List.tl c_l)

(* convert entail state to ctx with nf flow and quantify eres
   variable *)
(* need also a binding to catch handler's bound var *)
let conv_elim_res (cvar:typed_ident option)  (c:entail_state)
    (elim_ex_fn: context -> context) = 
  let res_typ, b_rez = get_exc_result_type c.es_formula in
  let ctx = (Ctx {c with es_formula = 
      (substitute_flow_into_f !norm_flow_int c.es_formula) } )  in
  match cvar with
    | None -> ctx
    | Some (cvt,cvn) ->        
        if not(b_rez) then ctx
        else begin
      	  let vsv_f = formula_of_pure_N (CP.mkEqVar (CP.SpecVar (res_typ, cvn, Primed)) (CP.mkeRes res_typ) no_pos) no_pos in
      	  let ctx1 = normalize_max_renaming_s vsv_f no_pos true ctx in
      	  let ctx1 = push_exists_context [CP.mkeRes res_typ] ctx1 in
      	  if !elim_exists then elim_ex_fn ctx1 else  ctx1
        end

let conv_elim_res (cvar:typed_ident option)  (c:entail_state)
    (elim_ex_fn: context -> context) = 
  let pr1 = pr_option (pr_pair string_of_typ pr_id) in
  let pr2 = !print_entail_state in
  Debug.no_2 "conv_elim_res" pr1 pr2 !print_context_short
      (fun _ _ -> conv_elim_res cvar c elim_ex_fn) cvar c

(* convert entail state to ctx with nf flow *)
let conv (c:entail_state) (nf(* :nflow *)) = (Ctx {c 
with es_formula = 
(substitute_flow_into_f nf c.es_formula) } )   

let conv_lst (c:entail_state) (nf_lst(*: nflow list *)) = 
  match nf_lst with
    | [] -> None
    | x::xs -> Some (List.fold_left (fun acc_ctx y -> mkOCtx (conv c y) acc_ctx no_pos) (conv c x)  xs)

let rec splitter (c:context) 
    (nf(* :nflow *)) (cvar:typed_ident option)  (elim_ex_fn: context -> context)
    (* : (context option, context option) (\* caught under nf flow, escaped from nf flow*\)   *)
    =
  let rec helper c = 
    match c with
      | Ctx b -> 
	      let ff =(flow_formula_of_ctx c no_pos) in	
	      if (subsume_flow nf ff.formula_flow_interval) then  (Some
            (conv_elim_res cvar b elim_ex_fn),None) (* change caught item to normal flow *)
	      else if not(overlapping nf ff.formula_flow_interval) then (None,Some c)
          else (* let t_caught = intersect_flow nf
                  ff.formula_flow_interval in *)
	        let t_escape_lst = subtract_flow_list ff.formula_flow_interval nf in
            (Some (conv_elim_res cvar b elim_ex_fn), (* change caught item to normal flow *)
	        conv_lst b t_escape_lst)
      | OCtx (b1,b2) -> 
	      let (r11,r12) = helper b1 in
	      let (r21,r22) = helper b2 in
	      let r1 = match (r11,r21) with 
	        | None, None -> None
	        | Some c, None -> Some c
	        | None, Some c -> Some c
	        | Some c1, Some c2 -> Some (mkOCtx c1 c2 no_pos)	in
	      let r2 = match (r12,r22) with 
	        | None, None -> None
	        | Some c, None -> Some c
	        | None, Some c -> Some c
	        | Some c1, Some c2 -> Some (mkOCtx c1 c2 no_pos) in
	      (r1,r2) in
  helper c

let splitter_wrapper p c nf cvar elim_ex_fn fn_esc =
	let r_caught,r_esc = splitter c nf cvar elim_ex_fn in
	match (r_esc,r_caught) with
	| None, None -> Err.report_error {Err.error_loc = no_pos;
								Err.error_text = "Split can not return both empty contexts\n"}
    | Some cl,None -> ([(p,fn_esc cl)],[])
	| None, Some c -> ([],[(p,c)])
	| Some cl,Some c ->  ([(p,fn_esc cl)],[(p,c)])
								
(* fn transforms context to list of partial context *)
(* fn_esc is being applied to context that escapes; for try-catch construct it may add (pid,0) label to it *)

let splitter_failesc_context  (nf(* :nflow *)) (cvar:typed_ident option) (fn_esc:context -> context)   
	(elim_ex_fn: context -> context) (pl :list_failesc_context) : list_failesc_context = 
   List.map (fun (fl,el,sl)->
						let r = List.map (fun (p,c)-> splitter_wrapper p c nf cvar elim_ex_fn fn_esc ) sl in
						let re,rs = List.split r in
						(fl,push_esc_elem el (List.concat re),(List.concat rs))) pl 

let splitter_failesc_context  (nf(* :nflow *)) (cvar:typed_ident option) (fn_esc:context -> context)   
	(elim_ex_fn: context -> context) (pl :list_failesc_context) : list_failesc_context = 
  let pr = !print_list_failesc_context in
  let pr2 = !print_flow in
  Debug.no_2 "splitter_failesc_context" pr2 pr pr (fun _ _ -> splitter_failesc_context nf cvar fn_esc elim_ex_fn pl) nf pl
	
let splitter_partial_context  (nf(* :nflow *)) (cvar:typed_ident option)   
    (fn:  path_trace -> context ->  list_partial_context) (fn_esc:context -> context) 
	(elim_ex_fn: context -> context) ((fl,sl):partial_context) : list_partial_context = 
	
  let r = List.map (fun (l,c)-> 
	let r1,r2 = splitter c nf cvar elim_ex_fn in 
	let r1 = match r1 with
	  | Some c-> Some (fn l c )  (* CF.SuccCtx[(CF.simplify_context c)] *)
	  | None -> None in
	match (r1,r2) with
	  | None, None -> Err.report_error {Err.error_loc = no_pos;
		Err.error_text = "Split can not return both empty contexts\n"}
	  | Some cl,None -> cl
	  | None, Some c -> [mk_partial_context   (fn_esc c) l]
	  | Some cl,Some c ->  list_partial_context_or cl  [(mk_partial_context (fn_esc c) l)]
	) sl 
  in
   list_partial_context_or [ (fl, []) ] (fold_partial_context_left_or r)

let add_to_steps (ss:steps) (s:string) = s::ss 

let get_prior_steps (c:context) = 
  match c with
    | Ctx es -> es.es_prior_steps 
    | OCtx _ -> print_string "Warning : OCtx with get_prior_steps \n"; [] ;;

let add_to_context (c:context) (s:string) = 
  (* set_context (fun es -> {es with es_prior_steps = add_to_steps es.es_prior_steps s;}) c *)
  match c with
    | Ctx es -> Ctx {es with es_prior_steps = add_to_steps es.es_prior_steps s; }
    | OCtx _ ->  (* let _ = Error.report_warning { *)
      (*             Error.error_loc = !post_pos; *)
      (*             Error.error_text = "[add_to_context] unexpected dealing with OCtx." *)
      (*           } in *)
      (* let _ = print_endline (!print_context_short c) in *)
      set_context (fun es -> {es with es_prior_steps = add_to_steps es.es_prior_steps s;}) c 
;;

let add_to_context_num i (c:context) (s:string) = 
  let pr x = match x with Ctx _ -> "Ctx" | OCtx _ -> "OCtx" in  
  Debug.no_1_num i "add_to_context" pr pr_no (fun _ -> add_to_context c s) c

let add_to_estate (es:entail_state) (s:string) = 
  {es with es_prior_steps = s::es.es_prior_steps; }

let overwrite_estate_with_steps (es:entail_state) (ss:steps) = 
  {es with es_prior_steps = ss; }

let add_to_estate_with_steps (es:entail_state) (ss:steps) = 
  {es with es_prior_steps = ss@es.es_prior_steps; }

let rec add_post post f = match f with
  | EBase b -> 
      let fec = match b.formula_struc_continuation with 
				| Some b-> add_post post b
				| _ -> let (svs,pf,(i_lbl,s_lbl)) = post in
               EAssume (svs,pf,(fresh_formula_label s_lbl)) in 
    EBase{b with formula_struc_continuation = Some fec}
  | ECase b -> ECase {b with formula_case_branches  = List.map (fun (c1,c2)-> (c1,(add_post post c2))) b.formula_case_branches;}
  | EAssume _ -> Err.report_error {Err.error_loc = no_pos; Err.error_text = "add post found an existing post\n"}
  | EInfer b ->  EInfer {b with formula_inf_continuation = add_post post b.formula_inf_continuation}
  | EList b -> EList (map_l_snd (add_post post) b)
  | EOr b -> EOr {b with formula_struc_or_f1 = add_post post b.formula_struc_or_f1; formula_struc_or_f2 = add_post post b.formula_struc_or_f2;}
  
(* TODO *)
let rec string_of_list_of_pair_formula ls =
  match ls with
	| [] -> ""
	| (f1,f2)::[] -> (!print_formula f1)^"*"^(!print_formula f2)
	| (f1,f2)::rest -> (!print_formula f1)^"*"^(!print_formula f2)^(string_of_list_of_pair_formula rest)

(* and print_formula = ref(fun (c:formula) -> "Cprinter not initialized") *)
(* and print_struc_formula = ref(fun (c:struc_formula) -> "Cprinter not initialized") *)
		
(* and split_struc_formula f0 = split_struc_formula_a f0 *)

and split_struc_formula f0 = Debug.no_1 "split_struc_formula" (!print_struc_formula) (string_of_list_of_pair_formula) split_struc_formula_a f0

(* split the struc_formula into the list of pre/post pairs *)  
and split_struc_formula_a (f:struc_formula):(formula*formula) list = match f with
		| ECase b-> 
			let r =  List.concat (List.map (fun (c1,c2)->
				let ll = split_struc_formula_a c2 in
				List.map (fun (d1,d2)-> ((normalize 4 d1 (formula_of_pure_N c1 b.formula_case_pos) b.formula_case_pos),d2)) ll) b.formula_case_branches) in
			List.map (fun (c1,c2)-> ((push_exists b.formula_case_exists c1),(push_exists b.formula_case_exists c2))) r 
		| EBase b-> 
				let ll = fold_opt split_struc_formula_a b.formula_struc_continuation in
				let e = List.map (fun (c1,c2)-> ((normalize 5 c1 b.formula_struc_base b.formula_struc_pos),c2)) ll in
				let nf = ((*b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@*)b.formula_struc_exists) in
				let e = List.map (fun (c1,c2)-> ((push_exists nf c1),(push_exists nf c2))) e in
				e
		| EAssume (x,b,_)-> [((mkTrue (mkNormalFlow ()) no_pos),b)]
		| EInfer b -> split_struc_formula_a b.formula_inf_continuation
		| EList b -> fold_l_snd split_struc_formula_a b 
		| EOr b -> (split_struc_formula_a b.formula_struc_or_f1)@ (split_struc_formula_a b.formula_struc_or_f2)

let rec filter_bar_branches (br:formula_label list option) (f0:struc_formula) :struc_formula = match br with
    | None -> f0
    | Some br -> 
		let rec filter_formula (f:formula):formula list = match f with
			| Base {formula_base_label = lbl} 
			| Exists {formula_exists_label = lbl} -> (match lbl with
			  | None -> Err.report_error { Err.error_loc = no_pos;Err.error_text = "view is unlabeled\n"} 
			  | Some lbl -> if (List.mem lbl br) then (Gen.Profiling.inc_counter "total_unfold_disjs";[f]) else (Gen.Profiling.inc_counter "saved_unfolds";[]))
			| Or b -> ((filter_formula b.formula_or_f1)@(filter_formula b.formula_or_f2)) in   
		let rec filter_helper (f:struc_formula):struc_formula = match f with
			| EBase b -> (match b.formula_struc_continuation with
				| None -> report_error no_pos "barrier is unlabeled \n"
				| Some f -> 
					let l = filter_helper f in
					if isConstEFalse l  then l else EBase {b with formula_struc_continuation = Some l})
			| ECase b -> 
				let l = List.map (fun (c1,c2)-> (c1,filter_helper c2)) b.formula_case_branches in
				let l = List.filter (fun (_,c2)-> not (isConstEFalse c2)) l in
				if l=[] then mkEFalse (mkFalseFlow)  no_pos else ECase {b with formula_case_branches = l}
			| EAssume (x,b,l)-> if (List.mem l br) then f else mkEFalse (mkFalseFlow)  no_pos
			| EInfer b ->
			  let l = filter_helper b.formula_inf_continuation in(* Need to check again *)
			  if isConstEFalse l then l else EInfer {b with formula_inf_continuation = l}
			| EList b -> mkEList (map_l_snd filter_helper b) 
			| EOr b -> mkEOr (filter_helper b.formula_struc_or_f1) (filter_helper b.formula_struc_or_f2) b.formula_struc_or_pos in
		filter_helper f0
  
		
		
let rec filter_branches (br:formula_label list option) (f0:struc_formula) :struc_formula = match br with
    | None -> f0
    | Some br -> 
		let rec filter_formula (f:formula):formula list = match f with
			| Base {formula_base_label = lbl} 
			| Exists {formula_exists_label = lbl} -> (match lbl with
			  | None -> Err.report_error { Err.error_loc = no_pos;Err.error_text = "view is unlabeled\n"} 
			  | Some lbl -> if (List.mem lbl br) then (Gen.Profiling.inc_counter "total_unfold_disjs";[f]) else (Gen.Profiling.inc_counter "saved_unfolds";[]))
			| Or b -> ((filter_formula b.formula_or_f1)@(filter_formula b.formula_or_f2)) in   
		let rec filter_helper (f:struc_formula):struc_formula = match f with
			| EBase b -> (match b.formula_struc_continuation with
				| None -> 
					let l = filter_formula b.formula_struc_base in
					if (l=[]) then mkEFalse (mkFalseFlow) no_pos else EBase {b with formula_struc_base = formula_of_disjuncts l}
				| Some f -> 
					let l = filter_helper f in
					if isConstEFalse l  then l else EBase {b with formula_struc_continuation = Some l})
			| ECase b -> 
				let l = List.map (fun (c1,c2)-> (c1,filter_helper c2)) b.formula_case_branches in
				let l = List.filter (fun (_,c2)-> not (isConstEFalse c2)) l in
				if l=[] then mkEFalse (mkFalseFlow)  no_pos else ECase {b with formula_case_branches = l}
			| EAssume (x,b,l)-> if (List.mem l br) then f else mkEFalse (mkFalseFlow)  no_pos
			| EInfer b ->
			  let l = filter_helper b.formula_inf_continuation in(* Need to check again *)
			  if isConstEFalse l then l else EInfer {b with formula_inf_continuation = l}
			| EList b -> mkEList (map_l_snd filter_helper b) 
			| EOr b -> mkEOr (filter_helper b.formula_struc_or_f1) (filter_helper b.formula_struc_or_f2) b.formula_struc_or_pos in
		filter_helper f0
  

let filter_branches (br:formula_label list option) (f0:struc_formula) :struc_formula =
  let pr = !print_struc_formula in
  let pr1 x = match x with
    | None -> "None"
    | Some l -> "Some"^string_of_int(List.length l) in
  Debug.no_2 "filter_branches" pr1 pr pr (fun _ _ -> filter_branches (br:formula_label list option) (f0:struc_formula)) br f0
  
let rec label_view (f0:struc_formula):struc_formula = 
  let rec label_formula (f:formula):formula = match f with
    | Base b -> Base{b with formula_base_label = Some (fresh_formula_label "")} 
    | Exists b -> Exists{b with formula_exists_label = Some (fresh_formula_label "")} 
    | Or b -> Or{b with formula_or_f1 = label_formula b.formula_or_f1;formula_or_f2 = label_formula b.formula_or_f2;}  in
  let rec label_struc (f:struc_formula):struc_formula = match f with
    | EBase b -> EBase{b with formula_struc_continuation = map_opt label_struc b.formula_struc_continuation; formula_struc_base= label_formula b.formula_struc_base}
    | ECase b -> ECase{b with formula_case_branches = map_l_snd label_struc b.formula_case_branches}
    | EAssume (x,b,l)-> EAssume (x,label_formula b,l)
    | EInfer b -> EInfer {b with formula_inf_continuation = label_struc b.formula_inf_continuation}
	| EOr b -> EOr  {b with formula_struc_or_f1 = label_struc b.formula_struc_or_f1; formula_struc_or_f2 = label_struc b.formula_struc_or_f2;}  
	| EList b -> EList (map_l_snd label_struc b) in
	label_struc f0
  
  
let get_view_branches (f0:struc_formula):(formula * formula_label) list= 
  let rec formula_br (f:formula):(formula * formula_label) list = match f with
    | Base {formula_base_label=lbl} 
    | Exists {formula_exists_label=lbl} -> (match lbl with | None -> [] | Some l -> [(f,l)])
    | Or b -> (formula_br b.formula_or_f1)@(formula_br b.formula_or_f2 )  in
	
	let rec struc_formula_br (f:struc_formula):(formula * formula_label) list = match f with
		| ECase b-> List.concat 
			(List.map (fun (c1,c2) -> 
				let np = (MCP.memoise_add_pure_N (MCP.mkMTrue b.formula_case_pos) c1) in
				let g_f = mkBase HEmp np TypeTrue (mkTrueFlow ()) [] b.formula_case_pos in
				List.map (fun (d1,d2)-> (normalize_combine g_f d1 no_pos,d2)) (struc_formula_br c2)) b.formula_case_branches)
		| EBase b-> 
			let l_e_v =(b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@b.formula_struc_exists) in
			(match b.formula_struc_continuation with 
				| Some l ->List.map (fun (c1,c2)-> 
					let r_f = normalize_combine b.formula_struc_base c1 b.formula_struc_pos in
					((push_exists l_e_v r_f),c2)) (struc_formula_br l)
				| None -> List.map (fun (c1,c2) -> ((push_exists l_e_v c1),c2) ) (formula_br b.formula_struc_base) )
		| EAssume (_,b,_)-> []
		| EInfer b -> struc_formula_br b.formula_inf_continuation
		| EList b -> fold_l_snd struc_formula_br b
		| EOr b -> (struc_formula_br b.formula_struc_or_f1)@(struc_formula_br b.formula_struc_or_f2)
	in	
  struc_formula_br f0
  

let get_view_branches (f0:struc_formula):(formula * formula_label) list=
  let rec add_label f l = match f with
    | Base b -> Base { b with formula_base_label = Some l}
    | Exists b -> Exists  {b with formula_exists_label = Some l}
    | Or b -> f in
  let res = get_view_branches f0 in
  List.map (fun (f,lbl) -> ((add_label f lbl),lbl)) res
 
	
let get_bar_branches (f0:struc_formula):(formula * formula_label) list= 
  let rec is_disj (f:formula) : bool = match f with
    | Base _
    | Exists _ -> false
    | Or b -> true in
	
	let rec struc_formula_br (f:struc_formula):(formula * formula_label) list = match f with
		| ECase b-> List.concat 
			(List.map (fun (c1,c2) -> 
				let np = (MCP.memoise_add_pure_N (MCP.mkMTrue b.formula_case_pos) c1) in
				let g_f = mkBase HTrue np TypeTrue (mkTrueFlow ()) [] b.formula_case_pos in
				List.map (fun (d1,d2)-> (normalize_combine g_f d1 no_pos,d2)) (struc_formula_br c2)) b.formula_case_branches)
		| EBase b-> 
			let l_e_v =(b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@b.formula_struc_exists) in
			if is_disj b.formula_struc_base then report_error b.formula_struc_pos "unexpected disjunction in requires clause of a barrier def " 
			else (match b.formula_struc_continuation with 
					| Some l ->List.map (fun (c1,c2)-> 
					let r_f = normalize_combine b.formula_struc_base c1 b.formula_struc_pos in
					((push_exists l_e_v r_f),c2)) (struc_formula_br l)
					| None -> report_error b.formula_struc_pos "barrier branch does not have post conditions")
		| EAssume (_,_,l)-> [(mkTrue_nf no_pos,l)]
		| EInfer b -> struc_formula_br b.formula_inf_continuation
		| EList b -> fold_l_snd struc_formula_br b
		| EOr b -> (struc_formula_br b.formula_struc_or_f1)@(struc_formula_br b.formula_struc_or_f2)
	in	
  struc_formula_br f0
	
let mkEBase_with_cont (pf:CP.formula) cont loc : struc_formula =
  EBase	{
	formula_struc_explicit_inst = [];
	formula_struc_implicit_inst = [];
	formula_struc_exists = [];
	(*formula_struc_base = mkBase HTrue (MCP.OnePF (pf)) TypeTrue (mkTrueFlow ()) [("",pf)] loc;*)
	formula_struc_base = mkBase HEmp (MCP.OnePF (pf)) TypeTrue (mkTrueFlow ()) [] loc;
	formula_struc_continuation = cont;
	formula_struc_pos = loc;
    (*formula_ext_complete = true;*)
  }	

let propagate_perm_struc_formula_x e (permvar:cperm_var)=
  let f_e_f e = None  in
  let f_f e = Some (propagate_perm_formula e permvar) in
  let f_h_f f = None in
  let f_p_t1 e = Some e in
  let f_p_t2 e = Some e in
  let f_p_t3 e = Some e in
  let f_p_t4 e = Some e in
  let f_p_t5 e = Some e in
  let f=(f_e_f,f_f,f_h_f,(f_p_t1,f_p_t2,f_p_t3,f_p_t4,f_p_t5)) in
    transform_struc_formula_w_perm f permvar e 

let propagate_perm_struc_formula e (permvar:cperm_var)=
  Debug.no_2 "propagate_perm_struc_formula" 
      !print_struc_formula !print_spec_var !print_struc_formula 
      propagate_perm_struc_formula_x  e permvar


let propagate_perm_struc_formula_x e (permvar:cperm_var)=
  let f_e_f e = None  in
  let f_f e = Some (propagate_perm_formula e permvar) in
  let f_h_f f = None in
  let f_p_t1 e = Some e in
  let f_p_t2 e = Some e in
  let f_p_t3 e = Some e in
  let f_p_t4 e = Some e in
  let f_p_t5 e = Some e in
  let f=(f_e_f,f_f,f_h_f,(f_p_t1,f_p_t2,f_p_t3,f_p_t4,f_p_t5)) in
    transform_struc_formula_w_perm f permvar e 

let propagate_perm_struc_formula e (permvar:cperm_var)=
  Debug.no_2 "propagate_perm_struc_formula" 
      !print_struc_formula !print_spec_var !print_struc_formula 
      propagate_perm_struc_formula_x  e permvar


and add_origs_to_node_struc (v:string) (e : struc_formula) origs = 
  let f_e_f e = None  in
  let f_f e = Some (add_origs_to_node v e origs)in
  let f_h_f f = Some f in
  let f_p_t1 e = Some e in
  let f_p_t2 e = Some e in
  let f_p_t3 e = Some e in
  let f_p_t4 e = Some e in
  let f_p_t5 e = Some e in
  let f=(f_e_f,f_f,f_h_f,(f_p_t1,f_p_t2,f_p_t3,f_p_t4,f_p_t5)) in
    transform_struc_formula f e

let disable_imm_last_phase_ctx ctx =
   transform_context
    (fun es ->
  		Ctx{es with es_imm_last_phase = false}
      ) ctx

and enable_imm_last_phase_ctx ctx =
   transform_context
    (fun es ->
  		Ctx{es with es_imm_last_phase = true}
      ) ctx

let add_to_aux_conseq_estate es to_aux_conseq pos =
  { es with es_aux_conseq = (*match es.es_aux_conseq with
    | None -> Some to_aux_conseq
    | Some f -> Some*) (CP.mkAnd  (*f*) es.es_aux_conseq to_aux_conseq pos)
  }

let add_to_aux_conseq lctx to_aux_conseq pos =
  (match lctx with
    | FailCtx _ -> lctx
    | SuccCtx cl ->
      let new_cl = List.map (fun c ->
      (transform_context
    	(fun es ->
    		Ctx  (add_to_aux_conseq_estate es to_aux_conseq pos)
      ) c)) cl
      in SuccCtx(new_cl))


let enable_imm_last_phase lctx =
  (match lctx with
    | FailCtx _ -> lctx
    | SuccCtx cl ->
      let new_cl = List.map (fun c -> enable_imm_last_phase_ctx c) cl
      in SuccCtx(new_cl))

and disable_imm_last_phase lctx =
  (match lctx with
    | FailCtx _ -> lctx
    | SuccCtx cl ->
      let new_cl = List.map (fun c -> disable_imm_last_phase_ctx c) cl
      in SuccCtx(new_cl))

and add_to_subst lctx r_subst l_subst =
  match lctx with
    | FailCtx _ -> lctx
    | SuccCtx cl ->
      let new_cl = List.map (fun c ->
      (transform_context
    	(fun es ->
    		Ctx{es with
    		    (* add to the substitution list *)
		    es_subst = ((fst es.es_subst)@r_subst, (snd es.es_subst)@l_subst);
    		})) c) cl
      in SuccCtx(new_cl)


let reset_original (f : formula) : formula = add_original f true 
let reset_original_es x = {x with es_formula = (reset_original x.es_formula)} 

let reset_original_list_partial_context (f : list_partial_context) : list_partial_context = 
  let f1 x = Ctx (reset_original_es x) in
  transform_list_partial_context (f1,(fun c->c)) f

let is_no_heap_h_formula (e : h_formula) : bool =
  let f x = match x with
	  | DataNode _
	  | ViewNode _ -> Some false
	  | _ -> None
  in
  fold_h_formula e f (List.for_all (fun x -> x))

let is_no_heap_struc_formula (e : struc_formula) : bool = 
  let f_struc_f _ _ = None in
  let f_f _ _ = None in
  let f_h_formula _ x = Some (x, is_no_heap_h_formula x) in
  let f_pure = 
    let f1 _ e = Some (e, true) in
    (f1,f1,f1) in
  let f_memo = 
    let f1 _ e = Some (e, true) in
    let f2 e _ = (e,true) in
    let f3 _ e = (e,[]) in
    (f1,f2,f3,f2,f2) in
  let f_arg =
    let f1 e _ = e in
    let f2 e _ = e in
    (f1,f1,f1,(f1,f1,f1),f2) in
  let f = (f_struc_f, f_f, f_h_formula, f_pure, f_memo) in
    snd(trans_struc_formula e false f f_arg (List.for_all (fun x -> x)))

let is_no_heap_struc_formula (e : struc_formula) : bool = 
  let pr = !print_struc_formula in
  Debug.no_1 "is_no_heap_struc_formula" pr string_of_bool is_no_heap_struc_formula e 

let extr_rhs_b (e:formula) =
  let h1, p1, fl1, t1,a1 = split_components e in
  let b1 = { formula_base_heap = h1;
  formula_base_pure = p1;
  formula_base_type = t1;
  formula_base_and = a1;
  formula_base_flow = fl1;
  formula_base_label = None;
  formula_base_pos = no_pos } in
  b1
    
and extr_lhs_b (es:entail_state) =
  let e = es.es_formula in
  let h1, p1, fl1, t1,a1 = split_components e in
  let b1 = { formula_base_heap = h1;
  formula_base_pure = p1;
  formula_base_type = t1;
  formula_base_and = a1;
  formula_base_flow = fl1;
  formula_base_label = None;
  formula_base_pos = no_pos } in
  b1

(** An Hoa : SECTION SIMPLIFY FORMULAE AND CONTEXT **)
	
let rec simplify_list_failesc_context (ctx : list_failesc_context) (bv : CP.spec_var list) = 
	List.map (fun x -> simplify_failesc_context x bv) ctx
	
and simplify_failesc_context (ctx : failesc_context) (bv : CP.spec_var list) = 
	match ctx with
		| (brfaillist,escstk,brctxlist) -> 
			let newbrctxlist = List.map (fun x -> simplify_branch_context x bv) brctxlist in
				(brfaillist,escstk,newbrctxlist)

and simplify_branch_context (brctx : branch_ctx) (bv : CP.spec_var list) =
	match brctx with
		| (pathtrc, ctx) ->
			let newctx = simplify_context ctx bv in
				(pathtrc, newctx)

and simplify_context (ctx : context) (bv : CP.spec_var list) = 
	match ctx with
		| Ctx ({ es_formula = esformula} as es) -> 
						let sesfml = simplify_formula esformula bv in
							Ctx { es with es_formula = sesfml }
		| OCtx (ctx1, ctx2) -> 
					OCtx (simplify_context ctx1 bv, simplify_context ctx2 bv)

and simplify_formula (f : formula) (bv : CP.spec_var list) = 
	match f with
		| Base ({formula_base_heap = heap;
						formula_base_pure = pure;} as fb) -> 
			let newheap,newpure,strrep = simplify_heap_pure heap pure bv in
			Base ({fb with formula_base_heap = newheap;
						formula_base_pure = newpure;})
		| Or ({formula_or_f1 = f1;
	        formula_or_f2 = f2;} as fo) -> 
			Or ({fo with formula_or_f1 = simplify_formula f1 bv;
					formula_or_f2 = simplify_formula f2 bv;})
		| Exists ({formula_exists_qvars = qvars;
	            formula_exists_heap = heap;
	            formula_exists_pure = pure;} as fe) ->
			let newheap,newpure,strrep = simplify_heap_pure heap pure bv in
			let nqvars = List.append (h_fv newheap) (MCP.mfv newpure) in (* Remove redundant quantified variables *)
			let nqvars = Gen.BList.intersect_eq CP.eq_spec_var qvars nqvars in
			Exists ({fe with formula_exists_qvars = nqvars;
	            formula_exists_heap = newheap;
	            formula_exists_pure = newpure;})

(** An Hoa : simplify a heap formula with the constraints, bv stores the base variables **)
(** STEP 1 : replace variables that could be replaced by "original variables" **)
(** STEP 2 : remove constraints concerning "unreachable" variables i.e. var without references **)
and simplify_heap_pure (h : h_formula) (p : MCP.mix_formula) (bv : CP.spec_var list) =
	let f = MCP.pure_of_mix p in
	let sst,strrep = CP.reduce_pure f bv in
	let nh = h_subst sst h in
	let np = MCP.simplify_mix_formula (MCP.memo_subst sst p) in
		(nh, np, strrep)

(** An Hoa : SECTION PARTIAL STRUCTURE **)

(**
 * An Hoa : general function to print a collection.
 **)
let string_of_set so s = "{ " ^ (String.concat " ; " (List.map so s)) ^ " }"


(**
 * An Hoa : Merge the partial heaps into a single heap node
 * For instance, 
 *         h::node<#,#,a> * h::node<#,b,#>
 * reduces to h::node<#,b,a> while
 *         h::node<#,#,a> * h::node<#,#,b>
 * is transformed to False.
 * TODO implement
 **)
let rec merge_partial_heaps f = match f with
	| Base fb -> let nh = merge_partial_h_formula fb.formula_base_heap in
					Base { fb with formula_base_heap = nh }
	| Or fo -> 	let nf1 = merge_partial_heaps fo.formula_or_f1 in
				let nf2 = merge_partial_heaps fo.formula_or_f2 in
					Or { fo with formula_or_f1 = nf1; formula_or_f2 = nf2; }
	| Exists fe -> let nh = merge_partial_h_formula fe.formula_exists_heap in
					Exists { fe with formula_exists_heap = nh }

and merge_partial_h_formula f = 
  Debug.no_1 "merge_partial_h_formula" 
      !print_h_formula !print_h_formula
      merge_partial_h_formula_x f

and merge_partial_h_formula_x f = 
	let sc = split_star_h f in
	let dns,vns = List.partition is_data sc in
	(* Collect the data pointers *)
	let dnrootptrs = List.map get_ptr_from_data dns in
	let dnrootptrs = Gen.BList.remove_dups_eq CP.eq_spec_var dnrootptrs in
	(* Partition the data nodes into groups of same pointer *)
	let dnodespart = List.map (fun x -> List.filter (fun y -> CP.eq_spec_var (get_ptr_from_data y) x) dns) dnrootptrs in
	(* Merge the data nodes in each group *)
	let merged_data_nodes = List.map merge_data_nodes_common_ptr dnodespart in
	(* Combine the parts to get the result *)
	combine_star_h (List.append merged_data_nodes vns)


(**
 * An Hoa : Splitting a h_formula by breaking the separation conjunction.
 **)
and split_star_h f = match f with
	| Star { h_formula_star_h1 = h1; h_formula_star_h2 = h2; } ->
		List.append (split_star_h h1) (split_star_h h2)
	| _ -> [f]


(**
 * An Hoa : Reverse operation of split_star_h i.e. combining nodes into a h_formula.
 * TODO express using fold_left instead.
 **)
and combine_star_h cs = match cs with
	| [] -> HEmp
	| h::t -> mkStarH h (combine_star_h t) no_pos


(**
 * An Hoa : Merge a list of data nodes with a common root pointer into either
 *          a single data node or HFalse if there is a clash (and HTrue if
 *          we are merging nothing. This case SHOULD NOT happen.)
 **)
and merge_data_nodes_common_ptr dns = 
	List.fold_left merge_two_nodes HEmp dns

(*LDK: TO CHECK ??? how to deal with perms correctly
Permissions v.s pertial fields
*)
(**
 * An Hoa : Supplementary function to merge two data nodes.
 **)
and merge_two_nodes dn1 dn2 =
	match dn1 with
	| DataNode { h_formula_data_node = dnsv1;
		h_formula_data_name = n1;
		h_formula_data_derv = dr1;
		h_formula_data_imm = i1;
		h_formula_data_arguments = args1;
        h_formula_data_perm = perm1;
        h_formula_data_origins = origs1;
        h_formula_data_original = orig1;
		h_formula_data_holes = holes1;
		h_formula_data_label = lb1;
		h_formula_data_remaining_branches = br1;
		h_formula_data_pruning_conditions = pc1;
		h_formula_data_pos = pos1 } -> (match dn2 with
			| DataNode { h_formula_data_node = dnsv2;
						h_formula_data_name = n2;
						h_formula_data_derv = dr2;
						h_formula_data_imm = i2;
						h_formula_data_arguments = args2;
                        h_formula_data_perm = perm2;
                        h_formula_data_origins = origs2;
                        h_formula_data_original = orig2;
						h_formula_data_holes = holes2;
						h_formula_data_label = lb2;
						h_formula_data_remaining_branches = br2;
						h_formula_data_pruning_conditions = pc2;
						h_formula_data_pos = pos2 } -> 
							(* [Internal] Check if a spec_var is a hole spec_var. *)
                            (* TO DO: ??? Can not use spec_var name to tell whether it is a hole
                            or not. It also depends on the positions stored in
                            h_formula_data_holes *)
							let is_hole_specvar sv = 
								let svname = CP.name_of_spec_var sv in
									svname.[0] = '#' in
							(* [Internal] Select the non-hole spec_var. *)
                            (* let _ = print_endline ("merge_two_nodes: \n ### args1 = " ^ (string_of_spec_var_list args1) ^ "\n ### args2 = " ^ (string_of_spec_var_list args2)) in *)
							let combine_vars sv1 sv2 =
								if (is_hole_specvar sv1) then (sv2,true) 
								else if (is_hole_specvar sv2) then (sv1,true)
								else (sv1,false)
							in
							let args, not_clashes = List.split (List.map2 combine_vars args1 args2) in
							let not_clashed = List.for_all (fun x -> x) not_clashes in
                            (* let _ = print_endline ("merge_two_nodes" ^ (string_of_bool not_clashed)) in *)
							let res = DataNode { h_formula_data_node = dnsv1;
										h_formula_data_name = n1;
						                h_formula_data_derv = dr1; (*TO CHECK*)
										h_formula_data_imm = i1;
										h_formula_data_arguments = args;
                                        h_formula_data_perm = None; (*perm1? perm2???*)
                                        h_formula_data_origins = origs1; (*??? how to merge??*)
                                        h_formula_data_original = orig1;(*??? how to merge??*)
										h_formula_data_holes = 
												Gen.BList.intersect_eq (=) holes1 holes2;
										h_formula_data_label = lb1;
										h_formula_data_remaining_branches = 
											(match br1 with
												| None -> br2
												| Some l1 -> (match br2 with
																| None -> br1
																| Some l2 -> Some (List.append l1 l2)));
										h_formula_data_pruning_conditions = List.append pc1 pc2;
										h_formula_data_pos = no_pos } in 
								if not_clashed then res else HFalse
      | HEmp -> dn1
      | HFalse -> HFalse
      | _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = ("[merge_two_nodes] Expect either HEmp or a DataNode but get " ^ (!print_h_formula dn2))} )
  | HEmp -> dn2
  | HFalse -> HFalse
  | _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = ("[merge_two_nodes] Expect either HEmp or a DataNode but get " ^ (!print_h_formula dn1)) }


(**
 * An Hoa : Create a list [x,x+1,...,x+n-1]
 **)
let rec first_naturals n x = if n = 0 then [] 
	else x :: (first_naturals (n-1) (x+1))


(**
 * An Hoa : Compute the indices of holes in a list of spec vars.
 **)
let compute_holes_list svs = 
	let temp = first_naturals (List.length svs) 0 in
	let res = List.map2 (fun x y -> if (CP.is_hole_spec_var x) then [y] else []) svs temp in
	let res = List.flatten res in
		res

(**
 * An Hoa : Check if svs contain a non-hole variable.
 **)
let is_empty svs = List.for_all CP.is_hole_spec_var svs


let mark_derv_self name f = 
  let rec h_h f = match f with
      | ViewNode h ->
        if (CP.name_of_spec_var h.h_formula_view_node)="self" && 
            h.h_formula_view_name = name then
              ViewNode {h with h_formula_view_original = false }
        else f   
      | Star s -> Star {s with 
          h_formula_star_h1 = h_h s.h_formula_star_h1;
          h_formula_star_h2 = h_h s.h_formula_star_h2;} 
      | Conj c -> Conj {c with 
          h_formula_conj_h1 = h_h c.h_formula_conj_h1;
          h_formula_conj_h2 = h_h c.h_formula_conj_h2;}
      | Phase p -> Phase {p with 
          h_formula_phase_rd = h_h p.h_formula_phase_rd;
          h_formula_phase_rw =  h_h p.h_formula_phase_rw;}     
      | DataNode _
      | Hole _ | HTrue | HFalse | HEmp | HRel _ -> f in
  let rec h_f f = match f with 
    | Or b -> Or {b with formula_or_f1 = h_f b.formula_or_f1; formula_or_f2 = h_f b.formula_or_f2; }
    | Base b-> Base {b with formula_base_heap = h_h b.formula_base_heap; }
    | Exists b-> Exists {b with formula_exists_heap = h_h b.formula_exists_heap; } in
  let rec h_struc f = match f with 
       | ECase b -> ECase{b with formula_case_branches = map_l_snd h_struc b.formula_case_branches}
       | EBase b -> EBase{b with 
            formula_struc_base = h_f b.formula_struc_base; 
            formula_struc_continuation = map_opt h_struc b.formula_struc_continuation}
       | EAssume _ -> failwith "marh_derv_self: not expecting assume\n"
       | EInfer b -> EInfer{b with formula_inf_continuation = h_struc b.formula_inf_continuation}
	   | EList b -> EList (map_l_snd h_struc b)
	   | EOr b -> EOr {b with formula_struc_or_f1 = h_struc b.formula_struc_or_f1; formula_struc_or_f2 = h_struc b.formula_struc_or_f2;}in       
  h_struc f


let push_case_f pf sf = 
  let rec helper f = match f with 
    | ECase f -> ECase {f with formula_case_branches = List.map (fun (c1,c2)-> (CP.mkAnd c1 pf no_pos, c2)) f.formula_case_branches}
    | EBase f -> EBase {f with formula_struc_continuation = map_opt helper f.formula_struc_continuation}
    | EInfer v -> EInfer {v with formula_inf_continuation = helper v.formula_inf_continuation}
    | EAssume _ -> f
    | EList b -> EList (map_l_snd helper b)
	| EOr b -> EOr {b with formula_struc_or_f1= helper b.formula_struc_or_f1; formula_struc_or_f2= helper b.formula_struc_or_f2;} in
  helper sf
  
(* this normalization removes EInfer from specs *)
let rec norm_specs (sp:struc_formula) : struc_formula = match sp with
    | ECase b -> ECase {b with formula_case_branches = map_l_snd norm_specs b.formula_case_branches}
    | EBase b ->  (* eliminate EBase if it is just true without existential *)
          if (isConstTrueFormula b.formula_struc_base) && b.formula_struc_explicit_inst==[] && b.formula_struc_implicit_inst==[] && b.formula_struc_exists==[] 
		  then match b.formula_struc_continuation with | None -> mkETrue  (mkTrueFlow ()) no_pos |Some l -> norm_specs l
          else  EBase {b with formula_struc_continuation = map_opt norm_specs b.formula_struc_continuation}
    | EAssume(svl,f,fl) -> sp
    | EInfer b -> norm_specs b.formula_inf_continuation (* eliminate EInfer where possible *)
	| EList b -> mkEList (map_l_snd norm_specs b)
	| EOr b -> mkEOr (norm_specs b.formula_struc_or_f1) (norm_specs b.formula_struc_or_f2) b.formula_struc_or_pos
let rec simplify_post post_fml post_vars = match post_fml with
  | Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos} -> 
    Or {formula_or_f1 = simplify_post f1 post_vars; 
        formula_or_f2 = simplify_post f2 post_vars; 
        formula_or_pos = pos}
  | _ -> 
    let h, p, fl, t, a = split_components post_fml in
    let p = CP.mkExists_with_simpl Omega.simplify post_vars (MCP.pure_of_mix p) None no_pos in
    let post_fml = mkBase h (MCP.mix_of_pure p) t fl a no_pos in
    post_fml



              (*formula_ext_complete = true;*)
						
let rec simp_ann_x heap pures = match heap with
  | Star {h_formula_star_h1 = h1;
    h_formula_star_h2 = h2;
    h_formula_star_pos = pos} ->
    let (h1,ps1) = simp_ann h1 pures in
    let (h2,ps2) = simp_ann h2 ps1 in
    (mkStarH h1 h2 pos,ps2)
  | Conj {h_formula_conj_h1 = h1;
    h_formula_conj_h2 = h2;
    h_formula_conj_pos = pos} ->
    let h1,ps1 = simp_ann h1 pures in
    let h2,ps2 = simp_ann h2 ps1 in
    (mkConjH h1 h2 pos,ps2)
  | Phase {h_formula_phase_rd = h1;
    h_formula_phase_rw = h2;
    h_formula_phase_pos = pos} ->
    let h1,ps1 = simp_ann h1 pures in
    let h2,ps2 = simp_ann h2 ps1 in
    (mkPhaseH h1 h2 pos,ps2)
  | DataNode data ->
    let imm = data.h_formula_data_imm in
    let ann_var = fv_ann imm in
    if ann_var = [] then (heap,pures)
    else
      let p,res = List.partition (fun p -> CP.fv p = ann_var) pures in
      begin
        match p with
        | [] -> (DataNode {data with h_formula_data_imm = mkConstAnn 2},res)
        | [hd] -> 
          let is = CP.getAnn hd in
          if is = [] then (heap,pures)
          else (DataNode {data with h_formula_data_imm = mkConstAnn (List.hd is)},res)
        | _ -> (heap,pures)
      end
  | ViewNode view ->
    let imm = view.h_formula_view_imm in
    let ann_var = fv_ann imm in
    if ann_var = [] then (heap,pures)
    else
      let p,res = List.partition (fun p -> CP.fv p = ann_var) pures in
      begin
        match p with
        | [] -> (ViewNode {view with h_formula_view_imm = mkConstAnn 2},res)
        | [hd] ->
          let is = CP.getAnn hd in
          if is = [] then (heap,pures)
          else
            (ViewNode {view with h_formula_view_imm = mkConstAnn (List.hd is)},res)
        | _ -> (heap,pures)
      end
  | _ -> (heap,pures)
     
and simp_ann heap pures =
  let pr1 = !print_h_formula in
  let pr2 = pr_list !print_pure_f in
  let pr3 = pr_pair pr1 pr2 in
  Debug.no_2 "simp_ann" pr1 pr2 pr3
    (fun _ _ -> simp_ann_x heap pures) heap pures
     
let rec simplify_fml_ann fml = match fml with
  | Or {formula_or_f1 = f1;
    formula_or_f2 = f2;
    formula_or_pos = pos} ->
    mkOr (simplify_fml_ann f1) (simplify_fml_ann f2) pos
  | Base b -> 
    let sub_ann, pures = List.partition CP.isSubAnn (CP.list_of_conjs (MCP.pure_of_mix b.formula_base_pure)) in
    let (h,ps) = simp_ann b.formula_base_heap sub_ann in
    let p = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) (CP.mkTrue no_pos) (ps@pures) in
    Base {b with formula_base_heap = h; formula_base_pure = MCP.mix_of_pure p}
  | Exists e ->
    let exists_p = MCP.pure_of_mix e.formula_exists_pure in
    let sub_ann, pures = List.partition CP.isSubAnn (CP.list_of_conjs exists_p) in
    let (h,ps) = simp_ann e.formula_exists_heap sub_ann in
    let p = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) (CP.mkTrue no_pos) (ps@pures) in
    let rm_vars = CP.diff_svl (CP.fv exists_p) (CP.fv p) in
    Exists {e with formula_exists_qvars = CP.diff_svl e.formula_exists_qvars rm_vars;
    formula_exists_heap = h; formula_exists_pure = MCP.mix_of_pure p}
    
let rec simplify_ann (sp:struc_formula) : struc_formula = match sp with
    | ECase b -> ECase {b with formula_case_branches = map_l_snd simplify_ann b.formula_case_branches}
    | EBase b -> EBase {b with formula_struc_base = simplify_fml_ann b.formula_struc_base; formula_struc_continuation = map_opt simplify_ann b.formula_struc_continuation}
    | EAssume(svl,f,fl) -> EAssume(svl,remove_lend (simplify_fml_ann f),fl)
    | EInfer b -> report_error no_pos "Do not expect EInfer at this level"
	| EList b -> mkEList (map_l_snd simplify_ann b)
	| EOr b -> mkEOr (simplify_ann b.formula_struc_or_f1) (simplify_ann b.formula_struc_or_f2) b.formula_struc_or_pos

let rec get_vars_without_rel pre_vars f = match f with
  | Or {formula_or_f1 = f1; formula_or_f2 = f2} ->
    (get_vars_without_rel pre_vars f1) @ (get_vars_without_rel pre_vars f2)
  | Base _ -> 
    let h, p, fl, t, a = split_components f in
    let vars = CP.remove_dups_svl (List.concat (List.map one_formula_fv a)) in
    (h_fv h) @ (CP.fv (CP.drop_rel_formula (MCP.pure_of_mix p))) @ vars
  | Exists e ->
    let h, p, fl, t, a = split_components f in
    let vars = List.concat (List.map one_formula_fv a) in
    let res = (h_fv h) @ (CP.fv (CP.drop_rel_formula (MCP.pure_of_mix p))) @ vars in
    let alias = MCP.ptr_equations_without_null p in
    let aset = CP.EMapSV.build_eset alias in
    let evars_to_del = List.concat (List.map (fun a -> if CP.intersect (CP.EMapSV.find_equiv_all a aset) pre_vars = [] then [] else [a]) e.formula_exists_qvars) in
    CP.diff_svl res evars_to_del


let normalize_varperm_formula_x (f:formula) : formula = 
  let rec helper f = match f with
    | Base b ->
        let mf = MCP.normalize_varperm_mix_formula b.formula_base_pure in
        Base {b with formula_base_pure = mf}
    | Exists b ->
        let mf = MCP.normalize_varperm_mix_formula b.formula_exists_pure in
        Exists {b with formula_exists_pure = mf}
    | Or o -> 
        let f1 = helper o.formula_or_f1 in
        let f2 = helper o.formula_or_f2 in
        Or {o with formula_or_f1 = f1; formula_or_f2 = f2}
  in helper f

let normalize_varperm_formula (f:formula) : formula = 
  Debug.no_1 "normalize_varperm_formula"
      !print_formula !print_formula
      normalize_varperm_formula_x f

let filter_varperm_one_formula (f:one_formula) : CP.formula list * one_formula = 
  let p = f.formula_pure in
  let ls,mf = MCP.filter_varperm_mix_formula p in
  (ls,{f with formula_pure=mf})

(* only filter in the main formula, including those in formula_*_and *)
let filter_varperm_formula_all_x (f:formula) : CP.formula list * formula = 
  let rec helper f = match f with
    | Base b ->
        let ls,mf = MCP.filter_varperm_mix_formula b.formula_base_pure in
        let a = b.formula_base_and in
        let fs,one_ls = List.split (List.map (filter_varperm_one_formula) a) in
        let ls2=List.concat fs in
        ls@ls2,Base {b with formula_base_pure = mf; 
            formula_base_and = one_ls}
    | Exists b ->
        let ls,mf = MCP.filter_varperm_mix_formula b.formula_exists_pure in
        let a = b.formula_exists_and in
        let fs,one_ls = List.split (List.map (filter_varperm_one_formula) a) in
        let ls2=List.concat fs in
        ls@ls2,Exists {b with formula_exists_pure = mf;
            formula_exists_and = one_ls}
    | Or o ->
        let ls1,f1 = helper o.formula_or_f1 in
        let ls2,f2 = helper o.formula_or_f2 in
        if (ls1=[] && ls2=[]) then
         ( [],Or {o with formula_or_f1 = f1; formula_or_f2 = f2})
        else
        (*This case may only happen when there is PermVar annotations*)
        report_error no_pos "filter_varperm_formula: disjunctive form"
         (* TO CHECK : can use approximation *)
  in helper f

let rec partition_triple fun1 fun2 lst = match lst with
  | [] -> ([],[],[])
  | l::ls -> 
    let (tail1,tail2,tail3) = partition_triple fun1 fun2 ls in
    if fun1 l then (l::tail1,tail2,tail3) else
    if fun2 l then (tail1,l::tail2,tail3) else (tail1,tail2,l::tail3)

let split_triple lst = List.fold_left (fun (a1,a2,a3) (b1,b2,b3) -> (a1@[b1],a2@[b2],a3@[b3])) ([],[],[]) lst

let add_fst elem = fun (a1,a2,a3) -> (elem@a1,a2,a3)

let add_rd elem = fun (a1,a2,a3) -> (a1,a2,elem@a3)

let rec get_pre_post_vars (pre_vars: CP.spec_var list) (sp:struc_formula): (CP.spec_var list * CP.spec_var list * CP.spec_var list) =
  match sp with
    | ECase b -> 
      let res = List.map (fun (p,s)-> add_fst (CP.fv p) (get_pre_post_vars pre_vars s)) b.formula_case_branches in
	  List.fold_left (fun (a1,a2,a3) (c1,c2,c3)-> (a1@c1,a2@c2,a3@c3)) ([],[],[]) res
      (*let pres,posts,inf_vars = split_triple res in (List.concat pres, List.concat posts, List.concat inf_vars)*)
    | EBase b -> 
		let base_vars =  fv b.formula_struc_base in
		(match b.formula_struc_continuation with
		| None -> (base_vars,[],[])
		| Some l ->  add_fst base_vars (get_pre_post_vars (pre_vars@base_vars) l))
    | EAssume(svl,f,fl) -> ([], (List.map CP.to_primed svl) @ (get_vars_without_rel pre_vars f), [])
    | EInfer b -> add_rd b.formula_inf_vars (get_pre_post_vars pre_vars b.formula_inf_continuation)
	| EList b->  
		let l = List.map (fun (_,c)-> get_pre_post_vars pre_vars c) b in
		List.fold_left (fun (a1,a2,a3) (c1,c2,c3)-> (a1@c1,a2@c2,a3@c3)) ([],[],[]) l
    | EOr b -> 
		let pre1, post1, iv1 = get_pre_post_vars pre_vars b.formula_struc_or_f1 in
		let pre2, post2, iv2 = get_pre_post_vars pre_vars b.formula_struc_or_f2 in
		(pre1@pre2, post1@post2, iv1@iv2)
		
let filter_varperm_formula_all (f:formula) : CP.formula list * formula =
  let pr_out (ls,f) = "\n ### ls = " ^ (pr_list !print_pure_f ls) ^ "\n ### f = " ^ (!print_formula f) in
  Debug.no_1 "filter_varperm_formula_all"  !print_formula pr_out filter_varperm_formula_all_x f


(* only filter the main formula, not filter formula_*_and *)
let filter_varperm_formula_x (f:formula) : CP.formula list * formula = 
  let rec helper f = match f with
    | Base b ->
        let ls,mf = MCP.filter_varperm_mix_formula b.formula_base_pure in
        ls,Base {b with formula_base_pure = mf}
    | Exists b ->
        let ls,mf = MCP.filter_varperm_mix_formula b.formula_exists_pure in
        ls,Exists {b with formula_exists_pure = mf}
    | Or o ->
        let ls1,f1 = helper o.formula_or_f1 in
        let ls2,f2 = helper o.formula_or_f2 in
        if (ls1=[] && ls2=[]) then
         ( [],Or {o with formula_or_f1 = f1; formula_or_f2 = f2})
        else (*This case may only happen when there is PermVar annotations*)
        report_error no_pos "filter_varperm_formula: disjunctive form"
  in helper f

(* only filter the main formula, not filter formula_*_and *)
let filter_varperm_formula (f:formula) : CP.formula list * formula =
  let pr_out (ls,f) = "\n ### ls = " ^ (pr_list !print_pure_f ls) ^ "\n ### f = " ^ (!print_formula f) in
  Debug.no_1 "filter_varperm_formula"  !print_formula pr_out filter_varperm_formula_x f

let drop_varperm_formula (f:formula) = 
  let rec helper f =
    match f with
      | Base b-> Base {b with formula_base_pure = MCP.drop_varperm_mix_formula b.formula_base_pure}
      | Exists b-> Exists {b with formula_exists_pure = MCP.drop_varperm_mix_formula b.formula_exists_pure}
      | Or b-> Or {b with formula_or_f1 = helper b.formula_or_f1;
	      formula_or_f2 = helper b.formula_or_f2}
  in
  helper f

let get_varperm_formula_x (f:formula) typ : CP.spec_var list =
  let rec helper f =
    match f with
      | Base b-> 
          let p = b.formula_base_pure in
          let res = MCP.get_varperm_mix_formula p typ in
          res
      | Exists b-> 
          let p = b.formula_exists_pure in
          let res = MCP.get_varperm_mix_formula p typ in
          res
      | Or b-> 
          let res1 = helper b.formula_or_f1 in
          let res2 = helper b.formula_or_f1 in
          (*approximation*)
          (match typ with
            | VP_Zero -> Gen.BList.remove_dups_eq CP.eq_spec_var_ident (res1@res2)
            | VP_Full -> Gen.BList.intersect_eq CP.eq_spec_var_ident res1 res2
            | VP_Value -> Gen.BList.intersect_eq CP.eq_spec_var_ident res1 res2
          )
  in
  helper f

let get_varperm_formula (f:formula) typ : CP.spec_var list =
  Debug.no_2 "get_varperm_formula" 
      !print_formula string_of_vp_ann !print_svl
      get_varperm_formula_x f typ

(*get varperm of all concurrent threads*)
let get_varperm_formula_all_x (f:formula) typ : CP.spec_var list =
  let rec helper f =
    match f with
      | Base b-> 
          let p = b.formula_base_pure in
          let a = b.formula_base_and in
          let func (a: one_formula) = 
            let a_base = formula_of_one_formula a in
            (helper a_base)
          in
          (*get varperm from child threads*)
          let c_vars = List.concat (List.map func a) in
          (*get varperm from main thread*)
          let m_vars = MCP.get_varperm_mix_formula p typ in
          (m_vars@c_vars)
      | Exists b-> 
          let p = b.formula_exists_pure in
          let a = b.formula_exists_and in
          let func (a: one_formula) = 
            let a_base = formula_of_one_formula a in
            (helper a_base)
          in
          (*get varperm from child threads*)
          let c_vars = List.concat (List.map func a) in
          (*get varperm from main thread*)
          let m_vars = MCP.get_varperm_mix_formula p typ in
          (m_vars@c_vars)
      | Or b-> 
          let res1 = helper b.formula_or_f1 in
          let res2 = helper b.formula_or_f1 in
          (*approximation*)
          (match typ with
            | VP_Zero -> Gen.BList.remove_dups_eq CP.eq_spec_var_ident (res1@res2)
            | VP_Full -> Gen.BList.intersect_eq CP.eq_spec_var_ident res1 res2
            | VP_Value -> Gen.BList.intersect_eq CP.eq_spec_var_ident res1 res2
          )
  in
  helper f

(*get varperm of all concurrent threads*)
let get_varperm_formula_all (f:formula) typ : CP.spec_var list =
  Debug.no_2 "get_varperm_formula_all"
      !print_formula string_of_vp_ann !print_svl
      get_varperm_formula_x f typ

(*automatically generate pre/post conditions of init[lock_sort](lock_var,lock_args) *)
let prepost_of_init_x (var:CP.spec_var) name sort (args:CP.spec_var list) (lbl:formula_label) pos = 
  let data_node = DataNode ({
      h_formula_data_node = var;
      h_formula_data_name = name;
	  h_formula_data_derv = false;
	  h_formula_data_imm = ConstAnn(Mutable);
	  h_formula_data_perm = None;
	  h_formula_data_origins = [];
	  h_formula_data_original = false; (*TO CHECK: tmporarily, to prohibit SPLITTING of permission*)
      h_formula_data_arguments = []; (*TO CHECK*)
	  h_formula_data_holes = [];
      h_formula_data_remaining_branches = None;
      h_formula_data_pruning_conditions = [];
      h_formula_data_label = None;
      h_formula_data_pos = pos}) 
  in
  let lock_node = ViewNode ({  
      h_formula_view_node = var; (*Have to reserve type of view_node to finalize*)
      h_formula_view_name = sort; (*lock_sort*)
      h_formula_view_derv = false;
      h_formula_view_imm = ConstAnn(Mutable); 
      h_formula_view_perm = None;
      h_formula_view_arguments = args;
      h_formula_view_modes = []; (*???*)
      h_formula_view_coercible = true; (*??*)
      h_formula_view_origins = [];
      h_formula_view_original = false;(*TO CHECK: tmporarily, to prohibit SPLITTING of permission*)
      h_formula_view_lhs_case = false;
      h_formula_view_unfold_num = 0;
      h_formula_view_remaining_branches = None;
      h_formula_view_pruning_conditions = [];
      h_formula_view_label = None;
      h_formula_view_pos = pos })
  in
  let post = formula_of_heap lock_node pos in
  let post = EAssume ([],post,lbl) in
  let pre = formula_of_heap data_node pos in
  EBase { 
	formula_struc_explicit_inst = [];
	formula_struc_implicit_inst = [];
	formula_struc_exists = [];
	formula_struc_base = pre;
	formula_struc_continuation = Some post;
	formula_struc_pos = pos}
  

(*automatically generate pre/post conditions of init[lock_sort](lock_var,lock_args) *)
let prepost_of_init (var:CP.spec_var) name sort (args:CP.spec_var list) (lbl:formula_label) pos = 
  Debug.no_4 "prepost_of_init"
      !print_sv
      (fun str -> str)
      (fun str -> str)
      !print_svl
      !print_struc_formula
      (fun _ _ _ _ -> prepost_of_init_x var name sort args lbl pos) var name sort args

(*automatically generate pre/post conditions of finalize[lock_sort](lock_var,lock_args) *)
let prepost_of_finalize_x (var:CP.spec_var) name sort (args:CP.spec_var list) (lbl:formula_label) pos : struc_formula = 
  let data_node = DataNode ({
      h_formula_data_node = var;
      h_formula_data_name = name;
	  h_formula_data_derv = false;
	  h_formula_data_imm = ConstAnn(Mutable);
	  h_formula_data_perm = None;
	  h_formula_data_origins = [];
	  h_formula_data_original = true; (*after finalize, allow SPLIT*)
      h_formula_data_arguments = []; (*TO CHECK*)
	  h_formula_data_holes = [];
      h_formula_data_remaining_branches = None;
      h_formula_data_pruning_conditions = [];
      h_formula_data_label = None;
      h_formula_data_pos = pos}) 
  in
  let lock_node = ViewNode ({  
      h_formula_view_node = var; (*Have to reserve type of view_node to finalize*)
      h_formula_view_name = sort; (*lock_sort*)
      h_formula_view_derv = false;
      h_formula_view_imm = ConstAnn(Mutable); 
      h_formula_view_perm = None;
      h_formula_view_arguments = args;
      h_formula_view_modes = []; (*???*)
      h_formula_view_coercible = true; (*??*)
      h_formula_view_origins = [];
      h_formula_view_original = false; (*NOT ALLOW SPLIT*)
      h_formula_view_lhs_case = false;
      h_formula_view_unfold_num = 0;
      h_formula_view_remaining_branches = None;
      h_formula_view_pruning_conditions = [];
      h_formula_view_label = None;
      h_formula_view_pos = pos })
  in
  let post = formula_of_heap data_node pos in
  let post = EAssume ([],post,lbl) in
  let pre = formula_of_heap lock_node pos in
  EBase { 
	formula_struc_explicit_inst = [];
	formula_struc_implicit_inst = [];
	formula_struc_exists = [];
	formula_struc_base = pre;
	formula_struc_continuation = Some post;
	formula_struc_pos = pos}

(*automatically generate pre/post conditions of finalize[lock_sort](lock_var,lock_args) *)
let prepost_of_finalize (var:CP.spec_var) name sort (args:CP.spec_var list) (lbl:formula_label) pos : struc_formula = 
  Debug.no_4 "prepost_of_finalize" !print_sv (fun str -> str) (fun str -> str) !print_svl
      !print_struc_formula       (fun _ _ _ _ -> prepost_of_finalize_x var name sort args lbl pos) var name sort args
		
let rec get_or_post_x rel_id (sp:struc_formula): formula list =  match sp with
  | ECase b -> fold_l_snd (get_or_post_x rel_id) b.formula_case_branches
  | EBase b -> fold_opt (get_or_post_x rel_id) b.formula_struc_continuation
  | EAssume(svl,f,fl) -> 
	(match f with
    | Or _ -> if CP.intersect (fv f) rel_id = [] then [] else [f]
    | _ -> [])
  | EInfer b -> get_or_post_x rel_id b.formula_inf_continuation 
  | EList b -> fold_l_snd (get_or_post_x rel_id) b
  | EOr b -> (get_or_post_x rel_id b.formula_struc_or_f1)@(get_or_post_x rel_id b.formula_struc_or_f2)

and get_or_post sp rel_id =
  let pr1 = !print_struc_formula in
  let pr2 = !print_svl in
  let pr3 = pr_list !print_formula in
  Debug.no_2 "get_or_post" pr1 pr2 pr3
    (fun _ _ -> get_or_post_x rel_id sp) sp rel_id

let prepost_of_acquire_x (var:CP.spec_var) sort (args:CP.spec_var list) (inv:formula) (lbl:formula_label) pos : struc_formula =
  let fresh_perm_name = Cpure.fresh_old_name "f" in
  let perm_t = cperm_typ () in
  let fresh_perm =  Cpure.SpecVar (perm_t,fresh_perm_name, Unprimed) in (*LDK TO CHECK*)
  let lock_node = ViewNode ({  
      h_formula_view_node = var; (*Have to reserve type of view_node to finalize*)
      h_formula_view_name = sort; (*lock_sort*)
      h_formula_view_derv = false;
      h_formula_view_imm = ConstAnn(Mutable); 
      h_formula_view_perm = Some fresh_perm;
      h_formula_view_arguments = args;
      h_formula_view_modes = []; (*???*)
      h_formula_view_coercible = true; (*??*)
      h_formula_view_origins = [];
      h_formula_view_original = false; (*NOT ALLOW SPLIT lemmas*)
      h_formula_view_lhs_case = false;
      h_formula_view_unfold_num = 0;
      h_formula_view_remaining_branches = None;
      h_formula_view_pruning_conditions = [];
      h_formula_view_label = None;
      h_formula_view_pos = pos })
  in
  let read_f = mkPermInv () fresh_perm in
  let tmp = formula_of_heap lock_node pos in
  let post = normalize 5 inv tmp pos in
  let post = EAssume ([],post,lbl) in
  let pre = mkBase lock_node (MCP.memoise_add_pure_N (MCP.mkMTrue pos) read_f) TypeTrue (mkTrueFlow ()) [] pos in
  EBase {
	formula_struc_explicit_inst = [];
	formula_struc_implicit_inst = [fresh_perm]; (*instantiate f*)
	formula_struc_exists = [];
	formula_struc_base = pre;
	formula_struc_continuation = Some post;
	formula_struc_pos = pos}

let prepost_of_acquire (var:CP.spec_var) sort (args:CP.spec_var list) (inv:formula) (lbl:formula_label) pos : struc_formula =
  Debug.no_4 "prepost_of_acquire" !print_sv (fun str -> str) !print_svl !print_formula !print_struc_formula
      (fun _ _ _ _ -> prepost_of_acquire_x var sort args inv lbl pos) var sort args inv
let unwrap_exists f =
  let rec helper f =
    match f with
      | Base b -> ([],[],f)
      | Exists b -> (b.formula_exists_qvars, 
        h_fv b.formula_exists_heap, Exists {b with formula_exists_qvars=[]} )
      | Or b -> 
        let (e1,h1,f1) = helper b.formula_or_f1 in
        let (e2,h2,f2) = helper b.formula_or_f2 in
        (e1@e2,h1@h2,mkOr f1 f2 b.formula_or_pos)
  in helper f

let add_exists vs f =
  if vs==[] then f
  else match f with
    | Exists b -> Exists {b with formula_exists_qvars=(vs@b.formula_exists_qvars)}
    | _ -> report_error no_pos "expecting ExistBase formula here"

let lax_impl_of_post f =
  let (evs,hvs,bf) = unwrap_exists f in
  let impl_vs = CP.intersect evs hvs in
  let new_evs = CP.diff_svl evs impl_vs in
  (impl_vs, add_exists new_evs bf)

let fv_wo_rel (f:formula) =
  let vs = fv f in
  List.filter (fun v -> (CP.type_of_spec_var v) != RelT) vs

(* Termination: Check whether a formula contains LexVar *) 
(* TODO: Termination: Need to add default term info
 * into a branch of OR context *) 
let rec has_lexvar_formula f =
  match f with
  | Base _
  | Exists _ ->
      let _, pure_f, _, _, a = split_components f in 
      CP.has_lexvar (MCP.pure_of_mix pure_f) 
  | Or { formula_or_f1 = f1; formula_or_f2 = f2 } ->
      (has_lexvar_formula f1) || (has_lexvar_formula f2)

     
let rec norm_struc_with_lexvar is_primitive struc_f  = match struc_f with
  | ECase ef -> ECase { ef with formula_case_branches = map_l_snd (norm_struc_with_lexvar is_primitive) ef.formula_case_branches }
  | EBase ef ->
      if (has_lexvar_formula ef.formula_struc_base) then struc_f
      else EBase { ef with formula_struc_continuation = map_opt (norm_struc_with_lexvar is_primitive) ef.formula_struc_continuation }
  | EAssume _ ->
      let lexvar = 
        if is_primitive then  CP.mkLexVar Term [] [] no_pos
        else CP.mkLexVar MayLoop [] [] no_pos in 
      mkEBase_with_cont (CP.mkPure lexvar) (Some struc_f) no_pos
  | EInfer ef -> EInfer { ef with formula_inf_continuation = norm_struc_with_lexvar is_primitive ef.formula_inf_continuation }
  | EList b -> mkEList (map_l_snd (norm_struc_with_lexvar is_primitive) b)
  | EOr b -> mkEOr (norm_struc_with_lexvar is_primitive b.formula_struc_or_f1) (norm_struc_with_lexvar is_primitive b.formula_struc_or_f2) b.formula_struc_or_pos

(* Termination: Add the call numbers and the implicit phase 
 * variables to specifications if the option 
 * --dis-call-num and --dis-phase-num are not enabled (default) *)      
 
let rec add_term_nums_struc struc_f log_vars call_num add_phase = match struc_f with
  | ECase ef ->
      let n_cl, pvs  = map_l_snd_res (fun c-> add_term_nums_struc c log_vars call_num add_phase) ef.formula_case_branches in
      (ECase { ef with formula_case_branches = n_cl }, List.concat pvs)
  | EBase ef ->
      let n_cont, pvc = map_opt_res (fun c-> add_term_nums_struc c log_vars call_num add_phase) ef.formula_struc_continuation in
      let n_base, pvb = add_term_nums_formula ef.formula_struc_base log_vars call_num add_phase in
      (EBase { ef with
        formula_struc_base = n_base;
        formula_struc_continuation = n_cont}, pvb @ pvc)
  | EAssume _ -> (struc_f, [])
  | EInfer ef ->
      let n_cont, pvc = add_term_nums_struc ef.formula_inf_continuation log_vars call_num add_phase in
      (EInfer { ef with formula_inf_continuation = n_cont }, pvc)
  | EList b -> 
	let n_sf, pvs = map_l_snd_res (fun c-> add_term_nums_struc c log_vars call_num add_phase) b in
	(EList n_sf, List.concat pvs)
  | EOr b -> 
	let f1,l1 = add_term_nums_struc b.formula_struc_or_f1 log_vars call_num add_phase in
	let f2,l2 = add_term_nums_struc b.formula_struc_or_f2 log_vars call_num add_phase in
	(EOr {b with formula_struc_or_f1 = f1;formula_struc_or_f2 = f2;}, l1@l2)

and add_term_nums_formula f log_vars call_num add_phase = 
  match f with
  | Base ({ formula_base_pure = p } as base) ->
      let p = MCP.pure_of_mix p in
      let pv = fresh_phase_var_opt add_phase in
      let n_p, n_pv = CP.add_term_nums_pure p log_vars call_num pv in
      (Base { base with formula_base_pure = MCP.mix_of_pure n_p }, n_pv)
  | Exists ({ formula_exists_pure = p } as ex) ->
      let p = MCP.pure_of_mix p in
      let pv = fresh_phase_var_opt add_phase in
      let n_p, n_pv = CP.add_term_nums_pure p log_vars call_num pv in
      (Exists { ex with formula_exists_pure = MCP.mix_of_pure n_p }, n_pv)
  | Or ({ formula_or_f1 = f1; formula_or_f2 = f2 } as orf) ->
      let n_f1, pv1 = add_term_nums_formula f1 log_vars call_num add_phase in
      let n_f2, pv2 = add_term_nums_formula f2 log_vars call_num add_phase in
      (Or { orf with formula_or_f1 = n_f1; formula_or_f2 = n_f2 }, pv1 @ pv2)

and fresh_phase_var_opt add_phase = 
  if add_phase then
    let pv_name = fresh_any_name "pv" in
    Some (CP.SpecVar(Int, pv_name, Unprimed))
  else None

(* Termination: Count the number of Term in a specification *)  
let rec count_term_struc (sf: struc_formula) : int = match sf with 
  | ECase b -> List.fold_left (fun acc (_, sf) -> acc + (count_term_struc sf)) 0 b.formula_case_branches
  | EBase b ->(match b.formula_struc_continuation with 
	| None ->count_term_formula b.formula_struc_base
	| Some l -> (count_term_formula b.formula_struc_base) + (count_term_struc l))
  | EAssume _ -> 0
  | EInfer b -> count_term_struc b.formula_inf_continuation
  | EList b -> List.fold_left (fun acc ef -> acc + (count_term_struc (snd ef))) 0 b
  | EOr b -> (count_term_struc b.formula_struc_or_f1)+(count_term_struc b.formula_struc_or_f2)
and count_term_formula f = match f with
  | Base b -> CP.count_term_pure (MCP.pure_of_mix b.formula_base_pure)
  | Exists b -> CP.count_term_pure (MCP.pure_of_mix b.formula_exists_pure)
  | Or b -> (count_term_formula b.formula_or_f1) + (count_term_formula b.formula_or_f2)
  
let get_ctx_label sctx =
  let rec helper c = match c with 
    | Ctx es -> es.es_group_lbl
    | OCtx (c1,c2) -> helper c1 
  in helper sctx
  
let update_ctx_label sctx l =
  let rec helper c = match c with 
    | Ctx es -> Ctx {es with es_group_lbl = l}
    | OCtx (c1,c2) -> OCtx (helper c1,helper c2) 
  in 
  if Lab2_List.is_unlabelled l then sctx
  else helper sctx

let merge_struc_pre (sp:struc_formula) (pre:formula list): struc_formula = 
	let rec helper sp pre = match sp with
		| ECase b -> report_error b.formula_case_pos ("Not supported nested case analysis")
		| EBase b -> sp
		| EAssume(svl,f,fl) -> 
			if isConstTrueFormula pre then sp
			else mkEBase pre (Some sp) no_pos
		| EInfer b -> EInfer {b with formula_inf_continuation = helper b.formula_inf_continuation pre}
		| EList _ | EOr _ -> report_error no_pos "Stages not supported" in
	match sp with
		| EList b-> (try EList (List.map2 (fun (l,e) a ->(l,helper e a)) b pre) with _ -> sp)
		| EOr b -> report_error no_pos "Do not expect EOr at merge_struc_pre"
		| _ -> (match pre with | x::[] -> helper sp x | _ -> sp)


let prepost_of_release_x (var:CP.spec_var) sort (args:CP.spec_var list) (inv:formula) (lbl:formula_label) pos : struc_formula =
  let fresh_perm_name = Cpure.fresh_old_name "f" in
  let perm_t = cperm_typ () in
  let fresh_perm =  Cpure.SpecVar (perm_t,fresh_perm_name, Unprimed) in (*LDK TO CHECK*)
  let lock_node = ViewNode ({  
      h_formula_view_node = var; (*Have to reserve type of view_node to finalize*)
      h_formula_view_name = sort; (*lock_sort*)
      h_formula_view_derv = false;
      h_formula_view_imm = ConstAnn(Mutable); 
      h_formula_view_perm = Some fresh_perm;
      h_formula_view_arguments = args;
      h_formula_view_modes = []; (*???*)
      h_formula_view_coercible = true; (*??*)
      h_formula_view_origins = [];
      h_formula_view_original = false;(*NOT ALLOW SPLIT lemmas in pre, but allow in post*)
      h_formula_view_lhs_case = false;
      h_formula_view_unfold_num = 0;
      h_formula_view_remaining_branches = None;
      h_formula_view_pruning_conditions = [];
      h_formula_view_label = None;
      h_formula_view_pos = pos })
  in
  let tmp = formula_of_heap lock_node pos in (*not allow SPLIT in pre*)
  let read_f = mkPermInv () fresh_perm in (*only need a certain permission to read*)
  let tmp_pre = mkBase lock_node (MCP.memoise_add_pure_N (MCP.mkMTrue pos) read_f) TypeTrue (mkTrueFlow ()) [] pos in
  let tmp = add_original tmp true in  (*but allow SPLIT in post*)
  let post = EAssume ([],tmp,lbl) in
  let pre = normalize 5 inv tmp_pre pos in
  let pre_evars, pre_base = split_quantifiers pre in
  EBase { 
	formula_struc_explicit_inst = [];
	formula_struc_implicit_inst = fresh_perm::pre_evars; (*instantiate*)
	formula_struc_exists = [];
	formula_struc_base = pre_base;
	formula_struc_continuation = Some post;
	formula_struc_pos = pos}

let prepost_of_release (var:CP.spec_var) sort (args:CP.spec_var list) (inv:formula) (lbl:formula_label) pos : struc_formula =
  Debug.no_4 "prepost_of_release" !print_sv (fun str -> str) !print_svl !print_formula !print_struc_formula
      (fun _ _ _ _ -> prepost_of_release_x var sort args inv lbl pos) var sort args inv

(*IMITATE CF.COMPOSE but do not compose 2 formulas*)
(* Put post into formula_*_and of f instread*)
let compose_formula_and_x (f : formula) (post : formula) (id: CP.spec_var) (ref_vars : CP.spec_var list) (val_vars : CP.spec_var list) pos =
  (*IMITATE CF.COMPOSE but do not compose 2 formulas*)
  (*Rename ref_vars for later join*)
  let rs = CP.fresh_spec_vars ref_vars in
  let rho1 = List.combine (List.map CP.to_unprimed ref_vars) rs in
  let rho2 = List.combine (List.map CP.to_primed ref_vars) rs in
  let new_f = subst rho2 f in
  let new_post = subst rho1 post in
  (* let new_f = push_exists rs new_f in (\* IMPORTANT: do not do this*\) *)
  (*Rename @value for later join*)
  (* y'=1 and x'=x+y' => y'=y_20 & y_20=1 and x'=x+y_20*)
  let fresh_vars = CP.fresh_spec_vars val_vars in
  let uprimed_vars = (List.map CP.to_unprimed fresh_vars) in
  let rho3 = List.combine val_vars uprimed_vars in
  (*x'=x+y_20*)
  let new_post2 = subst rho3 new_post in
  (*y_20=1*)
  let new_f2 = subst rho3 new_f in
  (*y'=y_20*)
  let func v1 v2 =
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (v1,no_pos)),
        (Cpure.Var (v2,no_pos)),
        no_pos
    )),None), None)
  in
  let new_f3 = List.fold_left (fun f (v1,v2) -> 
      let eq_f = func v1 v2 in
      (add_pure_formula_to_formula eq_f f)
  ) new_f2 rho3 in
  (*---------------------------------------------------*)
  (*NORMALIZE: f1 and (f2 or f3) ===> (f1 and f2) or (f1 and f3)*)
  let rec helper f post = 
    match post with
      | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
          Or ({formula_or_f1 = helper f f1; formula_or_f2 =  helper f f2; formula_or_pos = pos}) (*This case can not happen*)
      | _ ->
          (*Base or Exists*)
          let qvars,base = split_quantifiers post in
          let one_f = one_formula_of_formula base id in
          let one_f = {one_f with formula_ref_vars = ref_vars;} in
          (*add thread id*)
          (* let _ = print_endline ("\nLDK:" ^ (Cprinter.string_of_one_formula one_f)) in *)
          let evars = (* ref_vars@ *)qvars in (*TO CHECK*)
          let f1 = add_quantifiers evars f in
          let f2 = add_formula_and [one_f] f1 in
          f2
  in
  helper new_f3 new_post2

let compose_formula_and (f : formula) (post : formula) (id: CP.spec_var) (ref_vars : CP.spec_var list) (val_vars : CP.spec_var list) pos =
  Debug.no_2 "compose_formula_and"
      !print_formula 
      !print_formula 
      !print_formula
      (fun _ _ -> compose_formula_and_x f post id ref_vars val_vars pos) f post

(*add the post condition (phi) into formul_*_and *)
(*special compose_context_formula for concurrency*)
(*Ctx es o (f1 or f2) -> OCtx (es o f1) (es o f2)*)
let compose_context_formula_and (ctx : context) (phi : formula) (id: CP.spec_var) (ref_vars : CP.spec_var list) pos =
  let rec helper ctx phi = 
    (match ctx with
      | Ctx es -> begin
	      match phi with
		    | Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
			    let new_c1 = helper ctx phi1 in
			    let new_c2 = helper ctx phi2 in
			    let res = (mkOCtx new_c1 new_c2 pos ) in
			    res
		    | _ -> 
                (*collect @var for later use *)
                let val_vars = MCP.get_varperm_mix_formula es.es_pure  VP_Value in
                (*then clear entail_*)
                let es = clear_entailment_history_es_es es in
                let f = es.es_formula in
                (*   (\*IMITATE CF.COMPOSE but do not compose 2 formulas*\) *)
                let f2 = compose_formula_and f phi id ref_vars val_vars pos in
                let new_es = {es with
                    es_formula = f2;
                    es_unsat_flag =false;}
                in
                Ctx new_es
	  end
      | OCtx (c1, c2) -> 
	      let new_c1 = helper c1 phi in
	      let new_c2 = helper c2 phi in
	      let res = (mkOCtx new_c1 new_c2 pos) in
		  res
    )
  in
  helper ctx phi


let has_formula_and (f : formula) : bool = 
  let rec helper f = match f with
    | Base {formula_base_and = a}
    | Exists {formula_exists_and = a} ->
        (a!=[])
    | Or {formula_or_f1 = f1; formula_or_f2 =f2} ->
          (helper f1) || (helper f2) (*approximation*)
  in helper f

(*Automatically infer VPERM spec for sequential spec*)
let rec norm_struc_vperm struc_f ref_vars val_vars =
  Debug.no_3 "norm_ext_vperm" 
      !print_struc_formula !print_svl !print_svl !print_struc_formula
      norm_struc_vperm_x struc_f ref_vars val_vars

and norm_struc_vperm_x struc_f ref_vars val_vars = match struc_f with
  | ECase ({ formula_case_branches = cl } as ef) ->
      let n_cl = List.map (fun (c, sf) -> 
        (c, norm_struc_vperm sf ref_vars val_vars)) cl in
      ECase { ef with formula_case_branches = n_cl }
  | EBase ef ->
      let b = ef.formula_struc_base in
	  let cont = ef.formula_struc_continuation in
      let pos = ef.formula_struc_pos in
      if not (has_formula_and b) then
        (*sequential pre-condition*)
        let r_vars = get_varperm_formula b VP_Full in
        let v_vars = get_varperm_formula b VP_Value in
        let diff_r_vars = Gen.BList.difference_eq CP.eq_spec_var_ident r_vars ref_vars in
        let diff_v_vars = Gen.BList.difference_eq CP.eq_spec_var_ident v_vars val_vars in
        (*The specification of VPERM is not correct*)
        if (diff_r_vars!=[] || diff_v_vars!=[]) then
          let m1 = if diff_r_vars!=[] then "@full permissions not matched." else "" in
          let m2 = if diff_v_vars!=[] then "@val permissions not matched." else "" in
          Error.report_error { Error.error_loc = pos;Error.error_text = "VPERM specification is not correct. " ^ m1 ^ m2 ^ "\n" ^ (!print_struc_formula struc_f)}
        else
          let new_b = drop_varperm_formula b in
          let ref_f = CP.mk_varperm VP_Full ref_vars pos in
          let val_f = CP.mk_varperm VP_Value val_vars pos in
          let new_b = add_pure_formula_to_formula ref_f new_b in
          let new_b = add_pure_formula_to_formula val_f new_b in
          let n_cont = map_opt (fun c-> norm_struc_vperm c [] []) cont in
          EBase{ef with formula_struc_base = new_b; formula_struc_continuation = n_cont}
      else
        (*concurrency spec. USERS specify this precondition.
          Proceed to check for post-condition*)
        let n_cont = map_opt (fun c-> norm_struc_vperm c [] []) cont in
          EBase{ef with formula_struc_continuation = n_cont}
  | EAssume (vars,post,lb) ->
      (*We have (ref) vars in the post-condition*)
      let pos = pos_of_formula post in
      if not (has_formula_and post) then
        (*sequential post-condition*)
        let r_vars = get_varperm_formula post VP_Full in
        let diff_r_vars = Gen.BList.difference_eq CP.eq_spec_var_ident r_vars vars in
        if (diff_r_vars!=[]) then
          Error.report_error { Error.error_loc = pos;Error.error_text = "VPERM specification is not correct. @full permissions not matched.\n" ^ (!print_struc_formula struc_f)}
        else
          let new_post = drop_varperm_formula post in
          let ref_f = CP.mk_varperm VP_Full vars pos in
          let new_post = add_pure_formula_to_formula ref_f new_post in
          EAssume (vars,new_post,lb)
      else
        (*concurrency spec. USERS specify this*)
        struc_f
  | EInfer ({ formula_inf_continuation = cont }) ->struc_f (*Not handle this at the moment*)
  | EOr b -> EOr {b with 
				formula_struc_or_f1= norm_struc_vperm_x b.formula_struc_or_f1 ref_vars val_vars;
				formula_struc_or_f2= norm_struc_vperm_x b.formula_struc_or_f2 ref_vars val_vars;}
  | EList b-> EList (map_l_snd (fun c-> norm_struc_vperm_x c ref_vars val_vars) b)

let rec list_of_posts (sp:struc_formula) = match sp with
  | ECase b -> List.concat (List.map (fun (p,c) -> let res = list_of_posts c in
    List.map (fun (pures,post) -> ([p]@pures,post)) res) b.formula_case_branches)
  | EBase b ->
    (match b.formula_struc_continuation with
      | None -> []
      | Some f -> list_of_posts f)
  | EAssume(_,f,_) -> [([],f)]
  | EInfer b -> list_of_posts b.formula_inf_continuation
  | EList b -> List.concat (List.map (fun (_,e) -> list_of_posts e) b)
  | EOr b -> list_of_posts b.formula_struc_or_f1 @ list_of_posts b.formula_struc_or_f2

let rec transform_spec (sp:struc_formula) pairs = match sp with
  | ECase b -> ECase {b with formula_case_branches = (List.map (fun (p,c) -> 
    let new_pairs = List.concat (List.map (fun (x,y) -> if List.hd x == p then [(List.tl x,y)] else []) pairs) in
    (p,transform_spec c new_pairs)) b.formula_case_branches)}
  | EBase b -> EBase {b with formula_struc_continuation =
    (match b.formula_struc_continuation with
      | None -> None
      | Some f -> Some (transform_spec f pairs))}
  | EAssume(svl,f,fl) -> (match pairs with 
      | [([],p2)] -> EAssume(svl,p2,fl)
      | _ -> report_error no_pos "Error in transforming spec")
  | EInfer b -> EInfer {b with formula_inf_continuation = transform_spec b.formula_inf_continuation pairs}
  | EList b -> EList (List.map (fun (l,e) ->(l,transform_spec e pairs)) b)
  | EOr b -> EOr {b with formula_struc_or_f1 = transform_spec b.formula_struc_or_f1 pairs;
                         formula_struc_or_f2 = transform_spec b.formula_struc_or_f2 pairs}

let sum_of_int_lst lst = List.fold_left (+) 0 lst

let rec no_of_cnts_heap heap = match heap with
  | Star h -> no_of_cnts_heap h.h_formula_star_h1 + no_of_cnts_heap h.h_formula_star_h2
  | Conj h -> no_of_cnts_heap h.h_formula_conj_h1 + no_of_cnts_heap h.h_formula_conj_h2
(*  | StarList h -> sum_of_int_lst (List.map (fun (_,s) -> no_of_cnts_heap (Star s)) h)*)
  | Phase h -> no_of_cnts_heap h.h_formula_phase_rd + no_of_cnts_heap h.h_formula_phase_rw
  | DataNode _ -> 1
  | ViewNode _ -> 1
  | HRel _ -> 1
  | Hole _ -> 1
  | HTrue -> 1
  | HFalse -> 1
  | HEmp -> 0

let rec no_of_cnts_fml fml = match fml with
  | Or f -> no_of_cnts_fml f.formula_or_f1 + no_of_cnts_fml f.formula_or_f2
  | Base f -> no_of_cnts_heap f.formula_base_heap + CP.no_of_cnts (MCP.pure_of_mix f.formula_base_pure)
  | Exists f -> no_of_cnts_heap f.formula_exists_heap  + CP.no_of_cnts (MCP.pure_of_mix f.formula_exists_pure)

let rec no_of_cnts (sp:struc_formula) = match sp with
  | ECase b -> 
    let nums = List.map (fun (p,c) -> CP.no_of_cnts p + no_of_cnts c) b.formula_case_branches in
    sum_of_int_lst nums
  | EBase b -> no_of_cnts_fml b.formula_struc_base + 
    (match b.formula_struc_continuation with | None -> 0 | Some x -> no_of_cnts x)
  | EAssume(_,f,_) -> no_of_cnts_fml f
  | EInfer b -> no_of_cnts b.formula_inf_continuation
  | EList b -> 
    let nums = List.map (fun (_,e) -> no_of_cnts e) b in
    sum_of_int_lst nums
  | EOr b -> no_of_cnts b.formula_struc_or_f1 + no_of_cnts b.formula_struc_or_f2

let mkViewNode view_node view_name view_args pos = ViewNode
  { h_formula_view_node = view_node;
  h_formula_view_name = view_name;
  h_formula_view_derv = false;
  h_formula_view_arguments = view_args;
  h_formula_view_imm = ConstAnn Mutable;
  h_formula_view_perm = None;
  h_formula_view_modes = [];
  h_formula_view_coercible = true;
  h_formula_view_origins = [];
  h_formula_view_original = true;
  h_formula_view_lhs_case = true;
  h_formula_view_unfold_num = 0;
  h_formula_view_remaining_branches = None;
  h_formula_view_pruning_conditions = [];
  h_formula_view_label = None;
  h_formula_view_pos = pos}

let rec take_tl lst n = 
  if n=0 then lst
  else
    match lst with
    | [] -> report_error no_pos "New predicate do not have enough arguments"
    | l::ls -> take_tl ls (n-1)

let tran_args ex_args args length = 
  let new_args = take_tl args length in
  let new_args = CP.fresh_spec_vars new_args in
  (ex_args @ new_args, new_args)

let rec tran_spec_heap h sub_pair = match h with
  | Star {h_formula_star_h1 = h1;
    h_formula_star_h2 = h2;
    h_formula_star_pos = pos} -> 
    let res1 = tran_spec_heap h1 sub_pair in
    let res2 = tran_spec_heap h2 sub_pair in
    (mkStarH (fst res1) (fst res2) pos, snd res1 @ snd res2)
  | Conj {h_formula_conj_h1 = h1;
    h_formula_conj_h2 = h2;
    h_formula_conj_pos = pos} -> 
    let res1 = tran_spec_heap h1 sub_pair in
    let res2 = tran_spec_heap h2 sub_pair in
    (mkConjH (fst res1) (fst res2) pos, snd res1 @ snd res2)
  | Phase { h_formula_phase_rd = h1;
    h_formula_phase_rw = h2;
    h_formula_phase_pos = pos} -> 
    let res1 = tran_spec_heap h1 sub_pair in
    let res2 = tran_spec_heap h2 sub_pair in
    (mkPhaseH (fst res1) (fst res2) pos, snd res1 @ snd res2)
  | ViewNode v ->
    let ((old_view_name, old_view_vars),(new_view_name, new_view_vars)) = sub_pair in
    if v.h_formula_view_name = old_view_name then
      let new_args = tran_args v.h_formula_view_arguments new_view_vars 
      (List.length old_view_vars) in
      (ViewNode {v with h_formula_view_name = new_view_name;
      h_formula_view_arguments = fst new_args}, snd new_args)
    else (h,[])
  | _ -> (h,[])

let rec tran_spec_fml fml sub_pair is_ebase = match fml with
  | Or {formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = p} ->
    let res1 = tran_spec_fml f1 sub_pair is_ebase in
    let res2 = tran_spec_fml f2 sub_pair is_ebase in
    (mkOr (fst res1) (fst res2) p, snd res1 @ snd res2)
  | Base b ->
    let h, _, _, _, _ = split_components fml in
    let new_h = tran_spec_heap h sub_pair in
    let heap,evars = new_h in
    if evars = [] || is_ebase then
      (Base {b with formula_base_heap = heap}, evars)
    else 
      (mkExists_w_lbl evars heap b.formula_base_pure 
      b.formula_base_type b.formula_base_flow b.formula_base_and b.formula_base_pos b.formula_base_label, evars)
  | Exists e ->
    let h, _, _, _, _ = split_components fml in
    let new_h = tran_spec_heap h sub_pair in
    let heap,evars = new_h in
    if evars = [] || is_ebase then
      (Exists {e with formula_exists_heap = heap}, evars)
    else
      (Exists {e with formula_exists_heap = heap; formula_exists_qvars = e.formula_exists_qvars @ evars}, evars)

let rec tran_spec (sp:struc_formula) sub_pair = match sp with
  | ECase b -> 
    let res = List.map (fun (p,c) -> 
      let r = tran_spec c sub_pair in
      ((p,fst r), snd r)) b.formula_case_branches in
    let r1,r2 = List.split res in
    (ECase {b with formula_case_branches = r1}, List.concat r2)
  | EBase b -> 
    let rbase = tran_spec_fml b.formula_struc_base sub_pair true in
    let rcont = (match b.formula_struc_continuation with
      | None -> (None,[])
      | Some f -> let r = tran_spec f sub_pair in
        (Some (fst r), snd r)) in
    (EBase {b with 
      formula_struc_implicit_inst = b.formula_struc_implicit_inst @ snd rbase;
      formula_struc_base = fst rbase;
      formula_struc_continuation = fst rcont},snd rbase @ snd rcont)
  | EAssume(svl,f,fl) -> let r = tran_spec_fml f sub_pair false in
    (EAssume(svl,fst r,fl),snd r)
  | EInfer b -> let r = tran_spec b.formula_inf_continuation sub_pair in
    (EInfer {b with formula_inf_continuation = fst r},snd r)
  | EList b -> let r = List.map (fun (l,e) ->
      let res = tran_spec e sub_pair in ((l,fst res),snd res)) b in
    let r1,r2 = List.split r in
    (EList r1, List.concat r2)
  | EOr b -> 
    let r1 = tran_spec b.formula_struc_or_f1 sub_pair in
    let r2 = tran_spec b.formula_struc_or_f2 sub_pair in
    (EOr {b with formula_struc_or_f1 = fst r1;
                formula_struc_or_f2 = fst r2}, snd r1 @ snd r2)

let rec add_pure_fml fml rel_fml = match fml with
  | Or {formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = p} ->
    mkOr (add_pure_fml f1 rel_fml) (add_pure_fml f2 rel_fml) p
  | Base b ->
    let _, p, _, _, _ = split_components fml in
    let new_p = CP.mkAnd (MCP.pure_of_mix p) rel_fml no_pos in
    Base {b with formula_base_pure = MCP.mix_of_pure new_p}
  | Exists e ->
    let _, p, _, _, _ = split_components fml in
    let new_p = CP.mkAnd (MCP.pure_of_mix p) rel_fml no_pos in
    Exists {e with formula_exists_pure = MCP.mix_of_pure new_p}

let rec add_pure (sp:struc_formula) rel_fml_pre rel_fml_post = match sp with
  | ECase b -> ECase {b with formula_case_branches = (List.map (fun (p,c) -> 
    (p,add_pure c rel_fml_pre rel_fml_post)) b.formula_case_branches)}
  | EBase b -> EBase {b with 
    formula_struc_base = (match rel_fml_pre with
      | None -> b.formula_struc_base
      | Some fml -> add_pure_fml b.formula_struc_base fml);
    formula_struc_continuation =
    (match b.formula_struc_continuation with
      | None -> None
      | Some f -> Some (add_pure f rel_fml_pre rel_fml_post))}
  | EAssume(svl,f,fl) -> (match rel_fml_post with
      | None -> sp
      | Some fml -> EAssume(svl,add_pure_fml f fml,fl))
  | EInfer b -> EInfer {b with formula_inf_continuation = add_pure b.formula_inf_continuation rel_fml_pre rel_fml_post}
  | EList b -> EList (List.map (fun (l,e) ->(l,add_pure e rel_fml_pre rel_fml_post)) b)
  | EOr b -> EOr {b with formula_struc_or_f1 = add_pure b.formula_struc_or_f1 rel_fml_pre rel_fml_post;
                         formula_struc_or_f2 = add_pure b.formula_struc_or_f2 rel_fml_pre rel_fml_post}



let rec ctx_no_heap c = match c with 
  | Ctx e-> 
    let rec f_no_heap f = match f with
	  | Base f ->  not (is_complex_heap f.formula_base_heap)
	  | Exists f -> not (is_complex_heap f.formula_exists_heap)
	  | Or f -> (f_no_heap f.formula_or_f1) & (f_no_heap f.formula_or_f2) in
    f_no_heap e.es_formula
  | OCtx (c1,c2) -> (ctx_no_heap c1) & (ctx_no_heap c2)
  
  
  
let rec find_barr bln v f = 
  (*this is copied from context, actually it is general enough to be in cpure...*)
	let rec alias (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list = 
	  match ptr_eqs with
	  | (v1, v2) :: rest ->
		  let search v asets = List.partition (fun aset -> CP.mem v aset) asets in
		  let av1, rest1 = search v1 (alias rest) in
		  let av2, rest2 = search v2 rest1 in
		  let v1v2_set = CP.remove_dups_svl (List.concat ([v1; v2] :: (av1 @ av2))) in
		  v1v2_set :: rest2
	  | [] -> [] in
    let tester r1 r2 = if r2=None then r1 else report_error no_pos ("formula not normalized for barrier "^v) in
    let rec p_bar_eq p = try 
	List.map CP.name_of_spec_var
	 (List.find (List.exists (fun c-> (String.compare v (CP.name_of_spec_var c)=0))) (alias (MCP.ptr_equations_without_null p))) with _ -> [v] in
	
	let rec h_bars eqs f = match f with 
	  | Star h -> 
	    let rd = h_bars eqs h.h_formula_star_h1 in
		let rw = h_bars eqs h.h_formula_star_h2 in
	   (match rd with | None -> rw | _ -> tester rd rw)	  
	  | Conj c -> 
	    let rd = h_bars eqs c.h_formula_conj_h1 in
		let rw = h_bars eqs c.h_formula_conj_h2 in
	   (match rd with | None -> rw | _ -> tester rd rw)	  
	  | Phase p -> 
		let rd = h_bars eqs p.h_formula_phase_rd in
		let rw = h_bars eqs p.h_formula_phase_rw in
	   (match rd with | None -> rw | _ -> tester rd rw)
	  | DataNode d -> 
		  let str_eq v1 v2 = (String.compare v1 v2 ) = 0 in
		  let f1 = str_eq d.h_formula_data_name in
		  let f2 = str_eq (CP.name_of_spec_var d.h_formula_data_node) in
		  if (List.exists f1 bln)&&(List.exists f2 eqs) then 
			Some d (*(d.h_formula_data_name,d.h_formula_data_node::d.h_formula_data_arguments,d.h_formula_data_remaining_branches)*)
 		  else None
	  | ViewNode _ | Hole _ | HTrue | HEmp | HFalse | HRel _-> None in
    
    match f with
	  | Base f ->  h_bars (p_bar_eq f.formula_base_pure) f.formula_base_heap
	  | Exists f -> h_bars (p_bar_eq f.formula_exists_pure) f.formula_exists_heap
	  | Or f -> report_error no_pos "unexpected or in find barr" 

let find_barr bln v f = 
	Debug.no_2 "find_barr" (fun c->c) !print_formula (fun c-> "") (find_barr bln) v f
	

let get_bar_conds b_name self (l_f:(formula * formula_label) list): ((int option * Tree_shares.Ts.t_sh option * formula_label) list) =
	let helper (f,lbl) = match find_barr b_name self f with 
		| None  -> (None,None,lbl)
		| Some bd -> match f with
			| Or _ -> report_error no_pos "unexpected or in find barr" 
			| Base {formula_base_pure = p}
			| Exists {formula_exists_pure = p} ->
					let f = MCP.fold_mem_lst (CP.mkTrue no_pos) false false p in
					let perm = match bd.h_formula_data_perm with
						| None -> Some Tree_shares.Ts.top
						| Some v -> CP.get_inst_tree v f in
					(CP.get_inst_int (List.hd bd.h_formula_data_arguments) f, perm, lbl) in	
	List.map helper l_f
	
let get_bar_conds b_name self l_f =
	let string_of_lbl = (fun (c,_)-> string_of_int c) in
	Debug.no_3 "get_bar_conds" (pr_list (fun c->c)) (fun c-> c) 
		(pr_list (pr_pair !print_formula string_of_lbl)) 
		(pr_list (pr_triple (pr_opt string_of_int) (pr_opt Tree_shares.Ts.string_of) string_of_lbl))
	get_bar_conds b_name self l_f
	
	                      
let rec is_error_flow f =  match f with
  | Base b-> subsume_flow_f !error_flow_int b.formula_base_flow
  | Exists b-> subsume_flow_f !error_flow_int b.formula_exists_flow
  | Or b ->  is_error_flow b.formula_or_f1 && is_error_flow b.formula_or_f2 

let rec is_top_flow f =   match f with
  | Base b-> equal_flow_interval !top_flow_int b.formula_base_flow.formula_flow_interval
  | Exists b-> equal_flow_interval !top_flow_int b.formula_exists_flow.formula_flow_interval
  | Or b ->  is_top_flow b.formula_or_f1 && is_top_flow b.formula_or_f2 

let get_error_flow f = flow_formula_of_formula f
let get_top_flow f = flow_formula_of_formula f
