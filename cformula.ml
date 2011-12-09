(*
  Created 21-Feb-2006

  Formula
*)

open Globals
open Gen
open Exc.GTable
open Perm

module Err = Error
module CP = Cpure
module MCP = Mcpure

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

and t_formula_sub_type = { t_formula_sub_type_var : Cpure.spec_var;
t_formula_sub_type_type : ident }

and t_formula_and = { t_formula_and_f1 : t_formula;
t_formula_and_f2 : t_formula }


and struc_formula = ext_formula list

and ext_formula = 
  | ECase of ext_case_formula
  | EBase of ext_base_formula
  | EAssume of ((Cpure.spec_var list) *formula* formula_label)
  | EVariance of ext_variance_formula
  (*  struct_formula *)
(*
  | EScope of  (Cpure.spec_var list) 
*)


and ext_case_formula =
	{
		formula_case_branches : (Cpure.formula * struc_formula ) list;
		formula_case_exists : Cpure.spec_var list; (*should be absolete, to be removed *)
		formula_case_pos : loc 		
	}

and ext_base_formula =
	{
		formula_ext_explicit_inst : Cpure.spec_var list;
		formula_ext_implicit_inst : Cpure.spec_var list;
        (* 
           vars_free, vars_linking, vars_extracted 
        *)
		formula_ext_exists : Cpure.spec_var list;
		formula_ext_base : formula;
		formula_ext_continuation : struc_formula;
		formula_ext_pos : loc
	}

and ext_variance_formula =
	{
		formula_var_label : int option;
		formula_var_measures : (Cpure.exp * (Cpure.exp option)) list; (* variance expression and bound *)
		formula_var_escape_clauses : Cpure.formula list;
	  formula_var_continuation : struc_formula;
		formula_var_pos : loc
	}

and formula =
  | Base of formula_base
  | Or of formula_or
  | Exists of formula_exists

and list_formula = formula list

and formula_base = {  formula_base_heap : h_formula;
                      formula_base_pure : MCP.mix_formula;
                      formula_base_type : t_formula; (* a collection ot subtype information *)
		      (* formula_base_imm : bool; *)
                      formula_base_flow : flow_formula;
                      formula_base_branches : (branch_label * CP.formula) list;
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
			(* formula_exists_imm : bool; *)
                        formula_exists_flow : flow_formula;
                        formula_exists_branches : (branch_label * CP.formula) list;
                        formula_exists_label : formula_label option;
                        formula_exists_pos : loc }

and flow_formula = {  formula_flow_interval : nflow; 
                      formula_flow_link : (ident option)}
and flow_store = {
	formula_store_name : ident;
	formula_store_value : flow_formula;		
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
  (* | Mem of [[Var]] *)
  | Hole of int    
  | HTrue
  | HFalse
          
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
                        h_formula_data_imm : bool;
                        h_formula_data_perm : cperm; (* option; *) (*LDK: permission*)
                        (*added to support fractional splitting of data nodes*)
                        h_formula_data_origins : ident list;
                        h_formula_data_original : bool;
                        h_formula_data_arguments : CP.spec_var list;
						h_formula_data_holes : int list; (* An Hoa : list of fields not to be considered for partial structures *)
                        h_formula_data_label : formula_label option;
                        h_formula_data_remaining_branches :  (formula_label list) option;
                        h_formula_data_pruning_conditions :  (CP.b_formula * formula_label list ) list;
                        h_formula_data_pos : loc }

and h_formula_view = {  h_formula_view_node : CP.spec_var;
                        h_formula_view_name : ident;
                        h_formula_view_derv : bool;
                        h_formula_view_imm : bool;
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

(* utility functions *)

let empty_ext_variance_formula =
	{
		formula_var_label = None;
		formula_var_measures = [];
		formula_var_escape_clauses = [];
	  formula_var_continuation = [];
		formula_var_pos = no_pos;
	}

let rec has_variance_struc struc_f =
  List.exists (fun ef -> has_variance_ext ef) struc_f
  
and has_variance_ext ext_f = 
  match ext_f with
    | ECase { formula_case_branches = cl } ->
        List.exists (fun (_, sf) -> has_variance_struc sf) cl
    | EBase { formula_ext_continuation = cont } ->
        has_variance_struc cont
    | EAssume _ -> false
    | EVariance _ -> true

(* generalized to data and view *)
let get_ptr_from_data h =
  match h with
    | DataNode f -> f.h_formula_data_node
    | ViewNode f -> f.h_formula_view_node
    | _ -> report_error no_pos "get_ptr_from_data : data expected" 

let print_formula = ref(fun (c:formula) -> "printer not initialized")
let print_formula_base = ref(fun (c:formula_base) -> "printer not initialized")
let print_h_formula = ref(fun (c:h_formula) -> "printer not initialized")
let print_mix_f = ref(fun (c:MCP.mix_formula) -> "printer not initialized")
let print_mix_formula = print_mix_f
let print_ident_list = ref(fun (c:ident list) -> "printer not initialized")
let print_svl = ref(fun (c:CP.spec_var list) -> "printer not initialized")
let print_sv = ref(fun (c:CP.spec_var) -> "printer not initialized")
let print_struc_formula = ref(fun (c:struc_formula) -> "printer not initialized")
let print_ext_formula = ref(fun (c:ext_formula) -> "printer not initialized")
let print_flow_formula = ref(fun (c:flow_formula) -> "printer not initialized")
let print_spec_var = print_sv
let print_spec_var_list = print_svl
let print_flow = ref(fun (c:nflow) -> "printer not initialized")

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


let check_nonempty_spec (f:struc_formula) : bool = 
  if f==[] then false
  else true

let extr_formula_base e = match e with
      {formula_base_heap = h;
      formula_base_pure = p; 
      formula_base_type = t;
      formula_base_flow = fl;
      formula_base_branches = br;} -> (h,p,t,fl,br) 

let is_eq_node_name a b = (a=b)

let is_eq_data_name a b =
  match a,b with
    | {h_formula_data_name = c1;}, {h_formula_data_name = c2;}-> c1=c2

let is_eq_view_name a b =
  match a,b with
    | {h_formula_view_name = c1;}, {h_formula_view_name = c2;}-> c1=c2

let is_eq_view_name a b =
  Gen.Debug.no_2 "is_eq_view_name" (fun x->x) (fun x->x) string_of_bool (fun _ _ ->  is_eq_view_name a b) 
      a.h_formula_view_name b.h_formula_view_name

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
  Gen.Debug.no_2 "is_eq_view_spec" (fun x->x) (fun x->x) string_of_bool (fun _ _ ->  is_eq_view_spec a b) 
      a.h_formula_view_name b.h_formula_view_name

(* returns false if unsatisfiable *)
let is_sat_mem_formula (mf:mem_formula) : bool =
  let d = mf.mem_formula_mset in
  (CP.DisjSetSV.is_sat_dset d)

let rec formula_of_heap h pos = mkBase h (MCP.mkMTrue pos) TypeTrue (mkTrueFlow ()) [] pos
and formula_of_heap_fl h fl pos = mkBase h (MCP.mkMTrue pos) TypeTrue fl [] pos

and struc_formula_of_heap h pos = [EBase { 
	formula_ext_explicit_inst = [];	 
	formula_ext_implicit_inst = []; 
	formula_ext_exists = [];
	formula_ext_base = formula_of_heap h pos;
	formula_ext_continuation = [];
	formula_ext_pos = pos}]
  
and struc_formula_of_formula f pos = [EBase { 
	formula_ext_explicit_inst = [];	 
    formula_ext_implicit_inst = []; 
    formula_ext_exists = [];
	formula_ext_base = f;
	formula_ext_continuation = [];
	formula_ext_pos = pos}]
  
  
and mkTrueFlow () = 
  {formula_flow_interval = !top_flow_int; formula_flow_link = None;}
	  

and mkFalseFlow = {formula_flow_interval = false_flow_int; formula_flow_link = None;}

and mkNormalFlow () = { formula_flow_interval = !norm_flow_int; formula_flow_link = None;}

and mkErrorFlow () = { formula_flow_interval = !error_flow_int; formula_flow_link = None;}

and formula_of_mix_formula (p:MCP.mix_formula) (pos:loc) :formula= mkBase HTrue p TypeTrue (mkTrueFlow ()) [] pos

and formula_of_pure_formula (p:CP.formula) (pos:loc) :formula= 
  let mix_f = MCP.OnePF p in
  formula_of_mix_formula mix_f pos 

and formula_of_pure_aux (p:CP.formula) (status:int) (pos:loc) :formula=
  let mp = if (status >0 ) then MCP.memoise_add_pure_N (MCP.mkMTrue pos) p 
  else  MCP.memoise_add_pure_P (MCP.mkMTrue pos) p  in
  mkBase HTrue mp TypeTrue (mkTrueFlow ()) [] pos

and formula_of_pure_P (p:CP.formula) (pos:loc) :formula= formula_of_pure_aux p (-1) pos
  
and formula_of_pure_N (p:CP.formula) (pos:loc) :formula= formula_of_pure_aux p 1 pos
  
and formula_of_pure_with_branches_aux p br status pos = 
  let mp = if status>0 then MCP.memoise_add_pure_N (MCP.mkMTrue pos) p
  else MCP.memoise_add_pure_P (MCP.mkMTrue pos) p in
  mkBase HTrue mp TypeTrue (mkTrueFlow ()) br pos

and formula_of_pure_with_branches_N p br pos = formula_of_pure_with_branches_aux p br 1 pos

and formula_of_pure_with_branches_P p br pos = formula_of_pure_with_branches_aux p br (-1) pos

and formula_of_mix_formula_with_branches p br pos = mkBase HTrue p TypeTrue (mkTrueFlow ()) br pos

and formula_of_pure_with_branches_fl_aux p br fl status pos = 
  let mp = if status>0 then MCP.memoise_add_pure_N (MCP.mkMTrue pos) p 
  else MCP.memoise_add_pure_P (MCP.mkMTrue pos) p in
  mkBase HTrue mp TypeTrue fl br pos

and formula_of_pure_with_branches_fl_N p br fl pos = formula_of_pure_with_branches_fl_aux p br fl 1 pos

and formula_of_pure_with_branches_fl_P p br fl pos = formula_of_pure_with_branches_fl_aux p br fl (-1) pos
  
and formula_of_mix_formula_with_branches_fl (p:MCP.mix_formula) br fl pos = mkBase HTrue p TypeTrue fl br pos
and formula_of_base base = Base(base)

and data_of_h_formula h = match h with
  | DataNode d -> d
  | _ -> failwith ("data_of_h_formula: input is not a data node")

and isAnyConstFalse f = match f with
  | Exists ({formula_exists_heap = h;
    formula_exists_pure = p;
    formula_exists_branches = br; 
    formula_exists_flow = fl;})
  | Base ({formula_base_heap = h;
    formula_base_pure = p;
    formula_base_branches = br; 
    formula_base_flow = fl;}) ->
        (h = HFalse || MCP.isConstMFalse p || (List.filter (fun (_,f) -> CP.isConstFalse f) br <> []))||
			(is_false_flow fl.formula_flow_interval)
  | _ -> false


and isAllConstFalse f = match f with
  | Exists ({formula_exists_heap = h;
    formula_exists_pure = p;
    formula_exists_branches = br; 
    formula_exists_flow = fl;})
  | Base ({formula_base_heap = h;
    formula_base_pure = p;
    formula_base_branches = br; 
    formula_base_flow = fl;}) ->
        (h = HFalse || MCP.isConstMFalse p || (List.filter (fun (_,f) -> CP.isConstFalse f) br <> []))||
			(is_false_flow fl.formula_flow_interval)
  | _ -> false

and isConstDFalse f = 
  match f with
	| EBase b -> (isAnyConstFalse b.formula_ext_base)  
	| _ -> false

and isConstDTrue f = 
  match f with
	| EBase b -> (isStrictConstTrue b.formula_ext_base) &&(List.length b.formula_ext_continuation)==0
	| _ -> false

and isConstETrue f = 
  List.exists isConstDTrue f
          
and isConstEFalse f = 
  List.for_all isConstDFalse f

(* and isConstETrue f =  *)
(*   if (List.length f)<>1 then false *)
(*   else match (List.hd f) with *)
(* 	| EBase b -> (isStrictConstTrue b.formula_ext_base) &&(List.length b.formula_ext_continuation)==0 *)
(* 	| _ -> false *)
          
(* and isConstEFalse f =  *)
(*   if (List.length f)<>1 then false *)
(*   else match (List.hd f) with *)
(* 	| EBase b -> (isAnyConstFalse b.formula_ext_base)   *)
(* 	| _ -> false *)

and isConstETrueSpecs f = 
  if (List.length f)<>1 then false
  else match (List.hd f) with
	| EBase b -> (isStrictConstTrue b.formula_ext_base) && (((List.length b.formula_ext_continuation)==1 && 
          (match (List.hd b.formula_ext_continuation) with
            | EAssume (_,f,_)-> isStrictConstTrue f
            | _-> false)) || ((List.length b.formula_ext_continuation)==0))
	| _ -> false

          
and isStrictConstTrue_x f = match f with
  | Exists ({ formula_exists_heap = HTrue;
    formula_exists_pure = p;
    formula_exists_branches = br; 
    formula_exists_flow = fl; })
  | Base ({formula_base_heap = HTrue;
    formula_base_pure = p;
    formula_base_branches = br;
    formula_base_flow = fl;}) -> 
        MCP.isConstMTrue p && (List.filter (fun (_,f) -> not (CP.isConstTrue f)) br = [])&&(is_top_flow fl.formula_flow_interval)
	        (* don't need to care about formula_base_type  *)
  | _ -> false

and isStrictConstTrue (f:formula) = 
  Gen.Debug.no_1 "isStrictConstTrue" !print_formula string_of_bool isStrictConstTrue_x f

and isAnyConstTrue f = match f with
  | Exists ({formula_exists_heap = HTrue;
    formula_exists_pure = p;
    formula_exists_branches = br; 
	formula_exists_flow = fl; })
  | Base ({formula_base_heap = HTrue;
	formula_base_pure = p;
    formula_base_branches = br;
	formula_base_flow = fl;}) -> 
        MCP.isConstMTrue p && (List.filter (fun (_,f) -> not (CP.isConstTrue f)) br = [])
	        (* don't need to care about formula_base_type  *)
  | _ -> false

and is_complex_heap (h : h_formula) : bool = match h with
  | HTrue | HFalse -> false
  | _ -> true

and is_coercible_x (h : h_formula) : bool = match h with
  | ViewNode ({h_formula_view_coercible = c}) -> c
  | DataNode _ -> true (*LDK: assume that all data nodes are coercible*)
  | _ -> false

and is_coercible (h : h_formula) : bool =
  Gen.Debug.no_1 "is_coercible" !print_h_formula string_of_bool is_coercible_x h 


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



and get_imm (f : h_formula) : bool =  match f with
  | DataNode (h1) -> h1.h_formula_data_imm
  | ViewNode (h1) -> h1.h_formula_view_imm
  | _ -> false (* we shouldn't get here *)

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
(*   Gen.Debug.no_2 "subsume_flow" pr1 pr1 string_of_bool subsume_flow_x n p  *)

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
(*   Gen.Debug.no_2_num i "subsume_flow_ff" pr pr string_of_bool subsume_flow_ff_x f1 f2 *)

and overlap_flow_ff f1 f2 :bool = overlap_flow f1.formula_flow_interval f2.formula_flow_interval

(* and overlap_flow_ff f1 f2 :bool =  *)
(*   let pr = !print_flow_formula in *)
(*   Gen.Debug.no_2 "subsume_flow_ff" pr pr string_of_bool overlap_flow_ff_x f1 f2 *)

and get_flow_from_stack c l pos = 
  try
	let r = List.find (fun h-> ((String.compare h.formula_store_name c)==0)) l in
	r.formula_store_value
  with Not_found -> Err.report_error { 
	  Err.error_loc = pos;
	  Err.error_text = "the flow var stack \n"^
		  (String.concat " " (List.map (fun h-> (h.formula_store_name^"= "^
			  (string_of_flow (h.formula_store_value.formula_flow_interval) ^" "))) l))^
		  "\ndoes not contain "^c
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

and struc_formula_is_eq_flow (f:struc_formula) ff : bool =
  let rec helper (f:ext_formula) = match f with
	| EBase b ->
        (formula_is_eq_flow b.formula_ext_base ff) && (struc_formula_is_eq_flow b.formula_ext_continuation ff)
	| ECase b -> List.for_all (fun (_,c) -> struc_formula_is_eq_flow c ff) b.formula_case_branches 
	| EAssume (x,b,y) -> formula_is_eq_flow b ff
	| EVariance b -> struc_formula_is_eq_flow b.formula_var_continuation ff 
  in List.for_all helper f

and formula_subst_flow (f:formula) ff : formula =
  match f with
  | Base b-> Base {b with formula_base_flow = ff} 
  | Exists b-> Exists{b with formula_exists_flow = ff}
  | Or b -> Or {b with formula_or_f1 = formula_subst_flow b.formula_or_f1 ff;
	formula_or_f2 = formula_subst_flow b.formula_or_f2 ff}

and struc_formula_subst_flow (f:struc_formula) ff : struc_formula =
  let helper (f:ext_formula) = match f with
	| EBase b -> EBase {b with formula_ext_base = formula_subst_flow b.formula_ext_base ff ; 
		  formula_ext_continuation = struc_formula_subst_flow b.formula_ext_continuation ff}
	| ECase b -> ECase {b with formula_case_branches = 
              List.map (fun (c1,c2) -> (c1,(struc_formula_subst_flow c2 ff))) b.formula_case_branches;}
	| EAssume (x,b,y) -> EAssume (x,(formula_subst_flow b ff),y)
	| EVariance b -> EVariance {b with formula_var_continuation = struc_formula_subst_flow  b.formula_var_continuation ff}
  in
  List.map helper f	

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
  let rec helper (f:ext_formula) = match f with
	| EBase b ->
        flow_formula_of_formula b.formula_ext_base
        (*let fl1 = flow_formula_of_formula b.formula_ext_base in*)
        (*let fl2 = flow_formula_of_struc_formula b.formula_ext_continuation in
        compare_flow fl1 fl2 *)
	| ECase b ->
        let ls = List.map (fun (_,c2) -> (flow_formula_of_struc_formula c2)) b.formula_case_branches in
        fold_left_compare_flows ls
	| EAssume (x,b,y) -> flow_formula_of_formula b
	| EVariance b -> flow_formula_of_struc_formula b.formula_var_continuation
  in
  let flow_list = List.map helper f in
  fold_left_compare_flows flow_list

and substitute_flow_in_f to_flow from_flow (f:formula):formula = 
  Gen.Debug.no_3 "substitute_flow_in_f" string_of_flow string_of_flow !print_formula !print_formula (fun _ _ _ -> substitute_flow_in_f_x to_flow from_flow f) to_flow from_flow f

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
		
and substitute_flow_in_struc_f to_flow from_flow (f:struc_formula):struc_formula = 
  let helper (f:ext_formula) = match f with
	| EBase b -> EBase {b with formula_ext_base = substitute_flow_in_f to_flow from_flow b.formula_ext_base ; 
		  formula_ext_continuation = substitute_flow_in_struc_f to_flow from_flow  b.formula_ext_continuation}
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2) -> (c1,(substitute_flow_in_struc_f to_flow from_flow  c2))) b.formula_case_branches;}
	| EAssume (x,b,y) -> EAssume (x,(substitute_flow_in_f to_flow from_flow  b),y)
	| EVariance b -> EVariance {b with formula_var_continuation = substitute_flow_in_struc_f to_flow from_flow  b.formula_var_continuation}
  in
  List.map helper f	

and mkAndFlow (fl1:flow_formula) (fl2:flow_formula) flow_tr :flow_formula = 
  let pr = !print_flow_formula in
  let pr2 x = match x with Flow_combine -> "Combine" | Flow_replace -> "Replace" in
  Gen.Debug.no_3 "mkAndFlow" pr pr pr2 pr (fun _ _ _ -> mkAndFlow_x fl1 fl2 flow_tr) fl1 fl2 flow_tr

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
  (* let string_of_flow_formula f c =  *)
  (*   "{"^f^",("^(string_of_int (fst c.formula_flow_interval))^","^(string_of_int (snd c.formula_flow_interval))^ *)
  (*   ")="^(Gen.ExcNumbering.get_closest c.formula_flow_interval)^","^(match c.formula_flow_link with | None -> "" | Some e -> e)^"}" in *)

  (*   let _ = print_string ("\n"^(string_of_flow_formula "f1 " fl1)^"\n"^ *)
  (*   (string_of_flow_formula "f2 " fl2)^"\n"^ *)
  (*   (string_of_flow_formula "r " r)^"\n") in *)
  r

and get_case_guard_list lbl (lst:(Cpure.b_formula * formula_label list) list) :  CP.b_formula list= 
  List.fold_left (fun a (cond,lbl_lst) -> if (List.mem lbl lbl_lst) then cond::a else a) [] lst
      
and mkTrue (flowt: flow_formula) pos = Base ({formula_base_heap = HTrue; 
formula_base_pure = MCP.mkMTrue pos; 
formula_base_type = TypeTrue; 
(* formula_base_imm = false; *)
formula_base_flow = flowt (*(mkTrueFlow ())*);
formula_base_branches = [];
formula_base_label = None;
formula_base_pos = pos})

and mkTrue_nf pos = mkTrue (mkTrueFlow ()) pos

and mkFalse (flowt: flow_formula) pos = Base ({formula_base_heap = HFalse; 
formula_base_pure = MCP.mkMFalse pos; 
formula_base_type = TypeFalse;
(* formula_base_imm = false; *)
formula_base_flow = flowt (*mkFalseFlow*); (*Cpure.flow_eqs any_flow pos;*)
formula_base_branches = [];
formula_base_label = None;
formula_base_pos = pos})
  
and mkEFalse flowt pos = EBase({
	formula_ext_explicit_inst = [];
	formula_ext_implicit_inst = [];
	formula_ext_exists = [];
	formula_ext_base = mkFalse flowt pos;
	formula_ext_continuation = [];
	formula_ext_pos = pos})

and mkETrue flowt pos = EBase({
	formula_ext_explicit_inst = [];
	formula_ext_implicit_inst = [];
	formula_ext_exists = [];
	formula_ext_base = mkTrue flowt pos;
	formula_ext_continuation = [];
	formula_ext_pos = pos})
  
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
        
and mkBase_w_lbl (h : h_formula) (p : MCP.mix_formula) (t : t_formula) (fl : flow_formula) b (pos : loc) lbl: formula= 
  if MCP.isConstMFalse p || h = HFalse || (is_false_flow fl.formula_flow_interval)  then 
	mkFalse fl pos
  else 
	Base ({formula_base_heap = h; 
	formula_base_pure = p; 
	formula_base_type = t;
	(* formula_base_imm = contains_immutable_h_formula h; *)
	formula_base_flow = fl;
    formula_base_branches = b;
    formula_base_label = lbl;
	formula_base_pos = pos})
and mkBase (h : h_formula) (p : MCP.mix_formula) (t : t_formula) (fl : flow_formula) b (pos : loc) : formula= 
  mkBase_w_lbl h p t fl b pos None
      

and mkStarH (f1 : h_formula) (f2 : h_formula) (pos : loc) = match f1 with
  | HFalse -> HFalse
  | HTrue -> f2
  | _ -> match f2 with
      | HFalse -> HFalse
      | HTrue -> f1
      | _ -> Star ({h_formula_star_h1 = f1; 
		h_formula_star_h2 = f2; 
		h_formula_star_pos = pos})

and mkConjH (f1 : h_formula) (f2 : h_formula) (pos : loc) = match f1 with
  | HFalse -> HFalse
  | HTrue -> f2
  | _ -> match f2 with
      | HFalse -> HFalse
      | HTrue -> f1
      | _ -> Conj ({h_formula_conj_h1 = f1; 
		h_formula_conj_h2 = f2; 
		h_formula_conj_pos = pos})

and mkPhaseH (f1 : h_formula) (f2 : h_formula) (pos : loc) = 
  match f1 with
    | HFalse -> HFalse
    | HTrue -> f2
    | _ -> match f2 with
        | HFalse -> HFalse
        | HTrue -> f1
        | _ -> Phase ({h_formula_phase_rd = f1; 
		  h_formula_phase_rw = f2; 
		  h_formula_phase_pos = pos})

and is_simple_formula (f:formula) =
  let h, _, _, _, _ = split_components f in
  match h with
    | HTrue | HFalse 
    | DataNode _ -> true
    | ViewNode _ -> true
    | _ -> false
    
and fv_simple_formula (f:formula) = 
  let h, _, _, _, _ = split_components f in
  match h with
    | HTrue | HFalse -> []
    | DataNode h -> 
        let perm = h.h_formula_data_perm in
        let perm_vars = fv_cperm perm in
        perm_vars@(h.h_formula_data_node::h.h_formula_data_arguments)
    | ViewNode h -> 
        let perm = h.h_formula_view_perm in
        let perm_vars = fv_cperm perm in
        perm_vars@(h.h_formula_view_node::h.h_formula_view_arguments)
    | _ -> []

(*LDK: don't count perm var as free vars in a coercion*)
and fv_simple_formula_coerc (f:formula) = 
  let h, _, _, _, _ = split_components f in
  match h with
    | HTrue | HFalse -> []
    | DataNode h ->  h.h_formula_data_node::h.h_formula_data_arguments
    | ViewNode h ->  h.h_formula_view_node::h.h_formula_view_arguments
    | _ -> []
and mkStar (f1 : formula) (f2 : formula) flow_tr (pos : loc) =
  let h1, p1, fl1, b1, t1 = split_components f1 in
  let h2, p2, fl2, b2, t2 = split_components f2 in
  let h = mkStarH h1 h2 pos in
  let p = MCP.merge_mems p1 p2 true in
  let t = mkAndType t1 t2 in
  let b = CP.merge_branches b1 b2 in
  let fl = mkAndFlow fl1 fl2 flow_tr in
  mkBase h p t fl b pos
      
and combine_and_pure (f1:formula)(p:MCP.mix_formula)(f2:MCP.mix_formula):MCP.mix_formula*bool = 
  if (isAnyConstFalse f1) then (MCP.mkMFalse no_pos,false)
  else if (isAnyConstTrue f1) then (f2,true)
  else 
    let r = Gen.Profiling.no_1 "6_combine_mm" (MCP.merge_mems p f2) true in
    if (MCP.isConstMFalse r) then (r,false)
    else if (MCP.isConstMTrue r) then (r,false)
    else (r,true)      
      (*(sem_and p f2)
        and sem_and (p:mix_formula)(f2:mix_formula):(mix_formula*bool) = 
	    let ys  = Cpure.split_conjunctions f2 in
	    let ys' = List.filter (fun c-> not (Cpure.is_member_pure c p)) ys in
	    let y   = Cpure.join_conjunctions ys' in
	    if (Cpure.isConstFalse y) then (mkMFalse no_pos,false)
		else if (Cpure.isConstTrue y) then (p,false)
		else  ((merge_mems p y),true)*)

and sintactic_search (f:formula)(p:Cpure.formula):bool = match f with
  | Or b-> false		
  | Base _					
  | Exists _-> 
		let _, pl, _, br, _ = split_components f in	
		(MCP.memo_is_member_pure p pl)||(List.exists (fun (_,c)->Cpure.is_member_pure p c) br)

(* and print_formula = ref(fun (c:formula) -> "Cprinter not initialized") *)

and mkStar_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
  Gen.Debug.no_2 "mkstar_combine"
      (!print_formula)
      (!print_formula)
      (!print_formula)
      (fun f1 f2 -> mkStar_combine_x f1 f2 flow_tr pos) f1 f2 
	  
and mkStar_combine_x (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
  let h1, p1, fl1, b1, t1 = split_components f1 in
  let h2, p2, fl2, b2, t2 = split_components f2 in

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
  let b = CP.merge_branches b1 b2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  mkBase h p t fl b pos
	  
and mkConj_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
  let h1, p1, fl1, b1, t1 = split_components f1 in
  let h2, p2, fl2, b2, t2 = split_components f2 in
  let h = mkConjH h1 h2 pos in
  let p,_ = combine_and_pure f1 p1 p2 in
  let t = mkAndType t1 t2 in
  let b = CP.merge_branches b1 b2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  mkBase h p t fl b pos
	  
and mkPhase_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
  let h1, p1, fl1, b1, t1 = split_components f1 in
  let h2, p2, fl2, b2, t2 = split_components f2 in
  let h = mkPhaseH h1 h2 pos in
  let p,_ = combine_and_pure f1 p1 p2 in
  let t = mkAndType t1 t2 in
  let b = CP.merge_branches b1 b2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  mkBase h p t fl b pos

and mkAnd_pure_and_branch (f1 : formula) (p2 : MCP.mix_formula) b2 (pos : loc):formula = 
  if (isAnyConstFalse f1) then f1
  else 
	let h1, p1, fl1, b1, t1 = split_components f1 in		
    if (MCP.isConstMTrue p1) then mkBase h1 p2 t1 fl1 (CP.merge_branches b1 b2) pos
	else 
      mkBase h1 (MCP.merge_mems p1 p2 true) t1 fl1 (CP.merge_branches b1 b2) pos

          
and mkExists_w_lbl (svs : CP.spec_var list) (h : h_formula) (p : MCP.mix_formula) (t : t_formula) (fl:flow_formula) b (pos : loc) lbl=
  let tmp_b = {formula_base_heap = h;
  formula_base_pure = p;
  formula_base_type = t;
  (* formula_base_imm = contains_immutable_h_formula h; *)
  formula_base_flow = fl;
  formula_base_branches = b;
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
	(* formula_exists_imm = contains_immutable_h_formula h; *)
	formula_exists_flow = fl;
    formula_exists_branches = b;
    formula_exists_label = lbl;
	formula_exists_pos = pos})
and is_true (h : h_formula) = match h with
  | HTrue -> true
  | _ -> false

and mkExists (svs : CP.spec_var list) (h : h_formula) (p : MCP.mix_formula) (t : t_formula) (fl:flow_formula) b (pos : loc) = 
  mkExists_w_lbl svs h p t fl b pos None

and is_view (h : h_formula) = match h with
  | ViewNode _ -> true
  | _ -> false

and is_data (h : h_formula) = match h with
  | DataNode _ -> true
  | _ -> false

and get_node_name (h : h_formula) = match h with
  | ViewNode ({h_formula_view_name = c}) 
  | DataNode ({h_formula_data_name = c}) -> c
  | _ -> failwith ("get_node_name: invalid argument")

and get_node_perm (h : h_formula) = match h with
  | ViewNode ({h_formula_view_perm = c}) 
  | DataNode ({h_formula_data_perm = c}) -> c
  | _ -> failwith ("get_node_perm: invalid argument")

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
  Gen.Debug.no_1 "get_view_modes" !print_h_formula pr (fun _ -> get_view_modes_x h) h
  
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
  Gen.Debug.no_2 "h_add_origins" pr pr2 pr h_add_origins_a h origs

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
  Gen.Debug.no_2 "h_add_perm" pr pr2 pr h_add_perm_a h permvar

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
  Gen.Debug.no_2 "add_origins" pr pr2 pr add_origins_a f origs

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

and reset_struc_origins (f : struc_formula) = 
  let rec helper (f: struc_formula) =
	let ext_f (f:ext_formula) = match f with
	  | ECase b -> ECase {b with 
            formula_case_branches = List.map (fun (c1,c2) -> (c1,(helper c2))) b.formula_case_branches;}
	  | EBase b -> EBase {b with formula_ext_base = reset_origins b.formula_ext_base ; 
			formula_ext_continuation = helper b.formula_ext_continuation}
	  | EAssume (x,b,y) ->  EAssume (x,(reset_origins b),y)
	  | EVariance b -> EVariance {b with formula_var_continuation = helper b.formula_var_continuation}
	in
	List.map ext_f f in	
  helper f

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

and add_struc_original (f : struc_formula) original = 
  let rec helper (f: struc_formula) =
	let ext_f (f:ext_formula) = match f with
	  | ECase b -> ECase {b with 
            formula_case_branches = List.map (fun (c1,c2) -> (c1,(helper c2))) b.formula_case_branches;}
	  | EBase b -> EBase {b with formula_ext_base = add_original b.formula_ext_base original ; 
			formula_ext_continuation = helper b.formula_ext_continuation}
	  | EAssume (x,b,y) ->  EAssume (x,(add_original b original),y)
	  | EVariance b -> EVariance {b with formula_var_continuation = helper b.formula_var_continuation}
	in
	List.map ext_f f in	
  helper f

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

and struc_formula_set_lhs_case (f:struc_formula) (flag:bool) : struc_formula =
  let helper (f:ext_formula) = match f with
	| EBase b -> EBase {b with formula_ext_base = set_lhs_case b.formula_ext_base flag ; 
		  formula_ext_continuation = struc_formula_set_lhs_case b.formula_ext_continuation flag}
	| ECase b -> ECase {b with formula_case_branches = 
              List.map (fun (c1,c2) -> (c1 ,(struc_formula_set_lhs_case c2 flag))) b.formula_case_branches;}
	| EAssume (x,b,y) -> EAssume (x,(set_lhs_case b flag),y)
	| EVariance b -> 
        EVariance {b with 
            formula_var_continuation = struc_formula_set_lhs_case  b.formula_var_continuation flag}
  in
  List.map helper f	

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

and add_struc_origins (f:struc_formula) origs = 
  let rec helper (f: struc_formula) =
	let ext_f (f:ext_formula) = match f with
	  | ECase b -> ECase {b with 
            formula_case_branches = List.map (fun (c1,c2) -> (c1,(helper c2))) b.formula_case_branches;}
	  | EBase b -> EBase {b with formula_ext_base = add_origins b.formula_ext_base origs ; 
			formula_ext_continuation = helper b.formula_ext_continuation}
	  | EAssume (x,b,y) ->  EAssume (x,(add_origins b origs),y)
	  | EVariance b -> EVariance {b with formula_var_continuation = helper b.formula_var_continuation}
	in
	List.map ext_f f in	
  helper f

and no_change (svars : CP.spec_var list) (pos : loc) : CP.formula = match svars with
  | sv :: rest ->
	    let f = CP.mkEqVar (CP.to_primed sv) (CP.to_unprimed sv) pos in
	    let restf = no_change rest pos in
		CP.mkAnd f restf pos
  | [] -> CP.mkTrue pos
 
and pos_of_struc_formula (f:struc_formula): loc =
  if (List.length f)==0 then no_pos
  else match (List.hd f) with
	| ECase b -> b.formula_case_pos
	| EBase b -> b.formula_ext_pos
	| EAssume (x,b,_)-> pos_of_formula b
	| EVariance b -> b.formula_var_pos

and pos_of_formula (f : formula) : loc = match f with
  | Base ({formula_base_pos = pos}) -> pos
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> pos_of_formula f1
  (* | Or ({formula_or_pos = pos}) -> pos *)
  | Exists ({formula_exists_pos = pos}) -> pos

and struc_fv (f: struc_formula) : CP.spec_var list = 
  let rec ext_fv (f:ext_formula): CP.spec_var list = match f with
	| ECase b ->
		  Gen.BList.difference_eq CP.eq_spec_var
              (CP.remove_dups_svl (List.concat (List.map (fun (c1,c2) -> (CP.fv c1)@(struc_fv c2) ) b.formula_case_branches)))
              b.formula_case_exists
	| EBase b ->
		  let e = struc_fv b.formula_ext_continuation in
		  let be = fv b.formula_ext_base in
		  Gen.BList.difference_eq CP.eq_spec_var (CP.remove_dups_svl (e@be)) (b.formula_ext_explicit_inst @ b.formula_ext_implicit_inst@ b.formula_ext_exists)
	| EAssume (x,b,_) -> fv b
	| EVariance b ->
		  let measures_fv = (List.concat (List.map (fun (expr, bound) -> match bound with
			| None -> (CP.afv expr)
			| Some b_expr -> (CP.afv expr)@(CP.afv b_expr)) b.formula_var_measures)) in
		  let escapes_fv = (List.concat (List.map (fun f -> CP.fv f) b.formula_var_escape_clauses)) in
		  let continuation_fv = struc_fv b.formula_var_continuation in
		  Gen.BList.remove_dups_eq (=) (measures_fv@escapes_fv@continuation_fv)
  in CP.remove_dups_svl (List.fold_left (fun a c-> a@(ext_fv c)) [] f)
	     
and struc_post_fv (f:struc_formula):Cpure.spec_var list =
  let rec helper (f:ext_formula): Cpure.spec_var list = match f with
	| ECase b-> List.fold_left (fun a (_,c2)-> a@(struc_post_fv c2)) [] b.formula_case_branches
	| EBase b->	struc_post_fv b.formula_ext_continuation
	| EAssume (x,b,_)-> fv b
	| EVariance b -> struc_post_fv b.formula_var_continuation
  in	
  List.fold_left (fun a c-> a@(helper c)) [] f
	  
and fv (f : formula) : CP.spec_var list = match f with
  | Or ({formula_or_f1 = f1; 
	formula_or_f2 = f2}) -> CP.remove_dups_svl (fv f1 @ fv f2)
  | Base ({formula_base_heap = h; 
	formula_base_pure = p;
	formula_base_branches = br;
	formula_base_type = t}) -> 
      br_fv br (h_fv h @ MCP.mfv p)
  | Exists ({formula_exists_qvars = qvars; 
	formula_exists_heap = h; 
	formula_exists_pure = p; 
	formula_exists_type = t;
	(* formula_exists_imm = imm; *)
	formula_exists_flow = fl;
	formula_exists_branches = br;
    formula_exists_label = lbl;
	formula_exists_pos = pos}) -> 
	    let fvars = fv (Base ({formula_base_heap = h; 
		formula_base_pure = p; 
		formula_base_type = t;
		(* formula_base_imm = imm; *)
		formula_base_flow = fl;
        formula_base_branches = br;
        formula_base_label = lbl;
		formula_base_pos = pos})) in
	    let res = Gen.BList.difference_eq CP.eq_spec_var fvars qvars in
		res
		    
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
               h_formula_data_arguments = vs})
  | ViewNode ({h_formula_view_node = v; 
               h_formula_view_perm = perm; 
	           h_formula_view_arguments = vs}) -> 
      let pvars = fv_cperm perm in
      let pvars = 
        if pvars==[] then 
          pvars 
        else 
          let var = List.hd pvars in
          if (List.mem var vs) then [] else pvars
      in
      let vs=pvars@vs in
      if List.mem v vs then vs else v :: vs
  | HTrue | HFalse | Hole _ -> []

and br_fv br init_l: CP.spec_var list =
  CP.remove_dups_svl (List.fold_left (fun a (c1,c2)-> (CP.fv c2)@a) init_l br)
  
and f_top_level_vars_struc (f:struc_formula) : CP.spec_var list = 
  let helper f = match f with
  | ECase c-> List.concat (List.map (fun (_,c) -> f_top_level_vars_struc c) c.formula_case_branches)
  | EBase b -> 	(f_top_level_vars b.formula_ext_base) @ (f_top_level_vars_struc b.formula_ext_continuation)
  | EAssume _ -> []
  | EVariance _ -> [] in
  List.concat (List.map helper f)
        
and f_top_level_vars_x (f : formula) : CP.spec_var list = match f with
  | Base ({formula_base_heap = h}) -> (top_level_vars h)
  | Or ({ formula_or_f1 = f1;
	formula_or_f2 = f2}) -> (f_top_level_vars_x f1) @ (f_top_level_vars_x f2)
  | Exists ({formula_exists_heap = h}) -> (top_level_vars h)

and f_top_level_vars (f : formula) : CP.spec_var list = 
  let pr1 = !print_formula in
  let pr2 = !print_svl in
  Gen.Debug.no_1 "f_top_level_vars" pr1 pr2 f_top_level_vars_x f 


and top_level_vars (h : h_formula) : CP.spec_var list = match h with
  | Star ({h_formula_star_h1 = h1; 
	h_formula_star_h2 = h2}) -> (top_level_vars h1) @ (top_level_vars h2)
  | Conj ({h_formula_conj_h1 = h1; 
	h_formula_conj_h2 = h2}) -> (top_level_vars h1) @ (top_level_vars h2)
  | Phase ({h_formula_phase_rd = h1; 
	h_formula_phase_rw = h2}) -> (top_level_vars h1) @ (top_level_vars h2)
  | DataNode ({h_formula_data_node = v}) 
  | ViewNode ({h_formula_view_node = v}) -> [v]
  | HTrue | HFalse | Hole _ -> []

and get_formula_pos (f : formula) = match f with
  | Base ({formula_base_pos = p}) -> p
  | Or ({formula_or_pos = p}) -> p
  | Exists ({formula_exists_pos = p}) -> p 


(* substitution *)

and subst_avoid_capture (fr : CP.spec_var list) (t : CP.spec_var list) (f : formula) =
  Gen.Debug.no_3 "subst_avoid_capture" 
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
  Gen.Debug.no_3 "[cformula]subst_avoid_capture_h" !print_svl !print_svl !print_h_formula !print_h_formula
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

and subst_struc_pre sst (f : struc_formula) = 
  (* apply_par_struc_pre s f *)
  match sst with
  | s :: rest -> subst_struc_pre rest (apply_one_struc_pre s f)
  | [] -> f 

and apply_one_struc_pre  ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : struc_formula):struc_formula = 
  let rec helper (f:ext_formula):ext_formula = match f with
	| ECase b -> 
		  ECase ({b with 
              formula_case_branches = List.map (fun (c1,c2)-> ((CP.apply_one s c1),(apply_one_struc_pre s c2)) ) b.formula_case_branches;})      
	| EBase b ->
		  EBase ({
			  formula_ext_explicit_inst = List.map (subst_var s)  b.formula_ext_explicit_inst;
			  formula_ext_implicit_inst = List.map (subst_var s)  b.formula_ext_implicit_inst;
			  formula_ext_exists = List.map (subst_var s)  b.formula_ext_exists;
			  formula_ext_base = apply_one s  b.formula_ext_base;
			  formula_ext_continuation = apply_one_struc_pre s b.formula_ext_continuation;
			  formula_ext_pos = b.formula_ext_pos	
		  })
	| EAssume (x,b,y)-> if (List.mem fr x) then f
	  else EAssume (x, (apply_one s b),y)
	| EVariance b -> EVariance ({ b with
		  formula_var_measures = List.map (fun (expr, bound) -> match bound with
			| None -> ((CP.e_apply_one s expr), None)
			| Some b_expr -> ((CP.e_apply_one s expr), Some (CP.e_apply_one s b_expr))) b.formula_var_measures;
		  formula_var_escape_clauses = List.map (fun f -> CP.apply_one s f) b.formula_var_escape_clauses;
		  formula_var_continuation = apply_one_struc_pre s b.formula_var_continuation
	  })
  in	
  List.map helper f
      
and apply_one_struc  ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : struc_formula):struc_formula = 
  let rec helper (f:ext_formula):ext_formula = match f with
	| ECase b -> 
		  ECase ({b with formula_case_branches = List.map (fun (c1,c2)-> ((CP.apply_one s c1),(apply_one_struc s c2)) ) b.formula_case_branches;})
	| EBase b ->
		  EBase ({
			  formula_ext_explicit_inst = List.map (subst_var s)  b.formula_ext_explicit_inst;
			  formula_ext_implicit_inst = List.map (subst_var s)  b.formula_ext_implicit_inst;
			  formula_ext_exists = List.map (subst_var s)  b.formula_ext_exists;
			  formula_ext_base = apply_one s  b.formula_ext_base;
			  formula_ext_continuation = apply_one_struc s b.formula_ext_continuation;
			  formula_ext_pos = b.formula_ext_pos	
		  })
	| EAssume (x,b,y)-> EAssume((subst_var_list [s] x),(apply_one s b),y)
	| EVariance b -> EVariance ({ b with
		  formula_var_measures = List.map (fun (expr, bound) -> match bound with
			| None -> ((CP.e_apply_one s expr), None)
			| Some b_expr -> ((CP.e_apply_one s expr), Some (CP.e_apply_one s b_expr))) b.formula_var_measures;
		  formula_var_escape_clauses = List.map (fun f -> CP.apply_one s f) b.formula_var_escape_clauses;
		  formula_var_continuation = apply_one_struc s b.formula_var_continuation;
	  })
  in	
  List.map helper f

(*LDK: add a constraint formula between perm spec var of datanode to fresh spec var of a view decl  *)
and add_mix_formula_to_struc_formula  (rhs_p: MCP.mix_formula) (f : struc_formula): struc_formula =
  Gen.Debug.no_2 "add_mix_formula_to_struc_formula"
      !print_mix_formula !print_struc_formula !print_struc_formula
      add_mix_formula_to_struc_formula_x rhs_p f 

(*LDK: only heap need fractional permision spec var (perm) *)
and add_mix_formula_to_struc_formula_x (rhs_p: MCP.mix_formula) (f : struc_formula) : struc_formula =
  let rec helper (f:ext_formula):(ext_formula) = match f with
	| ECase b ->
        let _ = print_string ("[add_perm_to_struc_formula] Warning: rhs_p for ECase not added \n") in
        f
	| EBase b ->
        let ext_base = b.formula_ext_base in

        (* let _ = print_string ("ttt, add_rhspure_to_struc_formula_x:" *)
        (*                       ^ "\n  ext_base = " ^ (!print_formula ext_base) *)
        (*                       ^ "\n  b.formula_ext_explicit_inst = " ^ (!print_spec_var_list  b.formula_ext_explicit_inst) *)
        (*                       ^ "\n  b.formula_ext_implicit_inst = " ^ (!print_spec_var_list  b.formula_ext_implicit_inst) *)
        (*                       ^ "\n  b.formula_ext_exists = " ^ (!print_spec_var_list  b.formula_ext_exists) *)
        (*                       ^ "\n b.formula_ext_base = " ^ (!print_formula b.formula_ext_base) *)
        (*                       ^ "\n b.formula_ext_continuation = " ^ (!print_struc_formula b.formula_ext_continuation) *)
        (*                       ^ "\n\n") in *)


        let ext_base = add_mix_formula_to_formula rhs_p ext_base  in

        (* let _ = print_string ("ttt, add_rhspure_to_struc_formula_x: after add_rhspure_to_formula_ext_base \n") in *)

        let ext_cont_f = (add_mix_formula_to_struc_formula_x rhs_p b.formula_ext_continuation) in
        let res_f =
		  EBase ({
			  formula_ext_explicit_inst = b.formula_ext_explicit_inst;
			  formula_ext_implicit_inst = b.formula_ext_implicit_inst;
			  formula_ext_exists = b.formula_ext_exists;
			  formula_ext_base = ext_base;
			  (* formula_ext_base = apply_one_w_perm s  b.formula_ext_base permvar; *)
			  formula_ext_continuation = ext_cont_f;
			  formula_ext_pos = b.formula_ext_pos
		  })
        in res_f

	| EAssume (x,b,y)->
                let _ = print_string ("[add_perm_to_struc_formula] Warning: rhs_p for EAssume not added \n") in
                f
	| EVariance b ->
        let cont = add_mix_formula_to_struc_formula_x rhs_p b.formula_var_continuation in
        let res =
        EVariance ({ b with
		  formula_var_measures = b.formula_var_measures;
		  formula_var_escape_clauses = b.formula_var_escape_clauses;
		  formula_var_continuation = cont;
	  }) in
        res
  in
  let res = List.map helper f in
  res

(*LDK : add a constraint formula between perm spec var of datanode to fresh spec var of a view decl  *)
and add_mix_formula_to_formula  (f1_mix: MCP.mix_formula) (f2_f:formula) : formula =
  Gen.Debug.no_2 "add_mix_formula_to_formula_x" !print_mix_formula !print_formula
      !print_formula
      add_mix_formula_to_formula_x f1_mix f2_f

and add_mix_formula_to_formula_x (f1_mix: MCP.mix_formula) (f2_f:formula)  : formula=
  match f2_f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
        Or ({formula_or_f1 = add_mix_formula_to_formula_x f1_mix f1 ; formula_or_f2 =  add_mix_formula_to_formula_x f1_mix f2 ; formula_or_pos = pos})

    | Base ({  formula_base_heap = qh;
			   formula_base_pure = qp;
			   formula_base_type = tconstr;
			   (* formula_exists_imm = imm; *)
			   formula_base_flow = fl;
			   formula_base_branches = b;
			   formula_base_label = lbl;
			   formula_base_pos = pos}) ->

        let qp1 = add_mix_formula_to_mix_formula f1_mix qp in
        let res =
          Base ({  formula_base_heap = qh;
			       formula_base_pure = qp1;
			       formula_base_type = tconstr;
			       (* formula_exists_imm = imm; *)
			       formula_base_flow = fl;
			       formula_base_branches = b;
			       formula_base_label = lbl;
			       formula_base_pos = pos})

        in res

    | Exists ({formula_exists_qvars = qsv;
			   formula_exists_heap = qh;
			   formula_exists_pure = qp;
			   formula_exists_type = tconstr;
			   (* formula_exists_imm = imm; *)
			   formula_exists_flow = fl;
			   formula_exists_branches = b;
			   formula_exists_label = lbl;
			   formula_exists_pos = pos}) ->

        let qp1 = add_mix_formula_to_mix_formula f1_mix qp in
        let res =
          Exists ({formula_exists_qvars = qsv;
			       formula_exists_heap =  qh;
			       formula_exists_pure = qp1;
			       formula_exists_type = tconstr;
			       (* formula_exists_imm = imm; *)
			       formula_exists_flow = fl;
			       formula_exists_branches = b;
			       formula_exists_label = lbl;
			       formula_exists_pos = pos})
        in res

(*add f1 into p*)
and add_mix_formula_to_mix_formula (f1: MCP.mix_formula) (f2: MCP.mix_formula) :MCP.mix_formula = 
  (MCP.merge_mems f1 f2 true)

and add_formula_to_formula (f1: CP.formula) (f2:CP.formula) =
  (CP.And (f1,f2,no_pos))

and add_pure_formula_to_mix_formula (pure_f: CP.formula) (mix_f: MCP.mix_formula):MCP.mix_formula = 
  (match mix_f with
    | MCP.MemoF m1 -> 
        let _ = print_string ("[add_pure_formula_to_mix_formula] Warning: mix_f not added to MCP.MemoF \n") in
        mix_f
    | MCP.OnePF mix_f_pure -> 
        MCP.OnePF (add_formula_to_formula pure_f mix_f_pure)
  )

(*and subst sst (f : formula) = match sst with
  | s :: rest -> subst rest (apply_one s f)
  | [] -> f*)
	
(** An Hoa : replace the function subst above by substituting f in parallel **)

and subst sst (f : formula) = 
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula in
  Gen.Debug.no_2 "subst_one_by_one" pr1 pr2 pr2 subst_x sst f 

and subst_x sst (f : formula) =
  let rec helper f =
	match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
    Or ({formula_or_f1 = helper f1; formula_or_f2 =  helper f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h; 
					formula_base_pure = p; 
					formula_base_type = t;
					(* formula_base_imm = imm; *)
					formula_base_flow = fl;
					formula_base_branches = b;
					formula_base_label = lbl;
					formula_base_pos = pos}) -> 
		Base ({formula_base_heap = h_subst sst h; 
					formula_base_pure =MCP.regroup_memo_group (MCP.m_apply_par sst p); 
					formula_base_type = t;
					(* formula_base_imm = imm; *)
					formula_base_flow = fl;
					formula_base_label = lbl;
					formula_base_branches = List.map (fun (l, p1) -> (l, CP.apply_subs sst p1)) b;
					formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
						formula_exists_heap = qh; 
						formula_exists_pure = qp; 
						formula_exists_type = tconstr;
						(* formula_exists_imm = imm; *)
						formula_exists_flow = fl;
						formula_exists_branches = b;
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
									(* formula_exists_imm = imm; *)
									formula_exists_flow = fl;
									formula_exists_branches = List.map (fun (l, p1) -> (l, CP.apply_subs sst p1)) b;
									formula_exists_label = lbl;
									formula_exists_pos = pos})
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
							h_formula_data_imm = imm;  
							h_formula_data_perm = map_opt (CP.subst_var_par sst) perm;   (*LDK*)
							h_formula_data_arguments = List.map (CP.subst_var_par sst) svs;
							h_formula_data_holes = hs; (* An Hoa 16/8/2011 Holes added *)
							h_formula_data_origins = orgs;
							h_formula_data_original = original;
							h_formula_data_label = lbl;
							h_formula_data_remaining_branches = ann;
							h_formula_data_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_subs sst c,c2)) pcond;
							h_formula_data_pos = pos})
  | HTrue -> f
  | HFalse -> f
  | Hole _ -> f
(** An Hoa : End of heap formula substitution **) 

(* and subst_var_par sst v = try *)
(* 			List.assoc v sst *)
(* 	with Not_found -> v *)

and subst_one_by_one sst (f : formula) = 
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula in
  Gen.Debug.no_2 "subst_one_by_one" pr1 pr2 pr2 subst_one_by_one_x sst f 

and subst_one_by_one_x sst (f : formula) = match sst with
  | s :: rest -> subst_one_by_one_x rest (apply_one s f)
  | [] -> f

and subst_one_by_one_h sst (f : h_formula) = 
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_h_formula in
  Gen.Debug.no_2 "subst_one_by_one" pr1 pr2 pr2 subst_one_by_one_h_x sst f 

and subst_one_by_one_h_x sst (f : h_formula) = match sst with
  | s :: rest -> subst_one_by_one_h_x rest (h_apply_one s f)
  | [] -> f

and subst_var (fr, t) (o : CP.spec_var) = if CP.eq_spec_var fr o then t else o

and apply_one ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
        Or ({formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h; 
	formula_base_pure = p; 
	formula_base_type = t;
	(* formula_base_imm = imm; *)
	formula_base_flow = fl;
    formula_base_branches = b;
    formula_base_label = lbl;
	formula_base_pos = pos}) -> 
        Base ({formula_base_heap = h_apply_one s h; 
		formula_base_pure =MCP.regroup_memo_group (MCP.m_apply_one s p); 
		formula_base_type = t;
		(* formula_base_imm = imm; *)
		formula_base_flow = fl;
        formula_base_label = lbl;
        formula_base_branches = List.map (fun (l, p1) -> (l, CP.apply_one s p1)) b;
		formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
	formula_exists_heap = qh; 
	formula_exists_pure = qp; 
	formula_exists_type = tconstr;
	(* formula_exists_imm = imm; *)
	formula_exists_flow = fl;
    formula_exists_branches = b;
    formula_exists_label = lbl;
	formula_exists_pos = pos}) -> 
	    if List.mem (CP.name_of_spec_var fr) (List.map CP.name_of_spec_var qsv) then f 
	    else Exists ({formula_exists_qvars = qsv; 
		formula_exists_heap =  h_apply_one s qh; 
		formula_exists_pure = MCP.regroup_memo_group (MCP.m_apply_one s qp); 
		formula_exists_type = tconstr;
		(* formula_exists_imm = imm; *)
		formula_exists_flow = fl;
        formula_exists_branches = List.map (fun (l, p1) -> (l, CP.apply_one s p1)) b;
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
		(* h_formula_view_name = c;  *)
        (* h_formula_view_imm = imm;   *)
        h_formula_view_perm = subst_var_perm s perm;  (*LDK*)
		h_formula_view_arguments = List.map (subst_var s) svs;
	   (*  h_formula_view_modes = modes; *)
	   (*  h_formula_view_coercible = coble; *)
	   (*  h_formula_view_origins = orgs; *)
	   (*  h_formula_view_original = original; *)
	   (* h_formula_view_unfold_num = i; *)
	   (*  h_formula_view_label = lbl; *)
       (*  h_formula_view_remaining_branches = ann; *)
        h_formula_view_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_one s c,c2)) pcond
		(* h_formula_view_pos = pos *)
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
    	h_formula_data_imm = imm;  
    	h_formula_data_perm = subst_var_perm s perm; (*LDK*)
	    h_formula_data_origins = orgs;
	    h_formula_data_original = original;
		h_formula_data_arguments = List.map (subst_var s) svs;
	    h_formula_data_holes = hs;
		h_formula_data_label = lbl;
        h_formula_data_remaining_branches = ann;
        h_formula_data_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_one s c,c2)) pcond;
		h_formula_data_pos = pos})

  | HTrue -> f
  | HFalse -> f
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
			let new_h, new_p, new_fl, b, new_t = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl b pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end

and normalize i (f1 : formula) (f2 : formula) (pos : loc) = 
  Gen.Debug.no_2_num i "normalize" !print_formula !print_formula !print_formula (fun _  _ -> normalize_x f1 f2 pos) f1 f2
	    
and normalize_x (f1 : formula) (f2 : formula) (pos : loc) = 
  normalize_keep_flow f1 f2 Flow_combine pos
  (* normalize_keep_flow f1 f2 Flow_combine pos *)
      (* todo: check if this is ok *)

(* and normalize_replace (f1 : formula) (f2 : formula) (pos : loc) =  *)
(*   Gen.Debug.no_1 "normalize_replace" pr_no pr_no (fun _ -> normalize_replace_x f1 f2 pos) f1 *)

(*LDK*)
and normalize_replace (f1 : formula) (f2 : formula) (pos : loc) = 
  Gen.Debug.no_2 "normalize_replace" !print_formula !print_formula !print_formula
      (fun _ _ -> normalize_replace_x f1 f2 pos) f1 f2

and normalize_replace_x (f1 : formula) (f2 : formula) (pos : loc) = 
  normalize_keep_flow f1 f2 Flow_replace pos

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
			let new_h, new_p, new_fl, b, new_t = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl b pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end

and normalize_combine_star (f1 : formula) (f2 : formula) (pos : loc) = 
  let pr = !print_formula in
  Gen.Debug.no_2 "normalize_combine_star" pr pr pr 
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
			let new_h, new_p, new_fl, b, new_t = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl b pos in (* qvars[1|2] are fresh vars, hence no duplications *)
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
			let new_h, new_p, new_fl, b, new_t = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl b pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end

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

(* -- 13.05.2008 *)
(* normalizes but only renames the bound variables of f1 that clash with variables from fv(f2) *)
and normalize_only_clash_rename (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
        let eo1 = normalize_only_clash_rename o11 f2 pos in
        let eo2 = normalize_only_clash_rename o12 f2 pos in
		mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
		| Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
			  let eo1 = normalize_only_clash_rename f1 o21 pos in
			  let eo2 = normalize_only_clash_rename f1 o22 pos in
			  mkOr eo1 eo2 pos
		| _ -> begin
			let rf1 = (fst (rename_clash_bound_vars f1 f2)) in
			let rf2 = (*rename_bound_vars*) f2 in
			let qvars1, base1 = split_quantifiers rf1 in
			let qvars2, base2 = split_quantifiers rf2 in
			let new_base = mkStar_combine base1 base2 Flow_combine pos in
			let new_h, new_p, new_fl, b, new_t = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl b pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end
        (* 13.05.2008 -- *)

(* split a conjunction into heap constraints, pure pointer constraints, *)
(* and Presburger constraints *)
and split_components (f : formula) = 
  if (isAnyConstFalse f) then (HFalse,(MCP.mkMFalse no_pos),(flow_formula_of_formula f),[],TypeFalse)
  else match f with
    | Base ({formula_base_heap = h; 
	  formula_base_pure = p; 
      formula_base_branches = b;
      (* formula_base_imm = imm; *)
	  formula_base_flow =fl;
	  formula_base_type = t}) -> (h, p(*, imm*), fl, b, t)
    | Exists ({formula_exists_heap = h; 
	  formula_exists_pure = p; 
      formula_exists_branches = b;
      (* formula_exists_imm = imm; *)
	  formula_exists_flow = fl;
	  formula_exists_type = t}) -> (h, p(*, imm*), fl, b, t)
          (*| Exists ({formula_exists_pos = pos}) -> 
            Err.report_error {Err.error_loc = pos;
			Err.error_text = "split_components: don't expect EXISTS"}*)
    | Or ({formula_or_pos = pos}) -> 
          Err.report_error {Err.error_loc = pos;Err.error_text = "split_components: don't expect OR"}
			  
and split_quantifiers (f : formula) : (CP.spec_var list * formula) = match f with
  | Exists ({formula_exists_qvars = qvars; 
	formula_exists_heap =  h; 
	formula_exists_pure = p; 
	formula_exists_type = t;
	formula_exists_flow = fl;
	formula_exists_branches = b;
	formula_exists_pos = pos}) -> 
        (qvars, mkBase h p t fl b pos)
  | Base _ -> ([], f)
  | _ -> failwith ("split_quantifiers: invalid argument")

and add_quantifiers (qvars : CP.spec_var list) (f : formula) : formula = match f with
  | Base ({formula_base_heap = h; 
	formula_base_pure = p; 
	formula_base_type = t;
	formula_base_flow = fl;
    formula_base_branches = b;
	formula_base_pos = pos}) -> mkExists qvars h p t fl b pos
  | Exists ({formula_exists_qvars = qvs; 
	formula_exists_heap = h; 
	formula_exists_pure = p; 
	formula_exists_type = t;
	formula_exists_flow = fl;
    formula_exists_branches = b;
	formula_exists_pos = pos}) -> 
	    let new_qvars = CP.remove_dups_svl (qvs @ qvars) in
		mkExists new_qvars h p t fl b pos
  | _ -> failwith ("add_quantifiers: invalid argument")

(* 19.05.2008 *)
and remove_quantifiers (qvars : CP.spec_var list) (f : formula) : formula = match f with
  | Base _ -> f
  | Exists ({formula_exists_qvars = qvs; 
	formula_exists_heap = h; 
	formula_exists_pure = p; 
	formula_exists_type = t;
	formula_exists_flow = fl;
    formula_exists_branches = b;
	formula_exists_pos = pos}) -> 
	    let new_qvars = (List.filter (fun x -> not(List.exists (fun y -> CP.eq_spec_var x y) qvars)) qvs) in
	  	if (List.length new_qvars == 0) then mkBase h p t fl b pos
	  	else mkExists new_qvars h p t fl b pos
  | _ -> failwith ("add_quantifiers: invalid argument")
        (* 19.05.2008 *)

and push_struc_exists (qvars : CP.spec_var list) (f : struc_formula) = 
  List.map (fun c-> match c with
	| EBase b -> EBase {b with formula_ext_exists = b.formula_ext_exists @ qvars}
	| ECase b -> ECase {b with formula_case_exists = b.formula_case_exists @ qvars}
	| EAssume (x,b,y) -> EAssume (x,(push_exists qvars b),y)
	| EVariance b -> EVariance b) f
	  


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

(* and formula_of_disjuncts (f:formula list) : formula=  *)
(*   if (f=[]) then (mkTrue (mkTrueFlow()) no_pos) *)
(*   else List.fold_left (fun a c-> mkOr a c no_pos) (mkFalse (mkFalseFlow ) no_pos) f *)

and formula_of_disjuncts (f:formula list) : formula=
  match f with
    | [] -> (mkTrue (mkTrueFlow()) no_pos)
    | x::xs -> List.fold_left (fun a c-> mkOr a c no_pos) x xs

and rename_struc_bound_vars (f:struc_formula):struc_formula =
  let rec helper (f:ext_formula):ext_formula = match f with
	| ECase b-> 
		  let sst3 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_case_exists in
		  let f = ECase {b with formula_case_exists = (snd (List.split sst3));
			  formula_case_branches = List.map (fun (c1,c2)-> ((Cpure.rename_top_level_bound_vars c1),(rename_struc_bound_vars c2))) b.formula_case_branches;} in
		  List.hd(subst_struc sst3 [f])
	| EBase b-> 
		  let sst1 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_ext_explicit_inst in
		  let sst2 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_ext_implicit_inst in
		  let sst3 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_ext_exists in
		  let sst = sst1@sst2@sst3 in
		  let f = EBase {b with 
			  formula_ext_implicit_inst = (snd (List.split sst2));
			  formula_ext_explicit_inst = (snd (List.split sst1));
			  formula_ext_exists = (snd (List.split sst3));
			  formula_ext_base = rename_bound_vars b.formula_ext_base;
			  formula_ext_continuation = rename_struc_bound_vars b.formula_ext_continuation;
		  }in
		  let f = subst_struc sst [f] in
		  (List.hd f)
	| EAssume (x,b,y)-> EAssume (x,(rename_bound_vars b),y)
	| EVariance b -> EVariance { b with
		  formula_var_escape_clauses = List.map (fun f -> Cpure.rename_top_level_bound_vars f) b.formula_var_escape_clauses;
		  formula_var_continuation = rename_struc_bound_vars b.formula_var_continuation;
	  }	   
  in
  List.map helper f


and rename_bound_vars (f : formula) = rename_bound_vars_x f

(*
  and rename_bound_vars (f : formula) = 
  Gen.Debug.no_1 "rename_bound_vars" (!print_formula) (!print_formula) rename_bound_vars_x f
*)

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
	    let new_base_f = subst rho base_f in
	    let resform = add_quantifiers new_qvars new_base_f in
		resform

and propagate_perm_formula (f : formula) (permvar:cperm_var) : formula =
  Gen.Debug.no_2 "propagate_perm_formula"
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
        let mk_eq v = mkEq_cperm v permvar no_pos in
        let mk_eqs = List.map mk_eq vars in
        let mk_BForm (b:CP.b_formula): CP.formula = CP.BForm (b,None) in
        let mk_eqs = List.map mk_BForm mk_eqs in
        let perm_p = List.fold_left (fun res v -> CP.mkAnd v res no_pos) (CP.mkTrue no_pos) mk_eqs in
        let perm_p = MCP.OnePF perm_p in
        (* let _ = print_string ("propagate_perm_formula: Base" *)
        (*                       ^ "\n ### base_p = " ^ (!print_mix_f base_p) *)
        (*                       ^ "\n ### perm_p = " ^ (!print_mix_f perm_p) *)
        (*                       ^ "\n\n") in *)
        let base_p = add_mix_formula_to_mix_formula perm_p base_p in
        Base({f1 with formula_base_heap = f1_heap; formula_base_pure = base_p})
  | Exists f1 ->
        let f1_heap,vars = propagate_perm_h_formula f1.formula_exists_heap permvar in
        let base_p = f1.formula_exists_pure in
        let mk_eq v = mkEq_cperm v permvar no_pos in
        let mk_eqs = List.map mk_eq vars in
        let mk_BForm (b:CP.b_formula): CP.formula = CP.BForm (b,None) in
        let mk_eqs = List.map mk_BForm mk_eqs in
        let perm_p = List.fold_left (fun res v -> CP.mkAnd v res no_pos) (CP.mkTrue no_pos) mk_eqs in
        let perm_p = MCP.OnePF perm_p in
        (* let _ = print_string ("propagate_perm_formula: Exists" *)
        (*                       ^ "\n ### base_p = " ^ (!print_mix_f base_p) *)
        (*                       ^ "\n ### perm_p = " ^ (!print_mix_f perm_p) *)
        (*                       ^ "\n\n") in *)
        let base_p = add_mix_formula_to_mix_formula perm_p base_p in
        Exists({f1 with 
            formula_exists_qvars = List.append vars f1.formula_exists_qvars;
            formula_exists_heap = f1_heap; 
            formula_exists_pure = base_p})

(*Spec_var list to creat pure constraints: freshvar = permvar*)
and propagate_perm_h_formula (f : h_formula) (permvar:cperm_var) : h_formula * (CP.spec_var list) = 
  match f with
    | ViewNode f1 -> 
        let fresh_var = fresh_cperm_var permvar in
        let vn = ViewNode({f1 with h_formula_view_perm = Some fresh_var}) in
        (vn,[fresh_var])
    | DataNode f1 -> 
        let fresh_var = fresh_cperm_var permvar in
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

(* for immutability *)
(* and propagate_imm_struc_formula (sf : struc_formula) (imm : bool) : struc_formula =  *)
(* let helper (f : ext_formula) = match f with *)
(* 	| EBase b -> EBase {b with formula_ext_base = substitute_flow_in_f to_flow from_flow b.formula_ext_base ;  *)
(* 								   formula_ext_continuation = substitute_flow_in_struc_f to_flow from_flow  b.formula_ext_continuation} *)
(* 	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2) -> (c1,(substitute_flow_in_struc_f to_flow from_flow  c2))) b.formula_case_branches} *)
(* 	| EAssume (x,b,y) -> EAssume (x,(substitute_flow_in_f to_flow from_flow  b),y) *)
(* 	in *)
(* List.map helper f	 *)

and propagate_imm_formula (f : formula) (imm : bool) : formula = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	    let rf1 = propagate_imm_formula f1 imm in
	    let rf2 = propagate_imm_formula f2 imm in
	    let resform = mkOr rf1 rf2 pos in
		resform
  | Base f1 ->
        let f1_heap = propagate_imm_h_formula f1.formula_base_heap imm in
        Base({f1 with formula_base_heap = f1_heap})
  | Exists f1 ->
        let f1_heap = propagate_imm_h_formula f1.formula_exists_heap imm in
        Exists({f1 with formula_exists_heap = f1_heap})

and propagate_imm_h_formula (f : h_formula) (imm : bool) : h_formula = 
  match f with
    | ViewNode f1 -> ViewNode({f1 with h_formula_view_imm = imm})
    | DataNode f1 -> DataNode({f1 with h_formula_data_imm = imm})
    | Star f1 ->
	      let h1 = propagate_imm_h_formula f1.h_formula_star_h1 imm in
	      let h2 = propagate_imm_h_formula f1.h_formula_star_h2 imm in
	      mkStarH h1 h2 f1.h_formula_star_pos
    | Conj f1 ->
	      let h1 = propagate_imm_h_formula f1.h_formula_conj_h1 imm in
	      let h2 = propagate_imm_h_formula f1.h_formula_conj_h2 imm in
	      mkConjH h1 h2 f1.h_formula_conj_pos
    | Phase f1 ->
	      let h1 = propagate_imm_h_formula f1.h_formula_phase_rd imm in
	      let h2 = propagate_imm_h_formula f1.h_formula_phase_rw imm in
	      mkPhaseH h1 h2 f1.h_formula_phase_pos
    | _ -> f


(* -- 13.05.2008 *)
(* rename only those bound vars of f1 which clash with fv(f2) *)
(* return the new formula and the list of fresh names *)
and rename_struc_clash_bound_vars (f1 : struc_formula) (f2 : formula) : struc_formula  = 
  let rec helper (f1:ext_formula):(ext_formula) = match f1 with
	| EAssume (x,b,y)-> EAssume (x,(fst(rename_clash_bound_vars b f2)),y)
	| ECase b ->  
		  let r1 = List.map (fun (c1,c2) -> (c1,(rename_struc_clash_bound_vars c2 f2))) b.formula_case_branches in
		  let new_exs = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_case_exists in
		  let rho = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2))) new_exs) in
		  ECase {formula_case_exists = (snd (List.split new_exs));
		  formula_case_branches = List.map (fun (c1,c2)-> ((Cpure.subst rho c1),(subst_struc rho c2))) r1;
		  formula_case_pos = b.formula_case_pos}
	| EBase b -> 
		  let new_base_f,c1 = rename_clash_bound_vars b.formula_ext_base f2 in
		  let new_imp = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_ext_implicit_inst in
		  let new_exp = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_ext_explicit_inst in
		  let new_exs = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_ext_exists in
		  (* fresh_qvars contains only the freshly generated names *)
		  let rho_imp = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2)))  new_imp) in
		  let rho_exp = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2)))  new_exp) in
		  let rho_exs = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2)))  new_exs) in
		  let rho = rho_imp@rho_exp@rho_exs in
		  let new_base_f = subst rho new_base_f in
		  let new_cont_f = subst_struc rho b.formula_ext_continuation in
		  let new_cont_f = rename_struc_clash_bound_vars new_cont_f f2 in
		  EBase {b with 
			  formula_ext_implicit_inst = (snd (List.split new_imp));
			  formula_ext_explicit_inst = (snd (List.split new_exp));
			  formula_ext_exists = (snd (List.split new_exs));
			  formula_ext_base = new_base_f;
			  formula_ext_continuation = new_cont_f;
		  }
	| EVariance b -> EVariance { b with
		  formula_var_continuation = rename_struc_clash_bound_vars b.formula_var_continuation f2
	  }
  in
  List.map helper f1

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
   Gen.Debug.no_3 "compose_formula" pr1 pr1 pr3 pr1 (fun _ _ _ -> compose_formula_x delta phi x flow_tr pos) delta phi x
	  
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
  Gen.Debug.no_2 "get_var_type" 
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
        
        

and contains_mutable (f : formula) : bool =  match f with
  | Base(bf) -> contains_mutable_h_formula bf.formula_base_heap
  | Exists(ef) -> contains_mutable_h_formula ef.formula_exists_heap
  | Or({formula_or_f1 = f1;
    formula_or_f2 = f2;
    formula_or_pos = pos}) ->
        (contains_mutable f1) or (contains_mutable f2)
            
and contains_mutable_h_formula (f : h_formula) : bool =  match f with
  | DataNode (h1) -> not(h1.h_formula_data_imm)
  | ViewNode (h1) -> not(h1.h_formula_view_imm)
  | Conj({h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;
	h_formula_conj_pos = pos})
  | Phase({h_formula_phase_rd = h1;
	h_formula_phase_rw = h2;
	h_formula_phase_pos = pos})
  | Star({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos}) -> (contains_mutable_h_formula h1) or (contains_mutable_h_formula h2)
  | _ -> false

(*
  and contains_immutable (f : formula) : bool =
  match f with
  | Base(bf) -> bf.formula_base_imm
  | Exists(ef) -> ef.formula_exists_imm
  | Or({formula_or_f1 = f1;
  formula_or_f2 = f2;
  formula_or_pos = pos}) ->
  (contains_immutable f1) or (contains_immutable f2)
*)
        
and contains_immutable_debug f = 
  Gen.Debug.no_1 "contains_immutable"
      (!print_formula)
      (string_of_bool)
      contains_immutable f

and contains_immutable (f : formula) : bool =  match f with
  | Base(bf) -> contains_immutable_h_formula bf.formula_base_heap
  | Exists(ef) -> contains_immutable_h_formula ef.formula_exists_heap
  | Or({formula_or_f1 = f1;
    formula_or_f2 = f2;
    formula_or_pos = pos}) ->
        (contains_immutable f1) or (contains_immutable f2)
            
and contains_immutable_h_formula_debug f = 
  Gen.Debug.no_1 "contains_immutable_h_formula"
      (!print_h_formula)
      (string_of_bool)
      contains_immutable_h_formula f


and contains_immutable_h_formula (f : h_formula) : bool =  match f with
  | DataNode (h1) -> 
        if h1.h_formula_data_imm then
          let _ = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n") in true
        else
          false
  | ViewNode (h1) -> (* h1.h_formula_view_imm *)
        if h1.h_formula_view_imm then
          let _ = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n") in true
        else
          false

  | Conj({h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;
	h_formula_conj_pos = pos})
  | Phase({h_formula_phase_rd = h1;
	h_formula_phase_rw = h2;
	h_formula_phase_pos = pos}) -> true
  | Star({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos}) -> (contains_immutable_h_formula h1) or (contains_immutable_h_formula h2)
  | Hole _ -> false
  | _ -> false


and contains_phase_debug (f : h_formula) : bool =  
  Gen.Debug.no_1 "contains_phase"
      (!print_h_formula) 
      (string_of_bool)
      (contains_phase)
      f

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


and h_node_list (f: h_formula): CP.spec_var list = match f with
  | DataNode {h_formula_data_node = c}
  | ViewNode {h_formula_view_node = c} -> [c]
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
  | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
  -> (h_node_list h1)@(h_node_list h2)
  | _ -> []

(***************************************************************************************)
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
  Gen.Debug.no_1 "remove_true_conj_mix_formula" !print_mix_formula !print_mix_formula 
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
  Gen.Debug.no_1 "remove_dupl_conj_eq_mix_formula" !print_mix_formula !print_mix_formula 
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
  Gen.Debug.no_1 "remove_dupl_conj_eq_formula" !print_formula !print_formula 
      remove_dupl_conj_eq_formula_x f

(***************************************************************************************)


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

and apply_one_exp ((fr, t) as s : (CP.spec_var * CP.exp)) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
      Or ({formula_or_f1 = apply_one_exp s f1; formula_or_f2 =  apply_one_exp s f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h; 
		   formula_base_pure = p; 
		   formula_base_type = t;
		   (* formula_base_imm = imm; *)
       formula_base_branches = b;
		   formula_base_flow = fl;
       formula_base_label = lbl;
		   formula_base_pos = pos}) -> 
    Base ({formula_base_heap = h; 
			formula_base_pure = MCP.memo_apply_one_exp s p;
			(* formula_base_imm = imm; *)
			formula_base_flow = fl;
     	(* TODO: solve this *)
		 	(*formula_base_pure = CP.elim_idents (CP.apply_one_exp s p);*) (* substitute + easy simplification - eliminate identities where LHS identic to RHS *)
		 	formula_base_type = t;
      formula_base_branches = List.map (fun (l, p1) -> (l, CP.apply_one_exp s p1)) b;
      formula_base_label = lbl;
		 	formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
			 formula_exists_heap = qh; 
			 formula_exists_pure = qp; 
			 formula_exists_type = tconstr;
			 (* formula_exists_imm = imm; *)
       formula_exists_branches = b;
			 formula_exists_flow = fl;
       formula_exists_label = lbl;
			 formula_exists_pos = pos}) -> 
	  if List.mem (CP.name_of_spec_var fr) (List.map CP.name_of_spec_var qsv) then f 
	  else 
      Exists ({formula_exists_qvars = qsv; 
					formula_exists_heap =  qh; 
					formula_exists_pure = MCP.memo_apply_one_exp s qp; 
					formula_exists_type = tconstr;
					(* formula_exists_imm = imm; *)
					formula_exists_flow = fl;
          formula_exists_branches = List.map (fun (l, p1) -> (l, CP.apply_one_exp s p1)) b;
          formula_exists_label = lbl;
					formula_exists_pos = pos})

(*and combine_branch b *)
  
and replace_branches b = function
  | Or f -> failwith "replace_branches doesn't expect an Or"
  | Base f -> Base {f with formula_base_branches = b;}
  | Exists f -> Exists {f with formula_exists_branches = b;}


let flatten_branches p br =
  List.fold_left (fun p (l, f) -> CP.And (p, f,no_pos)) p br


let rec struc_to_formula_gen (f0:struc_formula):(formula*formula_label option list) list = 
	let rec get_label_f f = match f with
		| Or b-> (get_label_f b.formula_or_f1)@(get_label_f b.formula_or_f2)
		| Base{formula_base_label = l}| Exists{formula_exists_label = l} -> [l]in
	let rec ext_to_formula (f:ext_formula) = match f with
		| ECase b-> 
			  let r = List.concat (List.map 
				  (fun (c1,c2)-> 
					if (isConstEFalse c2) then []
					else
					let np = (MCP.memoise_add_pure_N (MCP.mkMTrue b.formula_case_pos) c1) in
					let npf = mkBase HTrue np TypeTrue (mkTrueFlow ()) [] b.formula_case_pos in
					let l = struc_to_formula_gen c2 in
					List.map (fun (c1,c2) -> (normalize_combine npf c1 no_pos,c2)) l) b.formula_case_branches) in
			  List.map (fun (c1,c2)-> ( (push_exists b.formula_case_exists c1),c2)) r 
		| EBase b-> 
				let nf,nl = b.formula_ext_base,(get_label_f b.formula_ext_base) in
				let lc = struc_to_formula_gen b.formula_ext_continuation in
				let f c = push_exists b.formula_ext_exists (normalize_combine nf c b.formula_ext_pos) in
				(match lc with
				  | [] -> [(f nf, nl)]
				  | _ -> List.map (fun (c1,c2)-> (f c1,nl@c2)) lc)
		| EAssume (_,b,_)-> [(b,[None])]
		| EVariance b -> struc_to_formula_gen b.formula_var_continuation
	in	
	List.concat (List.map ext_to_formula f0) 
	
(* let struc_to_formula f0 :formula = formula_of_disjuncts (fst (List.split (struc_to_formula_gen f0))) *)
(* TO-CHECK : why is above overridden *)

let rec split_conjuncts (f:formula):formula list = match f with 
  | Or b -> (split_conjuncts b.formula_or_f1)@(split_conjuncts b.formula_or_f2)
  | _ -> [f] 
  
let list_of_disjuncts f = split_conjuncts f

let join_conjunct_opt l = match l with
  | [] -> None
  | h::t -> Some (List.fold_left (fun a c-> mkOr c a no_pos) h t)
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
  Gen.Debug.no_1 "join_star_conjunctions_opt" pr1 pr2
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
  Gen.Debug.no_1 "split_star_conjunctions" !print_h_formula pr
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
let rec struc_to_formula_x (f0:struc_formula):formula = 
	let rec ext_to_formula (f:ext_formula):formula = match f with
		| ECase b-> let r = 
			if (List.length b.formula_case_branches) >0 then
			List.fold_left 
			(fun a (c1,c2)-> 
				(*let ng = Cpure.Not (c1,b.formula_case_pos) in*)
				if (isConstEFalse c2) then a
				else
        let c1 = MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) c1 in
				(mkOr a (normalize_combine 
							(mkBase HTrue c1 TypeTrue (mkTrueFlow ()) [] b.formula_case_pos ) 
							(struc_to_formula_x c2)
							b.formula_case_pos
						) 
						b.formula_case_pos
				)
				)
			(mkFalse (mkFalseFlow) b.formula_case_pos) b.formula_case_branches 
			else mkTrue (mkTrueFlow ()) b.formula_case_pos in
			push_exists b.formula_case_exists r 
		| EBase b-> 
				let e = normalize_combine b.formula_ext_base (struc_to_formula_x b.formula_ext_continuation) b.formula_ext_pos in
                (* is it necessary to also push the implicit vars? *)
				let nf = push_exists (b.formula_ext_explicit_inst@b.formula_ext_implicit_inst@b.formula_ext_exists) e in
				nf
		| EAssume (_,b,_)-> b 
		| EVariance b -> struc_to_formula_x b.formula_var_continuation (* (mkTrue (mkTrueFlow ()) b.formula_var_pos) *)
			in	
    formula_of_disjuncts (List.map ext_to_formula f0)
	(* if (List.length f0)>0 then *)
	(* 	List.fold_left (fun a c-> mkOr a (ext_to_formula c) no_pos) (mkFalse (mkFalseFlow) no_pos)f0 *)
	(* else mkTrue (mkTrueFlow ()) no_pos	 *)


and struc_to_formula f0 :formula = 
  let pr1 = !print_struc_formula in
  let pr2 = !print_formula in
  Gen.Debug.no_1 "struc_to_formula" pr1 pr2 struc_to_formula_x f0

(* An Hoa : construct pre-condition from a structured spec formula *)
let rec struc_to_precond_formula (f0 : struc_formula) : formula =
	let rec ext_to_precond_formula (f : ext_formula) : formula =
	match f with
	| ECase b ->
		let fold_function a (c1, c2) = 
			if (isConstEFalse c2) then a 
			else 
				let c1 = MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) c1 in 
					(mkOr a (normalize_combine (mkBase HTrue c1 TypeTrue (mkTrueFlow ()) [] b.formula_case_pos) (struc_to_precond_formula c2) b.formula_case_pos) b.formula_case_pos) in
		let r = if (List.length b.formula_case_branches) >0 then
			List.fold_left fold_function (mkFalse (mkFalseFlow) b.formula_case_pos) b.formula_case_branches 
		else mkTrue (mkTrueFlow ()) b.formula_case_pos in
			push_exists b.formula_case_exists r
	| EBase b -> 
		let e = normalize_combine b.formula_ext_base (struc_to_precond_formula b.formula_ext_continuation) b.formula_ext_pos in
		let nf = push_exists (b.formula_ext_explicit_inst@b.formula_ext_implicit_inst@b.formula_ext_exists) e in
			nf
	| EAssume (_,b,_) -> (* Eliminate assume by making it true *) formula_of_heap HTrue no_pos 
	| EVariance b -> struc_to_precond_formula b.formula_var_continuation in	
    formula_of_disjuncts (List.map ext_to_precond_formula f0)
(* An Hoa : end of pre-condition construction *)

and formula_to_struc_formula (f:formula):struc_formula =
	let rec helper (f:formula):struc_formula = match f with
		| Base b-> [EBase ({
			 		formula_ext_explicit_inst =[];
		 			formula_ext_implicit_inst = [];
					formula_ext_exists = [];
		 			formula_ext_base = f;
					formula_ext_continuation = [];
		 			formula_ext_pos = b.formula_base_pos})]
		| Exists b-> [EBase ({
			 		formula_ext_explicit_inst =[];
		 			formula_ext_implicit_inst = [];
					formula_ext_exists = [];
		 			formula_ext_base = f;
					formula_ext_continuation = [];
		 			formula_ext_pos = b.formula_exists_pos})]
		| Or b->  (helper b.formula_or_f1)@(helper b.formula_or_f2) in			
	(helper f)

and plug_ref_vars (f0:struc_formula) (w:Cpure.spec_var list):struc_formula = 
	let rec filter_quantifiers w f = match f with
	| Base _ -> f
	| Exists b -> Exists {b with formula_exists_qvars = Gen.BList.difference_eq (=) b.formula_exists_qvars w;}
	| Or b -> Or {b with 
						formula_or_f1 = filter_quantifiers w b.formula_or_f1;
						formula_or_f2 = filter_quantifiers w b.formula_or_f2;}in
	let rec helper (f0:ext_formula):ext_formula = match f0 with
	| EAssume (_,b,t)->  EAssume (w,(filter_quantifiers  w b),t)
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> (c1,(plug_ref_vars c2 w))) b.formula_case_branches;}
	| EBase b -> EBase {b with formula_ext_continuation = plug_ref_vars b.formula_ext_continuation w}
	| EVariance b -> EVariance {b with formula_var_continuation = plug_ref_vars b.formula_var_continuation w}
	in 
	List.map helper f0


and guard_vars f = Gen.BList.remove_dups_eq (=) (List.fold_left (fun a f-> a@(match f with
	| ECase b->
      Gen.BList.remove_dups_eq (=) (List.fold_left (fun a (c1,c2)-> a@(Cpure.fv c1)@(guard_vars c2)) [] b.formula_case_branches)
	| EBase b -> Gen.BList.difference_eq (=) (guard_vars b.formula_ext_continuation) b.formula_ext_exists
	| EAssume b-> []
	| EVariance b -> guard_vars b.formula_var_continuation
	)) [] f)

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
	| Hole _ -> None
	| HTrue 
	| HFalse -> Some f
    end
  | Exists b-> 
      begin
	match b.formula_exists_heap with
	  | Star _
	  | Conj _
	  | Phase _    
	  | DataNode _ 
	  | ViewNode _ 
	  | Hole _ -> None
	  | HTrue 
	  | HFalse -> Some f
      end


and case_to_disjunct f  =
  let pr = !print_struc_formula in
  Gen.Debug.no_1 "case_to_disjunct" pr pr case_to_disjunct_x f 

and case_to_disjunct_x f  =
  let rec push_pure c f =  match f with
    | ECase _ -> f (*this should never occur*) 
    | EBase b-> EBase {b with formula_ext_base = 
      normalize_combine 
        b.formula_ext_base 
          (formula_of_pure_N c no_pos) 
          no_pos}
    | _ -> EBase {
       formula_ext_explicit_inst = [];
       formula_ext_implicit_inst = [];
       formula_ext_exists = [];
       formula_ext_base = formula_of_pure_N c no_pos;
       formula_ext_continuation = [f];
       formula_ext_pos = no_pos;
    }	
  and helper f = match f with
    | ECase b-> 
        (List.concat (List.map (fun (c1,c2)-> 
          let f = case_to_disjunct_x c2 in 
          List.map (push_pure c1) f) b.formula_case_branches))
    | EBase b-> [EBase {b with formula_ext_continuation = (case_to_disjunct_x b.formula_ext_continuation)}]
    | _ -> [f] in
List.concat (List.map helper f)


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
  | HTrue 
  | HFalse 
  | Hole _ -> f
	
and replace_pure_formula_label nl f = match f with
  | CP.BForm (bf,_) -> CP.BForm (bf,(nl()))
  | CP.And (b1,b2,b3) -> CP.And ((replace_pure_formula_label nl b1),(replace_pure_formula_label nl b2),b3)
  | CP.Or (b1,b2,b3,b4) -> CP.Or ((replace_pure_formula_label nl b1),(replace_pure_formula_label nl b2),(nl()),b4)
  | CP.Not (b1,b2,b3) -> CP.Not ((replace_pure_formula_label nl b1),(nl()),b3)
  | CP.Forall (b1,b2,b3,b4) -> CP.Forall (b1,(replace_pure_formula_label nl b2),(nl()),b4)
  | CP.Exists (b1,b2,b3,b4) -> CP.Exists (b1,(replace_pure_formula_label nl b2),(nl()),b4)
    	
and replace_formula_label1 nl f = match f with
	| Base b->Base {b with 
			formula_base_heap = replace_heap_formula_label nl b.formula_base_heap ;
			formula_base_pure = MCP.replace_mix_formula_label nl b.formula_base_pure ;
			formula_base_branches = List.map (fun (c1,c2)-> (c1,( CP.replace_pure_formula_label nl c2))) b.formula_base_branches; }
	| Exists b->Exists {b with 
			formula_exists_heap = replace_heap_formula_label nl b.formula_exists_heap ;
			formula_exists_pure = MCP.replace_mix_formula_label nl b.formula_exists_pure ;
            formula_exists_branches = List.map (fun (c1,c2)-> (c1,( CP.replace_pure_formula_label nl c2))) b.formula_exists_branches; }
	| Or b -> Or {b with 
			formula_or_f1 = replace_formula_label1 nl b.formula_or_f1;
			formula_or_f2 = replace_formula_label1 nl b.formula_or_f2;	}
			
let rec replace_struc_formula_label1 nl f = List.map (fun f-> match f with
	| EBase b -> EBase {b with 
			formula_ext_base = replace_formula_label1 nl b.formula_ext_base;
			formula_ext_continuation = replace_struc_formula_label1 nl b.formula_ext_continuation}
	| ECase b -> 
      let new_br = List.map 
        (fun (c1,c2)-> 
          ((CP.replace_pure_formula_label nl c1), (replace_struc_formula_label1 nl c2))
        ) b.formula_case_branches in
      ECase { b with formula_case_branches = new_br;}
	| EAssume (b1,b2,b3)-> EAssume (b1,(replace_formula_label1 nl b2),b3)
	| EVariance b -> EVariance {b with formula_var_continuation = replace_struc_formula_label1 nl b.formula_var_continuation}) f
	
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
    | HTrue 
    | HFalse 
    | Hole _ -> [] 
        in match f with
	| Base b-> residue_labels_in_heap b.formula_base_heap 
	| Exists b->residue_labels_in_heap b.formula_exists_heap
	| Or b -> (residue_labels_in_formula b.formula_or_f1) @ (residue_labels_in_formula b.formula_or_f2)

let get_node_label n =  match n with
	| DataNode b -> b.h_formula_data_label
	| ViewNode b -> b.h_formula_view_label
	| _ -> None

(***************************************************************************************)
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
	      | Hole _	  
	      | HTrue
          | HFalse -> (e, f_comb []) 
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
	      | Hole _
	      | HTrue
	      | HFalse -> e


(* transform formula : f_p_t : pure formula
   f_f : formula
   f_h_f : heap formula
*)
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
              formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure;
              formula_base_branches =  List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) b.formula_base_branches;}
		| Or o -> 
			Or {o with 
                    formula_or_f1 = helper f o.formula_or_f1;
                    formula_or_f2 = helper f o.formula_or_f2;}
		| Exists e -> 
      Exists {e with
                formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap;
                formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure;
                formula_exists_branches = 
                  List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) e.formula_exists_branches;}
  in helper f e



let transform_formula f (e:formula):formula =
  let pr = !print_formula in
  Gen.Debug.no_2 "transform_formula" (fun _ -> "f") pr pr transform_formula_x f e

let transform_formula_w_perm_x (f:formula -> formula option) (e:formula) (permvar:cperm):formula =
	let r =  f e in 
	match r with
	| Some e1 -> e1
	| None  -> e

let transform_formula_w_perm (f:formula -> formula option) (e:formula) (permvar:cperm):formula =
  let pr = !print_formula in
  Gen.Debug.no_3 "transform_formula_w_perm" 
      (fun _ -> "f") pr !print_spec_var pr 
      transform_formula_w_perm_x f e permvar


(* let rec transform_formula f (e:formula):formula = *)
(* 	let (_, f_f, f_h_f, f_p_t) = f in *)
(* 	let r =  f_f e in  *)
(* 	match r with *)
(* 	| Some e1 -> e1 *)
(* 	| None  ->  *)

(*         let _ = print_string ("\n [Debug] transform_formula, e = " ^ (!print_formula e)) in  *)

(*         match e with	  *)
(* 		| Base b ->  *)

(*         let _ = print_string ("\n [Debug] transform_formula, base b = " ^ "\n") in *)

(*       Base{b with  *)
(*               formula_base_heap = transform_h_formula f_h_f b.formula_base_heap; *)
(*               formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure; *)
(*               formula_base_branches =  List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) b.formula_base_branches;} *)
(* 		| Or o ->  *)

(*         let _ = print_string ("\n [Debug] transform_formula, Or o = ") in  *)

(* Or {o with  *)
(*                     formula_or_f1 = transform_formula f o.formula_or_f1; *)
(*                     formula_or_f2 = transform_formula f o.formula_or_f2;} *)
(* 		| Exists e ->  *)

(*         let _ = print_string ("\n [Debug] transform_h_formula,before, Exists e = " ^(!print_h_formula e.formula_exists_heap)) in  *)
(*         let feh = transform_h_formula f_h_f e.formula_exists_heap in *)
(*         let _ = print_string ("\n [Debug] transform_h_formula,after, Exists e = " ^(!print_h_formula feh) ^ "\n") in  *)

(*         let fep = e.formula_exists_pure in *)
(*         let _ = print_string ("\n [Debug] transform_mix_formula,before, Exists e = " ^(!print_mix_f fep)) in *)
(*         let fep = MCP.transform_mix_formula f_p_t fep in *)
(*         let _ = print_string ("\n [Debug] transform_mix_formula,after, Exists e = " ^(!print_mix_f fep) ^ "\n") in         *)

(*       Exists {e with *)
(*                 formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap; *)
(*                 formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure; *)
(*                 formula_exists_branches =  *)
(*                   List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) e.formula_exists_branches;} *)



let transform_formula_w_perm_x (f:formula -> formula option) (e:formula) (permvar:cperm_var):formula =
	let r =  f e in 
	match r with
	| Some e1 -> e1
	| None  -> e


let transform_formula_w_perm (f:formula -> formula option) (e:formula) (permvar:cperm_var):formula =
  let pr = !print_formula in
  Gen.Debug.no_3 "transform_formula_w_perm" 
      (fun _ -> "f") pr !print_spec_var pr 
      transform_formula_w_perm_x f e permvar

let rec trans2_formula f (e:formula):formula =
	let (f_h_f, f_p_t) = f in
    match e with	 
		| Base b -> 
      Base{b with 
              formula_base_heap = transform_h_formula f_h_f b.formula_base_heap;
              formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure;
              formula_base_branches =  List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) b.formula_base_branches;}
		| Or o -> Or {o with 
                    formula_or_f1 = trans2_formula f o.formula_or_f1;
                    formula_or_f2 = trans2_formula f o.formula_or_f2;}
		| Exists e -> 
      Exists {e with
                formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap;
                formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure;
                formula_exists_branches = 
                  List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) e.formula_exists_branches;}

(* let rec trans3_formula (e:formula) (arg:'a) f  (f_args:'a->formula->'a)(f_comb:'b list -> 'b) :(formula * 'b) = *)
(* 	let (f_h_f, f_p_t) = f in *)
(*     let new_args = f_args arg e in *)
(*     match e with	  *)
(* 		| Base b ->  *)
(*       Base{b with  *)
(*               formula_base_heap = transform_h_formula f_h_f b.formula_base_heap; *)
(*               formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure; *)
(*               formula_base_branches =  List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) b.formula_base_branches;} *)
(* 		| Or o -> Or {o with  *)
(*                     formula_or_f1 = trans3_formula f o.formula_or_f1; *)
(*                     formula_or_f2 = trans3_formula f o.formula_or_f2;} *)
(* 		| Exists e ->  *)
(*       Exists {e with *)
(*                 formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap; *)
(*                 formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure; *)
(*                 formula_exists_branches =  *)
(*                   List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) e.formula_exists_branches;} *)

(***************************************************************************************)

let foldheap_formula (h:h_formula -> 'a) (f_comb: 'a list -> 'a)  (e:formula) : 'a =
  let rec helper e =
    match e with
      | Base {formula_base_heap = e} -> h e
      | Or { formula_or_f1 = e1; formula_or_f2 = e2} -> f_comb [helper e1;helper e2]
      | Exists {formula_exists_heap = e} -> h e
  in helper e


let foldheap_struc_formula (h:h_formula -> 'a) (f_comb: 'a list -> 'a)  (e:struc_formula): 'a =
  let rec helper (e:struc_formula) =
    let rs = List.map (helper_ext) e in
    f_comb rs
  and helper_ext  (e:ext_formula) : 'a =
    match e with
      | ECase {formula_case_branches = brs} -> 
            let rs = List.map (fun (_,e) -> helper e) brs in
            f_comb rs
      | EBase { formula_ext_base = b;
        formula_ext_continuation = c;
        } -> 
            let rs1 = foldheap_formula h f_comb b in
            let rs2 = helper c in
            f_comb [rs1;rs2]
      | EAssume (_,e,_) -> foldheap_formula h f_comb e
      | _ -> f_comb []
  in helper e


(* let trans_formula_2 f (e:formula) (arg:a) f (f_args: 'a->formula->'a) (f_comb:'b list -> 'b) : formula * 'b = *)
(* 	let (_, f_f, f_h_f, f_p_t) = f in *)
(* 	let r =  f_f e in  *)
(* 	match r with *)
(* 	| Some e1 -> e1 *)
(* 	| None  -> match e with	  *)
(* 		| Base b ->  *)
(*       Base{b with  *)
(*               formula_base_heap = transform_h_formula f_h_f b.formula_base_heap; *)
(*               formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure; *)
(*               formula_base_branches =  List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) b.formula_base_branches;} *)
(* 		| Or o -> Or {o with  *)
(*                     formula_or_f1 = transform_formula f o.formula_or_f1; *)
(*                     formula_or_f2 = transform_formula f o.formula_or_f2;} *)
(* 		| Exists e ->  *)
(*       Exists {e with *)
(*                 formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap; *)
(*                 formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure; *)
(*                 formula_exists_branches =  *)
(*                   List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) e.formula_exists_branches;} *)


let trans_formula (e: formula) (arg: 'a) f f_arg f_comb: (formula * 'b) =
  let f_ext_f, f_f, f_heap_f, f_pure, f_memo = f in
  let f_ext_f_arg, f_f_arg, f_heap_f_arg, f_pure_arg, f_memo_arg = f_arg in
  let trans_heap (e: h_formula) (arg: 'a) : (h_formula * 'b) =
    trans_h_formula e arg f_heap_f f_heap_f_arg f_comb
  in
  let trans_pure (e: CP.formula) (arg: 'a) : (CP.formula * 'b) = CP.trans_formula e arg f_pure f_pure_arg f_comb in
  let trans_mix (e: MCP.mix_formula) (arg: 'a) : (MCP.mix_formula * 'b) = 
      MCP.trans_mix_formula e arg (f_memo,f_pure) (f_memo_arg,f_pure_arg) f_comb in
  let trans_branches (branches: (branch_label * CP.formula) list) (arg: 'a) =
    let trans_branch (lbl, e: branch_label * CP.formula) =
      let ne, v = trans_pure e arg in
      ((lbl, ne), f_comb [v])
    in
    let new_branches, vals = List.split (List.map trans_branch branches) in
    (new_branches, f_comb vals)
  in
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
            let new_branches, v3 = trans_branches b.formula_base_branches new_arg in
            let new_base = Base { b with
              formula_base_heap = new_heap;
              formula_base_pure = new_pure;
              formula_base_branches = new_branches; }
            in
            (new_base, f_comb [v1; v2; v3])
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
            let new_branches, v3 = trans_branches e.formula_exists_branches new_arg in
            let new_exists = Exists { e with
              formula_exists_heap = new_heap;
              formula_exists_pure = new_pure;
              formula_exists_branches = new_branches; }
            in
            (new_exists, f_comb [v1; v2; v3])
  in
  trans_f e arg

let rec transform_ext_formula f (e:ext_formula) :ext_formula = 
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
				 formula_ext_base = transform_formula f b.formula_ext_base;
				 formula_ext_continuation = transform_struc_formula f b.formula_ext_continuation;
				}
		| EAssume (v,e,pid)-> EAssume (v,(transform_formula f e),pid)
		| EVariance b -> let (_, _, _, _, f_exp) = f_p_t in EVariance { b with
							formula_var_measures = List.map (fun (expr, bound) -> match bound with
															   | None -> ((CP.transform_exp f_exp expr), None)
															   | Some b_expr -> ((CP.transform_exp f_exp expr), Some (CP.transform_exp f_exp b_expr))) b.formula_var_measures;
							formula_var_escape_clauses = List.map (fun f -> CP.transform_formula f_p_t f) b.formula_var_escape_clauses;
							formula_var_continuation = transform_struc_formula f b.formula_var_continuation;
		  }

and transform_struc_formula f (e:struc_formula)	:struc_formula = 
	List.map (transform_ext_formula f) e

let rec transform_ext_formula_w_perm f (permvar:cperm_var) (e:ext_formula) :ext_formula = 
  let (f_e_f, f_f, f_h_f, f_p_t) = f in
	let r = f_e_f e in 
	match r with
	| Some e1 -> e1
	| None -> match e with
		| ECase c -> 
      let br' = 
        List.map (fun (c1,c2)-> ((CP.transform_formula f_p_t c1),(transform_struc_formula_w_perm f c2 permvar))) c.formula_case_branches in
      ECase {c with formula_case_branches = br';}
		| EBase b -> EBase{b with 
				 formula_ext_base = transform_formula_w_perm f_f b.formula_ext_base permvar;
				 formula_ext_continuation = transform_struc_formula_w_perm f b.formula_ext_continuation permvar;
				}
		| EAssume (v,e,pid)-> EAssume (v,(transform_formula_w_perm f_f e permvar),pid)
		| EVariance b -> let (_, _, _, _, f_exp) = f_p_t in EVariance { b with
							formula_var_measures = List.map (fun (expr, bound) -> match bound with
															   | None -> ((CP.transform_exp f_exp expr), None)
															   | Some b_expr -> ((CP.transform_exp f_exp expr), Some (CP.transform_exp f_exp b_expr))) b.formula_var_measures;
							formula_var_escape_clauses = List.map (fun f -> CP.transform_formula f_p_t f) b.formula_var_escape_clauses;
							formula_var_continuation = transform_struc_formula_w_perm f b.formula_var_continuation permvar;
		  }
    


and transform_struc_formula_w_perm f (e:struc_formula) (permvar:cperm_var) :struc_formula =
	List.map (transform_ext_formula_w_perm f permvar) e

let rec trans_ext_formula (e: ext_formula) (arg: 'a) f f_arg f_comb : (ext_formula * 'b) =
  let f_ext_f, f_f, f_h_formula, f_pure, f_memo = f in
  let f_ext_f_arg, f_f_arg, f_h_f_arg, f_pure_arg, f_memo_arg = f_arg in
  let trans_pure (e: CP.formula) (arg: 'a) : (CP.formula * 'b) =
    CP.trans_formula e arg f_pure f_pure_arg f_comb
  in
  let trans_struc (e: struc_formula) (arg: 'a) : (struc_formula * 'b) =
    trans_struc_formula e arg f f_arg f_comb
  in
  let trans_f (e: formula) (arg: 'a) : (formula * 'b) =
    trans_formula e arg f f_arg f_comb
  in
  let trans_ext (e: ext_formula) (arg: 'a) : (ext_formula * 'b) =
    let r = f_ext_f arg e in
    match r with
    | Some e1 -> e1
    | None ->
        let new_arg = f_ext_f_arg arg e in
        match e with
        | ECase c ->
            let helper (e: CP.formula * struc_formula): (CP.formula * struc_formula) * 'b =
              let e1, e2 = e in
              let ne1, v1 = trans_pure e1 new_arg in
              let ne2, v2 = trans_struc e2 new_arg in
              ((ne1, ne2), f_comb [v1; v2])
            in
            let new_case_branches, vals = List.split (List.map helper c.formula_case_branches) in
            (ECase {c with formula_case_branches = new_case_branches}, f_comb vals)
        | EBase b ->
            let new_base, v1 = trans_f b.formula_ext_base new_arg in
            let new_cont, v2 = trans_struc b.formula_ext_continuation new_arg in
            let new_b = EBase { b with
              formula_ext_base = new_base;
              formula_ext_continuation = new_cont; }
            in
            (new_b, f_comb [v1; v2])
        | EAssume (v, e, pid) ->
            let ne, r = trans_f e new_arg in
            (EAssume (v, ne, pid), f_comb [r])
		| EVariance b ->
			let (_, _, f_pure_exp) = f_pure in
			let (_, _, f_pure_exp_arg) = f_pure_arg in
			let new_escape_clauses, val1 = List.split (List.map (fun f -> trans_pure f new_arg) b.formula_var_escape_clauses) in
			let trans_pure_exp (e: CP.exp) (arg: 'a) : (CP.exp * 'b) = CP.trans_exp e arg f_pure_exp f_pure_exp_arg f_comb in
			let new_measures, val2 = List.split (List.map (fun (expr, bound) -> match bound with
												  | None -> let new_exp, v = (trans_pure_exp expr new_arg) in ((new_exp, None), v)
												  | Some b_expr -> let new_exp, v1 = (trans_pure_exp expr new_arg) in
																   let new_bexp, v2 = (trans_pure_exp b_expr new_arg) in
																   ((new_exp, Some new_bexp), f_comb [v1; v2])) b.formula_var_measures) in
			let new_cont, val3 = trans_struc b.formula_var_continuation new_arg in
			(EVariance { b with
						  formula_var_measures = new_measures;
						  formula_var_escape_clauses = new_escape_clauses
					  }, f_comb (val1@val2@[val3]))
  in
  trans_ext e arg

and trans_struc_formula (e: struc_formula) (arg: 'a) f f_arg f_comb : (struc_formula * 'b) =
  let trans_ext e = trans_ext_formula e arg f f_arg f_comb in
  let ne, vals = List.split (List.map trans_ext e) in
  (ne, f_comb vals)

(* let fold_struc_formula_args (e:struc_formula) (init_a:'a) (f:'a -> h_formula-> 'b option)  *)
(*       (f_args: 'a -> h_formula -> 'a) (comb_f: 'b list->'b) : 'b = *)
(*   let f1 ac e = match (f ac e) with *)
(*     | Some r -> Some (e,r) *)
(*     | None ->  None in *)
(*   snd(trans_struc_formula e init_a f1 f_args comb_f) *)

(***************************************************************************************)
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
	    | Hole _
	    | HTrue
	    | HFalse -> Some e in
  let f_m e = None in
  let f_a e = None in
	let f_b e = Some e in
	let f_e e = Some e in
	let f_p_f e = 
		match e with
		| CP.BForm (b,f_l) -> Some (CP.BForm (b,(n_l_f f_l)))
		| CP.And (e1,e2,l) -> None
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
	    | Hole _
	    | HTrue
	    | HFalse -> Some e in
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

(***************************************************************************************)
(* TODO *)
let rec string_of_list_of_pair_formula ls =
  match ls with
	| [] -> ""
	| (f1,f2)::[] -> (!print_formula f1)^"*"^(!print_formula f2)
	| (f1,f2)::rest -> (!print_formula f1)^"*"^(!print_formula f2)^(string_of_list_of_pair_formula rest)

(* and print_formula = ref(fun (c:formula) -> "Cprinter not initialized") *)
(* and print_struc_formula = ref(fun (c:struc_formula) -> "Cprinter not initialized") *)

and split_struc_formula f0 = split_struc_formula_a f0

and split_struc_formula_debug f0 =
  Gen.Debug.no_1 "split_struc_formula" (!print_struc_formula) (string_of_list_of_pair_formula) split_struc_formula_a f0
(* split the struc_formula into the list of pre/post pairs *)  
and split_struc_formula_a (f0:struc_formula):(formula*formula) list = 
	let rec ext_to_formula (f:ext_formula):(formula*formula) list = match f with
		| ECase b-> 
      let r =  List.concat (List.map (fun (c1,c2)->
				let ll = split_struc_formula_a c2 in
				List.map (fun (d1,d2)-> ((normalize 4 d1 (formula_of_pure_N c1 b.formula_case_pos) b.formula_case_pos),d2)) ll) b.formula_case_branches) in
			List.map (fun (c1,c2)-> ((push_exists b.formula_case_exists c1),(push_exists b.formula_case_exists c2))) r 
		| EBase b-> 
				let ll = split_struc_formula_a b.formula_ext_continuation in
				let e = List.map (fun (c1,c2)-> ((normalize 5 c1 b.formula_ext_base b.formula_ext_pos),c2)) ll in
				let nf = ((*b.formula_ext_explicit_inst@b.formula_ext_implicit_inst@*)b.formula_ext_exists) in
				let e = List.map (fun (c1,c2)-> ((push_exists nf c1),(push_exists nf c2))) e in
				e
		| EAssume (x,b,_)-> [((mkTrue (mkNormalFlow ()) no_pos),b)]
		| EVariance b -> split_struc_formula_a b.formula_var_continuation
			in	
	List.fold_left (fun a c-> a@(ext_to_formula c)) [] f0	

let rec filter_branches (br:formula_label list option) (f0:struc_formula) :struc_formula = 
  let rec filter_helper (br:formula_label list) (f0:struc_formula):struc_formula = 
  let rec filter_formula (f:formula):formula list = match f with
    | Base {formula_base_label = lbl} 
    | Exists {formula_exists_label = lbl} -> (match lbl with
      | None -> Err.report_error { Err.error_loc = no_pos;Err.error_text = "view is unlabeled\n"} 
      | Some lbl -> if (List.mem lbl br) then (Gen.Profiling.inc_counter "total_unfold_disjs";[f]) else (Gen.Profiling.inc_counter "saved_unfolds";[]))
    | Or b -> 
      ((filter_formula b.formula_or_f1)@(filter_formula b.formula_or_f2)) in    
  let filter_ext (f:ext_formula):ext_formula list = match f with
    | EBase b -> 
      if (b.formula_ext_continuation=[]) then 
        let l = filter_formula b.formula_ext_base in
        if (l=[]) then [] else [EBase {b with formula_ext_base = formula_of_disjuncts l}]
      else 
        let l = filter_helper br b.formula_ext_continuation in
        if l=[] then [] else [EBase {b with formula_ext_continuation = l}]
    | ECase b -> 
        let l = List.map (fun (c1,c2)-> (c1,filter_helper br c2)) b.formula_case_branches in
        let l = List.filter (fun (_,c2)->not (c2=[])) l in
        if l=[] then [] else [ECase {b with formula_case_branches = l}]
    | EAssume (x,b,l)-> if (List.mem l br) then [f] else []
	| EVariance b ->
		let l = filter_helper br b.formula_var_continuation in
        if l=[] then [] else [EVariance {b with formula_var_continuation = l}]
  in
  List.concat (List.map filter_ext f0) in
  match br with
    | None -> f0
    | Some l -> filter_helper l f0

let filter_branches (br:formula_label list option) (f0:struc_formula) :struc_formula =
  let pr = !print_struc_formula in
  let pr1 x = match x with
    | None -> "None"
    | Some l -> "Some"^string_of_int(List.length l) in
  Gen.Debug.no_2 "filter_branches" pr1 pr pr (fun _ _ -> filter_branches (br:formula_label list option) (f0:struc_formula)) br f0
  
let rec label_view (f0:struc_formula):struc_formula = 
  let rec label_formula (f:formula):formula = match f with
    | Base b -> Base{b with formula_base_label = Some (fresh_formula_label "")} 
    | Exists b -> Exists{b with formula_exists_label = Some (fresh_formula_label "")} 
    | Or b -> Or{b with formula_or_f1 = label_formula b.formula_or_f1;formula_or_f2 = label_formula b.formula_or_f2;}  in
  let label_ext (f:ext_formula):ext_formula = match f with
    | EBase b -> EBase{b with formula_ext_continuation = label_view b.formula_ext_continuation; formula_ext_base= label_formula b.formula_ext_base}
    | ECase b -> ECase{b with formula_case_branches = List.map (fun (c1,c2)->(c1,label_view c2)) b.formula_case_branches}
    | EAssume (x,b,l)-> EAssume (x,label_formula b,l)
	| EVariance b -> EVariance {b with formula_var_continuation = label_view b.formula_var_continuation}
  in
  List.map label_ext f0
  
  
let rec get_view_branches (f0:struc_formula):(formula * formula_label) list= 
  let rec formula_br (f:formula):(formula * formula_label) list = match f with
    | Base {formula_base_label=lbl} 
    | Exists {formula_exists_label=lbl} -> (match lbl with | None -> [] | Some l -> [(f,l)])
    | Or b -> (formula_br b.formula_or_f1)@(formula_br b.formula_or_f2 )  in
	let rec ext_formula_br (f:ext_formula):(formula * formula_label) list = match f with
		| ECase b-> List.concat 
        (List.map (fun (c1,c2) -> 
          let np = (MCP.memoise_add_pure_N (MCP.mkMTrue b.formula_case_pos) c1) in
          let g_f = mkBase HTrue np TypeTrue (mkTrueFlow ()) [] b.formula_case_pos in
          List.map (fun (d1,d2)-> (normalize_combine g_f d1 no_pos,d2)) (get_view_branches c2)) b.formula_case_branches)
		| EBase b-> 
      let l_e_v =(b.formula_ext_explicit_inst@b.formula_ext_implicit_inst@b.formula_ext_exists) in
      if b.formula_ext_continuation != [] then
        let l = get_view_branches b.formula_ext_continuation in
        List.map (fun (c1,c2)-> 
          let r_f = normalize_combine b.formula_ext_base c1 b.formula_ext_pos in
          ((push_exists l_e_v r_f),c2)) l 
      else 
        let r = formula_br b.formula_ext_base in
        List.map (fun (c1,c2) -> ((push_exists l_e_v c1),c2) ) r 
		| EAssume (_,b,_)-> []
		| EVariance b -> get_view_branches b.formula_var_continuation
	in	
  List.concat (List.map ext_formula_br f0)

let get_view_branches (f0:struc_formula):(formula * formula_label) list=
  let rec add_label f l = match f with
    | Base b -> Base { b with formula_base_label = Some l}
    | Exists b -> Exists  {b with formula_exists_label = Some l}
    | Or b -> f in
(* Or { b with formula_or_f1 = add_label b.formula_or_f1 l; *)
(*                          formula_or_f2 = add_label b.formula_or_f2 l} in *)
  let res = get_view_branches f0 in
  List.map (fun (f,lbl) -> ((add_label f lbl),lbl)) res
 

let mkEBase (pf:CP.formula) loc : ext_formula =
  EBase	{
	formula_ext_explicit_inst = [];
	formula_ext_implicit_inst = [];
	formula_ext_exists = [];
	(*formula_ext_base = mkBase HTrue (MCP.OnePF (pf)) TypeTrue (mkTrueFlow ()) [("",pf)] loc;*)
	formula_ext_base = mkBase HTrue (MCP.OnePF (pf)) TypeTrue (mkTrueFlow ()) [] loc;
	  (*Base {
		formula_base_heap = HTrue;
		formula_base_pure = MCP.OnePF (pf);
		formula_base_type = TypeTrue;
		formula_base_flow = mkTrueFlow ();
		formula_base_branches = [("",pf)];
		formula_base_label = None;
		formula_base_pos = loc;
	};*)
	formula_ext_continuation = [];
	formula_ext_pos = loc;
  }	
  
and propagate_imm_struc_formula e =
  let f_e_f e = None  in
  let f_f e = None in
  let f_h_f f = Some (propagate_imm_h_formula f true) in
  let f_p_t1 e = Some e in
  let f_p_t2 e = Some e in
  let f_p_t3 e = Some e in
  let f_p_t4 e = Some e in
  let f_p_t5 e = Some e in
  let f=(f_e_f,f_f,f_h_f,(f_p_t1,f_p_t2,f_p_t3,f_p_t4,f_p_t5)) in
    transform_struc_formula f e

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
    transform_struc_formula_w_perm f e permvar

let propagate_perm_struc_formula e (permvar:cperm_var)=
  Gen.Debug.no_2 "propagate_perm_struc_formula" 
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
    transform_struc_formula_w_perm f e permvar

let propagate_perm_struc_formula e (permvar:cperm_var)=
  Gen.Debug.no_2 "propagate_perm_struc_formula" 
      !print_struc_formula !print_spec_var !print_struc_formula 
      propagate_perm_struc_formula_x  e permvar

(***************************************************************************************)
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


(***************************************************************************************)
(*used by musterr.reset_original_es*)
let reset_original (f : formula) : formula = add_original f true 

(***************************************************************************************)
let is_no_heap_h_formula (e : h_formula) : bool =
  let f x = match x with
	  | DataNode _
	  | ViewNode _ -> Some false
	  | _ -> None
  in
  fold_h_formula e f (List.for_all (fun x -> x))

let is_no_heap_ext_formula (e : ext_formula) : bool = 
  let f_ext_f _ _ = None in
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
  let f = (f_ext_f, f_f, f_h_formula, f_pure, f_memo) in
    snd(trans_ext_formula e false f f_arg (List.for_all (fun x -> x)))

let is_no_heap_ext_formula (e : ext_formula) : bool = 
  let pr = !print_ext_formula in
  Gen.Debug.no_1 "is_no_heap_ext_formula" pr string_of_bool is_no_heap_ext_formula e

(***************************************************************************************)
(*used by musterr.extr_lhs_b*)
let extr_rhs_b (e:formula) =
  let h1, p1, fl1, br1, t1 = split_components e in
  let b1 = { formula_base_heap = h1;
  formula_base_pure = p1;
  formula_base_type = t1;
  formula_base_branches = br1;
  formula_base_flow = fl1;
  formula_base_label = None;
  formula_base_pos = no_pos } in
  b1

(***************************************************************************************)
(** An Hoa : SECTION SIMPLIFY FORMULAE AND CONTEXT **)
(*used by musterr.simplify_context*)
let rec simplify_formula (f : formula) (bv : CP.spec_var list) =
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

(***************************************************************************************)
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
	(* let _ = print_endline ("[merge_partial_h_formula] input = { " ^ (!print_h_formula f) ^ " }") in *)
	let sc = split_star_h f in
	(* let _ = print_endline ("[merge_partial_h_formula] split separation conjunction = { " ^ (String.concat " ; " (List.map !print_h_formula sc)) ^ " }") in *)
	let dns,vns = List.partition is_data sc in
	(* let _ = print_endline ("[merge_partial_h_formula] data nodes = " ^ (string_of_set !print_h_formula dns)) in *)
	(* let _ = print_endline ("[merge_partial_h_formula] other nodes = " ^ (string_of_set !print_h_formula vns)) in *)
	(* Collect the data pointers *)
	let dnrootptrs = List.map get_ptr_from_data dns in
	let dnrootptrs = Gen.BList.remove_dups_eq CP.eq_spec_var dnrootptrs in
	(* Partition the data nodes into groups of same pointer *)
	let dnodespart = List.map (fun x -> List.filter (fun y -> CP.eq_spec_var (get_ptr_from_data y) x) dns) dnrootptrs in
	(* let _ = print_endline ("[merge_partial_h_formula] grouped data nodes = " ^ (string_of_set (fun x -> string_of_set !print_h_formula x) dnodespart)) in *)
	(* Merge the data nodes in each group *)
	let merged_data_nodes = List.map merge_data_nodes_common_ptr dnodespart in
	(* let _ = print_endline ("[merge_partial_h_formula] merged data nodes = " ^ (string_of_set !print_h_formula merged_data_nodes)) in *)
	(* Combine the parts to get the result *)
	let f = combine_star_h (List.append merged_data_nodes vns) in
		f


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
	| [] -> HTrue
	| h::t -> mkStarH h (combine_star_h t) no_pos


(**
 * An Hoa : Merge a list of data nodes with a common root pointer into either
 *          a single data node or HFalse if there is a clash (and HTrue if
 *          we are merging nothing. This case SHOULD NOT happen.)
 **)
and merge_data_nodes_common_ptr dns = 
	List.fold_left merge_two_nodes HTrue dns

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
							let is_hole_specvar sv = 
								let svname = CP.name_of_spec_var sv in
									svname.[0] = '#' in
							(* [Internal] Select the non-hole spec_var. *)
							let combine_vars sv1 sv2 =
								if (is_hole_specvar sv1) then (sv2,true) 
								else if (is_hole_specvar sv2) then (sv1,true)
								else (sv1,false)
							in
							let args, not_clashes = List.split (List.map2 combine_vars args1 args2) in
							let not_clashed = List.for_all (fun x -> x) not_clashes in
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
			| HTrue -> dn1
			| HFalse -> HFalse
			| _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = ("[merge_two_nodes] Expect either HTrue or a DataNode but get " ^ (!print_h_formula dn2))} )
	| HTrue -> dn2
	| HFalse -> HFalse
	| _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = ("[merge_two_nodes] Expect either HTrue or a DataNode but get " ^ (!print_h_formula dn1)) }


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
      | Hole _ | HTrue | HFalse -> f in
  let rec h_f f = match f with
    | Or b -> Or {b with formula_or_f1 = h_f b.formula_or_f1; formula_or_f2 = h_f b.formula_or_f2; }
    | Base b-> Base {b with formula_base_heap = h_h b.formula_base_heap; }
    | Exists b-> Exists {b with formula_exists_heap = h_h b.formula_exists_heap; } in
  let rec h_struc f =
    let h_ext f = match f with
       | ECase b -> ECase{b with
              formula_case_branches = List.map (fun (c1,c2)-> (c1,h_struc c2)) b.formula_case_branches}
       | EBase b -> EBase{b with
            formula_ext_base = h_f b.formula_ext_base;
            formula_ext_continuation = h_struc b.formula_ext_continuation}
       | EAssume _
       | EVariance _ -> failwith "marh_derv_self: not expecting assume or variance\n" in
    List.map h_ext f in
  (h_struc f)


let rec push_case_f pf sf =
  let helper f = match f with
    | ECase f -> ECase {f with formula_case_branches = List.map (fun (c1,c2)-> (CP.mkAnd c1 pf no_pos, c2)) f.formula_case_branches}
    | EBase f -> EBase {f with formula_ext_continuation = push_case_f pf f.formula_ext_continuation}
    | EVariance v -> EVariance {v with formula_var_continuation = push_case_f pf v.formula_var_continuation}
    | EAssume _ -> f
  in
  List.map helper sf

(*********UNUSED MODULE: All methods are obsolete and should be removed******************)
module CFORMULA_UNUSED=
 struct
(***************************************************************************************)
(*unused - should be removed*)
let mk_empty_frame () : (h_formula * int ) =
  let hole_id = fresh_int () in
    (Hole(hole_id), hole_id)

(*unused - should be removed*)
let rec add_post post f = List.map (fun c-> match c with
  | EBase b ->
      let fec = if (List.length b.formula_ext_continuation)>0 then
                  add_post post b.formula_ext_continuation
                else
                  let (svs,pf,(i_lbl,s_lbl)) = post in
                  [EAssume (svs,pf,(fresh_formula_label s_lbl))] in
    EBase{b with formula_ext_continuation = fec}
  | ECase b ->
      let fcb1 = List.map (fun (c1,c2)->
          if (List.length c2)>0 then
          (c1,(add_post post c2))
        else
          let (svs,pf,(i_lbl,s_lbl)) = post in
          (c1,[EAssume (svs,pf,(fresh_formula_label s_lbl))])) b.formula_case_branches  in
      ECase {b with formula_case_branches  = fcb1;}
  | EAssume _ -> Err.report_error {Err.error_loc = no_pos; Err.error_text = "add post found an existing post\n"}
  | EVariance b ->
	  let fec = if (List.length b.formula_var_continuation)>0 then
                  add_post post b.formula_var_continuation
                else
                  let (svs,pf,(i_lbl,s_lbl)) = post in
                  [EAssume (svs,pf,(fresh_formula_label s_lbl))] in
		EVariance {b with formula_var_continuation = fec}
) f

 end;;
(********************END of IMPLEMENTATION of UNSED*********************)
