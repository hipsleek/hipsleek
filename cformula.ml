(*
  Created 21-Feb-2006

  Formula
*)

open Globals
open Gen

module Err = Error
module CP = Cpure
module MCP = Mcpure

type typed_ident = (typ * ident)

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
             (* ref parameters & straddling variables *)
  | EAssume of (((Cpure.spec_var list) * (Cpure.spec_var list)) *formula* formula_label)
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
                        h_formula_data_imm : bool;
                        h_formula_data_arguments : CP.spec_var list;
                        h_formula_data_label : formula_label option;
                        h_formula_data_remaining_branches :  (formula_label list) option;
                        h_formula_data_pruning_conditions :  (CP.b_formula * formula_label list ) list;
                        h_formula_data_pos : loc }

and h_formula_view = {  h_formula_view_node : CP.spec_var;
                        h_formula_view_name : ident;
                        h_formula_view_imm : bool;
                        h_formula_view_arguments : CP.spec_var list;
                        h_formula_view_modes : mode list;
                        h_formula_view_coercible : bool;
                        (* if this view is generated by a coercion from another view c, 
                           then c is in h_formula_view_origins. Used to avoid loopy coercions *)
                        h_formula_view_origins : ident list;
                        h_formula_view_original : bool;
                        h_formula_view_unfold_num : int; (* to prevent infinite unfolding *)
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

let print_formula = ref(fun (c:formula) -> "printer not initialized")
let print_h_formula = ref(fun (c:h_formula) -> "printer not initialized")
let print_ident_list = ref(fun (c:ident list) -> "printer not initialized")
let print_svl = ref(fun (c:CP.spec_var list) -> "printer not initialized")
let print_sv = ref(fun (c:CP.spec_var) -> "printer not initialized")
let print_struc_formula = ref(fun (c:struc_formula) -> "printer not initialized")
let print_ext_formula = ref(fun (c:ext_formula) -> "printer not initialized")
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
      formula_base_branches = br;} -> (h,p,t,fl,br) 

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

and mkNormalFlow () = { formula_flow_interval = !n_flow_int; formula_flow_link = None;}

and formula_of_mix_formula (p:MCP.mix_formula) (pos:loc) :formula= mkBase HTrue p TypeTrue (mkTrueFlow ()) [] pos

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

          
and isStrictConstTrue f = match f with
  | Exists ({ formula_exists_heap = HTrue;
    formula_exists_pure = p;
    formula_exists_branches = br; 
    formula_exists_flow = fl; })
  | Base ({formula_base_heap = HTrue;
    formula_base_pure = p;
    formula_base_branches = br;
    formula_base_flow = fl;}) -> 
        MCP.isConstMTrue p && (List.filter (fun (_,f) -> not (CP.isConstTrue f)) br = [])&&(is_true_flow fl.formula_flow_interval)
	        (* don't need to care about formula_base_type  *)
  | _ -> false
        
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
and non_overlapping (n1,n2) (p1,p2) : bool = n1>p2 || p1>n2
  
and overlapping n p : bool = not(non_overlapping n p)
and intersect_flow (n1,n2)(p1,p2) : (int*int)= ((if (n1<p1) then p1 else n1),(if (n2<p2) then n2 else p2))

and is_false_flow (p1,p2) :bool = (p2==0)&&(p1==0)
and is_true_flow p :bool = (equal_flow_interval !Globals.n_flow_int p)
  
and equal_flow_interval (n1,n2) (p1,p2) : bool = (n1==p1)&&(n2==p2) 

(*first subsumes the second*)
and subsume_flow (n1,n2)(p1,p2) : bool = if (is_false_flow (p1,p2)) then true else (n1<=p1)&&(p2<=n2) 

and overlap_flow t1 t2 : bool = (subsume_flow t1 t2) || (subsume_flow t2 t1)

and subtract_flow (n1,n2) (p1,p2)  : (nflow list) = 
  if n1<p1 then (n1,p1-1)::(subtract_flow (p1,n2) (p1,p2))
  else if n2>p2 then [(p2+1,n2)]
  else []

and disjoint_flow t1 t2 : bool = not(overlap_flow t1 t2) 

and subsume_flow_f (n1,n2) f :bool = subsume_flow (n1,n2) f.formula_flow_interval

and subsume_flow_ff f1 f2 :bool = subsume_flow f1.formula_flow_interval f2.formula_flow_interval

and get_flow_from_stack c l pos = 
  try
	let r = List.find (fun h-> ((String.compare h.formula_store_name c)==0)) l in
	r.formula_store_value
  with Not_found -> Err.report_error { 
	  Err.error_loc = pos;
	  Err.error_text = "the flow var stack \n"^
		  (String.concat " " (List.map (fun h-> (h.formula_store_name^"= "^
			  (let rr = h.formula_store_value.formula_flow_interval in
			  (string_of_int (fst rr))^(string_of_int (snd rr)))^" ")) l))^
		  "\ndoes not contain "^c}

and set_flow_in_formula_override (n:flow_formula) (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow = n}
  | Exists b-> Exists {b with formula_exists_flow = n}
  | Or b-> Or {formula_or_f1 = set_flow_in_formula_override n b.formula_or_f1;
	formula_or_f2 = set_flow_in_formula_override n b.formula_or_f2;
	formula_or_pos = b.formula_or_pos}
		
and set_flow_in_formula (n:flow_formula) (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow = if (subsume_flow_f !n_flow_int b.formula_base_flow) then n else b.formula_base_flow}
  | Exists b-> Exists {b with formula_exists_flow = if (subsume_flow_f !n_flow_int b.formula_exists_flow) then n else b.formula_exists_flow}
  | Or b-> Or {formula_or_f1 = set_flow_in_formula_override n b.formula_or_f1;
	formula_or_f2 = set_flow_in_formula_override n b.formula_or_f2;
	formula_or_pos = b.formula_or_pos}

		
and set_flow_to_link_f flow_store f pos = match f with
  | Base b-> Base {b with formula_base_flow = 
			if (equal_flow_interval b.formula_base_flow.formula_flow_interval false_flow_int) then b.formula_base_flow
			else
			  if (subsume_flow !n_flow_int b.formula_base_flow.formula_flow_interval ) then
				match b.formula_base_flow.formula_flow_link with
				  | None -> Error.report_error { Error.error_loc = pos;Error.error_text = "simple flow where link required"}
				  | Some v -> get_flow_from_stack v flow_store pos
			  else b.formula_base_flow}
  | Exists b-> Exists {b with formula_exists_flow = 
			if (equal_flow_interval b.formula_exists_flow.formula_flow_interval false_flow_int) then b.formula_exists_flow
			else
			  if (subsume_flow !n_flow_int b.formula_exists_flow.formula_flow_interval ) then 
				match b.formula_exists_flow.formula_flow_link with
				  | None -> Error.report_error { Error.error_loc = pos;Error.error_text = "simple flow where link required"}
				  | Some v -> get_flow_from_stack v flow_store pos
			  else b.formula_exists_flow}
  | Or b-> Or {formula_or_f1 = set_flow_to_link_f flow_store b.formula_or_f1 pos;
	formula_or_f2 = set_flow_to_link_f flow_store b.formula_or_f2 pos;
	formula_or_pos = b.formula_or_pos}

and flow_formula_of_formula (f:formula) (*pos*) : flow_formula = match f with
  | Base b-> b.formula_base_flow
  | Exists b-> b.formula_exists_flow
  | Or b-> 
		let fl1 = flow_formula_of_formula b.formula_or_f1 in
		let fl2 = flow_formula_of_formula b.formula_or_f2 in
		if (equal_flow_interval fl1.formula_flow_interval fl2.formula_flow_interval) then fl1
		else Err.report_error { Err.error_loc = no_pos;
		Err.error_text = "flow_formula_of_formula: disjunctive formula"}

and substitute_flow_in_f to_flow from_flow (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow = 
		    if (equal_flow_interval from_flow b.formula_base_flow.formula_flow_interval) then 
		      {formula_flow_interval = to_flow; formula_flow_link = b.formula_base_flow.formula_flow_link}
		    else b.formula_base_flow;}
  | Exists b-> Exists{b with formula_exists_flow = 
		    if (equal_flow_interval from_flow b.formula_exists_flow.formula_flow_interval) then 
		      {formula_flow_interval = to_flow; formula_flow_link = b.formula_exists_flow.formula_flow_link}
		    else b.formula_exists_flow;}	
  | Or b-> Or {formula_or_f1 = substitute_flow_in_f to_flow from_flow b.formula_or_f1;
	formula_or_f2 = substitute_flow_in_f to_flow from_flow b.formula_or_f2;
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
	  
(*this is used for adding formulas, links will be ignored since the only place where links can appear is in the context, the first one will be kept*)
and mkAndFlow (fl1:flow_formula) (fl2:flow_formula) flow_tr :flow_formula = 
  let int1 = fl1.formula_flow_interval in
  let int2 = fl2.formula_flow_interval in
  let r = if (is_false_flow int1) then fl1
  else if (is_false_flow int2) then fl2
  else match flow_tr with
	| Flow_replace -> 
		  {	formula_flow_interval = int2;
		  formula_flow_link = match (fl1.formula_flow_link,fl2.formula_flow_link)with
			| None,None -> None
			| Some s,None-> Some s
			| None, Some s -> Some s
			| _ ->  Err.report_error { Err.error_loc = no_pos; Err.error_text = "mkAndFlow: can not and two flows with two links"};}
	| Flow_combine ->
		  if (overlapping int1 int2) then 
			{	formula_flow_interval = intersect_flow int1 int2;
			formula_flow_link = match (fl1.formula_flow_link,fl2.formula_flow_link)with
			  | None,None -> None
			  | Some s,None-> Some s
			  | None, Some s -> Some s
			  | _ ->  Err.report_error { Err.error_loc = no_pos; Err.error_text = "mkAndFlow: can not and two flows with two links"};}
		  else {formula_flow_interval = false_flow_int; formula_flow_link = None} in
  (*let string_of_flow_formula f c = 
	"{"^f^",("^(string_of_int (fst c.formula_flow_interval))^","^(string_of_int (snd c.formula_flow_interval))^
	")="^(Gen.ExcNumbering.get_closest c.formula_flow_interval)^","^(match c.formula_flow_link with | None -> "" | Some e -> e)^"}" in

	let _ = print_string ("\n"^(string_of_flow_formula "f1 " fl1)^"\n"^
	(string_of_flow_formula "f2 " fl2)^"\n"^
	(string_of_flow_formula "r " r)^"\n") in*)
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
    let r = MCP.merge_mems p f2 true in
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

and mkStar_combine_debug (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
  Gen.Debug.no_2 "mkstar_combine"
      (!print_formula)
      (!print_formula)
      (!print_formula)
      (fun f1 f2 -> mkStar_combine f1 f2 flow_tr pos) f1 f2 
	  
and mkStar_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) = 
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
  | HTrue _ -> true
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
	  h_formula_view_original = false}
      else
	ViewNode {vn with 
	  h_formula_view_origins = origs @ vn.h_formula_view_origins;
	  (* set the view to be derived *)
	  h_formula_view_original = false}
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

and add_origins (f : formula) origs = 
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
	h_formula_data_arguments = vs0}) ->
        (*let vs = List.tl (List.tl vs0) in*)
        let vs = vs0 in
	    if List.mem v vs then vs else v :: vs
  | ViewNode ({h_formula_view_node = v; 
	h_formula_view_arguments = vs}) -> if List.mem v vs then vs else v :: vs
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
  Gen.Debug.no_3 "subst_avoid_capture" !print_svl !print_svl !print_formula !print_formula
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
      

and subst_var_list sst (svs : Cpure.spec_var list) = match svs with
  | [] -> []
  | sv :: rest ->
        let new_vars = subst_var_list sst rest in
        let new_sv = match List.filter (fun st -> fst st = sv) sst with
		  | [(fr, t)] -> t
		  | _ -> sv in
		new_sv :: new_vars

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
	| EAssume (x,b,y)-> 
          (* FISHY HERE since x is not binding vars *)
          (* if (List.mem fr x) then f *)
	      (* else *) EAssume (x, (apply_one s b),y)
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
	| EAssume ((x1,x2),b,y)-> EAssume(((subst_var_list [s] x1,subst_var_list [s] x2)),(apply_one s b),y)
	| EVariance b -> EVariance ({ b with
		  formula_var_measures = List.map (fun (expr, bound) -> match bound with
			| None -> ((CP.e_apply_one s expr), None)
			| Some b_expr -> ((CP.e_apply_one s expr), Some (CP.e_apply_one s b_expr))) b.formula_var_measures;
		  formula_var_escape_clauses = List.map (fun f -> CP.apply_one s f) b.formula_var_escape_clauses;
		  formula_var_continuation = apply_one_struc s b.formula_var_continuation;
	  })
  in	
  List.map helper f

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
		Base ({formula_base_heap = subst_heap sst h; 
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
									formula_exists_heap =  subst_heap sst qh; 
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
and subst_heap sst (f : h_formula) = 
	match f with
  | Star ({h_formula_star_h1 = f1; 
					h_formula_star_h2 = f2; 
					h_formula_star_pos = pos}) -> 
		Star ({h_formula_star_h1 = subst_heap sst f1; 
		h_formula_star_h2 = subst_heap sst f2; 
		h_formula_star_pos = pos})
  | Phase ({h_formula_phase_rd = f1; 
						h_formula_phase_rw = f2; 
						h_formula_phase_pos = pos}) -> 
		Phase ({h_formula_phase_rd = subst_heap sst f1; 
		h_formula_phase_rw = subst_heap sst f2; 
		h_formula_phase_pos = pos})
  | Conj ({h_formula_conj_h1 = f1; 
					h_formula_conj_h2 = f2; 
					h_formula_conj_pos = pos}) -> 
		Conj ({h_formula_conj_h1 = subst_heap sst f1; 
		h_formula_conj_h2 = subst_heap sst f2; 
		h_formula_conj_pos = pos})
  | ViewNode ({h_formula_view_node = x; 
							h_formula_view_name = c; 
							h_formula_view_imm = imm; 
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
							h_formula_view_arguments = List.map (CP.subst_var_par sst) svs;
							h_formula_view_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_subs sst c,c2)) pcond
		}
  | DataNode ({h_formula_data_node = x; 
							h_formula_data_name = c; 
							h_formula_data_imm = imm; 
							h_formula_data_arguments = svs; 
							h_formula_data_label = lbl;
							h_formula_data_remaining_branches = ann;
							h_formula_data_pruning_conditions = pcond;
							h_formula_data_pos = pos}) -> 
		DataNode ({h_formula_data_node = CP.subst_var_par sst x; 
							h_formula_data_name = c; 
							h_formula_data_imm = imm;  
							h_formula_data_arguments = List.map (CP.subst_var_par sst) svs;
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
    h_formula_data_imm = imm; 
	h_formula_data_arguments = svs; 
	h_formula_data_label = lbl;
    h_formula_data_remaining_branches = ann;
    h_formula_data_pruning_conditions = pcond;
	h_formula_data_pos = pos}) -> 
        DataNode ({h_formula_data_node = subst_var s x; 
		h_formula_data_name = c; 
    	h_formula_data_imm = imm;  
		h_formula_data_arguments = List.map (subst_var s) svs;
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
        let eo1 = normalize o11 f2 pos in
        let eo2 = normalize o12 f2 pos in
		mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
		| Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
			  let eo1 = normalize f1 o21 pos in
			  let eo2 = normalize f1 o22 pos in
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
	    
and normalize (f1 : formula) (f2 : formula) (pos : loc) = 
  normalize_keep_flow f1 f2 Flow_combine pos
      (* todo: check if this is ok *)
and normalize_combine (f1 : formula) (f2 : formula) (pos : loc) = normalize_combine_star f1 f2 pos

and normalize_combine_star (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
        let eo1 = normalize_combine_star o11 f2 pos in
        let eo2 = normalize_combine_star o12 f2 pos in
		mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
		| Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
			  let eo1 = normalize_combine_star f1 o21 pos in
			  let eo2 = normalize_combine_star f1 o22 pos in
			  mkOr eo1 eo2 pos
		| _ -> begin
			let rf1 = rename_bound_vars f1 in
			let rf2 = rename_bound_vars f2 in
			let qvars1, base1 = split_quantifiers rf1 in
			let qvars2, base2 = split_quantifiers rf2 in
			let new_base = mkStar_combine base1 base2 Flow_combine pos in
			let new_h, new_p, new_fl, b, new_t = split_components new_base in
			let resform = mkExists (qvars1 @ qvars2) new_h new_p new_t new_fl b pos in (* qvars[1|2] are fresh vars, hence no duplications *)
			resform
		  end
    end

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

and formula_of_disjuncts (f:formula list) : formula= 
  if (f=[]) then (mkTrue (mkTrueFlow()) no_pos)
  else List.fold_left (fun a c-> mkOr a c no_pos) (mkFalse (mkFalseFlow ) no_pos) f

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

and get_var_type v (f: formula): (typ * bool) = 
  let fv_list = fv f in
  let res_list = CP.remove_dups_svl (List.filter (fun c-> ((String.compare v (CP.name_of_spec_var c))==0)) fv_list) in
  match List.length res_list with
	| 0 -> (Void,false)
	| 1 -> (CP.type_of_spec_var (List.hd res_list),true)
	| _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = "could not find a coherent "^v^" type"}

and get_result_type (f: formula): (typ * bool) = get_var_type res f

  
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




 (* context functions *)
	
  
  
(*type formula_cache_no = int
  
type formula_cache_no_list = formula_cache_no list*)

type entail_state = {
  es_formula : formula; (* can be any formula ; 
    !!!!!  make sure that for each change to this formula the es_cache_no_list is update apropriatedly*)
  es_heap : h_formula; (* consumed nodes *)
  es_pure : (MCP.mix_formula * (branch_label * CP.formula) list);
  es_evars : CP.spec_var list;
  (*used by lemmas*)
  es_ivars : CP.spec_var list; (* ivars are the variables to be instantiated (for the universal lemma application)  *)
  (* es_expl_vars : CP.spec_var list; (\* vars to be explicit instantiated *\) *)
  es_ante_evars : CP.spec_var list;
  (* es_must_match : bool; *)
  (*used by late instantiation*)
  es_gen_expl_vars: CP.spec_var list; 
  es_gen_impl_vars: CP.spec_var list; 
  es_unsat_flag : bool; (* true - unsat already performed; false - requires unsat test *)
  es_pp_subst : (CP.spec_var * CP.spec_var) list;
  es_arith_subst : (CP.spec_var * CP.exp) list;
  es_success_pts : (formula_label * formula_label)  list  ;(* successful pt from conseq *)
  es_residue_pts : formula_label  list  ;(* residue pts from antecedent *)
  es_id      : int              ; (* unique +ve id *)
  es_orig_ante   : formula        ;  (* original antecedent formula *) 
  es_orig_conseq : struc_formula ;
  es_path_label : path_trace;
  es_prior_steps : steps; (* prior steps in reverse order *)
  (*es_cache_no_list : formula_cache_no_list;*)
  es_var_measures : CP.exp list;
  es_var_label : int option;
  es_var_ctx_lhs : CP.formula;
  es_var_ctx_rhs : CP.formula;
  es_var_subst : (CP.spec_var * CP.spec_var * ident) list;
  (* for immutability *)
(* INPUT : this is an alias set for the RHS conseq *)
(* to be used by matching strategy for imm *)
  es_rhs_eqset : (CP.spec_var * CP.spec_var) list;
(*  es_frame : (h_formula * int) list; *)
  es_cont : h_formula list;
  es_crt_holes : (h_formula * int) list;
  es_hole_stk : ((h_formula * int) list) list;
  es_aux_xpure_1 : MCP.mix_formula;
(* below are being used as OUTPUTS *)
  es_subst :  (CP.spec_var list *  CP.spec_var list) (* from * to *); 
  es_aux_conseq : CP.formula;
}

and context = 
  | Ctx of entail_state
  | OCtx of (context * context) (* disjunctive context *)
      (*| FailCtx of (fail_context list)*)

and steps = string list

and fail_context = {
  fc_prior_steps : steps; (* prior steps in reverse order *)
  fc_message : string;          (* error message *)
  fc_current_lhs : entail_state;     (* LHS context with success points *)
  fc_orig_conseq : struc_formula;     (* RHS conseq at the point of failure *)
  fc_failure_pts : formula_label list;     (* failure points in conseq *) 
  fc_current_conseq : formula;
}  
    
and fail_type =
  | Basic_Reason of fail_context
  | Trivial_Reason of string
  | Or_Reason of (fail_type * fail_type)
  | And_Reason of (fail_type * fail_type)
  | Continuation of fail_context    
  | Or_Continuation of (fail_type * fail_type)

      
and list_context = 
  | FailCtx of fail_type 
  | SuccCtx of context list
      
and branch_fail = path_trace * fail_type

and branch_ctx =  path_trace * context

and partial_context = (branch_fail list) * (branch_ctx list)  
    (* disjunct of failures and success *)

and esc_stack = ((control_path_id_strict * branch_ctx list) list)

and failesc_context = (branch_fail list) * esc_stack * (branch_ctx list)

and list_partial_context = partial_context list
 
and list_failesc_context = failesc_context list 
    (* conjunct of contexts *)
  
and list_failesc_context_tag = failesc_context Gen.Stackable.tag_list

let fold_context (f:'t -> entail_state -> 't) (a:'t) (c:context) : 't =
  let rec helper a c = match c with
    | Ctx es -> f a es
    | OCtx (c1,c2) -> helper (helper a c1) c2 in
  helper a c

let print_list_context_short = ref(fun (c:list_context) -> "printer not initialized")
let print_context_list_short = ref(fun (c:context list) -> "printer not initialized")
let print_context_short = ref(fun (c:context) -> "printer not initialized")
let print_entail_state = ref(fun (c:entail_state) -> "printer not initialized")


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

let es_simplify (e1:entail_state):entail_state = 
  let hfv0 = h_fv e1.es_heap in
  let pusher f vl = 
    if (vl==[]) then (f,[])
      else
        let h, p , fl , br , t  = split_components f in
        let hfv = (h_fv h)@hfv0 in
        let brfv = br_fv br [] in 
        let rv1 = Gen.BList.difference_eq (CP.eq_spec_var) vl hfv in
        let rvp,rvb = Gen.BList.diff_split_eq (CP.eq_spec_var) rv1 brfv in
        if (rv1==[]) then (f,[])
        else 
          let rp = 
            if (rvp==[]) then p
          else MCP.memo_pure_push_exists rvp p in
          (mkExists rvb h rp t fl br no_pos, [])  in

  let formula_simplify f aev= match f with 
    | Exists e ->
      let vl = e.formula_exists_qvars @ aev in
      pusher f vl
    | Base _ -> pusher f aev
    | Or c-> Err.report_error { Err.error_loc = no_pos; Err.error_text ="unexpected Or formula in es_simplify"} in
  let nf, naev = formula_simplify e1.es_formula e1.es_ante_evars in
  {e1 with es_formula = nf; es_ante_evars =naev}

let es_simplify e1 = 
  let pr  = !print_entail_state in
  Gen.Debug.no_1 "es_simplify" pr pr es_simplify e1
  
let rec context_simplify (c:context):context  = match c with
  | Ctx e -> Ctx ((*es_simplify*) e)
  | OCtx (c1,c2) -> OCtx ((context_simplify c1), (context_simplify c2))
  
let context_list_simplify (l:context list):context list = List.map context_simplify l

let list_context_simplify (l : list_context) : list_context = match l with
  | FailCtx _-> l
  | SuccCtx sc -> SuccCtx (List.map context_simplify sc)

let failesc_context_simplify ((l,a,cs) : failesc_context) : failesc_context = 
        let newcs = List.map (fun (p,c) -> (p,context_simplify c)) cs in
        (l,a,newcs)

let list_failesc_context_simplify (l : list_failesc_context) : list_failesc_context = 
  List.map failesc_context_simplify l



let mk_empty_frame () : (h_formula * int ) = 
  let hole_id = Globals.fresh_int () in
    (Hole(hole_id), hole_id)

let rec empty_es flowt pos = 
	let x = mkTrue flowt pos in
{
  es_formula = x;
  es_heap = HTrue;
  es_pure = (MCP.mkMTrue pos , []);
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
  es_orig_ante = x;
  es_orig_conseq = [mkETrue flowt pos] ;
  es_rhs_eqset = [];
  es_path_label  =[];
  es_prior_steps  = [];
  es_var_measures = [];
  es_var_label = None;
  es_var_ctx_lhs = CP.mkTrue pos;
  es_var_ctx_rhs = CP.mkTrue pos;
  es_var_subst = [];
  (*es_cache_no_list = [];*)
  es_cont = [];
  es_crt_holes = [];
  es_hole_stk = [];
  es_aux_xpure_1 = MCP.mkMTrue pos;
  es_subst = ([], []);
  es_aux_conseq = CP.mkTrue pos;

}

let empty_ctx flowt pos = Ctx (empty_es flowt pos)

let false_ctx flowt pos = 
	let x = mkFalse flowt pos in
	Ctx ({(empty_es flowt pos) with es_formula = x ; es_orig_ante = x; })

and true_ctx flowt pos = Ctx (empty_es flowt pos)

let mkFalse_branch_ctx = ([],false_ctx mkFalseFlow no_pos)

let rec contains_immutable_ctx (ctx : context) : bool =
  match ctx with
    | Ctx(es) -> contains_immutable es.es_formula
    | OCtx(c1, c2) -> (contains_immutable_ctx c1) or (contains_immutable_ctx c2)

(*let isStrictFalseCtx ctx = match ctx with
  | Ctx es -> isStrictConstFalse es.es_formula
  | _ -> false*)

let isAnyFalseCtx ctx = match ctx with
  | Ctx es -> isAnyConstFalse es.es_formula
  | _ -> false  

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

let mkOCtx ctx1 ctx2 pos =
  (*if (isFailCtx ctx1) || (isFailCtx ctx2) then or_fail_ctx ctx1 ctx2
  else*)  (* if isStrictTrueCtx ctx1 || isStrictTrueCtx ctx2 then *)
  (* true_ctx (mkTrueFlow ()) pos *)  (* not much point in checking
                                         for true *)
  (* else *) 
  if isAnyFalseCtx ctx1 then ctx2
  else if isAnyFalseCtx ctx2 then ctx1
  else OCtx (ctx1,ctx2) 

let or_context c1 c2 = mkOCtx c1 c2 no_pos 
  
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
  Gen.Debug.no_2 "or_context_list" pr pr pr (fun _ _ -> or_context_list cl10 cl20) cl10 cl20
  
let mkFailContext msg estate conseq pid pos = {
  fc_prior_steps = estate.es_prior_steps ;
  fc_message = msg ;
  fc_current_lhs = estate;
  fc_orig_conseq = estate.es_orig_conseq;
  fc_failure_pts = (match pid with | Some s-> [s] | _ -> []);
  fc_current_conseq = conseq;
}   
let mkFailCtx_in (ft:fail_type) = FailCtx ft

let mk_fail_partial_context_label (ft:fail_type) (lab:path_trace) : (partial_context) = ([(lab,ft)], []) 

(* let mk_partial_context (c:context) : (partial_context) = ([], [ ([], c) ] )  *)

let mk_partial_context (c:context) (lab:path_trace) : (partial_context) = ([], [ (lab, c) ] ) 
let mk_failesc_context (c:context) (lab:path_trace) : (failesc_context) = ([], [],[ (lab, c) ] ) 

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
  
  
  (*context set union*)

let is_cont t = 
  match t with
    | Continuation _ -> true
    | Or_Continuation _ -> true
    | _ -> false

let isFailCtx cl = match cl with 
	| FailCtx _ -> true
	| SuccCtx _ -> false

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
	    FailCtx (Or_Reason (t1,t2))  
  | FailCtx t1 ,SuccCtx t2 -> SuccCtx (simplify t2)
  | SuccCtx t1 ,FailCtx t2 -> SuccCtx (simplify t1)
  | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (simplify(t1@t2))

let list_context_union c1 c2 =
  let pr = !print_list_context_short in
  Gen.Debug.no_2_opt (fun _ -> not(isFailCtx c1 ||  isFailCtx c2) )  "list_context_union" 
      pr pr pr
      list_context_union_x c1 c2 

let rec union_context_left c_l = match (List.length c_l) with
  | 0 ->  Err.report_error {Err.error_loc = no_pos;  
              Err.error_text = "folding empty context list \n"}
  | 1 -> (List.hd c_l)
  | _ ->  List.fold_left list_context_union (List.hd c_l) (List.tl c_l)
    (* match a,c with *)
    (*  | FailCtx t1 ,FailCtx t2 ->  *)
	(*  if ((is_cont t1) && not(is_cont t2)) *)
	(*  then FailCtx(t1) *)
	(*  else *)
	(*    if ((is_cont t2) && not(is_cont t1)) *)
	(*    then FailCtx(t2) *)
	(*    else *)
	(*      if (is_cont t1) && (is_cont t2) then *)
	(*        FailCtx (Or_Continuation (t1,t2))   *)
	(*      else *)
	(*        FailCtx (Or_Reason (t1,t2))   *)
    (*  | FailCtx t1,SuccCtx t2 -> SuccCtx t2 *)
    (*  | SuccCtx t1,FailCtx t2 -> SuccCtx t1 *)
    (*  | SuccCtx t1,SuccCtx t2 -> SuccCtx (t1@t2)) (List.hd c_l) (List.tl c_l) *)

and fold_context_left_x c_l = union_context_left c_l 

and fold_context_left c_l = 
  let pr = !print_list_context_short in
  let pr1 x = String.concat "\n" (List.map !print_list_context_short x) in
  Gen.Debug.no_1 "fold_context_left" pr1 pr fold_context_left_x c_l
  
  (*list_context or*)
and or_list_context_x c1 c2 = match c1,c2 with
     | FailCtx t1 ,FailCtx t2 -> FailCtx (And_Reason (t1,t2))
     | FailCtx t1 ,SuccCtx t2 -> FailCtx t1
     | SuccCtx t1 ,FailCtx t2 -> FailCtx t2
     | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (or_context_list t1 t2)
     
and or_list_context c1 c2 = 
  let pr = !print_list_context_short in
  Gen.Debug.no_2 "or_list_context" pr pr pr or_list_context_x c1 c2

(* can remove redundancy here? *)

let isFailPartialCtx (fs,ss) =
  if (Gen.is_empty fs) then false else true

let isFailFailescCtx (fs,es,ss) =
  if (Gen.is_empty fs) then false else true
(* if (Gen.is_empty ss)&&(Gen.is_empty (colapse_esc_stack es)) then true else false *)

let isFailListPartialCtx cl =
  List.for_all isFailPartialCtx cl 

let isFailListFailescCtx cl =
  List.for_all isFailFailescCtx cl 
  
let isSuccessPartialCtx (fs,ss) =
if (Gen.is_empty fs) then true else false

let isSuccessFailescCtx (fs,_,_) =
if (Gen.is_empty fs) then true else false

let isSuccessListPartialCtx cl =
  cl==[] || List.exists isSuccessPartialCtx cl 
  
let isSuccessListFailescCtx cl =
  cl==[] || List.exists isSuccessFailescCtx cl 
  
let isNonFalseListPartialCtx cl = 
 List.exists (fun (_,ss)-> ((List.length ss) >0) && not (List.for_all (fun (_,c) -> isAnyFalseCtx c) ss )) cl


let isNonFalseListFailescCtx cl = 
 List.exists (fun (_,el,ss)-> 
  let ess = (colapse_esc_stack el)@ss in
  ((List.length ess) >0) && not (List.for_all (fun (_,c) -> isAnyFalseCtx c) ess )) cl

(* this should be applied to merging also and be improved *)
let count_false (sl:branch_ctx list) = List.fold_left (fun cnt (_,oc) -> if (isAnyFalseCtx oc) then cnt+1 else cnt) 0 sl

(* let remove_dupl_false (sl:branch_ctx list) =  *)
(*   let nf = count_false sl in *)
(*     if (nf=0) then sl *)
(*     else let n = List.length sl in *)
(*       if (nf=n) then [List.hd(sl)] *)
(*       else (List.filter (fun (_,oc) -> not (isAnyFalseCtx oc) ) sl) *)

let remove_dupl_false (sl:branch_ctx list) = 
  let nl = (List.filter (fun (_,oc) -> not (isAnyFalseCtx oc) ) sl) in
  if nl==[] then 
    if (sl==[]) then [mkFalse_branch_ctx]
    else [List.hd(sl)]
  else nl

let isFalseBranchCtxL (ss:branch_ctx list) = 
   (ss!=[]) && (List.for_all (fun (_,c) -> isAnyFalseCtx c) ss )

let remove_dupl_false (sl:branch_ctx list) = 
  let pr n = string_of_int(List.length n) in
  Gen.Debug.no_1 "remove_dupl_false" pr pr remove_dupl_false sl

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
  Gen.Debug.no_2 "list_partial_context_union" pr pr pr list_partial_context_union l1 l2

let list_failesc_context_union (l1:list_failesc_context) (l2:list_failesc_context):list_failesc_context = 
  let pr x = string_of_int(List.length x) in
  Gen.Debug.no_2 "list_failesc_context_union" pr pr pr list_failesc_context_union l1 l2


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
	    ((l1,And_Reason (b1,b2))::res, l1::pt)
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
    
let merge_failesc_context_or f ((f1,e1,s1):failesc_context) ((f2,e2,s2):failesc_context) : failesc_context =
  let s1 = remove_dupl_false s1 in
  let s2 = remove_dupl_false s2 in
   let (res_f,pt_fail_list) = merge_fail f1 f2 in
  let res_s = merge_success s1 s2 in
  let e1 = match e1 with | [] -> [((0,""),[])] | _-> e1 in
  let e2 = match e2 with | [] -> [((0,""),[])] | _-> e2 in
  let rec merge_esc e1 e2 = 
    match e1,e2 with
    | [],[] -> []
    | (l1,b1)::z1,(l2,b2)::z2 ->
      if not ((fst l1)==(fst l2)) then 
        Err.report_error {Err.error_loc = no_pos;  Err.error_text = "malfunction in merge failesc context lbl mismatch\n"}
      else (l1,merge_success b1 b2)::(merge_esc z1 z2)
    | _ ->   
      print_string ("stack e1: "^ (f e1)^":"^" stack e2: "^(f e2)^":"^"\n");
      Err.report_error {Err.error_loc = no_pos;  Err.error_text = "malfunction in merge failesc context \n"} in  
  let res_e = merge_esc e1 e2 in  
    (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f1,s1))); *)
    (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f2,s2))); *)
    (* print_string ("\nAfter :"^(Cprinter.summary_partial_context (res_f,res_s))); *)
    (res_f,res_e,res_s)


let simple_or pc1 pc2 =  ( (fst pc1)@(fst pc2),  remove_dupl_false ((snd pc1)@(snd pc2)) ) 

let list_partial_context_or_naive (l1:list_partial_context) (l2:list_partial_context) : list_partial_context = 
  List.concat (List.map (fun pc1-> (List.map (simple_or pc1) l2)) l1)
  (* List.concat (List.map (fun pc1-> (List.map (merge_partial_context_or pc1) l2)) l1) *)

let list_partial_context_or (l1:list_partial_context) (l2:list_partial_context) : list_partial_context = 
  (* List.concat (List.map (fun pc1-> (List.map (simple_or pc1) l2)) l1) *)
  List.concat (List.map (fun pc1-> (List.map (fun pc2 -> remove_dupl_false_pc (merge_partial_context_or pc1 pc2)) l2)) l1)

let list_partial_context_or (l1:list_partial_context) (l2:list_partial_context) : list_partial_context = 
  let pr x = string_of_int (List.length x) in 
  Gen.Debug.loop_2_no "list_partial_context_or" pr pr pr list_partial_context_or l1 l2 

let list_failesc_context_or f (l1:list_failesc_context) (l2:list_failesc_context) : list_failesc_context = 
  List.concat (List.map (fun pc1-> (List.map (fun pc2 -> remove_dupl_false_fe (merge_failesc_context_or f pc1 pc2)) l2)) l1)


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
  | OCtx (ctx1, ctx2) -> OCtx((set_context f ctx1), (set_context f ctx2))

and set_list_context f (ctx : list_context) : list_context = match ctx with
  | FailCtx f -> ctx
  | SuccCtx l -> let nl = List.map (set_context f) l in SuccCtx nl

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
	
(*23.10.2008*)

and compose_context_formula_x (ctx : context) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) : context = match ctx with
  | Ctx es -> begin
	  match phi with
		| Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
			let new_c1 = compose_context_formula_x ctx phi1 x flow_tr pos in
			let new_c2 = compose_context_formula_x ctx phi2 x flow_tr pos in
			let res = (mkOCtx new_c1 new_c2 pos ) in
			  res
		| _ -> Ctx {es with es_formula = compose_formula es.es_formula phi x flow_tr pos; es_unsat_flag =false;}
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
  Gen.Debug.no_3 "compose_context_formula" pr1 pr2 pr3 pr1 (fun _ _ _ -> compose_context_formula_x ctx phi x flow_tr pos) ctx phi x

(*TODO: expand simplify_context to normalize by flow type *)
and simplify_context (ctx:context):context = 
	if (allFalseCtx ctx) then (false_ctx (mkFalseFlow) no_pos)
								else  ctx
		
and normalize_es (f : formula) (pos : loc) (result_is_sat:bool) (es : entail_state): context = 
	Ctx {es with es_formula = normalize es.es_formula f pos; es_unsat_flag = es.es_unsat_flag&&result_is_sat} 

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
	  let res = OCtx (nc1, nc2) in
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

and formula_of_context ctx0 = match ctx0 with
  | OCtx (c1, c2) ->
	  let f1 = formula_of_context c1 in
	  let f2 = formula_of_context c2 in
		mkOr f1 f2 no_pos
  | Ctx es -> es.es_formula
  
(* -- added 16.05.2008 *)  
and formula_of_list_context (ctx : list_context) : formula =  match ctx with
  | FailCtx _ -> mkTrue (mkTrueFlow()) no_pos
  | SuccCtx ls -> List.fold_left (fun a c-> mkOr (formula_of_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) ls
(* 16.05.2008 -- *)

and list_formula_of_list_context (ctx : list_context) : list_formula =  match ctx with
  | FailCtx _ -> []
  | SuccCtx ls -> List.map (formula_of_context) ls


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
	
let struc_to_formula f0 :formula = formula_of_disjuncts (fst (List.split (struc_to_formula_gen f0)))
	
let rec split_conjuncts (f:formula):formula list = match f with 
  | Or b -> (split_conjuncts b.formula_or_f1)@(split_conjuncts b.formula_or_f2)
  | _ -> [f] 
  
let list_of_disjuncts f = split_conjuncts f

let join_conjunct_opt l = match l with
  | [] -> None
  | h::t -> Some (List.fold_left (fun a c-> mkOr c a no_pos) h t)
  
let rec struc_to_view_un_s (f0:struc_formula):(formula*formula_label) list = 
  let ifo = (struc_to_formula_gen f0) in
  List.map (fun (c1,c2)-> 
	let c2 = List.fold_left (fun a c2-> match c2 with | None -> a | Some s-> s::a) [] c2 in
	match c2 with
	| [x] -> (c1,x)
	| _ ->  Err.report_error {Err.error_loc = no_pos;  Err.error_text = " mismatch in view labeling \n"} ) ifo


let rec struc_to_formula (f0:struc_formula):formula = 
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
							(struc_to_formula c2)
							b.formula_case_pos
						) 
						b.formula_case_pos
				)
				)
			(mkFalse (mkFalseFlow) b.formula_case_pos) b.formula_case_branches 
			else mkTrue (mkTrueFlow ()) b.formula_case_pos in
			push_exists b.formula_case_exists r 
		| EBase b-> 
				let e = normalize_combine b.formula_ext_base (struc_to_formula b.formula_ext_continuation) b.formula_ext_pos in
				let nf = push_exists (b.formula_ext_explicit_inst@b.formula_ext_implicit_inst@b.formula_ext_exists) e in
				nf
		| EAssume (_,b,_)-> b 
		| EVariance b -> struc_to_formula b.formula_var_continuation (* (mkTrue (mkTrueFlow ()) b.formula_var_pos) *)
			in	
	if (List.length f0)>0 then
		List.fold_left (fun a c-> mkOr a (ext_to_formula c) no_pos) (mkFalse (mkFalseFlow) no_pos)f0
	else mkTrue (mkTrueFlow ()) no_pos	
	
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
	| EAssume ((_,vs),b,t)->  EAssume ((w,vs),((* FISHY *) filter_quantifiers  w b),t)
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> (c1,(plug_ref_vars c2 w))) b.formula_case_branches;}
	| EBase b -> EBase {b with formula_ext_continuation = plug_ref_vars b.formula_ext_continuation w}
	| EVariance b -> EVariance {b with formula_var_continuation = plug_ref_vars b.formula_var_continuation w}
	in 
	List.map helper f0


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
    
	(*
and filter_node (c: context) (p1:spec_var):context = 
	let rec helper_filter (f:formula):formula = match f with
		| Or b -> 
		| Base b ->
		| Exists b ->
	in match c with
		|OCtx (c1,c2) -> OCtx ((filter_node c1 p1),(filter_node c2 p2))
		| Ctx c -> Ctx {c with es_formula = (helper_filter c.es_formula)}
*)

and guard_vars f = Gen.BList.remove_dups_eq (=) (List.fold_left (fun a f-> a@(match f with
	| ECase b-> 
      Gen.BList.remove_dups_eq (=) (List.fold_left (fun a (c1,c2)-> a@(Cpure.fv c1)@(guard_vars c2)) [] b.formula_case_branches)
	| EBase b -> Gen.BList.difference_eq (=) (guard_vars b.formula_ext_continuation) b.formula_ext_exists
	| EAssume b-> []
	| EVariance b -> guard_vars b.formula_var_continuation
	)) [] f)
	
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

and set_es_evars (c:context)(v:Cpure.spec_var list):context = match c with
	| OCtx (c1,c2)-> OCtx ((set_es_evars c1 v),(set_es_evars c2 v))
	| Ctx e -> Ctx {e with es_evars = v}

  
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


and res_retrieve stab clean_res fl =
	if clean_res then  
		try 
			let r = Some (Hashtbl.find stab res) in
			(if (subsume_flow !exc_flow_int (Gen.ExcNumbering.get_hash_of_exc fl)) then (Hashtbl.remove stab res) else ());
			r
		with Not_found -> None
	else None

	
and res_replace stab rl clean_res fl =
	if clean_res&&(subsume_flow !exc_flow_int (Gen.ExcNumbering.get_hash_of_exc fl)) then 
		((Hashtbl.remove stab res);
		match rl with 
			| None -> () 
			| Some e-> Hashtbl.add stab res e) 
	else ()
	
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

let rec transform_formula f (e:formula):formula =
	let (_, f_f, f_h_f, f_p_t) = f in
	let r =  f_f e in 
	match r with
	| Some e1 -> e1
	| None  -> match e with	 
		| Base b -> 
      Base{b with 
              formula_base_heap = transform_h_formula f_h_f b.formula_base_heap;
              formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure;
              formula_base_branches =  List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) b.formula_base_branches;}
		| Or o -> Or {o with 
                    formula_or_f1 = transform_formula f o.formula_or_f1;
                    formula_or_f2 = transform_formula f o.formula_or_f2;}
		| Exists e -> 
      Exists {e with
                formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap;
                formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure;
                formula_exists_branches = 
                  List.map (fun (c1,c2) -> (c1, (CP.transform_formula f_p_t c2))) e.formula_exists_branches;}


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

let rec transform_context f (c:context):context = 
	match c with
	| Ctx e -> (f e)
	| OCtx (c1,c2) -> mkOCtx (transform_context f c1)(transform_context f c2) no_pos
		
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
    | Trivial_Reason s -> c
    | Basic_Reason br -> Basic_Reason (f br)
    | Continuation br -> Continuation (f br)
    | Or_Reason (ft1,ft2) -> Or_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
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
    | Trivial_Reason br -> f c []
    | Basic_Reason br -> f c []
    | Continuation br -> f c []
    | Or_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
    | Or_Continuation (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
    | And_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
    
(*let rec fold_list_context f (c:list_context) = 
  let f_f,f_c = f in
  match c with
    | FailCtx fc -> fold_fail_context f_f fc
    | SuccCtx sc -> List.map (fold_context f_c) sc*)
    
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
  transform_list_context ((fun es -> Ctx{es with es_formula = substitute_flow_in_f !n_flow_int !ret_flow_int es.es_formula;})
    ,(fun c->c)) ctx_list

and change_ret_flow_partial_ctx ctx_list = 
  transform_list_partial_context ((fun es -> Ctx{es with es_formula = substitute_flow_in_f !n_flow_int !ret_flow_int es.es_formula;})
    ,(fun c->c)) ctx_list
    
and change_ret_flow_failesc_ctx ctx_list = 
  transform_list_failesc_context 
    (idf,idf,(fun es -> Ctx{es with es_formula = substitute_flow_in_f !n_flow_int !ret_flow_int es.es_formula;})) ctx_list
    
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
    if !Globals.max_renaming then transform_list_partial_context ((normalize_es f pos b),(fun c->c)) ctx
      else transform_list_partial_context ((normalize_clash_es f pos b),(fun c->c)) ctx
let normalize_max_renaming_list_failesc_context f pos b ctx = 
    if !Globals.max_renaming then transform_list_failesc_context (idf,idf,(normalize_es f pos b)) ctx
      else transform_list_failesc_context (idf,idf,(normalize_clash_es f pos b)) ctx
let normalize_max_renaming_list_failesc_context f pos b ctx =
  Gen.Profiling.do_2 "normalize_max_renaming_list_failesc_context" (normalize_max_renaming_list_failesc_context f pos) b ctx
      
let normalize_max_renaming f pos b ctx = 
  if !Globals.max_renaming then transform_list_context ((normalize_es f pos b),(fun c->c)) ctx
  else transform_list_context ((normalize_clash_es f pos b),(fun c->c)) ctx

let normalize_max_renaming_s f pos b ctx = 
  if !Globals.max_renaming then transform_context (normalize_es f pos b) ctx
  else transform_context (normalize_clash_es f pos b) ctx

  
(*
  to be used in the type-checker. After every entailment, the history of consumed nodes
  must be cleared.
*)
let clear_entailment_history_es (es :entail_state) :context = 
  Ctx {(empty_es (mkTrueFlow ()) no_pos) with es_formula =
      es.es_formula; es_path_label = es.es_path_label;es_prior_steps= es.es_prior_steps;es_var_measures = es.es_var_measures; es_var_label = es.es_var_label;es_var_ctx_lhs = es.es_var_ctx_lhs;es_var_ctx_rhs = es.es_var_ctx_rhs} 
let clear_entailment_history (ctx : context) : context =  
  transform_context clear_entailment_history_es ctx
  
let clear_entailment_history_list (ctx : list_context) : list_context = 
  transform_list_context (clear_entailment_history_es,(fun c->c)) ctx 

let clear_entailment_history_partial_list (ctx : list_partial_context) : list_partial_context = 
  transform_list_partial_context (clear_entailment_history_es,(fun c->c)) ctx 

let clear_entailment_history_failesc_list (ctx : list_failesc_context) : list_failesc_context = 
  transform_list_failesc_context (idf,idf,clear_entailment_history_es) ctx 
  
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

(* convert entail state to ctx with nf flow and quantify res
   variable *)
(* need also a binding to catch handler's bound var *)
let conv_elim_res (cvar:typed_ident option)  (c:entail_state)
    (elim_ex_fn: context -> context) = 
  let rest, b_rez = get_result_type c.es_formula in
  let ctx = (Ctx {c with es_formula = 
      (substitute_flow_into_f !n_flow_int c.es_formula) } )  in
  match cvar with
    | None -> ctx
    | Some (cvt,cvn) ->        
        if not(b_rez) then ctx
        else begin
      	  let vsv_f = formula_of_pure_N (CP.mkEqVar (CP.SpecVar (rest, cvn, Primed)) (CP.mkRes rest) no_pos) no_pos in
      	  let ctx1 = normalize_max_renaming_s vsv_f no_pos true ctx in
      	  let ctx1 = push_exists_context [CP.mkRes rest] ctx1 in
      	  if !Globals.elim_exists then elim_ex_fn ctx1 else  ctx1
        end
          
(* convert entail state to ctx with nf flow *)
let conv (c:entail_state) (nf:nflow) = (Ctx {c 
with es_formula = 
(substitute_flow_into_f nf c.es_formula) } )   

let conv_lst (c:entail_state) (nf_lst:nflow list) = 
  match nf_lst with
    | [] -> None
    | x::xs -> Some (List.fold_left (fun acc_ctx y -> OCtx (conv c y,acc_ctx)) (conv c x)  xs)

let rec splitter (c:context) 
    (nf:nflow) (cvar:typed_ident option)  (elim_ex_fn: context -> context)
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
	        let t_escape_lst = subtract_flow ff.formula_flow_interval nf in
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

let splitter_failesc_context  (nf:nflow) (cvar:typed_ident option) (fn_esc:context -> context)   
	(elim_ex_fn: context -> context) (pl :list_failesc_context) : list_failesc_context = 
   List.map (fun (fl,el,sl)->
						let r = List.map (fun (p,c)-> splitter_wrapper p c nf cvar elim_ex_fn fn_esc ) sl in
						let re,rs = List.split r in
						(fl,push_esc_elem el (List.concat re),(List.concat rs))) pl 
	
let splitter_partial_context  (nf:nflow) (cvar:typed_ident option)   
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
    | OCtx _ -> print_string "Warning : OCtx with get_prior_steps "; [] ;;

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
  Gen.Debug.no_1_num i "add_to_context" pr pr_no (fun _ -> add_to_context c s) c

let add_to_estate (es:entail_state) (s:string) = 
  {es with es_prior_steps = s::es.es_prior_steps; }

let overwrite_estate_with_steps (es:entail_state) (ss:steps) = 
  {es with es_prior_steps = ss; }

let add_to_estate_with_steps (es:entail_state) (ss:steps) = 
  {es with es_prior_steps = ss@es.es_prior_steps; }

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
				List.map (fun (d1,d2)-> ((normalize d1 (formula_of_pure_N c1 b.formula_case_pos) b.formula_case_pos),d2)) ll) b.formula_case_branches) in
			List.map (fun (c1,c2)-> ((push_exists b.formula_case_exists c1),(push_exists b.formula_case_exists c2))) r 
		| EBase b-> 
				let ll = split_struc_formula_a b.formula_ext_continuation in
				let e = List.map (fun (c1,c2)-> ((normalize c1 b.formula_ext_base b.formula_ext_pos),c2)) ll in
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

and add_to_aux_conseq lctx to_aux_conseq pos =
  match lctx with
    | FailCtx _ -> lctx
    | SuccCtx cl ->
      let new_cl = List.map (fun c ->
      (transform_context
    	(fun es ->
    		Ctx{es with
    		    (* add to the aux conseq *)
    		    es_aux_conseq = CP.mkAnd es.es_aux_conseq to_aux_conseq pos;
    		})) c) cl
      in SuccCtx(new_cl)

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
    
and extr_lhs_b (es:entail_state) =
  let e = es.es_formula in
  let h1, p1, fl1, br1, t1 = split_components e in
  let b1 = { formula_base_heap = h1;
  formula_base_pure = p1;
  formula_base_type = t1;
  formula_base_branches = br1;
  formula_base_flow = fl1;
  formula_base_label = None;
  formula_base_pos = no_pos } in
  b1
	
(** An Hoa : simplify a list failesc context **)
let rec simplify_list_failesc_context (ctx : list_failesc_context) (bv : CP.spec_var list) = 
	List.map (fun x -> simplify_failesc_context x bv) ctx
	
(** An Hoa : simplify a failesc context **)
and simplify_failesc_context (ctx : failesc_context) (bv : CP.spec_var list) = 
	match ctx with
		| (brfaillist,escstk,brctxlist) -> 
			let newbrctxlist = List.map (fun x -> simplify_branch_context x bv) brctxlist in
				(brfaillist,escstk,newbrctxlist)
			
(** An Hoa : simplify a branch context **)
and simplify_branch_context (brctx : branch_ctx) (bv : CP.spec_var list) =
	match brctx with
		| (pathtrc, ctx) ->
			let newctx = simplify_context ctx bv in
				(pathtrc, newctx)

(** An Hoa : simplify a context **)
and simplify_context (ctx : context) (bv : CP.spec_var list) = 
	match ctx with
		| Ctx ({ es_formula = esformula;
				  es_heap = esheap;
				  es_pure = espure;
				  es_evars = esevars;
				  es_ivars = esivars;
				  es_ante_evars = esanteevars;
				  es_gen_expl_vars = esgenexplvars; 
				  es_gen_impl_vars = esgenimplvars; 
				  es_unsat_flag = esunsatflag;
				  es_pp_subst = esppsubst;
				  es_arith_subst = esarithsubst;
				  es_success_pts = essuccesspts;
				  es_residue_pts = esresiduepts;
				  es_id = esid;
				  es_orig_ante   = esorigante; 
				  es_orig_conseq = esorigconseq;
				  es_path_label = espathlabel;
				  es_prior_steps = espriorsteps;
				  es_var_measures = esvarmeasures;
				  es_var_label = esvarlabel;
				  es_var_ctx_lhs = esvarctxlhs;
				  es_var_ctx_rhs = esvarctxrhs;
				  es_var_subst = esvarsubst;
				  es_rhs_eqset = esrhseqset;
				  es_cont = escont;
				  es_crt_holes = escrtholes;
				  es_hole_stk = esholestk;
				  es_aux_xpure_1 = esauxxpure1;
				  es_subst = essubst; 
				  es_aux_conseq = esauxconseq;
					} as es) -> 
						let sesfml = simplify_es_formula esformula bv in
							Ctx { es with es_formula = sesfml }
		| OCtx (ctx1, ctx2) -> 
					OCtx (simplify_context ctx1 bv, simplify_context ctx2 bv)

(** An Hoa : simplify a general formula **)
and simplify_es_formula (f : formula) (bv : CP.spec_var list) = 
	(* Print the mix formula for testing purpose *)
	let print_mix_f (f : MCP.mix_formula) = match f with
		| MCP.MemoF mf -> (!MCP.print_mp_f mf)
		| MCP.OnePF pf -> (!CP.print_formula pf)
	in
(*	let freevars = fv f in                        *)
(*	let _ = print_endline (!print_svl freevars) in*)
	match f with
		| Base ({formula_base_heap = heap;
						formula_base_pure = pure;
						formula_base_type = fftype;
	          formula_base_flow = flow;
	          formula_base_branches = branches;
	          formula_base_label = label;
	          formula_base_pos = pos}) -> 
(*			let _ = print_endline (!print_h_formula heap) in*)
(*			let _ = print_endline (print_mix_f pure) in     *)
			let newheap,newpure = simplify_heap_pure heap pure bv in
			Base ({formula_base_heap = newheap;
						formula_base_pure = newpure;
						formula_base_type = fftype;
	          formula_base_flow = flow;
	          formula_base_branches = branches;
	          formula_base_label = label;
	          formula_base_pos = pos})
		| Or ({formula_or_f1 = f1;
	        formula_or_f2 = f2;
	        formula_or_pos = pos}) -> 
			Or ({formula_or_f1 = simplify_es_formula f1 bv;
					formula_or_f2 = simplify_es_formula f2 bv;
					formula_or_pos = pos})
		| Exists ({formula_exists_qvars = qvars;
	            formula_exists_heap = heap;
	            formula_exists_pure = pure;
	            formula_exists_type = ftype;
	            formula_exists_flow = flow;
	            formula_exists_branches = branches;
	            formula_exists_label = label;
	            formula_exists_pos = pos}) ->
(*			let _ = print_endline (!print_h_formula heap) in*)
(*			let _ = print_endline (print_mix_f pure) in     *)
			let newheap,newpure = simplify_heap_pure heap pure bv(*qvars*) in
			Exists ({formula_exists_qvars = qvars;
	            formula_exists_heap = newheap;
	            formula_exists_pure = newpure;
	            formula_exists_type = ftype;
	            formula_exists_flow = flow;
	            formula_exists_branches = branches;
	            formula_exists_label = label;
	            formula_exists_pos = pos})

(** An Hoa : simplify a heap formula with the constraints, bv stores the base variables **)
(** STEP 1 : replace variables that could be replaced by "original variables" **)
(** STEP 2 : remove constraints concerning "unreachable" variables i.e. var without references **)
and simplify_heap_pure (h : h_formula) (p : MCP.mix_formula) (bv : CP.spec_var list) =
	(* Print the base variables *)
(*	let _ = print_string "Specification & procedure base variables = " in*)
(*	let _ = print_endline (!print_svl bv) in                             *)
	(* Free variables in heap part *)
	let heapfv = h_fv h in
(*	let _ = print_string "Heap free variables = " in*)
(*	let _ = print_endline (!print_svl heapfv) in    *)
	(* Free variables in pure constraints *) 
	let purefv = MCP.mfv p in
(*	let _ = print_string "Pure free variables = " in*)
(*	let _ = print_endline (!print_svl purefv) in    *)
	(* Intermediate variables = all constraining variables subtract away the *)
	(* essential ones in heap and base; we try to eliminate them all *)
	let intfv = Gen.BList.difference_eq CP.eq_spec_var purefv heapfv in
	let intfv = Gen.BList.difference_eq CP.eq_spec_var intfv bv in
	let intfv = List.filter CP.is_unprimed intfv in
	let _ = print_string "Intermediate variables = " in
	let _ = print_endline (!print_svl intfv) in
	let nh = ref h in
	
	(** Internal function to process individual memoised group **)
	let process_memoised_group mg =
		let mgfv = mg.MCP.memo_group_fv in 
		let mgas = mg.MCP.memo_group_aset in 
		let mggs = mg.MCP.memo_group_slice in
		let mggc = mg.MCP.memo_group_cons in
		(* Removing intermediate variables : for each intermediate one, find the equality constraints and replace their instances in the heap *)
		(*let _ = print_string "@vars : " in
		let _ = print_endline (Cpure.EMapSV.string_of mgas) in*)
		(* spl stores a list of equal variables, including special vars for constants *)
		let spl = CP.EMapSV.get_elems mgas in
(*		let _ = print_endline (!print_svl spl) in*)
			if (CP.EMapSV.overlap spl bv) then
				let subv = List.fold_left (fun x y ->
					let r = CP.EMapSV.find mgas y in
					let r = if (r != []) then [y] else [] in
					List.append x r) [] bv in
				let subv = List.hd subv in
				let tobereplaced = CP.EMapSV.find_equiv_all subv mgas in
				(* Remove subv *)
				let tobereplaced = List.filter (fun x -> not (CP.eq_spec_var x subv)) tobereplaced in
				(* Primed variables cannot be replaced! *)
				let tobereplaced = List.filter CP.is_unprimed tobereplaced in
				(* Constant cannot be replaced as well! *)
				let tobereplaced = List.filter (fun x -> not (CP.is_const x)) tobereplaced in
				let sst = List.map (fun x -> (x,subv)) tobereplaced in
				(* Replaced variables which we can find the equivalent one in the set of logical variables *)
					nh := subst_heap sst !nh;
				(* We also have to replace the ones in this mg *)
				if (tobereplaced != []) then
					let _ = print_endline ("==> reducible :: replace variables in " ^ (!print_svl tobereplaced) ^ " by " ^ (!print_sv subv)) in
(*					let _ = print_string (!print_h_formula !nh) in*)
					(** Wrong! Only remove the ones that are replaced! 
                     Also, have to do substitution in the formulas as well.
										 Change the list of free variables. **)
(*					let _ = print_string "group slice = " in                                                  *)
(*					let _ = List.map (fun f -> print_endline (!CP.print_formula f)) mggs in                   *)
(*					let _ = print_string "group constraints = " in                                            *)
(*					let _ = List.map (fun c -> print_endline (!CP.print_b_formula c.MCP.memo_formula)) mggc in*)
					{ mg with 
						MCP.memo_group_fv = (Gen.BList.difference_eq CP.eq_spec_var mgfv tobereplaced);
						MCP.memo_group_aset = CP.EMapSV.mkEmpty;
						MCP.memo_group_slice = List.map (fun f -> CP.subst sst f) mggs;
						MCP.memo_group_cons = List.map (fun c -> let f = CP.b_apply_subs sst c.MCP.memo_formula in
																											{ c with MCP.memo_formula = f }) mggc }
				else (* let _ = print_string "==> irreducible.\n" in *) mg
			else (* let _ = print_string "==> irreducible.\n" in *) mg
	in
	(* Now, construct a more compact pure & heap *)
	match p with
		| MCP.MemoF fm -> 
				let aasets = List.map (fun x -> x.MCP.memo_group_aset) fm in
				let nfm = List.map process_memoised_group fm in 
					(!nh, MCP.MemoF nfm)
  	| MCP.OnePF f -> 
			let nf, sst = CP.reduce_pure f bv in
			let nh = subst_heap sst h in
			let np = MCP.OnePF nf in 
			(* Without --eps option, this is always the case. Rearrange the pure & then do replacement. *)
			(nh, np)
