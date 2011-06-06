(*
  Created 19-Feb-2006

  Input formulae
*)

open Globals
module P = Ipure
module IP = Iperm


type struc_formula = ext_formula list

and ext_formula = 
	| ECase of ext_case_formula
	| EBase of ext_base_formula
	| EAssume of (formula*formula_label)(*could be generalized to have a struc_formula type instead of simple formula*)
	| EVariance of ext_variance_formula


and ext_case_formula =
	{
		formula_case_branches : (P.formula * struc_formula ) list;
		formula_case_pos : loc 		
	}

and ext_base_formula =
	{
		 formula_ext_explicit_inst : (ident * primed) list;
		 formula_ext_implicit_inst : (ident * primed) list;
		 formula_ext_exists :  (ident * primed) list;
		 formula_ext_base : formula;
		 formula_ext_continuation : struc_formula;
		 formula_ext_pos : loc
	}
  
and ext_variance_formula =
	{
	    formula_var_label : int option;
		formula_var_measures : (P.exp * (P.exp option)) list;
		formula_var_escape_clauses : P.formula list;
		formula_var_continuation : struc_formula;
		formula_var_pos : loc
	}

and formula =
  | Base of formula_base
  | Exists of formula_exists
  | Or of formula_or

and formula_base = { formula_base_heap : h_formula;
                     formula_base_pure : P.formula;
                     formula_base_flow : flow_formula;
					 formula_base_perm : IP.perm_formula;
                     formula_base_branches : (branch_label * P.formula) list;
                     formula_base_pos : loc }

and formula_exists = { formula_exists_qvars : (ident * primed) list;
                       formula_exists_heap : h_formula;
                       formula_exists_pure : P.formula;
                       formula_exists_flow : flow_formula;
					   formula_exists_perm : IP.perm_formula;
                       formula_exists_branches : (branch_label * P.formula) list;
                       formula_exists_pos : loc }

and flow_formula = constant_flow				   
    
and formula_or = { formula_or_f1 : formula;
		   formula_or_f2 : formula;
		   formula_or_pos : loc }

and h_formula = (* heap formula *)
  | Phase of h_formula_phase
  | Conj of h_formula_conj  
  | Star of h_formula_star
  | HeapNode of h_formula_heap
  | HeapNode2 of h_formula_heap2
	  (* Don't distinguish between view and data node for now, as that requires look up *)
	  (*  | ArrayNode of ((ident * primed) * ident * P.exp list * loc) *)
	  (* pointer * base type * list of dimensions *)
  | HTrue 
  | HFalse
      
(*

  and h_formula = Phase of h_formula_phase
    | HeapNode of h_formula_heap
    | HeapNode2 of h_formula_heap2
	  (* Don't distinguish between view and data node for now, as that requires look up *)
	  (*  | ArrayNode of ((ident * primed) * ident * P.exp list * loc) *)
	  (* pointer * base type * list of dimensions *)
    | HTrue 
    | HFalse


  and h_formula_phase = { h_formula_phase_h1 : h_formula_rd;
    h_formula_phase_h2 : h_formula_rw;
    h_formula_phase_pos : loc 
  }

  and h_formula_rd = 
     RdConj of h_formula_rd_conj
     | RdStar of h_formula_rd_star
     | HRdTrue
     | HRdFalse

  and h_formula_rd_conj = {h_formula_rd_conj_h1 : h_formula_rd;
    h_formula_rd_conj_h2 : h_formula_rd;
    h_formula_rd_conj_pos : loc 
  }
  

  and h_formula_rd_star = {h_formula_rd_star_h1 : h_formula_rd;
    h_formula_rd_star_h2 : h_formula_rd;
    h_formula_rd_star_pos : loc 
  }

  and h_formula_rw = {h_formula_rw_h1 : h_formula_wr;
    h_formula_rw_h2 : h_formula;
    h_formula_rw_pos : loc
  }


  and h_formula_wr = 
     WrStar of h_formula_wr_star
     | HWrTrue
     | HWrFalse

  and h_formula_wr_star = {h_formula_wr_star_h1 : h_formula_wr_star;
    h_formula_wr_star_h2 : h_formula_wr_star;
    h_formula_wr_star_pos : loc
  }

*)
and h_formula_star = { h_formula_star_h1 : h_formula;
		       h_formula_star_h2 : h_formula;
		       h_formula_star_pos : loc }

and h_formula_conj = { h_formula_conj_h1 : h_formula;
		       h_formula_conj_h2 : h_formula;
		       h_formula_conj_pos : loc }

and h_formula_phase = { h_formula_phase_rd : h_formula;
			h_formula_phase_rw : h_formula;
			h_formula_phase_pos : loc }

and h_formula_heap = { h_formula_heap_node : (ident * primed);
		       h_formula_heap_name : ident;
		       h_formula_heap_imm : bool; 
		       h_formula_heap_full : bool;
		       h_formula_heap_with_inv : bool;
		       h_formula_heap_arguments : P.exp list;
		       h_formula_heap_pseudo_data : bool;
		       h_formula_heap_label : formula_label option;
			   h_formula_heap_perm : IP.frac_perm option;
		       h_formula_heap_pos : loc }

and h_formula_heap2 = { h_formula_heap2_node : (ident * primed);
			h_formula_heap2_name : ident;
			h_formula_heap2_imm : bool;
			h_formula_heap2_full : bool;
			h_formula_heap2_with_inv : bool;
			h_formula_heap2_arguments : (ident * P.exp) list;
			h_formula_heap2_pseudo_data : bool;
			h_formula_heap2_label : formula_label option;
			h_formula_heap2_perm : IP.frac_perm option;
			h_formula_heap2_pos : loc }
			
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
	
(* constructors *)

let rec formula_of_heap_1 h pos = mkBase h (P.mkTrue pos) top_flow (IP.mkTrue pos) [] pos

and formula_of_pure_1 p pos = mkBase HTrue p top_flow (IP.mkTrue pos) [] pos

and formula_of_heap_with_flow h f pos = mkBase h (P.mkTrue pos) f (IP.mkTrue pos)  [] pos

and formula_of_pure_with_flow p f fpc pos = mkBase HTrue p f fpc [] pos


and isConstFalse f0 = match f0 with
  | Base f -> begin
	  let h, p, pr = f.formula_base_heap, f.formula_base_pure,f.formula_base_perm in
		match h with
		  | HFalse -> true
		  | _ -> ((P.isConstFalse p)|| (IP.isConstFalse pr))
	end
  | _ -> false

and isConstTrue f0 = match f0 with
  | Base f -> begin
	  let h, p, pr = f.formula_base_heap, f.formula_base_pure, f.formula_base_perm in
		match h with
		  | HTrue -> (P.isConstTrue p)&&(IP.isConstTrue pr)
		  | _ -> false
	end
  | _ -> false

and isEConstFalse f0 = match f0 with
  | [EBase b] -> isConstFalse b.formula_ext_base
  | _ -> false

and isEConstTrue f0 = match f0 with
 	| [EBase b] -> isConstTrue b.formula_ext_base
  | _ -> false

and mkTrue flow pos = Base { formula_base_heap = HTrue;
						formula_base_pure = P.mkTrue pos;
						formula_base_flow = flow;
                        formula_base_branches = [];
						formula_base_perm = IP.mkTrue pos;
						formula_base_pos = pos }

and mkFalse flow pos = Base { formula_base_heap = HFalse;
						 formula_base_pure = P.mkFalse pos;
						 formula_base_flow = flow;
                         formula_base_branches = [];
						 formula_base_perm = IP.mkFalse pos;
						 formula_base_pos = pos }

and mkETrue flow pos = [EBase {
		 formula_ext_explicit_inst = [];
		 formula_ext_implicit_inst = [];
		 formula_ext_exists = [];
		 formula_ext_base = mkTrue flow pos;
		 formula_ext_continuation = [];
		 formula_ext_pos = pos	}]

and mkEFalse flow pos =[EBase {
		 formula_ext_explicit_inst = [];
		 formula_ext_implicit_inst = [];
		 formula_ext_exists = [];
		 formula_ext_base = mkFalse flow pos;
		 formula_ext_continuation = [];
		 formula_ext_pos = pos	}]
																				
and mkEOr f1 f2 pos = 
	if isEConstTrue f1 || isEConstTrue f2 then
	mkETrue top_flow pos
  else if isEConstFalse f1 then f2
  else if isEConstFalse f2 then f1
  else List.rev_append f1 f2

and mkEBase ei ii e b c l= EBase {
						 	formula_ext_explicit_inst = ei;
						 	formula_ext_implicit_inst = ii;
							formula_ext_exists = e;
						 	formula_ext_base = b;				
						 	formula_ext_continuation = c;
						 	formula_ext_pos = l;}
  
and mkOr f1 f2 pos =
  if isConstTrue f1 || isConstTrue f2 then
	mkTrue top_flow pos
  else if isConstFalse f1 then f2
  else if isConstFalse f2 then f1
  else Or { formula_or_f1 = f1;
			formula_or_f2 = f2;
			formula_or_pos = pos }

and mkBase (h : h_formula) (p : P.formula) flow (perm:IP.perm_formula) br pos = match h with
  | HFalse -> mkFalse flow pos
  | _ -> 
	  if P.isConstFalse p then 
		mkFalse flow pos 
	  else if IP.isConstFalse perm then mkFalse flow pos
	  else
		Base { formula_base_heap = h;
			   formula_base_pure = p;
			   formula_base_flow = flow;
			   formula_base_perm = perm;
               formula_base_branches = br;
			   formula_base_pos = pos }

and mkExists (qvars : (ident * primed) list) (h : h_formula) (p : P.formula) flow perm br pos = match h with
  | HFalse -> mkFalse flow pos
  | _ ->
	  if P.isConstFalse p then
		mkFalse flow pos
	  else if IP.isConstFalse perm then mkFalse flow pos
	  else 
		Exists { formula_exists_qvars = qvars;
             formula_exists_heap = h;
             formula_exists_pure = p;
             formula_exists_flow = flow;
			 formula_exists_perm = perm;
             formula_exists_branches = br;
             formula_exists_pos = pos }

and mkStar f1 f2 pos = match f1 with
  | HFalse -> HFalse
  | HTrue -> f2
  | _ -> match f2 with
	  | HFalse -> HFalse
	  | HTrue -> f1
	  | _ -> Star { h_formula_star_h1 = f1;
					h_formula_star_h2 = f2;
					h_formula_star_pos = pos }



and mkConj f1 f2 pos = match f1 with
  | HFalse -> HFalse
  | HTrue -> f2
  | _ -> match f2 with
	  | HFalse -> HFalse
	  | HTrue -> f1
	  | _ -> Conj { h_formula_conj_h1 = f1;
					h_formula_conj_h2 = f2;
					h_formula_conj_pos = pos }



and mkPhase f1 f2 pos = 
  match f1 with
  | HFalse -> HFalse
  | HTrue -> f2
  | _ -> match f2 with
	  | HFalse -> HFalse
	  | HTrue -> f1
	  | _ -> Phase { h_formula_phase_rd = f1;
					h_formula_phase_rw = f2;
					h_formula_phase_pos = pos }

and mkHeapNode c id perm i f inv pd hl ofl l= HeapNode { 
                   h_formula_heap_node = c;
                   h_formula_heap_name = id;
				   h_formula_heap_perm = perm;
                   h_formula_heap_imm = i;
                   h_formula_heap_full = f;
                   h_formula_heap_with_inv = inv;
                   h_formula_heap_pseudo_data = pd;
                   h_formula_heap_arguments = hl;
                   h_formula_heap_label = ofl;
                   h_formula_heap_pos = l }
          
and mkHeapNode2 c id perm i f inv pd ohl ofl l = HeapNode2 { 
                    h_formula_heap2_node = c;
                    h_formula_heap2_name = id;
					h_formula_heap2_perm = perm;
                    h_formula_heap2_imm = i;
                    h_formula_heap2_full = f;
                    h_formula_heap2_with_inv = inv;
                    h_formula_heap2_pseudo_data = pd;
                    h_formula_heap2_arguments = ohl;
                    h_formula_heap2_label = ofl;
                    h_formula_heap2_pos = l}
          
and pos_of_formula f0 = match f0 with
  | Base f -> f.formula_base_pos
  | Or f -> f.formula_or_pos
  | Exists f -> f.formula_exists_pos
	
and pos_of_struc_formula f0  = 
if (List.length f0)==0 then no_pos
	else match (List.hd f0) with 
	| ECase b -> b.formula_case_pos
	| EBase b -> b.formula_ext_pos
	| EAssume (b,_) -> pos_of_formula b
	| EVariance b -> b.formula_var_pos

let replace_branches b = function
  | Or f -> failwith "replace_branches doesn't expect an Or"
  | Base f -> Base {f with formula_base_branches = b;}
  | Exists f -> Exists {f with formula_exists_branches = b;}
;;

let flatten_branches p br =
  List.fold_left (fun p (l, f) -> P.And (p, f,no_pos)) p br
;;

let rec h_fv (f:h_formula):(ident*primed) list = match f with   
  | Conj ({h_formula_conj_h1 = h1; 
	   h_formula_conj_h2 = h2; 
	   h_formula_conj_pos = pos})
  | Phase ({h_formula_phase_rd = h1; 
	   h_formula_phase_rw = h2; 
	   h_formula_phase_pos = pos}) 
  | Star ({h_formula_star_h1 = h1; 
	   h_formula_star_h2 = h2; 
	   h_formula_star_pos = pos}) ->  Gen.BList.remove_dups_eq (=) ((h_fv h1)@(h_fv h2))
  | HeapNode {h_formula_heap_node = name ; 
		  h_formula_heap_perm = p;
	      h_formula_heap_arguments = b} -> Gen.BList.remove_dups_eq (=) (name:: (List.concat ((List.map Ipure.afv b)@(List.map IP.frac_fv (Gen.some2list p)))))
  | HeapNode2 { h_formula_heap2_node = name ;
		h_formula_heap2_perm = p;
		h_formula_heap2_arguments = b}-> Gen.BList.remove_dups_eq (=) (name:: (List.concat ((List.map (fun c-> (Ipure.afv (snd c))) b)@(List.map IP.frac_fv (Gen.some2list p)))))
  | HTrue -> [] 
  | HFalse -> [] 
;;


(*
let rec h_arg_fv (f:h_formula):(ident*primed) list = 
	let rec helper (f:h_formula):((ident*primed) list) (**( (ident*primed) list)*) =	match f with   
  | Star b -> 
		let r11,r12 =  helper b.h_formula_star_h1 in
		let r21,r22 =  helper b.h_formula_star_h2 in
		((r11@r21),(r12@r22))
  | HeapNode {h_formula_heap_node = name ; 
							h_formula_heap_arguments = b}->
		((List.map (fun c->match c with
			|Ipure.Var d -> (fst d) 
			| _ -> 	Error.report_error	{Error.error_loc = no_pos; Error.error_text = ("exp float out malfunction")} ) b) ,[name])
  | HeapNode2 { h_formula_heap2_node = name ;
								h_formula_heap2_arguments = b}->		
		((List.map (fun c->match (snd c) with
			|Ipure.Var d -> (fst d) 
			| _ -> 	Error.report_error	{Error.error_loc = no_pos; Error.error_text = "exp float out malfunction"} ) b) ,[name])
  | HTrue -> ([],[]) 
  | HFalse -> ([],[]) in
	let r1,r2 = helper f in
	Gen.BList.remove_dups_eq (=) r1 (*(Gen.BList.difference_eq (=) r1 r2)*)
;;*)



let rec struc_hp_fv (f:struc_formula): (ident*primed) list = 
						let rec helper (f:ext_formula):(ident*primed) list = Gen.BList.remove_dups_eq (=) ( match f with
							| EBase b-> Gen.BList.difference_eq (=) 
													((struc_hp_fv b.formula_ext_continuation)@(heap_fv b.formula_ext_base)) 
													(b.formula_ext_explicit_inst@b.formula_ext_implicit_inst)
							| ECase b-> List.fold_left (fun a (c1,c2)->
											a@ (struc_hp_fv c2)) [] b.formula_case_branches
							| EAssume (b,_)-> heap_fv b
							| EVariance b -> struc_hp_fv b.formula_var_continuation
							) in
						List.concat (List.map helper f)

and heap_fv (f:formula):(ident*primed) list = match f with
	| Base b-> h_fv b.formula_base_heap
	| Exists b-> Gen.BList.difference_eq (=) (Gen.BList.remove_dups_eq (=) ( h_fv b.formula_exists_heap)) b.formula_exists_qvars 
	| Or b-> Gen.BList.remove_dups_eq (=) ((heap_fv b.formula_or_f1)@(heap_fv b.formula_or_f2))
	
	
and unbound_heap_fv (f:formula):(ident*primed) list = match f with
	| Base b-> h_fv b.formula_base_heap
	| Exists b-> 
		Gen.BList.difference_eq (=) (h_fv b.formula_exists_heap) b.formula_exists_qvars
	| Or b-> Gen.BList.remove_dups_eq (=) ((unbound_heap_fv b.formula_or_f1)@(unbound_heap_fv b.formula_or_f2))

and struc_free_vars (f0:struc_formula) with_inst:(ident*primed) list= 
	let helper f = match f with
		| EBase b -> 
					let fvb = all_fv b.formula_ext_base in
					let fvc = struc_free_vars b.formula_ext_continuation with_inst in
					Gen.BList.remove_dups_eq (=) (Gen.BList.difference_eq (=) (fvb@fvc) 
           ( (if with_inst then [] else b.formula_ext_explicit_inst@ b.formula_ext_implicit_inst) @ b.formula_ext_exists))
		| ECase b -> 
				let fvc = List.fold_left (fun a (c1,c2)-> 
				a@(struc_free_vars c2 with_inst)@(Ipure.fv c1)) [] b.formula_case_branches in
				Gen.BList.remove_dups_eq (=) fvc		
		| EAssume (b,_)-> all_fv b
		| EVariance b ->
			let fv_ec = (List.fold_left (fun res x -> res@(Ipure.fv x)) [] b.formula_var_escape_clauses) in
			let fv_ex = (List.fold_left (fun res (expr, bound) -> match bound with
											| None -> res@(Ipure.afv expr)
											| Some b_expr -> res@(Ipure.afv expr)@(Ipure.afv b_expr)) [] b.formula_var_measures) in
			let fv_co = struc_free_vars b.formula_var_continuation with_inst in
			Gen.BList.remove_dups_eq (=) (fv_ex@fv_ec@fv_co)
	in Gen.BList.remove_dups_eq (=) (List.concat (List.map helper f0))
 
and struc_split_fv_debug f0 wi =
  Gen.Debug.no_2 "struc_split_fv" (!print_struc_formula) string_of_bool 
      (fun (l1,l2) -> (string_of_spec_var_list l1)^"|"^(string_of_spec_var_list l2)) struc_split_fv_a f0 wi

and struc_split_fv f0 wi = struc_split_fv_a f0 wi

and struc_split_fv_a (f0:struc_formula) with_inst:((ident*primed) list) * ((ident*primed) list)= 
	let helper f = match f with
		| EBase b -> 
					let fvb = all_fv b.formula_ext_base in
					let prc,psc = struc_split_fv_a b.formula_ext_continuation with_inst in
          let rm = (if with_inst then [] else b.formula_ext_explicit_inst@ b.formula_ext_implicit_inst) @ b.formula_ext_exists in
					(Gen.BList.remove_dups_eq (=) (Gen.BList.difference_eq (=) (fvb@prc) rm),(Gen.BList.difference_eq (=) psc rm))
		| ECase b -> 
				let prl,psl = List.fold_left (fun (a1,a2) (c1,c2)-> 
              let prc, psc = struc_split_fv_a c2 with_inst in
              ((a1@prc@(Ipure.fv c1)),psc@a2)
          ) ([],[]) b.formula_case_branches in
				(Gen.BList.remove_dups_eq (=) prl,Gen.BList.remove_dups_eq (=) psl)		
		| EAssume (b,_)-> ([],all_fv b)
		| EVariance b ->
			let prc, psc = struc_split_fv_a b.formula_var_continuation with_inst in
			let fv_ec = (List.fold_left (fun res x -> res@(Ipure.fv x)) [] b.formula_var_escape_clauses) in
			let fv_ex = (List.fold_left (fun res (expr, bound) -> match bound with
											| None -> res@(Ipure.afv expr)
											| Some b_expr -> res@(Ipure.afv expr)@(Ipure.afv b_expr)) [] b.formula_var_measures) in
			  (Gen.BList.remove_dups_eq (=) prc@fv_ec@fv_ex, Gen.BList.remove_dups_eq (=) psc)
			
	in
  let vl = List.map helper f0 in
  let prl, pcl = List.split vl in
	(Gen.BList.remove_dups_eq (=) (List.concat prl), Gen.BList.remove_dups_eq (=) (List.concat pcl))
 

and all_fv (f:formula):(ident*primed) list = match f with
	| Base b-> Gen.BList.remove_dups_eq (=) 
			(List.fold_left ( fun a (c1,c2)-> a@ (Ipure.fv c2)) ((h_fv b.formula_base_heap)@(Ipure.fv b.formula_base_pure)@(IP.fv b.formula_base_perm))
							b.formula_base_branches )
	| Exists b-> 
		let r = List.fold_left ( fun a (c1,c2)-> a@ (Ipure.fv c2)) ((h_fv b.formula_exists_heap)@(Ipure.fv b.formula_exists_pure)@(IP.fv b.formula_exists_perm))
							b.formula_exists_branches in
		Gen.BList.difference_eq (=) (Gen.BList.remove_dups_eq (=) r) b.formula_exists_qvars 
	| Or b-> Gen.BList.remove_dups_eq (=) ((all_fv b.formula_or_f1)@(all_fv b.formula_or_f2))
	
and add_quantifiers (qvars : (ident*primed) list) (f : formula) : formula = match f with
  | Base ({ formula_base_heap = h; 
            formula_base_pure = p; 
            formula_base_branches = b;
           formula_base_flow = f;
		   formula_base_perm = perm;
           formula_base_pos = pos}) -> mkExists qvars h p f perm b pos
  | Exists ({formula_exists_qvars = qvs; 
             formula_exists_heap = h; 
             formula_exists_pure = p; 
             formula_exists_flow = f;
             formula_exists_branches = b;
			 formula_exists_perm = perm;
             formula_exists_pos = pos}) -> 
	  let new_qvars = Gen.BList.remove_dups_eq (=) (qvs @ qvars) in
		mkExists new_qvars h p f perm b pos
  | _ -> failwith ("add_quantifiers: invalid argument")
	
and push_exists (qvars : (ident*primed) list) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
	  let new_f1 = push_exists qvars f1 in
	  let new_f2 = push_exists qvars f2 in
	  let resform = mkOr new_f1 new_f2 pos in
		resform
  | _ -> add_quantifiers qvars f ;;


let formula_to_struc_formula (f:formula):struc_formula =
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
	(helper f);;


let split_quantifiers (f : formula) : ( (ident * primed) list * formula) = match f with
  | Exists ({formula_exists_qvars = qvars; 
			 formula_exists_heap =  h; 
			 formula_exists_pure = p; 
			 formula_exists_flow = f;
			 formula_exists_branches = br; 
			 formula_exists_perm = perm;
			 formula_exists_pos = pos}) -> 
      (qvars, mkBase h p f perm br pos)
  | Base _ -> ([], f)
  | _ -> failwith ("split_quantifiers: invalid argument")

(*var substitution*)

let rec subst sst (f : formula) = match sst with
  | s :: rest -> subst rest (apply_one s f)
  | [] -> f 
      
and subst_var (fr, t) (o : (ident*primed)) = if (Ipure.eq_var fr o) then t else o
and subst_var_list ft (o : (ident*primed)) = let r = List.filter (fun (c1,c2)-> (Ipure.eq_var c1 o) ) ft in
	if (List.length r)==0 then o else snd (List.hd r)

and apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
      Or ({formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h;
					 formula_base_pure = p;
					 formula_base_flow = fl;
					 formula_base_perm = perm;
					 formula_base_branches = br;
					 formula_base_pos = pos }) -> 
      Base ({formula_base_heap = h_apply_one s h; 
			 formula_base_pure = Ipure.apply_one s p;
			 formula_base_perm = IP.apply_one s perm;
			 formula_base_flow = fl;
			 formula_base_branches = List.map (fun (c1,c2)-> (c1,(Ipure.apply_one s c2))) br;
			 formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
			 formula_exists_heap = qh; 
			 formula_exists_pure = qp; 
			 formula_exists_flow = fl;
			 formula_exists_perm = perm;
			 formula_exists_branches = br;
			 formula_exists_pos = pos}) -> 
	  if List.mem (fst fr) (List.map fst qsv) then f 
	  else Exists ({formula_exists_qvars = qsv; 
					formula_exists_heap =  h_apply_one s qh; 
					formula_exists_pure = Ipure.apply_one s qp; 
					formula_exists_flow = fl;
					formula_exists_perm = IP.apply_one s perm;
					formula_exists_branches = List.map (fun (c1,c2)-> (c1,(Ipure.apply_one s c2))) br;
					formula_exists_pos = pos})		

and h_apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : h_formula) = match f with
  | Conj ({h_formula_conj_h1 = h1; 
	   h_formula_conj_h2 = h2; 
	   h_formula_conj_pos = pos}) ->
      Conj ({h_formula_conj_h1 = h_apply_one s h1; 
	   h_formula_conj_h2 = h_apply_one s h2; 
	   h_formula_conj_pos = pos})
  | Phase ({h_formula_phase_rd = h1; 
	    h_formula_phase_rw = h2; 
	    h_formula_phase_pos = pos}) ->
      Phase ({h_formula_phase_rd = h_apply_one s h1; 
	    h_formula_phase_rw = h_apply_one s h2; 
	    h_formula_phase_pos = pos}) 
  | Star ({h_formula_star_h1 = f1; 
	   h_formula_star_h2 = f2; 
	   h_formula_star_pos = pos}) -> 
      Star ({h_formula_star_h1 = h_apply_one s f1; 
	     h_formula_star_h2 = h_apply_one s f2; 
	     h_formula_star_pos = pos})
  | HeapNode ({h_formula_heap_node = x; 
	       h_formula_heap_name = c; 
	       h_formula_heap_imm = imm; 
	       h_formula_heap_full = full; 
	       h_formula_heap_with_inv = winv;
		   h_formula_heap_perm = perm;
	       h_formula_heap_arguments = args;
	       h_formula_heap_pseudo_data = ps_data;
	       h_formula_heap_label = l;
	       h_formula_heap_pos = pos}) -> 
      HeapNode ({h_formula_heap_node = subst_var s x; 
		 h_formula_heap_name = c;
		 h_formula_heap_imm = imm; 
		 h_formula_heap_full = full;
		 h_formula_heap_perm = Gen.trans_some (IP.subst_perm s) perm;
		 h_formula_heap_with_inv = winv;
		 h_formula_heap_arguments = List.map (Ipure.e_apply_one s) args;
		 h_formula_heap_pseudo_data = ps_data;
		 h_formula_heap_label = l;
		 h_formula_heap_pos = pos})
  | HeapNode2 ({
		 h_formula_heap2_node = x;
		 h_formula_heap2_name = c;
		 h_formula_heap2_imm = imm;
		 h_formula_heap2_full = full;
		 h_formula_heap2_perm = perm;
		 h_formula_heap2_with_inv = winv;
		 h_formula_heap2_arguments = args;
		 h_formula_heap2_pseudo_data = ps_data;
		 h_formula_heap2_label = l;
		 h_formula_heap2_pos= pos}) -> 
      HeapNode2 ({
		   h_formula_heap2_node = subst_var s x;
		   h_formula_heap2_name =c;
		   h_formula_heap2_imm = imm;
		   h_formula_heap2_full =full;
		   h_formula_heap2_perm = Gen.trans_some (IP.subst_perm s) perm;
		   h_formula_heap2_with_inv = winv;
		   h_formula_heap2_arguments = List.map (fun (c1,c2)-> (c1,(Ipure.e_apply_one s c2))) args;
		   h_formula_heap2_pseudo_data =ps_data;
		   h_formula_heap2_label = l;
		   h_formula_heap2_pos = pos})
  | HTrue -> f
  | HFalse -> f
	  

and rename_bound_vars (f : formula) = 
	let add_quantifiers (qvars : (ident*primed) list) (f : formula) : formula = match f with
  | Base ({formula_base_heap = h; 
		   formula_base_pure = p;
		   formula_base_perm = perm;
		   formula_base_flow = fl;
		   formula_base_branches = br;  
		   formula_base_pos = pos}) -> mkExists qvars h p fl perm br pos
  | Exists ({formula_exists_qvars = qvs; 
			 formula_exists_heap = h; 
			 formula_exists_pure = p;
			 formula_exists_perm = perm;
			 formula_exists_flow = fl;
			 formula_exists_branches = br;  
			 formula_exists_pos = pos}) -> 
	  let new_qvars = Gen.BList.remove_dups_eq (=) (qvs @ qvars) in
		mkExists new_qvars h p fl perm br pos
  | _ -> failwith ("add_quantifiers: invalid argument") in		
	match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	  let rf1 = rename_bound_vars f1 in
	  let rf2 = rename_bound_vars f2 in
	  let resform = mkOr rf1 rf2 pos in
		resform
  | Base _ -> f
  | Exists _ ->
	  let qvars, base_f = split_quantifiers f in
	  let new_qvars = Ipure.fresh_vars qvars in
	  let rho = List.combine qvars new_qvars in
	  let new_base_f = subst rho base_f in
	  let resform = add_quantifiers new_qvars new_base_f in
		resform 


	
and subst_struc (sst:((ident * primed)*(ident * primed)) list) (f:struc_formula):struc_formula = 
	
	let rec helper (f:ext_formula):ext_formula = match f with
		| EAssume (b,tag) -> EAssume ((subst sst b),tag)
		| ECase b ->
			let r = List.map (fun (c1,c2)-> ((Ipure.subst sst c1),(subst_struc sst c2))) b.formula_case_branches in
			ECase ({formula_case_branches = r; formula_case_pos = b.formula_case_pos})
		| EBase b->
			let sb = subst sst b.formula_ext_base in
			let sc = subst_struc sst b.formula_ext_continuation in
			let se = List.map (subst_var_list sst) b.formula_ext_explicit_inst in
			let si = List.map (subst_var_list sst) b.formula_ext_implicit_inst in
			let s_exist = List.map (subst_var_list sst) b.formula_ext_exists in
			EBase ({
					formula_ext_implicit_inst = si;
					formula_ext_explicit_inst = se;
					formula_ext_exists = s_exist;
					formula_ext_base = sb;
					formula_ext_continuation = sc;
					formula_ext_pos = b.formula_ext_pos	})
		| EVariance b ->
			(* let subst_list_of_pair sst ls = match sst with
			  | [] -> ls
			  | s::rest -> subst_list_of_pair rest (Ipure.e_apply_one_list_of_pair s ls) in *)
			let subst_measures = (Ipure.subst_list_of_pair sst b.formula_var_measures) in
			let subst_escape = (List.map (Ipure.subst sst) b.formula_var_escape_clauses) in
		    let subst_continuation = subst_struc sst b.formula_var_continuation in
				EVariance {b with
								formula_var_measures = subst_measures;
								formula_var_escape_clauses = subst_escape;
								formula_var_continuation = subst_continuation
						   }
	in	
	List.map helper f


let rec rename_bound_var_struc_formula (f:struc_formula):struc_formula =
	let rec helper (f:ext_formula):ext_formula = match f with
		| EAssume (b,tag) -> EAssume ((rename_bound_vars b),tag)
		| ECase b-> ECase ({b with formula_case_branches = List.map (fun (c1,c2)-> (c1,(rename_bound_var_struc_formula c2))) b.formula_case_branches})
		| EBase b-> 
			(*let sst1 = List.map (fun (c1,c2)-> ((c1,c2),((Ipure.fresh_old_name c1),c2)))b.formula_ext_explicit_inst in*)
			let sst2 = List.map (fun (c1,c2)-> ((c1,c2),((Ipure.fresh_old_name c1),c2)))b.formula_ext_implicit_inst in
			let sst = (*sst1@*)sst2 in
			let nb = subst sst b.formula_ext_base in
			let nc = subst_struc sst b.formula_ext_continuation in		
			let new_base_f = rename_bound_vars nb in
			let new_cont_f = rename_bound_var_struc_formula nc in
			EBase ({b with 
				formula_ext_explicit_inst = (*snd (List.split sst1)*) b.formula_ext_explicit_inst;
		 		formula_ext_implicit_inst = snd (List.split sst2);
				formula_ext_base=new_base_f; formula_ext_continuation=new_cont_f})			
		| EVariance b -> EVariance ({ b with
										formula_var_continuation = rename_bound_var_struc_formula b.formula_var_continuation;
									})
			in
	List.map helper f



and float_out_exps_from_heap (f:formula ):formula = 
	
  let rec float_out_exps (f:h_formula):(h_formula * (((ident*primed)*Ipure.formula)list)) = match f with
    | Star b-> 
	let r11,r12 = float_out_exps b.h_formula_star_h1 in
	let r21,r22 = float_out_exps b.h_formula_star_h2 in
	  (Star ({h_formula_star_h1  =r11; h_formula_star_h2=r21;h_formula_star_pos = b.h_formula_star_pos}), 
	   (r12@r22))
    | Conj b-> 
	let r11,r12 = float_out_exps b.h_formula_conj_h1 in
	let r21,r22 = float_out_exps b.h_formula_conj_h2 in
	  (Conj ({h_formula_conj_h1  =r11; h_formula_conj_h2=r21;h_formula_conj_pos = b.h_formula_conj_pos}), 
	   (r12@r22))
    | Phase b-> 
	let r11,r12 = float_out_exps b.h_formula_phase_rd in
	let r21,r22 = float_out_exps b.h_formula_phase_rw in
	  (Phase ({h_formula_phase_rd  =r11; h_formula_phase_rw=r21;h_formula_phase_pos = b.h_formula_phase_pos}), 
	   (r12@r22))
    | HeapNode b-> 
	let na,ls = List.split (List.map (fun c->
					    match c with
					      | Ipure.Var _ -> (c,[])
					      | _ -> 
						  let nn = (("flted_"^(string_of_int b.h_formula_heap_pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
						  let nv = Ipure.Var (nn,b.h_formula_heap_pos) in
						  let npf = Ipure.BForm (Ipure.Eq (nv,c,b.h_formula_heap_pos), None) in																
						    (nv,[(nn,npf)])) b.h_formula_heap_arguments) in
	  (HeapNode ({b with h_formula_heap_arguments = na}),(List.concat ls))
    | HeapNode2 b ->	 
	let na,ls = List.split (List.map (fun c->
					    match (snd c) with
					      | Ipure.Var _ -> (c,[])
					      | _ -> 
						  let nn = (("flted_"^(string_of_int b.h_formula_heap2_pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
						  let nv = Ipure.Var (nn,b.h_formula_heap2_pos) in
						  let npf = Ipure.BForm (Ipure.Eq (nv,(snd c),b.h_formula_heap2_pos), None) in																
						    (((fst c),nv),[(nn,npf)])) b.h_formula_heap2_arguments) in
	  (HeapNode2 ({b with h_formula_heap2_arguments = na}),(List.concat ls))
    | HTrue -> (f,[])
    | HFalse -> (f,[]) in
    
  let rec helper (f:formula):formula =	match f with
    | Base b-> let rh,rl = float_out_exps b.formula_base_heap in
	if (List.length rl)== 0 then f
	else 
	  let r1,r2 = List.hd rl in
	  let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)-> ((c1::a1),(Ipure.mkAnd a2 c2 b.formula_base_pos)) ) ([r1],r2) (List.tl rl) in
	    Exists ({
		      formula_exists_qvars = r1;
		      formula_exists_heap = rh;
		      formula_exists_flow = b.formula_base_flow;
		      formula_exists_pure = Ipure.mkAnd r2 b.formula_base_pure b.formula_base_pos;
		      formula_exists_branches = List.map (fun (c1,c2)-> (c1,(Ipure.mkAnd r2 c2 b.formula_base_pos)))b.formula_base_branches;
		      formula_exists_pos = b.formula_base_pos;
			  formula_exists_perm = b.formula_base_perm;
		    })			
    | Exists b->
	let rh,rl = float_out_exps b.formula_exists_heap in
	  if (List.length rl)== 0 then f
	  else 
	    let r1,r2 = List.hd rl in
	    let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)-> ((c1::a1),(Ipure.mkAnd a2 c2 b.formula_exists_pos)) ) ([r1],r2) (List.tl rl) in
	      Exists ({
			formula_exists_qvars = r1@b.formula_exists_qvars;
			formula_exists_heap = rh;
			formula_exists_pure = Ipure.mkAnd r2 b.formula_exists_pure b.formula_exists_pos;
			formula_exists_flow = b.formula_exists_flow;
			formula_exists_branches = List.map (fun (c1,c2)-> (c1,(Ipure.mkAnd r2 c2 b.formula_exists_pos)))b.formula_exists_branches;
			formula_exists_pos = b.formula_exists_pos;
			formula_exists_perm = b.formula_exists_perm;
		      })	
    | Or b-> Or ({
		   formula_or_f1 = float_out_exps_from_heap b.formula_or_f1;
		   formula_or_f2 = float_out_exps_from_heap b.formula_or_f2;
		   formula_or_pos = b.formula_or_pos
		 })		
  in helper f

  

and float_out_perm_from_heap (f:formula ):formula = 
	
  let rec float_out_perm (f:h_formula):(h_formula * (ident*primed) list * IP.perm_formula) = match f with
    | Star b-> 
	let r11,r12,r13 = float_out_perm b.h_formula_star_h1 in
	let r21,r22,r23 = float_out_perm b.h_formula_star_h2 in
	  (Star ({h_formula_star_h1  =r11; h_formula_star_h2=r21;h_formula_star_pos = b.h_formula_star_pos}), (r12@r22),(IP.mkAnd r13 r23 no_pos))
    | Conj b-> 
	let r11,r12,r13 = float_out_perm b.h_formula_conj_h1 in
	let r21,r22,r23 = float_out_perm b.h_formula_conj_h2 in
	  (Conj ({h_formula_conj_h1  =r11; h_formula_conj_h2=r21;h_formula_conj_pos = b.h_formula_conj_pos}), (r12@r22),(IP.mkAnd r13 r23 no_pos))
    | Phase b-> 
	let r11,r12,r13 = float_out_perm b.h_formula_phase_rd in
	let r21,r22,r23 = float_out_perm b.h_formula_phase_rw in
	  (Phase ({h_formula_phase_rd = r11; h_formula_phase_rw=r21;h_formula_phase_pos = b.h_formula_phase_pos}),(r12@r22),(IP.mkAnd r13 r23 no_pos))
    | HeapNode b-> 
		let na,lv,pf = match  b.h_formula_heap_perm with 
			| None -> (b.h_formula_heap_perm,[],IP.mkTrue no_pos)
			| Some v->
			  if IP.isConstFrac v then (b.h_formula_heap_perm,[],IP.mkTrue no_pos)
			  else 
				let nn = (("flted_"^(string_of_int b.h_formula_heap_pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
				let npv = IP.mkVPerm nn in
				let npf = IP.mkEq npv v b.h_formula_heap_pos in
				(Some npv,[nn],npf) in		  
	  (HeapNode ({b with h_formula_heap_perm = na}),lv,pf)
    | HeapNode2 b ->	 
		let na,lv,pf = match  b.h_formula_heap2_perm with 
			| None -> (b.h_formula_heap2_perm,[],IP.mkTrue no_pos)
			| Some v->
			  if IP.isConstFrac v then (b.h_formula_heap2_perm,[],IP.mkTrue no_pos)
			  else 
				let nn = (("flted_"^(string_of_int b.h_formula_heap2_pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
				let npv = IP.mkVPerm nn in
				let npf = IP.mkEq npv v b.h_formula_heap2_pos in
				(Some npv,[nn],npf) in		  
	  (HeapNode2 ({b with h_formula_heap2_perm = na}),lv,pf)
    | HTrue -> (f,[],IP.mkTrue no_pos)
    | HFalse -> (f,[],IP.mkTrue no_pos) in
    
  let rec helper (f:formula):formula =	match f with
    | Base b-> let rh,rl,rpf = float_out_perm b.formula_base_heap in
	if (List.length rl)== 0 then f
	else 
	    Exists ({
		      formula_exists_qvars = rl;
		      formula_exists_heap = rh;
		      formula_exists_flow = b.formula_base_flow;
		      formula_exists_pure = b.formula_base_pure;
			  formula_exists_perm = IP.mkAnd rpf b.formula_base_perm b.formula_base_pos;
		      formula_exists_branches = b.formula_base_branches;
		      formula_exists_pos = b.formula_base_pos  })			
    | Exists b->
	let rh,rl,rpf = float_out_perm b.formula_exists_heap in
	  if (List.length rl)== 0 then f
	  else 
	      Exists ({ b with
			formula_exists_qvars = rl@b.formula_exists_qvars;
			formula_exists_heap = rh;
			formula_exists_perm = IP.mkAnd rpf b.formula_exists_perm b.formula_exists_pos; })	
    | Or b-> Or ({
		   formula_or_f1 = float_out_perm_from_heap b.formula_or_f1;
		   formula_or_f2 = float_out_perm_from_heap b.formula_or_f2;
		   formula_or_pos = b.formula_or_pos
		 })		
  in helper f

  
  
  
and float_out_perm_from_heap_struc (f:struc_formula):struc_formula =
    let rec helper (f:ext_formula):ext_formula = match f with
    | EAssume (b,tag) -> EAssume ((float_out_perm_from_heap b),tag)
    | ECase b -> ECase ({formula_case_branches = List.map (fun (c1,c2)-> (c1,(float_out_perm_from_heap_struc c2))) b.formula_case_branches ; formula_case_pos=b.formula_case_pos})
    | EBase b-> EBase ({b with
				 formula_ext_base = float_out_perm_from_heap b.formula_ext_base;
				 formula_ext_continuation = float_out_perm_from_heap_struc b.formula_ext_continuation;
				 })
		| EVariance b -> EVariance ({ b with
										formula_var_continuation = float_out_perm_from_heap_struc b.formula_var_continuation;
									})
	in	
    List.map helper f
  
	   
	   
and float_out_exps_from_heap_struc (f:struc_formula):struc_formula = 
  let rec helper (f:ext_formula):ext_formula = match f with
    | EAssume (b,tag) -> EAssume ((float_out_exps_from_heap b),tag)
    | ECase b -> ECase ({formula_case_branches = List.map (fun (c1,c2)-> (c1,(float_out_exps_from_heap_struc c2))) b.formula_case_branches ; formula_case_pos=b.formula_case_pos})
    | EBase b-> 	EBase ({
				 formula_ext_explicit_inst = b.formula_ext_explicit_inst;
				 formula_ext_implicit_inst = b.formula_ext_implicit_inst;
				 formula_ext_exists = b.formula_ext_exists ;
				 formula_ext_base = float_out_exps_from_heap b.formula_ext_base;
				 formula_ext_continuation = float_out_exps_from_heap_struc b.formula_ext_continuation;
				 formula_ext_pos = b.formula_ext_pos			
				})
		| EVariance b -> EVariance ({ b with
										formula_var_continuation = float_out_exps_from_heap_struc b.formula_var_continuation;
									})
	in	
    List.map helper f
      
and float_out_min_max (f :  formula) :  formula =
  match f with
  |  Base
      {
         formula_base_pos = l;
         formula_base_heap = h0;
		 formula_base_flow = fl;
         formula_base_branches = br;
         formula_base_pure = p0;
		 formula_base_perm = perm;
      } ->
      let (nh, nhpf) = float_out_heap_min_max h0 in
      let np = float_out_pure_min_max p0 in
         Base
          {
             formula_base_pos = l;
             formula_base_heap = nh;
			 formula_base_flow = fl;
             formula_base_branches = (List.map (fun (l, f) -> (l, float_out_pure_min_max f)) br);
             formula_base_pure =
              (match nhpf with
               | None -> np
               | Some e1 -> Ipure.And (np, e1, l));
			formula_base_perm = perm;
          }
  |  Exists
      {
         formula_exists_qvars = qv;
         formula_exists_heap = h0;
         formula_exists_pure = p0;
		 formula_exists_flow = fl;
         formula_exists_branches = br;
		 formula_exists_perm = perm;
         formula_exists_pos = l
      } ->
      let (nh, nhpf) = float_out_heap_min_max h0 in
      let np = float_out_pure_min_max p0 in
         Exists
          {
             formula_exists_qvars = qv;
             formula_exists_heap = nh;
			 formula_exists_flow = fl;
			 formula_exists_perm = perm;
             formula_exists_pure =
              (match nhpf with
               | None -> np
               | Some e1 -> (Ipure.And (np, e1, l)));
             formula_exists_branches = (List.map (fun (l, f) -> (l, float_out_pure_min_max f)) br);
             formula_exists_pos = l;
          }
  |  Or
      {
         formula_or_f1 = f1;
         formula_or_f2 = f2;
         formula_or_pos = l
      } ->
       Or
        {
           formula_or_f1 = float_out_min_max f1;
           formula_or_f2 = float_out_min_max f2;
           formula_or_pos = l;
        }

and float_out_exp_min_max (e: Ipure.exp): (Ipure.exp * (Ipure.formula * (string list) ) option) = match e with 
  | Ipure.Null _ -> (e, None)
  | Ipure.Var _ -> (e, None)
  | Ipure.IConst _ -> (e, None)
  | Ipure.FConst _ -> (e, None)
  | Ipure.Add (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let r = match (np1, np2) with
					| None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))in
			(Ipure.Add (ne1, ne2, l), r) 
  | Ipure.Subtract (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let r = match (np1, np2) with
					| None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))in
			(Ipure.Subtract (ne1, ne2, l), r) 
  | Ipure.Mult (e1, e2, l) ->
      let ne1, np1 = float_out_exp_min_max e1 in
      let ne2, np2 = float_out_exp_min_max e2 in
      let r = match np1, np2 with
        | None, None -> None
        | Some p, None -> Some p
        | None, Some p -> Some p
        | Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))
      in (Ipure.Mult (ne1, ne2, l), r)
  | Ipure.Div (e1, e2, l) ->
      let ne1, np1 = float_out_exp_min_max e1 in
      let ne2, np2 = float_out_exp_min_max e2 in
      let r = match np1, np2 with
        | None, None -> None
        | Some p, None -> Some p
        | None, Some p -> Some p
        | Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))
      in (Ipure.Div (ne1, ne2, l), r)						 
  | Ipure.Max (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let new_name = ("max"^(fresh_trailer())) in
			let nv = Ipure.Var((new_name, Unprimed), l) in
			let t = Ipure.BForm (Ipure.EqMax(nv, ne1, ne2, l), None) in 
			let r = match (np1, np2) with
					| None, None -> Some (t,[new_name])
					| Some (p1, l1), None -> Some ((Ipure.And(p1, t, l)), (new_name:: l1))
					| None, Some (p1, l1) -> Some ((Ipure.And(p1, t, l)), (new_name:: l1))
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And ((Ipure.And (p1, t, l)), p2, l)), new_name:: (List.rev_append l1 l2)) in
			(nv, r) 
			
			
  | Ipure.Min (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let new_name = ("min"^(fresh_trailer())) in
			let nv = Ipure.Var((new_name, Unprimed), l) in
			let t = Ipure.BForm (Ipure.EqMin(nv, ne1, ne2, l), None) in 
			let r = match (np1, np2) with
					| None, None -> Some (t,[new_name])
					| Some (p1, l1), None -> Some ((Ipure.And(p1, t, l)), (new_name:: l1))
					| None, Some (p2, l2) -> Some ((Ipure.And(p2, t, l)), (new_name:: l2))
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And ((Ipure.And (p1, t, l)), p2, l)), new_name:: (List.rev_append l1 l2)) in
			(nv, r) 
	
		(* bag expressions *)
  | Ipure.Bag (le, l) ->
			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in
			let r = List.fold_left (fun a c -> match (a, c)with
				  | None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in
			(Ipure.Bag (ne1, l), r)
  | Ipure.BagUnion (le, l) ->
			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in
			let r = List.fold_left (fun a c -> match (a, c)with
				  | None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in
			(Ipure.BagUnion (ne1, l), r)
  | Ipure.BagIntersect (le, l) ->
			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in
			let r = List.fold_left (fun a c -> match (a, c)with
				  | None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), List.rev_append l1 l2)) None np1 in
			(Ipure.BagIntersect (ne1, l), r)
  | Ipure.BagDiff (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let r = match (np1, np2) with
					| None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2)) in
			(Ipure.BagDiff (ne1, ne2, l), r) 
		(* list expressions *)
  | Ipure.List (le, l) ->
			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in
			let r = List.fold_left (fun a c -> match (a, c) with
				  | None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in
			(Ipure.List (ne1, l), r)
  | Ipure.ListAppend (le, l) ->
			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in
			let r = List.fold_left (fun a c -> match (a, c) with
				  | None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in
			(Ipure.ListAppend (ne1, l), r)
  | Ipure.ListCons (e1, e2, l) -> 
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let r = match (np1, np2) with
					| None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2)) in
			(Ipure.ListCons (ne1, ne2, l), r) 
  | Ipure.ListHead (e, l) -> 
			let ne1, np1 = float_out_exp_min_max e in
			(Ipure.ListHead (ne1, l), np1)
  | Ipure.ListTail (e, l) -> 
			let ne1, np1 = float_out_exp_min_max e in
			(Ipure.ListTail (ne1, l), np1)
  | Ipure.ListLength (e, l) -> 
			let ne1, np1 = float_out_exp_min_max e in
			(Ipure.ListLength (ne1, l), np1)
  | Ipure.ListReverse (e, l) -> 
			let ne1, np1 = float_out_exp_min_max e in
			(Ipure.ListReverse (ne1, l), np1)
	(* An Hoa : get rid of min/max in a[i] *)
  | Ipure.ArrayAt (a, i, l) ->
			let ne, np = float_out_exp_min_max i in
			(Ipure.ArrayAt (a, ne, l), np)

and float_out_pure_min_max (p : Ipure.formula) : Ipure.formula =
		
		let add_exists (t: Ipure.formula)(np1: (Ipure.formula * (string list))option)(np2: (Ipure.formula * (string list))option) l: Ipure.formula = 
			let r, ev = match np1 with
							| None -> (t,[])
							| Some (p1, ev1) -> (Ipure.And (t, p1, l), ev1) in
			let r, ev2 = match np2 with 
							| None -> (r, ev)
							| Some (p1, ev1) -> (Ipure.And(r, p1, l), (List.rev_append ev1 ev)) in 
		  List.fold_left (fun a c -> (Ipure.Exists ((c, Unprimed), a, None,l))) r ev2 in
		
		(* An Hoa : produce exists x_1 exists x_2 ... exists x_n t *)	
		(*let add_exists (t: Ipure.formula) (nps: (Ipure.formula * (string list))option list) l: Ipure.formula = 			
			let r, ev = match np1 with
							| None -> (t,[])
							| Some (p1, ev1) -> (Ipure.And (t, p1, l), ev1) in
			let r, ev2 = match np2 with 
							| None -> (r, ev)
							| Some (p1, ev1) -> (Ipure.And(r, p1, l), (List.rev_append ev1 ev)) in
		  List.fold_left (fun fml np -> let r, ev = match np1 with
							| None -> fml
							| Some (p, ev) -> (Ipure.And (t, p1, l), ev))
				 t
				 nps
		  List.fold_left (fun a c -> (Ipure.Exists ((c, Unprimed), a, None,l))) r ev2 in *)							
		(* End add_exists *)
				
		let rec float_out_b_formula_min_max (b: Ipure.b_formula) lbl: Ipure.formula = match b with
			| Ipure.BConst _ -> Ipure.BForm (b,lbl)
		  | Ipure.BVar _ -> Ipure.BForm (b,lbl)
		  | Ipure.Lt (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Lt (ne1, ne2, l), lbl) in
						add_exists t np1 np2 l
		  | Ipure.Lte (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Lte (ne1, ne2, l),lbl) in
						add_exists t np1 np2 l
		  | Ipure.Gt (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Gt (ne1, ne2, l), lbl) in
						add_exists t np1 np2 l
		  | Ipure.Gte (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Gte (ne1, ne2, l), lbl) in
						add_exists t np1 np2 l
		  | Ipure.Eq (e1, e2, l) ->
						let r = match e1 with
							| Ipure.Min(v1, v2, v3) -> let r2 = match e2 with
																	| Ipure.Null _
																	| Ipure.IConst _
                                  | Ipure.FConst _
																	| Ipure.Var _ ->
																			 let ne1 , np1 = float_out_exp_min_max v1 in
																			 let ne2 , np2 = float_out_exp_min_max v2 in
																			 let t = Ipure.BForm(Ipure.EqMin(e2, ne1, ne2, l), lbl) in
																			 add_exists t np1 np2 l
																	| _ -> 
																			 let ne1, np1 = float_out_exp_min_max e1 in
																			 let ne2, np2 = float_out_exp_min_max e2 in
																			 let t = Ipure.BForm (Ipure.Eq (ne1, ne2, l), lbl) in
																			 add_exists t np1 np2 l  in r2
							| Ipure.Max(v1, v2, v3) -> let r2 = match e2 with
																						| Ipure.Null _
																						| Ipure.IConst _
                                            | Ipure.FConst _
																						| Ipure.Var _ ->
																								 let ne1 , np1 = float_out_exp_min_max v1 in
																								 let ne2 , np2 = float_out_exp_min_max v2 in
																								 let t = Ipure.BForm(Ipure.EqMax(e2, ne1, ne2, l), lbl) in
																								 add_exists t np1 np2 l
																						| _ -> 
																							let ne1, np1 = float_out_exp_min_max e1 in
																							let ne2, np2 = float_out_exp_min_max e2 in
																							let t = Ipure.BForm (Ipure.Eq (ne1, ne2, l), lbl) in
																							add_exists t np1 np2 l 
																			in r2
							| Ipure.Null _
							| Ipure.IConst _
              | Ipure.FConst _
							| Ipure.Var _ -> let r2 = match e2 with
																					| Ipure.Min (v1, v2, v3) ->
																						 	 let ne1 , np1 = float_out_exp_min_max v1 in
																							 let ne2 , np2 = float_out_exp_min_max v2 in
																							 let t = Ipure.BForm(Ipure.EqMin(e1, ne1, ne2, l), lbl) in
																							 add_exists t np1 np2 l
																					| Ipure.Max (v1, v2, v3) ->
																							 let ne1 , np1 = float_out_exp_min_max v1 in
																							 let ne2 , np2 = float_out_exp_min_max v2 in
																							 let t = Ipure.BForm(Ipure.EqMax(e1, ne1, ne2, l), lbl) in
																							 add_exists t np1 np2 l
																					| _ -> 
																						let ne1, np1 = float_out_exp_min_max e1 in
																						let ne2, np2 = float_out_exp_min_max e2 in
																						let t = Ipure.BForm (Ipure.Eq (ne1, ne2, l), lbl) in
																						add_exists t np1 np2 l 
																in r2
							| _ ->
									let ne1, np1 = float_out_exp_min_max e1 in
									let ne2, np2 = float_out_exp_min_max e2 in
									let t = Ipure.BForm (Ipure.Eq (ne1, ne2, l), lbl) in
									add_exists t np1 np2 l 
							in r
		  | Ipure.Neq (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Neq (ne1, ne2, l), lbl) in
						add_exists t np1 np2 l
		  | Ipure.EqMax (e1, e2, e3, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let ne3, np3 = float_out_exp_min_max e3 in
						let t = Ipure.BForm (Ipure.EqMax (ne1, ne2, ne3, l), lbl) in
						let t = add_exists t np1 np2 l in
						let r = match np3 with 
							| None -> t
							| Some (p1, l1) -> List.fold_left (fun a c -> (Ipure.Exists ((c, Unprimed), a, lbl, l))) (Ipure.And(t, p1, l)) l1 in r
		  | Ipure.EqMin (e1, e2, e3, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let ne3, np3 = float_out_exp_min_max e3 in
						let t = Ipure.BForm (Ipure.EqMin (ne1, ne2, ne3, l), lbl) in
						let t = add_exists t np1 np2 l in
						let r = match np3 with 
							| None -> t
							| Some (p1, l1) -> List.fold_left (fun a c -> Ipure.Exists ((c, Unprimed), a, lbl, l)) (Ipure.And(t, p1, l)) l1 in r
		  | Ipure.BagIn (v, e, l) -> 
							let ne1, np1 = float_out_exp_min_max e in
							let r = match np1 with
								| None -> Ipure.BForm (Ipure.BagIn(v, ne1, l), lbl)
								| Some (r, l1) -> List.fold_left (fun a c -> Ipure.Exists ((c, Unprimed), a, lbl, l)) (Ipure.And(Ipure.BForm (Ipure.BagIn(v, ne1, l),lbl), r, l)) l1 in r 
		  | Ipure.BagNotIn (v, e, l) -> 
							let ne1, np1 = float_out_exp_min_max e in
							let r = match np1 with
								| None -> Ipure.BForm (Ipure.BagNotIn(v, ne1, l), lbl)
								| Some (r, l1) -> List.fold_left (fun a c -> Ipure.Exists ((c, Unprimed), a, lbl,  l)) (Ipure.And(Ipure.BForm (Ipure.BagIn(v, ne1, l),lbl), r, l)) l1 in r
		  | Ipure.BagSub (e1, e2, l) ->
					let ne1, np1 = float_out_exp_min_max e1 in
					let ne2, np2 = float_out_exp_min_max e2 in
					let t = Ipure.BForm (Ipure.BagSub (ne1, ne2, l),lbl) in
					add_exists t np1 np2 l
		  | Ipure.BagMin _ -> Ipure.BForm (b,lbl)
		  | Ipure.BagMax _ -> Ipure.BForm (b,lbl)	
		  | Ipure.ListIn (e1, e2, l) -> 
					let ne1, np1 = float_out_exp_min_max e1 in
					let ne2, np2 = float_out_exp_min_max e2 in
					let t = Ipure.BForm (Ipure.ListIn (ne1, ne2, l),lbl) in
					add_exists t np1 np2 l
		  | Ipure.ListNotIn (e1, e2, l) -> 
					let ne1, np1 = float_out_exp_min_max e1 in
					let ne2, np2 = float_out_exp_min_max e2 in
					let t = Ipure.BForm (Ipure.ListNotIn (ne1, ne2, l),lbl) in
					add_exists t np1 np2 l
		  | Ipure.ListAllN (e1, e2, l) ->
					let ne1, np1 = float_out_exp_min_max e1 in
					let ne2, np2 = float_out_exp_min_max e2 in
					let t = Ipure.BForm (Ipure.ListAllN (ne1, ne2, l),lbl) in
					add_exists t np1 np2 l
		  | Ipure.ListPerm (e1, e2, l) ->
					let ne1, np1 = float_out_exp_min_max e1 in
					let ne2, np2 = float_out_exp_min_max e2 in
					let t = Ipure.BForm (Ipure.ListPerm (ne1, ne2, l),lbl) in
					add_exists t np1 np2 l
			(* An Hoa : handle relation *)
			(* TODO Have to add the existential before the formula! Add a add_exists with a list instead *)
			| Ipure.RelForm (r, args, l) ->
					let nargs = List.map float_out_exp_min_max args in
					let nargse = List.map fst nargs in
					let t = Ipure.BForm (Ipure.RelForm (r, nargse, l), lbl) in
					t
			in		 
		match p with
			| Ipure.BForm (b,lbl) -> (float_out_b_formula_min_max b lbl)
  		| Ipure.And (f1, f2, l) -> Ipure.And((float_out_pure_min_max f1), (float_out_pure_min_max f2), l)
  		| Ipure.Or (f1, f2, lbl, l) -> Ipure.Or((float_out_pure_min_max f1), (float_out_pure_min_max f2), lbl,l)
  		| Ipure.Not (f1,lbl, l) -> Ipure.Not((float_out_pure_min_max f1), lbl, l)
  		| Ipure.Forall (v, f1, lbl, l) -> Ipure.Forall (v, (float_out_pure_min_max f1), lbl, l)
  		| Ipure.Exists (v, f1, lbl, l) -> Ipure.Exists (v, (float_out_pure_min_max f1), lbl, l)
		

and float_out_heap_min_max (h :  h_formula) :
  ( h_formula * (Ipure.formula option)) =
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
	 let args = h1. h_formula_heap_arguments in
	 let l = h1. h_formula_heap_pos in
	 let nl, new_p =
	   List.fold_left
             (fun (a, c) d -> 
	        match d with
		  | Ipure.Null _ 
		  | Ipure.IConst _
		  | Ipure.Var _ -> (d:: a, c)
		  | _ -> 
		      let new_name = fresh_var_name "ptr" l.start_pos.Lexing.pos_lnum in 
		      let nv = Ipure.Var((new_name, Unprimed), l) in
			(nv:: a, match c with
			   | None -> Some (float_out_pure_min_max (Ipure.BForm (Ipure.Eq (nv, d, l), None)) )
			   | Some s -> Some (Ipure.And ((float_out_pure_min_max (Ipure.BForm (Ipure.Eq (nv, d, l), None))), s, l)))) ([], None) args in
           (( HeapNode { h1 with  h_formula_heap_arguments = (List.rev nl);}), new_p)
    |  HeapNode2 h1 ->
	 let args = h1. h_formula_heap2_arguments in
	 let l = h1. h_formula_heap2_pos in
	 let nl, new_p =
	   List.fold_left
             (fun (a, c) (d1,d2) -> 
	        match d2 with
		  | Ipure.Null _ 
		  | Ipure.IConst _
		  | Ipure.Var _ -> ((d1,d2):: a, c)
		  | _ -> 
		      let new_name = fresh_var_name "ptr" l.start_pos.Lexing.pos_lnum in 
		      let nv = Ipure.Var((new_name, Unprimed), l) in
			((d1,nv):: a, match c with
			   | None -> Some (float_out_pure_min_max (Ipure.BForm (Ipure.Eq (nv, d2, l), None)) )
			   | Some s -> Some (Ipure.And ((float_out_pure_min_max (Ipure.BForm (Ipure.Eq (nv, d2, l), None)) ), s, l)))) ([], None) args in
           (( HeapNode2 { h1 with  h_formula_heap2_arguments = (List.rev nl);}), new_p)
    |  HTrue -> (h, None)
    |  HFalse -> (h, None)
	 
  
and float_out_struc_min_max (f0 : struc_formula): struc_formula = 
	let rec helper (f0: ext_formula):ext_formula = match f0 with
		| EAssume (b,tag) -> EAssume ((float_out_min_max b),tag)
		| ECase b-> ECase {
						 formula_case_branches = (List.map (fun (c1,c2)->
								((float_out_pure_min_max c1),(float_out_struc_min_max c2)))
								b.formula_case_branches);
						 formula_case_pos = b.formula_case_pos}
		| EBase b -> EBase {b with 
						 formula_ext_base = float_out_min_max b.formula_ext_base;
						 formula_ext_continuation = float_out_struc_min_max b.formula_ext_continuation}
		| EVariance b ->
			let fo_measures = (List.map (fun (expr, bound) -> match bound with
																| None -> ((fst (float_out_exp_min_max expr)), None)
																| Some bexpr -> ((fst (float_out_exp_min_max expr)), Some (fst (float_out_exp_min_max bexpr)))) b.formula_var_measures) in
			let fo_escape_clause = (List.map (fun f -> (float_out_pure_min_max f)) b.formula_var_escape_clauses) in
				EVariance ({ b with
					formula_var_measures = fo_measures;
					formula_var_escape_clauses = fo_escape_clause;
					formula_var_continuation = float_out_struc_min_max b.formula_var_continuation;
				})
	in
	List.map helper f0
		

and view_node_types_struc (f:struc_formula):ident list = 
	let helper (f:ext_formula):ident list = match f with
	| ECase b -> List.concat (List.map (fun (c1,c2)-> view_node_types_struc c2) b.formula_case_branches)
	| EBase b -> (view_node_types b.formula_ext_base)@(view_node_types_struc b.formula_ext_continuation)
	| EAssume (b,_) -> view_node_types b
	| EVariance b -> view_node_types_struc b.formula_var_continuation
	in
	Gen.BList.remove_dups_eq (=) (List.concat (List.map helper f))
		
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
	let rec has_top_flow (f:formula) = match f with
		| Base b-> if (String.compare b.formula_base_flow top_flow)<>0 then Error.report_error {
						Error.error_loc = b.formula_base_pos;
						Error.error_text = ("view formula can not have a non top flow( "^b.formula_base_flow^")")} else ()
		| Exists b-> if (String.compare b.formula_exists_flow top_flow)<>0 then Error.report_error {
						Error.error_loc = b.formula_exists_pos;
						Error.error_text = ("view formula can not have a non top flow("^b.formula_exists_flow^")")} else ()
		| Or b -> (has_top_flow b.formula_or_f1);(has_top_flow b.formula_or_f2) in
	let rec helper f0 = match f0 with
		| EBase b->   (has_top_flow b.formula_ext_base); (has_top_flow_struc b.formula_ext_continuation)
		| ECase b->   List.iter (fun (_,b1)-> (has_top_flow_struc b1)) b.formula_case_branches
		| EAssume (b,_)-> (has_top_flow b)
		| EVariance b -> has_top_flow_struc b.formula_var_continuation
		in
List.iter helper f

and subst_flow_of_formula fr t (f:formula):formula = match f with
	| Base b-> Base {b with formula_base_flow = 
		if (String.compare fr b.formula_base_flow)==0 then t else b.formula_base_flow;}
	| Exists b-> Exists {b with formula_exists_flow = 
		if (String.compare fr b.formula_exists_flow)==0 then t else b.formula_exists_flow;}
	| Or b -> Or {b with formula_or_f1 = (subst_flow_of_formula fr t b.formula_or_f1);
					  formula_or_f2 = (subst_flow_of_formula fr t b.formula_or_f2);}
	
and subst_stub_flow t f = subst_flow_of_formula stub_flow t f	

and subst_flow_of_struc_formula  fr t (f:struc_formula):struc_formula = 

let rec helper f = match f with
		| EBase b ->EBase {b with 
						 formula_ext_base = subst_flow_of_formula fr t b.formula_ext_base;
						 formula_ext_continuation = subst_flow_of_struc_formula fr t b.formula_ext_continuation}
		| ECase b ->ECase {b with
						 formula_case_branches = (List.map (fun (c1,c2)->
								(c1,(subst_flow_of_struc_formula fr t c2)))b.formula_case_branches)}
		| EAssume (b,tag)-> EAssume ((subst_flow_of_formula fr t b),tag) 
		| EVariance b -> EVariance ({ b with
										formula_var_continuation = subst_flow_of_struc_formula fr t b.formula_var_continuation;
								   })
in
List.map helper f 


and subst_stub_flow_struc (t:string) (f:struc_formula) : struc_formula = subst_flow_of_struc_formula stub_flow t f	


(* normalization of the heap formula *)
(* emp & emp * K == K *)

(* D@I@NE & emp * K *)
(* D@I & D@W    * K *)
(* D@I & D@I@NE * K@W *)


(* @NE = non-empty *)
(* @I = all immutable *)
(* @W = at least one W *)

(* KI = KI*KI *)


let rec normalize_h_formula (h : h_formula) : h_formula = match h with
  | Phase({h_formula_phase_rd = h1;
	 h_formula_phase_rw = h2;
	 h_formula_phase_pos = pos
	  }) ->
      (* conj in read phase -> split into two separate read phases *)
      let rd_phase = normalize_h_formula_rd_phase h1 in
      let wr_phase = normalize_h_formula h2 in 
      let res = insert_wr_phase rd_phase wr_phase in
	res
  | Star({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos
	 }) ->
      Star({h_formula_star_h1 = h1;
	  h_formula_star_h2 = normalize_h_formula h2;
	  h_formula_star_pos = pos
	 }) 
  | Conj({h_formula_conj_h1 = h1;
	 h_formula_conj_h2 = h2;
	 h_formula_conj_pos = pos
	 }) ->
	normalize_h_formula_rd_phase h
  | _ -> h
    
and contains_phase (h : h_formula) : bool = match h with
  | Phase _ -> true
  | Conj ({h_formula_conj_h1 = h1;
	   h_formula_conj_h2 = h2;
	   h_formula_conj_pos = pos;
    }) 
  | Star ({h_formula_star_h1 = h1;
	 h_formula_star_h2 = h2;
	 h_formula_star_pos = pos}) ->
      (contains_phase h1) or (contains_phase h2)
  | _ -> false

and normalize_h_formula_rd_phase (h : h_formula) : h_formula = match h with
  | Conj({h_formula_conj_h1 = h1;
	 h_formula_conj_h2 = h2;
	 h_formula_conj_pos = pos}) ->
      (* conj in read phase -> split into two separate read phases *)
      let conj1 = normalize_h_formula_rd_phase h1 in
	insert_rd_phase conj1 h2 
  | Phase _ -> failwith "Shouldn't have phases inside the reading phase\n"
  | _ -> Phase({h_formula_phase_rd = h;
		h_formula_phase_rw = HTrue;
		h_formula_phase_pos = no_pos;
	       })


and insert_wr_phase (f : h_formula) (wr_phase : h_formula) : h_formula = 
  match f with
    | Phase ({h_formula_phase_rd = h1;
	     h_formula_phase_rw = h2;
	     h_formula_phase_pos = pos}) ->
	let new_h2 = 
	  match h2 with
	    | HTrue -> wr_phase (* insert the new phase *)
	    | Star({h_formula_star_h1 = h1_star;
		    h_formula_star_h2 = h2_star;
		    h_formula_star_pos = pos_star
		   }) ->
		(* when insert_wr_phase is called, f represents a reading phase ->
		   all the writing phases whould be emp *)
		if (contains_phase h2_star) then
		  (* insert in the nested phase *)
		  Star({
			h_formula_star_h1 = h1_star;
			h_formula_star_h2 = insert_wr_phase h2_star wr_phase;
			h_formula_star_pos = pos_star
		       })
		else failwith ("[iformula.ml] : should contain phase\n")
		  
	    | _ -> Star({
			h_formula_star_h1 = h2;
			h_formula_star_h2 = wr_phase;
			h_formula_star_pos = pos
		       })
	in
	  (* reconstruct the phase *)
	  Phase({h_formula_phase_rd = h1;
		 h_formula_phase_rw = new_h2;
		h_formula_phase_pos = pos})
    | _ -> failwith ("[iformula.ml] : There should be a phase at this point\n")


and insert_rd_phase (f : h_formula) (rd_phase : h_formula) : h_formula = 
  match f with
    | Phase ({h_formula_phase_rd = h1;
	     h_formula_phase_rw = h2;
	     h_formula_phase_pos = pos}) ->
	let new_h2 = 
	(match h2 with
	   | HTrue -> 
	       (* construct the new phase *)
		let new_phase = Phase({h_formula_phase_rd = rd_phase; 
				  h_formula_phase_rw = HTrue;
				  h_formula_phase_pos = pos})
		in
		  (* input the new phase *)
		Star({h_formula_star_h1 = HTrue;
		      h_formula_star_h2 = new_phase;
		      h_formula_star_pos = pos})
	   | Conj _ -> failwith ("[cformula.ml] : Should not have conj at this point\n") (* the write phase does not contain conj *)	     
	   | Star ({h_formula_star_h1 = h1_star;
		    h_formula_star_h2 = h2_star;
		    h_formula_star_pos = pos_star
		   }) ->
	       let new_phase = insert_rd_phase h2_star rd_phase in
	       Star({h_formula_star_h1 = h1_star;
		     h_formula_star_h2 = new_phase;
		     h_formula_star_pos = pos_star})
	   | _ ->
		let new_phase = Phase({h_formula_phase_rd = rd_phase; 
				  h_formula_phase_rw = HTrue;
				  h_formula_phase_pos = pos})
		in
		Star({h_formula_star_h1 = h2;
		      h_formula_star_h2 = new_phase;
		      h_formula_star_pos = pos})
	)
	in
	  Phase({
		  h_formula_phase_rd = h1;
		  h_formula_phase_rw = new_h2;
		  h_formula_phase_pos = pos;
		})
    | Conj _ -> failwith ("[cformula.ml] : Should not have conj at this point\n")	     
    | _ -> 
		let new_phase = Phase({h_formula_phase_rd = rd_phase; 
				  h_formula_phase_rw = HTrue;
				  h_formula_phase_pos = no_pos})
		in
		let new_star = Star({h_formula_star_h1 = HTrue;
		      h_formula_star_h2 = new_phase;
		      h_formula_star_pos = no_pos})
		in 
		Phase({
		  h_formula_phase_rd = f;
		  h_formula_phase_rw = new_star;
		  h_formula_phase_pos = no_pos;
		})

