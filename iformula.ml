(*
  Created 19-Feb-2006

  Input formulae
*)

open Globals
open Exc.GTable
open Perm
module P = Ipure

type ann = ConstAnn of heap_ann | PolyAnn of ((ident * primed) * loc)

type struc_formula = ext_formula list

and ext_formula = 
	| ECase of ext_case_formula
	| EBase of ext_base_formula
	| EAssume of (formula*formula_label)(*could be generalized to have a struc_formula type instead of simple formula*)
	(*| EVariance of ext_variance_formula*)
 (* spec feature to induce inference *)
 | EInfer of ext_infer_formula

and ext_infer_formula =
  {
    formula_inf_post : bool; (* true if post to be inferred *)
    formula_inf_vars : (ident * primed) list;
    formula_inf_continuation : ext_formula;
    formula_inf_pos : loc
  }

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
        (* formula_ext_complete: bool;*)
		 formula_ext_pos : loc
	}
(*  
and ext_variance_formula =
	{
		formula_var_measures : (P.exp * (P.exp option)) list; (* Lexical ordering with bound *)
    formula_var_infer : P.exp list; (* list of exp to infer measure *)
		formula_var_continuation : ext_formula;
		formula_var_pos : loc
	}
*)
and formula =
  | Base of formula_base
  | Exists of formula_exists
  | Or of formula_or

and formula_base = { formula_base_heap : h_formula;
                     formula_base_pure : P.formula;
                     formula_base_flow : flow_formula;
                     formula_base_branches : (branch_label * P.formula) list;
                     formula_base_pos : loc }

and formula_exists = { formula_exists_qvars : (ident * primed) list;
                       formula_exists_heap : h_formula;
                       formula_exists_pure : P.formula;
                       formula_exists_flow : flow_formula;
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
		       h_formula_heap_derv : bool; 
		       h_formula_heap_imm : ann;
		       h_formula_heap_full : bool;
		       h_formula_heap_with_inv : bool;
		       h_formula_heap_perm : iperm; (*LDK: optional fractional permission*)
		       h_formula_heap_arguments : P.exp list;
		       h_formula_heap_pseudo_data : bool;
		       h_formula_heap_label : formula_label option;
		       h_formula_heap_pos : loc }

and h_formula_heap2 = { h_formula_heap2_node : (ident * primed);
			h_formula_heap2_name : ident;
			h_formula_heap2_derv : bool;
			h_formula_heap2_imm : ann;
			h_formula_heap2_full : bool;
			h_formula_heap2_with_inv : bool;
		    h_formula_heap2_perm : iperm; (*LDK: fractional permission*)
			h_formula_heap2_arguments : (ident * P.exp) list;
			h_formula_heap2_pseudo_data : bool;
			h_formula_heap2_label : formula_label option;
			h_formula_heap2_pos : loc }
let print_formula = ref(fun (c:formula) -> "printer not initialized")
let print_struc_formula = ref(fun (c:struc_formula) -> "printer not initialized")

(*move to ipure.ml*)
(* let linking_exp_list = ref (Hashtbl.create 100) *)
(* let _ = let zero = P.IConst (0, no_pos) *)
(* 		in Hashtbl.add !linking_exp_list zero 0 *)

let apply_one_imm (fr,t) a = match a with
  | ConstAnn _ -> a
  | PolyAnn (sv, pos) -> PolyAnn ((if P.eq_var sv fr then t else sv), pos)
  
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

let rec formula_of_heap_1 h pos = mkBase h (P.mkTrue pos) top_flow [] pos

and formula_of_pure_1 p pos = mkBase HTrue p top_flow [] pos

and formula_of_heap_with_flow h f pos = mkBase h (P.mkTrue pos) f [] pos

and formula_of_pure_with_flow p f pos = mkBase HTrue p f [] pos


and isConstFalse f0 = match f0 with
  | Base f -> begin
	  let h, p = f.formula_base_heap, f.formula_base_pure in
		match h with
		  | HFalse -> true
		  | _ -> (P.isConstFalse p)
	end
  | _ -> false

and isConstTrue f0 = match f0 with
  | Base f -> begin
	  let h, p = f.formula_base_heap, f.formula_base_pure in
		match h with
		  | HTrue -> (P.isConstTrue p)
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
						formula_base_pos = pos }

and mkFalse flow pos = Base { formula_base_heap = HFalse;
						 formula_base_pure = P.mkFalse pos;
						 formula_base_flow = flow;
                         formula_base_branches = [];
						 formula_base_pos = pos }

and mkETrue flow pos = [EBase {
		 formula_ext_explicit_inst = [];
		 formula_ext_implicit_inst = [];
		 formula_ext_exists = [];
		 formula_ext_base = mkTrue flow pos;
		 formula_ext_continuation = [];
         (*formula_ext_complete = true;*)
		 formula_ext_pos = pos	}]

and mkEFalse flow pos =[EBase {
		 formula_ext_explicit_inst = [];
		 formula_ext_implicit_inst = [];
		 formula_ext_exists = [];
		 formula_ext_base = mkFalse flow pos;
		 formula_ext_continuation = [];
        (* formula_ext_complete = true;*)
		 formula_ext_pos = pos	}]
																				
and mkEOr f1 f2 pos = 
	if isEConstTrue f1 || isEConstTrue f2 then
	mkETrue top_flow pos
  else if isEConstFalse f1 then f2
  else if isEConstFalse f2 then f1
  else List.rev_append f1 f2

and mkEBase ei ii e b c com l= EBase {
						 	formula_ext_explicit_inst = ei;
						 	formula_ext_implicit_inst = ii;
							formula_ext_exists = e;
						 	formula_ext_base = b;				
						 	formula_ext_continuation = c;
                            (*formula_ext_complete = com;*)
						 	formula_ext_pos = l;}
  
and mkOr f1 f2 pos =
  let raw =  Or { formula_or_f1 = f1;
			formula_or_f2 = f2;
			formula_or_pos = pos } in
   if (formula_same_flow f1 f2) then
    if (isConstTrue f1) then f1
    else if (isConstTrue f2) then f2
    else if (isConstFalse f1) then f2
    else if (isConstFalse f2) then f1
    else raw
   else raw
      
and mkBase (h : h_formula) (p : P.formula) flow br pos = match h with
  | HFalse -> mkFalse flow pos
  | _ -> 
	  if P.isConstFalse p then 
		mkFalse flow pos 
	  else 
		Base { formula_base_heap = h;
			   formula_base_pure = p;
			   formula_base_flow = flow;
               formula_base_branches = br;
			   formula_base_pos = pos }

and mkExists (qvars : (ident * primed) list) (h : h_formula) (p : P.formula) flow br pos = match h with
  | HFalse -> mkFalse flow pos
  | _ ->
	  if P.isConstFalse p then
		mkFalse flow pos
	  else
		Exists { formula_exists_qvars = qvars;
             formula_exists_heap = h;
             formula_exists_pure = p;
             formula_exists_flow = flow;
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
  (* | HTrue -> f2 *)
  | _ -> match f2 with
	  | HFalse -> HFalse
	  (* | HTrue -> f1 *)
	  | _ -> Phase { h_formula_phase_rd = f1;
					h_formula_phase_rw = f2;
					h_formula_phase_pos = pos }

and mkHeapNode c id dr i f inv pd perm hl ofl l= HeapNode { 
                   h_formula_heap_node = c;
                   h_formula_heap_name = id;
                   h_formula_heap_derv = dr;
                   h_formula_heap_imm = i;
                   h_formula_heap_full = f;
                   h_formula_heap_with_inv = inv;
                   h_formula_heap_pseudo_data = pd;
                   h_formula_heap_perm = perm; (*LDK: perm from parser*)
                   h_formula_heap_arguments = hl;
                   h_formula_heap_label = ofl;
                   h_formula_heap_pos = l }
          
and mkHeapNode2 c id dr i f inv pd perm ohl ofl l = HeapNode2 { 
                    h_formula_heap2_node = c;
                    h_formula_heap2_name = id;
                    h_formula_heap2_derv = dr;
                    h_formula_heap2_imm = i;
                    h_formula_heap2_full = f;
                    h_formula_heap2_with_inv = inv;
                    h_formula_heap2_pseudo_data = pd;
                    h_formula_heap2_perm = perm; (*LDK: perm from parser*)
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
	(*| EVariance b -> b.formula_var_pos*)
 | EInfer b -> b.formula_inf_pos

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
  
  
let replace_branches b = function
  | Or f -> failwith "replace_branches doesn't expect an Or"
  | Base f -> Base {f with formula_base_branches = b;}
  | Exists f -> Exists {f with formula_exists_branches = b;}
;;

let flatten_branches p br =
  List.fold_left (fun p (l, f) -> P.And (p, f,no_pos)) p br
;;


(**
 * An Hoa : function to extract the root of a quantified id.
 **)
let extract_var_from_id (id,p) =
	let ids = Str.split (Str.regexp "\\.") id in
	let var = List.hd ids in
		(var,p)
;;


let fv_imm ann = match ann with
  | ConstAnn _ -> []
  | PolyAnn (id,_) -> [id]
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
(*WN:TODO:DONE*)
 | HeapNode {h_formula_heap_node = name ;
          (* An Hoa : problem detected and fix - name is a 
             quantified id so that we need to extract the 
             real information inside *)
              h_formula_heap_perm = perm; (*LDK*)
              h_formula_heap_imm = imm; 
              h_formula_heap_arguments = b} ->
     let perm_vars = fv_iperm perm in
     let imm_vars =  fv_imm imm in
     Gen.BList.remove_dups_eq (=) (imm_vars@perm_vars@((extract_var_from_id name):: (List.concat (List.map Ipure.afv b))))
  | HeapNode2 { h_formula_heap2_node = name ;
                h_formula_heap2_perm = perm; (*LDK*)
              h_formula_heap2_imm = imm; 
		h_formula_heap2_arguments = b}-> 
     let perm_vars =  fv_iperm perm in
     let imm_vars =  fv_imm imm in
      Gen.BList.remove_dups_eq (=)  (imm_vars@perm_vars@((extract_var_from_id name):: (List.concat (List.map (fun c-> (Ipure.afv (snd c))) b) )))
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
							(*| EVariance b -> helper b.formula_var_continuation*)
              | EInfer b -> helper b.formula_inf_continuation
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
	let rec helper f = match f with
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
		(*| EVariance b ->
			let fv_ex = List.fold_left (fun acc (expr, bound) -> 
        match bound with
        | None -> acc@(P.afv expr)
				| Some b_expr -> acc@(P.afv expr)@(P.afv b_expr)) [] b.formula_var_measures in
      let fv_infer = List.fold_left (fun acc exp -> acc @ (P.afv exp)) [] b.formula_var_infer in 
			let fv_co = helper b.formula_var_continuation in
			Gen.BList.remove_dups_eq (=) (fv_ex@fv_infer@fv_co)*)
  | EInfer b ->
    let fvc = helper b.formula_inf_continuation in
    Gen.BList.remove_dups_eq (=) fvc
	in Gen.BList.remove_dups_eq (=) (List.concat (List.map helper f0))
 
and struc_split_fv_debug f0 wi =
  Debug.no_2 "struc_split_fv" (!print_struc_formula) string_of_bool 
      (fun (l1,l2) -> (string_of_spec_var_list l1)^"|"^(string_of_spec_var_list l2)) struc_split_fv_a f0 wi

and struc_split_fv f0 wi =
  Debug.no_2 "struc_split_fv" (!print_struc_formula) string_of_bool 
      (fun (l1,l2) -> (string_of_spec_var_list l1)^"|"^(string_of_spec_var_list l2)) struc_split_fv_a f0 wi


and struc_split_fv_a (f0:struc_formula) with_inst:((ident*primed) list) * ((ident*primed) list)= 
	let rec helper f = match f with
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
		(*| EVariance b ->
			let prc, psc = helper b.formula_var_continuation in
			let fv_ex = List.fold_left (fun acc (expr, bound) -> 
        match bound with
        | None -> acc@(P.afv expr)
        | Some b_expr -> acc@(P.afv expr)@(P.afv b_expr)) [] b.formula_var_measures in
      let fv_infer = List.fold_left (fun acc exp -> acc@(P.afv exp)) [] b.formula_var_infer in
			(Gen.BList.remove_dups_eq (=) prc@fv_ex@fv_infer, Gen.BList.remove_dups_eq (=) psc)*)
		| EInfer b ->
    let prc, psc = helper b.formula_inf_continuation in
    (Gen.BList.remove_dups_eq (=) prc, Gen.BList.remove_dups_eq (=) psc)
	in
  let vl = List.map helper f0 in
  let prl, pcl = List.split vl in
	(Gen.BList.remove_dups_eq (=) (List.concat prl), Gen.BList.remove_dups_eq (=) (List.concat pcl))
 

and all_fv (f:formula):(ident*primed) list = match f with
	| Base b-> Gen.BList.remove_dups_eq (=) 
			(List.fold_left ( fun a (c1,c2)-> a@ (Ipure.fv c2)) ((h_fv b.formula_base_heap)@(Ipure.fv b.formula_base_pure))
							b.formula_base_branches )
	| Exists b-> 
		let r = List.fold_left ( fun a (c1,c2)-> a@ (Ipure.fv c2)) ((h_fv b.formula_exists_heap)@(Ipure.fv b.formula_exists_pure))
							b.formula_exists_branches in
		Gen.BList.difference_eq (=) (Gen.BList.remove_dups_eq (=) r) b.formula_exists_qvars 
	| Or b-> Gen.BList.remove_dups_eq (=) ((all_fv b.formula_or_f1)@(all_fv b.formula_or_f2))
	
and add_quantifiers (qvars : (ident*primed) list) (f : formula) : formula = match f with
  | Base ({ formula_base_heap = h; 
            formula_base_pure = p; 
            formula_base_branches = b;
           formula_base_flow = f;
           formula_base_pos = pos}) -> mkExists qvars h p f b pos
  | Exists ({formula_exists_qvars = qvs; 
             formula_exists_heap = h; 
             formula_exists_pure = p; 
             formula_exists_flow = f;
             formula_exists_branches = b;
             formula_exists_pos = pos}) -> 
	  let new_qvars = Gen.BList.remove_dups_eq (=) (qvs @ qvars) in
		mkExists new_qvars h p f b pos
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
                    (*formula_ext_complete = true;*)
		 			formula_ext_pos = b.formula_base_pos})]
		| Exists b-> [EBase ({
			 		formula_ext_explicit_inst =[];
		 			formula_ext_implicit_inst = [];
					formula_ext_exists = [];
		 			formula_ext_base = f;
					formula_ext_continuation = [];
                    (*formula_ext_complete = true;*)
		 			formula_ext_pos = b.formula_exists_pos})]
		| Or b->  (helper b.formula_or_f1)@(helper b.formula_or_f2) in			
	Debug.no_1 "formula_to_struc_formula" !print_formula !print_struc_formula helper f;;
  
(* split a conjunction into heap constraints, pure pointer constraints, *)
(* and Presburger constraints *)
let split_components (f : formula) =  match f with
    | Base ({formula_base_heap = h; 
	  formula_base_pure = p; 
      formula_base_branches = b;
	  formula_base_flow =fl }) -> (h, p, fl, b)
    | Exists ({formula_exists_heap = h; 
	  formula_exists_pure = p; 
	  formula_exists_flow = fl;
      formula_exists_branches = br }) -> (h, p, fl, br)
    | _ -> failwith ("split_components: don't expect OR")

let split_quantifiers (f : formula) : ( (ident * primed) list * formula) = match f with
  | Exists ({formula_exists_qvars = qvars; 
			 formula_exists_heap =  h; 
			 formula_exists_pure = p; 
			 formula_exists_flow = f;
			 formula_exists_branches = br; 
			 formula_exists_pos = pos}) -> 
      (qvars, mkBase h p f br pos)
  | Base _ -> ([], f)
  | _ -> failwith ("split_quantifiers: invalid argument")

(*var substitution*)

let rec subst sst (f : formula) = match sst with
  | s :: rest -> subst rest (apply_one s f)
  | [] -> f 
        
and subst_var (fr, t) (o : (ident*primed)) = if (Ipure.eq_var fr o) then t else o
and subst_var_list ft (o : (ident*primed)) = 
  let r = List.filter (fun (c1,c2)-> (Ipure.eq_var c1 o) ) ft in
  match r with 
    | [] -> o
    | _ -> snd (List.hd r)

and apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
        Or ({formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h;
	formula_base_pure = p;
	formula_base_flow = fl;
	formula_base_branches = br;
	formula_base_pos = pos }) -> 
        Base ({formula_base_heap = h_apply_one s h; 
		formula_base_pure = Ipure.apply_one s p;
		formula_base_flow = fl;
		formula_base_branches = List.map (fun (c1,c2)-> (c1,(Ipure.apply_one s c2))) br;
		formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
	formula_exists_heap = qh; 
	formula_exists_pure = qp; 
	formula_exists_flow = fl;
	formula_exists_branches = br;
	formula_exists_pos = pos}) -> 
	    if List.mem (fst fr) (List.map fst qsv) then f 
	    else Exists ({formula_exists_qvars = qsv; 
		formula_exists_heap =  h_apply_one s qh; 
		formula_exists_pure = Ipure.apply_one s qp; 
		formula_exists_flow = fl;
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
	h_formula_heap_derv = dr; 
	h_formula_heap_imm = imm; 
	h_formula_heap_full = full; 
	h_formula_heap_with_inv = winv;
	h_formula_heap_perm = perm; (*LDK*)
	h_formula_heap_arguments = args;
	h_formula_heap_pseudo_data = ps_data;
	h_formula_heap_label = l;
	h_formula_heap_pos = pos}) -> 
      let imm = apply_one_imm s imm in
      let perm1 = match perm with
        | Some f -> Some (apply_one_iperm s f)
        | None -> None
      in HeapNode ({h_formula_heap_node = subst_var s x; 
		h_formula_heap_name = c;
	    h_formula_heap_derv = dr; 
		h_formula_heap_imm = imm; 
		h_formula_heap_full = full;
		h_formula_heap_with_inv = winv;
		h_formula_heap_perm = perm1 ; (*LDK*)
		h_formula_heap_arguments = List.map (Ipure.e_apply_one s) args;
		h_formula_heap_pseudo_data = ps_data;
		h_formula_heap_label = l;
		h_formula_heap_pos = pos})
  | HeapNode2 ({
		h_formula_heap2_node = x;
		h_formula_heap2_name = c;
	    h_formula_heap2_derv = dr; 
		h_formula_heap2_imm = imm;
		h_formula_heap2_full = full;
		h_formula_heap2_with_inv = winv;
		h_formula_heap2_arguments = args;
	    h_formula_heap2_perm = perm; (*LDK*)
		h_formula_heap2_pseudo_data = ps_data;
		h_formula_heap2_label = l;
		h_formula_heap2_pos= pos}) -> 
      let imm = apply_one_imm s imm in
      let perm1 = match perm with
        | Some f -> Some (apply_one_iperm s f)
        | None -> None
      in
        HeapNode2 ({
		    h_formula_heap2_node = subst_var s x;
		    h_formula_heap2_name =c;
	        h_formula_heap2_derv = dr; 
		    h_formula_heap2_imm = imm;
		    h_formula_heap2_full =full;
		    h_formula_heap2_with_inv = winv;
		    h_formula_heap2_perm = perm1; (*LDK*)
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
	  formula_base_flow = fl;
	  formula_base_branches = br;  
	  formula_base_pos = pos}) -> mkExists qvars h p fl br pos
    | Exists ({formula_exists_qvars = qvs; 
	  formula_exists_heap = h; 
	  formula_exists_pure = p;
	  formula_exists_flow = fl;
	  formula_exists_branches = br;  
	  formula_exists_pos = pos}) -> 
	      let new_qvars = Gen.BList.remove_dups_eq (=) (qvs @ qvars) in
		  mkExists new_qvars h p fl br pos
    | _ -> failwith ("add_quantifiers: invalid argument") in		
  match f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	      let rf1 = rename_bound_vars f1 in
	      let rf2 = rename_bound_vars f2 in
	      let resform = mkOr rf1 rf2 pos in
		  resform
    | Base _ -> f
    | Exists _ ->
				let _=print_endline ("Exists: rename bound vars") in
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
             (* formula_ext_complete = b.formula_ext_complete;*)
			  formula_ext_pos = b.formula_ext_pos	})
	(*| EVariance b ->
		  (* let subst_list_of_pair sst ls = match sst with
			 | [] -> ls
			 | s::rest -> subst_list_of_pair rest (Ipure.e_apply_one_list_of_pair s ls) in *)
		  let subst_measures = P.subst_list_of_pair sst b.formula_var_measures in
		  let subst_infer = P.subst_list_of_exp sst b.formula_var_infer in
		  let subst_cont = helper b.formula_var_continuation in
		  EVariance {b with
			  formula_var_measures = subst_measures;
			  formula_var_infer = subst_infer;
			  formula_var_continuation = subst_cont
		  }*)
  | EInfer b ->
    let si = List.map (subst_var_list sst) b.formula_inf_vars in
    let sc = helper b.formula_inf_continuation in
    EInfer {b with
      formula_inf_vars = si;
      formula_inf_continuation = sc;
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
		(*| EVariance b -> EVariance ({ b with
        formula_var_continuation = helper b.formula_var_continuation;
			})*)
  | EInfer b -> EInfer {b with
    (* Need to check again *)
    formula_inf_continuation = helper b.formula_inf_continuation;}
			in
	List.map helper f


and float_out_exps_from_heap (f:formula ):formula = float_out_exps_from_heap_x f
(* let pr = Iprinter.string_of_formula in *)
(* Debug.no_1 "float_out_exps_from_heap" pr pr float_out_exps_from_heap_x f *)

and float_out_exps_from_heap_x (f:formula ):formula = 
	
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
        (*LDK*)
        let perm = b.h_formula_heap_perm in
        let na_perm, ls_perm = float_out_iperm perm b.h_formula_heap_pos in
        let na,ls = List.split (List.map (fun c->
			match c with
			  | Ipure.Var _ -> (c,[])
			  | _ ->
				  let nn = (("flted_"^(string_of_int b.h_formula_heap_pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
				  let nv = Ipure.Var (nn,b.h_formula_heap_pos) in
				  let npf = 
					if !Globals.do_slicing then
                      try
                          let lexp = P.find_lexp_exp c !Ipure.linking_exp_list in
                                (*let _ = Hashtbl.remove !Ipure.linking_exp_list c in*)
						  Ipure.BForm ((Ipure.Eq (nv,c,b.h_formula_heap_pos), (Some (false, fresh_int(), lexp))), None)
                      with Not_found ->
						  Ipure.BForm ((Ipure.Eq (nv,c,b.h_formula_heap_pos), None), None)
                    else
                      Ipure.BForm ((Ipure.Eq (nv,c,b.h_formula_heap_pos), None), None) 
                        (* Slicing: TODO IL for linking exp *)
                  in
				  (nv,[(nn,npf)])) b.h_formula_heap_arguments) in
	    (HeapNode ({b with h_formula_heap_arguments = na; h_formula_heap_perm = na_perm}),(List.concat (ls_perm ::ls)))
    | HeapNode2 b ->
        (*LDK*)
        let perm = b.h_formula_heap2_perm in
        let na_perm, ls_perm = float_out_iperm perm b.h_formula_heap2_pos in
        let na,ls = List.split (List.map (fun c->
	        match (snd c) with
	          | Ipure.Var _ -> (c,[])
	          | _ -> 
		          let nn = (("flted_"^(string_of_int b.h_formula_heap2_pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
		          let nv = Ipure.Var (nn,b.h_formula_heap2_pos) in

		          let npf =
			        if !Globals.do_slicing then
			          try
				          let lexp = P.find_lexp_exp (snd c) !Ipure.linking_exp_list in
				  (*let _ = Hashtbl.remove !Ipure.linking_exp_list (snd c) in*)
				          Ipure.BForm ((Ipure.Eq (nv,(snd c),b.h_formula_heap2_pos), (Some (false, fresh_int(), lexp))), None)
			          with Not_found ->
				          Ipure.BForm ((Ipure.Eq (nv,(snd c),b.h_formula_heap2_pos), None), None)
			        else Ipure.BForm ((Ipure.Eq (nv,(snd c),b.h_formula_heap2_pos), None), None) in (* Slicing: TODO *)
		          (((fst c),nv),[(nn,npf)])) b.h_formula_heap2_arguments) in
        (HeapNode2 ({b with h_formula_heap2_arguments = na;h_formula_heap2_perm = na_perm}),(List.concat (ls_perm :: ls)))
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
		      formula_exists_pos = b.formula_base_pos
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
			formula_exists_pos = b.formula_exists_pos
		      })	
    | Or b-> Or ({
		   formula_or_f1 = float_out_exps_from_heap b.formula_or_f1;
		   formula_or_f2 = float_out_exps_from_heap b.formula_or_f2;
		   formula_or_pos = b.formula_or_pos
		 })		
  in helper f

       
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
                (* formula_ext_complete = b.formula_ext_complete;*)
				 formula_ext_pos = b.formula_ext_pos			
				})
		(*| EVariance b -> EVariance ({ b with
			  formula_var_continuation = helper b.formula_var_continuation;
			})*)
    | EInfer b -> EInfer ({b with 
      formula_inf_continuation = helper b.formula_inf_continuation;})
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
         formula_base_pure = p0
      } ->
      let (nh, nhpf) = float_out_heap_min_max h0 in
      let np = Ipure.float_out_pure_min_max p0 in
         Base
          {
             formula_base_pos = l;
             formula_base_heap = nh;
			 formula_base_flow = fl;
             formula_base_branches = (List.map (fun (l, f) -> (l, Ipure.float_out_pure_min_max f)) br);
             formula_base_pure =
              (match nhpf with
               | None -> np
               | Some e1 -> Ipure.And (np, e1, l));
          }
  |  Exists
      {
         formula_exists_qvars = qv;
         formula_exists_heap = h0;
         formula_exists_pure = p0;
		 formula_exists_flow = fl;
         formula_exists_branches = br;
         formula_exists_pos = l
      } ->
      let (nh, nhpf) = float_out_heap_min_max h0 in
      let np = Ipure.float_out_pure_min_max p0 in
         Exists
          {
             formula_exists_qvars = qv;
             formula_exists_heap = nh;
			 formula_exists_flow =fl;
             formula_exists_pure =
              (match nhpf with
               | None -> np
               | Some e1 -> (Ipure.And (np, e1, l)));
             formula_exists_branches = (List.map (fun (l, f) -> (l, Ipure.float_out_pure_min_max f)) br);
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

(*LDK: move them to ipure.ml*)
(* and float_out_exp_min_max (e: Ipure.exp): (Ipure.exp * (Ipure.formula * (string list) ) option) = match e with  *)
(*   | Ipure.Null _ -> (e, None) *)
(*   | Ipure.Var _ -> (e, None) *)
(*   | Ipure.IConst _ -> (e, None) *)
(*  | Ipure.Ann_Exp (e,_) -> float_out_exp_min_max e *)
(*   | Ipure.Add (e1, e2, l) -> *)
(* 			let ne1, np1 = float_out_exp_min_max e1 in *)
(* 			let ne2, np2 = float_out_exp_min_max e2 in *)
(* 			let r = match (np1, np2) with *)
(* 					| None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))in *)
(* 			(Ipure.Add (ne1, ne2, l), r)  *)
(*   | Ipure.Subtract (e1, e2, l) -> *)
(* 			let ne1, np1 = float_out_exp_min_max e1 in *)
(* 			let ne2, np2 = float_out_exp_min_max e2 in *)
(* 			let r = match (np1, np2) with *)
(* 					| None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))in *)
(* 			(Ipure.Subtract (ne1, ne2, l), r)  *)
(*   | Ipure.Mult (e1, e2, l) -> *)
(*       let ne1, np1 = float_out_exp_min_max e1 in *)
(*       let ne2, np2 = float_out_exp_min_max e2 in *)
(*       let r = match np1, np2 with *)
(*         | None, None -> None *)
(*         | Some p, None -> Some p *)
(*         | None, Some p -> Some p *)
(*         | Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2)) *)
(*       in (Ipure.Mult (ne1, ne2, l), r) *)
(*   | Ipure.Div (e1, e2, l) -> *)
(*       let ne1, np1 = float_out_exp_min_max e1 in *)
(*       let ne2, np2 = float_out_exp_min_max e2 in *)
(*       let r = match np1, np2 with *)
(*         | None, None -> None *)
(*         | Some p, None -> Some p *)
(*         | None, Some p -> Some p *)
(*         | Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2)) *)
(*       in (Ipure.Div (ne1, ne2, l), r)						  *)
(*   | Ipure.Max (e1, e2, l) -> *)
(* 			let ne1, np1 = float_out_exp_min_max e1 in *)
(* 			let ne2, np2 = float_out_exp_min_max e2 in *)
(* 			let new_name = ("max"^(fresh_trailer())) in *)
(* 			let nv = Ipure.Var((new_name, Unprimed), l) in *)
(* 			let lexp = P.find_lexp_exp e !linking_exp_list in (\* find the linking exp inside Max *\) *)
(* 			let t = Ipure.BForm ((Ipure.EqMax(nv, ne1, ne2, l), Some(false, Globals.fresh_int(), lexp)), None) in *)
(* 			(\* $ h = 1 + max(h1, h2) -> <$,_> h = 1 + max_1 & <_,_> max_1 = max(h1, h2) ==> h is still separated from h1, h2 *\) *)
(* 			let r = match (np1, np2) with *)
(* 					| None, None -> Some (t,[new_name]) *)
(* 					| Some (p1, l1), None -> Some ((Ipure.And(p1, t, l)), (new_name:: l1)) *)
(* 					| None, Some (p1, l1) -> Some ((Ipure.And(p1, t, l)), (new_name:: l1)) *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And ((Ipure.And (p1, t, l)), p2, l)), new_name:: (List.rev_append l1 l2)) in *)
(* 			(nv, r)  *)
			
			
(*   | Ipure.Min (e1, e2, l) -> *)
(* 			let ne1, np1 = float_out_exp_min_max e1 in *)
(* 			let ne2, np2 = float_out_exp_min_max e2 in *)
(* 			let new_name = ("min"^(fresh_trailer())) in *)
(* 			let nv = Ipure.Var((new_name, Unprimed), l) in *)
(* 			let lexp = P.find_lexp_exp e !linking_exp_list in (\* find the linking exp inside Min *\) *)
(* 			let t = Ipure.BForm ((Ipure.EqMin(nv, ne1, ne2, l), Some(false, Globals.fresh_int(), lexp)), None) in  *)
(* 			let r = match (np1, np2) with *)
(* 					| None, None -> Some (t,[new_name]) *)
(* 					| Some (p1, l1), None -> Some ((Ipure.And(p1, t, l)), (new_name:: l1)) *)
(* 					| None, Some (p2, l2) -> Some ((Ipure.And(p2, t, l)), (new_name:: l2)) *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And ((Ipure.And (p1, t, l)), p2, l)), new_name:: (List.rev_append l1 l2)) in *)
(* 			(nv, r)  *)
	
(* 		(\* bag expressions *\) *)
(*   | Ipure.Bag (le, l) -> *)
(* 			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in *)
(* 			let r = List.fold_left (fun a c -> match (a, c)with *)
(* 				  | None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in *)
(* 			(Ipure.Bag (ne1, l), r) *)
(*   | Ipure.BagUnion (le, l) -> *)
(* 			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in *)
(* 			let r = List.fold_left (fun a c -> match (a, c)with *)
(* 				  | None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in *)
(* 			(Ipure.BagUnion (ne1, l), r) *)
(*   | Ipure.BagIntersect (le, l) -> *)
(* 			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in *)
(* 			let r = List.fold_left (fun a c -> match (a, c)with *)
(* 				  | None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), List.rev_append l1 l2)) None np1 in *)
(* 			(Ipure.BagIntersect (ne1, l), r) *)
(*   | Ipure.BagDiff (e1, e2, l) -> *)
(* 			let ne1, np1 = float_out_exp_min_max e1 in *)
(* 			let ne2, np2 = float_out_exp_min_max e2 in *)
(* 			let r = match (np1, np2) with *)
(* 					| None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2)) in *)
(* 			(Ipure.BagDiff (ne1, ne2, l), r)  *)
(* 		(\* list expressions *\) *)
(*   | Ipure.List (le, l) -> *)
(* 			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in *)
(* 			let r = List.fold_left (fun a c -> match (a, c) with *)
(* 				  | None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in *)
(* 			(Ipure.List (ne1, l), r) *)
(*   | Ipure.ListAppend (le, l) -> *)
(* 			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in *)
(* 			let r = List.fold_left (fun a c -> match (a, c) with *)
(* 				  | None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in *)
(* 			(Ipure.ListAppend (ne1, l), r) *)
(*   | Ipure.ListCons (e1, e2, l) ->  *)
(* 			let ne1, np1 = float_out_exp_min_max e1 in *)
(* 			let ne2, np2 = float_out_exp_min_max e2 in *)
(* 			let r = match (np1, np2) with *)
(* 					| None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2)) in *)
(* 			(Ipure.ListCons (ne1, ne2, l), r)  *)
(*   | Ipure.ListHead (e, l) ->  *)
(* 			let ne1, np1 = float_out_exp_min_max e in *)
(* 			(Ipure.ListHead (ne1, l), np1) *)
(*   | Ipure.ListTail (e, l) ->  *)
(* 			let ne1, np1 = float_out_exp_min_max e in *)
(* 			(Ipure.ListTail (ne1, l), np1) *)
(*   | Ipure.ListLength (e, l) ->  *)
(* 			let ne1, np1 = float_out_exp_min_max e in *)
(* 			(Ipure.ListLength (ne1, l), np1) *)
(*   | Ipure.ListReverse (e, l) ->  *)
(* 			let ne1, np1 = float_out_exp_min_max e in *)
(* 			(Ipure.ListReverse (ne1, l), np1) *)
(* 	(\* An Hoa : get rid of min/max in a[i] *\) *)
(*   | Ipure.ArrayAt (a, i, l) -> *)
(*   			let ne1, np1 = List.split (List.map float_out_exp_min_max i) in *)
(* 			let r = List.fold_left (fun a c -> match (a, c) with *)
(* 				  	| None, None -> None *)
(* 					| Some p, None -> Some p *)
(* 					| None, Some p -> Some p *)
(* 					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in *)
(* 			(Ipure.ArrayAt (a, ne1, l), r) *)

(* and float_out_pure_min_max (p : Ipure.formula) : Ipure.formula = *)
		
(* 		let add_exists (t: Ipure.formula)(np1: (Ipure.formula * (string list))option)(np2: (Ipure.formula * (string list))option) l: Ipure.formula =  *)
(* 			let r, ev = match np1 with *)
(* 							| None -> (t,[]) *)
(* 							| Some (p1, ev1) -> (Ipure.And (t, p1, l), ev1) in *)
(* 			let r, ev2 = match np2 with  *)
(* 							| None -> (r, ev) *)
(* 							| Some (p1, ev1) -> (Ipure.And(r, p1, l), (List.rev_append ev1 ev)) in  *)
(* 		  List.fold_left (fun a c -> (Ipure.Exists ((c, Unprimed), a, None,l))) r ev2 in *)
		
(* 		(\* An Hoa : produce exists x_1 exists x_2 ... exists x_n t *\)	 *)
(* 		(\*let add_exists (t: Ipure.formula) (nps: (Ipure.formula * (string list))option list) l: Ipure.formula = 			 *)
(* 			let r, ev = match np1 with *)
(* 							| None -> (t,[]) *)
(* 							| Some (p1, ev1) -> (Ipure.And (t, p1, l), ev1) in *)
(* 			let r, ev2 = match np2 with  *)
(* 							| None -> (r, ev) *)
(* 							| Some (p1, ev1) -> (Ipure.And(r, p1, l), (List.rev_append ev1 ev)) in *)
(* 		  List.fold_left (fun fml np -> let r, ev = match np1 with *)
(* 							| None -> fml *)
(* 							| Some (p, ev) -> (Ipure.And (t, p1, l), ev)) *)
(* 				 t *)
(* 				 nps *)
(* 		  List.fold_left (fun a c -> (Ipure.Exists ((c, Unprimed), a, None,l))) r ev2 in *\)							 *)
(* 		(\* End add_exists *\) *)
				
(* 		let rec float_out_b_formula_min_max (b: Ipure.b_formula) lbl: Ipure.formula = *)
(* 		  let (pf,il) = b in *)
(* 		  match pf with *)
(* 		  | Ipure.BConst _ -> Ipure.BForm (b,lbl) *)
(* 		  | Ipure.BVar _ -> Ipure.BForm (b,lbl) *)
(* 		  | Ipure.Lt (e1, e2, l) -> *)
(* 						let ne1, np1 = float_out_exp_min_max e1 in *)
(* 						let ne2, np2 = float_out_exp_min_max e2 in *)
(* 						let t = Ipure.BForm ((Ipure.Lt (ne1, ne2, l), il), lbl) in *)
(* 						add_exists t np1 np2 l *)
(* 		  | Ipure.Lte (e1, e2, l) -> *)
(* 						let ne1, np1 = float_out_exp_min_max e1 in *)
(* 						let ne2, np2 = float_out_exp_min_max e2 in *)
(* 						let t = Ipure.BForm ((Ipure.Lte (ne1, ne2, l), il),lbl) in *)
(* 						add_exists t np1 np2 l *)
(* 		  | Ipure.Gt (e1, e2, l) -> *)
(* 						let ne1, np1 = float_out_exp_min_max e1 in *)
(* 						let ne2, np2 = float_out_exp_min_max e2 in *)
(* 						let t = Ipure.BForm ((Ipure.Gt (ne1, ne2, l), il), lbl) in *)
(* 						add_exists t np1 np2 l *)
(* 		  | Ipure.Gte (e1, e2, l) -> *)
(* 						let ne1, np1 = float_out_exp_min_max e1 in *)
(* 						let ne2, np2 = float_out_exp_min_max e2 in *)
(* 						let t = Ipure.BForm ((Ipure.Gte (ne1, ne2, l), il), lbl) in *)
(* 						add_exists t np1 np2 l *)
(* 		  | Ipure.Eq (e1, e2, l) -> *)
(* 						let r = match e1 with *)
(* 							| Ipure.Min(v1, v2, v3) -> let r2 = match e2 with *)
(* 																	| Ipure.Null _ *)
(* 																	| Ipure.IConst _ *)
(*                                   | Ipure.FConst _ *)
(* 																	| Ipure.Var _ -> *)
(* 																			 let ne1 , np1 = float_out_exp_min_max v1 in *)
(* 																			 let ne2 , np2 = float_out_exp_min_max v2 in *)
(* 																			 let t = Ipure.BForm((Ipure.EqMin(e2, ne1, ne2, l), il), lbl) in *)
(* 																			 add_exists t np1 np2 l *)
(* 																	| _ ->  *)
(* 																			 let ne1, np1 = float_out_exp_min_max e1 in *)
(* 																			 let ne2, np2 = float_out_exp_min_max e2 in *)
(* 																			 let t = Ipure.BForm ((Ipure.Eq (ne1, ne2, l), il), lbl) in *)
(* 																			 add_exists t np1 np2 l  in r2 *)
(* 							| Ipure.Max(v1, v2, v3) -> let r2 = match e2 with *)
(* 																						| Ipure.Null _ *)
(* 																						| Ipure.IConst _ *)
(*                                             | Ipure.FConst _ *)
(* 																						| Ipure.Var _ -> *)
(* 																								 let ne1 , np1 = float_out_exp_min_max v1 in *)
(* 																								 let ne2 , np2 = float_out_exp_min_max v2 in *)
(* 																								 let t = Ipure.BForm ((Ipure.EqMax(e2, ne1, ne2, l), il), lbl) in *)
(* 																								 add_exists t np1 np2 l *)
(* 																						| _ ->  *)
(* 																							let ne1, np1 = float_out_exp_min_max e1 in *)
(* 																							let ne2, np2 = float_out_exp_min_max e2 in *)
(* 																							let t = Ipure.BForm ((Ipure.Eq (ne1, ne2, l), il), lbl) in *)
(* 																							add_exists t np1 np2 l  *)
(* 																			in r2 *)
(* 							| Ipure.Null _ *)
(* 							| Ipure.IConst _ *)
(*               | Ipure.FConst _ *)
(* 							| Ipure.Var _ -> let r2 = match e2 with *)
(* 																					| Ipure.Min (v1, v2, v3) -> *)
(* 																						 	 let ne1 , np1 = float_out_exp_min_max v1 in *)
(* 																							 let ne2 , np2 = float_out_exp_min_max v2 in *)
(* 																							 let t = Ipure.BForm ((Ipure.EqMin(e1, ne1, ne2, l), il), lbl) in *)
(* 																							 add_exists t np1 np2 l *)
(* 																					| Ipure.Max (v1, v2, v3) -> *)
(* 																							 let ne1 , np1 = float_out_exp_min_max v1 in *)
(* 																							 let ne2 , np2 = float_out_exp_min_max v2 in *)
(* 																							 let t = Ipure.BForm ((Ipure.EqMax(e1, ne1, ne2, l), il), lbl) in *)
(* 																							 add_exists t np1 np2 l *)
(* 																					| _ ->  *)
(* 																						let ne1, np1 = float_out_exp_min_max e1 in *)
(* 																						let ne2, np2 = float_out_exp_min_max e2 in *)
(* 																						let t = Ipure.BForm ((Ipure.Eq (ne1, ne2, l), il), lbl) in *)
(* 																						add_exists t np1 np2 l  *)
(* 																in r2 *)
(* 							| _ -> *)
(* 									let ne1, np1 = float_out_exp_min_max e1 in *)
(* 									let ne2, np2 = float_out_exp_min_max e2 in *)
(* 									let t = Ipure.BForm ((Ipure.Eq (ne1, ne2, l), il), lbl) in *)
(* 									add_exists t np1 np2 l  *)
(* 							in r *)
(* 		  | Ipure.Neq (e1, e2, l) -> *)
(* 						let ne1, np1 = float_out_exp_min_max e1 in *)
(* 						let ne2, np2 = float_out_exp_min_max e2 in *)
(* 						let t = Ipure.BForm ((Ipure.Neq (ne1, ne2, l), il), lbl) in *)
(* 						add_exists t np1 np2 l *)
(* 		  | Ipure.EqMax (e1, e2, e3, l) -> *)
(* 						let ne1, np1 = float_out_exp_min_max e1 in *)
(* 						let ne2, np2 = float_out_exp_min_max e2 in *)
(* 						let ne3, np3 = float_out_exp_min_max e3 in *)
(* 						let t = Ipure.BForm ((Ipure.EqMax (ne1, ne2, ne3, l), il), lbl) in *)
(* 						let t = add_exists t np1 np2 l in *)
(* 						let r = match np3 with  *)
(* 							| None -> t *)
(* 							| Some (p1, l1) -> List.fold_left (fun a c -> (Ipure.Exists ((c, Unprimed), a, lbl, l))) (Ipure.And(t, p1, l)) l1 in r *)
(* 		  | Ipure.EqMin (e1, e2, e3, l) -> *)
(* 						let ne1, np1 = float_out_exp_min_max e1 in *)
(* 						let ne2, np2 = float_out_exp_min_max e2 in *)
(* 						let ne3, np3 = float_out_exp_min_max e3 in *)
(* 						let t = Ipure.BForm ((Ipure.EqMin (ne1, ne2, ne3, l), il), lbl) in *)
(* 						let t = add_exists t np1 np2 l in *)
(* 						let r = match np3 with  *)
(* 							| None -> t *)
(* 							| Some (p1, l1) -> List.fold_left (fun a c -> Ipure.Exists ((c, Unprimed), a, lbl, l)) (Ipure.And(t, p1, l)) l1 in r *)
(* 		  | Ipure.BagIn (v, e, l) ->  *)
(* 							let ne1, np1 = float_out_exp_min_max e in *)
(* 							let r = match np1 with *)
(* 								| None -> Ipure.BForm ((Ipure.BagIn(v, ne1, l), il), lbl) *)
(* 								| Some (r, l1) -> List.fold_left (fun a c -> Ipure.Exists ((c, Unprimed), a, lbl, l)) (Ipure.And (Ipure.BForm ((Ipure.BagIn(v, ne1, l), il), lbl), r, l)) l1 in r  *)
(* 		  | Ipure.BagNotIn (v, e, l) ->  *)
(* 							let ne1, np1 = float_out_exp_min_max e in *)
(* 							let r = match np1 with *)
(* 								| None -> Ipure.BForm ((Ipure.BagNotIn(v, ne1, l), il), lbl) *)
(* 								| Some (r, l1) -> List.fold_left (fun a c -> Ipure.Exists ((c, Unprimed), a, lbl,  l)) (Ipure.And (Ipure.BForm ((Ipure.BagIn(v, ne1, l), il), lbl), r, l)) l1 in r *)
(* 		  | Ipure.BagSub (e1, e2, l) -> *)
(* 					let ne1, np1 = float_out_exp_min_max e1 in *)
(* 					let ne2, np2 = float_out_exp_min_max e2 in *)
(* 					let t = Ipure.BForm ((Ipure.BagSub (ne1, ne2, l), il), lbl) in *)
(* 					add_exists t np1 np2 l *)
(* 		  | Ipure.BagMin _ -> Ipure.BForm (b,lbl) *)
(* 		  | Ipure.BagMax _ -> Ipure.BForm (b,lbl)	 *)
(* 		  | Ipure.ListIn (e1, e2, l) ->  *)
(* 					let ne1, np1 = float_out_exp_min_max e1 in *)
(* 					let ne2, np2 = float_out_exp_min_max e2 in *)
(* 					let t = Ipure.BForm ((Ipure.ListIn (ne1, ne2, l), il), lbl) in *)
(* 					add_exists t np1 np2 l *)
(* 		  | Ipure.ListNotIn (e1, e2, l) ->  *)
(* 					let ne1, np1 = float_out_exp_min_max e1 in *)
(* 					let ne2, np2 = float_out_exp_min_max e2 in *)
(* 					let t = Ipure.BForm ((Ipure.ListNotIn (ne1, ne2, l), il), lbl) in *)
(* 					add_exists t np1 np2 l *)
(* 		  | Ipure.ListAllN (e1, e2, l) -> *)
(* 					let ne1, np1 = float_out_exp_min_max e1 in *)
(* 					let ne2, np2 = float_out_exp_min_max e2 in *)
(* 					let t = Ipure.BForm ((Ipure.ListAllN (ne1, ne2, l), il), lbl) in *)
(* 					add_exists t np1 np2 l *)
(* 		  | Ipure.ListPerm (e1, e2, l) -> *)
(* 					let ne1, np1 = float_out_exp_min_max e1 in *)
(* 					let ne2, np2 = float_out_exp_min_max e2 in *)
(* 					let t = Ipure.BForm ((Ipure.ListPerm (ne1, ne2, l), il), lbl) in *)
(* 					add_exists t np1 np2 l *)
(* 			(\* An Hoa : handle relation *\) *)
(* 			(\* TODO Have to add the existential before the formula! Add a add_exists with a list instead *\) *)
(* 			| Ipure.RelForm (r, args, l) -> *)
(* 					let nargs = List.map float_out_exp_min_max args in *)
(* 					let nargse = List.map fst nargs in *)
(* 					let t = Ipure.BForm ((Ipure.RelForm (r, nargse, l), il), lbl) in *)
(* 					t *)
(* 			in		  *)
(* 		match p with *)
(* 			| Ipure.BForm (b,lbl) -> (float_out_b_formula_min_max b lbl) *)
(*   		| Ipure.And (f1, f2, l) -> Ipure.And((float_out_pure_min_max f1), (float_out_pure_min_max f2), l) *)
(*   		| Ipure.Or (f1, f2, lbl, l) -> Ipure.Or((float_out_pure_min_max f1), (float_out_pure_min_max f2), lbl,l) *)
(*   		| Ipure.Not (f1,lbl, l) -> Ipure.Not((float_out_pure_min_max f1), lbl, l) *)
(*   		| Ipure.Forall (v, f1, lbl, l) -> Ipure.Forall (v, (float_out_pure_min_max f1), lbl, l) *)
(*   		| Ipure.Exists (v, f1, lbl, l) -> Ipure.Exists (v, (float_out_pure_min_max f1), lbl, l) *)
		

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
	    let l = h1. h_formula_heap_pos in
	    let args = h1.h_formula_heap_arguments in
        (*LDK*)
	    let perm = h1.h_formula_heap_perm in
	    let nl_perm, new_p_perm = float_out_mix_max_iperm perm l in
	          let nl, new_p =
	            List.fold_left
                    (fun (a, c) d -> 
	                    match d with
		                  | Ipure.Null _ 
		                  | Ipure.IConst _
		                  | Ipure.Var _ -> (d::a, c)
		                  | _ -> 
		                      let new_name = fresh_var_name "ptr" l.start_pos.Lexing.pos_lnum in 
		                      let nv = Ipure.Var((new_name, Unprimed), l) in
		                      (nv::a, let lexp = P.find_lexp_exp d !Ipure.linking_exp_list 
				                      in match c with
		                                | None -> Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d, l), Some (false, fresh_int(), lexp)), None)))
		                                | Some s -> Some (Ipure.And ((Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d, l), Some (false, fresh_int(), lexp)), None))), s, l)))) ([], new_p_perm) args in
              (( HeapNode { h1 with  h_formula_heap_arguments = (List.rev nl); h_formula_heap_perm = nl_perm}), new_p)
    |  HeapNode2 h1 ->
	    let l = h1. h_formula_heap2_pos in
	    let args = h1. h_formula_heap2_arguments in
	    let perm = h1. h_formula_heap2_perm in
	    let nl_perm, new_p_perm = float_out_mix_max_iperm perm l in
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

			            ((d1,nv):: a, 
                         let lexp = P.find_lexp_exp d2 !Ipure.linking_exp_list in 
                         match c with
			               | None -> Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d2, l), Some (false, fresh_int(), lexp)), None)))
			               | Some s -> Some (Ipure.And ((Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv, d2, l), Some (false, fresh_int(), lexp)), None)) ), s, l)))) ([], new_p_perm) args 
        in
        (( HeapNode2 { h1 with  h_formula_heap2_arguments = (List.rev nl);h_formula_heap2_perm = nl_perm;}), new_p)
    |  HTrue -> (h, None)
    |  HFalse -> (h, None)
	 
  
and float_out_struc_min_max (f0 : struc_formula): struc_formula = 
	let rec helper (f0: ext_formula):ext_formula = match f0 with
		| EAssume (b,tag) -> EAssume ((float_out_min_max b),tag)
		| ECase b-> ECase {
						 formula_case_branches = (List.map (fun (c1,c2)->
								((Ipure.float_out_pure_min_max c1),(float_out_struc_min_max c2)))
								b.formula_case_branches);
						 formula_case_pos = b.formula_case_pos}
		| EBase b -> EBase {b with 
						 formula_ext_base = float_out_min_max b.formula_ext_base;
						 formula_ext_continuation = float_out_struc_min_max b.formula_ext_continuation}
		(*| EVariance b ->
			let fo_measures = List.map (fun (expr, bound) -> 
        match bound with
        | None -> ((fst (P.float_out_exp_min_max expr)), None)
				| Some bexpr -> ((fst (P.float_out_exp_min_max expr)), Some (fst (P.float_out_exp_min_max bexpr)))) b.formula_var_measures in
			let fo_infer =  List.map (fun e -> fst (P.float_out_exp_min_max e)) b.formula_var_infer in
				EVariance ({ b with
					formula_var_measures = fo_measures;
					formula_var_infer = fo_infer;
					formula_var_continuation = helper b.formula_var_continuation;
				})*)
  | EInfer b -> EInfer {b with
    formula_inf_continuation = helper b.formula_inf_continuation;}
	in
	List.map helper f0
		

and view_node_types_struc (f:struc_formula):ident list = 
	let rec helper (f:ext_formula):ident list = match f with
	| ECase b -> List.concat (List.map (fun (c1,c2)-> view_node_types_struc c2) b.formula_case_branches)
	| EBase b -> (view_node_types b.formula_ext_base)@(view_node_types_struc b.formula_ext_continuation)
	| EAssume (b,_) -> view_node_types b
	(*| EVariance b -> helper b.formula_var_continuation*)
 | EInfer b -> helper b.formula_inf_continuation
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
		(*| EVariance b -> helper b.formula_var_continuation*)
    | EInfer b -> helper b.formula_inf_continuation
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
		(*| EVariance b -> EVariance ({ b with
        formula_var_continuation = helper b.formula_var_continuation;
			})*)
  | EInfer b -> EInfer {b with
    formula_inf_continuation = helper b.formula_inf_continuation;}
in
List.map helper f 


and subst_stub_flow_struc (t:string) (f:struc_formula) : struc_formula = subst_flow_of_struc_formula stub_flow t f	
      
let rec break_formula (f : formula) : P.b_formula list list =
  match f with
	| Base bf -> [P.break_pure_formula bf.formula_base_pure]
	| Exists ef -> [P.break_pure_formula ef.formula_exists_pure]
	| Or orf -> (break_formula orf.formula_or_f1) @ (break_formula orf.formula_or_f2)

and break_ext_formula (f : ext_formula) : P.b_formula list list =
  match f with
	| ECase cf -> List.map
	  (fun (cond, sf) -> List.concat ([P.break_pure_formula cond] @ (break_struc_formula sf)))
	  cf.formula_case_branches
	| EBase bf -> [List.concat ((break_formula bf.formula_ext_base) @ (break_struc_formula bf.formula_ext_continuation))]
	| EAssume (af, _) -> break_formula af
	(*| EVariance _ -> []*)
 | EInfer bf -> break_ext_formula bf.formula_inf_continuation

and break_struc_formula (f : struc_formula) : P.b_formula list list =
  List.fold_left (fun a ef -> a @ (break_ext_formula ef)) [] f

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

let eq_var (sv1 : (ident * primed)) (sv2 : (ident * primed)) = match (sv1, sv2) with
  | ((v1, p1), (v2, p2)) -> v1 = v2 & p1 = p2

let diff_svl vl rl = Gen.BList.difference_eq eq_var vl rl

let rec prune_exists fml infer_vars = match fml with
  | Base _ -> fml
  | Or { formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos} -> 
    mkOr (prune_exists f1 infer_vars) (prune_exists f2 infer_vars) pos
  | Exists fml_ex ->
    let new_vars = diff_svl fml_ex.formula_exists_qvars infer_vars in
    Exists {fml_ex with formula_exists_qvars = new_vars}
