(*
  Created 19-Feb-2006

  Input formulae
*)

open Globals
open Exc.GTable
open Perm
open Label_only

module P = Ipure

let top_flow = top_flow

type ann = ConstAnn of heap_ann | PolyAnn of ((ident * primed) * loc)

and struc_formula = 
	| ECase of struc_case_formula
	| EBase of struc_base_formula
	| EAssume of (formula*formula_label*ensures_type)(*could be generalized to have a struc_formula type instead of simple formula*)
 (* spec feature to induce inference *)
	| EInfer of struc_infer_formula
	| EList of (spec_label_def*struc_formula) list 
	| EOr of  struc_or_formula

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
		 formula_struc_continuation : struc_formula option ;
		 formula_struc_pos : loc
	}

and formula =
  | Base of formula_base
  | Exists of formula_exists
  | Or of formula_or

and formula_base = { formula_base_heap : h_formula;
                     formula_base_pure : P.formula;
                     formula_base_flow : flow_formula;
                     formula_base_and: one_formula list;
                     formula_base_pos : loc }

and formula_exists = { formula_exists_qvars : (ident * primed) list;
                       formula_exists_heap : h_formula;
                       formula_exists_pure : P.formula;
                       formula_exists_flow : flow_formula;
                       formula_exists_and : one_formula list;
                       formula_exists_pos : loc }

and one_formula = {
    formula_heap : h_formula;
    formula_pure : P.formula;
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
  | Star of h_formula_star
  | HeapNode of h_formula_heap
  | HeapNode2 of h_formula_heap2
	  (* Don't distinguish between view and data node for now, as that requires look up *)
	  (*  | ArrayNode of ((ident * primed) * ident * P.exp list * loc) *)
	  (* pointer * base type * list of dimensions *)
  | HTrue 
  | HFalse
  | HEmp (* emp for classical logic *)

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

(* Interactive command line *)
let cmd: (string * (bool * struc_formula option * string option)) ref = ref ("", (false, None, None))

let print_formula = ref(fun (c:formula) -> "printer not initialized")
let print_h_formula = ref(fun (c:h_formula) -> "printer not initialized")
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
	
(* constructors *)

let rec formula_of_heap_1 h pos = mkBase h (P.mkTrue pos) top_flow [] pos

and formula_of_pure_1 p pos = mkBase HEmp p top_flow [] pos                (* pure formula has Empty heap *)

and formula_of_heap_with_flow h f pos = mkBase h (P.mkTrue pos) f [] pos

and formula_of_pure_with_flow p f a pos = mkBase HEmp p f a pos            (* pure formula has Empty heap *)

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
   formula_pos = b.formula_base_pos}

and one_formula_of_formula_exists b =
  {formula_heap = b.formula_exists_heap;
   formula_pure = b.formula_exists_pure;
   formula_thread = None;
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
		  | HEmp -> (P.isConstTrue p)
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

(* TRUNG TODO: should change name to mkEmp ? *)
and mkTrue flow pos = Base { formula_base_heap = HEmp;
						formula_base_pure = P.mkTrue pos;
						formula_base_flow = flow;
                        formula_base_and = [];
						formula_base_pos = pos }

and mkFalse flow pos = Base { formula_base_heap = HFalse;
						 formula_base_pure = P.mkFalse pos;
						 formula_base_flow = flow;
                         formula_base_and = [];
						 formula_base_pos = pos }

and mkETrue flow pos = EBase {
		 formula_struc_explicit_inst = [];
		 formula_struc_implicit_inst = [];
		 formula_struc_exists = [];
		 formula_struc_base = mkTrue flow pos;
		 formula_struc_continuation = None;
		 formula_struc_pos = pos	}

and mkEFalse flow pos = EBase {
		 formula_struc_explicit_inst = [];
		 formula_struc_implicit_inst = [];
		 formula_struc_exists = [];
		 formula_struc_base = mkFalse flow pos;
		 formula_struc_continuation = None;
		 formula_struc_pos = pos	}
			
and mkEFalseF () = mkEFalse false_flow no_pos			
and mkEOr (f1:struc_formula) (f2:struc_formula) pos :struc_formula= 
	if isEConstTrue f1 || isEConstTrue f2 then mkETrue top_flow pos
  else if isEConstFalse f1 then f2
  else if isEConstFalse f2 then f1
  else EOr { formula_struc_or_f1 = f1; formula_struc_or_f2 = f2; formula_struc_or_pos = pos}

and mkEBase ei ii e b c com l= EBase {
						 	formula_struc_explicit_inst = ei;
						 	formula_struc_implicit_inst = ii;
							formula_struc_exists = e;
						 	formula_struc_base = b;				
						 	formula_struc_continuation = c;
						 	formula_struc_pos = l;}
  
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
      
and mkBase (h : h_formula) (p : P.formula) flow (a: one_formula list) pos = match h with
  | HFalse -> mkFalse flow pos
  | _ -> 
	  if P.isConstFalse p then 
		mkFalse flow pos 
	  else 
		Base { formula_base_heap = h;
			   formula_base_pure = p;
			   formula_base_flow = flow;
			   formula_base_and = a;
			   formula_base_pos = pos }

and mkExists (qvars : (ident * primed) list) (h : h_formula) (p : P.formula) flow (a: one_formula list) pos = match h with
  | HFalse -> mkFalse flow pos
  | _ ->
	  if P.isConstFalse p then
		mkFalse flow pos
	  else
		Exists { formula_exists_qvars = qvars;
             formula_exists_heap = h;
             formula_exists_pure = p;
             formula_exists_flow = flow;
             formula_exists_and = a;
             formula_exists_pos = pos }

and mkOneFormula (h : h_formula) (p : P.formula) id pos = 
  {formula_heap =h;
   formula_pure = p;
   formula_thread = id;
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

and mkConj f1 f2 pos =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else Conj { h_formula_conj_h1 = f1;
              h_formula_conj_h2 = f2;
              h_formula_conj_pos = pos }

and mkPhase f1 f2 pos =
  match f1 with
  | HFalse -> HFalse
  | _ -> match f2 with
    | HFalse -> HFalse
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
	
and pos_of_struc_formula f0  = match f0 with 
	| ECase b -> b.formula_case_pos
	| EBase b -> b.formula_struc_pos
	| EAssume (b,_,_) -> pos_of_formula b
	| EInfer b -> b.formula_inf_pos
	| EOr b -> b.formula_struc_or_pos
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
     let perm_vars = (fv_iperm ()) perm in
     let imm_vars =  fv_imm imm in
     Gen.BList.remove_dups_eq (=) (imm_vars@perm_vars@((extract_var_from_id name):: (List.concat (List.map Ipure.afv b))))
  | HeapNode2 { h_formula_heap2_node = name ;
                h_formula_heap2_perm = perm; (*LDK*)
              h_formula_heap2_imm = imm; 
		h_formula_heap2_arguments = b}-> 
     let perm_vars =  (fv_iperm ()) perm in
     let imm_vars =  fv_imm imm in
      Gen.BList.remove_dups_eq (=)  (imm_vars@perm_vars@((extract_var_from_id name):: (List.concat (List.map (fun c-> (Ipure.afv (snd c))) b) )))
  | HTrue -> []
  | HFalse -> [] 
  | HEmp -> [] 
;;

let rec struc_hp_fv (f:struc_formula): (ident*primed) list =  match f with
	| EBase b-> Gen.BList.difference_eq (=) ((Gen.fold_opt struc_hp_fv b.formula_struc_continuation)@(heap_fv b.formula_struc_base)) 
					(b.formula_struc_explicit_inst@b.formula_struc_implicit_inst)
	| ECase b-> Gen.fold_l_snd struc_hp_fv b.formula_case_branches
	| EAssume (b,_,_)-> heap_fv b
    | EInfer b -> struc_hp_fv b.formula_inf_continuation
	| EList b -> Gen.BList.remove_dups_eq (=) (Gen.fold_l_snd struc_hp_fv b)
	| EOr b -> Gen.BList.remove_dups_eq (=) (struc_hp_fv b.formula_struc_or_f1 @ struc_hp_fv b.formula_struc_or_f2)
							
and heap_fv_one_formula (f:one_formula):(ident*primed) list = 
  (h_fv f.formula_heap)

(*TO CHECK: how about formula_and*)
and heap_fv (f:formula):(ident*primed) list = match f with
	| Base b-> 
        let avars = List.concat (List.map heap_fv_one_formula b.formula_base_and) in
        let hvars = h_fv b.formula_base_heap in
        Gen.BList.remove_dups_eq (=) hvars@avars
	| Exists b-> 
        let avars = List.concat (List.map heap_fv_one_formula b.formula_exists_and) in
        let hvars = h_fv b.formula_exists_heap in
        Gen.BList.difference_eq (=) (Gen.BList.remove_dups_eq (=) hvars@avars) b.formula_exists_qvars 
	| Or b-> Gen.BList.remove_dups_eq (=) ((heap_fv b.formula_or_f1)@(heap_fv b.formula_or_f2))
	
(*TO CHECK: how about formula_and*)	
and unbound_heap_fv (f:formula):(ident*primed) list = match f with
	| Base b-> 
        let avars = List.concat (List.map heap_fv_one_formula b.formula_base_and) in
        let hvars = h_fv b.formula_base_heap in
        Gen.BList.remove_dups_eq (=) hvars@avars
	| Exists b-> 
        let avars = List.concat (List.map heap_fv_one_formula b.formula_exists_and) in
        let hvars = h_fv b.formula_exists_heap in
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
	| EAssume (b,_,_)-> all_fv b
	| EInfer b -> Gen.BList.remove_dups_eq (=) ( struc_free_vars with_inst b.formula_inf_continuation)
	| EList b -> Gen.BList.remove_dups_eq (=) (Gen.fold_l_snd (struc_free_vars with_inst) b)
	| EOr b-> Gen.BList.remove_dups_eq (=) ((struc_free_vars with_inst b.formula_struc_or_f1)@(struc_free_vars with_inst b.formula_struc_or_f2))
	
	
 
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
		| EAssume (b,_,_)-> ([],all_fv b)
		| EInfer b -> helper b.formula_inf_continuation
		| EList b-> 
			let prl, pcl = List.split (List.map (fun c-> helper (snd c)) b) in
			(rde (List.concat prl), rde (List.concat pcl))
		| EOr b -> 
			let l1,l2 = helper b.formula_struc_or_f1 in
			let r1,r2 = helper b.formula_struc_or_f2 in
			(rde (l1@r1), rde (l2@r2)) in
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
  | Base ({ formula_base_heap = h; 
            formula_base_pure = p; 
           formula_base_flow = f;
           formula_base_and = a;
           formula_base_pos = pos}) -> mkExists qvars h p f a pos (*TO CHECK*)
  | Exists ({formula_exists_qvars = qvs; 
             formula_exists_heap = h; 
             formula_exists_pure = p; 
             formula_exists_flow = f;
             formula_exists_and = a;
             formula_exists_pos = pos}) -> 
	  let new_qvars = Gen.BList.remove_dups_eq (=) (qvs @ qvars) in
		mkExists new_qvars h p f a pos (*TO CHECK*)
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
		| Or b->  EOr { formula_struc_or_f1 = helper b.formula_or_f1; formula_struc_or_f2 = helper b.formula_or_f2; formula_struc_or_pos = b.formula_or_pos} in
	Debug.no_1 "formula_to_struc_formula" !print_formula !print_struc_formula helper f;;
  
(* split a conjunction into heap constraints, pure pointer constraints, *)
(* and Presburger constraints *)
let split_components (f : formula) =  match f with
    | Base ({formula_base_heap = h; 
	  formula_base_pure = p; 
          formula_base_and = a;
	  formula_base_flow =fl }) -> (h, p, fl, a)
    | Exists ({formula_exists_heap = h; 
	  formula_exists_pure = p; 
	  formula_exists_and = a;
      formula_exists_flow = fl }) -> (h, p, fl, a)
    | _ -> failwith ("split_components: don't expect OR")

let split_quantifiers (f : formula) : ( (ident * primed) list * formula) = match f with
  | Exists ({formula_exists_qvars = qvars; 
			 formula_exists_heap =  h; 
			 formula_exists_pure = p; 
			 formula_exists_flow = f;
			 formula_exists_and = a;
			 formula_exists_pos = pos}) -> (qvars, mkBase h p f a pos)
 
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

and split_one_formula (f : one_formula) = f.formula_heap, f.formula_pure, f.formula_thread, f.formula_pos

and one_formula_apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : one_formula) = 
  let h,p,id,pos = split_one_formula f in
  {formula_heap = h_apply_one s h;
   formula_pure = Ipure.apply_one s p;
   formula_thread = (match id with 
     | None -> None
     | Some v -> Some (subst_var s v));
   formula_pos = pos} 

and apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
        Or ({formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h;
	formula_base_pure = p;
	formula_base_flow = fl;
	formula_base_and = a;
	formula_base_pos = pos }) -> 
        Base ({formula_base_heap = h_apply_one s h; 
		formula_base_pure = Ipure.apply_one s p;
		formula_base_flow = fl;
	    formula_base_and = List.map (one_formula_apply_one s) a;
		formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
	formula_exists_heap = qh; 
	formula_exists_pure = qp; 
	formula_exists_flow = fl;
	formula_exists_and = a;
	formula_exists_pos = pos}) -> 
	    if List.mem (fst fr) (List.map fst qsv) then f 
	    else Exists ({formula_exists_qvars = qsv; 
		formula_exists_heap =  h_apply_one s qh; 
		formula_exists_pure = Ipure.apply_one s qp; 
		formula_exists_flow = fl;
	    formula_exists_and = List.map (one_formula_apply_one s) a;
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
        | Some f -> Some (apply_one_iperm () s f)
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
        | Some f -> Some (apply_one_iperm () s f)
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
  | HEmp -> f
	    

and rename_bound_vars (f : formula) = 
  let add_quantifiers (qvars : (ident*primed) list) (f : formula) : formula = match f with
    | Base b -> mkExists qvars b.formula_base_heap b.formula_base_pure b.formula_base_flow b.formula_base_and b.formula_base_pos
    | Exists b -> 
	      let new_qvars = Gen.BList.remove_dups_eq (=) (b.formula_exists_qvars @ qvars) in
		  mkExists new_qvars b.formula_exists_heap b.formula_exists_pure b.formula_exists_flow b.formula_exists_and b.formula_exists_pos


    | _ -> failwith ("add_quantifiers: invalid argument") in		
  match f with
    | Or b -> mkOr (rename_bound_vars b.formula_or_f1) (rename_bound_vars b.formula_or_f2) b.formula_or_pos
    | Base _ -> f
    | Exists _ ->
	      let qvars, base_f = split_quantifiers f in
	      let new_qvars = Ipure.fresh_vars qvars in
	      let rho = List.combine qvars new_qvars in
	      let new_base_f = subst rho base_f in
	      let resform = add_quantifiers new_qvars new_base_f in
		  resform 


	          
and subst_struc (sst:((ident * primed)*(ident * primed)) list) (f:struc_formula):struc_formula = match f with
	| EAssume (b,tag,t) -> EAssume ((subst sst b),tag,t)
	| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> ((Ipure.subst sst c1),(subst_struc sst c2))) b.formula_case_branches}
	| EBase b->  EBase {
			  formula_struc_implicit_inst = List.map (subst_var_list sst) b.formula_struc_implicit_inst;
			  formula_struc_explicit_inst = List.map (subst_var_list sst) b.formula_struc_explicit_inst;
			  formula_struc_exists = List.map (subst_var_list sst) b.formula_struc_exists;
			  formula_struc_base = subst sst b.formula_struc_base;
			  formula_struc_continuation = Gen.map_opt (subst_struc sst) b.formula_struc_continuation;
			  formula_struc_pos = b.formula_struc_pos}
  | EInfer b -> EInfer {b with
      formula_inf_vars = List.map (subst_var_list sst) b.formula_inf_vars;
      formula_inf_continuation = subst_struc sst b.formula_inf_continuation;}
  | EOr b -> EOr {b with formula_struc_or_f1 = subst_struc sst b.formula_struc_or_f1; formula_struc_or_f2 = subst_struc sst b.formula_struc_or_f2;}
  | EList b -> EList (Gen.map_l_snd (subst_struc sst) b)
             (* formula_ext_complete = b.formula_ext_complete;*)
  

let rec rename_bound_var_struc_formula (f:struc_formula):struc_formula = match f with
	| EAssume (b,tag,t) -> EAssume ((rename_bound_vars b),tag,t)
	| ECase b-> ECase {b with formula_case_branches = Gen.map_l_snd rename_bound_var_struc_formula b.formula_case_branches}
	| EBase b-> 
			let sst2 = List.map (fun (c1,c2)-> ((c1,c2),((Ipure.fresh_old_name c1),c2))) b.formula_struc_implicit_inst in
			EBase {b with 
				formula_struc_explicit_inst = b.formula_struc_explicit_inst;
		 		formula_struc_implicit_inst = snd (List.split sst2);
				formula_struc_base=rename_bound_vars (subst sst2 b.formula_struc_base); 
				formula_struc_continuation= Gen.map_opt rename_bound_var_struc_formula (Gen.map_opt (subst_struc sst2) b.formula_struc_continuation) }			
	| EInfer b -> EInfer {b with (* Need to check again *)
					formula_inf_continuation = rename_bound_var_struc_formula b.formula_inf_continuation;}
	| EList b -> EList (Gen.map_l_snd rename_bound_var_struc_formula b)
	| EOr b -> EOr {b with formula_struc_or_f1 = rename_bound_var_struc_formula b.formula_struc_or_f1; formula_struc_or_f2 = rename_bound_var_struc_formula b.formula_struc_or_f2;}


and float_out_exps_from_heap (f:formula ):formula = (* float_out_exps_from_heap_x f *)
let pr = !print_formula in
Debug.no_1 "float_out_exps_from_heap" pr pr float_out_exps_from_heap_x f

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
        let na_perm, ls_perm = float_out_iperm () perm b.h_formula_heap_pos in
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
        let na_perm, ls_perm = float_out_iperm () perm b.h_formula_heap2_pos in
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
    | HFalse -> (f,[]) 
    | HEmp -> (f,[]) in
  let helper_one_formula (f:one_formula) =
    let rh,rl = float_out_exps f.formula_heap in
    if (List.length rl) == 0 then ([],f)
    else
	  let r1,r2 = List.hd rl in
	  let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)-> ((c1::a1),(Ipure.mkAnd a2 c2 f.formula_pos)) ) ([r1],r2) (List.tl rl) in
      let new_p = Ipure.mkAnd r2 f.formula_pure f.formula_pos in
      (r1,mkOneFormula rh new_p f.formula_thread f.formula_pos)
  in
  let rec helper (f:formula):formula =	match f with
    | Base b-> let rh,rl = float_out_exps b.formula_base_heap in
	if (List.length rl)== 0 then f
	else 
	  let r1,r2 = List.hd rl in
	  let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)-> ((c1::a1),(Ipure.mkAnd a2 c2 b.formula_base_pos)) ) ([r1],r2) (List.tl rl) in
      let tmp = List.map helper_one_formula b.formula_base_and in
      let avars,afs = List.split tmp in
      let avars = List.concat avars in
	    Exists ({
		      formula_exists_qvars = avars@r1;
		      formula_exists_heap = rh;
		      formula_exists_flow = b.formula_base_flow;
		      formula_exists_pure = Ipure.mkAnd r2 b.formula_base_pure b.formula_base_pos;
		      formula_exists_and = afs;
		      formula_exists_pos = b.formula_base_pos
		    })
    | Exists b->
	let rh,rl = float_out_exps b.formula_exists_heap in
	  if (List.length rl)== 0 then f
	  else 
	    let r1,r2 = List.hd rl in
	    let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)-> ((c1::a1),(Ipure.mkAnd a2 c2 b.formula_exists_pos)) ) ([r1],r2) (List.tl rl) in
        let tmp = List.map helper_one_formula b.formula_exists_and in
        let avars,afs = List.split tmp in
        let avars = List.concat avars in
	      Exists ({
			formula_exists_qvars = avars@r1@b.formula_exists_qvars;
			formula_exists_heap = rh;
			formula_exists_pure = Ipure.mkAnd r2 b.formula_exists_pure b.formula_exists_pos;
			formula_exists_flow = b.formula_exists_flow;
		    formula_exists_and = afs;
			formula_exists_pos = b.formula_exists_pos
		      })	
    | Or b-> Or ({
		   formula_or_f1 = float_out_exps_from_heap b.formula_or_f1;
		   formula_or_f2 = float_out_exps_from_heap b.formula_or_f2;
		   formula_or_pos = b.formula_or_pos
		 })		
  in helper f
       
and float_out_exps_from_heap_struc (f:struc_formula):struc_formula = match f with
    | EAssume (b,tag,t) -> EAssume ((float_out_exps_from_heap b),tag,t)
    | ECase b -> ECase {b with formula_case_branches = Gen.map_l_snd float_out_exps_from_heap_struc b.formula_case_branches}
    | EBase b -> EBase {
				 formula_struc_explicit_inst = b.formula_struc_explicit_inst;
				 formula_struc_implicit_inst = b.formula_struc_implicit_inst;
				 formula_struc_exists = b.formula_struc_exists ;
				 formula_struc_base = float_out_exps_from_heap b.formula_struc_base;
				 formula_struc_continuation = Gen.map_opt float_out_exps_from_heap_struc b.formula_struc_continuation;
				 formula_struc_pos = b.formula_struc_pos}
    | EInfer b -> EInfer ({b with formula_inf_continuation = float_out_exps_from_heap_struc b.formula_inf_continuation;})
	| EList b -> EList (Gen.map_l_snd float_out_exps_from_heap_struc b)
	| EOr b-> EOr {b with formula_struc_or_f1 = float_out_exps_from_heap_struc b.formula_struc_or_f1; formula_struc_or_f2 = float_out_exps_from_heap_struc b.formula_struc_or_f2;}

and float_out_one_formula_min_max (f :  one_formula) :  one_formula =
  let (nh, nhpf) = float_out_heap_min_max f.formula_heap in
  let np = Ipure.float_out_pure_min_max f.formula_pure in
  let new_p =  (match nhpf with
    | None -> np
    | Some e1 -> Ipure.And (np, e1, f.formula_pos)) in
  mkOneFormula nh new_p f.formula_thread f.formula_pos

and float_out_min_max (f :  formula) :  formula =
  match f with
  |  Base
      {
         formula_base_pos = l;
         formula_base_heap = h0;
		 formula_base_flow = fl;
         formula_base_and = a;
         formula_base_pure = p0
      } ->
      let (nh, nhpf) = float_out_heap_min_max h0 in
      let np = Ipure.float_out_pure_min_max p0 in
         Base
          {
             formula_base_pos = l;
             formula_base_heap = nh;
			 formula_base_flow = fl;
             formula_base_pure =
              (match nhpf with
               | None -> np
               | Some e1 -> Ipure.And (np, e1, l));
             formula_base_and = List.map float_out_one_formula_min_max a;
          }
  |  Exists
      {
         formula_exists_qvars = qv;
         formula_exists_heap = h0;
         formula_exists_pure = p0;
		 formula_exists_flow = fl;
         formula_exists_and = a;
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
             formula_exists_and = List.map float_out_one_formula_min_max a;
             formula_exists_pos = l;
          }
  |  Or b-> Or {formula_or_f1 = float_out_min_max b.formula_or_f1;formula_or_f2 = float_out_min_max b.formula_or_f2;formula_or_pos = b.formula_or_pos;}

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
	    let nl_perm, new_p_perm = float_out_mix_max_iperm () perm l in
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
	    let nl_perm, new_p_perm = float_out_mix_max_iperm () perm l in
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
    |  HEmp -> (h, None)
	 
  
and float_out_struc_min_max (f0 : struc_formula): struc_formula = match f0 with
	| EAssume (b,tag,t) -> EAssume ((float_out_min_max b),tag,t)
	| ECase b-> ECase {b with 
					 formula_case_branches = (List.map (fun (c1,c2)->((Ipure.float_out_pure_min_max c1),(float_out_struc_min_max c2))) b.formula_case_branches)}
	| EBase b -> EBase {b with 
					 formula_struc_base = float_out_min_max b.formula_struc_base;
					 formula_struc_continuation = Gen.map_opt float_out_struc_min_max b.formula_struc_continuation}
	| EInfer b -> EInfer {b with formula_inf_continuation = float_out_struc_min_max b.formula_inf_continuation;}
	| EList b -> EList (Gen.map_l_snd float_out_struc_min_max b)
	| EOr b -> EOr {b with formula_struc_or_f1 = float_out_struc_min_max b.formula_struc_or_f1; formula_struc_or_f2 = float_out_struc_min_max b.formula_struc_or_f2;}
		

and view_node_types_struc (f:struc_formula):ident list = match f with
	| ECase b -> Gen.fold_l_snd view_node_types_struc b.formula_case_branches
	| EBase b -> (view_node_types b.formula_struc_base)@(Gen.fold_opt view_node_types_struc b.formula_struc_continuation)
	| EAssume (b,_,_) -> view_node_types b
	| EInfer b -> view_node_types_struc b.formula_inf_continuation
	| EList b -> Gen.BList.remove_dups_eq (=) (Gen.fold_l_snd view_node_types_struc b)
	| EOr b-> Gen.BList.remove_dups_eq (=) (view_node_types_struc b.formula_struc_or_f1 @ view_node_types_struc b.formula_struc_or_f2)
		
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
		| EBase b->   has_top_flow b.formula_struc_base; (match  b.formula_struc_continuation with | None -> () | Some l-> helper l)
		| ECase b->   List.iter (fun (_,b1)-> (helper b1)) b.formula_case_branches
		| EAssume (b,_,_)-> has_top_flow b
		| EInfer b-> helper b.formula_inf_continuation
		| EList b-> List.iter (fun c-> helper (snd c)) b
		| EOr b-> helper b.formula_struc_or_f1; helper b.formula_struc_or_f2 in
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
	| EAssume (b,tag,etype)-> EAssume ((subst_flow_of_formula fr t b),tag,etype) 
	| EInfer b -> EInfer {b with formula_inf_continuation = subst_flow_of_struc_formula fr t b.formula_inf_continuation;}
	| EList b-> EList (Gen.map_l_snd (subst_flow_of_struc_formula fr t) b	)
	| EOr b -> EOr {b with 
						formula_struc_or_f1 = subst_flow_of_struc_formula fr t b.formula_struc_or_f1; 
						formula_struc_or_f2 = subst_flow_of_struc_formula fr t b.formula_struc_or_f2;}

and subst_stub_flow_struc (t:string) (f:struc_formula) : struc_formula = subst_flow_of_struc_formula stub_flow t f	
      
let rec break_formula (f : formula) : P.b_formula list list =
  match f with
	| Base bf -> [P.break_pure_formula bf.formula_base_pure]
	| Exists ef -> [P.break_pure_formula ef.formula_exists_pure]
	| Or orf -> (break_formula orf.formula_or_f1) @ (break_formula orf.formula_or_f2)

and break_struc_formula (f : struc_formula) : P.b_formula list list = match f with
	| ECase cf -> List.map (fun (cond, sf) -> List.concat ([P.break_pure_formula cond] @ (break_struc_formula sf))) cf.formula_case_branches
	| EBase bf -> [List.concat ((break_formula bf.formula_struc_base) @ (Gen.fold_opt break_struc_formula bf.formula_struc_continuation))]
	| EAssume (af, _, _) -> break_formula af
	| EInfer bf -> break_struc_formula bf.formula_inf_continuation
	| EList b-> Gen.fold_l_snd break_struc_formula b
	| EOr b-> (break_struc_formula b.formula_struc_or_f1) @(break_struc_formula b.formula_struc_or_f2)

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
    
(*find thread id for each one_formula*)
(*remove thread = id and add id into  formula_thread*)
let float_out_thread_one_formula_x (f : one_formula) : one_formula =
  let p = f.formula_pure in
  let ps = P.list_of_conjs p in
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
  {f with formula_pure = new_p; formula_thread = thread_id}

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


let rec float_out_thread_struc_formula_x (f:struc_formula):struc_formula = match f with
    | EAssume (b,tag,t) -> EAssume ((float_out_thread b),tag,t)
    | ECase b -> ECase ({formula_case_branches = List.map (fun (c1,c2)-> (c1,(float_out_exps_from_heap_struc c2))) b.formula_case_branches ; formula_case_pos=b.formula_case_pos})
    | EBase b-> EBase {b with
				 formula_struc_base = float_out_thread b.formula_struc_base;
				 formula_struc_continuation =  Gen.map_opt float_out_thread_struc_formula_x b.formula_struc_continuation;
				}
    | EInfer b -> EInfer ({b with formula_inf_continuation = float_out_thread_struc_formula_x b.formula_inf_continuation;})
	| EList b -> EList (Gen.map_l_snd float_out_thread_struc_formula_x b)
	| EOr b -> EOr {b with 
			formula_struc_or_f1 = float_out_thread_struc_formula_x b.formula_struc_or_f1; 
			formula_struc_or_f2 = float_out_thread_struc_formula_x b.formula_struc_or_f2; }

let float_out_thread_struc_formula (f:struc_formula):struc_formula = 
  Debug.no_1 "float_out_thread_struc_formula"
      !print_struc_formula !print_struc_formula
      float_out_thread_struc_formula_x f

let mkEInfer xpost transpec pos = EInfer { 
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
		 | HeapNode2 h -> Gen.report_error no_pos "malfunction with convert to heap node"
		 | HTrue | HEmp | HFalse -> Bar_not_found in
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
		| EAssume (e,tag,_) -> if b then find_node t e else false
		| ECase e -> Gen.Basic.all_l_snd (helper b) e.formula_case_branches
		| EBase e-> (match e.formula_struc_continuation with | None -> false | Some cont-> helper (if b then b else find_node f e.formula_struc_base) cont)
		| EInfer e -> helper b e.formula_inf_continuation
		| EList e -> Gen.Basic.all_l_snd (helper b) e
		| EOr e -> helper b e.formula_struc_or_f1 && helper b e.formula_struc_or_f2 in
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
	let rec helper f =  match f with
		| ECase c -> ECase {c with formula_case_branches = List.map (fun (c1,c2)-> c1,helper c2) c.formula_case_branches} 
		| EBase b -> EBase {b with formula_struc_continuation = Gen.map_opt helper b.formula_struc_continuation}
		| EInfer b -> EInfer {b with formula_inf_continuation = helper b.formula_inf_continuation;}
		| EList b -> EList (Gen.map_l_snd helper b)
		| EOr b -> EOr {b with formula_struc_or_f1 = helper b.formula_struc_or_f1; formula_struc_or_f2 = helper b.formula_struc_or_f2;}
		| EAssume (e,pid,t)-> EAssume (fct e, pid, t) in
	helper f
	