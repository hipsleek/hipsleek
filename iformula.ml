(*
  Created 19-Feb-2006

  Input formulae
*)

open Globals
module P = Ipure

  

type formula =
  | Base of formula_base
  | Exists of formula_exists
  | Or of formula_or

and formula_base = { formula_base_heap : h_formula;
					 formula_base_pure : P.formula;
					 formula_base_pos : loc }

and formula_exists = { formula_exists_qvars : (ident * primed) list;
					   formula_exists_heap : h_formula;
					   formula_exists_pure : P.formula;
					   formula_exists_pos : loc }

and formula_or = { formula_or_f1 : formula;
				   formula_or_f2 : formula;
				   formula_or_pos : loc }

and h_formula = (* heap formula *)
  | Star of h_formula_star
  | HeapNode of h_formula_heap
  | HeapNode2 of h_formula_heap2
	  (* Don't distinguish between view and data node for now, as that requires look up *)
	  (*  | ArrayNode of ((ident * primed) * ident * P.exp list * loc) *)
	  (* pointer * base type * list of dimensions *)
  | HTrue 
  | HFalse
	  
and h_formula_star = { h_formula_star_h1 : h_formula;
					   h_formula_star_h2 : h_formula;
					   h_formula_star_pos : loc }

and h_formula_heap = { h_formula_heap_node : (ident * primed);
					   h_formula_heap_name : ident;
					   h_formula_heap_full : bool;
					   h_formula_heap_with_inv : bool;
					   h_formula_heap_arguments : P.exp list;
					   h_formula_heap_pseudo_data : bool;
					   h_formula_heap_pos : loc }

and h_formula_heap2 = { h_formula_heap2_node : (ident * primed);
						h_formula_heap2_name : ident;
						h_formula_heap2_full : bool;
						h_formula_heap2_with_inv : bool;
						h_formula_heap2_arguments : (ident * P.exp) list;
						h_formula_heap2_pseudo_data : bool;
						h_formula_heap2_pos : loc }

(* constructors *)

let rec formula_of_heap h pos = mkBase h (P.mkTrue pos) pos

and formula_of_pure p pos = mkBase HTrue p pos

and isConstFalse f0 = match f0 with
  | Base f -> begin
	  let h, p = f.formula_base_heap, f.formula_base_pure in
		match h with
		  | HFalse -> true
		  | _ -> match p with
			  | P.BForm (P.BConst (false, _)) -> true
			  | _ -> false
	end
  | _ -> false

and isConstTrue f0 = match f0 with
  | Base f -> begin
	  let h, p = f.formula_base_heap, f.formula_base_pure in
		match h with
		  | HTrue -> begin
			  match p with
				| P.BForm (P.BConst (true, _)) -> true
				| _ -> false
			end
		  | _ -> false
	end
  | _ -> false

and mkTrue pos = Base { formula_base_heap = HTrue;
						formula_base_pure = P.mkTrue pos;
						formula_base_pos = pos }

and mkFalse pos = Base { formula_base_heap = HFalse;
						 formula_base_pure = P.mkFalse pos;
						 formula_base_pos = pos }

and mkOr f1 f2 pos =
  if isConstTrue f1 || isConstTrue f2 then
	mkTrue pos
  else if isConstFalse f1 then f2
  else if isConstFalse f2 then f1
  else Or { formula_or_f1 = f1;
			formula_or_f2 = f2;
			formula_or_pos = pos }

and mkBase (h : h_formula) (p : P.formula) pos = match h with
  | HFalse -> mkFalse pos
  | _ -> 
	  if P.isConstFalse p then 
		mkFalse pos 
	  else 
		Base { formula_base_heap = h;
			   formula_base_pure = p;
			   formula_base_pos = pos }

and mkExists (qvars : (ident * primed) list) (h : h_formula) (p : P.formula) pos = match h with
  | HFalse -> mkFalse pos
  | _ ->
	  if P.isConstFalse p then
		mkFalse pos
	  else
		Exists { formula_exists_qvars = qvars;
				 formula_exists_heap = h;
				 formula_exists_pure = p;
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

and pos_of_formula f0 = match f0 with
  | Base f -> f.formula_base_pos
  | Or f -> f.formula_or_pos
  | Exists f -> f.formula_exists_pos
