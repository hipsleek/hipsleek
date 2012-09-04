(* asankhs:  Created on 03-Sep-2012 for Memory Specifications*)

open Globals
open Gen.Basic
open Iformula

module CF = Cformula
module CP = Cpure
module IP = Ipure
module MP = Mcpure
module Err = Error
module IF = Iformula
module I = Iast

let get_data_fields (ddn : (ident * ((I.typed_ident * loc * bool) list)) list)  (name : ident) : ((I.typed_ident * loc * bool) list) = 
	try (snd (List.find (fun c -> (*let _ = print_string(" DD: "^(fst c)^ "N: "^name) in  *)
	if (String.compare (fst c) name) == 0 then true else false) ddn))
	with | _ -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "Memory Region Field Layout not found in Data Decls";}
	
let rec get_data_decl_names (ddf : I.data_decl list) : (ident * ((I.typed_ident * loc * bool) list)) list = 
	match ddf with
	| x::xs -> (x.I.data_name,x.I.data_fields)::(get_data_decl_names xs)
	| [] -> []

let check_mem_formula_data_names (ddf : I.data_decl list) (fl : (ident * (ann list))) : bool = 
	let data_name_fields = get_data_decl_names ddf in
	let name = fst fl in
	if List.mem name (fst (List.split data_name_fields))
	then if List.length (snd fl) == List.length (get_data_fields data_name_fields name) 
		then true
		else Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "Number of Fields in Memory Region for "^name^" don't match with Data Decls";}
	else false
		
let check_mem_formula (vdf : I.view_decl) (ddcl : I.data_decl list) =
	match vdf.I.view_mem with
	| Some a -> if List.mem a.mem_formula_name vdf.I.view_vars 
			then 
			if List.for_all (fun v -> check_mem_formula_data_names ddcl v)  a.mem_formula_field_layout
			then ()
			else Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "Field Layout of "^ a.mem_formula_name ^" is not present in Data Decls";}
		else Err.report_error {
		Err.error_loc = no_pos;
		Err.error_text = "Memory Region "^ a.mem_formula_name ^" is not a parameter of View " ^ vdf.I.view_name;}
	| None -> ()

let trans_field_layout (iann : IF.ann list) : CF.ann list = List.map Immutable.iformula_ann_to_cformula_ann iann

let trans_mem_formula (imem : IF.mem_formula) : CF.mem_perm_formula = 
	let mem_var = CP.SpecVar(UNK,imem.mem_formula_name,Unprimed) in 
	let helpl1, helpl2 = List.split imem.mem_formula_field_layout in
	let helpl2 = List.map trans_field_layout helpl2 in
	let meml = List.combine helpl1 helpl2 in
			{CF.mem_formula_name  = mem_var;
			CF.mem_formula_exact = imem.mem_formula_exact;
			CF.mem_formula_field_layout =  meml}
			
let trans_view_mem (vmem : IF.mem_formula option) : CF.mem_perm_formula option = 
	match vmem with
	| Some a -> Some(trans_mem_formula a)
	| None -> None

let add_mem_invariant (inv : IP.formula) (vmem : IF.mem_formula option) : IP.formula =
	match vmem with
	| Some a -> let new_var = ("Anon"^(fresh_trailer()),Unprimed) in 
		let tmp_formula = IP.BForm((IP.BagNotIn(new_var, IP.Var((a.mem_formula_name,Unprimed),no_pos),no_pos),None),None) in
		let tmp_formula2 = IP.mkNeqExp (IP.Var(new_var, no_pos)) (IP.Null(no_pos)) no_pos in
		let add_formula = IP.mkOr tmp_formula tmp_formula2 None no_pos in
		let mem_inv = IP.mkForall [new_var] add_formula None no_pos
		in IP.mkAnd inv mem_inv (IP.pos_of_formula inv)
	| None -> inv

