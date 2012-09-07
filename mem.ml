(* asankhs:  Created on 03-Sep-2012 for Memory Specifications*)

open Globals
open Gen.Basic
open Iformula
open Iprinter

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
	| Some a -> (match a.mem_formula_exp with
		        | IP.Var (_,_)
  			| IP.BagDiff (_,_,_) 
 			| IP.Bag(_,_)
			| IP.BagIntersect (_,_)
  			| IP.BagUnion (_,_) ->
  			let allvs = IP.afv a.mem_formula_exp in
  			let fvs = (List.filter (fun c -> match c with 
  					| (a,Primed) 
  					| (a,Unprimed) -> if (List.mem a ("self"::vdf.I.view_vars)) then false else true) allvs) in
  			if (List.length fvs) == 0
			then 
			if List.for_all (fun v -> check_mem_formula_data_names ddcl v)  a.mem_formula_field_layout
			then ()
			else Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "Memory Field Layout of "^ vdf.I.view_name ^" is not present in Data Decls";}
			else Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "Memory Spec of "^ vdf.I.view_name ^" contains free variables " ^ (string_of_var_list fvs);}
			| _ -> Err.report_error {
				Err.error_loc = no_pos;
				Err.error_text = "Memory Spec of "^ vdf.I.view_name ^" contains unrecognized expressions";})
	| None -> ()


let add_mem_invariant (inv : IP.formula) (vmem : IF.mem_formula option) : IP.formula =
	match vmem with
	| Some a -> let new_var = ("Anon"^(fresh_trailer()),Unprimed) in 
		let tmp_formula = IP.BForm((IP.BagNotIn(new_var, a.mem_formula_exp,no_pos),None),None) in
		let tmp_formula2 = IP.mkNeqExp (IP.Var(new_var, no_pos)) (IP.Null(no_pos)) no_pos in
		let add_formula = IP.mkOr tmp_formula tmp_formula2 None no_pos in
		let mem_inv = IP.mkForall [new_var] add_formula None no_pos
		in IP.mkAnd inv mem_inv (IP.pos_of_formula inv)
	| None -> inv

