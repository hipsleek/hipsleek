(* asankhs:  Created on 03-Sep-2012 for Memory Specifications*)

open Globals
open Gen.Basic
open Iformula

module CF = Cformula
module CP = Cpure
module MP = Mcpure
module Err = Error
module IF = Iformula

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

