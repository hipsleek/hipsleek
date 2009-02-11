(*
  The frontend engine of SLEEK.
*)

open Globals
open Sleekcommons

module H = Hashtbl
module I = Iast
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure
module AS = Astsimp

module XF = Xmlfront
module NF = Nativefront

(*
  Global data structures. If we want to support push/pop commands,
  we'll need to make them into a stack of scopes.
*)
let iobj_def = { I.data_name = "Object";
				 I.data_fields = [];
				 I.data_parent_name = "";
				 I.data_invs = []; (* F.mkTrue no_pos; *)
				 I.data_methods = [] }

let iprog = { I.prog_data_decls = [iobj_def];
			  I.prog_enum_decls = [];
			  I.prog_view_decls = [];
			  I.prog_proc_decls = [];
			  I.prog_coercion_decls = [] }

let cobj_def = { C.data_name = "Object";
				 C.data_fields = [];
				 C.data_parent_name = "";
				 C.data_invs = [];
				 C.data_methods = [] }

let cprog = { C.prog_data_decls = [];
			  C.prog_view_decls = [];
			  C.prog_proc_decls = [];
			  C.prog_left_coercions = [];
			  C.prog_right_coercions = [] }

let residues = ref ([] : CF.context list)

let check_data_pred_name name : bool =
  try 
	let _ = I.look_up_data_def_raw iprog.I.prog_data_decls name in
	  false
  with
	| Not_found -> begin
		try
		  let _ = I.look_up_view_def_raw iprog.I.prog_view_decls name in
			false
		with
		  | Not_found -> true
	  end

let process_data_def ddef =
  (*
	print_string (Iprinter.string_of_data_decl ddef);
	print_string ("\n"); 
  *)
  if check_data_pred_name ddef.I.data_name then
	let tmp = iprog.I.prog_data_decls in
	  try
		iprog.I.prog_data_decls <- ddef :: iprog.I.prog_data_decls;
		let cddef = AS.trans_data iprog ddef in
		  cprog.C.prog_data_decls <- cddef :: cprog.C.prog_data_decls
	  with
		| _ -> iprog.I.prog_data_decls <- tmp
  else
	print_string (ddef.I.data_name ^ " is already defined.\n")

let process_pred_def pdef = 
  (*
	print_string (Iprinter.string_of_view_decl pdef);
	print_string ("\n");
  *)
  if check_data_pred_name pdef.I.view_name then
	let tmp = iprog.I.prog_view_decls in
	  try
		iprog.I.prog_view_decls <- pdef :: iprog.I.prog_view_decls;
		let cpdef = AS.trans_view iprog pdef in
		cprog.C.prog_view_decls <- cpdef :: cprog.C.prog_view_decls;
(* added 07.04.2008	*)			
		ignore (List.map (fun vdef -> AS.compute_view_x_formula cprog vdef !Globals.n_xpure) cprog.C.prog_view_decls);
(* added 07.04.2008	*)									  
	  with
		| _ -> iprog.I.prog_view_decls <- tmp
  else
	print_string (pdef.I.view_name ^ " is already defined.\n")

let rec meta_to_formula (mf0 : meta_formula) quant fv_idents stab : CF.formula = match mf0 with
	| MetaFormCF mf -> mf
  | MetaForm mf ->
		AS.trans_formula iprog quant fv_idents mf stab
  | MetaVar mvar -> begin
	  try 
		let mf = get_var mvar in
		  meta_to_formula mf quant fv_idents stab
	  with
		| Not_found ->
			print_string (mvar ^ " is undefined.\n");
			raise SLEEK_Exception
	end
  | MetaCompose (vs, mf1, mf2) -> begin
	  let cf1 = meta_to_formula mf1 quant fv_idents stab in
	  let cf2 = meta_to_formula mf2 quant fv_idents stab in
	  let svs = List.map (fun v -> AS.get_spec_var_stab v stab no_pos) vs in
	  let res = CF.compose_formula cf1 cf2 svs no_pos in
		res
	end
	  
let process_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  try
	let _ = residues := [] in
	let stab = H.create 103 in
	let ante = meta_to_formula iante0 false [] stab in
(*
	let ante_str = Cprinter.string_of_formula ante in
	let _ = print_string ("\nante: " ^ ante_str ^ "\n") in
*)
	let fvs = CF.fv ante in
	let fv_idents = List.map CP.name_of_spec_var fvs in
	let conseq = meta_to_formula iconseq0 false fv_idents stab in
	let ectx = CF.empty_ctx no_pos in
	let ctx = CF.build_context ectx ante no_pos in
	let rs, _ = Solver.heap_entail cprog false false [ctx] conseq no_pos in
	let rs = List.map (fun r -> Solver.elim_ante_evars r) rs in
	  residues := rs;
	  if Util.empty rs then
		print_string ("Fail.\n")
	  else
		print_string ("Valid.\n")
  with
	| _ -> (print_string "exception in entail check\n")
		
let process_capture_residue (lvar : ident) = 
	let flist = List.map CF.formula_of_context !residues in
		put_var lvar (Sleekcommons.MetaFormCF(List.hd flist))
		
let process_lemma ldef =
  let l2r, r2l = AS.trans_one_coercion iprog ldef in
	cprog.C.prog_left_coercions <- l2r @ cprog.C.prog_left_coercions;
	cprog.C.prog_right_coercions <- r2l @ cprog.C.prog_right_coercions

let process_print_command pcmd0 = match pcmd0 with
  | PVar pvar ->
	  let stab = H.create 103 in
	  let mf = try get_var pvar with Not_found->  Error.report_error {
                   Error.error_loc = no_pos;
                   Error.error_text = "couldn't find " ^ pvar;
                 }in
	  let pf = meta_to_formula mf false [] stab in
		print_string ((Cprinter.string_of_formula pf) ^ "\n")
  | PCmd pcmd -> 
	  if pcmd = "residue" then
		let flist = List.map CF.formula_of_context !residues in
		let fstr = List.map Cprinter.string_of_formula flist in
		let tmp = String.concat "\n\n;\n\n" fstr in
		  print_string tmp;
		  print_string "\n"
	  else
		print_string ("unsupported print command: " ^ pcmd)
