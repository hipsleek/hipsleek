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
			  I.prog_global_var_decls = [];
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

let residues = ref (None : CF.list_context option)

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
	let _ = Iast.build_exc_hierarchy true iprog in
	let _ = Util.c_h () in
	let cddef = AS.trans_data iprog ddef in
	let _ = if !Globals.print_core then print_string (Cprinter.string_of_data_decl cddef ^"\n") else () in
	  cprog.C.prog_data_decls <- cddef :: cprog.C.prog_data_decls
      with
	| _ -> dummy_exception() ; iprog.I.prog_data_decls <- tmp
      else begin
        dummy_exception() ;
	print_string (ddef.I.data_name ^ " is already defined.\n")
      end

let process_pred_def pdef = 
    
  if check_data_pred_name pdef.I.view_name then
	let tmp = iprog.I.prog_view_decls in
	  try
		let h = (self,Unprimed)::(res,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in
		let p = (self,Primed)::(res,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in
    let wf,_ = AS.case_normalize_struc_formula iprog h p pdef.Iast.view_formula false false in
		let new_pdef = {pdef with Iast.view_formula = wf} in
		iprog.I.prog_view_decls <- ( new_pdef :: iprog.I.prog_view_decls);
		(*let tmp_views = order_views iprog.I.prog_view_decls in*)
		(*let _ = print_string ("\n------ "^(Iprinter.string_of_struc_formula "\t" pdef.Iast.view_formula)^"\n normalized:"^(Iprinter.string_of_struc_formula "\t" wf)^"\n") in*)
		let cpdef = AS.trans_view iprog new_pdef in
		let old_vdec = cprog.C.prog_view_decls in
		cprog.C.prog_view_decls <- (cpdef :: cprog.C.prog_view_decls);
(* added 07.04.2008	*)	
		(*ignore (print_string ("init: "^(Iprinter.string_of_struc_formula "" pdef.Iast.view_formula )^"\n normalized: "^
							 (Iprinter.string_of_struc_formula "" wf )^"\n translated: "^
							 (Cprinter.string_of_struc_formula cpdef.Cast.view_formula)
							 ^"\n"
							 )
				)*)
		(* used to do this for all preds, due to mutable fields formulas exploded, i see no reason to redo for all: 
		ignore (List.map (fun vdef -> AS.compute_view_x_formula cprog vdef !Globals.n_xpure) cprog.C.prog_view_decls);*)
		ignore (AS.compute_view_x_formula cprog cpdef !Globals.n_xpure);
		let n_cpdef = AS.view_prune_inv_inference cprog cpdef in
    cprog.C.prog_view_decls <- (n_cpdef :: old_vdec);
    let n_cpdef = {n_cpdef with 
        C.view_formula =  Solver.prune_pred_struc cprog (Some Tpdispatcher.simplify) n_cpdef.C.view_formula ;
        C.view_un_struc_formula = Solver.prune_preds cprog (Some Tpdispatcher.simplify) n_cpdef.C.view_un_struc_formula;}in
		let _ = if !Globals.print_core then print_string (Cprinter.string_of_view_decl n_cpdef ^"\n") else () in
		cprog.C.prog_view_decls <- (n_cpdef :: old_vdec)
		(*print_string ("\npred def: "^(Cprinter.string_of_view_decl cpdef)^"\n")*)
(* added 07.04.2008	*)									  
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_view_decls <- tmp
  else
	print_string (pdef.I.view_name ^ " is already defined.\n")

	
let rec meta_to_struc_formula (mf0 : meta_formula) quant fv_idents stab : CF.struc_formula = match mf0 with
  | MetaFormCF mf -> (Cformula.formula_to_struc_formula mf)
  | MetaForm mf -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let p = List.map (fun c-> (c,Primed)) fv_idents in
      let wf,_ = AS.case_normalize_struc_formula iprog h p (Iformula.formula_to_struc_formula mf) false true in
	AS.trans_struc_formula iprog quant fv_idents wf stab false (*(Cpure.Prim Void) []*)
  | MetaVar mvar -> begin
      try 
	let mf = get_var mvar in
	  meta_to_struc_formula mf quant fv_idents stab
      with
	| Not_found ->
	    dummy_exception() ;
	    print_string (mvar ^ " is undefined.\n");
	    raise SLEEK_Exception
    end
  | MetaCompose (vs, mf1, mf2) -> begin
      let cf1 = meta_to_struc_formula mf1 quant fv_idents stab in
      let cf2 = meta_to_struc_formula mf2 quant fv_idents stab in
      let svs = List.map (fun v -> AS.get_spec_var_stab v stab no_pos) vs in
      let res = Solver.compose_struc_formula cf1 cf2 svs no_pos in
	res
    end
  | MetaEForm b -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let p = List.map (fun c-> (c,Primed)) fv_idents in
      let wf,_ = AS.case_normalize_struc_formula iprog h p b false true in
      let res = AS.trans_struc_formula iprog quant fv_idents wf stab false (*(Cpure.Prim Void) [] *) in
	res
	
let rec meta_to_formula (mf0 : meta_formula) quant fv_idents stab : CF.formula = match mf0 with
  | MetaFormCF mf -> mf
  | MetaForm mf ->
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let wf,_ = AS.case_normalize_formula iprog h false mf in
      let _ = Astsimp.collect_type_info_formula iprog wf stab false in
	AS.trans_formula iprog quant fv_idents false wf stab false
  | MetaVar mvar -> begin
      try 
	let mf = get_var mvar in
	  meta_to_formula mf quant fv_idents stab
      with
	| Not_found ->
	    dummy_exception() ;
	    print_string (mvar ^ " is undefined.\n");
	    raise SLEEK_Exception
    end
  | MetaCompose (vs, mf1, mf2) -> begin
      let cf1 = meta_to_formula mf1 quant fv_idents stab in
      let cf2 = meta_to_formula mf2 quant fv_idents stab in
      let svs = List.map (fun v -> AS.get_spec_var_stab v stab no_pos) vs in
      let res = Cformula.compose_formula cf1 cf2 svs Cformula.Flow_combine no_pos in
	res
    end
  | MetaEForm _ -> report_error no_pos ("can not have structured formula in antecedent")
	  
let process_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  try
    let _ = residues := None in
    let stab = H.create 103 in
    let ante = meta_to_formula iante0 false [] stab in
    (*
	  let ante_str = Cprinter.string_of_formula ante in
	  let _ = print_string ("\nante: " ^ ante_str ^ "\n") in
    *)
    let fvs = CF.fv ante in
    let fv_idents = List.map CP.name_of_spec_var fvs in
    let conseq = meta_to_struc_formula iconseq0 false fv_idents stab in
    (*let conseq = (Cformula.substitute_flow_in_struc_f !n_flow_int !top_flow_int conseq ) in*)
    let ectx = CF.empty_ctx (CF.mkTrueFlow ()) no_pos in
    let ctx = CF.build_context ectx ante no_pos in
    (*let ctx = List.hd (Cformula.change_flow_ctx  !top_flow_int !n_flow_int [ctx]) in*)
    (*let _ = print_string ("\n checking: "^(Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") in	*)
    let _ = if !Globals.print_core then print_string ((Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") else () in
    (*let ctx = CF.transform_context (Solver.elim_unsat_es cprog (ref 1)) ctx in*)
    (*let _ = print_string ("\n checking2: "^(Cprinter.string_of_context ctx)^"\n") in*)
    let rs, _ = Solver.heap_entail_struc_init cprog false false false (CF.SuccCtx[ctx]) conseq no_pos None in
    let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs in
    residues := Some rs;
    if CF.isFailCtx rs then begin 
	  print_string ("Fail.\n");
      if !Globals.print_err_sleek  then           
        print_string (Cprinter.string_of_list_context rs); 
    end 
    else
	  print_string ("Valid.\n")
  with
    | _ ->  
    Printexc.print_backtrace stdout;
    dummy_exception() ; (print_string "exception in entail check\n")	
	
let process_capture_residue (lvar : ident) = 
	let flist = match !residues with 
      | None -> (CF.mkTrue (CF.mkTrueFlow()) no_pos)
      | Some s -> CF.formula_of_list_context s in
		put_var lvar (Sleekcommons.MetaFormCF flist)
		
let process_lemma ldef =
  let ldef = Astsimp.case_normalize_coerc iprog ldef in
  let l2r, r2l = AS.trans_one_coercion iprog ldef in
  let l2r = List.concat (List.map (fun c-> AS.coerc_spec cprog true c) l2r) in
  let r2l = List.concat (List.map (fun c-> AS.coerc_spec cprog false c) r2l) in
  let _ = if !Globals.print_core then 
    print_string ((Cprinter.string_of_coerc_decl_list true l2r) ^"\n"^ (Cprinter.string_of_coerc_decl_list false r2l) ^"\n") else () in
	cprog.C.prog_left_coercions <- l2r @ cprog.C.prog_left_coercions;
	cprog.C.prog_right_coercions <- r2l @ cprog.C.prog_right_coercions

let process_print_command pcmd0 = match pcmd0 with
  | PVar pvar ->
	  let stab = H.create 103 in
	  let mf = try get_var pvar with Not_found->  Error.report_error {
                   Error.error_loc = no_pos;
                   Error.error_text = "couldn't find " ^ pvar;
                 }in
	  let pf = meta_to_struc_formula mf false [] stab in
		print_string ((Cprinter.string_of_struc_formula pf) ^ "\n")
  | PCmd pcmd -> 
	  if pcmd = "residue" then
      match !residues with
        | None -> print_string ": no residue \n"
        | Some s -> print_string ((Cprinter.string_of_formula 
              (CF.formula_of_list_context s))^"\n")
		else
			print_string ("unsupported print command: " ^ pcmd)
