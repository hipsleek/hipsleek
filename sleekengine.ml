(*
  The frontend engine of SLEEK.
*)

open Globals
open Sleekcommons
open Gen.Basic
open Exc.ETABLE_NFLOW

module H = Hashtbl
module I = Iast
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure
module LP = Lemproving
module AS = Astsimp

module XF = Xmlfront
module NF = Nativefront

let sleek_proof_counter = new Gen.counter 0

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
        I.prog_rel_decls = [];
        I.prog_axiom_decls = []; (* [4/10/2011] An Hoa *)
			  I.prog_proc_decls = [];
			  I.prog_coercion_decls = [];
              I.prog_hopred_decls = [];
}

let cobj_def = { C.data_name = "Object";
				 C.data_fields = [];
				 C.data_parent_name = "";
				 C.data_invs = [];
				 C.data_methods = [] }

let cprog = ref { C.prog_data_decls = [];
			  C.prog_view_decls = [];
				C.prog_rel_decls = []; (* An Hoa *)
				C.prog_axiom_decls = []; (* [4/10/2011] An Hoa *)
			  C.prog_proc_decls = [];
			  C.prog_left_coercions = [];
			  C.prog_right_coercions = [] }

let residues = ref (None : CF.list_context option)

let clear_iprog () =
  iprog.I.prog_data_decls <- [iobj_def];
  iprog.I.prog_view_decls <- [];
  iprog.I.prog_rel_decls <- [];
  iprog.I.prog_coercion_decls <- []

let clear_cprog () =
  !cprog.C.prog_data_decls <- [];
  !cprog.C.prog_view_decls <- [];
  !cprog.C.prog_rel_decls <- [];
  !cprog.C.prog_left_coercions <- [];
  !cprog.C.prog_right_coercions <- []

let clear_all () =
  Debug.clear_debug_log ();
  Tpdispatcher.clear_prover_log ();
  exlist # clear;
  clear_var_table ();
  clear_iprog ();
  clear_cprog ();
  residues := None

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
		  | Not_found -> (*true*)
			  (* An Hoa : modify to check for defined relation name as well. *)
				begin
					try
			  		let _ = I.look_up_rel_def_raw iprog.I.prog_rel_decls name in
						false
					with
			  		| Not_found -> true
		  	end
	  end

let check_data_pred_name name :bool = 
  let pr1 x = x in
  let pr2 = string_of_bool in 
  Gen.Debug.no_1 "check_data_pred_name" pr1 pr2 (fun _ -> check_data_pred_name name) name
    
(* let process_data_def ddef = *)
(*   print_endline (Iprinter.string_of_data_decl ddef); *)
(*   flush stdout; *)
(*   if check_data_pred_name ddef.I.data_name then *)
(*     let tmp = iprog.I.prog_data_decls in *)
(*     try *)
(*       iprog.I.prog_data_decls <- ddef :: iprog.I.prog_data_decls; *)
(*       Iast.build_exc_hierarchy true iprog; *)
(*       Exc.c_h (); *)
(*       let cddef = AS.trans_data iprog ddef in *)
(*       if !Globals.print_core then  *)
(*         print_string (Cprinter.string_of_data_decl cddef ^"\n"); *)
(*       !cprog.C.prog_data_decls <- cddef :: !cprog.C.prog_data_decls *)
(*     with *)
(*     | _ -> dummy_exception() ; iprog.I.prog_data_decls <- tmp *)
(*   else begin *)
(*     dummy_exception() ; *)
(*     print_string (ddef.I.data_name ^ " is already defined.\n") *)
(*   end *)

let process_pred_def pdef = 
    
  if check_data_pred_name pdef.I.view_name then
	let tmp = iprog.I.prog_view_decls in
	  try
		let h = (self,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in
		let p = (self,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in
		let wf,_ = AS.case_normalize_struc_formula iprog  h p pdef.Iast.view_formula false false [] in
		let new_pdef = {pdef with Iast.view_formula = wf} in
		let tmp_views = AS.order_views (new_pdef :: iprog.I.prog_view_decls) in
		iprog.I.prog_view_decls <- List.rev tmp_views;
(* ( new_pdef :: iprog.I.prog_view_decls); *)
		(*let _ = print_string ("\n------ "^(Iprinter.string_of_struc_formula "\t" pdef.Iast.view_formula)^"\n normalized:"^(Iprinter.string_of_struc_formula "\t" wf)^"\n") in*)
		let cpdef = AS.trans_view iprog new_pdef in
		let old_vdec = !cprog.C.prog_view_decls in
		!cprog.C.prog_view_decls <- (cpdef :: !cprog.C.prog_view_decls);
(* added 07.04.2008	*)	
		(*ignore (print_string ("init: "^(Iprinter.string_of_struc_formula "" pdef.Iast.view_formula )^"\n normalized: "^
							 (Iprinter.string_of_struc_formula "" wf )^"\n translated: "^
							 (Cprinter.string_of_struc_formula cpdef.Cast.view_formula)
							 ^"\n"
							 )
				)*)
		(* used to do this for all preds, due to mutable fields formulas exploded, i see no reason to redo for all: 
		ignore (List.map (fun vdef -> AS.compute_view_x_formula cprog vdef !Globals.n_xpure) cprog.C.prog_view_decls);*)
		ignore (AS.compute_view_x_formula !cprog cpdef !Globals.n_xpure);
        ignore (AS.set_materialized_prop cpdef);
	let cpdef = AS.fill_one_base_case !cprog cpdef in 
    let cpdef = 
      if !Globals.enable_case_inference then 
        AS.view_case_inference !cprog iprog.I.prog_view_decls cpdef else cpdef in
		let n_cpdef = AS.view_prune_inv_inference !cprog cpdef in
    !cprog.C.prog_view_decls <- (n_cpdef :: old_vdec);
    let n_cpdef = {n_cpdef with 
        C.view_formula =  Solver.prune_pred_struc !cprog true n_cpdef.C.view_formula ;
        C.view_un_struc_formula = List.map (fun (c1,c2) -> (Solver.prune_preds !cprog true c1,c2)) n_cpdef.C.view_un_struc_formula;}in
		let _ = if !Globals.print_core then print_string (Cprinter.string_of_view_decl n_cpdef ^"\n") else () in
		!cprog.C.prog_view_decls <- (n_cpdef :: old_vdec)
		(*print_string ("\npred def: "^(Cprinter.string_of_view_decl cpdef)^"\n")*)
(* added 07.04.2008	*)									  
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_view_decls <- tmp
  else
	print_string (pdef.I.view_name ^ " is already defined.\n")

let process_pred_def pdef = 
  Gen.Debug.no_1 "process_pred_def" pr_no pr_no process_pred_def pdef

let process_pred_def_4_iast pdef = 
  if check_data_pred_name pdef.I.view_name then
	let tmp = iprog.I.prog_view_decls in
	  try
		let h = (self,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in
		let p = (self,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in
		let wf,_ = AS.case_normalize_struc_formula iprog h p pdef.Iast.view_formula false false [] in
		let new_pdef = {pdef with Iast.view_formula = wf} in
		iprog.I.prog_view_decls <- ( new_pdef :: iprog.I.prog_view_decls);
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_view_decls <- tmp
  else
	print_string (pdef.I.view_name ^ " is already defined.\n")

let process_pred_def_4_iast pdef = 
  Gen.Debug.no_1 "process_pred_def_4_iast" pr_no pr_no process_pred_def_4_iast pdef


let convert_pred_to_cast () = 
  let tmp_views = (AS.order_views (iprog.I.prog_view_decls)) in
  let _ = Iast.set_check_fixpt iprog.I.prog_data_decls tmp_views in
  iprog.I.prog_view_decls <- tmp_views;
  let cviews = List.map (AS.trans_view iprog) tmp_views in
  let _ = !cprog.C.prog_view_decls <- cviews in
  let _ =  (List.map (fun vdef -> AS.compute_view_x_formula !cprog vdef !Globals.n_xpure) cviews) in
  let _ = (List.map (fun vdef -> AS.set_materialized_prop vdef) cviews) in
  let cprog1 = AS.fill_base_case !cprog in
  let cprog2 = AS.sat_warnings cprog1 in        
  let cprog3 = if (!Globals.enable_case_inference or !Globals.allow_pred_spec) then AS.pred_prune_inference cprog2 else cprog2 in
  let cprog4 = (AS.add_pre_to_cprog cprog3) in
  let cprog5 = if !Globals.enable_case_inference then AS.case_inference iprog cprog4 else cprog4 in
  let _ = if !Globals.print_core then print_string (Cprinter.string_of_program cprog5) else () in
  cprog := cprog5

let convert_pred_to_cast () = 
  Gen.Debug.no_1 "convert_pred_to_cast" pr_no pr_no convert_pred_to_cast ()

(* An Hoa : process the relational definition *)
let process_rel_def rdef =
  if check_data_pred_name rdef.I.rel_name then
	let tmp = iprog.I.prog_rel_decls in
	  try
		(*let h = (self,Unprimed)::(res,Unprimed)::(List.map (fun c-> (c,Unprimed)) rdef.Iast.view_vars ) in
		let p = (self,Primed)::(res,Primed)::(List.map (fun c-> (c,Primed)) rdef.Iast.view_vars ) in
		let wf,_ = AS.case_normalize_struc_formula iprog h p rdef.Iast.view_formula false false [] in
		let new_rdef = {rdef with Iast.view_formula = wf} in
		iprog.I.prog_view_decls <- ( new_rdef :: iprog.I.prog_view_decls);
		let crdef = AS.trans_view iprog new_rdef in
		let old_vdec = cprog.C.prog_view_decls in
		cprog.C.prog_view_decls <- (crdef :: cprog.C.prog_view_decls);
		ignore (AS.compute_view_x_formula cprog crdef !Globals.n_xpure);
    let crdef = 
      if !Globals.enable_case_inference then 
        AS.view_case_inference cprog iprog.I.prog_view_decls crdef else crdef in
		let n_crdef = AS.view_prune_inv_inference cprog crdef in
    cprog.C.prog_view_decls <- (n_crdef :: old_vdec);
    let n_crdef = {n_crdef with 
        C.view_formula =  Solver.prune_pred_struc cprog true n_crdef.C.view_formula ;
        C.view_un_struc_formula = List.map (fun (c1,c2) -> (Solver.prune_preds cprog true c1,c2)) n_crdef.C.view_un_struc_formula;}in
		let _ = if !Globals.print_core then print_string (Cprinter.string_of_view_decl n_crdef ^"\n") else () in
		cprog.C.prog_view_decls <- (n_crdef :: old_vdec) *)
			iprog.I.prog_rel_decls <- ( rdef :: iprog.I.prog_rel_decls);
			let crdef = AS.trans_rel iprog rdef in !cprog.C.prog_rel_decls <- (crdef :: !cprog.C.prog_rel_decls);
			(* Forward the relation to the smt solver. *)
			Smtsolver.add_relation crdef.C.rel_name crdef.C.rel_vars crdef.C.rel_formula;
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_rel_decls <- tmp
  else
		print_string (rdef.I.rel_name ^ " is already defined.\n")


(** An Hoa : process axiom
 *)
let process_axiom_def adef = begin
	iprog.I.prog_axiom_decls <- adef :: iprog.I.prog_axiom_decls;
	let cadef = AS.trans_axiom iprog adef in
		!cprog.C.prog_axiom_decls <- (cadef :: !cprog.C.prog_axiom_decls);
	(* Forward the axiom to the smt solver. *)
	Smtsolver.add_axiom cadef.C.axiom_hypothesis Smtsolver.IMPLIES cadef.C.axiom_conclusion;
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
	(* let _ = Iast.build_exc_hierarchy true iprog in *)
	(* let _ = Exc.compute_hierarchy 2 () in *)
	let cddef = AS.trans_data iprog ddef in
	let _ = if !Globals.print_core then print_string (Cprinter.string_of_data_decl cddef ^"\n") else () in
	  !cprog.C.prog_data_decls <- cddef :: !cprog.C.prog_data_decls
      with
	| _ -> dummy_exception() ; iprog.I.prog_data_decls <- tmp
      else begin
        dummy_exception() ;
	print_string (ddef.I.data_name ^ " is already defined.\n")
      end

let process_data_def ddef =
  Gen.Debug.no_1 "process_data_def" pr_no pr_no process_data_def ddef 

(** An Hoa : Second stage of parsing : iprog already contains the whole input.
             We do a reparse in order to distinguish between data & enum that
             is deferred in case of mutually dependent data definition.
 **)
let perform_second_parsing_stage () =
	let cddefs = List.map (AS.trans_data iprog) iprog.I.prog_data_decls in
		!cprog.C.prog_data_decls <- cddefs
	
let rec meta_to_struc_formula_x (mf0 : meta_formula) quant fv_idents stab : CF.struc_formula = match mf0 with
  | MetaFormCF mf -> (Cformula.formula_to_struc_formula mf)
  | MetaFormLCF mf -> (Cformula.formula_to_struc_formula (List.hd mf))
  | MetaForm mf -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let p = List.map (fun c-> (c,Primed)) fv_idents in
      let wf,_ = AS.case_normalize_struc_formula iprog h p (Iformula.formula_to_struc_formula mf) false true [] in
      AS.trans_I2C_struc_formula iprog quant fv_idents wf stab false (*(Cpure.Prim Void) []*)
  | MetaVar mvar -> begin
      try 
        let mf = get_var mvar in
          meta_to_struc_formula_x mf quant fv_idents stab
      with
        | Not_found ->
          dummy_exception() ;
          print_string (mvar ^ " is undefined.\n");
          raise SLEEK_Exception
      end
  | MetaCompose (vs, mf1, mf2) -> begin
      let cf1 = meta_to_struc_formula_x mf1 quant fv_idents stab in
      let cf2 = meta_to_struc_formula_x mf2 quant fv_idents stab in
      let svs = List.map (fun v -> AS.get_spec_var_stab v stab no_pos) vs in
      let res = Solver.compose_struc_formula cf1 cf2 svs no_pos in
      res
    end
  | MetaEForm b -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let p = List.map (fun c-> (c,Primed)) fv_idents in
      let wf,_ = AS.case_normalize_struc_formula iprog h p b false true [] in
      let res = AS.trans_I2C_struc_formula iprog quant fv_idents wf stab false (*(Cpure.Prim Void) [] *) in
      (* let _ = print_string ("\n1 before meta: " ^(Iprinter.string_of_struc_formula b)^"\n") in *)
      (* let _ = print_string ("\n2 before meta: " ^(Iprinter.string_of_struc_formula wf)^"\n") in *)
      (*let _ = print_string ("\n after meta: " ^ (Cprinter.string_of_struc_formula res)) in*)
      res
  | MetaEFormCF b -> b (* assume it has already been normalized *)

let meta_to_struc_formula (mf0 : meta_formula) quant fv_idents stab : CF.struc_formula =
  let pr1 = string_of_meta_formula in
  let pr2 = string_of_bool in
  let pr3 = Cprinter.string_of_struc_formula in 
  Gen.Debug.no_2 "meta_to_struc_formula" pr1 pr2 pr3 (fun _ _ -> meta_to_struc_formula_x mf0 quant fv_idents stab) mf0 quant

(* An Hoa : DETECT THAT EITHER OF 
AS.case_normalize_formula iprog h mf
Astsimp.collect_type_info_formula iprog wf stab false
AS.trans_formula iprog quant
IN THE FUNCTION GIVE AN EXCEPTION
TODO Check the 3 functions above!!!
*)
let rec meta_to_formula (mf0 : meta_formula) quant fv_idents stab : CF.formula = match mf0 with
  | MetaFormCF mf -> mf
  | MetaFormLCF mf ->	(List.hd mf)
  | MetaForm mf ->
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let wf = AS.case_normalize_formula iprog h mf in
      let _ = Astsimp.gather_type_info_formula iprog wf stab false in
      let r = AS.trans_formula iprog quant fv_idents false wf stab false in
      (*let _ = print_string (" before sf: " ^(Iprinter.string_of_formula wf)^"\n") in
      let _ = print_string (" after sf: " ^(Cprinter.string_of_formula r)^"\n") in*)
      r
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
  | MetaEForm _ | MetaEFormCF _ -> report_error no_pos ("cannot have structured formula in antecedent")

let run_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
		(* An Hoa : PRINT OUT THE INPUT *)
		(*  let _ = print_string "Call [Sleekengine.process_entail_check] with\n" in *)
		(* let _ = print_string ("ANTECEDENCE : " ^ (string_of_meta_formula iante0) ^ "\n") in *)
		(* let _ = print_string ("CONSEQUENCE : " ^ (string_of_meta_formula iconseq0) ^ "\n") in *)
  let _ = residues := None in
  let stab = H.create 103 in
  let ante = meta_to_formula iante0 false [] stab in    
  let ante = Solver.prune_preds !cprog true ante in
  let fvs = CF.fv ante in
  let fv_idents = List.map CP.name_of_spec_var fvs in
  let conseq = meta_to_struc_formula iconseq0 false fv_idents stab in
  let conseq = Solver.prune_pred_struc !cprog true conseq in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  (*let ctx = List.hd (Cformula.change_flow_ctx  !top_flow_int !n_flow_int [ctx]) in*)
  (* let _ = print_string ("\n checking: "^(Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") in *)
  (* An Hoa TODO uncomment let _ = if !Globals.print_core then print_string ((Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") else () in *)
  let _ = if !Globals.print_core then print_string ("\nrun_entail_check:\n"^(Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") else () in
  let ctx = CF.transform_context (Solver.elim_unsat_es !cprog (ref 1)) ctx in
  (*let _ = print_string ("\n checking2: "^(Cprinter.string_of_context ctx)^"\n") in*)
  (*let ante_flow_ff = (CF.flow_formula_of_formula ante) in*)
  let rs1, _ = 
  if not !Globals.disable_failure_explaining then
    Solver.heap_entail_struc_init_bug_inv !cprog false false 
        (CF.SuccCtx[ctx]) conseq no_pos None
  else
     Solver.heap_entail_struc_init !cprog false false 
        (CF.SuccCtx[ctx]) conseq no_pos None
  in
  (* let length_ctx ctx = match ctx with *)
  (*   | CF.FailCtx _ -> 0 *)
  (*   | CF.SuccCtx ctx0 -> List.length ctx0 in *)
  let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in
  residues := Some rs;
  (* print_string ( "\n Sleekengine.ml, run_entail_check 2: " ^ (Cprinter.string_of_list_context rs)^"\n"); *)
  flush stdout;
  let res =
    if not !Globals.disable_failure_explaining then ((not (CF.isFailCtx_gen rs)))
    else ((not (CF.isFailCtx rs)))
  in
  (res, rs)

let run_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let pr = string_of_meta_formula in
  let pr_2 = pr_pair string_of_bool Cprinter.string_of_list_context in
  Gen.Debug.no_2 "run_entail_check" pr pr pr_2 run_entail_check iante0 iconseq0

let print_entail_result (valid: bool) (residue: CF.list_context) (num_id: string) =
  if not valid then
    begin
      let s =
        if not !Globals.disable_failure_explaining then
          match CF.get_must_failure residue with
            | Some s -> "(must) cause:"^s 
            | _ -> (match CF.get_may_failure residue with
                | Some s -> "(may) cause:"^s
                | None -> "INCONSISTENCY : expected failure but success instead"
              )
        else ""
      in
      print_string (num_id^": Fail. "^s^"\n")
          (*if !Globals.print_err_sleek then *)
          (* ;print_string ("printing here: "^(Cprinter.string_of_list_context rs)) *)
    end
  else
    begin
	  print_string (num_id^": Valid.\n")
          (* ;print_string ("printing here: "^(Cprinter.string_of_list_context rs)) *)
    end  

let print_exc (check_id: string) =
  Printexc.print_backtrace stdout;
  dummy_exception() ; 
  print_string ("exception in " ^ check_id ^ " check\n")

let process_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let num_id = "Entail ("^(string_of_int (sleek_proof_counter#inc_and_get))^")" in
  try 
    let valid, rs = run_entail_check iante0 iconseq0 in
    print_entail_result valid rs num_id
  with _ -> print_exc num_id

let process_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let pr = string_of_meta_formula in
  Gen.Debug.no_2 "process_entail_check" pr pr (fun _ -> "?") process_entail_check iante0 iconseq0

let process_capture_residue (lvar : ident) = 
	let flist = match !residues with 
      | None -> [(CF.mkTrue (CF.mkTrueFlow()) no_pos)]
      | Some s -> CF.list_formula_of_list_context s in
		put_var lvar (Sleekcommons.MetaFormLCF flist)

let process_lemma ldef =
  let ldef = AS.case_normalize_coerc iprog ldef in
  let l2r, r2l = AS.trans_one_coercion iprog ldef in
  let l2r = List.concat (List.map (fun c-> AS.coerc_spec !cprog true c) l2r) in
  let r2l = List.concat (List.map (fun c-> AS.coerc_spec !cprog false c) r2l) in
  let _ = if !Globals.print_core then 
    print_string ("\nleft:\n " ^ (Cprinter.string_of_coerc_decl_list l2r) ^"\n right:\n"^ (Cprinter.string_of_coerc_decl_list r2l) ^"\n") else () in
  !cprog.C.prog_left_coercions <- l2r @ !cprog.C.prog_left_coercions;
  !cprog.C.prog_right_coercions <- r2l @ !cprog.C.prog_right_coercions;
  let get_coercion c_lst = match c_lst with 
    | [c] -> Some c
    | _ -> None in
  let l2r = get_coercion l2r in
  let r2l = get_coercion r2l in
  residues := None;
  residues := (LP.verify_lemma l2r r2l !cprog (ldef.I.coercion_name) ldef.I.coercion_type)

let process_lemma ldef =
  Gen.Debug.no_1 "process_lemma" Iprinter.string_of_coerc_decl (fun _ -> "?") process_lemma ldef


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
        | Some s -> print_string ((Cprinter.string_of_list_formula 
              (CF.list_formula_of_list_context s))^"\n")
	  else
			print_string ("unsupported print command: " ^ pcmd)

let get_residue () =
  !residues
  (*match !residues with*)
    (*| None -> ""*)
    (*| Some s -> Cprinter.string_of_list_formula (CF.list_formula_of_list_context s)*)


