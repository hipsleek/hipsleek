(*
  The frontend engine of SLEEK.
*)

open Globals
open Sleekcommons
open Gen.Basic
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Perm
open Label_only

module H = Hashtbl
module I = Iast
module Inf = Infer
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure
module LP = Lemproving
module AS = Astsimp
module DD = Debug
module XF = Xmlfront
module NF = Nativefront
module NEG = Neg

let sleek_proof_counter = new Gen.counter 0

(*
  Global data structures. If we want to support push/pop commands,
  we'll need to make them into a stack of scopes.
*)
let iobj_def =  {I.data_name = "Object";
				 I.data_fields = [];
				 I.data_parent_name = "";
				 I.data_invs = []; (* F.mkTrue no_pos; *)
				 I.data_methods = [] }

let iprog = { I.prog_data_decls = [iobj_def];
			  I.prog_global_var_decls = [];
			  I.prog_logical_var_decls = [];
			  I.prog_enum_decls = [];
			  I.prog_view_decls = [];
			  I.prog_func_decls = [];
			  I.prog_rel_decls = [];
			  I.prog_rel_ids = [];
			  I.prog_axiom_decls = []; (* [4/10/2011] An Hoa *)
			  I.prog_proc_decls = [];
			  I.prog_coercion_decls = [];
              I.prog_hopred_decls = [];
			  I. prog_barrier_decls = [];
}

let cobj_def = { C.data_name = "Object";
				 C.data_fields = [];
				 C.data_parent_name = "";
				 C.data_invs = [];
				 C.data_methods = [] }

let cprog = ref { C.prog_data_decls = [];
			  C.prog_view_decls = [];
			  C.prog_logical_vars = [];
(*				C.prog_func_decls = [];*)
				C.prog_rel_decls = []; (* An Hoa *)
				C.prog_axiom_decls = []; (* [4/10/2011] An Hoa *)
			  (*C.old_proc_decls = [];*)
			  C.new_proc_decls = Hashtbl.create 1; (* no need for proc *)
			  C.prog_left_coercions = [];
			  C.prog_right_coercions = [];
			  C. prog_barrier_decls = []}

let residues =  ref (None : (CF.list_context * bool) option)    (* parameter 'bool' is used for printing *)

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
			  		| Not_found -> 
              begin
					      try
			        		let _ = I.look_up_func_def_raw iprog.I.prog_func_decls name in
						      false
					      with
			        		| Not_found -> true
		        	end
		  	end
	  end

let check_data_pred_name name :bool = 
  let pr1 x = x in
  let pr2 = string_of_bool in 
  Debug.no_1 "check_data_pred_name" pr1 pr2 (fun _ -> check_data_pred_name name) name
    

let process_pred_def pdef = 
  (* TODO : how come this method not called? *)
  (* let _ = print_string ("process_pred_def:" *)
  (*                       ^ "\n\n") in *)
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
    (*let cpdef =  if !Globals.enable_case_inference then AS.view_case_inference !cprog iprog.I.prog_view_decls cpdef else cpdef in*)
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
  let pr = Iprinter.string_of_view_decl in
  Debug.no_1 "process_pred_def" pr pr_no process_pred_def pdef

let process_pred_def_4_iast pdef = 
  if check_data_pred_name pdef.I.view_name then
	let tmp = iprog.I.prog_view_decls in
	  try
		let h = (self,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in
		let p = (self,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in
		let wf,_ = AS.case_normalize_struc_formula iprog h p pdef.Iast.view_formula false false [] in
        let inv_lock = pdef.I.view_inv_lock in
        let inv_lock =
          (match inv_lock with
            | None -> None
            | Some f ->
                let new_f = AS.case_normalize_formula iprog h f in (*TO CHECK: h or p*)
                Some new_f)
        in
		let new_pdef = {pdef with Iast.view_formula = wf;Iast.view_inv_lock = inv_lock} in
		iprog.I.prog_view_decls <- ( new_pdef :: iprog.I.prog_view_decls);
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_view_decls <- tmp
  else
	print_string (pdef.I.view_name ^ " is already defined.\n")

let process_pred_def_4_iast pdef = 
  let pr = Iprinter.string_of_view_decl in
  Debug.no_1 "process_pred_def_4_iast" pr pr_no process_pred_def_4_iast pdef


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
  let cprog5 = (*if !Globals.enable_case_inference then AS.case_inference iprog cprog4 else*) cprog4 in
  let _ = if !Globals.print_input then print_string (Iprinter.string_of_program iprog) else () in
  let _ = if !Globals.print_core then print_string (Cprinter.string_of_program cprog5) else () in
  cprog := cprog5

let convert_pred_to_cast () = 
  Debug.no_1 "convert_pred_to_cast" pr_no pr_no convert_pred_to_cast ()

(* TODO: *)
let process_func_def fdef =
  if check_data_pred_name fdef.I.func_name then
	let tmp = iprog.I.prog_func_decls in
	  try
			iprog.I.prog_func_decls <- ( fdef :: iprog.I.prog_func_decls);
			(*let cfdef = AS.trans_func iprog fdef in !cprog.C.prog_func_decls <- (cfdef :: !cprog.C.prog_func_decls);*)
			(*Smtsolver.add_function cfdef.C.func_name cfdef.C.func_vars cfdef.C.func_formula;*)
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_func_decls <- tmp
  else
		print_string (fdef.I.func_name ^ " is already defined.\n")

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
	

let process_lemma ldef =
  let ldef = AS.case_normalize_coerc iprog ldef in
  let l2r, r2l = AS.trans_one_coercion iprog ldef in
  let l2r = List.concat (List.map (fun c-> AS.coerc_spec !cprog true c) l2r) in
  let r2l = List.concat (List.map (fun c-> AS.coerc_spec !cprog false c) r2l) in
  (* TODO : WN print input_ast *)
  let _ = if !Globals.print_input then print_string (Iprinter.string_of_coerc_decl ldef) in
  let _ = if !Globals.print_core then 
    print_string ("\nleft:\n " ^ (Cprinter.string_of_coerc_decl_list l2r) ^"\n right:\n"^ (Cprinter.string_of_coerc_decl_list r2l) ^"\n") else () in
  !cprog.C.prog_left_coercions <- l2r @ !cprog.C.prog_left_coercions;
  !cprog.C.prog_right_coercions <- r2l @ !cprog.C.prog_right_coercions;
  let get_coercion c_lst = match c_lst with 
    | [c] -> Some c
    | _ -> None in
  let l2r = get_coercion l2r in
  let r2l = get_coercion r2l in
  let res = LP.verify_lemma l2r r2l !cprog (ldef.I.coercion_name) ldef.I.coercion_type in
  residues := (match res with
               | None -> None;
               | Some ls_ctx -> Some (ls_ctx, true))

let process_lemma ldef =
  Debug.no_1 "process_lemma" Iprinter.string_of_coerc_decl (fun _ -> "?") process_lemma ldef

	
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
	let _ = if !Globals.print_input then print_string (Iprinter.string_of_data_decl ddef ^"\n") else () in
	let _ = if !Globals.print_core then print_string (Cprinter.string_of_data_decl cddef ^"\n") else () in
	!cprog.C.prog_data_decls <- cddef :: !cprog.C.prog_data_decls;
	if !perm=NoPerm || not !enable_split_lemma_gen then () 
	else (process_lemma (Iast.gen_normalize_lemma_split ddef);process_lemma (Iast.gen_normalize_lemma_comb ddef))
      with
	| _ -> dummy_exception() ; iprog.I.prog_data_decls <- tmp
      else begin
        dummy_exception() ;
	print_string (ddef.I.data_name ^ " is already defined.\n")
      end

let process_barrier_def bd = 
    if !Globals.print_core then print_string (Iprinter.string_of_barrier_decl bd) else () ;
	 try
	    let bd = AS.case_normalize_barrier iprog bd in
		let cbd = AS.trans_bdecl iprog bd in
		(*let cbd = AS.normalize_barr_decl !cprog cbd in*)
		AS.check_barrier_wf !cprog cbd;
		print_string ("Barrrier "^bd.I.barrier_name^" Success\n")
	 with 
		| Error.Malformed_barrier s -> print_string ("Barrrier "^bd.I.barrier_name^" Fail: "^s^"\n")
    
let process_barrier_def bd = 
	Debug.no_1 "process_barrier" (fun _ -> "") (fun _ -> "done") process_barrier_def bd
  

	  
let process_data_def ddef =
  Debug.no_1 "process_data_def" pr_no pr_no process_data_def ddef 

(** An Hoa : Second stage of parsing : iprog already contains the whole input.
             We do a reparse in order to distinguish between data & enum that
             is deferred in case of mutually dependent data definition.
 **)
let perform_second_parsing_stage () =
	let cddefs = List.map (AS.trans_data iprog) iprog.I.prog_data_decls in
		!cprog.C.prog_data_decls <- cddefs
	
let rec meta_to_struc_formula (mf0 : meta_formula) quant fv_idents stab : CF.struc_formula = 
  let rec helper (mf0 : meta_formula) quant fv_idents stab : CF.struc_formula = 
    match mf0 with
  | MetaFormCF mf -> 
      (Cformula.formula_to_struc_formula mf)
  | MetaFormLCF mf -> 
      (Cformula.formula_to_struc_formula (List.hd mf))
  | MetaForm mf -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let p = List.map (fun c-> (c,Primed)) fv_idents in
      let wf,_ = AS.case_normalize_struc_formula iprog h p (Iformula.formula_to_struc_formula mf) false true [] in
      AS.trans_I2C_struc_formula iprog quant fv_idents wf stab false (*(Cpure.Prim Void) []*)
  | MetaVar mvar -> 
      begin
      try 
        let mf = get_var mvar in
          helper mf quant fv_idents stab
      with
        | Not_found ->
          dummy_exception() ;
          print_string (mvar ^ " is undefined.\n");
          raise SLEEK_Exception
      end
  | MetaCompose (vs, mf1, mf2) -> 
      begin
      let cf1 = helper mf1 quant fv_idents stab in
      let cf2 = helper mf2 quant fv_idents stab in
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
  in helper mf0 quant fv_idents stab 


let meta_to_struc_formula (mf0 : meta_formula) quant fv_idents stab : CF.struc_formula = Debug.no_4 "meta_to_struc_formula"
  string_of_meta_formula
  string_of_bool
  string_of_ident_list
  AS.string_of_stab
  Cprinter.string_of_struc_formula
  meta_to_struc_formula mf0 quant fv_idents stab

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
      (* let _ = print_string (" before sf: " ^(Iprinter.string_of_formula wf)^"\n") in *)
      (* let _ = print_string (" after sf: " ^(Cprinter.string_of_formula r)^"\n") in *)
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

let meta_to_formula (mf0 : meta_formula) quant fv_idents stab : CF.formula =
  let pr_meta = string_of_meta_formula in
  let pr_f = Cprinter.string_of_formula in
  Debug.no_1 "Sleekengine.meta_to_formual" pr_meta pr_f
             (fun mf -> meta_to_formula mf quant fv_idents stab) mf0

(* let run_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) = *)
(* 		(\*  let _ = print_string "Call [Sleekengine.run_entail_check] with\n" in *\) *)
(* 		(\* let _ = print_string ("ANTECEDENCE : " ^ (string_of_meta_formula iante0) ^ "\n") in *\) *)
(* 		(\* let _ = print_string ("CONSEQUENCE : " ^ (string_of_meta_formula iconseq0) ^ "\n") in *\) *)
(*   let _ = residues := None in *)
(*   let stab = H.create 103 in *)
(*   let ante = meta_to_formula iante0 false [] stab in *)
(*   (\*let _ = print_endline "1: prune ante in check entailment" in*\) *)
(*   let ante = Solver.prune_preds !cprog true ante in *)
(*   let ante = *)
(*     if (Perm.allow_perm ()) then *)
(*       (\*add default full permission to ante; *)
(*         need to add type of full perm to stab *\) *)
(*       CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante *)
(*     else ante *)
(*   in *)
(*   let vk = AS.fresh_proc_var_kind stab Float in *)
(*   let _ = H.add stab (full_perm_name ()) vk in *)
(* (\*  let _ = flush stdout in*\) *)
(*   let fvs = CF.fv ante in *)
(*   let fv_idents = List.map CP.name_of_spec_var fvs in *)
(*   let conseq = meta_to_struc_formula iconseq0 false fv_idents stab in *)
(*   (\*let _ = print_endline "2: prune conseq in check entailment" in*\) *)
(*   let conseq = Solver.prune_pred_struc !cprog true conseq in *)
(*   let _ = Debug.devel_pprint ("\nrun_entail_check:" *)
(*                         ^ "\n ### ante = "^(Cprinter.string_of_formula ante) *)
(*                         ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq) *)
(*                         ^"\n\n") no_pos in *)
(*   let es = CF.empty_es (CF.mkTrueFlow ()) no_pos in *)
(*   let ante = Solver.normalize_formula_w_coers !cprog es ante !cprog.C.prog_left_coercions in *)
(*   let _ = Debug.devel_pprint ("\nrun_entail_check: after normalization" *)
(*                         ^ "\n ### ante = "^(Cprinter.string_of_formula ante) *)
(*                         ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq) *)
(*                         ^"\n\n") no_pos in *)
(*   let ectx = CF.empty_ctx (CF.mkTrueFlow ()) no_pos in *)
(*   let ctx = CF.build_context ectx ante no_pos in *)
(*   (\*let ctx = List.hd (Cformula.change_flow_ctx  !top_flow_int !norm_flow_int [ctx]) in*\) *)
(*   (\* (\\*let ctx = List.hd (Cformula.change_flow_ctx  !top_flow_int !n_flow_int [ctx]) in*\\) *\) *)
(*   (\* let _ = print_string ("\n checking: "^(Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") in *\) *)
(*   (\* An Hoa TODO uncomment  *\) *)
(*   let _ = if !Globals.print_core then print_string ("\nrun_entail_check:\n"^(Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") else () in *)
(*   let _ = if !Globals.print_input then print_string ("\n"^(string_of_meta_formula iante0)^" |- "^(string_of_meta_formula iconseq0)^"\n") else () in *)
(*   let ctx = CF.transform_context (Solver.elim_unsat_es !cprog (ref 1)) ctx in *)
(*   (\* let ante_flow_ff = (CF.flow_formula_of_formula ante) in *\) *)
(*   let rs1, _ = *)
(*   if not !Globals.disable_failure_explaining then *)
(*     Solver.heap_entail_struc_init_bug_inv !cprog false false *)
(*         (CF.SuccCtx[ctx]) conseq no_pos None *)
(*   else *)
(*      Solver.heap_entail_struc_init !cprog false false *)
(*         (CF.SuccCtx[ctx]) conseq no_pos None *)
(*   in *)
(*   (\* let length_ctx ctx = match ctx with *\) *)
(*   (\*   | CF.FailCtx _ -> 0 *\) *)
(*   (\*   | CF.SuccCtx ctx0 -> List.length ctx0 in *\) *)
(*   let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in *)
(*   residues := Some rs; *)
(*   (\* print_string ( "\n Sleekengine.ml, run_entail_check 2: " ^ (Cprinter.string_of_list_context rs)^"\n"); *\) *)
(*   flush stdout; *)
(*   let res = *)
(*     if not !Globals.disable_failure_explaining then ((not (CF.isFailCtx_gen rs))) *)
(*     else ((not (CF.isFailCtx rs))) *)
(*   in *)
(*   (res, rs) *)

let run_infer_one_pass (ivars: ident list) (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let _ = residues := None in
  let stab = H.create 103 in
  let _ = if (!Globals.print_input) then print_endline ("INPUT: \n ### ante = " ^ (string_of_meta_formula iante0) ^"\n ### conseq = " ^ (string_of_meta_formula iconseq0)) else () in
  let _ = Debug.devel_pprint ("\nrun_entail_check:"
                              ^ "\n ### iante0 = "^(string_of_meta_formula iante0)
                              ^ "\n ### iconseq0 = "^(string_of_meta_formula iconseq0)
                              ^"\n\n") no_pos in
  let ante = meta_to_formula iante0 false [] stab in
  (*let ante = Solver.normalize_formula_w_coers !cprog (CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos) ante !cprog.C.prog_left_coercions in*)
  let ante = Solver.prune_preds !cprog true ante in
  let ante = (*important for permissions*)
    if (Perm.allow_perm ()) then
      (*add default full permission to ante;
        need to add type of full perm to stab *)
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  let vk = AS.fresh_proc_var_kind stab Float in
  let _ = H.add stab (full_perm_name ()) vk in
(*  let _ = flush stdout in*)
  (* let csq_extra = meta_to_formula iconseq0 false [] stab in *)
  (* let conseq_fvs = CF.fv csq_extra in *)
  (* let _ = print_endline ("conseq vars"^(Cprinter.string_of_spec_var_list conseq_fvs)) in *)
  let fvs = CF.fv ante in
  (* let ivars_fvs = List.map (fun n -> CP.SpecVar (UNK,n,Unprimed)) ivars in *)
  (* let _ = print_endline ("ivars"^(Cprinter.string_of_spec_var_list ivars_fvs)) in *)
  (* let _ = print_endline ("ante vars"^(Cprinter.string_of_spec_var_list fvs)) in *)
  let fv_idents = (List.map CP.name_of_spec_var fvs)@ivars in
  (* need to make ivars be global *)
  let conseq = meta_to_struc_formula iconseq0 false fv_idents (* (List.map CP.name_of_spec_var fvs) *) stab in
  (* let conseq1 = meta_to_struc_formula iconseq0 false fv_idents stab in *)
  let conseq = Solver.prune_pred_struc !cprog true conseq in
  let _ = Debug.devel_zprint (lazy ("\nrun_entail_check:"
                        ^"\n ### ivars = "^(pr_list pr_id ivars)
                        ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                        ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq)
                        ^"\n\n")) no_pos in
  let es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ante = Solver.normalize_formula_w_coers !cprog es ante !cprog.C.prog_left_coercions in
  let _ = if (!Globals.print_core) then print_endline ("INPUT: \n ### ante = " ^ (Cprinter.string_of_formula ante) ^"\n ### conseq = " ^ (Cprinter.string_of_struc_formula conseq)) else () in
  let _ = Debug.devel_zprint (lazy ("\nrun_entail_check: after normalization"
                        ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                        ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq)
                        ^"\n\n")) no_pos in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  (* List of vars appearing in original formula *)
  let orig_vars = CF.fv ante @ CF.struc_fv conseq in
  (* List of vars needed for abduction process *)
  let vars = List.map (fun v -> AS.get_spec_var_stab_infer v orig_vars no_pos) ivars in
  (* Init context with infer_vars and orig_vars *)
  let (vrel,iv) = List.partition (fun v -> CP.type_of_spec_var v == RelT(*  ||  *)
              (* CP.type_of_spec_var v == FuncT *)) vars in
  (* let _ = print_endline ("WN: vars rel"^(Cprinter.string_of_spec_var_list vrel)) in *)
  (* let _ = print_endline ("WN: vars inf"^(Cprinter.string_of_spec_var_list iv)) in *)
  let ctx = Inf.init_vars ctx iv vrel orig_vars in

  let _ = if !Globals.print_core 
    then print_string ("\nrun_infer:\n"^(Cprinter.string_of_formula ante)
        ^" "^(pr_list pr_id ivars)
      ^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") 
    else () 
  in
  let ctx = CF.transform_context (Solver.elim_unsat_es !cprog (ref 1)) ctx in
  let rs1, _ = 
    if not !Globals.disable_failure_explaining then
      Solver.heap_entail_struc_init_bug_inv !cprog false false 
        (CF.SuccCtx[ctx]) conseq no_pos None
    else
      Solver.heap_entail_struc_init !cprog false false 
        (CF.SuccCtx[ctx]) conseq no_pos None
  in
  (* let _ = print_endline ("WN# 1:"^(Cprinter.string_of_list_context rs1)) in *)
  let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in
  (* let _ = print_endline ("WN# 2:"^(Cprinter.string_of_list_context rs)) in *)
  flush stdout;
  let res =
    if not !Globals.disable_failure_explaining then ((not (CF.isFailCtx_gen rs)))
    else ((not (CF.isFailCtx rs))) in
  residues := Some (rs, res);
  (res, rs,ante)

let run_infer_one_pass ivars (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let pr = string_of_meta_formula in
  let pr1 = pr_list pr_id in
  let pr_2 = fun (v,r,_) -> pr_pair string_of_bool Cprinter.string_of_list_context (v,r) in
  Debug.no_3 "run_infer_one_pass" pr1 pr pr pr_2 run_infer_one_pass ivars iante0 iconseq0

let run_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  run_infer_one_pass [] iante0 iconseq0

let run_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let pr = string_of_meta_formula in
  let pr_2 = pr_pair string_of_bool Cprinter.string_of_list_context in
  Debug.no_2 "run_entail_check" pr pr pr_2 run_entail_check iante0 iconseq0

let run_sat_check (iante0 : meta_formula) =
  let _ = residues := None in
  let stab = H.create 103 in
  let _ = if (!Globals.print_input) then print_endline ("INPUT: \n ### formula = " ^ (string_of_meta_formula iante0)) else () in
  let _ = Debug.devel_pprint ("\nrun_sat_check:"
                              ^ "\n ### iante0 = "^(string_of_meta_formula iante0)
                              ^"\n\n") no_pos in
  let ante = meta_to_formula iante0 false [] stab in
  let ante = Solver.prune_preds !cprog false ante in
  let fvs = CF.fv ante in
  let fv_idents = (List.map CP.name_of_spec_var fvs) in
  (* need to make ivars be global *)
  (* let conseq = meta_to_struc_formula iconseq0 false fv_idents stab in *)
  (* let conseq = Solver.prune_pred_struc !cprog true conseq in *)
  let _ = Debug.devel_zprint (lazy ("\nrun_sat_check:"
                        (* ^"\n ### ivars = "^(pr_list pr_id ivars) *)
                        ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                        (* ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq) *)
                        ^"\n\n")) no_pos in
  let es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ante = Solver.normalize_formula_w_coers !cprog es ante !cprog.C.prog_left_coercions in
  let _ = if (!Globals.print_core) then print_endline ("INPUT: \n ### ante = " ^ (Cprinter.string_of_formula ante)) else () in
  let _ = Debug.devel_zprint (lazy ("\nrun_entail_check: after normalization"
                        ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                        ^"\n\n")) no_pos in
  (* let rec check_sat_or f= *)
  (*   match f with *)
  (*     | CF.Base _ *)
  (*     | CF.Exists _ -> Solver.verify_pre_is_sat !cprog f *)
  (*     | CF.Or { CF.formula_or_f1 = f1; *)
  (*               CF.formula_or_f2 = f2; } -> (check_sat_or f1) or (check_sat_or f2) *)
  (* in *)
   (* if (\* (check_sat_or ante) *\) (Solver.verify_pre_is_sat !cprog ante) then 1 else 0 *)
  NEG.check_sat !cprog ante

let run_sat_check (iante0 : meta_formula) =
  let pr = string_of_meta_formula in
  let pr_2 = string_of_int in
  Debug.no_1 "run_sat_check" pr pr_2 run_sat_check iante0


let print_entail_result ante (valid: bool) (residue: CF.list_context) (num_id: string) =
  DD.ninfo_hprint (add_str "residue: " !CF.print_list_context) residue no_pos;
  (* Termination: SLEEK result printing *)
  let term_res = CF.collect_term_ann_and_msg_list_context residue in
  let t_valid = not (List.for_all (fun (b,_) -> b) term_res) in
  let term_output = 
    if t_valid then ""
    else
      snd (List.fold_left (fun (no,a) (b,m) ->
        if b then (no+1, a ^ "<" ^ (string_of_int no) ^ ">:" ^ m ^ "\n")
        else (no+1, a)) (1,"") term_res)
  in
  if not valid then
    begin
      let s =
        if not !Globals.disable_failure_explaining then
          match CF.get_must_failure residue with
            | Some s ->
                let sat = if !Globals.check_sat then
                      (match NEG.check_sat !cprog ante with
                        | 1 -> "sat"
                        | 0 -> "bot"
                        | _ -> "unknown"
                      )
                    else ""
                in
                ("(must: " ^ sat ^ ") cause:"^s)
            | _ -> (match CF.get_may_failure residue with
                | Some s -> "(may) cause:"^s
                | None -> "INCONSISTENCY : expected failure but success instead"
              )
        (*should check bot with is_bot_status*)
        else ""
      in
      print_string (num_id^": Fail."^s^"\n"^term_output^"\n");
          (*if !Globals.print_err_sleek then *)
          (* ;print_string ("printing here: "^(Cprinter.string_of_list_context rs)) *)
    end
  else
    begin
        let s =
        if not !Globals.disable_failure_explaining then
          match CF.list_context_is_eq_flow residue false_flow_int with
            | true -> "(bot)"
            | false -> (*expect normal (OK) here*) ""
        else ""
        in
        if t_valid then print_string (num_id^": Valid. "^s^"\n"^term_output^"\n")
        else print_string (num_id^": Fail. "^s^"\n"^term_output^"\n")
        (* ;print_string ("printing here: "^(Cprinter.string_of_list_context residue)) *)
    end
  (* with e -> *)
  (*     let _ =  Error.process_exct(e)in *)

let print_entail_result ante (valid: bool) (residue: CF.list_context) (num_id: string) =
  let pr0 = string_of_bool in
  let pr = !CF.print_list_context in
  DD.no_2 "print_entail_result" pr0 pr (fun _ -> "") 
    (fun _ _ -> print_entail_result ante valid residue num_id) valid residue


let run_neg_x iform =
  let stab = H.create 103 in
  let _ = if (!Globals.print_input) then print_endline ("INPUT: \n ### f = " ^
 (string_of_meta_formula iform)) else () in
  let _ = Debug.devel_pprint ("\nrun neg:"
                              ^ "\n ### f = "^(string_of_meta_formula iform)
                              ^"\n\n") no_pos in
  let form = meta_to_formula iform false [] stab in
  let form = Solver.prune_preds !cprog true form in
  let fvs = CF.fv form in
  (* let ivars_fvs = List.map (fun n -> CP.SpecVar (UNK,n,Unprimed)) ivars in *)
  (* let _ = print_endline ("ivars"^(Cprinter.string_of_spec_var_list ivars_fvs)) in *)
  (* let _ = print_endline ("ante vars"^(Cprinter.string_of_spec_var_list fvs)) in *)
  let fv_idents = (List.map CP.name_of_spec_var fvs) in
  (* need to make ivars be global *)
  NEG.neg_formula !cprog form

let run_neg iform =
Debug.no_1 "run_neg" string_of_meta_formula Cprinter.string_of_formula
    (fun _ ->  run_neg_x iform) iform

let process_neg iform =
  let neg_f = run_neg iform in
  (* let _ = print_endline ("neg:"^(Cprinter.string_of_formula neg_f)) in *)
  ()

let print_exc (check_id: string) =
  Printexc.print_backtrace stdout;
  dummy_exception() ; 
  print_string ("exception caught " ^ check_id ^ " check\n")

let process_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let nn = "("^(string_of_int (sleek_proof_counter#inc_and_get))^") " in
  let num_id = "\nEntail "^nn in
  try 
    let valid, rs,ante = run_entail_check iante0 iconseq0 in
    print_entail_result ante valid rs num_id
  with ex -> 
         let _ = print_string ("\nEntailment Failure "^nn^(Printexc.to_string ex)^"\n") 
         in ()
  (* with e -> print_exc num_id *)

let process_pinfer_x p_univ0 ph0=
  let _ = residues := None in
  let stab = H.create 103 in
  let pred_univ = meta_to_formula  p_univ0 false [] stab in
  let pred_univ = Solver.prune_preds !cprog true pred_univ in
  let pd = meta_to_formula  ph0 false [] stab in
  let pd = Solver.prune_preds !cprog true pd in

  let h_u, mf_u,_,_,_ = CF.split_components pred_univ in
  (* let p_u = Mcpure.pure_of_mix mf_u in *)
  let h, mf,_,_,_ = CF.split_components pd in
  (* let p = Mcpure.pure_of_mix mf in *)
  (match h_u,h with
    | CF.ViewNode hv_u , CF.ViewNode hv->
        let _ = DD.devel_pprint "heap: View" no_pos in
        let vd_u = C.look_up_view_def_raw !cprog.C.prog_view_decls hv_u.CF.h_formula_view_name in
        let vd = C.look_up_view_def_raw !cprog.C.prog_view_decls hv.CF.h_formula_view_name in
        let _ = Inferp.synthesize_neg_view_def vd_u vd in
        print_endline "process_pinfer"
    | _ -> print_endline "process_pinfer: not process"
  )

let process_pinfer puniv ph=
 let pr = string_of_meta_formula in
  let pr_2 = (fun _ -> "out") in
  Debug.no_2 "process_pinfer" pr pr pr_2 process_pinfer_x puniv ph

let process_sat_check (iante0 : meta_formula) =
  let nn = "("^(string_of_int (sleek_proof_counter#inc_and_get))^") " in
  let num_id = "\nsat "^nn in
  try 
    let res = run_sat_check iante0 in
    let sat =
    match res with
      | 0 -> "unsat"
      | 1 -> "sat"
      | _ -> "unknown"
    in
    print_endline (num_id ^": " ^ sat)
  with ex -> 
         let _ = print_string ("\nEntailment Failure "^nn^(Printexc.to_string ex)^"\n") 
         in ()
  (* with e -> print_exc num_id *)


let process_infer (ivars: ident list) (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let nn = "("^(string_of_int (sleek_proof_counter#inc_and_get))^") " in
  let num_id = "\nEntail "^nn in
  try 
    let valid, rs, ante = run_infer_one_pass ivars iante0 iconseq0 in
    print_entail_result ante valid rs num_id
  with ex -> 
      (* print_exc num_id *)
         let _ = print_string ("\nEntailment Failure "^nn^(Printexc.to_string ex)^"\n") 
         in ()

let process_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let pr = string_of_meta_formula in
  Debug.no_2 "process_entail_check" pr pr (fun _ -> "?") process_entail_check iante0 iconseq0

let process_capture_residue (lvar : ident) = 
	let flist = match !residues with 
      | None -> [(CF.mkTrue (CF.mkTrueFlow()) no_pos)]
      | Some (ls_ctx, print) -> CF.list_formula_of_list_context ls_ctx in
		put_var lvar (Sleekcommons.MetaFormLCF flist)

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
        (* | Some s -> print_string ((Cprinter.string_of_list_formula  *)
        (*       (CF.list_formula_of_list_context s))^"\n") *)
        (*print all posible outcomes and their traces with numbering*)
        | Some (ls_ctx, print) ->
            if (print) then 
              print_string ((Cprinter.string_of_numbered_list_formula_trace
                               (CF.list_formula_trace_of_list_context ls_ctx))^"\n" );
	  else
			print_string ("unsupported print command: " ^ pcmd)

let get_residue () = !residues

let get_residue () =
  Debug.no_1 "get_residue" pr_no (pr_opt pr_no) get_residue ()
  (*match !residues with*)
    (*| None -> ""*)
    (*| Some s -> Cprinter.string_of_list_formula (CF.list_formula_of_list_context s)*)


