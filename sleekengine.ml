(*
  The frontend engine of SLEEK.
*)

open Globals
open Wrapper
open Others
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
module CEQ = Checkeq
module TI = Typeinfer
module SAU = Sautility
module SAC = Sacore
module MCP = Mcpure

let sleek_proof_counter = new Gen.counter 0

(*
  Global data structures. If we want to support push/pop commands,
  we'll need to make them into a stack of scopes.
*)
let iobj_def =  {I.data_name = "Object";
I.data_fields = [];
I.data_pos = no_pos;
I.data_parent_name = "";
I.data_invs = []; (* F.mkTrue no_pos; *)
I.data_is_template = false;
I.data_methods = [] }

let iprog = { I.prog_include_decls =[];
I.prog_data_decls = [iobj_def];
I.prog_global_var_decls = [];
I.prog_logical_var_decls = [];
I.prog_enum_decls = [];
I.prog_view_decls = [];
I.prog_func_decls = [];
I.prog_rel_decls = [];
I.prog_rel_ids = [];
I.prog_hp_decls = [];
I.prog_hp_ids = [];
I.prog_axiom_decls = []; (* [4/10/2011] An Hoa *)
I.prog_proc_decls = [];
I.prog_coercion_decls = [];
I.prog_hopred_decls = [];
I. prog_barrier_decls = [];
}

let cobj_def = { C.data_name = "Object";
				 C.data_fields = [];
				 C.data_pos = no_pos;
				 C.data_parent_name = "";
				 C.data_invs = [];
				 C.data_methods = [] }

let cprog = ref { 
    C.prog_data_decls = [];
    C.prog_view_decls = [];
    C.prog_logical_vars = [];
    (*	C.prog_func_decls = [];*)
    C.prog_rel_decls = []; (* An Hoa *)
    C.prog_hp_decls = [];
    C.prog_axiom_decls = []; (* [4/10/2011] An Hoa *)
    (*C.old_proc_decls = [];*)
    C.new_proc_decls = Hashtbl.create 1; (* no need for proc *)
    (*C.prog_left_coercions = [];
    C.prog_right_coercions = [];*)
    C. prog_barrier_decls = []}
	
let _ = 
	Lem_store.all_lemma # clear_right_coercion;
	Lem_store.all_lemma # clear_left_coercion

let residues =  ref (None : (CF.list_context * bool) option)    (* parameter 'bool' is used for printing *)

let sleek_hprel_assumes = ref ([]: CF.hprel list)
let sleek_hprel_defns = ref ([]: (CF.cond_path_type * CF.hp_rel_def) list)

let sleek_hprel_unknown = ref ([]: (CF.cond_path_type * (CP.spec_var * CP.spec_var list)) list)
let sleek_hprel_dang = ref ([]: (CP.spec_var *CP.spec_var list) list)

let clear_iprog () =
  iprog.I.prog_data_decls <- [iobj_def];
  iprog.I.prog_view_decls <- [];
  iprog.I.prog_rel_decls <- [];
  iprog.I.prog_hp_decls <- [];
  iprog.I.prog_coercion_decls <- []

let clear_cprog () =
  !cprog.C.prog_data_decls <- [];
  !cprog.C.prog_view_decls <- [];
  !cprog.C.prog_rel_decls <- [];
  !cprog.C.prog_hp_decls <- [];
  (*!cprog.C.prog_left_coercions <- [];*)
  (*!cprog.C.prog_right_coercions <- []*)
  Lem_store.all_lemma # clear_right_coercion;
  Lem_store.all_lemma # clear_left_coercion

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
		  let _ = I.look_up_view_def_raw 3 iprog.I.prog_view_decls name in
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
			        		  | Not_found ->
                                begin
					                try
			        		            let _ = I.look_up_hp_def_raw iprog.I.prog_hp_decls name in
						                false
					                with
			        		          | Not_found -> true
		        	            end
		        	    end
		  	    end
	end

let check_data_pred_name name :bool =
  let pr1 x = x in
  let pr2 = string_of_bool in
  Debug.no_1 "check_data_pred_name" pr1 pr2 (fun _ -> check_data_pred_name name) name

let silenced_print f s = if !Globals.silence_output then () else f s 

let process_pred_def pdef = 
  (* TODO : how come this method not called? *)
  (* let _ = print_string ("process_pred_def:" *)
  (*                       ^ "\n\n") in *)
  if check_data_pred_name pdef.I.view_name then
    let curr_view_decls = iprog.I.prog_view_decls in
	(* let tmp = iprog.I.prog_view_decls in *)
	  try
		let h = (self,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in
		let p = (self,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in
		iprog.I.prog_view_decls <- pdef :: curr_view_decls;
		let wf = AS.case_normalize_struc_formula_view 10 iprog h p pdef.Iast.view_formula false 
          false (*allow_post_vars*) false [] in
		let new_pdef = {pdef with Iast.view_formula = wf} in
		let tmp_views = AS.order_views (new_pdef :: iprog.I.prog_view_decls) in
		iprog.I.prog_view_decls <- List.rev tmp_views;
(* ( new_pdef :: iprog.I.prog_view_decls); *)
		(*let _ = print_string ("\n------ "^(Iprinter.string_of_struc_formula "\t" pdef.Iast.view_formula)^"\n normalized:"^(Iprinter.string_of_struc_formula "\t" wf)^"\n") in*)
		let cpdef = AS.trans_view iprog [] new_pdef in 
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
		let _ = if (!Globals.print_core || !Globals.print_core_all) then print_string (Cprinter.string_of_view_decl n_cpdef ^"\n") else () in
		!cprog.C.prog_view_decls <- (n_cpdef :: old_vdec)
		(*print_string ("\npred def: "^(Cprinter.string_of_view_decl cpdef)^"\n")*)
(* added 07.04.2008	*)									  
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_view_decls <- curr_view_decls
  else
	(* print_string (pdef.I.view_name ^ " is already defined.\n") *)
	report_error pdef.I.view_pos (pdef.I.view_name ^ " is already defined.")

let process_pred_def pdef = 
  let pr = Iprinter.string_of_view_decl in
  Debug.no_1 "process_pred_def" pr pr_no process_pred_def pdef

(* WN : why are there two versions of process_pred_def ? *)
let process_pred_def_4_iast pdef = 
  if check_data_pred_name pdef.I.view_name then
    let curr_view_decls = iprog.I.prog_view_decls in
    iprog.I.prog_view_decls <- pdef :: curr_view_decls;
  else
    report_error pdef.I.view_pos (pdef.I.view_name ^ " is already defined.")

let process_pred_def_4_iast pdef = 
  let pr = Iprinter.string_of_view_decl in
  Debug.no_1 "process_pred_def_4_iast" pr pr_no process_pred_def_4_iast pdef

(*should call AS.convert_pred_to_cast
it seems that the following method is no longer used.
It is replaced by convert_data_and_pred_to_cast
*)
let convert_pred_to_cast () = 
  let infer_views = if (!Globals.infer_mem) 
    then List.map (fun c -> Mem.infer_mem_specs c iprog) iprog.I.prog_view_decls 
    else iprog.I.prog_view_decls in 
  iprog.I.prog_view_decls <- infer_views; 
  let tmp_views = (AS.order_views (iprog.I.prog_view_decls)) in
  Debug.tinfo_pprint "after order_views" no_pos;
  let _ = Iast.set_check_fixpt iprog.I.prog_data_decls tmp_views in
  Debug.tinfo_pprint "after check_fixpt" no_pos;
  iprog.I.prog_view_decls <- tmp_views;
  let cviews = List.map (AS.trans_view iprog []) tmp_views in
  Debug.tinfo_pprint "after trans_view" no_pos;
  let cviews =
    if !Globals.pred_elim_useless then
      Norm.norm_elim_useless cviews (List.map (fun vdef -> vdef.C.view_name) cviews)
    else cviews
  in
  let _ = !cprog.C.prog_view_decls <- cviews in
  let cviews1 =
    if !Globals.norm_extract then
      Norm.norm_extract_common !cprog cviews (List.map (fun vdef -> vdef.C.view_name) cviews)
    else cviews
  in
  let cviews2 =
    if !Globals.norm_cont_analysis then
      Norm.cont_para_analysis !cprog cviews1
    else
      cviews1
  in
  let _ = !cprog.C.prog_view_decls <- cviews2 in
  let _ =  (List.map (fun vdef -> AS.compute_view_x_formula !cprog vdef !Globals.n_xpure) cviews2) in
  Debug.tinfo_pprint "after compute_view" no_pos;
  let _ = (List.map (fun vdef -> AS.set_materialized_prop vdef) !cprog.C.prog_view_decls) in
  Debug.tinfo_pprint "after materialzed_prop" no_pos;
  let cprog1 = AS.fill_base_case !cprog in
  let cprog2 = AS.sat_warnings cprog1 in        
  let cprog3 = if (!Globals.enable_case_inference or (not !Globals.dis_ps)(* !Globals.allow_pred_spec *)) 
    then AS.pred_prune_inference cprog2 else cprog2 in
  let cprog4 = (AS.add_pre_to_cprog cprog3) in
  let cprog5 = (*if !Globals.enable_case_inference then AS.case_inference iprog cprog4 else*) cprog4 in
  let _ = if (!Globals.print_input || !Globals.print_input_all) then print_string (Iprinter.string_of_program iprog) else () in
  let _ = if (!Globals.print_core || !Globals.print_core_all) then print_string (Cprinter.string_of_program cprog5) else () in
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
		let wf,_ = AS.case_normalize_struc_formulas iprog h p rdef.Iast.view_formula false false [] in
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
		let _ = if !Globals.print_core || !Globals.print_core_all then print_string (Cprinter.string_of_view_decl n_crdef ^"\n") else () in
		cprog.C.prog_view_decls <- (n_crdef :: old_vdec) *)
			iprog.I.prog_rel_decls <- ( rdef :: iprog.I.prog_rel_decls);
			let crdef = AS.trans_rel iprog rdef in !cprog.C.prog_rel_decls <- (crdef :: !cprog.C.prog_rel_decls);
			(* Forward the relation to the smt solver. *)
			Smtsolver.add_relation crdef.C.rel_name crdef.C.rel_vars crdef.C.rel_formula;
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_rel_decls <- tmp
  else
		print_string (rdef.I.rel_name ^ " is already defined.\n")

let process_hp_def hpdef =
  let _ = print_string (hpdef.I.hp_name ^ " is defined.\n") in
  if check_data_pred_name hpdef.I.hp_name then
	let tmp = iprog.I.prog_hp_decls in
	  try
            (* PURE_RELATION_OF_HEAP_PRED *)
            (* are these a newly added hp_pred? *)
            iprog.I.prog_hp_decls <- ( hpdef :: iprog.I.prog_hp_decls);
	      let chpdef, p_chpdef = AS.trans_hp iprog hpdef in
              let _ = !cprog.C.prog_hp_decls <- (chpdef :: !cprog.C.prog_hp_decls) in
              let _ = !cprog.C.prog_rel_decls <- (p_chpdef::!cprog.C.prog_rel_decls) in
	      (* Forward the relation to the smt solver. *)
              let args = fst (List.split chpdef.C.hp_vars_inst) in
	      Smtsolver.add_hp_relation chpdef.C.hp_name args chpdef.C.hp_formula;
	  with
	    | _ ->  
                  begin
                  dummy_exception() ; 
                    (* why do we perform restoration here? *)
                  iprog.I.prog_hp_decls <- tmp
                  end
  else
	print_string (hpdef.I.hp_name ^ " is already defined.\n")

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
  let _ = if (!Globals.print_input || !Globals.print_input_all) then print_string (Iprinter.string_of_coerc_decl ldef) in
  let _ = if (!Globals.print_core || !Globals.print_core_all) then 
    print_string ("\nleft:\n " ^ (Cprinter.string_of_coerc_decl_list l2r) ^"\n right:\n"^ (Cprinter.string_of_coerc_decl_list r2l) ^"\n") else () in
  (* WN_all_lemma - should we remove the cprog updating *)
  let _ = Lem_store.all_lemma # add_left_coercion l2r in 
  let _ = Lem_store.all_lemma # add_right_coercion r2l in 
  (*!cprog.C.prog_left_coercions <- l2r @ !cprog.C.prog_left_coercions;*)
  (*!cprog.C.prog_right_coercions <- r2l @ !cprog.C.prog_right_coercions;*)
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
  if check_data_pred_name ddef.I.data_name then
    let tmp = iprog.I.prog_data_decls in
    iprog.I.prog_data_decls <- ddef :: iprog.I.prog_data_decls;
  else begin
    dummy_exception() ;
    (* print_string (ddef.I.data_name ^ " is already defined.\n") *)
	report_error ddef.I.data_pos (ddef.I.data_name ^ " is already defined.")
  end

let process_data_def ddef =
  Debug.no_1 "process_data_def" pr_no pr_no process_data_def ddef 

(*L2: should call convert_pred_to_cast*)
let convert_data_and_pred_to_cast_x () =
  (* convert data *)
  List.iter (fun ddef ->
    let cddef = AS.trans_data iprog ddef in
    !cprog.C.prog_data_decls <- cddef :: !cprog.C.prog_data_decls;
    if !perm=NoPerm || not !enable_split_lemma_gen then () 
    else (process_lemma (Iast.gen_normalize_lemma_split ddef);process_lemma (Iast.gen_normalize_lemma_comb ddef))
  ) iprog.I.prog_data_decls;

  (* convert pred *)
  let tmp_views = List.map (fun pdef ->
    let h = (self,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in
    let p = (self,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in
    let wf = AS.case_normalize_struc_formula_view 11 iprog h p pdef.Iast.view_formula false false false [] in
    let inv_lock = pdef.I.view_inv_lock in
    let inv_lock = (
      match inv_lock with
      | None -> None
      | Some f ->
          let new_f = AS.case_normalize_formula iprog h f None in (*TO CHECK: h or p*)
          Some new_f
    ) in
    let new_pdef = {pdef with Iast.view_formula = wf;Iast.view_inv_lock = inv_lock} in
    new_pdef
  ) iprog.I.prog_view_decls in
  let tmp_views = (AS.order_views tmp_views) in
  Debug.tinfo_pprint "after order_views" no_pos;
  let _ = Iast.set_check_fixpt iprog.I.prog_data_decls tmp_views in
  Debug.tinfo_pprint "after check_fixpt" no_pos;
  iprog.I.prog_view_decls <- tmp_views;
  let cviews = List.map (AS.trans_view iprog []) tmp_views in
  Debug.tinfo_pprint "after trans_view" no_pos;
  let cviews =
    if !Globals.pred_elim_useless then
      Norm.norm_elim_useless cviews (List.map (fun vdef -> vdef.C.view_name) cviews)
    else cviews
  in
  let _ = !cprog.C.prog_view_decls <- cviews in
  let cviews1 =
    if !Globals.norm_extract then
      Norm.norm_extract_common !cprog cviews (List.map (fun vdef -> vdef.C.view_name) cviews)
    else cviews
  in
  let cviews2 =
    if !Globals.norm_cont_analysis then
      Norm.cont_para_analysis !cprog cviews1
    else
      cviews1
  in
  let _ = !cprog.C.prog_view_decls <- cviews2 in
  let _ =  (List.map (fun vdef -> AS.compute_view_x_formula !cprog vdef !Globals.n_xpure) cviews2) in
  Debug.tinfo_pprint "after compute_view" no_pos;
  let _ = (List.map (fun vdef -> AS.set_materialized_prop vdef) cviews2) in
  Debug.tinfo_pprint "after materialzed_prop" no_pos;
  let cprog1 = AS.fill_base_case !cprog in
  let cprog2 = AS.sat_warnings cprog1 in        
  let cprog3 = if (!Globals.enable_case_inference or (not !Globals.dis_ps)(* !Globals.allow_pred_spec *)) 
    then AS.pred_prune_inference cprog2 else cprog2 in
  let cprog4 = (AS.add_pre_to_cprog cprog3) in
  let cprog5 = (*if !Globals.enable_case_inference then AS.case_inference iprog cprog4 else*) cprog4 in
  let _ = if (!Globals.print_input || !Globals.print_input_all) then print_string (Iprinter.string_of_program iprog) else () in
  let _ = if (!Globals.print_core || !Globals.print_core_all) then print_string (Cprinter.string_of_program cprog5) else () in
  cprog := cprog5

let convert_data_and_pred_to_cast () = 
  Debug.no_1 "convert_data_and_pred_to_cast" pr_no pr_no convert_data_and_pred_to_cast_x ()

let process_barrier_def bd = 
    if !Globals.print_core || !Globals.print_core_all then print_string (Iprinter.string_of_barrier_decl bd) else () ;
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

(** An Hoa : Second stage of parsing : iprog already contains the whole input.
             We do a reparse in order to distinguish between data & enum that
             is deferred in case of mutually dependent data definition.
 **)
let perform_second_parsing_stage () =
	let cddefs = List.map (AS.trans_data iprog) iprog.I.prog_data_decls in
		!cprog.C.prog_data_decls <- cddefs
	
let rec meta_to_struc_formula (mf0 : meta_formula) quant fv_idents (rel0: rel option) (tlist:TI.spec_var_type_list) 
	: (TI.spec_var_type_list*CF.struc_formula) = 
  let rec helper (mf0 : meta_formula) quant fv_idents tl : (TI.spec_var_type_list*CF.struc_formula) = 
    match mf0 with
    | MetaFormCF mf -> 
        (tl,(Cformula.formula_to_struc_formula mf))
    | MetaFormLCF mf -> 
        (tl,(Cformula.formula_to_struc_formula (List.hd mf)))
    | MetaForm mf -> 
        let h = List.map (fun c-> (c,Unprimed)) fv_idents in
        let p = List.map (fun c-> (c,Primed)) fv_idents in
        let wf,_ = AS.case_normalize_struc_formula 12 iprog h p (Iformula.formula_to_struc_formula mf) true 
          true (*allow_post_vars*) true [] in
        AS.trans_I2C_struc_formula 8 iprog quant fv_idents wf tl false (*(Cpure.Prim Void) []*) false (*check_pre*) 
    | MetaVar mvar -> 
        begin
        try 
          let mf = get_var mvar in
            helper mf quant fv_idents tl
        with
          | Not_found ->
            dummy_exception() ;
            print_string (mvar ^ " is undefined.\n");
            raise SLEEK_Exception
        end
    | MetaCompose (vs, mf1, mf2) -> 
        begin
        let (n_tl,cf1) = helper mf1 quant fv_idents tl in
        let (n_tl,cf2) = helper mf2 quant fv_idents n_tl in
        let svs = List.map (fun v -> TI.get_spec_var_type_list v n_tl no_pos) vs in
        let res = Solver.compose_struc_formula cf1 cf2 svs no_pos in
        (n_tl,res)
      end
  | MetaEForm b -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let p = List.map (fun c-> (c,Primed)) fv_idents in
      let wf,_ = AS.case_normalize_struc_formula 13 iprog h p b true (* allow_primes *) 
        true (*allow_post_vars*) true [] in
      let (n_tl,res) = AS.trans_I2C_struc_formula 9 iprog quant fv_idents wf tl false 
        false (*check_pre*) (*(Cpure.Prim Void) [] *) in
      (* let _ = print_string ("\n1 before meta: " ^(Iprinter.string_of_struc_formula b)^"\n") in *)
      (* let _ = print_string ("\n2 before meta: " ^(Iprinter.string_of_struc_formula wf)^"\n") in *)
      (*let _ = print_string ("\n after meta: " ^ (Cprinter.string_of_struc_formula res)) in*)
      (n_tl,res)
  | MetaEFormCF b ->       (* let _ = print_string ("\n (andreeac) meta_to_struc_formula 6") in *) (tl,b) (* assume it has already been normalized *)
  in helper mf0 quant fv_idents tlist 


let meta_to_struc_formula (mf0 : meta_formula) quant fv_idents (rel0: rel option) (tlist:TI.spec_var_type_list) 
	: (TI.spec_var_type_list*CF.struc_formula) 
	= Debug.no_4 "meta_to_struc_formula"
  string_of_meta_formula
  string_of_bool
  string_of_ident_list
  TI.string_of_tlist
  (pr_pair pr_none Cprinter.string_of_struc_formula)
  (fun _ _ _ _  ->  meta_to_struc_formula mf0 quant fv_idents rel0 tlist )mf0 quant fv_idents tlist

(* An Hoa : DETECT THAT EITHER OF 
AS.case_normalize_formula iprog h mf
AS.collect_type_info_formula iprog wf stab false
AS.trans_formula iprog quant
IN THE FUNCTION GIVE AN EXCEPTION
TODO Check the 3 functions above!!!
*)
let rec meta_to_formula (mf0 : meta_formula) quant fv_idents (tlist:TI.spec_var_type_list) 
  : (TI.spec_var_type_list*CF.formula) = 
	match mf0 with
  | MetaFormCF mf -> (tlist,mf)
  | MetaFormLCF mf ->	(tlist,(List.hd mf))
  | MetaForm mf -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      (* let _ = print_string (" before norm: " ^(Iprinter.string_of_formula mf)^"\n") in *)
      let wf = AS.case_normalize_formula iprog h mf None in
      let n_tl = TI.gather_type_info_formula iprog wf tlist false in
      let (n_tl,r) = AS.trans_formula iprog quant fv_idents false wf n_tl false in
      (* let _ = print_string (" before sf: " ^(Iprinter.string_of_formula wf)^"\n") in *)
      (* let _ = print_string (" after sf: " ^(Cprinter.string_of_formula r)^"\n") in *)
      (n_tl,r)
  | MetaVar mvar -> begin
      try 
				let mf = get_var mvar in
	  			meta_to_formula mf quant fv_idents tlist
      with
			| Not_found ->
	    	dummy_exception() ;
	    	print_string (mvar ^ " is undefined.\n");
	    	raise SLEEK_Exception
    	end
  | MetaCompose (vs, mf1, mf2) -> begin
      let (n_tl,cf1) = meta_to_formula mf1 quant fv_idents tlist in
      let (n_tl,cf2) = meta_to_formula mf2 quant fv_idents n_tl in
      let svs = List.map (fun v -> TI.get_spec_var_type_list v n_tl no_pos) vs in
      let res = Cformula.compose_formula cf1 cf2 svs Cformula.Flow_combine no_pos in
			(n_tl,res)
    end
  | MetaEForm _ | MetaEFormCF _ -> report_error no_pos ("cannot have structured formula in antecedent")

let meta_to_formula (mf0 : meta_formula) quant fv_idents (tlist:TI.spec_var_type_list) : (TI.spec_var_type_list*CF.formula) = 
  let pr_meta = string_of_meta_formula in
  let pr_f = Cprinter.string_of_formula in
  Debug.no_1 "Sleekengine.meta_to_formual" pr_meta pr_none
             (fun mf -> meta_to_formula mf quant fv_idents tlist) mf0

let rec meta_to_formula_not_rename (mf0 : meta_formula) quant fv_idents (tlist:TI.spec_var_type_list)
	: (TI.spec_var_type_list*CF.formula) = 
	match mf0 with
  | MetaFormCF mf -> (tlist,mf)
  | MetaFormLCF mf -> (tlist,(List.hd mf))
  | MetaForm mf ->
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let wf = AS.case_normalize_formula_not_rename iprog h mf in
     
      let n_tl = TI.gather_type_info_formula iprog wf tlist false in
      (*let _ = print_endline ("WF: " ^ Iprinter.string_of_formula wf ) in *)
      let (n_tl,r) = AS.trans_formula iprog quant fv_idents false wf n_tl false in
      (* let _ = print_string (" before sf: " ^(Iprinter.string_of_formula wf)^"\n") in *)
      (* let _ = print_string (" after sf: " ^(Cprinter.string_of_formula r)^"\n") in *)
      (n_tl,r)
  | MetaVar mvar -> begin
      try 
				let mf = get_var mvar in
	  			meta_to_formula_not_rename mf quant fv_idents tlist
      with
			| Not_found ->
	    	dummy_exception() ;
	    	print_string (mvar ^ " is undefined.\n");
	    	raise SLEEK_Exception
    	end
  | MetaCompose (vs, mf1, mf2) -> begin
      let (n_tl,cf1) = meta_to_formula_not_rename mf1 quant fv_idents tlist in
      let (n_tl,cf2) = meta_to_formula_not_rename mf2 quant fv_idents n_tl in
      let svs = List.map (fun v -> TI.get_spec_var_type_list v n_tl no_pos) vs in
      let res = Cformula.compose_formula cf1 cf2 svs Cformula.Flow_combine no_pos in
			(n_tl,res)
    end
  | MetaEForm _ | MetaEFormCF _ -> report_error no_pos ("cannot have structured formula in antecedent")

let run_simplify (iante0 : meta_formula) =
  let (n_tl,ante) = meta_to_formula iante0 false [] [] in
  let ante = Solver.prune_preds !cprog true ante in
  let ante =
    if (Perm.allow_perm ()) then
      (*add default full permission to ante;
        need to add type of full perm to stab *)
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  let (h,p,_,_,_) = CF.split_components ante in
  let pf = MCP.pure_of_mix p in
  (* print_endline "calling tp_dispatcher?"; *)
  let r = Tpdispatcher.simplify_tp pf in
  r

let run_hull (iante0 : meta_formula) = 
  let (n_tl,ante) = meta_to_formula iante0 false [] [] in
  let ante = Solver.prune_preds !cprog true ante in
  let ante =
    if (Perm.allow_perm ()) then
      (*add default full permission to ante;
        need to add type of full perm to stab *)
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  let (h,p,_,_,_) = CF.split_components ante in
  let pf = MCP.pure_of_mix p in
  (* print_endline "calling tp_dispatcher?"; *)
  let r = Tpdispatcher.hull pf in
  r


let run_pairwise (iante0 : meta_formula) = 
  let (n_tl,ante) = meta_to_formula iante0 false [] [] in
  let ante = Solver.prune_preds !cprog true ante in
  let ante =
    if (Perm.allow_perm ()) then
      (*add default full permission to ante;
        need to add type of full perm to stab *)
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  let (h,p,_,_,_) = CF.split_components ante in
  let pf = MCP.pure_of_mix p in
  (* print_endline "calling tp_dispatcher?"; *)
  let r = Tpdispatcher.tp_pairwisecheck pf in
  r

let run_infer_one_pass (ivars: ident list) (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let _ = residues := None in
  let _ = Infer.rel_ass_stk # reset in
  let _ = Sa2.rel_def_stk # reset in
  let _ = if (!Globals.print_input || !Globals.print_input_all) then print_endline ("INPUT: \n ### 1 ante = " ^ (string_of_meta_formula iante0) ^"\n ### conseq = " ^ (string_of_meta_formula iconseq0)) else () in
  let _ = Debug.devel_pprint ("\nrun_entail_check 1:"
                              ^ "\n ### iante0 = "^(string_of_meta_formula iante0)
                              ^ "\n ### iconseq0 = "^(string_of_meta_formula iconseq0)
                              ^"\n\n") no_pos in
  let (n_tl,ante) = meta_to_formula iante0 false [] [] in
  (*let ante = Solver.normalize_formula_w_coers !cprog (CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos) ante !cprog.C.prog_left_coercions in*)
  let ante = Solver.prune_preds !cprog true ante in
  let ante = (*important for permissions*)
    if (Perm.allow_perm ()) then
      (*add default full permission to ante;
        need to add type of full perm to stab *)
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  (* let ante = AS.add_param_ann_constraints_formula ante in *)
  let vk = TI.fresh_proc_var_kind n_tl Float in
  let n_tl = TI.type_list_add  (full_perm_name ()) vk n_tl in
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
  (* let conseq = if (!Globals.allow_field_ann) then meta_to_struc_formula iconseq0 false fv_idents None stab  *)
  let (n_tl,conseq) =
    if (!Globals.allow_field_ann) 
    then meta_to_struc_formula iconseq0 false fv_idents (Some Globals.RSubAnn) n_tl
    else meta_to_struc_formula iconseq0 false fv_idents None n_tl in
  (* let _ = print_endline ("conseq: " ^ (Cprinter.string_of_struc_formula conseq)) in *)
  (* let conseq1 = meta_to_struc_formula iconseq0 false fv_idents stab in *)
  let pr = Cprinter.string_of_struc_formula in
  let _ = DD.tinfo_hprint (add_str "conseq(after meta-)" pr) conseq no_pos in 
  let conseq = Solver.prune_pred_struc !cprog true conseq in
  let _ = DD.tinfo_hprint (add_str "conseq(after prune)" pr) conseq no_pos in 
  (* let _ = DD.info_pprint "Andreea : false introduced by add_param_ann_constraints_struc" no_pos in *)
  (* let _ = DD.info_pprint "=============================================================" no_pos in *)
  let conseq = AS.add_param_ann_constraints_struc conseq in
  let _ = DD.tinfo_hprint (add_str "conseq(after add param)" pr) conseq no_pos in 
  (* let conseq = AS.add_param_ann_constraints_struc conseq in  *)
  let _ = Debug.devel_zprint (lazy ("\nrun_entail_check 2:"
                        ^"\n ### ivars = "^(pr_list pr_id ivars)
                        ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                        ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq)
                        ^"\n\n")) no_pos in
  let es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let left_co = Lem_store.all_lemma # get_left_coercion in
  let ante = Solver.normalize_formula_w_coers 11 !cprog es ante left_co (* !cprog.C.prog_left_coercions *) in
  let _ = if (!Globals.print_core || !Globals.print_core_all) then print_endline ("INPUT: \n ### ante = " ^ (Cprinter.string_of_formula ante) ^"\n ### conseq = " ^ (Cprinter.string_of_struc_formula conseq)) else () in
  let _ = Debug.devel_zprint (lazy ("\nrun_entail_check 3: after normalization"
                        ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                        ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq)
                        ^"\n\n")) no_pos in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let ctx = Solver.elim_exists_ctx ctx in
  (* List of vars appearing in original formula *)
  let orig_vars = CF.fv ante @ CF.struc_fv conseq in
  (* List of vars needed for abduction process *)
  let vars = List.map (fun v -> TI.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) ivars in
  (* Init context with infer_vars and orig_vars *)
  let (vrel,iv) = List.partition (fun v -> is_RelT (CP.type_of_spec_var v)(*  ||  *)
              (* CP.type_of_spec_var v == FuncT *)) vars in
  let (v_hp_rel,iv) = List.partition (fun v -> CP.type_of_spec_var v == HpT(*  ||  *)
              (* CP.type_of_spec_var v == FuncT *)) iv in
  (* let _ = print_endline ("WN: vars rel"^(Cprinter.string_of_spec_var_list vrel)) in *)
  (* let _ = print_endline ("WN: vars hp rel"^(Cprinter.string_of_spec_var_list v_hp_rel)) in *)
  (* let _ = print_endline ("WN: vars inf"^(Cprinter.string_of_spec_var_list iv)) in *)
  let ctx = Inf.init_vars ctx iv vrel v_hp_rel orig_vars in
  (* let _ = print_string ((pr_list_ln Cprinter.string_of_view_decl) !cprog.Cast.prog_view_decls)  in *)
  let _ = if !Globals.print_core || !Globals.print_core_all
    then print_string ("\nrun_infer:\n"^(Cprinter.string_of_formula ante)
        ^" "^(pr_list pr_id ivars)
      ^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") 
    else () 
  in
  let ctx = 
    if !Globals.delay_proving_sat then ctx
    else CF.transform_context (Solver.elim_unsat_es 9 !cprog (ref 1)) ctx in
  let _ = if (CF.isAnyFalseCtx ctx) then
        print_endline ("[Warning] False ctx")
  in
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
  (*  let _ = print_endline ("WN# 2:"^(Cprinter.string_of_list_context rs)) in  *)
  (* flush stdout; *)
  let res =
    if not !Globals.disable_failure_explaining then ((not (CF.isFailCtx_gen rs)))
    else ((not (CF.isFailCtx rs))) in
  residues := Some (rs, res);
  (res, rs,v_hp_rel)

let run_infer_one_pass ivars (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let pr = string_of_meta_formula in
  let pr1 = pr_list pr_id in
  let pr_2 = pr_triple string_of_bool Cprinter.string_of_list_context !CP.print_svl in
  let nn = (sleek_proof_counter#get) in
  let f x = wrap_proving_kind (PK_Sleek_Entail nn) (run_infer_one_pass ivars iante0) x in
  Debug.no_3 "run_infer_one_pass" pr1 pr pr pr_2 (fun _ _ _ -> f iconseq0) ivars iante0 iconseq0

let process_rel_assume cond_path (ilhs : meta_formula) (igurad_opt : meta_formula option) (irhs: meta_formula)=
  (* let _ = DD.info_pprint "process_rel_assume" no_pos in *)
  (* let stab = H.create 103 in *)
  let stab = [] in
  let (stab,lhs) = meta_to_formula ilhs false [] stab in
  let fvs = CF.fv lhs in
  let fv_idents = (List.map CP.name_of_spec_var fvs) in
  let (stab,rhs) = meta_to_formula irhs false fv_idents stab in
  let all_vs = fvs@(CF.fv rhs) in
  let fv_idents = (List.map CP.name_of_spec_var all_vs) in
  let guard = match igurad_opt with
    | None -> None
    | Some iguard -> let (_,guard0) = meta_to_formula iguard false fv_idents stab in
      let _, guard = CF.split_quantifiers guard0 in
      (* let _ = Debug.info_pprint (Cprinter.string_of_formula guard) no_pos in *)
      let p = CF.get_pure guard in
      let eq = (Mcpure.ptr_equations_without_null (Mcpure.mix_of_pure p)) in
      let guard1 = CF.subst eq guard in
      (* if CP.isConstTrue p then *)
        let hfs = CF.heap_of guard1 in
        CF.join_star_conjunctions_opt hfs
      (* else report_error no_pos "Sleekengine.process_rel_assume: guard should be heaps only" *)
  in
  let orig_vars = CF.fv lhs @ CF.fv rhs in
  let lhps = CF.get_hp_rel_name_formula lhs in
  let rhps = CF.get_hp_rel_name_formula rhs in
  (* let _ =  print_endline ("LHS = " ^ (Cprinter.string_of_formula lhs)) in *)
  (* let _ =  print_endline ("RHS = " ^ (Cprinter.string_of_formula rhs)) in *)
  (*TODO: LOC: hp_id should be cond_path*)
  (* why not using mkHprel? *)
  let knd = CP.RelAssume (CP.remove_dups_svl (lhps@rhps)) in
  let new_rel_ass = CF.mkHprel_1 knd lhs guard rhs cond_path in
  (*     CF.hprel_kind = CP.RelAssume (CP.remove_dups_svl (lhps@rhps)); *)
  (*     unk_svl = [];(\*inferred from norm*\) *)
  (*     unk_hps = []; *)
  (*     predef_svl = []; *)
  (*     hprel_lhs = lhs; *)
  (*     hprel_guard = guard; *)
  (*     hprel_rhs = rhs; *)
  (*     hprel_path = cond_path; *)
  (*     hprel_proving_kind = Others.proving_kind # top_no_exc; *)
  (* } in *)
  (*hp_assumes*)
  let _ = Debug.ninfo_pprint (Cprinter.string_of_hprel_short new_rel_ass) no_pos in
  let _ = sleek_hprel_assumes := !sleek_hprel_assumes@[new_rel_ass] in
  ()

let process_rel_defn cond_path (ilhs : meta_formula) (irhs: meta_formula)=
  (* let _ = DD.info_pprint "process_rel_assume" no_pos in *)
  (* let stab = H.create 103 in *)
  let stab = [] in
  let (stab,lhs) = meta_to_formula ilhs false [] stab in
  let fvs = CF.fv lhs in
  let fv_idents = (List.map CP.name_of_spec_var fvs) in
  let (stab,rhs) = meta_to_formula irhs false fv_idents stab in
  let hfs = CF.heap_of lhs in
  let hf = match hfs with
    | [x] -> x
    | _ -> report_error no_pos "sleekengine.process_rel_defn: rel defn"
  in
  let hp,args = CF.extract_HRel hf in
  (* let _ =  print_endline ("LHS = " ^ (Cprinter.string_of_formula lhs)) in *)
  (* let _ =  print_endline ("RHS = " ^ (Cprinter.string_of_formula rhs)) in *)
  (*TODO: LOC: hp_id should be cond_path*)
  let pr_new_rel_defn =  (cond_path, (CP.HPRelDefn (hp, List.hd args, List.tl args), hf, None, rhs))
  in
  (*hp_defn*)
  (* let pr= pr_pair CF.string_of_cond_path Cprinter.string_of_hp_rel_def_short in *)
  (* let _ = Debug.ninfo_pprint ((pr pr_new_rel_defn) ^ "\n") no_pos in *)
  let _ =  sleek_hprel_defns := ! sleek_hprel_defns@[pr_new_rel_defn] in
  ()

let process_decl_hpdang hp_names =
  let process hp_name=
    let hp_def = Cast.look_up_hp_def_raw !cprog.Cast.prog_hp_decls hp_name in
    let hp = Cpure.SpecVar (HpT , hp_name, Unprimed) in
    let args = fst (List.split hp_def.Cast.hp_vars_inst) in
    (hp,args)
  in
  let hpargs = List.map process hp_names in
  let _ = Debug.ninfo_pprint ("dangling: " ^
      (let pr = pr_list (pr_pair !Cpure.print_sv !Cpure.print_svl) in pr hpargs)) no_pos in
  let _ = sleek_hprel_dang := !sleek_hprel_dang@hpargs in
  ()

let process_decl_hpunknown (cond_path, hp_names) =
  let process hp_name=
    let hp_def = Cast.look_up_hp_def_raw !cprog.Cast.prog_hp_decls hp_name in
    let hp = Cpure.SpecVar (HpT , hp_name, Unprimed) in
    let args = fst (List.split hp_def.Cast.hp_vars_inst) in
    (cond_path, (hp,args))
  in
  let hpargs = List.map process hp_names in
  let _ = Debug.ninfo_pprint (("unknown: " ^
      (let pr = pr_list (pr_pair CF.string_of_cond_path (pr_pair !Cpure.print_sv !Cpure.print_svl)) in pr hpargs)) ^ "\n") no_pos in
  let _ = sleek_hprel_unknown := !sleek_hprel_unknown@hpargs in
  ()

let shape_infer_pre_process constrs pre_hps post_hps=
  let unk_hpargs = !sleek_hprel_dang in
  let link_hpargs = !sleek_hprel_unknown in
  (*** BEGIN PRE/POST ***)
  let orig_vars = List.fold_left (fun ls cs-> ls@(CF.fv cs.CF.hprel_lhs)@(CF.fv cs.CF.hprel_rhs)) [] !sleek_hprel_assumes in
  let pre_vars = List.map (fun v -> TI.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (pre_hps) in
  let post_vars = List.map (fun v -> TI.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (post_hps) in
  let pre_vars1 = (CP.remove_dups_svl pre_vars) in
  let post_vars1 = (CP.remove_dups_svl post_vars) in
  let infer_pre_vars,pre_hp_rels  = List.partition (fun sv ->
      let t = CP.type_of_spec_var sv in
      not ((* is_RelT t || *) is_HpT t )) pre_vars1 in
  let infer_post_vars,post_hp_rels  = List.partition (fun sv ->
      let t = CP.type_of_spec_var sv in
      not ((* is_RelT t || *) is_HpT t )) post_vars1 in
  (*END*)
  let infer_vars = infer_pre_vars@infer_post_vars in
  let sel_hps = pre_hp_rels@post_hp_rels in
  (* let sel_hps, sel_post_hps = SAU.get_pre_post pre_hps post_hps constrs in *)
  (***END PRE/POST***)
  (* let constrs2, unk_map, unk_hpargs = SAC.detect_dangling_pred hp_lst_assume sel_hps [] in *)
  let constrs2,unk_map = if unk_hpargs = [] then (constrs ,[]) else
    let unk_hps = List.map fst unk_hpargs in
    List.fold_left (fun (ls_cs,map) cs ->
      let new_cs, n_map,_ = SAC.do_elim_unused cs unk_hps map in
      (ls_cs@[new_cs], n_map)
  ) ([], []) constrs
  in
  (constrs2, sel_hps, post_hp_rels, unk_map, unk_hpargs, link_hpargs)

let process_shape_infer pre_hps post_hps=
  (* let _ = DD.info_pprint "process_shape_infer" no_pos in *)
  let hp_lst_assume = !sleek_hprel_assumes in
  let constrs2, sel_hps, sel_post_hps, unk_map, unk_hpargs, link_hpargs=
    shape_infer_pre_process hp_lst_assume pre_hps post_hps
  in
  let ls_hprel, ls_inferred_hps =
    if List.length sel_hps> 0 && List.length hp_lst_assume > 0 then
      let infer_shape_fnc =  if not (!Globals.pred_syn_modular) then
        Sa2.infer_shapes
      else Sa3.infer_shapes (* Sa.infer_hps *)
      in
      infer_shape_fnc iprog !cprog "" constrs2
          sel_hps sel_post_hps unk_map unk_hpargs link_hpargs true false
    else [],[]
  in
  let _ =
    begin
      let rel_defs = if not (!Globals.pred_syn_modular) then
        Sa2.rel_def_stk
      else Sa3.rel_def_stk
      in
      if not(rel_defs# is_empty) then
        let defs = List.sort CF.hpdef_cmp (rel_defs # get_stk) in
        print_endline "";
      print_endline "\n*************************************";
      print_endline "*******relational definition ********";
      print_endline "*************************************";
      (* print_endline (rel_defs # string_of_reverse); *)
       let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
       print_endline (pr1 defs);
      print_endline "*************************************"
    end
  in
  (* let _ = if(!Globals.cp_test || !Globals.cp_prefile) then *)
  (*    CEQ.cp_test !cprog hp_lst_assume ls_inferred_hps sel_hps *)
  (* in *)
  ()
let process_shape_divide pre_hps post_hps=
   (* let _ = DD.info_pprint "process_shape_divide" no_pos in *)
  let hp_lst_assume = !sleek_hprel_assumes in
  let constrs2, sel_hps, sel_post_hps, unk_map, unk_hpargs, link_hpargs=
    shape_infer_pre_process hp_lst_assume pre_hps post_hps
  in
  (* let ls_cond_defs_drops = *)
  (*   if List.length sel_hps> 0 && List.length hp_lst_assume > 0 then *)
  (*     let infer_shape_fnc = Sa2.infer_shapes_divide in *)
  (*     infer_shape_fnc iprog !cprog "" constrs2 [] *)
  (*         sel_hps sel_post_hps unk_map unk_hpargs link_hpargs true false *)
  (*   else [] *)
  (* in *)
  (* let pr_one (cond, hpdefs,_, _, link_hpargs,_)= *)
  (*   begin *)
  (*     if not(List.length hpdefs = 0) then *)
  (*       let pr_path_defs = List.map (fun (_, hf,_,f) -> (cond,(hf,f))) hpdefs in *)
  (*       let pr_path_dangs = List.map (fun (hp,_) -> (cond, hp)) link_hpargs in *)
  (*       print_endline ""; *)
  (*     print_endline "\n*************************************"; *)
  (*     print_endline "*******relational definition ********"; *)
  (*     print_endline "*************************************"; *)
  (*     let _ = List.iter (fun pair -> print_endline (Cprinter.string_of_pair_path_def pair) ) pr_path_defs in *)
  (*     let _ = List.iter (fun pair -> print_endline (Cprinter.string_of_pair_path_dang pair) ) pr_path_dangs in *)
  (*     print_endline "*************************************" *)
  (*   end *)
  (* in *)
  (* let _ = List.iter pr_one ls_cond_defs_drops in *)
  let ls_cond_danghps_constrs = SAC.partition_constrs_4_paths link_hpargs hp_lst_assume in
  let pr_one (cond, _,constrs)=
    begin
      if constrs <> [] then
        let _ = print_endline ("Group: " ^ (CF.string_of_cond_path cond)) in
        print_endline ((pr_list_ln Cprinter.string_of_hprel_short) constrs)
    end
  in
  let _ = List.iter pr_one ls_cond_danghps_constrs in
  ()

let process_shape_conquer sel_ids cond_paths=
  let _ = DD.ninfo_pprint "process_shape_conquer\n" no_pos in
  let ls_pr_defs = !sleek_hprel_defns in
  let link_hpargs = !sleek_hprel_unknown in
  let defs =
    (* if not (!Globals.pred_syn_modular) then *)
      let orig_vars = List.fold_left (fun ls (_,(_,hf,_,_))-> ls@(CF.h_fv hf)) [] ls_pr_defs in
      let sel_hps = List.map (fun v -> TI.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (sel_ids) in
      let sel_hps  = List.filter (fun sv ->
          let t = CP.type_of_spec_var sv in
          ((* is_RelT t || *) is_HpT t )) sel_hps in
      let ls_path_link = SAU.dang_partition link_hpargs in
      let ls_path_defs = SAU.defn_partition ls_pr_defs in
      (*pairing*)
      let ls_path_link_defs = SAU.pair_dang_constr_path ls_path_defs ls_path_link
        (pr_list_ln Cprinter.string_of_hp_rel_def_short) in
      let ls_path_defs_settings = List.map (fun (path,link_hpargs, defs) ->
          (path, defs, [],link_hpargs,[])) ls_path_link_defs in
      Sa2.infer_shapes_conquer iprog !cprog "" ls_path_defs_settings sel_hps
    (* else *)
    (*   Sa3.infer_shapes iprog !cprog "" constrs2 *)
    (*       sel_hps sel_post_hps unk_map unk_hpargs link_hpargs true false *)
  in
  let _ =
    begin
      let rel_defs =  Sa2.rel_def_stk in
      if not(rel_defs# is_empty) then
        let defs = List.sort CF.hpdef_cmp (rel_defs # get_stk) in
        print_endline "";
      print_endline "\n*************************************";
      print_endline "*******relational definition ********";
      print_endline "*************************************";
      (* print_endline (rel_defs # string_of_reverse); *)
       let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
       print_endline (pr1 defs);
      print_endline "*************************************"
    end
  in
  ()

let process_shape_postObl pre_hps post_hps=
   let hp_lst_assume = !sleek_hprel_assumes in
  let constrs2, sel_hps, sel_post_hps, unk_map, unk_hpargs, link_hpargs=
    shape_infer_pre_process hp_lst_assume pre_hps post_hps
  in
  let grp_link_hpargs = SAU.dang_partition link_hpargs in
  let cond_path = [] in
   let link_hpargs = match grp_link_hpargs with
    | [] -> []
    | (_, a)::_ -> a
  in
  let ls_inferred_hps, ls_hprel, _, _ =
    if List.length sel_hps> 0 && List.length hp_lst_assume > 0 then
      let infer_shape_fnc = Sa2.infer_shapes_from_fresh_obligation in
      infer_shape_fnc iprog !cprog "" false cond_path constrs2 [] []
          sel_hps sel_post_hps [] unk_hpargs link_hpargs true unk_map false
          [] [] []
    else [], [],[],[]
  in
  let _ = begin
      if (ls_hprel <> []) then
        let pr = pr_list_ln Cprinter.string_of_hp_rel_def in
        print_endline "";
      print_endline "\n************************************************";
      print_endline "*******relational definition (obligation)********";
      print_endline "**************************************************";
      print_endline (pr ls_hprel);
      print_endline "*************************************"
    end
  in
  ()

let process_shape_sconseq pre_hps post_hps=
  (* let _ = DD.info_pprint "process_shape_infer" no_pos in *)
  let hp_lst_assume = !sleek_hprel_assumes in
  let sel_hps, sel_post_hps = SAU.get_pre_post pre_hps post_hps hp_lst_assume in
  let constrs1 = SAC.do_strengthen_conseq !cprog [] hp_lst_assume in
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let _ =
  begin
    print_endline "\n*************************************";
    print_endline "*******relational assumptions (1) ********";
    print_endline "*************************************";
    print_endline (pr1 constrs1);
    print_endline "*************************************";
  end;
  in
  (* let _ = if(!Globals.cp_test || !Globals.cp_prefile) then *)
  (*    CEQ.cp_test !cprog hp_lst_assume ls_inferred_hps sel_hps *)
  (* in *)
  ()

let process_shape_sante pre_hps post_hps=
  (* let _ = DD.info_pprint "process_shape_infer" no_pos in *)
  let hp_lst_assume = !sleek_hprel_assumes in
  let sel_hps, sel_post_hps = SAU.get_pre_post pre_hps post_hps hp_lst_assume in
  let constrs1 = SAC.do_strengthen_ante !cprog [] hp_lst_assume in
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let _ =
  begin
    print_endline "\n*************************************";
    print_endline "*******relational assumptions (1) ********";
    print_endline "*************************************";
    print_endline (pr1 constrs1);
    print_endline "*************************************";
  end;
  in
  (* let _ = if(!Globals.cp_test || !Globals.cp_prefile) then *)
  (*    CEQ.cp_test !cprog hp_lst_assume ls_inferred_hps sel_hps *)
  (* in *)
  ()

let process_shape_infer_prop pre_hps post_hps=
  (* let _ = DD.info_pprint "process_shape_infer_prop" no_pos in *)
  let hp_lst_assume = !sleek_hprel_assumes in
  (*get_dangling_pred constrs*)
  let constrs2, sel_hps, sel_post_hps, unk_map, unk_hpargs, link_hpargs=
    shape_infer_pre_process hp_lst_assume pre_hps post_hps
  in
  let ls_hprel, ls_inferred_hps=
    let infer_shape_fnc =  if not (!Globals.pred_syn_modular) then
      Sa2.infer_shapes
    else Sa3.infer_shapes (* Sa.infer_hps *)
    in
    infer_shape_fnc iprog !cprog "" hp_lst_assume
        sel_hps sel_post_hps unk_map unk_hpargs link_hpargs false false
  in
  let _ = if not (!Globals.pred_syn_modular) then
    begin
      let rel_defs =  Sa2.rel_def_stk in
      if not(rel_defs# is_empty) then
        print_endline "";
      print_endline "\n*************************************";
      print_endline "*******relational definition ********";
      print_endline "*************************************";
      print_endline (Sa2.rel_def_stk # string_of_reverse);
      print_endline "*************************************"
    end
  in
  (* let _ = if(!Globals.cp_test || !Globals.cp_prefile) then *)
  (*    CEQ.cp_test !cprog hp_lst_assume ls_inferred_hps sel_hps *)
  (* in *)
  ()

let process_shape_split pre_hps post_hps=
  (* let _, sel_post_hps = SAU.get_pre_post pre_hps post_hps !sleek_hprel_assumes in *)
  (*get infer_vars*)
  let orig_vars = List.fold_left (fun ls cs-> ls@(CF.fv cs.CF.hprel_lhs)@(CF.fv cs.CF.hprel_rhs)) [] !sleek_hprel_assumes in
  let pre_vars = List.map (fun v -> TI.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (pre_hps) in
  let post_vars = List.map (fun v -> TI.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (post_hps) in
  let pre_vars1 = (CP.remove_dups_svl pre_vars) in
  let post_vars1 = (CP.remove_dups_svl post_vars) in
  let infer_pre_vars,pre_hp_rels  = List.partition (fun sv ->
      let t = CP.type_of_spec_var sv in
      not ((* is_RelT t || *) is_HpT t )) pre_vars1 in
  let infer_post_vars,post_hp_rels  = List.partition (fun sv ->
      let t = CP.type_of_spec_var sv in
      not ((* is_RelT t || *) is_HpT t )) post_vars1 in
  (*END*)
  let infer_vars = infer_pre_vars@infer_post_vars in
  let sel_hp_rels = pre_hp_rels@post_hp_rels in
  (*sleek level: depend on user annotation. with hip, this information is detected automatically*)
  let constrs1, unk_map, unk_hpargs = SAC.detect_dangling_pred !sleek_hprel_assumes sel_hp_rels [] in
   let link_hpargs = !sleek_hprel_unknown in
   let grp_link_hpargs = SAU.dang_partition link_hpargs in
    let link_hpargs = match grp_link_hpargs with
    | [] -> []
    | (_, a)::_ -> a
  in
   let cond_path = [] in
  let new_constrs,_,_ = Sa2.split_constr !cprog cond_path constrs1 post_hp_rels infer_vars unk_map (List.map fst unk_hpargs) (List.map fst link_hpargs) in
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  begin
    print_endline "\n*************************************";
    print_endline "*******relational assumptions (1) ********";
    print_endline "*************************************";
    print_endline (pr1 new_constrs);
    print_endline "*************************************";
  end;
  ()

let process_shape_elim_useless sel_vnames=
  let view_defs = Norm.norm_elim_useless !cprog.Cast.prog_view_decls sel_vnames in
  let _ = !cprog.Cast.prog_view_decls <- view_defs in
  let pr = pr_list_ln Cprinter.string_of_view_decl in
  let _ = Debug.info_pprint ("views after ELIM: \n" ^ (pr view_defs)) no_pos in
  ()

let process_shape_extract sel_vnames=
  let view_defs = Norm.norm_extract_common !cprog !cprog.Cast.prog_view_decls sel_vnames in
  let _ = !cprog.Cast.prog_view_decls <- view_defs in
  let pr = pr_list_ln Cprinter.string_of_view_decl in
  let _ = Debug.tinfo_pprint ("views after EXTRACTION: \n" ^ (pr view_defs)) no_pos in
  ()

(* the value of flag "exact" decides the type of entailment checking              *)
(*   None       -->  forbid residue in RHS when the option --classic is turned on *)
(*   Some true  -->  always check entailment exactly (no residue in RHS)          *)
(*   Some false -->  always check entailment inexactly (allow residue in RHS)     *)
let run_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) (etype: entail_type) =
  wrap_classic etype (run_infer_one_pass [] iante0) iconseq0
  
let run_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) (etype: entail_type) =
  let with_timeout = 
    let fctx = CF.mkFailCtx_in (CF.Trivial_Reason
      (CF.mk_failure_may "timeout" Globals.timeout_error)) in
    (false, fctx,[]) in
  Procutils.PrvComms.maybe_raise_and_catch_timeout_sleek
    (run_entail_check iante0 iconseq0) etype with_timeout

let run_entail_check (iante : meta_formula) (iconseq : meta_formula) (etype: entail_type) =
  let pr = string_of_meta_formula in
  let pr_2 = pr_triple string_of_bool Cprinter.string_of_list_context !CP.print_svl in
  Debug.no_2 "run_entail_check" pr pr pr_2 (fun _ _ -> run_entail_check iante iconseq etype) iante iconseq

let print_entail_result sel_hps (valid: bool) (residue: CF.list_context) (num_id: string):bool =
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
            | Some s -> "(must) cause:"^s
            | _ -> (match CF.get_may_failure residue with
                | Some s -> "(may) cause:"^s
                | None -> "INCONSISTENCY : expected failure but success instead"
              )
                  (*should check bot with is_bot_status*)
        else ""
      in
      (* Get the timeout message *)
      let timeout = 
        if !Globals.sleek_timeout_limit > 0. then
          match CF.get_may_failure residue with
            | Some "timeout" -> " (timeout) "
            | _ -> ""
        else ""
      in
      Log.last_cmd # dumping "sleek_dump(fail)";
      silenced_print print_string (num_id^": Fail."^timeout^s^"\n"^term_output^"\n"); flush stdout;
	  false
      (*if !Globals.print_err_sleek then *)
      (* ;print_string ("printing here: "^(Cprinter.string_of_list_context rs)) *)
    end
  else
    begin
         (* let sel_hp_rels = CF.get_infer_vars_sel_hp_list_ctx residue in *)
      let s =
        if not !Globals.disable_failure_explaining then
          match CF.list_context_is_eq_flow residue false_flow_int with
            | true -> "(bot)"
            | false -> (*expect normal (OK) here*) ""
        else ""
      in
      if t_valid then (silenced_print print_string (num_id^": Valid. "^s^"\n"^term_output^"\n"); true)
      else 
        begin
          Log.last_cmd # dumping "sleek_dump(fail2)";
          silenced_print print_string (num_id^": Fail. "^s^"\n"^term_output^"\n");
          false
        end

      (* let hp_lst_assume = Infer.rel_ass_stk # get_stk in *)
      (* if not(Infer.rel_ass_stk# is_empty) then *)
      (*   begin *)
      (*     print_endline "*************************************"; *)
      (*     print_endline "*******relational assumption ********"; *)
      (*     print_endline "*************************************"; *)
      (*     (\* print_endline (Infer.rel_ass_stk # string_of_reverse); *\) *)
      (*     print_endline "*************************************"; *)
      (*     Infer.rel_ass_stk # reset *)
      (*   end; *)
      (* (\* let _ = Debug.info_pprint (" sel_hps:" ^ (!CP.print_svl sel_hps)) no_pos in *\) *)
      (* let ls_hprel, _(\* ls_inferred_hps *\), _ (\* dropped_hps *\) = *)
      (*   if !Globals.pred_syn_flag && (hp_lst_assume <> []) then *)
      (*     Sa.infer_hps !cprog num_id hp_lst_assume *)
      (*         sel_hps [] [] *)
      (*   else [],[],[] *)
      (* in *)
      (* if not(Sa.rel_def_stk# is_empty) then *)
      (*   begin *)
	  (*       print_endline "";  *)
	  (*       print_endline "*************************************"; *)
	  (*       print_endline "*******relational definition ********"; *)
	  (*       print_endline "*************************************"; *)
      (*       (\* print_endline (Sa.rel_def_stk # string_of_reverse); *\) *)
	  (*       print_endline "*************************************"; *)
      (*         Sa.rel_def_stk #reset; *)
      (*   end; *)
      (* already printed in the result *)
      (* if not(Infer.infer_rel_stk# is_empty) then *)
      (*   begin *)
      (*     print_endline "*************************************"; *)
      (*     print_endline "*******inferred pure relations ******"; *)
      (*     print_endline "*************************************"; *)
      (*     print_endline (Infer.infer_rel_stk # string_of_reverse); *)
      (*     print_endline "*************************************"; *)
      (*     Infer.infer_rel_stk # reset *)
      (*   end; *)
      (* ;print_string ("printing here: "^(Cprinter.string_of_list_context residue)) *)
    end
  (* with e -> *)
  (*     let _ =  Error.process_exct(e)in *)

let print_exception_result s (num_id: string) =
          Log.last_cmd # dumping "sleek_dump(exception)";
          silenced_print print_string (num_id^": EXC. "^s^"\n")

let print_entail_result sel_hps (valid: bool) (residue: CF.list_context) (num_id: string):bool =
  let pr0 = string_of_bool in
  let pr = !CF.print_list_context in
  DD.no_2 "print_entail_result" pr0 pr (fun _ -> "") 
    (fun _ _ -> print_entail_result sel_hps valid residue num_id) valid residue


let print_exc (check_id: string) =
  Printexc.print_backtrace stdout;
  dummy_exception() ; 
  print_string ("exception caught " ^ check_id ^ " check\n")

(* the value of flag "exact" decides the type of entailment checking              *)
(*   None       -->  forbid residue in RHS when the option --classic is turned on *)
(*   Some true  -->  always check entailment exactly (no residue in RHS)          *)
(*   Some false -->  always check entailment inexactly (allow residue in RHS)     *)
let process_entail_check_x (iante : meta_formula) (iconseq : meta_formula) (etype : entail_type) =
  let nn = (sleek_proof_counter#inc_and_get) in
  let num_id = "\nEntail "^(string_of_int nn) in
    try 
      let valid, rs, _(*sel_hps*) = 
        wrap_proving_kind (PK_Sleek_Entail nn) (run_entail_check iante iconseq) etype in
      print_entail_result [] (*sel_hps*) valid rs num_id
    with ex ->
        let exs = (Printexc.to_string ex) in
        let _ = print_exception_result exs (*sel_hps*) num_id in
        (* (\* let _ = print_string "caught\n"; Printexc.print_backtrace stdout in *\) *)
        (* let _ = print_string ("\nEntailment Problem "^num_id^(Printexc.to_string ex)^"\n")  in *)
        false
  (* with e -> print_exc num_id *)

(* the value of flag "exact" decides the type of entailment checking              *)
(*   None       -->  forbid residue in RHS when the option --classic is turned on *)
(*   Some true  -->  always check entailment exactly (no residue in RHS)          *)
(*   Some false -->  always check entailment inexactly (allow residue in RHS)     *)
let process_entail_check (iante : meta_formula) (iconseq : meta_formula) (etype: entail_type) =
  let pr = string_of_meta_formula in
  Debug.no_2 "process_entail_check_helper" pr pr (fun _ -> "?") process_entail_check_x iante iconseq etype

let process_eq_check (ivars: ident list)(if1 : meta_formula) (if2 : meta_formula) =
  (*let _ = print_endline ("\n Compare Check") in*)
  let nn = "("^(string_of_int (sleek_proof_counter#inc_and_get))^") " in
  let num_id = "\nCheckeq "^nn in  
  let _ = if (!Globals.print_input || !Globals.print_input_all) then print_endline ("INPUT: \n ### if1 = " ^ (string_of_meta_formula if1) ^"\n ### if2 = " ^ (string_of_meta_formula if2)) else () in
  let _ = Debug.devel_pprint ("\nrun_cmp_check:"
                              ^ "\n ### f1 = "^(string_of_meta_formula if1)
                              ^ "\n ### f2 = "^(string_of_meta_formula if2)
                              ^"\n\n") no_pos in
  
  let (n_tl,f1) = meta_to_formula_not_rename if1 false [] []  in
  let (n_tl,f2) = meta_to_formula_not_rename if2 false [] n_tl  in

  let _ = if (!Globals.print_core || !Globals.print_core_all) then print_endline ("INPUT: \n ### formula 1= " ^ (Cprinter.string_of_formula f1) ^"\n ### formula 2= " ^ (Cprinter.string_of_formula f2)) else () in

  (*let f2 = Solver.prune_preds !cprog true f2 in *)
  if(not !Globals.dis_show_diff) then(
    let (res, mt_list) = CEQ.checkeq_formulas_with_diff ivars f1 f2 in
    let _ = if(res) then(
      print_string (num_id^": Valid.")
    )
      else
        print_string (num_id^": Fail.\n")
  (* print_endline ("\n VALID") else print_endline ("\n FAIL") *)
    in
    ()
  )
  else (
    let (res, mt_list) = CEQ.checkeq_formulas ivars f1 f2 in
    let _ = if(res) then(
      print_string (num_id^": Valid.")
    )
      else
        print_string (num_id^": Fail.\n")
  (* print_endline ("\n VALID") else print_endline ("\n FAIL") *)
    in
    let _ = if(res) then Debug.info_pprint (CEQ.string_of_map_table (List.hd mt_list) ^ "\n") no_pos in
    ()
   )

let print_result f m =
      print_endline (((add_str m Cprinter.string_of_pure_formula) f)^"\n")

let process_simplify (f : meta_formula) =
  let num_id = "Simplify  ("^(string_of_int (sleek_proof_counter#inc_and_get))^")" in  
  try 
    let rs = run_simplify f in
    print_result rs num_id
  with _ -> print_exc num_id

let process_hull (f : meta_formula) =
  let num_id = "Hull  ("^(string_of_int (sleek_proof_counter#inc_and_get))^")" in  
  try 
    let rs = run_hull f in
    print_result rs num_id
  with _ -> print_exc num_id

let process_pairwise (f : meta_formula) =
  let num_id = "PairWise  ("^(string_of_int (sleek_proof_counter#inc_and_get))^")" in  
  try 
    let rs = run_pairwise f in
    print_result rs num_id
  with _ -> print_exc num_id


let process_infer (ivars: ident list) (iante0 : meta_formula) (iconseq0 : meta_formula) etype =
  let nn = "("^(string_of_int (sleek_proof_counter#inc_and_get))^") " in
  let num_id = "\nEntail "^nn in
    try 
      let valid, rs, sel_hps = wrap_classic etype (run_infer_one_pass ivars iante0) iconseq0 in
      print_entail_result sel_hps valid rs num_id
    with ex -> 
        (* print_exc num_id *)
        print_string "caught\n"; Printexc.print_backtrace stdout;
        let _ = print_string ("\nEntailment Problem "^nn^(Printexc.to_string ex)^"\n") 
        in false

let process_capture_residue (lvar : ident) = 
	let flist = match !residues with 
      | None -> [(CF.mkTrue (CF.mkTrueFlow()) no_pos)]
      | Some (ls_ctx, print) -> CF.list_formula_of_list_context ls_ctx in
		put_var lvar (Sleekcommons.MetaFormLCF flist)

let process_print_command pcmd0 = match pcmd0 with
  | PVar pvar ->	  
	  let mf = try get_var pvar with Not_found->  Error.report_error {
                   Error.error_loc = no_pos;
                   Error.error_text = "couldn't find " ^ pvar;
                 }in
	  let (n_tl,pf) = meta_to_struc_formula mf false [] None [] in
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
                    (* let _ = print_endline (Cprinter.string_of_list_context ls_ctx) in *)
                    print_string ((Cprinter.string_of_numbered_list_formula_trace_inst !cprog
                        (CF.list_formula_trace_of_list_context ls_ctx))^"\n" );
	else
	  print_string ("unsupported print command: " ^ pcmd)

let process_cmp_command (input: ident list * ident * meta_formula list) =
  let iv,var,fl = input in
  if var = "residue" then
    match !residues with
      | None -> print_string ": no residue \n"
      | Some (ls_ctx, print) ->(
        if (print) then (
	  if(List.length fl = 1) then (
	    let f = List.hd fl in
	    let cfs = CF.list_formula_of_list_context ls_ctx in
	    let cf1 = (List.hd cfs) in (*if ls-ctx has exacly 1 ele*)	    
	    let (n_tl,cf2) = meta_to_formula_not_rename f false [] []  in
	    let _ = Debug.info_pprint ("Compared residue: " ^ (Cprinter.string_of_formula cf2) ^ "\n") no_pos in
	    let res,mt = CEQ.checkeq_formulas iv cf1 cf2 in
	    if(res) then  print_string ("EQUAL\n") else  print_string ("NOT EQUAL\n")
	  )
	  else  print_string ("ERROR: Input is 1 formula only\n")
	)
      )
  else if (var = "assumption") then(
    match !residues with
      | None -> print_string ": no residue \n"
      | Some (ls_ctx, print) ->(
        if (print) then (
	  if(List.length fl = 2) then (
	    let f1,f2 = (List.hd fl, List.hd (List.tl fl)) in	    
	    let (n_tl,cf11) = meta_to_formula_not_rename f1 false [] []  in
	    let (n_tl,cf12) = meta_to_formula_not_rename f2 false [] n_tl  in
	    let _ = Debug.info_pprint ("Compared assumption: " ^ (Cprinter.string_of_formula cf11) ^ ", " ^ (Cprinter.string_of_formula cf12) ^ "\n") no_pos in
	    let hprels = match ls_ctx with
	      | CF.SuccCtx (c::_) ->  CF.collect_hp_rel c
	      | _ -> [] (*TODO: report error ?*)
	    in
	    let hprel1 = List.hd hprels in
	    let cf21,cf22 = hprel1.CF.hprel_lhs,hprel1.CF.hprel_rhs in
	    let res,mtl = CEQ.check_equiv_constr iv (cf11,cf12) (cf21, cf22) in
	    if(res) then  print_string ("EQUAL\n") else  print_string ("NOT EQUAL\n")
	  )
	  else  print_string ("ERROR: Input is 1 formula only\n")
	)
      )
  )
  else
    print_string ("unsupported compare command: " ^ var)

let get_residue () = !residues

let get_residue () =
  Debug.no_1 "get_residue" pr_no (pr_opt pr_no) get_residue ()
  (*match !residues with*)
    (*| None -> ""*)
    (*| Some s -> Cprinter.string_of_list_formula (CF.list_formula_of_list_context s)*)

let meta_constr_to_constr (meta_constr: meta_formula * meta_formula): (CF.formula * CF.formula) = 
  let if1, if2 = meta_constr in  
  let (n_tl,f1) = meta_to_formula_not_rename if1 false [] []  in
  let (n_tl,f2) = meta_to_formula_not_rename if2 false [] n_tl  in
  (f1,f2)

