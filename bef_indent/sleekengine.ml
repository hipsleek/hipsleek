#include "xdebug.cppo"
open VarGen
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

let string_of_vres t =
  match t with
    | VR_Valid -> "Valid"
    | VR_Fail s -> "Fail"^(if s<0 then "_May" else if s>0 then "_Must" else "")
    | VR_Unknown s -> "UNKNOWN("^s^")"



(* let transfrom_bexpr_x lhs rhs tl= *)
(*   (lhs, rhs) *)

(* let transfrom_bexpr lhs rhs tl= *)
(*   let pr1 = !CP.print_formula in *)
(*   let pr2 = Typeinfer.string_of_tlist in *)
(*   Debug.no_3 "transfrom_bexpr" pr1 pr1 pr2 (pr_pair pr1 pr1) *)
(*       (fun _ _ _ -> transfrom_bexpr_x lhs rhs tl) *)
(*       lhs rhs tl *)


let proc_sleek_result_validate is_valid lc =
  let eres = if not is_valid then
  let final_error_opt = CF.get_final_error lc in
  match final_error_opt with
    | Some (_, fk) -> begin
        match fk with
          | CF.Failure_May _ -> VR_Fail 1
          | CF.Failure_Must _ -> VR_Fail 1
          | _ -> VR_Fail (-1) (* INCONSISTENCY *)
      end
    | None -> VR_Fail (-1) (* INCONSISTENCY *)
  else VR_Valid
  in
  (eres, CF.flow_formula_of_list_context lc)
  (* match lc with *)
  (*   | CF.FailCtx _ -> *)
  (*     if CF.is_must_failure lc then *)
  (*       if CF.is_sat_failure lc then *)
  (*         (\* must fail + have cex*\) *)
  (*         VR_Fail 1 *)
  (*       else VR_Fail (-1) *)
  (*     else *)
  (*       if CF.is_may_failure lc then *)
  (*         (\* may fail + have cex*\) *)
  (*         VR_Fail 1 *)
  (*       else VR_Fail (-1) *)
  (*   | CF.SuccCtx c ->  *)
  (*     match CF.get_must_error_from_ctx c with *)
  (*     | None -> VR_Valid *)
  (*     | (Some (_,cex)) -> if Cformula.is_sat_fail cex then VR_Fail 1 else (VR_Fail (-1)) *)

(* TODO : why do we need two diff kinds of must-errors? *)
(* Is there any difference between the two? *)

let proc_sleek_result_validate b lc =
  Debug.no_1 "proc_sleek_result_validate" 
  Cprinter.string_of_list_context_short (fun (er,_) -> string_of_vres er)
  (fun _ -> proc_sleek_result_validate b lc) lc

module H = Hashtbl
module I = Iast
(* module Inf = Infer *)
(* module C = Cast *)
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure
(* module LP = Lemproving *)
(* module AS = Astsimp *)
(* module DD = Debug *)
module XF = Xmlfront
module NF = Nativefront
module CEQ = Checkeq
(* module TI = Typeinfer *)
(* module SAU = Sautility *)
(* module SAC = Sacore *)
module MCP = Mcpure
(* module SC = Sleekcore *)
(* module LEM = Lemma *)
module LO2 = Label_only.Lab2_List
module TP = Tpdispatcher
(* module FP = Fixpoint *)

let sleek_proof_counter = new Gen.counter 0

let unexpected_cmd = ref []

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

let iexc_def =  {I.data_name = raisable_class;
I.data_fields = [];
I.data_pos = no_pos;
I.data_parent_name = "Object";
I.data_invs = []; (* F.mkTrue no_pos; *)
I.data_is_template = false;
I.data_methods = [] }

let ithrd_def =  {I.data_name = Globals.thrd_name ;
I.data_fields = [];
I.data_pos = no_pos;
I.data_parent_name = "Object";
I.data_invs = []; (* F.mkTrue no_pos; *)
I.data_is_template = false;
I.data_methods = [] }

let iprog = { I.prog_include_decls =[];
I.prog_data_decls = [iobj_def;ithrd_def;iexc_def];
I.prog_global_var_decls = [];
I.prog_logical_var_decls = [];
I.prog_enum_decls = [];
I.prog_view_decls = [];
I.prog_func_decls = [];
I.prog_rel_decls = [];
I.prog_rel_ids = [];
I.prog_templ_decls = [];
I.prog_ut_decls = [];
I.prog_hp_decls = [];
I.prog_hp_ids = [];
I.prog_axiom_decls = []; (* [4/10/2011] An Hoa *)
I.prog_proc_decls = [];
I.prog_coercion_decls = [];
I.prog_hopred_decls = [];
I. prog_barrier_decls = [];
I.prog_test_comps = [];
}

let cobj_def = { Cast.data_name = "Object";
				 Cast.data_fields = [];
				 Cast.data_pos = no_pos;
				 Cast.data_parent_name = "";
				 Cast.data_invs = [];
				 Cast.data_methods = [] }

let cprog = ref { 
    Cast.prog_data_decls = [];
    Cast.prog_view_decls = [];
    Cast.prog_logical_vars = [];
    (*	Cast.prog_func_decls = [];*)
    Cast.prog_rel_decls = []; (* An Hoa *)
    Cast.prog_templ_decls = [];
    Cast.prog_ut_decls = [];
    Cast.prog_hp_decls = [];
    Cast.prog_view_equiv = [];
    Cast.prog_axiom_decls = []; (* [4/10/2011] An Hoa *)
    (*Cast.old_proc_decls = [];*)
    Cast.new_proc_decls = Hashtbl.create 1; (* no need for proc *)
    (*Cast.prog_left_coercions = [];
    Cast.prog_right_coercions = [];*)
    Cast. prog_barrier_decls = []}

let _ =
  Lem_store.all_lemma # clear_right_coercion;
  Lem_store.all_lemma # clear_left_coercion

let update_iprog ip=
  iprog = ip

(* Moved to CFormula *)
(* let residues =  ref (None : (CF.list_context * bool) option)    (\* parameter 'bool' is used for printing *\) *)

let sleek_hprel_assumes = ref ([]: CF.hprel list)
let sleek_hprel_defns = ref ([]: (CF.cond_path_type * CF.hp_rel_def) list)

let sleek_hprel_unknown = ref ([]: (CF.cond_path_type * (CP.spec_var * CP.spec_var list)) list)
let sleek_hprel_dang = ref ([]: (CP.spec_var *CP.spec_var list) list)

let should_infer_tnt = ref true

let clear_iprog () =
  iprog.I.prog_data_decls <- [iobj_def;ithrd_def];
  iprog.I.prog_view_decls <- [];
  iprog.I.prog_rel_decls <- [];
  iprog.I.prog_hp_decls <- [];
  iprog.I.prog_templ_decls <- [];
  iprog.I.prog_ut_decls <- [];
  iprog.I.prog_coercion_decls <- []

let clear_cprog () =
  !cprog.Cast.prog_data_decls <- [];
  !cprog.Cast.prog_view_decls <- [];
  !cprog.Cast.prog_rel_decls <- [];
  !cprog.Cast.prog_hp_decls <- [];
  !cprog.Cast.prog_templ_decls <- [];
  !cprog.Cast.prog_ut_decls <- [];
  (*!cprog.Cast.prog_left_coercions <- [];*)
  (*!cprog.Cast.prog_right_coercions <- []*)
  Lem_store.all_lemma # clear_right_coercion;
  Lem_store.all_lemma # clear_left_coercion

let clear_all () =
  Debug.clear_debug_log ();
  Tpdispatcher.clear_prover_log ();
  exlist # clear;
  clear_var_table ();
  clear_iprog ();
  clear_cprog ();
  CF.residues := None

(*L2: move to astsimp*)
(* let check_data_pred_name name : bool = *)
(*   try *)
(* 	let _ = I.look_up_data_def_raw iprog.I.prog_data_decls name in *)
(* 	  false *)
(*   with *)
(* 	| Not_found -> begin *)
(* 		try *)
(* 		  let _ = I.look_up_view_def_raw 3 iprog.I.prog_view_decls name in *)
(* 			false *)
(* 		with *)
(* 		  | Not_found -> (\*true*\) *)
(* 			  (\* An Hoa : modify to check for defined relation name as well. *\) *)
(* 				begin *)
(* 					try *)
(* 			  		let _ = I.look_up_rel_def_raw iprog.I.prog_rel_decls name in *)
(* 						false *)
(* 					with *)
(* 			  		| Not_found -> *)
(*                         begin *)
(* 					        try *)
(* 			        		    let _ = I.look_up_func_def_raw iprog.I.prog_func_decls name in *)
(* 						      false *)
(* 					        with *)
(* 			        		  | Not_found -> *)
(*                                 begin *)
(* 					                try *)
(* 			        		            let _ = I.look_up_hp_def_raw iprog.I.prog_hp_decls name in *)
(* 						                false *)
(* 					                with *)
(* 			        		          | Not_found -> true *)
(* 		        	            end *)
(* 		        	    end *)
(* 		  	    end *)
(* 	end *)

(* let check_data_pred_name name :bool = *)
(*   let pr1 x = x in *)
(*   let pr2 = string_of_bool in *)
(*   Debug.no_1 "check_data_pred_name" pr1 pr2 (fun _ -> check_data_pred_name name) name *)

let silenced_print f s = if !Gen.silence_output then () else f s 

(*no longer used*)
(* let process_pred_def pdef =  *)
(*   (\* TODO : how come this method not called? *\) *)
(*   (\* let _ = print_string ("process_pred_def:" *\) *)
(*   (\*                       ^ "\n\n") in *\) *)
(*   if Astsimp.check_data_pred_name iprog pdef.I.view_name then *)
(*     let curr_view_decls = iprog.I.prog_view_decls in *)
(* 	(\* let tmp = iprog.I.prog_view_decls in *\) *)
(* 	  try *)
(* 		let h = (self,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in *)
(* 		let p = (self,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in *)
(* 		iprog.I.prog_view_decls <- pdef :: curr_view_decls; *)
(* 		let wf = Astsimp.case_normalize_struc_formula_view 10 iprog h p pdef.Iast.view_formula false  *)
(*           false (\*allow_post_vars*\) false [] in *)
(* 		let new_pdef = {pdef with Iast.view_formula = wf} in *)
(* 		let tmp_views = Astsimp.order_views (new_pdef :: iprog.I.prog_view_decls) in *)
(* 		iprog.I.prog_view_decls <- List.rev tmp_views; *)
(* (\* ( new_pdef :: iprog.I.prog_view_decls); *\) *)
(* 		(\*let _ = print_string ("\n------ "^(Iprinter.string_of_struc_formula "\t" pdef.Iast.view_formula)^"\n normalized:"^(Iprinter.string_of_struc_formula "\t" wf)^"\n") in*\) *)
(* 		let cpdef = Astsimp.trans_view iprog [] new_pdef in  *)
(* 		let old_vdec = !cprog.Cast.prog_view_decls in *)
(* 		!cprog.Cast.prog_view_decls <- (cpdef :: !cprog.Cast.prog_view_decls); *)
(* (\* added 07.04.2008	*\)	 *)
(* 		(\*ignore (print_string ("init: "^(Iprinter.string_of_struc_formula "" pdef.Iast.view_formula )^"\n normalized: "^ *)
(* 							 (Iprinter.string_of_struc_formula "" wf )^"\n translated: "^ *)
(* 							 (Cprinter.string_of_struc_formula cpdef.Cast.view_formula) *)
(* 							 ^"\n" *)
(* 							 ) *)
(* 				)*\) *)
(* 		(\* used to do this for all preds, due to mutable fields formulas exploded, i see no reason to redo for all:  *)
(* 		ignore (List.map (fun vdef -> Astsimp.compute_view_x_formula cprog vdef !Globals.n_xpure) cprog.Cast.prog_view_decls);*\) *)
(* 		ignore (Astsimp.compute_view_x_formula !cprog cpdef !Globals.n_xpure); *)
(*         ignore (Astsimp.set_materialized_prop cpdef); *)
(* 	let cpdef = Astsimp.fill_one_base_case !cprog cpdef in  *)
(*     (\*let cpdef =  if !Globals.enable_case_inference then Astsimp.view_case_inference !cprog iprog.I.prog_view_decls cpdef else cpdef in*\) *)
(* 	let n_cpdef = Astsimp.view_prune_inv_inference !cprog cpdef in *)
(*     !cprog.Cast.prog_view_decls <- (n_cpdef :: old_vdec); *)
(*     let n_cpdef = {n_cpdef with  *)
(*         Cast.view_formula =  Solver.prune_pred_struc !cprog true n_cpdef.Cast.view_formula ; *)
(*         Cast.view_un_struc_formula = List.map (fun (c1,c2) -> (Solver.prune_preds !cprog true c1,c2)) n_cpdef.Cast.view_un_struc_formula;}in *)
(* 		let _ = if (!Globals.print_core || !Globals.print_core_all) then print_string (Cprinter.string_of_view_decl n_cpdef ^"\n") else () in *)
(* 		!cprog.Cast.prog_view_decls <- (n_cpdef :: old_vdec) *)
(* 		(\*print_string ("\npred def: "^(Cprinter.string_of_view_decl cpdef)^"\n")*\) *)
(* (\* added 07.04.2008	*\)									   *)
(* 	  with *)
(* 		| _ ->  dummy_exception() ; iprog.I.prog_view_decls <- curr_view_decls *)
(*   else *)
(* 	(\* print_string (pdef.I.view_name ^ " is already defined.\n") *\) *)
(* 	report_error pdef.I.view_pos (pdef.I.view_name ^ " is already defined.") *)

(* let process_pred_def pdef =  *)
(*   let pr = Iprinter.string_of_view_decl in *)
(*   Debug.no_1 "process_pred_def" pr pr_no process_pred_def pdef *)

(* WN : why are there two versions of process_pred_def ? *)
(*L2: moved to astsimp.ml*)
(* let process_pred_def_4_iast pdef =  *)
(*   if Astsimp.check_data_pred_name iprog pdef.I.view_name then *)
(*     let curr_view_decls = iprog.I.prog_view_decls in *)
(*     iprog.I.prog_view_decls <- pdef :: curr_view_decls; *)
(*   else *)
(*     report_error pdef.I.view_pos (pdef.I.view_name ^ " is already defined.") *)

let process_pred_def_4_iast pdef =
  (* let pr = Iprinter.string_of_view_decl in *)
  (* Debug.no_1 "process_pred_def_4_iast" pr pr_no process_pred_def_4_iast pdef *)
  Astsimp.process_pred_def_4_iast iprog true pdef

(*should call Astsimp.convert_pred_to_cast
it seems that the following method is no longer used.
It is replaced by convert_data_and_pred_to_cast
*)
(* let convert_pred_to_cast () =  *)
(*   let infer_views = if (!Globals.infer_mem)  *)
(*     then List.map (fun c -> Mem.infer_mem_specs c iprog) iprog.I.prog_view_decls  *)
(*     else iprog.I.prog_view_decls in  *)
(*   iprog.I.prog_view_decls <- infer_views;  *)
(*   let tmp_views = (Astsimp.order_views (iprog.I.prog_view_decls)) in *)
(*   x_tinfo_pp "after order_views" no_pos; *)
(*   let _ = Iast.set_check_fixpt iprog.I.prog_data_decls tmp_views in *)
(*   x_tinfo_pp "after check_fixpt" no_pos; *)
(*   iprog.I.prog_view_decls <- tmp_views; *)
(*   let cviews = List.map (Astsimp.trans_view iprog []) tmp_views in *)
(*   x_tinfo_pp "after trans_view" no_pos; *)
(*   let cviews = *)
(*     if !Globals.pred_elim_useless then *)
(*       Norm.norm_elim_useless cviews (List.map (fun vdef -> vdef.Cast.view_name) cviews) *)
(*     else cviews *)
(*   in *)
(*   let _ = !cprog.Cast.prog_view_decls <- cviews in *)
(*   let cviews1 = *)
(*     if !Globals.norm_extract then *)
(*       Norm.norm_extract_common !cprog cviews (List.map (fun vdef -> vdef.Cast.view_name) cviews) *)
(*     else cviews *)
(*   in *)
(*   let cviews2 = *)
(*     if !Globals.norm_cont_analysis then *)
(*       Norm.cont_para_analysis !cprog cviews1 *)
(*     else *)
(*       cviews1 *)
(*   in *)
(*   let _ = !cprog.Cast.prog_view_decls <- cviews2 in *)
(*   let _ =  (List.map (fun vdef -> Astsimp.compute_view_x_formula !cprog vdef !Globals.n_xpure) cviews2) in *)
(*   x_tinfo_pp "after compute_view" no_pos; *)
(*   let _ = (List.map (fun vdef -> Astsimp.set_materialized_prop vdef) !cprog.Cast.prog_view_decls) in *)
(*   x_tinfo_pp "after materialzed_prop" no_pos; *)
(*   let cprog1 = Astsimp.fill_base_case !cprog in *)
(*   let cprog2 = Astsimp.sat_warnings cprog1 in         *)
(*   let cprog3 = if (!Globals.enable_case_inference or (not !Globals.dis_ps)(\* !Globals.allow_pred_spec *\))  *)
(*     then Astsimp.pred_prune_inference cprog2 else cprog2 in *)
(*   let cprog4 = (Astsimp.add_pre_to_cprog cprog3) in *)
(*   let cprog5 = (\*if !Globals.enable_case_inference then Astsimp.case_inference iprog cprog4 else*\) cprog4 in *)
(*   let _ = if (!Globals.print_input || !Globals.print_input_all) then print_string (Iprinter.string_of_program iprog) else () in *)
(*   let _ = if (!Globals.print_core || !Globals.print_core_all) then print_string (Cprinter.string_of_program cprog5) else () in *)
(*   cprog := cprog5 *)

(* let convert_pred_to_cast () =   *)
(*   Debug.no_1 "convert_pred_to_cast" pr_no pr_no convert_pred_to_cast () *)

(* TODO: *)
let process_func_def fdef =
  if Astsimp.check_data_pred_name iprog fdef.I.func_name then
    let tmp = iprog.I.prog_func_decls in
    try
      iprog.I.prog_func_decls <- ( fdef :: iprog.I.prog_func_decls);
	(*let cfdef = Astsimp.trans_func iprog fdef in !cprog.Cast.prog_func_decls <- (cfdef :: !cprog.Cast.prog_func_decls);*)
	(*Smtsolver.add_function cfdef.Cast.func_name cfdef.Cast.func_vars cfdef.Cast.func_formula;*)
    with
      | _ ->  dummy_exception() ; iprog.I.prog_func_decls <- tmp
    else
      print_string (fdef.I.func_name ^ " is already defined.\n")

(* An Hoa : process the relational definition *)
let process_rel_def rdef =
  if Astsimp.check_data_pred_name iprog rdef.I.rel_name then
	let tmp = iprog.I.prog_rel_decls in
	  try
		(*let h = (self,Unprimed)::(res,Unprimed)::(List.map (fun c-> (c,Unprimed)) rdef.Iast.view_vars ) in
		let p = (self,Primed)::(res,Primed)::(List.map (fun c-> (c,Primed)) rdef.Iast.view_vars ) in
		let wf,_ = Astsimp.case_normalize_struc_formulas iprog h p rdef.Iast.view_formula false false [] in
		let new_rdef = {rdef with Iast.view_formula = wf} in
		iprog.I.prog_view_decls <- ( new_rdef :: iprog.I.prog_view_decls);
		let crdef = Astsimp.trans_view iprog new_rdef in
		let old_vdec = cprog.Cast.prog_view_decls in
		cprog.Cast.prog_view_decls <- (crdef :: cprog.Cast.prog_view_decls);
		ignore (Astsimp.compute_view_x_formula cprog crdef !Globals.n_xpure);
    let crdef = 
      if !Globals.enable_case_inference then 
        Astsimp.view_case_inference cprog iprog.I.prog_view_decls crdef else crdef in
		let n_crdef = Astsimp.view_prune_inv_inference cprog crdef in
    cprog.Cast.prog_view_decls <- (n_crdef :: old_vdec);
    let n_crdef = {n_crdef with 
        Cast.view_formula =  Solver.prune_pred_struc cprog true n_crdef.Cast.view_formula ;
        Cast.view_un_struc_formula = List.map (fun (c1,c2) -> (Solver.prune_preds cprog true c1,c2)) n_crdef.Cast.view_un_struc_formula;}in
		let _ = if !Globals.print_core || !Globals.print_core_all then print_string (Cprinter.string_of_view_decl n_crdef ^"\n") else () in
		cprog.Cast.prog_view_decls <- (n_crdef :: old_vdec) *)
			iprog.I.prog_rel_decls <- ( rdef :: iprog.I.prog_rel_decls);
			let crdef = Astsimp.trans_rel iprog rdef in !cprog.Cast.prog_rel_decls <- (crdef :: !cprog.Cast.prog_rel_decls);
			(* Forward the relation to the smt solver. *)
			let _ = Smtsolver.add_relation crdef.Cast.rel_name crdef.Cast.rel_vars crdef.Cast.rel_formula in
                        Z3.add_relation crdef.Cast.rel_name crdef.Cast.rel_vars crdef.Cast.rel_formula;
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_rel_decls <- tmp
  else
		print_string (rdef.I.rel_name ^ " is already defined.\n")

let process_templ_def tdef =
  if Astsimp.check_data_pred_name iprog tdef.I.templ_name then
	  let tmp = iprog.I.prog_templ_decls in
	  try
      iprog.I.prog_templ_decls <- (tdef::iprog.I.prog_templ_decls);
      !cprog.Cast.prog_templ_decls <- (Astsimp.trans_templ iprog tdef)::!cprog.Cast.prog_templ_decls
    with _ -> dummy_exception (); iprog.I.prog_templ_decls <- tmp 
  else print_endline_quiet (tdef.I.templ_name ^ " is already defined.")

let process_ut_def utdef =
  if Astsimp.check_data_pred_name iprog utdef.I.ut_name then
	  let tmp = iprog.I.prog_ut_decls in
	  try
      iprog.I.prog_ut_decls <- (utdef::iprog.I.prog_ut_decls);
      !cprog.Cast.prog_ut_decls <- (Astsimp.trans_ut iprog utdef)::!cprog.Cast.prog_ut_decls
    with _ -> dummy_exception (); iprog.I.prog_ut_decls <- tmp 
  else print_endline_quiet (utdef.I.ut_name ^ " is already defined.")

let process_hp_def hpdef =
  let _ = print_string (hpdef.I.hp_name ^ " is defined.\n") in
  if Astsimp.check_data_pred_name iprog hpdef.I.hp_name then
	let tmp = iprog.I.prog_hp_decls in
	  try
            (* PURE_RELATION_OF_HEAP_PRED *)
            (* are these a newly added hp_pred? *)
            iprog.I.prog_hp_decls <- ( hpdef :: iprog.I.prog_hp_decls);
	      let chpdef, p_chpdef = Astsimp.trans_hp iprog hpdef in
              let _ = !cprog.Cast.prog_hp_decls <- (chpdef :: !cprog.Cast.prog_hp_decls) in
              let _ = !cprog.Cast.prog_rel_decls <- (p_chpdef::!cprog.Cast.prog_rel_decls) in
	      (* Forward the relation to the smt solver. *)
              let args = fst (List.split chpdef.Cast.hp_vars_inst) in
	      let _ = Smtsolver.add_hp_relation chpdef.Cast.hp_name args chpdef.Cast.hp_formula in
              Z3.add_hp_relation chpdef.Cast.hp_name args chpdef.Cast.hp_formula;
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
  let cadef = Astsimp.trans_axiom iprog adef in
  !cprog.Cast.prog_axiom_decls <- (cadef :: !cprog.Cast.prog_axiom_decls);
  (* Forward the axiom to the smt solver. *)
  let _ = Smtsolver.add_axiom cadef.Cast.axiom_hypothesis Smtsolver.IMPLIES cadef.Cast.axiom_conclusion in
  Z3.add_axiom cadef.Cast.axiom_hypothesis Z3.IMPLIES cadef.Cast.axiom_conclusion;
end

(*this function is never called. it is replaced by process_list_lemma
TO REMOVE
*)
let process_lemma ldef =
  let ldef = Astsimp.case_normalize_coerc iprog ldef in
  let l2r, r2l = Astsimp.trans_one_coercion iprog ldef in
  let l2r = List.concat (List.map (fun c-> Astsimp.coerc_spec !cprog c) l2r) in
  let r2l = List.concat (List.map (fun c-> Astsimp.coerc_spec !cprog c) r2l) in
  (* TODO : WN print input_ast *)
  let _ = if (!Globals.print_input || !Globals.print_input_all) then print_string (Iprinter.string_of_coerc_decl ldef) in
  let _ = if (!Globals.print_core || !Globals.print_core_all) then
    print_string ("\nleft:\n " ^ (Cprinter.string_of_coerc_decl_list l2r) ^"\n right:\n"^ (Cprinter.string_of_coerc_decl_list r2l) ^"\n") else () in
  (* WN_all_lemma - should we remove the cprog updating *)
  let _ = Lem_store.all_lemma # add_coercion l2r r2l in
  (* let _ = Lem_store.all_lemma # add_right_coercion r2l in  *)
  (*!cprog.Cast.prog_left_coercions <- l2r @ !cprog.Cast.prog_left_coercions;*)
  (*!cprog.Cast.prog_right_coercions <- r2l @ !cprog.Cast.prog_right_coercions;*)
  let res = x_add Lemproving.verify_lemma 2 l2r r2l !cprog (ldef.I.coercion_name) ldef.I.coercion_type in
  ()
  (* CF.residues := (match res with *)
  (*   | None -> None; *)
  (*   | Some ls_ctx -> Some (ls_ctx, true)) *)

let process_lemma ldef =
  Debug.no_1 "process_lemma" Iprinter.string_of_coerc_decl (fun _ -> "?") process_lemma ldef

let print_residue residue =
  (* let _ = Debug.info_pprint "inside p res" no_pos in *)
  if (not !Globals.smt_compete_mode) then
    match residue with
      | None -> begin
          (* let _ = Debug.ninfo_pprint "inside p res" no_pos in *)
          print_string ": no residue \n"
              (* | Some s -> print_string ((Cprinter.string_of_list_formula  *)
              (*       (CF.list_formula_of_list_context s))^"\n") *)
              (*print all posible outcomes and their traces with numbering*)
        end
      | Some (ls_ctx, print, local_dfa) -> begin
          let _ = print_string "Residue:\n" in
          (* let is_empty_states = match ls_ctx with *)
          (*   | CF.SuccCtx ls -> List.length ls = 0 *)
          (*   | _ -> false *)
          (* in *)
          if not local_dfa (*!Globals.disable_failure_explaining *) then
              (* let _ = Debug.info_pprint "a" no_pos in *)
              (* let _ = print_endline (Cprinter.string_of_list_context ls_ctx) in *)
              print_string ((Cprinter.string_of_numbered_list_formula_trace_inst !cprog
                  (CF.list_formula_trace_of_list_context ls_ctx))^"\n" )
            else
              (* let _ = Debug.info_pprint "b" no_pos in *)
              if print then
                (* let _ = print_string ((pr_list pr_none (CF.list_formula_trace_of_list_context ls_ctx))^ *)
                (*   (Cprinter.string_of_list_context ls_ctx)^"\n") in () *)
                print_string ((Cprinter.string_of_numbered_list_formula_trace_inst !cprog
                    (CF.list_formula_trace_of_list_context ls_ctx))^"\n" )
              else let _ =  print_string "{ }\n" in ()
        end

let process_list_lemma ldef_lst  =
  let lem_infer_fnct r1 r2 =
    let _ = begin
      let rel_defs = if not (!Globals.pred_syn_modular) then
        Sa2.rel_def_stk
      else Cformula.rel_def_stk
      in
      if not(rel_defs# is_empty) then
        let defs0 = List.sort CF.hpdef_cmp (rel_defs # get_stk) in
        (* let pre_preds,post_pred,rem = List.fold_left ( fun (r1,r2,r3) d -> *)
        (*     match d.CF.hprel_def_kind with *)
        (*       | CP.HPRelDefn (hp,_,_) -> if (CP.mem_svl hp sel_post_hps) then (r1,r2@[d],r3) else *)
        (*           if (CP.mem_svl hp sel_hps) then (r1@[d],r2,r3) else (r1,r2,r3@[d]) *)
        (*       | _ -> (r1,r2,r3@[d]) ) ([],[],[]) defs0 in *)
        (* let defs = pre_preds@post_pred@rem in *)
        let defs1 = if !Globals.print_en_tidy then List.map Cfout.rearrange_def defs0 else defs0 in
        print_endline_quiet "";
        print_endline_quiet "\n*************************************";
        print_endline_quiet "*******relational definition ********";
        print_endline_quiet "*************************************";
        let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
        print_endline_quiet (pr1 defs1);
        print_endline_quiet "*************************************"
    end
    in
    let _ =
      let _ = Debug.info_hprint (add_str "fixpoint1"
          (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_quad pr1 pr1 pr1 pr1))) r1 no_pos in
      let _ = print_endline_quiet "" in
      ()
    in
    r2 
  in
  Lemma.process_list_lemma_helper ldef_lst iprog !cprog lem_infer_fnct 

  (* let lst = ldef_lst.Iast.coercion_list_elems in *)
  (* (\* why do we check residue for ctx? do we really need a previous context? *\) *)
  (* let ctx = match !CF.residues with *)
  (*   | None            ->  CF.SuccCtx [CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos] *)
  (*   | Some (CF.SuccCtx ctx, _) -> CF.SuccCtx ctx *)
  (*   | Some (CF.FailCtx ctx, _) -> CF.SuccCtx [CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos] in *)
  (* (\* andreeac: to check if it should skip lemma proving *\) *)
  (* let res = *)
  (*   match ldef_lst.Iast.coercion_list_kind with *)
  (*     | LEM            -> Lemma.manage_lemmas lst iprog !cprog *)
  (*     | LEM_TEST       -> (Lemma.manage_test_lemmas lst iprog !cprog ) *)
  (*     | LEM_TEST_NEW   -> (Lemma.manage_test_new_lemmas lst iprog !cprog ) *)
  (*     | LEM_UNSAFE     -> Lemma.manage_unsafe_lemmas lst iprog !cprog *)
  (*     | LEM_SAFE       -> Lemma.manage_safe_lemmas lst iprog !cprog *)
  (*     | LEM_INFER      -> snd (Lemma.manage_infer_lemmas lst iprog !cprog) *)
  (*     | LEM_INFER_PRED      -> let r1,r2 = Lemma.manage_infer_pred_lemmas lst iprog !cprog Solver.xpure_heap in *)
  (*       let _ = *)
  (*         begin *)
  (*           let rel_defs = if not (!Globals.pred_syn_modular) then *)
  (*             Sa2.rel_def_stk *)
  (*           else Sa3.rel_def_stk *)
  (*           in *)
  (*           if not(rel_defs# is_empty) then *)
  (*             let defs0 = List.sort CF.hpdef_cmp (rel_defs # get_stk) in *)
  (*             (\* let pre_preds,post_pred,rem = List.fold_left ( fun (r1,r2,r3) d -> *\) *)
  (*             (\*     match d.CF.hprel_def_kind with *\) *)
  (*             (\*       | CP.HPRelDefn (hp,_,_) -> if (CP.mem_svl hp sel_post_hps) then (r1,r2@[d],r3) else *\) *)
  (*             (\*           if (CP.mem_svl hp sel_hps) then (r1@[d],r2,r3) else (r1,r2,r3@[d]) *\) *)
  (*             (\*       | _ -> (r1,r2,r3@[d]) ) ([],[],[]) defs0 in *\) *)
  (*             (\* let defs = pre_preds@post_pred@rem in *\) *)
  (*             let defs1 = if !Globals.print_en_tidy then List.map CF.rearrange_def defs0 else defs0 in *)
  (*             print_endline ""; *)
  (*             print_endline "\n*************************************"; *)
  (*             print_endline "*******relational definition ********"; *)
  (*             print_endline "*************************************"; *)
  (*             let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in *)
  (*             print_endline (pr1 defs1); *)
  (*             print_endline "*************************************" *)
  (*         end *)
  (*       in *)
  (*       let _ = *)
  (*         let _ = Debug.info_hprint (add_str "fixpoint" *)
  (*             (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_quad pr1 pr1 pr1 pr1))) r1 no_pos in *)
  (*         let _ = print_endline "" in *)
  (*         () *)
  (*       in *)
  (*       r2 *)
  (* in *)
  (* match res with *)
  (*   | None | Some [] -> CF.clear_residue () *)
  (*   | Some(c::_) -> CF.set_residue true c *)

let process_list_lemma ldef_lst =
  Debug.no_1 "process_list_lemma" pr_none pr_none process_list_lemma  ldef_lst

let process_data_def ddef =
  if Astsimp.check_data_pred_name iprog ddef.I.data_name then
    (* let tmp = iprog.I.prog_data_decls in *)
    let _ = iprog.I.prog_data_decls <- ddef :: (List.filter (fun dd -> not(string_compare dd.I.data_name raisable_class)) iprog.I.prog_data_decls) in
    let _ = if (!Globals.perm = Globals.Dperm || !Globals.perm = Globals.Bperm) then () else
      let _ = Iast.build_exc_hierarchy true iprog in
      let _ = exlist # compute_hierarchy  in
      let _ = iprog.I.prog_data_decls <- iprog.I.prog_data_decls@[iexc_def] in
      ()
    in ()
  else begin
    dummy_exception() ;
    (* print_string (ddef.I.data_name ^ " is already defined.\n") *)
    report_error ddef.I.data_pos (ddef.I.data_name ^ " is already defined.")
  end

let process_data_def ddef =
  Debug.no_1 "process_data_def" pr_none pr_none process_data_def ddef

(*should merge with astsimp.convert_pred_to_cast*)
let convert_data_and_pred_to_cast_x () =
  (* convert data *)
  let _ = I.annotate_field_pure_ext iprog in
  List.iter (fun ddef ->
    let cddef = Astsimp.trans_data iprog ddef in
    !cprog.Cast.prog_data_decls <- cddef :: !cprog.Cast.prog_data_decls;
    if !perm=NoPerm || not !enable_split_lemma_gen then ()
    else (
      process_lemma (Iast.gen_normalize_lemma_split ddef);
      process_lemma (Iast.gen_normalize_lemma_comb ddef)
    ) (* andreeac: why is process_lemma still called at this point if, subsequentlly (after the call of convert_data_and_pred_to_cast) lemmas are processed again in sleek.ml --- alternatively, remove the call from seek and keep this one *)
  ) iprog.I.prog_data_decls;

  (* convert pred *)
  let tmp_views = List.map (fun pdef ->
    let h = (self,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in
    let p = (self,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in
    let wf = Astsimp.case_normalize_struc_formula_view 11 iprog h p pdef.Iast.view_formula false false false [] in
    let inv_lock = pdef.I.view_inv_lock in
    let inv_lock = (
      match inv_lock with
      | None -> None
      | Some f ->
          let new_f = Astsimp.case_normalize_formula iprog h f in (*TO CHECK: h or p*)
          Some new_f
    ) in
    let new_pdef = {pdef with Iast.view_formula = wf;Iast.view_inv_lock = inv_lock} in
    new_pdef
  ) iprog.I.prog_view_decls in
  let tmp_views,ls_mut_rec_views = (Astsimp.order_views tmp_views) in
  x_tinfo_pp "after order_views" no_pos;
  let _ = Iast.set_check_fixpt iprog iprog.I.prog_data_decls tmp_views in
  x_tinfo_pp "after check_fixpt" no_pos;
  iprog.I.prog_view_decls <- tmp_views;
  (* collect immutable info for splitting view params *)
  let _ = List.map (fun v ->  v.I.view_imm_map <- Immutable.icollect_imm v.I.view_formula v.I.view_vars v.I.view_data_name iprog.I.prog_data_decls )  iprog.I.prog_view_decls  in
  let _ = x_tinfo_hp (add_str "view_decls:"  (pr_list (pr_list (pr_pair Iprinter.string_of_imm string_of_int))))  (List.map (fun v ->  v.I.view_imm_map) iprog.I.prog_view_decls) no_pos in
  let tmp_views_derv,tmp_views= List.partition (fun v -> v.I.view_derv) tmp_views in
  (* let all_mutrec_vnames = (List.concat ls_mut_rec_views) in *)
(*   let cviews0,_ = List.fold_left (fun (transed_views view -> *)
(*       let nview = Astsimp.trans_view iprog mutrec_vnames *)
(*         transed_views [] view in *)
(*       transed_views@[nview] *)
(* ) ([]) tmp_views in *)
(*   let cviews0 = Fixcalc.compute_inv_mutrec ls_mut_rec_views cviews0a in *)
  let _ = if !Globals.smt_compete_mode then
    let _ = Debug.ninfo_hprint (add_str "tmp_views" (pr_list (fun vdcl -> vdcl.Iast.view_name))) tmp_views no_pos in
    let num_vdecls = List.length tmp_views  in
    (* let _ = if num_vdecls <= gen_baga_inv_threshold then *)
    (*     (\* let _ = Globals.gen_baga_inv := false in *\) *)
    (*   (\* let _ = Globals.dis_pred_sat () in *\) *)
    (*     () *)
    (* else *)
    (*   let _ = Globals.lemma_gen_unsafe := false in *)
    (*   (\* let _ = Globals.lemma_syn := false in *\) *)
    (*   () *)
    (* in *)
    let _ =  if !Globals.graph_norm &&  num_vdecls > !graph_norm_decl_threshold then
      let _ = Globals.graph_norm := false in
      ()
    else ()
    in
    (* let _ = if ls_mut_rec_views != [] (\* || num_vdecls > 2 *\) then *)
    (*   (\* lemma_syn does not work well with mut_rec views. Loc: to improve*\) *)
    (*   let _ = Globals.lemma_syn := false in *)
    (*   () *)
    (* else () in *)
    ()
  else ()
  in
  let cur_lem_syn = !Globals.lemma_syn in
  (*turn off generate lemma during trans views*)
  let _ = Globals.lemma_syn := false in
  let cviews0 = Astsimp.trans_views iprog ls_mut_rec_views (List.map (fun v -> (v,[]))  tmp_views) in
  (* x_tinfo_pp "after trans_view" no_pos; *)
  (*derv and spec views*)
  let tmp_views_derv1 = Astsimp.mark_rec_and_der_order tmp_views_derv in
  let cviews_derv = List.fold_left (fun norm_views v ->
              let der_view = Derive.trans_view_dervs iprog Rev_ast.rev_trans_formula Astsimp.trans_view norm_views v in
              (cviews0@[der_view])
          ) cviews0 tmp_views_derv1 in
  let _ = x_tinfo_hp (add_str "derv length" (fun ls -> string_of_int (List.length ls))) tmp_views_derv1 no_pos in
  let cviews = (* cviews0a@ *)cviews_derv in
  let cviews =
    if !Globals.norm_elim_useless  (* !Globals.pred_elim_useless *) then
      Norm.norm_elim_useless cviews (List.map (fun vdef -> vdef.Cast.view_name) cviews)
    else cviews
  in
  let _ = !cprog.Cast.prog_view_decls <- cviews in
  let cviews1 =
    if !Globals.norm_extract then
      Norm.norm_extract_common iprog !cprog cviews (List.map (fun vdef -> vdef.Cast.view_name) cviews)
    else cviews
  in
  let cviews2 =
    if !Globals.norm_cont_analysis then
      let cviews2a = Norm.cont_para_analysis !cprog cviews1 in
     cviews2a
    else
      cviews1
  in
  let _ = !cprog.Cast.prog_view_decls <- cviews2 in
  let _ =  (List.map (fun vdef -> Astsimp.compute_view_x_formula !cprog vdef !Globals.n_xpure) cviews2) in
  x_tinfo_pp "after compute_view" no_pos;
  let _ = (List.map (fun vdef -> Astsimp.set_materialized_prop vdef) cviews2) in
  let cviews2 = (List.map (fun vdef -> Norm.norm_formula_for_unfold !cprog vdef) cviews2) in
  let _ = !cprog.Cast.prog_view_decls <- cviews2 in
  x_tinfo_pp "after materialzed_prop" no_pos;
  let cprog1 = Astsimp.fill_base_case !cprog in
  let cprog2 = Astsimp.sat_warnings cprog1 in
  let cprog3 = if (!Globals.enable_case_inference || (not !Globals.dis_ps)(* !Globals.allow_pred_spec *)) 
    then Astsimp.pred_prune_inference cprog2 else cprog2 in
  let cprog4 = (Astsimp.add_pre_to_cprog cprog3) in
  let cprog5 = if !Globals.enable_case_inference then Astsimp.case_inference iprog cprog4 else cprog4 in
  let cprog6 =  if
    (* !Globals.smt_compete_mode && (!Globals.pred_sat || !Globals.graph_norm ) && *)
   (not (!Globals.lemma_gen_safe || !Globals.lemma_gen_unsafe
    || !Globals.lemma_gen_safe_fold || !Globals.lemma_gen_unsafe_fold || !Globals.seg_fold || !Globals.lemma_syn)) then
    cprog5
  else
    try
      Cast.categorize_view cprog5
    with _ -> cprog5
  in
  let cprog6 = if (!Globals.en_trec_lin ) then Norm.convert_tail_vdefs_to_linear cprog6 else cprog6 in
  let _ =  (* if (!Globals.lemma_gen_safe || !Globals.lemma_gen_unsafe *)
           (*     || !Globals.lemma_gen_safe_fold || !Globals.lemma_gen_unsafe_fold) then *)
    try
      Lemma.generate_all_lemmas iprog cprog6
    with _ -> ()
  in
  let cprog6a =
     if !Globals.norm_cont_analysis then
     let is_need_seg_opz, cviews3a = Norm.norm_ann_seg_opz iprog cprog6 cprog6.Cast.prog_view_decls in
     let _ = if is_need_seg_opz then
       let _ = Frame.seg_opz := true in
       ()
     else
       let _ = Frame.seg_opz := false in
       ()
     in
     let cprog2a = {cprog6 with Cast.prog_view_decls = cviews3a} in
     cprog2a
     else cprog6
  in
  let cprog6 = if (* !Globals.lemma_gen_unsafe || !Globals.lemma_gen_safe *)false then
    Lemutil.norm_checkeq_views iprog cprog6a cprog6a.Cast.prog_view_decls
  else cprog6a
  in
  let _ = Globals.lemma_syn := cur_lem_syn in
  let _ = if (!Globals.print_input || !Globals.print_input_all) then print_string (Iprinter.string_of_program iprog) else () in
  let _ = if (!Globals.print_core || !Globals.print_core_all) then print_string (Cprinter.string_of_program cprog6) else () in
  cprog := cprog6

let convert_data_and_pred_to_cast () = 
  let pr _ = pr_list Iprinter.string_of_view_decl iprog.I.prog_view_decls in
  let pr2 _ = pr_list Cprinter.string_of_view_decl !cprog.Cast.prog_view_decls in
  Debug.no_1 "convert_data_and_pred_to_cast" pr pr2 convert_data_and_pred_to_cast_x ()

let process_barrier_def bd = 
    if !Globals.print_core || !Globals.print_core_all then print_string (Iprinter.string_of_barrier_decl bd) else () ;
	 try
	    let bd = Astsimp.case_normalize_barrier iprog bd in
		let cbd = Astsimp.trans_bdecl iprog bd in
		(*let cbd = Astsimp.normalize_barr_decl !cprog cbd in*)
		Astsimp.check_barrier_wf !cprog cbd;
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
  (*annotate field*)
  let _ = I.annotate_field_pure_ext iprog in
  let cddefs = List.map (Astsimp.trans_data iprog) iprog.I.prog_data_decls in
  !cprog.Cast.prog_data_decls <- cddefs

let rec meta_to_struc_formula (mf0 : meta_formula) quant fv_idents (tlist:Typeinfer.spec_var_type_list) 
	: (Typeinfer.spec_var_type_list*CF.struc_formula) = 
  let rec helper (mf0 : meta_formula) quant fv_idents tl : (Typeinfer.spec_var_type_list*CF.struc_formula) = 
    match mf0 with
    | MetaFormCF mf -> 
        (tl,(Cformula.formula_to_struc_formula mf))
    | MetaFormLCF mf -> 
        (tl,(Cformula.formula_to_struc_formula (List.hd mf)))
    | MetaForm mf -> 
        let h = List.map (fun c-> (c,Unprimed)) fv_idents in
        let p = List.map (fun c-> (c,Primed)) fv_idents in
        let wf,_ = x_add Astsimp.case_normalize_struc_formula 12 iprog h p (Iformula.formula_to_struc_formula mf) true 
          true (*allow_post_vars*) true [] in
        Astsimp.trans_I2C_struc_formula 8 iprog false quant fv_idents wf tl false (*(Cpure.Prim Void) []*) false (*check_pre*) 
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
        let svs = List.map (fun v -> Typeinfer.get_spec_var_type_list v n_tl no_pos) vs in
        let res = Solver.compose_struc_formula cf1 cf2 svs no_pos in
        (n_tl,res)
      end
  | MetaEForm b -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let p = List.map (fun c-> (c,Primed)) fv_idents in
      let wf,_ = x_add Astsimp.case_normalize_struc_formula 13 iprog h p b true (* allow_primes *) 
        true (*allow_post_vars*) true [] in
      let (n_tl,res) = Astsimp.trans_I2C_struc_formula 9 iprog false quant fv_idents wf tl false 
        false (*check_pre*) (*(Cpure.Prim Void) [] *) in
      (* let _ = print_string ("\n1 before meta: " ^(Iprinter.string_of_struc_formula b)^"\n") in *)
      (* let _ = print_string ("\n2 before meta: " ^(Iprinter.string_of_struc_formula wf)^"\n") in *)
      (*let _ = print_string ("\n after meta: " ^ (Cprinter.string_of_struc_formula res)) in*)
      (n_tl,res)
  | MetaEFormCF b ->       (* let _ = print_string ("\n (andreeac) meta_to_struc_formula 6") in *) (tl,b) (* assume it has already been normalized *)
  in helper mf0 quant fv_idents tlist 

let meta_to_struc_formula (mf0 : meta_formula) quant fv_idents (tlist:Typeinfer.spec_var_type_list) 
	: (Typeinfer.spec_var_type_list*CF.struc_formula) 
	= Debug.no_4 "meta_to_struc_formula"
  string_of_meta_formula
  string_of_bool
  string_of_ident_list
  Typeinfer.string_of_tlist
  (pr_pair pr_none Cprinter.string_of_struc_formula)
  (fun _ _ _ _  ->  meta_to_struc_formula mf0 quant fv_idents tlist )mf0 quant fv_idents tlist

(* An Hoa : DETECT THAT EITHER OF 
Astsimp.case_normalize_formula iprog h mf
Astsimp.collect_type_info_formula iprog wf stab false
Astsimp.trans_formula iprog quant
IN THE FUNCTION GIVE AN EXCEPTION
TODO Check the 3 functions above!!!
*)
let rec meta_to_formula (mf0 : meta_formula) quant fv_idents (tlist:Typeinfer.spec_var_type_list) 
  : (Typeinfer.spec_var_type_list*CF.formula) =
  let rec helper (f : Cformula.formula) (subst_vars : Cpure.spec_var list) : Cformula.formula =
    match f with
      | Cformula.Or fo ->
            let f1 = fo.Cformula.formula_or_f1 in
            let f2 = fo.Cformula.formula_or_f2 in
            let pos = fo.Cformula.formula_or_pos in
            Cformula.mkOr (helper f1 subst_vars) (helper f2 subst_vars) pos
      | _ ->
            let svl = Cformula.fv f in
            let subst_vars = List.filter (fun sv -> List.mem sv svl) subst_vars in
            let new_const0 = List.map (fun sv ->
                Cpure.mkNull sv no_pos) subst_vars in
            let new_const = List.fold_left (fun f0 f1 ->
                Cpure.mkAnd f0 f1 no_pos) (Cpure.mkTrue no_pos) new_const0 in
            let new_h, new_p, new_vp, new_fl, new_t, new_a = Cformula.split_components f in
            let new_p = Mcpure.mix_of_pure (Cpure.mkAnd new_const (Mcpure.pure_of_mix new_p) no_pos) in
            let new_f = Cformula.mkExists subst_vars new_h new_p new_vp new_t new_fl new_a no_pos in
            new_f
  in
	match mf0 with
  | MetaFormCF mf -> (tlist,mf)
  | MetaFormLCF mf ->	(tlist,(List.hd mf))
  | MetaForm mf -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      (* let _ = print_string (" before norm: " ^(Iprinter.string_of_formula mf)^"\n") in *)
      let wf = x_add Astsimp.case_normalize_formula iprog h mf in
      let n_tl = Typeinfer.gather_type_info_formula iprog wf tlist false in
      let (n_tl,r) = Astsimp.trans_formula iprog quant fv_idents false wf n_tl false in
      (* let _ = print_string (" before sf: " ^(Iprinter.string_of_formula wf)^"\n") in *)
      (* let _ = print_string (" after sf: " ^(Cprinter.string_of_formula r)^"\n") in *)
      let svl = Cformula.fv r in
      let null_vars0 = List.find_all (fun sv ->
          match sv with Cpure.SpecVar(_,name,_) -> name = "null") svl in
      let null_vars = Cpure.remove_dups_svl null_vars0 in
      let subst_vars = List.map (fun sv ->
          match sv with Cpure.SpecVar(typ,name,pr) ->
              Cpure.SpecVar(typ,fresh_any_name name,pr)) null_vars in
      let new_r = Cformula.subst_avoid_capture null_vars subst_vars r in
      let new_r = helper new_r subst_vars in
      let new_n_tl = List.map (fun (id,svi) ->
          if id = "null" then
            let subst_sv = List.find (fun sv ->
                match sv with Cpure.SpecVar(t1,id1,pr1) ->
                    Cpure.are_same_types t1 svi.Typeinfer.sv_info_kind
            ) subst_vars in
            let Cpure.SpecVar(_,new_id,_) = subst_sv in
            (new_id,svi)
          else
            (id,svi)
      ) n_tl in
      (* let _ = print_string (" after sf: " ^(Cprinter.string_of_formula new_r)^"\n") in *)
      (* let _ = print_string (" n_tl: " ^ (Typeinfer.string_of_tlist new_n_tl)^"\n") in *)
      (new_n_tl,new_r)
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
    let svs = List.map (fun v -> Typeinfer.get_spec_var_type_list v n_tl no_pos) vs in
    let res = Cformula.compose_formula cf1 cf2 svs Cformula.Flow_combine no_pos in
    (n_tl,res)
    end
  | MetaEForm _ | MetaEFormCF _ -> report_error no_pos ("cannot have structured formula in antecedent")

let meta_to_formula (mf0 : meta_formula) quant fv_idents (tlist:Typeinfer.spec_var_type_list) : (Typeinfer.spec_var_type_list*CF.formula) = 
  let pr_meta = string_of_meta_formula in
  let pr_f = Cprinter.string_of_formula in
  let pr2 (_,f) = pr_f f in
  Debug.no_1 "Sleekengine.meta_to_formula" pr_meta pr2
             (fun mf -> meta_to_formula mf quant fv_idents tlist) mf0

let rec meta_to_formula_not_rename (mf0 : meta_formula) quant fv_idents (tlist:Typeinfer.spec_var_type_list)
	: (Typeinfer.spec_var_type_list*CF.formula) = 
	match mf0 with
  | MetaFormCF mf -> (tlist,mf)
  | MetaFormLCF mf -> (tlist,(List.hd mf))
  | MetaForm mf ->
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let wf = Astsimp.case_normalize_formula_not_rename iprog h mf in
      let n_tl = Typeinfer.gather_type_info_formula iprog wf tlist false in
      (*let _ = print_endline ("WF: " ^ Iprinter.string_of_formula wf ) in *)
      let (n_tl,r) = Astsimp.trans_formula iprog quant fv_idents false wf n_tl false in
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
      let svs = List.map (fun v -> Typeinfer.get_spec_var_type_list v n_tl no_pos) vs in
      let res = Cformula.compose_formula cf1 cf2 svs Cformula.Flow_combine no_pos in
			(n_tl,res)
    end
  | MetaEForm _ | MetaEFormCF _ -> report_error no_pos ("cannot have structured formula in antecedent")

let run_simplify (iante0 : meta_formula) =
  let (n_tl,ante) = meta_to_formula iante0 false [] [] in
  let ante = Cvutil.prune_preds !cprog true ante in
  let ante =
    if (Perm.allow_perm ()) then
      (*add default full permission to ante;
        need to add type of full perm to stab *)
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  let (h,p,_,_,_,_) = CF.split_components ante in
  let pf = MCP.pure_of_mix p in
  (* print_endline "calling tp_dispatcher?"; *)
  let r = Tpdispatcher.simplify_tp pf in
  r

let run_hull (iante0 : meta_formula) = 
  let (n_tl,ante) = meta_to_formula iante0 false [] [] in
  let ante = Cvutil.prune_preds !cprog true ante in
  let ante =
    if (Perm.allow_perm ()) then
      (*add default full permission to ante;
        need to add type of full perm to stab *)
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  let (h,p,_,_,_,_) = CF.split_components ante in
  let pf = MCP.pure_of_mix p in
  (* print_endline "calling tp_dispatcher?"; *)
  let r = Tpdispatcher.hull pf in
  r


let run_pairwise (iante0 : meta_formula) = 
  let (n_tl,ante) = meta_to_formula iante0 false [] [] in
  let ante = Cvutil.prune_preds !cprog true ante in
  let ante =
    if (Perm.allow_perm ()) then
      (*add default full permission to ante;
        need to add type of full perm to stab *)
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  let (h,p,_,_,_,_) = CF.split_components ante in
  let pf = MCP.pure_of_mix p in
  (* print_endline "calling tp_dispatcher?"; *)
  let r = Tpdispatcher.tp_pairwisecheck pf in
  r

let run_infer_one_pass itype (ivars: ident list) (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let _ = CF.residues := None in
  let _ = Infer.rel_ass_stk # reset in
  let _ = Sa2.rel_def_stk # reset in
  let _ = CF.rel_def_stk # reset in
  let _ = Iast.set_iprog iprog in
  let _ = if (!Globals.print_input || !Globals.print_input_all) then print_endline_quiet ("INPUT 6: \n ### 1 ante = " ^ (string_of_meta_formula iante0) ^"\n ### conseq = " ^ (string_of_meta_formula iconseq0)) else () in
  let _ = x_dinfo_pp ("\nrun_entail_check 1:"
                              ^ "\n ### iante0 = "^(string_of_meta_formula iante0)
                              ^ "\n ### iconseq0 = "^(string_of_meta_formula iconseq0)
                              ^"\n\n") no_pos in
  let (n_tl,ante) = meta_to_formula iante0 false [] [] in
  (*let ante = x_add Solver.normalize_formula_w_coers !cprog (CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos) ante !cprog.Cast.prog_left_coercions in*)
  let ante = Cvutil.prune_preds !cprog true ante in
  let ante = (*important for permissions*)
    if (Perm.allow_perm ()) then
      (*add default full permission to ante;
        need to add type of full perm to stab *)
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  (* let ante = Astsimp.add_param_ann_constraints_formula ante in *)
  let vk = Typeinfer.fresh_proc_var_kind n_tl Float in
  let n_tl = Typeinfer.type_list_add  (full_perm_name ()) vk n_tl in
(*  let _ = flush stdout in*)
  (* let csq_extra = meta_to_formula iconseq0 false [] stab in *)
  (* let conseq_fvs = CF.fv csq_extra in *)
  (* let _ = print_endline ("conseq vars"^(Cprinter.string_of_spec_var_list conseq_fvs)) in *)
  let fvs = CF.fv ante in
  (* let ivars_fvs = List.map (fun n -> CP.SpecVar (UNK,n,Unprimed)) ivars in *)
  (* let _ = print_endline ("ivars"^(Cprinter.string_of_spec_var_list ivars_fvs)) in *)
  (* let _ = print_endline ("ante vars"^(Cprinter.string_of_spec_var_list fvs)) in *)
  (* Disable putting implicit existentials on unbound heap variables *)
  let fv_idents = (List.map CP.name_of_spec_var fvs)@ivars in
  let fv_idents =
    if !Globals.dis_impl_var then
      let conseq_idents = List.map (fun (v, _) -> v) (fv_meta_formula iconseq0) in
      Gen.BList.remove_dups_eq (fun v1 v2 -> String.compare v1 v2 == 0) (fv_idents @ conseq_idents)
    else fv_idents
  in
  (* need to make ivars be global *)
  (* let conseq = if (!Globals.allow_field_ann) then meta_to_struc_formula iconseq0 false fv_idents None stab  *)
  let (n_tl,conseq) = meta_to_struc_formula iconseq0 false fv_idents  n_tl in
  (* let _ = print_endline ("conseq: " ^ (Cprinter.string_of_struc_formula conseq)) in *)
  (* let ante,conseq = transfrom_bexpr ante conseq n_tl in *)
  (* let conseq1 = meta_to_struc_formula iconseq0 false fv_idents stab in *)
  let conseq_fvs = CF.struc_fv conseq in
  let sst = List.fold_left (fun sst0 ((CP.SpecVar (t1, id1, p1)) as sv1) ->
      try
        let sv2 = List.find (fun (CP.SpecVar (t2, id2, p2)) -> String.compare id1 id2 = 0 &&
                p1=p2 && t1!=t2) conseq_fvs
        in
        sst0@[(sv1,sv2)]
      with _ ->  sst0
  ) [] fvs
  in
  (*let _ = print_endline "run_infer_one_pass" in*)
  let ante1 = CF.subst sst ante in
  let ante = Cfutil.transform_bexpr ante1 in
  let conseq = CF.struc_formula_trans_heap_node [] Cfutil.transform_bexpr conseq in
  let pr = Cprinter.string_of_struc_formula in
  let _ = x_tinfo_hp (add_str "conseq(after meta-)" pr) conseq no_pos in
  let orig_vars = CF.fv ante @ CF.struc_fv conseq in
  (* List of vars needed for abduction process *)
  let vars = List.map (fun v ->
      try
        let _ = Cast.look_up_hp_def_raw !cprog.Cast.prog_hp_decls v in
        CP.SpecVar (HpT, v, Unprimed)
      with _ ->
        Typeinfer.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos
  ) ivars in
  (* let ante,conseq = Cfutil.normalize_ex_quans_conseq !cprog ante conseq in *)
  let (res, rs,v_hp_rel) = x_add Sleekcore.sleek_entail_check 8 itype vars !cprog [] ante conseq in
  (* CF.residues := Some (rs, res); *)
  ((res, rs,v_hp_rel), (ante,conseq))

let run_infer_one_pass itype ivars (iante0 : meta_formula) (iconseq0 : meta_formula) =
  let pr = string_of_meta_formula in
  let pr1 = pr_list pr_id in
  let pr_2 = pr_triple string_of_bool Cprinter.string_of_list_context !CP.print_svl in
  let nn = (sleek_proof_counter#get) in
  let f x = wrap_proving_kind (PK_Sleek_Entail nn) (run_infer_one_pass itype ivars iante0) x in
  Debug.no_3 "run_infer_one_pass" pr1 pr pr (pr_pair pr_2 pr_none) (fun _ _ _ -> f iconseq0) ivars iante0 iconseq0

let process_term_assume (iante: meta_formula) (iconseq: meta_formula) =
  let stab = [] in
  let (stab, ante) = meta_to_formula iante false [] stab in
  let fvs = CF.fv ante in
  let fv_idents = List.map CP.name_of_spec_var fvs in
  let (stab, conseq) = meta_to_formula iconseq false fv_idents stab in
  let _ = Term.check_term_assume !cprog ante conseq in
  ()


let run_infer_one_pass_set_states itype (ivars: ident list) (iante0s : meta_formula list) (iconseq0 : meta_formula) =
  let run_infer_fct ante = run_infer_one_pass itype ivars ante iconseq0 in
  match iante0s with
    | [] -> report_error no_pos "empty state"
    | ante::rest ->
          let ((r0, rs0, v0), pr0) = run_infer_fct ante in
          let (r, list_rs) =
            List.fold_left (fun (acc_r, acc_rs) antei ->
                let ((ri, rsi,_),_) = run_infer_fct antei in
                (acc_r||ri, acc_rs@[rsi])
            ) (r0, [rs0]) rest
          in
          let comb_rs = CF.union_context_left list_rs in
          (* let _ = print_endline ("comb_rs: "^(Cprinter.string_of_list_context comb_rs)) in *)
          let _ = CF.residues := Some (comb_rs, r, !Globals.disable_failure_explaining) in
          ((r, comb_rs, v0), pr0)


let process_rel_assume cond_path (ilhs : meta_formula) (igurad_opt : meta_formula option) (irhs: meta_formula)=
  (* let _ = Debug.info_pprint "process_rel_assume" no_pos in *)
  (* let stab = H.create 103 in *)
  let stab = [] in
  let (stab,lhs) = meta_to_formula ilhs false [] stab in
  let fvs = CF.fv lhs in
  let fv_idents = (List.map CP.name_of_spec_var fvs) in
  let (stab,rhs) = meta_to_formula irhs false fv_idents stab in
  let rhs = CF.elim_exists rhs in
  let all_vs = fvs@(CF.fv rhs) in
  let fv_idents = (List.map CP.name_of_spec_var all_vs) in
  let (stab,lhs) = meta_to_formula ilhs false fv_idents stab in
  let lhs = CF.elim_exists lhs in
  let guard = match igurad_opt with
    | None -> None
    | Some iguard -> let (_,guard0) = meta_to_formula iguard false fv_idents stab in
      let guard1 = CF.elim_exists guard0 in
      let _, guard = CF.split_quantifiers guard1 in
      (* let _ = Debug.info_pprint (Cprinter.string_of_formula guard) no_pos in *)
      let p = CF.get_pure guard in
      let eq = (Mcpure.ptr_equations_without_null (Mcpure.mix_of_pure p)) in
      let guard1 = CF.subst eq guard in
      (* if CP.isConstTrue p then *)
        (* let hfs = CF.heap_of guard1 in *)
        (* CF.join_star_conjunctions_opt hfs *)
      Some guard1
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
  let _ = Debug.ninfo_zprint  (lazy  (Cprinter.string_of_hprel_short new_rel_ass)) no_pos in
  let _ = sleek_hprel_assumes := !sleek_hprel_assumes@[new_rel_ass] in
  ()

let process_rel_defn cond_path (ilhs : meta_formula) (irhs: meta_formula) extn_info=
  (* let _ = Debug.info_pprint "process_rel_assume" no_pos in *)
  (* let stab = H.create 103 in *)
  let stab = [] in
  let (stab,lhs) = meta_to_formula ilhs false [] stab in
  let fvs = CF.fv lhs in
  let fv_idents = (List.map CP.name_of_spec_var fvs) in
  let (stab,rhs) = meta_to_formula irhs false fv_idents stab in
  let rhs = CF.elim_exists rhs in
  let hfs = CF.heap_of lhs in
  let hf = match hfs with
    | [x] -> x
    | _ -> report_error no_pos "sleekengine.process_rel_defn: rel defn"
  in
  let hp,args = CF.extract_HRel hf in
  (* let _ =  print_endline ("LHS = " ^ (Cprinter.string_of_formula lhs)) in *)
  (* let _ =  print_endline ("RHS = " ^ (Cprinter.string_of_formula rhs)) in *)
  (*TODO: LOC: hp_id should be cond_path*)
  if extn_info = [] then
    let pr_new_rel_defn =  (cond_path, CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, List.hd args, List.tl args))  hf [(rhs, None)] None)
    in
    (*hp_defn*)
    (* let pr= pr_pair CF.string_of_cond_path Cprinter.string_of_hp_rel_def_short in *)
    (* let _ = Debug.ninfo_zprint  (lazy  ((pr pr_new_rel_defn) ^ "\n")) no_pos in *)
    let _ =  sleek_hprel_defns := ! sleek_hprel_defns@[pr_new_rel_defn] in
    ()
  else
    let rhs = Predicate. extend_pred_dervs iprog !cprog (List.map snd !sleek_hprel_defns) hp args extn_info in
    let r, others = Sautil.find_root (!cprog) [hp] args (CF.list_of_disjs rhs) in
    let exted_pred = CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, r, others))  hf [(rhs, None)] None in
    let _ = Cast.set_proot_hp_def_raw (Sautil.get_pos args 0 r) (!cprog).Cast.prog_hp_decls (CP.name_of_spec_var hp) in
    let pr_new_rel_defn =  (cond_path, exted_pred) in
    let _ = Debug.info_hprint  (add_str "extn pred:\n"  (Cprinter.string_of_hp_rel_def_short )) exted_pred no_pos in
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
  let _ = Debug.ninfo_zprint  (lazy  ("dangling: " ^
      (let pr = pr_list (pr_pair !Cpure.print_sv !Cpure.print_svl) in pr hpargs))) no_pos in
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
  let _ = Debug.ninfo_zprint  (lazy  (("unknown: " ^
      (let pr = pr_list (pr_pair CF.string_of_cond_path (pr_pair !Cpure.print_sv !Cpure.print_svl)) in pr hpargs)) ^ "\n")) no_pos in
  let _ = sleek_hprel_unknown := !sleek_hprel_unknown@hpargs in
  ()

let shape_infer_pre_process constrs pre_hps post_hps=
  let unk_hpargs = !sleek_hprel_dang in
  let link_hpargs = !sleek_hprel_unknown in
  (*** BEGIN PRE/POST ***)
  let orig_vars = List.fold_left (fun ls cs-> ls@(CF.fv cs.CF.hprel_lhs)@(CF.fv cs.CF.hprel_rhs)) [] !sleek_hprel_assumes in
  let pre_vars = List.map (fun v -> Typeinfer.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (pre_hps) in
  let post_vars = List.map (fun v -> Typeinfer.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (post_hps) in
  let pre_vars1 = (CP.remove_dups_svl pre_vars) in
  let post_vars1 = (CP.remove_dups_svl post_vars) in
  let infer_pre_vars,pre_hp_rels  = List.partition (fun sv ->
      let t = CP.type_of_spec_var sv in
      not ((* is_RelT t || *) is_HpT t )) pre_vars1 in
  let infer_post_vars,post_hp_rels  = List.partition (fun sv ->
      let t = CP.type_of_spec_var sv in
      not ((* is_RelT t || *) is_HpT t )) post_vars1 in
  (*END*)
  (* let infer_vars = infer_pre_vars@infer_post_vars in *)
  let sel_hps = pre_hp_rels@post_hp_rels in
  (* let sel_hps, sel_post_hps = Sautil.get_pre_post pre_hps post_hps constrs in *)
  (***END PRE/POST***)
  (* let constrs2, unk_map, unk_hpargs = Sacore.detect_dangling_pred hp_lst_assume sel_hps [] in *)
  let constrs2,unk_map = if unk_hpargs = [] then (constrs ,[]) else
    let unk_hps = List.map fst unk_hpargs in
    List.fold_left (fun (ls_cs,map) cs ->
      let new_cs, n_map,_ = Sacore.do_elim_unused cs unk_hps map in
      (ls_cs@[new_cs], n_map)
  ) ([], []) constrs
  in
  (constrs2, sel_hps, post_hp_rels, unk_map, unk_hpargs, link_hpargs)

let process_shape_infer pre_hps post_hps=
  (* let _ = Debug.info_pprint "process_shape_infer" no_pos in *)
  let hp_lst_assume = !sleek_hprel_assumes in
  let constrs2, sel_hps, sel_post_hps, unk_map, unk_hpargs, link_hpargs=
    shape_infer_pre_process hp_lst_assume pre_hps post_hps
  in
  let ls_hprel, ls_inferred_hps,_ =
    if List.length sel_hps> 0 && List.length hp_lst_assume > 0 then
      let infer_shape_fnc =  if not (!Globals.pred_syn_modular) then
        Sa2.infer_shapes
      else Sa3.infer_shapes (* Sa.infer_hps *)
      in
      infer_shape_fnc iprog !cprog "" constrs2
          sel_hps sel_post_hps unk_map unk_hpargs link_hpargs true false (!norm_flow_int)
    else [],[],[]
  in
  let _ =
    begin
      let rel_defs = if not (!Globals.pred_syn_modular) then
        Sa2.rel_def_stk
      else CF.rel_def_stk
      in
      if not(rel_defs# is_empty) then
        let defs0 = List.sort CF.hpdef_cmp (rel_defs # get_stk) in
        let pre_preds,post_pred,rem = List.fold_left ( fun (r1,r2,r3) d ->
            match d.CF.hprel_def_kind with
              | CP.HPRelDefn (hp,_,_) -> if (CP.mem_svl hp sel_post_hps) then (r1,r2@[d],r3) else
                  if (CP.mem_svl hp sel_hps) then (r1@[d],r2,r3) else (r1,r2,r3@[d])
              | _ -> (r1,r2,r3@[d]) ) ([],[],[]) defs0 in
        let defs = pre_preds@post_pred@rem in
        let defs1 = if !Globals.print_en_tidy then List.map Cfout.rearrange_def defs else defs in
        print_endline_quiet "";
      print_endline_quiet "\n*************************************";
      print_endline_quiet "*******relational definition ********";
      print_endline_quiet "*************************************";
      (* print_endline (rel_defs # string_of_reverse); *)
       let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
       print_endline_quiet (pr1 defs1);
      print_endline_quiet "*************************************"
    end
  in
  (* let _ = if(!Globals.cp_test || !Globals.cp_prefile) then *)
  (*    CEQ.cp_test !cprog hp_lst_assume ls_inferred_hps sel_hps *)
  (* in *)
  ()

let relation_pre_process constrs pre_hps post_hps=
  (*** BEGIN PRE/POST ***)
  let orig_vars = List.fold_left (fun ls cs-> ls@(CF.fv cs.CF.hprel_lhs)@(CF.fv cs.CF.hprel_rhs)) [] constrs in
  let pre_vars = List.map (fun v -> Typeinfer.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (pre_hps) in
  let post_vars = List.map (fun v -> Typeinfer.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (post_hps) in
  let pre_vars1 = (CP.remove_dups_svl pre_vars) in
  let post_vars1 = (CP.remove_dups_svl post_vars) in
  let infer_pre_vars,pre_hp_rels  = List.partition (fun sv ->
      let t = CP.type_of_spec_var sv in
      not ( is_RelT t )) pre_vars1 in
  let infer_post_vars,post_hp_rels  = List.partition (fun sv ->
      let t = CP.type_of_spec_var sv in
      not ( is_RelT t  )) post_vars1 in
  (*END*)
  (*pairs of (cpure.formula, rel name)*)
  let pre_invs, pre_constrs, post_constrs = List.fold_left (fun (r0,r1,r2) hprel ->
      match hprel.CF.hprel_kind with
        | CP.RelAssume _ -> begin
              let rhs_p =  CF.get_pure hprel.CF.hprel_rhs in
              try
                let rel = CP.name_of_rel_form rhs_p in
                if CP.mem_svl rel post_hp_rels then
                  r0,r1,r2@[(CF.get_pure hprel.CF.hprel_lhs, rhs_p)]
                else
                  if CP.isConstTrue rhs_p then
                    (r0@[(CF.get_pure hprel.CF.hprel_lhs)], r1, r2)
                  else
                    (r0, r1@[(CF.get_pure hprel.CF.hprel_lhs, rhs_p)], r2)
              with _ ->
                  if CP.isConstTrue rhs_p then
                    (r0@[(CF.get_pure hprel.CF.hprel_lhs)], r1, r2)
                  else (r0, r1@[(CF.get_pure hprel.CF.hprel_lhs, rhs_p)], r2)
          end
        | _ -> (r0,r1,r2)
  ) ([],[],[]) constrs in
  (pre_invs, pre_constrs, post_constrs,  pre_hp_rels, post_hp_rels)

let process_rel_infer pre_rels post_rels =
  (* let _ = Debug.info_pprint "process_rel_infer" no_pos in *)
  (*************INTERNAL*****************)
  let pr = !CP.print_formula in
  (* let compute_fixpoint_pre_rel rel_name rel_args pre_oblgs proc_spec= *)
  (*   let pre_rel = CP.mkRel rel_name (List.map (fun sv -> CP.mkVar sv no_pos) rel_args) no_pos in *)
  (*   let rec_oblgs,ini_oblgs = normalize_pre_oblgs rel_args rel_name pre_oblgs in *)
  (*   let pre_fixs = Fixpoint.pre_rel_fixpoint pre_rel [] [] FixcalCast.compute_fixpoint_td *)
  (*     ini_oblgs rel_args proc_spec rec_oblgs in *)
  (*   let _ = List.map (fun ( _,_, pre_rel,pre_def) -> *)
  (*       let _ = Debug.info_hprint (add_str "fixpoint for pre-rels" ( (pr_pair pr pr))) (pre_rel, pre_def) no_pos in *)
  (*       (pre_rel,pre_def) *)
  (*   ) pre_fixs in *)
  (*   () *)
  (* in *)
  (*************END INTERNAL*****************)
  let hp_lst_assume = !sleek_hprel_assumes in
  let proc_spec = CF.mkETrue_nf no_pos in
  (* let pre_invs0, pre_rel_constrs, post_rel_constrs, pre_rel_ids, post_rels = relation_pre_process hp_lst_assume pre_rels post_rels in *)
  let rels = Infer.infer_rel_stk # get_stk in
  let reloblgs, reldefns = List.partition (fun (rt,_,_) -> CP.is_rel_assume rt) rels in
  let is_infer_flow = Pi.is_infer_flow reldefns in
  let reldefns = if is_infer_flow then Pi.add_flow reldefns else List.map (fun (_,f1,f2) -> (f1,f2)) reldefns in
  let post_rels = List.map (fun id -> CP.mk_typed_spec_var (RelT []) id) post_rels in
  let _ = Debug.ninfo_hprint (add_str "reldefns" (pr_list (pr_pair pr pr))) reldefns no_pos in
  let post_rel_constrs, pre_rel_constrs = List.partition (fun (_,x) -> Pi.is_post_rel x post_rels) reldefns in
  let _ = Debug.ninfo_hprint (add_str "post_rel_constrs" (pr_list (pr_pair pr pr))) post_rel_constrs no_pos in
  (* let post_rel_constrs = post_rel_constrs@pre_rel_constrs in *)
  (* let post_rel_df,pre_rel_df = List.partition (fun (_,x) -> is_post_rel x post_vars) reldefns in *)
  (* let r = Fixpoint.rel_fixpoint_wrapper pre_invs0 [] pre_rel_constrs post_rel_constrs pre_rel_ids post_rels proc_spec 1 in *)
  (* let _ = Debug.info_hprint (add_str "fixpoint2" *)
  (*     (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_quad pr1 pr1 pr1 pr1))) r no_pos in *)
  (* let _ = print_endline "process_rel_infer" in *)
  let r = x_add Fixcalc.compute_fixpoint 2 post_rel_constrs post_rels proc_spec in
  let _ = Debug.info_hprint (add_str "fixpoint2"
      (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_pair pr1 pr1))) r no_pos in
  let _ = print_endline_quiet "" in
  ()

let process_shape_lfp sel_hps=
  (**********INTERNAL**********)
  let transfrom_assumption hp0 ls_pdefs cs=
    try
      let hp,args = CF.extract_HRel_f cs.CF.hprel_lhs in
      if CP.eq_spec_var hp0 hp then ls_pdefs@[(hp, args, cs.CF.hprel_rhs)]
      else ls_pdefs
    with _ -> ls_pdefs
  in
  (*******END INTERNAL ********)
  let ls_pdefs, defs = List.fold_left (fun (r1,r2) (_,hp_def) ->
      match hp_def.CF.def_cat with
        | CP.HPRelDefn (hp,_,_) -> let hp_name = CP.name_of_spec_var hp in
          if Gen.BList.mem_eq (fun s1 s2 -> String.compare s1 s2 =0) hp_name sel_hps then
            let _,args = CF.extract_HRel hp_def.CF.def_lhs in
            let pdefs = List.map (fun (f) -> (hp, args, f))
              (List.fold_left (fun r (f,_) -> r@(CF.list_of_disjs f)) [] hp_def.CF.def_rhs) in
            (r1@[pdefs], r2)
          else (r1,r2@[hp_def])
        | _ -> (r1,r2@[hp_def])
  ) ([],[]) (!sleek_hprel_defns) in
  let _ = Debug.ninfo_hprint ( add_str "  ls_pdefs (lfp): " (pr_list_ln (pr_list_ln (pr_triple !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula)))) ls_pdefs no_pos in
  let unk_hps = List.map (fun (_,(hp,_)) -> hp) (!sleek_hprel_unknown) in
  let hp_defs = List.map (Sacore.compute_lfp !cprog unk_hps defs) ls_pdefs in
  let _ = print_endline_quiet "" in
  let _ = print_endline_quiet "\n*************************************" in
  let _ = print_endline_quiet "*******lfp definition ********" in
  let _ = print_endline_quiet "*************************************" in
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def_short in
  let _ = print_endline_quiet (pr1 hp_defs) in
  let _ = print_endline_quiet "*************************************" in
  ()

let process_shape_rec sel_hps=
  (**********INTERNAL**********)
  let transfrom_assumption hp0 ls_pdefs cs=
    try
      let hp,args = CF.extract_HRel_f cs.CF.hprel_rhs in
      if CP.eq_spec_var hp0 hp then ls_pdefs@[(hp, args, cs.CF.hprel_lhs)]
      else ls_pdefs
    with _ -> ls_pdefs
  in
  let transform_to_hpdef pdefs=
    match pdefs with
      | [] -> report_error no_pos "sleekengine. process_shape_rec"
      | [(hp,args,f)] -> let def_cat = (CP.HPRelDefn (hp, List.hd args, List.tl args)) in
        {CF.def_cat = def_cat;
        CF.def_lhs = (CF.HRel (hp, List.map (fun sv -> CP.mkVar sv no_pos) args, no_pos));
        CF.def_rhs = List.map (fun f0 -> (f0,None)) (CF.list_of_disjs f);
        CF.def_flow = None;
        }
      | (hp,args0,f)::rest ->
            let fs = List.map (fun (_,args1, f1) ->
                let sst = List.combine args1 args0 in
                CF.subst sst f1
            ) rest in
            {CF.def_cat= (CP.HPRelDefn (hp, List.hd args0, List.tl args0));
             CF.def_lhs= (CF.HRel (hp, List.map (fun sv -> CP.mkVar sv no_pos) args0, no_pos));
             CF.def_rhs = List.map (fun f0 -> (f0,None)) (f::fs);
             CF.def_flow = None;
            }
  in
  (*******END INTERNAL ********)
  let _ = Debug.info_hprint (add_str  "  sleekengine " pr_id) "process_lfp\n" no_pos in
  let hp_lst_assume = !sleek_hprel_assumes in
  let constrs2, sel_hps, _, _, _, link_hpargs=
    shape_infer_pre_process hp_lst_assume sel_hps []
  in
  let ls_pdefs = List.map (fun hp ->
      List.fold_left (transfrom_assumption hp) [] constrs2
  ) sel_hps in
  let unk_hps = List.map (fun (_, (hp,_)) -> hp) link_hpargs in
  (* let defs = List.map snd !sleek_hprel_defns in *)
  let hp_defs = List.map (transform_to_hpdef) ls_pdefs in
  let _ = sleek_hprel_defns := !sleek_hprel_defns@(List.map (fun a -> ([],a)) hp_defs) in
  let _ = print_endline_quiet "" in
  let _ = print_endline_quiet "\n*************************************" in
  let _ = print_endline_quiet "*******recurrence ********" in
  let _ = print_endline_quiet "*************************************" in
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def_short in
  let _ = print_endline_quiet (pr1 hp_defs) in
  let _ = print_endline_quiet "*************************************" in
  ()

let process_validate exp_res opt_fl ils_es =
  if not !Globals.show_unexpected_ents then () else
  (**********INTERNAL**********)
  let preprocess_constr act_idents act_ti (ilhs, irhs)=
    let (n_tl,lhs) = meta_to_formula ilhs false act_idents act_ti in
    let fvs = CF.fv lhs in
    let fv_idents = (List.map CP.name_of_spec_var fvs) in
    let (_, rhs) = meta_to_formula irhs false (fv_idents@act_idents) n_tl in
    (lhs,rhs)
  in
  let preprocess_iestate act_vars (iguide_vars, ief, iconstrs) =
    let act_idents = (List.map CP.name_of_spec_var act_vars) in
    let act_ti = List.fold_left (fun ls (CP.SpecVar(t,sv,_)) ->
              let vk = Typeinfer.fresh_proc_var_kind ls t in
              ls@[(sv,vk)]
    ) [] act_vars in
    let (n_tl,es_formula) = meta_to_formula ief false (act_idents) act_ti in
    let orig_vars = CF.fv es_formula in
    let guide_vars = List.map (fun v -> Typeinfer.get_spec_var_type_list_infer (v, Unprimed) (orig_vars@act_vars) no_pos)
      iguide_vars in
    let constrs = List.map (preprocess_constr act_idents act_ti) iconstrs in
    (guide_vars, es_formula, constrs)
  in
  (*******END INTERNAL ********)
  (* let _ = Debug.info_hprint (add_str  "  sleekengine " pr_id) "process_validate\n" no_pos in *)
  let nn = (sleek_proof_counter#get) in
  let validate_id = "Validate " ^ (string_of_int nn) ^": " in
  let res_str = ref "" in
  (*get current residue -> FAIL? VALID*)
  let rs = !CF.residues in
  let a_r, ls_a_es, act_vars = match !CF.residues with
    | None ->
          let _ = res_str := "Expecting "^(string_of_vres exp_res)^"BUT got no residue" in
          let _ = unexpected_cmd := !unexpected_cmd @ [nn] in
          (*   if (exp_res = "Fail") *)
          (*   then *)
          (*     res_str := "Expected.\n" *)
          (*   else *)
          (*     let _ = unexpected_cmd := !unexpected_cmd @ [nn] in *)
          (*     res_str :=  "Not Expected.\n" *)
          (* in *)
          (**res = Fail*)
          false, [], []
    | Some (lc, res, ldfa) -> 
          begin (*res*)
            let res, fls = proc_sleek_result_validate res lc in
            let unexp =
              match res, exp_res with
                | VR_Valid, VR_Valid -> None
                | VR_Fail n1, VR_Fail n2 -> 
                      if n2==0 then None
                      else if n1==n2 then None
                      else Some( "Expecting"^(string_of_vres exp_res)^" BUT got : "^(string_of_vres res))
                | _,_ -> Some ("Expecting 3 "^(string_of_vres exp_res)^" BUT got : "^(string_of_vres res))
            in
            let _ = match unexp with
              | None -> begin
                  match opt_fl with
                    | None -> res_str := "OK" (*do not compare expect flow *)
                    | Some id -> if not !Globals.enable_error_as_exc then res_str := "OK" else
                          let reg = Str.regexp "\#E" in
                          let res_fl_ids = List.map (fun ff ->
                          let fl_w_sharp = exlist # get_closest ff.CF.formula_flow_interval in
                          Str.global_replace reg "" fl_w_sharp
                      ) fls in
                      let _ = Debug.ninfo_hprint (add_str "res_fl_ids" (pr_list pr_id)) res_fl_ids no_pos in
                      if List.exists (fun id1 -> string_compare id1 id) res_fl_ids then
                        res_str := "OK"
                      else
                        let _ = unexpected_cmd := !unexpected_cmd @ [nn] in
                        res_str := ( "Expecting flow "^(id))
                end
              | Some s -> 
                    let _ = unexpected_cmd := !unexpected_cmd @ [nn] in
                    res_str := s
            in
            match lc with 
              | CF.SuccCtx cl ->
                    let ls_a_es = List.fold_left (fun ls_es ctx -> ls_es@(CF.flatten_context ctx)) [] cl in
                    let act_vars = List.fold_left (fun ls es -> ls@(CF.es_fv es)) [] ls_a_es in
                    (true, ls_a_es, CP.remove_dups_svl act_vars)
              |  _ -> (false,[],[])
            (* match lc with *)
            (*   | CF.FailCtx _ -> *)
            (*         let _ = *)
            (*           if ((res && exp_res = "Valid") || (not res && exp_res = "Fail") || *)
            (*               (CF.is_must_failure lc && exp_res = "Fail_Must") || *)
            (*               (not (CF.is_bot_failure lc) && exp_res = "Fail_May"))  *)
            (*             (\* if (exp_res = "Fail") *\) *)
            (*           then *)
            (*             res_str := "Expected.\n" *)
            (*           else  *)
            (*             let _ = unexpected_cmd := !unexpected_cmd @ [nn] in *)
            (*             res_str := "Not Expected.\n" *)
            (*         in *)
            (*         (false, [], []) *)
            (*   | CF.SuccCtx cl -> *)
            (*         let ls_a_es = List.fold_left (fun ls_es ctx -> ls_es@(CF.flatten_context ctx)) [] cl in *)
            (*         let act_vars = List.fold_left (fun ls es -> ls@(CF.es_fv es)) [] ls_a_es in *)
            (*         let _ = *)
            (*           if ((res && exp_res = "Valid") || (not res && exp_res = "Fail")) *)
            (*           then *)
            (*             res_str := "Expected.\n" *)
            (*           else *)
            (*             let _ = unexpected_cmd := !unexpected_cmd @ [nn] in *)
            (*             res_str := "Not Expected.\n" *)
            (*         in *)
            (*         (true, ls_a_es, CP.remove_dups_svl act_vars) *)
      end
  in
  let _ = print_string (validate_id ^ !res_str) in
  (*expect: r = FAIL? Valid*)
  (* let ex_r = if String.compare r "Valid" == 0 then true else *)
  (*   if String.compare r "FAIL" == 0 then false else *)
  (*     report_error no_pos "SLEEKENGINE.process_validate: expected result should be Valid or FAIL" *)
  (* in *)
  let ex_r = true in
  let _ = match a_r, ex_r with
    | false, true
    | true, false -> (* let _ = print_endline (validate_id ^ "FAIL.") in *) ()
    | false, false -> (* let _ = print_endline (validate_id ^ "SUCCast.") in *) ()
    | true, true ->
          (*syn new unknown preds generated between cprog and iprog*)
          let inew_hprels = Saout.syn_hprel !cprog.Cast.prog_hp_decls iprog.I.prog_hp_decls in
          let _ = iprog.I.prog_hp_decls <- (iprog.I.prog_hp_decls@inew_hprels) in
          (*for each succ context: validate residue + inferred results*)
          let ls_expect_es = List.map (preprocess_iestate act_vars) ils_es in
          let b, es_opt, ls_fail_ass = Sleekcore.validate ls_expect_es ls_a_es in
          (* let _ = if b then *)
          (*   print_endline (validate_id ^ "SUCCast.") *)
          (* else *)
          (*   print_endline (validate_id ^ "FAIL.") *)
          (* in *) ()
  in
  let _ = print_endline_quiet ("\n") in
  ()

let process_shape_divide pre_hps post_hps=
   (* let _ = Debug.info_pprint "process_shape_divide" no_pos in *)
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
  let ls_cond_danghps_constrs = Sacore.partition_constrs_4_paths link_hpargs hp_lst_assume in
  let pr_one (cond, _,constrs)=
    begin
      if constrs <> [] then
        let _ = print_endline_quiet ("Group: " ^ (CF.string_of_cond_path cond)) in
        print_endline_quiet ((pr_list_ln Cprinter.string_of_hprel_short) constrs)
    end
  in
  let _ = List.iter pr_one ls_cond_danghps_constrs in
  ()

let process_shape_conquer sel_ids cond_paths=
  let _ = Debug.ninfo_pprint "process_shape_conquer\n" no_pos in
  let ls_pr_defs = !sleek_hprel_defns in
  let link_hpargs = !sleek_hprel_unknown in
  let (* defs *) _ =
    (* if not (!Globals.pred_syn_modular) then *)
      let orig_vars = List.fold_left (fun ls (_,d)-> ls@(CF.h_fv d.CF.def_lhs)) [] ls_pr_defs in
      let sel_hps = List.map (fun v -> Typeinfer.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (sel_ids) in
      let sel_hps  = List.filter (fun sv ->
          let t = CP.type_of_spec_var sv in
          ((* is_RelT t || *) is_HpT t )) sel_hps in
      let ls_path_link = Sautil.dang_partition link_hpargs in
      let ls_path_defs = Sautil.defn_partition ls_pr_defs in
      (*pairing*)
      let ls_path_link_defs = Sautil.pair_dang_constr_path ls_path_defs ls_path_link
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
        print_endline_quiet "";
      print_endline_quiet "\n*************************************";
      print_endline_quiet "*******relational definition ********";
      print_endline_quiet "*************************************";
      (* print_endline (rel_defs # string_of_reverse); *)
       let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
       print_endline_quiet (pr1 defs);
      print_endline_quiet "*************************************"
    end
  in
  ()

let process_shape_postObl pre_hps post_hps=
   let hp_lst_assume = !sleek_hprel_assumes in
  let constrs2, sel_hps, sel_post_hps, unk_map, unk_hpargs, link_hpargs=
    shape_infer_pre_process hp_lst_assume pre_hps post_hps
  in
  let grp_link_hpargs = Sautil.dang_partition link_hpargs in
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
        print_endline_quiet "";
      print_endline_quiet "\n************************************************";
      print_endline_quiet "*******relational definition (obligation)********";
      print_endline_quiet "**************************************************";
      print_endline_quiet (pr ls_hprel);
      print_endline_quiet "*************************************"
    end
  in
  ()

let process_shape_sconseq pre_hps post_hps=
  (* let _ = Debug.info_pprint "process_shape_infer" no_pos in *)
  let hp_lst_assume = !sleek_hprel_assumes in
  let (* sel_hps *)_ , (* sel_post_hps *) _ = Sautil.get_pre_post pre_hps post_hps hp_lst_assume in
  let constrs1 = Sacore.do_strengthen_conseq !cprog [] hp_lst_assume in
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let _ =
  begin
    print_endline_quiet "\n*************************************";
    print_endline_quiet "*******relational assumptions (1) ********";
    print_endline_quiet "*************************************";
    print_endline_quiet (pr1 constrs1);
    print_endline_quiet "*************************************";
  end;
  in
  (* let _ = if(!Globals.cp_test || !Globals.cp_prefile) then *)
  (*    CEQ.cp_test !cprog hp_lst_assume ls_inferred_hps sel_hps *)
  (* in *)
  ()

let process_shape_sante pre_hps post_hps=
  (* let _ = Debug.info_pprint "process_shape_infer" no_pos in *)
  let hp_lst_assume = !sleek_hprel_assumes in
  let (* sel_hps *) _ , (* sel_post_hps *) _ = Sautil.get_pre_post pre_hps post_hps hp_lst_assume in
  let constrs1 = Sacore.do_strengthen_ante !cprog [] hp_lst_assume in
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let _ =
  begin
    print_endline_quiet "\n*************************************";
    print_endline_quiet "*******relational assumptions (1) ********";
    print_endline_quiet "*************************************";
    print_endline_quiet (pr1 constrs1);
    print_endline_quiet "*************************************";
  end;
  in
  (* let _ = if(!Globals.cp_test || !Globals.cp_prefile) then *)
  (*    CEQ.cp_test !cprog hp_lst_assume ls_inferred_hps sel_hps *)
  (* in *)
  ()

let process_pred_split ids=
  let _ = Debug.info_hprint (add_str "process_pred_split" pr_id) "\n" no_pos in
  let unk_hps = List.map (fun (_, (hp,_)) -> hp) (!sleek_hprel_unknown) in
  let unk_hps = (List.map (fun (hp,_) -> hp) (!sleek_hprel_dang))@ unk_hps in
  (*find all sel pred def*)
  let sel_hp_defs = List.fold_left (fun r (_,def) ->
      match def.CF.def_cat with
        | CP.HPRelDefn (hp,_,_) -> let hp_name = CP.name_of_spec_var hp in
          if Gen.BList.mem_eq (fun id1 id2 -> String.compare id1 id2 = 0) hp_name ids then (r@[def]) else r
        | _ -> r
  ) [] !sleek_hprel_defns in
  let hp_defs1, split_map = Sacore.pred_split_hp iprog !cprog unk_hps Infer.rel_ass_stk Cformula.rel_def_stk sel_hp_defs in
  let _ = if split_map = [] then () else
    (*print*)
    let _ = print_endline_quiet ("\n" ^((pr_list_ln Cprinter.string_of_hp_rel_def) hp_defs1)) in
    ()
  in
  ()

let process_norm_seg ids=
  let _ = Debug.info_hprint (add_str "process_pred_norm_seg" pr_id) "\n" no_pos in
  let unk_hps = List.map (fun (_, (hp,_)) -> hp) (!sleek_hprel_unknown) in
  let unk_hps = (List.map (fun (hp,_) -> hp) (!sleek_hprel_dang))@ unk_hps in
  (*find all sel pred def*)
  let sel_hp_defs = List.fold_left (fun r (_,def) ->
      match def.CF.def_cat with
        | CP.HPRelDefn (hp,_,_) -> let hp_name = CP.name_of_spec_var hp in
          if Gen.BList.mem_eq (fun id1 id2 -> String.compare id1 id2 = 0) hp_name ids then (r@[def]) else r
        | _ -> r
  ) [] !sleek_hprel_defns in
  (* let hp_defs1, split_map = Sacore.pred_split_hp iprog !cprog unk_hps Infer.rel_ass_stk Cformula.rel_def_stk sel_hp_defs in *)
  (* let _ = if split_map = [] then () else *)
  (*   (\*print*\) *)
  (*   let _ = print_endline ("\n" ^((pr_list_ln Cprinter.string_of_hp_rel_def) hp_defs1)) in *)
  (*   () *)
  (* in *)
  ()

let process_pred_norm_disj ids=
  let _ = Debug.info_hprint (add_str "process_pred_split" pr_id) "\n" no_pos in
  (* let unk_hps = List.map (fun (_, (hp,_)) -> hp) (!sleek_hprel_unknown) in *)
  (* let unk_hps = (List.map (fun (hp,_) -> hp) (!sleek_hprel_dang))@ unk_hps in *)
  (*find all sel pred def*)
  let sel_hp_defs = List.fold_left (fun r (_,def) ->
      match def.CF.def_cat with
        | CP.HPRelDefn (hp,_,_) -> let hp_name = CP.name_of_spec_var hp in
          if Gen.BList.mem_eq (fun id1 id2 -> String.compare id1 id2 = 0) hp_name ids then (r@[def]) else r
        | _ -> r
  ) [] !sleek_hprel_defns in
  ()

let process_shape_infer_prop pre_hps post_hps=
  (* let _ = Debug.info_pprint "process_shape_infer_prop" no_pos in *)
  let hp_lst_assume = !sleek_hprel_assumes in
  (*get_dangling_pred constrs*)
  let constrs2, sel_hps, sel_post_hps, unk_map, unk_hpargs, link_hpargs=
    shape_infer_pre_process hp_lst_assume pre_hps post_hps
  in
  let ls_hprel, (* ls_inferred_hps *) _ ,_=
    let infer_shape_fnc =  if not (!Globals.pred_syn_modular) then
      Sa2.infer_shapes
    else Sa3.infer_shapes (* Sa.infer_hps *)
    in
    infer_shape_fnc iprog !cprog "" hp_lst_assume
        sel_hps sel_post_hps unk_map unk_hpargs link_hpargs false false (!norm_flow_int)
  in
  let _ = if not (!Globals.pred_syn_modular) then
    begin
      let rel_defs =  Cformula.rel_def_stk in
      if not(rel_defs# is_empty) then
        print_endline_quiet "";
      print_endline_quiet "\n*************************************";
      print_endline_quiet "*******relational definition ********";
      print_endline_quiet "*************************************";
      print_endline_quiet (Cformula.rel_def_stk # string_of_reverse);
      print_endline_quiet "*************************************"
    end
  in
  (* let _ = if(!Globals.cp_test || !Globals.cp_prefile) then *)
  (*    CEQ.cp_test !cprog hp_lst_assume ls_inferred_hps sel_hps *)
  (* in *)
  ()

let process_shape_split pre_hps post_hps=
  (* let _, sel_post_hps = Sautil.get_pre_post pre_hps post_hps !sleek_hprel_assumes in *)
  (*get infer_vars*)
  let orig_vars = List.fold_left (fun ls cs-> ls@(CF.fv cs.CF.hprel_lhs)@(CF.fv cs.CF.hprel_rhs)) [] !sleek_hprel_assumes in
  let pre_vars = List.map (fun v -> Typeinfer.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (pre_hps) in
  let post_vars = List.map (fun v -> Typeinfer.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) (post_hps) in
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
  let constrs1, unk_map, unk_hpargs = Sacore.detect_dangling_pred !sleek_hprel_assumes sel_hp_rels [] in
   let link_hpargs = !sleek_hprel_unknown in
   let grp_link_hpargs = Sautil.dang_partition link_hpargs in
    let link_hpargs = match grp_link_hpargs with
    | [] -> []
    | (_, a)::_ -> a
  in
   let cond_path = [] in
  let new_constrs,_,_ = Sa3.split_base_constr !cprog cond_path constrs1 post_hp_rels sel_hp_rels 
    infer_vars unk_map (List.map fst unk_hpargs) (List.map fst link_hpargs) in
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  begin
    print_endline_quiet "\n*************************************";
    print_endline_quiet "*******relational assumptions (1) ********";
    print_endline_quiet "*************************************";
    print_endline_quiet (pr1 new_constrs);
    print_endline_quiet "*************************************";
  end;
  ()

let process_shape_elim_useless sel_vnames=
  let view_defs = Norm.norm_elim_useless !cprog.Cast.prog_view_decls sel_vnames in
  let _ = !cprog.Cast.prog_view_decls <- view_defs in
  let pr = pr_list_ln Cprinter.string_of_view_decl in
  let _ = Debug.info_zprint  (lazy  ("views after ELIM: \n" ^ (pr view_defs))) no_pos in
  ()

let process_shape_extract sel_vnames=
  let view_defs = Norm.norm_extract_common iprog !cprog !cprog.Cast.prog_view_decls sel_vnames in
  let _ = !cprog.Cast.prog_view_decls <- view_defs in
  let pr = pr_list_ln Cprinter.string_of_view_decl in
  let _ = x_tinfo_zp  (lazy  ("views after EXTRACTION: \n" ^ (pr view_defs))) no_pos in
  ()

(* the value of flag "exact" decides the type of entailment checking              *)
(*   None       -->  forbid residue in RHS when the option --classic is turned on *)
(*   Some true  -->  always check entailment exactly (no residue in RHS)          *)
(*   Some false -->  always check entailment inexactly (allow residue in RHS)     *)
let run_entail_check (iante0 : meta_formula list) (iconseq0 : meta_formula) (etype: entail_type) =
  wrap_classic etype (fun conseq ->
      let (r, (cante, cconseq)) = run_infer_one_pass_set_states [] [] iante0 conseq in
      (*let _ = print_endline "run_entail_check_2" in*)
      let res, _, _ = r in
      let _ = if !Globals.gen_smt then
         let _ = Slk2smt.smt_ent_cmds := !Slk2smt.smt_ent_cmds@[(iante0, iconseq0, etype, cante, cconseq, res)] in
         ()
       else () in
      r
  ) iconseq0

let run_entail_check (iante0 : meta_formula list) (iconseq0 : meta_formula) (etype: entail_type) =
  let with_timeout =
    let fctx = CF.mkFailCtx_in (CF.Trivial_Reason
      (CF.mk_failure_may "timeout" Globals.timeout_error, [])) (CF.Ctx (CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled  no_pos)) (CF.mk_cex false) in
    (false, fctx,[]) in
  (*let _ = print_endline "run_entail_check_1" in*)
  Procutils.PrvComms.maybe_raise_and_catch_timeout_sleek
    (run_entail_check iante0 iconseq0) etype with_timeout

let run_entail_check (iante : meta_formula list) (iconseq : meta_formula) (etype: entail_type) =
  let pr = string_of_meta_formula in
  let pr_2 = pr_triple string_of_bool Cprinter.string_of_list_context !CP.print_svl in
  Debug.no_2 "run_entail_check" (pr_list pr) pr pr_2 (fun _ _ -> run_entail_check iante iconseq etype) iante iconseq

let print_entail_result sel_hps (valid: bool) (residue: CF.list_context) (num_id: string):bool =
  Debug.ninfo_hprint (add_str "residue: " !CF.print_list_context) residue no_pos;
  Debug.ninfo_hprint (add_str "valid: " string_of_bool) valid no_pos;
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
          let final_error_opt = CF.get_final_error residue in
          match final_error_opt with
            | Some (s, fk) -> begin
                match fk with
                  | CF.Failure_May _ -> "(may) cause:"^s
                  | CF.Failure_Must _ -> "(must) cause:"^s
                  | _ -> "INCONSISTENCY : expected failure but success instead"
              end
            | None -> "INCONSISTENCY : expected failure but success instead"
          (* match CF.get_must_failure residue with *)
          (*   | Some (s, cex) -> *)
          (*         (\* let reg1 = Str.regexp "base case unfold failed" in *\) *)
          (*         (\* let _ = try *\) *)
          (*         (\*   if Str.search_forward reg1 s 0 >=0 then *\) *)
          (*         (\*     let _ = smt_is_must_failure := (Some false) in () *\) *)
          (*         (\*   else let _ = smt_is_must_failure := (Some true) in *\) *)
          (*         (\*   () *\) *)
          (*         (\* with _ -> let _ = smt_is_must_failure := (Some true) in () *\) *)
          (*         (\* in *\) *)
          (*         let is_sat,ns = Cformula.cmb_fail_msg ( "(must) cause:"^s) cex in *)
          (*         let _ = smt_is_must_failure := (Some is_sat) in *)
          (*         ns *)
          (*   | _ -> (match CF.get_may_failure residue with *)
          (*       | Some (s, cex) -> begin *)
          (*             (\* try *\) *)
          (*             (\*   let reg1 = Str.regexp "Nothing_to_do" in *\) *)
          (*             (\*   let _ = if Str.search_forward reg1 s 0 >=0 then *\) *)
          (*             (\*     let _ = smt_is_must_failure := (Some false) in () *\) *)
          (*             (\*   else *\) *)
          (*             (\*     if is_lem_syn_reach_bound () then *\) *)
          (*             (\*       let _ = smt_is_must_failure := (Some false) in () *\) *)
          (*             (\*     else *\) *)
          (*             (\*       () *\) *)
          (*             (\*   in *\) *)
          (*           let is_sat,ns = Cformula.cmb_fail_msg ( "(may) cause:"^s) cex in *)
          (*           let _ = smt_is_must_failure := (Some is_sat) in *)
          (*           ns *)
          (*               (\* with _ -> *\) *)
          (*             (\*     let _ = smt_is_must_failure := (Some false) in *\) *)
          (*             (\*     "(may) cause:"^s *\) *)
          (*         end *)
          (*       | None -> "INCONSISTENCY : expected failure but success instead" *)
          (*     ) *)
                  (*should check bot with is_bot_status*)
        else ""
      in
      (* Get the timeout message *)
      let timeout = 
        if !Globals.sleek_timeout_limit > 0. then
          match CF.get_may_failure residue with
            | Some ("timeout",_) -> " (timeout) "
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
      if t_valid then
         let _ = (* if !Globals.smt_compete_mode then print_string "UNSAT" else *)
          silenced_print print_string (num_id^": Valid. "^s^"\n"^term_output^"\n")
        in
        true
      else
        begin
          let _ = (* if !Globals.smt_compete_mode then print_string "SAT" else *)
            Log.last_cmd # dumping "sleek_dump(fail2)";
            silenced_print print_string (num_id^": Fail. "^s^"\n"^term_output^"\n")
          in
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
      (* (\* let _ = Debug.info_zprint  (lazy  (" sel_hps:" ^ (!CP.print_svl sel_hps))) no_pos in *\) *)
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
  let _ = Log.last_cmd # dumping "sleek_dump(exception)" in
  let _ = smt_is_must_failure := (Some false) in
  let _ = silenced_print print_string (num_id^": EXCast. "^s^"\n") in
  ()

let print_sat_result (unsat: bool) (sat:bool) (num_id: string) =
  let res =
    if unsat then "UNSAT\n\n"
    else if sat then "SAT\n\n"
    else "UNKNOWN\n\n"
  in silenced_print print_string (num_id^": "^res); flush stdout

let print_entail_result sel_hps (valid: bool) (residue: CF.list_context) (num_id: string):bool =
  let pr0 = string_of_bool in
  let pr = !CF.print_list_context in
  Debug.no_2 "print_entail_result" pr0 pr (fun _ -> "")
    (fun _ _ -> print_entail_result sel_hps valid residue num_id) valid residue

let print_exc (check_id: string) =
  print_backtrace_quiet ();
  dummy_exception() ;
  print_string_quiet ("exception caught " ^ check_id ^ " check\n")

let process_sat_check_x (f : meta_formula) =
  let nn = (sleek_proof_counter#inc_and_get) in
  let num_id = "\nCheckSat "^(string_of_int nn) in
  let (_,f) = meta_to_formula f false [] [] in
  let f = Cvutil.prune_preds !cprog true f in
  let unsat_command f = not(x_add Solver.unsat_base_nth 7 !cprog (ref 0) f) in
  let res = x_add Solver.unsat_base_nth 1 !cprog (ref 0) f in
  let sat_res =
    if res then false
    else wrap_under_baga unsat_command f (* WN: invoke SAT checking *)
  in print_sat_result res sat_res num_id

let process_sat_check (f : meta_formula) =
  let pr = string_of_meta_formula in
  Debug.no_1 "process_sat_check" pr (fun _ -> "?") process_sat_check_x f

let process_nondet_check (v: ident) (mf: meta_formula) =
  if (!Globals.print_input || !Globals.print_input_all) then (
    print_endline_quiet ("Check_nondet:\n ### var = " ^ v ^"\n ### formula = " ^ (string_of_meta_formula mf));
  );
  let (_,f) = meta_to_formula mf false [] [] in
  let pf = CF.get_pure f in
  let res = CP.check_non_determinism v pf in
  let nn = (sleek_proof_counter#inc_and_get) in
  let res_str = if res then "Valid" else "Fail" in
  let msg = "\nNondet constraint " ^ (string_of_int nn) ^ ": " ^ res_str ^ "." in
  print_endline_quiet msg
  
(* the value of flag "exact" decides the type of entailment checking              *)
(*   None       -->  forbid residue in RHS when the option --classic is turned on *)
(*   Some true  -->  always check entailment exactly (no residue in RHS)          *)
(*   Some false -->  always check entailment inexactly (allow residue in RHS)     *)
let process_entail_check_x (iante : meta_formula list) (iconseq : meta_formula) (etype : entail_type) =
  let nn = (sleek_proof_counter#inc_and_get) in
  let num_id = "\nEntail "^(string_of_int nn) in
    try
      let valid, rs, _(*sel_hps*) =
        wrap_proving_kind (PK_Sleek_Entail nn) (run_entail_check iante iconseq) etype in
      print_entail_result [] (*sel_hps*) valid rs num_id
    with ex ->
        let exs = (Printexc.to_string ex) in
        let _ = print_exception_result exs (*sel_hps*) num_id in
		let _ = if !VarGen.trace_failure then
		  (print_string "caught\n"; print_backtrace_quiet ()) else () in
        (* (\* let _ = print_string "caught\n"; Printexc.print_backtrace stdout in *\) *)
        (* let _ = print_string ("\nEntailment Problem "^num_id^(Printexc.to_string ex)^"\n")  in *)
        false
  (* with e -> print_exc num_id *)

(* the value of flag "exact" decides the type of entailment checking              *)
(*   None       -->  forbid residue in RHS when the option --classic is turned on *)
(*   Some true  -->  always check entailment exactly (no residue in RHS)          *)
(*   Some false -->  always check entailment inexactly (allow residue in RHS)     *)
let process_entail_check (iante : meta_formula list) (iconseq : meta_formula) (etype: entail_type) =
  let pr = string_of_meta_formula in
  Debug.no_2 "process_entail_check_helper" (pr_list pr) pr (fun _ -> "?") process_entail_check_x iante iconseq etype

let process_templ_solve (idl: ident list) = 
  Template.collect_and_solve_templ_assumes !cprog idl

(* Solving termination relation assumptions in Sleek *)  
let process_term_infer () =
  begin
    Ti.solve !should_infer_tnt true !cprog; 
    Ti.finalize ();
    should_infer_tnt := true
  end

let process_check_norm_x (f : meta_formula) =
  let nn = "(" ^ (string_of_int (sleek_proof_counter#inc_and_get)) ^ ") " in
  let num_id = "\nCheckNorm " ^ nn in  
  let () = if (!Globals.print_input || !Globals.print_input_all) 
    then print_endline_quiet ("INPUT 7: \n ### f = " ^ (string_of_meta_formula f)) 
    else () 
  in
  let _ = x_dinfo_pp ("\nprocess_check_norm:" ^ "\n ### f = "^(string_of_meta_formula f)  ^"\n\n") no_pos in
  let (n_tl, cf) = meta_to_formula f false [] []  in
  let _ = if (!Globals.print_core || !Globals.print_core_all) then print_endline_quiet ("INPUT 8: \n ### cf = " ^ (Cprinter.string_of_formula cf)) else () in
  let estate = (CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos) in
  let newf = x_add Solver.prop_formula_w_coers 1 !cprog estate cf (Lem_store.all_lemma # get_left_coercion) in
  let _ = print_string (num_id ^ ": " ^ (Cprinter.string_of_formula newf) ^ "\n\n") in
  () (* TO IMPLEMENT*)

let process_check_norm (f : meta_formula) =
  let pr = string_of_meta_formula in
  Debug.no_1 "process_check_norm" pr (fun _ -> "?") process_check_norm_x f

let process_eq_check (ivars: ident list)(if1 : meta_formula) (if2 : meta_formula) =
  (*let _ = print_endline ("\n Compare Check") in*)
  let nn = "("^(string_of_int (sleek_proof_counter#inc_and_get))^") " in
  let num_id = "\nCheckeq "^nn in  
  let _ = if (!Globals.print_input || !Globals.print_input_all) then print_endline_quiet ("INPUT 9: \n ### if1 = " ^ (string_of_meta_formula if1) ^"\n ### if2 = " ^ (string_of_meta_formula if2)) else () in
  let _ = x_dinfo_pp ("\nrun_cmp_check:"
                              ^ "\n ### f1 = "^(string_of_meta_formula if1)
                              ^ "\n ### f2 = "^(string_of_meta_formula if2)
                              ^"\n\n") no_pos in
  
  let (n_tl,f1) = meta_to_formula_not_rename if1 false [] []  in
  let (n_tl,f2) = meta_to_formula_not_rename if2 false [] n_tl  in

  let _ = if (!Globals.print_core || !Globals.print_core_all) then print_endline_quiet ("INPUT 3: \n ### formula 1= " ^ (Cprinter.string_of_formula f1) ^"\n ### formula 2= " ^ (Cprinter.string_of_formula f2)) else () in

  (*let f2 = Solver.prune_preds !cprog true f2 in *)
  if(not !Globals.dis_show_diff) then(
      let _ = Debug.ninfo_hprint (add_str "BEFORE" pr_id) "2" no_pos in
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
      let _ = if(res) then Debug.info_zprint  (lazy  (CEQ.string_of_map_table (List.hd mt_list) ^ "\n")) no_pos in
      ()
  )

let print_result f m =
      print_endline_quiet (((add_str m Cprinter.string_of_pure_formula) f)^"\n")

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

let process_infer itype (ivars: ident list) (iante0 : meta_formula) (iconseq0 : meta_formula) etype =
  let nn = "("^(string_of_int (sleek_proof_counter#inc_and_get))^") " in
  let is_tnt_flag = List.mem INF_TERM itype in
  (* combine local vs. global of failure explaining *)
  let dfailure_anlysis = if List.mem INF_EFA itype then false else
    if List.mem INF_DFA itype then true else !Globals.disable_failure_explaining
  in
  let old_dfa = !Globals.disable_failure_explaining in
  let _ = Globals.disable_failure_explaining := dfailure_anlysis in
  let num_id = "\nEntail "^nn in
  let r=  try
      let (valid, rs, sel_hps),_ = wrap_classic etype (run_infer_one_pass_set_states itype ivars [iante0]) iconseq0 in
      let res = print_entail_result sel_hps valid rs num_id in
      let _ = if is_tnt_flag then should_infer_tnt := !should_infer_tnt && res in
      (*   match itype with *)
      (* | Some INF_TERM -> should_infer_tnt := !should_infer_tnt && res *)
      (* | _ -> ()  *)
      (* in  *)
      res
    with ex -> 
        (* print_exc num_id *)
        (if !VarGen.trace_failure then (print_string "caught\n"; print_backtrace_quiet ()));
        let _ = print_string ("\nEntail "^nn^": "^(Printexc.to_string ex)^"\n") in
        let _ = if is_tnt_flag then should_infer_tnt := false in
        (*   let _ = match itype with *)
        (* | Some INF_TERM -> should_infer_tnt := false *)
        (* | _ -> ()  *)
        false
  in
  let _ = Globals.disable_failure_explaining := old_dfa in
  r

let process_capture_residue (lvar : ident) =
	let flist = match !CF.residues with
      | None -> [(CF.mkTrue (CF.mkTrueFlow()) no_pos)]
      | Some (ls_ctx, print, _) -> CF.list_formula_of_list_context ls_ctx in
		put_var lvar (Sleekcommons.MetaFormLCF flist)

let process_print_command pcmd0 =
  match pcmd0 with
  | PVar pvar ->
	  let mf = try get_var pvar with Not_found->  Error.report_error {
                   Error.error_loc = no_pos;
                   Error.error_text = "couldn't find " ^ pvar;
                 }in
	  let (n_tl,pf) = meta_to_struc_formula mf false [] [] in
		print_string ((Cprinter.string_of_struc_formula pf) ^ "XXXHello\n")
  | PCmd pcmd ->
	if pcmd = "lemmas" then
          Lem_store.all_lemma # dump
	else if pcmd = "residue" then
          let _ = Debug.ninfo_pprint "inside residue" no_pos in
          print_residue !CF.residues
          (* match !CF.residues with *)
          (*   | None -> print_string ": no residue \n" *)
          (*         (\* | Some s -> print_string ((Cprinter.string_of_list_formula  *\) *)
          (*         (\*       (CF.list_formula_of_list_context s))^"\n") *\) *)
          (*         (\*print all posible outcomes and their traces with numbering*\) *)
          (*   | Some (ls_ctx, print) -> *)
          (*         if (print) then *)
          (*           (\* let _ = print_endline (Cprinter.string_of_list_context ls_ctx) in *\) *)
          (*           print_string ((Cprinter.string_of_numbered_list_formula_trace_inst !cprog *)
          (*               (CF.list_formula_trace_of_list_context ls_ctx))^"\n" ); *)
	else
	  print_string ("unsupported print command: " ^ pcmd)

let process_cmp_command (input: ident list * ident * meta_formula list) =
  let iv,var,fl = input in
  if var = "residue" then
    match !CF.residues with
      | None -> print_string ": no residue \n"
      | Some (ls_ctx, print, _) -> begin
        if (print) then begin
      	  if(List.length fl = 1) then (
      	    let f = List.hd fl in
      	    let cfs = CF.list_formula_of_list_context ls_ctx in
      	    let cf1 = (List.hd cfs) in (*if ls-ctx has exacly 1 ele*)
      	    let (n_tl,cf2) = meta_to_formula_not_rename f false [] []  in
      	    let _ = Debug.info_zprint  (lazy  ("Compared residue: " ^ (Cprinter.string_of_formula cf2) ^ "\n")) no_pos in
      	    let res,mt = CEQ.checkeq_formulas iv cf1 cf2 in
      	    if(res) then  print_string ("EQUAL\n") else  print_string ("NOT EQUAL\n")
      	  )
	        else print_string ("ERROR: Input is 1 formula only\n")
	      end
      end
  else if (var = "assumption") then(
    match !CF.residues with
      | None -> print_string ": no residue \n"
      | Some (ls_ctx, print, _) ->(
        if (print) then (
	  if(List.length fl = 2) then (
	    let f1,f2 = (List.hd fl, List.hd (List.tl fl)) in	    
	    let (n_tl,cf11) = meta_to_formula_not_rename f1 false [] []  in
	    let (n_tl,cf12) = meta_to_formula_not_rename f2 false [] n_tl  in
	    let _ = Debug.info_zprint  (lazy  ("Compared assumption: " ^ (Cprinter.string_of_formula cf11) ^ ", " ^ (Cprinter.string_of_formula cf12) ^ "\n")) no_pos in
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

let get_residue () = !CF.residues

let get_residue () =
  Debug.no_1 "get_residue" pr_no (pr_opt pr_no) get_residue ()
  (*match !CF.residues with*)
    (*| None -> ""*)
    (*| Some s -> Cprinter.string_of_list_formula (CF.list_formula_of_list_context s)*)

let meta_constr_to_constr (meta_constr: meta_formula * meta_formula): (CF.formula * CF.formula) = 
  let if1, if2 = meta_constr in  
  let (n_tl,f1) = meta_to_formula_not_rename if1 false [] []  in
  let (n_tl,f2) = meta_to_formula_not_rename if2 false [] n_tl  in
  (f1,f2)

