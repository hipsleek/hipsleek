open Globals
open Solver
open Cast

module CF = Cformula
module CP = Cpure
module U = Util
module TP = Tpdispatcher
module PTracer = Prooftracer

let log_spec = ref ""
  (* checking expression *)
let flow_store = ref ([] : CF.flow_store list)

let num_para = ref (1)
let sort_input = ref false
let webserver = ref false

let parallelize num =
  num_para := num

(* assumes the pre, and starts the simbolic execution*)
let rec check_specs (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) spec_list e0 : bool = 
  let rec do_spec_verification (spec: Cformula.ext_formula):bool = 
    (*let _ = print_string (Cprinter.string_of_ext_formula spec) in*)
    let pos_spec = CF.pos_of_struc_formula [spec] in
      log_spec := (Cprinter.string_of_ext_formula spec) ^ ", Line " ^ (string_of_int pos_spec.start_pos.Lexing.pos_lnum);	 
      match spec with
	| Cformula.ECase b -> List.for_all (fun (c1,c2)-> 
					      let nctx = CF.transform_context (combine_es_and prog c1 true) ctx in
					      let r = check_specs prog proc nctx c2 e0 in
						(*let _ = Debug.devel_pprint ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n") pos_spec in*)
						r) b.Cformula.formula_case_branches
	| Cformula.EBase b ->
	    let nctx = 
	      if !Globals.max_renaming 
	      then (CF.transform_context (CF.normalize_es b.Cformula.formula_ext_base b.Cformula.formula_ext_pos false) ctx)
	      else (CF.transform_context (CF.normalize_clash_es b.Cformula.formula_ext_base b.Cformula.formula_ext_pos false) ctx) in
	    let r = check_specs prog proc nctx b.Cformula.formula_ext_continuation e0 in
	      (*let _ = Debug.devel_pprint ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n") pos_spec in*)
	      r
	| Cformula.EAssume (x,b,y) ->
	    let ctx1 = CF.transform_context (elim_unsat_es prog (ref 1)) ctx in
	      (*let _ = print_string ("\n pre eli : "^(Cprinter.string_of_context ctx)^"\n post eli: "^(Cprinter.string_of_context ctx1)^"\n") in*)
	      if (Cformula.isAnyFalseCtx ctx1) then
		let _ = print_string ("False precondition detected in procedure "^proc.proc_name^"\n with context: "^
					(Cprinter.string_of_context ctx)) in 
		  true
	      else
		let _ = Util.push_time ("method "^proc.proc_name) in
		  try 
		    let r = 
		      flow_store := [];
		      let ctx1 = CF.set_flow_in_context_override
			{ CF.formula_flow_interval = !n_flow_int; CF.formula_flow_link = None} ctx1 in
		      let ctx1 = CF.add_path_id ctx1 (Some y,-1) in
		      let lpc = [CF.mk_partial_context ctx1 []] in 
			(* print_string ("\n ***PRECOND:" ^ (Cprinter.string_of_list_partial_context lpc) ^ "\n"); *)
			(* print_string ("\nLength of List Partial Ctx: " ^ (Cprinter.string_of_list_partial_context(lpc)));  *)
			let res_ctx = check_exp prog proc lpc e0 y in
			  (* print_string ("\nLength of List Partial Ctx: " ^ (Cprinter.string_of_list_partial_context(res_ctx)));  *)
			  (*if CP.are_same_types proc.proc_return void_type then*)
			  (* void procedures may not contain a return in all branches,
			     so we need to make a catch-all check at the end of the body *)
			  (*let _ = print_string ("finalr : "^(Cprinter.string_of_context_list res_ctx)^"\n") in*)
			let res_ctx = Cformula.change_ret_flow_partial_ctx res_ctx in
			  (* print_string ("\n ***List of partial ctx before POST-CHECK:" ^ (Cprinter.string_of_list_partial_context lpc) ^ "\n"); *)
			  if (CF.isFailListPartialCtx res_ctx) then false
			  else
			    let tmp_ctx = check_post prog proc res_ctx b (Cformula.pos_of_formula b) y in
			      (CF.isSuccessListPartialCtx tmp_ctx) 
		    in
		      (*let _ = Debug.devel_pprint ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n") pos_spec in*)
		    let _ = Util.pop_time ("method "^proc.proc_name) in
		      r
		  with _ as e -> 
		    let _ = Util.pop_time ("method "^proc.proc_name) in raise e
  in	
    List.for_all do_spec_verification spec_list

and check_exp (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_partial_context) e0 (post_start_label:formula_label) : CF.list_partial_context = 
  if (exp_to_check e0) then 
    (*let _ = if (List.exists Cformula.isFalseCtx ctx) then 
      print_string ("\n expr: "^
      (Cprinter.string_of_exp e0)
      ^"\n false ctx: "^(Cprinter.string_of_pos (Cast.pos_of_exp e0))^" "^(Cprinter.string_of_context_list ctx)^"\n") in*)
    Cformula.find_false_list_partial_ctx ctx (Cast.pos_of_exp e0)
  else ();
  let check_exp1 (ctx : CF.list_partial_context) : CF.list_partial_context = 
    match e0 with
	(* for theorem proving *)
	(* | Label e ->  *)
	(* 	  let ctx = CF.add_path_id_ctx_partial_list ctx e.exp_label_path_id in *)
	(* 	    (check_exp prog proc ctx e.exp_label_exp post_start_label) *)
      | Unfold ({exp_unfold_var = sv;
		 exp_unfold_pos = pos}) -> begin
	  let res = unfold_partial_context (Prog prog) ctx sv true pos in
	    res
	end
	  (* for code *)
      | Assert ({exp_assert_asserted_formula = c1_o;
		 exp_assert_assumed_formula = c2;
		 exp_assert_path_id = (pidi,s);
		 exp_assert_pos = pos}) -> begin
	  (*let _ =print_string ("inside assert"^(match c1_o with | None -> "no formula "| Some c1_o ->Cprinter.string_of_struc_formula c1_o)^"\n") in*)
	  (* let s1 = CF.get_start_partial_label ctx in *)
          let s1 = snd post_start_label in
	    if (String.length s)>0 && (String.length s1)>0 && (String.compare s s1 <> 0)  then (print_string "inside label missmatch \n";ctx)
	    else
	      let new_ctx = match c1_o with
		| None -> ctx
		| Some c1 ->
		    (*
		      let _ = print_string ("[typechecker.ml, line 62, assert]: pre to be entailed " ^ (Cprinter.string_of_formula c1) ^ "\n") in
		      let _ = print_string ("[typechecker.ml, line 63, assert]: context before entailment:\n" ^ (Cprinter.string_of_context_list ctx) ^ "\n\n") in
		    *)
		    let to_print = "Proving assert/assume in method " ^ proc.proc_name ^ " for spec: \n" ^ !log_spec ^ "\n" in	
		      Debug.devel_pprint to_print pos;
		      let rs,prf = heap_entail_struc_list_partial_context_init prog false false false ctx c1 pos None in
			(* print_string ("AAA :"^Cprinter.string_of_list_partial_context rs); *)
		      let _ = PTracer.log_proof prf in
			Debug.pprint ("assert condition:\n" ^ (Cprinter.string_of_struc_formula c1)) pos;
			(* Solver.entail_hist#upd (pidi,s) rs; *)
			if not(CF.isFailListPartialCtx rs)
			then
			  (* Debug.print_info "assert" ("assert ok\n") pos; *)
			  (Debug.pprint ("Residual:\n" ^ (Cprinter.string_of_list_partial_context rs)) pos; rs)
			else (* Debug.print_info "assert" ("assert failed\n") pos; *)
			  rs
			    (*ctx*) in
		if CF.isFailListPartialCtx new_ctx then 
	          begin 
                    Debug.print_info "assert/assume" ("has failed\n") pos; 
		    new_ctx
		  end
		else
		  match c2 with
		    | None -> Err.report_error {Err.error_loc = pos; Err.error_text = "assert/assume should not be here; it should have been handled earlier!"}
		    | Some c ->
			(let assumed_ctx = CF.normalize_max_renaming_list_partial_context c pos false new_ctx in
			   (*print_int (!Omega.test_number);*)
			 let ret =CF.transform_list_partial_context ((elim_unsat_es prog (ref 1)),(fun c->c)) assumed_ctx in
			   (*print_int
			     (!Omega.test_number);*)
			   ret)
			  (* match c2 with *)
			  (*   | None -> Err.report_error {Err.error_loc = pos; Err.error_text = "assert/assume should not be here; it should have been handled earlier!"} *)
			  (*   | Some c -> *)
			  (*       Debug.pprint ("assume condition:\n" ^ (Cprinter.string_of_formula c)) pos; *)
			  (*       if not(CF.isFailListPartialCtx new_ctx) then *)
			  (* 	let assumed_ctx = CF.normalize_max_renaming_list_partial_context c pos false new_ctx in *)
			  (* 	  (\*print_int (!Omega.test_number);*\) *)
			  (* 	let ret =CF.transform_list_partial_context ((elim_unsat_es prog (ref 1)),(fun c->c)) assumed_ctx in *)
			  (* 	  (\*print_int (!Omega.test_number);*\) *)
			  (* 	  ret *)
			  (*       else new_ctx *)
	end
      | Assign ({exp_assign_lhs = v;
		 exp_assign_rhs = rhs;
		 exp_assign_pos = pos}) -> begin
	  (*let _ = print_string ("-> pre ass : "^(Cprinter.string_of_pos pos)^" "^(Cprinter.string_of_context_list ctx)^"\n") in*)
	  let ctx1 = check_exp prog proc ctx rhs post_start_label (*flow_store*) in
	    (*  let _ = print_string ("-> pre assert : "^(Cprinter.string_of_pos pos)^"\n"^(Cprinter.string_of_context_list ctx1)^"\n") in*)
	    (* Debug.devel_pprint ("delta at beginning of assignment to " ^ v ^ ":\n" ^ (string_of_constr delta) ^ "\n") pos; *)
	  let fct c1 = 
	    if (CF.subsume_flow_f !n_flow_int (CF.flow_formula_of_formula c1.CF.es_formula)) then 
	      let t = U.unsome (type_of_exp rhs) in
	      let vsv = CP.SpecVar (t, v, Primed) in (* rhs must be non-void *)
	      let link = CF.formula_of_pure (CP.mkEqVar vsv (P.mkRes t) pos) pos in
	      let tmp_ctx1 = CF.compose_context_formula (CF.Ctx c1) link [vsv] CF.Flow_combine pos in
	      let tmp_ctx2 = CF.push_exists_context [CP.mkRes t] tmp_ctx1 in
	      let resctx = if !Globals.elim_exists then elim_exists_ctx tmp_ctx2 else tmp_ctx2 in
		resctx 
	    else (CF.Ctx c1) in
	  let r = CF.transform_list_partial_context (fct,(fun c->c)) ctx1 in
	    (*let _ = print_string ("-> post assert : "^(Cprinter.string_of_context_list r)^"\n") in*)
	    r
	end
      | BConst ({exp_bconst_val = b;
		 exp_bconst_pos = pos}) -> begin
	  let res_v = CP.mkRes bool_type in
	  let tmp1 = CP.BForm (CP.BVar (res_v, pos), None) in
	  let tmp2 =
	    if b then tmp1
	    else CP.Not (tmp1, None, pos) in
	  let f = CF.formula_of_pure tmp2 pos in
	  let res_ctx = CF.normalize_max_renaming_list_partial_context f pos true ctx in
	    
	    res_ctx
	end
      | Bind ({exp_bind_type = body_t;
	       exp_bind_bound_var = (v_t, v);
	       exp_bind_fields = lvars;
	       exp_bind_body = body;
	       exp_bind_path_id = pid;
	       exp_bind_pos = pos}) -> begin
	  (* Debug.devel_pprint ("bind: delta at beginning of bind\n" ^ (string_of_constr delta) ^ "\n") pos; *)
	  let field_types, vs = List.split lvars in
	  let v_prim = CP.SpecVar (v_t, v, Primed) in
	  let vs_prim = List.map2 (fun v -> fun t -> CP.SpecVar (t, v, Primed)) vs field_types in
	  let p = CP.fresh_spec_var v_prim in
	    (*--- 09.05.2000 *)
	    (*let _ = (print_string ("\n[typechecker.ml, line 116]: fresh name = " ^ (Cprinter.string_of_spec_var p) ^ "!!!!!!!!!!!\n")) in*)
	    (*09.05.2000 ---*)
	  let link_pv = CF.formula_of_pure
	    (CP.mkAnd (CP.mkEqVar v_prim p pos) (CP.BForm (CP.mkNeq (CP.Var (p, pos)) (CP.Null pos) pos, None)) pos) pos in
	    (*let _ = print_string ("[typechecker.ml, check__exp]: link_pv: " ^ Cprinter.string_of_formula link_pv ^ "\n") in*)
	    (*	  let link_pv = CF.formula_of_pure (CP.mkEqVar v_prim p pos) pos in *)
	  let tmp_ctx =
	    if !Globals.large_bind then
	      CF.normalize_max_renaming_list_partial_context link_pv pos false ctx
	    else ctx in
	  let unfolded = unfold_partial_context (Prog prog) tmp_ctx v_prim true pos in
	    (* let unfolded_prim = if !Globals.elim_unsat then elim_unsat unfolded else unfolded in *)
	  let _ = Debug.devel_pprint ("bind: unfolded context:\n"
				      ^ (Cprinter.string_of_list_partial_context unfolded)
				      ^ "\n") pos in
	    (* let _ = Debug.devel_pprint ("bind: unfolded formula after eliminating unsatisfiable disjuncts:\n"
	       ^ (string_of_constr unfolded) ^ "\n") pos in *)
	  let c = CP.name_of_type v_t in
	    (*--- 09.05.2000 *)
	    (* change performed on 09.04.2008 *)
	    (* before: *)
	    (*let fn1 = fresh_name () in
	      let fn2 = fresh_name () in
	      let _ = (print_string ("\n[typechecker.ml, line 132]: fresh name = " ^ fn1 ^ "!!!!!!!!!!!\n")) in
	      let _ = (print_string ("\n[typechecker.ml, line 133]: fresh name = " ^ fn2 ^ "!!!!!!!!!!!\n")) in
	      let ext_var = CP.SpecVar (CP.OType c, fn1, Unprimed) in
	      let t_var = CP.SpecVar (CP.OType c, fn2, Unprimed) in*)
	    (*09.05.2008 ---*)
	    (* 09.06.08*)
	    (*let ext_var = CP.SpecVar (CP.OType c, c, Unprimed) in*)
	    (*let t_var = CP.SpecVar (CP.OType c, c, Unprimed) in*)
	  let vdatanode = CF.DataNode ({CF.h_formula_data_node = (if !Globals.large_bind then p else v_prim);
					CF.h_formula_data_name = c;
					CF.h_formula_data_arguments = (*t_var :: ext_var ::*) vs_prim;
					CF.h_formula_data_label = None;
					CF.h_formula_data_pos = pos}) in
	  let vheap = CF.formula_of_heap vdatanode pos in
	  let to_print = "Proving binding in method " ^ proc.proc_name ^ " for spec " ^ !log_spec ^ "\n" in
	    Debug.devel_pprint to_print pos;
	    (*  let _ = print_string "pint ++2\n" in*)
	    let rs_prim, prf = heap_entail_list_partial_context_init prog false false  unfolded vheap pos pid in
	      (*let _ = print_string "pint 2\n" in*)
	    let _ = PTracer.log_proof prf in
	    let rs = CF.clear_entailment_history_partial_list rs_prim in
	      (* Solver.entail_hist#upd_opt pid rs ("No label for BIND at line"  ^ (string_of_int pos.start_pos.Lexing.pos_lnum)); *)
              if (CF.isFailListPartialCtx rs) then   
		(* Err.report_error {Err.error_loc = pos; Err.error_text = "bind: node " ^ (Cprinter.string_of_h_formula vdatanode) ^ " cannot be derived from context"} *)
		begin
		  Debug.print_info ("("^(Cprinter.get_label_list_partial_context rs)^") ") ("bind: node " ^ (Cprinter.string_of_h_formula vdatanode) ^ " cannot be derived from context\n") pos; (* add branch info *)
		  rs
		    (* Err.report_error { Err.error_loc = pos; *)
		    (* 			 Err.error_text = "no precondition is satisfied"} *)
		end

              else 
		begin
		  let process_one cc =
		    let tmp_res1 = check_exp prog proc [cc] body post_start_label in 
		    let tmp_res2 = CF.normalize_max_renaming_list_partial_context vheap pos true tmp_res1 in
		    let tmp_res3 = CF.push_exists_list_partial_context vs_prim tmp_res2 in
		    let res =if !Globals.elim_exists then elim_exists_partial_ctx_list tmp_res3
		    else tmp_res3 in
		      res 
		  in
		  let tmp_res = List.concat (List.map process_one rs) in
		    tmp_res
		end

	(* ( match rs with *)
	(*     | CF.FailCtx _ -> *)
	(* 	  Err.report_error {Err.error_loc = pos; *)
	(* 			    Err.error_text = "bind: node " ^ (Cprinter.string_of_h_formula vdatanode) ^ " cannot be derived from context"} *)
	(*     | CF.SuccCtx sl -> *)
	(* 	  let process_one cc = *)
	(* 	    let tmp_res1 = check_exp prog proc (CF.SuccCtx[cc]) body in  *)
	(* 	    let tmp_res2 = CF.normalize_max_renaming vheap pos true tmp_res1 in *)
	(* 	    let tmp_res3 = CF.push_exists_list_context vs_prim tmp_res2 in *)
	(* 	    let res =if !Globals.elim_exists then elim_exists_ctx_list tmp_res3 *)
	(* 	    else tmp_res3 in *)
	(* 	      (\* Debug.devel_pprint ("bind: delta1:\n" ^ (string_of_constr delta1) ^ "\n") pos; *)
	(* 		 Debug.devel_pprint ("bind: delta2:\n" ^ (string_of_constr delta2) ^ "\n") pos; *)
	(* 		 Debug.devel_pprint ("bind: delta3:\n" ^ (string_of_constr delta3) ^ "\n") pos; *)
	(* 		 Debug.devel_pprint ("bind: after existential quantifier elimination:\n" *)
	(* 		 ^ (string_of_constr resform) ^ "\n") pos; *\) *)
	(* 	      res in *)
	(* 	  let tmp_res = CF.fold_context_left (List.map process_one sl) in *)
	(* 	    tmp_res *)
	(* ) *)
	end;
      | Block ({exp_block_type = t;
		exp_block_body = e;
		exp_block_local_vars = local_vars;
		exp_block_pos = pos}) -> begin
	  (*let ctx = add_path_id_ctx_list ctx (pid,0) in*)
	  let ctx1 = check_exp prog proc ctx e post_start_label (*flow_store*) in
	  let svars = List.map (fun (t, n) -> CP.SpecVar (t, n, Primed)) local_vars in
	  let ctx2 = CF.push_exists_list_partial_context svars ctx1 in
	  let ctx3 = if !Globals.elim_exists then elim_exists_partial_ctx_list ctx2 else ctx2 in
	    (* let _, tmp1 = List.split local_vars in *)
	    (*		print_string ("local_vars:\n" ^ (String.concat ", " tmp1) ^ "\n"); *)
	    ctx3
	end
	  (*
	    | Cast ({exp_cast_target_type = target_t;
	    exp_cast_body = body;
	    exp_cast_pos = pos}) -> begin
	    end
	  *)
      | Cond ({exp_cond_type = t;
	       exp_cond_condition = v;
	       exp_cond_then_arm = e1;
	       exp_cond_else_arm = e2;
	       exp_cond_path_id =pid;
	       exp_cond_pos = pos}) -> begin
	  let then_cond_prim = CP.BForm (CP.mkBVar v Primed pos, None) in
	  let else_cond_prim = CP.mkNot then_cond_prim None pos in
	  let then_ctx = combine_list_partial_context_and_unsat_now prog ctx then_cond_prim in
	    Debug.devel_pprint ("conditional: then_delta:\n" ^ (Cprinter.string_of_list_partial_context then_ctx)) pos;
	    let else_ctx =combine_list_partial_context_and_unsat_now prog ctx else_cond_prim in
	      Debug.devel_pprint ("conditional: else_delta:\n" ^ (Cprinter.string_of_list_partial_context else_ctx)) pos;
	      (* let then_ctx1 = CF.add_cond_label_list_partial_context pid 0 then_ctx in *)
	      (* let else_ctx1 = CF.add_cond_label_list_partial_context pid 1 else_ctx in *)
	      let then_ctx2 = check_exp prog proc then_ctx e1 post_start_label in
	      let else_ctx2 = check_exp prog proc else_ctx e2 post_start_label in
	      let res = CF.list_partial_context_or then_ctx2 else_ctx2 in
		(* print_string ("\nBefore THEN  :"^(Cprinter.summary_list_partial_context then_ctx)); *)
		(* print_string ("\nBefore THEN  :"^(Cprinter.summary_list_partial_context then_ctx2)); *)
		(* 	(\* print_string ("THEN "^Cprinter.string_of_list_partial_context(then_ctx2)); *\) *)
		(* 	(\* print_string ("ELSE "^Cprinter.string_of_list_partial_context(else_ctx2)); *\) *)
		(* 	print_string ("\nJOIN "^Cprinter.summary_list_partial_context(res)); *)
 		(* print_string ("End JOIN"); *)
		res
	end;
      | Debug ({exp_debug_flag = flag;
		exp_debug_pos = pos}) -> begin
	  (if flag then Omega.log_mark "debug on"
	   else Omega.log_mark "debug off");
	  Debug.devel_debug_on := flag;
	  ctx
	end;

      | ICall ({exp_icall_receiver = recv;
		exp_icall_receiver_type = recv_t; (* this is the type of the receiver *)
		exp_icall_type = ret_t; (* this is the return type *)
		exp_icall_method_name = mn;
		exp_icall_arguments = vs_prim;
		exp_icall_visible_names = p_svars;
		exp_icall_pos = pos}) ->
	  Err.report_error {Err.error_loc = pos;
			    Err.error_text = "[typechecker.ml]: We do not support instant calls"}
	    (* commented out on 09.06.08: we don't care about ICall for now --> it can be removed
	       begin (* mn is mingled name of the method *)
	       let check_conjunct ctx proc specs : CF.context list =
	       let vs = recv :: vs_prim in (* actual arguments, including receiver *)
	       let fargs = (recv_t, "this") :: proc.proc_args in (* formal ones, including this *)
	       let farg_names = List.map snd fargs in
	       let farg_types = List.map fst fargs in
	       let farg_spec_vars = List.map2
	       (fun n -> fun t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
 	       let actual_spec_vars = List.map2
	       (fun n -> fun t -> CP.SpecVar (t, n, Unprimed)) vs farg_types in
	       let check_pre_post (org_pre, org_post) =
	       let free_vars = CP.difference (CF.fv org_pre) farg_spec_vars in
	       let free_vars_fresh = CP.fresh_spec_vars free_vars in
	    (*let _ = (print_string ("\n[typechecker.ml, line 281]: fresh name = " ^ (Cprinter.string_of_spec_var_list free_vars_fresh) ^ "!!!!!!!!!!!\n")) in*)
	    (* -- 16.05.2008 *)
	       let renamed_pre =
	       if !Globals.max_renaming then (CF.rename_bound_vars org_pre)
	       else (fst (CF.rename_clash_bound_vars org_pre (CF.formula_of_context ctx)))
	       in
	       let renamed_post =
	       if !Globals.max_renaming then (CF.rename_bound_vars org_post)
	       else (fst (CF.rename_clash_bound_vars org_post (CF.formula_of_context ctx)))
	    (* 16.05.2008 -- *)
	       in
	    (* before : *)
	    (*let renamed_pre = CF.rename_bound_vars org_pre in*)
	    (*let renamed_post = CF.rename_bound_vars org_post in*)
	       let st1 = List.combine free_vars free_vars_fresh in
	       let fr_vars = farg_spec_vars @ (List.map CP.to_primed farg_spec_vars) in
	       let to_vars = actual_spec_vars @ (List.map CP.to_primed actual_spec_vars) in
	       let tmp_pre = CF.subst st1 renamed_pre in
	       let tmp_post = CF.subst st1 renamed_post in
	       let pre = CF.subst_avoid_capture fr_vars to_vars tmp_pre in
	       let post = CF.subst_avoid_capture fr_vars to_vars tmp_post in
	       let st2 = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) actual_spec_vars in
	       let pre2 = CF.subst st2 pre in
	       let rs_prim, prf = heap_entail prog false [ctx] pre2 pos in
	       let _ = PTracer.log_proof prf in
	       let rs = CF.clear_entailment_history_list rs_prim in
	    (*
	       let _ = print_string ("\nctx at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_context_list ctx) ^ "\n") in
	       let _ = print_string ("\nrs at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_context_list rs) ^ "\n") in
	       let _ = print_string ("\npre2 at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_formula pre2) ^ "\n")  in
	    *)
	       let xpure_pre2_prim = xpure_consumed_pre prog pre2 in
	    (*
	       let xpure_pre2_prim = xpure prog pre2 in
	    *)
	       let xpure_pre2_sec = CP.mkExists p_svars xpure_pre2_prim pos in
	       let xpure_pre2 =
	       if !Globals.hull_pre_inv then TP.hull xpure_pre2_sec
	       else TP.simplify xpure_pre2_sec in
	    (*
	       let _ = print_string ("xpure_pre2 at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_pure_formula xpure_pre2) ^ "\n") in
	       let _ = print_string ("p_svars at call: " ^ mn ^ ":\n"
	       ^ (String.concat ", " (List.map CP.name_of_spec_var p_svars)) ^ "\n") in
	    *)
	       let process_one c =
	       let r = CP.subst_var_list_avoid_capture fr_vars to_vars proc.proc_by_name_params in
	       let w = actual_spec_vars in
	       let v = CP.difference w r in
	       let nox_v = CF.no_change v pos in
	       let nox_v_pre = CP.mkAnd nox_v xpure_pre2 pos in
	       let tmp_f =
	       if !Globals.max_renaming then CF.normalize post (CF.formula_of_pure nox_v_pre pos) pos
	       else CF.normalize_only_clash_rename post (CF.formula_of_pure nox_v_pre pos) pos
	       in
	    (*
	       let _ = print_string ("\nnox_v_pre at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_pure_formula nox_v_pre) ^ "\n") in
	       let _ = print_string ("\npost at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_formula post) ^ "\n") in
	       let _ = print_string ("\ntmp_f at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_formula tmp_f) ^ "\n") in
	    *)
	       let tmp_res = CF.compose_context_formula c tmp_f w pos in
	    (*
	       let _ = print_string ("\ntmp_res at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_context tmp_res) ^ "\n") in
	       let _ = print_string ("\nunsat_tmp_f at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_formula (elim_unsat_all prog tmp_f)) ^ "\n") in
	    *)
	       let tmp_res1 =
	       if !Globals.elim_exists then elim_exists_ctx tmp_res
	       else tmp_res in
	    (*
	       let _ = print_string ("\ntmp_res1 at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_context tmp_res1) ^ "\n") in
	       let _ = Omega.log_mark ("res_unsat: " ^ mn) in
	    *)
	       let res =
	       if !Globals.elim_unsat then Solver.elim_unsat_ctx prog tmp_res1
	       else tmp_res1 in
	    (*
	       let _ = Omega.log_mark ("res_unsat_end: " ^ mn) in
	       let _ = print_string ("\nres at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_context res) ^ "\n") in
	    *)
	       res in
	       let res = List.map process_one rs in
	       res in
	       let tmp_res = List.map check_pre_post proc.proc_static_specs in
	       let res = List.concat tmp_res in
	    (*
	       let _ = print_string ("\nres at call: " ^ mn ^ ":\n"
	       ^ (Cprinter.string_of_context_list res) ^ "\n") in
	    *)
	       if U.empty res then
	       Err.report_error {Err.error_loc = pos;
	       Err.error_text = "no precondition is satisfied"}
	       else
	       res in
	       let rec check_one_context ctx = match ctx with
	       | CF.OCtx (c1, c2) ->
	       let rs1 = check_one_context c1 in
	       let rs2 = check_one_context c2 in
	       rs1 @ rs2
	       | CF.Ctx estate -> begin
	       let h, p, tc = CF.split_components estate.CF.es_formula in
	    (* getting the node that is aliased with recv  *)
	       let eqns = ptr_equations p in
	       let recv_sp = CP.SpecVar (CP.OType (CP.name_of_type recv_t), recv, Primed) in
	       let asets = alias ((recv_sp, recv_sp) :: eqns) in
	       let recv_aset = get_aset asets recv_sp  in (* find the alias set containing p2 *)
	       let anodes_prim,_ = get_aliased_node prog h recv_aset in
	       let anodes = List.map fst anodes_prim in
	       if U.empty anodes then
	       Err.report_error {Err.error_loc = pos;
	       Err.error_text = "receiver is not available in context"}
	       else
	       let tvar_o = CF.find_type_var (List.hd anodes) recv in
	       match tvar_o with
	       | None -> Err.report_error {Err.error_loc = pos;
	       Err.error_text = "no precondition is satisfied"}
	       | Some tvar -> begin
	       let proc, specs = find_spec_type prog tc tvar mn pos in
	       check_conjunct ctx proc specs
	       end
	       end in
	       let tmp1 = List.map check_one_context ctx in
	       let tmp2 = List.concat tmp1 in
	       --> if uncommented add the call to the context path
	       tmp2
	       end
	    *)

      | IConst ({exp_iconst_val = i;
		 exp_iconst_pos = pos}) ->
	  let c_e = CP.IConst (i, pos) in
	  let res_v = CP.Var (CP.mkRes int_type, pos) in
	  let f = CF.formula_of_pure (CP.mkEqExp res_v c_e pos) pos in
	  let res_ctx = CF.normalize_max_renaming_list_partial_context f pos true ctx in
	    res_ctx
      | FConst {exp_fconst_val = f; exp_fconst_pos = pos} ->
	  let c_e = CP.FConst (f, pos) in
	  let res_v = CP.Var (CP.mkRes float_type, pos) in
	  let f = CF.formula_of_pure (CP.mkEqExp res_v c_e pos) pos in
	  let res_ctx = CF.normalize_max_renaming_list_partial_context f pos true ctx in
	    res_ctx
      | New ({exp_new_class_name = c;
	      exp_new_parent_name = pname;
	      exp_new_arguments = args;
	      exp_new_pos = pos}) -> begin
	  let field_types, vs = List.split args in
	  let heap_args = List.map2 (fun n -> fun t -> CP.SpecVar (t, n, Primed))
	    vs field_types in
	    (*--- 09.05.2000 *)
	    (*let fn1 = fresh_name () in
	      let fn2 = fresh_name () in*)
	    (*
	      let _ = (print_string ("\n[typechecker.ml, line 409]: fresh name = " ^ fn1 ^ "!!!!!!!!!!!\n")) in
	      let _ = (print_string ("\n[typechecker.ml, line 410]: fresh name = " ^ fn2 ^ "!!!!!!!!!!!\n")) in
	    *)
	    (*09.05.2000 ---*)
	    (*let type_var = CP.SpecVar (CP.OType c, fn1, Unprimed) in
	      let type_constr = CF.TypeExact ({CF.t_formula_sub_type_var = type_var;
	      CF.t_formula_sub_type_type = c}) in*)
	    (*c let ext_var = CP.SpecVar ((CP.OType ("Ext~" ^ pname ^ "~" ^ c)), fn2, Unprimed) in*)
	    (*let ext_null = CP.mkNull ext_var pos in*)
	  let heap_node = CF.DataNode ({CF.h_formula_data_node = CP.SpecVar (CP.OType c, res, Unprimed);
					CF.h_formula_data_name = c;
					CF.h_formula_data_arguments =
					   (*type_var :: ext_var :: *) heap_args;
					CF.h_formula_data_label = None;
					CF.h_formula_data_pos = pos}) in
	    (*c let heap_form = CF.mkExists [ext_var] heap_node ext_null type_constr pos in*)
	  let heap_form = CF.mkBase heap_node (CP.mkTrue pos) CF.TypeTrue (CF.mkTrueFlow ()) [] pos in
	  let res = CF.normalize_max_renaming_list_partial_context heap_form pos true ctx in
	    res
	end;
	  (*  | FieldRead (tf, (v, tv), (f, idx), pos) -> begin
	      let c = CP.name_of_type tv in
	      i need a special check that
	      - checks if node v::c<...> is in ctx, perform unfolding if necessary
	      - returns that node??? For field read, I just need to add res=a to every branch
	      - the worst combination is x.f; g(x); x.f; g(x). i.e. start with
	      view, unfold, fold, unfold, fold, etc...
	      end
	  *)
      | Null pos ->
	  let p = CP.mkEqExp (CP.mkVar (CP.SpecVar (CP.OType "", res, Unprimed)) pos) (CP.Null pos) pos in
	  let f = CF.formula_of_pure p pos in
	  let res = CF.normalize_max_renaming_list_partial_context f pos true ctx in
	    res
	      (* | Return ({exp_return_type = t;
		 exp_return_val = oe;
		 exp_return_pos = pos}) -> begin
		 let ctx1 = (match oe with
		 | None -> ctx
		 | Some e -> check__exp prog proc ctx post e) in
		 let _ = check_post prog proc ctx1 post pos in
		 [CF.false_ctx pos] (* anything following return is not reachable *)
		 end*)
      | SCall ({exp_scall_type = ret_t;
		exp_scall_method_name = mn;
		exp_scall_arguments = vs;
		exp_scall_visible_names = p_svars;
		exp_scall_path_id = pid;
		exp_scall_pos = pos}) -> begin (* mn is mingled name of the method *)
	  (*print_endline "\nSCALL!"; flush stdout;*)
	  let proc = look_up_proc_def pos prog.prog_proc_decls mn in
	  let farg_types, farg_names = List.split proc.proc_args in
	  let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
	  let actual_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) vs farg_types in
	    
	  let check_pre_post org_spec (sctx:CF.list_partial_context):CF.list_partial_context =
	    (* free vars = linking vars that appear both in pre and are not formal arguments *)
	    let pre_free_vars = CP.difference (CP.difference (Cformula.struc_fv org_spec) (Cformula.struc_post_fv org_spec)) farg_spec_vars in
	      (* free vars get to be substituted by fresh vars *)
	    let pre_free_vars_fresh = CP.fresh_spec_vars pre_free_vars in
	    let renamed_spec = 
              if !Globals.max_renaming then (Cformula.rename_struc_bound_vars org_spec)
              else (Cformula.rename_struc_clash_bound_vars org_spec (CF.formula_of_list_partial_context ctx))
	    in
	    let st1 = List.combine pre_free_vars pre_free_vars_fresh in
	    let fr_vars = farg_spec_vars @ (List.map CP.to_primed farg_spec_vars) in
	    let to_vars = actual_spec_vars @ (List.map CP.to_primed actual_spec_vars) in
	      (*let _ = print_string ("\n trt from: "^(Cprinter.string_of_spec_var_list fr_vars)^"\n"^
		"\n  to: "^(Cprinter.string_of_spec_var_list to_vars)^"\n in: "^(Cprinter.string_of_struc_formula renamed_spec)^"\n") in*)
	    let renamed_spec = CF.subst_struc st1 renamed_spec in
	    let renamed_spec= CF.subst_struc_avoid_capture fr_vars to_vars renamed_spec in
	    let st2 = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) actual_spec_vars in
	    let pre2 = CF.subst_struc_pre st2 renamed_spec in
	    let to_print = "Proving precondition in method " ^ proc.proc_name ^ " for spec:\n" ^ !log_spec ^ "\n" in
	      Debug.devel_pprint to_print pos;
	      let rs,prf = heap_entail_struc_list_partial_context_init prog false false true sctx pre2 pos pid in
		(* Solver.entail_hist#upd_opt pid rs ("No label for SCALL at line"  ^ (string_of_int pos.start_pos.Lexing.pos_lnum)); *)
	      let _ = PTracer.log_proof prf in
		rs in
	    
	  let res = if(CF.isFailListPartialCtx ctx) then ctx
	  else check_pre_post proc.proc_static_specs_with_pre ctx in
	    
	    if (CF.isFailListPartialCtx res)then begin
              Debug.print_info ("precondition checking ("^(Cprinter.get_label_list_partial_context res)^") ") ("none is satisfied\n") pos; (* add branch info *)
	      res
		(* Err.report_error { Err.error_loc = pos; *)
		(* 			 Err.error_text = "no precondition is satisfied"} *)
	    end
	    else res
	end
      | Seq ({exp_seq_type = te2;
	      exp_seq_exp1 = e1;
	      exp_seq_exp2 = e2;
	      exp_seq_pos = pos}) -> begin
	  let ctx1 = check_exp prog proc ctx e1 post_start_label (*flow_store*) in (* Astsimp ensures that e1 is of type void *)
	    check_exp prog proc ctx1 e2 post_start_label (*flow_store*)
	end
      | This ({exp_this_type = t;
	       exp_this_pos = pos}) -> begin
	  let tmp = CF.formula_of_pure (CP.mkEqVar (CP.mkRes t) (CP.SpecVar (t, "this", Unprimed)) pos) pos in
	  let ctx1 = CF.normalize_max_renaming_list_partial_context tmp pos true ctx in
	    ctx1
	end
      | Var ({exp_var_type = t;
	      exp_var_name = v;
	      exp_var_pos = pos}) -> begin
	  let tmp = CF.formula_of_pure (CP.mkEqVar (CP.mkRes t) (CP.SpecVar (t, v, Primed)) pos) pos in
	  let ctx1 = CF.normalize_max_renaming_list_partial_context tmp pos true ctx in
	    ctx1
	end;
      | VarDecl _ -> ctx (* nothing to do *)
      | Unit pos -> ctx
      | Sharp ({exp_sharp_type =t;
		exp_sharp_flow_type = ft;(*P.flow_typ*)
		exp_sharp_val = v; (*maybe none*)
		exp_sharp_unpack = un;(*true if it must get the new flow from the second element of the current flow pair*)
		exp_sharp_path_id = pid;
		exp_sharp_pos = pos})	-> 
	  (*let _ =print_string ("sharp start ctx: "^ (Cprinter.string_of_context_list ctx)^"\n") in
	    let _ = print_string ("raising: "^(Cprinter.string_of_exp e0)^"\n") in*)
	  let nctx = match v with 
	    | Sharp_prog_var (t,v) -> 
		let tmp = CF.formula_of_pure (CP.mkEqVar (CP.mkRes t) (CP.SpecVar (t, v, Primed)) pos) pos in
		let ctx1 = CF.normalize_max_renaming_list_partial_context tmp pos true ctx in
		  ctx1
	    | Sharp_finally v -> 
		let fct es = 
		  let rest, b_rez = CF.get_var_type v es.CF.es_formula in
		    if b_rez then
                      let vsv_f = CF.formula_of_pure (CP.mkEqVar (CP.SpecVar (rest, v, Primed)) (P.mkRes rest) pos) pos in
			if !Globals.max_renaming then CF.normalize_es vsv_f pos true es
			else CF.normalize_clash_es vsv_f pos true es
		    else CF.Ctx es
		in
		  CF.transform_list_partial_context (fct,(fun c-> c)) ctx
	    | Sharp_no_val -> ctx in
	  let r = (match ft with 
		     | Sharp_ct nf -> 
			 if not un then CF.transform_list_partial_context 
			   ((fun es -> 
			       CF.Ctx {es with CF.es_formula = CF.set_flow_in_formula nf es.CF.es_formula}),
			    (fun c->c)) nctx
			 else CF.transform_list_partial_context 
			   ((fun es -> 
			       CF.Ctx {es with CF.es_formula = CF.set_flow_to_link_f !flow_store es.CF.es_formula no_pos}),
			    (fun c->c)) nctx
		     | Sharp_v v -> CF.transform_list_partial_context 
			 ((fun es -> 
			     CF.Ctx {es with CF.es_formula = CF.set_flow_in_formula (CF.get_flow_from_stack v !flow_store pos) es.CF.es_formula}),
			  (fun c->c)) nctx )in
	    CF.add_path_id_ctx_partial_list r (pid,0)

      | Try ({exp_try_body = body;
      	      exp_catch_clause = cc;
      	      exp_try_path_id = pid;
      	      exp_try_pos = pos })->
	  let ctx1 = check_exp prog proc ctx body post_start_label in
	  let fn (l:path_trace) (lpc:CF.context) : CF.list_partial_context =
	    (check_exp prog proc [CF.mk_partial_context lpc l] cc.exp_catch_body post_start_label) in

	  let apply_catch_partial_context2 (pc : CF.partial_context) :CF.list_partial_context =
	    (CF.splitter_partial_context (cc.exp_catch_flow_type)
	       (cc.exp_catch_var) fn (fun c -> CF.add_path_id c (pid,0)) elim_exists_ctx) pc in

	  let rec apply_catch_context (ctx_crt : CF.context) (lab:path_trace) :CF.list_partial_context =
	    match ctx_crt with
      	      |CF.OCtx (c1,c2)-> CF.list_partial_context_or (apply_catch_context c1 lab) (apply_catch_context c1 lab)
      	      |CF.Ctx c1 ->
      		 let nf  =  CF.flow_formula_of_formula c1.CF.es_formula in
      		   if not (CF.subsume_flow_f cc.exp_catch_flow_type nf) then
      		     (CF.add_path_id_ctx_partial_list
      			[([],[(lab,ctx_crt)])] (pid,0))
      		   else
      		     let nctx = CF.set_flow_in_ctx_override ctx_crt {CF.formula_flow_interval = !n_flow_int; CF.formula_flow_link = nf.CF.formula_flow_link} in
      		       flow_store := (match cc.exp_catch_flow_var with
      					| None -> !flow_store
      					| Some v -> {CF.formula_store_name = v; CF.formula_store_value = nf;}::!flow_store) ;
      		       match cc.exp_catch_var with
      			 |Some (cvt,cvn) ->
      			    let rest, b_rez = CF.get_result_type c1.CF.es_formula in
      			    let ctx =
      			      if b_rez then
      				let vsv_f = CF.formula_of_pure (CP.mkEqVar (CP.SpecVar (rest, cvn, Primed)) (P.mkRes rest) pos) pos in
      				let ctx1 = 	CF.normalize_max_renaming vsv_f pos true (CF.SuccCtx [nctx]) in
      				let ctx1 = CF.push_exists_list_context [CP.mkRes rest] ctx1 in
      				  if !Globals.elim_exists then elim_exists_ctx_list ctx1 else ctx1
      			      else (CF.SuccCtx [nctx]) in
      			    let ctx1 = CF.repl_label_list_partial_context lab (check_exp prog proc (CF.mk_list_partial_context_label ctx lab) cc.exp_catch_body post_start_label) in
      			      if b_rez then CF.push_exists_list_partial_context [(CP.SpecVar (rest, cvn, Primed))] ctx1
      			      else ctx1
      			 | None ->
      			     CF.repl_label_list_partial_context lab (check_exp prog proc [(CF.mk_partial_context nctx lab)] cc.exp_catch_body post_start_label)
	  in
	  let rec apply_catch_partial_context ((fl,sl) : CF.partial_context):CF.list_partial_context =
	    let res_sl = List.map (fun (l,c) -> apply_catch_context c l) sl  in
	    let res = CF.fold_partial_context_left_or res_sl in
              if (U.empty fl) then res
              else CF.list_partial_context_or [(fl,[])] res
	  in
	    CF.fold_partial_context_left_or (List.map apply_catch_partial_context2 ctx1)

      | _ -> 
	  failwith ((Cprinter.string_of_exp e0) ^ " is not supported yet")  
  in
  let helper (cl:CF.list_partial_context) : CF.list_partial_context = 
    (* print list of partial context first *)
    (* print_string ("\n ***HELPER_IN-list of partial context "^Cprinter.summary_list_partial_context ctx); *)
    if CF.isFailListPartialCtx cl then cl
    else
      let r = List.map (CF.splitter_partial_context !n_flow_int None
			  (fun l c -> check_exp1 [CF.mk_partial_context c l]) (fun x
										 -> x) (fun x -> x)) cl in
      let r1 = CF.fold_partial_context_left_union r in
	(* print_string ("\n ***HELPER-OUT list of partial context "^Cprinter.summary_list_partial_context ctx); *)
	r1 
  in
    (* check for dprint and assert first ..*)
    match e0 with
      | Label e -> 
	  let ctx = CF.add_path_id_ctx_partial_list ctx e.exp_label_path_id in
	  let ctx = CF.add_cond_label_list_partial_context (fst e.exp_label_path_id) (snd e.exp_label_path_id) ctx in
	    (check_exp prog proc ctx e.exp_label_exp post_start_label)
      | Dprint ({exp_dprint_string = str;
		 exp_dprint_visible_names = visib_names;
		 exp_dprint_pos = pos}) -> begin
	  if str = "" then begin
	    let str1 = (Cprinter.string_of_list_partial_context ctx)  in
	    let tmp1 = "\ndprint: " ^ pos.start_pos.Lexing.pos_fname
	      ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^ ": ctx: " ^ str1 ^ "\n" in
	    let tmp1 = if (previous_failure ()) then ("partial context: "^tmp1) else tmp1 in
	      print_string tmp1;
	      ctx
	  end else begin
	    ignore (Drawing.dot_of_partial_context_file prog ctx visib_names str);
	    ctx
	  end
	end;
      | Assert ({exp_assert_asserted_formula = c1_o;
		 exp_assert_assumed_formula = c2;
		 exp_assert_path_id = (pidi,s);
		 exp_assert_pos = pos}) -> begin
	  (*let _ =print_string ("inside assert"^(match c1_o with | None -> "no formula "| Some c1_o ->Cprinter.string_of_struc_formula c1_o)^"\n") in*)
	  (* let s1 = CF.get_start_partial_label ctx in *)
	  if CF.isFailListPartialCtx ctx then ctx
	  else
            match c2 with 
	      | Some c -> helper ctx (* handled at small context level *)
	      | None ->
		  let s1 = snd post_start_label in
		    (* print_string ("\n\nLABEL PRECOND: " ^ s1 ^ "\nLabel ASSERT: " ^ s ^"\n\n"); *)
		    if (String.length s)>0 && (String.length s1)>0 && (String.compare s s1 <> 0)  then ((* print_string "inside label missmatch \n"; *)ctx)
		    else
		      let new_ctx = match c1_o with
			| None -> ctx
			| Some c1 ->
			    (*
			      let _ = print_string ("[typechecker.ml, line 62, assert]: pre to be entailed " ^ (Cprinter.string_of_formula c1) ^ "\n") in
			      let _ = print_string ("[typechecker.ml, line 63, assert]: context before entailment:\n" ^ (Cprinter.string_of_context_list ctx) ^ "\n\n") in
			    *)
			    let to_print = "Proving assert in method " ^ proc.proc_name ^ " for spec:\n" ^ !log_spec ^ "\n" in	
			      Debug.devel_pprint to_print pos;
                              (* print_string ("\n***CRT STATE : " ^ (Cprinter.string_of_list_partial_context ctx) ^ "\n"); *)
			      (* print_string ("\n***ASSERT COND : " ^ (Cprinter.string_of_struc_formula c1) ^ "\n\n\n\n"); *)
			      let rs,prf = heap_entail_struc_list_partial_context_init prog false false false ctx c1 pos None in
			      let _ = PTracer.log_proof prf in
				Debug.pprint ("assert condition:\n" ^ (Cprinter.string_of_struc_formula c1)) pos;
				(* Solver.entail_hist#upd (pidi,s) rs; *)
				if not(CF.isFailListPartialCtx rs)
				then
				  (Debug.print_info "assert" (s ^" : ok\n") pos;
				   Debug.pprint ("Residual:\n" ^ (Cprinter.string_of_list_partial_context rs)) pos;
				   rs)
				else (Debug.print_info "assert" (s ^" : failed\n") pos;rs (*ctx*)) in ctx
	end
      |  _ -> (helper ctx)
	   

and check_post (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_partial_context) (post : CF.formula) pos (pid:formula_label) : CF.list_partial_context  =
  (* match ctx with *)
  (*   | CF.FailCtx fr ->  *)
  (* 	let _ = print_string "found a fail context before checking the postcondition\n" in *)
  (* 	  ctx(\* *)
  (* 	       if (U.empty fcl) then ctx *)
  (* 	       else begin *)
  (* 	       push_fail_ctx (fr,fcl); *)
  (* 	       let r =(check_post prog proc (CF.SuccCtx fcl) post pos pid) in *)
  (* 	       pop_fail_ctx (); *)
  (* 	       let _ = print_string ("got into check_post on the failCtx branch"^(string_of_bool (CF.isFailCtx r))^"\n") in *)
  (* 	       (CF.or_list_context_outer r (CF.mkFailCtx_in fr)) *)
  (* 	       end*\) *)
  (*   | CF.SuccCtx _ ->  *)

  (*let _ = print_string ("got into check_post on the succCtx branch\n") in*)
  let vsvars = List.map (fun p -> CP.SpecVar (fst p, snd p, Unprimed))
    proc.proc_args in
  let r = proc.proc_by_name_params in
  let w = List.map CP.to_primed (CP.difference vsvars r) in
    (* print_string ("\nLength of List Partial Ctx: " ^ (Cprinter.summary_list_partial_context(ctx)));  *)
  let final_state_prim = CF.push_exists_list_partial_context w ctx in
    (* print_string ("\nLength of List Partial Ctx: " ^ (Cprinter.summary_list_partial_context(final_state_prim)));  *)
  let final_state = 
    if !Globals.elim_exists then elim_exists_partial_ctx_list final_state_prim else final_state_prim in
    Debug.devel_print ("Final state:\n" ^ (Cprinter.string_of_list_partial_context final_state_prim) ^ "\n");
    Debug.devel_print ("Final state after existential quantifier elimination:\n"
		       ^ (Cprinter.string_of_list_partial_context final_state) ^ "\n");
    Debug.devel_pprint ("Post-cond:\n" ^ (Cprinter.string_of_formula  post) ^ "\n") pos;
    let to_print = "Proving postcondition in method " ^ proc.proc_name ^ " for spec\n" ^ !log_spec ^ "\n" in
      Debug.devel_pprint to_print pos;	
      (*print_string ("context list: " ^ (Cprinter.string_of_context_list final_state ) ^ "\n");*)
      (*print_string ("tr:"^(string_of_int (List.length
	final_state))^"\n"); let _ = List.map (fun c-> let rec fct f =
	match f with | CF.Ctx c -> let rs, prf = heap_entail_init prog
	false false [f] post pos in if (CF.isFailCtx_list rs) then
	print_string ("\n fail: "^(Cprinter.string_of_context f)^"\n")
	else () | CF.FailCtx _ ->print_string ("\n fail:
	"^(Cprinter.string_of_context c)^"\n") | CF.OCtx (c1,c2) ->
	((fct c1);(fct c2)) in fct c) final_state in *)
      (* print_string ("\nLength of List Partial Ctx: " ^ (Cprinter.summary_list_partial_context(final_state)));  *)
      let rs, prf = heap_entail_list_partial_context_init prog false false final_state post pos (Some pid) 
      in
	(* print_string ("\nPOST after entail: " ^ (Cprinter.string_of_list_partial_context rs)); *)
      let _ = (* match final_state with  *)
	(* |CF.SuccCtx cl -> if List.for_all CF.isAnyFalseCtx cl then () else  *)
	PTracer.log_proof prf
	  (* | _ -> ()	 *)
      in
	(* Solver.entail_hist#upd pid rs; *)
	if (CF.isSuccessListPartialCtx rs) then rs
	else
	  Err.report_error {Err.error_loc = pos;
			    Err.error_text = "Post condition "
	      ^ (Cprinter.string_of_formula post)
	      ^ " cannot be derived by the system.\n By : "^(Cprinter.string_of_list_partial_context final_state)
	      ^ "\n fail ctx: "^(Cprinter.string_of_list_partial_context rs)}




(* checking procedure *)
and check_proc (prog : prog_decl) (proc : proc_decl) : bool =
  let unmin_name = unmingle_name proc.proc_name in
  let check_flag = ((U.empty !procs_verified) || List.mem unmin_name !procs_verified)
    && not (List.mem unmin_name !Inliner.inlined_procs)
  in
    if check_flag then begin
      match proc.proc_body with
	| None -> true (* sanity checks have been done by the translation *)
	| Some body -> begin
	    if !Globals.print_proc then
	      print_string ("Procedure " ^ proc.proc_name ^ ":\n"
			    ^ (Cprinter.string_of_proc_decl proc) ^ "\n\n");
	    print_string (("Checking procedure ") ^ proc.proc_name ^ "... "); flush stdout;
	    Debug.devel_pprint (("Checking procedure ") ^ proc.proc_name ^ "... ") proc.proc_loc;
	    Debug.devel_pprint ("Specs :\n" ^ Cprinter.string_of_struc_formula proc.proc_static_specs) proc.proc_loc;
	    let ftypes, fnames = List.split proc.proc_args in
	      (* fsvars are the spec vars corresponding to the parameters *)
	    let fsvars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in
	      (*Debug.devel_pprint ("fsvars : " ^ Cprinter.string_of_spec_var_list fsvars) proc.proc_loc;*)
	    let nox = CF.formula_of_pure (CF.no_change fsvars proc.proc_loc) proc.proc_loc in
	    let init_form = nox in(*
				    if !Globals.max_renaming then
	      (* if the max_renaming flag is on --> rename all the bound vars when doing the normalization *)
			   	    (CF.normalize pre nox (CF.pos_of_formula pre))
			   	    else
	      (* if the max_renaming flag is off --> rename only the bound vars from pre which clash with the free vars of nox *)
			  	    (CF.normalize_only_clash_rename pre nox (CF.pos_of_formula pre))
				    in*)
	    let init_ctx1 = CF.empty_ctx (CF.mkTrueFlow ()) proc.proc_loc in
	    let init_ctx = CF.build_context init_ctx1 init_form proc.proc_loc in
	    let pp = check_specs prog proc init_ctx (proc.proc_static_specs @ proc.proc_dynamic_specs) body in
	    let result =
	      if pp then begin
		print_string ("\nProcedure "^proc.proc_name^" SUCCESS\n");
		true
	      end else begin print_string ("\nProcedure "^proc.proc_name^" result FAIL\n"); false end in
	      (*
		if List.for_all check_pre_post pp then begin
		print_string ("SUCCESS\n");
		true
		end else false in *)
	      result
	  end
    end else
      true

(* check entire program *)
let check_proc_wrapper prog proc =
  try
    check_proc prog proc
  with _ as e ->
    if !Globals.check_all then begin
      dummy_exception();
      print_string ("\nProcedure "^proc.proc_name^" FAIL\n");
      print_string ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      false
    end else
      raise e

(*
let check_view vdef =
  let ante = vdef.view_formula in
  let conseq = vdef.view_invariant in
  let pos = get_constr_pos conseq in
  let ctx = build_ctx (Ctx (es_empty (get_constr_pos conseq))) ante pos in
  let ok, res = heap_entail false ctx conseq pos in
	if ok then
	  true
	else (* if !Globals.check_all then begin
			print_string ("Error detected when checking view " ^ vdef.view_name ^ ": invalid invariant");
			false
			end else *)
	  report_error pos ("Error detected when checking view " ^ vdef.view_name ^ ": invalid invariant")

let check_view_wrapper def = match def with
  | Data _ -> true
  | View vdef -> check_view vdef
*)

let check_data (prog : prog_decl) (cdef : data_decl) =
  if not (U.empty cdef.data_methods) then
	print_string ("\nChecking class " ^ cdef.data_name ^ "...\n\n");
  List.map (check_proc_wrapper prog) cdef.data_methods

let check_coercion (prog : prog_decl) =
  let check_entailment c_lhs c_rhs =
    let pos = CF.pos_of_formula c_lhs in
    let ctx = CF.build_context (CF.empty_ctx (CF.mkTrueFlow ()) pos) c_lhs pos in
    let rs, prf = heap_entail_init prog false false (CF.SuccCtx [ctx]) c_rhs pos in
    let _ = PTracer.log_proof prf in
      (* Solver.entail_hist := (" coercion check",rs):: !Solver.entail_hist ; *)
      if not(CF.isFailCtx rs) then begin
	Error.report_error { Error.error_loc = pos;
			     Error.error_text = "coercion is not valid" }
      end in
    (*TODO: find and unfold all instances of the head predicate in both sides *)
    (*let unfold_head_pred hname f0 : int = *)
  let check_left_coercion coer =
    let pos = CF.pos_of_formula coer.coercion_head in
    let lhs = unfold (Prog prog) coer.coercion_head (CP.SpecVar (CP.OType "", self, Unprimed)) true pos in
    let rhs = unfold (Prog prog) coer.coercion_body (CP.SpecVar (CP.OType "", self, Unprimed)) true pos in
      check_entailment lhs rhs in
    (* check_entailment lhs coer.coercion_body in *)
  let check_right_coercion coer =
    let pos = CF.pos_of_formula coer.coercion_head in
    let rhs = unfold (Prog prog) coer.coercion_head (CP.SpecVar (CP.OType "", self, Unprimed)) true pos in
    let lhs = unfold (Prog prog) coer.coercion_body (CP.SpecVar (CP.OType "", self, Unprimed)) true pos in
      check_entailment lhs rhs
	(* check_entailment coer.coercion_body rhs *)
  in
    ignore (List.map (fun coer -> check_left_coercion coer) prog.prog_left_coercions);
    List.map (fun coer -> check_right_coercion coer) prog.prog_right_coercions


let rec size (expr : exp) =
  match expr with
    | Label e -> size e.exp_label_exp
    | CheckRef ex -> 1
    | Java ex -> 1
    | Assert ex -> 1
    | Assign ex -> 1 + (size ex.exp_assign_rhs)
    | BConst ex -> 1
    | Bind ex -> 1 + (size ex.exp_bind_body)
    | Block ex -> 1 + (size ex.exp_block_body)
    | Cond ex -> 1 + (size ex.exp_cond_then_arm) + (size ex.exp_cond_else_arm)
    | Cast ex -> 1 + (size ex.exp_cast_body)
    | Debug ex -> 1
    | Dprint ex -> 1
    | FConst ex -> 1
    | ICall ex -> 1 + (List.length ex.exp_icall_arguments)
    | IConst ex -> 1
    | New ex -> 1
    | Null ex -> 1
    | Print ex -> 1
	(*| Return ex -> 1 + (match ex.exp_return_val with | None -> 1 | Some ex1 -> (size ex1))*)
    | SCall ex -> 1 + (List.length ex.exp_scall_arguments)
    | Seq ex -> 1 + (size ex.exp_seq_exp1) + (size ex.exp_seq_exp2)
    | This ex -> 1
    | Var ex -> 1
    | VarDecl ex -> 1
    | Unfold ex -> 1
    | Unit ex -> 1
    | While ex -> 1 + 2*(List.length ex.exp_while_spec) + (size ex.exp_while_body)
    | _ -> 1

let size_proc_decl (proc_d : proc_decl) =
  (match proc_d.proc_body with
  | None -> 0
  | Some ex -> (size ex)) + 2*((List.length proc_d.proc_static_specs) + (List.length proc_d.proc_dynamic_specs))

let compare_proc_decl (proc1 : proc_decl) (proc2 : proc_decl) =
  (size_proc_decl proc2) - (size_proc_decl proc1)

let init_files () =
  begin
    Omega.init_files ();
    Setmona.init_files ();
  end

let check_proc_wrapper_map prog (proc,num) =
  if !Tpdispatcher.external_prover then Tpdispatcher.Netprover.set_use_socket_map (List.nth !Tpdispatcher.external_host_ports (num mod (List.length !Tpdispatcher.external_host_ports))); (* make this dynamic according to availability of server machines*)
  try
    check_proc prog proc
  with _ as e ->
    if !Globals.check_all then begin
      print_string ("\nProcedure "^proc.proc_name^" FAIL\n");
      print_string ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      false
    end else
      raise e

let check_proc_wrapper_map_net prog (proc,num) =
  try
    check_proc prog proc
  with _ as e ->
    if !Globals.check_all then begin
      print_string ("\nProcedure "^proc.proc_name^" FAIL\n");
      print_string ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      false
    end else
      raise e

let check_prog (prog : prog_decl) =
  if !Globals.check_coercions then begin
    print_string "Checking coercions... ";
    ignore (check_coercion prog);
    print_string "DONE."
  end else begin
    ignore (List.map (check_data prog) prog.prog_data_decls);
    ignore (List.map (check_proc_wrapper prog) prog.prog_proc_decls);
    (*let rec numbers num = if num = 1 then [0] else (numbers (num-1))@[(num-1)]in
      let filtered_proc = (List.filter (fun p -> p.proc_body <> None) prog.prog_proc_decls) in
      let num_list = numbers (List.length filtered_proc) in
      let prog_proc_decls_num = if !sort_input then
      List.map2 (fun a b -> (a,b)) (List.sort compare_proc_decl filtered_proc) num_list
      else 
      List.map2 (fun a b -> (a,b)) filtered_proc num_list in
      if (!num_para = 0) then
      ignore(Paralib1.map_para init_files (check_proc_wrapper_map prog) prog_proc_decls_num)
      else if (!num_para > 1) then
      if !Tpdispatcher.external_prover then
      ignore(Paralib1v2.map_para_net init_files (check_proc_wrapper_map_net prog) prog_proc_decls_num !num_para)
      else
      ignore(Paralib1v2.map_para init_files (check_proc_wrapper_map prog) prog_proc_decls_num !num_para)
      else if (!num_para = 1) then begin
      ignore (List.map (check_proc_wrapper prog) prog.prog_proc_decls);
      if !webserver then Net.IO.write_job_web (!Tpdispatcher.Netprover.out_ch) (-1) "" "" 1 else ()
      end
      else
      () *)
  end
