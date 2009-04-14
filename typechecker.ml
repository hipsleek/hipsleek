open Globals
open Solver
open Cast

module CF = Cformula
module CP = Cpure
module U = Util
module TP = Tpdispatcher
module PTracer = Prooftracer

(* checking expression *)

(* assumes the pre, and starts the simbolic execution*)
let rec check_specs (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) spec_list e0 : bool = 

				let rec do_spec_verification (spec: Cformula.ext_formula):bool = match spec with
					| Cformula.ECase b -> List.for_all (fun (c1,c2)-> 
								let nctx = combine_context_and prog ctx c1 true  in
								check_specs prog proc nctx c2 e0) b.Cformula.formula_case_branches
					| Cformula.EBase b ->
								let nctx = 
									if !Globals.max_renaming 
										then (CF.normalize_context_formula ctx b.Cformula.formula_ext_base b.Cformula.formula_ext_pos false)
										else (CF.normalize_clash_context_formula ctx b.Cformula.formula_ext_base b.Cformula.formula_ext_pos false) in
								check_specs prog proc nctx b.Cformula.formula_ext_continuation e0
					| Cformula.EAssume (x,b) ->
								let ctx1 = elim_unsat_ctx prog ctx in
								if (Cformula.isFalseCtx ctx1) then
									let _ = print_string ("False precondition detected in procedure "^proc.proc_name^"\n with context: "^
										(Cprinter.string_of_context ctx)) in 
									true
								else
								let _ = Util.push_time ("method "^proc.proc_name) in
								try 
								let r = 
									let res_ctx = check_exp prog proc [ctx1] b e0 in
									if CP.are_same_types proc.proc_return void_type then
									  (* void procedures may not contain a return in all branches,
										 so we need to make a catch-all check at the end of the body *)
									  let tmp_ctx = check_post prog proc res_ctx b (Cformula.pos_of_formula b) in
										not (U.empty tmp_ctx)
									else
									  not (U.empty res_ctx)  in
								let _ = Util.pop_time ("method "^proc.proc_name) in
								 r
								 with _ as e -> 
									let _ = Util.pop_time ("method "^proc.proc_name) in raise e
								  in	
	List.for_all do_spec_verification spec_list
	
and check_exp (prog : prog_decl) (proc : proc_decl) (ctx : CF.context list) post e0 : CF.context list = 
  if (exp_to_check e0) then 
	Cformula.find_false_ctx ctx 
		(Cast.pos_of_exp e0) 
		else ();
  match e0 with
	(* for theorem proving *)
  | Unfold ({exp_unfold_var = sv;
			 exp_unfold_pos = pos}) -> begin
	  let res = List.map (fun c -> unfold_context (Prog prog) c sv true pos) ctx in
		res
	end
(* for code *)
  | Assert ({exp_assert_asserted_formula = c1_o;
			 exp_assert_assumed_formula = c2;
			 exp_assert_pos = pos}) -> begin
	  let new_ctx = match c1_o with
		 | None -> ctx
		 | Some c1 ->
		 		(*
		 		let _ = print_string ("[typechecker.ml, line 62, assert]: pre to be entailed " ^ (Cprinter.string_of_formula c1) ^ "\n") in
				let _ = print_string ("[typechecker.ml, line 63, assert]: context before entailment:\n" ^ (Cprinter.string_of_context_list ctx) ^ "\n\n") in
				*)
			 let rs,prf = heap_entail_struc prog false false false ctx c1 pos in
			 let _ = PTracer.log_proof prf in
			 Debug.pprint ("assert condition:\n" ^ (Cprinter.string_of_struc_formula c1)) pos;
			 if not (U.empty rs) then
			   let resstr = String.concat "\n;\n" (List.map (fun c -> Cprinter.string_of_context c) rs) in
			   Debug.print_info "assert" ("assert ok\n") pos;
			   Debug.pprint ("Residual:\n" ^ resstr) pos;
               rs
			 else (
			   Debug.print_info "assert" ("assert failed\n") pos;
               ctx
             ) in
	  match c2 with
	  | None -> ctx
	  | Some c ->
		  Debug.pprint ("assume condition:\n" ^ (Cprinter.string_of_formula c)) pos;
		  let assumed_ctx =
			if !Globals.max_renaming then List.map (fun cc -> (*CF.set_context_formula*) CF.normalize_context_formula cc c pos false) new_ctx
			else List.map (fun cc -> (*CF.set_context_formula*) CF.normalize_clash_context_formula cc c pos false) new_ctx
		  in
          (*print_int (!Omega.test_number);*)
          let ret = List.map (elim_unsat_ctx prog) assumed_ctx in
          (*print_int (!Omega.test_number);*)
          ret
	end
  | Assign ({exp_assign_lhs = v;
			 exp_assign_rhs = rhs;
			 exp_assign_pos = pos}) -> begin
      let ctx1 = check_exp prog proc ctx post rhs in
		(* Debug.devel_pprint ("delta at beginning of assignment to " ^ v ^ ":\n" ^ (string_of_constr delta) ^ "\n") pos; *)
	  let t = U.unsome (type_of_exp rhs) in
	  let vsv = CP.SpecVar (t, v, Primed) in (* rhs must be non-void *)
	  let link = CF.formula_of_pure (CP.mkEqVar vsv (P.mkRes t) pos) pos in
	  let tmp_ctx1 = List.map (fun c -> CF.compose_context_formula c link [vsv] pos) ctx1 in
	  let tmp_ctx2 = List.map (fun c -> CF.push_exists_context [CP.mkRes t] c) tmp_ctx1 in
	  let resctx = if !Globals.elim_exists then List.map (fun c -> elim_exists_ctx c) tmp_ctx2 else tmp_ctx2 in
		(* Debug.devel_pprint ("assignment: tmp_delta:\n" ^ (string_of_constr tmp_delta)) pos;
		   Debug.devel_pprint ("assignment: tmp_delta1:\n" ^ (string_of_constr tmp_delta1)) pos;
		   Debug.devel_pprint ("assignment: after existential quantifier elimination:\n" ^ (string_of_constr resform)) pos; *)
		resctx
    end
  | BConst ({exp_bconst_val = b;
			 exp_bconst_pos = pos}) -> begin
	  let res_v = CP.mkRes bool_type in
	  let tmp1 = CP.BForm (CP.BVar (res_v, pos)) in
	  let tmp2 =
		if b then tmp1
		else CP.Not (tmp1, pos) in
	  let f = CF.formula_of_pure tmp2 pos in
	  let res_ctx =
	  	if !Globals.max_renaming then List.map (fun c -> CF.normalize_context_formula c f pos true) ctx
	  	else List.map (fun c -> CF.normalize_clash_context_formula c f pos true) ctx
	  in
		res_ctx
	end
  | Bind ({exp_bind_type = body_t;
		   exp_bind_bound_var = (v_t, v);
		   exp_bind_fields = lvars;
		   exp_bind_body = body;
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
		(CP.mkAnd (CP.mkEqVar v_prim p pos) (CP.BForm (CP.mkNeq (CP.Var (p, pos)) (CP.Null pos) pos)) pos) pos in
		(*let _ = print_string ("[typechecker.ml, check_exp]: link_pv: " ^ Cprinter.string_of_formula link_pv ^ "\n") in*)
		(*	  let link_pv = CF.formula_of_pure (CP.mkEqVar v_prim p pos) pos in *)
	  let tmp_ctx =
		if !Globals.large_bind then
			begin
			if !Globals.max_renaming then List.map (fun c -> CF.normalize_context_formula c link_pv pos false) ctx
			else List.map (fun c -> CF.normalize_clash_context_formula c link_pv pos false) ctx
			end
		else ctx in
	  let unfolded = List.map (fun c -> unfold_context (Prog prog) c v_prim true pos) tmp_ctx in
		(* let unfolded_prim = if !Globals.elim_unsat then elim_unsat unfolded else unfolded in *)
	  let _ = Debug.devel_pprint ("bind: unfolded context:\n"
								  ^ (String.concat "\n;;\n" (List.map (fun c -> Cprinter.string_of_context c) unfolded))
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
									CF.h_formula_data_pos = pos}) in
	  let vheap = CF.formula_of_heap vdatanode pos in
	  let rs_prim, prf = heap_entail prog false false unfolded vheap pos in
	  let _ = PTracer.log_proof prf in
	  let rs = CF.clear_entailment_history_list rs_prim in
		if not (U.empty rs) then
		  let process_one cc =
			let tmp_res1 = check_exp prog proc [cc] post body in
			let tmp_res2 =
				if !Globals.max_renaming then List.map (fun c -> CF.normalize_context_formula c vheap pos true) tmp_res1
				else List.map (fun c -> CF.normalize_clash_context_formula c vheap pos true) tmp_res1
			in
			let tmp_res3 = List.map (fun c -> CF.push_exists_context vs_prim c) tmp_res2 in
			let res =
			  if !Globals.elim_exists then List.map (fun c -> elim_exists_ctx c) tmp_res3
			  else tmp_res3 in
			  (* Debug.devel_pprint ("bind: delta1:\n" ^ (string_of_constr delta1) ^ "\n") pos;
				 Debug.devel_pprint ("bind: delta2:\n" ^ (string_of_constr delta2) ^ "\n") pos;
				 Debug.devel_pprint ("bind: delta3:\n" ^ (string_of_constr delta3) ^ "\n") pos;
				 Debug.devel_pprint ("bind: after existential quantifier elimination:\n"
				 ^ (string_of_constr resform) ^ "\n") pos; *)
			  res in
		  let tmp_res = List.map process_one rs in
		  let res = List.concat tmp_res in
			res
		else
		  Err.report_error {Err.error_loc = pos;
							Err.error_text = "bind: node " ^ (Cprinter.string_of_h_formula vdatanode)
			  ^ " cannot be derived from context"}
    end;
  | Block ({exp_block_type = t;
			exp_block_body = e;
			exp_block_local_vars = local_vars;
			exp_block_pos = pos}) -> begin
	  let ctx1 = check_exp prog proc ctx post e in
	  let svars = List.map (fun (t, n) -> CP.SpecVar (t, n, Primed)) local_vars in
	  let ctx2 = List.map (fun c -> CF.push_exists_context svars c) ctx1 in
	  let ctx3 = if !Globals.elim_exists then List.map (fun c -> elim_exists_ctx c) ctx2 else ctx2 in
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
		   exp_cond_pos = pos}) -> begin
	  let then_cond_prim = CP.BForm (CP.mkBVar v Primed pos) in
	  let else_cond_prim = CP.mkNot then_cond_prim pos in
	 (* let then_cond = CF.formula_of_pure then_cond_prim pos in
	  let else_cond = CF.formula_of_pure else_cond_prim pos in*)
	  let process_one c =
		let then_ctx = combine_context_and_unsat_now prog c then_cond_prim in

		(*Debug.devel_pprint ("conditional: then_delta1:\n" ^ (Cprinter.string_of_context then_ctx1)) pos;*)
		(*let then_ctx =  Solver.elim_unsat_ctx prog then_ctx1 in*)

		(*let _ = print_string ("\nbefore: \t\t" ^ (Cprinter.string_of_context c)^"\n cond: "^(Cprinter.string_of_formula then_cond)^"\n after: "^
		(Cprinter.string_of_context then_ctx1)^"\n after elim: "^
		(Cprinter.string_of_context then_ctx)^"\n") in*)
		
		Debug.devel_pprint ("conditional: then_delta:\n" ^ (Cprinter.string_of_context then_ctx)) pos;
		let else_ctx =combine_context_and_unsat_now prog c else_cond_prim in
			(*if !Globals.max_renaming then CF.normalize_context_formula c else_cond pos
			else CF.normalize_clash_context_formula c else_cond pos
		in*)
		(*Debug.devel_pprint ("conditional: else_delta1:\n" ^ (Cprinter.string_of_context else_ctx1)) pos;
		let else_ctx = Solver.elim_unsat_ctx prog else_ctx1 in*)
		Debug.devel_pprint ("conditional: else_delta:\n" ^ (Cprinter.string_of_context else_ctx)) pos;
		
		
		let then_ctx2 = check_exp prog proc [then_ctx] post e1 in
		
		let else_ctx2 = check_exp prog proc [else_ctx] post e2 in
		let res = CF.or_context_list then_ctx2 else_ctx2 in
		  res in
	  let tmp_res = List.map process_one ctx in
	  let res = List.concat tmp_res in
		res
    end;
  | Debug ({exp_debug_flag = flag;
			exp_debug_pos = pos}) -> begin
	  (if flag then Omega.log_mark "debug on"
	   else Omega.log_mark "debug off");
	  Debug.devel_debug_on := flag;
	  ctx
	end;
  | Dprint ({exp_dprint_string = str;
			 exp_dprint_visible_names = visib_names;
			 exp_dprint_pos = pos}) -> begin
	  if str = "" then begin
		let str1 = String.concat "\n;;\n" (List.map (fun c-> 
				"\n\n context length: "^(string_of_int (Cformula.count_or c))^"\n"^(Cprinter.string_of_context c)) ctx)  in
		let tmp1 = "\nprint: " ^ pos.Lexing.pos_fname
		  ^ ":" ^ (string_of_int pos.Lexing.pos_lnum) ^ ": ctx: "^(string_of_int (List.length ctx))^"\n" ^ str1 ^ "\n" in
	
	
		  (*
			let str2 = String.concat "\n;;\n"
			(List.map Cprinter.string_of_context (List.map (fun c -> Solver.elim_unsat_ctx prog c) ctx)) in
			let tmp2 = "\nprint:" ^ pos.Lexing.pos_fname ^ ":"
			^ (string_of_int pos.Lexing.pos_lnum) ^ ": unsat removed:\n" ^ str2 ^ "\n"
			in *)
		  print_string tmp1;
		  (* print_string tmp2; *)
		  ctx
	  end else if str = "disj_count" then begin
		let tmp1 = List.map CF.disj_count_ctx ctx in
		let tmp = List.fold_left (+) 0 tmp1 in
		  Debug.print_info "dprint"
			("number of disjuncts: " ^ (string_of_int tmp) ^ "\n") pos;
		  ctx
	  end else begin
		ignore (Drawing.dot_of_context_file prog ctx visib_names str);
		ctx
	  end
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
		tmp2
	end
	*)

  | IConst ({exp_iconst_val = i;
			 exp_iconst_pos = pos}) ->
	  let c_e = CP.IConst (i, pos) in
	  let res_v = CP.Var (CP.mkRes int_type, pos) in
	  let f = CF.formula_of_pure (CP.mkEqExp res_v c_e pos) pos in
	  let res_ctx =
	  	if !Globals.max_renaming then List.map (fun c -> CF.normalize_context_formula c f pos true) ctx
	  	else List.map (fun c -> CF.normalize_clash_context_formula c f pos true) ctx
	  in
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
									CF.h_formula_data_pos = pos}) in
	  (*c let heap_form = CF.mkExists [ext_var] heap_node ext_null type_constr pos in*)
	  let heap_form = CF.mkBase heap_node (CP.mkTrue pos) CF.TypeTrue [] pos in
	  let res =
	  	if !Globals.max_renaming then List.map (fun c -> CF.normalize_context_formula c heap_form pos true) ctx
	  	else List.map (fun c -> CF.normalize_clash_context_formula c heap_form pos true) ctx
	  in
		res
    end;
  | Null pos ->
	  let p = CP.mkEqExp (CP.mkVar (CP.SpecVar (CP.OType "", res, Unprimed)) pos) (CP.Null pos) pos in
	  let f = CF.formula_of_pure p pos in
	  let res =
	  	if !Globals.max_renaming then List.map (fun c -> CF.normalize_context_formula c f pos true) ctx
	  	else List.map (fun c -> CF.normalize_clash_context_formula c f pos true) ctx
	  in
		res
  | Return ({exp_return_type = t;
			 exp_return_val = oe;
			 exp_return_pos = pos}) -> begin
	  let ctx1 = (match oe with
					| None -> ctx
					| Some e -> check_exp prog proc ctx post e) in
	  let _ = check_post prog proc ctx1 post pos in
		[CF.false_ctx pos] (* anything following return is not reachable *)
	end
  | SCall ({exp_scall_type = ret_t;
			exp_scall_method_name = mn;
			exp_scall_arguments = vs;
			exp_scall_visible_names = p_svars;
			exp_scall_pos = pos}) -> begin (* mn is mingled name of the method *)
      (*print_endline "\nSCALL!"; flush stdout;*)
 	  let proc = look_up_proc_def pos prog.prog_proc_decls mn in
      let farg_types, farg_names = List.split proc.proc_args in
	  let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
 	  let actual_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) vs farg_types in
      let check_pre_post sctx org_spec =
        (* free vars = linking vars that appear both in pre and are not formal arguments *)
		let pre_free_vars = CP.difference (CP.difference (Cformula.struc_fv org_spec) (Cformula.struc_post_fv org_spec)) farg_spec_vars in
		(* free vars get to be substituted by fresh vars *)
		let pre_free_vars_fresh = CP.fresh_spec_vars pre_free_vars in
		(* rename bound vars in the callee pre/post *)
		(* -- 16.05.2008 *)
		let renamed_spec =
		  if !Globals.max_renaming then (Cformula.rename_struc_bound_vars org_spec)
		  else (Cformula.rename_struc_clash_bound_vars org_spec (CF.formula_of_context_list ctx))
		in
		let st1 = List.combine pre_free_vars pre_free_vars_fresh in
		let fr_vars = farg_spec_vars @ (List.map CP.to_primed farg_spec_vars) in
		let to_vars = actual_spec_vars @ (List.map CP.to_primed actual_spec_vars) in
		(*let _ = print_string ("\n from: "^(Cprinter.string_of_spec_var_list fr_vars)^"\n"^
		"\n  to: "^(Cprinter.string_of_spec_var_list to_vars)^"\n") in*)
		let renamed_spec = CF.subst_struc st1 renamed_spec in
		let renamed_spec= CF.subst_struc_avoid_capture fr_vars to_vars renamed_spec in
		let st2 = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) actual_spec_vars in
		(*let _ = print_string ("\n unprimed: "^(Cprinter.string_of_spec_var_list (fst (List.split st2)))^"\n"^
		"\n  primed: "^(Cprinter.string_of_spec_var_list (snd (List.split st2)))^"\n") in*)
		let pre2 = CF.subst_struc_pre st2 renamed_spec in
		(*let  _ =print_string ("\n old spec "^(string_of_int (List.length org_spec))^"\n"^(Cprinter.string_of_struc_formula org_spec)^"\n new spec:"^(Cprinter.string_of_struc_formula pre2)^"\n") in*)
        (*print_endline ("SC: opr" ^ Cprinter.string_of_formula org_pre);*)
		(*print_endline ("SC: orig" ^ Cprinter.string_of_struc_formula org_spec);
		print_endline ("SC: renamed " ^ Cprinter.string_of_struc_formula renamed_spec);
		print_endline ("SC: pre2 " ^ Cprinter.string_of_struc_formula pre2);
		print_endline ("SC: ctx " ^ Cprinter.string_of_context sctx);*)
		let rs,prf = heap_entail_struc prog false false true [sctx] pre2 pos in
		(*let _ = print_string ("\n finishing scall at line "^(string_of_int (pos.Lexing.pos_lnum))^"\n") in *)
		(*let _ = print_string ("\n before call: "^(Cprinter.string_of_context sctx)^"\n pre: "^
		(Cprinter.string_of_struc_formula pre2)
		^"\n after call: "^(Cprinter.string_of_context_list rs)^"\n") in*)
		let _ = PTracer.log_proof prf in
		rs
      in
      let check_one_small_context sctx =
        let res = check_pre_post sctx proc.proc_static_specs_with_pre in
        (*print_string "\nRES_SMALL_LEN: "; print_int (List.length res); flush stdout;*)
        if res = [] then raise Exit else res
      in
      let rec split_ctx_or = function
        | CF.Ctx x -> [CF.Ctx x]
        | CF.OCtx (c1, c2) -> (split_ctx_or c1) @ (split_ctx_or c2)
      in
      (* formula list list -> context list *)
      let rec join_ctx_or = function
        | h :: t -> begin match t with
          | [] -> h
          | t ->
            let subcall = join_ctx_or t in
            let fold_fun l f = List.rev_append (List.map (fun c-> (CF.mkOCtx f c pos) ) subcall) l in
            List.fold_left fold_fun [] h
        end
        | [] -> assert false
      in
      let check_one_context ctx =
        let sctxs = split_ctx_or ctx in
        (*print_string "\nSMALL_CTXS: "; print_int (List.length sctxs); flush stdout;*)
        let ress =
          try join_ctx_or (List.map check_one_small_context  sctxs)
          with Exit -> []
        in
        ress
      in
      let res = List.concat (List.map check_one_context ctx) in
      (*print_string "\nRES_LEN: "; print_int (List.length res); flush stdout;*)
	  (*let _ = print_string ("[typechecker.ml, line 62, assert]: pre to be entailed " ^ (Cprinter.string_of_formula c1) ^ "\n") in*)
	  (*let _ = print_string ("[typechecker.ml]: res:\n" ^ (Cprinter.string_of_context_list res) ^ "\n\n") in*)

	  if U.empty res then
		Err.report_error { Err.error_loc = pos;
						   Err.error_text = "no precondition is satisfied"}
	  else res
	        end
  | Seq ({exp_seq_type = te2;
		  exp_seq_exp1 = e1;
		  exp_seq_exp2 = e2;
		  exp_seq_pos = pos}) -> begin
      let ctx1 = check_exp prog proc ctx post e1 in (* Astsimp ensures that e1 is of type void *)
		check_exp prog proc ctx1 post e2
    end
  | This ({exp_this_type = t;
		   exp_this_pos = pos}) -> begin
      let tmp = CF.formula_of_pure (CP.mkEqVar (CP.mkRes t) (CP.SpecVar (t, "this", Unprimed)) pos) pos in
      let ctx1 =
      	if !Globals.max_renaming then List.map (fun c -> CF.normalize_context_formula c tmp pos true) ctx
      	else List.map (fun c -> CF.normalize_clash_context_formula c tmp pos true) ctx
      in
		ctx1
	end
  | Var ({exp_var_type = t;
		  exp_var_name = v;
		  exp_var_pos = pos}) -> begin
      let tmp = CF.formula_of_pure (CP.mkEqVar (CP.mkRes t) (CP.SpecVar (t, v, Primed)) pos) pos in
      let ctx1 =
      	if !Globals.max_renaming then List.map (fun c -> CF.normalize_context_formula c tmp pos true) ctx
      	else List.map (fun c -> CF.normalize_clash_context_formula c tmp pos true) ctx
     	in
		ctx1
    end;
  | VarDecl _ -> ctx (* nothing to do *)
  | Unit pos -> ctx
  | _ -> failwith ((Cprinter.string_of_exp e0) ^ " is not supported yet")

and check_post (prog : prog_decl) (proc : proc_decl) (ctx : CF.context list) (post : CF.formula) pos =
  let vsvars = List.map (fun p -> CP.SpecVar (fst p, snd p, Unprimed))
	proc.proc_args in
  let r = proc.proc_by_name_params in
  let w = List.map CP.to_primed (CP.difference vsvars r) in
  let final_state_prim = List.map (fun c -> CF.push_exists_context w c) ctx in
  let final_state = List.map
	(fun c -> if !Globals.elim_exists then elim_exists_ctx c else c)
	final_state_prim
  in
	Debug.devel_print ("Final state:\n"
					   ^ (String.concat "\n;;\n"
							(List.map Cprinter.string_of_context final_state_prim))
					   ^ "\n");
	Debug.devel_print ("Final state after existential quantifier elimination:\n"
					   ^ (String.concat "\n;;\n"
							(List.map Cprinter.string_of_context final_state))
					   ^ "\n");
	Debug.devel_pprint ("Post-cond:\n" ^ (Cprinter.string_of_formula  post) ^ "\n") pos;
	let rs, prf = heap_entail prog false false final_state post pos in
	let _ =
	  if List.for_all CF.isFalseCtx final_state then ()
	  else PTracer.log_proof prf
	in
	  if not (U.empty rs) then begin
		rs
	  end else
		Err.report_error {Err.error_loc = pos;
						  Err.error_text = "Post condition "
			^ (Cprinter.string_of_formula post)
			^ " cannot be derived by the system."}

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
			(*print_string ("\n[typechecker.ml, line 658]: free vars(precond)" ^ Cprinter.string_of_spec_var_list (CF.fv (fst (List.hd proc.proc_static_specs))));*)
			Debug.devel_pprint (("Checking procedure ") ^ proc.proc_name ^ "... ") proc.proc_loc;
			Debug.devel_pprint ("Specs : " ^ Cprinter.string_of_struc_formula proc.proc_static_specs) proc.proc_loc;
			let ftypes, fnames = List.split proc.proc_args in
			(* fsvars are the spec vars corresponding to the parameters *)
			let fsvars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in
			(*Debug.devel_pprint ("fsvars : " ^ Cprinter.string_of_spec_var_list fsvars) proc.proc_loc;*)
			(* forall par. par = par' *)
			let nox = CF.formula_of_pure (CF.no_change fsvars proc.proc_loc) proc.proc_loc in
			(* -- 13.05.2008 *)
			let init_form = nox in(*
					if !Globals.max_renaming then
						(* if the max_renaming flag is on --> rename all the bound vars when doing the normalization *)
			   		(CF.normalize pre nox (CF.pos_of_formula pre))
			   	else
			   		(* if the max_renaming flag is off --> rename only the bound vars from pre which clash with the free vars of nox *)
			  	 	(CF.normalize_only_clash_rename pre nox (CF.pos_of_formula pre))
			  in*)
			  (* 13.05.2008 -- *)
			  (*Debug.devel_pprint ("Nox : " ^ Cprinter.string_of_formula nox) proc.proc_loc;
			  Debug.devel_pprint ("Normalized precond : " ^ Cprinter.string_of_formula init_form) proc.proc_loc;*)
 		    let init_ctx1 = CF.empty_ctx proc.proc_loc in
			let init_ctx = CF.build_context init_ctx1 init_form proc.proc_loc in
			(*let _ = print_string ("\n trans proc body: "^(Cprinter.string_of_exp body)^"\n") in*)
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
	let ctx = CF.build_context (CF.empty_ctx pos) c_lhs pos in
	let rs, prf = heap_entail prog false false [ctx] c_rhs pos in
	let _ = PTracer.log_proof prf in
	  if U.empty rs then begin
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


let check_prog (prog : prog_decl) =
  if !Globals.check_coercions then begin
	print_string "Checking coercions... ";
	ignore (check_coercion prog);
	print_string "DONE."
  end else begin
	ignore (List.map (check_data prog) prog.prog_data_decls);
	ignore (List.map (check_proc_wrapper prog) prog.prog_proc_decls)
  end
