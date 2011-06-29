open Globals
open Solver
open Cast
open Gen.Basic

module CF = Cformula
module CP = Cpure
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

let rec check_specs prog proc ctx spec_list e0 = 
  Gen.Debug.no_2 "check_specs" (Cprinter.string_of_context) (Cprinter.string_of_struc_formula) (string_of_bool) (fun ctx spec_list -> (check_specs_a prog proc ctx spec_list e0)) ctx spec_list

(* and check_specs prog proc ctx spec_list e0 = check_specs_a prog proc ctx spec_list e0 *)
      
(* assumes the pre, and starts the symbolic execution*)
and check_specs_a (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) (spec_list:CF.struc_formula) e0 : bool = 
  let rec do_spec_verification (spec: Cformula.ext_formula):bool = 
    (*let _ = print_string (Cprinter.string_of_ext_formula spec) in*)
    let pos_spec = CF.pos_of_struc_formula [spec] in
    log_spec := (Cprinter.string_of_ext_formula spec) ^ ", Line " ^ (string_of_int pos_spec.start_pos.Lexing.pos_lnum);	 
    match spec with
	  | Cformula.ECase b -> List.for_all (fun (c1,c2)-> 
			(*let _ = print_string ("check_specs: ECase: " ^ (Cprinter.string_of_context ctx) ^ "\n") in*)
		let mn = Cast.unmingle_name (proc.Cast.proc_name) in
        let f_formula = fun f -> None in
		let f_b_formula = function
		  | CP.BVar (CP.SpecVar (t,i,p), loc) -> Some (CP.BVar ((CP.SpecVar (t,i^"_"^mn,p)), loc))
		  | _ -> None
		in
		let f_exp = function
		  | CP.Var (CP.SpecVar (t,i,p), loc) -> Some (CP.Var ((CP.SpecVar (t,i^"_"^mn,p)), loc))
		  | _ -> None
		in
		let new_c1 = CP.transform_formula (true,true,f_formula,f_b_formula,f_exp) c1 in
		(*let _ = print_string ("c1: " ^ (Cprinter.string_of_pure_formula c1) ^ "\n") in
		let _ = print_string ("new c1: " ^ (Cprinter.string_of_pure_formula new_c1) ^ "\n") in*)
		
		    let nctx = CF.transform_context (fun es -> CF.Ctx {es with CF.es_var_ctx_lhs = CP.mkAnd es.CF.es_var_ctx_lhs new_c1 pos_spec}) ctx  in  
			let nctx = CF.transform_context (combine_es_and prog (MCP.mix_of_pure c1) true) nctx in
			(*let _ = print_string ("check_specs: ECase: " ^ (Cprinter.string_of_context nctx) ^ "\n") in*)
			let r = check_specs_a prog proc nctx c2 e0 in
			(*let _ = Debug.devel_pprint ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n") pos_spec in*)
			r) b.Cformula.formula_case_branches
	  | Cformula.EBase b ->
		    (*let _ = print_string ("check_specs: EBase: " ^ (Cprinter.string_of_context ctx) ^ "\n") in*)
	        let nctx = 
	          if !Globals.max_renaming 
	          then (CF.transform_context (CF.normalize_es b.Cformula.formula_ext_base b.Cformula.formula_ext_pos false) ctx)
	          else (CF.transform_context (CF.normalize_clash_es b.Cformula.formula_ext_base b.Cformula.formula_ext_pos false) ctx) in
			(*let _ = print_string ("check_specs: EBase: " ^ (Cprinter.string_of_context nctx) ^ "\n") in*)
	        let r = check_specs_a prog proc nctx b.Cformula.formula_ext_continuation e0 in
	        (*let _ = Debug.devel_pprint ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n") pos_spec in*)
	        r
	  | Cformula.EVariance b ->
			(*let _ = print_string ("check_specs: EVariance: " ^ (Cprinter.string_of_context ctx) ^ "\n") in*)
		    (*let _ = print_string "check_specs: EVariance: before nctx\n" in*)
			let nctx = CF.transform_context (fun es -> CF.Ctx {es with Cformula.es_var_measures = List.map (fun (e,b) -> e) b.Cformula.formula_var_measures;
			  Cformula.es_var_label = b.Cformula.formula_var_label}) ctx in
			(*let _ = print_string ("check_specs: EVariance: " ^ (Cprinter.string_of_context nctx) ^ "\n") in*)
		    check_specs_a prog proc nctx b.Cformula.formula_var_continuation e0
	  | Cformula.EAssume (x,b,y) ->
            let _ = set_post_pos (CF.pos_of_formula b) in
	        let ctx1 = CF.transform_context (elim_unsat_es prog (ref 1)) ctx in
	        (*let _ = print_string ("\n pre eli : "^(Cprinter.string_of_context ctx)^"\n post eli: "^(Cprinter.string_of_context ctx1)^"\n") in*)
	        if (Cformula.isAnyFalseCtx ctx1) then
		      let _ = print_string ("\nFalse precondition detected in procedure "^proc.proc_name^"\n with context: "^
				  (Cprinter.string_of_context_short ctx)) in 
		      true
	        else
		      let _ = Gen.Profiling.push_time ("method "^proc.proc_name) in
		      try 
		        let r = 
		          flow_store := [];
		          let ctx1 = CF.set_flow_in_context_override
			        { CF.formula_flow_interval = !n_flow_int; CF.formula_flow_link = None} ctx1 in
		          let ctx1 = CF.add_path_id ctx1 (Some y,-1) in
		          let lfe = [CF.mk_failesc_context ctx1 []] in 
			      let res_ctx = CF.list_failesc_to_partial (check_exp prog proc lfe e0 y) in
			      let res_ctx = Cformula.change_ret_flow_partial_ctx res_ctx in
				  (*let _ = print_string ("check_specs: EAssume: " ^ (Cprinter.string_of_list_partial_context res_ctx) ^ "\n") in*)
			      if (CF.isFailListPartialCtx res_ctx) then false
			      else
			        let tmp_ctx = check_post prog proc res_ctx b (Cformula.pos_of_formula b) y in
                    (* let _ = print_endline ("Answer after post :"^(string_of_int (List.length tmp_ctx))) in *)
			        (CF.isSuccessListPartialCtx tmp_ctx) 
		        in
		        let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in
		        r
		      with _ as e -> 
		          let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in raise e
  in	
  List.for_all do_spec_verification spec_list

and check_exp prog proc ctx e0 label = Gen.Debug.no_3 "check_exp" (fun proc -> proc.proc_name) (Cprinter.string_of_list_failesc_context) (Cprinter.string_of_exp) (Cprinter.string_of_list_failesc_context) (fun proc ctx e0 -> check_exp_a prog proc ctx e0 label) proc ctx e0

(* and check_exp prog proc ctx e0 label = check_exp_a prog proc ctx e0 label *)

and check_exp_a (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_failesc_context) e0 (post_start_label:formula_label) : CF.list_failesc_context = 
  if (exp_to_check e0) then  
    (* let _ = if (List.exists CF.isAnyFalseFailescCtx ctx) then *)
    (*   print_string ("\n false at :"^(Cprinter.string_of_exp e0))  *)
    (* else () in *)
    CF.find_false_list_failesc_ctx ctx (Cast.pos_of_exp e0) 
  else ();
	let check_exp1 (ctx : CF.list_failesc_context) : CF.list_failesc_context = 
      match e0 with
	    | Label e ->
	          let ctx = CF.add_path_id_ctx_failesc_list ctx e.exp_label_path_id in
	          let ctx = CF.add_cond_label_list_failesc_context (fst e.exp_label_path_id) (snd e.exp_label_path_id) ctx in
	          (check_exp prog proc ctx e.exp_label_exp post_start_label)
        | Unfold ({exp_unfold_var = sv;
          exp_unfold_pos = pos}) -> unfold_failesc_context (prog,None) ctx sv true pos 
	          (* for code *)
        | Assert ({ exp_assert_asserted_formula = c1_o;
          exp_assert_assumed_formula = c2;
          exp_assert_path_id = (pidi,s);
          exp_assert_pos = pos}) -> 
              begin
	            let s1 = snd post_start_label in
	            if (String.length s)>0 && (String.length s1)>0 && (String.compare s s1 <> 0)  then ctx
	            else
                  let (ts,ps) = List.partition (fun (fl,el,sl)-> (List.length fl) = 0) ctx in
	              let new_ctx = match c1_o with
                    | None -> ts
                    | Some c1 ->
                          let c1 = prune_pred_struc prog true c1 in (* specialise asserted formula *)
                          let to_print = "Proving assert/assume in method " ^ proc.proc_name ^ " for spec: \n" ^ !log_spec ^ "\n" in	
                          Debug.devel_pprint(*print_info "assert"*) to_print pos;
                          let rs,prf = heap_entail_struc_list_failesc_context_init prog false false ts c1 pos None in
                          let _ = PTracer.log_proof prf in                    
                          Debug.pprint(*print_info "assert"*) ("assert condition:\n" ^ (Cprinter.string_of_struc_formula c1)) pos;
                          if CF.isSuccessListFailescCtx rs then 
				            (Debug.print_info "assert" (s ^(if (CF.isNonFalseListFailescCtx ts) then " : ok\n" else ": unreachable\n")) pos;
				            Debug.pprint(*print_info "assert"*) ("Residual:\n" ^ (Cprinter.string_of_list_failesc_context rs)) pos)
				          else Debug.print_info "assert/assume" (s ^" : failed\n") pos ;
                          rs in 
                  let res = match c2 with
                    | None -> ts
                    | Some c ->
                          let c = prune_preds prog false c in (* specialise assumed formula *)
                          let assumed_ctx = CF.normalize_max_renaming_list_failesc_context c pos false new_ctx in
                          let r =CF.transform_list_failesc_context (idf,idf,(elim_unsat_es prog (ref 1))) assumed_ctx in
                          List.map CF.remove_dupl_false_fe r in
                  (ps@res)
	          end
        | Assign ({ exp_assign_lhs = v;
          exp_assign_rhs = rhs;
          exp_assign_pos = pos}) -> begin
            let ctx1 = check_exp prog proc ctx rhs post_start_label in
            let _ = CF.must_consistent_list_failesc_context "assign 1" ctx1  in
	        let fct c1 = 
	          if (CF.subsume_flow_f !n_flow_int (CF.flow_formula_of_formula c1.CF.es_formula)) then 
	            let t = Gen.unsome (type_of_exp rhs) in
	            let vsv = CP.SpecVar (t, v, Primed) in (* rhs must be non-void *)
	            let link = CF.formula_of_mix_formula (MCP.mix_of_pure (CP.mkEqVar vsv (P.mkRes t) pos)) pos in
                let ctx1 = (CF.Ctx c1) in
                let _ = CF.must_consistent_context "assign 1a" ctx1  in
                (* TODO : eps bug below *)
	            let tmp_ctx1 = CF.compose_context_formula ctx1 link [vsv] CF.Flow_combine pos in
                let _ = CF.must_consistent_context "assign 2" tmp_ctx1  in
	            let tmp_ctx2 = CF.push_exists_context [CP.mkRes t] tmp_ctx1 in
                let _ = CF.must_consistent_context "assign 3" tmp_ctx2  in
	            let resctx = if !Globals.elim_exists then elim_exists_ctx tmp_ctx2 else tmp_ctx2 in
                let _ = CF.must_consistent_context "assign 4" resctx  in
		        resctx 
	          else (CF.Ctx c1) in
	        let res = CF.transform_list_failesc_context (idf,idf,fct) ctx1 in
            let _ = CF.must_consistent_list_failesc_context "assign final" res  in
            res
	      end
        | BConst ({exp_bconst_val = b;
          exp_bconst_pos = pos}) -> begin
	        let res_v = CP.mkRes bool_type in
	        let tmp1 = CP.BForm (CP.BVar (res_v, pos), None) in
	        let tmp2 =
	          if b then tmp1
	          else CP.Not (tmp1, None, pos) in
	        let f = CF.formula_of_pure_N tmp2 pos in
	        CF.normalize_max_renaming_list_failesc_context f pos true ctx 
	      end
        | Bind ({ exp_bind_type = body_t;
          exp_bind_bound_var = (v_t, v);
          exp_bind_fields = lvars;
          exp_bind_body = body;
          exp_bind_imm = imm;
		  exp_bind_path_id = pid;
          exp_bind_pos = pos}) -> begin

	        (* let _  = print_string("BIND\n"); flush stdout in *)
	        (* let _ = print_string("\n\nbind body = " ^ (Cprinter.string_of_exp body) ^ "\n\n") in   *)


            (* Debug.devel_pprint ("bind: delta at beginning of bind\n" ^ (string_of_constr delta) ^ "\n") pos; *)
	        let _ = set_proving_loc pos in
	        let field_types, vs = List.split lvars in
	        let v_prim = CP.SpecVar (v_t, v, Primed) in
	        let vs_prim = List.map2 (fun v -> fun t -> CP.SpecVar (t, v, Primed)) vs field_types in
	        let p = CP.fresh_spec_var v_prim in
	        let link_pv = CF.formula_of_pure_N
	          (CP.mkAnd (CP.mkEqVar v_prim p pos) (CP.BForm (CP.mkNeq (CP.Var (p, pos)) (CP.Null pos) pos, None)) pos) pos in
	        (*let _ = print_string ("[typechecker.ml, check__exp]: link_pv: " ^ Cprinter.string_of_formula link_pv ^ "\n") in*)
	        (*	  let link_pv = CF.formula_of_pure (CP.mkEqVar v_prim p pos) pos in *)
	        let tmp_ctx =
	          if !Globals.large_bind then
	            CF.normalize_max_renaming_list_failesc_context link_pv pos false ctx
	          else ctx in
            let _ = CF.must_consistent_list_failesc_context "bind 1" ctx  in
	        let unfolded = unfold_failesc_context (prog,None) tmp_ctx v_prim true pos in
	        (* let unfolded_prim = if !Globals.elim_unsat then elim_unsat unfolded else unfolded in *)
            let _ = CF.must_consistent_list_failesc_context "bind 2" unfolded  in
	        let _ = Debug.devel_pprint ("bind: unfolded context:\n" ^ (Cprinter.string_of_list_failesc_context unfolded)
            ^ "\n") pos in
	        (* let _ = print_string ("bind: unfolded context:\n" ^ (Cprinter.string_of_list_failesc_context unfolded) *)
            (*     ^ "\n") in *)

	        let c = string_of_typ v_t in
	        let vdatanode = CF.DataNode ({
                CF.h_formula_data_node = (if !Globals.large_bind then p else v_prim);
                CF.h_formula_data_name = c;
			    CF.h_formula_data_imm = imm;
                CF.h_formula_data_arguments = (*t_var :: ext_var ::*) vs_prim;
                CF.h_formula_data_label = None;
                CF.h_formula_data_remaining_branches = None;
                CF.h_formula_data_pruning_conditions = [];
                CF.h_formula_data_pos = pos}) in
	        let vheap = CF.formula_of_heap vdatanode pos in
		    let vheap = prune_preds prog false vheap in
	        let to_print = "Proving binding in method " ^ proc.proc_name ^ " for spec " ^ !log_spec ^ "\n" in
	        Debug.devel_pprint to_print pos;
			if (Gen.is_empty unfolded) then unfolded
			else 
	          let rs_prim, prf = heap_entail_list_failesc_context_init prog false  unfolded vheap pos pid in
              let _ = CF.must_consistent_list_failesc_context "bind 3" rs_prim  in
	          let _ = PTracer.log_proof prf in
	          let rs = CF.clear_entailment_history_failesc_list rs_prim in
              let _ = CF.must_consistent_list_failesc_context "bind 4" rs  in
	          if (CF.isSuccessListFailescCtx unfolded) && not(CF.isSuccessListFailescCtx rs) then   
                begin
		          Debug.print_info ("("^(Cprinter.string_of_label_list_failesc_context rs)^") ") 
                      ("bind: node " ^ (Cprinter.string_of_h_formula vdatanode) ^ " cannot be derived from context\n") pos; (* add branch info *)
		          Debug.print_info ("(Cause of Failure)")
                     (Cprinter.string_of_failure_list_failesc_context rs) pos;
		          rs
                end
              else 
                begin
                  let tmp_res1 = check_exp prog proc rs body post_start_label in 
                  let _ = CF.must_consistent_list_failesc_context "bind 5" tmp_res1  in
		          (* let _ = print_string ("bind: tmp_res1:\n" ^ (Cprinter.string_of_list_failesc_context tmp_res1) *)
                  (*   ^ "\n") in *)
                  let tmp_res2 = 
		            if (not imm) then
		              CF.normalize_max_renaming_list_failesc_context vheap pos true tmp_res1 
		            else tmp_res1
		          in
                  let _ = CF.must_consistent_list_failesc_context "bind 6" tmp_res2  in
		          (* let _ = print_string ("bind: tmp_res2:\n" ^ (Cprinter.string_of_list_failesc_context tmp_res2) *)
                  (* ^ "\n") in  *)
                  let tmp_res3 = CF.push_exists_list_failesc_context vs_prim tmp_res2 in
                   let _ = CF.must_consistent_list_failesc_context "bind 7" tmp_res3  in
                  (* let _ = print_string ("bind: tmp_res3:\n" ^ (Cprinter.string_of_list_failesc_context tmp_res3) *)
                  (*     ^ "\n") in *)
		           let res = if !Globals.elim_exists then elim_exists_failesc_ctx_list tmp_res3 else tmp_res3 in
                   let _ = CF.must_consistent_list_failesc_context "bind 8" res  in
                   res
	                
                end
          end;
	          
        | Block ({exp_block_type = t;
          exp_block_body = e;
          exp_block_local_vars = local_vars;
          exp_block_pos = pos}) -> begin
	        let ctx1 = check_exp prog proc ctx e post_start_label in
	        let svars = List.map (fun (t, n) -> CP.SpecVar (t, n, Primed)) local_vars in
	        let ctx2 = CF.push_exists_list_failesc_context svars ctx1 in
	        if !Globals.elim_exists then elim_exists_failesc_ctx_list ctx2 else ctx2
	      end
		| Catch b -> Error.report_error {Err.error_loc = b.exp_catch_pos;
          Err.error_text = "[typechecker.ml]: malformed cast, unexpected catch clause"}
        | Cond ({ exp_cond_type = t;
          exp_cond_condition = v;
          exp_cond_then_arm = e1;
          exp_cond_else_arm = e2;
          exp_cond_path_id =pid;
          exp_cond_pos = pos}) -> begin
	        let pure_cond = (CP.BForm (CP.mkBVar v Primed pos, None)) in
	        let then_cond_prim = MCP.mix_of_pure pure_cond in
	        let else_cond_prim = MCP.mix_of_pure (CP.mkNot pure_cond None pos) in
	        let then_ctx = combine_list_failesc_context_and_unsat_now prog ctx then_cond_prim in
	        Debug.devel_pprint ("conditional: then_delta:\n" ^ (Cprinter.string_of_list_failesc_context then_ctx)) pos;
	        let else_ctx =combine_list_failesc_context_and_unsat_now prog ctx else_cond_prim in
	        Debug.devel_pprint ("conditional: else_delta:\n" ^ (Cprinter.string_of_list_failesc_context else_ctx)) pos;
	        let then_ctx1 = CF.add_cond_label_list_failesc_context pid 0 then_ctx in
	        let else_ctx1 = CF.add_cond_label_list_failesc_context pid 1 else_ctx in 
	        let then_ctx2 = check_exp prog proc then_ctx1 e1 post_start_label in
	        let else_ctx2 = check_exp prog proc else_ctx1 e2 post_start_label in
	        let res = CF.list_failesc_context_or (Cprinter.string_of_esc_stack) then_ctx2 else_ctx2 in
		    res
	      end;
        | Dprint ({exp_dprint_string = str;
          exp_dprint_visible_names = visib_names;
          exp_dprint_pos = pos}) -> begin
		    let ctx = prune_ctx_failesc_list prog ctx in
            let ctx = list_failesc_context_and_unsat_now prog ctx in
            if str = "" then begin
              let str1 = (Cprinter.string_of_list_failesc_context ctx)  in
	          (if (Gen.is_empty ctx) then
                (print_string ("\ndprint: empty/false context")) 
	          else
                let tmp1 = "\ndprint: " ^ pos.start_pos.Lexing.pos_fname
                  ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^ ": ctx: " ^ str1 ^ "\n" in
                let tmp1 = if (previous_failure ()) then ("failesc context: "^tmp1) else tmp1 in
                print_string tmp1);
              ctx
            end else begin
              ignore (Drawing.dot_of_partial_context_file prog ctx visib_names str);
              ctx
            end
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
          exp_icall_pos = pos}) ->
              Err.report_error {Err.error_loc = pos;
              Err.error_text = "[typechecker.ml]: We do not support instant calls"}
        | IConst ({exp_iconst_val = i;
          exp_iconst_pos = pos}) ->
	          let c_e = CP.IConst (i, pos) in
	          let res_v = CP.Var (CP.mkRes int_type, pos) in
	          let f = CF.formula_of_mix_formula (MCP.mix_of_pure (CP.mkEqExp res_v c_e pos)) pos in
	          let res_ctx = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
	          res_ctx
        | FConst {exp_fconst_val = f; exp_fconst_pos = pos} ->
	          let c_e = CP.FConst (f, pos) in
	          let res_v = CP.Var (CP.mkRes float_type, pos) in
	          let f = CF.formula_of_mix_formula (MCP.mix_of_pure (CP.mkEqExp res_v c_e pos)) pos in
	          let res_ctx = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
	          res_ctx
        | New ({exp_new_class_name = c;
          exp_new_parent_name = pname;
          exp_new_arguments = args;
          exp_new_pos = pos}) -> begin
	        let field_types, vs = List.split args in
	        let heap_args = List.map2 (fun n -> fun t -> CP.SpecVar (t, n, Primed))
	          vs field_types in
	        let heap_node = CF.DataNode ({
                CF.h_formula_data_node = CP.SpecVar (Named c, res, Unprimed);
                CF.h_formula_data_name = c;
		        CF.h_formula_data_imm = false;
                CF.h_formula_data_arguments =(*type_var :: ext_var :: *) heap_args;
                CF.h_formula_data_remaining_branches = None;
                CF.h_formula_data_pruning_conditions = [];
                CF.h_formula_data_label = None;
                CF.h_formula_data_pos = pos}) in
	        (*c let heap_form = CF.mkExists [ext_var] heap_node ext_null type_constr pos in*)
	        let heap_form = CF.mkBase heap_node (MCP.mkMTrue pos) CF.TypeTrue (CF.mkTrueFlow ()) [] pos in
            let heap_form = prune_preds prog false heap_form in
	        let res = CF.normalize_max_renaming_list_failesc_context heap_form pos true ctx in
	        res
	      end;
        | Null pos ->
	          let p = CP.mkEqExp (CP.mkVar (CP.SpecVar (Named "", res, Unprimed)) pos) (CP.Null pos) pos in
	          let f = CF.formula_of_mix_formula (MCP.mix_of_pure p) pos in
	          let res = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
	          res
		| EmptyArray _ -> ctx (* An Hoa : no change in context for empty array *)
        | SCall ({exp_scall_type = ret_t;
          exp_scall_method_name = mn;
          exp_scall_arguments = vs;
		  exp_scall_is_rec = ir;
          exp_scall_path_id = pid;
          exp_scall_pos = pos}) -> begin (* mn is mingled name of the method *)
	        let _ = set_proving_loc pos in
	        let proc = look_up_proc_def pos prog.prog_proc_decls mn in
	        let farg_types, farg_names = List.split proc.proc_args in
	        let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
	        let actual_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) vs farg_types in
	        let check_pre_post org_spec (sctx:CF.list_failesc_context):CF.list_failesc_context =
			  (* Stripping the "variance" feature from org_spec if the call is not a recursive call *)
			  (*print_string ("\ncheck_specs: SCall: " ^ (if ir then "is rec: " else "") ^ "org_spec: " ^ (Cprinter.string_of_struc_formula org_spec) ^ "\n");*)
			  (*let _ = print_string ("\ncheck_pre_post@SCall@check_exp: org_spec" ^ (Cprinter.string_of_struc_formula org_spec) ^ "\n") in*)
			  let stripped_spec = if ir then org_spec else
				let rec strip_variance ls = match ls with
				  | [] -> []
				  | spec::rest -> match spec with
					  | Cformula.EVariance e -> (strip_variance e.Cformula.formula_var_continuation)@(strip_variance rest)
					  | Cformula.EBase b -> (Cformula.EBase {b with Cformula.formula_ext_continuation = strip_variance b.Cformula.formula_ext_continuation})::(strip_variance rest)
					  | Cformula.ECase c -> (Cformula.ECase {c with Cformula.formula_case_branches = List.map (fun (cpf, sf) -> (cpf, strip_variance sf)) c.Cformula.formula_case_branches})::(strip_variance rest)
					  | _ -> spec::(strip_variance rest)
				in strip_variance org_spec
			  in
			  (*let _ = print_string ("\ncheck_specs: SCall: " ^ (if ir then "is rec: " else "") ^ "stripped_spec: " ^ (Cprinter.string_of_struc_formula stripped_spec) ^ "\n") in*)
			  (* org_spec -> stripped_spec *)
	          (* free vars = linking vars that appear both in pre and are not formal arguments *)
	          let pre_free_vars = Gen.BList.difference_eq CP.eq_spec_var (Gen.BList.difference_eq CP.eq_spec_var (Cformula.struc_fv stripped_spec(*org_spec*)) (Cformula.struc_post_fv stripped_spec(*org_spec*))) farg_spec_vars in
	          (* free vars get to be substituted by fresh vars *)
	          let pre_free_vars_fresh = CP.fresh_spec_vars pre_free_vars in
	          let renamed_spec = 
                if !Globals.max_renaming then (Cformula.rename_struc_bound_vars stripped_spec(*org_spec*))
                else (Cformula.rename_struc_clash_bound_vars stripped_spec(*org_spec*) (CF.formula_of_list_failesc_context sctx))
	          in
	          let st1 = List.combine pre_free_vars pre_free_vars_fresh in
			  (*let _ = print_string (List.fold_left (fun res (p1, p2) -> res ^ "(" ^ (Cprinter.string_of_spec_var p1) ^ "," ^ (Cprinter.string_of_spec_var p2) ^ ") ") "\ncheck_spec: mapping org_spec to new_spec: \n" st1) in*)
	          let fr_vars = farg_spec_vars @ (List.map CP.to_primed farg_spec_vars) in
	          let to_vars = actual_spec_vars @ (List.map CP.to_primed actual_spec_vars) in

			  (*let l = (String.index mn '$') in
              let new_mn = String.create l in
			  let _ = print_string ("mn: " ^ mn ^ "\n") in
			  let _ = String.blit mn 0 new_mn 0 l in
			  let _ = print_string ("New mn: " ^ new_mn ^ "\n") in*)
			  let var_subst = List.map2 (fun e1 e2 -> (e1, e2, (Cast.unmingle_name mn))) to_vars fr_vars in
			  let sctx = List.map
				(fun fctx -> let (lb,estk,lbctx) = fctx in
							 let nlbctx = List.map
							   (fun bctx -> let (pt,ctx) = bctx in
											let nctx = CF.transform_context
											  (fun es -> CF.Ctx {es with CF.es_var_subst = es.CF.es_var_subst @ var_subst}) ctx in (pt,nctx)) lbctx in
				             (lb,estk,nlbctx)) sctx in

			  
			  (*let _ = print_string ("\ncheck_pre_post@SCall@check_exp: renamed_spec1: " ^ (Cprinter.string_of_struc_formula renamed_spec) ^ "\n") in*)
	          let renamed_spec = CF.subst_struc st1 renamed_spec in
			  
			  (*let _ = print_string ("\ncheck_pre_post@SCall@check_exp: renamed_spec2: " ^ (Cprinter.string_of_struc_formula renamed_spec) ^ "\n") in
			  let _ = print_string ("\ncheck_pre_post@SCall@check_exp: fr_vars: " ^ (Cprinter.string_of_spec_var_list fr_vars) ^ "\n") in
			  let _ = print_string ("\ncheck_pre_post@SCall@check_exp: to_vars: " ^ (Cprinter.string_of_spec_var_list to_vars) ^ "\n") in*)				
	          let renamed_spec = CF.subst_struc_avoid_capture fr_vars to_vars renamed_spec in

			  (*let _ = print_string ("\ncheck_pre_post@SCall@check_exp: renamed_spec3: " ^ (Cprinter.string_of_struc_formula renamed_spec) ^ "\n") in*)
	          let st2 = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) actual_spec_vars in
	          let pre2 = CF.subst_struc_pre st2 renamed_spec in
              let new_spec = (Cprinter.string_of_struc_formula pre2) in
			  (*let _ = print_string ("\ncheck_pre_post@SCall@check_exp: new_spec: " ^ new_spec ^ "\n") in*)
			  (* Termination checking *)
			  let str_debug_variance = if (ir) then "Checking the termination of the recursive call " ^ mn ^ " in method " ^ proc.proc_name ^ ": " ^ (Cprinter.string_of_pos pos) ^ "\n" else "" in
			  Debug.devel_pprint (str_debug_variance ^ "\n") pos;
			  (*print_string (str_debug_variance ^ "\n");*)
			  (* TODO: call the entailment checking function in solver.ml *)
	          let to_print = "Proving precondition in method " ^ proc.proc_name ^ " for spec:\n" ^ new_spec
                (*!log_spec*) in
	          Debug.devel_pprint (to_print^"\n") pos;
	          let rs,prf = heap_entail_struc_list_failesc_context_init prog false true sctx pre2 pos pid in
		      let _ = PTracer.log_proof prf in
              (*let _ = print_string ((Cprinter.string_of_list_failesc_context rs)^"\n") in*)
				
              if (CF.isSuccessListFailescCtx sctx) && (CF.isFailListFailescCtx rs) then
                Debug.print_info "procedure call" (to_print^" has failed \n") pos else () ;
              rs in	        
	        let check_pre_post org_spec (sctx:CF.list_failesc_context):CF.list_failesc_context =
              let _ = Cprinter.string_of_list_failesc_context in
              let pr2 = Cprinter.summary_list_failesc_context in
              let pr3 = Cprinter.string_of_struc_formula in
              Gen.Debug.loop_2_no "check_pre_post" pr3 pr2 pr2 (fun _ _ ->  check_pre_post org_spec sctx) org_spec sctx in
	        let res = if(CF.isFailListFailescCtx ctx) then ctx
            else check_pre_post proc.proc_static_specs_with_pre ctx in	
		    
            res
          end
        | Seq ({exp_seq_type = te2;
          exp_seq_exp1 = e1;
          exp_seq_exp2 = e2;
          exp_seq_pos = pos}) -> begin
	        let ctx1 = check_exp prog proc ctx e1 post_start_label (*flow_store*) in (* Astsimp ensures that e1 is of type void *)
	        check_exp prog proc ctx1 e2 post_start_label (*flow_store*)
	      end
        | Time (b,s,_) -> if b then Gen.Profiling.push_time s else Gen.Profiling.pop_time s; ctx
        | This ({exp_this_type = t;
          exp_this_pos = pos}) -> 
              begin
                let tmp = CF.formula_of_mix_formula  (MCP.mix_of_pure (CP.mkEqVar (CP.mkRes t) (CP.SpecVar (t, "this", Unprimed)) pos)) pos in
                CF.normalize_max_renaming_list_failesc_context tmp pos true ctx 
              end
        | Var ({exp_var_type = t;
          exp_var_name = v;
          exp_var_pos = pos}) -> 
              begin
                let tmp = CF.formula_of_mix_formula  (MCP.mix_of_pure (CP.mkEqVar (CP.mkRes t) (CP.SpecVar (t, v, Primed)) pos)) pos in
                CF.normalize_max_renaming_list_failesc_context tmp pos true ctx 
              end
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
		              let tmp = CF.formula_of_mix_formula  (MCP.mix_of_pure (CP.mkEqVar (CP.mkRes t) (CP.SpecVar (t, v, Primed)) pos)) pos in
		              let ctx1 = CF.normalize_max_renaming_list_failesc_context tmp pos true ctx in
		              ctx1
	            | Sharp_finally v -> 
		              let fct es = 
		                let rest, b_rez = CF.get_var_type v es.CF.es_formula in
		                if b_rez then
                          let vsv_f = CF.formula_of_mix_formula  (MCP.mix_of_pure (CP.mkEqVar (CP.SpecVar (rest, v, Primed)) (P.mkRes rest) pos)) pos in
			              if !Globals.max_renaming then CF.normalize_es vsv_f pos true es
			              else CF.normalize_clash_es vsv_f pos true es
		                else CF.Ctx es
		              in
		              CF.transform_list_failesc_context (idf,idf,fct) ctx
	            | Sharp_no_val -> ctx in
	          let r = match ft with 
                | Sharp_ct nf -> 
			          if not un then 
                        CF.transform_list_failesc_context 
                            (idf,idf,(fun es -> CF.Ctx {es with CF.es_formula = CF.set_flow_in_formula nf es.CF.es_formula})) nctx
			          else CF.transform_list_failesc_context 
                        (idf,idf,(fun es -> CF.Ctx {es with CF.es_formula = CF.set_flow_to_link_f !flow_store es.CF.es_formula no_pos})) nctx
                | Sharp_v v -> CF.transform_list_failesc_context 
			          (idf,idf,
                      (fun es -> CF.Ctx {es with CF.es_formula = CF.set_flow_in_formula (CF.get_flow_from_stack v !flow_store pos) es.CF.es_formula}))
                          nctx in
	          CF.add_path_id_ctx_failesc_list r (pid,0)
        | Try ({exp_try_body = body;
      	  exp_catch_clause = cc;
      	  exp_try_path_id = pid;
      	  exp_try_pos = pos })->
		      let cc = get_catch_of_exp cc in
              let ctx = CF.transform_list_failesc_context (idf,(fun c-> CF.push_esc_level c pid),(fun x-> CF.Ctx x)) ctx in
	          let ctx1 = check_exp prog proc ctx body post_start_label in
              let ctx2 = CF.pop_esc_level_list ctx1 pid in
              let ctx3 = CF.transform_list_failesc_context (idf,(fun c-> CF.push_esc_level c pid),(fun x-> CF.Ctx x)) ctx2 in
              let ctx4 = CF.splitter_failesc_context (cc.exp_catch_flow_type) (cc.exp_catch_var) 
                (fun c -> CF.add_path_id c (Some pid,0)) elim_exists_ctx ctx3 in
              let ctx5 = check_exp prog proc ctx4 cc.exp_catch_body post_start_label in
              CF.pop_esc_level_list ctx5 pid
	    | _ -> 
	          failwith ((Cprinter.string_of_exp e0) ^ " is not supported yet")  in
    let ctx = if (not !Globals.failure_analysis) then List.filter (fun (f,s,c)-> Gen.is_empty f ) ctx  
    else ctx in
    let (fl,cl) = List.partition (fun (_,s,c)-> Gen.is_empty c && CF.is_empty_esc_stack s) ctx in
    (* if (Gen.is_empty cl) then fl
       else *)	    
    let failesc = CF.splitter_failesc_context !n_flow_int None (fun x->x)(fun x -> x) cl in
    ((check_exp1 failesc) @ fl)
        
and check_post (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_partial_context) (post : CF.formula) pos (pid:formula_label) : CF.list_partial_context  =
  (* let ctx = list_partial_context_and_unsat_now prog ctx in *)
  let _ = pr_list Cprinter.string_of_partial_context in
  let pr1 x = string_of_int (List.length x) in
  let pr2 x = "List Partial Context "^(pr_list (pr_pair pr1 pr1) x) in
  Gen.Debug.no_2(* loop_2_no *) "check_post" Cprinter.string_of_pos pr2 pr2  
      (fun _ _ -> 
          let r = check_post_x prog proc ctx post pos pid in
          (* let r = list_partial_context_and_unsat_now prog r in *)
          r ) pos ctx

and check_post_x (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_partial_context) (post : CF.formula) pos (pid:formula_label) : CF.list_partial_context  =
  (*let _ = print_string ("got into check_post on the succCtx branch\n") in*)
  (*let _ = print_string ("context before post: "^(Cprinter.string_of_list_partial_context ctx)^"\n") in*)
  let vsvars = List.map (fun p -> CP.SpecVar (fst p, snd p, Unprimed))
    proc.proc_args in
  let r = proc.proc_by_name_params in
  let w = List.map CP.to_primed (Gen.BList.difference_eq CP.eq_spec_var vsvars r) in
  (* print_string ("\nLength of List Partial Ctx: " ^ (Cprinter.summary_list_partial_context(ctx)));  *)
  let final_state_prim = CF.push_exists_list_partial_context w ctx in
  (* print_string ("\nLength of List Partial Ctx: " ^ (Cprinter.summary_list_partial_context(final_state_prim)));  *)
  (* let _ = print_flush ("length:"^(string_of_int (List.length final_state_prim))) in *)
  let final_state = 
    if !Globals.elim_exists then (elim_exists_partial_ctx_list final_state_prim) else final_state_prim in
  (* Debug.devel_print ("Final state:\n" ^ (Cprinter.string_of_list_partial_context final_state_prim) ^ "\n"); *)
  (*  Debug.devel_print ("Final state after existential quantifier elimination:\n" *)
  (* ^ (Cprinter.string_of_list_partial_context final_state) ^ "\n"); *)
  Debug.devel_pprint ("Post-cond:\n" ^ (Cprinter.string_of_formula  post) ^ "\n") pos;
  let to_print = "Proving postcondition in method " ^ proc.proc_name ^ " for spec\n" ^ !log_spec ^ "\n" in
  Debug.devel_pprint to_print pos;
  let rs, prf = heap_entail_list_partial_context_init prog false final_state post pos (Some pid) in
  let _ = PTracer.log_proof prf in
  if (CF.isSuccessListPartialCtx rs) then 
    rs
  else begin
    (* get source code position of failed branches *)
    let locs_of_failures = 
      List.fold_left (fun res ctx -> res @ (locs_of_partial_context ctx)) [] rs 
    in
    let string_of_loc_list locs =
      List.fold_left (fun res l -> res ^ (string_of_loc_by_char_num l) ^ ",") "" locs
    in
    Err.report_error {
        Err.error_loc = pos;
        Err.error_text = Printf.sprintf
			(* "Post condition %s cannot be derived by the system.\n By: %s \n fail ctx: %s\nPossible locations of failures: %s." *)
            "Post condition cannot be derived by the system."
            (*(Cprinter.string_of_formula post)
              (Cprinter.string_of_list_partial_context final_state)
              (Cprinter.string_of_list_partial_context rs)
              (string_of_loc_list locs_of_failures)*)
    }
  end


(* checking procedure *)
and check_proc (prog : prog_decl) (proc : proc_decl) : bool =
  let unmin_name = unmingle_name proc.proc_name in
  let check_flag = ((Gen.is_empty !procs_verified) || List.mem unmin_name !procs_verified)
    && not (List.mem unmin_name !Inliner.inlined_procs)
  in
  if check_flag then begin
    match proc.proc_body with
	  | None -> true (* sanity checks have been done by the translation *)
	  | Some body -> begin
	      if !Globals.print_proc then
	        print_string ("Procedure " ^ proc.proc_name ^ ":\n"
			^ (Cprinter.string_of_proc_decl 3 proc) ^ "\n\n");
	      print_string (("Checking procedure ") ^ proc.proc_name ^ "... "); flush stdout;
	      Debug.devel_pprint (("Checking procedure ") ^ proc.proc_name ^ "... ") proc.proc_loc;
	      Debug.devel_pprint ("Specs :\n" ^ Cprinter.string_of_struc_formula proc.proc_static_specs) proc.proc_loc;
	      let ftypes, fnames = List.split proc.proc_args in
	      (* fsvars are the spec vars corresponding to the parameters *)
	      let fsvars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in
	      (*Debug.devel_pprint ("fsvars : " ^ Cprinter.string_of_spec_var_list fsvars) proc.proc_loc;*)
	      let nox = CF.formula_of_pure_N (CF.no_change fsvars proc.proc_loc) proc.proc_loc in
	      let init_form = nox in(*
				                  if !Globals.max_renaming then
	      (* if the max_renaming flag is on --> rename all the bound vars when doing the normalization *)
			   	                  (CF.normalize pre nox (CF.pos_of_formula pre))
			   	                  else
	      (* if the max_renaming flag is off --> rename only the bound vars from pre which clash with the free vars of nox *)
			  	                  (CF.normalize_only_clash_rename pre nox (CF.pos_of_formula pre))
				                  in*)
	      let init_ctx1 = CF.empty_ctx (CF.mkTrueFlow ()) proc.proc_loc in
		  (*let _ = print_string ("check_proc: init_ctx1: " ^ (Cprinter.string_of_context init_ctx1) ^ "\n") in
		    let _ = print_string ("check_proc: init_form: " ^ (Cprinter.string_of_formula init_form) ^ "\n") in*)
	      let init_ctx = CF.build_context init_ctx1 init_form proc.proc_loc in
		  (*let _ = print_string ("check_proc: init_ctx: " ^ (Cprinter.string_of_context init_ctx) ^ "\n") in*)
		  (* Add es_var_measures *)
		  (*let init_ctx = CF.add_es_var_measures init_ctx2 proc.proc_static_specs in*)
	      let pp = check_specs prog proc init_ctx (proc.proc_static_specs @ proc.proc_dynamic_specs) body in
	      let result =
	        if pp then begin
		      print_string ("\nProcedure "^proc.proc_name^" SUCCESS\n");
		      true
	        end else begin print_string ("\nProcedure "^proc.proc_name^" result FAIL-1\n"); false end in
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
(* check_proc prog proc *)
  try
    check_proc prog proc  
  with _ as e ->
    if !Globals.check_all then begin
      (* dummy_exception(); *)
      print_string ("\nProcedure "^proc.proc_name^" FAIL-2\n");
      print_string ("\nException"^(Printexc.to_string e)^"Occurred!\n");
      Printexc.print_backtrace(stdout);
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
  if not (Gen.is_empty cdef.data_methods) then
	print_string ("\nChecking class " ^ cdef.data_name ^ "...\n\n");
  List.map (check_proc_wrapper prog) cdef.data_methods

let check_coercion (prog : prog_decl) =
  let check_entailment c_lhs c_rhs =
    let pos = CF.pos_of_formula c_lhs in
    let ctx = CF.build_context (CF.empty_ctx (CF.mkTrueFlow ()) pos) c_lhs pos in
    let rs, prf = heap_entail_init prog false (CF.SuccCtx [ctx]) c_rhs pos in
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
    let lhs = unfold_nth 9 (prog,None) coer.coercion_head (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
    let rhs = unfold_nth 10 (prog,None) coer.coercion_body (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
      check_entailment lhs rhs in
    (* check_entailment lhs coer.coercion_body in *)
  let check_right_coercion coer =
    let pos = CF.pos_of_formula coer.coercion_head in
    let rhs = unfold_nth 11 (prog,None) coer.coercion_head (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
    let lhs = unfold_nth 12 (prog,None) coer.coercion_body (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
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
    | Time _ -> 1
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
      print_string ("\nProcedure "^proc.proc_name^" FAIL-3\n");
      print_string ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      false
    end else
      raise e 

let check_proc_wrapper_map_net prog (proc,num) =
  try
    check_proc prog proc
  with _ as e ->
    if !Globals.check_all then begin
      print_string ("\nProcedure "^proc.proc_name^" FAIL-4\n");
      print_string ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      false
    end else
      raise e


let rec equalpf_a f1 f2 =
  let r1,_,_ = (Tpdispatcher.imply f1 f2 "" false None) in
  let r2,_,_ = (Tpdispatcher.imply f2 f1 "" false None) in
  r1 & r2

and equalpf f1 f2 = Gen.Debug.no_2 "equalpf" (Cprinter.string_of_pure_formula) (Cprinter.string_of_pure_formula) (string_of_bool) equalpf_a f1 f2

and comparepf_a f1 f2 =
  let r1,_,_ = (Tpdispatcher.imply f1 f2 "" false None) in
  let r2,_,_ = (Tpdispatcher.imply f2 f1 "" false None) in
  if (r1 & r2) then 0
  else compare (Cprinter.string_of_pure_formula f1) (Cprinter.string_of_pure_formula f2)
	
and comparepf f1 f2 = Gen.Debug.no_2 "comparepf" (Cprinter.string_of_pure_formula) (Cprinter.string_of_pure_formula) (string_of_int) comparepf_a f1 f2

module FComp = struct
  type t = CP.formula
  let compare = comparepf
  let hash = Hashtbl.hash
  let equal = equalpf
end
module IG = Graph.Persistent.Digraph.Concrete(FComp)
module IGO = Graph.Oper.P(IG)
module IGN = Graph.Oper.Neighbourhood(IG)
module IGC = Graph.Components.Make(IG)
module IGP = Graph.Path.Check(IG)

module IComp = struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end
module GS = Graph.Persistent.Digraph.Concrete(IComp)
module GSO = Graph.Oper.P(GS)
module GSN = Graph.Oper.Neighbourhood(GS)
module GSC = Graph.Components.Make(GS)
module GSP = Graph.Path.Check(GS)

  
let build_state_trans_graph ls =
  (*print_string ("\ncheck_prog: call graph:\n" ^
	(List.fold_left (fun rs (f1,f2) -> rs ^ "\n" ^ (Cprinter.string_of_pure_formula f1) ^ " ->" ^ (Cprinter.string_of_pure_formula f2)) "" !Solver.graph) ^ "\n");*)

  let gr = IG.empty in
  let g = List.fold_left (fun g (f1,f2) ->
    let ng1 = IG.add_vertex g f1 in
	(*let _ = print_string (if (ng1 = g) then (Cprinter.string_of_pure_formula f1) ^ ": not added\n" else (Cprinter.string_of_pure_formula f1) ^ ": added\n") in*)
	let ng2 = IG.add_vertex ng1 f2 in
	(*let _ = print_string (if (ng2 = ng1) then (Cprinter.string_of_pure_formula f2) ^ ": not added\n" else (Cprinter.string_of_pure_formula f2) ^ ": added\n") in*)
	let ng3 = IG.add_edge ng2 f1 f2 in
	(*let _ = print_string (let edge = "Edge " ^ (Cprinter.string_of_pure_formula f1) ^ "->" ^ (Cprinter.string_of_pure_formula f2) in
						  if (ng3 = ng2) then edge ^ ": not added\n" else edge ^ ": added\n") in*)
	ng3) gr ls in
  g

let scc_numbering g =
  (*let _ = print_string "List of vertices:\n" in
  let _ = IG.iter_vertex (fun v -> print_string ((Cprinter.string_of_pure_formula v) ^ "\n")) g in*)
  
  let scc_list = IGC.scc_list g in
  
  (*let _ = print_string ("The number of scc: " ^ (string_of_int (List.length scc_list)) ^ "\n") in
  let _ = List.iter (fun ls -> List.iter (fun v -> print_string ((Cprinter.string_of_pure_formula v) ^ "; "); print_string "\n") ls) scc_list in*)

  let scc_list = snd (List.fold_left (fun (n,rs) l -> (n+1, rs @ [(n,l)])) (0,[]) scc_list) in

  (*let _ = print_string ("New scc list: " ^ (string_of_int (List.length scc_list)) ^ "\n") in
  let _ = List.iter (fun (n,ls) -> print_string ((string_of_int n) ^ ": "); List.iter (fun v -> print_string ((Cprinter.string_of_pure_formula v) ^ "; "); print_string "\n") ls) scc_list in*)

  let mem e ls = List.fold_left (fun rs e1 -> if (equalpf e e1) then true else rs) false ls in
  let meml ls1 ls2 = List.fold_left (fun rs e -> if (mem e ls2) then true else rs) false ls1 in
  
  let scc_graph = GS.empty in
  
  let scc_graph = List.fold_left (fun sg (n,_) -> GS.add_vertex sg n) scc_graph scc_list in

  let scc_graph = List.fold_left (fun sg (n,l) ->
	let neighbours = IGN.list_from_vertices g l in
	List.fold_left (fun nsg (n1,l1) -> if (meml l1 neighbours) then GS.add_edge nsg n n1 else nsg) sg scc_list 
  ) scc_graph scc_list in

  let (nscc, fscc) = GSC.scc scc_graph in

  (*let lscc = GSC.scc_list scc_graph in*)

  (*let _ = print_string ("The number of transformed scc: " ^ (string_of_int nscc) ^ "\n") in
  let _ = List.iter (fun ls -> List.iter (fun v -> print_string ((string_of_int v) ^ "; "); print_string "\n") ls) lscc in
  let _ = print_string ("The mapping from label to scc number: \n") in
  let _ = List.iter (fun (n,_) -> print_string ((string_of_int n) ^ "->" ^ (string_of_int (fscc n)) ^ "\n")) scc_list in*)

  fun v -> List.fold_left (fun rs (n,l) -> if (mem v l) then (fscc n) else rs) 0 scc_list
  

let variance_numbering ls g =
  let f = scc_numbering g in
  let nf = fun v -> if ((List.length (IGN.list_from_vertex g v)) = 0) then 0 else (f v) in
  let helper ele =
	let (es,e) = ele in
	let nes = {es with CF.es_var_label =
		let user_defined_var_label_lhs = es.CF.es_var_label in
		match user_defined_var_label_lhs with
		  | None -> Some (nf es.CF.es_var_ctx_lhs)
		  | Some i -> if (i = 0 || i = -1) then user_defined_var_label_lhs
			          else Some (nf es.CF.es_var_ctx_lhs)} in
	let ne = {e with CF.formula_var_label =
		let user_defined_var_label_rhs = e.CF.formula_var_label in
		match user_defined_var_label_rhs with
		  | None -> Some (nf es.CF.es_var_ctx_rhs)
		  | Some i -> if (i = 0 || i = -1) then user_defined_var_label_rhs
			          else Some (nf es.CF.es_var_ctx_rhs)}
	in (nes,ne)
  in List.map (fun e -> helper e) ls
		
let check_prog (prog : prog_decl) =
  if (Printexc.backtrace_status ()) then print_string "backtrace active"
  else (* print_string "bactracke inactive"; *)
(*    (print_string "raising\n";
    raise Not_found);
*) if !Globals.check_coercions then begin
    print_string "Checking coercions... ";
    ignore (check_coercion prog);
    print_string "DONE."
  end else begin
    ignore (List.map (check_data prog) prog.prog_data_decls);
    ignore (List.map (check_proc_wrapper prog) prog.prog_proc_decls);

	let g = build_state_trans_graph !Solver.variance_graph in
	let cl = variance_numbering !Solver.var_checked_list g in
	List.iter (fun (es,e) -> heap_entail_variance prog es e) cl
	    
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

let check_prog (prog : prog_decl) =
  Gen.Debug.no_1 "check_prog" (fun _ -> "?") (fun _ -> "?") check_prog prog 
