module DD = Debug
open Globals
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Solver
open Cast
open Gen.Basic
open Perm

module CF = Cformula
module CP = Cpure
module TP = Tpdispatcher
module PTracer = Prooftracer
module I = Iast
module LP = Lemproving
module Inf = Infer
module AS = Astsimp

let log_spec = ref ""
  (* checking expression *)
let flow_store = ref ([] : CF.flow_store list)

let num_para = ref (1)
let sort_input = ref false
let webserver = ref false

(* global option to switch on/off the simplification of context after symbolic execution *)
let simplify_context = ref false 

let parallelize num =
  num_para := num

(* let rec check_specs prog proc ctx spec_list e0 = *)
(*   check_specs_a prog proc ctx spec_list e0 *)
(*       (\*Debug.loop_2_no "check_specs" (Cprinter.string_of_context) (Cprinter.string_of_struc_formula) (string_of_bool) (fun ctx spec_list -> (check_specs_a prog proc ctx spec_list e0)) ctx spec_list*\) *)

(* (\* and check_specs prog proc ctx spec_list e0 = check_specs_a prog proc ctx spec_list e0 *\) *)
      
(* (\* assumes the pre, and starts the symbolic execution*\) *)
(* and check_specs_a (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) (spec_list:CF.struc_formula) e0 : bool = *)
(*   (\* let (_,_,b) = check_specs_infer prog proc ctx spec_list e0 in *\) *)
(*   (\* b *\) *)
(*       let rec do_spec_verification (spec: CF.ext_formula):bool = *)
(*         (\*let _ = print_string (Cprinter.string_of_ext_formula spec) in*\) *)
(*         let pos_spec = CF.pos_of_struc_formula [spec] in *)
(*         log_spec := (Cprinter.string_of_ext_formula spec) ^ ", Line " ^ (string_of_int pos_spec.start_pos.Lexing.pos_lnum); *)
(*         match spec with *)
(*           | CF.ECase b -> *)
(*         	    List.for_all (fun (c1, c2) -> *)
(*         	        let mn = Cast.unmingle_name (proc.Cast.proc_name) in (\*get proc_name*\) *)
(*         	        let f_formula = fun f -> None in *)
(*         	        let f_b_formula (pf, il) = match pf with *)
(*         		      | CP.BVar (CP.SpecVar (t,i,p), loc) -> Some ((CP.BVar ((CP.SpecVar (t,i^"_"^mn,p)), loc)), il) *)
(*         		      | _ -> None *)
(*         	        in *)
(*                     (\*???*\) *)
(*         	        let f_exp = function *)
(*         		      | CP.Var (CP.SpecVar (t,i,p), loc) -> Some (CP.Var ((CP.SpecVar (t,i^"_"^mn,p)), loc)) *)
(*         		      | _ -> None *)
(*         	        in *)
(*                     (\*???*\) *)
(*         	        let new_c1 = CP.transform_formula (true, true, f_formula, f_b_formula, f_exp) c1 in *)
(*         	        (\* Termination: Add source condition *\) *)
(*         	        let nctx = CF.transform_context (fun es -> *)
(*         		        CF.Ctx {es with CF.es_var_ctx_lhs = CP.mkAnd es.CF.es_var_ctx_lhs new_c1 pos_spec}) ctx  in (\*???*\) *)

(*   	        (\*let _ = print_string ("\ncheck_specs: nctx: " ^ (Cprinter.string_of_context nctx) ^ "\n") in*\) *)
	  
(*   	        let nctx = CF.transform_context (combine_es_and prog (MCP.mix_of_pure c1) true) nctx in *)
(*   	        let r = check_specs_a prog proc nctx c2 e0 in *)
(*   	        (\*let _ = Debug.devel_zprint (lazy ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n")) pos_spec in*\) *)
(*   	        r) b.CF.formula_case_branches *)
(*     | CF.EBase b -> *)
(*           Debug.devel_zprint (lazy ("check_specs: EBase: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos; *)
(*           let nctx = *)
(*             if !Globals.max_renaming *)
(*             then (CF.transform_context (CF.normalize_es b.CF.formula_ext_base b.CF.formula_ext_pos false) ctx) (\*apply normalize_es into ctx.es_state*\) *)
(*             else (CF.transform_context (CF.normalize_clash_es b.CF.formula_ext_base b.CF.formula_ext_pos false) ctx) in *)
(*   		(\* let _ = print_string ("check_specs: EBase: New context = " ^ (Cprinter.string_of_context nctx) ^ "\n") in *\) *)
(*           let r = check_specs_a prog proc nctx b.CF.formula_ext_continuation e0 in *)
(*           let _ = Debug.devel_zprint (lazy ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n")) pos_spec in *)
(*           r *)
(*     | CF.EVariance b -> *)
(*           Debug.devel_zprint (lazy ("check_specs: EVariance: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos; *)
(*   		let nctx = CF.transform_context (fun es -> CF.Ctx {es with CF.es_var_measures = List.map (fun (e,b) -> e) b.CF.formula_var_measures; *)
(*   		    CF.es_var_label = b.CF.formula_var_label}) ctx in *)
(*   	    check_specs_a prog proc nctx b.CF.formula_var_continuation e0 *)
(*     | CF.EInfer b -> *)
(*           Debug.devel_zprint (lazy ("check_specs: EInfer: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos; *)
(*           let vars = b.CF.formula_inf_vars in *)
(*           let nctx = CF.transform_context (fun es -> CF.Ctx {es with CF.es_infer_vars = vars}) ctx in *)
(*           check_specs_a prog proc nctx b.CF.formula_inf_continuation e0 *)
(*     | CF.EAssume (x,post_cond,post_label) -> *)
(*           if(Immutable.is_lend post_cond) then *)
(*         	  Error.report_error *)
(*   	          {Error.error_loc = pos_spec; *)
(*   	          Error.error_text =  ("The postcondition cannot contain @L heap predicates/data nodes\n")} *)
(*           else *)
(*             let _ = post_pos#set (CF.pos_of_formula post_cond) in *)
(*             Debug.devel_zprint (lazy ("check_specs: EAssume: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos; *)
(*             let ctx1 = CF.transform_context (elim_unsat_es prog (ref 1)) ctx in *)
(*             (\* let _ = print_string ("\n pre eli : "^(Cprinter.string_of_context ctx)^"\n post eli: "^(Cprinter.string_of_context ctx1)^"\n") in *\) *)
(*             if (CF.isAnyFalseCtx ctx1) then *)
(*   	        let _ = Debug.devel_pprint ("\nFalse precondition detected in procedure "^proc.proc_name^"\n with context: "^ *)
(*   			    (Cprinter.string_of_context_short ctx)) no_pos in *)
(*   	        true *)
(*             else *)
(*   	        let _ = Gen.Profiling.push_time ("method "^proc.proc_name) in *)
(*   	        try *)
(*   	          let r = *)
(*   	            flow_store := []; *)
(*   	            let ctx1 = CF.set_flow_in_context_override *)
(*   		          { CF.formula_flow_interval = !norm_flow_int; CF.formula_flow_link = None} ctx1 in *)
(*   	            let ctx1 = CF.add_path_id ctx1 (Some post_label,-1) in *)
(*                   (\* need to add initial esc_stack *\) *)
(*                   let init_esc = [((0,""),[])] in *)
(*   	            let lfe = [CF.mk_failesc_context ctx1 [] init_esc] in *)
(*   		        let res_ctx = CF.list_failesc_to_partial (check_exp prog proc lfe e0 post_label) in *)
(*                   (\* let _ = print_string ("\n WN 1 : "^(Cprinter.string_of_list_partial_context res_ctx)) in *\) *)
(*   		        let res_ctx = CF.change_ret_flow_partial_ctx res_ctx in *)
(*                   (\* let _ = print_string ("\n WN 2 : "^(Cprinter.string_of_list_partial_context res_ctx)) in *\) *)
(*   		        if (CF.isFailListPartialCtx res_ctx) then false *)
(*   		        else *)
(*                     let lh = Inf.collect_pre_heap_list_partial_context res_ctx in *)
(*                     let lp = Inf.collect_pre_pure_list_partial_context res_ctx in *)
(*   		          let tmp_ctx = check_post prog proc res_ctx post_cond (CF.pos_of_formula post_cond) post_label in *)
(*                     let res = CF.isSuccessListPartialCtx tmp_ctx in *)
(*                     (if res then *)
(*                       let flist = Inf.collect_formula_list_partial_context tmp_ctx in *)
(*                       begin *)
(*                         if (List.length lh)+(List.length lp) > 0 then *)
(*                           begin *)
(*                             print_endline ("\nInferred Heap:"^(pr_list Cprinter.string_of_h_formula lh)) ; *)
(*                             print_endline ("Inferred Pure:"^(pr_list Cprinter.string_of_pure_formula lp)) *)
(*                           end *)
(*                         else print_endline " "; *)
(*                         print_endline ("Residual Post : "^(pr_list Cprinter.string_of_formula flist)) *)
(*                       end); res *)
(*   	          in *)
(*   	          let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in *)
(*   	          r *)
(*   	        with _ as e -> *)
(*   	            let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in raise e *)
(* in *)
(* (\* let _ = print_string ("\ncheck_specs: " ^ (Cprinter.string_of_context ctx) ^ "\n") in *\) *)
(* List.for_all do_spec_verification spec_list *)

let pre_ctr = new Gen.counter 0

let rec check_specs_infer (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) (spec_list:CF.struc_formula) e0 do_infer: 
      CF.struc_formula * (CF.formula list) * ((CP.formula * CP.formula) list) * bool =
  let _ = pre_ctr # reset in
  let pr1 = Cprinter.string_of_struc_formula in
  (* let pr1n s = Cprinter.string_of_struc_formula (CF.norm_specs s) in *)
  let pr2 s = "nothing" in
  let pr3 = pr_quad pr1 pr2 pr2 string_of_bool in
  Debug.no_1 "check_specs_infer" pr1 pr3
      (fun _ -> check_specs_infer_a prog proc ctx spec_list e0 do_infer) spec_list

and check_specs_infer_a (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) (spec_list:CF.struc_formula) e0 do_infer: 
      CF.struc_formula * (CF.formula list) * ((CP.formula * CP.formula) list) * bool =
  let r = List.map (do_spec_verify_infer prog proc ctx e0 do_infer) spec_list in
  let (sl,pl,rl,bl) = List.fold_left (fun (a1,a2,a3,a4) (b1,b2,b3,b4) -> (a1@[b1],a2@b2,a3@b3,a4@[b4])) ([],[],[],[]) r in
  (CF.norm_specs sl, pl, rl, List.for_all pr_id bl)

and do_spec_verify_infer (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) e0 (do_infer:bool) (spec: CF.ext_formula) 
      : (CF.ext_formula * (CF.formula list) * ((CP.formula * CP.formula) list) * bool) =
  let rec helper (spec: CF.ext_formula) :  CF.ext_formula * (CF.formula list) * ((CP.formula * CP.formula) list) * bool =
    (*let _ = print_string (Cprinter.string_of_ext_formula spec) in*)
    let pos_spec = CF.pos_of_struc_formula [spec] in
    log_spec := (Cprinter.string_of_ext_formula spec) ^ ", Line " ^ (string_of_int pos_spec.start_pos.Lexing.pos_lnum);	 
    match spec with
	  | CF.ECase b ->
            let r =
		      List.map (fun (c1, c2) -> 
		          let mn = Cast.unmingle_name (proc.Cast.proc_name) in (*get proc_name*)
		          let f_formula = fun f -> None in
		          let f_b_formula (pf, il) = match pf with
			        | CP.BVar (CP.SpecVar (t,i,p), loc) -> Some ((CP.BVar ((CP.SpecVar (t,i^"_"^mn,p)), loc)), il)
			        | _ -> None
		          in 
		          let f_exp = function
			        | CP.Var (CP.SpecVar (t,i,p), loc) -> Some (CP.Var ((CP.SpecVar (t,i^"_"^mn,p)), loc))
			        | _ -> None
		          in 
		          let new_c1 = CP.transform_formula (true, true, f_formula, f_b_formula, f_exp) c1 in
		          (* Termination: Add source condition *)
		          let nctx = CF.transform_context (fun es ->
			          CF.Ctx {es with CF.es_var_ctx_lhs = CP.mkAnd es.CF.es_var_ctx_lhs new_c1 pos_spec}) ctx  in (*???*)
		          (*let _ = print_string ("\ncheck_specs: nctx: " ^ (Cprinter.string_of_context nctx) ^ "\n") in*)
		          let nctx = CF.transform_context (combine_es_and prog (MCP.mix_of_pure c1) true) nctx in
		          let (new_c2,pre,rel,f) = check_specs_infer_a prog proc nctx c2 e0 do_infer in
                  (* Thai: Need to generate EBase from pre if necessary *)
                  let new_c2 = 
                    if pre!=[] then 
                      begin
                        pre_ctr # inc ;
                        List.map2 CF.merge_ext_pre new_c2 pre 
                      end
                    else new_c2 in
		          (*let _ = Debug.devel_zprint (lazy ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n")) pos_spec in*)
		          ((c1,new_c2),(rel,f))) b.CF.formula_case_branches in
            let (cbl,fl) = List.split r in
            let (rel_ls,fl) = List.split fl in
            let rel = List.concat rel_ls in
            let br = List.for_all pr_id fl in
            let new_spec = CF.ECase {b with CF.formula_case_branches=cbl} in
            (new_spec,[],rel,true)
	  | CF.EBase b ->
            Debug.devel_zprint (lazy ("check_specs: EBase: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos;
	        let nctx = 
	          if !Globals.max_renaming 
	          then (CF.transform_context (CF.normalize_es b.CF.formula_ext_base b.CF.formula_ext_pos false) ctx) (*apply normalize_es into ctx.es_state*)
	          else (CF.transform_context (CF.normalize_clash_es b.CF.formula_ext_base b.CF.formula_ext_pos false) ctx) in
			(* let _ = print_string ("check_specs: EBase: New context = " ^ (Cprinter.string_of_context nctx) ^ "\n") in *)
	        let (c,pre,rels,r) = check_specs_infer_a prog proc nctx b.CF.formula_ext_continuation e0 do_infer in
	        let _ = Debug.devel_zprint (lazy ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n")) pos_spec in
            (*         print_endline ("FML: " ^ Cprinter.string_of_formula pre);*)
            let base = b.CF.formula_ext_base in
            let pos = b.CF.formula_ext_pos in
            let new_base = begin
              match pre with
                | [] -> base
                | [p] -> (pre_ctr # inc; CF.normalize 1 base p pos)
                | _ -> report_error pos ("Spec has more than 2 pres but only 1 post")
            end in
            let _ = if rels==[] then () else pre_ctr#inc  
            in
	        (CF.EBase {b with CF.formula_ext_base = new_base; CF.formula_ext_continuation = c}, [], rels, r) 
	  | CF.EVariance b ->
            Debug.devel_zprint (lazy ("check_specs: EVariance: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos;
			let nctx = CF.transform_context (fun es -> CF.Ctx {es with CF.es_var_measures = List.map (fun (e,b) -> e) b.CF.formula_var_measures;
			    CF.es_var_label = b.CF.formula_var_label}) ctx in
		    let (c,pre,rel,f) = check_specs_infer_a prog proc nctx b.CF.formula_var_continuation e0 do_infer in
	        (CF.EVariance {b with CF.formula_var_continuation = c}, pre, rel,f) 
      | CF.EInfer b ->
            Debug.devel_zprint (lazy ("check_specs: EInfer: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos;
            let postf = b.CF.formula_inf_post in
            let vars = if do_infer then b.CF.formula_inf_vars else [] in
            let (vars_rel,vars_inf) = List.partition (fun v -> match v with CP.SpecVar(t,_,_) -> t==RelT) vars in
            (* let _ = print_endline ("WN:Vars to Infer"^Cprinter.string_of_spec_var_list vars_inf) in *)
            (* let _ = print_endline ("WN:Vars to Rel"^Cprinter.string_of_spec_var_list vars_rel) in *)
            (if vars!=[] || postf then pre_ctr # inc) ;
            let nctx = CF.transform_context (fun es -> 
                CF.Ctx {es with CF.es_infer_vars = vars_inf;CF.es_infer_vars_rel = vars_rel;CF.es_infer_post = postf}) ctx in
            let (c,pre,rel,f) = do_spec_verify_infer prog proc nctx e0 do_infer b.CF.formula_inf_continuation in
            (* TODO : should convert to EBase if pre!=[] *)
            let pos = b.CF.formula_inf_pos in
            let new_c = if pre=[] then c else
                begin
                match c with
                | CF.EAssume _ -> CF.EBase {
                    CF.formula_ext_explicit_inst = [];
                    CF.formula_ext_implicit_inst = [];
                    CF.formula_ext_exists = [];
                    CF.formula_ext_base = (match pre with 
                      | [a] -> a 
                      | _ -> report_error pos ("Spec has more than 2 pres but only 1 post"));
                    CF.formula_ext_continuation = [c];
                    CF.formula_ext_pos = pos;
                  }
                | _ -> c
                end
            in
            (new_c,[],rel,f)
	  | CF.EAssume (var_ref,post_cond,post_label) ->
	        if(Immutable.is_lend post_cond) then
	      	  Error.report_error
	              {Error.error_loc = pos_spec;
	              Error.error_text =  ("The postcondition cannot contain @L heap predicates/data nodes\n")}
	        else
              let _ = post_pos#set (CF.pos_of_formula post_cond) in
              Debug.devel_zprint (lazy ("check_specs: EAssume: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos;
	          let ctx1 = CF.transform_context (elim_unsat_es prog (ref 1)) ctx in
	          (* let _ = print_string ("\n pre eli : "^(Cprinter.string_of_context ctx)^"\n post eli: "^(Cprinter.string_of_context ctx1)^"\n") in *)
	          if (CF.isAnyFalseCtx ctx1) then
	            let _ = Debug.devel_zprint (lazy ("\nFalse precondition detected in procedure "^proc.proc_name^"\n with context: "^
	    		    (Cprinter.string_of_context_short ctx))) no_pos in
	            (spec,[],[],true)
	          else
	            let _ = Gen.Profiling.push_time ("method "^proc.proc_name) in
	            try
	              let spec_and_inferred_post, inferred_pre, inferred_rel, r =
	                flow_store := [];
	                let ctx1 = CF.set_flow_in_context_override
	    	          { CF.formula_flow_interval = !norm_flow_int; CF.formula_flow_link = None} ctx1 in
	                let ctx1 = CF.add_path_id ctx1 (Some post_label,-1) in
                    (* need to add initial esc_stack *)
                    let init_esc = [((0,""),[])] in
	                let lfe = [CF.mk_failesc_context ctx1 [] init_esc] in
	    	        let res_ctx = CF.list_failesc_to_partial (check_exp prog proc lfe e0 post_label) in
	                (* let _ = print_string ("\n WN 1 : "^(Cprinter.string_of_list_partial_context res_ctx)) in *)
	    	        let res_ctx = CF.change_ret_flow_partial_ctx res_ctx in
	                (* let _ = print_string ("\n WN 2 : "^(Cprinter.string_of_list_partial_context res_ctx)) in *)
                    let pos = CF.pos_of_formula post_cond in
	    	        if (CF.isFailListPartialCtx res_ctx) 
                    then (spec, [], [],false)
	    	        else
                      let lh = Inf.collect_pre_heap_list_partial_context res_ctx in
                      let lp = Inf.collect_pre_pure_list_partial_context res_ctx in
                      let post_iv = Inf.collect_infer_vars_list_partial_context res_ctx in
                      (* no abductive inference for post-condition *)
                      let res_ctx = Inf.remove_infer_vars_all_list_partial_context res_ctx in
                      (* let iv = CF.collect_infer_vars ctx in *)
                      let postf = CF.collect_infer_post ctx in
                       let (impl_vs,post_cond) = 
                        if pre_ctr # get > 0 then 
                          let (impl_vs,new_post) = CF.lax_impl_of_post post_cond in
                          if impl_vs!=[] then
                            begin
                                DD.devel_pprint ">>>>>> Convert Exists to Implicit Vars for Post-Cond <<<<<<" pos;
                                DD.devel_pprint ("Extra Implicit Vars :"^(Cprinter.string_of_spec_var_list impl_vs)) pos;
                                DD.devel_pprint ("New Post Cond :"^(Cprinter.string_of_formula new_post)) pos
                            end;
                          (impl_vs,new_post)
                        else ([],post_cond) in
                      let res_ctx = Inf.add_impl_vars_list_partial_context impl_vs res_ctx in
                      let tmp_ctx = check_post prog proc res_ctx post_cond (CF.pos_of_formula post_cond) post_label in
                      let rels = Gen.BList.remove_dups_eq (=) (Inf.collect_rel_list_partial_context tmp_ctx) in
                      let res = CF.isSuccessListPartialCtx tmp_ctx in
                      let infer_pre_flag = (List.length lh)+(List.length lp) > 0 in
                      (* Fail with some tests *)
                      let infer_post_flag = postf in
                      (* let infer_post_flag = false in *)
                      let new_spec_post, pre =
                        if res then
                          let flist = Inf.collect_formula_list_partial_context tmp_ctx in
                          let i_pre =
                            if infer_pre_flag then (
                                DD.devel_pprint ">>>>>> HIP gather infer pre <<<<<<" pos;
                                DD.devel_pprint ("Inferred Heap :"^(pr_list Cprinter.string_of_h_formula lh)) pos;
                                DD.devel_pprint ("Inferred Pure :"^(pr_list Cprinter.string_of_pure_formula lp)) pos;
                                print_endline ("\nInferred Heap:"^(pr_list Cprinter.string_of_h_formula lh)) ;
                                print_endline ("Inferred Pure:"^(pr_list Cprinter.string_of_pure_formula lp));
                                (*let vars = (List.concat (List.map CF.h_fv lh)) @ (List.concat (List.map CP.fv lp)) in*)
                                let fml = List.fold_left CF.normalize_combine_heap (CF.formula_of_heap CF.HEmp no_pos) lh in
                                let fml = List.fold_left (fun f p -> CF.normalize 1 fml p no_pos)
                                  fml (List.map (fun p -> CF.formula_of_pure_formula p no_pos) lp)
                                in if Solver.verify_pre_is_sat prog fml then [fml] else []
                            )
                            else
                              (*print_endline " ";*)
                              []
                                  (* CF.formula_of_heap CF.HTrue no_pos *)
                          in
                          let i_post =
                            if not(infer_post_flag) then spec
                            else
                              begin
                                let pre_vars = CF.context_fv ctx in
                                (* filter out is_prime *)
                                let pre_vars = List.filter (fun v -> not(CP.is_primed v)) pre_vars in
                                (* add vars of pre *)
                                let pre_vars = pre_vars @ (if i_pre = [] then [] else CF.fv (List.hd i_pre)) in
                                (* (\* add infer_vars *\) *)
                                let pre_vars = CP.remove_dups_svl (pre_vars @ post_iv) in
                                (* drop @L heap nodes from flist *)
                                let flist = List.map CF.remove_lend flist in
                                let flist = Gen.BList.remove_dups_eq (=) (List.map (fun fml -> Solver.simplify_post_heap_only fml prog) flist) in
                                (* TODO: flist denotes a disjunction! see ll-b.ss *)
                                let post_vars = List.concat (List.map CF.fv flist) in
                                let heap_vars = List.concat (List.map (fun f -> CF.fv_heap_of f) flist) in
                                (* ref parameters *)
                                let vr = List.map CP.to_primed var_ref in
                                let post_vars = CP.diff_svl post_vars (pre_vars@heap_vars@vr) in
                                (* filter out res *)
                                let post_vars = List.filter (fun v -> not(CP.is_res_spec_var v)) post_vars in
                                let post_vars = CP.remove_dups_svl post_vars in
                                (* let _ = print_endline ("Pre Vars :"^Cprinter.string_of_spec_var_list pre_vars) in *)
                                (* let _ = print_endline ("Exists Post Vars :"^Cprinter.string_of_spec_var_list post_vars) in *)
                                let post_fml = if flist!=[] then 
                                    let tmp = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 no_pos) 
                                      (List.hd flist) (List.tl flist) in
                                    CF.normalize 1 tmp post_cond no_pos
                                  else post_cond in
                                let post_fml = if rels = [] then Solver.simplify_post post_fml post_vars prog None 
                                  else (
(*                                    print_endline ("LEN: " ^ (string_of_int (List.length rels)));   *)
                                    let (rel_fml, post, pre) = Fixcalc.compute_fixpoint rels in
(*                                    print_endline ("\nPOST: "^Cprinter.string_of_pure_formula post);*)
(*                                    print_endline ("PRE : "^Cprinter.string_of_pure_formula pre);   *)
(*                                    print_endline ("Rel:"^Cprinter.string_of_pure_formula rel_fml); *)
(*                                    print_endline ("FML:"^Cprinter.string_of_formula post_fml);     *)
                                    Solver.simplify_post post_fml post_vars prog (Some (rel_fml, post)))
                                in
                                DD.devel_pprint ">>>>>> HIP gather inferred post <<<<<<" pos;
                                DD.devel_pprint ("Initial Residual post :"^(pr_list Cprinter.string_of_formula flist)) pos;
                                DD.devel_pprint ("Final Post :"^(Cprinter.string_of_formula post_fml)) pos;
                                (* print_endline ("Initial Residual Post : "^(pr_list Cprinter.string_of_formula flist)); *)
                                (* print_endline ("Final Residual Post : "^(Cprinter.string_of_formula post_fml)); *)
                                let inferred_post = CF.EAssume (CP.remove_dups_svl (var_ref(* @post_vars *)),post_fml,post_label) in
                                inferred_post
                              end in
                          (i_post, i_pre)
                        else (spec,[])
                      in (new_spec_post, pre, rels, res)
	              in
	              let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in
	              (spec_and_inferred_post,inferred_pre,inferred_rel,r)
                      (* if (lh==[] & lp==[]) then 		           *)
                      (*   (spec,r) *)
                      (* else  *)
                      (*   let hf = List.fold_left (fun a b ->  *)
                      (*       if a==CF.HTrue then b  *)
                      (*       else CF.Star {CF.h_formula_star_h1=a; CF.h_formula_star_h2=b; CF.h_formula_star_pos=no_pos}) CF.HTrue lh in *)
                      (*   let pf = CP.conj_of_list lp no_pos in *)
                      (*   (CF.mk_ebase_inferred_pre hf pf [spec],r) *)
	            with _ as e ->
	                let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in raise e
  in helper spec

and check_exp prog proc ctx e0 label =
  let pr_pn x = x.proc_name in
  let pr = Cprinter.string_of_list_failesc_context in
  Debug.no_2 "check_exp" pr (Cprinter.string_of_exp) pr (fun _ _ -> check_exp_a prog proc ctx e0 label) ctx e0

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
          exp_unfold_pos = pos}) -> 
              unfold_failesc_context (prog,None) ctx sv true pos
	              (* for code *)
        | Assert ({ exp_assert_asserted_formula = c1_o;
          exp_assert_assumed_formula = c2;
          exp_assert_path_id = (pidi,s);
          exp_assert_pos = pos}) -> let _ = if !print_proof && (match c1_o with | None -> false | Some _ -> true) then 
          	begin
          	  Prooftracer.push_assert_assume e0;
          	  Prooftracer.add_assert_assume e0;
              Prooftracer.start_compound_object ();
			  Tpdispatcher.push_suppress_imply_output_state ();
			  Tpdispatcher.unsuppress_imply_output ();
          	end in
          begin
	        let _ = proving_loc#set pos in
	        let s1 = snd post_start_label in
            (* let _ = print_string ("labels:"^s^"#"^s1^"#"^"\n") in *)
	        if (String.length s)>0 (* && (String.length s1)>0 *) && (String.compare s s1 <> 0) then ctx
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
			  let _ = if !print_proof  && (match c1_o with | None -> false | Some _ -> true) then 
                begin
          		  Prooftracer.add_assert_assume e0;
                  (* Prooftracer.end_object (); *)
                  Prooftracer.pop_div ();
                  Prooftracer.pop_div ();
				  Tpdispatcher.restore_suppress_imply_output_state ();
                end in
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
	          if (CF.subsume_flow_f !norm_flow_int (CF.flow_formula_of_formula c1.CF.es_formula)) then 
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
	        let tmp1 = CP.BForm ((CP.BVar (res_v, pos), None), None, None) in
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
          exp_bind_read_only = read_only;
		  exp_bind_path_id = pid;
          exp_bind_pos = pos}) -> begin
            (* Debug.devel_zprint (lazy ("bind: delta at beginning of bind\n" ^ (string_of_constr delta) ^ "\n")) pos; *)
	        let _ = proving_loc#set pos in
	        let field_types, vs = List.split lvars in
	        let v_prim = CP.SpecVar (v_t, v, Primed) in
	        let vs_prim = List.map2 (fun v -> fun t -> CP.SpecVar (t, v, Primed)) vs field_types in
	        let p = CP.fresh_spec_var v_prim in
	        let link_pv = CF.formula_of_pure_N
	          (CP.mkAnd (CP.mkEqVar v_prim p pos) (CP.BForm ((CP.mkNeq (CP.Var (p, pos)) (CP.Null pos) pos, None), None, None)) pos) pos in
	        (*let _ = print_string ("[typechecker.ml, check__exp]: link_pv: " ^ Cprinter.string_of_formula link_pv ^ "\n") in*)
	        (*	  let link_pv = CF.formula_of_pure (CP.mkEqVar v_prim p pos) pos in *)
	        let tmp_ctx =
	          if !Globals.large_bind then
	            CF.normalize_max_renaming_list_failesc_context link_pv pos false ctx
	          else ctx in
            (* let _ = print_endline ("WN1 ctx: "^Cprinter.string_of_list_failesc_context ctx) in *)
            (* let _ = print_endline ("WN1 tmp_ctx: "^Cprinter.string_of_list_failesc_context tmp_ctx) in *)
            let _ = CF.must_consistent_list_failesc_context "bind 1" ctx  in
	        let unfolded = unfold_failesc_context (prog,None) tmp_ctx v_prim true pos in
	        (* let unfolded_prim = if !Globals.elim_unsat then elim_unsat unfolded else unfolded in *)
            let _ = CF.must_consistent_list_failesc_context "bind 2" unfolded  in
	        let _ = Debug.devel_zprint (lazy ("bind: unfolded context:\n" ^ (Cprinter.string_of_list_failesc_context unfolded)
            ^ "\n")) pos in
	        (* let _ = print_string ("bind: unfolded context:\n" ^ (Cprinter.string_of_list_failesc_context unfolded) *)
            (*     ^ "\n") in *)

	        let c = string_of_typ v_t in
            let fresh_frac_name = Cpure.fresh_old_name "f" in
            let fresh_frac =  Cpure.SpecVar (v_t,fresh_frac_name, Unprimed) in (*LDK*)
	        let vdatanode = CF.DataNode ({
                CF.h_formula_data_node = (if !Globals.large_bind then p else v_prim);
                CF.h_formula_data_name = c;
			    CF.h_formula_data_derv = false; (*TO CHECK: assume false*)
			    CF.h_formula_data_imm = CF.ConstAnn(imm);
			    CF.h_formula_data_perm = Some fresh_frac; (*LDK: belong to HIP, deal later ???*)
			    CF.h_formula_data_origins = []; (*deal later ???*)
			    CF.h_formula_data_original = true; (*deal later ???*)
                CF.h_formula_data_arguments = (*t_var :: ext_var ::*) vs_prim;
				CF.h_formula_data_holes = []; (* An Hoa : Don't know what to do *)
                CF.h_formula_data_label = None;
                CF.h_formula_data_remaining_branches = None;
                CF.h_formula_data_pruning_conditions = [];
                CF.h_formula_data_pos = pos}) in
	        let vheap = CF.formula_of_heap vdatanode pos in

            (*Test whether fresh_frac is full permission or not
              writable -> fresh_frac = full_perm => normally
              read-only -> fresh_frac != full_perm => in order to 
              detect permission violation
              We use exp_bind_read_only. If true -> read only -> 0.0<f<=1.0
              Othewiese, false -> write -> f=1.0
            *)
            let vheap = 
              if (Perm.allow_perm ()) then 
                if (read_only)
                then
                  let read_f = mkPermInv fresh_frac in
                  CF.mkBase vdatanode (MCP.memoise_add_pure_N (MCP.mkMTrue pos) read_f) CF.TypeTrue (CF.mkTrueFlow ()) [] pos
                else
                  let write_f = mkPermWrite fresh_frac in
                  CF.mkBase vdatanode (MCP.memoise_add_pure_N (MCP.mkMTrue pos) write_f) CF.TypeTrue (CF.mkTrueFlow ()) [] pos
              else
                vheap
            in

		    let vheap = prune_preds prog false vheap in
	        let to_print = "Proving binding in method " ^ proc.proc_name ^ " for spec " ^ !log_spec ^ "\n" in
	        Debug.devel_pprint to_print pos;
			if (Gen.is_empty unfolded) then unfolded
			else 
	          let rs_prim, prf = heap_entail_list_failesc_context_init prog false  unfolded vheap pos pid in
              let _ = CF.must_consistent_list_failesc_context "bind 3" rs_prim  in
	          let _ = PTracer.log_proof prf in
	          let rs = CF.clear_entailment_history_failesc_list (fun x -> None) rs_prim in
              let _ = CF.must_consistent_list_failesc_context "bind 4" rs  in
	          if (CF.isSuccessListFailescCtx unfolded) && not(CF.isSuccessListFailescCtx rs) then   
                begin
		          Debug.print_info ("("^(Cprinter.string_of_label_list_failesc_context rs)^") ") 
                      ("bind: node " ^ (Cprinter.string_of_h_formula vdatanode) ^ " cannot be derived from context\n") pos; (* add branch info *)
		          Debug.print_info ("(Cause of Bind Failure)")
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
		            if (imm != Lend) then 
		              CF.normalize_max_renaming_list_failesc_context vheap pos true tmp_res1 
    			          (* for Lend, it should not be added back *)
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
          end; (*end Bind*)
	          
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
	        let pure_cond = (CP.BForm ((CP.mkBVar v Primed pos, None), None, None)) in
	        let then_cond_prim = MCP.mix_of_pure pure_cond in
	        let else_cond_prim = MCP.mix_of_pure (CP.mkNot pure_cond None pos) in
	        let then_ctx = combine_list_failesc_context_and_unsat_now prog ctx then_cond_prim in
	        Debug.devel_zprint (lazy ("conditional: then_delta:\n" ^ (Cprinter.string_of_list_failesc_context then_ctx))) pos;
	        let else_ctx =combine_list_failesc_context_and_unsat_now prog ctx else_cond_prim in
	        Debug.devel_zprint (lazy ("conditional: else_delta:\n" ^ (Cprinter.string_of_list_failesc_context else_ctx))) pos;
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
                (print_string ("\ndprint:"^pos.start_pos.Lexing.pos_fname
                ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^" empty/false context")) 
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
            (* let frac = Some (CP.FConst (1.0, pos)) in (\*LDK: a new node created with frac perm = 1.0*\) *) (*fresh_variable = full_perm*)
	        let heap_node = CF.DataNode ({
                CF.h_formula_data_node = CP.SpecVar (Named c, res_name, Unprimed);
                CF.h_formula_data_name = c;
		        CF.h_formula_data_derv = false;
		        CF.h_formula_data_imm = CF.ConstAnn(Mutable);
		        CF.h_formula_data_perm = None; (*LDK: deal later*)
			    CF.h_formula_data_origins = []; (*deal later ???*)
			    CF.h_formula_data_original = true; (*deal later ???*)

                CF.h_formula_data_arguments =(*type_var :: ext_var :: *) heap_args;
				CF.h_formula_data_holes = []; (* An Hoa : Don't know what to do *)
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
	          let p = CP.mkEqExp (CP.mkVar (CP.SpecVar (Named "", res_name, Unprimed)) pos) (CP.Null pos) pos in
	          let f = CF.formula_of_mix_formula (MCP.mix_of_pure p) pos in
	          let res = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
	          res
		| EmptyArray _ -> ctx (* An Hoa : no change in context for empty array *)
        | SCall ({
			  exp_scall_type = ret_t;
			  exp_scall_method_name = mn; (* mn is mingled name of the method *)
			  exp_scall_arguments = vs;
			  exp_scall_is_rec = ir;
			  exp_scall_path_id = pid;
			  exp_scall_pos = pos}) ->
		      begin
                let _ = proving_loc#set pos in
	            let proc = look_up_proc_def pos prog.prog_proc_decls mn in
	            let farg_types, farg_names = List.split proc.proc_args in
	            let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
	            let actual_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) vs farg_types in
                
                (* Internal function to check pre/post condition of the function call. *)        
	            let check_pre_post org_spec (sctx:CF.list_failesc_context) should_output_html : CF.list_failesc_context =
                  (* Termination: Stripping the "variance" feature from org_spec
				     if the call is not a recursive call *)
			      let stripped_spec = if ir then org_spec else
                    let rec strip_variance ls = match ls with
                      | [] -> []
                      | spec::rest -> match spec with
                          | CF.EVariance e -> (strip_variance e.CF.formula_var_continuation)@(strip_variance rest)
                          | CF.EInfer e -> (strip_variance [e.CF.formula_inf_continuation])@(strip_variance rest)
                          | CF.EBase b -> (CF.EBase {b with CF.formula_ext_continuation = strip_variance b.CF.formula_ext_continuation})::(strip_variance rest)
                          | CF.ECase c -> (CF.ECase {c with CF.formula_case_branches = List.map (fun (cpf, sf) -> (cpf, strip_variance sf)) c.CF.formula_case_branches})::(strip_variance rest)
                          | _ -> spec::(strip_variance rest)
                    in strip_variance org_spec
                  in

                  (* org_spec -> stripped_spec *)
	              (* free vars = linking vars that appear both in pre and are not formal arguments *)
                  let pre_free_vars = Gen.BList.difference_eq CP.eq_spec_var
                    (Gen.BList.difference_eq CP.eq_spec_var (CF.struc_fv stripped_spec(*org_spec*))
                        (CF.struc_post_fv stripped_spec(*org_spec*))) farg_spec_vars in
                  (* free vars get to be substituted by fresh vars *)
                  let pre_free_vars_fresh = CP.fresh_spec_vars pre_free_vars in
                  let renamed_spec = 
                    if !Globals.max_renaming then (CF.rename_struc_bound_vars stripped_spec(*org_spec*))
                    else (CF.rename_struc_clash_bound_vars stripped_spec(*org_spec*) (CF.formula_of_list_failesc_context sctx))
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
                  (* Termination: Cache the subst for output pretty printing *)
                  let sctx = if not ir then sctx else
                    let var_subst = List.map2 (fun e1 e2 -> (e1, e2, (Cast.unmingle_name mn))) to_vars fr_vars in
                    List.map (fun fctx ->
                        let (lb,estk,lbctx) = fctx in
                        let nlbctx = List.map (fun bctx ->
                            let (pt,ctx) = bctx in
                            let nctx = CF.transform_context (fun es -> 
                                CF.Ctx {es with CF.es_var_subst = es.CF.es_var_subst @ var_subst; 
                                    CF.es_var_loc = pos}) ctx in (pt,nctx)) lbctx in
                        (lb,estk,nlbctx)) sctx
                  in
                  (*let _ = print_string ("\ncheck_pre_post@SCall@sctx: " ^
                    (Cprinter.string_of_pos pos) ^ "\n" ^
                    (Cprinter.string_of_list_failesc_context sctx) ^ "\n") in*)
                  let renamed_spec = CF.subst_struc st1 renamed_spec in
                  let renamed_spec = CF.subst_struc_avoid_capture fr_vars to_vars renamed_spec in
                  let st2 = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) actual_spec_vars in
                  let pre2 = CF.subst_struc_pre st2 renamed_spec in
                  let new_spec = (Cprinter.string_of_struc_formula pre2) in
                  (*let _ = print_string ("\ncheck_pre_post@SCall@check_exp: new_spec: " ^ new_spec ^ "\n") in*)
                  (* Termination checking *)
                  let str_debug_variance = if (ir) then "Checking the termination of the recursive call " ^ mn ^ " in method " ^ proc.proc_name ^ ": " ^ (Cprinter.string_of_pos pos) ^ "\n" else "" in
                  let _ = Debug.devel_zprint (lazy (str_debug_variance)) pos in
                  let _ = 
                    if not (CF.isNonFalseListFailescCtx sctx) & ir & (CF.has_variance_struc stripped_spec) then
                      (* Termination: Add a false entail state for 
                       * unreachable recursive call if variance exists *)
                      var_checked_list := !var_checked_list @ [(
                          {(CF.false_es CF.mkFalseFlow pos) with CF.es_var_label = Some (-1); CF.es_var_loc = pos}, 
                          CF.empty_ext_variance_formula)];
                  in 
                  (*print_string (str_debug_variance ^ "\n");*) 
                  
                  (* TODO: call the entailment checking function in solver.ml *)
                  (* let _ = print_endline ("WN 1:"^Cprinter.string_of_list_failesc_context sctx) in *)
                  let successful_ctx = List.map CF.succ_context_of_failesc_context sctx in
                  let ctx_print = "\nCurrent States: " ^ (pr_list Cprinter.string_of_context_short successful_ctx)  in
                  let to_print = "\nProving precondition in method " ^ proc.proc_name ^ " for spec:\n" ^ new_spec (*!log_spec*) in
                  let to_print = ("\nVerification Context:"^(post_pos#string_of_pos)^to_print) in
                  Debug.devel_zprint (lazy (to_print^"\n")) pos;
				  (* An Hoa : output the context and new spec before checking pre-condition *)
				  let _ = if !print_proof && should_output_html then Prooftracer.push_list_failesc_context_struct_entailment sctx pre2 in
                  let rs, prf = heap_entail_struc_list_failesc_context_init prog false true sctx pre2 pos pid in
				  let _ = if !print_proof && should_output_html then Prooftracer.pop_div () in
                  (* The context returned by heap_entail_struc_list_failesc_context_init, rs, is the context with unbound existential variables initialized & matched. *)
                  let _ = PTracer.log_proof prf in

                  (*let _ = print_string (("\nres ctx: ") ^ (Cprinter.string_of_list_failesc_context rs) ^ "\n") in*)
                  
                  if (CF.isSuccessListFailescCtx sctx) && (CF.isFailListFailescCtx rs) then
                    let to_print = to_print^ctx_print in
                    Debug.print_info "Procedure Call" (to_print^" has failed \n") pos 
                 else () ;
                  rs in
                (* Call check_pre_post with debug information *)
                let check_pre_post org_spec (sctx:CF.list_failesc_context) should_output_html : CF.list_failesc_context =
                  (* let _ = Cprinter.string_of_list_failesc_context in *)
                  let pr2 = Cprinter.string_of_list_failesc_context in
                  let pr3 = Cprinter.string_of_struc_formula in
                  Debug.no_2_loop "check_pre_post" pr3 pr2 pr2 (fun _ _ ->  check_pre_post org_spec sctx should_output_html) org_spec sctx in
				let _ = if !print_proof then Prooftracer.start_compound_object () in
                let scall_pre_cond_pushed = if !print_proof then
                  begin
                    Tpdispatcher.push_suppress_imply_output_state ();
                    Tpdispatcher.unsuppress_imply_output ();
            		Prooftracer.push_pre e0;
                    (* print_endline ("CHECKING PRE-CONDITION OF FUNCTION CALL " ^ (Cprinter.string_of_exp e0)) *)
                  end else false in

                let res = if (CF.isFailListFailescCtx ctx) then
				  let _ = if !print_proof && scall_pre_cond_pushed then Prooftracer.append_html "Program state is unreachable." in
                  ctx 
                else check_pre_post (proc.proc_stk_of_static_specs#top) ctx scall_pre_cond_pushed in
				let _ = if !print_proof then Prooftracer.add_pre e0 in
                let _ = if !print_proof && scall_pre_cond_pushed then 
                  begin
                    Prooftracer.pop_div ();
                    Tpdispatcher.restore_suppress_imply_output_state ();
                    (* print_endline "OK.\n" *)
                  end in 
                res
              end
        | Seq ({exp_seq_type = te2;
          exp_seq_exp1 = e1;
          exp_seq_exp2 = e2;
          exp_seq_pos = pos}) -> begin
	        let ctx1 = check_exp prog proc ctx e1 post_start_label (*flow_store*) in 
            (* Astsimp ensures that e1 is of type void *)
            (* let _ = print_endline ("WN C1:"^(Cprinter.string_of_list_failesc_context ctx1)) in *)
	        let ctx2= check_exp prog proc ctx1 e2 post_start_label (*flow_store*) in
            (* let _ = print_endline ("WN C2:"^(Cprinter.string_of_list_failesc_context ctx2)) in *)
            ctx2
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
	          (* let _ =print_string ("sharp start ctx: "^ (Cprinter.string_of_list_failesc_context ctx)^"\n") in *)
	          (* let _ = print_string ("raising: "^(Cprinter.string_of_exp e0)^"\n") in *)
	          (* let _ = print_string ("sharp flow type: "^(Cprinter.string_of_sharp_flow ft)^"\n") in *)
	          let nctx = match v with 
	            | Sharp_var (t,v) -> 
                      let t1 = (get_sharp_flow ft) in
                      (* let _ = print_endline ("Sharp Flow:"^(string_of_flow t1) ^" Exc:"^(string_of_flow !raisable_flow_int)) in *)
                      let vr = if is_subset_flow t1 !raisable_flow_int then (CP.mkeRes t)
                      else (CP.mkRes t) in
		              let tmp = CF.formula_of_mix_formula  (MCP.mix_of_pure (CP.mkEqVar vr (CP.SpecVar (t, v, Primed)) pos)) pos in
		              let ctx1 = CF.normalize_max_renaming_list_failesc_context tmp pos true ctx in
		              ctx1
	            | Sharp_flow v -> 
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
                | Sharp_id v -> CF.transform_list_failesc_context 
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
	let check_exp1 (ctx : CF.list_failesc_context) : CF.list_failesc_context =
      let pr = Cprinter.string_of_list_failesc_context in
      Debug.no_1 "check_exp1" pr pr check_exp1 ctx in
    let ctx = if (not !Globals.failure_analysis) then List.filter (fun (f,s,c)-> Gen.is_empty f ) ctx  
    else ctx in
	(* An Hoa : Simplify the context before checking *)
	let ctx = if !simplify_context then 
	  CF.simplify_list_failesc_context ctx proc.Cast.proc_important_vars
	else ctx in
	let (fl,cl) = List.partition (fun (_,s,c)-> Gen.is_empty c && CF.is_empty_esc_stack s) ctx in
    (* let _ = print_endline ("WN:ESCAPE:"^(Cprinter.string_of_list_failesc_context fl)) in *)
    (* let _ = print_endline ("WN:CURRENT:"^(Cprinter.string_of_list_failesc_context cl)) in *)
    (* if (Gen.is_empty cl) then fl
       else *)	    
    let failesc = CF.splitter_failesc_context !norm_flow_int None (fun x->x)(fun x -> x) cl in
    ((check_exp1 failesc) @ fl)
        
and check_post (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_partial_context) (post : CF.formula) pos (pid:formula_label) : CF.list_partial_context  =
  (* let ctx = list_partial_context_and_unsat_now prog ctx in *)
  let pr = Cprinter.string_of_list_partial_context in
  let pr1 = Cprinter.string_of_formula in
  (* let pr2 x = "List Partial Context "^(pr_list (pr_pair pr1 pr1) x) in *)
  Debug.no_2(* loop_2_no *) "check_post" pr pr1 pr (*Cprinter.string_of_pos pr2 pr2*)  
      (fun _ _ -> 
          let r = check_post_x prog proc ctx post pos pid in
          (* let r = list_partial_context_and_unsat_now prog r in *)
          r ) ctx post

and check_post_x (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_partial_context) (post : CF.formula) pos (pid:formula_label) : CF.list_partial_context  =
  (* let _ = print_string ("got into check_post on the succCtx branch\n") in *)
  (* let _ = print_string ("context before post: "^(Cprinter.string_of_list_partial_context ctx)^"\n") in *)
  let _ = if !print_proof then
	begin
	  Prooftracer.push_post ();
   	  Prooftracer.start_compound_object ();
	  Prooftracer.push_list_partial_context_formula_entailment ctx post;
	  Tpdispatcher.push_suppress_imply_output_state ();
	  Tpdispatcher.unsuppress_imply_output ();
	  (* print_endline "VERIFYING POST-CONDITION" *)
	end in
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
  Debug.devel_zprint (lazy ("Post-cond:\n" ^ (Cprinter.string_of_formula  post) ^ "\n")) pos;
  let to_print = "Proving postcondition in method " ^ proc.proc_name ^ " for spec\n" ^ !log_spec ^ "\n" in
  Debug.devel_pprint to_print pos;
  let rs, prf = heap_entail_list_partial_context_init prog false final_state post pos (Some pid) in
  let _ = PTracer.log_proof prf in
  let _ = if !print_proof then 
    begin
	  Tpdispatcher.restore_suppress_imply_output_state ();
	  Prooftracer.add_post ();
      Prooftracer.pop_div ();
      Prooftracer.pop_div ();
	  (* print_endline "DONE!" *)
	end in
  if (CF.isSuccessListPartialCtx rs) then 
    rs
  else begin
    (* get source code position of failed branches *)
    (*let locs_of_failures = 
      List.fold_left (fun res ctx -> res @ (locs_of_partial_context ctx)) [] rs 
      in*)
    (*let string_of_loc_list locs =
      List.fold_left (fun res l -> res ^ (string_of_loc_by_char_num l) ^ ",") "" locs
      in*)
    begin
	  Debug.print_info ("("^(Cprinter.string_of_label_list_partial_context rs)^") ") 
          ("Postcondition cannot be derived from context\n") pos; 
	  Debug.print_info ("(Cause of PostCond Failure)")
          (Cprinter.string_of_failure_list_partial_context rs) pos;
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
  end


(* checking procedure: (PROC p61) *)
and check_proc (prog : prog_decl) (proc : proc_decl) : bool =
  let unmin_name = unmingle_name proc.proc_name in
  let check_flag = ((Gen.is_empty !procs_verified) || List.mem unmin_name !procs_verified)
    && not (List.mem unmin_name !Inliner.inlined_procs)
  in
  if check_flag then 
  	begin
	  match proc.proc_body with
	    | None -> true (* sanity checks have been done by the translation *)
	    | Some body ->
		      begin
			    if !Globals.print_proc then 
				  print_string ("Procedure " ^ proc.proc_name ^ ":\n" ^ (Cprinter.string_of_proc_decl 3 proc) ^ "\n\n");
			    print_string (("Checking procedure ") ^ proc.proc_name ^ "... "); flush stdout;
			    Debug.devel_zprint (lazy (("Checking procedure ") ^ proc.proc_name ^ "... ")) proc.proc_loc;
			    Debug.devel_zprint (lazy ("Specs :\n" ^ Cprinter.string_of_struc_formula proc.proc_static_specs)) proc.proc_loc;
			    let ftypes, fnames = List.split proc.proc_args in
			    (* fsvars are the spec vars corresponding to the parameters *)
			    let fsvars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in
			    let nox = CF.formula_of_pure_N (CF.no_change fsvars proc.proc_loc) proc.proc_loc in (*init(V) := v'=v*)
			    let init_form = nox in
			    let init_ctx1 = CF.empty_ctx (CF.mkTrueFlow ()) proc.proc_loc in
                (*add default full permission = 1.0 to ante; 
                  need to add type of full perm to stab
                *)
                let init_form =
                  if (Perm.allow_perm ()) then
                    CF.add_mix_formula_to_formula (full_perm_constraint ()) init_form
                  else
                    init_form
                in
		        let init_ctx = CF.build_context init_ctx1 init_form proc.proc_loc in
			    let _ = if !print_proof then begin 
				  Prooftracer.push_proc proc;
				  Prooftracer.start_compound_object ();
				end
			    in
			    let pp, exc = 
                  try (* catch exception to close the section appropriately *)
                    (* let f = check_specs prog proc init_ctx (proc.proc_static_specs (\* @ proc.proc_dynamic_specs *\)) body in *)
                    let (new_spec,_,rels,f) = check_specs_infer prog proc init_ctx (proc.proc_static_specs (* @ proc.proc_dynamic_specs *)) body true in
                    let new_spec = CF.simplify_ann new_spec in
                    if (pre_ctr # get> 0) 
                    then
                      begin
                        let new_spec = AS.add_pre prog new_spec in
                        let _ = proc.proc_stk_of_static_specs # push new_spec in
                        let old_sp = Cprinter.string_of_struc_formula proc.proc_static_specs in
                        let new_sp = Cprinter.string_of_struc_formula new_spec in
                        let new_rels = pr_list Cprinter.string_of_lhs_rhs rels in
                        let _ = 
                          if rels = [] then ()
                          else (
                            let (_, post, pre) = Fixcalc.compute_fixpoint rels in
                            print_endline ("\nPOST: "^Cprinter.string_of_pure_formula post);
                            print_endline ("PRE : "^Cprinter.string_of_pure_formula pre);)
                        in
                        print_endline ("OLD SPECS: "^old_sp);
                        print_endline ("NEW SPECS: "^new_sp);
                        print_endline ("NEW RELS: "^new_rels);
                        let f = if f && !reverify_flag then 
                          let _,_,_,is_valid = check_specs_infer prog proc init_ctx new_spec body false in
                          is_valid
                          else f in
                        ()
                      end;
				    (f, None) 
                  with | _ as e -> (false, Some e) in
		        let _ = if !print_proof then begin
				  Prooftracer.pop_div ();
				  Prooftracer.add_proc proc pp;
				end
				in
		        let _ = match exc with | Some e -> raise e | None -> () in
			    let result = if pp then begin
				  print_string ("\nProcedure "^proc.proc_name^" SUCCESS\n");
		      	  true
	        	end else begin
	        	  print_string ("\nProcedure "^proc.proc_name^" result FAIL-1\n"); 
	        	  false 
	        	end in
	      		result
		      end
	end else true

(* check entire program *)
let check_proc_wrapper prog proc =
(* check_proc prog proc *)
  try
	(*  let _ = print_endline ("check_proc_wrapper : proc = " ^ proc.Cast.proc_name) in *)
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
  let find_coerc coercs name =
    try
      Some (List.find (fun coerc -> coerc.coercion_name = name) coercs)
    with _ -> None in

  (* combine the 2 lists of coercions into one list of lemmas:
     - coercions that have the same name in the left and right list of coercions -> (Some c1,Some c2)
     - left coercion c -> (Some c, None)
     - right coercion c -> (None, Some c)
  *)
  let lemmas = List.map (fun l2r_coerc -> (Some l2r_coerc, find_coerc prog.prog_right_coercions l2r_coerc.coercion_name) ) prog.prog_left_coercions in
  (* add to lemmas the coercions from prog.prog_right_coercions that do not have a corresponding pair in prog.prog_left_coercions *)
  let lemmas = lemmas @ List.map (fun r2l_coerc -> (None, Some r2l_coerc))
    (List.filter 
        (fun r2l_coerc -> List.for_all (fun l2r_coerc -> r2l_coerc.coercion_name <> l2r_coerc.coercion_name) prog.prog_left_coercions)
        prog.prog_right_coercions) in
   List.iter (fun (l2r, r2l) -> 
       let (coerc_type, coerc_name) = 
       match (l2r, r2l) with
         | (Some coerc_l2r, None) -> (I.Left, coerc_l2r.coercion_name)
         | (None, Some coerc_r2l) -> (I.Right, coerc_r2l.coercion_name)
         | (Some coerc1, Some coerc2) -> (I.Equiv, coerc1.coercion_name)
         | (None, None) ->  Error.report_error {Err.error_loc = no_pos; Err.error_text = "[typechecker.ml]: Lemma can't be empty"}
       in
       let _ = LP.verify_lemma l2r r2l prog coerc_name coerc_type in ()
   ) lemmas

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

and equalpf f1 f2 = Debug.no_2 "equalpf" (Cprinter.string_of_pure_formula) (Cprinter.string_of_pure_formula) (string_of_bool) equalpf_a f1 f2

and comparepf_a f1 f2 =
  let r1,_,_ = (Tpdispatcher.imply f1 f2 "" false None) in
  let r2,_,_ = (Tpdispatcher.imply f2 f1 "" false None) in
  if (r1 & r2) then 0
  else compare (Cprinter.string_of_pure_formula f1) (Cprinter.string_of_pure_formula f2)
	
and comparepf f1 f2 = Debug.no_2 "comparepf" (Cprinter.string_of_pure_formula) (Cprinter.string_of_pure_formula) (string_of_int) comparepf_a f1 f2

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

(* TODO : This printing of check_prog needs to be tidied *)
let build_state_trans_graph ls =
  (*print_string ("\ncheck_prog: call graph:\n" ^
	(List.fold_left (fun rs (f1,f2) -> rs ^ "\n" ^ (Cprinter.string_of_pure_formula f1) ^ " ->" ^ (Cprinter.string_of_pure_formula f2)) "" !Solver.variance_graph) ^ "\n");*)

  let gr = IG.empty in
  let g = List.fold_left (fun g (f1,f2) ->
    let ng1 = IG.add_vertex g f1 in
	let ng2 = IG.add_vertex ng1 f2 in
	let ng3 = IG.add_edge ng2 f1 f2 in
	ng3) gr ls in
  g

let scc_numbering g =
  let scc_list = IGC.scc_list g in
  let scc_list = snd (List.fold_left (fun (n,rs) l -> (n+1, rs @ [(n,l)])) (0,[]) scc_list) in

  let mem e ls = List.fold_left (fun rs e1 -> if (equalpf e e1) then true else rs) false ls in
  let meml ls1 ls2 = List.fold_left (fun rs e -> if (mem e ls2) then true else rs) false ls1 in
  
  let scc_graph = GS.empty in
  
  let scc_graph = List.fold_left (fun sg (n,_) -> GS.add_vertex sg n) scc_graph scc_list in

  let scc_graph = List.fold_left (fun sg (n,l) ->
	let neighbours = IGN.list_from_vertices g l in
	List.fold_left (fun nsg (n1,l1) -> if (meml l1 neighbours) then GS.add_edge nsg n n1 else nsg) sg scc_list 
  ) scc_graph scc_list in

  let (nscc, fscc) = GSC.scc scc_graph in

  fun v -> List.fold_left (fun rs (n,l) -> if (mem v l) then (fscc n) else rs) 0 scc_list
  

let variance_numbering ls g =
  if !Globals.term_auto_number then
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
  else ls

let check_prog (prog : prog_decl) (iprog : I.prog_decl) =
	let _ = if (Printexc.backtrace_status ()) then print_endline "backtrace active" in 
    if !Globals.check_coercions then 
      begin
      print_string "Checking lemmas... ";
      (* ignore (check_coercion prog); *)
      check_coercion prog;
      print_string "DONE.\n"
      end;
    (* List of procs with user-given order *)
    let proc_ordered_by_user = prog.prog_proc_decls in
    let iproc_main_names = List.map (fun p -> p.I.proc_name) iprog.I.prog_proc_decls in
    (*    let _ = List.iter (fun p -> print_endline (string_of_bool p.proc_is_main)) proc_ordered_by_user in     *)
    (*    let _ = List.iter (fun p -> print_endline (string_of_bool p.I.proc_is_main)) iprog.I.prog_proc_decls in*)
    
    let is_sub name1 name2 = if String.length name1 >= String.length name2 then false 
      else let n = String.length name1 in name1 = (String.sub name2 0 n) && String.get name2 n = '$' in
    
    let proc_top, proc_base = 
      List.partition (fun proc -> proc.proc_is_main) proc_ordered_by_user in
    (*    let _ = Printf.printf "The scc list of program:\n"; List.iter (fun l -> (List.iter (fun c -> print_string (" "^c)) l; Printf.printf "\n")) !call_graph; Printf.printf "**********\n" in*)
    
    let call_hierachy = List.concat !call_graph in    
    let call_hierachy = List.filter (fun c -> List.mem c iproc_main_names) call_hierachy in
    let proc_top_names = List.map (fun p -> p.proc_name) proc_top in
    let get_name n names = List.find (fun x -> is_sub n x) names in
    let call_hierachy = List.map (fun n -> get_name n proc_top_names) call_hierachy in
    (*let _ = List.iter (fun n -> print_endline n) call_hierachy in*)
    (*let _ = List.iter (fun n -> print_endline n) proc_top_names in*)
    
    let mk_index list_names =
      let rec make_enum a b = if a > b then [] else a::(make_enum (a + 1) b) in
      let list_index = make_enum 0 ((List.length list_names) - 1) in
      List.combine list_names list_index
    in
    let cal_index name list =
      if not(List.mem name call_hierachy) then 0
      else
        try List.assoc name list
        with _ -> report_error no_pos ("Error in cal_index")
    in
    let new_call_hierachy = mk_index call_hierachy in
    
    let proc_top = List.map (fun p -> {p with proc_call_order = (cal_index p.proc_name new_call_hierachy)}) proc_top in
    let sort_by_call procs =
      List.fast_sort (fun proc1 proc2 -> proc1.proc_call_order - proc2.proc_call_order) procs in
    let proc_top = sort_by_call proc_top in
    let proc_ordered_by_call = proc_top @ proc_base in
    
    ignore (List.map (check_data prog) prog.prog_data_decls);
    ignore (List.map (check_proc_wrapper prog) proc_ordered_by_call);
    let g = build_state_trans_graph !Solver.variance_graph in
    let cl = variance_numbering !Solver.var_checked_list g in
    if (List.length cl) != 0 then
      let _ = if !print_proof then begin Prooftracer.push_term (); end in
      let _ = List.iter (fun (es,e) -> heap_entail_variance prog es e) cl in
      if !print_proof then begin Prooftracer.pop_div (); end 
    else () 
	    
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

let check_prog (prog : prog_decl) iprog =
  Debug.no_1 "check_prog" (fun _ -> "?") (fun _ -> "?") check_prog prog iprog
