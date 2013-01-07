module DD = Debug
open Globals
open Stat_global
open Global_var
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Solver
open Cast
open Gen.Basic
open Perm
open Label_only
open Label
module CF = Cformula
module CP = Cpure
module TP = Tpdispatcher
module PTracer = Prooftracer
module I = Iast
module LP = Lemproving
module Inf = Infer
module AS = Astsimp
module CEQ = Checkeq
module M = Lexer.Make(Token.Token)
module H = Hashtbl
let store_label = new store Lab2_List.unlabelled Lab2_List.string_of

let phase_infer_ind = ref false

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

(*pre_f : pre-condition*)

(* pre_f = b.CF.formula_ext_base *)
let check_varperm (prog : prog_decl) (proc : proc_decl) (spec: CF.struc_formula) (ctx : CF.context) (pre_f:CF.formula) pos = 
  (*************************************************************)
  (********* Check permissions variables in pre-condition ******)
  (*************************************************************) 
  (*In the precondition, there will be @value in the main thread and @full in the child threads*)
  (*a parameter MUST be either @value or @full*)
  (*TO DO: have to deal with OR *)
  (*Pickup variable permissions in both thread only*)
  Debug.devel_zprint (lazy ("\ncheck_specs: EBase: checking VarPerm in the precondition:  \n" ^ (Cprinter.string_of_struc_formula spec) ^ "\n")) pos;
  (* let vp_list,_ = CF.filter_varperm_formula_all pre_f in *)
  (* let val_list, vp_rest = List.partition (fun f -> CP.is_varperm_of_typ f VP_Value) vp_list in *)
  (* let full_list, vp_rest2 = List.partition (fun f -> CP.is_varperm_of_typ f VP_Full) vp_rest in *)
  (* let _ = if (vp_rest2!=[]) then *)
  (*       report_error pos ("\ncheck_specs: EBase: unexpected @zero VarPerm in the pre-condition") *)
  (* in *)
  (* let val_vars = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Value)) val_list) in *)
  (* let full_vars = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Full)) full_list) in *)
  let zero_vars = CF.get_varperm_formula_all pre_f VP_Zero in
  let _ = if (zero_vars!=[]) then
        report_error pos ("\ncheck_specs: EBase: unexpected @zero VarPerm in the pre-condition")
  in
  let val_vars = CF.get_varperm_formula_all pre_f VP_Value in
  let full_vars = CF.get_varperm_formula_all pre_f VP_Full in
  let tmp = Gen.BList.intersect_eq CP.eq_spec_var_ident val_vars full_vars in
  let _ = if (tmp!=[]) then
        report_error pos ("\ncheck_specs: EBase: duplicated VarPerm: " ^ (Cprinter.string_of_spec_var_list tmp))
  in
  (*Ensure that all arguments have corresponding varialbe permissions*)
  let farg_types, farg_names = List.split proc.proc_args in
  let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
  (*let all_vars = val_vars@full_vars in
  let tmp1 = Gen.BList.difference_eq CP.eq_spec_var_ident farg_spec_vars all_vars in*)
  (*enable this check require enabling --ann-vp *)
  (* let _ = if (tmp1!=[]) then *)
  (*       report_error pos ("\ncheck_specs: EBase: missing variable permissions for " ^ (Cprinter.string_of_spec_var_list tmp1)) *)
  (* in *)
  (*Find out @zero for the main thread*)
  (*Pickup variable permissions in the main thread only*)
  (* let vp_list2,_ = CF.filter_varperm_formula pre_f in *)
  (* let full_list2, vp_rest4 = List.partition (fun f -> CP.is_varperm_of_typ f VP_Full) vp_list2 in *)
  (* let val_list2, _ = List.partition (fun f -> CP.is_varperm_of_typ f VP_Value) vp_rest4 in *)
  (* let full_vars2 = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Full)) full_list2) in *)
  (* let val_vars2 = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Value)) val_list2) in *)

  let val_vars2 = CF.get_varperm_formula pre_f VP_Value in
  let full_vars2 = CF.get_varperm_formula pre_f VP_Full in
  let all_vars2 = full_vars2@val_vars2 in
  (*@zero of the main thread*)
  let zero_vars = Gen.BList.difference_eq CP.eq_spec_var_ident farg_spec_vars all_vars2 in
  let ctx = CF.transform_context (fun es -> CF.Ctx {es with CF.es_var_zero_perm = zero_vars}) ctx in
  (*drop VarPerm in the main thread*)
  let ext_base = CF.drop_varperm_formula pre_f in
  Debug.devel_zprint (lazy ("\n check_specs: EBase: checking VarPerm in the precondition: Done. " ^ "\n ### zero_vars = " ^ (Cprinter.string_of_spec_var_list zero_vars) ^ "\n")) pos;
  (ctx,ext_base)
(*************************************************************)
(*****<<<< Check permissions variables in pre-condition ******)
(*************************************************************) 

(*checking whether the current state has full permissions of a list of spec vars *)
(*check at | Var | Bind | Assign | Sharp_var*)
let check_full_varperm_x prog ctx ( xs:CP.spec_var list) pos =
  if (not  (CF.isSuccessListFailescCtx ctx)) || (Gen.is_empty ctx)  then (true,ctx) (*propagate fail contexts*)
  else
    let _ = Debug.devel_pprint ("check_full_varperm for var " ^ (Cprinter.string_of_spec_var_list xs)^ "\n") pos in
    let full_p = CP.mk_varperm_full xs pos in
    let full_f = CF.formula_of_pure_formula full_p pos in
    let rs,prf = heap_entail_list_failesc_context_init prog false ctx full_f None None None pos None in
    (if (CF.isFailListFailescCtx rs) then
          let _ = Debug.print_info "VarPerm Failure" ("check_full_varperm: var " ^ (Cprinter.string_of_spec_var_list xs)^ " MUST have full permission" ^ "\n") pos in
          (false,rs)
     else
          (true,ctx))

let check_full_varperm prog ctx ( xs:CP.spec_var list) pos =
  let pr_out = pr_pair string_of_bool Cprinter.string_of_list_failesc_context in
  Debug.no_2 "check_full_varperm"
      Cprinter.string_of_list_failesc_context
      Cprinter.string_of_spec_var_list
      pr_out
      (fun _ _ -> check_full_varperm_x prog ctx xs pos) ctx xs

let pre_ctr = new Gen.counter 0
let post_ctr = new Gen.counter 0

(* WN : moved so solver.ml so that sleek can use *)
(* (\*Merging fractional heap nodes when possible using normalization lemmas*\) *)
(* let normalize_list_failesc_context_w_lemma prog lctx = *)
(*   if not (Perm.allow_perm ()) then lctx *)
(*   else *)
(*     (\*TO CHECK merging nodes*\) *)
(*     let fct (es:CF.entail_state) = *)
(*       let es = CF.clear_entailment_vars es in *)
(*       (\*create a tmp estate for normalizing*\) *)
(*       let tmp_es = CF.empty_es (CF.mkTrueFlow ()) es.CF.es_group_lbl no_pos in *)
(*       CF.Ctx {es with CF.es_formula = normalize_formula_w_coers prog tmp_es es.CF.es_formula prog.prog_left_coercions} *)
(*     in *)
(*     let res = CF.transform_list_failesc_context (idf,idf,fct) lctx in *)
(*     res *)

(* let normalize_list_failesc_context_w_lemma prog lctx = *)
(*   let pr = pr_none in *)
(*   Debug.no_1 "normalize_list_failesc_context_w_lemma" pr pr *)
(*       (normalize_list_failesc_context_w_lemma prog) lctx *)
  
let rec check_specs_infer (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) (spec_list:CF.struc_formula) e0 do_infer: 
      CF.struc_formula * (CF.formula list) * ((CP.rel_cat * CP.formula * CP.formula) list) * (CF.hprel list) * (CP.spec_var list) * (CP.spec_var list) * ( CP.spec_var* CP.xpure_view) list * bool =
  let _ = pre_ctr # reset in
  let _ = post_ctr # reset in
  let pr1 = Cprinter.string_of_struc_formula in
  (* let pr1n s = Cprinter.string_of_struc_formula (CF.norm_specs s) in *)
  let pr2 = add_str "inferred rels" (fun l -> string_of_int (List.length l)) in
  let pr2a = add_str "formulae" (pr_list Cprinter.string_of_formula) in
  let pr2b = add_str "inferred hp rels" (fun l -> string_of_int (List.length l)) in
  let pr4 = Cprinter.string_of_spec_var_list in
  let pr5 = pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_xpure_view) in
  let pr3 = pr_hepta pr1 pr2a  pr2 pr2b pr4 pr5 string_of_bool in
  let f = wrap_proving_kind "CHECK-SPECS" (check_specs_infer_a prog proc ctx e0 do_infer) in
  Debug.no_1 "check_specs_infer" pr1 pr3
      (fun _ -> f spec_list) spec_list

(* Termination *)      
(* This procedure to check that Term[x1,x2,...,xn] are bounded by x1,x2,...,xn>=0 *)
(* In case of failure, please put message into term_msg stack *)
(* The resulting ctx may contain inferred constraint *)
and check_bounded_term_x prog ctx post_pos =
  let check_bounded_one_measures m es =
    (* Termination: filter the exp of phase variables 
     * (their value non-negative numbers in default) *)
    let m = List.filter (fun e -> 
        not (Gen.BList.overlap_eq CP.eq_spec_var (CP.afv e) prog.prog_logical_vars)) m in
    if m == [] then (es, CF.SuccCtx [(CF.Ctx es)])
    else begin
      let m_pos = match m with
        | [] -> no_pos
        | e::_ -> CP.pos_of_exp e 
      in
      let ctx = CF.Ctx es in
      let bnd_formula_l = List.map (fun e ->
          CP.mkPure (CP.mkGte e (CP.mkIConst 0 m_pos) m_pos)) m in
      let bnd_formula = CF.formula_of_pure_formula
        (CP.join_conjunctions bnd_formula_l) m_pos in
      let rs, _ = heap_entail_one_context 12 prog false ctx bnd_formula None None None post_pos in
      let _ = Debug.trace_hprint (add_str "Result context" 
          !CF.print_list_context) rs no_pos in
      let term_pos = (m_pos, no_pos) in
      let term_res, n_es =
        let f_ctx = CF.formula_of_context ctx in
        if (CF.isFailCtx rs) then 
          let tr = (term_pos, None, Some f_ctx, Term.MayTerm_S (Term.Not_Bounded_Measure m)) in
          let err_msg = Term.string_of_term_res tr in
          let _ = Term.add_term_err_stk err_msg in
          tr, { es with CF.es_term_err = Some err_msg }
        else 
          (term_pos, None, Some f_ctx, Term.Term_S Term.Bounded_Measure),
        es
      in
      let _ = Debug.trace_hprint (add_str "New es" !CF.print_entail_state) n_es no_pos in
      let _ = Term.add_term_res_stk term_res in 
      n_es, rs
    end
  in
  let check_bounded_one_measures m es =
    Debug.no_1 "check_bounded_one_measures"
        (pr_list !CP.print_exp) (fun _ -> "")
        (fun _ -> check_bounded_one_measures m es) m
  in 
  
  if (!Globals.dis_term_chk || !Globals.dis_bnd_chk) then (ctx, [])
  else 
    let ctx = Term.strip_lexvar_lhs ctx in
    match ctx with
      | CF.Ctx es ->  
            let m = match es.CF.es_var_measures with
              | None -> []
              | Some (_, ml, _) -> ml
            in 
            let _ = Debug.trace_hprint (add_str "Measures" 
                (pr_list !CP.print_exp)) m no_pos in
            let _ = Debug.trace_hprint (add_str "Orig context" 
                !CF.print_context) ctx no_pos in
            let n_es, rs = check_bounded_one_measures m es in
            (CF.Ctx n_es, Inf.collect_rel_list_context rs)
      | CF.OCtx (ctx1, ctx2) ->
            let n_ctx1, rl1 = check_bounded_term prog ctx1 post_pos in
            let n_ctx2, rl2 = check_bounded_term prog ctx2 post_pos in
            (CF.OCtx (n_ctx1, n_ctx2), rl1 @ rl2)

and check_bounded_term prog ctx post_pos =
  let pr = !CF.print_context in
  let pr1 = pr_pair !CF.print_context (pr_list Cprinter.string_of_lhs_rhs) in
  let f = wrap_proving_kind "TERM-BND" (check_bounded_term_x prog ctx) in
  Debug.no_1 "check_bounded_term" pr pr1 (fun _ -> f post_pos) ctx

(*and check_specs_infer_a (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) (sp:CF.struc_formula) e0 do_infer: 
  CF.struc_formula * (CF.formula list) * ((CP.rel_cat * CP.formula * CP.formula) list) * bool = do_spec_verify_infer prog proc ctx sp e0 do_infer*)
      
and check_specs_infer_a (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) (e0:exp) (do_infer:bool) (spec: CF.struc_formula)  
      : CF.struc_formula * (CF.formula list) * ((CP.rel_cat * CP.formula * CP.formula) list) *(CF.hprel list) * (CP.spec_var list)* (CP.spec_var list) * (CP.spec_var*CP.xpure_view ) list * bool =
  let rec helper (ctx : CF.context) (spec: CF.struc_formula) :  CF.struc_formula * (CF.formula list) * ((CP.rel_cat * CP.formula * CP.formula) list) *(CF.hprel list) * (CP.spec_var list)* (CP.spec_var list) * (CP.spec_var*CP.xpure_view) list * bool =
    let pos_spec = CF.pos_of_struc_formula spec in
    let _= proving_loc # set pos_spec in
    log_spec := (Cprinter.string_of_struc_formula spec) ^ ", Line " ^ (string_of_int pos_spec.start_pos.Lexing.pos_lnum);	 
    match spec with
      | CF.ECase b ->
            let r =
	          List.map (fun (c1, c2) -> 
		          let nctx = CF.transform_context (combine_es_and prog (MCP.mix_of_pure c1) true) ctx in
		          let (new_c2,pre,rel,hprel, sel_hps,sel_post_hps, unk_map,f) = helper nctx c2 in
                  (* Thai: Need to generate EBase from pre if necessary *)
                  let new_c2 =  if pre!=[] then (pre_ctr # inc ; CF.merge_struc_pre new_c2 pre) else new_c2 in
		          ((c1,new_c2),(rel,f),((hprel, sel_hps),(sel_post_hps,unk_map)))) b.CF.formula_case_branches
            in
            let (cbl,fl,hprel_ls) = split3 r in
            let (rel_ls,fl) = List.split fl in
            let rel = List.concat rel_ls in
            let hp_pairs1,hp_pairs2 = List.split hprel_ls in
            let hprels,sel_hps = List.split hp_pairs1 in
            let sel_post_hps,ls_unk_map = List.split hp_pairs2 in
            let hprel = List.concat hprels in
            let sel_hps = List.hd sel_hps in
            let unk_map = List.concat ls_unk_map in
            let br = List.for_all pr_id fl in
            let new_spec = CF.ECase {b with CF.formula_case_branches=cbl} in
            (new_spec,[],rel,hprel, sel_hps,List.concat sel_post_hps, unk_map,br)
                (* (new_spec,[],true) *)
      | CF.EBase b ->
            let vs = b.CF.formula_struc_explicit_inst @ b.CF.formula_struc_implicit_inst in
            stk_vars # push_list vs;
            Debug.devel_zprint (lazy ("check_specs: EBase: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos;
            (*************************************************************)
            (********* Check permissions variables in pre-condition ******)
            (*************************************************************) 
	        let has_lexvar = CF.has_lexvar_formula b.CF.formula_struc_base in
            let ctx,ext_base = if (!Globals.ann_vp) && (not has_lexvar) then
              check_varperm prog proc spec ctx b.CF.formula_struc_base pos_spec 
            else (ctx,b.CF.formula_struc_base)
            in
            (*************************************************************)
            (*****<<<< Check permissions variables in pre-condition ******)
            (*************************************************************) 
	        let nctx = 
	          if !Globals.max_renaming 
	          then (CF.transform_context (CF.normalize_es ext_base b.CF.formula_struc_pos false) ctx) (*apply normalize_es into ctx.es_state*)
	          else (CF.transform_context (CF.normalize_clash_es ext_base b.CF.formula_struc_pos false) ctx) in
	        (* Termination: Move lexvar to es_var_measures *)
	        let nctx = if (not has_lexvar) then nctx else Term.strip_lexvar_lhs nctx in
            let (c,pre,rels,hprels, sel_hps,sel_post_hps, unk_map,r) = match b.CF.formula_struc_continuation with | None -> (None,[],[],[],[], [], [],true) | Some l -> let r1,r2,r3,r4,r5,r6,r7,r8 = helper nctx l in (Some r1,r2,r3,r4,r5,r6,r7,r8) in            stk_vars # pop_list vs;
	        let _ = Debug.devel_zprint (lazy ("\nProving done... Result: " ^ (string_of_bool r) ^ "\n")) pos_spec in
            let new_base = match pre with
              | [] -> b.CF.formula_struc_base
              | [p] -> (pre_ctr # inc; Solver.simplify_pre (CF.normalize 1 b.CF.formula_struc_base p pos_spec) [])
              | _ -> report_error pos_spec ("Spec has more than 2 pres but only 1 post") in
            Debug.trace_hprint (add_str "Base" !CF.print_formula) b.CF.formula_struc_base no_pos;
            Debug.trace_hprint (add_str "New Base" !CF.print_formula) new_base no_pos;
            let _ = if (rels) ==[] && hprels == [] then () else pre_ctr#inc  in
	        (CF.EBase {b with CF.formula_struc_base = new_base; CF.formula_struc_continuation = c}, [], rels,hprels,sel_hps,sel_post_hps,unk_map, r)
      | CF.EInfer b ->
            Debug.devel_zprint (lazy ("check_specs: EInfer: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos;
            let postf = b.CF.formula_inf_post in
            let postxf = b.CF.formula_inf_xpost in
            let vars = if do_infer then b.CF.formula_inf_vars else [] in
            let _ = Debug.ninfo_pprint ("EInfer: " ^ (!CP.print_svl vars)) no_pos in
            let new_formula_inf_continuation,new_args = 
              begin
                match b.CF.formula_inf_transpec with
                  | None -> b.CF.formula_inf_continuation,[]
                  | Some (old_view_name, new_view_name) -> 
                        let old_view = look_up_view_def b.CF.formula_inf_pos prog.prog_view_decls old_view_name in
                        let new_view = look_up_view_def b.CF.formula_inf_pos prog.prog_view_decls new_view_name in
                        let sub_pair = ((old_view_name,old_view.view_vars),(new_view_name,new_view.view_vars)) in
                        let new_spec,new_args = CF.tran_spec b.CF.formula_inf_continuation sub_pair in
                        Debug.tinfo_hprint (add_str "NEW SPECS" pr_spec) new_spec no_pos;
                        new_spec,new_args
              end
            in
            let vars, new_formula_inf_continuation = 
              if vars = [] then
                begin
                  match postxf with
                    | None -> 
                          if new_args = [] then [],new_formula_inf_continuation 
                          else
                            let pre_vars,_,_ = CF.get_pre_post_vars [] new_formula_inf_continuation in
                            let pre_args, _ = List.partition (fun x -> List.mem x pre_vars) new_args in
                            (*                      let new_rel_pre = CP.fresh_spec_var_rel () in*)
                            let new_rel_post = CP.fresh_spec_var_rel () in
                            (*                      let new_rel_fml_pre = CP.BForm ((CP.RelForm (new_rel_pre, List.map (fun v -> CP.mkVar v no_pos) pre_args, no_pos),None),None) in*)
                            let new_rel_fml_post = CP.BForm ((CP.RelForm (new_rel_post, List.map (fun v -> CP.mkVar v no_pos) new_args, no_pos),None),None) in
                            let new_spec = CF.add_pure new_formula_inf_continuation None (Some new_rel_fml_post) in
                            Debug.tinfo_hprint (add_str "NEW SPECS" pr_spec) new_spec no_pos;
                            pre_args@[new_rel_post],new_spec
                    | Some pflag -> 
                          if not(pflag) then 
                            if new_args = [] then 
                              let pre_vars,_,_ = CF.get_pre_post_vars [] new_formula_inf_continuation in
                              pre_vars,new_formula_inf_continuation
                            else 
                              (*                        let new_rel = CP.fresh_spec_var_rel () in*)
                              (*                        let new_rel_fml = CP.BForm ((CP.RelForm (new_rel, List.map (fun v -> CP.mkVar v no_pos) new_args, no_pos),None),None) in*)
                              (*                        let new_spec = CF.add_pure new_formula_inf_continuation (Some new_rel_fml) None in*)
                              (*                        Debug.info_hprint (add_str "NEW SPECS" pr_spec) new_spec no_pos;*)
                              (*                        [new_rel],new_spec*)
                              new_args,new_formula_inf_continuation
                          else
                            if pflag then
                              let new_rel = CP.fresh_spec_var_rel () in
                              let new_rel_fml = CP.BForm ((CP.RelForm (new_rel, List.map (fun v -> CP.mkVar v no_pos) new_args, no_pos),None),None) in
                              let new_spec = CF.add_pure new_formula_inf_continuation None (Some new_rel_fml) in
                              Debug.tinfo_hprint (add_str "NEW SPECS" pr_spec) new_spec no_pos;
                              [new_rel],new_spec
                            else [],new_formula_inf_continuation
                end
              else vars,new_formula_inf_continuation 
            in
            let _ = proc.proc_stk_of_static_specs # push new_formula_inf_continuation in
            let (vars_rel,vars_inf) = List.partition (fun v -> CP.type_of_spec_var v == RelT ) vars in
            let (vars_hp_rel,vars_inf) = List.partition (fun v -> CP.type_of_spec_var v == HpT ) vars_inf in
            let new_vars = vars_inf @ (List.filter (fun r -> List.mem r (CF.struc_fv new_formula_inf_continuation)) vars_rel) in
            let new_vars = new_vars @ (List.filter (fun r -> List.mem r (CF.struc_fv new_formula_inf_continuation)) vars_hp_rel) in
            (if new_vars!=[] || postf then pre_ctr # inc) ;
            let nctx = CF.transform_context (fun es -> 
                CF.Ctx {es with CF.es_infer_vars = es.CF.es_infer_vars@vars_inf;
                    CF.es_infer_vars_rel = es.CF.es_infer_vars_rel@vars_rel;
                    CF.es_infer_vars_hp_rel = es.CF.es_infer_vars_hp_rel@vars_hp_rel;
                    CF.es_infer_vars_sel_hp_rel = es.CF.es_infer_vars_sel_hp_rel@vars_hp_rel;
                    CF.es_infer_vars_sel_post_hp_rel = es.CF.es_infer_vars_sel_post_hp_rel;
                    CF.es_infer_post = es.CF.es_infer_post || postf}) ctx in
            let (c,pre,rel,hprel, _, post_hps ,unk_map,f) = helper nctx new_formula_inf_continuation in
            let new_c = if pre=[] then c else
              match c with
                | CF.EAssume _ -> CF.EBase {
                      CF.formula_struc_explicit_inst = [];
                      CF.formula_struc_implicit_inst = [];
                      CF.formula_struc_exists = [];
                      CF.formula_struc_base = (match pre with 
                        | [a] -> a 
                        | _ -> report_error pos_spec ("Spec has more than 2 pres but only 1 post"));
                      CF.formula_struc_continuation = Some c;
                      CF.formula_struc_pos = pos_spec;}
                | _ -> c in
            (new_c,[],rel,hprel,vars_hp_rel,post_hps,unk_map,f)
      | CF.EList b -> 
	        let (sl,pl,rl,hprl,selhps,sel_posthps,unk_map,bl) = List.fold_left (fun (a1,a2,a3,a4,a5,a6,a7,a8) (l,c) ->
		        let (b1,b2,b3,b4,b5,b6,b7,b8) =
                  store_label # set l;
                  helper (CF.update_ctx_label ctx l) c in
		        (a1@[(l,b1)],a2@b2,a3@b3,a4@b4,a5@b5,a6@b6,a7@b7,a8@[b8])) ([],[],[],[],[],[],[],[]) b in
	        Debug.trace_hprint (add_str "SPECS (before norm_specs)" pr_spec) (CF.EList sl) no_pos;
	        (CF.norm_specs (CF.EList sl), pl, rl, hprl,selhps,sel_posthps, unk_map,List.for_all pr_id bl) 
      | CF.EOr b -> 
	        let s1,p1,r1,hpr1,selhp1,post_selhp1,unk_map1,b1 = helper ctx b.CF.formula_struc_or_f1 in
            let s2,p2,r2,hpr2,selhp2,post_selhp2,unk_map2,b2 = helper ctx b.CF.formula_struc_or_f2 in
	        (CF.norm_specs (CF.EOr {b with CF.formula_struc_or_f1 = s1;CF.formula_struc_or_f2 = s2;}), p1@p2, r1@r2,
            hpr1@hpr2, selhp1@selhp2,post_selhp1@post_selhp2, unk_map1@unk_map2, pr_id b1 && pr_id b2)
      | CF.EAssume (var_ref,post_cond,post_label,etype) ->
            let curr_vars = stk_vars # get_stk in
            (* let ovars = CF.fv post_cond in *)
            (* let ov = CP.diff_svl ovars curr_vars in *)
            in_vars # set curr_vars ;
            Debug.tinfo_hprint (add_str "curr vars" !CP.print_svl) curr_vars no_pos;
            (* Debug.info_hprint (add_str "fv post" !CP.print_svl) ovars no_pos; *)
            (* Debug.info_hprint (add_str "out vars" !CP.print_svl) ov no_pos; *)
	        if(Immutable.is_lend post_cond) then
	          Error.report_error {Error.error_loc = pos_spec; Error.error_text =  ("The postcondition cannot contain @L heap predicates/data nodes\n")}
	        else
              let _ = post_pos#set (CF.pos_of_formula post_cond) in
              Debug.devel_zprint (lazy ("check_specs: EAssume: " ^ (Cprinter.string_of_context ctx) ^ "\n")) no_pos;
              (*let _ = print_endline  ("todo:check_specs: EAssume: " ^ (Cprinter.string_of_context ctx) ^ "\n") in*)
	          let ctx1 = if !Globals.disable_pre_sat then ctx else CF.transform_context (elim_unsat_es 2 prog (ref 1)) ctx in
	          if (CF.isAnyFalseCtx ctx1) then
	            let _ = Debug.devel_zprint (lazy ("\nFalse precondition detected in procedure "^proc.proc_name^"\n with context: "^
	    	        (Cprinter.string_of_context_short ctx))) no_pos in
	            let _ = print_endline ("\n\nWarning: False precondition detected in procedure "^proc.proc_name^"\n with context: "^ (Cprinter.string_of_context_short ctx)) in
	            (spec,[],[],[], [], [],[],true)
	          else
	            let _ = Gen.Profiling.push_time ("method "^proc.proc_name) in
	            try
	              let spec_and_inferred_post, inferred_pre, inferred_rel, inferred_hp_rel, sel_hps,sel_post_hps, unk_map, r =
	                flow_store := [];
	                let ctx1 = CF.set_flow_in_context_override
	    	          { CF.formula_flow_interval = !norm_flow_int; CF.formula_flow_link = None} ctx1 in
	                let ctx1 = CF.add_path_id ctx1 (Some post_label,-1) in
                    (* need to add initial esc_stack *)
                    let init_esc = [((0,""),[])] in
	                let lfe = [CF.mk_failesc_context ctx1 [] init_esc] in
                    (* Termination: Check boundedness of the measures 
                     * before going into the function body *)
                    let (_, rankbnds) = check_bounded_term prog ctx1 (CF.pos_of_formula post_cond) in
		    let _ = Gen.Profiling.push_time "typechecker : check_exp" in
                    let res_ctx = check_exp prog proc lfe e0 post_label in
                    (*Clear es_pure before check_post*)
	                let res_ctx =  CF.transform_list_failesc_context (idf,idf, (fun es -> CF.Ctx (CF.clear_entailment_es_pure es))) res_ctx in
	    	    let res_ctx = CF.list_failesc_to_partial res_ctx in
		    let _ = Gen.Profiling.pop_time "typechecker : check_exp" in
	            (* let _ = print_string ("\n WN 1 :"^(Cprinter.string_of_list_partial_context res_ctx)) in *)
	    	    let res_ctx = CF.change_ret_flow_partial_ctx res_ctx in
	            (* let _ = print_string ("\n WN 2 : "^(Cprinter.string_of_list_partial_context res_ctx)) in*)
                    let pos = CF.pos_of_formula post_cond in
	    	        if (CF.isFailListPartialCtx_new res_ctx)
                    then (spec, [], [],[], [],[],[], false)
	    	        else
                      let lh = Inf.collect_pre_heap_list_partial_context res_ctx in
                      let lp = Inf.collect_pre_pure_list_partial_context res_ctx in
                      let post_iv = Inf.collect_infer_vars_list_partial_context res_ctx in
                      (* Why? Bug cll-count-base.ss *)
                      (* no abductive inference for post-condition *)
                      (* let res_ctx = if !do_abd_from_post then res_ctx else 
                         Inf.remove_infer_vars_all_list_partial_context res_ctx in*)
                      (* let iv = CF.collect_infer_vars ctx in *)
                      let postf = CF.collect_infer_post ctx in
                      let (impl_vs,post_cond) =
                        (* below seems to cause problem for verification *)
                        (* see bug-sort-ll.ss *)
                        if  pre_ctr # get > 0  then 
                          let (impl_vs,new_post) = CF.lax_impl_of_post post_cond in
                          if impl_vs!=[] then
                            begin
                              DD.devel_pprint ">>>>>> Convert Exists to Implicit Vars for Post-Cond <<<<<<" pos;
                              DD.devel_pprint ("Extra Vars :"^(Cprinter.string_of_spec_var_list impl_vs)) pos;
                              DD.devel_pprint ("New Post Cond :"^(Cprinter.string_of_formula new_post)) pos
                            end;
                          (impl_vs,new_post)
                        else ([],post_cond) in
                      stk_evars # push_list impl_vs;
                      (* TODO: Timing *)
                      let pres, posts, _ = CF.get_pre_post_vars [] (proc.proc_stk_of_static_specs # top) in
                      let pre_vars = CP.remove_dups_svl (pres @ (List.map 
                          (fun (t,id) -> CP.SpecVar (t,id,Unprimed)) proc.proc_args)) in
                      let impl_vs, expl_vs = List.partition (fun v -> CP.mem_svl v (pre_vars@posts)) impl_vs in
                      DD.devel_pprint ("Pre Vars :"^(Cprinter.string_of_spec_var_list pre_vars)) pos;
                      DD.devel_pprint ("Post Vars :"^(Cprinter.string_of_spec_var_list posts)) pos;
                      DD.devel_pprint ("Extra Implicit Vars :"^(Cprinter.string_of_spec_var_list impl_vs)) pos;
                      DD.devel_pprint ("Extra Explicit Vars :"^(Cprinter.string_of_spec_var_list expl_vs)) pos;
                      (* TODO: Timing *)
                      let res_ctx = Inf.add_impl_expl_vars_list_partial_context impl_vs expl_vs res_ctx in
                      let pos_post = (CF.pos_of_formula post_cond) in
                      (* Termination: Collect the constraints of
                       * phase transitions inferred by inference 
                       * Need to filter the constraints and normalize 
                       * them - We only interest constraints related 
                       * to logical variables *)
                      let _ = if !Globals.dis_term_chk then () else
                        let log_vars = prog.Cast.prog_logical_vars in
                        let cl = List.filter (fun f -> 
                            Gen.BList.overlap_eq CP.eq_spec_var (CP.fv f) log_vars) lp in
                        let _ = if not (Gen.is_empty lp) then 
                          DD.ninfo_hprint (add_str "Inferred constraints" (pr_list !CP.print_formula)) lp pos in
                        let _ = Term.add_phase_constr_by_scc proc (List.map TP.simplify_raw cl) in ()
                      in
                      (* TODO : collecting rel twice as a temporary fix to losing ranking rel inferred during check_post *)
                      (*                      let rel1 =  Inf.collect_rel_list_partial_context res_ctx in*)
                      (*                      DD.dinfo_pprint ">>>>> Performing check_post STARTS" no_pos;*)
                      let tmp_ctx = check_post prog proc res_ctx post_cond pos_post post_label etype in
                      (*                      DD.dinfo_pprint ">>>>> Performing check_post ENDS" no_pos;*)
                      (* Termination: collect error messages from successful states *)
                      let term_err_msg = CF.collect_term_err_list_partial_context tmp_ctx in 
                      let _ = List.iter (fun m -> Term.add_term_err_stk m) term_err_msg in
                      (*                      let rel2 = Inf.collect_rel_list_partial_context tmp_ctx in*)
                      (*                      let rels = Gen.BList.remove_dups_eq (==) (rel1@rel2) in*)
                      let rels = Gen.BList.remove_dups_eq (=) (Inf.collect_rel_list_partial_context tmp_ctx) in
                      let hp_rels = Gen.BList.remove_dups_eq (=) (Inf.collect_hp_rel_list_partial_context tmp_ctx) in
                      let sel_hps= CP.remove_dups_svl (CF.get_infer_vars_sel_hp_partial_ctx_list tmp_ctx) in
                      let sel_post_hps= CP.remove_dups_svl (CF.get_infer_vars_sel_post_hp_partial_ctx_list tmp_ctx) in
                      let unk_map = Inf.collect_hp_unk_map_list_partial_context tmp_ctx in
                      let res = CF.isSuccessListPartialCtx tmp_ctx in
                      (* Debug.info_pprint ("TMP CTX: " ^ (Cprinter.string_of_list_partial_context tmp_ctx) ^ "\n") no_pos; *)
                      let lp = (* if not !do_abd_from_post then lp else ( *)
                        Debug.devel_zprint (lazy ("TMP CTX: " ^ (Cprinter.string_of_list_partial_context tmp_ctx) ^ "\n")) no_pos;
                        let lp_new = Inf.collect_pre_pure_list_partial_context tmp_ctx in
                        (*let old_lp = CP.conj_of_list lp no_pos in*)
                        (*DD.devel_pprint ("Old inferred Pure :"^(pr_list Cprinter.string_of_pure_formula lp)) pos;
                          DD.devel_pprint ("New inferred Pure :"^(pr_list Cprinter.string_of_pure_formula lp_new)) pos;*)
                        let lp_new = List.filter (fun p -> (*not(TP.imply_raw p old_lp) && *)not(CP.include_specific_val p)) lp_new in
                        lp@lp_new (* ) *) 
                      in
                      let infer_pre_flag = (List.length lh)+(List.length lp) > 0 in
                      (* Fail with some tests *)
                      let infer_post_flag = postf in
                      (* let infer_post_flag = false in *)
                      let new_spec_post, pre =
                        if res then
                          let flist = Inf.collect_formula_list_partial_context tmp_ctx in
                          let i_pre =
                            if infer_pre_flag then (
                                DD.info_pprint ">>>>>> HIP gather infer pre <<<<<<" pos;
                                DD.info_pprint ("Inferred Heap :"^(pr_list Cprinter.string_of_h_formula lh)) pos;
                                DD.info_pprint ("Inferred Pure :"^(pr_list Cprinter.string_of_pure_formula lp)) pos;
                                (* print_endline ("\nInferred Heap:"^(pr_list Cprinter.string_of_h_formula lh)) ; *)
                                (* print_endline ("Inferred Pure:"^(pr_list Cprinter.string_of_pure_formula lp)); *)
                                (*let vars = (List.concat (List.map CF.h_fv lh)) @ (List.concat (List.map CP.fv lp)) in*)
                                let fml = List.fold_left CF.normalize_combine_heap (CF.formula_of_heap CF.HEmp no_pos) lh in
                                let fml = CF.normalize 1 fml (CF.formula_of_pure_formula (CP.arith_simplify_new (CP.conj_of_list lp no_pos)) no_pos) no_pos in
                                if Solver.verify_pre_is_sat prog fml then [fml] else []
                            )
                            else
                              (*print_endline " ";*)
                              []
                                  (* CF.formula_of_heap CF.HTrue no_pos *)
                          in
                          let i_post =
                            if not(infer_post_flag) then spec
                            else
                              if rels!=[] then let _ = post_ctr # inc in spec
                              else
                                begin
                                  let _ = post_ctr # inc in
                                  let pre_vars = CF.context_fv ctx in
                                  (* filter out is_prime *)
                                  let pre_vars = List.filter (fun v -> not(CP.is_primed v)) pre_vars in
                                  (* add vars of pre *)
                                  let pre_vars = pre_vars @ (if i_pre = [] then [] else CF.fv (List.hd i_pre)) in
                                  (* (\* add infer_vars *\) *)
                                  let pre_vars = CP.remove_dups_svl (pre_vars @ post_iv) in
                                  (* drop @L heap nodes from flist *)
                                  let flist = List.map CF.remove_lend flist in
                                  (*let _ = List.iter (fun f -> print_endline ("FLIST: " ^ Cprinter.string_of_formula f)) flist in*)
                                  let flist = Gen.BList.remove_dups_eq (=) (flist) in
                                  (* TODO: flist denotes a disjunction! see ll-b.ss *)
                                  let post_vars = List.concat (List.map CF.fv flist) in
                                  let heap_vars = List.concat (List.map (fun f -> CF.fv_heap_of f) flist) in
                                  let heap_vars_init = CF.fv_heap_of post_cond in
                                  (* ref parameters *)
                                  let vr = List.map CP.to_primed var_ref in
                                  let post_vars = CP.diff_svl post_vars (pre_vars@heap_vars@heap_vars_init@vr) in
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
                                  (* TODO : What if we have multiple ensures in a spec? *)
                                  (* It may be too early to compute a fix-point. *)
                                  let post_fml,_ = (*if rels = [] then *)Solver.simplify_post post_fml post_vars prog None [] true [] [] in
                                  DD.devel_pprint ">>>>>> HIP gather inferred post <<<<<<" pos;
                                  DD.devel_pprint ("Initial Residual post :"^(pr_list Cprinter.string_of_formula flist)) pos;
                                  DD.devel_pprint ("Final Post :"^(Cprinter.string_of_formula post_fml)) pos;
                                  (* print_endline ("Initial Residual Post : "^(pr_list Cprinter.string_of_formula flist)); *)
                                  (* print_endline ("Final Residual Post : "^(Cprinter.string_of_formula post_fml)); *)
                                  let inferred_post = CF.EAssume (CP.remove_dups_svl (var_ref(* @post_vars *)),post_fml,post_label, etype) in
                                  inferred_post
                                end in
                          (i_post, i_pre)
                        else (spec,[])
                      in (new_spec_post, pre, rankbnds@rels, hp_rels,sel_hps,sel_post_hps, unk_map, res)
	              in
	              let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in
	              (spec_and_inferred_post,inferred_pre,inferred_rel,inferred_hp_rel, sel_hps,sel_post_hps, unk_map, r)
	            with
                  | Err.Ppf (e, ifk) ->
                        (match ifk with
                          | 1 -> if CF.is_error_flow post_cond  then
                              (spec, [],[],[],[],[], [], true) else
                                let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in
                                (Err.report_error1 e "Proving precond failed")
                          | 3 ->
                                if CF.is_top_flow post_cond then
                                  (spec, [],[],[],[],[],[], true) else
                                    let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in
                                    (Err.report_error1 e "Proving precond failed")
                          | _ -> let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in
                            (Err.report_error1 e "Proving precond failed")
                        )
                  |_ as e ->
	                   let _ = Gen.Profiling.pop_time ("method "^proc.proc_name) in raise e
  in 
  helper ctx spec 

(*we infer automatically from ctx*)
and infer_lock_invariant_x lock_var ctx pos =
  try 
      let found_args,found_name = CF.collect_heap_args_list_failesc_context ctx lock_var in
      let found_arg_names = List.map (fun v -> CP.name_of_spec_var v) found_args in
      if (found_name = "") then
        report_error pos "Scall : could not infer invariant name"
      else if (found_name = lock_name) then
        report_error pos "Scall : lock has not been initialized"
      else
        (found_name,found_arg_names)
  with _ -> report_error pos ("Scall : could not find heap node for lock " ^ (Cprinter.string_of_spec_var lock_var))

(*
  transform l1=l2 into l1=l2 & level(l1)=level(l2)
  This is to maintain information about locklevels in the presence
  of elim_exists
*)
and trans_level_eqn_list_failesc_context (ctx: CF.list_failesc_context) : CF.list_failesc_context =
  let translate_level_es es =
    let new_f = CF.translate_level_eqn_formula es.CF.es_formula in
    let new_es = {es with CF.es_formula = new_f} in (*trigger unsat_check*)
    CF.Ctx new_es
  in
  let ctx = CF.transform_list_failesc_context (idf,idf,translate_level_es) ctx in
  ctx

(*
  transform level(l1) into l1_mu
*)
and trans_level_list_partial_context (ctx:CF.list_partial_context) : CF.list_partial_context =
  let translate_level_es es =
    let new_f = CF.translate_level_formula es.CF.es_formula in
    let new_es = {es with CF.es_formula = new_f} in (*trigger unsat_check*)
    CF.Ctx new_es
  in
  let ctx = CF.transform_list_partial_context (translate_level_es, (fun c -> c)) ctx in
  ctx

and infer_lock_invariant lock_var ctx pos =
  let pr_out = pr_pair Cprinter.string_of_ident (pr_list Cprinter.string_of_ident) in
  Debug.no_2 "infer_lock_invariant"
      Cprinter.string_of_spec_var Cprinter.string_of_list_failesc_context pr_out
      (fun _ _ -> infer_lock_invariant_x lock_var ctx pos) lock_var ctx
(*
   Important arugments:
   ctx,e0 : current ctx and exp
   mn : mingled procedure name
   lock: lockset (if any)
   vs: arguments of the corresponding call
*)
and check_scall_fork prog ctx e0 (post_start_label:formula_label) ret_t mn lock vs ir pid pos =
  (*=========================*)
  (*=== id=FORK(fn,args) ====*)
  (*=========================*)
  (* let _ = print_endline ("\ncheck_exp: SCall: fork") in *)
  let fn = List.hd vs in
  (* let _ = print_endline ("\ncheck_exp: SCall: vs = " ^ (string_of_ident_list vs)) in *)
  let fargs = List.tl vs in
  let proc = look_up_proc_def pos prog.new_proc_decls fn in
  let farg_types, farg_names = List.split proc.proc_args in
  let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
  let actual_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) fargs farg_types in
  (*=======check_pre_post========*)
  (* Internal function to check pre/post condition of the fork call. *)
  let check_pre_post org_spec (sctx:CF.list_failesc_context) should_output_html : CF.list_failesc_context =
    (* Termination: Stripping the "variance" feature from org_spec
	   if the call is not a recursive call *)
    (*TO CHECK: neccessary -> YES*)
    (*fork is not a recursive call*)
	let stripped_spec = org_spec in
    (* org_spec -> stripped_spec *)
	(* free vars = linking vars that appear both in pre and are not formal arguments *)
    let pre_free_vars = Gen.BList.difference_eq CP.eq_spec_var
      (Gen.BList.difference_eq CP.eq_spec_var (Cformula.struc_fv stripped_spec(*org_spec*))
           (Cformula.struc_post_fv stripped_spec(*org_spec*))) farg_spec_vars in
    (*LOCKSET: ls is not free var, it is a ghost argument in proc_args*)
    (* let _ = print_endline (" ### pre_free_vars = " ^ (Cprinter.string_of_spec_var_list pre_free_vars)) in *)
    let ls_var = [(CP.mkLsVar Unprimed)] in
    let lsmu_var = [(CP.mkLsmuVar Unprimed)] in
    let waitlevel_var = [(CP.mkWaitlevelVar Unprimed)] in (*added for consistency, later waitlevel constraints are removed*)
    (*when fork, do not consider waitlevel because it is not used
      for delayed checking*)
    let pre_free_vars = List.filter (fun v -> CP.name_of_spec_var v <> Globals.ls_name && CP.name_of_spec_var v <> Globals.lsmu_name && CP.name_of_spec_var v <> Globals.waitlevel_name) pre_free_vars in
    (* free vars get to be substituted by fresh vars *)
    let pre_free_vars_fresh = CP.fresh_spec_vars pre_free_vars in
    let renamed_spec = 
      if !Globals.max_renaming then (Cformula.rename_struc_bound_vars stripped_spec(*org_spec*))
      else (Cformula.rename_struc_clash_bound_vars stripped_spec(*org_spec*) (CF.formula_of_list_failesc_context sctx))
    in
    let st1 = List.combine pre_free_vars pre_free_vars_fresh in
    let fr_vars = farg_spec_vars @ (List.map CP.to_primed farg_spec_vars) in
    let to_vars = actual_spec_vars @ (List.map CP.to_primed actual_spec_vars) in
    (* Termination: Cache the subst for output pretty printing *)
    (* Assume: fork is not a recursive call*)
    let renamed_spec = CF.subst_struc st1 renamed_spec in
    let renamed_spec = CF.subst_struc_avoid_capture fr_vars to_vars renamed_spec in
    let st2 = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) actual_spec_vars in
    (*ALSO rename ls to ls'*)
    (* let st_ls = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) ls_vars in *)
    (* let st3=s t2@st_ls in (*TO CHECK*) *)
    (*ALSO rename ls to ls', lsmu to lsmu'*)
    let st_ls = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) ls_var in
    let st_lsmu = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) lsmu_var in
    let st_waitlevel = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) waitlevel_var in
    let st3= st2@st_ls@st_lsmu@st_waitlevel in
    let pre2 = CF.subst_struc_pre st3 renamed_spec in
    let new_spec = (Cprinter.string_of_struc_formula pre2) in
    (*Termination checking *) (*TO CHECK: neccessary ???*)
    (* TODO: call the entailment checking function in solver.ml *)
    let to_print = "\nProving precondition in forked method " ^ proc.proc_name ^ " for spec:\n" ^ new_spec (*!log_spec*) in
    let to_print = ("\nVerification Context:"^(post_pos#string_of_pos)^to_print) in
    Debug.devel_pprint (to_print^"\n") pos;
	(* An Hoa : output the context and new spec before checking pre-condition *)
	let _ = if !print_proof && should_output_html then Prooftracer.push_list_failesc_context_struct_entailment sctx pre2 in

    (*Call heap_entail... to prove the precondition and add the post condition into thread id*)
    let tid = CP.fresh_thread_var () in
    let rs, prf = heap_entail_struc_list_failesc_context_init prog false true sctx pre2 (Some tid) None None pos pid in

	let _ = if !print_proof && should_output_html then Prooftracer.pop_div () in
    let _ = PTracer.log_proof prf in
    (* let _ = print_endline (("\n ### fork: after res ctx: ") ^ (Cprinter.string_of_list_failesc_context rs)) in *)
    if (CF.isSuccessListFailescCtx sctx) && (CF.isFailListFailescCtx rs) then
      if (!Globals.is_deployed) then
        Debug.print_info "procedure call" ("\nProving precondition in forked method " ^ proc.proc_name ^ " has failed \n") pos
      else
        Debug.print_info "procedure call" (to_print^" has failed \n") pos
    else () ;
    rs
  in
  (*=======check_pre_post - END ========*)
  (* Call check_pre_post with debug information *)
  let check_pre_post org_spec (sctx:CF.list_failesc_context) should_output_html : CF.list_failesc_context =
    (* let _ = Cprinter.string_of_list_failesc_context in *)
    let pr2 = Cprinter.summary_list_failesc_context in
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
      else check_pre_post (proc.proc_stk_of_static_specs#top) ctx scall_pre_cond_pushed
  in
  let _ = if !print_proof then Prooftracer.add_pre e0 in
  let _ = if !print_proof && scall_pre_cond_pushed then 
        begin
            Prooftracer.pop_div ();
            Tpdispatcher.restore_suppress_imply_output_state ();
        (* print_endline "OK.\n" *)
        end in
  (* let _ = print_endline (("\n ### fork: res (final) ctx: ") ^ (Cprinter.string_of_list_failesc_context res)) in *)
  res
(*=========================*)
(*===== <<< FORK ==========*)
(*=========================*)

(*
   Important arugments:
   ctx,e0 : current ctx and exp
   mn : mingled procedure name
   lock: lockset (if any)
   vs: arguments of the corresponding call
*)
and check_scall_join prog ctx e0 (post_start_label:formula_label) ret_t mn lock vs ir pid pos =
  (*=========================*)
  (*========= JOIN ==========*)
  (*=========================*)
  (* let proc = look_up_proc_def pos prog.prog_proc_decls mn in *)
  (* let farg_types, farg_names = List.split proc.proc_args in *)
  (* let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in *)
  (* let actual_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) vs farg_types in *)
  (*=======check_pre_post - START ========*)
  (*=======check_pre_post - END ========*)
  (*Find the thread and compose (or merge???) it with the main formula*)
  (*Currently, we assume pass-by-value -> merge is ok.
    Otherwise, we have to compose*)
  let tid = List.hd vs in
  let tid =  CP.SpecVar (thread_typ, tid, Primed) in (*TO CHECK: Primed or Unprimed*)
  let _ = Debug.devel_pprint ("\ncheck_exp: SCall : join : before join(" ^ (Cprinter.string_of_spec_var tid) ^") \n ### ctx: " ^ (Cprinter.string_of_list_failesc_context ctx)) pos  in
  let empty_struc = CF.mkETrue (CF.mkTrueFlow ()) pos in
  (*Perform Delay lockset checking and join at Solver.heap_entail_conjunct_lhs_struc*)
  let rs, prf = heap_entail_struc_list_failesc_context_init prog false true ctx empty_struc None None (Some tid) pos pid in
  let rs = normalize_list_failesc_context_w_lemma prog rs in
  if (CF.isSuccessListFailescCtx ctx) && (CF.isFailListFailescCtx rs) then
    Debug.print_info "procedure call" ("join("^ (CF.string_of_spec_var tid)^") has failed.\n"  ^ (Cprinter.string_of_list_failesc_context rs)^ " \n") pos else () ;
  rs
(*=========================*)
(*===<<<<<= JOIN ==========*)
(*=========================*)

(*
   Important arugments:
   ctx,e0 : current ctx and exp
   mn : mingled procedure name
   lock: lockset (if any)
   vs: arguments of the corresponding call
*)

(*========================================================*)
(*==========lock operations ==============================*)
(*== init/finalize/acquires/release[LOCK](lock,args) =====*)
(*========================================================*)
and check_scall_lock_op prog ctx e0 (post_start_label:formula_label) ret_t mn lock vs ir pid pos =
  let mn_str = Cast.unmingle_name mn in
  if (not (CF.isNonFalseListFailescCtx ctx)) then
    ctx
  else
    if (CF.isFailListFailescCtx ctx) then
      let _ = Debug.print_info "procedure call" ("\nempty/false context: Proving precondition in method " ^ mn ^ " has failed \n") pos in
      ctx
    else
      let l = List.hd vs in
      let lock_args = List.tl vs in
      let lock_var =  CP.SpecVar (lock_typ, l, Primed) in
      let lock_sort = match lock with
        | None ->
            if (mn_str=Globals.init_name) then
              Err.report_error { Err.error_loc = pos; Err.error_text = ("SCall :: init requires an associated lock");}
            else ""
        | Some v -> v
      in
      let lock_sort,lock_args = if lock_sort <> "" then
            (*user provides annotations*)
            (lock_sort,lock_args)
          else
            (*we infer automatically from ctx*)
            infer_lock_invariant lock_var ctx pos
      in
      let vdef = look_up_view_def_raw prog.prog_view_decls lock_sort in
      let types = List.map (fun v -> CP.type_of_spec_var v) vdef.view_vars in
      let new_args = List.map2 (fun arg typ ->  CP.SpecVar (typ, arg, Primed) ) lock_args types in
      let self_var =  CP.SpecVar (Named vdef.view_data_name, self, Unprimed) in
      let fr_vars = self_var::vdef.view_vars in
      let to_vars = lock_var::new_args in
      (*init/finalize does not need invariant*)
      let inv_lock = match vdef.view_inv_lock with
        | None -> 
            (CF.mkTrue (CF.mkTrueFlow ()) pos)
        | Some f -> f 
      in
      let renamed_inv = CF.subst_avoid_capture fr_vars to_vars inv_lock in
      let prepost =
        if (mn_str=Globals.acquire_name)
        then
          (***generating spec for acquire***)
          CF.prepost_of_acquire lock_var lock_sort new_args renamed_inv post_start_label pos
        else if (mn_str=Globals.release_name) then
          (***generating spec for release***)
          CF.prepost_of_release lock_var lock_sort new_args renamed_inv post_start_label pos
        else if (mn_str=Globals.finalize_name) then
          (***generating spec for finalize***)
          CF.prepost_of_finalize lock_var lock_sort new_args post_start_label pos
        else
          (***generating spec for init***)
          CF.prepost_of_init lock_var lock_sort new_args post_start_label pos
      in
      let prepost = prune_pred_struc prog true prepost in (* specialise --eps *)
      let ctx = 
        if (mn_str=Globals.finalize_name) then
          (*try to combine fractional permission before finalize*)
          normalize_list_failesc_context_w_lemma prog ctx
        else ctx
      in
      let to_print = "\nProving precondition in method " ^ mn ^ " for spec:\n" ^ (Cprinter.string_of_struc_formula prepost)  in
      let to_print = ("\nVerification Context:"^(post_pos#string_of_pos)^to_print) in
      Debug.devel_zprint (lazy (to_print^"\n")) pos;
      (*TO CHECK: clear_entailment can effect reasoning??? *)
	  let ctx = CF.clear_entailment_history_failesc_list (fun x -> None) ctx in
      let rs, prf = heap_entail_struc_list_failesc_context_init prog false true ctx prepost None None None pos pid in
      (* let _ = print_string (("\nSCall: acquire: rs =  ") ^ (Cprinter.string_of_list_failesc_context rs) ^ "\n") in *)
      if (CF.isSuccessListFailescCtx ctx) && (CF.isFailListFailescCtx rs) then
        if (!Globals.is_deployed) then
          Debug.print_info "procedure call" ("\nProving precondition in method " ^ mn ^ " has failed \n") pos
        else
          Debug.print_info "procedure call" (to_print^" has failed \n") pos else () ;
      (*NORMALIZE after acquiring some new states*)
      let tmp_res = normalize_list_failesc_context_w_lemma prog rs in
      let tmp_res2 =
        if (mn_str=Globals.acquire_name) then
          (*acquire() an invariant may cause UNSAT*)
          let unsat_check_fct es =
            let new_es = {es with CF.es_unsat_flag = false} in (*trigger unsat_check*)
            elim_unsat_es 12 prog (ref 1) new_es
          in
          let tmp_res2 = CF.transform_list_failesc_context (idf,idf,unsat_check_fct) tmp_res in 
          tmp_res2
        else if (mn_str=Globals.release_name) then
          (*release: Those variables whose @full[] have been captured in the variant
            won't exist in pure constraint after release*)
          let full_vars = CF.get_varperm_formula renamed_inv VP_Full in
          let fresh_vars = CP.fresh_spec_vars full_vars in
          let fct (es:CF.entail_state) =
            let new_f = CF.subst_avoid_capture_pure full_vars fresh_vars es.CF.es_formula in
            let new_es = {es with CF.es_formula = new_f} in
            (* let _ = print_endline ("es_formula = " ^ (Cprinter.string_of_formula es.CF.es_formula)) in *)
            (* let _ = print_endline ("new_f = " ^ (Cprinter.string_of_formula new_f)) in *)
            CF.Ctx {es with CF.es_formula = new_f;}
          in
          if (full_vars!=[]) then 
            CF.transform_list_failesc_context (idf,idf,fct) tmp_res 
          else tmp_res
        else
          (*init/finalize: do nothing*)
          tmp_res
      in
      tmp_res2
  (*============================================================*)
  (*== <<< init/finalize/acquires/release[LOCK](lock,args) =====*)
  (*============================================================*)

  
(* and check_exp prog proc ctx (e0:exp) label =                          *)
(*   Gen.Profiling.do_1 "check_exp" (check_exp_d prog proc ctx e0) label *)
      
and check_exp prog proc ctx (e0:exp) label =
  let pr = Cprinter.string_of_list_failesc_context in
  Debug.no_2 "check_exp" pr (Cprinter.string_of_exp) pr (fun _ _ ->
      Gen.Profiling.push_time "check_exp_a"; 
      let res = check_exp_a prog proc ctx e0 label in
      Gen.Profiling.pop_time "check_exp_a"; res) ctx e0

and check_exp_a (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_failesc_context) (e0:exp) (post_start_label:formula_label) : CF.list_failesc_context = 
  if (exp_to_check e0) then  CF.find_false_list_failesc_ctx ctx (Cast.pos_of_exp e0)
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
          exp_assert_type = atype;
          exp_assert_pos = pos}) -> 
	          let assert_op ()=
		        let _ = if !print_proof && (match c1_o with | None -> false | Some _ -> true) then 
                  begin
                    Prooftracer.push_assert_assume e0;
                    Prooftracer.add_assert_assume e0;
                    Prooftracer.start_compound_object ();
	                Tpdispatcher.push_suppress_imply_output_state ();
	                Tpdispatcher.unsuppress_imply_output ();
                  end in
                begin
                  if !Globals.dis_ass_chk then ctx else
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
                              (* let _ = Log.update_sleek_proving_kind Log.ASSERTION in *)
                              let rs,prf = heap_entail_struc_list_failesc_context_init prog false false ts c1 None None None pos None in
                              let _ = PTracer.log_proof prf in  
                              Debug.pprint(*print_info "assert"*) ("assert condition:\n" ^ (Cprinter.string_of_struc_formula c1)) pos;
                              if CF.isSuccessListFailescCtx rs then 
			                    (Debug.print_info "assert" (s ^(if (CF.isNonFalseListFailescCtx ts) then " : ok\n" else ": unreachable\n")) pos;
			                    Debug.devel_pprint(*print_info "assert"*) ("Residual:\n" ^ (Cprinter.string_of_list_failesc_context rs)) pos)
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
                              let r =if !Globals.disable_assume_cmd_sat then assumed_ctx 
			                  else 
				                CF.transform_list_failesc_context (idf,idf,(elim_unsat_es 4 prog (ref 1))) assumed_ctx in
                              List.map CF.remove_dupl_false_fe r in
                      (ps@res)
	            end
	          in
              wrap_classic atype (wrap_proving_kind "ASSERT/ASSUME" assert_op) ()
        | Assign ({ exp_assign_lhs = v;
          exp_assign_rhs = rhs;
          exp_assign_pos = pos}) ->
              let pr = Cprinter.string_of_exp in
              let check_rhs_exp rhs = Debug.no_1 "check Assign (rhs)" pr (fun _ -> "void") 
                (fun rhs -> check_exp prog proc ctx rhs post_start_label) rhs in
              let assign_op () =
                begin
                  let _ = proving_loc#set pos in
                  let b,res = (if !Globals.ann_vp then
                    (*check for access permissions*)
                    let t = Gen.unsome (type_of_exp rhs) in
                    let var = (CP.SpecVar (t, v, Primed)) in
                    check_full_varperm prog ctx [var] pos
                  else true,ctx)
                  in
                  if (not b) then res (*do not have permission for variable v*)
                  else
                    (* let _ = Gen.Profiling.push_time "[check_rhs_exp] Assign" in *)
                    let ctx1 = check_rhs_exp rhs in
                    (* let _ = Gen.Profiling.pop_time "[check_rhs_exp] Assign" in *)
                    (* let _ = print_endline ("RHS: " ^ (Cprinter.string_of_list_failesc_context ctx1)) in *)
                    (* let _ = Gen.Profiling.push_time "[check_exp] Assign: other" in *)
                    (* let _ = print_endline ("\nAssign: ctx1:\n" ^ (Cprinter.string_of_list_failesc_context ctx1)) in *)
                    let _ = CF.must_consistent_list_failesc_context "assign 1" ctx1  in
                    let fct c1 =
                      (* let _ = Gen.Profiling.push_time "[check_exp] Assign: fct" in *)
                      let res = if (CF.subsume_flow_f !norm_flow_int (CF.flow_formula_of_formula c1.CF.es_formula)) then
                        let t = Gen.unsome (type_of_exp rhs) in
                        let vsv = CP.SpecVar (t, v, Primed) in (* rhs must be non-void *)
                        let tmp_vsv = CP.fresh_spec_var vsv in
                        let compose_es = CF.subst [(vsv, tmp_vsv); ((P.mkRes t), vsv)] c1.CF.es_formula in
                        let compose_ctx = (CF.Ctx ({c1 with CF.es_formula = compose_es})) in
                        (* print_endline ("ASSIGN CTX: " ^ (Cprinter.string_of_context compose_ctx)); *)
                        compose_ctx
                            
                      (* let link = CF.formula_of_mix_formula (MCP.mix_of_pure (CP.mkEqVar vsv (P.mkRes t) pos)) pos in *)
                      (* let ctx1 = (CF.Ctx c1) in                                                                      *)
                      (* let _ = CF.must_consistent_context "assign 1a" ctx1  in                                        *)
                      (* (* TODO : eps bug below *)                                                                     *)
                      (* let tmp_ctx1 = CF.compose_context_formula ctx1 link [vsv] false CF.Flow_combine pos in         *)
                      (* let _ = CF.must_consistent_context "assign 2" tmp_ctx1  in                                     *)
                      (* let tmp_ctx2 = CF.push_exists_context [CP.mkRes t] tmp_ctx1 in                                 *)
                      (* let _ = CF.must_consistent_context "assign 3" tmp_ctx2  in                                     *)
                      (* let resctx = if !Globals.elim_exists then elim_exists_ctx tmp_ctx2 else tmp_ctx2 in            *)
                      (* let _ = CF.must_consistent_context "assign 4" resctx  in                                       *)
                      (* resctx                                                                                         *)
                      else (CF.Ctx c1) in
                      (* let _ = Gen.Profiling.pop_time "[check_exp] Assign: fct" in *)
                      res 
                    in
                    (* let _ = Gen.Profiling.push_time "[check_exp] Assign: transform" in *)
                    let res = CF.transform_list_failesc_context (idf,idf,fct) ctx1 in
                    (* let _ = Gen.Profiling.pop_time "[check_exp] Assign: transform" in *)
                    (* let _ = Gen.Profiling.push_time "[check_exp] Assign: consistent" in *)
                    let _ = CF.must_consistent_list_failesc_context "assign final" res  in
                    (* let _ = Gen.Profiling.pop_time "[check_exp] Assign: consistent" in *)
                    (* let _ = Gen.Profiling.pop_time "[check_exp] Assign: other" in *)
                    res
                end
	          in
	          Gen.Profiling.push_time "[check_exp] Assign";  
	          let res = wrap_proving_kind "ASSIGN" assign_op () in
	          Gen.Profiling.pop_time "[check_exp] Assign";
	          res		
	    | Barrier {exp_barrier_recv = b; exp_barrier_pos = pos} ->			
	          let mkprf prf_l = PTracer.ContextList
		        {PTracer.context_list_ante = []; PTracer.context_list_conseq = CF.mkETrue (CF.mkTrueFlow ()) pos; PTracer.context_list_proofs = prf_l; } in
	          let rec process_ctx ctx = match ctx with
		        | CF.OCtx (c1, c2) ->
                      let r1, p1  = process_ctx c1 in
		              let r2, p2  = process_ctx c2 in
		              (CF.or_list_context r1 r2),(PTracer.mkOrStrucLeft ctx (CF.mkETrue (CF.mkTrueFlow ()) pos) [p1;p2])
		        | CF.Ctx c -> 
		              match CF.find_barr (List.map (fun c-> c.barrier_name) prog.prog_barrier_decls) (snd b) c.CF.es_formula with 
			            | None -> report_error pos ("context does not contain any info on barrier "^(snd b)) 
			            | Some bar_dn -> 
			                  let bn,args,branches = bar_dn.CF.h_formula_data_name,bar_dn.CF.h_formula_data_node::bar_dn.CF.h_formula_data_arguments,bar_dn.CF.h_formula_data_remaining_branches in						
			                  let bd = try List.find (fun c-> bn=c.barrier_name) prog.prog_barrier_decls with | _ -> failwith "error in barr find " in
			                  let from_v = CP.SpecVar(Named bn,self, Unprimed)::bd.barrier_shared_vars in
			                  let bd_spec = CF.subst_struc (List.combine from_v args) (CF.filter_bar_branches branches bd.barrier_def) in
			                  let helper c bd_spec = 
				                let pr1 c = Cprinter.string_of_context (CF.Ctx c) in
				                let pr2 f = Cprinter.string_of_struc_formula f in
				                Debug.no_2_loop "barrier entail" pr1 pr2 (fun c-> "") 
				                    (fun _ _ -> heap_entail_struc_init prog false true (CF.SuccCtx [CF.Ctx c]) bd_spec pos None) c bd_spec (*r,proof*) 
				                    (*try
				                      Printexc.record_backtrace true ;
				                      with e ->
				                      (print_string "gagamita\n"; let bt = Printexc.get_backtrace () in print_endline bt; raise e)*) in 
			                  helper c bd_spec in
	          
	          let barr_failesc_context (f,e,n) =  
		        let esc_skeletal = List.map (fun (l,_) -> (l,[])) e in
		        let res = List.map (fun (lbl,c2)-> 
		            let list_context_res,prf =process_ctx c2 in					
		            match list_context_res with
		              | CF.FailCtx t -> [([(lbl,t)],esc_skeletal,[])],prf
		              | CF.SuccCtx ls -> List.map ( fun c-> ([],esc_skeletal,[(lbl,c)])) ls,prf) n in
		        let res_l,prf_l =List.split res in
		        let res = List.fold_left (CF.list_failesc_context_or Cprinter.string_of_esc_stack) [(f,e,[])] res_l in
		        (res, mkprf prf_l)  in
	          
	          let barr_failesc_context (f,e,n) =
		        let pr1 (_,_,n) = pr_list (fun (_,c)-> Cprinter.string_of_context c) n in   
		        let pr2 (l,_) = String.concat "\n result: " (List.map (fun (_,_,c)-> pr_list (fun c-> Cprinter.string_of_context (snd c)) c) l) in
		        Debug.no_1_loop "barrier_failesc_context" pr1 pr2 barr_failesc_context (f,e,n) in
	          
              let to_print = ("\nVerification Context:"^(post_pos#string_of_pos)^"\nBarrier call \n") in
              Debug.devel_zprint (lazy (to_print^"\n")) pos;
	          
	          if (ctx==[]) then [] (*([],PTracer.UnsatAnte)*)
	          else 
		        let r = List.map barr_failesc_context ctx in
		        let r_ctx , prf_r = List.split r in
		        let rs = List.fold_left CF.list_failesc_context_union (List.hd r_ctx) (List.tl r_ctx) in
		        let _ = PTracer.log_proof (mkprf prf_r) in
		        if (CF.isSuccessListFailescCtx ctx) && (CF.isFailListFailescCtx rs) then Debug.print_info "barrier call" (to_print^" has failed \n") pos else () ;
		        (* normalize_list_failesc_context_w_lemma prog rs *)
                rs
		            
        | BConst ({exp_bconst_val = b;
          exp_bconst_pos = pos}) -> begin
	        Gen.Profiling.push_time "[check_exp] BConst";
	        let res_v = CP.mkRes bool_type in
	        let tmp1 = CP.BForm ((CP.BVar (res_v, pos), None), None) in
            (* TODO: Slicing - Can we mark a boolean constant as linking var                 *)
            (* let tmp1 =                                                                    *)
            (*   if !Globals.infer_lvar_slicing then                                         *)
            (*     CP.set_il_formula tmp1 (Some (false, fresh_int (), [CP.mkVar res_v pos])) *)
            (*   else tmp1                                                                   *)
            (* in                                                                            *)
	        let tmp2 =
	          if b then tmp1
	          else CP.Not (tmp1, None, pos) in
	        let f = CF.formula_of_pure_N tmp2 pos in
	        let res = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
	        Gen.Profiling.push_time "[check_exp] BConst";
	        res
	      end

        | Bind ({ exp_bind_type = body_t;
          exp_bind_bound_var = (v_t, v);
          exp_bind_fields = lvars;
          exp_bind_body = body;
          exp_bind_imm = imm;
          exp_bind_read_only = read_only;
	      exp_bind_path_id = pid;
          exp_bind_pos = pos}) -> 
              let bind_op () =
                begin
                  let b,res = (if !Globals.ann_vp then
                    (*check for access permissions*)
                    let var = (CP.SpecVar (v_t, v, Primed)) in
                    check_full_varperm prog ctx [var] pos
                  else
                    true,ctx)
                  in
                  if (not b) then res (*do not have permission for variable v*)
                  else
                    (* Debug.devel_zprint (lazy ("bind: delta at beginning of bind\n" ^ (string_of_constr delta) ^ "\n")) pos; *)
	                let _ = proving_loc#set pos in
                    let lsv = List.map (fun (t,i) -> CP.SpecVar(t,i,Unprimed)) lvars in
	                let field_types, vs = List.split lvars in
	                let v_prim = CP.SpecVar (v_t, v, Primed) in
	                let vs_prim = List.map2 (fun v -> fun t -> CP.SpecVar (t, v, Primed)) vs field_types in
	                let p = CP.fresh_spec_var v_prim in
	                let link_pv = CF.formula_of_pure_N
	                  (CP.mkAnd (CP.mkEqVar v_prim p pos) (CP.BForm ((CP.mkNeq (CP.Var (p, pos)) (CP.Null pos) pos, None), None)) pos) pos in
	                (* let _ = print_string ("[typechecker.ml, check__exp]: link_pv: " ^ Cprinter.string_of_formula link_pv ^ "\n") in*)
	                (*	  let link_pv = CF.formula_of_pure (CP.mkEqVar v_prim p pos) pos in *)
	                (* let _ = print_endline ("bind: unfolded context: after check_full_perm \n" ^ (Cprinter.string_of_list_failesc_context ctx)) in *)
	                let tmp_ctx =
	                  if !Globals.large_bind then
	                    CF.normalize_max_renaming_list_failesc_context link_pv pos false ctx
	                  else ctx in
                    (* let _ = print_endline ("WN1 ctx: "^Cprinter.string_of_list_failesc_context ctx) in *)
                    (* let _ = print_endline ("WN1 tmp_ctx: "^Cprinter.string_of_list_failesc_context tmp_ctx) in *)
                    let _ = CF.must_consistent_list_failesc_context "bind 1" ctx  in
	                (* let _ = print_endline ("bind: unfolded context: before unfold: ### vprim = "^ (Cprinter.string_of_spec_var v_prim)^ " \n" ^ (Cprinter.string_of_list_failesc_context tmp_ctx)) in *)
	                let unfolded = unfold_failesc_context (prog,None) tmp_ctx v_prim true pos in
	                (* let _ = print_endline ("bind: unfolded context: after unfold \n" ^ (Cprinter.string_of_list_failesc_context unfolded)) in *)
	                (* let unfolded_prim = if !Globals.elim_unsat then elim_unsat unfolded else unfolded in *)
                    let _ = CF.must_consistent_list_failesc_context "bind 2" unfolded  in
	                let _ = Debug.devel_zprint (lazy ("bind: unfolded context:\n" ^ (Cprinter.string_of_list_failesc_context unfolded)
                    ^ "\n")) pos in
	                (* let _ = print_string ("bind: unfolded context:\n" ^ (Cprinter.string_of_list_failesc_context unfolded) *)
                    (*     ^ "\n") in *)

	                let c = string_of_typ v_t in
                    let fresh_frac_name = Cpure.fresh_old_name "f" in
                    let perm_t = cperm_typ () in
                    let fresh_frac =  Cpure.SpecVar (perm_t,fresh_frac_name, Unprimed) in (*LDK TO CHECK*)
                    (* let perm = (if (Perm.allow_perm ()) then  *)
                    (*       (\*there exists fresh_frac statisfy ... *\) *)
                    (*       (if (read_only) then *)
                    (*             Some fresh_frac  *)
                    (*        else *)
                    (*             (\* writeable *\) *)
                    (*             None) *)
                    (*     else None) *)
                    (* in *)
	                let vdatanode = CF.DataNode ({
                        CF.h_formula_data_node = (if !Globals.large_bind then p else v_prim);
                        CF.h_formula_data_name = c;
		                CF.h_formula_data_derv = false; (*TO CHECK: assume false*)
		                CF.h_formula_data_imm = CF.ConstAnn(imm);
		                CF.h_formula_data_perm = if (Perm.allow_perm ()) then Some fresh_frac else None; (*LDK: belong to HIP, deal later ???*)
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
                        (*there exists fresh_frac statisfy ... *)
                        if (read_only)
                        then
                          let read_f = mkPermInv () fresh_frac in
                          CF.mkBase vdatanode (MCP.memoise_add_pure_N (MCP.mkMTrue pos) read_f) CF.TypeTrue (CF.mkTrueFlow ()) [] pos
                        else
                          let write_f = mkPermWrite () fresh_frac in
                          CF.mkBase vdatanode (MCP.memoise_add_pure_N (MCP.mkMTrue pos) write_f) CF.TypeTrue (CF.mkTrueFlow ()) [] pos
                      else
                        vheap
                    in

	                let vheap = prune_preds prog false vheap in
                    let struc_vheap = CF.EBase { 
	                    CF.formula_struc_explicit_inst = [];	 
                        CF.formula_struc_implicit_inst = if (Perm.allow_perm ()) then [fresh_frac] else [];  (*need to instantiate f*)
                        CF.formula_struc_exists = [];
	                    CF.formula_struc_base = vheap;
	                    CF.formula_struc_continuation = None;
	                    CF.formula_struc_pos = pos} in
	                let to_print = "Proving binding in method " ^ proc.proc_name ^ " for spec " ^ !log_spec ^ "\n" in
	                Debug.devel_pprint to_print pos;
	                if (Gen.is_empty unfolded) then unfolded
	                else
		              let _ = consume_all := true in
                      (* let _ = DD.info_pprint ("       sleek-logging (binding):" ^ (to_print)) pos in *)
                      (* let _ = Log.update_sleek_proving_kind Log.BINDING in *)
	                  let rs_prim, prf = heap_entail_struc_list_failesc_context_init prog false  true unfolded struc_vheap None None None pos pid in
		              let _ = consume_all := false in
                      let _ = CF.must_consistent_list_failesc_context "bind 3" rs_prim  in
	                  let _ = PTracer.log_proof prf in
	                  let rs = CF.clear_entailment_history_failesc_list (fun x -> None) rs_prim in
                      let _ = CF.must_consistent_list_failesc_context "bind 4" rs  in
	                  if (CF.isSuccessListFailescCtx_new unfolded) && not(CF.isSuccessListFailescCtx_new rs) then
                        begin
		                  Debug.print_info ("("^(Cprinter.string_of_label_list_failesc_context rs)^") ") 
                              ("bind: node " ^ (Cprinter.string_of_h_formula vdatanode) ^ " cannot be derived from context\n") pos; (* add branch info *)
		                  Debug.print_info ("(Cause of Bind Failure)")
                              (Cprinter.string_of_failure_list_failesc_context rs) pos;
		                  rs
                        end
                      else 
                        begin
                          stk_vars # push_list lsv;
                          let tmp_res1 = check_exp prog proc rs body post_start_label in 
                          stk_vars # pop_list lsv;
                          let _ = CF.must_consistent_list_failesc_context "bind 5" tmp_res1  in
                          let tmp_res2 = 
		                    if (imm != Lend) then 
		                      CF.normalize_max_renaming_list_failesc_context vheap pos true tmp_res1 
    			                  (* for Lend, it should not be added back *)
		                    else tmp_res1
		                  in
                          let _ = CF.must_consistent_list_failesc_context "bind 6" tmp_res2  in
                          let tmp_res3 = CF.push_exists_list_failesc_context vs_prim tmp_res2 in
                          let _ = CF.must_consistent_list_failesc_context "bind 7" tmp_res3  in
		                  let res = if !Globals.elim_exists then elim_exists_failesc_ctx_list tmp_res3 else tmp_res3 in
                          let _ = CF.must_consistent_list_failesc_context "bind 8" res  in
                          (* normalize_list_failesc_context_w_lemma prog res *)
                          res
                        end
                end  (*end Bind*)
              in
              wrap_proving_kind "BIND" bind_op ()
	              
        | Block ({exp_block_type = t;
          exp_block_body = e;
          exp_block_local_vars = local_vars;
          exp_block_pos = pos}) -> begin
            Gen.Profiling.push_time "[check_exp] Block";
            let vss = List.map (fun (t,i) -> CP.SpecVar(t,i,Unprimed)) local_vars in
            stk_vars # push_list vss;
	        let ctx1 = check_exp prog proc ctx e post_start_label in
            stk_vars # pop_list vss;
	        let svars = List.map (fun (t, n) -> CP.SpecVar (t, n, Primed)) local_vars in
	        let ctx2 = CF.push_exists_list_failesc_context svars ctx1 in
	        (* let _ = print_endline ("\ncheck_exp: Block: ctx2:\n" ^ (Cprinter.string_of_list_failesc_context ctx2)) in *)
	        (* let _ = print_endline ("\ncheck_exp: Block: after elim_exists ctx2:\n" ^ (Cprinter.string_of_list_failesc_context (elim_exists_failesc_ctx_list ctx2))) in *)
            let ctx2 = if (!Globals.allow_locklevel) then
                  trans_level_eqn_list_failesc_context ctx2
                else ctx2
            in
	        let res = if !Globals.elim_exists then elim_exists_failesc_ctx_list ctx2 else ctx2 in
            Gen.Profiling.pop_time "[check_exp] Block";
            res
	      end
	    | Catch b -> Error.report_error {Err.error_loc = b.exp_catch_pos;
          Err.error_text = "[typechecker.ml]: malformed cast, unexpected catch clause"}
        | Cond ({ exp_cond_type = t;
          exp_cond_condition = v;
          exp_cond_then_arm = e1;
          exp_cond_else_arm = e2;
          exp_cond_path_id =pid;
          exp_cond_pos = pos}) ->
              let cond_op () =
                begin
	              let _ = proving_loc#set pos in
	              let pure_cond = (CP.BForm ((CP.mkBVar v Primed pos, None), None)) in
	              let then_cond_prim = MCP.mix_of_pure pure_cond in
	              let else_cond_prim = MCP.mix_of_pure (CP.mkNot pure_cond None pos) in
	              let then_ctx = 
		            if !Globals.delay_if_sat then combine_list_failesc_context prog ctx then_cond_prim
		            else  combine_list_failesc_context_and_unsat_now prog ctx then_cond_prim in
	              Debug.devel_zprint (lazy ("conditional: then_delta:\n" ^ (Cprinter.string_of_list_failesc_context then_ctx))) pos;
	              let else_ctx =
		            if !Globals.delay_if_sat then combine_list_failesc_context prog ctx else_cond_prim
		            else  combine_list_failesc_context_and_unsat_now prog ctx else_cond_prim in
		          
	              Debug.devel_zprint (lazy ("conditional: else_delta:\n" ^ (Cprinter.string_of_list_failesc_context else_ctx))) pos;
	              let then_ctx1 = CF.add_cond_label_list_failesc_context pid 0 then_ctx in
	              let else_ctx1 = CF.add_cond_label_list_failesc_context pid 1 else_ctx in 
	              let then_ctx2 = check_exp prog proc then_ctx1 e1 post_start_label in
	              let else_ctx2 = check_exp prog proc else_ctx1 e2 post_start_label in
	              let res = CF.list_failesc_context_or (Cprinter.string_of_esc_stack) then_ctx2 else_ctx2 in
	              res
	            end in
	          Gen.Profiling.push_time "[check_exp] Cond";
              let res = wrap_proving_kind "IF" cond_op () in
	          Gen.Profiling.pop_time "[check_exp] Cond";
	          res
              ;
        | Dprint ({exp_dprint_string = str;
          exp_dprint_visible_names = visib_names;
          exp_dprint_pos = pos}) -> begin
            (* let _ = print_endline ("check_exp: Dprint: ctx :" ^ (Cprinter.string_of_list_failesc_context ctx)) in *)
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
	          Gen.Profiling.push_time "[check_exp] IConst";
	          let c_e = CP.IConst (i, pos) in
	          let res_v = CP.Var (CP.mkRes int_type, pos) in
              let c = CP.mkEqExp res_v c_e pos in
              let c = 
                if !Globals.infer_lvar_slicing then 
                  CP.set_il_formula c (Some (false, fresh_int(), [res_v]))
                else c 
              in
	          let f = CF.formula_of_mix_formula (MCP.mix_of_pure c) pos in
	          let res_ctx = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
	          Gen.Profiling.pop_time "[check_exp] IConst";
	          res_ctx
        | FConst {exp_fconst_val = f; exp_fconst_pos = pos} ->
	          let c_e = CP.FConst (f, pos) in
	          let res_v = CP.Var (CP.mkRes float_type, pos) in
              let c = CP.mkEqExp res_v c_e pos in
              let c =
                if !Globals.infer_lvar_slicing then
                  CP.set_il_formula c (Some (false, fresh_int(), [res_v]))
                else c
              in
	          let f = CF.formula_of_mix_formula (MCP.mix_of_pure c) pos in
	          let res_ctx = CF.normalize_max_renaming_list_failesc_context f pos true ctx in
	          res_ctx
        | New ({exp_new_class_name = c;
          exp_new_parent_name = pname;
          exp_new_arguments = args;
          exp_new_pos = pos}) -> begin
	        let field_types, vs = List.split args in
	        let heap_args = List.map2 (fun n -> fun t -> CP.SpecVar (t, n, Primed))
	          vs field_types in
            let res_var =  CP.SpecVar (Named c, res_name, Unprimed) in
            let new_heap_args,level_f = if (!Globals.allow_locklevel && c=lock_name) then
                  (*If this is a lock, astsimpl ensures that it has a single argument*)
                  (*Bring locklevel out to form a new expression*)
                  let arg = List.hd heap_args in
                  let arg_var = CP.Var (arg,pos) in
                  let level = CP.mkLevel res_var pos in
                  let eqn = CP.mkEqExp level arg_var pos in
                  let gt_f = CP.mkGtExp arg_var (CP.IConst (0,pos)) pos in
                  let f = CP.And (eqn,gt_f,pos) in
                  let nf = MCP.mix_of_pure f in
                  ([],nf)
                else (heap_args,MCP.mkMTrue pos)
            in
	        let heap_node = CF.DataNode ({
                CF.h_formula_data_node = CP.SpecVar (Named c, res_name, Unprimed);
                CF.h_formula_data_name = c;
		        CF.h_formula_data_derv = false;
		        CF.h_formula_data_imm = CF.ConstAnn(Mutable);
		        CF.h_formula_data_perm = None; (*None means full permission*)
			    CF.h_formula_data_origins = [];
			    CF.h_formula_data_original = true;

                CF.h_formula_data_arguments =(*type_var :: ext_var :: *) new_heap_args;
		        CF.h_formula_data_holes = []; (* An Hoa : Don't know what to do *)
                CF.h_formula_data_remaining_branches = None;
                CF.h_formula_data_pruning_conditions = [];
                CF.h_formula_data_label = None;
                CF.h_formula_data_pos = pos}) in
	        (*c let heap_form = CF.mkExists [ext_var] heap_node ext_null type_constr pos in*)
            (*If this is not a lock, level_f = true*)
	        let heap_form = CF.mkBase heap_node level_f CF.TypeTrue (CF.mkTrueFlow ()) [] pos in
            (* let _ = print_endline ("heap = " ^ (Cprinter.string_of_formula heap_form)) in *)
            let heap_form = prune_preds prog false heap_form in
	        let res = CF.normalize_max_renaming_list_failesc_context heap_form pos true ctx in
            (* let _ = print_endline ("res = " ^ (Cprinter.string_of_list_failesc_context res)) in *)
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
	          exp_scall_lock = lock;
	          exp_scall_arguments = vs;
	          exp_scall_is_rec = ir;
	          exp_scall_path_id = pid;
	          exp_scall_pos = pos}) ->
	          begin
		        Gen.Profiling.push_time "[check_exp] SCall";
                let _ = proving_loc#set pos in
                let mn_str = Cast.unmingle_name mn in
                let farg_types, farg_names = List.split proc.proc_args in
                (*=========================*)
                (*======= CONCURRENCY======*)
                (*=========================*)
                if (mn_str=Globals.fork_name) then
                  (*FORK*)
                  check_scall_fork prog ctx e0 post_start_label ret_t mn lock vs ir pid pos
                else if (mn_str=Globals.join_name) then
                  (*JOIN*)
                  check_scall_join prog ctx e0 post_start_label ret_t mn lock vs ir pid pos
                else if (mn_str=Globals.acquire_name || mn_str=Globals.release_name || mn_str=Globals.finalize_name || mn_str=Globals.init_name) then
                  (*Lock operations: init/finalize/acquire/release*)
                  check_scall_lock_op prog ctx e0 post_start_label ret_t mn lock vs ir pid pos
                (*=========================*)
                (*===<<<<= CONCURRENCY=====*)
                (*=========================*)
                else
                  (*=========================*)
                  (*=== NORMAL METHOD CALL ==*)
                  (*=========================*)
	              let proc = look_up_proc_def pos prog.new_proc_decls mn in
                  (* let _ = Debug.info_pprint ("   " ^ proc.Cast.proc_name) no_pos in *)
                  (* let _ = Debug.info_pprint ("   spec: " ^(Cprinter.string_of_struc_formula proc.Cast.proc_static_specs)) no_pos in *)
	              let farg_types, farg_names = List.split proc.proc_args in
	              let farg_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) farg_names farg_types in
	              let actual_spec_vars = List.map2 (fun n t -> CP.SpecVar (t, n, Unprimed)) vs farg_types in
                  (***************************************************************************)
                  (* let _ = print_endline (proc.proc_name ^ ": " ^ (!CF.print_struc_formula proc.proc_static_specs)) in *)
                  (* let _ = print_endline (proc.proc_name ^ ": " ^ (!CF.print_struc_formula proc.proc_stk_of_static_specs#top)) in  *)

                  (* Internal function to check pre/post condition of the function call. *)
	              let check_pre_post org_spec (sctx:CF.list_failesc_context) should_output_html : CF.list_failesc_context =
                    (* Termination: Stripping the "variance" feature from
                     * org_spec if the call is not a recursive call *)
                    (*let stripped_spec = if ir then org_spec else CF.strip_variance org_spec in*)
                    let lbl_ctx = store_label # get in
                    let org_spec2 = 
                      if ir && !auto_number then match org_spec with
                        | CF.EList b -> 
                              let l = CF.Label_Spec.filter_label_rec lbl_ctx b in
                              CF.EList l
                        | _ -> org_spec 
                      else org_spec in
                    let stripped_spec = org_spec2 in 
                    (* org_spec -> stripped_spec *)
	                (* free vars = linking vars that appear both in pre and are not formal arguments *)
                    (* Termination: The logical vars should not be renamed *)
                    let pre_free_vars = Gen.BList.difference_eq CP.eq_spec_var
                      (Gen.BList.difference_eq CP.eq_spec_var (CF.struc_fv stripped_spec(*org_spec*))
                          (CF.struc_post_fv stripped_spec(*org_spec*))) (farg_spec_vars@prog.Cast.prog_logical_vars) in
                    (* let pre_free_vars = Gen.BList.difference_eq CP.eq_spec_var *)
                    (*   pre_free_vars prog.Cast.prog_logical_vars in  *)
                    (* free vars get to be substituted by fresh vars *)
                    (* removing ranking var and unknown predicate from renaming *)
                    let pre_free_vars = List.filter (fun v -> let t = CP.type_of_spec_var v in t != RelT && t != HpT) pre_free_vars in
                  (*LOCKSET: ls is not free var*)
                  let ls_var = [(CP.mkLsVar Unprimed)] in
                  let lsmu_var = [(CP.mkLsmuVar Unprimed)] in
                  let waitlevel_var = [(CP.mkWaitlevelVar Unprimed)] in
                  let pre_free_vars = List.filter (fun v -> CP.name_of_spec_var v <> Globals.ls_name && CP.name_of_spec_var v <> Globals.lsmu_name && CP.name_of_spec_var v <> Globals.waitlevel_name) pre_free_vars in
                    (* let _ = print_endline ("WN free vars to rename : "^(Cprinter.string_of_spec_var_list pre_free_vars)) in *)
                    let pre_free_vars_fresh = CP.fresh_spec_vars pre_free_vars in
                    let renamed_spec = 
                      if !Globals.max_renaming then (CF.rename_struc_bound_vars stripped_spec(*org_spec*))
                      else (CF.rename_struc_clash_bound_vars stripped_spec(*org_spec*) (CF.formula_of_list_failesc_context sctx))
                    in
                    let st1 = List.combine pre_free_vars pre_free_vars_fresh in
                    (*let _ = print_string (List.fold_left (fun res (p1, p2) -> res ^ "(" ^ (Cprinter.string_of_spec_var p1) ^ "," ^ (Cprinter.string_of_spec_var p2) ^ ") ") "\ncheck_spec: mapping org_spec to new_spec: \n" st1) in*)
                    let fr_vars = farg_spec_vars @ (List.map CP.to_primed farg_spec_vars) in
                    let to_vars = actual_spec_vars @ (List.map CP.to_primed actual_spec_vars) in

                    (* let _ = print_string ("\ncheck_pre_post@SCall@sctx: " ^
                       (Cprinter.string_of_pos pos) ^ "\n" ^
                       (Cprinter.string_of_list_failesc_context sctx) ^ "\n\n") in*)
                    (* let _ = Debug.info_pprint ("  renamed spec 1 " ^ (Cprinter.string_of_struc_formula renamed_spec)) no_pos in *)
                    let renamed_spec = CF.subst_struc st1 renamed_spec in
                    let renamed_spec = CF.subst_struc_avoid_capture fr_vars to_vars renamed_spec in
                    (* let _ = Debug.info_pprint ("  renamed spec 2 " ^ (Cprinter.string_of_struc_formula renamed_spec)) no_pos in *)
                    (* let _ = Debug.info_pprint ("  renamed spec 3:" ^ (Cprinter.string_of_struc_formula renamed_spec)) no_pos in *)
                    let st2 = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) actual_spec_vars in
                  (*ALSO rename ls to ls',lsmu to lsmu'*)
                  let st_ls = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) ls_var in
                  let st_lsmu = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) lsmu_var in
                  let st_waitlevel = List.map (fun v -> (CP.to_unprimed v, CP.to_primed v)) waitlevel_var in
                  let st3= st2@st_ls@st_lsmu@st_waitlevel in
                  let pre2 = CF.subst_struc_pre st3 renamed_spec in
                    let new_spec = (Cprinter.string_of_struc_formula pre2) in
                    (* Termination: Store unreachable state *)
                    let _ = 
                      if ir then (* Only check termination of a recursive call *)
                        let _ = DD.devel_zprint 
                          (lazy (">>>>>>> Termination Checking: " ^ mn ^ " <<<<<<<")) pos in
                        (* Normalise the specification with variance                     let f = wrap_proving_kind "PRE-2" (check_pre_post org_spec sctx) in

                           * to further inference or error reporting *)
                        if not (CF.isNonFalseListFailescCtx sctx) then
                          let _ = Term.add_unreachable_res sctx pos in ()
                        else ()
                      else ()
                    in

                    (* TODO: call the entailment checking function in solver.ml *)
                    let to_print = "\nProving precondition in method " ^ proc.proc_name ^ " for spec:\n" ^ new_spec (*!log_spec*) in
                    let to_print = ("\nVerification Context:"^(post_pos#string_of_pos)^to_print) in
                    Debug.devel_zprint (lazy (to_print^"\n")) pos;
		            (* An Hoa : output the context and new spec before checking pre-condition *)
		            let _ = if !print_proof && should_output_html then Prooftracer.push_list_failesc_context_struct_entailment sctx pre2 in
                    (* let _ = print_endline ("\nlocle: check_pre_post@SCall@sctx: " ^ *)
                    (*                              (Cprinter.string_of_list_failesc_context sctx)) in *)
                    (*we use new rules to judge the spec*)
                    let rs, prf = heap_entail_struc_list_failesc_context_init prog false true sctx pre2 None None None pos pid in
                    
		            let _ = if !print_proof && should_output_html then Prooftracer.pop_div () in
                    (* The context returned by heap_entail_struc_list_failesc_context_init, rs, is the context with unbound existential variables initialized & matched. *)
                    let _ = PTracer.log_proof prf in

                    (*let _ = print_string (("\nEND SCALL ctx: ") ^ (Cprinter.string_of_list_failesc_context rs) ^ "\n") in*)
                    (* if (CF.isSuccessListFailescCtx sctx) && (CF.isFailListFailescCtx rs) then
                       Debug.print_info "procedure call" (to_print^" has failed \n") pos else () ; *)
                    rs
                  in
                  (*******************************END_CHECK_PRE_POST****************************************)
                  (* Call check_pre_post with debug information *)
                  (***************************************************************************)
                  let check_pre_post org_spec (sctx:CF.list_failesc_context) should_output_html : CF.list_failesc_context =
                    (* let _ = Cprinter.string_of_list_failesc_context in *)
                    let pr2 = Cprinter.string_of_list_failesc_context in
                    let pr3 = Cprinter.string_of_struc_formula in
                    (* let _ = Log.update_sleek_proving_kind Log.PRE in *)
                    let f = wrap_proving_kind "PRE-2" (check_pre_post org_spec sctx) in
                    Debug.no_2_loop "check_pre_post" pr3 pr2 pr2 (fun _ _ ->  f should_output_html) org_spec sctx in
		          
		          let check_pre_post org_spec (sctx:CF.list_failesc_context) should_output_html : CF.list_failesc_context =
		            Gen.Profiling.do_1 "check_pre_post" (check_pre_post org_spec sctx) should_output_html
		          in
		          let _ = if !print_proof then Prooftracer.start_compound_object () in
                  let scall_pre_cond_pushed = if !print_proof then
                    begin
                      Tpdispatcher.push_suppress_imply_output_state ();
                      Tpdispatcher.unsuppress_imply_output ();
            	      Prooftracer.push_pre e0;
                      (* print_endline ("CHECKING PRE-CONDITION OF FUNCTION CALL " ^ (Cprinter.string_of_exp e0)) *)
                    end else false in

                  let res = if (CF.isFailListFailescCtx_new ctx) then
		            let _ = if !print_proof && scall_pre_cond_pushed then Prooftracer.append_html "Program state is unreachable." in
                    (*  let _ = print_endline "locle7" in*)
                    ctx
                  else
                    (*  let _ = print_endline "locle8" in *)
                    (*let p = CF.pos_of_struc_formula  proc.proc_static_specs_with_pre in*)
                    let pre_with_new_pos = CF.subst_pos_struc_formula pos (proc.proc_stk_of_static_specs#top) in                      
                    check_pre_post pre_with_new_pos ctx scall_pre_cond_pushed
                  in
		          let _ = if !print_proof then Prooftracer.add_pre e0 in
                  let _ = if !print_proof && scall_pre_cond_pushed then 
                    begin
                      Prooftracer.pop_div ();
                      Tpdispatcher.restore_suppress_imply_output_state ();
                      (* print_endline "OK.\n" *)
                    end in
                  (* let _ = Debug.info_pprint  (("\ncheck_exp: SCall: res : ") ^ (Cprinter.string_of_list_failesc_context res)) no_pos in *)
		          Gen.Profiling.pop_time "[check_exp] SCall";
                  (* let _ = print_endline (("\ncheck_exp: SCall: res : ") ^ (Cprinter.string_of_list_failesc_context res)) in *)
                  if (CF.isSuccessListFailescCtx_new res) then
                    (* let _ = print_endline ("\nlocle1:" ^ proc.proc_name) in*)
                    let _ = Debug.ninfo_pprint ("   We may need to transfer hpdef of callee into caller here. and remove all callee' hprel assumptions") no_pos in
                    res
                  else begin
                    (*   let _ = print_endline ("\nlocle2:" ^ proc.proc_name) in *)
                    (* get source code position of failed branches *)
                    (if (!Globals.is_deployed) then
                          let _ = Debug.print_info "procedure call" ("\nProving precondition in method " ^ mn ^ " has failed \n") pos in
                          res
                     else
                    (*FAILURE explaining*)
                    let to_print = "\nProving precondition in method " ^ proc.proc_name ^ " Failed.\n" in
                    let _ =
                      if not !Globals.disable_failure_explaining then
                        let s,fk= CF.get_failure_list_failesc_context res
                          (*match CF.get_must_failure_list_partial_context rs with
                            | Some s -> "(must) cause:\n"^s
                            | None -> (match CF.get_may_failure_list_partial_context rs with
                            | Some s -> "(may) cause:\n"^s
                            | None -> "INCONSISTENCY : expected failure but success instead"
                            ) *)
                          (*should check bot with is_bot_status*)
                        in
                        if (String.length s) >  0 then
                          (* let _ = print_string (to_print ^s^"\n") in *)
                          (* Err.report_error { *)
                          (*       Err.error_loc = pos; *)
                          (*       Err.error_text = Printf.sprintf *)
                          (*           "Proving precondition in method failed." *)
                          (*   } *)
                          raise (Err.Ppf ({
                              Err.error_loc = pos;
                              Err.error_text = (to_print ^s)
                          }, match fk with
                            | CF.Failure_Bot _ -> 0
                            | CF.Failure_Must _ -> 1
                            | CF.Failure_Valid -> 2
                            | CF.Failure_May _ -> 3))
                        else ()
                      else
                        begin
                          Debug.print_info ("("^(Cprinter.string_of_label_list_failesc_context res)^") ") 
                              ("Proving precondition in method failed\n") pos;
	                      Debug.print_info ("(Cause of PreCond Failure)")
                              (Cprinter.string_of_failure_list_failesc_context res) pos;
                          Err.report_error {
                              Err.error_loc = pos;
                              Err.error_text = Printf.sprintf
                                  "Proving precondition in method failed."
                          }
                        end
                    in
                    res)
                  end
              end
        | Seq ({exp_seq_type = te2;
          exp_seq_exp1 = e1;
          exp_seq_exp2 = e2;
          exp_seq_pos = pos}) -> begin
	        let ctx1 = check_exp prog proc ctx e1 post_start_label (*flow_store*) in 
            (* Astsimp ensures that e1 is of type void *)
            (* let _ = print_endline ("WN C1:"^(Cprinter.string_of_list_failesc_context ctx1)) in*)
	        let ctx2= check_exp prog proc ctx1 e2 post_start_label (*flow_store*) in
            (* let _ = print_endline ("WN C2:"^(Cprinter.string_of_list_failesc_context ctx2)) in*)	
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
		        Gen.Profiling.push_time "[check_exp] Var";
                let b,res = (if !Globals.ann_vp then
                  let var = (CP.SpecVar (t, v, Primed)) in
                  check_full_varperm prog ctx [var] pos
                else
                  true,ctx)
                in
                let res = if (not b) then res (*do not have permission for variable v*)
                else
                  let tmp = CF.formula_of_mix_formula  (MCP.mix_of_pure (CP.mkEqVar (CP.mkRes t) (CP.SpecVar (t, v, Primed)) pos)) pos in
                  CF.normalize_max_renaming_list_failesc_context tmp pos true ctx
		        in
		        Gen.Profiling.pop_time "[check_exp] Var";
		        res 
              end
        | VarDecl _ -> ctx (* nothing to do *)
        | Unit pos -> ctx
        | Sharp ({exp_sharp_type =t;
          exp_sharp_flow_type = ft;(*P.flow_typ*)
          exp_sharp_val = v; (*maybe none*)
          exp_sharp_unpack = un;(*true if it must get the new flow from the second element of the current flow pair*)
          exp_sharp_path_id = pid;
          exp_sharp_pos = pos})	-> 
	        (*   let _ =print_string ("sharp start ctx: "^ (Cprinter.string_of_list_failesc_context ctx)^"\n") in *)
	        (*   let _ = print_string ("raising: "^(Cprinter.string_of_exp e0)^"\n") in *)
	        (*   let _ = print_string ("sharp flow type: "^(Cprinter.string_of_sharp_flow ft)^"\n") in *)
            (* let _ = print_endline ("flow_store = " ^ (Cprinter.string_of_flow_store !flow_store)) in *)
	          let nctx = match v with 
	            | Sharp_var (t,v) ->
                      let b,res = (if !Globals.ann_vp then
                        (*check for access permissions*)
                        let var = (CP.SpecVar (t, v, Primed)) in
                        check_full_varperm prog ctx [var] pos
                      else
                        true,ctx)
                      in
                      if (not b) then res (*do not have permission for variable v*)
                      else
                        let t1 = (get_sharp_flow ft) in
                        (* let _ = print_endline ("Sharp Flow:"^(string_of_flow t1) ^" Exc:"^(string_of_flow !raisable_flow_int)) in *)
                        let vr = if is_subset_flow t1 !raisable_flow_int || is_subset_flow t1 !loop_ret_flow_int then (CP.mkeRes t)
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
              (* let _ = print_endline ("WN:ESCAPE ctx3 :"^(Cprinter.string_of_list_failesc_context ctx3)) in *)
              (*Decide which to escape, and which to be caught.
              Caught exceptions become normal flows*)
              let ctx4 = CF.splitter_failesc_context (cc.exp_catch_flow_type) (cc.exp_catch_var) 
                (fun c -> CF.add_path_id c (Some pid,0)) elim_exists_ctx ctx3 in
              (* let _ = print_endline ("WN:ESCAPE ctx4:"^(Cprinter.string_of_list_failesc_context ctx4)) in *)
              let ctx5 = check_exp prog proc ctx4 cc.exp_catch_body post_start_label in
              CF.pop_esc_level_list ctx5 pid
	    | _ -> 
	          failwith ((Cprinter.string_of_exp e0) ^ " is not supported yet")  in
    let check_exp1 (ctx : CF.list_failesc_context) : CF.list_failesc_context =
      let pr = Cprinter.string_of_list_failesc_context in
      Debug.no_1 "check_exp1" pr pr check_exp1 ctx in
    let check_exp1 (ctx : CF.list_failesc_context) : CF.list_failesc_context =
      Gen.Profiling.do_1 "check_exp1" check_exp1 ctx in

    let ctx = if (not !Globals.failure_analysis) then List.filter (fun (f,s,c)-> Gen.is_empty f ) ctx  
    else ctx in
    (* An Hoa : Simplify the context before checking *)
    let ctx = if (!simplify_context) then
      CF.simplify_list_failesc_context ctx proc.Cast.proc_important_vars
    else ctx in
    let (fl,cl) = List.partition (fun (_,s,c)-> Gen.is_empty c && CF.is_empty_esc_stack s) ctx in
    (* let _ = print_endline ("WN:ESCAPE:"^(Cprinter.string_of_list_failesc_context fl)) in *)
    (* let _ = print_endline ("WN:CURRENT:"^(Cprinter.string_of_list_failesc_context cl)) in *)
    (* if (Gen.is_empty cl) then fl
       else *)
    let failesc = CF.splitter_failesc_context !norm_flow_int None (fun x->x)(fun x -> x) cl in
    ((check_exp1 failesc) @ fl)		
	    
and check_post (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_partial_context) (post : CF.formula) pos (pid:formula_label) (etype: ensures_type) : CF.list_partial_context  =
  let pr = Cprinter.string_of_list_partial_context in
  let pr1 = Cprinter.string_of_formula in
  (*  let pr2 = Cprinter.string_of_list_partial_context in*)
  (* let _ = Debug.info_pprint "CG dont trust 0" pos; flush(stdout) in *)
  (* let _ = Log.update_sleek_proving_kind Log.POST in *)
  (* let _ = Debug.info_pprint "CG dont trust" pos; flush(stdout) in *)
  let f = wrap_proving_kind "POST" (check_post_x prog proc ctx post pos pid) in
  Debug.no_2_loop "check_post" pr pr1 pr (fun _ _ -> f etype) ctx post

and check_post_x (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_partial_context) (post : CF.formula) pos (pid:formula_label) (etype: ensures_type) : CF.list_partial_context  =
  wrap_classic etype (check_post_x_x prog proc ctx post pos) pid


      
      
and pr_spec = Cprinter.string_of_struc_formula

and pr_spec2 = Cprinter.string_of_struc_formula_for_spec

and check_post_x_x (prog : prog_decl) (proc : proc_decl) (ctx : CF.list_partial_context) (post : CF.formula) pos (pid:formula_label): CF.list_partial_context  =
  (* let _ = print_string ("got into check_post on the succCtx branch\n") in *)
  (* let _ = print_string ("context before post: "^(Cprinter.string_of_list_partial_context ctx)^"\n") in *)
  (* let _= print_endline ("Check post list ctx: "^Cprinter.string_of_list_partial_context ctx) in *)
  if !Globals.dis_post_chk then ctx else 
    let _ = if !print_proof then
      begin
	    Prooftracer.push_post ();
        Prooftracer.start_compound_object ();
	    Prooftracer.push_list_partial_context_formula_entailment ctx post;
	    Tpdispatcher.push_suppress_imply_output_state ();
	    Tpdispatcher.unsuppress_imply_output ();
	    (* print_endline "VERIFYING POST-CONDITION" *)
      end in
    (* Termination: Poststate of Loop must be unreachable (soundness) *)
    let _ = if !Globals.dis_term_chk || !Globals.dis_post_chk then true 
    else Term.check_loop_safety prog proc ctx post pos pid in
    let ctx = if (!Globals.allow_locklevel) then
          (*to maintain the information of locklevels on varables
            whose scopes are within scope of this procedure only.
            For example, for any pass-by-value or local variables,
            at the end of the procedure, it will become existential
            variables. Exist vars, however, will be renamed sometimes.
            However, elim_exists is not aware of constraints on locklevels,
            we have to maintain these constraints by translating before
            elim_exists
          *)
          trans_level_list_partial_context ctx
        else ctx
    in
    let fn_state=
      if (!Globals.disable_failure_explaining) then
        let vsvars = List.map (fun p -> CP.SpecVar (fst p, snd p, Unprimed))
          proc.proc_args in
        let r = proc.proc_by_name_params in
        let w = List.map CP.to_primed (Gen.BList.difference_eq CP.eq_spec_var vsvars r) in

        (* print_string ("\nLength of List Partial Ctx: " ^ (Cprinter.summary_list_partial_context(ctx)));  *)
        let final_state_prim = CF.push_exists_list_partial_context w ctx in
        (* print_string ("\nLength of List Partial Ctx: " ^ (Cprinter.summary_list_partial_context(final_state_prim)));  *)
        (* let _ = print_flush ("length:"^(string_of_int (List.length final_state_prim))) in *)
        (* let _ = print_endline ("Final state prim :\n" ^ (Cprinter.string_of_list_partial_context final_state_prim)) in *)
        let final_state = 
          if !Globals.elim_exists then (elim_exists_partial_ctx_list final_state_prim) else final_state_prim in
        (* let _ = print_endline ("Final state :\n" ^ (Cprinter.string_of_list_partial_context final_state)) in *)
        (* Debug.devel_print ("Final state:\n" ^ (Cprinter.string_of_list_partial_context final_state_prim) ^ "\n"); *)
        (*  Debug.devel_print ("Final state after existential quantifier elimination:\n" *)
        (* ^ (Cprinter.string_of_list_partial_context final_state) ^ "\n"); *)
        Debug.devel_zprint (lazy ("Post-cond:\n" ^ (Cprinter.string_of_formula  post) ^ "\n")) pos;
        let to_print = "Proving postcondition in method " ^ proc.proc_name ^ " for spec\n" ^ !log_spec ^ "\n" in
        Debug.devel_pprint to_print pos;
        final_state
      else ctx
    in
    (* let _ = DD.ninfo_pprint ("       sleek-logging (POST): "  ^ "\n" ^ (to_print)) pos in *)
    let f1 = CF.formula_is_eq_flow post !error_flow_int in
    (* let f2 = CF.list_context_is_eq_flow cl !norm_flow_int in *)
     (* let _ = print_string ("\n WN 4 : "^(Cprinter.string_of_list_partial_context (\*ctx*\) fn_state)) in *)
    let rs, prf =
      if f1 then
        begin
          let post = (CF.formula_subst_flow post (CF.mkNormalFlow())) in
           let (ans,prf) = heap_entail_list_partial_context_init prog false fn_state post None None None pos (Some pid) in
          (CF.invert_list_partial_context_outcome CF.invert_ctx_branch_must_fail CF.invert_fail_branch_must_fail ans,prf)
        end
      else
      heap_entail_list_partial_context_init prog false fn_state post None None None pos (Some pid)
    in
    let _ = PTracer.log_proof prf in
    let _ = if !print_proof then
      begin
	    Tpdispatcher.restore_suppress_imply_output_state ();
	    Prooftracer.add_post ();
        Prooftracer.pop_div ();
        Prooftracer.pop_div ();
	    (* print_endline "DONE!" *)
      end in
    if (CF.isSuccessListPartialCtx_new rs) then
      rs
    else begin
      (* get source code position of failed branches *)
      (*let locs_of_failures = 
        List.fold_left (fun res ctx -> res @ (locs_of_partial_context ctx)) [] rs 
        in*)
      (*let string_of_loc_list locs =
        List.fold_left (fun res l -> res ^ (string_of_loc_by_char_num l) ^ ",") "" locs
        in*)
      let _ =
        if not !Globals.disable_failure_explaining then
          let s,fk= CF.get_failure_list_partial_context rs
            (*match CF.get_must_failure_list_partial_context rs with
              | Some s -> "(must) cause:\n"^s
              | None -> (match CF.get_may_failure_list_partial_context rs with
              | Some s -> "(may) cause:\n"^s
              | None -> "INCONSISTENCY : expected failure but success instead"
              ) *)
            (*should check bot with is_bot_status*)
          in
          let _ = print_string ("\nPost condition cannot be derived:\n" ^s^"\n") in
          Err.report_error {
              Err.error_loc = pos;
              Err.error_text = ("Post condition cannot be derived.")
          }
        else
          begin
            Debug.print_info ("("^(Cprinter.string_of_label_list_partial_context rs)^") ")
                ("Postcondition cannot be derived from context\n") pos;
	        Debug.print_info ("(Cause of PostCond Failure)")
                (Cprinter.string_of_failure_list_partial_context rs) pos;
            Err.report_error {
                Err.error_loc = pos;
                Err.error_text = Printf.sprintf
		            (*         "Post condition %s cannot be derived by the system.\n By: %s \n fail ctx: %s\nPossible locations of failures: %s." *)
                    "Post condition cannot be derived by the system."
                    (* (Cprinter.string_of_formula post)
                       (Cprinter.string_of_list_partial_context final_state)
                       (Cprinter.string_of_list_partial_context rs)
                       (string_of_loc_list locs_of_failures)*)
            }
          end
      in
      rs
    end
      (* process each scc set of mutual-rec procedures *)
      (* to be used for inferring phase constraints *)
      (* replacing each spec with new spec with phase numbering *)
and proc_mutual_scc (prog: prog_decl) (proc_lst : proc_decl list) (fn:prog_decl -> proc_decl -> unit) =
  let rec helper lst = 
    match lst with
      | [] -> ()
      | p::ps -> (fn prog p); helper ps 
  in helper proc_lst

(* checking procedure: (PROC p61) *)
and check_proc (prog : prog_decl) (proc : proc_decl) cout_option (mutual_grp : proc_decl list) : bool =
  let unmin_name = unmingle_name proc.proc_name in
  (* get latest procedure from table *)
  let proc = 
    find_proc prog proc.proc_name
  in
  let check_flag = ((Gen.is_empty !procs_verified) || List.mem unmin_name !procs_verified)
    && not (List.mem unmin_name !Inliner.inlined_procs)
  in
  if check_flag then 
    begin
      match proc.proc_body with
	    | None -> true (* sanity checks have been done by the translation *)
	    | Some body ->
	          begin
                stk_vars # reset;
                (* push proc.proc_args *)
                let args = List.map (fun (t,i) -> CP.SpecVar(t,i,Unprimed) ) proc.proc_args in
                stk_vars # push_list args;
                let pr_flag = not(!phase_infer_ind) in
		        if !Globals.print_proc && pr_flag then 
		          print_string ("Procedure " ^ proc.proc_name ^ ":\n" ^ (Cprinter.string_of_proc_decl 3 proc) ^ "\n\n");
		        if pr_flag then
                  begin
                    print_string (("\nChecking procedure ") ^ proc.proc_name ^ "... "); flush stdout;
		            Debug.devel_zprint (lazy (("Checking procedure ") ^ proc.proc_name ^ "... ")) proc.proc_loc;
		            Debug.devel_zprint (lazy ("Specs :\n" ^ Cprinter.string_of_struc_formula proc.proc_static_specs)) proc.proc_loc;
                  end;
                (*****LOCKSET variable: ls'=ls *********)
                let args = 
                  if (!allow_ls) then
                    let lsmu_var = (lsmu_typ,lsmu_name) in
                    let ls_var = (ls_typ,ls_name) in
                    if (!Globals.allow_locklevel) then
                      (*LS and LSMU are ghost variables*)
                      lsmu_var::ls_var::proc.proc_args
                    else
                      ls_var::proc.proc_args
                  else
                    proc.proc_args
                in
                (******************************)
			    let ftypes, fnames = List.split args in
		        (* fsvars are the spec vars corresponding to the parameters *)
		        let fsvars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in
                let pf = (CF.no_change fsvars proc.proc_loc) in (*init(V) := v'=v*)
                (* let pf = if (!Globals.allow_locklevel) then  *)
                (*       CP.translate_level_eqn_pure pf (\*l'=l ==> level(l')=level(l)*\) *)
                (*     else pf *)
                (* in *)
			    let nox = CF.formula_of_pure_N  pf proc.proc_loc in 
		        let init_form = nox in
		        let init_ctx1 = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled  proc.proc_loc in
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
                (* Termination: Add the set of logical variables into the initial context *)
                let init_ctx = 
                  if !Globals.dis_term_chk then init_ctx
                  else Inf.restore_infer_vars_ctx proc.proc_logical_vars [] init_ctx in
                let _ = Debug.trace_hprint (add_str "Init Ctx" !CF.print_context) init_ctx no_pos in
		        let _ = if !print_proof then begin 
		          Prooftracer.push_proc proc;
		          Prooftracer.start_compound_object ();
		        end
		        in
		        let pp, exc = 
                  try (* catch exception to close the section appropriately *)
                    (* let f = check_specs prog proc init_ctx (proc.proc_static_specs (\* @ proc.proc_dynamic_specs *\)) body in *)
		            let old_hpdecls = prog.prog_hp_decls in
                    let (new_spec,fm,rels,hprels,sel_hp_rels,sel_post_hp_rels,hp_rel_unkmap,f) = check_specs_infer prog proc init_ctx (proc.proc_static_specs (* @ proc.proc_dynamic_specs *)) body true in
                    Debug.trace_hprint (add_str "SPECS (after specs_infer)" pr_spec) new_spec no_pos;
                    Debug.trace_hprint (add_str "fm formula " (pr_list !CF.print_formula)) fm no_pos;
                    let new_spec = CF.simplify_ann new_spec in
		            
                    let (rels,rest) = (List.partition (fun (a1,a2,a3) -> match a1 with | CP.RelDefn _ -> true | _ -> false) rels) in
                    
                    let (lst_assume,lst_rank) = (List.partition (fun (a1,a2,a3) -> match a1 with | CP.RelAssume _ -> true | _ -> false) rest) in
                    let (hprels,hp_rest) = (List.partition (fun hp -> match hp.CF.hprel_kind with | CP.RelDefn _ -> true | _ -> false) hprels) in
                    
                    let (hp_lst_assume,hp_rest) = (List.partition (fun hp -> match hp.CF.hprel_kind with | CP.RelAssume _ -> true | _ -> false) hp_rest) in
                    (*let lst_assume = List.map (fun (_,a2,a3)-> (a2,a3)) lst_assume in*)
                    let rels = List.map (fun (_,a2,a3)-> (a2,a3)) rels in
                    (* let hprels = List.map (fun (_,a2,a3)-> (a2,a3)) hprels in *)
                    (* let hp_lst_assume = List.map (fun (_,a2,a3)-> (a2,a3)) hp_lst_assume in *)
		            (* let hp_lst_simplified_assume = Sa2.simplify_lst_constrs hp_lst_assume in *)
                    if not(Infer.infer_rel_stk# is_empty) then
                      begin
                        print_endline "\n*************************************";
                        print_endline "*******pure relation assumption ******";
                        print_endline "*************************************";
                        print_endline (Infer.infer_rel_stk # string_of_reverse);
                        print_endline "*************************************";
(*                        Infer.infer_rel_stk # reset;*)
                      end;                    
                    if not(Infer.rel_ass_stk# is_empty) then
                      begin
                        print_endline ""; 
                        print_endline "*************************************";
                        print_endline "*******relational assumption ********";
                        print_endline "*************************************";
                        print_endline (Infer.rel_ass_stk # string_of_reverse);
                        print_endline "*************************************" 
                      end;
		            let ls_hprel, ls_inferred_hps, dropped_hps =
                      if !Globals.sa_en_norm then Sa.infer_hps prog hp_lst_assume
                        sel_hp_rels sel_post_hp_rels (Gen.BList.remove_dups_eq
                            (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) hp_rel_unkmap)
                      else [],[],[]
                    in
                    if not(Sa.rel_def_stk# is_empty) then
                      begin
		                print_endline ""; 
		                print_endline "*************************************";
		                print_endline "*******relational definition ********";
		                print_endline "*************************************";
                        print_endline (Sa.rel_def_stk # string_of_reverse);
		                print_endline "*************************************"
                      end;
		            (*****************************support function**************************)
		            let print_res_list rl def=
		              let pr1 =  pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula in
		              (* let pr_mix_mtl =   pr_list_ln (pr_triple CEQ.string_of_map_table pr1 pr1) in *)
		              let pr_res (c1,c2,mtb) = 
			            if(List.length mtb == 0) then  "no-diff-info"
			            else (
			                let (_,d1,d2) = List.hd mtb in
			                if(def) then "Infer def: " ^ pr1 c1 ^ "\nExpected def: " ^ pr1 c2 ^ "\nDiff1: " ^ pr1 d1 ^ "\nDiff2: " ^ pr1 d2 
			                else "Infer constr: " ^ pr1 c1 ^ "\nExpected constr: " ^ pr1 c2 ^ "\nDiff1: " ^ pr1 d1 ^ "\nDiff2: " ^ pr1 d2 
			            )
		              in
		              List.fold_left (fun piv sr -> piv  ^ sr ^ "\n" ) "" (List.map (fun r -> (pr_res) r) rl)
		            in
		            let string_of_hp_decls hpdecls = 
		              (
			              let string_of_hp_decl hpdecl =
			                (
			                    let name = hpdecl.hp_name in
			                    let pr_arg arg = 
			                      let t = CP.type_of_spec_var arg in 
				                  let arg_name = Cprinter.string_of_spec_var arg in
				                  let arg_name = if(String.compare arg_name "res" == 0) then fresh_name () else arg_name in
			                      (CP.name_of_type t) ^ " " ^ arg_name
			                    in
			                    let args = pr_lst ", " pr_arg hpdecl.hp_vars in
			                    "HeapPred "^ name ^ "(" ^ args ^ ").\n"
			                )
			              in
			              List.fold_left (fun piv e -> piv ^ string_of_hp_decl e) "" hpdecls 
		              )
		            in
		            let save_names = List.map (fun hp-> hp.Cast.hp_name) old_hpdecls in
		            let get_new_var var vnames =
		              (*Notice: (TODO) assume that var are form x_x -> it means new var x1 can not be supl with some x1 :D*)
		              let check_dupl n = List.exists (fun sn -> String.compare sn n == 0) save_names in
		              let name = CP.full_name_of_spec_var var in
		              let (typ,raw_name,p) = match var with
			            | CP.SpecVar s -> s
		              in
		              let mkname name i = 
			            if(i < 0) then name else ( name ^ (string_of_int i)) 
		              in
		              let new_var,new_vnames = 
			            let rec add name root_var vnames =
			              match vnames with
			                | [] -> 
			                      let new_name =   match root_var with
				                    | CP.SpecVar (typ,root_name,p) -> root_name
			                      in  
			                      if(check_dupl new_name) then (
				                      add name root_var [(root_var, [("", -1)] )]
			                      ) else (root_var,[(root_var, [(name, -1)] )])
			                | (vn,m)::y -> (
			                      if(CP.eq_spec_var vn root_var ) then (
				                      try (
				                          let _, indx = List.find (fun (v,i) -> String.compare v name == 0) m in
				                          let new_name,p =   match root_var with
				                            | CP.SpecVar (typ,root_name,p) ->  mkname root_name indx,p
				                          in  
				                          let n_var =  CP.SpecVar (typ,new_name,p) in
				                          (n_var , vnames)
				                      )
				                      with _ -> (
				                          let (x,indx) = List.hd m in 
				                          let indx = indx + 1 in
				                          let new_name,p =   match root_var with
				                            | CP.SpecVar (typ,root_name,p) ->  mkname root_name indx,p
				                          in  
				                          if(check_dupl new_name) then (
				                              add name root_var ((vn,("",indx)::m)::y)
				                          )
				                          else (
				                              let n_var =  CP.SpecVar (typ,new_name,p) in
				                              (n_var, (vn,(name,indx)::m)::y)
				                          )
				                      )
			                      )
			                      else (
				                      let (n,vns) = add name root_var y in
				                      (n,(vn,m)::vns)
			                      )
			                  )
			            in
			            let root_var  = try (
			                let i = String.index name '_' in (*make root var is all a-z -> no worry for x1 case above*)
			                let n = String.sub name 0 i in 
			                CP.SpecVar (typ, n, Unprimed) 
			            ) with _ -> let n = if p = Unprimed then name else raw_name in
			            CP.SpecVar (typ, n, Unprimed) 
			            in
			            add name root_var vnames 
		              in
		              (new_var, new_vnames)
		            in 
		            let simplify_varname  sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls name_mtb =
		              (* print_string " simplify_varname\n"; *)
		              let  hp_lst_assume = List.map (fun hp -> (hp.CF.hprel_lhs,hp.CF.hprel_rhs)) hp_lst_assume in
		              let change_hp f = CF.subst name_mtb f in
		              let ls_inferred_hps =   List.map (fun (_,hf,f2) -> (change_hp (CF.formula_of_heap hf no_pos), change_hp f2))  ls_inferred_hps  in
		              let sim_each_ass (f1,f2) mtb vnames =
			            let all_vars = CP.remove_dups_svl (CF.fv f1 @ CF.fv f2) in
			            let all_vars = List.filter (fun v-> not(List.exists (fun sv -> CP.eq_spec_var sv v) sel_hp_rels)) all_vars in			
			            let (new_mtb,vns) = List.fold_left (fun (curr_mtb,curr_vnames) var -> 
			                let (new_var,new_vnames) = get_new_var var curr_vnames in
			                ((var,new_var)::curr_mtb, new_vnames) ) ([],vnames) all_vars 
			            in
			            let rename_hp f = CF.subst new_mtb f in
			            let filter_hp vnames = List.filter (fun (v,_) -> CP.is_hprel_typ v) vnames in
			            let filter_mtb mtb = List.filter (fun (v,_) -> CP.is_hprel_typ v) mtb in
			            ((rename_hp f1,rename_hp f2),(filter_mtb new_mtb)@mtb,filter_hp vns)
		              in 
		              let rename_all hpdecls hp_mtb = 
			            let rename_one hpdecl hp_mtb = 
			              let name = hpdecl.Cast.hp_name in
			              let vars = hpdecl.Cast.hp_vars in
			              try (
			                  let (a, b) = List.find (fun (a,_) -> String.compare (CP.full_name_of_spec_var a) name == 0) hp_mtb in
			                  let new_name = CP.full_name_of_spec_var b in
			                  let (_,new_vars) = List.fold_left (fun piv v -> 
				                  let (index,vs) = piv in
				                  let (typ,raw_name,p) = match v with
				                    | CP.SpecVar s -> s
				                  in
				                  let new_name = "v" ^ (string_of_int index) in
				                  let new_sv = CP.SpecVar (typ,new_name,p) in
				                  (index+1,new_sv::vs)
			                  ) (0,[]) vars in
			                  [({hpdecl with Cast.hp_name = new_name;
				                  Cast.hp_vars = new_vars})]
			              )
			              with 
			                | Not_found -> []
			            in
			            List.concat (List.map (fun h -> rename_one h hp_mtb) hpdecls)
		              in
		              
		              let (hp_lst_assume, mtb,vnames) = List.fold_left (fun piv ass -> let (r,m,vn) = piv in
		              let (rh,mh,vn1) = sim_each_ass ass m vn in
		              (rh::r,mh,vn1)
		              ) ([],[],[]) hp_lst_assume in
		              let (ls_inferred_hps, mtb2,vnames2) = List.fold_left (fun piv hp -> let (r,m,vn) = piv in
		              let (rh,mh,vn1) = sim_each_ass hp m vn in
		              (rh::r,mh,vn1)
		              ) ([],mtb,vnames) ls_inferred_hps in
		              let hp_mtb = mtb2 in
		              let hpdecls = rename_all hpdecls hp_mtb in 
		              (hpdecls,hp_lst_assume,ls_inferred_hps)
		            in
		            let string_of_message sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls = 
		              let hp_decls = string_of_hp_decls hpdecls in
		              let pr_ass f1 f2 (x,y) = (f1 x)^" --> "^(f2 y) in
		              let pr1 =  pr_lst ";\n" (pr_ass Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
		              let ass_cont = pr1 hp_lst_assume in
		              let hpdefs_cont =  pr1 ls_inferred_hps in 
		              let ass = "ass " ^ (!CP.print_svl sel_hp_rels) ^ "[]: {\n" ^ ass_cont ^ "\n}\n" in
		              let hpdefs = "hpdefs " ^ (!CP.print_svl sel_hp_rels) ^ "[]: {\n"  ^ hpdefs_cont ^ "\n}\n"in
		              let test_comps = ass ^ hpdefs  in
		              let unmin_name = unmingle_name proc.proc_name in
		              let expected_res = "SUCCESS" in (*TODO: final res here (in inference, often SUCCESS*)
		              let message = hp_decls ^ "\n" ^ unmin_name ^":" ^ expected_res ^"[\n" ^ test_comps ^ "]\n" in
		              message
		            in
		            let is_match_constrs il constrs = 
		              if(not(!Globals.show_diff_constrs)) then 
			            CEQ.checkeq_constrs il (List.map (fun hp -> hp.CF.hprel_lhs,hp.CF.hprel_rhs) hp_lst_assume) constrs 
		              else
			            let res,res_list = CEQ.checkeq_constrs_with_diff il (List.map (fun hp -> hp.CF.hprel_lhs,hp.CF.hprel_rhs) hp_lst_assume) constrs in
			            if(not(res)) then 
			              print_string ("\nDiff constrs " ^ proc.proc_name ^ " {\n" ^ (print_res_list res_list false) ^ "\n}\n" );
			            res
		            in
		            let is_match_defs il sl defs = 
		              if(!Globals.show_diff_constrs) then (
			              let res,res_list = CEQ.checkeq_defs_with_diff il sl ls_inferred_hps defs sel_hp_rels in
			              if(not(res)) then 
			                print_string ("\nDiff defs " ^ proc.proc_name ^ " {\n" ^ (print_res_list res_list true) ^ "\n}\n" );
			              res
		              )
		              else let r,_ = CEQ.checkeq_defs_with_diff  il sl ls_inferred_hps defs sel_hp_rels in r
		            in
		            (**************************************************************)
		            (*****************************cp-test**************************)
		            let _ = if(!Globals.cp_test || !Globals.cp_prefile) then(
		                let _ = Gen.Profiling.push_time "Compare res with cp file" in
		                let test_comps = proc.Cast.proc_test_comps in
		                
		                let (res1, res2) =
			              match test_comps with
			                | None -> (false,false)
			                | Some (tcs) -> (
			                      let ass = tcs.Cast.expected_ass in
			                      let hpdefs = tcs.Cast.expected_hpdefs in
			                      match ass,hpdefs with
			                        | None, None -> (false, false)
			                        | Some (il,sl,a), None -> (is_match_constrs il a, false) 
			                        | None, Some (il,sl,d) -> (false, is_match_defs il sl d)
			                        | Some (il1,sl1,a), Some (il2,sl2,d) ->  (is_match_constrs il1 a, is_match_defs il2 sl2 d)
			                  )
		                in
		                let is_have_tc = match test_comps with
			              | None -> false 
			              | _ -> true
		                in
		                let _ = 
			              if(is_have_tc) then (
			                  let _ = if(res1) then 
			                    print_string ("Compare ass " ^ proc.proc_name ^ " SUCCESS\n" )
			                  else 
			                    print_string ("Compare ass " ^ proc.proc_name ^ " FAIL\n" )
			                  in
			                  let _ = if(res2) then 
			                    print_string ("Compare defs " ^ proc.proc_name ^ " SUCCESS\n" )
			                  else 
			                    print_string ("Compare defs " ^ proc.proc_name ^ " FAIL\n" )
			                  in
			                  ()
			              )
		                in
		                let _ = Gen.Profiling.pop_time "Compare res with cp file" in
		                ()
		            ) in
		            (****************************end cp-test**************************)
		            (*****************************************************************)
		            (************************gen_cpfile*******************************)
		            let _ = if(!Globals.gen_cpfile) then(
		                let _ = Gen.Profiling.push_time "Gen cp file" in
		                let file_name = !Globals.cpfile in
		                let hpdecls = prog.prog_hp_decls in
		                (*dropped_hps: decrease num of args --> should chaneg the hp_decl + change name also !!! *)
		                let revise_hpdecls hpdecl dropped_hps =
			              let name = hpdecl.Cast.hp_name in
			              try (
			                  let (sv,_,eargs) = List.find (fun (a,b,c) -> String.compare (CP.full_name_of_spec_var a) name == 0) dropped_hps in
			                  let new_hp_vars = List.fold_left List.append [] (List.map CP.afv eargs) in
			                  let new_name = Globals.hp_default_prefix_name ^ (string_of_int (Globals.fresh_int())) in
			                  print_string ("from name: " ^name ^" --> name: "^ new_name ^ "\n" );
			                  let new_sv =  CP.SpecVar (HpT,new_name,Unprimed) in
			                  let new_hpdecl =  ({hpdecl with Cast.hp_name = new_name;
				                  Cast.hp_vars = new_hp_vars}) in
			                  (new_hpdecl::[hpdecl],[(sv,new_sv)])
			              )
			              with 
			                | Not_found -> ([hpdecl],[])
		                in
		                let pairs = List.map (fun c-> revise_hpdecls c dropped_hps) hpdecls in
		                let e1,e2 = List.split pairs in
		                let hpdecls = List.concat e1 in
		                let name_mtb = List.concat e2 in (*mtb: name --> new_name*)
		                let (hpdecls1,hp_lst_assume1, ls_inferred_hps1) = simplify_varname sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls name_mtb in
		                let message = string_of_message sel_hp_rels hp_lst_assume1 ls_inferred_hps1 hpdecls1 in
		                let _ = try
			              (* let cout = open_out file_name in *)
			              (*let co = Format.formatter_of_out_channel cout in
			                Format.fprintf co "%s\n" message;*)
			              (
			                  match cout_option with
				                | Some cout -> Printf.fprintf cout "%s\n" message;   (* write something *)   
				                | _ -> ()
			              )
		                      (* Printf.fprintf cout "%s\n" "End!!!!!!!!!!!!!!!!!!!!!!!!!!!!!";   (\* write something *\)  *)  
			                  (* close_out cout *)
			            with Sys_error _ as e ->
			                Format.printf "Cannot open file \"%s\": %s\n" file_name (Printexc.to_string e)
		                in
		                let _ = Gen.Profiling.pop_time "Gen cp file" in
		                ()			
		            )
		            in
		            (************************end gen_cpfile*******************************)
                    (*****************************************************************)
                    let lst_rank = List.map (fun (_,a2,a3)-> (a2,a3)) lst_rank in
                    (*let _ = Ranking.do_nothing in*)
                    Debug.trace_hprint (add_str "SPECS (after simplify_ann)" pr_spec) new_spec no_pos;

                    Debug.trace_hprint (add_str "SPECS (before add_pre)" pr_spec) new_spec no_pos;
                    Debug.tinfo_hprint (add_str "NEW SPECS(B4)" pr_spec) new_spec no_pos;
                    let new_spec = AS.add_pre prog new_spec in
                    Debug.tinfo_hprint (add_str "NEW SPECS(AF)" pr_spec) new_spec no_pos;

                    if (pre_ctr # get> 0) 
                    then
                      begin
                        let new_spec =                           
                          let inf_post_flag = post_ctr # get > 0 in
                          Debug.devel_pprint ("\nINF-POST-FLAG: " ^string_of_bool inf_post_flag) no_pos;
                          let pres, posts, inf_vars = CF.get_pre_post_vars [] proc.proc_static_specs in
                          let pre_vars = CP.remove_dups_svl (pres @ (List.map 
                              (fun (t,id) -> CP.SpecVar (t,id,Unprimed)) proc.proc_args)) in
                          let post_vars = CP.remove_dups_svl posts in
                          try 
                            begin
                              (* type: (Fixbag.CP.formula * Fixbag.CP.Label_Pure.exp_ty) list *)
                              let pr = Cprinter.string_of_pure_formula in
                              Debug.tinfo_hprint (add_str "rels" (pr_list (pr_pair pr pr))) rels no_pos;
                              Debug.tinfo_hprint (add_str "mutual grp" (pr_list (fun x -> x.proc_name))) mutual_grp no_pos;
                              let triples (*(rel, post)*) = 
                                if rels = [] then (Infer.infer_rel_stk # reset;[])
                                else if mutual_grp != [] then []
                                else
                                  (let rels = List.map (fun (rt,f1,f2) -> (f1,f2)) Infer.infer_rel_stk # get_stk in
                                  Infer.infer_rel_stk # reset;
                                  Fixcalc.compute_fixpoint 2 rels pre_vars (proc.proc_stk_of_static_specs # top))
                              in
                              (* let pr_ty = !CP.Label_Pure.ref_string_of_exp in *)
                              Infer.fixcalc_rel_stk # push_list triples;
                              begin
                                print_endline "\n*************************************";
                                print_endline "*******fixcalc of pure relation *******";
                                print_endline "*************************************";
                                print_endline (Infer.fixcalc_rel_stk # string_of_reverse);
                                print_endline "*************************************"
                              end;                    
                              (* Debug.info_hprint (add_str "triples" (pr_list (pr_pair pr pr_ty))) triples no_pos; *)
                              let triples = List.map (fun (rel,post) ->
                                  let exist_vars = CP.diff_svl (CP.fv rel) inf_vars in
                                  (*                                let _ = Debug.info_hprint (add_str "EVARS : " !CP.print_svl) exist_vars no_pos in*)
                                  let pre_new = TP.simplify_exists_raw exist_vars post in
                                  (rel,post,pre_new)) triples in
                              let evars = stk_evars # get_stk in
                              (*                            let evars = [] in*)
                              let _ = List.iter (fun (rel,post,pre) ->
                                  Debug.info_pprint ("REL : "^Cprinter.string_of_pure_formula rel) no_pos;
                                  Debug.info_pprint ("POST: "^Cprinter.string_of_pure_formula post) no_pos;
                                  Debug.info_pprint ("PRE : "^Cprinter.string_of_pure_formula pre) no_pos) triples in
                              (* let _ = print_endline ( "   new_spec 1: " ^ (Cprinter.string_of_struc_formula new_spec)) in *)
                              if triples = [] then fst (Solver.simplify_relation new_spec None pre_vars post_vars prog inf_post_flag evars lst_assume)
                              else
                                let new_spec1 = (CF.transform_spec new_spec (CF.list_of_posts (proc.proc_stk_of_static_specs # top))) in
                                fst (Solver.simplify_relation new_spec1
                                    (Some triples) pre_vars post_vars prog inf_post_flag evars lst_assume)
                            end
                          with ex -> 
                              begin
                                Debug.info_pprint "PROBLEM with fix-point calculation" no_pos;
                                (* Debug.info_pprint ("Exception:"^(Printexc.to_string ex)) no_pos; *)

                                raise ex
                                (* new_spec *)
                              end
                        in
                        (* TODO WN : what happen to the old MayLoop? *)
                        (* let new_spec = CF.norm_struc_with_lexvar new_spec false in  *)
                        let _ = proc.proc_stk_of_static_specs # push new_spec in
                        (* let old_sp = Cprinter.string_of_struc_formula proc.proc_static_specs in *)
                        (* let new_sp = Cprinter.string_of_struc_formula new_spec in *)
                        (* let new_rels = pr_list Cprinter.string_of_only_lhs_rhs rels in *)
                        if !dis_post_chk then
                          (f,None)
                        else 
                          begin
                            (*let vars = stk_vars # get_stk in*)
                            (* let order_var v1 v2 vs = *)
                            (*   if List.exists (CP.eq_spec_var_nop v1) vs then *)
                            (*     if List.exists (CP.eq_spec_var_nop v2) vs then None *)
                            (*     else Some (v2,v1) *)
                            (*   else if List.exists (CP.eq_spec_var_nop v2) vs then Some (v1,v2) *)
                            (*   else None in *)
                            (* let rec extr_subs xs vs subs rest = match xs with  *)
                            (*   | [] -> (vs,subs,rest) *)
                            (*   | ((v1,v2) as p)::xs1 -> let m = order_var v1 v2 vs in *)
                            (*     (match m with *)
                            (*       | None -> extr_subs xs1 vs subs (p::rest)   *)
                            (*       | Some ((fr,t) as p2) -> extr_subs xs1 (fr::vs) (p2::subs) rest) in *)
                            (* let extr_subs xs vs subs rest =  *)
                            (*   let pr_vars = !CP.print_svl in *)
                            (*   let pr_subs = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
                            (*   let pr_res = pr_triple pr_vars pr_subs pr_subs in *)
                            (*   Debug.no_2 "extr_subs" pr_subs pr_vars pr_res (fun _ _ -> extr_subs xs vs subs rest) xs vs in *)
                            (* let rec simplify_subs xs vs ans =  *)
                            (*   let (vs1,subs,rest) = extr_subs xs vs [] [] in *)
                            (*    if subs==[] then ans *)
                            (*    else simplify_subs_f rest vs1 (subs@ans) *)
                            (* in  *)
                            (* let ra = List.map (fun (l,r) -> MCP.pure_ptr_equations l) lst_assume in *)
                            (* let subs = List.map (fun xs -> CP.simplify_subs xs vars []) ra in *)
                            (* Debug.info_hprint (add_str "alias" (pr_list (pr_list (pr_pair !CP.print_sv !CP.print_sv)))) ra no_pos; *)
                            (* Debug.info_hprint (add_str "subs" (pr_list (pr_list (pr_pair !CP.print_sv !CP.print_sv)))) subs no_pos; *)
                            Debug.ninfo_hprint (add_str "OLD SPECS" pr_spec) proc.proc_static_specs no_pos;
                            Debug.ninfo_hprint (add_str "NEW SPECS" pr_spec) new_spec no_pos;
                            Debug.ninfo_hprint (add_str "NEW RELS" (pr_list_ln Cprinter.string_of_only_lhs_rhs)) rels no_pos;
                            Debug.ninfo_hprint (add_str "NEW ASSUME" (pr_list_ln Cprinter.string_of_lhs_rhs)) lst_assume no_pos;
                            Debug.ninfo_hprint (add_str "NEW HP RELS" (pr_list_ln Cprinter.string_of_hprel)) hprels no_pos;
                            Debug.ninfo_hprint (add_str "NEW HP ASSUME" (pr_list_ln Cprinter.string_of_hprel)) hp_lst_assume no_pos;
			                Debug.ninfo_hprint (add_str "NEW INFERRED HP" (pr_list_ln Cprinter.string_of_hprel)) ls_inferred_hps no_pos;
                            Debug.tinfo_hprint (add_str "NEW RANK" (pr_list_ln Cprinter.string_of_only_lhs_rhs)) lst_rank no_pos;
                            Debug.tinfo_hprint (add_str "NEW CONJS" string_of_int) ((CF.no_of_cnts new_spec)-(CF.no_of_cnts proc.proc_static_specs)) no_pos;
                            stk_evars # reset;
                            (*                            let _ = Inf.print_spec (" " ^ (Inf.get_proc_name proc.proc_name) ^ "\n" ^ (pr_spec2 (CF.struc_to_prepost new_spec))) (Inf.get_file_name Sys.argv.(1)) in*)
                            let f = if f && !reverify_flag then 
                              let _,_,_,_,_,_,_,is_valid = check_specs_infer prog proc init_ctx new_spec body false in is_valid
                            else f 
                            in
                            (f, None)
                          end
                      end
		            else (f, None) 
                  with | _ as e -> (false, Some e) in
		        let _ = if !print_proof then begin
		          Prooftracer.pop_div ();
		          Prooftracer.add_proc proc pp;
		        end
		        in
		        let _ = match exc with | Some e -> raise e | None -> () in
                if pr_flag then
                  begin
		            if pp then print_string ("\nProcedure "^proc.proc_name^" SUCCESS\n")
	                else print_string ("\nProcedure "^proc.proc_name^" result FAIL-1\n")
                  end;
	      	    pp
	          end
    end else true

let check_proc (prog : prog_decl) (proc : proc_decl) cout_option (mutual_grp : proc_decl list) : bool =
  let pr p = pr_id (name_of_proc p)  in
  Debug.no_1_opt (fun _ -> not(is_primitive_proc proc))
      "check_proc" pr string_of_bool (check_proc prog) proc cout_option mutual_grp

let check_phase_only prog  proc =
(* check_proc prog proc *)
  try
	(*  let _ = print_endline ("check_proc_wrapper : proc = " ^ proc.Cast.proc_name) in *)
    let _=check_proc prog proc in () 
  with _ as e ->
      print_string ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      print_string ("\nException "^(Printexc.to_string e)^" during check_phase_only!\n");
      Printexc.print_backtrace(stdout);
      ()

(* check entire program *)
let check_proc_wrapper prog proc cout_option mutual_grp =
(* check_proc prog proc *)
  try
	(*  let _ = print_endline ("check_proc_wrapper : proc = " ^ proc.Cast.proc_name) in *)
    let res = check_proc prog proc cout_option mutual_grp in 
    (* Termination: Infer the phase numbers of functions in a scc group *) 
    (* TODO: The list of scc group does not 
     * need to be computed many times *)
    (* let n_res =  *)
    (*   if (proc.Cast.proc_is_main &&  *)
    (*       not !Globals.dis_phase_num &&  *)
    (*       not !Globals.dis_term_chk) then *)
    (*   begin *)
    (*     let (_, mutual_grps) = Cast.re_proc_mutual (Cast.sort_proc_decls (Cast.list_of_procs prog)) in *)
    (*     let name_mutual_grps = List.map (fun lp -> List.map (fun p -> p.Cast.proc_name) lp) mutual_grps in *)
    (*     let mutual_grp = List.find (fun g -> List.mem proc.Cast.proc_name g) name_mutual_grps in *)
    (*     let n_prog = Term.phase_num_infer_scc_grp mutual_grp prog proc in *)
    (*     (\* Termination: Reverify all procedures in the scc group *\) *)
    (*     if !term_reverify then *)
    (*       let scc_procs = List.map (fun nm -> Cast.find_proc n_prog nm) mutual_grp in  *)
    (*       List.for_all (fun p -> check_proc n_prog p) scc_procs  *)
    (*     else res  *)
    (*   end *)
    (*   else res *)
    (* in n_res *)
    res
  with _ as e ->
    if !Globals.check_all then begin
      (* dummy_exception(); *)
      print_string ("\nProcedure "^proc.proc_name^" FAIL-2\n");
      print_string ("\nException "^(Printexc.to_string e)^" Occurred!\n");
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

let init_files () =
  begin
    Omega.init_files ();
    Setmona.init_files ();
  end

let check_proc_wrapper_map prog (proc,num) cout_option =
  if !Tpdispatcher.external_prover then Tpdispatcher.Netprover.set_use_socket_map (List.nth !Tpdispatcher.external_host_ports (num mod (List.length !Tpdispatcher.external_host_ports))); (* make this dynamic according to availability of server machines*)
  try
    check_proc prog proc cout_option []
  with _ as e ->
    if !Globals.check_all then begin
      print_string ("\nProcedure "^proc.proc_name^" FAIL-3\n");
      print_string ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      false
    end else
      raise e 

let check_proc_wrapper_map_net prog  (proc,num) cout_option =
  try
    check_proc prog proc cout_option []
  with _ as e ->
    if !Globals.check_all then begin
      print_string ("\nProcedure "^proc.proc_name^" FAIL-4\n");
      print_string ("\nError(s) detected when checking procedure " ^ proc.proc_name ^ "\n");
      false
    end else
      raise e

let stk_tmp_checks = new Gen.stack 


let drop_phase_infer_checks() =
  stk_tmp_checks # push !dis_bnd_chk;
  stk_tmp_checks # push !dis_term_msg;
  stk_tmp_checks # push !dis_post_chk;
  stk_tmp_checks # push !dis_ass_chk;
  dis_bnd_chk := true;
  dis_term_msg := true;
  dis_post_chk := true;
  dis_ass_chk := true;
  phase_infer_ind := true

let restore_phase_infer_checks() =
  phase_infer_ind := false;
  dis_ass_chk := stk_tmp_checks # pop_top;
  dis_post_chk := stk_tmp_checks # pop_top;
  dis_term_msg := stk_tmp_checks # pop_top;
  dis_bnd_chk := stk_tmp_checks # pop_top

let check_prog (prog : prog_decl) =
  let cout_option = if(!Globals.gen_cpfile) then (
    Some (open_out (!Globals.cpfile))
  )
    else  None
  in
  let _ = if (Printexc.backtrace_status ()) then print_endline "backtrace active" in 
   (* let _ = Debug.info_pprint ("  check_prog: " ^ (Cprinter.string_of_program prog) ) no_pos in *)
  if !Globals.check_coercions then 
    begin
      print_string "Checking lemmas... ";
      (* ignore (check_coercion prog); *)
      check_coercion prog;
      print_string "DONE.\n"
    end;
  
  ignore (List.map (check_data prog) prog.prog_data_decls);
  (* Sort the proc_decls by proc_call_order *)
  let l_proc = Cast.list_of_procs prog in
  let proc_prim, proc_main = List.partition Cast.is_primitive_proc l_proc in
  let sorted_proc_main = Cast.sort_proc_decls proc_main in
  let _ = Debug.ninfo_hprint (add_str "sorted_proc_main"
      (pr_list Astsimp.pr_proc_call_order)
  ) sorted_proc_main no_pos in
  (* this computes a list of scc mutual-recursive methods for processing *)
  let proc_scc = List.fold_left (fun a x -> match a with
    | [] -> [[x]]
    | xs::xss -> 
          let i=(List.hd xs).proc_call_order in
          if i==x.proc_call_order then (x::xs)::xss
          else [x]::a
  ) [] sorted_proc_main in
  let proc_scc = List.rev proc_scc in
  let () = Debug.tinfo_hprint (add_str "SCC" (pr_list (pr_list (Astsimp.pr_proc_call_order)))) proc_scc no_pos in
  (* flag to determine if can skip phase inference step *)
  let skip_pre_phase = (!Globals.dis_phase_num || !Globals.dis_term_chk) in
  let prog = List.fold_left (fun prog scc -> 
      let prog =
        let call_order = (List.hd scc).proc_call_order in
        (* perform phase inference for mutual-recursive groups captured by stk_scc_with_phases *)
        if not(skip_pre_phase) && (stk_scc_with_phases # mem call_order) then 
          begin
            Debug.dinfo_pprint ">>>>>> Perform Phase Inference for a Mutual Recursive Group  <<<<<<" no_pos;
            Debug.dinfo_hprint (add_str "SCC"  (pr_list (fun p -> p.proc_name))) scc no_pos;
            drop_phase_infer_checks();
            proc_mutual_scc prog scc (fun prog proc -> ignore (check_proc prog proc cout_option []));
            restore_phase_infer_checks();
            (* the message here should be empty *)
            (* Term.term_check_output Term.term_res_stk; *)
            Term.phase_num_infer_whole_scc prog scc 
          end
        else prog in
      let mutual_grp = ref scc in
      Debug.tinfo_hprint (add_str "MG"  (pr_list (fun p -> p.proc_name))) !mutual_grp no_pos;
      let _ = proc_mutual_scc prog scc (fun prog proc ->
        begin 
          mutual_grp := List.filter (fun x -> x.proc_name != proc.proc_name) !mutual_grp;
          Debug.tinfo_hprint (add_str "SCC"  (pr_list (fun p -> p.proc_name))) scc no_pos;
          Debug.tinfo_hprint (add_str "MG_new"  (pr_list (fun p -> p.proc_name))) !mutual_grp no_pos;
          ignore (check_proc_wrapper prog proc cout_option !mutual_grp)
        end
      ) in        
      prog
  ) prog proc_scc 
  in 

  ignore (List.map (fun proc -> check_proc_wrapper prog proc cout_option []) ((* sorted_proc_main @ *) proc_prim));
  (*ignore (List.map (check_proc_wrapper prog) prog.prog_proc_decls);*)
  let _ =  match cout_option with
    | Some cout -> close_out cout
    | _ -> ()
  in 
  Term.term_check_output ()
	    
let check_prog (prog : prog_decl) =
  Debug.no_1 "check_prog" (fun _ -> "?") (fun _ -> "?") check_prog prog 
  (*Debug.no_1 "check_prog" (fun _ -> "?") (fun _ -> "?") check_prog prog iprog*)
