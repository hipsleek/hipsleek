#include "xdebug.cppo"
open VarGen
open GlobProver

let parse_only = ref false

let dump_ss = ref false

let typecheck_only = ref false

let rtc = ref false

let comp_pred = ref false

let pred_to_compile = ref ([] : string list)

let print_version_flag = ref false


let inter_hoa = ref false

let enable_gui = ref false

type front_end =
  | XmlFE
  | NativeFE

let fe = ref NativeFE

let set_pred arg =
  comp_pred := true;
  pred_to_compile := arg :: !pred_to_compile

let set_proc_verified arg =
  let procs = Gen.split_by "," arg in
  Globals.procs_verified := procs @ !Globals.procs_verified

let set_validate_config arg =
  Globals.validate_target := arg;
  Globals.validate := true

let set_gen_cpfile arg =
  Globals.cpfile := arg;
  Globals.gen_cpfile := true

let set_lib_file arg =
  Globals.lib_files := [arg]

let set_tp solver=
  let () = print_endline ("!!! init_tp by user: ") in
  Tpdispatcher.set_tp true solver

let set_frontend fe_str = match fe_str  with
  | "native" -> fe := NativeFE
  | "xml" -> fe := XmlFE
  | _ -> failwith ("Unsupported frontend: " ^ fe_str)


(* arguments/flags that might be used both by sleek and hip *)
let common_arguments = [
  ("--pprint", Arg.Set Globals.pretty_print,
   "Pretty print.");
  ("--sctx", Arg.Set Typechecker.simplify_context, "Simplify the context before each execution in symbolic execution."); (* An Hoa *)
  ("--sdp", Arg.Set Globals.simplify_dprint,
   "Simplify the entail state before printing the dprint state."); (* An Hoa *)
  ("--dis-sdp", Arg.Clear Globals.simplify_dprint,
   "Disable Simplify the entail state before printing the dprint state."); (* An Hoa *)
  ("-wpf", Arg.Set Globals.print_proof,
   "Print all the verification conditions, the input to external prover and its output.");
  ("--ufdp", Arg.Set Solver.unfold_duplicated_pointers,
  "Do unfolding of predicates with duplicated pointers."); (* An Hoa *)
  (* Labelling Options *)
  ("--temp-opt", Arg.Set Globals.temp_opt_flag,
   "Temporary option flag.");
  ("--temp-opt2", Arg.Set Globals.temp_opt_flag2,
   "Temporary option flag2.");
  ("--dis-lbl", Arg.Set Globals.remove_label_flag,
   "Disable Labelling of Formula by removing AndList.");
  ("--lbl-dis-split-conseq", Arg.Clear Globals.label_split_conseq,
   "Disable the splitting of consequent to expose labels.");
  ("--lbl-dis-split-ante", Arg.Clear Globals.label_split_ante,
   "Disable the splitting of antecedent to expose labels.");
  ("--lea-sat", Arg.Set Globals.label_aggressive_sat,
   "Enable aggressive splitting of label for sat.");
  ("--lea-imply", Arg.Set Globals.label_aggressive_imply,
   "Enable aggressive splitting of label for implications.");
  ("--lbl-en-aggr", Arg.Unit (fun _ ->
       Globals.label_aggressive_imply := true;
       Globals.label_aggressive_sat := true ),
   "Enable aggressive splitting of label.");
  ("--lbl-dis-aggr", Arg.Unit (fun _ ->
       Globals.label_aggressive_imply := false;
       Globals.label_aggressive_sat := false ),
   "Disable aggressive splitting of label.");
  ("--lbl-dis-aggr-imply", Arg.Unit (fun _ ->
       Globals.label_aggressive_imply := false),
   "Disable aggressive splitting of label for imply.");
  ("--lbl-dis-aggr-sat", Arg.Unit (fun _ ->
       Globals.label_aggressive_sat := false),
   "Disable aggressive splitting of label for sat.");
  ("--lda", Arg.Unit (fun _ ->
       Globals.label_aggressive_imply := false;
       Globals.label_aggressive_sat := false ),
   "Shorthand for --lbl-dis-aggr splitting of label.");
  ("--lea", Arg.Unit (fun _ ->
       Globals.label_aggressive_imply := true;
       Globals.label_aggressive_sat := true ),
   "Shorthand for --lbl-en-aggr.");
  (* UNSAT("":cf,"a":af,"b":bf)
     --> UNSAT(cf&af) | UNSAT(cf & bf) *)
  (* aggressive UNSAT("":cf,"a":af,"b":bf)
     --> UNSAT(cd) | UNSAT(af) & UNSAT(bf) *)
  (* IMPLY("":cf,"a":af,"b":bf --> "a":ta,"b":tb)
     --> IMPLY(cf&af -->ta) & IMPLY (cf&bf-->tb) *)
  (* aggressive IMPLY("":cf,"a":af,"b":bf --> "a":ta,"b":tb)
     --> IMPLY(af -->ta) & IMPLY (bf-->tb) *)
  (* ("--en-label-aggr-sat", Arg.Set Globals.label_aggressive_sat, "enable aggressive splitting of labels during unsat"); *)
  (* ("--dis-label-aggr-sat", Arg.Clear Globals.label_aggressive_sat, "disable aggressive splitting of labels during unsat"); *)
  (* ("--en-label-aggr", Arg.Set Globals.label_aggressive_flag, "enable aggressive splitting of labels"); *)
  (* ("--dis-label-aggr", Arg.Clear Globals.label_aggressive_flag, "disable aggressive splitting of labels"); *)
  ("--en-mult", Arg.Set Globals.prelude_is_mult,
   "Enable using mult as prim.");
  ("--en-ptr-arith", Arg.Set Globals.ptr_arith_flag,
   "Enable use of Ptr Arithmetic (incl type checking).");
  ("--dis-ptr-arith", Arg.Clear Globals.ptr_arith_flag,
   "Disable use of Ptr Arithmetic (incl type checking).");
  ("--dis-mult", Arg.Clear Globals.prelude_is_mult,
   "Enable using mult as prim.");
  ("--dis-ufdp", Arg.Clear Solver.unfold_duplicated_pointers,
   "Disable unfolding of predicates with duplicated pointers."); (* An Hoa *)
  ("--ahwytdi", Arg.Set Smtsolver.try_induction,
   "Try induction in case of failure implication."); (* An Hoa *)
  ("--smtimply", Arg.Set Smtsolver.outconfig.Smtsolver.print_implication,
   "Print the antecedent and consequence for each implication check."); (* An Hoa *)
  ("--smtout", Arg.Set Globals.print_original_solver_output,
   "Print the original output given by the SMT solver."); (* An Hoa *)
  ("--smtinp", Arg.Set Globals.print_original_solver_input,
   "Print the program generated SMT input."); (* An Hoa *)
  ("--no-omega-simpl", Arg.Clear Globals.omega_simpl,
   "Do not use Omega to simplify the arithmetic constraints when using other solver");
  ("--no-simpl", Arg.Set Globals.no_simpl,
   "Do not simplify the arithmetic constraints");
  ("--simpl-pure-part", Arg.Set Globals.simplify_pure,
   "Simplify the pure part of the formulas");
  (* ("--combined-lemma-heuristic", Arg.Set Globals.lemma_heuristic, *)
  (* "Use the combined coerce&match + history heuristic for lemma application"); *)
  ("--push-exist-deep", Arg.Set Globals.push_exist_deep,
   "Push exist as deep as possible");
  ("--move-exist-to-LHS", Arg.Set Globals.move_exist_to_LHS,
   "Move instantiation (containing existential vars) to the LHS at the end of the folding process");
  ("--max-renaming", Arg.Set Globals.max_renaming,
   "Always rename the bound variables");
  ("--dis-anon-exist", Arg.Clear Globals.anon_exist,
   "Disallow anonymous variables in the precondition to be existential");
  ("--en-anon-exist", Arg.Set Globals.anon_exist,
   "Allow anonymous variables in the precondition to be existential");
  ("--LHS-wrap-exist", Arg.Set Globals.wrap_exist,
   "Existentially quantify the fresh vars in the residue after applying ENT-LHS-EX");
  ("-noee", Arg.Clear Globals.elim_exists_flag,
   "No eliminate existential quantifiers before calling TP.");
  ("--no-filter", Arg.Clear Globals.filtering_flag,
   "No assumption filtering.");
  ("--filter-false", Arg.Set Globals.filtering_false_flag,
   "Enable false in assumption filtering.");
  ("--dis-filter-false", Arg.Clear Globals.filtering_false_flag,
   "Disable false in assumption filtering.");
  ("--filter", Arg.Set Globals.filtering_flag,
   "Enable assumption filtering.");
  ("--constr-filter", Arg.Set Globals.enable_constraint_based_filtering, "Enable assumption filtering based on contraint type");
  ("--no-split-rhs", Arg.Clear Globals.split_rhs_flag,
   "No Splitting of RHS(conseq).");
  ("--array-expansion", Arg.Set Globals.array_expansion, "Use expansion strategy to deal with array, in code level");
  ("--array-translate-out",Arg.Set Globals.array_translate, "Translate out array in formula");
  ("--dis-array-translate-out",Arg.Clear Globals.array_translate, "Disable Translate out array in formula");
  ("--ato",Arg.Set Globals.array_translate, "shorthand for --array-translate-out");
  ("--dlp", Arg.Clear Globals.check_coercions,
   "Disable Lemma Proving");
  ("--dis-auto-num", Arg.Clear Globals.auto_number,
   "Disable Auto Numbering");
  ("--dis-slk-log-filter", Arg.Clear Globals.sleek_log_filter,
   "Sleek Log Filter Flag");
  ("--elp", Arg.Set Globals.check_coercions,
   "enable lemma proving");
  ("--eel", Arg.Set Globals.eager_coercions,
   "enable earger lemma applying");
  ("--del", Arg.Clear Globals.eager_coercions,
   "diable earger lemma applying");
  ("--dump-lemmas", Arg.Set Globals.dump_lemmas,
   "enable lemma printing");
  ("--dl", Arg.Set Globals.dump_lemmas,
   "enable lemma printing");
  ("--dump-lemmas-short", Arg.Unit
     (fun _ -> Globals.dump_lemmas := true;
       Globals.dump_lemmas_med := true;),
   "enable lemma printing (short version)");
  ("--dls", Arg.Unit
     (fun _ ->
        Globals.dump_lemmas_med := true;
        Globals.dump_lemmas := true;),
   "enable lemma printing (short version)");
  ("--dump-lem-processing-info", Arg.Set Globals.dump_lem_proc,
   "Turn on printing during lemma processing (incl lemma proving) ");
  ("--dlpi", Arg.Set Globals.dump_lem_proc,
   "same as --dump-lem-processing-info ");
  ("--trace", Arg.Set Debug.trace_on,
   "Turn on brief tracing");
  ("--dis-trace", Arg.Clear Debug.trace_on,
   "Turn off brief tracing");
  ("-dd", Arg.Unit (fun _ ->
      Debug.devel_debug_on :=true;
      Debug.devel_debug_steps :=true
     ),
   "Turn on devel_debug on short and normal output");
  ("-dd-steps", Arg.Set Debug.devel_debug_steps,
   "Turn on tracing of entailment proving steps ");
  ("-dd-esl", Arg.Int (fun n ->
       Globals.proof_logging_txt:=true;
       Globals.sleek_logging_txt:=true;
       Debug.devel_debug_on:=false;
       Debug.devel_debug_sleek_proof := n;
     ),
   "Turn on devel_debug for a particular sleek proof");
  ("-dd-short", Arg.Unit (fun () -> Debug.devel_debug_on := true; Globals.debug_level := Globals.Short),
   "Turn on devel_debug only short output");
  ("-dd-long", Arg.Unit (fun () -> Debug.devel_debug_on := true; Globals.debug_level := Globals.Long),
   "Turn on devel_debug on all outputs");
  ("--dd-debug",  Arg.Unit
     (fun _ ->
        Debug.debug_print:=true;
        Globals.print_type:=true;
     ),
   "Use it for more precise printing to support debugging");
  ("-dd-threshold", Arg.Set_int Debug.call_threshold,
   "--dd-calls threshold number before printing");
  ("-dd-debug", Arg.Set Debug.devel_debug_on,
   "Turn on devel_debug");
  ("-dd-calls", Arg.String
     (fun s ->
        Debug.dump_calls:=true;
        Debug.call_str:=s;
        Gen.debug_precise_trace:=true;),
   "Dump summary of debugged calls (related to rgx)");
  ("--dd-calls", Arg.Unit
     (fun _ ->
        Debug.dump_calls:=true;
        Gen.debug_precise_trace:=true;),
   "Dump summary of debugged calls");
  ("--dd-calls-all", Arg.Unit
     (fun _ ->
        Debug.dump_calls:=true;
        Debug.dump_callers_flag:=true;
        Debug.dump_calls_all:=true;
        Gen.debug_precise_trace:=true;
     ),
   "Dump all debugged calls");
  ("--dd-callers-all", Arg.Unit
     (fun _ ->
        Debug.dump_calls:=true;
        Debug.dump_callers_flag:=true;
        (* Debug.dump_calls_all:=true; *)
        Gen.debug_precise_trace:=true;
     ),
   "Dump all debugged calls");
  ("-dd-calls-all", Arg.String
     (fun s ->
        Debug.dump_calls:=true;
        Debug.dump_calls_all:=true;
        Gen.debug_precise_trace:=true;
        Debug.call_str:=s;
     ),
   "Dump all debugged calls (related to rgx)");
  ("--dis-ddb", Arg.Clear Debug.trace_on,
   "Turn off experimental trace_on");
  ("--en-ddb", Arg.Set Debug.trace_on,
   "Turn on experimental trace_on");
  ("--en-early-contra", Arg.Set Globals.early_contra_flag,
   "Enable early contra detection always");
  ("--dis-early-contra", Arg.Clear Globals.early_contra_flag,
   "Diable early contra detection which now only happens with inference");
  ("-dd-print-orig-conseq", Arg.Unit Debug.enable_dd_and_orig_conseq_printing,
   "Enable printing of the original consequent while debugging. Automatically enables -dd (debugging) ");
  ("--en-imp-top", Arg.Set Globals.imply_top_flag,
   "Enable proof logging of Imply_Top");
  ("--dis-imp-top", Arg.Clear Globals.imply_top_flag,
   "Disable proof logging of Imply_Top");
  ("-gist", Arg.Set Globals.show_gist,
   "Show gist when implication fails");
  ("--hull-pre-inv", Arg.Set Globals.hull_pre_inv,
   "Hull precondition invariant at call sites");
  ("--sat-timeout", Arg.Float (fun v -> Globals.sat_timeout_limit:=v; Globals.user_sat_timeout:=true),
   "Timeout for sat checking");
  ("--imply-timeout", Arg.Set_float Globals.imply_timeout_limit,
   "Timeout for imply checking");
  ("--slk-timeout", Arg.Set_float Globals.sleek_timeout_limit,
   "Timeout for SLEEK entailment");
  ("--ds-provers-timeout", Arg.Set Globals.dis_provers_timeout,
   "Disable timeout on provers");
  ("--log-proof", Arg.String Prooftracer.set_proof_file,
   "Log (failed) proof to file");
  ("--trace-failure", Arg.Set VarGen.trace_failure,
   "Enable trace all failure (and exception). Use make gbyte");
  ("--trace-exc", Arg.Set VarGen.trace_exc,
   "Enable trace of exceptions invoked by methods");
  ("--trace-log", Arg.Set Gen.debug_trace_log,
   "Enable trace of method logs during debugging");
  ("--trace-log-num", Arg.Int (fun i ->
       Gen.debug_trace_log_num:=i;
       Gen.debug_trace_log :=true;
     ),
   "Enable trace of a specific method call for debugging");
  ("--trace-loop", Arg.Set VarGen.trace_loop,
   "Enable trace of method header during debugging");
  ("--trace-loop-all", Arg.Unit (fun _ ->
       VarGen.trace_loop_all :=true;
       VarGen.trace_loop :=true;
     ),
   "Enable trace of method header during debugging (with details on arg)");
  (* Exception(fixcalc_of_pure_formula):Stack overflow *)
  (* Exception(compute_def@6):Failure("compute_def:Error in translating the input for fixcalc") *)
  (* Exception(compute_fixpoint_aux@5):Failure("compute_def:Error in translating the input for fixcalc") *)
  (* Exception(compute_fixpoint#5@4):Failure("compute_def:Error in translating the input for fixcalc") *)
  ("--trace-all", Arg.Set Globals.trace_all,
   "Trace all proof paths");
  ("--log-cvcl", Arg.String Cvclite.set_log_file,
   "Log all CVC Lite formula to specified log file");
  (* ("--log-cvc4", Arg.String Cvc4.set_log_file, *)
  ("--log-cvc4", Arg.Unit Cvc4.set_log_file,    "Log all formulae sent to CVC4 in file allinput.cvc4");
  ("--log-omega", Arg.Set Omega.log_all_flag,
   "Log all formulae sent to Omega Calculator in file allinput.oc");
  ("--log-z3", Arg.Set Smtsolver.log_all_flag,
   "Log all formulae sent to z3 in file allinput.z3");
  ("--log-z3n", Arg.Set Z3.log_all_flag,
   "Log all formulae sent to z3 in file allinput.z3n");
  ("--log-isabelle", Arg.Set Isabelle.log_all_flag,
   "Log all formulae sent to Isabelle in file allinput.thy");
  ("--log-coq", Arg.Set Coq.log_all_flag,
   "Log all formulae sent to Coq in file allinput.v");
  ("--log-mona", Arg.Set Mona.log_all_flag,
   "Log all formulae sent to Mona in file allinput.mona");
  ("--log-redlog", Arg.Set Redlog.is_log_all,
   "Log all formulae sent to Reduce/Redlog in file allinput.rl");
  ("--log-math", Arg.Set Mathematica.is_log_all,
   "Log all formulae sent to Mathematica in file allinput.math");
  ("--use-isabelle-bag", Arg.Set Isabelle.bag_flag,
   "Use the bag theory from Isabelle, instead of the set theory");
  ("--ann-derv", Arg.Set Globals.ann_derv,"manual annotation of derived nodes");
  ("--en-weaker-pre", Arg.Set Globals.weaker_pre_flag,"Enable Weaker Pre-Condition to be Inferred");
  ("--dis-weaker-pre", Arg.Clear Globals.weaker_pre_flag,"Disable Weaker Pre-Condition to be Inferred");
  ("--warn-fvars-rhs-match", Arg.Set Globals.warn_fvars_rhs_match,"Enable Warning of Free Vars in RHS of Match");
  ("--warn-post-free-vars", Arg.Set Globals.warn_post_free_vars,"Enable Warning of Free Vars in Post-Conditions");
  ("--warn-trans-context", Arg.Set Globals.warn_trans_context,"Enable Warning of Non-empty Perm Vars");
  ("--warn-nonempty-perm-vars", Arg.Set Globals.warn_nonempty_perm_vars,"Enable Warning of Non-empty Perm Vars");
  ("--warn-do-match-infer-heap", Arg.Set Globals.warn_do_match_infer_heap,"Enable Warning of do_match during infer_heap");
  (* WN : this excludes ann_vars and ho_vars, but include perm_vars *)
  ("--warn-free-vars-conseq", Arg.Set Globals.warn_free_vars_conseq,"Enable Warning of Non-empty free heap vars in conseq");
  ("--new-infer-large-step", Arg.Set Globals.new_infer_large_step,"Enable new large step inference with simple LHS");
  ("--new-tp-simplify", Arg.Clear Globals.old_tp_simplify,"Use om_simplify instead of TP.simplify_raw");
  ("--en-mkeqn-opt", Arg.Set Globals.mkeqn_opt_flag,"Enable mkeqn optimization");
  ("--dis-mkeqn-opt", Arg.Clear Globals.mkeqn_opt_flag,"Disable mkeqn optimization");
  ("--old-univ-lemma", Arg.Set Globals.old_univ_lemma,"Use old univ lemma technique (bug with ex6e3e.slk)");
  ("--old-compute-act", Arg.Set Globals.old_compute_act,"Use old method of filtering actions");
  ("--new-compute-act", Arg.Clear Globals.old_compute_act,"Use new (better) method of filtering actions");
  ("--old-heap-contra", Arg.Clear Globals.new_heap_contra,"Do not use heap contra (bug with ex6e3f9.slk --pnum 4)");
  ("--new-heap-contra", Arg.Set Globals.new_heap_contra,"Use heap contra for inference (bug with ex6e3f9.slk --pnum 4)");
  ("--new-univ-lemma", Arg.Clear Globals.old_univ_lemma,"Use new univ lemma technique (bug with ex6e3e.slk)");
  ("--old-tp-simplify", Arg.Set Globals.old_tp_simplify,"Use TP.simplify_raw (bug with ex25m5d.slk)");
  ("--new-pred-extn", Arg.Clear Globals.old_pred_extn,"Use old pred extension");
  ("--old-pred-extn", Arg.Set Globals.old_pred_extn,"Use new pred extension approach");
  ("--old-lemma-switch", Arg.Set Globals.old_lemma_switch,"Use old lemma switching approach");
  ("--new-lemma-switch", Arg.Clear Globals.old_lemma_switch,"Use new lemma switching approach");
  ("--old-free-var-lhs", Arg.Set Globals.old_free_var_lhs,"Use free vars of LHS for fold lemma proving");
  ("--new-free-var-lhs", Arg.Clear Globals.old_free_var_lhs,"Use guards/parameter as free vars of LHS in fold lemma proving");
  ("--old-field-tag", Arg.Set Globals.old_field_tag,"Add old field tags VAL_i, REC_i to data fields");
  ("--new-field-tag", Arg.Clear Globals.old_field_tag,"Do not old field tags VAL_i, REC_i to data fields");
  ("--old-lemma-unfold", Arg.Set Globals.old_lemma_unfold,"Do not use lemma single unfold");
  ("--new-lemma-unfold", Arg.Clear Globals.old_lemma_unfold,"Use lemma single unfold");
  ("--new-trace-classic", Arg.Set Globals.new_trace_classic,"Trace classic ");
  ("--old-trace-classic", Arg.Clear Globals.new_trace_classic,"No tracing for classic ");
  ("--old-view-equiv", Arg.Set Globals.old_view_equiv,"Do not use view equivalence (pred reuse)");
  ("--new-view-equiv", Arg.Clear Globals.old_view_equiv,"Use view equivalence (pred reuse)");
  ("--old-search-always", Arg.Set Globals.old_search_always,"Allow search_action always..");
  ("--new-search-always", Arg.Clear Globals.old_search_always,"Use smart search_action always..");
  ("--en-cond-always", Arg.Set Globals.cond_action_always,"Allow cond_action always..");
  ("--en-rev-priority", Arg.Set Globals.rev_priority,"Allow reverser priority for action ");
  ("--old-coer-target", Arg.Set Globals.old_coer_target,"Allow coer_target check before applying lemma");
  ("--old-infer-large-step", Arg.Clear Globals.new_infer_large_step,"Disble new large step inference with simple LHS");
  ("--en-infer-back-ptr", Arg.Set Globals.infer_back_ptr,"Enable infer back pointer for infer_fold");
("--dis-infer-back-ptr", Arg.Clear Globals.infer_back_ptr,"Disble infer back pointer for infer_fold");
  ("--new-infer-complex-lhs", Arg.Clear Globals.old_infer_complex_lhs,"Disallow inference of complex LHS");
  ("--old-infer-complex-lhs", Arg.Set Globals.old_infer_complex_lhs,"Allow inference of complex LHS");
  ("--new-rm-htrue", Arg.Set Globals.new_rm_htrue,"Enable removal of htrue from ante");
  ("--old-base-case-fold-hprel", Arg.Set Globals.old_base_case_fold_hprel,"Use old method of base_case_fold for inferring hprel");
  ("--new-base-case-fold-hprel", Arg.Clear Globals.old_base_case_fold_hprel,"Use new  method of base_case_fold for inferring hprel");
  ("--old-fvars-as-impl-match", Arg.Set Globals.old_fvars_as_impl_match,"Use old method where free var is treated as implicit vars");
  ("--new-fvars-as-impl-match", Arg.Clear Globals.old_fvars_as_impl_match,"New method where free var are not treated as implicit vars");
  ("--old-unsound-no-progress", Arg.Set Globals.old_unsound_no_progress,"Use old lemma proving without fold progress checking");
  ("--new-unsound-no-progress", Arg.Clear Globals.old_unsound_no_progress,"Use new lemma proving with fold progress checking");
  ("--old-infer-heap", Arg.Set Globals.old_infer_heap,"Use old method of scheduling Infer_Heap");
  ("--new-infer-heap", Arg.Clear Globals.old_infer_heap,"Use new method of scheduling Infer_Heap");
  ("--old-mater-coercion", Arg.Set Globals.old_mater_coercion,"Use Old Mater Coercion Selection");
  ("--new-mater-coercion", Arg.Clear Globals.old_mater_coercion,"Use New Mater Coercion Selection");
  ("--old-keep-triv-relass", Arg.Set Globals.old_keep_triv_relass,"Keep trivial relation assume (hp_rel and pure relation) during inference");
  ("--new-keep-triv-relass", Arg.Clear Globals.old_keep_triv_relass,"Remove trivial relation assume during inference");
  ("--old-post-impl-to-ex", Arg.Set Globals.old_post_impl_to_ex,"Convert impl to exist vars in post-condition");
  ("--old-post-conv-impl", Arg.Set Globals.old_post_conv_impl,"Convert exist vars in post-condition to implicit");
  ("--new-post-conv-impl", Arg.Clear Globals.old_post_conv_impl,"Convert exist vars in post-condition to implicit");
  ("--old-classic-rhs-emp", Arg.Set Globals.old_classic_rhs_emp,"Use old handling of classic rhs emp");
  ("--new-classic-rhs-emp", Arg.Clear Globals.old_classic_rhs_emp,"Use new handling of classic rhs emp");
  ("--old-incr-infer", Arg.Set Globals.old_incr_infer,"Use old inference system");
  ("--old-rm-htrue", Arg.Clear Globals.new_rm_htrue,"Disable removal of htrue from ante");
  ("--old-keep-all-matchres", Arg.Set Globals.old_keep_all_matchres,"Keep all matchres including empty ones");
  ("--new-keep-all-matchres", Arg.Clear Globals.old_keep_all_matchres,"Filter out matchres that are empty first");
  ("--old-do-match-infer-heap", Arg.Set Globals.old_do_match_infer_heap,"Enable do match during infer_heap (seems wrong)");
  ("--new-do-match-infer-heap", Arg.Clear Globals.old_do_match_infer_heap,"Disable do match during infer_heap (cleaner)");
  ("--old-infer-hprel-classic", Arg.Set Globals.old_infer_hprel_classic,"Enable infer hp_rel handling of classic (seems redundant)");
  ("--old-collect-hprel", Arg.Set Globals.old_collect_hprel,"Enable Old False which invokes infer_hp_rel without classic");
  ("--old-collect-false", Arg.Set Globals.old_collect_false,"Enable Old False Collection Method (to detect unsoundness)");
  ("--old-base-case-unfold", Arg.Set Globals.old_base_case_unfold,"Enable Old BaseCaseUnfold Method");
  ("--old-infer-collect", Arg.Set Globals.old_infer_collect,"Enable Old Infer Collect Method");
  ("--old-infer-hp-collect", Arg.Set Globals.old_infer_hp_collect,"Enable Old Infer Collect Method for Shape");
  ("--old-impl-gather", Arg.Set Globals.old_impl_gather,"Enable Extra Impl Gather at CF.struc_formula_trans_heap_node");
  ("--old-parse-fix", Arg.Set Globals.old_parse_fix,"Enable Old Parser for FixCalc (to handle self/REC)");
  ("--en-hrel-as-view", Arg.Set Globals.hrel_as_view_flag,"Enable HRel as view");
  ("--dis-hrel-as-view", Arg.Clear Globals.hrel_as_view_flag,"Disable HRel as view");
  ("--en-init-para", Arg.Set Globals.init_para_flag,"Enable init_para for infer relation ");
  ("--adhoc-1", Arg.Set Globals.adhoc_flag_1,"Enable Adhoc Flag 1");
  ("--adhoc-2", Arg.Set Globals.adhoc_flag_2,"Enable Adhoc Flag 2");
  ("--adhoc-3", Arg.Set Globals.adhoc_flag_3,"Enable Adhoc Flag 3");
  ("--adhoc-4", Arg.Set Globals.adhoc_flag_4,"Enable Adhoc Flag 4");
  ("--adhoc-5", Arg.Set Globals.adhoc_flag_5,"Enable Adhoc Flag 5");
  ("--adhoc-6", Arg.Set Globals.adhoc_flag_6,"Enable Adhoc Flag 6");
  ("--old-univ-vars", Arg.Set Globals.old_univ_vars,"Old method of using univ vars");
  ("--new-univ-vars", Arg.Clear Globals.old_univ_vars,"New method of using univ vars");
  ("--old-keep-absent", Arg.Set Globals.old_keep_absent,"Keep absent nodes during expure - unsound");
  ("--old-empty-to-conseq", Arg.Set Globals.old_empty_to_conseq,"Keep to_conseq empty");
  ("--assert-unsound-false", Arg.Set Globals.assert_unsound_false, "Flag unsound false");
  ("--assert-no-glob-vars", Arg.Set Globals.assert_no_glob_vars, "Flag if non-empty to_conseq");
  ("--assert-nonlinear", Arg.Set Globals.assert_nonlinear,"Enable Asserting Testing of Nonlnear Pre-Processing");
  ("--ann-vp", Arg.Set Globals.ann_vp,"manual annotation of variable permissions");
  ("--dis-ann-vp", Arg.Clear Globals.ann_vp,"disable manual annotation of variable permissions");
  ("--ls", Arg.Set Globals.allow_ls,"enable locksets during verification");
  ("--en-web-compile", Arg.Set Globals.web_compile_flag,"enable web compilation setting");
  ("--dis-web-compile", Arg.Clear Globals.web_compile_flag,"disable web compilation setting");
  ("--dis-ls", Arg.Clear Globals.allow_ls,"disable locksets during verification");
  ("--locklevel", Arg.Set Globals.allow_locklevel,"enable locklevels during verification");
  ("--dis-locklevel", Arg.Clear Globals.allow_locklevel,"disable locklevels during verification");
  ("--dis-lsmu-infer", Arg.Clear Globals.allow_lsmu_infer,"disable simple inference of lsmu");
  ("--en-lsmu-infer", Arg.Set Globals.allow_lsmu_infer,"enable simple inference of lsmu");
  ("--en-false-unk-infer", Arg.Set Globals.infer_false_imply_unknown,"Enable false -> unknown to be inferred");
  ("--dis-false-unk-infer", Arg.Clear Globals.infer_false_imply_unknown,"Disable false -> unknown to be inferred");
  ("--dis-para", Arg.Unit Perm.disable_para,"disable concurrency verification");
  ("--en-para", Arg.Unit Perm.enable_para,"enable concurrency verification");
  ("--dis-change-flow", Arg.Clear Globals.change_flow,"disable change spec flow");
  ("--en-change-flow", Arg.Set Globals.change_flow,"enable change spec flow");
  ("--en-thrd-resource", Arg.Set Globals.allow_threads_as_resource,"enable threads as resource");
  ("--en-thrd-and-conj", Arg.Clear Globals.allow_threads_as_resource,"enable threads as AND-conjunction (not threads as resource)");
  ("--seg-opt", Arg.Set Globals.graph_norm,"enable the graph-based optimization for segment data structures");
  ("--dis-seg-opt", Arg.Clear Globals.graph_norm,"disable the graph-based optimization for segment data structures");
  ("--oc-dis-simp", Arg.Clear Globals.oc_simplify,"disable oc simplification");
  ("--oc-en-simp", Arg.Set Globals.oc_simplify,"enable oc simplification");
  ("--en-nonlinear", Arg.Set Globals.non_linear_flag,"enable non-linear pre-processing");
  ("--dis-nonlinear", Arg.Clear Globals.non_linear_flag,"disable non-linear pre-processing");
  (* ("--oc-en-matrix", Arg.Set Globals.oc_matrix_eqn,"enable oc matrix equational solvingline of constants"); *)
  (* ("--oc-dis-matrix", Arg.Clear Globals.oc_matrix_eqn,"enable oc matrix equational solving of constants"); *)
  ("--oc-en-warning", Arg.Set Globals.oc_warning,"Enable Omega warning");
  ("--oc-dis-warning", Arg.Clear Globals.oc_warning,"Disable Omega warning");
  ("--oc-dis-adv-simp", Arg.Clear Globals.oc_adv_simplify,"disable oc advancde simplification");
  ("--oc-en-adv-simp", Arg.Set Globals.oc_adv_simplify,"enable oc advanced simplification");
  ("--imm", Arg.Set Globals.allow_imm,"enable the use of immutability annotations");
  ("--en-imm-norm", Arg.Set Globals.allow_imm_norm, "enable normalization of immutability annotations (default)");
  ("--dis-imm-norm", Arg.Clear Globals.allow_imm_norm, "disable normalization of immutability annotations");
  ("--field-imm", Arg.Unit ( fun _ ->
       Globals.allow_field_ann := true;
       Globals.imm_merge := true;
       Globals.simpl_memset := true;
     ),"enable the use of immutability annotations for data fields");
  ("--memset-opt", Arg.Set Globals.ineq_opt_flag,"to optimize the inequality set enable");
  ("--dis-field-imm", Arg.Clear Globals.allow_field_ann,"disable the use of immutability annotations for data fields");
  ("--allow-array-inst", Arg.Set Globals.allow_array_inst,"Allow instantiation of existential arrays");
  ("--en-remove-abs", Arg.Set Globals.remove_abs,"remove @A nodes from formula (incl nodes with all fields ann with @A)");
  ("--dis-remove-abs", Arg.Clear Globals.remove_abs,"disable removing @A nodes from formula (incl nodes with all fields ann with @A)");
  ("--en-imm-merge", Arg.Set Globals.imm_merge,"try to merge aliased nodes");
  ("--dis-imm-merge", Arg.Clear Globals.imm_merge,"don't merge aliased nodes");
  ("--en-weak-imm", Arg.Set Globals.imm_weak,"enable weak instatiation (<:)");
  ("--dis-weak-imm", Arg.Clear Globals.imm_weak,"enable strong instatiation (=)");
  ("--en-imm-simplif-inst", Arg.Set Globals.imm_simplif_inst,"don't merge aliased nodes");
  ("--dis-imm-simplif-inst", Arg.Clear Globals.imm_simplif_inst,"don't merge aliased nodes");
  ("--en-aggresive-imm-inst", Arg.Set Globals.aggresive_imm_inst,"add lhs_imm<:rhs_imm to state (during matching), when lhs_imm is unrestricted");
  ("--dis-aggresive-immf-inst", Arg.Clear Globals.aggresive_imm_inst,"don't add lhs_imm<:rhs_imm, when lhs_imm is unrestricted");
  ("--en-imm-simpl", Arg.Set Globals.imm_add,"simplify imm addition");
  ("--dis-imm-simpl", Arg.Clear Globals.imm_add,"disable imm addition simplification");
  ("--imm-inf-seq", Arg.Unit (fun _ ->
       Globals.imm_seq := true;
       Globals.imm_sim := false;), "infer imm pre/post sequentially");
  ("--imm-inf-sim",  Arg.Unit (fun _ ->
       Globals.imm_sim := true;
       Globals.imm_seq := false;), "infer imm pre/post simultaneously ");
  ("--mem", Arg.Unit (fun _ ->
       Globals.allow_mem := true;
       Globals.allow_field_ann := true;),
   "Enable the use of Memory Specifications");
  ("--dis-mem", Arg.Clear Globals.allow_mem,"Disable the use of Memory Specifications");
  ("--ramify", Arg.Clear Solver.unfold_duplicated_pointers,"Use Ramification (turns off unfold on dup pointers)");
  ("--gen-coq-file", Arg.Set Globals.gen_coq_file, "Generate a Coq file with all axioms and lemmas to prove for certified reasoning");
  ("--allow-ramify", Arg.Unit (fun _ ->
       Globals.allow_ramify := true;
       Solver.unfold_duplicated_pointers := false;)
  , "Enable Coq based Ramification for Shared Structures");
  ("--en-filter-infer-search",Arg.Set Globals.filter_infer_search,"Enable filter on search result with inference");
  ("--dis-filter-infer-search",Arg.Clear Globals.filter_infer_search,"Enable filter on search result with inference");
  ("--infer-mem",Arg.Set Globals.infer_mem,"Enable inference of memory specifications");
  ("--infer-en-raw",Arg.Set Globals.infer_raw_flag,"Enable simplify_raw during pure inference");
  ("--infer-dis-raw",Arg.Clear Globals.infer_raw_flag,"Disable simplify_raw during pure inference");
  ("--pa",Arg.Set Globals.pa,"Program analysis with memory specifications");
  ("--reverify", Arg.Set Globals.reverify_flag,"enable re-verification after specification inference");
  ("--reverify-all", Arg.Set Globals.reverify_all_flag,"enable re-verification after heap specification inference");
  ("--dis-imm", Arg.Unit (fun _ ->
       Globals.allow_imm:=false;
       (* Globals.early_contra_flag:=false *)
       (* WN : quick fix *)
       (* WN : xpure_enum is not working properly with early_contra for --eps *)
     ),"disable the use of immutability annotations");
  ("--imm-en-subs-rhs", Arg.Set Globals.allow_imm_subs_rhs,"enable the substitution of rhs eq for immutability");
  ("--imm-dis-subs-rhs", Arg.Clear Globals.allow_imm_subs_rhs,"disable the substitution of rhs eq for immutability");
  ("--en-imm-inv", Arg.Set Globals.allow_imm_inv,"enable the addition of immutability invariant for implication");
  ("--dis-imm-inv", Arg.Clear Globals.allow_imm_inv,"disable the additionof of immutability invariant for implication");
  ("--dis-inf", Arg.Clear Globals.allow_inf,"disable support for infinity ");
  ("--en-inf", Arg.Unit (fun _ ->
       Globals.allow_inf:=true;
       Globals.deep_split_disjuncts:=true
     ),"enable support for infinity (tgt with --dsd) ");
  ("--en-inf-qe", Arg.Unit( fun _ ->
       Globals.allow_inf := true;
       Globals.allow_inf_qe := true;
       (*Globals.early_contra_flag := false;
         Globals.simpl_unfold2 := true;
         Globals.simpl_unfold3 := true;*)
       (*Globals.elim_exists_flag := false;
         Globals.simplify_imply := false;
         Globals.filtering_flag := false;*)
       Globals.ann_vp := false;),
   "enable support for quantifier elimination in PAinfinity ");
  ("--en-inf-qe-coq", Arg.Unit( fun _ ->
       Globals.allow_inf := true;
       Globals.allow_norm := false;
       Globals.allow_inf_qe_coq := true;
       Globals.early_contra_flag := false;
       (*Globals.simpl_unfold2 := true;
         Globals.simpl_unfold3 := true;*)
       (*Globals.elim_exists_flag := false;*)
       (*Globals.simplify_imply := false;*)
       (*Globals.filtering_flag := false;*)
       Globals.ann_vp := false;),
   "use the quantifier elimination procedure implemented in coq for PAinfinity ");
  ("--en-inf-qe-coq-simp", Arg.Unit( fun _ ->
       Globals.allow_inf := true;
       Globals.allow_norm := false;
       Globals.allow_inf_qe_coq := true;
       Globals.allow_inf_qe_coq_simp := true;
       Globals.early_contra_flag := false;
       (*Globals.simpl_unfold2 := true;
         Globals.simpl_unfold3 := true;*)
       (*Globals.elim_exists_flag := false;*)
       (*Globals.simplify_imply := false;*)
       (*Globals.filtering_flag := false;*)
       Globals.ann_vp := false;),
   "use the quantifier elimination procedure with simplification implemented in coq for PAinfinity ");
  ("--en-qe-fix", Arg.Unit( fun _ ->
       Globals.allow_inf := true;
       Globals.allow_inf_qe := true;
       Globals.allow_qe_fix := true;),
   "use the quantifier elimination procedure for inference ");
  ("--dis-dsd", Arg.Clear Globals.deep_split_disjuncts,"disable deep splitting of disjunctions");
  ("--dsd", Arg.Set Globals.deep_split_disjuncts,"enable deep splitting of disjunctions");
  ("--en-disj-conseq", Arg.Set Globals.preprocess_disjunctive_consequence,"enable handle disjunctive consequence");
  ("--ioc", Arg.Set Globals.check_integer_overflow,"Enable Integer Overflow Checker");
  ("--no-coercion", Arg.Clear Globals.use_coercion,
   "Turn off coercion mechanism");
  ("--no-exists-elim", Arg.Clear Globals.elim_exists_ff,
   "Turn off existential quantifier elimination during type-checking");
  ("--no-diff", Arg.Set Solver.no_diff,
   "Drop disequalities generated from the separating conjunction");
  ("--no-set", Arg.Clear Globals.use_set,
   "Turn off set-of-states search");
  ("--unsat-elim", Arg.Set Globals.elim_unsat,
   "Turn on unsatisfiable formulae elimination during type-checking");
  ("--unsat-consumed", Arg.Set Globals.unsat_consumed_heap,
   "Add consumed heap for unsat checking");
  ("--en-disj-compute", Arg.Set Globals.disj_compute_flag,
   "Enable re-computation of user-supplied disj. invariant");
  ("--dis-comp-xp0", Arg.Clear Globals.compute_xpure_0,
   "Disable the computation of xpure 0");
  ("--dis-inv-wrap", Arg.Clear Globals.inv_wrap_flag,
   "Disable the wrapping of --lda for pred invariant proving");
  ("--dis-lhs-case", Arg.Clear Globals.lhs_case_flag,
   "Disable LHS Case Analysis");
  ("--en-lhs-case", Arg.Set Globals.lhs_case_flag,
   "Enable LHS Case Analysis");
  ("--en-infer-case-as-or", Arg.Set Globals.infer_case_as_or_flag,
   "Enable inferring CASE as OR");
  ("--dis-infer-case-as-or", Arg.Clear Globals.infer_case_as_or_flag,
   "Disable inferring CASE as OR");
  ("--en-lhs-case-search", Arg.Set Globals.lhs_case_search_flag,
   "Replace Cond_action by Search for LHS Case Analysis");
  ("-nxpure", Arg.Set_int Globals.n_xpure,
   "Number of unfolding using XPure");
  ("-mona-cycle", Arg.Set_int Mona.mona_cycle,
   "Number of times mona can be called before it restarts (default 90)");
  ("-v:", Arg.Set_int VarGen.verbose_num,
   "Verbosity level for Debugging");
  ("-fixcalc-disj", Arg.Set_int Globals.fixcalc_disj,
   "Number of disjunct for fixcalc computation");
  ("--dis-smart-xpure", Arg.Clear Globals.smart_xpure,
   "Smart xpure with 0 then 1; otherwise just 1 ; not handled by infer yet");
  ("--dis-precise-xpure", Arg.Clear Globals.precise_perm_xpure, "disable adding x!=y when the permissions of x and y overlap or exceed the full permission");
  ("--en-smart-memo", Arg.Set Globals.smart_memo,
   "Smart memo with no_complex; if fail try complex formula");
  ("--en-pre-residue", Arg.Unit (fun _ -> Globals.pre_residue_lvl := 1),
   "Always add pre inferred to residue, ee if it is disjunctive");
  ("--dis-pre-residue", Arg.Unit (fun _ -> Globals.pre_residue_lvl := -1),
   "Never pre inferred to residue, ee if it is conjunctive");
  (* default is to add only conjunctive pre to residue when
     pre_residue_lvl ==0 *)
  ("-num-self-fold-search", Arg.Set_int Globals.num_self_fold_search,
   "Allow Depth of Unfold/Fold Self Search");
  ("--en-self-fold", Arg.Set Globals.self_fold_search_flag,
   "Enable Limited Search with Self Unfold/Fold");
  ("--dis-self-fold", Arg.Clear Globals.self_fold_search_flag,
   "Disable Limited Search with Self Unfold/Fold");
  ("-parse", Arg.Set parse_only,"Parse only");
  ("--parser", Arg.Symbol (["default"; "cil"], Parser.set_parser), "Choose different parser: default; cil");
  ("--dump-ss", Arg.Set dump_ss, "Dump ss files");
  ("-core", Arg.Set typecheck_only,"Type-Checking and Core Preprocessing only");
  ("--print-iparams", Arg.Set Globals.print_mvars,"Print input parameters of predicates");
  ("--print-tidy", Arg.Set Globals.print_en_tidy,"enable tidy printing (with shorter names)");
  ("--dis-print-tidy", Arg.Clear Globals.print_en_tidy,"disable tidy printing (with shorter names)");
  ("--print-inline", Arg.Set Globals.print_en_inline,"enable printing (with fewer intermediates)");
  ("--dis-print-inline", Arg.Clear Globals.print_en_inline,"disable printing (with fewer intermediates)");
  ("--print-html", Arg.Set Globals.print_html,"enable html printing");
  ("--print-type", Arg.Set Globals.print_type,"Print type info");
  ("--print-extra", Arg.Set Globals.print_extra,"Print extra info");
  ("--dis-type-err", Arg.Clear Globals.enforce_type_error,"Give just warning for type errors");
  ("--en-type-err", Arg.Set Globals.enforce_type_error,"Stricly enforce type errors");
  ("--print-x-inv", Arg.Set Globals.print_x_inv,
   "Print computed view invariants");
  ("--print-en-relassume", Arg.Set Globals.print_relassume,
   "Enable printing of inferred relational assumptions (hip)");
  ("--print-dis-relassume", Arg.Clear Globals.print_relassume,
   "Disable printing of inferred relational assumptions (hip)");
  ("--print-cnv-null", Arg.Set Globals.print_cnv_null,
   "Print translation to convert null");
  ("--pr_str_assume", Arg.Set Globals.print_assume_struc, "Print structured formula for assume");
  ("-stop", Arg.Clear Globals.check_all,
   "Stop checking on erroneous procedure");
  ("--build-image", Arg.Symbol (["true"; "false"], Isabelle.building_image),
   "Build the image theory in Isabelle - default false");
  ("-tp", Arg.Symbol (["cvcl"; "cvc4"; "oc";"oc-2.1.6"; "co"; "isabelle"; "coq"; "mona"; "monah"; "z3"; "z3-2.19"; "z3n"; "z3-4.3.1"; "zm"; "om";
                       "oi"; "set"; "cm"; "OCRed"; "redlog"; "rm"; "prm"; "spass";"parahip"; "math"; "minisat" ;"auto";"log"; "dp"], (set_tp) (* Tpdispatcher.set_tp *)),
   "Choose theorem prover:\n\tcvcl: CVC Lite\n\tcvc4: CVC4\n\tomega: Omega Calculator (default)\n\tco: CVC4 then Omega\n\tisabelle: Isabelle\n\tcoq: Coq\n\tmona: Mona\n\tz3: Z3\n\tom: Omega and Mona\n\toi: Omega and Isabelle\n\tset: Use MONA in set mode.\n\tcm: CVC4 then MONA.");
  ("--dis-tp-batch-mode", Arg.Clear Tpdispatcher.tp_batch_mode,"disable batch-mode processing of external theorem provers");
  ("-perm", Arg.Symbol (["fperm"; "cperm"; "dperm"; "bperm"; "none"], Perm.set_perm),
   "Choose type of permissions for concurrency :\n\t fperm: fractional permissions\n\t cperm: counting permissions");
  ("--permprof", Arg.Set Globals.perm_prof, "Enable perm prover profiling (for distinct shares)");
  ("--en-split-fixcalc", Arg.Set Globals.split_fixcalc, "Enable split fixcalc (for infer post)");
  ("--dis-split-fixcalc", Arg.Clear Globals.split_fixcalc, "Disable split fixcalc (for infer post)");
  ("--dsf", Arg.Clear Globals.split_fixcalc, "Disable split fixcalc (for infer post)");
  ("--omega-interval", Arg.Set_int Omega.omega_restart_interval,
   "Restart Omega Calculator after number of proof. Default = 0, not restart");
  ("--use-field", Arg.Set Globals.use_field,
   "Use field construct instead of bind");
  ("--use-large-bind", Arg.Set Globals.large_bind,
   "Use large bind construct, where the bound variable may be changed in the body of bind");
  ("-infer", Arg.String (fun s ->
       Globals.infer_const_obj # set_init_arr s),"Infer constants e.g. @term@pre@post@imm@shape");  (* some processing to check @term,@post *)
  ("--ana-ni",Arg.Unit (fun () ->
       Globals.ptr_arith_flag := true;
       Globals.infer_const_obj # set INF_ANA_NI
     ),"Enable analysis of @NI");
  ("-debug", Arg.String (fun s ->
       Debug.z_debug_file:=s; z_debug_flag:=true),
   "Read from a debug log file");
  ("-prelude", Arg.String (fun s ->
       Globals.prelude_file:=Some s),
   "Read from a specified prelude file");
  ("-debug-regexp", Arg.String (fun s ->
       Debug.z_debug_file:=("$"^s); z_debug_flag:=true),
   "Match logged methods from a regular expression");
  ("-dre", Arg.String (fun s ->
       (* let _ = print_endline ("!!!-dre "^s) in *)
       Debug.z_debug_file:=("$"^s); z_debug_flag:=true;
       Debug.read_main ()
     ),
   "Shorthand for -debug-regexp");
  ("-show-push-list", Arg.String (fun s ->
       let _ = print_endline ("!!!-show-push-list "^s) in
       let () = Globals.show_push_list:=Some s in
       let () = if not(s="") then Globals.show_push_list_rgx := Some (Str.regexp s) in
       ()
     ),
   "Show all push-list with that name (reg-ex)");
  ("-drea", Arg.String (fun s ->
       Debug.z_debug_file:=("$.*"); z_debug_flag:=true;
       Debug.mk_debug_arg s),
   "Matched input/output with reg-exp");
  ("-dre-trace", Arg.String (fun s ->
       let _ = print_endline ("!!!-dre "^s) in
       Debug.z_debug_file:=("$"^s); z_debug_flag:=true;
       Debug.debug_pattern_on := true;
       Debug.dump_calls:=true;
       Debug.dump_calls_all:=true;
       Gen.debug_precise_trace:=true;
       Debug.debug_pattern := (Str.regexp s)),
   "Matched debug calls and its calees with reg-exp");
  ("-v", Arg.Set Debug.debug_on,
   "Verbose");
  ("--pipe", Arg.Unit Tpdispatcher.Netprover.set_use_pipe,
   "use external prover via pipe");
  ("--dsocket", Arg.Unit (fun () -> Tpdispatcher.Netprover.set_use_socket "loris-7:8888"),
   "<host:port>: use external prover via loris-7:8888");
  ("--socket", Arg.String Tpdispatcher.Netprover.set_use_socket,
   "<host:port>: use external prover via socket");
  ("--prover", Arg.String (Tpdispatcher.set_tp true),
   "<p,q,..> comma-separated list of provers to try in parallel");
  (* ("--enable-sat-stat", Arg.Set Globals.enable_sat_statistics,  *)
  (* "enable sat statistics"); *)
  ("--en-pstat", Arg.Set Gen.profiling,
   "enable profiling statistics");
  ("--en-cstat", Arg.Set Gen.enable_counters, "enable counter statistics");
  ("--dis-time-stat", Arg.Clear Globals.enable_time_stats, "disable timing statistics from being printed");
  ("--dis-count-stat", Arg.Clear Globals.enable_count_stats, "disable counting statistics from being printed");
  ("--en-stat", (Arg.Tuple [Arg.Set Gen.profiling; Arg.Set Gen.enable_counters]),
   "enable all statistics");
  ("--sbc", Arg.Set Globals.enable_syn_base_case,
   "use only syntactic base case detection");
  ("--dbc", Arg.Set Globals.dis_base_case_unfold, "explicitly disable base case unfold");
  ("--dis-simpl-view-norm" , Arg.Clear Globals.simplified_case_normalize,
   "disable simplified view def normalization");
  ("--eci", Arg.Set Globals.enable_case_inference,
   "enable struct formula inference");
  ("--dci", Arg.Clear Globals.enable_case_inference,
   "disable struct formula inference");
  ("--pcp", Arg.Set Globals.print_core,
   "print core representation");
  ("--pip", Arg.Set Globals.print_input,
   "print input representation");
  ("--pcil", Arg.Set Globals.print_cil_input,
   "print cil representation");
  ("--pcp-all", Arg.Set Globals.print_core_all,
   "print core representation (including primitive library)");
  ("--pip-all", Arg.Set Globals.print_input_all,
   "print input representation (including primitive library)");
  (* ("--dis-cache", Arg.Set Globals.no_cache_formula, *)
  (* "Do not cache result of satisfiability and validity checking"); *)
  ("--dis-cache", Arg.Set Globals.no_cache_formula,
   "Disable Caching result of satisfiability and validity checking");
  ("--en-cache", Arg.Clear Globals.no_cache_formula,
   "Cache result of satisfiability and validity checking");
  ("--dis-simplify-imply", Arg.Clear Globals.simplify_imply,
   "Simplification of existential for imply calls");
  ("--web", Arg.String (fun s -> (Tpdispatcher.Netprover.set_use_socket_for_web s); Tpdispatcher.webserver := true; Typechecker.webserver := true; Paralib1v2.webs := true; Paralib1.webs := true) ,
   "<host:port>: use external web service via socket");
  ("-para", Arg.Int Typechecker.parallelize,
   "Use Paralib map_para instead of List.map in typecheker");
  ("--priority",Arg.String Tpdispatcher.Netprover.set_prio_list,
   "<proc_name1:prio1;proc_name2:prio2;...> To be used along with webserver");
  ("--decrprio",Arg.Set Tpdispatcher.decr_priority ,
   "use a decreasing priority scheme");
  ("--rl-no-pseudo-ops", Arg.Clear Redlog.no_pseudo_ops,
   "Do not pseudo-strengthen/weaken formulas before send to Redlog");
  ("--rl-no-ee", Arg.Set Redlog.no_elim_exists,
   "Do not try to eliminate existential quantifier with Redlog");
  ("--rl-no-simplify", Arg.Set Redlog.no_simplify,
   "Do not try to simplify non-linear formulas with Redlog");
  ("--rl-cache", Arg.Clear Redlog.no_cache,
   "Use cache for unsatisfiability and implication's checking with Redlog");
  ("--rl-timeout", Arg.Set_float Redlog.timeout,
   "Set timeout (in seconds) for is_sat or imply with Redlog");
  ("--failure-analysis",Arg.Set Globals.failure_analysis,
   "Turn on failure analysis");
  ("--exhaust-match",Arg.Set Globals.exhaust_match,
   "Turn on exhaustive matching for base case of predicates");
  ("--use-tmp",Arg.Unit set_tmp_files_path,
   "Use a local folder located in /tmp/your_username for the prover's temporary files");
  ("--esn", Arg.Set Globals.enable_norm_simp, "enable simplifier in fast imply");
  (* ("--eps", Arg.Set Globals.allow_pred_spec, "enable predicate specialization together with memoized formulas"); *)
  ("-version", Arg.Set Globals.print_version_flag,"current version of software");
  (* ("--dfe", Arg.Set Globals.disable_failure_explaining,"disable failure explaining"); *)
  ("--en-failure-analysis", Arg.Clear Globals.disable_failure_explaining,"enable failure explanation analysis");
  ("--efa", Arg.Clear Globals.disable_failure_explaining,"shorthand for --en-failure-analysis");
  ("--efa-exc", Arg.Set Globals.enable_error_as_exc,"enable to transform error as exception");
  ("--dis-efa-exc", Arg.Clear Globals.enable_error_as_exc,"disable to transform error as exception");
  ("--efa-may", Arg.Unit
     (fun _ ->
        Globals.infer_const_obj # set INF_ERR_MAY
     ),"set may error scenrio as default");
  ("--dfa", Arg.Set Globals.disable_failure_explaining,"shorthand for --dis-failure-analysis");
  ("--refine-error", Arg.Set Globals.simplify_error,
   "Simplify the error");
  (*("--redlog-int-relax", Arg.Set Redlog.integer_relax_mode, "use redlog real q.e to prove intefer formula  *experiment*");*)
  (*("--redlog-ee", Arg.Set Redlog.is_ee, "enable Redlog existential quantifier elimination");*)
  ("--redlog-presburger", Arg.Set Redlog.is_presburger, "use presburger arithmetic for redlog");
  ("--redlog-timeout", Arg.Set_float Redlog.timeout, "<sec> checking a formula using redlog with a timeout after <sec> seconds");
  (*("--redlog-manual", Arg.Set Redlog.manual_mode, " manual config for reduce/redlog");*)
  (*("--dpc", Arg.Clear Globals.enable_prune_cache,"disable prune caching");*)
  ("--dis-elimrc", Arg.Set Globals.disable_elim_redundant_ctr, "disable redundant constraint elimination in memo pure");
  ("--esi",Arg.Set Globals.enable_strong_invariant, "enable strong predicate invariant");
  ("--en-red-elim", Arg.Set Globals.enable_redundant_elim, "enable redundant elimination under eps");
  ("--eap", Arg.Set Globals.enable_aggressive_prune, "enable aggressive prunning");
  ("--constr-filter", Arg.Set Globals.enable_constraint_based_filtering, "Enable assumption filtering based on contraint type");
  (* ("--dap", Arg.Clear Globals.disable_aggressive_prune, "never use aggressive prunning"); *)
  ("--efp",Arg.Set Globals.enable_fast_imply, " enable fast imply only for --eps pruning; incomplete");
  (* ("--dfp",Arg.Clear Globals.enable_fast_imply, " disable syntactic imply only for --eps"); *)
  ("-memo-print", Arg.Set_int Globals.memo_verbosity,
   "level of detail in memo printing 0-verbose 1-brief 2-standard(default)");
  ("--increm",Arg.Set Globals.enable_incremental_proving, " enable incremental proving ");
  ("--en-null-aliasing", Arg.Set Globals.enulalias, "enable null aliasing ");
  (*for cav experiments*)
  (*maintains one slice if memo formulas are used otherwise has no effect*)
  ("--force-one-slice", Arg.Set Globals.f_1_slice,"use one slice for memo formulas");
  ("--force-no-memo", Arg.Set Globals.no_memoisation,"");
  ("--no-incremental", Arg.Set Globals.no_incremental,"");
  ("--no-LHS-prop-drop", Arg.Set Globals.no_LHS_prop_drop,"");
  ("--no-RHS-prop-drop", Arg.Set Globals.no_RHS_prop_drop,"");
  (* if memo formulas are not used, use a similar slicing for unsat checks at the Tpdispatcher *)
  ("--force-sat-slice", Arg.Set Globals.do_sat_slice, "for no eps, use sat slicing");
  (*maintains multi slices but combines them into one slice just before going to the prover
    in Tpdispatcher. If memo formulas are not used it has no effect*)
  ("--force-one-slice-proving" , Arg.Set Globals.f_2_slice,"use one slice for proving (sat, imply)");

  (* String Inference *)
  ("--old-pred-synthesis", Arg.Clear Globals.new_pred_syn, "Disable new predicate synthesis");
  ("--ops", Arg.Clear Globals.new_pred_syn, "Disable new predicate synthesis");
  ("--new-pred-synthesis", Arg.Set Globals.new_pred_syn, "Enable new predicate synthesis");
  ("--en-pred-elim-node", Arg.Set Globals.pred_elim_node, "Eliminate common nodes in derived predicates");
  ("--dis-pred-elim-node", Arg.Clear Globals.pred_elim_node, "Disable common nodes elimination in derived predicates");

  (* Template *)
  ("--dis-norm", Arg.Set Globals.dis_norm, "Disable arithmetic normalization");
  ("-lp", Arg.Symbol ([ "z3"; "clp"; "glpk"; "lps"; "oz3"; "oclp"; "oglpk"; "olps" ],
                      Tlutils.set_solver), "Choose LP solver");
  ("--piecewise", Arg.Set Globals.templ_piecewise, "Enable piecewise function inference");
  ("--dis-ln-z3", Arg.Set Globals.dis_ln_z3, "Disable linearization on Z3 (using non-linear engine)");

  (* Termination options *)
  ("--dis-term-check", Arg.Set Globals.dis_term_chk, "turn off the termination checking");
  ("--term-verbose", Arg.Set_int Globals.term_verbosity,
   "level of detail in termination printing 0-verbose 1-standard(default)");
  ("--dis-call-num", Arg.Set Globals.dis_call_num, "turn off the automatic call numbering");
  ("--dis-phase-num", Arg.Set Globals.dis_phase_num, "turn off the automatic phase numbering");
  ("--term-reverify", Arg.Set Globals.term_reverify,
   "enable re-verification for inferred termination specifications");
  ("--term-en-bnd-pre", Arg.Set Globals.term_bnd_pre_flag,
   "enable boundedness check at pre-condition");
  ("--term-dis-bnd-pre", Arg.Clear Globals.term_bnd_pre_flag,
   "disable boundedness check at pre-condition (boundedness check at recursive call)");
  ("--dis-bnd-check", Arg.Set Globals.dis_bnd_chk, "turn off the boundedness checking");
  ("--dis-term-msg", Arg.Set Globals.dis_term_msg, "turn off the printing of termination messages");
  ("--dis-post-check", Arg.Set Globals.dis_post_chk, "turn off the post_condition and loop checking");
  ("--post-eres", Arg.Set Globals.post_add_eres, "add res=eres.val for post-condition proving");
  ("--add-pre", Arg.Set Globals.add_pre, "to add pre of case-spec into post-cond");
  ("--dis-add-pre", Arg.Clear Globals.add_pre, "not to add pre of case-spec into post-cond");
  ("--post-flow", Arg.Set Globals.post_infer_flow, "add exception flow as a post-cond parameter for inference");
  ("--dis-post-flow", Arg.Clear Globals.post_infer_flow, "add exception flow as a post-cond parameter for inference");
  ("--dis-assert-check", Arg.Set Globals.dis_ass_chk, "turn off the assertion checking");
  ("--dis-log-filter", Arg.Clear Globals.log_filter, "turn off the log initial filtering");
  ("--en-weaken-rel", Arg.Set Globals.oc_weaken_rel_flag, "Enable weakening of relation");
  ("--dis-weaken-rel", Arg.Clear Globals.oc_weaken_rel_flag, "Disable weakening of relation");

  (* TermInf: Options for Termination Inference *)
  ("--en-gen-templ-slk", Arg.Set Globals.gen_templ_slk, "Generate sleek file for template inference");
  ("--gts", Arg.Set Globals.gen_templ_slk, "shorthand for --en-gen-templ-slk");
  ("--tnt-verbose", Arg.Set_int Globals.tnt_verbosity,
   "level of detail in termination inference printing 0-verbose 1-standard (default)");
  ("--infer-lex", Arg.Set Globals.tnt_infer_lex,
   "enable lexicographic ranking function inference");
  ("--en-infer-lex", Arg.Set Globals.tnt_infer_lex,
   "enable lexicographic ranking function inference");
  ("--dis-infer-lex", Arg.Clear Globals.tnt_infer_lex,
   "disable lexicographic ranking function inference");
  ("--term-add-post", Arg.Set Globals.tnt_add_post, "Automatically infer necessary postcondition");
  ("--dis-term-add-post", Arg.Clear Globals.tnt_add_post, "Automatically infer necessary postcondition");
  ("--abd-strategy", Arg.Set_int Globals.tnt_abd_strategy,
   "level of detail in termination printing 0-template(default) 1-size-change");
  ("--en-infer-nondet", Arg.Set Globals.tnt_infer_nondet,
   "enable local inference for nondeterminism");
  ("--dis-infer-nondet", Arg.Clear Globals.tnt_infer_nondet,
   "disable local inference for nondeterminism");
  ("--tnt-max-iter", Arg.Set_int Globals.tnt_thres,
   "maximum number of iteration on TNT algorithm");

  (* Slicing *)
  ("--auto-eps", Arg.Set Globals.auto_eps_flag, "Enable automatic proof slicing for mona");
  ("--dis-auto-eps", Arg.Clear Globals.auto_eps_flag, "Disable automatic proog slicing for mona");
  ("--eps", Arg.Set Globals.en_slc_ps, "Enable slicing with predicate specialization");
  ("--dis-eps", Arg.Clear Globals.en_slc_ps, "Disable slicing with predicate specialization");
  ("--overeps", Arg.Set Globals.override_slc_ps, "Override --eps, for run-fast-tests testing of modular examples");
  ("--dis-ps", Arg.Set Globals.dis_ps, "Disable predicate specialization");
  ("--dis-ann", Arg.Set Globals.dis_slc_ann, "Disable aggressive slicing with annotation scheme (not default)");
  ("--slc-rel-level", Arg.Set_int Globals.slicing_rel_level, "Set depth for GetCtr function");
  ("--slc-ann-ineq", Arg.Set Globals.opt_ineq, "Enable inference of agressive slicing with inequalities");
  ("--slc-lvar-infer", Arg.Set Globals.infer_lvar_slicing, "Enable linking variable inference of agressive slicing");
  ("--dis-oc", Arg.Set Redlog.dis_omega, "Disable Omega when Redlog is invoked");

  (* ("--en-slicing", Arg.Set Globals.do_slicing, "Enable forced slicing"); *)
  (* ("--dis-slicing", Arg.Set Globals.dis_slicing, "Disable slicing, equivalent to "); *) (* similar to --force-one-slice *)
  (* ("--slc-opt-imply", Arg.Set_int Globals.opt_imply, "Enable optimal implication for forced slicing"); *) (* not used *)
  ("--slc-multi-provers", Arg.Set Globals.multi_provers, "Enable multiple provers for proving multiple properties");
  ("--slc-sat-slicing", Arg.Set Globals.is_sat_slicing, "Enable slicing before sending formulas to provers");
  (* similar to --force-sat-slice when no memo formula used *)
  ("--slc-ann-infer", Arg.Set Globals.infer_slicing, "Enable slicing label inference");
  ("--delay-case-sat", Arg.Set Globals.delay_case_sat, "Disable unsat checking for case entailment");
  ("--force-post-sat", Arg.Set Globals.force_post_sat, "Force unsat checking when assuming a postcondition");
  ("--delay-if-sat", Arg.Set Globals.delay_if_sat, "Disable unsat checking for a conditional");
  ("--delay-proving-sat", Arg.Set Globals.delay_proving_sat, "Disable unsat checking prior to proving requires");
  ("--delay-assert-sat", Arg.Set Globals.disable_assume_cmd_sat, "Disable unsat checking done at an ASSUME COMMAND");
  ("--en-precond-sat", Arg.Clear Globals.disable_pre_sat, "Enable unsat checking of method preconditions");

  (* HO predicate *)
  ("--ho-always-split", Arg.Set Globals.ho_always_split, "Apply lemma_split when possible at par/thread");
  ("--en-contra-ho", Arg.Set Globals.contra_ho_flag, "Enable Contra HO Instantiation");
  ("--dis-contra-ho", Arg.Clear Globals.contra_ho_flag, "Disable Contra HO Instantiation");
  ("--dis-ho-always-split", Arg.Clear Globals.ho_always_split, "Disable selective apply of lemma_split");

  (* Proof Logging *)
  ("--en-logging", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true; Globals.proof_logging:=true ), "Enable proof logging");
  ("--en-logging-txt", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true ), "Enable proof logging into text file");
  ("--dump-proof", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true; Globals.dump_proof:=true
     ), "Dump proof log at end of command");
  ("--epl", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true ), "Shorthand for --en-logging-txt");
  ("--dis-proof-details", Arg.Unit (fun _ ->
       Globals.log_proof_details:=false ), "Disable proof strings to be recorded");
  ("--en-proof-details", Arg.Unit (fun _ ->
       Globals.log_proof_details:=true ), "Enable proof strings to be recorded");
  ("--epd", Arg.Unit (fun _ ->
       Globals.log_proof_details:=true ), "Shorthand for --en-proof-details");
  ("--en-slk-logging", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true;
       Globals.sleek_logging_txt:=true), "Enable sleek and proof logging with text file");
  ("--esl", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true;
       Globals.sleek_logging_txt:=true
     ), "Shorthand for --en-slk-logging");
  ("--esl-all", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true;
       Globals.sleek_logging_txt:=true;
       Globals.sleek_log_all := true
     ), "Shorthand for --en-slk-logging");
  ("--dump-slk-proof", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true;
       Globals.sleek_logging_txt:=true;
       Globals.dump_sleek_proof:=true
     ), "Dump sleek proof log at end of command");
  ("--gen-vc", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true;
       Globals.sleek_logging_txt:=true;
       Globals.sleek_gen_vc:=true
     ), "Generate verification condition with frame in sleek format");
  ("--gen-vc-exact", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true;
       Globals.sleek_logging_txt:=true;
       Globals.sleek_gen_vc_exact:=true
     ), "Generate exact verification condition in sleek format");
  ("--gen-sat", Arg.Unit (fun _ ->
       Globals.proof_logging_txt:=true;
       Globals.sleek_logging_txt:=true;
       Globals.sleek_gen_sat:=true
     ), "Generate check sat formula");
  (* abduce pre from post *)
  ("--abdfpost", Arg.Set Globals.do_abd_from_post, "Enable abduction from post-condition");
  (* incremental spec *)
  ("--inc", Arg.Set Globals.do_infer_inc, "Enable incremental spec inference");
  (* invariant *)
  ("--inv-test", Arg.Set Globals.do_test_inv, "Enable explicit checking of invariant (for run-fast-test)");
  ("--dis-inv-test", Arg.Clear Globals.do_test_inv, "Disable explicit checking of invariant (for run-fast-test)");
  ("--inv", Arg.Set Globals.do_infer_inv, "Enable invariant inference");
  ("--en-unexpected",Arg.Set Globals.show_unexpected_ents,"displays unexpected results");
  ("--dis-unexpected",Arg.Clear Globals.show_unexpected_ents,"do not show unexpected results");
  ("--double-check",Arg.Set Globals.double_check,"double checking new syn baga");
  ("--dis-double-check",Arg.Clear Globals.double_check,"disable double-checking new syn baga");
  ("--use-baga",Arg.Set Globals.use_baga,"use baga only (no inv infer)");
  ("--dis-use-baga",Arg.Clear Globals.use_baga,"disable use baga only (no inv infer)");
  (* ("--inv-baga",Arg.Set Globals.gen_baga_inv,"generate baga inv from view"); *)
  ("--inv-baga",Arg.Unit (fun _ ->  Globals.use_baga := true; Globals.gen_baga_inv := true),"generate baga inv from view");
  ("--dis-inv-baga",Arg.Clear Globals.gen_baga_inv,"disable baga inv from view");
  ("--en-delay-eelim",Arg.Set Globals.delay_eelim_baga_inv,"delay simplification during inference of shape baga inv");
  ("--dis-inv-check",Arg.Set Globals.dis_baga_inv_check,"disable dis_baga_inv_check");
  ("--pred-sat", Arg.Unit Globals.en_pred_sat ," turn off oc-simp for pred sat checking");
  ("--baga-xpure",Arg.Set Globals.use_baga (* Globals.baga_xpure *),"use baga for xpure");
  ("--dis-baga-xpure",Arg.Clear Globals.use_baga (* Globals.baga_xpure *),"do not use baga for xpure");
  (* ("--inv-baga",Arg.Set Globals.gen_baga_inv,"generate baga inv from view"); *)
  ("--dis-imm-baga",Arg.Clear Globals.baga_imm,"disable baga inv from view");
  ("--en-imm-baga",Arg.Clear Globals.baga_imm,"disable baga inv from view");

  ("--prove-invalid",Arg.Set Globals.prove_invalid,"enable prove invalid");
  ("--dis-prove-invalid",Arg.Clear Globals.prove_invalid,"disable prove invalid");

  (* use classical reasoning in separation logic *)
  ("--classic",
   Arg.Unit (fun _ -> Globals.infer_const_obj # set Globals.INF_CLASSIC),
   (* Arg.Set Globals.opt_classic,  *)
   "Use classical reasoning in separation logic");
  ("--dis-classic",
   Arg.Unit (fun _ -> Globals.infer_const_obj # reset Globals.INF_CLASSIC),
   (* Arg.Clear Globals.opt_classic,  *)
   "Disable classical reasoning in separation logic");
  ("--dis-split", Arg.Set Globals.use_split_match, "Disable permission splitting lemma (use split match instead)");
  ("--old-lemma-settings", Arg.Unit (fun _ ->
       Globals.old_norm_w_coerc := true;
       Globals.old_univ_lemma := true;
       Globals.old_search_always := true;
     ), "Allow old lemma settings");
  ("--old-norm-w-coerc", Arg.Set Globals.old_norm_w_coerc, "Allow old normalize formula with coercions (may loop)");
  ("--lem-en-norm", Arg.Set Globals.allow_lemma_norm, "Allow case-normalize for lemma");
  ("--lem-dis-norm", Arg.Clear Globals.allow_lemma_norm, "Disallow case-normalize for lemma");
  ("--lem-en-fold", Arg.Set Globals.allow_lemma_fold, "Allow do_fold with right lemma");
  ("--en-rd-lemma", Arg.Set Globals.allow_rd_lemma, "Enable rd-lemma");
  ("--lem-dis-fold", Arg.Clear Globals.allow_lemma_fold, "Disable do_fold with right lemma");
  ("--lem-en-switch", Arg.Set Globals.allow_lemma_switch, "Allow lhs/lhs switching for Lemma Proving");
  ("--lem-dis-switch", Arg.Clear Globals.allow_lemma_switch, "Disallow lhs/lhs switching for Lemma Proving");
  ("--lem-en-deep-unfold", Arg.Set Globals.allow_lemma_deep_unfold, "Allow deep unfold for Lemma Proving");
  ("--lem-dis-deep-unfold", Arg.Clear Globals.allow_lemma_deep_unfold, "Disallow deep unfold for Lemma Proving");
  ("--lem-en-residue", Arg.Set Globals.allow_lemma_residue, "Allow residue for Lemma Proving");
  ("--lem-dis-residue", Arg.Clear Globals.allow_lemma_residue, "Disallow residue for Lemma Proving");
  ("--lem-dis-lhs-unfold", Arg.Clear Globals.enable_lemma_lhs_unfold, "Disable LHS unfold for Lemma Proving");
  ("--lem-en-lhs-unfold", Arg.Set Globals.enable_lemma_lhs_unfold, "Enable LHS unfold for Lemma Proving");
  ("--lem-dis-unk-unfold", Arg.Clear Globals.enable_lemma_unk_unfold, "Disable unknown heap unfold for Lemma Proving");
  ("--lem-en-unk-unfold", Arg.Set Globals.enable_lemma_unk_unfold, "Enable unknown heap unfold for Lemma Proving");
  ("--ulhs", Arg.Set Globals.enable_lemma_lhs_unfold, "Shortcut for --lem-en-lhs-unfold");
  ("--urhs", Arg.Set Globals.enable_lemma_rhs_unfold, "Shortcut for --lem-en-rhs-unfold");
  ("--lem-en-rhs-unfold", Arg.Set Globals.enable_lemma_rhs_unfold, "Enable RHS unfold for Lemma Proving");
  ("--lem-dis-rhs-unfold", Arg.Clear Globals.enable_lemma_rhs_unfold, "Disable RHS unfold for Lemma Proving");
  ("--en-lemma-s", Arg.Set Globals.enable_split_lemma_gen, "Enable automatic generation of splitting lemmas");
  ("--en-smart-lem-search", Arg.Set Globals.smart_lem_search, "Activate a smart heuristic for lemma search");
  ("--dis-smart-lem-search", Arg.Clear Globals.smart_lem_search, "Use naive heuristic for lemma search");
  ("--en-ctx-norm", Arg.Set Globals.en_norm_ctx,    "Enable  - merge identical residual states based on syntactic checking");
  ("--dis-ctx-norm", Arg.Clear Globals.en_norm_ctx, "Disable - merge identical residual states based on syntactic checking");
  ("--en-trec2lin", Arg.Set Globals.en_trec_lin,    "Enable  - conversion of tail-recursive defs to linear form");
  ("--dis-trec2lin", Arg.Clear Globals.en_trec_lin, "Disable - conversion of tail-recursive defs to linear form");
  ("--dis-show-diff", Arg.Set Globals.dis_show_diff, "Show differences between formulae");
  ("--dis-sem", Arg.Set Globals.dis_sem, "Show differences between formulae");
  ("--en-cp-trace", Arg.Set Globals.cond_path_trace, "Enable the tracing of conditional paths");
  ("--dis-cp-trace", Arg.Clear Globals.cond_path_trace, "Disable the tracing of conditional paths");
  (* WN: Please use longer meaningful variable names *)
  ("--sa-ep", Arg.Set VarGen.sap, "Print intermediate results of normalization");
  ("--sa-en-part", Arg.Set Globals.sa_part, "enable partition parameters into rele groups");
  ("--sa-dis-part", Arg.Clear Globals.sa_part, "disable partition parameters into rele groups");
  ("--sa-dp", Arg.Clear VarGen.sap, "disable Printing intermediate results of normalization");
  ("--sa-prefix-pred", Arg.Clear Globals.sa_prefix_emp, "disable pre-condition fixpoint as empty during shape analysis");
  ("--dis-infer-heap", Arg.Clear Globals.fo_iheap, "disable first-order infer_heap");
  ("--sa-error", Arg.Set Globals.sae, "infer error spec");
  ("--sa-dis-error", Arg.Clear Globals.sae, "disable to infer error spec");
  ("--sa-case", Arg.Set Globals.sac, "combine case spec");
  ("--sa-dis-case", Arg.Clear Globals.sac, "disable to combine case spec");
  ("--sa-gen-spec", Arg.Set Globals.sags, "enable generate spec with unknown preds for inference");
  ("--gsf", Arg.Set Globals.sa_gen_slk, "shorthand for -sa-gen-sleek-file");
  ("--gff", Arg.Set Globals.gen_fixcalc, "shorthand for gen-fixcalc-file");
  ("--sa-gen-sleek-file", Arg.Set Globals.sa_gen_slk, "gen sleek file after split_base");
  ("--sa-en-cont", Arg.Set Globals.norm_cont_analysis, "enable cont analysis for views");
  ("--sa-dis-cont", Arg.Clear Globals.norm_cont_analysis, "disable cont analysis for views");
  ("--en-sep-pure-fields", Arg.Set Globals.sep_pure_fields, "separate pure fields in unknown heap predicates");
  ("--dis-sep-pure-fields", Arg.Clear Globals.sep_pure_fields, "combine pure fields in unknown heap predicates");
  ("--pred-dis-mod", Arg.Clear Globals.pred_syn_modular, "disable modular predicate synthesis (use old algo)");
  ("--pred-en-mod", Arg.Set Globals.pred_syn_modular, "using modular predicate synthesis");
  ("--en-syn-mode", Arg.Set Globals.syntatic_mode, "check two formulas are equivalent syntatically. default is semantic checking via sleek");
  ("--pred-en-oblg", Arg.Set Globals.pred_en_oblg, "enable sa_en_pre_oblg");
  ("--pred-dis-oblg", Arg.Clear Globals.pred_en_oblg, "enable sa_en_pre_oblg");
  ("--sa-dnc", Arg.Set Globals.sa_dnc, "algorithm of normalization with divide and conquer");
  (* ("--sa-en-norm", Arg.Set Globals.sa_en_norm, "do normalization"); *)
  (* ("--sa-dis-infer", Arg.Clear Globals.sa_en, "do not infer shape"); *)
  (* ("--sa-dis-pred", Arg.Clear Globals.sa_en, "do not synthesize shape"); *)
  ("--en-pred-syn", Arg.Set Globals.pred_syn_flag, "enable predicate synthesis");
  ("--dis-pred-syn", Arg.Clear Globals.pred_syn_flag, "disable predicate synthesis");
  ("--dps", Arg.Clear Globals.pred_syn_flag, "shorthand for --dis-pred-syn");
  (* ("--sa-dangling", Arg.Set Globals.sa_dangling, "elim dangling HP/pointers"); *)
  ("--inf-en-split-ante", Arg.Set Globals.infer_deep_ante_flag, "enable deep split of ante for pure inference");
  ("--iesa", Arg.Set Globals.infer_deep_ante_flag, "shorthand for --inf-en-split-ante");
  ("--inf-dis-split-ante", Arg.Clear Globals.infer_deep_ante_flag, "disable deep split of ante for pure inference");
  ("--pred-dis-infer", Arg.Clear Globals.sa_syn, "disable the shape inference stage");
  ("--lem-en-syn", Arg.Set Globals.lemma_syn, "enable the lemma synthesis");
  ("--lem-gen-safe", Arg.Set Globals.lemma_gen_safe, "enable generating (and proving) both fold and unfold lemmas for special predicates");
  ("--lem-gen-safe-fold", Arg.Set Globals.lemma_gen_safe_fold, "enable generating (and proving) fold lemmas for special predicates");
  ("--lem-gen-unsafe", Arg.Set Globals.lemma_gen_unsafe, "enable generating (without proving) both fold and unfold lemmas for special predicates");
  ("--lem-rev-unsafe", Arg.Set Globals.lemma_rev_unsafe, "enable generating (without proving) both rev lemmas for special predicates");
  ("--lem-gen-unsafe-fold", Arg.Set Globals.lemma_gen_unsafe_fold, "enable generating (without proving) fold lemmas for special predicates");
  ("--en-acc-fold", Arg.Set Globals.acc_fold, "enable accelerated folding");
  ("--seg-fold", Arg.Set Globals.seg_fold, "enable seg folding");
  ("--dis-acc-fold", Arg.Clear Globals.acc_fold, "disable accelerated folding");
  ("--elg", Arg.Set Globals.lemma_gen_unsafe, "enable lemma generation (lem-gen-unsafe)");
  ("--dlg",
   Arg.Unit
     (fun _ ->
        Globals.lemma_gen_unsafe := false; Globals.lemma_gen_unsafe_fold := false;
        Globals.lemma_gen_safe := false; Globals.lemma_gen_safe_fold := false
     ),
   "disable lemma generation (--dis-lem-gen)");
  ("--dis-lem-gen",
   Arg.Unit
     (fun _ ->
        Globals.lemma_gen_unsafe := false; Globals.lemma_gen_unsafe_fold := false;
        Globals.lemma_gen_safe := false; Globals.lemma_gen_safe_fold := false
     ),
   "disable lemma generation");
  ("--en-cyc-check", Arg.Set Globals.cyc_proof_syn, "enable the detection of cyclic proof syntatically");
  ("--dis-cyc-check", Arg.Clear Globals.cyc_proof_syn, "disable the detection of cyclic proof syntatically");
  ("--pred-en-useless-para", Arg.Set Globals.pred_elim_useless, "enable the elimination of useless parameter from HP predicate and user-defined predicates (view)");
  ("--pred-dis-useless-para", Arg.Clear Globals.pred_elim_useless, "disable the elimination of useless parameter from HP predicate and user-defined predicates (view)");
  ("--pred-en-dangling", Arg.Set Globals.pred_elim_dangling, "enable the elimination of dangling predicate from derived HP defns");
  ("--pred-dis-dangling", Arg.Clear Globals.pred_elim_dangling, "disable the elimination of dangling predicate from derived HP defns");
  ("--pred-dtv", Arg.Clear Globals.pred_trans_view, "disable trans HP defns to view after synthesis");
  ("--sa-refine-dang", Arg.Set Globals.sa_refine_dang, "refine dangling among branches of one hprels def");
  (* ("--sa-inlining", Arg.Set Globals.sa_inlining, "inline dangling HP/pointers"); *)
  ("--pred-en-eup", Arg.Set Globals.pred_elim_unused_preds, "enable the elimination of unused hprel predicates");
  ("--pred-dis-eup", Arg.Clear Globals.pred_elim_unused_preds, "disable the elimination of unused hprel predicates");
  ("--sa-en-pure-field",
   (*  Arg.Set Globals.sa_pure_field *)
   Arg.Unit
     ( fun _ ->
         Globals.infer_const_obj # set Globals.INF_PURE_FIELD
     ), "enable the inference of pure field property");
  ("--sa-dis-pure-field",
   Arg.Unit
     ( fun _ ->
         Globals.infer_const_obj # reset Globals.INF_PURE_FIELD
     ),"disable the inference of pure field property");
  ("--sa-ext", Arg.Set Globals.sa_ex, "enable the inference of shape and pure property (predicate level)");
  ("--sa-pure", Arg.Set Globals.sa_pure, "enable the inference of shape and pure property");
  ("--sa-dis-ext", Arg.Clear Globals.sa_ex, "disable the inference of shape and pure property");
  ("--sa-en-sp-split", Arg.Set Globals.sa_sp_split_base, "enable special base case split at entailment");
  ("--sa-dis-sp-split", Arg.Clear Globals.sa_sp_split_base, "disable special base case split at entailment");
  ("--sa-en-split", Arg.Set Globals.sa_infer_split_base, "enable base case splitting of relational assumption at shape infer");
  ("--sa-dis-split", Arg.Clear Globals.sa_infer_split_base, "disable base case splitting of relational assumption at shape infer");
  ("--sa-fb", Arg.Set_int Globals.sa_fix_bound, "number of loops for fixpoint");
  ("--pred-en-split", Arg.Set Globals.pred_split, "splitting hp args into multiple hp if possible");
  ("--pred-dis-seg-split", Arg.Clear Globals.pred_seg_split, "disable segmentation");
  ("--sa-unify-dangling", Arg.Set Globals.sa_unify_dangling, "unify branches of definition to instantiate dangling predicate");
  ("--pred-disj-unify", Arg.Set Globals.pred_disj_unify, "attempt to unify two similar predicates among inferred pred defs");
  ("--pred-seg-unify", Arg.Set Globals.pred_seg_unify, "attempt to segmentation pred defs");
  ("--pred-conj-unify", Arg.Set Globals.pred_conj_unify, "attempt to conj-unify among inferred assumption");
  ("--pred-en-equiv", Arg.Set Globals.pred_equiv, "attempt to reuse predicates with identical definition");
  ("--pred-dis-equiv", Arg.Clear Globals.pred_equiv, "disable reuse of predicates with identical definition");
  ("--pred-en-seg", Arg.Set Globals.pred_norm_seg, "attempt to seg predicates");
  ("--pred-dis-seg", Arg.Clear Globals.pred_norm_seg, "disable seg of predicates");
  ("--pred-unify-post", Arg.Set Globals.pred_unify_post, "unify (branches, syntax) definition of post-predicates");
  ("--pred-unify-inter", Arg.Set Globals.pred_unify_inter, "unify inter definition of predicates. before inlining");
  ("--pred-dis-unify-inter", Arg.Clear Globals.pred_unify_inter, "disable unify inter definition of predicates. before inlining");
  ("--sa-tree-simp", Arg.Set Globals.sa_tree_simp, "simplify a tree branches of definition");
  ("--sa-subsume", Arg.Set Globals.sa_subsume, "use subsume when comparing definitions after infering");
  (* ("--norm-useless", Arg.Set Globals.norm_elim_useless, "elim useless parameters of user-defined predicates (view)"); *)
  ("--norm-extract", Arg.Set Globals.norm_extract, "extract common pattern among branches of user-defined predicates (view)");
  ("--en-norm-disj", Arg.Set Globals.allow_norm_disj, "enable the normalization of disjunct during simplify");
  ("--dis-norm-disj", Arg.Clear Globals.allow_norm_disj, "disable the normalization of disjunct during simplify");
  ("--sa-en-print-decl" , Arg.Set Globals.print_heap_pred_decl, "enable predicates declaration printing");
  ("--sa-dis-print-decl" , Arg.Clear Globals.print_heap_pred_decl, "disable predicates declaration printing");
  ("--en-print-ann" , Arg.Set Globals.print_ann, "enable annotation printing (default)");
  ("--dis-print-clean", Arg.Clear Globals.print_clean_flag, "disable cleaner printing");
  ("--print-clean" , Arg.Set Globals.print_clean_flag, "enable cleaner printing (not default)");
  ("--print-derv" , Arg.Set Globals.print_derv, "enable [derv,orig] annotation printing");
  ("--dis-print-derv" , Arg.Clear Globals.print_derv, "disable [derv,orig] annotation printing (default)");
  ("--en-texify", Arg.Set Globals.texify, "output latex formulas");
  ("--en-testing", Arg.Set Globals.testing_flag, "generate for testing comparison with start/stop markers");
  ("--etcnf",Arg.Set Globals.tc_drop_unused, "quantify names that will not be used from the context after each Hoare rule");
  (*("--etcsu1",Arg.Set Globals.simpl_unfold1,"keep only default branch when unsat-ing");*)
  ("--etcsu2",Arg.Set Globals.simpl_unfold2,"syntactically deal with equalities and disequalities between vars for sat");
  ("--etcsu3",Arg.Set Globals.simpl_unfold3,"syntactically deal with equalities and disequalities between vars for imply");
  ("--pnum",Arg.Int (fun n ->
       Globals.sleek_num_to_verify := n),"Specific sleek number to verify");
  ("--etcsu1",Arg.Set Globals.simpl_memset,"use the old,complicated memset calculator");
  ("--dis-implicit-var",Arg.Set Globals.dis_impl_var, "disable implicit existential");
  ("--en-implicit-var",Arg.Clear Globals.dis_impl_var, "enable implicit existential (default)");
  ("--en-get-model", Arg.Set Globals.get_model, "enable get model in z3");
  ("--dis-get-model", Arg.Clear Globals.get_model, "disable get model in z3 (default)");
  ("--en-warning", Arg.Set VarGen.en_warning_msg, "enable warning (default)");
  ("--dis-warning", Arg.Clear VarGen.en_warning_msg, "disable warning (switch to report error)");
  ("--webprint", Arg.Unit
    (fun _ ->
      Debug.webprint := false;
      VarGen.web_location := false;
      Globals.enable_count_stats:= false;
      Globals.enable_time_stats:= false;
      Globals.tnt_web_mode:=true),
    "only prints essentials");
  ("--print-min",
   Arg.Unit
     (fun _ ->
        Globals.show_unexpected_ents := false;
        Debug.trace_on := false;
        Debug.devel_debug_on:= false;
        Globals.lemma_ep := false;
        Gen.silence_output:=false;
        Globals.enable_count_stats:=false;
        Globals.enable_time_stats:=false;
        Globals.lemma_gen_unsafe:=true;
        (* Globals.lemma_syn := true; *)
        (* Globals.acc_fold := true; *)
        Globals.smart_lem_search := true;
        Globals.print_min := true;
        (* Globals.gen_baga_inv := true; *)
        (* Globals.en_pred_sat (); *)
        (* Globals.do_infer_inv := true; *)
        (* Globals.lemma_gen_unsafe := true; *)
        (* Globals.graph_norm := true; *)
        (* Globals.is_solver_local := true; *)
        Globals.disable_failure_explaining := false;
        (* Globals.smt_compete_mode:=true; *)
        Globals.return_must_on_pure_failure := true;
        Globals.dis_impl_var := true),
   "Minimal printing only");
  ("--svcomp-compete",
   Arg.Unit
     (fun _ ->
        (* print_endline "inside svcomp-compete setting"; *)
        compete_mode:=true; (* main flag *)
        Globals.enforce_type_error:=false;
        Globals.svcomp_compete_mode:=true; (* main flag *)
        (* Globals.show_unexpected_ents := false; *)
        (* diable printing *)
        VarGen.trace_failure := false;
        Debug.trace_on := false;
        Debug.devel_debug_on:= false;
        Globals.lemma_ep := false;
        Gen.silence_output:=true;
        Globals.enable_count_stats:=false;
        Globals.enable_time_stats:=false;

        (* Globals.lemma_gen_unsafe:=true;    *)
        (* Globals.lemma_syn := true;         *)
        (* Globals.acc_fold := true;          *)
        (* Globals.smart_lem_search := true;  *)
        (* Globals.gen_baga_inv := true; *)
        (* Globals.en_pred_sat (); *)
        (* Globals.do_infer_inv := true; *)
        (* Globals.lemma_gen_unsafe := true; *)
        (* Globals.graph_norm := true; *)

        Globals.is_solver_local := true;
        (* Omega.omegacalc:=  *)
        (*   if (Sys.file_exists "./oc") then "./oc" *)
        (*   else "oc"; *)
        (* Fixcalc.fixcalc_exe := *)
        (*   if (Sys.file_exists "./fixcalc") then "./fixcalc" *)
        (*   else "fixcalc"; *)
        (* Smtsolver.smtsolver_path := *)
        (*   if (Sys.file_exists "./z3-4.3.2") then "./z3-4.3.2" *)
        (*   else "z3-4.3.2"; *)
        Globals.disable_failure_explaining := false;
        Globals.return_must_on_pure_failure := true;
        (* Globals.dis_impl_var := true *)
     ),
   "SVCOMP14 competition mode - essential printing only");
  ("--tnt-web-mode",
   Arg.Unit
     (fun _ ->
        (* print_endline "inside svcomp-compete setting"; *)
        compete_mode:=true; (* main flag *)
        Globals.svcomp_compete_mode:=true; (* main flag *)
        Globals.tnt_web_mode:=true; (* main flag *)
        (* Globals.show_unexpected_ents := false; *)
        (* diable printing *)
        VarGen.trace_failure := false;
        Debug.trace_on := false;
        Debug.devel_debug_on:= false;
        Globals.lemma_ep := false;
        Gen.silence_output:=true;
        Globals.enable_count_stats:=false;
        Globals.enable_time_stats:=false;

        (* Globals.lemma_gen_unsafe:=true;    *)
        (* Globals.lemma_syn := true;         *)
        (* Globals.acc_fold := true;          *)
        (* Globals.smart_lem_search := true;  *)
        (* Globals.gen_baga_inv := true; *)
        (* Globals.en_pred_sat (); *)
        (* Globals.do_infer_inv := true; *)
        (* Globals.lemma_gen_unsafe := true; *)
        (* Globals.graph_norm := true; *)

        Globals.is_solver_local := true;
        (* Omega.omegacalc:=  *)
        (*   if (Sys.file_exists "./oc") then "./oc" *)
        (*   else "oc"; *)
        (* Fixcalc.fixcalc_exe := *)
        (*   if (Sys.file_exists "./fixcalc") then "./fixcalc" *)
        (*   else "fixcalc"; *)
        (* Smtsolver.smtsolver_path := *)
        (*   if (Sys.file_exists "./z3-4.3.2") then "./z3-4.3.2" *)
        (*   else "z3-4.3.2"; *)
        Globals.disable_failure_explaining := false;
        Globals.return_must_on_pure_failure := true;
        (* Globals.dis_impl_var := true *)
     ),
   "Essential printing only for HipTNT+ website");
  ("--smt-compete",
   Arg.Unit
     (fun _ ->
        compete_mode:=true; (* main flag *)
        Globals.smt_compete_mode:=true;
        Globals.enforce_type_error:=false;
        Globals.show_unexpected_ents := false;
        Debug.trace_on := false;
        Debug.devel_debug_on:= false;
        Globals.lemma_ep := false;
        Gen.silence_output:=true;
        Globals.enable_count_stats:=false;
        Globals.enable_time_stats:=false;
        Globals.lemma_gen_unsafe:=true;
        Globals.lemma_syn := true;
        Globals.acc_fold := true;
        Globals.smart_lem_search := true;
        (* Globals.gen_baga_inv := true; *)
        Globals.en_pred_sat ();
        (* Globals.do_infer_inv := true; *)
        (* Globals.lemma_gen_unsafe := true; *)
        Globals.graph_norm := true;
        Globals.is_solver_local := true;
        Globals.disable_failure_explaining := false;
        Globals.return_must_on_pure_failure := true;
        Globals.dis_impl_var := true),
   "SMT competition mode - essential printing only");
  ("--smt-compete-test",
   Arg.Unit
     (fun _ ->
        (* Globals.show_unexpected_ents := true;  *)
        (*this flag is one that is  diff with compared to --smt-compete *)
        compete_mode:=true; (* main flag *)
        Globals.smt_compete_mode :=true;
        Debug.trace_on := true;
        Debug.devel_debug_on:= false;
        Globals.lemma_ep := false;
        Gen.silence_output:=false;
        Globals.enable_count_stats:=false;
        Globals.enable_time_stats:=false;
        Globals.lemma_gen_unsafe:=true;
        Globals.lemma_syn := true;
        Globals.acc_fold := true;
        Globals.smart_lem_search := true;
        (* Globals.en_pred_sat (); *)
        Globals.gen_baga_inv := false;
        (* Globals.do_infer_inv := true; *)
        Globals.graph_norm := true;
        Globals.is_solver_local := true;
        Globals.disable_failure_explaining := false;
        Globals.return_must_on_pure_failure := true;
        Globals.dis_impl_var := true),
   "SMT competition mode - essential printing only + show unexpected ents");
  ("--smt-test",
   Arg.Unit
     (fun _ ->
        Globals.show_unexpected_ents := true;
        (*this flag is one that is  diff with compared to --smt-compete *)
        Debug.trace_on := true;
        Debug.devel_debug_on:= false;
        Globals.lemma_ep := false;
        Gen.silence_output:=false;
        Globals.enable_count_stats:=false;
        Globals.enable_time_stats:=false;
        (* Globals.lemma_gen_unsafe:=true; *)
        Globals.lemma_rev_unsafe:=true;
        Globals.lemma_syn := true;
        (* Globals.acc_fold := true; *)
        (* Globals.smart_lem_search := true; *)
        Globals.seg_fold := true;
        Globals.en_pred_sat ();
        (* Globals.gen_baga_inv := false; *)
        (* Globals.do_infer_inv := true; *)
        Globals.graph_norm := true;
        (* Globals.is_solver_local := false; *)
        Globals.disable_failure_explaining := false;
        Globals.smt_compete_mode :=true;
        Globals.return_must_on_pure_failure := true;
        Globals.dis_impl_var := true),
   "SMT competition mode - essential printing only + show unexpected ents + sat + seg_fold");
  ("--gen-smt",Arg.Set Globals.gen_smt,"generate smt from slk");
  ("--force-print-residue", Arg.Set Globals.force_print_residue, "Always print residue")
]

(* arguments/flags used only by hip *)
let hip_specific_arguments = [ ("-cp", Arg.String set_pred,
                                "Compile specified predicate to Java.");
                               ("-rtc", Arg.Set rtc,
                                "Compile to Java with runtime checks.");
                               ("-nopp", Arg.String Rtc.set_nopp,
                                "-nopp caller:callee: do not check callee's pre/post in caller");
                               ("-nofield", Arg.String Rtc.set_nofield,
                                "-nofield proc: do not perform field check in proc");
                               ("--verify-callees", Arg.Set Globals.verify_callees,
                                "Verify callees of the specified procedures");
                               ("-inline", Arg.String Inliner.set_inlined,
                                "Procedures to be inlined");
                               ("-p", Arg.String set_proc_verified,
                                "Procedure to be verified. If none specified, all are verified.");
                               ("-print", Arg.Set Globals.print_proc,
                                "Print procedures being checked");
                               ("--dis-pgbv", Arg.Clear Globals.pass_global_by_value,
                                "disable pass read global variables by value");
                               ("--en-pgbv", Arg.Set Globals.pass_global_by_value,
                                "enable pass read global variables by value");
                               ("--sqt", Arg.Set Globals.seq_to_try,
                                "translate seq to try");
                               ("-validate", Arg.String set_validate_config,
                                "compare set of constraints");
                               ("-cp-pre-test", Arg.Set Globals.cp_prefile,
                                "compare set of constraints");
                               ("-gen-cpfile", Arg.String set_gen_cpfile,
                                "compare set of constraints");
                               ("-lib", Arg.String set_lib_file,
                                "lib");
                             ]

(* arguments/flags used only by sleek *)
let sleek_specific_arguments = [
  ("-fe", Arg.Symbol (["native"; "xml"], set_frontend),
   "Choose frontend:\n\tnative: Native (default)\n\txml: XML");
  ("-int", Arg.Set inter_hoa,
   "Run in interactive mode.");
  ("--slk-err", Arg.Set Globals.print_err_sleek,
   "print sleek errors");
  ("--iw",  Arg.Set Globals.wrap_exists_implicit_explicit ,
   "existentially wrap instantiations after the entailment");
]

(* arguments/flags used only in the gui *)
let gui_specific_arguments = [
  ("--gui", Arg.Set enable_gui, "enable GUI");
]

(* all hip's arguments and flags *)
let hip_arguments = common_arguments @ hip_specific_arguments

(* all sleek's arguments and flags *)
let sleek_arguments = common_arguments @ sleek_specific_arguments

(* all arguments and flags used in the gui*)
let gui_arguments = common_arguments @ hip_specific_arguments @ gui_specific_arguments
;;


(* let parseinput userinp = *)
(*   (\* Read the arguments *\) *)
(*   Printf.printf "String:%s\n" (Array.get userinp 2); *)
(*   Arg.parse_argv ?current:(Some (ref 0)) userinp *)
(*     speclist *)
(*     (fun x -> raise (Arg.Bad ("Bad argument : " ^ x))) *)
(*     usage; *)
(*   Printf.printf "Set stuff to:   %d '%s'\n%!"  !someint !somestr  *)


(* let  parseit line = *)
(*   Printf.printf "processing %s%!\n" line; *)
(*   (\* TODO rewrite without Str*\) *)
(*   let listl = (Str.split (Str.regexp " ") line) in *)
(*   parseinput (Array.of_list listl) *)

let parse_arguments_with_string s =
  let _ = print_endline s in
  let slst = (Str.split (Str.regexp " ") s) in
  let _ = List.iter (fun s -> print_endline (s^"##")) slst in
  let s_array = Array.of_list (Str.split (Str.regexp " ") s) in
  Arg.parse_argv ?current:(Some (ref 0)) s_array common_arguments (fun x -> ()) "Inner flags!"
;;

let check_option_consistency () =
  (* Slicing and Specilization Consistency *)
  if not !Globals.en_slc_ps then begin
    Globals.dis_ps := true;
    Globals.dis_slc_ann := true;
  end;
  if !Globals.perm=Globals.Dperm then Globals.use_split_match:=true else () ;
  if !Globals.perm<>Globals.NoPerm then Globals.allow_imm:=false else () ;
  (* if !Globals.allow_imm && Perm.allow_perm() then *)
  (* begin *)
  (*   Gen.Basic.report_error no_pos "immutability and permission options cannot be turned on at the same time" *)
  (* end *)
;; (*Clean warning*)
Astsimp.inter_hoa := !inter_hoa;;

Typechecker.save_flags  := fun ()->() ;;
Typechecker.restore_flags := fun ()-> ();;
Typechecker.parse_flags := fun (sl:(string*(Globals.flags option)) list)->
  List.iter(fun (s1,s2)->
      try
        let _,f,_=List.find(fun (a,_,_)-> (String.compare a s1) ==0) hip_arguments in
        let rec process_arg s1 s2 f : unit= match f with
          |	Arg.Unit f -> f ()
          | Arg.Expand _
          |   Arg.Rest _
          |   Arg.Rest_all _
          |	Arg.Bool _-> ()
          |	Arg.Set b -> b:=true
          |	Arg.Clear b -> b:=false
          |	Arg.Set_string b-> (match s2 with Some (Globals.Flag_str i)-> b:=i | _ -> failwith ("invalid flag argument for "^s1))
          |	Arg.String f -> (match s2 with | Some (Globals.Flag_str s)-> f s | _ -> failwith ("invalid flag argument for "^s1))
          |	Arg.Set_int b-> (match s2 with Some (Globals.Flag_int i)-> b:=i | _ -> failwith ("invalid flag argument for "^s1))
          |   Arg.Int f -> (match s2 with Some (Globals.Flag_int i)-> f i | _ -> failwith ("invalid flag argument for "^s1))
          |	Arg.Set_float b-> (match s2 with Some (Globals.Flag_float i)-> b:=i | _ -> failwith ("invalid flag argument for "^s1))
          |   Arg.Float f-> (match s2 with | Some (Globals.Flag_float s)-> f s | _ -> failwith ("invalid flag argument for "^s1))
          |	Arg.Tuple l -> List.iter (process_arg s1 s2) l
          |	Arg.Symbol (sl, f) ->
            try
              (match s2 with
               | Some (Globals.Flag_str s)-> f (List.find(fun a-> (String.compare a s) ==0) sl)
               | _ -> failwith ("invalid flag argument for "^s1))
            with  Not_found -> failwith ("invalid flag "^s1) in
        process_arg s1 s2 f
      with Not_found -> failwith ("invalid flag "^s1)) sl;;
