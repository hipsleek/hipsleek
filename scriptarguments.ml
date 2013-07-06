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

let set_file_cp arg =
  Globals.file_cp := arg;
   Globals.cp_test := true

let set_gen_cpfile arg =
  Globals.cpfile := arg;
   Globals.gen_cpfile := true

let set_lib_file arg =
  Globals.lib_files := [arg]

let set_frontend fe_str = match fe_str  with
  | "native" -> fe := NativeFE
  | "xml" -> fe := XmlFE
  | _ -> failwith ("Unsupported frontend: " ^ fe_str)


(* arguments/flags that might be used both by sleek and hip *)
let common_arguments = [
  ("--sctx", Arg.Set Typechecker.simplify_context, "Simplify the context before each execution in symbolic execution."); (* An Hoa *)
  (*("--sdp", Arg.Set Cprinter.simplify_dprint,
  "Simplify the entail state before printing the dprint state."); (* An Hoa *) *)
  ("-wpf", Arg.Set Globals.print_proof,
   "Print all the verification conditions, the input to external prover and its output.");
  (* ("--ufdp", Arg.Set Solver.unfold_duplicated_pointers, *)
  (* "Do unfolding of predicates with duplicated pointers."); (\* An Hoa *\) *)
  ("--dis-ufdp", Arg.Clear Solver.unfold_duplicated_pointers,
   "Disable unfolding of predicates with duplicated pointers."); (* An Hoa *)
  ("--ahwytdi", Arg.Set Smtsolver.try_induction,
   "Try induction in case of failure implication."); (* An Hoa *)
  ("--smtimply", Arg.Set Smtsolver.outconfig.Smtsolver.print_implication,
   "Print the antecedent and consequence for each implication check."); (* An Hoa *)
  ("--smtout", Arg.Set Smtsolver.outconfig.Smtsolver.print_original_solver_output,
   "Print the original output given by the SMT solver."); (* An Hoa *)
  ("--smtinp", Arg.Set Smtsolver.outconfig.Smtsolver.print_input,
   "Print the program generated SMT input."); (* An Hoa *)
  ("--no-omega-simpl", Arg.Clear Globals.omega_simpl,
   "Do not use Omega to simplify the arithmetic constraints when using other solver");
  ("--no-simpl", Arg.Set Globals.no_simpl,
   "Do not simplify the arithmetic constraints");
  ("--simpl-pure-part", Arg.Set Globals.simplify_pure,
   "Simplify the pure part of the formulas");
  (* ("--combined-lemma-heuristic", Arg.Set Globals.lemma_heuristic, *)
  (* "Use the combined coerce&match + history heuristic for lemma application"); *)
  ("--move-exist-to-LHS", Arg.Set Globals.move_exist_to_LHS,
   "Move instantiation (containing existential vars) to the LHS at the end of the folding process");
  ("--max-renaming", Arg.Set Globals.max_renaming,
   "Always rename the bound variables");
  ("--no-anon-exist", Arg.Clear Globals.anon_exist,
   "Disallow anonymous variables in the precondition to be existential");
  ("--LHS-wrap-exist", Arg.Set Globals.wrap_exist,
   "Existentially quantify the fresh vars in the residue after applying ENT-LHS-EX");
  ("-noee", Arg.Clear Globals.elim_exists_flag,
   "No eliminate existential quantifiers before calling TP.");
  ("--no-filter", Arg.Clear Globals.filtering_flag,
  "No assumption filtering.");
  ("--filter", Arg.Set Globals.filtering_flag,
   "Enable assumption filtering.");
  ("--no-split-rhs", Arg.Clear Globals.split_rhs_flag,
   "No Splitting of RHS(conseq).");
  ("--dlp", Arg.Clear Globals.check_coercions,
   "Disable Lemma Proving");
  ("--dis-auto-num", Arg.Clear Globals.auto_number,
   "Disable Auto Numbering");
  ("--dis-sleek-log-filter", Arg.Clear Globals.sleek_log_filter,
   "Sleek Log Filter Flag");
  ("--elp", Arg.Set Globals.check_coercions,
   "Enable Lemma Proving");
  ("--trace", Arg.Set Debug.trace_on,
   "Turn on brief tracing");
  ("--dis-trace", Arg.Clear Debug.trace_on,
   "Turn off brief tracing");
  ("-dd", Arg.Set Debug.devel_debug_on,
   "Turn on devel_debug");
  ("-dd-print-orig-conseq", Arg.Unit Debug.enable_dd_and_orig_conseq_printing,
   "Enable printing of the original consequent while debugging. Automatically enables -dd (debugging) ");
  ("-gist", Arg.Set Globals.show_gist,
   "Show gist when implication fails");
  ("--hull-pre-inv", Arg.Set Globals.hull_pre_inv,
   "Hull precondition invariant at call sites");
  ("--sat-timeout", Arg.Set_float Globals.sat_timeout_limit,
   "Timeout for sat checking");
  ("--imply-timeout", Arg.Set_float Globals.imply_timeout_limit,
   "Timeout for imply checking");
  ("--sleek-timeout", Arg.Set_float Globals.sleek_timeout_limit,
   "Timeout for SLEEK entailment");
  ("--ds-provers-timeout", Arg.Set Globals.dis_provers_timeout,
   "Disable timeout on provers");
  ("--log-proof", Arg.String Prooftracer.set_proof_file,
   "Log (failed) proof to file");
  ("--trace-failure", Arg.Set Globals.trace_failure,
   "Enable trace all failure (and exception)");
  ("--trace-all", Arg.Set Globals.trace_all,
   "Trace all proof paths");
  ("--log-cvcl", Arg.String Cvclite.set_log_file,
   "Log all CVC Lite formula to specified log file");
  (* ("--log-cvc3", Arg.String Cvc3.set_log_file, *)
  ("--log-cvc3", Arg.Unit Cvc3.set_log_file,    "Log all formulae sent to CVC3 in file allinput.cvc3");
  ("--log-omega", Arg.Set Omega.log_all_flag,
   "Log all formulae sent to Omega Calculator in file allinput.oc");
  ("--log-z3", Arg.Set Smtsolver.log_all_flag,
   "Log all formulae sent to z3 in file allinput.z3");
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
  ("--ann-vp", Arg.Set Globals.ann_vp,"manual annotation of variable permissions");
  ("--dis-ann-vp", Arg.Clear Globals.ann_vp,"manual annotation of variable permissions");
  ("--ls", Arg.Set Globals.allow_ls,"enable locksets during verification");
  ("--en-web-compile", Arg.Set Globals.web_compile_flag,"enable web compilation setting");
  ("--dis-ls", Arg.Clear Globals.allow_ls,"disable locksets during verification");
  ("--locklevel", Arg.Set Globals.allow_locklevel,"enable locklevels during verification");
  ("--dis-locklevel", Arg.Clear Globals.allow_locklevel,"disable locklevels during verification");
  ("--dis-para", Arg.Unit Perm.disable_para,"disable concurrency verification");
  ("--en-para", Arg.Unit Perm.enable_para,"enable concurrency verification");
  ("--imm", Arg.Set Globals.allow_imm,"enable the use of immutability annotations");
  ("--field-ann", Arg.Set Globals.allow_field_ann,"enable the use of immutability annotations for data fields");
  ("--memset-opt", Arg.Set Globals.ineq_opt_flag,"to optimize the inequality set enable");
  ("--dis-field-ann", Arg.Clear Globals.allow_field_ann,"disable the use of immutability annotations for data fields");
  (*("--mem", Arg.Set Globals.allow_mem,"Enable the use of Memory Specifications");*)
  ("--dis-mem", Arg.Clear Globals.allow_mem,"Disable the use of Memory Specifications");
  ("--ramify", Arg.Clear Solver.unfold_duplicated_pointers,"Use Ramification (turns off unfold on dup pointers)");
  ("--reverify", Arg.Set Globals.reverify_flag,"enable re-verification after specification inference");
  ("--reverify-all", Arg.Set Globals.reverify_all_flag,"enable re-verification after heap specification inference");
  ("--dis-imm", Arg.Clear Globals.allow_imm,"disable the use of immutability annotations");
  ("--dis-inf", Arg.Clear Globals.allow_inf,"disable support for infinity ");
  ("--dsd", Arg.Set Globals.deep_split_disjuncts,"enable deep splitting of disjunctions");
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
  ("--en-disj-compute", Arg.Set Globals.disj_compute_flag,
   "Enable re-computation of user-supplied disj. invariant");
  ("--dis-lhs-case", Arg.Clear Globals.lhs_case_flag,
   "Disable LHS Case Analysis");
  ("--en-lhs-case", Arg.Set Globals.lhs_case_flag,
   "Enable LHS Case Analysis");
  ("--en-lhs-case-search", Arg.Set Globals.lhs_case_search_flag,
   "Replace Cond_action by Search for LHS Case Analysis");
  ("-nxpure", Arg.Set_int Globals.n_xpure,
   "Number of unfolding using XPure");
  ("-v:", Arg.Set_int Globals.verbose_num,
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
  ("--en-self-fold-search", Arg.Set Globals.self_fold_search_flag,
   "Enable Limited Search with Self Unfold/Fold");
  ("-parse", Arg.Set parse_only,"Parse only");
  ("--parser", Arg.Symbol (["default"; "cil"], Parser.set_parser), "Choose different parser: default; cil");
  ("--dump-ss", Arg.Set dump_ss, "Dump ss files");
  ("-core", Arg.Set typecheck_only,"Type-Checking and Core Preprocessing only");
  ("--print-iparams", Arg.Set Globals.print_mvars,"Print input parameters of predicates");
  ("--print-type", Arg.Set Globals.print_type,"Print type info");
  ("--print-x-inv", Arg.Set Globals.print_x_inv,
   "Print computed view invariants");
  ("--pr_str_assume", Arg.Set Globals.print_assume_struc, "Print structured formula for assume");
  ("-stop", Arg.Clear Globals.check_all,
   "Stop checking on erroneous procedure");
  ("--build-image", Arg.Symbol (["true"; "false"], Isabelle.building_image),
   "Build the image theory in Isabelle - default false");
  ("-tp", Arg.Symbol (["cvcl"; "cvc3"; "oc";"oc-2.1.6"; "co"; "isabelle"; "coq"; "mona"; "monah"; "z3"; "z3-2.19"; "zm"; "om";
   "oi"; "set"; "cm"; "redlog"; "rm"; "prm"; "spass";"parahip"; "math"; "minisat" ;"auto";"log"; "dp"], Tpdispatcher.set_tp),
   "Choose theorem prover:\n\tcvcl: CVC Lite\n\tcvc3: CVC3\n\tomega: Omega Calculator (default)\n\tco: CVC3 then Omega\n\tisabelle: Isabelle\n\tcoq: Coq\n\tmona: Mona\n\tz3: Z3\n\tom: Omega and Mona\n\toi: Omega and Isabelle\n\tset: Use MONA in set mode.\n\tcm: CVC3 then MONA.");
  ("--dis-tp-batch-mode", Arg.Clear Tpdispatcher.tp_batch_mode,"disable batch-mode processing of external theorem provers");
  ("-perm", Arg.Symbol (["fperm"; "cperm"; "dperm";"none"], Perm.set_perm),
   "Choose type of permissions for concurrency :\n\t fperm: fractional permissions\n\t cperm: counting permissions");
  ("--permprof", Arg.Set Globals.perm_prof, "Enable perm prover profiling (for distinct shares)");
  ("--omega-interval", Arg.Set_int Omega.omega_restart_interval,
   "Restart Omega Calculator after number of proof. Default = 0, not restart");
  ("--use-field", Arg.Set Globals.use_field,
   "Use field construct instead of bind");
  ("--use-large-bind", Arg.Set Globals.large_bind,
   "Use large bind construct, where the bound variable may be changed in the body of bind");
  ("-v", Arg.Set Debug.debug_on,
   "Verbose");
  ("--pipe", Arg.Unit Tpdispatcher.Netprover.set_use_pipe,
   "use external prover via pipe");
  ("--dsocket", Arg.Unit (fun () -> Tpdispatcher.Netprover.set_use_socket "loris-7:8888"),
   "<host:port>: use external prover via loris-7:8888");
  ("--socket", Arg.String Tpdispatcher.Netprover.set_use_socket,
   "<host:port>: use external prover via socket");
  ("--prover", Arg.String Tpdispatcher.set_tp,
   "<p,q,..> comma-separated list of provers to try in parallel");
  (* ("--enable-sat-stat", Arg.Set Globals.enable_sat_statistics,  *)
  (* "enable sat statistics"); *)
  ("--en-pstat", Arg.Set Globals.profiling,
   "enable profiling statistics");
  ("--en-cstat", Arg.Set Globals.enable_counters, "enable counter statistics");
  ("--dis-time-stat", Arg.Clear Globals.enable_time_stats, "disable timing statistics from being printed");
  ("--dis-count-stat", Arg.Clear Globals.enable_count_stats, "disable counting statistics from being printed");
  ("--en-stat", (Arg.Tuple [Arg.Set Globals.profiling; Arg.Set Globals.enable_counters]),
   "enable all statistics");
  ("--sbc", Arg.Set Globals.enable_syn_base_case,
   "use only syntactic base case detection");
  ("--dis-simpl-view-norm" , Arg.Clear Globals.simplified_case_normalize, 
	"disable simplified view def normalization");
  ("--eci", Arg.Set Globals.enable_case_inference,
   "enable struct formula inference");
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

  (* Termination options *)
  ("--dis-term-check", Arg.Set Globals.dis_term_chk, "turn off the termination checking");
  ("--term-verbose", Arg.Set_int Globals.term_verbosity,
      "level of detail in termination printing 0-verbose 1-standard(default)");
  ("--dis-call-num", Arg.Set Globals.dis_call_num, "turn off the automatic call numbering");
  ("--dis-phase-num", Arg.Set Globals.dis_phase_num, "turn off the automatic phase numbering");
  ("--term-reverify", Arg.Set Globals.term_reverify,
   "enable re-verification for inferred termination specifications");
  ("--dis-bnd-check", Arg.Set Globals.dis_bnd_chk, "turn off the boundedness checking");
  ("--dis-term-msg", Arg.Set Globals.dis_term_msg, "turn off the printing of termination messages");
  ("--dis-post-check", Arg.Set Globals.dis_post_chk, "turn off the post_condition and loop checking");
  ("--dis-assert-check", Arg.Set Globals.dis_ass_chk, "turn off the assertion checking");
  ("--dis-log-filter", Arg.Clear Globals.log_filter, "turn off the log initial filtering");

  (* Slicing *)
  ("--eps", Arg.Set Globals.en_slc_ps, "Enable slicing with predicate specialization");
  ("--dpall", Arg.Clear Globals.no_prune_all, "Disable specialization all the way");  
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
  
  (* Proof Logging *)
  ("--en-logging", Arg.Set Globals.proof_logging, "Enable proof logging");
  ("--en-logging-txt", Arg.Set Globals.proof_logging_txt, "Enable proof logging output text file in addition");
  ("--en-sleek-logging-txt", Arg.Set Globals.sleek_logging_txt, "Enable sleek logging output text file in addition");

  (* abduce pre from post *)
  ("--abdfpost", Arg.Set Globals.do_abd_from_post, "Enable abduction from post-condition");
  (* incremental spec *)
  ("--inc", Arg.Set Globals.do_infer_inc, "Enable incremental spec inference");
  (* invariant *)
  ("--inv", Arg.Set Globals.do_infer_inv, "Enable invariant inference");

  (* use classical reasoning in separation logic *)
  ("--classic", Arg.Set Globals.opt_classic, "Use classical reasoning in separation logic");
  ("--dis-split", Arg.Set Globals.use_split_match, "Disable permission splitting lemma (use split match instead)");
  ("--en-lemma-s", Arg.Set Globals.enable_split_lemma_gen, "Enable automatic generation of splitting lemmas");
  ("--dis-show-diff", Arg.Set Globals.dis_show_diff, "Show differences between formulae");
  ("--dis-sem", Arg.Set Globals.dis_sem, "Show differences between formulae");
  ("--en-cp-trace", Arg.Set Globals.cond_path_trace, "Enable the tracing of conditional paths");
  ("--dis-cp-trace", Arg.Clear Globals.cond_path_trace, "Disable the tracing of conditional paths");
  ("--sa-print-inter", Arg.Set Globals.sa_print_inter, "Print intermediate results of normalization");
  ("--sa-old", Arg.Set Globals.sa_old, "old algorithm of normalization");
   ("--sa-dnc", Arg.Set Globals.sa_dnc, "algorithm of normalization with divide and conquer");
  (* ("--sa-en-norm", Arg.Set Globals.sa_en_norm, "do normalization"); *)
  ("--sa-dis", Arg.Clear Globals.sa_en, "donot infer shape");
  (* ("--sa-dangling", Arg.Set Globals.sa_dangling, "elim dangling HP/pointers"); *)
  ("--pred-dis-infer", Arg.Clear Globals.pred_infer_flag, "disable the shape inference stage");
  ("--pred-en-useless-para", Arg.Set Globals.pred_elim_useless, "enable the elimination of useless parameter from HP predicate and user-defined predicates (view)");
  ("--pred-dis-useless-para", Arg.Clear Globals.pred_elim_useless, "disable the elimination of useless parameter from HP predicate and user-defined predicates (view)");
  ("--pred-en-dangling", Arg.Set Globals.pred_elim_dangling, "enable the elimination of dangling predicate from derived HP defns");
  ("--pred-dis-dangling", Arg.Clear Globals.pred_elim_dangling, "disable the elimination of dangling predicate from derived HP defns");
  ("--sa-refine-dang", Arg.Set Globals.sa_refine_dang, "refine dangling among branches of one hprels def");
  (* ("--sa-inlining", Arg.Set Globals.sa_inlining, "inline dangling HP/pointers"); *)
  ("--pred-en-eup", Arg.Set Globals.pred_elim_unused_preds, "enable the elimination of unused hprel predicates");
  ("--pred-dis-eup", Arg.Clear Globals.pred_elim_unused_preds, "disable the elimination of unused hprel predicates");
  ("--sa-en-pure-field", Arg.Set Globals.sa_pure_field, "enable the inference of pure field property");
  ("--sa-dis-pure-field", Arg.Clear Globals.sa_pure_field, "disable the inference of pure field property");
  ("--sa-en-sp-split", Arg.Set Globals.sa_sp_split_base, "enable special base case split at entailment");
  ("--sa-dis-sp-split", Arg.Clear Globals.sa_sp_split_base, "disable special base case split at entailment");
  ("--sa-en-split", Arg.Set Globals.sa_infer_split_base, "enable base case splitting of relational assumption at shape infer");
  ("--sa-dis-split", Arg.Clear Globals.sa_infer_split_base, "disable base case splitting of relational assumption at shape infer");
  ("--sa-split", Arg.Set Globals.sa_en_split, "splitting hp args into multiple hp if possible");
  ("--sa-unify-dangling", Arg.Set Globals.sa_unify_dangling, "unify branches of definition to instantiate dangling predicate");
  ("--pred-disj-unify", Arg.Set Globals.pred_disj_unify, "attempt to unify two similar predicates among inferred pred defs");
   ("--pred-conj-unify", Arg.Set Globals.pred_conj_unify, "attempt to conj-unify among inferred assumption");
  ("--pred-equiv", Arg.Set Globals.pred_equiv, "attempt to reuse predicates with identical definition");
  ("--sa-tree-simp", Arg.Set Globals.sa_tree_simp, "simplify a tree branches of definition");
  ("--sa-subsume", Arg.Set Globals.sa_subsume, "use subsume when comparing definitions after infering");
  (* ("--norm-useless", Arg.Set Globals.norm_elim_useless, "elim useless parameters of user-defined predicates (view)"); *)
  ("--norm-extract", Arg.Set Globals.norm_extract, "extract common pattern among branches of user-defined predicates (view)");
  ("--sa-en-print-decl" , Arg.Set Globals.print_heap_pred_decl, "enable predicates declaration printing");
  ("--sa-dis-print-decl" , Arg.Clear Globals.print_heap_pred_decl, "disable predicates declaration printing");
  ("--en-print-ann" , Arg.Set Globals.print_ann, "enable annotation printing (default)");
  ("--dis-print-ann", Arg.Clear Globals.print_ann, "disable annotation printing");
  ("--en-texify", Arg.Set Globals.texify, "output latex formulas");
  ("--en-testing", Arg.Set Globals.testing_flag, "generate for testing comparison with start/stop markers");

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
  ("--sqt", Arg.Set Globals.seq_to_try,
   "translate seq to try");
  ("-cp-test", Arg.String set_file_cp,
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
  (*   Gen.Basic.report_error Globals.no_pos "immutability and permission options cannot be turned on at the same time" *)
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
				|   Arg.Rest _ 
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
