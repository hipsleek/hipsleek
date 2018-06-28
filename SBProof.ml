open SBGlobals
open SBCast
open SBLib
open SBLib.Basic
open SBUnify

module DB = SBDebug
module NO = SBNormalize
module PT = SBPuretp
module PE = SBProfile

(*****************************************************************)
(************      data structure used by prover       ***********)

(** the entire proof tree *)
type proof_tree =
  | PtSearch of proof_tree_search
  | PtDerive of proof_tree_derive

and backjump = {
  bkj_ent_id : int;
  bkj_rule : rule;
}

(** proof tree corresponding to search and application of inference rules *)
and proof_tree_search = {
  pts_goal : goal;
  pts_sub_trees : proof_tree list;   (* all possible searched sub-trees *)
  pts_bidirection : bool;
  pts_heur : proof_heuristic;
  pts_status : proof_tree_status;
}

(** proof tree corresponding to derivation of an inference rule *)
and proof_tree_derive = {
  ptd_goal : goal;
  ptd_rule : rule;                   (* all derived sub-trees *)
  ptd_bidirection : bool;
  ptd_sub_trees : proof_tree list;
  ptd_heur : proof_heuristic;
  ptd_status : proof_tree_status;
}

and proof_tree_status =
  | PtValid of proof_tree_core
  | PtInvalid
  | PtUnkn of string
  | PtInfer of proof_tree_core     (* for more complete, try a list of ptcore *)

and proof_heuristic =
  | PhHM
  | PhML

and proof_tree_core = {
  ptc_goal : goal;
  ptc_rule : rule;
  ptc_stats : proof_tree_core_stats;
  ptc_mutual_hypos : hypothesis list;
  ptc_assums : assumption list;
  ptc_sub_trees : proof_tree_core list;
  ptc_backjump : backjump option;
}

and  meta_rule =
  | MrStarData
  | MrStarView
  | MrViewRight
  | MrInduction
  | MrHypothesis
  | MrTheorem
  | MrExclMid
  | MrGenLeft
  | MrNormalize
  | MrAxiom
  | MrUnknown

and rule =
  | RlStarData of rule_star_data
  | RlStarView of rule_star_view
  | RlViewLeft of rule_view_left
  | RlViewRight of rule_view_right
  | RlInduction of rule_induction
  | RlHypothesis of rule_hypothesis
  | RlTheorem of rule_theorem
  | RlExclMid of rule_excl_mid
  | RlPureEntail of rule_pure_entail
  | RlEqualLeft of rule_equal_left
  | RlExistsLeft of rule_exists_left
  | RlExistsRight of rule_exists_right
  | RlEmpLeft of rule_emp_left
  | RlEmpRight of rule_emp_right
  | RlDropLeft of rule_drop_left
  | RlDropRight of rule_drop_right
  | RlGenLeft of rule_gen_left
  | RlWeakenLeft of rule_weaken_left
  | RlUnfoldRel of rule_unfold_relation
  | RlFalseLeft of rule_false_left
  | RlInferRel of rule_infer_relation
  | RlInferEnt of rule_infer_entail         (* This should be a meta rule *)

and view_unfold_case = {
  vuc_view : view_form;
  vuc_orig_form : formula;
  vuc_view_case_id : int;
  vuc_view_case_form : formula;
  vuc_base_case : bool;
  vuc_new_form : formula;
  vuc_num_datas : int;
  vuc_num_views : int;
}

and view_fold_case = {
  vfc_view : view_form;
  vfc_orig_form : formula;
  vfc_view_case_id : int;
  vfc_view_case_form : formula;
  vfc_base_case : bool;
  vfc_new_form : formula;
  vfc_num_datas : int;
  vfc_num_views : int;
}

and view_split = {
  vsp_head : view_form;              (* extracted view *)
  vsp_rest : heap_form * pure_form;  (* remaining part *)
  vsp_view_recur : view_recur_typ;
  vsp_qvars : quantifier list;      (* quantifiers *)
  vsp_unfold_cases : view_unfold_case list;
  vsp_orig_form: formula;
}

and data_split = {
  dsp_head : data_form;              (* extracted data *)
  dsp_rest : heap_form * pure_form;  (* remaining part *)
  dsp_qvars : quantifier list;      (* quantifiers *)
  dsp_full : formula;
}

and heap_pos =
  | HpHead
  | HpTail
  | HpHdtl
  | HpUnkn

and priority =
  | PrioHigh
  | PrioLow
  | PrioEqual

and excl_mid_case_type =
  | EmctPlanned
  | EmctUnplanned

and excl_mid_case = {
  emc_pure_cond : pure_form;
  emc_rule_planned : rule list;
  emc_type : excl_mid_case_type;
}

and excl_mid_seed = {
  ems_view_right : rule_view_right list;
  ems_hypothesis : rule_hypothesis list;
  ems_theorem : rule_theorem list;
}

and form_gen_type =
  | FgUninstHeap
  | FgWeakenPure of pure_form

and rule_star_data = {
  rsd_lg_data : data_form;
  rsd_lg_rest : heap_form * pure_form;
  rsd_lg_qvars : quantifier list;
  rsd_rg_data : data_form;
  rsd_rg_rest : heap_form * pure_form;
  rsd_rg_qvars : quantifier list;
  rsd_match_args_form : pure_form;
  rsd_can_match_all_args : bool;
  rsd_has_common_arg : bool;
  rsd_num_common_args : int;
  rsd_same_data_name : bool;
  rsd_same_root : bool;
  rsd_rdata_has_fvars : bool;
  rsd_rdata_has_qvars : bool;
  rsd_heuristics : proof_heuristic;
  rsd_trivial : bool;
}

and rule_star_view = {
  rsv_lg_view : view_form;
  rsv_lg_rest : heap_form * pure_form;
  rsv_lg_qvars : quantifier list;
  rsv_rg_view : view_form;
  rsv_rg_rest : heap_form * pure_form;
  rsv_rg_qvars : quantifier list;
  rsv_match_args_form : pure_form;
  rsv_can_match_all_args : bool;
  rsv_rview_has_fvars : bool;
  rsv_rview_has_qvars : bool;
  rsv_has_common_arg : bool;
  rsv_num_common_args : int;
  rsv_same_view_name : bool;
  rsv_heuristics : proof_heuristic;
  rsv_trivial : bool;
}

and rule_view_left = {
  rvl_lg_view : view_form;
  rvl_fold_case : view_fold_case;
  rvl_has_view_common_root : bool;
  rvl_has_view_common_args : bool;
  rvl_num_ldatas : int;
  rvl_num_rdatas : int;
  rvl_num_lviews : int;
  rvl_num_rviews : int;
  rvl_heuristics : proof_heuristic;
  rvl_trivial : bool;
}

and rule_view_right = {
  rvr_rg_view : view_form;
  rvr_unfold_case : view_unfold_case;
  rvr_has_data_same_root : bool;
  rvr_has_data_same_args : bool;
  rvr_num_ldatas : int;
  rvr_num_rdatas : int;
  rvr_num_lviews : int;
  rvr_num_rviews : int;
  rvr_heuristics : proof_heuristic;
  rvr_trivial : bool;
}

(* induction using formula order *)
and rule_induction = {
  rid_ent_id : int;
  rid_lg_view : view_form;
  rid_lg_view_pos : heap_pos;
  rid_unfold_cases : view_unfold_case list;
  rid_record_hypo : bool;
  rid_has_view_common_root : bool;
  rid_has_view_common_arg : bool;
  rid_has_data_same_root : bool;
  rid_has_data_common_arg_indt_case : bool;
  rid_has_related_emid_cond : bool;
  rid_rg_has_indirect_recur_view : bool;
  rid_lg_view_vars : var list;
  rid_heuristics : proof_heuristic;
  rid_trivial : bool;
}

and rule_hypothesis = {
  (* TODO: extend this rule with failure on heap and pure information *)
  rhp_hp : hypothesis;
  rhp_unf_ssts : subst list;
  rhp_unf_residue : heap_form;
  rhp_assums: assumption list;
  rhp_heurs : proof_heuristic;
}

and rule_theorem = {
  rth_th : theorem;
  rth_left : bool;
  rth_unf_ssts : subst list;
  rth_unf_ssts_len : int;
  rth_unf_residue : heap_form;
  rth_heuristics : proof_heuristic;
}

and rule_excl_mid = {
  rem_seed_cond : pure_form;
  rem_seed_rule : excl_mid_seed;
  rem_cases : excl_mid_case list;
  rem_heuristics : proof_heuristic;
}

and rule_gen_left = {
  rgl_new_lg : formula;
  rgl_gen_exps : exp list;
  rgl_base_hypo_unf : (hypothesis * unification) option;
  rgl_has_gen_emid_vars : bool;
  rgl_has_gen_unfolded_exps : bool;
}

and rule_weaken_left = {
  rwl_new_lg : formula;
  rwl_dropped_pf : pure_form;
  rwl_base_hypo_unf : (hypothesis * unification) option;
  rwl_has_gen_emid_vars : bool;
}

and rule_equal_left = {
  reql_lg : formula;
}

and rule_exists_left = {
  rexl_lg : formula;
}

and rule_exists_right = {
  rexr_rg : formula;
}

and rule_emp_left = {
  reml_lg : formula;
}

and rule_emp_right = {
  remr_rg : formula;
}

and rule_drop_left = {
  rdl_lg : formula;
  rdl_lg_drop : pure_form;
}

and rule_drop_right = {
  rdr_rg : formula;
  rdr_rg_drop : pure_form;
}

and rule_unfold_relation = {
  rur_lg_rels : rel_form list;
  rur_rg_rels : rel_form list;
}

and rule_pure_entail = {
  rpe_lg : formula;
  rpe_rg : formula;
  rpe_status : mvlogic;
}

and rule_false_left = {
  rfl_lg : formula;
}

and rule_infer_relation = {
  rir_lg : formula;
  rir_rg : formula;
  rir_hconsumed : heap_atom list;
  rir_assumption : assumption;
}

and rule_infer_entail = {
  rie_goal : goal;
  rie_rdefns : rel_defn list;
  rie_entail : entailment;
}

(* a hypothesis is a conjectured entailment *)
and hypothesis = {
  hp_ent_id : int;                   (* id of the entailment *)
  hp_renaming : renaming list;       (* renaming from entailment -> hypo *)
  hp_lhs : formula;
  hp_rhs : formula;
  hp_lstats : formula_stats;
  hp_rstats : formula_stats;
}

and theorem = {
  th_name : string;         (* name of the theorem / lemma *)
  th_lhs : formula;
  th_rhs : formula;
  th_lhs_name : string;
  th_rhs_name : string;
  th_origin : lemma_origin;
  th_lstats : formula_stats;
  th_rstats : formula_stats;
}

and counter_theorem = {
  cth_name : string;         (* name of the counter theorem *)
  cth_lhs : formula;
  cth_rhs : formula;
  cth_status : mvlogic;
  cth_lstats : formula_stats;
  cth_rstats : formula_stats;
}

and entail_id = int

(* goal is an entailment in the conclusion of an inference rule *)
and goal = {
  gl_ent_id : entail_id;              (* id of the corriesponding entailment *)
  gl_lhs : formula;
  gl_rhs : formula;
  gl_hconsumed : heap_atom list;
  gl_hreplaced : heap_atom list;
  gl_proof_mode : proof_mode;
  gl_need_infer_lemma : bool;
  gl_need_check_unsat_lhs : bool;
  gl_depth_infer : int;
  gl_trace : trace_item list;         (* the most recent trace is at the head *)
  gl_tstats : trace_stats;
  gl_lhs_encoded : pure_form;
  gl_lhs_derived_groups : derived_group list;
  gl_rhs_derived_groups : derived_group list;
  gl_lstats : formula_stats;
  gl_rstats : formula_stats;
  gl_gstats : goal_stats;
  gl_matching_plans : unification list;
  gl_has_unplanned_excl_mid : bool;
  gl_rhs_unproved_patoms : pure_form list;
  gl_cache_rule : cache_rule option;
  gl_precise_unifying_plans : unification list;
  gl_hooked_rules : rule list;
  gl_assums : assumption list;
  gl_hypos : hypothesis list;
  gl_unproductive_reason : string option;
}

and goal_stats = {
  gst_fvs : var list;
  gst_num_rfvars : int;
  gst_num_rfnames : int;
  gst_view_names : string list;
  gst_data_names : string list;
  gst_num_view_names : int;
  gst_num_data_names : int;
  gst_num_hatoms : int;
  gst_num_indirect_recur_views : int;
  gst_has_common_vname : bool;
  gst_has_common_hvars : bool;
  gst_has_diff_vname : bool;
}

and proof_tree_core_stats = {
  pst_mr_star_data : int;
  pst_mr_star_view : int;
  pst_mr_view_right : int;
  pst_mr_induction : int;
  pst_mr_hypothesis : int;
  pst_mr_theorem : int;
  pst_mr_excl_mid : int;
  pst_width : int;
  pst_height : int;
  pst_size : int;
}

and assumption = {
  asm_id : int;
  asm_lhs : formula;
  asm_rhs : formula;
  asm_hconsumed : heap_atom list;
  asm_trace : trace_item list;
} [@@deriving fields]

and infer_entail = {
  ife_ptree : proof_tree option;
  ife_good_lemma_ptree : bool;
  ife_rdefns : rel_defns;
  ife_goal_origin : goal;
  ife_entail_inferred : entailment;
}

and infer_entails = infer_entail list

and infer_action = {
  iat_pmode : proof_mode;
  iat_constr : infer_constraint_typ;
}

and cache_rule = {
  crl_star_data : rule list;
  crl_star_view : rule list;
  crl_hypothesis : rule list;
  crl_theorem : rule list;
}

and trace_stats = {
  tst_size : int;
  tst_star_data : int;
  tst_star_view : int;
  tst_view_right : int;
  tst_induction : int;
  tst_hypothesis : int;
  tst_theorem: int;
  tst_gen_left : int;
  tst_weaken_left : int;
  tst_drop_left : int;
  tst_drop_right : int;
  tst_excmid : int;
  tst_excmid_view_right : int;
  tst_excmid_unkrel_unplan : int;
  tst_excmid_unkrel_plan : int;
  tst_used_hypo_id_excmid : int list;
}

and formula_stats = {
  fst_fvs : var list;
  fst_fhvs : var list;
  fst_fpvs : var list;
  fst_qvs : var list;
  fst_qhvs : var list;
  fst_hvs : var list;
  fst_is_pure : bool;
  fst_has_data : bool;
  fst_has_view : bool;
  fst_has_view_recur : bool;
  fst_has_view_recur_direct : bool;
  fst_has_view_arith_args : bool;
  fst_has_unk_rform : bool;
  fst_has_known_rform : bool;
  fst_num_prels : int;
  fst_num_datas : int;
  fst_num_views : int;
  fst_num_indirect_recur_views : int;
  fst_num_hatoms : int;
  fst_prels : rel_form list;
  fst_datas : data_form list;
  fst_views : view_form list;
  fst_rforms : rel_form list;
  fst_hatoms : heap_atom list;
  fst_hatom_heads : heap_atom list;
  fst_hatom_tails : heap_atom list;
  fst_hatom_hdtls : heap_atom list;
  fst_data_names : string list;
  fst_view_names : string list;
  fst_view_split : view_split list;
  fst_data_split : data_split list;
  fst_pure_pfs : pure_form list;
  fst_component : quantifier list * heap_form * pure_form;
}

and derived_group = {
  drg_hatoms : heap_atom list;   (* hatoms obtained from one-step deriving *)
  drg_level : int;
}

and trace_item = {
  tri_rule : rule;
  tri_lhs : formula;
  tri_rhs : formula;
  tri_lhs_size : int;
  tri_rhs_size : int;
  tri_ent_size : int;
}

and derivation = {
  drv_kind : derivation_kind;
  drv_heur : proof_heuristic;
  drv_rule : rule;
  drv_goal : goal;
}

and derivation_kind =
  | DrvStatus of mvlogic
  | DrvSubgoals of goal list
  | DrvBackjump of (goal list * entail_id)

and prove_action =
  | PraDrv of derivation
  | PraRule of rule
  (* | PraBackjump of rule *)  (* TODO *)

and prover_threshold = {
  pth_tree_max_width : int;
  pth_goal_max_depth_unfold_group : int;
  pth_goal_unfold_right_intensive : bool;
  pth_lemma_max_num_infer_per_goal : int;
  pth_lemma_max_infer_assumpts : int;
  pth_trace_max_length : int;
  pth_trace_max_length_uninst_var : int;
  pth_trace_max_length_gen_left : int;
  pth_trace_max_length_check_unsat : int;
  pth_trace_min_length_mining : int;
  pth_trace_min_length_inconsist : int;
  pth_trace_max_induction : int;
  pth_trace_max_hypothesis : int;
  pth_trace_max_view_right : int;
}

and infer_rdefn = {
  ird_rdefns : rel_defn list;
  ird_solver : infer_solver;
}

and infer_rdefns = infer_rdefn list

and verify_ifent = {
  vif_ifents : infer_entail list;
  vif_continue : bool;
  vif_msg : string;
}

and verify_ifents = verify_ifent list

and infer_state = {
  ist_prog : program;
  ist_mode : proof_mode;
  ist_constr : infer_constraint_typ;
  ist_partial : bool;
  ist_start_time : float;
  mutable ist_interact : bool;
  mutable ist_inferred_ents : entailment list;
  mutable ist_failed_ents : entailment list;
  ist_lhs_vars : var list;
  ist_rhs_vars : var list;
}

and prover_state = {
  prs_prog : program;
  prs_threshold : prover_threshold;
  mutable prs_start_time : float;
  mutable prs_timeout : float;
  mutable prs_interact : bool;
  mutable prs_stats : PE.stats_entail;
  mutable prs_theorems : theorem list;
  mutable prs_infer_lemma_attempted : string list;
  mutable prs_assums : assumption list;
  mutable prs_counter_theorems : counter_theorem list;
}

exception EMvl of mvlogic option
exception EPrio of (priority * string)
exception ERules of rule list
exception EPtree of proof_tree
exception EPtrees of proof_tree list
exception EAssums of assumption list
exception ERdefns of rel_defn list
exception ELemmas of lemma list
exception ELemmaTemplates of lemma_template list
exception EEnts of entailment list
exception EIfents of infer_entail list
exception EVifent of verify_ifent

let time_choose_hypo = ref 0.
let time_choose_infer = ref 0.
let time_choose_theorem = ref 0.

(*****************************************************************)
(*******************         Exception         *******************)

let raise_prio ?(msg="") prio = raise (EPrio (prio, msg))

let raise_prio_high msg = raise_prio PrioHigh ~msg:msg

let raise_prio_low msg = raise_prio PrioLow ~msg:msg

let raise_rdefns rds = raise (ERdefns rds)

let raise_rules rs = raise (ERules rs)

let raise_lemmas lms = raise (ELemmas lms)

let raise_lemma_templates lmts = raise (ELemmaTemplates lmts)

let raise_ents ents = raise (EEnts ents)

let raise_ifents ifents = raise (EIfents ifents)

let raise_vifent vifent = raise (EVifent vifent)

let raise_ptrees ptrees = raise (EPtrees ptrees)

let raise_ptree pt = raise (EPtree pt)

(*****************************************************************)
(*******************         Printings         *******************)

let pr_heap_pos = function
  | HpHead -> "HpHead"
  | HpTail -> "HpTail"
  | HpHdtl -> "HpHdtl"
  | HpUnkn -> "HpUnkn"

let pr_hpos = pr_heap_pos

let pr_hpf (hf, pf) = (pr_hf hf) ^ " & " ^ (pr_pf pf)

let pr_vsplit vsp =
  let sqvars = pr_qvars vsp.vsp_qvars in
  let svf = pr_vf vsp.vsp_head in
  let srest = pr_hpf vsp.vsp_rest in
  svf ^ " ++ " ^ srest ^ " ++ " ^ sqvars

let pr_vsps = pr_listln pr_vsplit

let pr_dsplit dsp =
  let pr_rest (h, p) = (pr_hf h) ^ " & " ^ (pr_pf p) in
  pr_pair pr_df pr_rest (dsp.dsp_head, dsp.dsp_rest)

let pr_dsps = pr_listln pr_dsplit

let pr_unfold_case ufc =
  pr_f ufc.vuc_new_form ^ " (@C: " ^ (pr_int ufc.vuc_view_case_id) ^ ")"

let pr_fold_case fc =
  pr_f fc.vfc_new_form ^ " (@C: " ^ (pr_int fc.vfc_view_case_id) ^ ")"

let pr_ufcs = pr_listln pr_unfold_case

let pr_vfc = pr_fold_case

let pr_vfcs = pr_listln pr_fold_case

let pr_hp hp = (pr_f hp.hp_lhs) ^ " |- " ^ (pr_f hp.hp_rhs)

let pr_hps hps =
  DB.format_msg " HYPOTHESES: " (pr_items ~bullet:"  #" pr_hp hps)

let pr_th th = (pr_f th.th_lhs) ^ " |- " ^ (pr_f th.th_rhs)

let pr_ths ths =
  DB.format_msg " THEOREMS: " (pr_items ~bullet:"  #" pr_th ths)

let pr_weight = pr_float

let rec pr_assumption asm ?(trace=true) ?(consumed=true) =
  let res = (pr_f asm.asm_lhs) ^ " |- " ^ (pr_f asm.asm_rhs) in
  let res =
    if consumed && (asm.asm_hconsumed != []) then
      res ^ "\n    +++ Consumed: " ^ (pr_has asm.asm_hconsumed)
    else res in
  let pr_tri x = "(" ^ (pr_rule x.tri_rule) ^ "; "
                 ^ "@S:" ^ (pr_int x.tri_ent_size) ^ ")" in
  let res =
    if trace then
      asm.asm_trace |> List.rev |>
      pr_list ~sep:"\n       ==> " ~obrace:"[" ~cbrace: "]" pr_tri |>
      (fun s -> res ^ "\n    +++ Trace: " ^ s)
    else res in
  res

and pr_asm asm = pr_assumption asm ~trace:false ~consumed:false

and pr_asms ?(bullet="  # ") asms = pr_items ~bullet:bullet pr_asm asms

and pr_heur = function
  | PhHM -> "Human"
  | PhML -> "ML"

and pr_mrule mrule : string =
  match mrule with
  | MrStarData -> "MrStarData"
  | MrStarView -> "MrStarView"
  | MrViewRight -> "MrViewRight"
  | MrInduction -> "MrInduction"
  | MrHypothesis -> "MrHypothesis"
  | MrTheorem -> "MrTheorem"
  | MrExclMid -> "MrExclMid"
  | MrGenLeft -> "MrGenLeft"
  | MrAxiom -> "MrAxiom"
  | MrNormalize -> "MrNormalize"
  | MrUnknown -> "MrUnknown"

and pr_rsd rsd =
  let d1, d2 = rsd.rsd_lg_data, rsd.rsd_rg_data in
  let srsd = (pr_df d1) ^ ", " ^ (pr_df d2) in
  let srsd =
    if !DB.debug_deep_mode then
      srsd ^ " +++ lhs-rest: " ^ (pr_hpf rsd.rsd_lg_rest)
      ^ ", rhs-rest: " ^ (pr_hpf rsd.rsd_rg_rest)
    else srsd in
  "STAR-DATA {" ^ srsd
  ^ ", trivial: " ^ (pr_bool rsd.rsd_trivial)
  ^ "}"

and pr_rsv rsv =
  let v1, v2 = rsv.rsv_lg_view, rsv.rsv_rg_view in
  "STAR-VIEW {" ^ (pr_vf v1) ^ ", " ^ (pr_vf v2)
  ^ ", trivial: " ^ (pr_bool rsv.rsv_trivial)
  ^ "}"

and pr_rvl rvl =
  "VIEW-LEFT: {" ^ (pr_vf rvl.rvl_lg_view)
  ^ ", @C:" ^ (pr_int rvl.rvl_fold_case.vfc_view_case_id)
  ^ "}"

and pr_rvr rvr =
  "VIEW-RIGHT: {" ^ (pr_vf rvr.rvr_rg_view)
  ^ ", @C:" ^ (pr_int rvr.rvr_unfold_case.vuc_view_case_id)
  ^ ", trivial: " ^ (pr_bool rvr.rvr_trivial)
  ^ "}"

and pr_rid rid =
  let ids = List.map (fun x -> x.vuc_view_case_id) rid.rid_unfold_cases in
  let sids = pr_list ~sep:"," pr_int ids in
  "INDUCTION: {" ^ (pr_vf rid.rid_lg_view) ^
  ", record IH: " ^ (pr_bool rid.rid_record_hypo) ^
  ", @C:" ^ sids ^ "}"

and pr_rhp rhp =
  let hp = (pr_f rhp.rhp_hp.hp_lhs) ^ " |- " ^ (pr_f rhp.rhp_hp.hp_rhs) in
  let ssts = "  +++ ssts: " ^ (pr_ssts rhp.rhp_unf_ssts) in
  let asms = match rhp.rhp_assums with
    | [] -> ""
    | _ -> "  +++ iassums: " ^ (pr_asms rhp.rhp_assums) in
  "HYPOTHESIS: {" ^ hp ^ ssts ^ asms ^ "}"

and pr_rth rth =
  let l, r = rth.rth_th.th_lhs, rth.rth_th.th_rhs in
  "THEOREM: {"
  ^ (pr_f l) ^ " |- " ^ (pr_f r)
  ^ "  +++ left: " ^ (pr_bool rth.rth_left)
  ^ "  +++ ssts: " ^ (pr_ssts rth.rth_unf_ssts) ^ "}"

and pr_reql reql =
  "EQUAL-LEFT: {LHS: " ^ (pr_f reql.reql_lg) ^ "}"

and pr_rexl rexl =
  "EXIST-LEFT: {LHS: " ^ (pr_f rexl.rexl_lg) ^ "}"

and pr_rexr rexr =
  "EXIST-RIGHT: {RHS: " ^ (pr_f rexr.rexr_rg) ^ "}"

and pr_reml reml =
  "EMP-LEFT: {LHS: " ^ (pr_f reml.reml_lg) ^ "}"

and pr_remr remr =
  "EMP-RIGHT: {RHS: " ^ (pr_f remr.remr_rg) ^ "}"

and pr_rdl rdl = "DROP-LEFT: {" ^ (pr_pf rdl.rdl_lg_drop) ^ "}"

and pr_rdr rdr = "DROP-RIGHT: {" ^ (pr_pf rdr.rdr_rg_drop) ^ "}"

and pr_rur rur =
  "UNFOLD-RELATION: {" ^ (pr_list pr_rf (rur.rur_lg_rels @ rur.rur_rg_rels)) ^ "}"

and pr_rpe rpe =
  let l, r = rpe.rpe_lg, rpe.rpe_rg in
  "PURE-ENTAIL: {Entail: " ^ (pr_f l) ^ " |- " ^ (pr_f r)
  ^ ". Status: " ^ (pr_mvl rpe.rpe_status) ^ "}"

and pr_rfl rfl =
  "FALSE-LEFT: {" ^ "LHS: " ^ (pr_f rfl.rfl_lg) ^ "}"

and pr_ems ems =
  let rhps = List.map (fun r -> RlHypothesis r) ems.ems_hypothesis in
  let rvrs = List.map (fun r -> RlViewRight r) ems.ems_view_right in
  let rths = List.map (fun r -> RlTheorem r) ems.ems_theorem in
  pr_list pr_rule (rhps @ rvrs @ rths)

and pr_rem rem =
  match rem.rem_cases with
  | [emc] -> "EXCL-MID: {" ^ "Cond: " ^ (pr_pf emc.emc_pure_cond) ^ "}"
  | _ ->
    "EXCL-MID: {"
    ^ "Seed cond: " ^ (pr_pf rem.rem_seed_cond)
    ^ " +++ Seed rules: " ^ (pr_lcs (pr_ems rem.rem_seed_rule)) ^ "}"

and pr_rir rir =
  "INFER-RELATION: {" ^ "ASSUMPTION: " ^ (pr_asm rir.rir_assumption) ^ "}"

and pr_rie rie =
  "INFER-ENTAIL: {"
  ^ "GOAL ORIGIN: " ^ (pr_gc rie.rie_goal) ^ "; "
  ^ "RELATIONS: " ^ (pr_rds rie.rie_rdefns) ^ "; "
  ^ "ENTAIL INFERRED: " ^ (pr_ent rie.rie_entail) ^ "}"

and pr_rgl rgl =
  "GEN-LEFT: {\n" ^
  "    # New LHS: " ^ (pr_f rgl.rgl_new_lg) ^ " \n" ^
  "    # Gen exps: " ^ (pr_exps rgl.rgl_gen_exps)  ^ "\n" ^
  (match rgl.rgl_base_hypo_unf with
    | None -> ""
    | Some (hp, unf) ->
      let rnm = hp.hp_renaming |> List.map Pair.reverse in
      let lhs, rhs = Pair.fold (rename_var_f rnm) hp.hp_lhs hp.hp_rhs in
      "    # Based entailment: (" ^ (pr_int hp.hp_ent_id) ^ ") " ^
      (pr_f lhs) ^ " |- " ^ (pr_f rhs)) ^
  "}"

and pr_rwl rwl =
  "WEAKEN-LEFT: {\n" ^
  "    # New LHS: " ^ (pr_f rwl.rwl_new_lg) ^ " \n" ^
  "    # Weaken pf: " ^ (pr_pf rwl.rwl_dropped_pf) ^ "\n" ^
  (match rwl.rwl_base_hypo_unf with
    | None -> ""
    | Some (hp, unf) ->
      let rnm = hp.hp_renaming |> List.map Pair.reverse in
      let lhs, rhs = Pair.fold (rename_var_f rnm) hp.hp_lhs hp.hp_rhs in
      "    # Based entailment: (" ^ (pr_int hp.hp_ent_id) ^ ") " ^
      (pr_f lhs) ^ " |- " ^ (pr_f rhs)) ^
  "}"

and pr_rule rule =
  match rule with
  | RlStarData rsd -> pr_rsd rsd
  | RlStarView rsv -> pr_rsv rsv
  | RlViewLeft rvl -> pr_rvl rvl
  | RlViewRight rvr -> pr_rvr rvr
  | RlInduction rid -> pr_rid rid
  | RlHypothesis rhp -> pr_rhp rhp
  | RlTheorem rth -> pr_rth rth
  | RlPureEntail rpe -> pr_rpe rpe
  | RlEqualLeft reql -> pr_reql reql
  | RlExistsLeft rexl -> pr_rexl rexl
  | RlExistsRight rexr -> pr_rexr rexr
  | RlEmpLeft reml -> pr_reml reml
  | RlEmpRight remr -> pr_remr remr
  | RlDropLeft rdl -> pr_rdl rdl
  | RlDropRight rdr -> pr_rdr rdr
  | RlUnfoldRel rur -> pr_rur rur
  | RlFalseLeft rfl -> pr_rfl rfl
  | RlExclMid rem -> pr_rem rem
  | RlInferRel rir -> pr_rir rir
  | RlInferEnt rie -> pr_rie rie
  | RlGenLeft rgl -> pr_rgl rgl
  | RlWeakenLeft rwl -> pr_rwl rwl

and pr_rules rules =
  pr_list ~sep:"\n" ~obrace:"[" ~cbrace:"]" ~indent:0 pr_rule rules

and pr_ruless ruless =
  let pr_rules rules =
    pr_list ~sep:"\n" ~obrace:"[" ~cbrace:"]" ~extra:"  " pr_rule rules in
  pr_items ~bullet:"#" pr_rules ruless

and pr_gent goal =
  let consumed = pr_has goal.gl_hconsumed in
  (pr_f goal.gl_lhs) ^ " +++ " ^ consumed ^ " |- " ^ (pr_f goal.gl_rhs)

and print_trace_item tri =
  "(" ^ (pr_rule tri.tri_rule) ^
  ";  @S: " ^ (pr_int tri.tri_ent_size) ^
  ";  @ENT: " ^ (pr_entlr tri.tri_lhs tri.tri_rhs) ^ ")"

and pr_tri tri  = print_trace_item tri

and print_goal ?(indent=0) ?(detail=true) ?(trace=true) ?(consumed=true) goal =
  let res = pr_indent indent in
  let res = res ^ "GOAL: { \n" in
  let res = res ^ "  - Entail (" ^ (pr_int goal.gl_ent_id) ^ "): " ^
            (pr_f goal.gl_lhs) ^ " |- " ^ (pr_f goal.gl_rhs) ^ "\n" in
  let res =
    if (goal.gl_hconsumed == []) || (consumed = false) then res
    else res ^ "  - Consumed: " ^ (pr_has goal.gl_hconsumed) ^ "\n" in
  let res = match goal.gl_proof_mode with
    | PrfInferAll | PrfInferBasic | PrfInferLhs | PrfInferRhs ->
      let context = match goal.gl_assums with
        | [] -> "[]"
        | _ -> "\n" ^ (pr_asms ~bullet:"     #" goal.gl_assums) in
      res ^ "  - Infer contexts: " ^ context ^ "\n"
    | _ -> res in
  let res =
    if not !DB.debug_deep_mode then res
    else res ^ "  - Unproved RHS: \
               " ^ (pr_pfs goal.gl_rhs_unproved_patoms) ^ "\n" in
  let res =
    if not !DB.debug_deep_mode then res
    else res ^ "  - Hypos: " ^ (pr_hps goal.gl_hypos) ^ "\n" in
  let res =
    if trace then
      goal.gl_trace |> List.rev |>
      pr_list ~sep:"\n       ==> " ~obrace:"[" ~cbrace: "]" pr_tri |>
      (fun s -> res ^ "  - Trace: " ^ s)
    else res in
  res ^ "}"

and pr_g goal =
  print_goal ~indent:0 ~detail:true ~trace:true ~consumed:true goal

(* print concise *)
and pr_gc goal = (pr_f goal.gl_lhs) ^ " |- " ^ (pr_f goal.gl_rhs)

let print_goals ?(indent=0) goals =
  let pr_g = print_goal ~indent:indent in
  pr_list ~sep:"\n" ~obrace:"[" ~cbrace:"]" pr_g goals

let pr_gs goals =
  print_goals ~indent:0 goals

let prid_derivation ?(indent=0) drv =
  let sid = pr_indent indent in
  match drv.drv_kind with
  | DrvSubgoals gs ->
    let gls = match gs with
      | [] -> "No entailments"
      | [g] -> pr_gc g
      | _ -> "\n    # " ^ (pr_list ~sep:(sid ^ "\n    # ") pr_gc gs) in
    let res = sid ^ "Sub-Goals Inter: {" ^ "\n" in
    let res = res ^ sid ^ "  + Entails: " ^ gls ^ "\n" in
    let res = res ^ sid ^ "  + Rule: " ^ (pr_rule drv.drv_rule) in
    res ^ "}"
  | DrvStatus tvl ->
    let res = sid ^ "Sub-Goals Atom: {" ^ "\n" in
    let res = res ^ sid ^ "  + State: " ^ (pr_mvl tvl) ^ "\n" in
    let res = res ^ sid ^ "  + Rule: " ^ (pr_rule drv.drv_rule) in
    res ^ "}"
  | DrvBackjump (_, eid) ->
    let res = "Backjump to entailment (" ^ (pr_int eid) ^ "): {\n" in
    (* let res = res ^ sid ^ "  + Entails: " ^  ^ "\n" in *)
    let res = res ^ sid ^ "  + Rule: " ^ (pr_rule drv.drv_rule) in
    res ^ "}"

let pr_drv = prid_derivation ~indent:0

let prid_derivations ?(indent=0) derivations =
  let pr_drv = prid_derivation ~indent:indent in
  match derivations with
  | [] | [_] -> pr_list ~obrace:"[" ~cbrace:"]" pr_drv derivations
  | _ -> pr_items ~bullet:" -" ~obrace:"[" ~cbrace:"]" pr_drv derivations

let pr_drvs = prid_derivations ~indent:0

let pr_rule_drvs drvs =
  let rules = List.map (fun x -> x.drv_rule) drvs in
  pr_list ~sep:"\n" ~obrace:"[" ~cbrace:"]" pr_rule rules

let pr_rule_drvss drvss =
  let pr_rule_drvs drvs =
    let rules = List.map (fun x -> x.drv_rule) drvs in
    pr_list ~sep:"\n" ~obrace:"[" ~cbrace:"]" ~extra:"  " pr_rule rules in
  pr_items ~bullet:"#"  pr_rule_drvs drvss

let pr_prio prio = match prio with
  | PrioEqual -> "PrioEqual"
  | PrioLow ->  "PrioLow"
  | PrioHigh ->  "PrioHigh"

let pr_ptree_status pts = match pts with
  | PtValid _ -> "PtValid"
  | PtInvalid -> "PtInvalid"
  | PtUnkn msg -> "PtUnknown(" ^ msg ^ ")"
  | PtInfer ptc ->
    let assumptions = pr_asms ~bullet:"     #" ptc.ptc_assums in
    if (EString.exists assumptions "#") then
      "PtInfer, with assumptions: \n" ^ assumptions
    else "PtInfer, with assumptions: " ^ assumptions

let pr_ptree pt = match pt with
  | PtSearch pts -> pr_ptree_status pts.pts_status
  | PtDerive ptd -> pr_ptree_status ptd.ptd_status

let pr_ptree_detail pt =
  let pr_st st = match st with
    | PtSearch pts -> "[Search]: " ^ (pr_gent pts.pts_goal)
    | PtDerive ptd ->
      "[Derived " ^ (pr_rule ptd.ptd_rule) ^ "]: " ^  (pr_gent ptd.ptd_goal) in
  match pt with
  | PtSearch pts ->
    "Proof Tree Search: \n"
    ^ "  Goal: " ^ (pr_gent pts.pts_goal) ^ "\n"
    ^ "  Status: " ^ (pr_ptree_status pts.pts_status) ^ "\n"
    ^ "  Sub-trees: "
    ^ (pr_items ~bullet:"     #" pr_st pts.pts_sub_trees)
  | PtDerive ptd ->
    "Proof Tree Derive: \n"
    ^ "  Goal: " ^ (pr_gent ptd.ptd_goal) ^ "\n"
    ^ "  Status: " ^ (pr_ptree_status ptd.ptd_status) ^ "\n"
    ^ "  Sub-trees: \n"
    ^ (pr_items ~bullet:"     #" pr_st ptd.ptd_sub_trees)

let pr_infer_state ist =
  "Mode: " ^ (pr_prm ist.ist_mode) ^ "; "
  ^ "Constr: " ^ (pr_infer_constr_typ ist.ist_constr) ^ "; "
  ^ ("Lvars: " ^ (pr_vs ist.ist_lhs_vars)) ^ "; "
  ^ ("Rvars: " ^ (pr_vs ist.ist_rhs_vars))

let pr_ist = pr_infer_state

let pr_infer_action iat =
  "(" ^ (pr_prm iat.iat_pmode) ^ ", " ^ (pr_infer_constr_typ iat.iat_constr) ^ ")"

let pr_iat = pr_infer_action

let pr_iats = pr_list pr_iat

let pr_infer_entail ife =
  "Infer entailment result: \n"
  ^ "  + Goal origin: " ^ (pr_gc ife.ife_goal_origin) ^ "\n"
  ^ "  + Proof tree: " ^ (pr_opt pr_ptree ife.ife_ptree) ^ "\n"
  ^ "  + Is good lemma tree: " ^ (pr_bool ife.ife_good_lemma_ptree) ^ "\n"
  ^ "  + Relations: " ^ (pr_rds ife.ife_rdefns) ^ "\n"
  ^ "  + Entailment inferred: " ^ (pr_ent ife.ife_entail_inferred)

let pr_ife = pr_infer_entail

let pr_ifes = pr_items ~bullet:"  @@" pr_ife

let pr_isv = pr_infer_solver

let pr_infer_rdefn ird =
  "  # Rdefns: " ^ ( pr_rdsl ird.ird_rdefns)
  ^ "\n   # Solver: " ^ (pr_isv ird.ird_solver)

let pr_ird = pr_infer_rdefn

let pr_irds = pr_items ~bullet:"  +++\n" pr_ird

let pr_verify_ifent vif =
  "  # Infer entails: " ^ ( pr_ifes vif.vif_ifents)
  ^ "\n   # Continue: " ^ (pr_bool vif.vif_continue)
  ^ "\n   # Msg: " ^  vif.vif_msg

let pr_vif = pr_verify_ifent

let pr_vifs = pr_items ~bullet:"  +++\n" pr_vif

(*****************************************************************)
(*******************      fold, map, iter      *******************)

(* TODO: implement the folde, map, iter over the proof tree *)

type iter_goal_t = goal -> unit
type iter_rule_t = rule -> unit
type iter_ptcore_t = proof_tree_core -> unit option
type iter_ptcrg_t = iter_ptcore_t * iter_goal_t * iter_rule_t

let rec iter_goal (fg: iter_goal_t) g : unit = fg g

let rec iter_rule (fr: iter_rule_t) r : unit = fr r

let rec iter_ptcore ((fp, fg, fr) as fa : iter_ptcrg_t) ptc =
  match fp ptc with
  | Some res -> res
  | None ->
    let _ = iter_rule fr ptc.ptc_rule in
    let _ = iter_goal fg ptc.ptc_goal in
    List.iter (iter_ptcore fa) ptc.ptc_sub_trees

type 'a fold_goal_t = 'a -> goal -> 'a option
type 'a fold_rule_t = 'a -> rule -> 'a option
type 'a fold_ptcore_t = 'a -> proof_tree_core -> 'a option
type 'a fold_ptsearch_t = 'a -> proof_tree_search -> 'a option
type 'a fold_ptderive_t = 'a -> proof_tree_derive -> 'a option
type 'a fold_ptcrg_t = 'a fold_ptcore_t * 'a fold_goal_t * 'a fold_rule_t
type 'a fold_ptsrg_t = 'a fold_ptsearch_t * 'a fold_goal_t * 'a fold_rule_t
type 'a fold_ptdrg_t = 'a fold_ptderive_t * 'a fold_goal_t * 'a fold_rule_t

let rec fold_goal (fg: 'a fold_goal_t) acc g : 'a =
  match fg acc g with
  | Some res -> res
  | None -> acc

let rec fold_rule (fr: 'a fold_rule_t) acc r : 'a =
  match fr acc r with
  | Some res -> res
  | None -> acc

let rec fold_ptcore ((fp, fg, fr) as fa : 'a fold_ptcrg_t) acc ptc =
  match fp acc ptc with
  | Some res -> res
  | None ->
    let acc = fold_rule fr acc ptc.ptc_rule in
    let acc = fold_goal fg acc ptc.ptc_goal in
    List.fold_left (fun nacc pt ->
      fold_ptcore fa nacc pt) acc ptc.ptc_sub_trees

(*****************************************************************)
(******************       heap splitting      ********************)

let rec mk_view_unfold_cases prog orig_form view rest qvars =
  DB.trace_3 "mk_view_unfold_cases" (pr_f, pr_vf, pr_qvars, pr_ufcs)
    orig_form view qvars
    (fun () -> mk_view_unfold_cases_x prog orig_form view rest qvars)

and mk_view_unfold_cases_x prog orig_form view rest qvars =
  unfold_vform prog.prog_views view |>
  List.map (fun vdc ->
    let new_form = mk_hstar_f_hf vdc.vdc_form (fst rest) |>
                   (fun t -> mk_hstar_f_pf t (snd rest)) |>
                   mk_qform qvars |> NO.simplify_all in
    let view_case_form = mk_qform qvars vdc.vdc_form in
    { vuc_view = view ;
      vuc_orig_form = orig_form ;
      vuc_view_case_id = vdc.vdc_id;
      vuc_view_case_form = view_case_form;
      vuc_base_case = vdc.vdc_base_case;
      vuc_new_form = new_form;
      vuc_num_datas = new_form |> collect_data_form |> List.length;
      vuc_num_views = new_form |> collect_view_form |> List.length; })

let rec mk_view_fold_case prog orig_form view vdc rest =
  DB.trace_2 "mk_view_fold_case" (pr_f, pr_vf, pr_vfc) orig_form view
    (fun () -> mk_view_fold_case_x prog orig_form view vdc rest)

and mk_view_fold_case_x prog orig_form view vdc rest =
  let new_form = mk_hstar_hf_vf (fst rest) view |>
                 (fun t -> mk_fbase t (snd rest)) |> NO.simplify_all in
  { vfc_view = view ;
    vfc_orig_form = orig_form ;
    vfc_view_case_id = vdc.vdc_id;
    vfc_view_case_form = vdc.vdc_form;
    vfc_base_case = vdc.vdc_base_case;
    vfc_new_form = new_form;
    vfc_num_datas = new_form |> collect_data_form |> List.length;
    vfc_num_views = new_form |> collect_view_form |> List.length; }

let mk_data_split head rest qvars full =
  { dsp_head = head;
    dsp_rest = rest;
    dsp_qvars = qvars;
    dsp_full = full }

let mk_view_split prog orig_form head rest qvars =
  let vdefn = find_view_defn prog.prog_views head.viewf_name in
  let ufcases = mk_view_unfold_cases prog orig_form head rest qvars in
  { vsp_head = head;
    vsp_rest = rest;
    vsp_view_recur = vdefn.view_recurt;
    vsp_qvars = qvars;
    vsp_unfold_cases = ufcases;
    vsp_orig_form = orig_form }

(* split one element from a list,
   return all possible pairs of split element and remained element *)
let split_one (xs : 'a list) : ('a * 'a list) list =
  let rec split acc head tail = match tail with
    | [] -> acc
    | x::xs ->
      let acc = acc @ [(x, head @ xs)] in split acc (head @ [x]) xs in
  split [] [] xs


(* split one data_form from a formula
   return all possible pairs of split element and remained element *)
let rec split_data (f: formula) : data_split list =
  DB.trace_1 "split_data" (pr_f, pr_dsps) f
    (fun () -> split_data_x f)

and split_data_x (f: formula) : data_split list =
  let rec split_df hf : (data_form * heap_form) list =
    match hf with
    | HEmp _ -> []
    | HAtom (dfs, vfs, p) ->
      split_one dfs |> List.map (fun (x, xs) -> (x, HAtom (xs, vfs, p)))
    | HStar (h1, h2, p) ->
      let rs1 = split_df h1 |> List.map (fun (x, y) -> (x, mk_hstar y h2)) in
      let rs2 = split_df h2 |> List.map (fun (x, y) -> (x, mk_hstar h1 y)) in
      rs1 @ rs2
    | HWand _ -> error "split_data: handle HWand later" in
  let rec split f qvars : data_split list =
    match f with
    | FBase (hf, pf, p) ->
      split_df hf |> List.map (fun (x, y) -> mk_data_split x (y, pf) qvars f)
    | FExists (vs, f0, p) -> split f0 ((QExists vs) :: qvars)
    | FForall (vs, f0, p) -> split f0 ((QForall vs) :: qvars) in
  split f []

(* split one view_form from a formula
   return all possible pairs of split element and remained element *)
let rec split_view prog (f: formula) : view_split list =
  DB.trace_1 "split_view" (pr_f, pr_vsps) f
    (fun () -> split_view_x prog f)

and split_view_x prog (f: formula) : view_split list =
  let rec split_vf hf : (view_form * heap_form) list =
    match hf with
    | HEmp _ -> []
    | HAtom (dfs, vfs, p) ->
      split_one vfs |> List.map (fun (x, xs) -> (x, HAtom (dfs, xs, p)))
    | HStar (h1, h2, p) ->
      let rs1 = split_vf h1 |> List.map (fun (x, y) -> (x, mk_hstar y h2)) in
      let rs2 = split_vf h2 |> List.map (fun (x, y) -> (x, mk_hstar h1 y)) in
      rs1 @ rs2
    | HWand _ -> error "split_view: handle HWand later" in
  let rec split f qvars : view_split list =
    match f with
    | FBase (hf, pf, p) ->
      hf |> split_vf |>
      List.map (fun (x, y) -> mk_view_split prog f x (y, pf) qvars)
    | FExists (vs, f0, p) -> split f0 ((QExists vs) :: qvars)
    | FForall (vs, f0, p) -> split f0 ((QForall vs) :: qvars) in
  split f []

let compare_dsp d1 d2 = compare_df d1.dsp_head d2.dsp_head

let compare_vsp v1 v2 = compare_vf v1.vsp_head v2.vsp_head

let find_hatom_heads vdefns hatoms =
  let heads = hatoms |> List.filter (fun ha1 ->
    hatoms |> List.for_all (fun ha2 ->
      not (check_hatom_link vdefns ha2 ha1))) in
  (* DB.hprint "find_hatom_heads: hatoms: " pr_has hatoms; *)
  (* DB.hprint "find_hatom_heads: heads: " pr_has heads; *)
  heads

let find_hatom_tails vdefns hatoms =
  hatoms |> List.filter (fun ha1 ->
    hatoms |> List.for_all (fun ha2 ->
      not (check_hatom_link vdefns ha1 ha2)))

let get_heap_pos fst ha =
  if List.exists (eq_hatom ha) fst.fst_hatom_heads then HpHead
  else if List.exists (eq_hatom ha) fst.fst_hatom_tails then HpTail
  else if List.exists (eq_hatom ha) fst.fst_hatom_hdtls then HpHdtl
  else HpUnkn

let rec find_unproved_conjuncts prog lhs rhs : pure_form list =
  DB.trace_2 "find_unproved_conjuncts" (pr_f, pr_f, pr_pfs) lhs rhs
    (fun () -> find_unproved_conjuncts_x prog lhs rhs)

and find_unproved_conjuncts_x prog lhs rhs : pure_form list =
  let plhs = lhs |>
             NO.encode_formula prog in
  let prhs = rhs |>
             extract_pf |>
             NO.simplify_all_pf |>
             NO.push_qvars_inward_pf in
  (* do not collect quantified formulae since Z3 doesn't handle them well *)
  let conjs = collect_pure_conjuncts_pf prhs |>
              List.filter (fun pf -> match pf with
                | PForall _ | PExists _ -> false
                | _ -> true) in
  List.filter (fun x -> PT.check_imply_slice_lhs plhs x != MvlTrue) conjs

(********************************************************************)
(*******************         Constructors         *******************)

let mk_assum lhs rhs hconsumed trace : assumption =
  (* let lhs, rhs, rnm = rename_all_var_entail lhs rhs in *)
  let rhs = NO.simplify_exists_var_by_equal rhs in
  (* let hconsumed = List.map (rename_var_ha rnm) hconsumed in *)
  { asm_id = new_assumption_id ();
    asm_lhs = lhs;
    asm_rhs = rhs;
    asm_hconsumed = hconsumed;
    asm_trace = trace; }

let mk_assum_pure lhs rhs : assumption =
  let lhs, rhs, _ = rename_all_var_entail_pure lhs rhs in
  let rhs = NO.simplify_exists_var_by_equal_pf rhs in
  { asm_id = new_assumption_id ();
    asm_lhs = mk_fpure lhs;
    asm_rhs = mk_fpure rhs;
    asm_hconsumed = [];
    asm_trace = []; }

let mk_assum_false lhs hconsumed trace : assumption =
  let rhs = mk_ffalse no_pos in
  let lhs, rnm = rename_all_var lhs in
  let hconsumed = List.map (rename_var_ha rnm) hconsumed in
  { asm_id = new_assumption_id ();
    asm_lhs = lhs;
    asm_rhs = rhs;
    asm_hconsumed = hconsumed;
    asm_trace = trace; }

let mk_trace_item goal rule =
  let lst, rst = goal.gl_lstats, goal.gl_rstats in
  let lhs_size = lst.fst_num_datas + lst.fst_num_views in
  let rhs_size = rst.fst_num_datas + rst.fst_num_views in
  { tri_rule = rule;
    tri_lhs = goal.gl_lhs;
    tri_rhs = goal.gl_rhs;
    tri_lhs_size = lhs_size;
    tri_rhs_size = rhs_size;
    tri_ent_size = lhs_size + rhs_size; }


let mk_trace_stats prog traces =
  let star_data = ref 0 in
  let star_view = ref 0 in
  let view_right = ref 0 in
  let induction = ref 0 in
  let hypothesis = ref 0 in
  let theorem = ref 0 in
  let gen_left = ref 0 in
  let weaken_left = ref 0 in
  let drop_left = ref 0 in
  let drop_right = ref 0 in
  let excl_mid_view_right = ref 0 in
  let excl_mid = ref 0 in
  let excl_mid_unkrel_unplanned = ref 0 in
  let excl_mid_unkrel_planned = ref 0 in
  let excl_mid_hypo_ids = ref [] in
  let _ = List.iter (fun t ->
    match t.tri_rule with
    | RlStarData _ -> star_data := !star_data + 1
    | RlStarView _ -> star_view := !star_view + 1
    | RlViewRight _ -> view_right := !view_right + 1
    | RlInduction _ -> induction := !induction + 1
    | RlHypothesis _ -> hypothesis := !hypothesis + 1
    | RlTheorem _ -> theorem := !theorem + 1
    | RlGenLeft _ -> gen_left := !gen_left + 1
    | RlWeakenLeft _ -> weaken_left := !weaken_left + 1
    | RlDropLeft _ -> drop_left := !drop_left + 1
    | RlDropRight _ -> drop_right := !drop_right + 1
    | RlExclMid rem ->
      excl_mid := !excl_mid + 1;
      let _ = match rem.rem_cases with
        | [emc] ->
          let has_unk_rform = has_unk_rform_pf prog.prog_rels emc.emc_pure_cond in
          if has_unk_rform && (emc.emc_type = EmctUnplanned) then
            excl_mid_unkrel_unplanned := !excl_mid_unkrel_unplanned + 1
          else excl_mid_unkrel_planned := !excl_mid_unkrel_planned + 1
        | _ -> () in
      if rem.rem_seed_rule.ems_hypothesis != [] then (
        let rhp = List.hd rem.rem_seed_rule.ems_hypothesis in
        excl_mid_hypo_ids := !excl_mid_hypo_ids @ [rhp.rhp_hp.hp_ent_id]);
      if rem.rem_seed_rule.ems_view_right != [] then
        excl_mid_view_right := !excl_mid_view_right + 1;
    | _ -> ()) traces in
  { tst_size = List.length traces;
    tst_star_data = !star_data;
    tst_star_view = !star_view;
    tst_view_right = !view_right;
    tst_induction = !induction;
    tst_hypothesis = !hypothesis;
    tst_theorem = !theorem;
    tst_gen_left = !gen_left;
    tst_weaken_left = !weaken_left;
    tst_drop_left = !drop_left;
    tst_drop_right = !drop_right;
    tst_excmid = !excl_mid;
    tst_excmid_view_right = !excl_mid_view_right;
    tst_excmid_unkrel_unplan = !excl_mid_unkrel_unplanned;
    tst_excmid_unkrel_plan = !excl_mid_unkrel_planned;
    tst_used_hypo_id_excmid = !excl_mid_hypo_ids; }

let mk_formula_stats prog f : formula_stats =
  let vdefns = prog.prog_views in
  let qvars, hf, pf = extract_components_f f in
  let qvs = vars_of_qvars qvars in
  let prels = collect_rform_pf pf in
  let num_prels = List.length prels in
  let dsplit = f |> split_data |> List.sortd compare_dsp in
  let vsplit = f |> split_view prog |> List.sortd compare_vsp in
  let datas = collect_data_form f in
  let views = collect_view_form f in
  let rforms = collect_rform f in
  let hatoms = collect_hatom f in
  let data_names = datas |> List.map (fun d -> d.dataf_name) |> dedup_ss in
  let view_names = views |> List.map (fun v -> v.viewf_name) |> dedup_ss in
  let num_datas, num_views = List.length datas, List.length views in
  let has_view_recur = List.exists (is_recur_vf vdefns) views in
  let has_view_recur_direct = List.exists (is_recur_direct_vf vdefns) views in
  (* DB.hprint "Formula: " pr_f f; *)
  let hatom_heads = find_hatom_heads prog.prog_views hatoms in
  let hatom_tails = find_hatom_tails prog.prog_views hatoms in
  let hatom_hdtls = List.intersect eq_hatom hatom_heads hatom_tails in
  let hatom_heads = List.diff eq_hatom hatom_heads hatom_hdtls in
  let hatom_tails = List.diff eq_hatom hatom_tails hatom_hdtls in
  let pure_pfs = f |> collect_pure_conjuncts |> List.exclude is_true_pf in
  let num_indirect_recur_views = views |> List.filter (fun vf ->
    is_recur_indirect_vf vdefns vf) |> List.length in
  let stats = {
    fst_fvs = fv f;
    fst_fhvs = fhv f;
    fst_fpvs = fv_pf pf;
    fst_qvs = qvs;
    fst_qhvs = intersect_vs qvs (fv_hf hf);
    fst_hvs = fv_hf hf;
    fst_is_pure = (views=[] && datas=[]);
    fst_has_data = (datas != []);
    fst_has_view = (views != []);
    fst_has_view_recur = has_view_recur;
    fst_has_view_recur_direct = has_view_recur_direct;
    fst_has_view_arith_args = List.exists has_int_arg_vf views;
    fst_has_unk_rform = has_unk_rform prog.prog_rels f;
    fst_has_known_rform = has_known_rform prog.prog_rels f;
    fst_num_prels = num_prels;
    fst_num_datas = num_datas;
    fst_num_views = num_views;
    fst_num_hatoms = num_datas + num_views;
    fst_num_indirect_recur_views = num_indirect_recur_views;
    fst_prels = prels;
    fst_datas = datas;
    fst_views = views;
    fst_rforms = rforms;
    fst_hatoms = hatoms;
    fst_hatom_heads = hatom_heads;
    fst_hatom_tails = hatom_tails;
    fst_hatom_hdtls = hatom_hdtls;
    fst_data_names = data_names;
    fst_view_names = view_names;
    fst_pure_pfs = pure_pfs;
    fst_data_split = dsplit;
    fst_view_split = vsplit;
    fst_component = (qvars, hf, pf);
  } in
  stats

let mk_goal_stats prog lst rst =
  let vdefns = prog.prog_views in
  let view_names = dedup_ss (lst.fst_view_names @ rst.fst_view_names) in
  let data_names = dedup_ss (lst.fst_data_names @ rst.fst_data_names) in
  let views = lst.fst_views @ rst.fst_views in
  let lvnames, rvnames = lst.fst_view_names, rst.fst_view_names in
  let rforms = lst.fst_rforms @ rst.fst_rforms in
  let rfvs = rforms |> fv_rfs |> dedup_vs in
  let rfnames = rforms |> List.map (fun rf -> rf.prel_name) |> dedup_ss in
  let has_common_vname = intersected_ss lvnames rvnames in
  let has_common_hvars =
    let lhvs = lst.fst_hatoms |> fv_has in
    let rhvs = rst.fst_hatoms |> fv_has in
    (intersected_vs lhvs rhvs) in
  let num_indirect_recur_views = views |> List.filter (fun vf ->
    is_recur_indirect_vf vdefns vf) |> List.length in
  let has_diff_vname = not (eq_ss lvnames rvnames) in
  { gst_fvs = dedup_vs (lst.fst_fvs @ rst.fst_fvs);
    gst_num_rfvars = List.length rfvs;
    gst_num_rfnames = List.length rfnames;
    gst_view_names = view_names;
    gst_data_names = data_names;
    gst_num_view_names = List.length view_names;
    gst_num_data_names = List.length data_names;
    gst_num_hatoms = lst.fst_num_hatoms + rst.fst_num_hatoms;
    gst_num_indirect_recur_views = num_indirect_recur_views;
    gst_has_common_vname = has_common_vname;
    gst_has_common_hvars = has_common_hvars;
    gst_has_diff_vname = has_diff_vname; }

let mk_hypothesis prog goal : hypothesis =
  let lhs, rhs, rnm = rename_all_var_entail goal.gl_lhs goal.gl_rhs in
  { hp_ent_id = goal.gl_ent_id;
    hp_renaming = rnm;
    hp_lhs = lhs;
    hp_rhs = rhs;
    hp_lstats = mk_formula_stats prog lhs;
    hp_rstats = mk_formula_stats prog rhs; }

let mk_theorem prog name lhs rhs origin : theorem =
  let lhs, rhs = match origin with
    | LorgSynth -> lhs, rhs
    | _ ->
      let nlhs, nrhs, _ = rename_all_var_entail lhs rhs in
      nlhs, nrhs in
  let lhs, rhs = NO.simplify_all_lhs_rhs prog lhs rhs in
  let lname = create_formula_name lhs in
  let rname = create_formula_name rhs in
  { th_name = name;
    th_lhs = lhs;
    th_rhs = rhs;
    th_lhs_name = lname;
    th_rhs_name = rname;
    th_origin = origin;
    th_lstats = mk_formula_stats prog lhs;
    th_rstats = mk_formula_stats prog rhs; }

let mk_theorem_from_lemma prog lm : theorem =
  let lhs, rhs = lm.lm_lhs, lm.lm_rhs in
  let lhs, rhs = NO.simplify_all_lhs_rhs prog lhs rhs in
  mk_theorem prog lm.lm_name lhs rhs lm.lm_origin

let mk_lemma_from_theorem th : lemma =
  { lm_name = th.th_name;
    lm_lhs = th.th_lhs;
    lm_rhs = th.th_rhs;
    lm_status = LmsValid;
    lm_kind = LmkSafe;
    lm_origin = th.th_origin;
    lm_pos = no_pos }

let mk_counter_theorem prog name lhs rhs status : counter_theorem =
  let lhs, rhs, _ = rename_all_var_entail lhs rhs in
  { cth_name = name;
    cth_lhs = lhs;
    cth_rhs = rhs;
    cth_status = status;
    cth_lstats = mk_formula_stats prog lhs;
    cth_rstats = mk_formula_stats prog rhs; }

let mk_rule_star_data_core goal lsp rsp =
  let lst, rst = goal.gl_lstats, goal.gl_rstats in
  let gst, tst = goal.gl_gstats, goal.gl_tstats in
  let ldata, rdata = lsp.dsp_head, rsp.dsp_head in
  let lhrest, rhrest = fst lsp.dsp_rest, fst rsp.dsp_rest in
  let largs = ldata.dataf_root::ldata.dataf_args in
  let rargs = rdata.dataf_root::rdata.dataf_args in
  let dvars, qvars = fv_df rdata, vars_of_qvars rsp.dsp_qvars in
  let is_same_root = is_same_root_df lsp.dsp_head rsp.dsp_head in
  let trivial = if is_same_root then true else
    if goal.gl_proof_mode = PrfInferLhs &&
       not (intersected_vs lst.fst_fhvs rst.fst_fhvs) &&
       List.length goal.gl_trace < 5 &&
       gst.gst_num_rfvars <= 6 &&
       ldata.dataf_origin != HorgInput &&
       rdata.dataf_origin != HorgInput &&
       not (is_emp_hf lhrest) && not (is_emp_hf rhrest) then
      true
    else false in
  let same_data_name = eq_s ldata.dataf_name rdata.dataf_name in
  let match_args_form =
    if (eq_s ldata.dataf_name rdata.dataf_name) &&
       (List.length ldata.dataf_args = List.length rdata.dataf_args) then
      List.map2 mk_eq_exp largs rargs |>
      mk_pconj |>
      mk_qform_pf rsp.dsp_qvars
    else mk_false no_pos in
  let num_common_args =
    if (eq_s ldata.dataf_name rdata.dataf_name) then
      List.fold_left2 (fun acc x y ->
        if (eq_exp x y) then acc + 1 else acc) 0 largs rargs
    else 0 in
  let can_match_all_args =
    if (eq_s ldata.dataf_name rdata.dataf_name) then
      let largs = ldata.dataf_root::ldata.dataf_args in
      let rargs = rdata.dataf_root::rdata.dataf_args in
      List.for_all2 (fun x y ->
        if (eq_exp x y) then true
        else match y with
          | Var (v, _) -> mem_vs v (get_exists_vars rsp.dsp_qvars)
          | _ -> false) largs rargs
    else false in
  let rdata_has_fvars = (diff_vs dvars qvars) != [] in
  let rdata_has_qvars = intersected_vs dvars qvars in
  { rsd_lg_data = lsp.dsp_head;
    rsd_lg_rest = lsp.dsp_rest;
    rsd_lg_qvars = lsp.dsp_qvars;
    rsd_rg_data = rsp.dsp_head;
    rsd_rg_rest = rsp.dsp_rest;
    rsd_rg_qvars = rsp.dsp_qvars;
    rsd_match_args_form = match_args_form;
    rsd_can_match_all_args = can_match_all_args;
    rsd_has_common_arg = num_common_args > 0;
    rsd_num_common_args = num_common_args;
    rsd_same_data_name = same_data_name;
    rsd_same_root = is_same_root;
    rsd_rdata_has_fvars = rdata_has_fvars;
    rsd_rdata_has_qvars = rdata_has_qvars;
    rsd_heuristics = PhHM;
    rsd_trivial = trivial; }

let mk_rule_star_data goal lsp rsp =
  RlStarData (mk_rule_star_data_core goal lsp rsp)

let mk_rule_star_data_all goal lsp rsp =
  let rcore = mk_rule_star_data_core goal lsp rsp in
  (RlStarData rcore, rcore)

let mk_rule_star_view_core goal lsp rsp =
  let lview, rview = lsp.vsp_head, rsp.vsp_head in
  let lhrest, rhrest = fst lsp.vsp_rest, fst rsp.vsp_rest in
  let vvars, qvars = fv_vf rview, vars_of_qvars rsp.vsp_qvars in
  let rst = goal.gl_rstats in
  let match_args_form =
    if (eq_s lview.viewf_name rview.viewf_name) &&
       (List.length lview.viewf_args = List.length rview.viewf_args) then
      List.map2 mk_eq_exp lview.viewf_args rview.viewf_args |>
      mk_pconj |> mk_qform_pf rsp.vsp_qvars
    else mk_false no_pos in
  let trivial =
    if eq_vf lsp.vsp_head rsp.vsp_head &&
       rst.fst_num_hatoms > 1 then true
    else if (eq_s lview.viewf_name rview.viewf_name) &&
            (is_emp_hf lhrest) && (is_emp_hf rhrest) then true
    else if (goal.gl_proof_mode = PrfInferRhs) &&
            (fhv goal.gl_rhs = []) && (rst.fst_num_datas = 0) &&
            (not (is_emp_hf lhrest)) && (not (is_emp_hf rhrest)) then true
    else false in
  let same_view_name = eq_s lview.viewf_name rview.viewf_name in
  let num_common_args =
    if (eq_s lview.viewf_name rview.viewf_name) then
      let largs, rargs = lview.viewf_args, rview.viewf_args in
      List.fold_left2 (fun acc x y ->
        if (eq_exp x y) then acc + 1 else acc) 0 largs rargs
    else 0 in
  let can_match_all_args =
    if (eq_s lview.viewf_name rview.viewf_name) then
      let largs, rargs = lview.viewf_args, rview.viewf_args in
      List.for_all2 (fun x y ->
        if (eq_exp x y) then true
        else match y with
          | Var (v, _) -> mem_vs v (get_exists_vars rsp.vsp_qvars)
          | _ -> false) largs rargs
    else false in
  let rview_has_fvars = (diff_vs vvars qvars) != [] in
  let rview_has_qvars = intersected_vs vvars qvars in
  { rsv_lg_view = lview;
    rsv_lg_rest = lsp.vsp_rest;
    rsv_lg_qvars = lsp.vsp_qvars;
    rsv_rg_view = rview;
    rsv_rg_rest = rsp.vsp_rest;
    rsv_rg_qvars = rsp.vsp_qvars;
    rsv_match_args_form = match_args_form;
    rsv_can_match_all_args = can_match_all_args;
    rsv_rview_has_fvars = rview_has_fvars;
    rsv_rview_has_qvars = rview_has_qvars;
    rsv_has_common_arg = num_common_args > 0;
    rsv_num_common_args = num_common_args;
    rsv_same_view_name = same_view_name;
    rsv_heuristics = PhHM;
    rsv_trivial = trivial; }

let mk_rule_star_view goal lsp rsp =
  RlStarView (mk_rule_star_view_core goal lsp rsp)

let mk_rule_star_view_all goal lsp rsp =
  let rcore = mk_rule_star_view_core goal lsp rsp in
  (RlStarView rcore, rcore)

let mk_rule_view_left_core goal lview fold_case =
  let ldatas = goal.gl_lstats.fst_datas in
  let rdatas = collect_data_form fold_case.vfc_new_form in
  let lviews = goal.gl_lstats.fst_views in
  let rviews = collect_view_form fold_case.vfc_new_form in
  let new_datas = collect_data_form fold_case.vfc_view_case_form in
  let has_data_same_root = List.exists_pair (fun ld rd ->
    (is_same_type_df ld rd) && (is_same_root_df ld rd)) ldatas new_datas in
  let has_data_same_args = List.exists_pair (fun ld rd ->
    (is_same_type_df ld rd) && (is_common_args_df ld rd)) ldatas new_datas in
  { rvl_lg_view = lview;
    rvl_fold_case = fold_case;
    rvl_has_view_common_root = has_data_same_root;
    rvl_has_view_common_args = has_data_same_args;
    rvl_num_ldatas = List.length ldatas;
    rvl_num_rdatas = List.length rdatas;
    rvl_num_lviews = List.length lviews;
    rvl_num_rviews = List.length rviews;
    rvl_heuristics = PhHM;
    rvl_trivial = false; }

let mk_rule_view_left goal lview fold_case =
  RlViewLeft (mk_rule_view_left_core goal lview fold_case)

let mk_rule_view_right_core goal rview unfold_case =
  let ldatas = goal.gl_lstats.fst_datas in
  let rdatas = collect_data_form unfold_case.vuc_new_form in
  let lviews = goal.gl_lstats.fst_views in
  let rviews = collect_view_form unfold_case.vuc_new_form in
  let new_datas = collect_data_form unfold_case.vuc_view_case_form in
  let has_data_same_root = List.exists_pair (fun ld rd ->
    (is_same_type_df ld rd) && (is_same_root_df ld rd)) ldatas new_datas in
  let has_data_same_args = List.exists_pair (fun ld rd ->
    (is_same_type_df ld rd) && (is_common_args_df ld rd)) ldatas new_datas in
  { rvr_rg_view = rview;
    rvr_unfold_case = unfold_case;
    rvr_has_data_same_root = has_data_same_root;
    rvr_has_data_same_args = has_data_same_args;
    rvr_num_ldatas = List.length ldatas;
    rvr_num_rdatas = List.length rdatas;
    rvr_num_lviews = List.length lviews;
    rvr_num_rviews = List.length rviews;
    rvr_heuristics = PhHM;
    rvr_trivial = false; }

let mk_rule_view_right goal rview unfold_case =
  RlViewRight (mk_rule_view_right_core goal rview unfold_case)

let mk_rule_view_right_all goal rview unfold_case =
  let rcore = mk_rule_view_right_core goal rview unfold_case in
  (RlViewRight rcore, rcore)

let mk_rule_induction_core prog goal vsp unfold_cases record_hypo =
  let lst, rst = goal.gl_lstats, goal.gl_rstats in
  let rdatas = rst.fst_datas in
  let vdefns, lview = prog.prog_views, vsp.vsp_head in
  let icases = List.fold_left (fun acc u ->
    if u.vuc_base_case then acc
    else acc @ [u.vuc_view_case_form]) [] unfold_cases in
  let ndatass = icases |> List.map collect_data_form in
  let has_data_same_root = ndatass |> List.for_all (fun dfs ->
    List.exists_pair (fun df1 df2 ->
      eq_exp df1.dataf_root df2.dataf_root) dfs rdatas) in
  let has_data_common_arg_indt_case = ndatass |> List.for_all (fun dfs ->
    List.exists_pair is_common_args_df dfs rdatas) in
  let rg_has_indirect_recur_view = goal.gl_rstats.fst_views |>
                                   List.exists (is_recur_indirect_vf vdefns ) in
  let lvroots = get_view_root vdefns lview in
  let has_view_common_root = rst.fst_views |> List.exists (fun vf ->
    (eq_s lview.viewf_name vf.viewf_name) &&
    List.exists2 (fun arg1 arg2 ->
      (eq_exp arg1 arg2) && (List.exists (eq_exp arg1) lvroots)
    ) lview.viewf_args vf.viewf_args) in
  let has_view_common_arg = rst.fst_views |> List.exists (fun vf ->
    (eq_s lview.viewf_name vf.viewf_name) &&
    List.exists2 eq_exp lview.viewf_args vf.viewf_args) in
  let trivial =
    if (vsp.vsp_view_recur = VrtNone) then true
    else if List.exists is_int_exp vsp.vsp_head.viewf_args then false
    else unfold_cases |> List.for_all (fun ufc ->
      let ndatas = collect_data_form ufc.vuc_view_case_form in
      (is_pure_f ufc.vuc_view_case_form) ||
      List.exists_pair (fun ld rd ->
        (is_same_type_df ld rd) && (is_same_root_df ld rd)) ndatas rdatas) in
  let indt_vvars = fv_vf vsp.vsp_head in
  let has_gen_emid_vars = goal.gl_trace |> List.exists (fun tri ->
    match tri.tri_rule with
    | RlExclMid rem -> intersected_vs (fv_pf rem.rem_seed_cond) indt_vvars
    | _ -> false) in
  { rid_ent_id = goal.gl_ent_id;
    rid_lg_view = vsp.vsp_head;
    rid_lg_view_pos = get_heap_pos lst (HView vsp.vsp_head);
    rid_unfold_cases = unfold_cases;
    rid_record_hypo = record_hypo;
    rid_has_view_common_root = has_view_common_root;
    rid_has_view_common_arg = has_view_common_arg;
    rid_has_data_same_root = has_data_same_root;
    rid_has_data_common_arg_indt_case = has_data_common_arg_indt_case;
    rid_has_related_emid_cond = has_gen_emid_vars;
    rid_rg_has_indirect_recur_view = rg_has_indirect_recur_view;
    rid_lg_view_vars = fv_vf vsp.vsp_head;
    rid_heuristics = PhHM;
    rid_trivial = trivial; }

let mk_rule_induction prog goal vsp unfold_cases record_hypo =
  RlInduction (mk_rule_induction_core prog goal vsp unfold_cases record_hypo)

let mk_rule_hypothesis_core ?(assums=[]) hypo unf =
  { rhp_hp = hypo;
    rhp_unf_ssts = unf.unf_correct_ssts;
    rhp_unf_residue = mk_hstar_hatoms unf.unf_residue;
    rhp_assums = assums;
    rhp_heurs = PhHM; }

let mk_rule_hypothesis ?(assums=[]) hypo unf =
  RlHypothesis (mk_rule_hypothesis_core ~assums:assums hypo unf)

let mk_rule_theorem_core theorem unf left =
  { rth_th = theorem;
    rth_left = left;
    rth_unf_ssts = unf.unf_correct_ssts;
    rth_unf_ssts_len = List.length unf.unf_correct_ssts;
    rth_unf_residue = mk_hstar_hatoms unf.unf_residue;
    rth_heuristics = PhHM; }

let mk_rule_theorem theorem unf left =
  RlTheorem (mk_rule_theorem_core theorem unf left)

let mk_rule_equal_left_core lhs =
  { reql_lg = lhs; }

let mk_rule_equal_left lhs =
  RlEqualLeft (mk_rule_equal_left_core lhs)

let mk_rule_exists_left_core lhs =
  { rexl_lg = lhs; }

let mk_rule_exists_left lhs =
  RlExistsLeft (mk_rule_exists_left_core lhs)

let mk_rule_exists_right_core rhs =
  { rexr_rg = rhs; }

let mk_rule_exists_right rhs =
  RlExistsRight (mk_rule_exists_right_core rhs)

let mk_rule_emp_left_core lhs =
  { reml_lg = lhs; }

let mk_rule_emp_left lhs =
  RlEmpLeft (mk_rule_emp_left_core lhs)

let mk_rule_emp_right_core rhs =
  { remr_rg = rhs; }

let mk_rule_emp_right rhs =
  RlEmpRight (mk_rule_emp_right_core rhs)

let mk_rule_drop_left_core lhs pf =
  { rdl_lg = lhs;
    rdl_lg_drop = pf; }

let mk_rule_drop_left lhs pf =
  RlDropLeft (mk_rule_drop_left_core lhs pf)

let mk_rule_drop_right_core rhs pf =
  { rdr_rg = rhs;
    rdr_rg_drop = pf; }

let mk_rule_drop_right rhs pf =
  RlDropRight (mk_rule_drop_right_core rhs pf)

let mk_rule_unfold_relation_core lrels rrels =
  { rur_lg_rels = lrels;
    rur_rg_rels = rrels; }

let mk_rule_unfold_relation lrels rrels =
  RlUnfoldRel (mk_rule_unfold_relation_core lrels rrels)

let mk_rule_gen_left_core ?(base=None) nlhs exps prog goal =
  let gen_vs = fv_exps exps in
  let has_gen_emid_vars = goal.gl_trace |> List.exists (fun tri ->
    match tri.tri_rule with
    | RlExclMid rem -> intersected_vs (fv_pf rem.rem_seed_cond) gen_vs
    | _ -> false) in
  let has_gen_unfolded_exps =
    goal.gl_trace |> List.map (fun tri ->
      match tri.tri_rule with
      | RlInduction rid ->
        if rid.rid_lg_view.viewf_ancestor_ids = [] then []
        else rid.rid_lg_view.viewf_args
      | _ -> []) |> List.concat |> List.exists_pair eq_exp exps in
  { rgl_new_lg = nlhs;
    rgl_gen_exps = exps;
    rgl_base_hypo_unf = base;
    rgl_has_gen_emid_vars = has_gen_emid_vars;
    rgl_has_gen_unfolded_exps = has_gen_unfolded_exps; }

let mk_rule_gen_left ?(base=None) nlhs exps prog goal =
  RlGenLeft (mk_rule_gen_left_core ~base:base nlhs exps prog goal)

let mk_rule_weaken_left_core ?(base=None) nlhs wpf goal =
  let dropped_vs = fv_pf wpf in
  let has_gen_emid_vars = goal.gl_trace |> List.exists (fun tri ->
    match tri.tri_rule with
    | RlExclMid rem -> intersected_vs (fv_pf rem.rem_seed_cond) dropped_vs
    | _ -> false) in
  { rwl_new_lg = nlhs;
    rwl_dropped_pf = wpf;
    rwl_base_hypo_unf = base;
    rwl_has_gen_emid_vars = has_gen_emid_vars; }

let mk_rule_weaken_left ?(base=None) nlhs wpf goal =
  RlWeakenLeft (mk_rule_weaken_left_core ~base:base nlhs wpf goal)

let mk_rule_pure_entail_core lhs rhs status =
  { rpe_lg = lhs;
    rpe_rg = rhs;
    rpe_status = status; }

let mk_rule_pure_entail lhs rhs status =
  RlPureEntail (mk_rule_pure_entail_core lhs rhs status)

let mk_rule_false_left_core lhs =
  { rfl_lg = lhs; }

let mk_rule_false_left lhs =
  RlFalseLeft (mk_rule_false_left_core lhs)

let mk_rule_excl_mid_core ?(plan_rules=[]) cond  =
  let emcs = match plan_rules with
    | [RlHypothesis _] | [RlTheorem _]->
      let emc1 = { emc_pure_cond = cond;
                   emc_rule_planned = plan_rules;
                   emc_type = EmctPlanned; } in
      let emc2 = { emc_pure_cond = mk_pneg cond;
                   emc_rule_planned = [];
                   emc_type = EmctUnplanned; } in
      [emc1; emc2]
    | _ ->
      let emc1 = { emc_pure_cond = cond;
                   emc_rule_planned = plan_rules;
                   emc_type = EmctPlanned; } in
      let emc2 = { emc_pure_cond = mk_pneg cond;
                   emc_rule_planned = plan_rules;
                   emc_type = EmctPlanned; } in
      [emc1; emc2] in
  let rhps, rths, rvrs = ref [], ref [], ref [] in
  let _ = List.iter (fun r -> match r with
    | RlHypothesis rhp -> rhps := !rhps @ [rhp]
    | RlViewRight rvr -> rvrs := !rvrs @ [rvr]
    | RlTheorem rth -> rths := !rths @ [rth]
    | _ -> ()) plan_rules in
  let ems = { ems_hypothesis = !rhps;
              ems_theorem = !rths;
              ems_view_right = !rvrs; } in
  { rem_seed_cond = cond;
    rem_seed_rule = ems;
    rem_cases = emcs;
    rem_heuristics = PhHM; }

let mk_rule_excl_mid ?(plan_rules=[]) cond =
  RlExclMid (mk_rule_excl_mid_core cond ~plan_rules:plan_rules)

let mk_rule_infer_relation_core lhs rhs consumed assumption =
  { rir_lg = lhs;
    rir_rg = rhs;
    rir_hconsumed = consumed;
    rir_assumption = assumption; }

let mk_rule_infer_relation lhs rhs consumed assumption =
  RlInferRel (mk_rule_infer_relation_core lhs rhs consumed assumption)

let mk_rule_infer_relation_false_core lhs consumed assumption =
  { rir_lg = lhs;
    rir_rg = mk_ffalse no_pos;
    rir_hconsumed = consumed;
    rir_assumption = assumption; }

let mk_rule_infer_relation_false lhs consumed assumption =
  RlInferRel (mk_rule_infer_relation_false_core lhs consumed assumption)

let mk_rule_infer_entail_core goal rdefns ent =
  { rie_goal = goal;
    rie_rdefns = rdefns;
    rie_entail = ent; }

let mk_rule_infer_entail goal rdefns ent =
  RlInferEnt (mk_rule_infer_entail_core goal rdefns ent)

(* A trivial rule is a complete rule *)
let is_rule_trivial rule =
  if not !proof_use_trivial then false else
    match rule with
    | RlPureEntail _ -> true
    | RlDropLeft _ | RlDropRight _ -> true
    | RlEmpLeft _ | RlEmpRight _ -> true
    | RlEqualLeft _ | RlExistsLeft _ | RlExistsRight _ -> true
    | RlUnfoldRel _ -> true
    | RlStarView rsv -> rsv.rsv_trivial
    | RlStarData rsd -> rsd.rsd_trivial
    | RlViewRight rvr -> rvr.rvr_trivial
    | _ -> false

let is_rule_bidirection rule =
  match rule with
  | RlPureEntail _ | RlFalseLeft _
  | RlEmpLeft _ | RlEmpRight _
  | RlExistsLeft _ | RlEqualLeft _
  | RlInduction _ | RlExclMid _ -> true
  | RlUnfoldRel _ -> true
  | _ -> false

let is_unplanned_excl_mid_case emc =
  emc.emc_type = EmctUnplanned

(* a trivial rule is a complete rule *)
let is_rule_handle_heap_atom = function
  | RlStarData _ | RlStarView _ | RlViewRight _
  | RlInduction _ | RlHypothesis _ | RlTheorem _ -> true
  | _ -> false

let is_excl_mid_seed_rule_hypo rem =
  rem.rem_seed_rule.ems_hypothesis != []

let is_excl_mid_seed_rule_view_right rem =
  rem.rem_seed_rule.ems_view_right != []

let mk_goal ?(mode=PrfEntail) prog lhs rhs =
  let lst, rst = Pair.fold (mk_formula_stats prog) lhs rhs in
  let gst = mk_goal_stats prog lst rst in
  let unproved_rhs_patoms = find_unproved_conjuncts prog lhs rhs in
  let goal = {
    gl_ent_id = new_entail_id ();
    gl_lhs = lhs;
    gl_rhs = rhs;
    gl_hconsumed = [];
    gl_hreplaced = [];
    gl_lstats = lst;
    gl_rstats = rst;
    gl_gstats = gst;
    gl_lhs_derived_groups = [];
    gl_rhs_derived_groups = [];
    gl_lhs_encoded = NO.encode_formula prog lhs;
    gl_rhs_unproved_patoms = unproved_rhs_patoms;
    gl_cache_rule = None;
    gl_precise_unifying_plans = [];
    gl_matching_plans = [];
    gl_hooked_rules = [];
    gl_proof_mode = mode;
    gl_need_infer_lemma = false;
    gl_need_check_unsat_lhs = false;
    gl_depth_infer = 0;
    gl_has_unplanned_excl_mid = false;
    gl_trace = [];
    gl_tstats = mk_trace_stats prog [];
    gl_hypos = [];
    gl_assums = [];
    gl_unproductive_reason = None; } in
  goal

let mk_unsat_goal prog f =
  mk_goal ~mode:PrfUnsat prog f (mk_ffalse no_pos)

let mk_goal_of_entail ?(mode=PrfEntail) prog ent =
  mk_goal ~mode:mode prog ent.ent_lhs ent.ent_rhs

let mk_entail_of_goal goal =
  mk_entailment ~mode:goal.gl_proof_mode goal.gl_lhs goal.gl_rhs

let mk_infer_rdefn solver rdefns =
  {ird_rdefns = rdefns; ird_solver = solver}

let mk_verify_ifent ifents continue msg =
  { vif_ifents = ifents;
    vif_continue = continue;
    vif_msg = msg; }

let neg_prio prio = match prio with
  | PrioHigh -> PrioLow
  | PrioEqual -> PrioEqual
  | PrioLow -> PrioHigh

(** handling derived groups by looking at hatoms' ID *)
let remove_derived_groups dr_groups removed_hatom =
  List.filter (fun drg ->
    List.for_all (fun x -> not (eq_hatom x removed_hatom)) drg.drg_hatoms
  ) dr_groups

(** handling derived groups by looking at hatoms' ID *)
let update_derived_groups dr_groups deriving_hatoms new_hatoms =
  if new_hatoms = [] then dr_groups
  else
    let main_groups, other_groups = List.fold_left (fun acc x ->
      let nmgrs, nogrs = acc in
      let mgs, ogs = List.partition (fun drg ->
        List.exists (fun y -> eq_hatom x y) drg.drg_hatoms) nogrs in
      (nmgrs@mgs, ogs)
    ) ([], dr_groups) deriving_hatoms in
    let new_main_groups = match main_groups with
      | [] -> [{drg_level = 1; drg_hatoms = new_hatoms}]
      | _ ->
        List.map (fun drg ->
          {drg_level = drg.drg_level + 1;
           drg_hatoms = drg.drg_hatoms@new_hatoms}) main_groups in
    new_main_groups@other_groups

(** handling derived groups by looking at hatoms' ID *)
let has_derived_group_contain_hatom pstate dr_groups hatom : bool =
  let pth = pstate.prs_threshold in
  List.exists (fun drg ->
    if (drg.drg_level <= pth.pth_goal_max_depth_unfold_group) then false
    else List.exists (fun x -> eq_hatom x hatom) drg.drg_hatoms
  ) dr_groups

let mk_derivation_goals ?(heur=PhHM) rule goal subgoals =
  { drv_kind = DrvSubgoals subgoals;
    drv_heur = heur;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_infer ?(heur=PhHM) rule goal =
  { drv_kind = DrvStatus MvlInfer;
    drv_heur = heur;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_valid ?(heur=PhHM) rule goal =
  { drv_kind = DrvStatus MvlTrue;
    drv_heur = heur;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_invalid ?(heur=PhHM) rule goal =
  { drv_kind = DrvStatus MvlFalse;
    drv_heur = heur;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_unknown ?(heur=PhHM) rule goal =
  { drv_kind = DrvStatus MvlUnkn;
    drv_heur = heur;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_backjump ?(heur=PhHM) entail_id rule goal subgoals =
  { drv_kind = DrvBackjump (subgoals, entail_id);
    drv_heur = heur;
    drv_rule = rule;
    drv_goal = goal; }

let mk_assume_pent istate prog asm : pure_entail =
  let lhs, rhs = asm.asm_lhs, asm.asm_rhs in
  let lhs, rhs = NO.simplify_all_lhs_rhs ~infer:true prog lhs rhs in
  let hconsumed, constr = asm.asm_hconsumed, istate.ist_constr in
  let plhs1, plhs2 = lhs |> extract_pf |> NO.currify_prel_null_ptr in
  let prhs1, prhs2 = rhs |> NO.encode_infer_rhs ~constr:constr prog |>
                     NO.currify_prel_null_ptr in
  let plhs = mk_pconj [plhs1; plhs2; prhs2] in
  let prhs = prhs1 in
  mk_pure_entail plhs prhs

let mk_prover_threshold prog goal =
  let lst, rst, vdefns = goal.gl_lstats, goal.gl_rstats, prog.prog_views in
  let lsize, rsize = lst.fst_num_hatoms, rst.fst_num_hatoms in
  let lviews, rviews = lst.fst_views, rst.fst_views in
  let num_lviews, num_rviews = lst.fst_num_views, rst.fst_num_views in
  let views, gsize = lviews @ rviews, lsize + rsize in
  let _ = match List.exists (is_recur_mutual_vf vdefns) views with
    | true -> thd_max_level_unfolding_group := 2
    | false -> thd_max_level_unfolding_group := 1 in
  let prover_threshold = {
    pth_tree_max_width = !thd_max_proof_tree_width;
    pth_goal_max_depth_unfold_group = 2;
    pth_goal_unfold_right_intensive = gsize > 10;
    pth_lemma_max_num_infer_per_goal = 0;
    pth_lemma_max_infer_assumpts = !thd_max_infer_assumpts;
    pth_trace_max_length = max (gsize * 3 + 1) !thd_max_trace_length;
    pth_trace_max_length_uninst_var = 3;
    pth_trace_max_length_gen_left = !thd_max_trace_length_gen_left;
    pth_trace_max_length_check_unsat = 1;
    pth_trace_min_length_mining = max (gsize * 2) !thd_min_trace_length_mining;
    pth_trace_min_length_inconsist = !thd_min_trace_length_mining;
    pth_trace_max_induction = max (num_lviews * 3 + 1) !thd_max_induction;
    pth_trace_max_view_right = max (gsize * 3 + 1) !thd_max_view_right;
    pth_trace_max_hypothesis = !thd_max_hypothesis; } in
  match goal.gl_proof_mode with
  | PrfInferBasic | PrfInferLhs | PrfInferRhs | PrfInferAll ->
    { prover_threshold with
      pth_goal_max_depth_unfold_group = 3;
      pth_goal_unfold_right_intensive = gsize > 10;
      pth_lemma_max_num_infer_per_goal = !thd_max_num_inferred_ents;
      pth_lemma_max_infer_assumpts = !thd_max_infer_assumpts;
      pth_trace_max_length = max (gsize * 5 + 1) !thd_max_trace_length;
      pth_trace_max_length_uninst_var = 1;
      pth_trace_max_length_check_unsat = 2;
      pth_trace_min_length_mining = max (gsize * 3) !thd_min_trace_length_mining;
      pth_trace_min_length_inconsist = !thd_min_trace_length_mining;
      pth_trace_max_induction = max (gsize * 2 + 1) !thd_max_induction;
      pth_trace_max_view_right = max (gsize * 3 + 1) !thd_max_view_right;
      pth_trace_max_hypothesis = !thd_max_hypothesis; }
  | _ -> prover_threshold

let mk_prover_state ?(interact=false) prog goal : prover_state =
  DB.dhprint "PROOF MODE: " pr_proof_mode goal.gl_proof_mode;
  let theorems = List.map (mk_theorem_from_lemma prog) prog.prog_lemmas in
  let timeout = match goal.gl_proof_mode with
    | PrfInferBasic -> !timeout_check_unknown_basic
    | PrfInferLhs | PrfInferRhs
    | PrfInferAll -> !timeout_check_unknown_entail
    | PrfVerifyLemma -> !timeout_verify_valid_ptree
    | PrfVerifyIndtLemma -> !timeout_verify_indt_ptree
    | _ -> !timeout_check_entail in
  let pstate = {
    prs_prog = prog;
    prs_threshold = mk_prover_threshold prog goal;
    prs_start_time = get_time ();
    prs_timeout = float_of_int timeout;
    prs_theorems = theorems;
    prs_infer_lemma_attempted = [];
    prs_counter_theorems = [];
    prs_interact = interact;
    prs_assums = [];
    prs_stats = PE.mk_stats_entail (); } in
  pstate

let mk_infer_state ?(partial=true) ?(interact=false)
      mode constr prog lvars rvars =
  { ist_prog = prog;
    ist_mode = mode;
    ist_constr = constr;
    ist_partial = partial;
    ist_start_time = get_time ();
    ist_interact = interact;
    ist_inferred_ents = [];
    ist_failed_ents = [];
    ist_lhs_vars = lvars;
    ist_rhs_vars = rvars; }

let mk_infer_entail ptree rdefns goal entail =
  { ife_ptree = ptree;
    ife_good_lemma_ptree = false;
    ife_rdefns = rdefns;
    ife_goal_origin = goal;
    ife_entail_inferred = entail; }

let is_proof_tree_bidirection ptree =
  match ptree with
  | PtDerive ptd -> ptd.ptd_bidirection
  | PtSearch pts -> pts.pts_bidirection

let mk_proof_tree_search ?(heur=PhHM) goal sub_trees status : proof_tree =
  PtSearch {
    pts_goal = goal;
    pts_sub_trees = sub_trees;
    pts_bidirection = List.exists is_proof_tree_bidirection sub_trees;
    pts_heur = heur;
    pts_status = status; }

let mk_proof_tree_derive ?(heur=PhHM) goal rule sub_trees status : proof_tree =
  PtDerive {
    ptd_goal = goal;
    ptd_rule = rule;
    ptd_bidirection = is_rule_bidirection rule;
    ptd_sub_trees = sub_trees;
    ptd_heur = heur;
    ptd_status = status; }

let mk_proof_tree_core_stats () =
  { pst_mr_star_data = 0;
    pst_mr_star_view = 0;
    pst_mr_view_right = 0;
    pst_mr_induction = 0;
    pst_mr_hypothesis = 0;
    pst_mr_theorem = 0;
    pst_mr_excl_mid = 0;
    pst_width = 0;
    pst_height = 0;
    pst_size = 0 }

let get_meta_rule rule : meta_rule =
  match rule with
  | RlStarData _ -> MrStarData
  | RlStarView _ -> MrStarView
  | RlViewRight _ -> MrViewRight
  | RlInduction _ -> MrInduction
  | RlHypothesis _ -> MrHypothesis
  | RlTheorem _ -> MrTheorem
  | RlExclMid _ -> MrExclMid
  | RlPureEntail _ | RlFalseLeft _ -> MrAxiom
  | RlEmpLeft _ | RlEmpRight _ -> MrNormalize
  | RlEqualLeft _ | RlExistsLeft _ | RlExistsRight _ -> MrNormalize
  | RlDropLeft _ | RlDropRight _ | RlUnfoldRel _ -> MrNormalize
  | _ -> MrUnknown

let mk_proof_tree_core ?(assums=[]) ?(mutualhp=[]) goal rule sub_ptrees =
  let stats =
    let default_stats = mk_proof_tree_core_stats () in
    let pst = sub_ptrees |> List.fold_left (fun acc ptc ->
      let st = ptc.ptc_stats in
      { pst_mr_star_data = acc.pst_mr_star_data + st.pst_mr_star_data;
        pst_mr_star_view = acc.pst_mr_star_view + st.pst_mr_star_view;
        pst_mr_view_right = acc.pst_mr_view_right + st.pst_mr_view_right;
        pst_mr_induction = acc.pst_mr_induction + st.pst_mr_induction;
        pst_mr_hypothesis = acc.pst_mr_hypothesis + st.pst_mr_hypothesis;
        pst_mr_theorem = acc.pst_mr_theorem + st.pst_mr_theorem;
        pst_mr_excl_mid = acc.pst_mr_excl_mid + st.pst_mr_excl_mid;
        pst_width = max acc.pst_width st.pst_width;
        pst_height = max acc.pst_height st.pst_height;
        pst_size = acc.pst_size + st.pst_size }) default_stats in
    let pst = match  get_meta_rule rule with
      | MrStarData -> {pst with pst_mr_star_data = pst.pst_mr_star_data + 1}
      | MrStarView -> {pst with pst_mr_star_view = pst.pst_mr_star_view + 1}
      | MrViewRight -> {pst with pst_mr_view_right = pst.pst_mr_view_right + 1}
      | MrInduction -> {pst with pst_mr_induction = pst.pst_mr_induction + 1}
      | MrHypothesis -> {pst with pst_mr_hypothesis = pst.pst_mr_hypothesis + 1}
      | MrTheorem -> {pst with pst_mr_theorem = pst.pst_mr_theorem + 1}
      | MrExclMid -> {pst with pst_mr_excl_mid = pst.pst_mr_excl_mid + 1}
      | _ -> pst in
    { pst with
      pst_size = pst.pst_size + 1;
      pst_height = pst.pst_height + 1;
      pst_width = max pst.pst_width (List.length sub_ptrees) } in
  { ptc_goal = goal;
    ptc_rule = rule;
    ptc_stats = stats;
    ptc_assums = assums;
    ptc_mutual_hypos = mutualhp;
    ptc_sub_trees = sub_ptrees;
    ptc_backjump = None; }

let mk_ptree_search_unkn ?(heur=PhHM) goal subtrees msg =
  mk_proof_tree_search ~heur:heur goal subtrees (PtUnkn msg)

let mk_ptree_search_invalid ?(heur=PhHM) goal subtrees =
  mk_proof_tree_search ~heur:heur goal subtrees PtInvalid

let mk_backjump ent_id rule =
  { bkj_ent_id = ent_id;
    bkj_rule = rule; }

(*****************************************************************)
(*******************         Utilities         *******************)

let get_ptree_status (ptree: proof_tree) : proof_tree_status =
  match ptree with
  | PtSearch p -> p.pts_status
  | PtDerive p -> p.ptd_status

let get_ptree_goal (ptree: proof_tree) : goal=
  match ptree with
  | PtSearch p -> p.pts_goal
  | PtDerive p -> p.ptd_goal

let get_ptree_validity ptree : mvlogic =
  let pts = get_ptree_status ptree in
  match pts with
  | PtValid _ -> MvlTrue
  | PtInvalid -> MvlFalse
  | PtUnkn _ -> MvlUnkn
  | PtInfer _ -> MvlInfer

let update_ptree_backjump (ptree: proof_tree) bkj : proof_tree =
  let ptstatus = get_ptree_status ptree in
  let ptstatus = match ptstatus with
    | PtValid ptc -> PtValid {ptc with ptc_backjump = Some bkj}
    | PtInfer ptc -> PtInfer {ptc with ptc_backjump = Some bkj}
    | _ -> ptstatus in
  match ptree with
  | PtSearch p -> PtSearch {p with pts_status = ptstatus}
  | PtDerive p -> PtDerive {p with ptd_status = ptstatus}


let update_rule_heur heur rule =
  match rule with
  | RlStarData rsd -> RlStarData {rsd with rsd_heuristics = heur}
  | RlStarView rsv -> RlStarView {rsv with rsv_heuristics = heur}
  | RlViewLeft rvl -> RlViewLeft {rvl with rvl_heuristics = heur}
  | RlViewRight rvr -> RlViewRight {rvr with rvr_heuristics = heur}
  | RlInduction rid -> RlInduction {rid with rid_heuristics = heur}
  | RlHypothesis rhp -> RlHypothesis {rhp with rhp_heurs = heur}
  | RlTheorem rth -> RlTheorem {rth with rth_heuristics = heur}
  | RlExclMid rem -> RlExclMid {rem with rem_heuristics = heur}
  | RlPureEntail _ -> rule
  | RlEqualLeft _ -> rule
  | RlExistsLeft _ -> rule
  | RlExistsRight _ -> rule
  | RlEmpLeft _ -> rule
  | RlEmpRight _ -> rule
  | RlDropLeft _ -> rule
  | RlDropRight _ -> rule
  | RlGenLeft _ -> rule
  | RlWeakenLeft _ -> rule
  | RlUnfoldRel _ -> rule
  | RlFalseLeft _ -> rule
  | RlInferRel _ -> rule
  | RlInferEnt _ -> rule

let get_rule_heur rule = match rule with
  | RlStarData rsd -> rsd.rsd_heuristics
  | RlStarView rsv -> rsv.rsv_heuristics
  | RlViewLeft rvl -> rvl.rvl_heuristics
  | RlViewRight rvr -> rvr.rvr_heuristics
  | RlInduction rid -> rid.rid_heuristics
  | RlHypothesis rhp -> rhp.rhp_heurs
  | RlTheorem rth -> rth.rth_heuristics
  | RlExclMid rem -> rem.rem_heuristics
  | RlPureEntail _ -> PhHM
  | RlEqualLeft _ -> PhHM
  | RlExistsLeft _ -> PhHM
  | RlExistsRight _ -> PhHM
  | RlEmpLeft _ -> PhHM
  | RlEmpRight _ -> PhHM
  | RlDropLeft _ -> PhHM
  | RlDropRight _ -> PhHM
  | RlGenLeft _ -> PhHM
  | RlWeakenLeft _ -> PhHM
  | RlUnfoldRel _ -> PhHM
  | RlFalseLeft _ -> PhHM
  | RlInferRel _ -> PhHM
  | RlInferEnt _ -> PhHM

let get_rules_heur rules =
  let heurs = List.map get_rule_heur rules in
  if List.exists ((=) PhML) heurs then PhML
  else PhHM

let get_ptree_heur (ptree: proof_tree) : proof_heuristic =
  match ptree with
  | PtSearch p -> p.pts_heur
  | PtDerive p -> p.ptd_heur

let combine_heurs heurs =
  if List.exists ((=) PhML) heurs then PhML
  else PhHM

let is_valid_status status =
  match status with
  | PtValid _ -> true
  | _ -> false

let is_invalid_status status =
  match status with
  | PtInvalid -> true
  | _ -> false

let is_valid_ptree ptree : bool =
  ptree |> get_ptree_status |> is_valid_status

let is_invalid_ptree ptree : bool =
  ptree |> get_ptree_status |> is_invalid_status

let get_rule_heap_pos goal rule : (heap_pos * heap_pos) =
  let lst, rst = goal.gl_lstats, goal.gl_rstats in
  match rule with
  | RlStarData rsd ->
    let lha, rha = HData rsd.rsd_lg_data, HData rsd.rsd_rg_data in
    (get_heap_pos lst lha, get_heap_pos rst rha)
  | RlStarView rsv ->
    let lha, rha = HView rsv.rsv_lg_view, HView rsv.rsv_rg_view in
    (get_heap_pos lst lha, get_heap_pos rst rha)
  | RlInduction rid ->
    (get_heap_pos lst (HView rid.rid_lg_view), HpUnkn)
  | RlViewRight rvr ->
    (HpUnkn, get_heap_pos lst (HView rvr.rvr_rg_view))
  | _ -> (HpUnkn, HpUnkn)

(*********************************************************************)
(******************        RULES UTILITIES        ********************)

let is_rule_star_data = function
  | RlStarData _ -> true
  | _ -> false

let is_rule_star_view = function
  | RlStarView _ -> true
  | _ -> false

let is_rule_induction = function
  | RlInduction _ -> true
  | _ -> false

let is_rule_induction_inductive_case = function
  | RlInduction rid ->
    rid.rid_unfold_cases |> List.for_all (fun ufc -> not ufc.vuc_base_case)
  | _ -> false

let is_rule_view_right = function
  | RlViewRight _ -> true
  | _ -> false

let is_rule_view_right_inductive_case = function
  | RlViewRight rvr -> not rvr.rvr_unfold_case.vuc_base_case
  | _ -> false

let is_rule_hypothesis = function
  | RlHypothesis _ -> true
  | _ -> false

let is_rule_theorem = function
  | RlTheorem _ -> true
  | _ -> false

let is_rule_theorem_left = function
  | RlTheorem rth -> rth.rth_left
  | _ -> false

let is_rule_theorem_right = function
  | RlTheorem rth -> not rth.rth_left
  | _ -> false

let is_rule_weaken_left = function
  | RlWeakenLeft _ -> true
  | _ -> false

let is_rule_gen_left = function
  | RlGenLeft _ -> true
  | _ -> false

let is_rule_excl_mid = function
  | RlExclMid _ -> true
  | _ -> false

let is_rule_spatial = function
  | RlStarData _
  | RlStarView _
  | RlViewRight _
  | RlInduction _
  | RlHypothesis _
  | RlTheorem _
  | RlExclMid _
  | RlGenLeft _ -> true
  | _ -> false

let is_rule_normalization = function
  | RlExistsLeft _ | RlExistsRight _
  | RlEqualLeft _ | RlDropRight _
  | RlEmpLeft _ | RlEmpRight _
  | RlUnfoldRel _ -> true
  | _ -> false

let is_rule_axiom = function
  | RlPureEntail _
  | RlFalseLeft _ -> true
  | _ -> false

let get_latest_rule goal =
  let rules = List.map (fun t -> t.tri_rule) goal.gl_trace in
  match rules with
  | [] -> None
  | x::_ -> Some x

let get_latest_spatial_rules goal num =
  let rules =
    goal.gl_trace |> List.map (fun t -> t.tri_rule) |>
    List.filter is_rule_spatial in
  if (List.length rules <= num) then rules
  else rules |> List.split_nth num |> fst

let is_latest_rule_theorem_same_theorem goal th =
  let rec check rules =
    match rules with
    | (RlTheorem rth)::_ -> (eq_s rth.rth_th.th_name th.th_name)
    | _ -> false in
  let rules = List.map (fun t -> t.tri_rule) goal.gl_trace in
  check rules

let is_recent_rule_induction_without_hypothesis goal =
  let rec check rules =
    match rules with
    | [] -> false
    | (RlHypothesis _)::_ -> false
    | (RlInduction _)::_ -> true
    | r::rs ->  check rs in
  let rules = List.map (fun t -> t.tri_rule) goal.gl_trace in
  check rules

let is_recent_rule_induction_without_view_right goal =
  let rec check rules =
    match rules with
    | (RlInduction _)::_ -> true
    | (RlEqualLeft _)::rs -> check rs
    | (RlExistsLeft _)::rs -> check rs
    | _ -> false in
  let rules = List.map (fun t -> t.tri_rule) goal.gl_trace in
  check rules

let is_latest_rule_spatial goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlViewRight _)::_ -> true
  | _ -> false

let is_latest_spatial_rule_star_data goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlStarData _)::_ -> true
  | _ -> false

let is_latest_spatial_rule_star_view goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlStarView _)::_ -> true
  | _ -> false

let is_latest_spatial_rule_view_right goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlViewRight _)::_ -> true
  | _ -> false

let is_latest_spatial_rule_induction goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlInduction _)::_ -> true
  | _ -> false

let is_latest_spatial_rule_induction_record_hypo goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlInduction rid)::_ -> rid.rid_record_hypo
  | _ -> false

let is_latest_spatial_rule_hypothesis goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlHypothesis _)::_ -> true
  | _ -> false

let is_latest_spatial_rule_theorem goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlTheorem _)::_ -> true
  | _ -> false

let is_latest_spatial_rule_gen_left goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  |(RlGenLeft _)::_ -> true
  | _ -> false

let is_latest_spatial_rule_excl_middle goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlExclMid _)::_ -> true
  | _ -> false

let is_latest_spatial_rule_trivial goal =
  match get_latest_spatial_rules goal 1 with
  | [] -> false
  | (RlStarData rsd)::_ -> rsd.rsd_trivial
  | (RlStarView rsv)::_ -> rsv.rsv_trivial
  | (RlViewRight rvr)::_ -> rvr.rvr_trivial
  | (RlInduction rid)::_ -> rid.rid_trivial
  | _ -> false

let collect_used_spatial_rules goal =
  goal.gl_trace |>
  List.map (fun t -> t.tri_rule) |>
  List.filter is_rule_spatial

let is_theorem_applied_earlier ?(left=true) goal th =
  goal |> collect_used_spatial_rules |>
  List.exists (function
    | RlTheorem rth ->
      (rth.rth_left = left) &&
      (eq_s rth.rth_th.th_name th.th_name)
    | _ -> false)


(*********************************************************************)
(******************        GOAL UTILITIES        ********************)

let has_unprocessed_unplanned_excl_mid goal =
  let rec extract_head trs acc = match trs with
    | [] -> acc
    | tr::trs -> match tr.tri_rule with
      | RlExclMid rem -> (match rem.rem_cases with
        | [emc] ->
          if emc.emc_type = EmctUnplanned then acc
          else extract_head trs (acc @ [tr.tri_rule])
        | _ -> extract_head trs (acc @ [tr.tri_rule]))
      | _ -> extract_head trs (acc @ [tr.tri_rule]) in
  let trs = extract_head goal.gl_trace [] in
  not (List.exists is_rule_induction trs)

let check_good_inductive_ptree ptree =
  let rec is_induction_ptc ptc = match ptc.ptc_rule with
    | RlHypothesis rhp -> true
    | RlTheorem rth -> rth.rth_th.th_origin = LorgSynth
    | _ -> List.exists is_induction_ptc ptc.ptc_sub_trees in
  match get_ptree_status ptree with
  | PtValid ptc | PtInfer ptc -> is_induction_ptc ptc
  | _ -> false

let check_potential_inductive_lemma goal ptree =
  (* let lst, rst = goal.gl_lstats, goal.gl_rstats in *)
  let is_convert_lemma goal =
    (goal.gl_lstats.fst_num_hatoms = 1) &&
    (goal.gl_rstats.fst_num_hatoms = 1) in
  let rec is_induction_ptree ptree = match ptree with
    | PtSearch pts -> List.exists is_induction_ptree pts.pts_sub_trees
    | PtDerive ptd -> match ptd.ptd_rule with
      | RlHypothesis rhp -> true
      | RlTheorem rth -> rth.rth_th.th_origin = LorgSynth
      | _ -> List.exists is_induction_ptree ptd.ptd_sub_trees in
  match get_ptree_status ptree with
  | PtValid ptc | PtInfer ptc ->
    (is_induction_ptree ptree) ||
    (is_convert_lemma goal)
  | _ -> false

let is_pmode_prove goal = match goal.gl_proof_mode with
  | PrfEntail | PrfUnsat
  | PrfVerifyLemma | PrfVerifyIndtLemma -> true
  | _ -> false

let is_pmode_verify goal = match goal.gl_proof_mode with
  | PrfVerifyLemma | PrfVerifyIndtLemma -> true
  | _ -> false

let is_pmode_entail goal = match goal.gl_proof_mode with
  | PrfEntail | PrfVerifyLemma | PrfVerifyIndtLemma -> true
  | _ -> false

let is_pmode_unsat goal = match goal.gl_proof_mode with
  | PrfUnsat -> true
  | _ -> false

let is_pmode_infer goal = match goal.gl_proof_mode with
  | PrfInferAll | PrfInferBasic | PrfInferRhs | PrfInferLhs -> true
  | _ -> false

let is_pmode_infer_basic goal = match goal.gl_proof_mode with
  | PrfInferBasic -> true
  | _ -> false

let is_pmode_infer_lhs goal = match goal.gl_proof_mode with
  | PrfInferLhs -> true
  | _ -> false

let is_pmode_infer_rhs goal = match goal.gl_proof_mode with
  | PrfInferRhs -> true
  | _ -> false

let collect_rform_goal goal =
  [goal.gl_lhs; goal.gl_rhs] |> collect_rform_fs

let check_equiv_rdefn rd1 rd2 =
  if (eq_s rd1.rel_name rd2.rel_name) then
    match rd1.rel_body, rd2.rel_body with
    | RbForm f1, RbForm f2 ->
      let ssts = List.map2 (fun v1 v2 ->
        (v1, mk_exp_var v2)) rd1.rel_params rd2.rel_params in
      let nf1 = subst_pf ssts f1 in
      (* PT.check_equiv nf1 f2 *)
      let pfs1, pfs2 = Pair.fold collect_pure_conjuncts_pf nf1 f2 in
      (List.for_all (fun g -> List.exists (eq_patom g) pfs1) pfs2) &&
      (List.for_all (fun g -> List.exists (eq_patom g) pfs2) pfs1)
    | _ -> false
  else false

let dedup_rdefns rds =
  rds |> List.fold_left (fun acc rd ->
    if List.exists (check_equiv_rdefn rd) acc then acc
    else acc @ [rd]) []

let check_equiv_rdefns rds1 rds2 =
  let rds1, rds2 = dedup_rdefns rds1, dedup_rdefns rds2 in
  if List.length rds1 = List.length rds2 then
    List.for_all (fun rd -> List.exists (check_equiv_rdefn rd) rds1) rds2
  else false

let check_equiv_infer_rdefn ird1 ird2 =
  let rds1, rds2 = dedup_rdefns ird1.ird_rdefns, dedup_rdefns ird2.ird_rdefns in
  if List.length rds1 = List.length rds2 then
    List.for_all (fun rd -> List.exists (check_equiv_rdefn rd) rds1) rds2
  else false

let dedup_rdefnss rdss =
  rdss |> List.fold_left (fun acc rds ->
    if List.exists (check_equiv_rdefns rds) acc then acc
    else acc @ [rds]) []

let dedup_infer_rdefns irds =
  irds |> List.fold_left (fun acc ird ->
    if List.exists (check_equiv_infer_rdefn ird) acc then acc
    else acc @ [ird]) []

let dedup_assums asms =
  asms |> List.dedup (fun x y -> x.asm_id = y.asm_id)

let dedup_hypos hypos =
  hypos |> List.dedup (fun x y -> x.hp_ent_id = y.hp_ent_id)


let create_name_lemma_convert vdefn1 vdefn2 =
  str_lemma_convert ^ "_" ^ vdefn1.view_name ^ "_" ^ vdefn2.view_name

let create_name_lemma_combine lhs rhs =
  let lhfs = lhs |> collect_hatom |> List.sortd compare_ha |> pr_has in
  let rhfs = rhs |> collect_hatom |> List.sortd compare_ha |> pr_has in
  str_lemma_combine ^ "_" ^ lhfs ^ "_" ^ rhfs

let create_name_lemma_split lhs rhs =
  let lhfs = lhs |> collect_hatom |> List.sortd compare_ha |> pr_has in
  let rhfs = rhs |> collect_hatom |> List.sortd compare_ha |> pr_has in
  str_lemma_split ^ "_" ^ lhfs ^ "_" ^ rhfs

let is_lemma_name name lm = eq_s lm.lm_name name

let is_theorem_name name th = eq_s th.th_name name

let is_reverse_theorem th1 th2 =
  (eq_s th1.th_lhs_name th2.th_rhs_name) &&
  (eq_s th1.th_rhs_name th2.th_lhs_name)

let collect_used_theorems ptree =
  let rec collect ths ptc =
    let ths = match ptc.ptc_rule with
      | RlTheorem rth -> rth.rth_th::ths
      | _ -> ths in
    ptc.ptc_sub_trees |>
    List.fold_left (fun acc ptc -> collect acc ptc) ths in
  let pts = get_ptree_status ptree in
  let ths = match pts with
    | PtValid ptc -> collect [] ptc
    | _ -> [] in
  List.dedup (fun th1 th2 -> eq_s th1.th_name th2.th_name) ths

let create_lemma_name_hatoms lhas rhas =
  let lname =
    lhas |> List.map (function
      | HData df -> df.dataf_name
      | HView vf -> vf.viewf_name) |>
    List.sorti String.compare |> String.concat "_" in
  let rname =
    rhas |> List.map (function
      | HData df -> df.dataf_name
      | HView vf -> vf.viewf_name) |>
    List.sorti String.compare |> String.concat "_" in
  "_" ^ lname ^ "__entail__" ^ rname ^ "_"

let create_lemma_name lhs rhs =
  let lhas, rhas = collect_hatom lhs, collect_hatom rhs in
  create_lemma_name_hatoms lhas rhas

let update_attempt_inferring_lemma_hatoms pstate lhas rhas =
  let name = create_lemma_name_hatoms lhas rhas in
  let names = pstate.prs_infer_lemma_attempted in
  if not (List.exists (String.equal name) names) then
    pstate.prs_infer_lemma_attempted <- names @ [name]

let update_attempt_inferring_lemma pstate lhs rhs =
  let name = create_lemma_name lhs rhs in
  let names = pstate.prs_infer_lemma_attempted in
  if not (List.exists (String.equal name) names) then
    pstate.prs_infer_lemma_attempted <- names @ [name]

let check_attempt_inferring_lemma_hatoms pstate lhas rhas  =
  let name = create_lemma_name_hatoms lhas rhas in
  let names = pstate.prs_infer_lemma_attempted in
  names |> List.exists (String.equal name)

let check_attempt_inferring_lemma pstate lhs rhs  =
  let name = create_lemma_name lhs rhs in
  let names = pstate.prs_infer_lemma_attempted in
  names |> List.exists (String.equal name)

let check_equiv_lemma_template_hatoms (lhas1, rhas1) (lhas2, rhas2) =
  let name1 = create_lemma_name_hatoms lhas1 rhas1 in
  let name2 = create_lemma_name_hatoms lhas2 rhas2 in
  eq_s name1 name2

let reset_pstate_timeout pstate timeout =
  let _ = pstate.prs_timeout <- float_of_int timeout in
  pstate.prs_start_time <- get_time ();
