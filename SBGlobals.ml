include SBLib.Print

module EString = ExtLib.String


exception EBool of bool
exception EInt of int
exception EFloat of float
exception EStringOpt of string option


(***********************************************************)
(****************        common types       ****************)

type sat_solver =
  | SsvApprox
  | SsvIndt

type release_type =
  | RlsInternal
  | RlsLemmaSynthesis
  | RlsMutualInduction
  | RlsFailureAnalysis

type lemma_kind =
  | LmkSafe
  | LmkUnsafe

type lemma_status =
  | LmsUnknown
  | LmsValid

and lemma_typ =
  | LmtSplit
  | LmtCombine
  | LmtConvert

type infer_rels_typ =
  | IfrWeak
  | IfrStrong

type infer_constraint_typ =
  | IctArith
  | IctPointer
  | IctAll
  | IctAuto

type inter_answer =
  | AnsQuit
  | AnsIn
  | AnsOut

type proof_mode =
  | PrfInferAll
  | PrfInferBasic
  | PrfInferRhs
  | PrfInferLhs
  | PrfVerifyIndtLemma
  | PrfVerifyLemma
  | PrfEntail
  | PrfUnsat

let pr_sat_solver = function
  | SsvApprox -> "SatSolverAppox"
  | SsvIndt -> "SatSolverInduction"

let pr_ssv = pr_sat_solver

let pr_infer_rels_typ = function
  | IfrWeak -> "InferRelsWeak"
  | IfrStrong -> "InferRelsStrong"

let pr_ifr = pr_infer_rels_typ

let pr_infer_constr_typ = function
  | IctArith -> "IctArith"
  | IctPointer -> "IctPointer"
  | IctAll -> "IctAll"
  | IctAuto -> "IctAuto"

let pr_ict = pr_infer_constr_typ

let rec pr_proof_mode mode = match mode with
  | PrfInferAll -> "InferAll"
  | PrfInferBasic -> "InferBasic"
  | PrfInferRhs -> "InferRhs"
  | PrfInferLhs -> "InferLhs"
  | PrfVerifyLemma -> "ProveVerifyLemma"
  | PrfVerifyIndtLemma -> "PrfVerifyIndtLemma"
  | PrfEntail -> "ProveEntail"
  | PrfUnsat -> "ProveUnsat"

let rec pr_prm = pr_proof_mode

let pr_lemma_typ = function
  | LmtSplit -> "split"
  | LmtCombine -> "combine"
  | LmtConvert -> "convert"

let pr_lmt = pr_lemma_typ

let get_infer_rels_type prm = match prm with
  | PrfInferAll -> IfrStrong
  | PrfInferBasic -> IfrWeak
  | PrfInferLhs -> IfrStrong
  | PrfInferRhs -> IfrStrong
  | _ -> IfrWeak



(************************************)
(***       global variables       ***)


(* constants *)
let str_default_data = "node"
let str_default_field = "field"
let str_anon_name = "anon"
let str_lemma_convert = "lemma_convert"
let str_lemma_combine = "lemma_combine"
let str_lemma_split = "lemma_split"

(* input *)
let input_file_name = ref ""
let source_files = ref ([] : string list)
let output_dir = ref "./output"
let build_release = RlsInternal
(* let build_release = RlsFailureAnalysis *)

(* rules *)
let proof_use_rule_theorem = ref true
let proof_use_rule_drop_left = ref true
let proof_use_rule_gen_left = ref false
let proof_use_rule_gen_left_uninst_entail = ref false
let proof_use_rule_excl_mid = ref false

(* induction *)
let mutual_induction = ref false
let proof_check_lhs_unsat = ref true
let proof_use_backjump = ref true
let proof_use_trivial = ref true
let proof_use_counter_theorem = ref false
let infer_invariant = ref true
let proof_interactive = ref false
let proof_check_consistency = ref false    (* check consistency *)

(* failure learning *)
let failure_learning = ref false
let failure_learning_early = ref false

(* disprove *)
let disprove_entail = ref false

(* machine learning *)
let machine_learning = ref false
let machine_learning_all = ref false       (* purely use ML *)
let machine_learning_hybrid = ref false    (* use ML for high confidence *)
let machine_learning_hybrid_confidence = ref 0.5
let machine_learning_send_filename = ref false
let machine_learning_enginee = ref "nn"
let machine_learning_top_rules = ref 1

(* lemma synthesis*)
let proof_lemma_synthesis = ref false
let proof_lemma_synthesis_early = ref false
let lemma_infer_convert = ref true
let lemma_infer_combine = ref true
let lemma_infer_split = ref true

(* constraint solving *)
let use_farkas_incr = ref true
let puretp_use_cache = ref true

(* printing *)
let print_prover_stats = ref false
let print_prover_option = ref false
let print_prog_iast = ref false
let print_prog_iast_typed = ref false
let print_prog_cast = ref false
let print_prog_cast_detail = ref false
let print_lemma_stats = ref false
let print_failure_stats = ref false


(* dump data *)
let dump_ptcore_latex = ref false
let dump_ptree_latex = ref false
let dump_ptree_xml = ref false
let dump_ptree_profile = ref false
let dump_prog_sleek = ref false
let dump_prog_cyclist_entail = ref false
let dump_prog_cyclist_sat = ref false
let dump_prog_smt = ref false

(* time out, in seconds *)
let timeout_check_enabled = ref true
let timeout_puretp = ref 5
let timeout_infer_lemma = ref 80
let timeout_check_entail = ref 120
let timeout_check_unknown_basic = ref 2
let timeout_check_unknown_entail = ref 2
let timeout_verify_valid_ptree = ref 3
let timeout_verify_indt_ptree = ref 3

(* index counter *)
let index_var = ref 0                     (* use in proof phase *)
let index_heap = ref 0                    (* use in proof phase *)
let index_var_infer = ref 0               (* use in infer phase *)
let index_farkas_var = ref 0
let index_pred = ref 0
let index_lemma = ref 0
let index_entail = ref 0                  (* counter for entailment id *)
let index_assumption = ref 0              (* counter for infer context id *)

(***********************************)
(******       threshold       ******)

let thd_max_level_unfolding_group = ref 2
let thd_max_trace_length = ref 20
let thd_max_excmid_unkrel_unplan = ref 5
let thd_min_trace_length_mining = ref 8
let thd_min_trace_length_inconsist = ref 10
let thd_max_trace_length_gen_left = ref 5
let thd_max_trace_length_check_unsat = ref 3
let thd_max_lhs_size_unifying_plan = ref 6
let thd_max_proof_tree_width = ref 3
let thd_max_induction = ref 5
let thd_max_view_left = ref 5
let thd_max_view_right = ref 5
let thd_max_hypothesis = ref 3
let thd_max_mutual_lemma = ref 20
let thd_max_num_rules_preprocess = ref 8
let thd_max_num_farkas_pents = ref 10
let thd_max_num_pents_solving_partial = ref 8
let thd_min_size_choose_only_theorem = ref 8
let thd_max_size_infer_lemma_constr = ref 5
let thd_min_size_infer_lemma_direct = ref 6
let thd_max_num_inferred_ents = ref 1
let thd_max_infer_assumpts = ref 8  (* old is 15 *)
let thd_max_num_unify = ref 5
let thd_max_num_formula_split = ref 5
let thd_max_drop_left =  ref 6
let thd_min_num_rules_remove_useless = ref 1
let thd_max_templ_conj = ref 5
let thd_farkas_max_num_negate_model = ref 4
let thd_max_depth_infer = ref 6
let thd_max_size_decomposed_rdefn = ref 8

(*********************************************)
(***       generic functions               ***)

let fnone = fun _ -> None
let fid = fun x -> x

let dedup_gen eq xs =
  let mem x xs = List.exists (eq x) xs in
  let rec do_remove xs = match xs with
    | [] -> []
    | x::xs -> if (mem x xs) then do_remove xs else x::(do_remove xs) in
  do_remove xs

(*********************************************************)
(****************        positions        ****************)

type pos = {                           (* position *)
  pos_begin : Lexing.position;
  pos_end : Lexing.position;
}

let no_lexpos = {
  Lexing.pos_fname = "";
  Lexing.pos_lnum = 0;
  Lexing.pos_bol = 0;
  Lexing.pos_cnum = 0 }

let no_pos = {
  pos_begin = no_lexpos;
  pos_end = no_lexpos;}

let pr_lexpos pos =
  (string_of_int pos.Lexing.pos_lnum) ^ ":"
  ^ (string_of_int (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))

let pr_pos pos =
  (pr_lexpos pos.pos_begin) ^ "-" ^ (pr_lexpos pos.pos_end)

(*******************************************************)
(****************      basic types      ****************)

type mvlogic =                    (* many-valued logic *)
  | MvlTrue
  | MvlFalse
  | MvlUnkn
  | MvlInfer

let neg_mvl = function
  | MvlTrue -> MvlFalse
  | MvlFalse -> MvlTrue
  | MvlUnkn -> MvlUnkn
  | MvlInfer -> MvlInfer

let pr_mvl = function
  | MvlTrue -> "MvlTrue"
  | MvlFalse -> "MvlFalse"
  | MvlUnkn -> "MvlUnkn"
  | MvlInfer -> "MvlInfer"

type status =
  | StsValid
  | StsInvalid
  | StsSat
  | StsUnsat
  | StsUnkn
  | StsNone

let pr_status sts = match sts with
  | StsValid -> "Valid"
  | StsInvalid -> "Invalid"
  | StsSat -> "Sat"
  | StsUnsat -> "Unsat"
  | StsUnkn -> "Unknown"
  | StsNone -> "None"

(***************************************************)
(****************        type       ****************)

type typ =
  | TInt
  | TBool
  | TUnk
  | TVoid
  | TNull
  | TData of string          (* data structure type *)
  | TVar of int              (* type variable, used for type inference *)

let eq_t t1 t2 = match t1, t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TUnk, TUnk -> true
  | TVoid, TVoid -> true
  | TNull, TNull -> true
  | TData n1, TData n2 -> String.compare n1 n2 = 0
  | TVar i1, TVar i2 -> i1 = i2
  | _ -> false

let pr_typ t = match t with
  | TInt -> "Int"
  | TBool -> "Bool"
  | TVoid -> "Void"
  | TData name -> name
  | TNull -> "Null"
  | TUnk -> "TUnk"
  | TVar i -> "TVar_" ^ (string_of_int i)

let typ_of_var var = snd var

let is_int_typ t = (t = TInt)

let is_ptr_typ = function
  | TData _ -> true
  | TNull -> true
  | _ -> false

let mem_ts t ts = List.exists (fun x -> eq_t t x) ts

let dedup_ts ts    =
  let rec dedup xs = match xs with
    | [] -> []
    | x::xs -> if (mem_ts x xs) then dedup xs else x::(dedup xs) in
  dedup ts

let check_ict_typ constr typ =
  match constr, typ with
  | IctAll, _
  | IctArith, TInt
  | IctPointer, TNull
  | IctPointer, TData _ -> true
  | _ -> false

let check_ict_var constr var =
  check_ict_typ constr (typ_of_var var)

let choose_ict_typs typs =
  let has_int = List.exists is_int_typ typs in
  let has_ptr = List.exists is_ptr_typ typs in
  if has_int && has_ptr then IctAll
  else if has_int then IctArith
  else if has_ptr then IctPointer
  else IctAuto

(************************************)
(***           variables          ***)

type var = (string * typ)

(************************************)
(***   error printing functions   ***)

let get_latest_call_stack n =
  n |> Printexc.get_callstack |> Printexc.raw_backtrace_to_string

let warning msg =
  if (build_release != RlsInternal) then ()
  else if !proof_check_consistency then
    prerr_endline ("\n!!! WARNING (CONSISTENT-MODE): " ^ msg)
  else prerr_endline ("\n!!! Warning: " ^ msg)

let hwarning msg f x =
  let msg = msg ^ " " ^ (f x) in
  warning msg

let fhwarning (msg: string) f x =
  let msg = msg ^ " " ^ (f x) in
  let _ = warning msg in
  failwith msg

let error msg =
  let msg = match build_release with
    | RlsInternal ->
      "\n!!! Error: " ^ msg ^
      "\n!!!Latest call stack:\n" ^ (get_latest_call_stack 10)
    | _ -> "Error: " ^ msg in
  let _ = prerr_endline msg in
  exit 0

let herror msg f x =
  let msg = msg ^ " " ^ (f x) in
  error msg

(************************************)
(*******   naming functions   *******)

let fresh_var_suffix suffix =
  let _ = suffix := !suffix + 1 in
  string_of_int !suffix

let fresh_heap_id () =
  index_heap := !index_heap + 1;
  !index_heap

let extract_var_name_prefix_suffix name =
  let prefix, suffix =
    try
      let uscore_rindex = String.rindex name '_' in
      let prefix_len = uscore_rindex in
      let prefix = String.sub name 0 prefix_len in
      let suffix_len = (String.length name) - (uscore_rindex + 1) in
      let suffix = String.sub name (uscore_rindex + 1) suffix_len in
      let suffix = int_of_string suffix in
      (prefix, suffix)
    with _ -> (name, -1) in
  prefix, suffix

let rec fresh_var_name ?(suffix=index_var) ?(sep="_") name =
  SBDebug.trace_1 "fresh_var_name" (pr_s, pr_s) name
    (fun () -> fresh_var_name_x ~suffix:suffix name ~sep:sep)

and fresh_var_name_x ?(suffix=index_var) ?(sep="_") name =
  let prefix, _ = extract_var_name_prefix_suffix name in
  let suffix = fresh_var_suffix suffix in
  prefix ^ sep ^ suffix

let fresh_var_new_name ?(suffix=index_var) ?(sep="_") () =
  let prefix = "fv" in
  let suffix = fresh_var_suffix suffix in
  prefix ^ sep ^ suffix

let fresh_var_anonym_name ?(suffix=index_var) ?(sep="_") () =
  let prefix = str_anon_name in
  let suffix = fresh_var_suffix suffix in
  prefix ^ sep ^ suffix

let fresh_var ?(suffix=index_var) ?(sfsep="_") (v: var) : var =
  let (vname, vtyp) = v in
  let nvname = fresh_var_name ~suffix:suffix ~sep:sfsep vname in
  (nvname, vtyp)

let fresh_var_of_typ ?(suffix=index_var) ?(sfsep="_") ty =
  let vname = fresh_var_new_name ~suffix:suffix ~sep:sfsep () in
  (vname, ty)

let fresh_pred_name () =
  let _ = index_pred := !index_pred + 1 in
  "pred_" ^ (string_of_int !index_pred)

let fresh_rel_name () =
  let _ = index_pred := !index_pred + 1 in
  "rel_" ^ (string_of_int !index_pred)

let fresh_lemma_name name =
  let _ = index_lemma := !index_lemma + 1 in
  name ^ "_" ^ (string_of_int !index_lemma)


(***********************************************************)
(**************       string functions       ***************)

let is_empty_s s = String.compare (String.trim s) "" = 0

let eq_s s1 s2 = String.compare s1 s2 = 0

let neq_s s1 s2 = String.compare s1 s2 != 0

let count_ss s ss = ss |> List.filter (eq_s s) |> List.length

let mem_ss s ss = List.exists (fun x -> eq_s s x) ss

let subset_ss ss1 ss2 = ss1 |> List.for_all (fun s -> mem_ss s ss2)

let intersect_ss ss1 ss2 = List.filter (fun s -> mem_ss s ss2) ss1

let intersected_ss ss1 ss2 = (intersect_ss ss1 ss2 != [])

let diff_ss ss1 ss2 = List.filter (fun s -> not (mem_ss s ss2)) ss1

let eq_ss ss1 ss2 = (diff_ss ss1 ss2 = []) && (diff_ss ss2 ss1 = [])

let dedup_ss ss    =
  let rec dedup xs = match xs with
    | [] -> []
    | x::xs -> if (mem_ss x xs) then dedup xs else x::(dedup xs) in
  dedup ss

let submset_ss ss1 ss2 =
  ss1 |> dedup_ss |> List.for_all (fun s ->
    (count_ss s ss1) <= (count_ss s ss2))

let has_newline str =
  try
    let _ = Str.search_forward (Str.regexp "\n") str 0 in
    true
  with Not_found -> false

(************************************************************)
(**************       integer functions       ***************)

let compare_int i1 i2 =
  if i1 < i2 then -1
  else if i1 = i2 then 0
  else 1

let mem_ints i is = List.exists (fun x -> i = x) is

let intersect_ints is1 is2 = List.filter (fun x -> mem_ints x is2) is1

let intersected_ints is1 is2 = (intersect_ints is1 is2) != []

let diff_ints is1 is2 = List.filter (fun x -> not (mem_ints x is2)) is1

let eq_ints is1 is2 = (diff_ints is1 is2 = []) && (diff_ints is2 is1 = [])

(*************************************************************)
(************         configuration mode         *************)

let enable_mode_lemma_synthesis () =
  proof_check_lhs_unsat := true;
  proof_lemma_synthesis:= true;
  print_failure_stats := false;
  proof_use_rule_gen_left_uninst_entail := false;
  lemma_infer_convert := true;
  lemma_infer_combine := true;
  lemma_infer_split := true

let enable_mode_lemma_synthesis_early () =
  proof_check_lhs_unsat := true;
  proof_lemma_synthesis_early := true;
  proof_lemma_synthesis := true;
  print_failure_stats := false;
  proof_use_rule_gen_left_uninst_entail := false;
  lemma_infer_convert := true;
  lemma_infer_combine := true;
  lemma_infer_split := true

let enable_mode_mutual_induction () =
  mutual_induction := true;
  proof_use_trivial := true;
  proof_lemma_synthesis_early := false;
  proof_lemma_synthesis := false;
  failure_learning := false;
  proof_use_rule_gen_left := false;
  proof_use_rule_gen_left_uninst_entail := false;
  proof_use_rule_excl_mid := false

let enable_mode_failure_learning () =
  proof_check_lhs_unsat := true;
  failure_learning := true;
  proof_use_trivial := true;
  print_failure_stats := true;
  timeout_check_entail := 120;
  proof_use_rule_drop_left := true;
  proof_use_rule_gen_left := true;
  proof_use_rule_excl_mid := true;
  proof_use_rule_gen_left_uninst_entail := true;
  mutual_induction := false

let enable_mode_disproving () =
  disprove_entail := true

let enable_mode_mutual_induction_with_failure_analysis () =
  mutual_induction := true;
  proof_check_lhs_unsat := true;
  failure_learning := true;
  proof_use_trivial := true;
  print_failure_stats := true;
  proof_use_rule_drop_left := true;
  proof_use_rule_gen_left := true;
  proof_use_rule_excl_mid := true;
  proof_use_rule_gen_left_uninst_entail := true

let enable_mode_check_unsat () =
  proof_check_lhs_unsat := true;
  proof_lemma_synthesis:= false;
  proof_use_rule_gen_left_uninst_entail := true;
  proof_use_rule_gen_left := true;
  proof_lemma_synthesis_early := false;
  proof_lemma_synthesis := false

let enable_mode_check_entail_normal () =
  proof_check_lhs_unsat := false;
  proof_lemma_synthesis:= false;
  proof_lemma_synthesis_early := false;
  print_failure_stats := false;
  proof_use_rule_gen_left_uninst_entail := false

let enable_mode_verify_lemma () =
  mutual_induction := false;
  proof_check_lhs_unsat := false;
  proof_lemma_synthesis_early := false;
  proof_lemma_synthesis := false;
  print_failure_stats := false;
  proof_use_rule_gen_left := false;
  proof_use_rule_gen_left_uninst_entail := false


(*************************************************************)
(**************         some functions         ***************)

let new_entail_id () =
  index_entail := !index_entail + 1;
  !index_entail

let new_assumption_id () =
  index_assumption := !index_assumption + 1;
  !index_assumption

let is_builtin_data data_name =
  EString.starts_with data_name str_default_data


let raise_bool b = raise (EBool b)

let raise_int i = raise (EInt i)
