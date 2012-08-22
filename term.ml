open Gen.Basic
open Globals
open Cprinter
open Cformula

module CP = Cpure
module MCP = Mcpure
module DD = Debug
module TP = Tpdispatcher
module Inf = Infer

type phase_trans = int * int

(* Transition on termination with measures (if any) *)
type term_trans = CP.p_formula * CP.p_formula

(* Transition on program location 
 * src: post_pos
 * dst: proving_loc *)
type term_trans_loc = loc * loc

type term_reason =
  (* Quantum Technique *)
  | Quantum_Technique_Measure_Not_Decreasing of term_trans option
  | Quantum_Technique_Measure_Not_Bounded of CP.exp list
  | Quantum_Technique_Measure_Decreasing of term_trans option
  | Quantum_Technique_Measure_Bounded
  (* Limit Technique *)
  | Limit_Technique_Transition_Invalid of term_trans option
  | Limit_Technique_Loop_Condition_Always_Valid of term_trans option
  | Limit_Technique_Prove_Termination_Succeed of term_trans option
  | Limit_Technique_Precondition_Invalid
  (* General *)
  | Invalid_Status_Trans of term_trans

(* The termination can only be determined when 
 * a base case or an infinite loop is reached *)  
type term_status =
  | Term_S of term_reason
  | NonTerm_S of term_reason
  | MayTerm_S of term_reason (* used for not decreasing or not bounded measures *)
  | Unreachable
  | UnsoundLoop 
  | TermErr of term_reason (* used for invalid status transition *)

(* Location of the transition (from spec to call),
 * Termination Annotation transition,
 * Context and 
 * Its termination status *)
type term_res = term_trans_loc * term_trans option * formula option * term_status

(* We are only interested in two kinds 
 * of constraints in phase inference:
 * p2>p1 and p2>=p1 *)
exception Invalid_Phase_Constr
type phase_constr =
  | P_Gt of (CP.spec_var * CP.spec_var)  (* p2>p1 *)
  | P_Gte of (CP.spec_var * CP.spec_var) (* p2>=p1 *)

(* Using stack to store term_res *)
let term_res_stk : term_res Gen.stack = new Gen.stack

(* Using stack to store term error messages *)
let term_err_stk : string Gen.stack = new Gen.stack

let add_term_res_stk m = 
  if !Globals.dis_term_msg then ()
  else term_res_stk # push m

let add_term_err_stk m =
  if !Globals.dis_term_msg then ()
  else term_err_stk # push m

(* Using stack to store inferred phase
 * transition constraints by inference *)
let phase_constr_stk : CP.formula Gen.stack = new Gen.stack

(* Using hash table to store inferred 
 * phase transition constraints by 
 * inference by mutual scc group *)
let phase_constr_tbl : (int, (ident * CP.formula list) list) Hashtbl.t = 
  Hashtbl.create 20

(* Printing Utilities *)
let pr_phase_trans (trans: phase_trans) =
  let (src, dst) = trans in
  fmt_string "Transition ";
  pr_int src; fmt_string "->"; pr_int dst

let string_of_phase_trans (trans: phase_trans) = 
  poly_string_of_pr pr_phase_trans trans

let pr_term_trans (term_src, term_dst) =
  fmt_open_hbox();
  pr_p_formula term_src;
  fmt_string " -> ";
  pr_p_formula term_dst;
  fmt_close_box()

let string_of_term_trans = poly_string_of_pr pr_term_trans

let pr_term_reason = function
  | Quantum_Technique_Measure_Not_Decreasing _ ->
      fmt_string "Quantum Technique: The variance is not well-founded (not decreasing)."
  | Quantum_Technique_Measure_Not_Bounded _ ->
      fmt_string "Quantum Technique: The variance is not well-founded (not bounded)."
  | Quantum_Technique_Measure_Decreasing _ ->
      fmt_string "Quantum Technique: The variance is decreasing."
  | Quantum_Technique_Measure_Bounded ->
      fmt_string "Quantum Technique: The variance is bounded."
  | Limit_Technique_Transition_Invalid _ ->
      fmt_string "Limit_Technique_Transition_Invalid"
  | Limit_Technique_Loop_Condition_Always_Valid _ -> 
      fmt_string "Limit_Technique_Loop_Condition_Always_Valid"
  | Limit_Technique_Prove_Termination_Succeed _ ->
      fmt_string "Limit_Technique_Prove_Termination_Succeed"
  | Limit_Technique_Precondition_Invalid _ ->
      fmt_string "Limit_Technique_Precondition_Invalid"
  | Invalid_Status_Trans trans -> 
      pr_term_trans trans;
      fmt_string " transition is invalid."

let pr_term_reason_short = function
  | Quantum_Technique_Measure_Not_Decreasing ann_trans -> 
      fmt_string "not decreasing)";
      (match ann_trans with
        | None -> ()
        | Some trans ->  
          fmt_string " ";
          pr_term_trans trans)
  | Quantum_Technique_Measure_Decreasing ann_trans -> 
      fmt_string "decreasing)";
      (match ann_trans with
        | None -> ()
        | Some trans ->  
          fmt_string " ";
          pr_term_trans trans)
  | Quantum_Technique_Measure_Not_Bounded le -> 
      fmt_string "not bounded)";
      pr_seq "" pr_formula_exp le;
  | Quantum_Technique_Measure_Bounded ->
      fmt_string "bounded)"
  | Limit_Technique_Transition_Invalid _ ->
      fmt_string "Limit_Technique_Transition_Invalid)"
  | Limit_Technique_Loop_Condition_Always_Valid _ ->
      fmt_string "Limit_Technique_Loop_Condition_Always_Valid)"
  | Limit_Technique_Prove_Termination_Succeed _ ->
      fmt_string "Limit_Technique_Prove_Termination_Succeed)"
  | Limit_Technique_Precondition_Invalid _ ->
      fmt_string "Limit_Technique_Precondition_Invalid)"
  | Invalid_Status_Trans ann_trans ->
      fmt_string "invalid transition)";
      fmt_string " ";
      pr_term_trans ann_trans

let string_of_term_reason (reason: term_reason) =
  poly_string_of_pr pr_term_reason reason

let pr_term_status = function
  | Term_S reason -> fmt_string "Terminating: "; pr_term_reason reason
  | NonTerm_S reason -> fmt_string "Non-terminating: "; pr_term_reason reason
  | MayTerm_S reason -> fmt_string "May-terminating: "; pr_term_reason reason
  | Unreachable -> fmt_string "Unreachable state."
  | UnsoundLoop -> fmt_string "Unsound context with Loop."
  | TermErr reason -> fmt_string "Error: "; pr_term_reason reason

let pr_term_status_short = function
  | Term_S r -> 
      fmt_string "(OK: ";
      pr_term_reason_short r;
      (* fmt_string ")" *)
  | Unreachable -> fmt_string "(UNR)"
  | MayTerm_S r -> 
      fmt_string "(MayTerm ERR: ";
      pr_term_reason_short r;
      (* fmt_string ")" *)
  | UnsoundLoop -> fmt_string "(ERR: unsound Loop (expecting false ctx))"
  | TermErr r -> 
      fmt_string "(ERR: ";
      pr_term_reason_short r
  | NonTerm_S _ -> fmt_string "(NonTerm_S)"

let string_of_term_status = poly_string_of_pr pr_term_status

let pr_term_ctx (ctx: formula) =
  let h_f, p_f, _, _, _ = split_components ctx in
  begin
    fmt_string "Current context";
    fmt_print_newline ();
    pr_wrap_test "heap: " is_empty_heap pr_h_formula h_f;
    pr_wrap_test "pure: " MCP.isConstMTrue pr_mix_formula p_f;
    fmt_print_newline ();
  end 

let string_of_term_ctx = poly_string_of_pr pr_term_ctx

let pr_term_trans_loc (src, dst) =
(*  let fname = src.start_pos.Lexing.pos_fname in*)
  let src_line = src.start_pos.Lexing.pos_lnum in
  let dst_line = dst.start_pos.Lexing.pos_lnum in
  (* fmt_string (fname ^ " "); *)
  fmt_string ("(" ^ (string_of_int src_line) ^ ")");
  if (dst_line != 0) then
    (fmt_string ("->");
    fmt_string ("(" ^ (string_of_int dst_line) ^ ")"))

let pr_term_res pr_ctx (pos, trans, ctx, status) =
  pr_term_trans_loc pos;
  fmt_string " ";
  pr_term_status_short status;
  (match ctx with
  | None -> ();
  | Some c -> 
      if pr_ctx then (fmt_string ":\n"; pr_term_ctx c) else (););
  (*
  if pr_ctx then fmt_string ">>>>> " else fmt_string ": ";
  pr_term_status status;
  *)
  if pr_ctx then fmt_print_newline () else ()

let string_of_term_res = poly_string_of_pr (pr_term_res false)

let pr_term_res_stk stk =
  let stk =
    let (err, ok) = List.partition (fun (_, _, _, status) ->
      match status with
      | Term_S _
      | Unreachable -> false
      | _ -> true
    ) stk in
    if (!Globals.term_verbosity == 0) then err@ok
    else err
  in 
  List.iter (fun r -> 
    pr_term_res (!Globals.term_verbosity == 0) r; 
    fmt_print_newline ();) stk

let pr_term_err_stk stk =
  List.iter (fun m -> fmt_string m; fmt_print_newline ()) stk

let pr_phase_constr = function
  | P_Gt (v1, v2) -> 
      pr_spec_var v1; fmt_string ">"; pr_spec_var v2
  | P_Gte (v1, v2) -> 
      pr_spec_var v1; fmt_string ">="; pr_spec_var v2 

let string_of_phase_constr = poly_string_of_pr pr_phase_constr
(* End of Printing Utilities *)

(* To find a LexVar formula *)
exception Exn_TermVar of string;;
exception Exn_LexVar of string;;
exception Exn_SeqVar of string;;

(* let rec has_variance_struc struc_f = *)
(*   List.exists (fun ef -> has_variance_ext ef) struc_f *)
  
(* and has_variance_ext ext_f =  *)
(*   match ext_f with *)
(*     | ECase { formula_case_branches = cl } -> *)
(*         List.exists (fun (_, sf) -> has_variance_struc sf) cl *)
(*     | EBase { formula_ext_continuation = cont } -> *)
(*         has_variance_struc cont *)
(*     | EAssume _ -> false *)
(*     | EVariance _ -> true *)
(*     | EInfer {formula_inf_continuation = cont} -> has_variance_ext cont *)

(* let lexvar_of_evariance (v: ext_variance_formula) : CP.formula option = *)
(*   if (v.formula_var_measures = []) then None *)
(*   else *)
(*	   let vm = fst (List.split v.formula_var_measures) in *)
(*	   let vi = v.formula_var_infer in *)
(*     let pos = v.formula_var_pos in *)
(*     Some (CP.mkPure (CP.mkLexVar Term vm vi pos)) *)

(* let measures_of_evariance (v: ext_variance_formula) : (term_ann * CP.exp list * CP.exp list) = *)
(*   let vm = fst (List.split v.formula_var_measures) in *)
(*	 let vi = v.formula_var_infer in *)
(*   (Term, vm, vi) *)
  
let find_lexvar_b_formula (bf: CP.b_formula) : CP.p_formula =
  let (pf, _) = bf in
  match pf with
  | CP.LexVar _ -> pf
  | _ -> raise (Exn_LexVar "LexVar not found!")

let rec find_lexvar_formula (f: CP.formula) : CP.p_formula =
  match f with
  | CP.BForm (bf, _) -> find_lexvar_b_formula bf
  | CP.And (f1, f2, _) ->
      (try find_lexvar_formula f1
      with _ -> find_lexvar_formula f2)
  | _ -> raise (Exn_LexVar "LexVar not found!")

let find_seqvar_b_formula (bf: CP.b_formula) : CP.p_formula =
  let (pf, _) = bf in
  match pf with
  | CP.SeqVar _ -> pf
  | _ -> raise (Exn_SeqVar "SeqVar not found!")

let rec find_seqvar_formula (f: CP.formula) : CP.p_formula =
  match f with
  | CP.BForm (bf, _) -> find_seqvar_b_formula bf
  | CP.And (f1, f2, _) ->
      (try find_seqvar_formula f1
      with _ -> find_seqvar_formula f2)
  | _ -> raise (Exn_SeqVar "SeqVar not found!")

let find_termvar_b_formula (bf: CP.b_formula) : CP.p_formula =
  let (pf, _) = bf in
  match pf with
  | CP.LexVar _
  | CP.SeqVar _ -> pf
  | _ -> raise (Exn_TermVar "TermVar not found 2!")

let rec find_termvar_formula (f: CP.formula) : CP.p_formula =
  match f with
  | CP.BForm (bf, _) -> find_termvar_b_formula bf
  | CP.And (f1, f2, _) -> (
      try find_termvar_formula f1 
      with _ -> find_termvar_formula f2
    )
  | _ -> raise (Exn_TermVar "TermVar not found 3!")

(* To syntactically simplify LexVar formula *) 
(* (false,[]) means not decreasing *)
let rec syn_simplify_lexvar bnd_measures =
  match bnd_measures with
  (* 2 measures are identical, 
   * so that they are not decreasing *)
  | [] -> (false, [])   
  | (s,d)::rest -> 
      if (CP.eqExp s d) then syn_simplify_lexvar rest
      else if (CP.is_gt CP.eq_spec_var s d) then (true, [])
      else if (CP.is_lt CP.eq_spec_var s d) then (false, [])
      else (true, bnd_measures) 

let find_lexvar_es (es: entail_state) : CP.p_formula =
  match es.es_var_measures with
  | Some (CP.LexVar lex) -> CP.LexVar lex
  | _ -> raise (Exn_LexVar "LexVar not found!")

(** find sequence var in entail_state*)
let find_seqvar_es (es: entail_state) : CP.p_formula =
  match es.es_var_measures with
  | Some (CP.SeqVar seq) -> CP.SeqVar seq
  | _ -> raise (Exn_SeqVar "SeqVar not found!")

let find_termvar_es (es: entail_state) : CP.p_formula =
  match es.es_var_measures with
  | Some (CP.LexVar lex) -> CP.LexVar lex
  | Some (CP.SeqVar seq) -> CP.SeqVar seq
  | _ -> raise (Exn_SeqVar "SeqVar not found!")

let zero_exp = [CP.mkIConst 0 no_pos]
 
let one_exp = [CP.mkIConst 1 no_pos] 

(* Normalize the longer LexVar prior to the shorter one *)
let norm_lexvar_measures_by_length src dst =
  let sl = List.length src in
  let dl = List.length dst in
  (* if dl==0 && sl>0 then None *)
  (* else *)
  if (sl = dl) then Some (src, dst)
  else if (sl > dl) then
    if dl=0 then None
    else Some ((Gen.BList.take dl src)@one_exp, dst@zero_exp)
  else Some (src, Gen.BList.take sl dst)

let norm_seqvar_measures_trans_x trans =
  (* TRUNG BUG*)
  match trans with
  | Some (CP.SeqVar seq1, CP.SeqVar seq2) -> (
      match seq1.CP.seq_element, seq2.CP.seq_element with
      | CP.Null _, _ -> None
      | _, CP.Null _ -> None
      | _, _ -> (
          if (seq1.CP.seq_ann = seq2.CP.seq_ann) && (seq1.CP.seq_decrease = seq2.CP.seq_decrease) then
            Some (seq1, seq2)
          else
            None
        )
    )
  | _ ->
      None

let norm_seqvar_measures_trans trans =
  let pr_in trans = (
    match trans with
    | None -> "trans = None"
    | Some (term_s, term_d) -> 
        "trans = Some: " 
        ^ "\n    trans_source = " ^ (Cprinter.string_of_p_formula term_s)
        ^ "\n    trans_dest   = " ^ (Cprinter.string_of_p_formula term_d)
  ) in
  let pr_out res = (
    match res with
    | None -> "None"
    | Some _ -> "Some"
  ) in
  Debug.no_1 "norm_seqvar_measures_trans" pr_in pr_out (fun t -> norm_seqvar_measures_trans_x t) trans

(** strip termination var from a formula
    return: termvar * remained formula *)
let strip_termvar_mix_formula_x (mf: MCP.mix_formula) =
  let mf_p = MCP.pure_of_mix mf in
  let mf_ls = CP.split_conjunctions mf_p in
  let (termforms, other_p) = List.partition (CP.is_termvar) mf_ls in
  let extract_termvar (f : CP.formula) : CP.p_formula =
    match f with
    | CP.BForm ((CP.LexVar lexinfo,_),_) -> CP.LexVar lexinfo
    | CP.BForm ((CP.SeqVar seqinfo,_),_) -> CP.SeqVar seqinfo 
    | _ -> let _ = report_error no_pos "[term.ml] unexpected Term in check_lexvar_rhs" in
           raise (Exn_TermVar "TermVar invalid") in
  let termvars = List.map extract_termvar termforms in
  (termvars, CP.join_conjunctions other_p)

let strip_termvar_mix_formula (mf: MCP.mix_formula) =
  let pr = Cprinter.string_of_mix_formula in
  let pr_out (a, b) = 
    let termvars = Cprinter.string_of_list_f Cprinter.string_of_p_formula a in
    let remained_rhs = Cprinter.string_of_pure_formula b in
    "termvars = " ^ termvars ^ "  ## " ^ "remained_rhs = " ^ remained_rhs in 
  Debug.no_1 "strip_termvar_mix_formula" pr pr_out strip_termvar_mix_formula_x mf

(* Termination: The boundedness checking for HIP has been done before *)  
let check_lexvar_measures_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p src_lv dst_lv t_ann_trans pos =
  let ans  = norm_lexvar_measures_by_length src_lv dst_lv in
  let l_pos = post_pos # get in
  let l_pos = if l_pos == no_pos then pos else l_pos in (* Update pos for SLEEK output *)
  let term_pos = (l_pos, proving_loc # get) in
  match ans with
      (* From primitive calls - 
       * Do not need to add messages to stack *)
    | None -> (estate, lhs_p, rhs_p, None)     
    | Some (src_lv, dst_lv) ->
        (* TODO : Let us assume Term[] is for base-case
           and primitives. In the case of non-primitive,
           it will be converted to Term[call] using
           the call hierarchy. No need for Term[-1]
           and some code dealing with primitives below *)
        let orig_ante = estate.es_formula in
        (* [s1,s2] |- [d1,d2] -> [(s1,d1), (s2,d2)] *)
        let bnd_measures = List.map2 (fun s d -> (s, d)) src_lv dst_lv in
        (* [(0,0), (s2,d2)] -> [(s2,d2)] *)
        let res, bnd_measures = syn_simplify_lexvar bnd_measures in
        if bnd_measures = [] then 
          let lexvar = find_lexvar_es estate in
          let t_ann, ml, il = match lexvar with
                              | CP.LexVar lex -> (lex.CP.lex_ann, lex.CP.lex_exp, lex.CP.lex_tmp)
                              | _ -> raise (Exn_LexVar "LexVar not found!") in
          (* Residue of the termination,
           * The termination checking result - 
           * For HIP: stored in term_res_stk
           * For SLEEK: stored in the stack of error msg (es_var_stack) 
           * and update es_term_err *)
          let term_measures, term_res, term_err_msg =
            if res then (* The measures are decreasing *)
              Some (CP.mkLexVar t_ann ml il no_pos), (* Residue of termination *)
              (term_pos, t_ann_trans, Some orig_ante, Term_S (Quantum_Technique_Measure_Decreasing t_ann_trans)),
              None
            else 
              Some (CP.mkLexVar (Fail TermErr_May) ml il no_pos),
              (term_pos, t_ann_trans, Some orig_ante, MayTerm_S (Quantum_Technique_Measure_Not_Decreasing t_ann_trans)),
              Some (string_of_term_res (term_pos, t_ann_trans, None, MayTerm_S (Quantum_Technique_Measure_Not_Decreasing t_ann_trans))) 
          in
          (* let term_stack = match term_err_msg with *)
          (*  | None -> estate.es_var_stack *)
          (*  | Some msg -> (* add_term_err_stk msg; *) msg::estate.es_var_stack *)
          (* in *)
          let term_err = match estate.es_term_err with
            | None -> term_err_msg
            | Some _ -> estate.es_term_err 
          in
          let n_estate = { estate with
            es_var_measures = term_measures;
            (* es_var_stack = term_stack; *)
            es_term_err = term_err;
          } in
          add_term_res_stk term_res;
          (n_estate, lhs_p, rhs_p, None)
        else
          (* [(s1,d1), (s2,d2)] -> [[(s1,d1)], [(s1,d1),(s2,d2)]]*)
          let lst_measures = List.fold_right (fun bm res ->
            [bm]::(List.map (fun e -> bm::e) res)) bnd_measures [] in
          (* [(s1,d1),(s2,d2)] -> s1=d1 & s2>d2 *)
          let lex_formula measure = snd (List.fold_right (fun (s,d) (flag,res) ->
            let f = 
              if flag then CP.BForm ((CP.mkGt s d pos, None), None) (* s>d *)
              else CP.BForm ((CP.mkEq s d pos, None), None) in (* s=d *)
              (false, CP.mkAnd f res pos)) measure (true, CP.mkTrue pos)) in
          let rank_formula = List.fold_left (fun acc m ->
            CP.mkOr acc (lex_formula m) None pos) (CP.mkFalse pos) lst_measures in
          let lhs = MCP.pure_of_mix (MCP.merge_mems lhs_p xpure_lhs_h1 true) in
          DD.devel_zprint (lazy ("Rank formula: " ^ (Cprinter.string_of_pure_formula rank_formula))) pos;
          (* TODO: rhs_p & rhs_p_br & heap_entail_build_mix_formula_check pos & rank_formula(I,O) *)
          (*let (estate,_,rank_formula,_) = Inf.infer_collect_rel TP.is_sat_raw estate xpure_lhs_h1 
            lhs_p (MCP.mix_of_pure rank_formula) [] (fun i_es_vars i_lhs i_rhs i_pos -> i_lhs, i_rhs) pos in
          let rank_formula = MCP.pure_of_mix rank_formula in*)
          let entail_res, _, _ = TP.imply lhs rank_formula "" false None in 
          begin
            (* print_endline ">>>>>> trans_lexvar_rhs <<<<<<" ; *)
            (* print_endline ("Transformed RHS: " ^ (Cprinter.string_of_mix_formula rhs_p)) ; *)
            DD.devel_zprint (lazy (">>>>>> [term.ml][trans_lexvar_rhs] <<<<<<")) pos;
            DD.devel_zprint (lazy ("Transformed RHS: " ^ (Cprinter.string_of_mix_formula rhs_p))) pos;
            DD.devel_zprint (lazy ("LHS (lhs_p): " ^ (Cprinter.string_of_mix_formula lhs_p))) pos;
            DD.devel_zprint (lazy ("LHS (xpure 0): " ^ (Cprinter.string_of_mix_formula xpure_lhs_h0))) pos;
            DD.devel_zprint (lazy ("LHS (xpure 1): " ^ (Cprinter.string_of_mix_formula xpure_lhs_h1))) pos;
            DD.devel_zprint (lazy ("Wellfoundedness checking: " ^ (string_of_bool entail_res))) pos;
          end;
          let lexvar = find_lexvar_es estate in
          let t_ann, ml, il = match lexvar with
                              | CP.LexVar lex -> (lex.CP.lex_ann, lex.CP.lex_exp, lex.CP.lex_tmp)
                              | _ -> raise (Exn_LexVar "LexVar not found!") in
          let term_measures, term_res, term_err_msg, rank_formula =
            if entail_res then (* Decreasing *) 
              Some (CP.mkLexVar t_ann ml il no_pos), 
              (term_pos, t_ann_trans, Some orig_ante, Term_S (Quantum_Technique_Measure_Decreasing t_ann_trans)),
              None, 
              None
            else
              if Inf.no_infer_all estate then (* No inference at all *)
                Some (CP.mkLexVar (Fail TermErr_May) ml il no_pos),
                (term_pos, t_ann_trans, Some orig_ante, MayTerm_S (Quantum_Technique_Measure_Not_Decreasing t_ann_trans)),
                Some (string_of_term_res (term_pos, t_ann_trans, None, MayTerm_S (Quantum_Technique_Measure_Not_Decreasing t_ann_trans))),
                None
              else
                (* Inference: the es_var_measures will be
                 * changed based on the result of inference 
                 * The term_res_stk and es_var_stack 
                 * should be updated based on this result: 
                 * MayTerm_S -> Term_S *)
                (* Assumming Inference will be successed *)
                Some (CP.mkLexVar t_ann ml il no_pos),
                (term_pos, t_ann_trans, Some orig_ante, Term_S (Quantum_Technique_Measure_Decreasing t_ann_trans)),
                None, 
                Some rank_formula  
          in 
          (* let term_stack = match term_err_msg with *)
          (*  | None -> estate.es_var_stack *)
          (*  | Some msg -> (* add_term_err_stk msg; *) msg::estate.es_var_stack *)
          (* in *)
          let term_err = match estate.es_term_err with
            | None -> term_err_msg
            | Some _ -> estate.es_term_err 
          in
          let n_estate = { estate with
            es_var_measures = term_measures;
            (* es_var_stack = term_stack; *)
            es_term_err = term_err
          } in
          add_term_res_stk term_res;
          (n_estate, lhs_p, rhs_p, rank_formula)

let check_lexvar_measures estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p src_lv dst_lv t_ann_trans pos =
  let pr = !print_mix_formula in
  let pr1 = !CP.print_formula in
  let pr2 = !print_entail_state in
  let pr3 = pr_list !CP.print_exp in
  Debug.no_5 "check_lexvar_measures" pr2 
      (add_str "lhs_p" pr) 
      (add_str "rhs_p" pr) 
      (add_str "src_lv" pr3) 
      (add_str "src_rv" pr3)
    (fun (es, lhs, rhs, rank_fml) -> 
        pr_quad pr2 (add_str "lhs" pr) 
            (add_str "rhs" pr) 
            (add_str "rank_fml" (pr_option pr1)) 
            (es, lhs, rhs, rank_fml))  
      (fun _ _ _ _ _ -> check_lexvar_measures_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p src_lv dst_lv t_ann_trans pos) 
        estate lhs_p rhs_p src_lv dst_lv

(* To handle LexVar formula *)
(* Remember to remove LexVar in RHS *)
let check_lexvar_rhs_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos =
  try
    begin
      let _ = DD.trace_hprint (add_str "es" !print_entail_state) estate pos in
      let conseq = MCP.pure_of_mix rhs_p in
      let lexvar_dst = find_lexvar_formula conseq in
      let t_ann_d, dst_lv, l_pos = match lexvar_dst with
                                   | CP.LexVar lex -> (lex.CP.lex_ann, lex.CP.lex_exp, lex.CP.lex_loc)
                                   | _ -> raise (Exn_LexVar "LexVar not found!") in
      let lexvar_src = find_lexvar_es estate in
      let t_ann_s, src_lv, src_il = match lexvar_src with
                          | CP.LexVar lex -> (lex.CP.lex_ann, lex.CP.lex_exp, lex.CP.lex_tmp)
                          | _ -> raise (Exn_LexVar "LexVar not found!") in
      let t_ann_trans = (lexvar_src, lexvar_dst) in
      let t_ann_trans_opt = Some t_ann_trans in
      let _, rhs_p = strip_termvar_mix_formula rhs_p in
      let rhs_p = MCP.mix_of_pure rhs_p in
      let p_pos = post_pos # get in
      let p_pos = if p_pos == no_pos then l_pos else p_pos in (* Update pos for SLEEK output *)
      let term_pos = (p_pos, proving_loc # get) in
      match (t_ann_s, t_ann_d) with
      | (Term, Term)
      | (Fail TermErr_May, Term) ->
          (* Check wellfoundedness of the transition *)
          check_lexvar_measures estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p
            src_lv dst_lv t_ann_trans_opt l_pos
      | (Term, _)
      | (Fail TermErr_May, _) -> 
          let term_res = (term_pos, t_ann_trans_opt, Some estate.es_formula,
            TermErr (Invalid_Status_Trans t_ann_trans)) in
          add_term_res_stk term_res;
          add_term_err_stk (string_of_term_res term_res);
          let term_measures = (
            match t_ann_d with
            | Loop 
            | Fail TermErr_Must ->
                Some (CP.mkLexVar (Fail TermErr_Must) src_lv src_il no_pos)
            | MayLoop
            | Fail TermErr_May ->
                Some (CP.mkLexVar (Fail TermErr_May) src_lv src_il no_pos)
            | Term ->
                let _ = report_error no_pos "[term.ml] unexpected Term in check_lexvar_rhs" in
                raise (Exn_LexVar "LexVar invalid")
          ) in
          let term_err = match estate.es_term_err with
            | None ->  Some (string_of_term_res term_res)
            | Some _ -> estate.es_term_err 
          in
          let n_estate = {estate with 
            es_var_measures = term_measures;
            (* es_var_stack = (string_of_term_res term_res)::estate.es_var_stack; *)
            es_term_err = term_err;
          } in
          (n_estate, lhs_p, rhs_p, None)
      | (Loop, _) ->
          let term_measures = Some (CP.mkLexVar Loop [] [] no_pos) in
          let n_estate = {estate with es_var_measures = term_measures} in
          (n_estate, lhs_p, rhs_p, None)
      | (MayLoop, _) ->
          let term_measures = Some (CP.mkLexVar MayLoop [] [] no_pos) in 
          let n_estate = {estate with es_var_measures = term_measures} in
          (n_estate, lhs_p, rhs_p, None)
      | (Fail TermErr_Must, _) ->
          let n_estate = {estate with 
            es_var_measures = Some (CP.mkLexVar (Fail TermErr_Must) src_lv src_il no_pos);
          } in
          (n_estate, lhs_p, rhs_p, None)
    end
  with e -> (
    let n_estate = {estate with
      es_var_measures = Some (CP.mkLexVar (Fail TermErr_May) [] [] no_pos);
      es_term_err = Some ("!!!Exception while checking termination 1: " ^ (Printexc.to_string e));
    } in
    (n_estate, lhs_p, rhs_p, None)
  )

  (* if (not !Globals.dis_term_chk) or (estate.es_term_err == None) then *)
  (*   check_term_rhs estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos *)
  (* else *)
  (*   (* Remove LexVar in RHS *) *)
  (*   let _, rhs_p = strip_lexvar_mix_formula rhs_p in *)
  (*   let rhs_p = MCP.mix_of_pure rhs_p in *)
  (*   (estate, lhs_p, rhs_p, None) *)

let check_lexvar_rhs estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos =
  let pr = !print_mix_formula in
  let pr2 = !print_entail_state in
   Debug.no_3 "trans_lexvar_rhs" pr2 pr pr
    (fun (es, lhs, rhs, _) -> pr_triple pr2 pr pr (es, lhs, rhs))  
      (fun _ _ _ -> check_lexvar_rhs_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos) estate lhs_p rhs_p

(* collect the update function from a transition constraint *)
(* by obtaining only the assignments (consider only Eq p_formula) *)
let collect_update_function_x (transition_constraint: CP.formula) : CP.formula =
  let is_assignment (pf: CP.p_formula) : bool =
    match pf with
    | CP.Eq _ -> true
    | _ -> false in
  let rec convert_formula (f: CP.formula) : CP.formula = (
    match f with
    | CP.BForm ((pf, _), _) ->
        if is_assignment pf then f
        else CP.mkTrue no_pos
    | CP.And (f1, f2, l) ->
        let new_f1 =
          match f1 with
          | CP.BForm ((pf, _), _) ->
              if is_assignment pf then f1
              else CP.mkTrue no_pos
          | _ -> convert_formula f1 in
        let new_f2 =
          match f2 with
          | CP.BForm ((pf, _), _) ->
              if is_assignment pf then f2
              else CP.mkTrue no_pos
          | _ -> convert_formula f2 in
        CP.And (new_f1, new_f2, l)
    | CP.AndList formula_list ->
        let (ls, fs) = List.split formula_list in
        let new_fs =
          List.map (
            fun f -> match f with
            | CP.BForm ((pf, _), _) ->
                if is_assignment pf then f
                else CP.mkTrue no_pos
            | _ -> convert_formula f
          ) fs in
        let new_formula_list = List.combine ls new_fs in
        CP.AndList new_formula_list
    | CP.Or (f1, f2, l1, l2) ->
        let new_f1 =
          match f1 with
          | CP.BForm ((pf, _), _) ->
              if is_assignment pf then f1
              else CP.mkTrue no_pos
          | _ -> convert_formula f1 in
        let new_f2 =
          match f2 with
          | CP.BForm ((pf, _), _) ->
              if is_assignment pf then f2
              else CP.mkTrue no_pos
          | _ -> convert_formula f2 in
        CP.Or (new_f1, new_f2, l1, l2)
    | CP.Not (f, l1, l2) ->
        (* let new_f = convert_formula f in *)
        (* CP.Not (new_f, l1, l2)           *)
        CP.mkTrue no_pos
    | CP.Forall (s, f, l1, l2) ->
        (* let new_f = convert_formula f in *)
        (* CP.Forall (s, new_f, l1, l2)     *)
        CP.mkTrue no_pos
    | CP.Exists (s, f, l1, l2) ->
        (* let new_f = convert_formula f in *)
        (* CP.Exists (s, new_f, l1, l2)     *)
        CP.mkTrue no_pos
  ) in
  convert_formula transition_constraint

let collect_update_function (transition_constraint: CP.formula) : CP.formula =
  let pr = !CP.print_formula in
  Debug.no_1 "collect_update_function" pr pr collect_update_function_x transition_constraint

(* collect the arithmetic constraint from a transition constraint *)
(* by obtaining only the assignments or comparision formula *)
let collect_arithmetic_constraint_x (transition_constraint: CP.formula) : CP.formula =
  let is_arithmetic_formula (pf: CP.p_formula) : bool =
    match pf with
    | CP.Eq _ | CP.Neq _ | CP.Lt _ | CP.Lte _ | CP.Gt _ | CP.Gte _ -> true
    | _ -> false in
  let rec convert_formula (f: CP.formula) : CP.formula = (
    match f with
    | CP.BForm ((pf, _), _) ->
        if is_arithmetic_formula pf then f
        else CP.mkTrue no_pos
    | CP.And (f1, f2, l) ->
        let new_f1 =
          match f1 with
          | CP.BForm ((pf, _), _) ->
              if is_arithmetic_formula pf then f1
              else CP.mkTrue no_pos
          | _ -> convert_formula f1 in
        let new_f2 =
          match f2 with
          | CP.BForm ((pf, _), _) ->
              if is_arithmetic_formula pf then f2
              else CP.mkTrue no_pos
          | _ -> convert_formula f2 in
        CP.And (new_f1, new_f2, l)
    | CP.AndList formula_list ->
        let (ls, fs) = List.split formula_list in
        let new_fs =
          List.map (
            fun f -> match f with
            | CP.BForm ((pf, _), _) ->
                if is_arithmetic_formula pf then f
                else CP.mkTrue no_pos
            | _ -> convert_formula f
          ) fs in
        let new_formula_list = List.combine ls new_fs in
        CP.AndList new_formula_list
    | CP.Or (f1, f2, l1, l2) ->
        let new_f1 =
          match f1 with
          | CP.BForm ((pf, _), _) ->
              if is_arithmetic_formula pf then f1
              else CP.mkTrue no_pos
          | _ -> convert_formula f1 in
        let new_f2 =
          match f2 with
          | CP.BForm ((pf, _), _) ->
              if is_arithmetic_formula pf then f2
              else CP.mkTrue no_pos
          | _ -> convert_formula f2 in
        CP.Or (new_f1, new_f2, l1, l2)
    | CP.Not (f, l1, l2) ->
        (* let new_f = convert_formula f in *)
        (* CP.Not (new_f, l1, l2)           *)
        CP.mkTrue no_pos
    | CP.Forall (s, f, l1, l2) ->
        (* let new_f = convert_formula f in *)
        (* CP.Forall (s, new_f, l1, l2)     *)
        CP.mkTrue no_pos
    | CP.Exists (s, f, l1, l2) ->
        (* let new_f = convert_formula f in *)
        (* CP.Exists (s, new_f, l1, l2)     *)
        CP.mkTrue no_pos
  ) in
  convert_formula transition_constraint

let collect_arithmetic_constraint (transition_constraint: CP.formula) : CP.formula =
  let pr = !CP.print_formula in
  Debug.no_1 "collect_arithmetic_constraint" pr pr collect_arithmetic_constraint_x transition_constraint

let check_decreasing_seqvar_precondition_x (assumption: CP.formula)
                                           (domain_src: CP.formula)
                                           (loopcond: CP.formula)
                                           : (bool * string) =
  (* initial constraint -> domain_src *)
  let domain_src_check, _, _ = TP.imply assumption domain_src "" false None in
  let _ = Debug.dinfo_pprint ("++ In function: check_decreasing_seqvar_precondition_x") no_pos in
  let _ = Debug.dinfo_pprint ("assumption = " ^ (Cprinter.string_of_pure_formula assumption)) no_pos in
  let _ = Debug.dinfo_pprint ("domain_src = " ^ (Cprinter.string_of_pure_formula domain_src))  no_pos in
  let _ = Debug.dinfo_pprint ("domain_src_check = " ^ (string_of_bool domain_src_check))  no_pos in
  if not domain_src_check then
    (false, "Domain doesn't cover assumption!")
  else (
    (* (assumption -> precondition is VALID *)
    let loopcond_check, _, _ = TP.imply assumption loopcond "" false None in
    let _ = Debug.dinfo_pprint ("++ In function: check_decreasing_seqvar_precondition_x") no_pos in
    let _ = Debug.dinfo_pprint ("assumption = " ^ (Cprinter.string_of_pure_formula assumption)) no_pos in
    let _ = Debug.dinfo_pprint ("loopcond = " ^ (Cprinter.string_of_pure_formula loopcond)) no_pos in
    let _ = Debug.dinfo_pprint ("loopcond_check = " ^ (string_of_bool loopcond_check)) no_pos in
    if not loopcond_check then 
      (false, "Loop condition isn't satisfiable! Program won't enter the loop.")
    else
      (true, "Precondition checking OK!")
  )


let check_decreasing_seqvar_precondition (assumption: CP.formula)
                                         (domain_src: CP.formula)
                                         (loopcond: CP.formula)
                                         : (bool * string) =
  let pr_in = Cprinter.string_of_pure_formula in
  let pr_out = string_of_bool in
  Debug.no_2 "check_decreasing_seqvar_precondition"
             pr_in pr_in pr_out
             (fun p1 p2 -> check_decreasing_seqvar_precondition_x p1 p2)
             assumption domain_src loopcond

let check_decreasing_seqvar_transition_x (assumption : CP.formula)
                                         (seqvar_src: CP.sequence_info)
                                         (seqvar_dst: CP.sequence_info)
                                         : (bool * string) =
  let element_src = seqvar_src.CP.seq_element in
  let domain_src = seqvar_src.CP.seq_domain in
  let limit_src = seqvar_src.CP.seq_limit in 
  let element_dst = seqvar_dst.CP.seq_element in
  let domain_dst = seqvar_dst.CP.seq_domain in
  let limit_dst = seqvar_dst.CP.seq_limit in 
  (* domain coverage check*)
  let init_constraint = collect_arithmetic_constraint assumption in
  let domain_src_cons = CP.mkAnd init_constraint domain_src no_pos in
  let domain_cover_check, _, _ = TP.imply domain_src_cons domain_dst "" false None in 
  let _ = Debug.dinfo_pprint ("++ In function: check_decreasing_seqvar_transition_x") no_pos in
  let _ = Debug.dinfo_pprint ("domain_src_cons = " ^ (Cprinter.string_of_pure_formula domain_src_cons)) no_pos in
  let _ = Debug.dinfo_pprint ("domain_dst = " ^ (Cprinter.string_of_pure_formula domain_dst)) no_pos in
  let _ = Debug.dinfo_pprint ("domain_cover_check = " ^ (string_of_bool domain_cover_check)) no_pos in
  if not domain_cover_check then
    (false, "Domain isn't covered in recursive call!")
  else (
    (* distance decrease check *)
    let distance_constraint = (
      match limit_src, limit_dst with
      | CP.SConst (Pos_infinity, _), _
      | _, CP.SConst (Pos_infinity, _) ->
          let _ = report_error no_pos "check_decreasing_seqvar_transition: the lower-bound of the domain can't be Pos_infinity" in
          raise (Exn_SeqVar "The domain of measure is invalid")
      | CP.SConst (Neg_infinity, _), CP.SConst (Neg_infinity, _) ->
          (* Constraint: element_src > elment_dst *)
          CP.mkPure (CP.mkGt element_src element_dst no_pos)
      | CP.SConst (Neg_infinity, _), _
      | _, CP.SConst (Neg_infinity, _) ->
          let _ = report_error no_pos "check_decreasing_seqvar_transition: Neg_infinity cannot appears in only 1 side of transition" in
          raise (Exn_SeqVar "The domain of measure is invalid")
      | _ ->
          (* Constraint: (element_src > limit_src)      *)
          (*             && (element_dst > limit_dst)   *)
          (*             && (element_src > element_dst) *)
          let dc1 = CP.mkPure (CP.mkGt element_src limit_src no_pos) in
          let dc2 = CP.mkPure (CP.mkGt element_dst limit_dst no_pos) in
          let dc3 = CP.mkPure (CP.mkGt element_src element_dst no_pos) in
          CP.mkAnd dc1 (CP.mkAnd dc2 dc3 no_pos) no_pos
      ) in
    let domain_constraint = CP.mkAnd init_constraint (CP.mkAnd domain_src domain_dst no_pos) no_pos in
    let distance_decrease_check, _, _ = TP.imply domain_constraint distance_constraint "" false None in
    let _ = Debug.dinfo_pprint ("++ In function: check_decreasing_seqvar_transition_x") no_pos in
    let _ = Debug.dinfo_pprint ("domain_constraint = " ^ (Cprinter.string_of_pure_formula domain_constraint)) no_pos in
    let _ = Debug.dinfo_pprint ("distance_constraint = " ^ (Cprinter.string_of_pure_formula distance_constraint)) no_pos in
    let _ = Debug.dinfo_pprint ("distance_decrease_check = " ^ (string_of_bool distance_decrease_check)) no_pos in
    if not distance_decrease_check then
      (false, "The measure doesn't decrease!")
    else
      (true, "Transition checking succeed!")
  )

let check_decreasing_seqvar_transition (assumption : CP.formula)
                                       (seqvar_src: CP.sequence_info)
                                       (seqvar_dst: CP.sequence_info)
                                       : (bool * string) =
  let pr_in1 = Cprinter.string_of_pure_formula in
  let pr_in2 (seqinfo: CP.sequence_info) = Cprinter.string_of_p_formula (CP.SeqVar seqinfo) in
  let pr_in3 (seqinfo: CP.sequence_info) = Cprinter.string_of_p_formula (CP.SeqVar seqinfo) in
  let pr_out = string_of_bool in
  Debug.no_3 "check_decreasing_seqvar_transition"
            pr_in1 pr_in2 pr_in3 pr_out
            (fun in1 in2 in3 -> check_decreasing_seqvar_transition_x in1 in2 in3)
            assumption seqvar_src seqvar_dst 

let check_decreasing_seqvar_terminability_x (assumption: CP.formula)
                                            (element: CP.exp)
                                            (limit: CP.exp)
                                            (loop_condition: CP.formula)
                                            : bool =
  let term_constraint = (
    match limit with
    | CP.SConst (Pos_infinity, _) ->
        let _ = report_error no_pos "check_decreasing_seqvar_terminability_x: limit can't be Pos_infinity" in
        raise (Exn_SeqVar "SeqVar invalid")
    | CP.SConst (Neg_infinity, _) ->
        let vars = CP.afv element in
        let bound_var = CP.fresh_new_spec_var Float in
        let bound_exp = CP.mkPure (CP.mkLt element (CP.mkVar bound_var no_pos) no_pos) in
        let termcond = CP.mkNot_s loop_condition in
        let f = CP.mkOr (CP.mkNot_s bound_exp) termcond None no_pos in
        let fdomain = CP.collect_formula_domain f in
        let fForAll = CP.mkImply fdomain f no_pos in
        let term_formula = CP.mkForall vars fForAll None no_pos in
        CP.mkExists [bound_var] term_formula None no_pos
    | _ ->
        let vars = CP.afv element in
        let epsilon = CP.fresh_new_spec_var Float in
        let constraint1 = CP.mkPure (CP.mkGt element limit no_pos) in
        let constraint2 = CP.mkPure (CP.mkLt element (CP.mkAdd limit (CP.mkVar epsilon no_pos) no_pos) no_pos) in
        let termcond = CP.mkNot_s loop_condition in
        let f = CP.mkOr (CP.mkNot_s (CP.mkAnd constraint1 constraint2 no_pos)) termcond None no_pos in
        let fdomain = CP.collect_formula_domain f in
        let fForAll = CP.mkImply fdomain f no_pos in
        let term_formula = CP.mkForall vars fForAll None no_pos in
        let eps_formula = CP.mkPure (CP.mkGt (CP.mkVar epsilon no_pos) (CP.mkFConst 0.0 no_pos) no_pos) in
        CP.mkExists [epsilon] (CP.mkAnd eps_formula term_formula no_pos) None no_pos
  ) in
  let terminability_check, _, _ = TP.imply (CP.mkTrue no_pos) term_constraint "" false None in
  let _ = Debug.dinfo_pprint ("++ In function: check_decreasing_seqvar_terminability_x") no_pos in
  let _ = Debug.dinfo_pprint ("term_constraint = " ^ (Cprinter.string_of_pure_formula term_constraint))  no_pos in
  let _ = Debug.dinfo_pprint ("terminability_check = " ^ (string_of_bool terminability_check))  no_pos in
  terminability_check

let check_decreasing_seqvar_terminability (assumption: CP.formula)
                                          (element: CP.exp)
                                          (limit: CP.exp)
                                          (loop_condition: CP.formula)
                                          : bool =
  let pr_in1 = Cprinter.string_of_pure_formula in
  let pr_in2 = Cprinter.string_of_formula_exp in
  let pr_in3 = Cprinter.string_of_formula_exp in
  let pr_in4 = Cprinter.string_of_pure_formula in
  let pr_out = string_of_bool in
  Debug.no_4 "check_decreasing_seqvar_terminability"
             pr_in1 pr_in2 pr_in3 pr_in4 pr_out
             (fun in1 in2 in3 in4 -> check_decreasing_seqvar_terminability_x in1 in2 in3 in4)
             assumption element limit loop_condition

let check_decreasing_seqvar_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p (trans : term_trans option) =
  let (seqvar_src, seqvar_dst) = match trans with
                           | Some (CP.SeqVar seq1, CP.SeqVar seq2) -> seq1, seq2
                           | _ -> raise (Exn_SeqVar "SeqVar not found!") in
  let element_src = seqvar_src.CP.seq_element in
  let limit_src = seqvar_src.CP.seq_limit in
  let loopcond_src = seqvar_src.CP.seq_loopcond in
  let domain_src = seqvar_src.CP.seq_domain in
  let pos_dst = seqvar_dst.CP.seq_loc in
  let pos = post_pos # get in
  let pos = if pos == no_pos then pos_dst else pos in (* Update pos for SLEEK output *)
  let term_pos = (pos, proving_loc # get) in
  let assumption = MCP.pure_of_mix (MCP.merge_mems lhs_p xpure_lhs_h1 true) in
  let orig_ante = estate.es_formula in
  let term_measures, term_res, term_err_msg, rank_formula = (
    (* check precondition *)
    let precondition_res,detail_msg = check_decreasing_seqvar_precondition assumption domain_src loopcond_src in
    if not precondition_res then
      Some (CP.SeqVar {seqvar_src with CP.seq_ann = Fail TermErr_May}),
      (term_pos, trans, Some orig_ante, MayTerm_S (Limit_Technique_Precondition_Invalid)),
      Some (string_of_term_res (term_pos, trans, None, MayTerm_S (Limit_Technique_Precondition_Invalid)) ^ " - " ^ detail_msg),
      None
    else (
      (* check transition *)
      let trans_res, detail_msg = check_decreasing_seqvar_transition assumption seqvar_src seqvar_dst in
      if not trans_res then
        Some (CP.SeqVar {seqvar_src with CP.seq_ann = Fail TermErr_May}),
        (term_pos, trans, Some orig_ante, MayTerm_S (Limit_Technique_Transition_Invalid trans)),
        Some (string_of_term_res (term_pos, trans, None, MayTerm_S (Limit_Technique_Transition_Invalid trans)) ^ " - " ^ detail_msg),
        None
      else (
        (* check terminability *)
        let terminability_res = check_decreasing_seqvar_terminability assumption element_src limit_src loopcond_src in
        if not terminability_res then
          Some (CP.SeqVar {seqvar_src with CP.seq_ann = Fail TermErr_May}),
          (term_pos, trans, Some orig_ante, MayTerm_S (Limit_Technique_Loop_Condition_Always_Valid trans)),
          Some (string_of_term_res (term_pos, trans, None, MayTerm_S (Limit_Technique_Loop_Condition_Always_Valid trans))),
          None
        else
          Some (CP.SeqVar seqvar_src), 
          (term_pos, trans, Some orig_ante, Term_S (Limit_Technique_Prove_Termination_Succeed trans)),
          None, 
          None
      )
    )
  ) in
  let term_err = match estate.es_term_err with
    | None -> term_err_msg
    | Some _ -> estate.es_term_err 
  in
  let n_estate = { estate with
    es_var_measures = term_measures;
    (* es_var_stack = term_stack; *)
    es_term_err = term_err
  } in
  add_term_res_stk term_res;
  (n_estate, lhs_p, rhs_p, rank_formula)

let check_decreasing_seqvar estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p (trans : term_trans option) =
  let pr = !print_mix_formula in
  let pr1 = !CP.print_formula in
  let pr2 = !print_entail_state in
  let pr3  trans =
    match trans with
    | None -> "None_term_trans"
    | Some (term_s, term_d) -> "term_trans_source = " ^ (Cprinter.string_of_p_formula term_s) 
                               ^ " && term_trans_dest = " ^ (Cprinter.string_of_p_formula term_d) in
  Debug.no_4 "check_decreasing_seqvar" pr2 
    (add_str "lhs_p" pr)
    (add_str "rhs_p" pr) 
    (add_str "term_trans" pr3)
    (fun (es, lhs, rhs, rank_fml) ->
       pr_quad pr2 (add_str "lhs" pr)
       (add_str "rhs" pr)
       (add_str "rank_fml" (pr_option pr1))
       (es, lhs, rhs, rank_fml))
    (fun _ _ _ _ -> check_decreasing_seqvar_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p trans) 
    estate lhs_p rhs_p trans

let check_general_seqvar_init_and_term_constraint_x (assumption: CP.formula) (loopcond: CP.formula) : bool =
  (* initial termination constraint: (assumption -> loopcond) is SAT *)
  let loopcond_check, _, _ = TP.imply assumption loopcond "" false None in
  let _ = Debug.dinfo_pprint ("In function: check_general_seqvar_init_and_term_constraint_x") no_pos in
  let _ = Debug.dinfo_pprint ("assumption = " ^ (Cprinter.string_of_pure_formula assumption)) no_pos in
  let _ = Debug.dinfo_pprint ("loopcond = " ^ (Cprinter.string_of_pure_formula loopcond)) no_pos in
  let _ = Debug.dinfo_pprint ("loopcond_check = " ^ (string_of_bool loopcond_check)) no_pos in
  loopcond_check

let check_general_seqvar_init_and_term_constraint (assumption: CP.formula) (loopcond: CP.formula) : bool =
  let pr_in = Cprinter.string_of_pure_formula in
  let pr_out = string_of_bool in
  Debug.no_2 "check_general_seqvar_init_and_term_constraint"
             pr_in pr_in pr_out
             (fun p1 p2 -> check_general_seqvar_init_and_term_constraint_x p1 p2)
             assumption loopcond

let check_general_seqvar_transition_x (assumption : CP.formula)
                                      (seqvar_src: CP.sequence_info)
                                      (seqvar_dst: CP.sequence_info)
                                      : (bool * string) =
  let element_src = seqvar_src.CP.seq_element in
  let domain_src = seqvar_src.CP.seq_domain in
  let limit_src = seqvar_src.CP.seq_limit in 
  let element_dst = seqvar_dst.CP.seq_element in
  let domain_dst = seqvar_dst.CP.seq_domain in
  let limit_dst = seqvar_dst.CP.seq_limit in 
  (* possible limit constraint: update_function & (element_src = limit_src) => element_dst = limit_dst *)
  let update_function = collect_update_function assumption in
  let fixpoint_check = (
    match limit_src, limit_dst with
    | CP.SConst _, _
    | _, CP.SConst _ ->
        (* TRUNG TODO: consider the case when infinity appears in one or both two side of entailment *)
        let _ = report_error no_pos "check_general_seqvar_transition: the infinity is handled only in decreasing sequences" in
        raise (Exn_SeqVar "SeqVar invalid")
    | _, _ ->
        let fixpoint_src = CP.mkAnd update_function (CP.mkPure (CP.mkEq element_src limit_src no_pos)) no_pos in
        let fixpoint_dst = CP.mkPure (CP.mkEq element_dst limit_dst no_pos) in
        let fixpoint_check, _, _ = TP.imply fixpoint_src fixpoint_dst "" false None in
        let _ = Debug.dinfo_pprint ("++ In function: check_general_seqvar_transition_x") no_pos in
        let _ = Debug.dinfo_pprint ("fixpoint_src = " ^ (Cprinter.string_of_pure_formula fixpoint_src)) no_pos in
        let _ = Debug.dinfo_pprint ("fixpoint_dst = " ^ (Cprinter.string_of_pure_formula fixpoint_dst)) no_pos in
        let _ = Debug.dinfo_pprint ("fixpoint_check = " ^ (string_of_bool fixpoint_check)) no_pos in
        fixpoint_check
  ) in
  if not fixpoint_check then
    (false, "Fixpoint checking fail")
  else (
    (* domain check*)
    let domain_src_cons = CP.mkAnd update_function domain_src no_pos in
    let domain_entail_check, _, _ = TP.imply domain_src_cons domain_dst "" false None in 
    let _ = Debug.dinfo_pprint ("++ In function: check_general_seqvar_transition_x") no_pos in
    let _ = Debug.dinfo_pprint ("update_function = " ^ (Cprinter.string_of_pure_formula update_function)) no_pos in
    let _ = Debug.dinfo_pprint ("domain_src = " ^ (Cprinter.string_of_pure_formula domain_src)) no_pos in
    let _ = Debug.dinfo_pprint ("domain_dst = " ^ (Cprinter.string_of_pure_formula domain_dst)) no_pos in
    let _ = Debug.dinfo_pprint ("domain_entail_check = " ^ (string_of_bool domain_entail_check)) no_pos in
    if not domain_entail_check then
      (false, "Domain-entail checking fail")
    else (
      (* distance check *)
      let distance_constraint = (
        match limit_src, limit_dst with
        | CP.SConst _, _
        | _, CP.SConst _ ->
            (* TRUNG TODO: consider the case when infinity appears in one or both two side of entailment *)
            let _ = report_error no_pos "check_general_seqvar_transition: the infinity is handled only in decreasing sequences" in
            raise (Exn_SeqVar "SeqVar invalid")
        | _, _ ->
            (* decreasing distance constraint  |element_src - limit_src| > |element_dst - limit_dst| *)
            let dist_src = CP.mkAbs (CP.mkSubtract element_src limit_src no_pos) no_pos in
            let dist_dst = CP.mkAbs (CP.mkSubtract element_dst limit_dst no_pos) no_pos in
            CP.mkPure (CP.mkGt dist_src dist_dst no_pos)
      ) in
      let domain_constraint = CP.mkAnd (CP.mkAnd domain_src domain_dst no_pos) update_function no_pos in
      let distance_decrease_check, _, _ = TP.imply domain_constraint distance_constraint "" false None in
      let _ = Debug.dinfo_pprint ("++ In function: check_general_seqvar_transition_x") no_pos in
      let _ = Debug.dinfo_pprint ("domain_constraint = " ^ (Cprinter.string_of_pure_formula domain_constraint)) no_pos in
      let _ = Debug.dinfo_pprint ("distance_constraint = " ^ (Cprinter.string_of_pure_formula distance_constraint)) no_pos in
      let _ = Debug.dinfo_pprint ("distance_decrease_check = " ^ (string_of_bool distance_decrease_check)) no_pos in
      if not distance_decrease_check then
        (false, "Decreasing-distance checking fail")
      else (
        (* check the coverage of domain over the initial constraint *)
        let domain_cover_check, _, _ = TP.imply assumption domain_constraint "" false None in
        let _ = Debug.dinfo_pprint ("++ In function: check_general_seqvar_transition_x") no_pos in
        let _ = Debug.dinfo_pprint ("assumption = " ^ (Cprinter.string_of_pure_formula assumption)) no_pos in
        let _ = Debug.dinfo_pprint ("domain_constraint = " ^ (Cprinter.string_of_pure_formula domain_constraint)) no_pos in
        let _ = Debug.dinfo_pprint ("domain_cover_check = " ^ (string_of_bool domain_cover_check)) no_pos in
        if not domain_cover_check then
          (false, "Domain-cover checking fail")
        else (
          (* verify the limit: the smallest distance to the limit is 0 *)
          let limit_src_constraint = (
            let vars_src = CP.afv element_src in
            let new_v = CP.fresh_new_spec_var Float in
            let newbound = CP.mkVar new_v no_pos in
            let cons1 = CP.mkPure (CP.mkGt newbound (CP.mkFConst 0.0 no_pos) no_pos) in
            let dist_src = CP.mkAbs (CP.mkSubtract element_src limit_src no_pos) no_pos in
            let cons2 = CP.mkPure (CP.mkGt dist_src newbound no_pos) in
            let f = CP.mkImply domain_src (CP.mkAnd cons1 cons2 no_pos)no_pos in
            let fdomain = CP.collect_formula_domain f in
            let fForAll = CP.mkImply fdomain f no_pos in
            CP.mkNot_s (CP.mkExists [new_v] (CP.mkForall vars_src fForAll None no_pos) None no_pos)
          ) in
          let limit_src_check, _, _ = TP.imply domain_src limit_src_constraint "" false None in
          let _ = Debug.dinfo_pprint ("++ In function: check_general_seqvar_transition_x") no_pos in
          let _ = Debug.dinfo_pprint ("domain_src = " ^ (Cprinter.string_of_pure_formula domain_src)) no_pos in
          let _ = Debug.dinfo_pprint ("limit_src_constraint = " ^ (Cprinter.string_of_pure_formula limit_src_constraint))  no_pos in
          let _ = Debug.dinfo_pprint ("limit_src_check = " ^ (string_of_bool limit_src_check)) no_pos in
          if not limit_src_check then
            (false, "Limit checking fail (distance to fixpoint isn't the biggest lowerbound)")
          else (
            let limit_dst_constraint = (
              let vars_dst = CP.afv element_dst in
              let new_v = CP.fresh_new_spec_var Float in
              let newbound = CP.mkVar new_v no_pos in
              let cons1 = CP.mkPure (CP.mkGt newbound (CP.mkFConst 0.0 no_pos) no_pos) in
              let dist_dst = CP.mkAbs (CP.mkSubtract element_dst limit_dst no_pos) no_pos in
              let cons2 = CP.mkPure (CP.mkGt dist_dst newbound no_pos) in
              let f = CP.mkImply domain_dst (CP.mkAnd cons1 cons2 no_pos)no_pos in
              let fdomain = CP.collect_formula_domain f in
              let fForAll = CP.mkImply fdomain f no_pos in
              CP.mkNot_s (CP.mkExists [new_v] (CP.mkForall vars_dst fForAll None no_pos) None no_pos)
            ) in
            let limit_dst_check, _, _ = TP.imply domain_dst limit_dst_constraint "" false None in
            let _ = Debug.dinfo_pprint ("++ In function: check_general_seqvar_transition_x") no_pos in
            let _ = Debug.dinfo_pprint ("domain_dst = " ^ (Cprinter.string_of_pure_formula domain_dst)) no_pos in
            let _ = Debug.dinfo_pprint ("limit_dst_constraint = " ^ (Cprinter.string_of_pure_formula limit_dst_constraint))  no_pos in
            let _ = Debug.dinfo_pprint ("limit_dst_check = " ^ (string_of_bool limit_dst_check)) no_pos in
            if not limit_dst_check then
              (false, "Limit checking fail (distance to fixpoint isn't the biggest lowerbound)")
            else
              (true, "Transition checking succeed")          )
        )
      )
    )
  )

let check_general_seqvar_transition (assumption : CP.formula)
                                    (seqvar_src: CP.sequence_info)
                                    (seqvar_dst: CP.sequence_info)
                                    : (bool * string) =
  let pr_in1 = Cprinter.string_of_pure_formula in
  let pr_in2 (seqinfo: CP.sequence_info) = Cprinter.string_of_p_formula (CP.SeqVar seqinfo) in
  let pr_in3 (seqinfo: CP.sequence_info) = Cprinter.string_of_p_formula (CP.SeqVar seqinfo) in
  let pr_out = string_of_bool in
  Debug.no_3 "check_general_seqvar_transition"
            pr_in1 pr_in2 pr_in3 pr_out
            (fun in1 in2 in3 -> check_general_seqvar_transition_x in1 in2 in3)
            assumption seqvar_src seqvar_dst 

let check_general_seqvar_limit_and_term_constraint_x (assumption: CP.formula)
                                                     (element: CP.exp)
                                                     (limit: CP.exp)
                                                     (loopcond: CP.p_formula list)
                                                     : bool = 
  let vars = CP.afv element in
  let epsilon = CP.fresh_new_spec_var Float in
  let constraint1 = CP.mkPure (CP.mkGt element limit no_pos) in
  let constraint2 = CP.mkPure (CP.mkLt element (CP.mkAdd limit (CP.mkVar epsilon no_pos) no_pos) no_pos) in
  let lst = List.map CP.mkPure loopcond in
  let tc = List.fold_left (fun x y -> CP.mkOr x y None no_pos) (CP.mkFalse no_pos) lst in 
  let f = CP.mkOr (CP.mkNot_s (CP.mkAnd constraint1 constraint2 no_pos)) tc None no_pos in
  let fdomain = CP.collect_formula_domain f in
  let fForAll = CP.mkImply fdomain f no_pos in
  let term_formula = CP.mkForall vars fForAll None no_pos in
  let eps_formula = CP.mkPure (CP.mkGt (CP.mkVar epsilon no_pos) (CP.mkFConst 0.0 no_pos) no_pos) in
  let term_constraint = CP.mkExists [epsilon] (CP.mkAnd eps_formula term_formula no_pos) None no_pos in
  let loopcond_check, _, _ = TP.imply assumption term_constraint "" false None in
  let _ = Debug.dinfo_pprint ("++ In function: check_general_seqvar_limit_and_term_constraint_x") no_pos in
  let _ = Debug.dinfo_pprint ("assumption = " ^ (Cprinter.string_of_pure_formula assumption)) no_pos in
  let _ = Debug.dinfo_pprint ("term_constraint = " ^ (Cprinter.string_of_pure_formula term_constraint)) no_pos in
  let _ = Debug.dinfo_pprint ("loopcond_check = " ^ (string_of_bool loopcond_check)) no_pos in
  loopcond_check

let check_general_seqvar_limit_and_term_constraint (assumption: CP.formula)
                                                   (element: CP.exp)
                                                   (limit: CP.exp)
                                                   (loopcond: CP.p_formula list)
                                                   : bool =
  let pr_in1 = Cprinter.string_of_pure_formula in
  let pr_in2 = Cprinter.string_of_formula_exp in
  let pr_in3 = Cprinter.string_of_formula_exp in
  let pr_in4 = Cprinter.string_of_pure_formula in
  let pr_out = string_of_bool in
  Debug.no_4 "check_general_seqvar_limit_and_term_constraint"
             pr_in1 pr_in2 pr_in3 pr_in4 pr_out
             (fun in1 in2 in3 in4 -> check_general_seqvar_limit_and_term_constraint_x in1 in2 in3 in4)
             assumption element limit loopcond

let check_general_seqvar_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p (trans : term_trans option) =
  let (seqvar_src, seqvar_dst) = match trans with
                           | Some (CP.SeqVar seq1, CP.SeqVar seq2) -> seq1, seq2
                           | _ -> raise (Exn_SeqVar "SeqVar not found!") in
  let loopcond_src = seqvar_src.CP.seq_loopcond in
  let pos_dst = seqvar_dst.CP.seq_loc in
  let pos = post_pos # get in
  let pos = if pos == no_pos then pos_dst else pos in (* Update pos for SLEEK output *)
  let term_pos = (pos, proving_loc # get) in
  let assumption = MCP.pure_of_mix (MCP.merge_mems lhs_p xpure_lhs_h1 true) in
  let orig_ante = estate.es_formula in
  let term_measures, term_res, term_err_msg, rank_formula = (
    (* check transition *)
    let trans_res, detail_msg = check_general_seqvar_transition assumption seqvar_src seqvar_dst in
    if not trans_res then
      Some (CP.SeqVar {seqvar_src with CP.seq_ann = Fail TermErr_May}),
      (term_pos, trans, Some orig_ante, MayTerm_S (Limit_Technique_Transition_Invalid trans)),
      Some (string_of_term_res (term_pos, trans, None, MayTerm_S (Limit_Technique_Transition_Invalid trans)) ^ " - " ^ detail_msg),
      None
    else (
      (* check termination based on initial constraint *)
      let init_res = check_general_seqvar_init_and_term_constraint assumption loopcond_src in
      if init_res then
        Some (CP.SeqVar seqvar_src), 
        (term_pos, trans, Some orig_ante, Term_S Limit_Technique_Precondition_Invalid),
        None,
        None
      else (
        (* check term cosntraint *)
        (* let limit_res = check_general_seqvar_limit_and_term_constraint assumption element_src limit_src loopcond_src in *)
        (* if not limit_res then                                                                                                *)
        (*   Some (CP.SeqVar {seqvar_src with CP.seq_ann = Fail TermErr_May}),                                                  *)
        (*   (term_pos, trans, Some orig_ante, MayTerm_S (Limit_Technique_Loop_Condition_Always_Valid trans)),                     *)
        (*   Some (string_of_term_res (term_pos, trans, None, MayTerm_S (Limit_Technique_Loop_Condition_Always_Valid trans))),     *)
        (*   None                                                                                                               *)
        (* else                                                                                                                 *)
          Some (CP.SeqVar seqvar_src), 
          (term_pos, trans, Some orig_ante, Term_S (Limit_Technique_Prove_Termination_Succeed trans)),
          None, 
          None
      )
    )
  ) in
  let term_err = match estate.es_term_err with
    | None -> term_err_msg
    | Some _ -> estate.es_term_err 
  in
  let n_estate = { estate with
    es_var_measures = term_measures;
    (* es_var_stack = term_stack; *)
    es_term_err = term_err
  } in
  add_term_res_stk term_res;
  (n_estate, lhs_p, rhs_p, rank_formula)

let check_general_seqvar estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p trans =
  let pr = !print_mix_formula in
  let pr1 = !CP.print_formula in
  let pr2 = !print_entail_state in
  let pr3  trans =
    match trans with
    | None -> "None_term_trans"
    | Some (term_s, term_d) -> "term_trans_source = " ^ (Cprinter.string_of_p_formula term_s) 
                               ^ " && term_trans_dest = " ^ (Cprinter.string_of_p_formula term_d) in
  Debug.no_4 "check_general_seqvar" pr2
    (add_str "lhs_p" pr)
    (add_str "rhs_p" pr) 
    (add_str "term_trans" pr3)
    (fun (es, lhs, rhs, rank_fml) ->
       pr_quad pr2 (add_str "lhs" pr)
       (add_str "rhs" pr)
       (add_str "rank_fml" (pr_option pr1))
       (es, lhs, rhs, rank_fml))
    (fun _ _ _ _ -> check_general_seqvar_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p trans) 
    estate lhs_p rhs_p trans

(* Termination: check sequence var *)  
let check_seqvar_measures_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p (trans : term_trans option)  =
  (* (estate, lhs_p, rhs_p, None) *)
  let ans = norm_seqvar_measures_trans trans in
  match ans with
  | None ->
      (* no need to check termination by seqvar transition*) 
      (estate, lhs_p, rhs_p, None)
  | Some (seqvar_src, seqvar_dst) -> (
      if (seqvar_src.CP.seq_decrease) then 
        check_decreasing_seqvar estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p trans
      else
        check_general_seqvar estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p trans
    )

let check_seqvar_measures estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p (trans : term_trans option) =
  let pr = !print_mix_formula in
  let pr1 = !CP.print_formula in
  let pr2 = !print_entail_state in
  let pr3  trans =
    match trans with
    | None -> "None_term_trans"
    | Some (term_s, term_d) -> "term_trans_source = " ^ (Cprinter.string_of_p_formula term_s) 
                               ^ " && term_trans_dest = " ^ (Cprinter.string_of_p_formula term_d) in
  Debug.no_4 "check_seqvar_measures" pr2 
      (add_str "lhs_p" pr)
      (add_str "rhs_p" pr) 
      (add_str "term_trans" pr3)
    (fun (es, lhs, rhs, rank_fml) -> 
        pr_quad pr2 (add_str "lhs" pr) 
            (add_str "rhs" pr) 
            (add_str "rank_fml" (pr_option pr1)) 
            (es, lhs, rhs, rank_fml))  
      (fun _ _ _ _ -> check_seqvar_measures_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p trans) 
        estate lhs_p rhs_p trans

(* To handle SeqVar formula *)
(* Remember to remove SeqVar in RHS *)
let check_seqvar_rhs_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos =
  try (
    let _ = DD.trace_hprint (add_str "es" !print_entail_state) estate pos in
    let conseq = MCP.pure_of_mix rhs_p in
    let seqvar_dst = find_seqvar_formula conseq in
    let seqinfo_dst = match seqvar_dst with
                  | CP.SeqVar seqinfo -> seqinfo
                  | _ -> raise (Exn_SeqVar "SeqVar not found!") in
    let ann_dst = seqinfo_dst.CP.seq_ann in
    let pos_dst = seqinfo_dst.CP.seq_loc in
    let seqvar_src = find_seqvar_es estate in
    let seqinfo_src = match seqvar_src with
                  | CP.SeqVar seqinfo -> seqinfo
                  | _ -> raise (Exn_SeqVar "SeqVar not found!") in
    let _ = Debug.dinfo_pprint ("++ In function check_seqvar_rhs_x") no_pos in
    let _ = Debug.dinfo_pprint ("seqvar_src = " ^ (Cprinter.string_of_p_formula seqvar_src)) no_pos in 
    let _ = Debug.dinfo_pprint ("seqvar_dst = " ^ (Cprinter.string_of_p_formula seqvar_dst)) no_pos in 
    let ann_src = seqinfo_src.CP.seq_ann in
    let trans = (seqvar_src, seqvar_dst) in
    let trans_opt = Some trans in
    let _, rhs_p = strip_termvar_mix_formula rhs_p in
    let rhs_p = MCP.mix_of_pure rhs_p in
    let p_pos = post_pos # get in
    let p_pos = if p_pos == no_pos then pos_dst else p_pos in (* Update pos for SLEEK output *)
    let term_pos = (p_pos, proving_loc # get) in
    match (ann_src, ann_dst) with
    | (Term, Term)
    | (Fail TermErr_May, Term) ->
        (* Check wellfoundedness of the transition *)
        check_seqvar_measures estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p trans_opt
    | (Term, _)
    | (Fail TermErr_May, _) ->
        let term_res = (term_pos, trans_opt, Some estate.es_formula,
          TermErr (Invalid_Status_Trans trans)) in
        add_term_res_stk term_res;
        add_term_err_stk (string_of_term_res term_res);
        let term_measures = (
          match ann_dst with
          | Loop
          | Fail TermErr_Must ->
              Some (CP.SeqVar {seqinfo_src with CP.seq_ann = Fail TermErr_Must})
          | MayLoop
          | Fail TermErr_May ->
              Some (CP.SeqVar {seqinfo_src with CP.seq_ann = Fail TermErr_May})
          | Term ->
              let _ = report_error no_pos "[term.ml] unexpected Term in check_seqvar_rhs" in
              raise (Exn_SeqVar "SeqVar invalid")
        ) in
        let term_err = match estate.es_term_err with
          | None ->  Some (string_of_term_res term_res)
          | Some _ -> estate.es_term_err
        in
        let n_estate = {estate with
          es_var_measures = term_measures;
          (* es_var_stack = (string_of_term_res term_res)::estate.es_var_stack; *)
          es_term_err = term_err;
        } in
        (n_estate, lhs_p, rhs_p, None)
    | (Loop, _) ->
        let term_measures = Some (CP.SeqVar {seqinfo_src with CP.seq_ann = Loop}) in
        let n_estate = {estate with es_var_measures = term_measures} in
        (n_estate, lhs_p, rhs_p, None)
    | (MayLoop, _) ->
        let term_measures = Some (CP.SeqVar {seqinfo_src with CP.seq_ann = MayLoop}) in
        let n_estate = {estate with es_var_measures = term_measures} in
        (n_estate, lhs_p, rhs_p, None)
    | (Fail TermErr_Must, _) ->
        let n_estate = {estate with
          es_var_measures = Some (CP.SeqVar {seqinfo_src with CP.seq_ann = Fail TermErr_Must})
        } in
        (n_estate, lhs_p, rhs_p, None)
  )
  with e -> (
    let new_measures = match estate.es_var_measures with
      | Some (CP.SeqVar seqinfo) -> Some (CP.SeqVar {seqinfo with CP.seq_ann = Fail TermErr_May})
      | _ -> failwith "!!! Error: cannot find SeqVar in termination measurement" in
    let n_estate = {estate with
      es_var_measures = new_measures;
      es_term_err = Some ("!!!Exception while checking termination 2: " ^ (Printexc.to_string e));
    } in
    (n_estate, lhs_p, rhs_p, None)
  )

let check_seqvar_rhs estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos =
  let pr = !print_mix_formula in
  let pr2 = !print_entail_state in
   Debug.no_3 "check_seqvar_rhs" pr2 pr pr
    (fun (es, lhs, rhs, _) -> pr_triple pr2 pr pr (es, lhs, rhs))  
    (fun _ _ _ -> check_seqvar_rhs_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos) estate lhs_p rhs_p

(* To handle Termination Var formula *)
(* Remember to remove SeqVar in RHS *)
let check_term_rhs_x_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos =
  try (
    let conseq = MCP.pure_of_mix rhs_p in
    let termvar_conseq = find_termvar_formula conseq in
    let termvar_es = estate.es_var_measures in
    let _ = Debug.dinfo_pprint "++ In function: check_term_rhs_x_x" no_pos in
    match (termvar_es, termvar_conseq) with
    | Some CP.LexVar _, CP.LexVar _ ->
        let _ = Debug.dinfo_pprint "--> go to check_lexvar_rhs" no_pos in
        check_lexvar_rhs estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos
    | Some CP.SeqVar _, CP.SeqVar _ ->
        let _ = Debug.dinfo_pprint "--> go to check_seqvar_rhs" no_pos in
        check_seqvar_rhs estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos
    | _ ->
        let _ = Debug.dinfo_pprint "--> exception!! No check termination" no_pos in
        let s = match termvar_es with None -> "None" | Some v -> Cprinter.string_of_p_formula v in
        let _ = Debug.dinfo_pprint ("termvar_es = " ^ s) no_pos in
        let _ = Debug.dinfo_pprint ("termvar_conseq = " ^ (Cprinter.string_of_p_formula termvar_conseq)) no_pos in
        raise (Exn_TermVar "Invalid TermVar Transition!")
  ) 
  with e -> (
    match e with
    | Exn_TermVar s ->
        let _ = Debug.dinfo_pprint ("--> Exception: Exn_TermVar - " ^ s)  no_pos in
        (estate, lhs_p, rhs_p, None)
    | _ ->
        let _ = Debug.dinfo_pprint "--> exception!! No check termination" no_pos in
        failwith ("!!! Exception while proving termintion: " ^ (Printexc.to_string e))
    (* match e with                                                                                       *)
    (* | (Exn_SeqVar "SeqVar invalid") -> (                                                               *)
    (*     let new_measures = match estate.es_var_measures with                                           *)
    (*       | Some (CP.SeqVar seqinfo) -> Some (CP.SeqVar {seqinfo with CP.seq_ann = Fail TermErr_May})  *)
    (*       | _ -> failwith "!!! Error: cannot find SeqVar in termination measurement" in                *)
    (*     let n_estate = {estate with                                                                    *)
    (*       es_var_measures = new_measures;                                                              *)
    (*       es_term_err = Some ("!!!Exception while checking termination 4: " ^ (Printexc.to_string e)); *)
    (*     } in                                                                                           *)
    (*     (n_estate, lhs_p, rhs_p, None)                                                                 *)
    (*   )                                                                                                *)
    (* | _ -> (estate, lhs_p, rhs_p, None)                                                                *)
  )

(* To handle Termination var formula *)
(* Remember to remove SeqVar in RHS *)
let check_term_rhs_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos =
  let _ = Debug.dinfo_pprint "++ In function: check_term_rhs_x" no_pos in
  if (!Globals.dis_term_chk) or (estate.es_term_err != None) then
    let _ = Debug.dinfo_pprint "--> no check termintion" no_pos in
    let _, rhs_p = strip_termvar_mix_formula rhs_p in
    let rhs_p = MCP.mix_of_pure rhs_p in
    (estate, lhs_p, rhs_p, None)
  else
    let _ = Debug.dinfo_pprint "--> start checking termintion" no_pos in
    check_term_rhs_x_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos 

let check_term_rhs estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos =
  let pr = !print_mix_formula in
  let pr2 = !print_entail_state in
   Debug.no_3 "check_term_rhs" pr2 pr pr
    (fun (es, lhs, rhs, _) -> pr_triple pr2 pr pr (es, lhs, rhs))  
      (fun _ _ _ -> check_term_rhs_x estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos) estate lhs_p rhs_p

(** strip the termination var from lhs of a context and move it to es_var_measures *)
let strip_termvar_lhs_x (ctx: context) : context =
  let es_strip_termvar_lhs (es: entail_state) : context =
    let _, pure_f, _, _, _ = split_components es.es_formula in
    let (termvars, other_p) = strip_termvar_mix_formula pure_f in
    (* Using transform_formula to update the pure part of es_f *)
    let f_e_f _ = None in
    let f_f _ = None in
    let f_h_f e = Some e in
    let f_m mp = Some (MCP.memoise_add_pure_N_m (MCP.mkMTrue_no_mix no_pos) other_p) in
    let f_a _ = None in
    let f_p_f pf = Some other_p in
    let f_b _ = None in
    let f_e _ = None in
    match termvars with
    | [] -> Ctx es
    | termvar::[] -> 
        Ctx { es with 
          es_formula = transform_formula (f_e_f, f_f, f_h_f, (f_m, f_a, f_p_f, f_b, f_e)) es.es_formula;
          es_var_measures = Some (termvar); 
        }
    | _ -> report_error no_pos "[term.ml][strip_termvar_lhs]: More than one TermVar to be stripped."
  in transform_context es_strip_termvar_lhs ctx

let strip_termvar_lhs (ctx: context) : context =
  let pr = Cprinter.string_of_context in
  Debug.no_1 "strip_termvar_lhs" pr pr strip_termvar_lhs_x ctx

(* End of Termination Var handling *) 


(* HIP: Collecting information for termination proof *)
(* let report_term_error (ctx: formula) (reason: term_reason) pos : term_res = *)
(*   let err = (pos, None, Some ctx, TermErr reason) in *)
(*   add_term_res_stk err; *)
(*   err *)

let add_unreachable_res (ctx: list_failesc_context) pos : term_res =
  let _ = 
    begin
      DD.devel_zprint (lazy (">>>>>> [term.ml][add_unreachable_res] <<<<<<")) pos;
      DD.devel_hprint (add_str "Context" Cprinter.string_of_list_failesc_context) ctx pos
    end
  in
  let term_pos = (post_pos # get, proving_loc # get) in
  let succ_ctx = succ_context_of_list_failesc_context ctx in
  let orig_ante_l = List.concat (List.map collect_orig_ante succ_ctx) in
  let orig_ante = formula_of_disjuncts orig_ante_l in
  let term_res = (term_pos, None, Some orig_ante, Unreachable) in
  add_term_res_stk term_res;
  term_res

(*****************************************)
(* Phase Transition Inference            *)
(*****************************************)
(* Store the inferred phase constraints *)
(* TODO: These constraints should be normalized
 * and filtered to keep only constraints 
 * related to LexVar before adding them to stack *)
let add_phase_constr (lp: CP.formula list) =
  phase_constr_stk # push_list lp

(* Build the graph for phase numbering based on
 * inferred phase constraints
 * p2>p1 -> p2 --> p1
 * p2>=p1 -> {p2,p1} 
 * [x>y, y>=z] --> [[x], [y,z]] *)
let rec phase_constr_of_formula_list (fl: CP.formula list) : phase_constr list =
  let fl = List.concat (List.map CP.split_conjunctions fl) in
  List.fold_left (fun a f -> 
    let c = phase_constr_of_formula f in 
    match c with
    | Some c -> c::a
    | None -> a) [] fl
  
and phase_constr_of_formula (f: CP.formula) : phase_constr option =
  match f with
  | CP.BForm (bf, _) -> phase_constr_of_b_formula bf
  | _ -> None 

and phase_constr_of_b_formula (bf: CP.b_formula) : phase_constr option =
  let (pf, _) = bf in
  match pf with
    | CP.Eq (e1, e2, _) ->
        let v1 = var_of_exp e1 in
        let v2 = var_of_exp e2 in
        (match (v1, v2) with
         | Some v1, Some v2 -> Some (P_Gte (v1, v2))
         | _ -> None)
    | CP.Gt (e1, e2, _) ->
        let v1 = var_of_exp e1 in
        let v2 = var_of_exp e2 in
        (match (v1, v2) with
         | Some v1, Some v2 -> Some (P_Gt (v1, v2))
         | _ -> None)
    | CP.Gte (e1, e2, _) ->
        let v1 = var_of_exp e1 in
        let v2 = var_of_exp e2 in
        (match (v1, v2) with
         | Some v1, Some v2 -> Some (P_Gte (v1, v2))
         | _ -> None)
    | CP.Lt (e1, e2, _) ->
        let v1 = var_of_exp e1 in
        let v2 = var_of_exp e2 in
        (match (v1, v2) with
         | Some v1, Some v2 -> Some (P_Gt (v2, v1))
         | _ -> None)
    | CP.Lte (e1, e2, _) ->
        let v1 = var_of_exp e1 in
        let v2 = var_of_exp e2 in
        (match (v1, v2) with
         | Some v1, Some v2 -> Some (P_Gte (v2, v1))
         | _ -> None)
    | _ -> None

and var_of_exp (exp: CP.exp) : CP.spec_var option =
  match exp with
  | CP.Var (sv, _) -> Some sv
  | _ -> None

let fv_of_phase_constr (c: phase_constr) =
  match c with
  | P_Gte (v1, v2) -> [v1; v2]
  | P_Gt (v1, v2) -> [v1; v2]

(* Old phase inference mechanism - To be removed *)
(*
module PComp = 
struct
  type t = CP.spec_var list
  let compare = 
    fun l1 l2 -> 
      if (Gen.BList.list_setequal_eq CP.eq_spec_var l1 l2) then 0 
      else 
        let pr = pr_list !CP.print_sv in
        String.compare (pr l1) (pr l2)
  let hash = Hashtbl.hash
  let equal = Gen.BList.list_setequal_eq CP.eq_spec_var
end

module PG = Graph.Persistent.Digraph.Concrete(PComp)
module PGO = Graph.Oper.P(PG)
module PGN = Graph.Oper.Neighbourhood(PG)
module PGC = Graph.Components.Make(PG)
module PGP = Graph.Path.Check(PG)
module PGT = Graph.Traverse.Dfs(PG)

(* Group spec_vars of related 
 * P_Gte constraints together *)
let rec group_related_vars (cl: phase_constr list) : CP.spec_var list list =
  let gte_l = List.fold_left (fun a c ->
    match c with 
    | P_Gt _ -> a
    | P_Gte (v1, v2) -> [v1; v2]::a 
  ) [] cl in
  let rec partition_gte_l l =
    match l with
    | [] -> []
    | h::t ->
        let n_t = partition_gte_l t in
        let r, ur = List.partition (fun sl -> 
          Gen.BList.overlap_eq CP.eq_spec_var h sl
        ) n_t in
        let n_h = Gen.BList.remove_dups_eq CP.eq_spec_var (h @ (List.concat r)) in
        n_h::ur
  in partition_gte_l gte_l

let build_phase_constr_graph (gt_l: (CP.spec_var list * CP.spec_var list) list) =
  let g = PG.empty in
  let g = List.fold_left (fun g (l1, l2) ->
    let ng1 = PG.add_vertex g l1 in
	  let ng2 = PG.add_vertex ng1 l2 in
	  let ng3 = PG.add_edge ng2 l1 l2 in
	ng3) g gt_l in
  g

let rank_gt_phase_constr (cl: phase_constr list) =
  let eq_l = group_related_vars cl in
  (*
  let pr_v = !CP.print_sv in
  let pr_vl = pr_list pr_v in
  let _ = print_endline ("\neq_l: " ^ (pr_list pr_vl eq_l)) in
  *)
  let gt_l = List.fold_left (fun a c ->
    match c with
    | P_Gt (v1, v2) -> (v1, v2)::a
    | P_Gte _ -> a
  ) [] cl in

  (* let _ = print_endline ("\ngt_l: " ^ (pr_list (pr_pair pr_v pr_v) gt_l)) in *)
  
  let find_group v l =
    try List.find (fun e -> Gen.BList.mem_eq CP.eq_spec_var v e) l
    with _ -> [v]
  in 
  (*
  let gt_l = List.map (fun (v1, v2) -> 
    let g_v1 = find_group v1 eq_l in
    let g_v2 = find_group v2 eq_l in
    (* p2>p1 and p2>=p1 are not allowed *)
    if (Gen.BList.overlap_eq CP.eq_spec_var g_v1 g_v2) then
      raise Invalid_Phase_Constr
    else (g_v1, g_v2)
  ) gt_l in
  *)

  let gt_l = List.fold_left (fun acc (v1, v2) ->
    let g_v1 = find_group v1 eq_l in
    let g_v2 = find_group v2 eq_l in
    (* Get rid of p2>p1 and p2>=p1 *)
    if (Gen.BList.overlap_eq CP.eq_spec_var g_v1 g_v2) then acc
    else (g_v1, g_v2)::acc
  ) [] gt_l in

  (*let _ = print_endline ("\n1. gt_l: " ^ (pr_list (pr_pair pr_vl pr_vl) gt_l)) in*)

  let g = build_phase_constr_graph gt_l in

  if (PGT.has_cycle g) then (* Contradiction: p2>p1 & p1>p2 *)
    raise Invalid_Phase_Constr
  else
    let n, f_scc = PGC.scc g in
    PG.fold_vertex (fun l a -> (f_scc l, l)::a) g []

let value_of_vars (v: CP.spec_var) l : int =
  try
    let (i, _) = List.find (fun (i, vl) -> 
      Gen.BList.mem_eq CP.eq_spec_var v vl
    ) l in i
  with _ -> raise Invalid_Phase_Constr
*)

module PComp = 
struct
  type t = CP.spec_var
  let compare = fun v1 v2 -> 
    if (CP.eq_spec_var v1 v2) then 0
    else 
      let pr = !CP.print_sv in
      String.compare (pr v1) (pr v2)
  let hash = Hashtbl.hash
  let equal = CP.eq_spec_var
end

module PG = Graph.Persistent.Digraph.Concrete(PComp)
module PGO = Graph.Oper.P(PG)
module PGN = Graph.Oper.Neighbourhood(PG)
module PGC = Graph.Components.Make(PG)
module PGP = Graph.Path.Check(PG)
module PGT = Graph.Traverse.Dfs(PG)

(* Build phase constraint graph based on the 
 * list of inferred phase constraints 
 * P_Gt/P_Gte (v1, v2) -> v1 --> v2 *)
let build_phase_constr_graph (cl: phase_constr list) = 
  let g = PG.empty in
  let g = List.fold_left (fun g c ->
    let s, d = match c with
      | P_Gt (v1, v2) -> v1, v2
      | P_Gte (v1, v2) -> v1, v2
    in 
    let ng1 = PG.add_vertex g s in
    let ng2 = PG.add_vertex ng1 d in
    let ng3 = PG.add_edge ng2 s d in
    ng3
  ) g cl in
  g

(* Assign a unique integer for each scc group 
 * of phase variables *)  
let rank_phase_constr (cl: phase_constr list) =
  let g = build_phase_constr_graph cl in
  let n, f_scc = PGC.scc g in
  PG.fold_vertex (fun v a -> (v, f_scc v)::a) g []

let rank_phase_constr (cl: phase_constr list) =
  let pr = pr_list string_of_phase_constr in
  let pr2 = pr_list (pr_pair !CP.print_sv  string_of_int) in
  Debug.no_1 "rank_phase_constr" pr pr2 rank_phase_constr cl

let value_of_var (v: CP.spec_var) l : int =
  try List.assoc v l
  with _ -> raise Invalid_Phase_Constr

(* let phase_num_infer () = *)
(*   (\* Phase Numbering *\)  *)
(*   let pr_v = !CP.print_sv in *)
(*   let pr_vl = pr_list pr_v in *)
(*   let cl = phase_constr_of_formula_list (phase_constr_stk # get_stk) in *)
(*   let _ = Debug.trace_hprint (add_str "Phase Constrs" (pr_list string_of_phase_constr)) cl no_pos in *)
(*   let l =  *)
(*     try rank_gt_phase_constr cl  *)
(*     with _ ->  *)
(*       fmt_string ("Termination: Contradiction in Phase Constraints."); []  *)
(*   in *)
(*   begin *)
(*     Debug.trace_hprint (add_str "Inferred phase constraints" *)
(*       (pr_list !CP.print_formula)) (phase_constr_stk # get_stk) no_pos; *)
(*     Debug.trace_hprint (add_str "Phase Numbering" *)
(*       (pr_list (pr_pair string_of_int (pr_list !CP.print_sv))) *)
(*     ) l no_pos; *)
(*   end *)

(* let phase_num_infer () = *)
(*   let pr = fun _ -> "" in *)
(*   Debug.no_1 "phase_num_infer" pr pr phase_num_infer () *)

(* Do infer phase number per scc group *)
(* Triggered when phase constraints of 
 * all function in a scc group has been 
 * collected - The result may be empty 
 * if the graph has only one vertex 
 * + None -> exception
 * + Some [] -> all_zero
 * + Some _ *)
let phase_num_infer_one_scc (pl : CP.formula list) =
  (* Phase Numbering *) 
  (* let pr_v = !CP.print_sv in *)
  (* let pr_vl = pr_list pr_v in *)
  let cl = phase_constr_of_formula_list pl in
  let s_msg = (add_str "Phase Constrs" (pr_list string_of_phase_constr)) cl in 
  (* let _ = Debug.trace_hprint (add_str "Phase Constrs" (pr_list string_of_phase_constr)) cl no_pos in *)
  let _ = Debug.trace_pprint s_msg no_pos in
  let l = 
    try 
      (* let r = rank_gt_phase_constr cl in *)
      let r = rank_phase_constr cl in
      let _ = 
        begin
          Debug.trace_hprint (add_str "Inferred phase constraints"
            (pr_list !CP.print_formula)) (phase_constr_stk # get_stk) no_pos;
          Debug.trace_hprint (add_str "Phase Numbering"
            (* (pr_list (pr_pair string_of_int (pr_list !CP.print_sv)))) r no_pos; *)
            (pr_list (pr_pair !CP.print_sv string_of_int))) r no_pos;
        end
      in 

      if Gen.is_empty r then
        let fv = List.concat (List.map fv_of_phase_constr cl) in
        Some (r, fv)
      else Some (r, [])
    with _ -> 
      fmt_string ("\nTermination: Error in Phase Inference." ^ "\n" ^ s_msg); None 
  in
  l

let phase_num_infer_one_scc (pl: CP.formula list)  =
  let pr = fun _ -> "" in
  let pr2 = (add_str "Phase Ctr" (pr_list !CP.print_formula)) in
  Debug.no_1 "phase_num_infer_one_scc" pr2 pr phase_num_infer_one_scc pl

(* Infer the phase numbers at the end of check_prog *) 
(* Currently, this method is redundant because we do
 * aggressive phase inference per scc group *)  
let phase_num_infer_by_scc () = 
  Hashtbl.iter (fun i pl -> 
    let cl = List.concat (List.map (fun (_, l) -> l) pl) in
    Debug.trace_hprint (add_str ("scc " ^ (string_of_int i))
      (pr_list !CP.print_formula)) cl no_pos;
    let _ = phase_num_infer_one_scc cl in ()
  ) phase_constr_tbl

let phase_num_infer_by_scc () =
  let pr = fun _ -> "" in
  Debug.no_1 "phase_num_infer_by_scc" pr pr phase_num_infer_by_scc ()

(* this method adds phase constraint into a table indexed by call number *)
(* it seems to be done on a per-call basis *)
let add_phase_constr_by_scc (proc: Cast.proc_decl) (lp: CP.formula list) =
  let index = proc.Cast.proc_call_order in
  let pname = proc.Cast.proc_name in
  let con = (pname, lp) in
  try
    let cons = Hashtbl.find phase_constr_tbl index in
    Hashtbl.replace phase_constr_tbl index (con::cons)
  with Not_found -> Hashtbl.add phase_constr_tbl index [con]

let add_phase_constr_by_scc (proc: Cast.proc_decl) (lp: CP.formula list) =
  let pr = fun _ -> "" in
  let pr1 = add_str "phase ctr added" (pr_list !CP.print_formula) in
  Debug.no_1 "add_phase_constr_by_scc" pr1 pr (add_phase_constr_by_scc proc) lp

let subst_phase_num_exp subst exp = 
  match exp with
  | CP.Var (v, pos) ->
      (try
        let i = List.assoc v subst in
        CP.mkIConst i pos
      with _ -> exp)
  | _ -> exp 

(* Substitute the value of phase variables into specification *)
(* If all values are zero then the phase fields will be removed *)  
let subst_phase_num_struc rem_phase subst (struc: struc_formula) : struc_formula =
  let f_e _ = None in
  let f_f _ = None in
  let f_h _ = None in
  let f_m _ = None in
  let f_a _ = None in
  let f_pf _ = None in
  let f_bf bf =
    let (pf, sl) = bf in
    match pf with
    (* restoring ml from the 3rd argument *)
    | CP.LexVar t_info ->
		    let t_ann = t_info.CP.lex_ann in
		    let ml = t_info.CP.lex_tmp in
			  let pos = t_info.CP.lex_loc in
        Debug.dinfo_hprint (add_str "lex_tmp" (pr_list !CP.print_exp)) ml no_pos;
        let subs_extra = match ml with
          | _::e::_ -> begin
            match CP.get_var_opt e with
            | None -> []
            | Some v -> 
                if (List.exists (fun (v2,_) -> CP.eq_spec_var v v2) subst) then [] 
                else 
                  begin
                    Debug.info_hprint (add_str "var -> 0" !CP.print_sv) v no_pos;
                    [(v,0)]
                  end
                end
          | _ -> [] 
        in
        let n_ml =
          if rem_phase == [] then
            (* replace the phase var with integer *)
            List.map (fun m -> subst_phase_num_exp (subs_extra@subst) m) ml 
          else 
            (* to remove phase vars in rem_phase *)
            List.filter (fun e -> match CP.get_var_opt e with
              | None -> true
              | Some v -> not(CP.mem_svl v rem_phase)) ml
        in Some (CP.mkLexVar t_ann n_ml ml pos, sl)
      (* TRUNG TODO: check SeqVar case *)
      | _ -> None
  in
  let f_pe _ = None in
  let e_f = f_e, f_f, f_h, (f_m, f_a, f_pf, f_bf, f_pe) in

  (* Remove inferred variables from EInfer *)
  let f_ext ext = match ext with
    | EInfer ({ formula_inf_vars = iv; formula_inf_continuation = cont } as e) ->
          let lv = fst (List.split subst) in
          let n_iv = Gen.BList.difference_eq CP.eq_spec_var iv lv in
          let n_cont = transform_struc_formula e_f cont in
          if Gen.is_empty n_iv then Some n_cont
          else Some (EInfer { e with 
              formula_inf_vars = n_iv;
              formula_inf_continuation = n_cont })
    | _ -> None
  in
  
  let s_f = f_ext, f_f, f_h, (f_m, f_a, f_pf, f_bf, f_pe) in
  let n_struc = transform_struc_formula s_f struc in
  let _ = 
    begin
      (* Debug.trace_hprint (add_str ("proc name") (pr_id)) pname no_pos; *)
      Debug.trace_hprint (add_str ("subst") (pr_list (pr_pair !CP.print_sv string_of_int))) subst no_pos;
      Debug.trace_hprint (add_str ("OLD_SPECS") (!print_struc_formula)) struc no_pos;
      Debug.trace_hprint (add_str ("NEW_SPECS") (!print_struc_formula)) n_struc no_pos;
    end 
  in
  n_struc

let subst_phase_num_struc rp subst (struc: struc_formula) : struc_formula =
  let pr = !print_struc_formula in
  let pr0 = !CP.print_svl in
  let pr1 = pr_list (pr_pair !CP.print_sv string_of_int) in
  Debug.no_3 (* (fun _ -> not (Gen.is_empty struc)) *) 
  "subst_phase_num_struc" pr0 pr1 pr pr 
  (subst_phase_num_struc) rp subst struc

(* let subst_phase_num_struc subst (struc: struc_formula) : struc_formula = *)
(*   if struc==[] then struc *)
(*   else subst_phase_num_struc subst struc *)

let subst_phase_num_proc rp subst (proc: Cast.proc_decl) : Cast.proc_decl =
  let s_specs = subst_phase_num_struc rp subst proc.Cast.proc_static_specs in
  let d_specs = subst_phase_num_struc rp subst proc.Cast.proc_dynamic_specs in
  let _ = proc.Cast.proc_stk_of_static_specs # push s_specs in 
  { proc with
      Cast.proc_static_specs = s_specs;
      Cast.proc_dynamic_specs = d_specs; }

let phase_num_infer_whole_scc (prog: Cast.prog_decl) (proc_lst: Cast.proc_decl list) : Cast.prog_decl =
  let mutual_grp = List.map (fun p -> p.Cast.proc_name) proc_lst in
  match proc_lst with
    | [] -> print_endline "ERROR : empty SCC prog_lst!"; prog
    | proc::_ ->
          begin
            let index = proc.Cast.proc_call_order in
            try
              let cons = Hashtbl.find phase_constr_tbl index in
              (* let grp = fst (List.split cons) in *)
              (* let is_full_grp = Gen.BList.list_setequal_eq (=) grp mutual_grp in *)
              let is_full_grp = true in
              Debug.trace_hprint (add_str ("proc") (pr_id)) proc.Cast.proc_name no_pos;
              Debug.trace_hprint (add_str "full_grp?" string_of_bool) is_full_grp no_pos;
              (* Trigger phase number inference when 
               * all needed information is collected *)
              if is_full_grp then
                let cl = List.concat (snd (List.split cons)) in
                let inf_num = phase_num_infer_one_scc cl in
                Debug.trace_hprint (add_str "list of ctr" 
                    (pr_list !CP.print_formula)) cl no_pos;
                let subst =
                  match inf_num with
                    | None -> []
                    | Some (inf_num, fv) ->
                          begin
                            if not (Gen.is_empty inf_num) then
                              (* List.concat (List.map (fun (i, l) -> List.map (fun v -> (v, i)) l) inf_num) *)
                              inf_num
                            else
                              (* The inferred graph has only one vertex *)
                              (* All of phase variables will be assigned by 0 *)
                              (* let fv = List.concat (List.map (fun f -> CP.fv f) cl) in*)
                              let fv = Gen.BList.remove_dups_eq CP.eq_spec_var fv in
                              List.map (fun v -> (v, 0)) fv
                          end
                in
                (* Termination: Add the inferred phase numbers 
                 * into specifications of functions in mutual group *)
                (* if subst==[] then  *)
                (*   begin *)
                (*     Debug.info_hprint (add_str "Mutual Rec Group" (pr_list pr_id)) mutual_grp no_pos;  *)
                (*     Debug.info_pprint "Phase Subst is EMPTY" no_pos; *)
                (*     prog *)
                (*   end *)
                (* else  *)
                  (* all_zero is set if subs is only of form [v1->0,..,vn->0]
                     in this scenario, there is no need for phase vars at all *)
                  begin
                    Debug.devel_zprint (lazy (" >>>>>> [term.ml][Adding Phase Numbering] <<<<<<")) no_pos;
                    let all_zero = List.for_all (fun (_,i) -> i==0) subst in
                    let rp = if all_zero then List.map (fun (v,_) -> v) subst else [] in
                    if all_zero then
                      Debug.trace_hprint (add_str ("Phase to remove") !CP.print_svl) rp no_pos
                    else begin
                      Debug.info_hprint (add_str "Mutual Rec Group" (pr_list pr_id)) mutual_grp no_pos; 
                      Debug.info_hprint (add_str "Phase Numbering"
                          (pr_list (pr_pair !CP.print_sv string_of_int))) subst no_pos
                    end;
                    let n_tbl = Cast.proc_decls_map (fun proc ->
                        if (List.mem proc.Cast.proc_name mutual_grp) 
                        then subst_phase_num_proc rp subst proc
                        else proc
                    ) prog.Cast.new_proc_decls in  
                    { prog with Cast.new_proc_decls = n_tbl }
                  end
              else prog
            with Not_found -> prog
          end

let phase_num_infer_whole_scc (prog: Cast.prog_decl) (proc_lst: Cast.proc_decl list) : Cast.prog_decl =
  let mutual_grp = List.map (fun p -> p.Cast.proc_name) proc_lst in
  let pr _ = pr_list pr_id mutual_grp in
  Debug.no_1 "phase_num_infer_whole_scc" pr pr_no (phase_num_infer_whole_scc prog) proc_lst 

(* Main function of the termination checker *)
let term_check_output () =
  (* if not !Globals.dis_term_msg then *)
    (fmt_string "\nTermination checking result:\n";
    (if (!Globals.term_verbosity == 0) then pr_term_res_stk (term_res_stk # get_stk)
    else pr_term_err_stk (term_err_stk # get_stk));
    fmt_print_newline ())

let rec get_loop_ctx c =
  match c with
    | Ctx es -> (
        match es.es_var_measures with
        | None -> []
        | Some (CP.LexVar lex) -> if lex.CP.lex_ann == Loop then [es] else []
        | Some (CP.SeqVar seq) -> if seq.CP.seq_ann == Loop then [es] else []
        | _ -> report_error no_pos "Term.get_loop_ctx: Invalid value of es_var_measures.";
      )
    | OCtx (c1,c2) -> (get_loop_ctx c1) @ (get_loop_ctx c2)

let get_loop_only sl =
  let ls = List.map (fun (_,c) -> get_loop_ctx c) sl in
  List.concat ls

let add_unsound_ctx (es: entail_state) pos = 
  let term_pos = (post_pos # get, no_pos) in
  let term_res = (term_pos, None, Some es.es_formula, UnsoundLoop) in
  add_term_res_stk term_res;
  add_term_err_stk (string_of_term_res term_res)

(* if Loop, check that ctx is false *)
let check_loop_safety (prog : Cast.prog_decl) (proc : Cast.proc_decl) (ctx : list_partial_context) post pos (pid:formula_label) : bool  =
  Debug.trace_hprint (add_str "proc name" pr_id) proc.Cast.proc_name pos;
  let good_ls = List.filter (fun (fl,sl) -> fl==[]) ctx in (* Not a fail context *)
  let loop_es = List.concat (List.map (fun (fl,sl) -> get_loop_only sl) good_ls) in
  if loop_es==[] then true
  else 
    begin
      Debug.devel_zprint (lazy (" >>>>>> [term.ml][check loop safety] <<<<<<")) no_pos;
      Debug.trace_hprint (add_str "res ctx" Cprinter.string_of_list_partial_context_short) ctx pos;
      Debug.devel_hprint (add_str "loop es" (pr_list Cprinter.string_of_entail_state_short)) loop_es pos;
      (* TODO: must check that each entail_state from loop_es implies false *)
      let unsound_ctx = List.find_all (fun es -> not (isAnyConstFalse es.es_formula)) loop_es in
      if unsound_ctx == [] then true
      else
        begin
        Debug.devel_hprint (add_str "unsound Loop" (pr_list Cprinter.string_of_entail_state_short)) unsound_ctx pos;
        List.iter (fun es -> add_unsound_ctx es pos) unsound_ctx;
        false
        end;
    end

let check_loop_safety (prog : Cast.prog_decl) (proc : Cast.proc_decl) (ctx : list_partial_context) post pos (pid:formula_label) : bool  =
  Debug.no_1 "check_loop_safety" 
      pr_id string_of_bool (fun _ -> check_loop_safety prog proc ctx post pos pid) proc.Cast.proc_name

