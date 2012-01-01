module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module DD = Debug
open Gen.Basic
open Globals
open Cprinter

type phase_trans = int * int

type term_reason =
  (* The variance is not well-founded *)
  | Not_Decrease_Measure     
  | Not_Bounded_Measure
  (* The variance is well-founded *)
  | Valid_Measure   
  (* Reachability *)
  | Base_Case_Reached
  | Non_Term_Reached
  (* Reason for error *)
  | Invalid_Phase_Trans

(* The termination can only be determined when 
 * a base case or an infinite loop is reached *)  
type term_status =
  | Term of term_reason
  | NonTerm of term_reason
  | MayTerm of term_reason
  | Unreachable (* Original context causes unreachable *)
  | TermErr of term_reason

(* Location of the recursive call/loop and its termination status *)
type term_res = loc * term_status

(* Using stack to store term_res *)
let term_res_stk : term_res Gen.stack = new Gen.stack

(* Printing Utilities *)
let pr_phase_trans (trans: phase_trans) =
  let (src, dst) = trans in
  fmt_string "Transition ";
  pr_int src; fmt_string "->"; pr_int dst

let string_of_phase_trans (trans: phase_trans) = 
  poly_string_of_pr pr_phase_trans trans

let pr_term_reason = function
  | Not_Decrease_Measure -> fmt_string "The variance is not well-founded (not decreasing)."
  | Not_Bounded_Measure -> fmt_string "The variance is not well-founded (not bounded)."
  | Valid_Measure -> fmt_string "The given variance is well-founded."
  | Base_Case_Reached -> fmt_string "The base case is reached."
  | Non_Term_Reached -> fmt_string "A non-terminating state is reached."
  | Invalid_Phase_Trans -> fmt_string "The phase transition number is invalid."

let string_of_term_reason (reason: term_reason) =
  poly_string_of_pr pr_term_reason reason

let pr_term_status = function
  | Term reason -> fmt_string "Terminating: "; pr_term_reason reason
  | NonTerm reason -> fmt_string "Non-terminating: "; pr_term_reason reason
  | MayTerm reason -> fmt_string "May-terminating: "; pr_term_reason reason
  | Unreachable -> fmt_string "Unreachable state"
  | TermErr reason -> fmt_string "Error: "; pr_term_reason reason

let string_of_term_status = poly_string_of_pr pr_term_status

let pr_term_res (pos, status) =
  fmt_string (string_of_loc pos);
  fmt_string ": ";
  pr_term_status status

let string_of_term_res = poly_string_of_pr pr_term_res

let pr_term_res_stk stk =
  List.iter (fun r -> pr_term_res r; fmt_string "\n"; flush stdout) stk

let term_check_output stk =
  fmt_string "\nTermination checking result:\n";
  pr_term_res_stk (stk # get_stk);
  fmt_string "\n"

(* End of Printing Utilities *)

(* To find a LexVar formula *)
exception LexVar_Not_found;;
exception Invalid_Phase_Num;;

let find_lexvar_b_formula (bf: CP.b_formula) : (CP.exp list * CP.exp list) =
  let (pf, _) = bf in
  match pf with
  | CP.LexVar (el, il, _) -> (el, il)
  | _ -> raise LexVar_Not_found

let rec find_lexvar_formula (f: CP.formula) : (CP.exp list * CP.exp list) =
  match f with
  | CP.BForm (bf, _) -> find_lexvar_b_formula bf
  | CP.And (f1, f2, _) ->
      (try find_lexvar_formula f1
      with _ -> find_lexvar_formula f2)
  | _ -> raise LexVar_Not_found

(* To syntactic simplify LexVar formula *)  
let rec syn_simplify_lexvar bnd_measures =
  match bnd_measures with
  | [] -> []
  | (s,d)::rest -> 
      if (CP.eqExp s d) then syn_simplify_lexvar rest
      else if (CP.is_gt CP.eq_spec_var s d) then []
      else if (CP.is_lt CP.eq_spec_var s d) then [(s,d)]
      else bnd_measures 

let find_lexvar_es (es: CF.entail_state) =
  match es.CF.es_var_measures with
  | None -> raise LexVar_Not_found
  | Some (el, il) -> (el, il)

(* To handle LexVar formula *)
let trans_lexvar_rhs estate lhs_p rhs_p pos =
  try
    let conseq = MCP.pure_of_mix rhs_p in
    let dst_lv = fst (find_lexvar_formula conseq) in (* [d1,d2] *)
    let src_lv = fst (find_lexvar_es estate) in
    (* Filter LexVar in RHS *)
    let rhs_ls = CP.split_conjunctions conseq in
    let (_, other_rhs) = List.partition (CP.is_lexvar) rhs_ls in
    let conseq = CP.join_conjunctions other_rhs in
    (* [s1,s2] |- [d1,d2] -> [(s1,d1), (s2,d2)] *)
    let bnd_measures = List.map2 (fun s d -> (s, d)) src_lv dst_lv in
    (* [(0,0), (s2,d2)] -> [(s2,d2)] *)
    let bnd_measures = syn_simplify_lexvar bnd_measures in
    if bnd_measures = [] then (estate, lhs_p, MCP.mix_of_pure conseq)
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
      let n_conseq = CP.mkAnd conseq (CP.simplify_disj rank_formula) pos in
      let n_rhs_p = MCP.mix_of_pure n_conseq in
      begin
        (* print_endline ">>>>>> trans_lexvar_rhs <<<<<<" ; *)
        (* print_endline ("Transformed RHS: " ^ (Cprinter.string_of_mix_formula n_rhs_p)) ; *)
        DD.devel_pprint ">>>>>> trans_lexvar_rhs <<<<<<" pos;
        DD.devel_pprint ("Transformed RHS: " ^ (Cprinter.string_of_mix_formula n_rhs_p)) pos;
      end;
      (estate, lhs_p, n_rhs_p)
  with _ -> (estate, lhs_p, rhs_p)

let trans_lexvar_rhs estate lhs_p rhs_p pos =
  let pr = !CF.print_mix_formula in
  let pr2 = !CF.print_entail_state_short in
   Gen.Debug.no_2 "trans_lexvar_rhs" pr pr (pr_triple pr2 pr pr)  
      (fun _ _ -> trans_lexvar_rhs estate lhs_p rhs_p pos) lhs_p rhs_p

let strip_lexvar_mix_formula (mf: MCP.mix_formula) =
  let mf_p = MCP.pure_of_mix mf in
  let mf_ls = CP.split_conjunctions mf_p in
  let (lexvar, other_p) = List.partition (CP.is_lexvar) mf_ls in
  (lexvar, CP.join_conjunctions other_p)

let strip_lexvar_lhs (ctx: CF.context) : CF.context =
  let es_strip_lexvar_lhs (es: CF.entail_state) : CF.context =
    let _, pure_f, _, _, _ = CF.split_components es.CF.es_formula in
    let (lexvar, other_p) = strip_lexvar_mix_formula pure_f in
    (* Using transform_formula to update the pure part of es_f *)
    let f_e_f _ = None in
    let f_f _ = None in
    let f_h_f e = Some e in
    let f_m mp = Some (MCP.memoise_add_pure_N_m (MCP.mkMTrue_no_mix no_pos) other_p) in
    let f_a _ = None in
    let f_p_f pf = Some other_p in
    let f_b _ = None in
    let f_e _ = None in
    match lexvar with
    | [] -> CF.Ctx es
    | lv::[] -> CF.Ctx { es with 
      CF.es_formula = CF.transform_formula (f_e_f, f_f, f_h_f, (f_m, f_a, f_p_f, f_b, f_e)) es.CF.es_formula;
      CF.es_var_measures = Some (find_lexvar_formula lv); 
    }
    | _ -> report_error no_pos "[term.ml][strip_lexvar_lhs]: More than one LexVar to be stripped." 
  in CF.transform_context es_strip_lexvar_lhs ctx

let strip_lexvar_lhs (ctx: CF.context) : CF.context =
  let pr = Cprinter.string_of_context in
  Gen.Debug.no_1 "strip_lexvar_lhs" pr pr strip_lexvar_lhs ctx

let get_phase_num (measure: CF.ext_variance_formula) : int =
  let phase_num = fst (List.nth measure.CF.formula_var_measures 1) in
  if (CP.is_num phase_num) then CP.to_int_const phase_num CP.Floor 
  else raise Invalid_Phase_Num 
  
let check_term_measure f (ctx: CF.context) (measure: CF.ext_variance_formula) pos : term_res =
  let term_res = 
    try
      let phase_num = get_phase_num measure in 
      if (phase_num < 0) then
        (pos, NonTerm Non_Term_Reached)
      else if (phase_num = 0) then
        (pos, Term Base_Case_Reached)
      else 
        let lv = CF.formula_of_pure_formula (CF.lexvar_of_evariance measure) pos in
        let res = f ctx lv pos in (* check decreasing *)
        if (CF.isFailCtx res) then (pos, MayTerm Not_Decrease_Measure)
        else
          (* The default lower bound is zero *)
          let zero = List.map (fun _ -> CP.mkIConst 0 pos) measure.CF.formula_var_measures in       
          let bnd = CF.formula_of_pure_formula (CP.mkPure (CP.mkLexVar zero [] pos)) pos in
          let res = f ctx bnd pos in (* check boundedness *)
          if (CF.isFailCtx res) then (pos, MayTerm Not_Bounded_Measure)
          else (pos, Term Valid_Measure)
    with 
    | Invalid_Phase_Num
    | Failure "nth" -> (pos, TermErr Invalid_Phase_Trans)
  in 
  term_res_stk # push term_res;
  term_res


