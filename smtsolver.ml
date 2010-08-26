(**
 * Author           : Wong Choon Teng Justin
 * Last modified    : Wed Aug 12 16:47:05 SGT 2009
 *
 * Tests for validity and satisfiability of a core pure formula using various SMT solvers
 *
 * TODO:
 * Error checking(runProver)
 * Bag/Set constraints not handled
 * Check renaming of ?vars in exists
 *)

(**
 * Modified on Aug 22, 2010 by lebinh
 * Various changes :)
 *)

open Globals
module CP = Cpure

module StringSet = Set.Make(String)


(**
 * Temp files used to feed input and capture output from provers
 *)
let infile = "/tmp/in" ^ (string_of_int (Unix.getpid ())) ^ ".smt"
let outfile = "/tmp/out" ^ (string_of_int (Unix.getpid ()))


(******************
 * Helper funcs
 ******************)

(**
 * Checking whether a formula is linear or not
 *)
let rec is_linear_exp exp = match exp with
  | CP.Null _ | CP.Var _ | CP.IConst _ -> true
  | CP.Add (e1, e2, _) | CP.Subtract (e1, e2, _) -> 
      (is_linear_exp e1) && (is_linear_exp e2)
  | CP.Mult (e1, e2, _) -> 
      let res = match e1, e2 with
        | CP.IConst _, _ -> is_linear_exp e2
        | _, CP.IConst _ -> is_linear_exp e1
        | _, _ -> false
      in res
  | _ -> false

let is_linear_bformula b = match b with
  | CP.BConst _ -> true
  | CP.BVar _ -> true
  | CP.Lt (e1, e2, _) | CP.Lte (e1, e2, _) 
  | CP.Gt (e1, e2, _) | CP.Gte (e1, e2, _)
  | CP.Eq (e1, e2, _) | CP.Neq (e1, e2, _) -> 
      (is_linear_exp e1) && (is_linear_exp e2)
  | CP.EqMax (e1, e2, e3, _) | CP.EqMin (e1, e2, e3, _) -> 
      (is_linear_exp e1) && (is_linear_exp e2) && (is_linear_exp e3)
  | _ -> false
  
let rec is_linear_formula f0 = match f0 with
  | CP.BForm (b,_) -> is_linear_bformula b
  | CP.Not (f, _, _) | CP.Forall (_, f, _, _) | CP.Exists (_, f, _, _) ->
      is_linear_formula f;
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _, _) -> 
      (is_linear_formula f1) && (is_linear_formula f2)

(**
 * Checking whether a formula is quantifier-free or not
 *)
let rec is_quantifier_free_formula f0 = match f0 with
  | CP.BForm _ -> true
  | CP.Not (f, _, _) -> is_quantifier_free_formula f
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _, _) ->
      (is_quantifier_free_formula f1) && (is_quantifier_free_formula f2)
  | CP.Forall _ | CP.Exists _ -> false


(**
 * Logic types for smt solvers
 * based on smt-lib benchmark specs
 *)
type smtlogic =
  | QF_LIA    (* quantifier free linear integer arithmetic *)
  | QF_NIA    (* quantifier free nonlinear integer arithmetic *)
  | AUFLIA    (* arrays, uninterpreted functions and linear integer arithmetic *)
  | UFNIA     (* uninterpreted functions and nonlinear integer arithmetic *)

let string_of_logic logic =
  match logic with
  | QF_LIA -> "QF_LIA"
  | QF_NIA -> "QF_NIA"
  | AUFLIA -> "AUFLIA"
  | UFNIA -> "UFNIA"

let logic_for_formulas f1 f2 =
  let linear = (is_linear_formula f1) && (is_linear_formula f2) in
  let quantifier_free = (is_quantifier_free_formula f1) && (is_quantifier_free_formula f2) in
  match linear, quantifier_free with
  | true, true -> QF_LIA
  | false, true -> QF_NIA
  | true, false -> AUFLIA (* should I use UFNIA instead? *)
  | false, false -> UFNIA


(**
 * Define SMT provers and commands needed to run them
 *)
type smtprover =
  | Z3
  | Cvc3
  | Yices

let command_for prover = 
  let helper s = s ^ infile ^ " | tail -n 1 > " ^ outfile in
  match prover with
  | Z3 -> helper "z3 -smt2 "
  | Cvc3 -> helper "cvc3 -lang smt "
  | Yices -> helper "yices "


(**
 * smt of spec_var
 *)
let smt_of_spec_var (sv : CP.spec_var) qvars =
  let getname sv = match sv with
    | CP.SpecVar (_, v, _) -> v ^ (if CP.is_primed sv then "'" else "")
  in
  match qvars with
  | None -> getname sv
  | Some set ->
      (* Smt-lib format requires quantified vars begin with a '?'
       * So, I pass a set of all known quantified vars (qvars) along with every
       * formulas and check it here to put a '?' accordingly
       *)
      let name = getname sv in
      let prefix = if StringSet.mem name set then "?" else "" in
      prefix ^ name

let rec smt_of_exp a qvars =
  match a with
  | CP.Null _ -> "0"
  | CP.Var (sv, _) -> smt_of_spec_var sv (Some qvars)
  | CP.IConst (i, _) -> if i >= 0 then string_of_int i else "(- 0 " ^ (string_of_int (0-i)) ^ ")"
  | CP.FConst _ -> failwith ("[smtsolver.ml]: ERROR in constraints (float should not appear here)")
  | CP.Add (a1, a2, _) -> "(+ " ^(smt_of_exp a1 qvars)^ " " ^ (smt_of_exp a2 qvars)^")"
  | CP.Subtract (a1, a2, _) -> "(- " ^(smt_of_exp a1 qvars)^ " " ^ (smt_of_exp a2 qvars)^")"
  | CP.Mult (a1, a2, _) -> "( * " ^ (smt_of_exp a1 qvars) ^ " " ^ (smt_of_exp a2 qvars) ^ ")"
  (* UNHANDLED *)
  | CP.Div _ -> failwith "[smtsolver.ml]: divide is not supported."
  | CP.Bag ([], _) -> "0"
  | CP.Max _
  | CP.Min _ -> failwith ("Smtsolver.smt_of_exp: min/max should not appear here")
  | CP.Bag _
  | CP.BagUnion _
  | CP.BagIntersect _
  | CP.BagDiff _ -> failwith ("[smtsolver.ml]: ERROR in constraints (set should not appear here)")
  | CP.List _ 
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListAppend _
  | CP.ListReverse _ -> failwith ("[smtsolver.ml]: ERROR in constraints (lists should not appear here)")

let rec smt_of_b_formula b qvars =
  let smt_of_spec_var v = smt_of_spec_var v (Some qvars) in
  let smt_of_exp e = smt_of_exp e qvars in
  match b with
  | CP.BConst (c, _) -> if c then "true" else "false"
  | CP.BVar (sv, _) -> "(= 1 " ^(smt_of_spec_var sv) ^ ")"
  | CP.Lt (a1, a2, _) -> "(< " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Lte (a1, a2, _) -> "(<= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Gt (a1, a2, _) -> "(> " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Gte (a1, a2, _) -> "(>= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Eq (a1, a2, _) -> "(= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Neq (a1, a2, _) ->
      if CP.is_null a2 then
        "(> " ^(smt_of_exp a1)^ " 0)"
      else if CP.is_null a1 then
        "(> " ^(smt_of_exp a2)^ " 0)"
      else
        "(not (= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ "))"
  | CP.EqMax (a1, a2, a3, _) ->
      let a1str = smt_of_exp a1 in
      let a2str = smt_of_exp a2 in
      let a3str = smt_of_exp a3 in
      "(or (and (= " ^ a1str ^ " " ^ a2str ^ ") (>= "^a2str^" "^a3str^")) (and (= " ^ a1str ^ " " ^ a3str ^ ") (< "^a2str^" "^a3str^")))"
  | CP.EqMin (a1, a2, a3, _) ->
      let a1str = smt_of_exp a1 in
      let a2str = smt_of_exp a2 in
      let a3str = smt_of_exp a3 in
      "(or (and (= " ^ a1str ^ " " ^ a2str ^ ") (< "^a2str^" "^a3str^")) (and (= " ^ a1str ^ " " ^ a3str ^ ") (>= "^a2str^" "^a3str^")))"
      (* UNHANDLED *)
  | CP.BagIn (v, e, l)    -> " in(" ^ (smt_of_spec_var v) ^ ", " ^ (smt_of_exp e) ^ ")"
  | CP.BagNotIn (v, e, l) -> " NOT(in(" ^ (smt_of_spec_var v) ^ ", " ^ (smt_of_exp e) ^"))"
  | CP.BagSub (e1, e2, l) -> " subset(" ^ smt_of_exp e1 ^ ", " ^ smt_of_exp e2 ^ ")"
  | CP.BagMax _ | CP.BagMin _ -> 
      failwith ("smt_of_b_formula: BagMax/BagMin should not appear here.\n")
  | CP.ListIn _ | CP.ListNotIn _ | CP.ListAllN _ | CP.ListPerm _ -> 
      failwith ("smt_of_b_formula: ListIn ListNotIn ListAllN ListPerm should not appear here.\n")

let rec smt_of_formula f qvars =
  match f with
  | CP.BForm (b,_) -> (smt_of_b_formula b qvars)
  | CP.And (p1, p2, _) -> "(and " ^ (smt_of_formula p1 qvars) ^ " " ^ (smt_of_formula p2 qvars) ^ ")"
  | CP.Or (p1, p2,_, _) -> "(or " ^ (smt_of_formula p1 qvars) ^ " " ^ (smt_of_formula p2 qvars) ^ ")"
  | CP.Not (p,_, _) ->
      begin
        match p with
        | CP.BForm (CP.BVar (bv, _),_) -> "(= 0 " ^ (smt_of_spec_var bv (Some qvars)) ^ ")"
        | _ -> "(not " ^ (smt_of_formula p qvars) ^ ")"
      end
  | CP.Forall (sv, p, _,_) ->
      (* see smt_of_spec_var for explanations of the qvars set *)
      let varname = smt_of_spec_var sv None in
      let qvars = StringSet.add varname qvars in
      "(forall (?" ^ varname ^ " Int) " ^ (smt_of_formula p qvars) ^ ")"
  | CP.Exists (sv, p, _,_) ->
      (* see smt_of_spec_var for explanations of the qvars set *)
      let varname = smt_of_spec_var sv None in
      let qvars = StringSet.add varname qvars in
      "(exists (?" ^ varname ^ " Int) " ^ (smt_of_formula p qvars) ^ ")"


(**
 * output for smt-lib v2.0 format
 *)
and to_smt_v2 ante conseq logic fvars =
  let rec decfuns vars = match vars with
    (* let's assume all vars are Int *)
    | [] -> ""
    | var::rest -> "(declare-fun " ^ (smt_of_spec_var var None) ^ " () Int)\n" ^ (decfuns rest)
  in ( 
    "(set-logic " ^ (string_of_logic logic) ^ ")\n" ^ 
    (decfuns fvars) ^
    "(assert " ^ ante ^ ")\n" ^
    "(assert (not " ^ conseq ^ "))\n" ^
    "(check-sat)\n")

(**
 * output for smt-lib v1.2 format
 *)
and to_smt_v1 ante conseq logic fvars =
  let rec defvars vars = match vars with
    | [] -> ""
    | var::rest -> "(" ^ (smt_of_spec_var var None) ^ " Int) " ^ (defvars rest)
  in
  let extrafuns = 
    if fvars = [] then "" 
    else ":extrafuns (" ^ (defvars fvars) ^ ")\n"
  in (
    "(benchmark blahblah \n" ^
    ":status unknown\n" ^
    ":logic " ^ (string_of_logic logic) ^ "\n" ^
    extrafuns ^
    ":assumption " ^ ante ^ "\n" ^
    ":formula (not " ^ conseq ^ ")\n" ^
    ")")

(**
 * Converts a core pure formula into SMT-LIB format which can be run through various SMT provers.
 *)
let to_smt (ante : CP.formula) (conseq : CP.formula option) (prover: smtprover) : string =
  let conseq = match conseq with
    (* We don't have conseq part in is_sat checking *)
    | None -> CP.mkFalse no_pos
    | Some f -> f
  in
  let ante_fv = CP.fv ante in
  let conseq_fv = CP.fv conseq in
  let all_fv = CP.remove_dups (ante_fv @ conseq_fv) in
  let ante_str = smt_of_formula ante StringSet.empty in
  let conseq_str = smt_of_formula conseq StringSet.empty in
  let logic = logic_for_formulas ante conseq in
  let res = match prover with
    | Z3 ->  to_smt_v2 ante_str conseq_str logic all_fv
    | Cvc3 | Yices ->  to_smt_v1 ante_str conseq_str logic all_fv
  in res

(**
 * Runs the specified prover and returns output
 *)
let run prover input =
  let out_stream = open_out infile in
  output_string out_stream input;
  close_out out_stream;
  let cmd = command_for prover in
  let _ = Sys.command cmd in
  let in_stream = open_in outfile in
  let res = input_line in_stream in
  close_in in_stream;
  (*
  Sys.remove infile;
  Sys.remove outfile;
  *)
  res


(**
 * Test for validity
 * To check the implication P -> Q, we check the satisfiability of
 * P /\ not Q
 * If it is satisfiable, then the original implication is false.
 * If it is unsatisfiable, the original implication is true.
 * We also consider unknown is the same as sat
 *)
let smt_imply (ante : Cpure.formula) (conseq : Cpure.formula) (prover: smtprover) : bool =
  let input = to_smt ante (Some conseq) prover in
  let output = run prover input in
  let res = output = "unsat" in
  res

let imply ante conseq = smt_imply ante conseq Z3

(**
 * Test for satisfiability
 * We also consider unknown is the same as sat
 *)
let smt_is_sat (f : Cpure.formula) (sat_no : string) (prover: smtprover) : bool =
  let input = to_smt f None prover in
  let output = run prover input in
  let res = output = "unsat" in
  not res

let is_sat f sat_no = smt_is_sat f sat_no Z3

(**
 * To be implemented
 *)
let simplify (f: CP.formula) : CP.formula = f
let hull (f: CP.formula) : CP.formula = f
let pairwisecheck (f: CP.formula): CP.formula = f

