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
open Cpure

module CP = Cpure

module StringSet = Set.Make(String)

(**
 * Relation definition
*)
type relation_definition = 
  | RelDefn of (ident * CP.spec_var list * CP.formula)

(**
 * Temp files used to feed input and capture output from provers
*)
let infile = "/tmp/in" ^ (string_of_int (Unix.getpid ())) ^ ".smt"
let outfile = "/tmp/out" ^ (string_of_int (Unix.getpid ()))
let print_input = ref false
let print_original_solver_output = ref false

let print_pure = ref (fun (c:CP.formula)-> " printing not initialized")

(**
 * @author An Hoa
 * Relation definitions. To be appended by process_rel_def appropriately.
*)
let rel_defs = ref ([] : relation_definition list)

(**
 * Add a new relation definition. 
 * Notice that we have to add the relation at the end in order to preserve the order of appearance of the relations.
*)
let add_rel_def rdef =
  (* let rn = match rdef with RelDefn (a,_,_) -> a in
     	let _ = print_string ("Smtsolver :: add relation definition - " ^ rn ^ "\n") in *) 
  rel_defs := !rel_defs @ [rdef]

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
  | CP.ArrayAt (a, i,_) -> is_linear_exp i (* v[i] is linear <==> i is linear*)
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
  | CP.RelForm (r, args, _) -> (* An Hoa : Relation is linear <==> the parameters are all linear *)
    let al = List.map is_linear_exp args in
    not (List.mem false al) (* Check if any of args is not linear *)
  | _ -> false

let rec is_linear_formula f0 = match f0 with
  | CP.BForm (b,_) -> is_linear_bformula b
  | CP.Not (f, _, _) | CP.Forall (_, f, _, _) | CP.Exists (_, f, _, _) ->
    is_linear_formula f;
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _, _) -> 
    (is_linear_formula f1) && (is_linear_formula f2)

let rec get_formula_of_rel_with_name rn rdefs =
  if (rn = "dom") then (CP.mkTrue Globals.no_pos) else
    match rdefs with
    | [] -> failwith ("Relation " ^ rn ^ " is not found!")
    | h :: t -> match h with RelDefn (r,_,f) -> if (r = rn) then f else get_formula_of_rel_with_name rn t

(**
 * Collect the relations that we use
*)
let rec collect_relation_names_bformula b collected = match b with
  | CP.RelForm (r,_,_) ->
    if (List.mem r collected || r = "update_array") then collected
    else (* Add r to the list of collected relations &
            		        collect relations that r depends on *)
      let collected = r :: collected in
      collect_relation_names_formula (get_formula_of_rel_with_name r !rel_defs) collected
  | _ -> collected

(**
 * Collect the relations that we use
*)
and collect_relation_names_formula f0 collected = match f0 with
  | CP.BForm (b, _) -> collect_relation_names_bformula b collected
  | CP.Not (f, _, _) | CP.Forall (_,f,_,_) | CP.Exists (_,f,_,_)-> collect_relation_names_formula f collected
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _, _) ->
    (* Collect from f1 first, then collect from f2 *)
    let collected = collect_relation_names_formula f1 collected in
    collect_relation_names_formula f2 collected 
(*
(**
 * Collect the relations that we use
 *)
let rec collect_relation_names_bformula b = match b with
	| CP.RelForm (r,_,_) -> [r]
  | _ -> []

and collect_relation_names_formula f0 = match f0 with
  | CP.BForm (b, _) -> collect_relation_names_bformula b
  | CP.Not (f, _, _) | CP.Forall (_,f,_,_) | CP.Exists (_,f,_,_)-> collect_relation_names_formula f
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _, _) ->
		(* Collect from f1 first, then collect from f2 *)
		(collect_relation_names_formula f1) @ (collect_relation_names_formula f2) *)


(**
 * Checking whether a formula is quantifier-free or not
*)
let rec is_quantifier_free_formula f0 = match f0 with
  | CP.BForm (b,_) -> (* true *)(* An Hoa *)
    begin 
      match b with
      | CP.RelForm _ -> false (* Contain relation ==> we need to use forall to axiomatize ==> not quantifier free! *)
      | _ -> true 
    end
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
  | Cvc4
  | Yices

(**
   An Hoa : Remove the "tail -n 1" because the new version of z3 solver prints the result on the first line following by the error / warning message. 
*)
let command_for prover = 
  let helper s = s ^ infile ^ (* " | tail -n 1 > " *) " > " ^ outfile in
  match prover with
  | Z3 -> helper "z3 -smt2 "
  | Cvc4 -> helper "cvc4 --lang=smt "
  | Yices -> helper "yices "

(** An Hoa
 * Get the type of a spec_var
*)
let extract_type sv = 
  match sv with
  | CP.SpecVar (t,_,_) -> t

(** An Hoa
 * Get the name of a spec_var
*)
let extract_name sv = 
  match sv with
  | CP.SpecVar (_,n,_) -> n

(** An Hoa : 
 * Find the SMT corresponding of typ
*)
let rec smt_of_typ t = 
  match t with
  | CP.Prim pt -> begin match pt with
      | Bool -> "Int" (* Weird but Hip/sleek use integer to represent "Bool" : 0 = false and > 0 is true. *)
      | Float -> "Real"
      | Int -> "Int"
      | Void | Globals.Bag | Globals.List -> "" (* Fail! *)
    end
  | CP.OType _ -> "Int" (* TODO : RECOVER failwith ("Object types are not supported in Z3! - " ^ CP.name_of_type t) *)
  | CP.Array et -> "(Array Int " ^ smt_of_typ et ^ ")"

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
  | CP.ArrayAt (a, i, l) -> 
    (* An Hoa : TODO EDIT APPROPRIATELY *)
    "(select " ^ (smt_of_spec_var a (Some qvars)) ^ " " ^ (smt_of_exp i qvars) ^ ")"

let rec smt_of_b_formula b qvars =
  let smt_of_spec_var v = smt_of_spec_var v (Some qvars) in
  let smt_of_exp e = smt_of_exp e qvars in
  match b with
  | CP.BConst (c, _) -> if c then "true" else "false"
  | CP.BVar (sv, _) -> "(> " ^(smt_of_spec_var sv) ^ " 0)"
  | CP.Lt (a1, a2, _) -> "(< " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Lte (a1, a2, _) -> "(<= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Gt (a1, a2, _) -> "(> " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Gte (a1, a2, _) -> "(>= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Eq (a1, a2, _) -> 
    if CP.is_null a2 then
      "(< " ^(smt_of_exp a1)^ " 1)"
    else if CP.is_null a1 then
      "(< " ^(smt_of_exp a2)^ " 1)"
    else
      "(= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
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
  | CP.RelForm (r, args, l) ->
    (* An Hoa : TODO EDIT APPROPRIATELY *)
    let smt_args = List.map smt_of_exp args in 
    if (r = "update_array") then
      let orig_array = List.nth smt_args 0 in
      let index = List.nth smt_args 1 in
      let value = List.nth smt_args 2 in
      let new_array = List.nth smt_args 3 in
      "(= " ^ new_array ^ " (store " ^ orig_array ^ " " ^ index ^ " " ^ value ^ "))"
    else
      "(" ^ r ^ " " ^ (String.concat " " smt_args) ^ ")"

let rec smt_of_formula f qvars =
  match f with
  | CP.BForm (b,_) -> (smt_of_b_formula b qvars)
  | CP.And (p1, p2, _) -> "(and " ^ (smt_of_formula p1 qvars) ^ " " ^ (smt_of_formula p2 qvars) ^ ")"
  | CP.Or (p1, p2,_, _) -> "(or " ^ (smt_of_formula p1 qvars) ^ " " ^ (smt_of_formula p2 qvars) ^ ")"
  | CP.Not (p,_, _) -> "(not " ^ (smt_of_formula p qvars) ^ ")"
  | CP.Forall (sv, p, _,_) ->
    (* see smt_of_spec_var for explanations of the qvars set *)
    let varname = smt_of_spec_var sv None in
    let qvars = StringSet.add varname qvars in
    "(forall (?" ^ varname ^ " " ^ (smt_of_typ (extract_type sv)) ^ ") " (* " Int) " *) ^ (smt_of_formula p qvars) ^ ")"
  | CP.Exists (sv, p, _,_) ->
    (* see smt_of_spec_var for explanations of the qvars set *)
    let varname = smt_of_spec_var sv None in
    let qvars = StringSet.add varname qvars in
    "(exists (?" ^ varname ^ " " ^ (smt_of_typ (extract_type sv)) ^ ") " (* " Int) " *) ^ (smt_of_formula p qvars) ^ ")"


(* An Hoa : get the corresponding typed variable. For instance, *)

let smt_typed_var_of_spec_var sv = 
  match sv with
  | CP.SpecVar (t, id, _) -> "(" ^ (smt_of_spec_var sv None) ^ " " ^ (smt_of_typ t) ^ ")"

(**
 * Process the relation definition
 * @return A pair of two strings: the first being declare-fun relation declaration and the second
 *         be the axiomatization.
*)				
let smt_of_rel_def (rdef : relation_definition) =
  match rdef with
  | RelDefn	(rn,rv,rf) ->
    let rel_signature = String.concat " " (List.map smt_of_typ (List.map extract_type rv)) in
    let rel_typed_vars = String.concat " " (List.map smt_typed_var_of_spec_var rv) in
    let rel_params = String.concat " " (List.map extract_name rv) in
    (* Declare the relation in form of a function --> Bool *)
    (* Axiomatize the relation using an assertion*)
    ("(declare-fun " ^ rn ^ " (" ^ rel_signature ^ ") Bool)\n",
     "(assert (forall " ^ rel_typed_vars ^ " (= (" ^ rn ^ " " ^ rel_params ^ ") " ^ (smt_of_formula rf StringSet.empty) ^ ")))\n")

(**
 * output for smt-lib v2.0 format
*)
let to_smt_v2 ante conseq logic fvars used_rels_defs =
  let rec decfuns vars = match vars with
    (* let's assume all vars are Int *)
    | [] -> ""
    | var::rest -> "(declare-fun " ^ (smt_of_spec_var var None) ^ " () " ^ (smt_of_typ (extract_type var)) ^ ")\n" (* " () Int)\n" *) ^ (decfuns rest) (* An Hoa : modify the declare-fun *) 
  in 
  let rds = (List.map smt_of_rel_def used_rels_defs) in
  let rel_def_df = (String.concat "" (List.map fst rds)) in
  let rel_def_ax = (String.concat "" (List.map snd rds)) in
  ("(set-logic AUFNIA" ^ (* (string_of_logic logic) ^*) ")\n" ^ 
   (decfuns fvars) ^ rel_def_df ^ rel_def_ax ^ (* Collect the declare-fun first and then do the axiomatization to prevent missing function error *)
   (*"(declare-fun update_array ((Array Int Int) Int Int (Array Int Int)) Bool)" ^
     		"(assert (forall (a (Array Int Int)) (i Int) (v Int) (r (Array Int Int)) 
     		         (= (update_array a i v r) (= r (store a i v)))))" ^*)
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
  let all_fv = Gen.BList.remove_dups_eq (=) (ante_fv @ conseq_fv) in
  let ante_str = smt_of_formula ante StringSet.empty in
  let conseq_str = smt_of_formula conseq StringSet.empty in
  let logic = logic_for_formulas ante conseq in
  (* relations that appears in the ante and conseq *)
  let used_rels = (collect_relation_names_formula ante []) @ (collect_relation_names_formula conseq []) in
  (*let used_rels = (collect_relation_names_formula ante) @ (collect_relation_names_formula conseq) in*)
  let used_rels_defs = List.map (fun x -> match x with | RelDefn (rn,_,_) -> if List.mem rn used_rels then [x] else []) !rel_defs in
  let used_rels_defs = List.concat used_rels_defs in
  let res = match prover with
    | Z3 ->  to_smt_v2 ante_str conseq_str logic all_fv used_rels_defs
    | Cvc4 | Yices ->  to_smt_v1 ante_str conseq_str logic all_fv
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

(** An Hoa
 * Switch to choose whether to do induction.
*)
let try_induction = ref false
let max_induction_level = ref 0

(** An Hoa
 * Select the candidates to do induction on. Just find all
 * relation dom(_,low,high) that appears and collect the 
 * { high - low } such that ante |- low <= high.
*)
let rec collect_induction_value_candidates (ante : CP.formula) (conseq : CP.formula) : (CP.exp list) =
  match conseq with
  | BForm (b,_) -> (match b with
      | RelForm ("dom",[_;low;high],_) -> (* check if we can prove ante |- low <= high? *) [CP.mkSubtract high low no_pos]
      | _ -> [])
  | And (f1,f2,_) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
  | Or (f1,f2,_,_) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
  | Not (f,_,_) -> (collect_induction_value_candidates ante f)
  | Forall _ | Exists _ -> []

(** An Hoa
 * Select the value to do induction on.
 * A simple approach : induct on the length of an array.
*)
and choose_induction_value (ante : CP.formula) (conseq : CP.formula) : CP.exp = 
  let vals = collect_induction_value_candidates ante conseq in
  List.hd vals

(** An Hoa
 * Create a variable totally different from the ones in vlist.
*)
and create_induction_var (vlist : CP.spec_var list) : CP.spec_var =
  (* We select the appropriate variable with name "omg_i"*)
  (* with i minimal natural number such that omg_i is not in vlist *)
  let rec create_induction_var_helper vlist i = match vlist with
    | [] -> i
    | hd :: tl -> 
      let v = SpecVar (int_type,"omg_" ^ (string_of_int i),Unprimed) in
      if CP.mem v vlist then
        create_induction_var_helper vlist (i+1)
      else 
        create_induction_var_helper vlist i
  in let i = create_induction_var_helper vlist 0 in
  SpecVar (int_type,"omg_" ^ (string_of_int i),Unprimed)

(** An Hoa
 * Generate the base case, induction hypothesis and induction case
 * for a formula phi(v,v_1,v_2,...) with new induction variable v.
 * v = expression of v_1,v_2,...
*)
and gen_induction_formulas (phi : CP.formula) (indval : CP.exp) : (CP.formula * CP.formula * CP.formula) =
  let p = fv phi in (* collect free variables in phi *)
  let v = create_induction_var p in (* create induction variable *)
  let phiv = mkAnd phi (CP.mkEqExp (CP.mkVar v no_pos) indval no_pos) no_pos in (* phiv(v) = phi /\ (v = indval) *)
  let phi0 = CP.apply_one_term (v, CP.mkIConst 0 no_pos) phiv in (* base case phiv[v/0] *)
  let phihyp = CP.mkForall p phiv None no_pos in (* induction hypothesis, add universal quantifiers to all free variables in phi *)
  let phivp1 = CP.apply_one_term (v, CP.mkAdd (CP.mkVar v no_pos) (CP.mkIConst 1 no_pos) no_pos) phiv in (* inductive case phiv[v/v+1], we try to prove phihyp --> phiv[v/v+1] *)
  (phi0, phihyp, phivp1)

(** An Hoa
 * Check implication with induction heuristic.
*)
and smt_imply_with_induction (ante : CP.formula) (conseq : CP.formula) (prover: smtprover) : bool =
  true

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
  let _ = if !print_input then print_string ("Generated SMT input :\n" ^ input) in
  let output = run prover input in
  let _ = if !print_original_solver_output then print_string ("=1=> SMT output : " ^ output ^ "\n") in
  let res = output = "unsat" in
  (* TODO Try induction in "unsat" case! *)
  res

(* For backward compatibility, use Z3 as default *
 * Probably, a better way is modify the tpdispatcher.ml to call imply with a
 * specific smt-prover argument as well *)
let imply ante conseq = smt_imply ante conseq Z3

(**
 * Test for satisfiability
 * We also consider unknown is the same as sat
*)
let smt_is_sat (f : Cpure.formula) (sat_no : string) (prover: smtprover) : bool =
  let input = to_smt f None prover in
  (*let _ = if !print_input then print_string ("Generated SMT input :\n" ^ input) in*)
  let output = run prover input in
  (*let _ = if !print_original_solver_output then print_string ("==> SMT output : " ^ output ^ "\n") in*)
  let res = output = "unsat" in
  not res

(* see imply *)
let is_sat f sat_no = smt_is_sat f sat_no Z3

(* let is_sat f sat_no = Gen.Debug.loop_2 "is_sat" (!print_pure) (fun x->x) string_of_bool is_sat f sat_no *)


(**
 * To be implemented
*)
let simplify (f: CP.formula) : CP.formula = f
let hull (f: CP.formula) : CP.formula = f
let pairwisecheck (f: CP.formula): CP.formula = f

