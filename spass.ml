open Globals
open Gen.Basic
open Cpure

module StringSet = Set.Make(String)

(* Pure formula printing function, to be intialized by cprinter module *)

let print_pure = ref (fun (c: Cpure.formula) -> " printing not initialized")

(***************************************************************
TRANSLATE CPURE FORMULA TO SMT FORMULA
**************************************************************)

let spass_of_spec_var sv =
  (Cpure.name_of_spec_var sv) ^ (if Cpure.is_primed sv then "_primed" else "")

let rec spass_of_exp (e0 : Cpure.exp) : string =
  match e0 with
  | Cpure.Null _      -> "NULL"
  | Cpure.Var (sv, _) -> spass_of_spec_var sv
  | Cpure.IConst _    -> illegal_format "SPASS don't support IConst expresion"
  | Cpure.FConst _    -> illegal_format "SPASS don't support FConst expresion"
  | Cpure.AConst _    -> illegal_format "SPASS don't support AConst expresion"
  | Cpure.Add _       -> illegal_format "SPASS don't support Add expresion"
  | Cpure.Subtract _  -> illegal_format "SPASS don't support Substract expresion"
  | Cpure.Mult _      -> illegal_format "SPASS don't support Mult expresion"
  | Cpure.Div _       -> illegal_format "SPASS don't support Div expresion"
  | Cpure.Max _       -> illegal_format "SPASS don't support Max expresion"
  | Cpure.Min _       -> illegal_format "SPASS don't support Min expresion"
    (* bag expressions *)
  | Cpure.Bag _
  | Cpure.BagUnion _
  | Cpure.BagIntersect _
  | Cpure.BagDiff _    -> illegal_format "SPASS don't support Bag expresion"
  (* list expressions *)
  | Cpure.List _
  | Cpure.ListCons _
  | Cpure.ListHead _
  | Cpure.ListTail _
  | Cpure.ListLength _
  | Cpure.ListAppend _
  | Cpure.ListReverse _
  | Cpure.ArrayAt _    -> illegal_format "SPASS don't support List/Array expresion"

and spass_of_b_formula (bf : Cpure.b_formula) : string =
  match bf with
  | (pf, _) -> spass_of_p_formula pf

and spass_of_p_formula (pf : Cpure.p_formula) : string =
  match pf with
  | BConst (c, _)   -> if c then "true" else "false"
  | BVar (sv, _)    -> spass_of_spec_var sv
  | Lt _            -> illegal_format "SPASS don't support Lt p_formula"
  | Lte _           -> illegal_format "SPASS don't support Lte p_formula"
  | Gt _            -> illegal_format "SPASS don't support Gt p_formula"
  | Gte _           -> illegal_format "SPASS don't support Gte p_formula"
  | SubAnn _        -> illegal_format "SPASS don't support SubAnn p_formula"
  | Eq (e1, e2, _)  -> "equal(" ^ (spass_of_exp e1) ^ "," ^ (spass_of_exp e2) ^ ")"
  | Neq (e1, e2, _) -> "not(equal(" ^ (spass_of_exp e1) ^ "," ^ (spass_of_exp e2) ^ "))"
  | EqMax _         -> illegal_format "SPASS don't support EqMax p_formula"
  | EqMin _         -> illegal_format "SPASS don't support EqMin p_formula"
  (* bag formulas *)
  | BagIn _
  | BagNotIn _
  | BagSub _
  | BagMin _
  | BagMax _        -> illegal_format "SPASS don't support Bag p_formula"
  (* list formulas *)
  | ListIn _
  | ListNotIn _
  | ListAllN _
  | ListPerm _
  | RelForm _       -> illegal_format "SPASS don't support List p_formula"

and spass_of_formula f =
  match f with
  | BForm (b, _)         -> spass_of_b_formula b
  | And (f1, f2, _)      -> "and(" ^ (spass_of_formula f1) ^ ", " ^ (spass_of_formula f2) ^ ")"
  | Or (f1, f2, _, _)    -> "or(" ^ (spass_of_formula f1) ^ ", " ^ (spass_of_formula f2) ^ ")"
  | Not (f, _, _)        -> "not(" ^ (spass_of_formula f) ^ ")"
  | Forall (sv, f, _, _) -> "forall([" ^ (spass_of_spec_var sv) ^ "]," ^ (spass_of_formula f) ^ ")"
  | Exists (sv, f, _, _) -> "exists([" ^ (spass_of_spec_var sv) ^ "]," ^ (spass_of_formula f) ^ ")"

let spass_of_formula f =
  Debug.no_1 "spass_of_formula" !print_pure pr_id spass_of_formula f

(*************************************************************)
(* Check whether spass can handle the expression, formula... *)
let rec can_spass_handle_expression (exp: Cpure.exp) : bool =
  match exp with
  | Null _         -> true
  | Var _          -> true
  | IConst _       -> false
  | FConst _       -> false
  | AConst _       -> false
  (* arithmetic expressions *)
  | Add _
  | Subtract _
  | Mult _
  | Div _
  | Max _
  | Min _          -> false
  (* bag expressions *)
  | Bag _
  | BagUnion _
  | BagIntersect _
  | BagDiff _      -> false
  (* list expressions *)
  | List _
  | ListCons _
  | ListHead _
  | ListTail _
  | ListLength _
  | ListAppend _
  | ListReverse _
  | ArrayAt _      -> false

and can_spass_handle_p_formula (pf : Cpure.p_formula) : bool =
  match pf with
  | BConst _             -> true
  | BVar _               -> true
  | Lt _                 -> false
  | Lte _                -> false
  | Gt _                 -> false
  | Gte _                -> false
  | SubAnn (ex1, ex2, _) -> (can_spass_handle_expression ex1) && (can_spass_handle_expression ex2)
  | Eq (ex1, ex2, _)     -> (can_spass_handle_expression ex1) && (can_spass_handle_expression ex2)
  | Neq (ex1, ex2, _)    -> (can_spass_handle_expression ex1) && (can_spass_handle_expression ex2)
  | EqMax _              -> false
  | EqMin _              -> false
  (* bag formulars *)
  | BagIn _
  | BagNotIn _
  | BagSub _
  | BagMin _
  | BagMax _             -> false
  (* list formulas *)
  | ListIn _
  | ListNotIn _
  | ListAllN _
  | ListPerm _
  | RelForm _            -> false

and can_spass_handle_b_formula (bf : Cpure.b_formula) : bool =
  match bf with
  | (pf, _) -> can_spass_handle_p_formula pf

and can_spass_handle_formula (f: Cpure.formula) : bool =
  match f with
  | BForm (bf, _)       -> can_spass_handle_b_formula bf
  | And (f1, f2, _)     -> (can_spass_handle_formula f1) && (can_spass_handle_formula f2)
  | Or (f1, f2, _, _)   -> (can_spass_handle_formula f1) && (can_spass_handle_formula f2)
  | Not (f, _, _)       -> can_spass_handle_formula f
  | Forall (_, f, _, _) -> can_spass_handle_formula f
  | Exists (_, f, _, _) -> can_spass_handle_formula f

(***************************************************************
INTERACTION
**************************************************************)

type validity_t =
  | Valid     (* prover returns valid *)
  | Invalid   (* prover returns invalid *)
  | Unknown   (* prover returns unknown or there is an exeption *)
  | Aborted   (* prover returns an exceptions *)

type prover_output_t = {
  original_output_text: string list; (* original output of the prover *)
  validity_result: validity_t; (* validity information *)
}

let string_of_spass_output output =
  (String.concat "\n" output.original_output_text)

let rec collect_output chn accumulated_output : string list =
  let output =
    try
      let line = input_line chn in
      collect_output chn (accumulated_output @ [line])
    with End_of_file -> accumulated_output in
  output

(* read the output stream of SPASS prover, return (conclusion * reason)    *)
(* TODO: this function need to be optimized                                *)
let get_prover_result (output : string list) : validity_t =
  (* debug *)
  (* let _ = print_endline "** In functin get_prover_result:" in *)
  (* List.iter (fun x -> print_endline x) output; *)
  let rec is_start_with (subtext: string) (text: string) : bool =
  (
    let len = String.length subtext in
    try 
      if (String.sub text 0 len = subtext) then true
      else false
    with _ -> false
  ) in
  let conclusion_line = try List.find (is_start_with "SPASS beiseite:") output
                        with Not_found -> "Unknown" in
  (* debug *)
  (* let _ = print_endline ("-- get_prover_result: " ^ conclusion_line) in *)
  let validity =
    if (conclusion_line = "SPASS beiseite: Completion found.") then
      Invalid
    else if (conclusion_line = "SPASS beiseite: Proof found.") then
      Valid
    else
      Unknown in 
  validity

let get_answer (chn: in_channel) (input: string) : prover_output_t =
  (* debug *)
  (* let _ = print_endline "** In function get_answer" in *)
  let output = collect_output chn [] in
  (* let _ = print_endline "-- spass output: " in
  List.iter (fun x -> print_endline x) output; *)
  let prover_output = {
    original_output_text = output;
    validity_result = get_prover_result output;
  } in
  prover_output

let remove_file filename =
  try Sys.remove filename;
  with e -> ignore e

(* Global settings *)
let spass_timeout_limit = 15.0
let prover_process = ref { name = "SPASS";
                           pid = 0;
                           inchannel = stdin;
                           outchannel = stdout;
                           errchannel = stdin 
                          }

(***********)
let log_all_flag = ref false

let log_file = open_out ("allinput.spass")
let path_to_spass = "SPASS"
let prover_name = "SPASS"

let set_process (proc: Globals.prover_process_t) =
  prover_process := proc

(* Runs the specified prover and returns output *)
let check_problem (input: string) (timeout: float) : prover_output_t =
  (* debug *)
  (* let _ = print_endline "** In function Spass.check_problem" in *)
  let file_suffix = Random.int 1000000 in
  let infile = "/tmp/in" ^ (string_of_int file_suffix) ^ ".spass" in
  let _ = print_endline ("-- input: \n" ^ input) in 
  let out_stream = open_out infile in
  output_string out_stream input;
  close_out out_stream;
  let set_process proc = prover_process := proc in
  let fnc () =
    let _ = Procutils.PrvComms.start false stdout (prover_name, path_to_spass, [|path_to_spass; infile|]) set_process (fun () -> ()) in
    get_answer !prover_process.inchannel input in
  let res =
    try
      Procutils.PrvComms.maybe_raise_timeout fnc () timeout
    with _ -> ((* exception : return the safe result to ensure soundness *)
      Printexc.print_backtrace stdout;
      print_endline ("WARNING: Restarting prover due to timeout");
      Unix.kill !prover_process.pid 9;
      ignore (Unix.waitpid [] !prover_process.pid);
      { original_output_text = []; validity_result = Aborted; }
    ) in
  let _ = Procutils.PrvComms.stop false stdout !prover_process 0 9 (fun () -> ()) in
  remove_file infile;
  res

(* prelulde is used to log the input file of the prover *)
let prelude () =
  let finished = ref false in
  while not !finished do
    let line = input_line (!prover_process.inchannel) in
    (* let _ = print_endline line in *)
    (if !log_all_flag then
        output_string log_file ("[spass.ml]: >> " ^ line ^ "\nSpass is running\n") );
    if ((String.length line) = 0) then finished := true;
  done;
  ()

(***************************************************************
GENERATE SMT INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
**************************************************************)

(* spass: output for dfg format *)
let to_spass_dfg (ante: Cpure.formula) (conseq: Cpure.formula) (fvars: Cpure.spec_var list) : string =
  let dfg_description =
    ( "list_of_descriptions.\n"
      ^ "  name({*sleek-problem*}).\n"
      ^ "  author({*sleek*}).\n"
      ^ "  status(unknown).\n"
      ^ "  description({*This is an problem generated by sleek prover.*}).\n"
      ^ "end_of_list.\n\n") in
  let dfg_symbols =
    let create_constant (fvar : Cpure.spec_var) =
      "(" ^ (spass_of_spec_var fvar) ^ ", 0)" in
    let constants_list = List.map create_constant fvars in
    let constants_list = constants_list @ ["(NULL, 0)"] in
    let dfg_constants = String.concat ", " constants_list in
    ( "list_of_symbols.\n"
      ^ "  functions[" ^ dfg_constants ^ "].\n"
      ^ "end_of_list.\n\n") in
  let dfg_formulae_axioms =
    let ante_str = spass_of_formula ante in
    let axiom_label = "axiom1" in
    ( "list_of_formulae(axioms).\n"
      ^ "  formula(" ^ ante_str ^ ", " ^ axiom_label ^ ").\n"
      ^ "end_of_list.\n\n") in
  let dfg_formulae_conjectures =
    let conseq_str = spass_of_formula conseq in
    let conseq_label = "conjecture1" in
    ( "list_of_formulae(conjectures).\n"
      ^ "  formula(" ^ conseq_str ^ ", " ^ conseq_label ^ ").\n"
      ^ "end_of_list.\n\n") in
  let dfg_setting =
    ( "list_of_settings(SPASS).\n"
      ^ "{*\n"
      ^ "  set_flag(DocProof,0).\n"
      ^ "  set_flag(PProblem, 0).\n"
      ^ "  set_flag(PStatistic, 0).\n"
      ^ "*}\n"
      ^ "end_of_list.\n\n") in
  let result =
    ( "begin_problem(auto_generated_problem).\n\n"
      ^ dfg_description
      ^ dfg_symbols
      ^ dfg_formulae_axioms
      ^ dfg_formulae_conjectures
      ^ dfg_setting
      ^ "end_problem.") in
  result

let to_spass (ante : Cpure.formula) (conseq : Cpure.formula option) : string =
  (* debug *)
  (* let _ = print_endline "** In function to_spass:" in *)
  let conseq = match conseq with
    (* We don't have conseq part in is_sat checking *)
    | None   -> Cpure.mkFalse no_pos
    | Some f -> f
  in
  let ante_fv = Cpure.fv ante in
  let conseq_fv = Cpure.fv conseq in
  let all_fv = Gen.BList.remove_dups_eq (=) (ante_fv @ conseq_fv) in
  let res = to_spass_dfg ante conseq all_fv in
  (* let _ = print_endline ("-- Input problem in DFG format:\n" ^ res) in *)
  (* use for debug: print formula in Omega format *)
  (* let omega_temp_f = Cpure.mkOr (mkNot ante None no_pos) conseq None no_pos in
  let omega_ante = Omega.omega_of_formula ante in
  let omega_conseq = Omega.omega_of_formula conseq in
  let omega_pvars = Omega.get_vars_formula omega_temp_f in
  let omega_vstr = Omega.omega_of_var_list (Gen.BList.remove_dups_eq (=) omega_pvars) in
  let omega_formula  =  "complement {[" ^ omega_vstr ^ "] : (" ^ omega_ante ^ "  ==>  " ^ omega_conseq ^ ")}" ^ ";" ^ Gen.new_line_str in
  let omega_temp_str = Omega.omega_of_formula omega_temp_f in
  let omega_temp_formula  =  "complement {[" ^ omega_vstr ^ "] : (" ^ omega_temp_str ^ ")}" ^ ";" ^ Gen.new_line_str in
  let _ = print_endline ("-- Input problem in Omega format - omega_temp_str:\n" ^ omega_formula) in
  let _ = print_endline ("-- Input problem in Omega format - omega_temp_formula:\n" ^ omega_temp_formula) in *)
  res

(**************************************************************
MAIN INTERFACE : CHECKING IMPLICATION AND SATISFIABILITY
*************************************************************)

(**
* Test for validity
* To check the implication P -> Q, we check the satisfiability of
* P /\ not Q
* If it is satisfiable, then the original implication is false.
* If it is unsatisfiable, the original implication is true.
* We also consider unknown is the same as sat
*)

let rec spass_imply (ante : Cpure.formula) (conseq : Cpure.formula) timeout : bool =
  (* let _ = "** In function Spass.spass_imply" in *)
  let pr = !print_pure in
  let result = 
    Debug.no_2_loop "spass_imply" (pr_pair pr pr) string_of_float string_of_bool
    (fun _ _ -> spass_imply_x ante conseq timeout) (ante, conseq) timeout in
  (* let omega_result = Omega.imply ante conseq "" timeout in
  let _ = print_endline ("-- spass_imply result: " ^ (if result then "TRUE" else "FALSE")) in
  let _ = print_endline ("-- omega_imply result: " ^ (if omega_result then "TRUE" else "FALSE")) in *)
  result;
    

and spass_imply_x (ante : Cpure.formula) (conseq : Cpure.formula) timeout : bool =
  (* let _ = "** In function Spass.spass_imply_x" in *)
  let res, should_run_spass =
    if not ((can_spass_handle_formula ante) && (can_spass_handle_formula conseq)) then
      (* for debug *)
      (* let fomega_ante = Omega.omega_of_formula ante in
      let _ = print_endline ("can_spass_handle_formula ante:" ^ fomega_ante ^ ": " ^ 
              (if (can_spass_handle_formula ante) then "true" else "false")) in
      let fomega_conseq = Omega.omega_of_formula conseq in
      let _ = print_endline ("can_spass_handle_formula conseq:" ^ fomega_conseq^ ": " ^ 
              (if (can_spass_handle_formula conseq) then "true" else "false")) in *)
      try
        let _ = print_endline "-- use Omega.imply_..." in
        match (Omega.imply_with_check ante conseq "" timeout) with
        | None -> (false, true)
        | Some r -> (r, false)
      with _ -> (false, true) (* TrungTQ: Maybe BUG: in the exception case, it should return UNKNOWN *)
    else (false, true) in
  if (should_run_spass) then
    (* let _ = print_endline "-- use Spass.check_problem" in *)
    let spass_input = to_spass ante (Some conseq) in
    let validity = check_problem spass_input timeout in
    (* let prover_output = String.concat "\n" output.original_output_text in *)
    (* debug let _ = print_endline ("** prover output:" ^              *)
    (* prover_output) in                                               *)
    let res =
      match validity.validity_result with (* TrungTQ: may be bugs here *)
      | Valid -> true
      | Invalid -> false
      | Unknown -> false
      | Aborted -> false in
    res
  else
    res

let imply (ante: Cpure.formula) (conseq: Cpure.formula) (timeout: float) : bool =
  (* let _ = print_endline "** In function Spass.imply:" in *)
  let result = spass_imply ante conseq timeout in
  (* let _ = print_endline ("-- imply result: " ^ (if result then "true" else "false" )) in *)
  result

let imply_with_check (ante : Cpure.formula) (conseq : Cpure.formula) (imp_no : string) (timeout: float) : bool option =
  (* let _ = print_endline "** In function Spass.imply_with_check:" in *)
  Cpure.do_with_check2 "" (fun a c -> imply a c timeout) ante conseq

let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let _ = print_endline "** In function Spass.imply:" in *)
  try
    let result = imply ante conseq timeout in
    result
  with Illegal_Prover_Format s -> (
    print_endline ("\nWARNING : Illegal_Prover_Format for :"^s);
    print_endline ("Apply z3.imply on ante Formula :"^(!print_pure ante));
    print_endline ("and conseq Formula :"^(!print_pure conseq));
    flush stdout;
    failwith s
  )

let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let _ = print_endline "** In function Spass.imply:" in *)
  Debug.no_1_loop "smt.imply" string_of_float string_of_bool
    (fun _ -> imply ante conseq timeout) timeout

(**
* Test for satisfiability
* We also consider unknown is the same as sat
*)

let spass_is_sat (f : Cpure.formula) (sat_no : string) timeout : bool =
  (* debug *)
  (* let _ = print_endline "** In function Spass.spass_is_sat:" in *)
  (* anything that SPASS counldn't handle will be transfer to Omega *)
  let res, should_run_spass =
    if not (can_spass_handle_formula f) then
      (* for debug *)
      (* let fomega = Omega.omega_of_formula f in
      let _ = print_endline ("can_spass_handle_formula f: " ^ fomega ^ ": " ^ 
              (if (can_spass_handle_formula f) then "true" else "false")) in
      let _ = print_endline "-- use Omega.is_sat..." in *)
      try
        let optr = (Omega.is_sat_with_check f sat_no) in
        match optr with
        | Some r -> (r, false)
        | None -> (true, false)
      with _ -> (true, false) (* TrungTQ: Maybe BUG: Why res = true in exception case? It should return UNKNOWN *)
    else (false, true) in
  if (should_run_spass) then
    (* let _ = print_endline "-- use Spass.check_problem..." in *)
    (* to check sat of f, spass check the validity of negative(f) or (f => None) *)
    let spass_input = to_spass f None in
    let validity = check_problem spass_input timeout in
    let res =
      match validity.validity_result with
      | Invalid -> true      (* if neg(f) invalid ==> f sat *) 
      | Valid   -> false     (* if neg(f) valid   ==> f unsat *)
      | _       -> false in  (* other, consider f unsat *)
    res
  else
    res

(* spass *)
let spass_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  spass_is_sat f sat_no spass_timeout_limit

(* spass *)
let spass_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  let pr = !print_pure in
  let result = Debug.no_1 "spass_is_sat" pr string_of_bool (fun _ -> spass_is_sat f sat_no) f in
  (* let omega_result = Omega.is_sat f sat_no in
  let _ = print_endline ("-- spass_is_sat result: " ^ (if result then "TRUE" else "FALSE")) in
  let _ = print_endline ("-- Omega.is_sat result: " ^ (if omega_result then "TRUE" else "FALSE")) in *)
  result

(* see imply *)
let is_sat (f: Cpure.formula) (sat_no: string) : bool =
  (* debug *)
  (* let _ = print_endline "** In function Spass.is_sat: " in *)
  let result = spass_is_sat f sat_no in
  (* let _ = print_endline ("-- is_sat result: " ^ (if result then "true" else "false")) in *)
  result

let is_sat_with_check (pe : Cpure.formula) sat_no : bool option =
  Cpure.do_with_check "" (fun x -> is_sat x sat_no) pe

(* let is_sat f sat_no = Debug.loop_2_no "is_sat" (!print_pure) (fun x->x) *)
(* string_of_bool is_sat f sat_no                                          *)

let is_sat (pe : Cpure.formula) (sat_no: string) : bool =
  (* let _ = print_endline "** In function Spass.is_sat: " in *)
  try
    is_sat pe sat_no;
  with Illegal_Prover_Format s -> (
    print_endline ("\nWARNING : Illegal_Prover_Format for :"^s);
    print_endline ("Apply Spass.is_sat on formula :"^(!print_pure pe));
    flush stdout;
    failwith s
  )

(**
* To be implemented
*)
let simplify (f: Cpure.formula) : Cpure.formula =
  (* debug *)
  (* let _ = print_endline "** In function Spass.simplify" in *)
  try (Omega.simplify f) with _ -> f

let simplify (pe : Cpure.formula) : Cpure.formula =
  match (Cpure.do_with_check "" simplify pe) with
  | None -> pe
  | Some f -> f

let hull (f: Cpure.formula) : Cpure.formula = f

let pairwisecheck (f: Cpure.formula): Cpure.formula = f