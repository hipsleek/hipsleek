#include "xdebug.cppo"
open Globals
open VarGen
open GlobProver
open Gen.Basic
open Cpure

module StringSet = Set.Make(String)

(* Global settings *)
let spass_timeout_limit = 15.0
let spass_process = ref { name = "SPASS";
                          pid = 0;
                          inchannel = stdin;
                          outchannel = stdout;
                          errchannel = stdin 
                        }

let test_number = ref 0
let last_test_number = ref 0
let spass_restart_interval = ref (-1)
let log_all_flag = ref false
let is_spass_running = ref false
let in_timeout = ref 15.0 (* default timeout is 15 seconds *)
let spass_call_count: int ref = ref 0
let log_file = open_log_out ("allinput.spass")
let spass_path = "SPASS-MOD"
let spass_name = "SPASS-MOD"
let spass_input_format = "dfg"   (* valid value is: "dfg" or "tptp" *)
let spass_input_mode = "stdin"    (* valid value is: "file" or "stdin" *) 


(***************************************************************
   TRANSLATE CPURE FORMULA TO PROBLEM IN DFG FORMAT
 **************************************************************)

let spass_dfg_of_spec_var sv =
  (Cpure.name_of_spec_var sv) ^ (if Cpure.is_primed sv then "_primed" else "")

(* return exp in string * list of functions in string * list of predicates in string *)
let rec spass_dfg_of_exp (e0 : Cpure.exp) : (string * string list * string list) =
  match e0 with
  | Cpure.Null _      -> ("NULL", ["NULL"], [])
  | Cpure.Var (sv, _) -> let func = spass_dfg_of_spec_var sv in (func, [func], [])
  (* illegal_format "SPASS don't support Var expresion" *)
  | Cpure.IConst _    -> illegal_format "SPASS don't support IConst expresion"
  | Cpure.FConst _    -> illegal_format "SPASS don't support FConst expresion"
  | Cpure.AConst _    -> illegal_format "SPASS don't support AConst expresion"
  | Cpure.Tsconst _   -> illegal_format "SPASS don't support Tsconst expresion"
  | Cpure.NegInfConst _
  | Cpure.InfConst _ -> illegal_format "SPASS don't support infconst expresion"
  | Cpure.Bptriple _   -> illegal_format "SPASS don't support Bptriple expresion"
  | Cpure.Tup2 _   -> illegal_format "SPASS don't support Tup2 expresion"
  | Cpure.Add _       -> illegal_format "SPASS don't support Add expresion"
  | Cpure.Level _ -> illegal_format ("z3.smt_of_exp: level should not appear here")
  | Cpure.Subtract _  -> illegal_format "SPASS don't support Substract expresion"
  | Cpure.Mult _      -> illegal_format "SPASS don't support Mult expresion"
  | Cpure.Div _       -> illegal_format "SPASS don't support Div expresion"
  | Cpure.Max _       -> illegal_format "SPASS don't support Max expresion"
  | Cpure.Min _       -> illegal_format "SPASS don't support Min expresion"
  | Cpure.TypeCast _       -> illegal_format "SPASS don't support TypeCast expresion"
  (* bag expressions *)
  | Cpure.Bag _
  | Cpure.BagUnion _
  | Cpure.BagIntersect _
  | Cpure.BagDiff _   -> illegal_format "SPASS don't support Bag expresion"
  (* list expressions *)
  | Cpure.List _
  | Cpure.ListCons _
  | Cpure.ListHead _
  | Cpure.ListTail _
  | Cpure.ListLength _
  | Cpure.ListAppend _
  | Cpure.ListReverse _ -> illegal_format "SPASS don't support List expresion"
  (* array expressions *)
  | Cpure.ArrayAt _   -> illegal_format "SPASS don't support Array expresion"
  (* other *)
  | Cpure.Func _      -> illegal_format "SPASS don't support Func expresion"
  | Cpure.Template _      -> illegal_format "SPASS don't support Template expresion"

(* return b_formula in string * list of functions in string * list of predicates in string *)
and spass_dfg_of_b_formula (bf : Cpure.b_formula) : (string * string list * string list) =
  match bf with
  | (pf, _) -> spass_dfg_of_p_formula pf

(* return p_formula in string * list of functions in string * list of predicates in string *)
and spass_dfg_of_p_formula (pf : Cpure.p_formula) : (string * string list * string list) =
  match pf with
  | Frm (sv, _)    -> (
      let pred = spass_dfg_of_spec_var sv in
      (pred, [], [pred]) 
    ) 
  | LexVar _        -> illegal_format "SPASS don't support LexVar p_formula"
  | BConst (c, _)   -> if c then ("true", [], []) else ("false", [], [])
  | BVar (sv, _)    -> (
      let pred = spass_dfg_of_spec_var sv in
      (pred, [], [pred]) 
    ) 
  | Lt _            -> illegal_format "SPASS don't support Lt p_formula"
  | Lte _           -> illegal_format "SPASS don't support Lte p_formula"
  | Gt _            -> illegal_format "SPASS don't support Gt p_formula"
  | Gte _           -> illegal_format "SPASS don't support Gte p_formula"
  | SubAnn _        -> illegal_format "SPASS don't support SubAnn p_formula"
  | Eq (e1, e2, _)  -> (
      let (s1, func_list1, pred_list1) = spass_dfg_of_exp e1 in
      let (s2, func_list2, pred_list2) = spass_dfg_of_exp e2 in
      let s = "equal(" ^ s1 ^ "," ^ s2 ^ ")" in 
      let func_list = Gen.BList.remove_dups_eq (=) func_list1 @ func_list2 in
      let pred_list = Gen.BList.remove_dups_eq (=) pred_list1 @ pred_list2 in
      (s, func_list, pred_list)
    )
  | Neq (e1, e2, _) -> (
      let (s1, func_list1, pred_list1) = spass_dfg_of_exp e1 in
      let (s2, func_list2, pred_list2) = spass_dfg_of_exp e2 in
      let s = "not(equal(" ^ s1 ^ "," ^ s2 ^ "))" in 
      let func_list = Gen.BList.remove_dups_eq (=) func_list1 @ func_list2 in
      let pred_list = Gen.BList.remove_dups_eq (=) pred_list1 @ pred_list2 in
      (s, func_list, pred_list)
    ) 
  | EqMax _         -> illegal_format "SPASS don't support EqMax p_formula"
  | EqMin _         -> illegal_format "SPASS don't support EqMin p_formula"
  (* | VarPerm _       -> illegal_format "SPASS don't support VarPerm p_formula" *)
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
  | ImmRel _
  | RelForm _       -> illegal_format "SPASS don't support List p_formula"
  | XPure _ -> Error.report_no_pattern()

(* return formula in string * list of functions in string * list of predicates in string *)
and spass_dfg_of_formula f : (string * string list * string list) =
  match f with
  | BForm (b, _)         -> spass_dfg_of_b_formula b
  | AndList _ -> Gen.report_error no_pos "spass.ml: encountered AndList, should have been already handled"
  | And (f1, f2, _)      -> (
      let (s1, func_list1, pred_list1) = spass_dfg_of_formula f1 in
      let (s2, func_list2, pred_list2) = spass_dfg_of_formula f2 in
      let s = "and(" ^ s1 ^ ", " ^ s2 ^ ")" in
      let func_list = Gen.BList.remove_dups_eq (=) func_list1 @ func_list2 in
      let pred_list = Gen.BList.remove_dups_eq (=) pred_list1 @ pred_list2 in
      (s, func_list, pred_list)
    )
  | Or (f1, f2, _, _)    -> (
      let (s1, func_list1, pred_list1) = spass_dfg_of_formula f1 in
      let (s2, func_list2, pred_list2) = spass_dfg_of_formula f2 in
      let s = "or(" ^ s1 ^ ", " ^ s2 ^ ")" in
      let func_list = Gen.BList.remove_dups_eq (=) func_list1 @ func_list2 in
      let pred_list = Gen.BList.remove_dups_eq (=) pred_list1 @ pred_list2 in
      (s, func_list, pred_list)
    ) 
  | Not (f, _, _)        -> (
      let (s, func_list, pred_list) = spass_dfg_of_formula f in
      let new_s = "not(" ^ s ^ ")" in 
      (new_s, func_list, pred_list)
    ) 
  | Forall (sv, f, _, _) -> (
      let (s, func_list, pred_list) = spass_dfg_of_formula f in
      let local_sv = spass_dfg_of_spec_var sv in
      let new_s = "forall([" ^ local_sv ^ "]," ^ s ^ ")" in
      let new_func_list = Gen.BList.remove_elem_eq (=) local_sv func_list in 
      let new_pred_list = Gen.BList.remove_elem_eq (=) local_sv pred_list in
      (new_s, new_func_list, new_pred_list)
    )
  | Exists (sv, f, _, _) -> (
      let (s, func_list, pred_list) = spass_dfg_of_formula f in
      let local_sv = spass_dfg_of_spec_var sv in
      let new_s = "exists([" ^ local_sv ^ "]," ^ s ^ ")" in
      let new_func_list = Gen.BList.remove_elem_eq (=) local_sv func_list in 
      let new_pred_list = Gen.BList.remove_elem_eq (=) local_sv pred_list in
      (new_s, new_func_list, new_pred_list)
    ) 

(* let spass_dfg_of_formula f = *)
(*   Debug.no_1 "spass_of_formula" Cprinter.string_of_pure_formula pr_id spass_dfg_of_formula f *)

(***************************************************************
   TRANSLATE CPURE FORMULA TO PROBLEM IN TPTP FORMAT
 **************************************************************)

let spass_tptp_of_spec_var sv =
  (Cpure.name_of_spec_var sv) ^ (if Cpure.is_primed sv then "_primed" else "")

let rec spass_tptp_of_exp (e0 : Cpure.exp) : string =
  match e0 with
  | Cpure.Null _      -> "ssNULL"
  | Cpure.Var (sv, _) -> spass_tptp_of_spec_var sv
  | Cpure.IConst _    -> illegal_format "SPASS don't support IConst expresion"
  | Cpure.FConst _    -> illegal_format "SPASS don't support FConst expresion"
  | Cpure.AConst _    -> illegal_format "SPASS don't support AConst expresion"
  | Cpure.Tsconst _   -> illegal_format "SPASS don't support Tsconst expresion"
  | Cpure.NegInfConst _
  | Cpure.InfConst _ -> illegal_format "SPASS don't support infconst expresion"
  | Cpure.Bptriple _   -> illegal_format "SPASS don't support Bptriple expresion"
  | Cpure.Tup2 _   -> illegal_format "SPASS don't support Tup2 expresion"
  | Cpure.Add _       -> illegal_format "SPASS don't support Add expresion"
  | Cpure.Subtract _  -> illegal_format "SPASS don't support Substract expresion"
  | Cpure.Mult _      -> illegal_format "SPASS don't support Mult expresion"
  | Cpure.Div _       -> illegal_format "SPASS don't support Div expresion"
  | Cpure.Max _       -> illegal_format "SPASS don't support Max expresion"
  | Cpure.Min _       -> illegal_format "SPASS don't support Min expresion"
  | Cpure.TypeCast _       -> illegal_format "SPASS don't support TypeCast expresion"
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
  | Cpure.ListReverse _ -> illegal_format "SPASS don't support List expresion"
  (* array expressions *)
  | Cpure.ArrayAt _    -> illegal_format "SPASS don't support Array expresion"
  (* other *)
  | Cpure.Func _       -> illegal_format "SPASS don't support Func expresion"
  | Cpure.Template _       -> illegal_format "SPASS don't support Template expresion"
  | Cpure.Level _ -> Error.report_no_pattern()

and spass_tptp_of_b_formula (bf : Cpure.b_formula) : string =
  match bf with
  | (pf, _) -> spass_tptp_of_p_formula pf

and spass_tptp_of_p_formula (pf : Cpure.p_formula) : string =
  match pf with
  | Frm (sv, _)    -> spass_tptp_of_spec_var sv
  | LexVar _        -> illegal_format "SPASS don't support LexVar p_formula"
  | BConst (c, _)   -> if c then "$true" else "$false"
  | BVar (sv, _)    -> spass_tptp_of_spec_var sv
  | Lt _            -> illegal_format "SPASS don't support Lt p_formula"
  | Lte _           -> illegal_format "SPASS don't support Lte p_formula"
  | Gt _            -> illegal_format "SPASS don't support Gt p_formula"
  | Gte _           -> illegal_format "SPASS don't support Gte p_formula"
  | SubAnn _        -> illegal_format "SPASS don't support SubAnn p_formula"
  | Eq (e1, e2, _)  -> "(" ^ (spass_tptp_of_exp e1) ^ " = " ^ (spass_tptp_of_exp e2) ^ ")"
  | Neq (e1, e2, _) -> "(" ^ (spass_tptp_of_exp e1) ^ " != " ^ (spass_tptp_of_exp e2) ^ ")"
  | EqMax _         -> illegal_format "SPASS don't support EqMax p_formula"
  | EqMin _         -> illegal_format "SPASS don't support EqMin p_formula"
  (* | VarPerm _       -> illegal_format "SPASS don't support VarPerm p_formula" *)
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
  | ImmRel _
  | RelForm _       -> illegal_format "SPASS don't support List p_formula"
  | XPure _ -> Error.report_no_pattern()

and spass_tptp_of_formula f =
  match f with
  | BForm (b, _)         -> spass_tptp_of_b_formula b
  | And (f1, f2, _)      -> "(" ^ (spass_tptp_of_formula f1) ^ " & " ^ (spass_tptp_of_formula f2) ^ ")"
  | AndList _            -> Gen.report_error no_pos "[spass.ml] handle AndList later"
  | Or (f1, f2, _, _)    -> "(" ^ (spass_tptp_of_formula f1) ^ " | " ^ (spass_tptp_of_formula f2) ^ ")"
  | Not (f, _, _)        -> "~ " ^ (spass_tptp_of_formula f)
  | Forall (sv, f, _, _) -> "( ! [" ^ (spass_tptp_of_spec_var sv) ^ "] : " ^ (spass_tptp_of_formula f) ^ ")"
  | Exists (sv, f, _, _) -> "( ? [" ^ (spass_tptp_of_spec_var sv) ^ "] : " ^ (spass_tptp_of_formula f) ^ ")"

let spass_tptp_of_formula f =
  Debug.no_1 "spass_of_formula" Cprinter.string_of_pure_formula pr_id spass_tptp_of_formula f

(*************************************************************)
(* Check whether spass can handle the expression, formula... *)
let rec can_spass_handle_expression (exp: Cpure.exp) : bool =
  match exp with
  | Cpure.Null _         -> true
  | Cpure.Var _          -> true
  | Cpure.IConst _       -> false
  | Cpure.FConst _       -> false
  | Cpure.AConst _       -> false
  | Cpure.Tsconst _      -> false
  | Cpure.NegInfConst _
  | Cpure.InfConst _ -> false
  (* arithmetic expressions *)
  | Cpure.Add _
  | Cpure.Subtract _
  | Cpure.Mult _
  | Cpure.Div _
  | Cpure.Max _
  | Cpure.Min _
  | Cpure.TypeCast _     -> false
  (* bag expressions *)
  | Cpure.Bag _
  | Cpure.BagUnion _
  | Cpure.BagIntersect _
  | Cpure.BagDiff _      -> false
  (* list expressions *)
  | Cpure.List _
  | Cpure.ListCons _
  | Cpure.ListHead _
  | Cpure.ListTail _
  | Cpure.ListLength _
  | Cpure.ListAppend _
  | Cpure.ListReverse _  -> false
  (* array expressions *)
  | Cpure.ArrayAt _      -> false
  | Cpure.Template _ -> false
  | Cpure.Func (sv, exp_list, _) -> List.for_all (fun e -> can_spass_handle_expression e) exp_list
  | Cpure.Level _
  | Cpure.Tup2 _      -> Error.report_no_pattern();
  | Cpure.Bptriple _      -> Error.report_no_pattern();


and can_spass_handle_p_formula (pf : Cpure.p_formula) : bool =
  match pf with
  | Frm _               -> false
  | LexVar _             -> false
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
  (* | VarPerm _            -> false *)
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
  | ImmRel _
  | RelForm _            -> false
  | XPure _ -> Error.report_no_pattern()

and can_spass_handle_b_formula (bf : Cpure.b_formula) : bool =
  match bf with
  | (pf, _) -> can_spass_handle_p_formula pf

and can_spass_handle_formula (f: Cpure.formula) : bool =
  match f with
  | BForm (bf, _)       -> can_spass_handle_b_formula bf
  | And (f1, f2, _)     -> (can_spass_handle_formula f1) && (can_spass_handle_formula f2)
  | AndList _           -> Gen.report_error no_pos "[spass.ml] handle AndList later"
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

let string_of_prover_validity_output (output: prover_output_t) =
  match output.validity_result with
  | Valid -> "Valid"
  | Invalid -> "Invalid"
  | Unknown -> "Unknown"
  | Aborted -> "Aborted"

let string_of_spass_output output =
  (String.concat "\n" output.original_output_text)

(* collect the output information of a process
   return : a string list of output and running state of process: "true" if still running, otherwise "false" *)
let rec collect_output (chn: in_channel) (accumulated_output: string list) : (string list * bool) =
  try
    let line = input_line chn in
    (* let () = print_endline ("  -- output: " ^ line) in *)
    if line = "---SPASS-MOD-STOP---" then
      (accumulated_output, true)
    else
      collect_output chn (accumulated_output @ [line])
  with 
  | End_of_file ->  (accumulated_output, false)

(* read the output stream of SPASS prover, return (conclusion * reason)    *)
(* TODO: this function need to be optimized                                *)
let get_prover_result (output : string list) : validity_t =
  (* debug *)
  (* let () = print_endline "** In functin get_prover_result:" in *)
  (* List.iter (fun x -> print_endline x) output; *)
  let rec is_start_with (subtext: string) (text: string) : bool =
    let len = String.length subtext in
    try 
      if (String.sub text 0 len = subtext) then true
      else false
    with _ -> false in
  let conclusion_line = try List.find (is_start_with "SPASS beiseite:") output
    with Not_found -> "Unknown" in
  (* debug *)
  (* let () = print_endline ("-- get_prover_result: " ^ conclusion_line) in *)
  let validity =
    if (conclusion_line = "SPASS beiseite: Completion found.") then
      Invalid
    else if (conclusion_line = "SPASS beiseite: Proof found.") then
      Valid
    else
      Unknown in 
  validity

(* output:  - prover_output 
            - the running status of prover: true if running, otherwise false *)
let get_answer (chn: in_channel) : (prover_output_t * bool)=
  let (output, running_state) = collect_output chn [] in
  let prover_output = {
    original_output_text = output;
    validity_result = get_prover_result output;
  } in
  (prover_output, running_state)

let remove_file filename =
  try Sys.remove filename;
  with e -> ignore e

let set_process (proc: prover_process_t) =
  spass_process := proc

let start () =
  if not !is_spass_running then (
    print_endline_quiet ("Starting SPASS... \n");
    last_test_number := !test_number;
    let prelude () = () in
    if (spass_input_format = "dfg") then (
      Procutils.PrvComms.start !log_all_flag log_file (spass_name, spass_path, [|spass_path; "-Stdin=1"|]) set_process prelude;
      is_spass_running := true;
    )
    else (
      Procutils.PrvComms.start !log_all_flag log_file (spass_name, spass_path, [|spass_path; "-Stdin=1"; "-TPTP"|]) set_process prelude;
      is_spass_running := true;
    )
  )

(* stop SPASS system *)
let stop () =
  if !is_spass_running then (
    let num_tasks = !test_number - !last_test_number in
    print_string_if !Globals.enable_count_stats ("Stop SPASS... " ^ (string_of_int !spass_call_count) ^ " invocations "); flush stdout;
    let () = Procutils.PrvComms.stop !log_all_flag log_file !spass_process num_tasks Sys.sigkill (fun () -> ()) in
    is_spass_running := false;
  )
  else Debug.info_pprint "SPASS is not running" no_pos

(* restart Omega system *)
let restart reason =
  if !is_spass_running then (
    let () = print_string_if !Globals.enable_count_stats (reason ^ " Restarting SPASS after ... " ^ (string_of_int !spass_call_count) ^ " invocations ") in
    Procutils.PrvComms.restart !log_all_flag log_file reason "SPASS" start stop
  )
  else (
    let () = print_string_if !Globals.enable_count_stats (reason ^ " not restarting SPASS ... " ^ (string_of_int !spass_call_count) ^ " invocations ") in 
    start ()
  )

(* Runs the specified prover and returns output *)
let check_problem_through_file (input: string) (timeout: float) : prover_output_t =
  (* debug *)
  (* let () = print_endline "** In function Spass.check_problem" in *)
  let file_suffix = Random.int 1000000 in
  let infile = "/tmp/in" ^ (string_of_int file_suffix) ^ ".spass" in
  (* let () = print_endline ("-- input: \n" ^ input) in *) 
  let out_stream = open_out infile in
  output_string out_stream input;
  close_out out_stream;
  let set_process proc = spass_process := proc in
  let fnc () =
    if (spass_input_format = "dfg") then (
      Procutils.PrvComms.start false stdout (spass_name, spass_path, [|spass_path; infile|]) set_process (fun () -> ());
      spass_call_count := !spass_call_count + 1;
      let (prover_output, running_state) = get_answer !spass_process.inchannel in
      is_spass_running := running_state;
      prover_output;
    )
    else if (spass_input_format = "tptp") then (
      Procutils.PrvComms.start false stdout (spass_name, spass_path, [|spass_path; "-TPTP"; "-DocProof=0"; "-PProblem=0"; "-PStatistic=0"; infile|]) set_process (fun () -> ());
      spass_call_count := !spass_call_count + 1;
      let (prover_output, running_state) = get_answer !spass_process.inchannel in
      is_spass_running := running_state;
      prover_output;
    )
    else illegal_format "[spass.ml] The value of spass_input_format is invalid!" in
  let res =
    if not (!dis_provers_timeout) then
      try
        let res = Procutils.PrvComms.maybe_raise_timeout fnc () timeout in
        res
      with _ -> (
          print_backtrace_quiet ();
          print_endline_quiet ("WARNING: Restarting prover due to timeout");
          Unix.kill !spass_process.pid 9;
          ignore (Unix.waitpid [] !spass_process.pid);
          { original_output_text = []; validity_result = Aborted; }
        ) 
    else 
      try fnc ()
      with exc -> 
        restart "Restarting SPASS because of timeout.";
        if !Omega.is_omega_running then Omega.restart "Restarting Omega because of timeout.";
        (* failwith "spass timeout"; *)
        raise exc
  in
  let () = Procutils.PrvComms.stop false stdout !spass_process 0 9 (fun () -> ()) in
  remove_file infile;
  res

let check_problem_through_file (input: string) (timeout: float) : prover_output_t =
  Debug.no_1 "check_problem_through_file"
    (fun s -> s) string_of_prover_validity_output
    (fun f -> check_problem_through_file f timeout) input

(* Runs the specified prover and returns output *)
let check_problem_through_stdin (input: string) (timeout: float) : prover_output_t =
  (* debug *)
  (*let () = print_endline "** In function Spass.check_problem_through_stdin" in 
    let () = print_endline ("  -- input: \n" ^ input) in*)
  if not !is_spass_running then (
    (*let () = print_endline "  -- start SPASS" in*)
    start ()
  )
  else if (!spass_call_count = !spass_restart_interval) then (
    (*let () = print_endline "  -- restart SPASS" in
      restart("Regularly restart:1 ");*)
    spass_call_count := 0;
  );
  (*let () = print_endline (" -- spass_process_pid: " ^ string_of_int(!spass_process.pid)) in*)
  let fnc f =
    output_string (!spass_process.outchannel) f;
    flush (!spass_process.outchannel);
    let () = incr spass_call_count in
    let (prover_output, running_state) = get_answer !spass_process.inchannel in
    is_spass_running := running_state;
    prover_output in
  let res =
    if not (!dis_provers_timeout) then
      try
        let res = Procutils.PrvComms.maybe_raise_timeout fnc input timeout in
        res
      with 
      | _ -> (
          print_backtrace_quiet ();
          print_endline_quiet ("WARNING: Restarting prover due to timeout");
          Unix.kill !spass_process.pid 9;
          ignore (Unix.waitpid [] !spass_process.pid);
          { original_output_text = []; validity_result = Aborted; }
        ) 
    else 
      try fnc input
      with
      | Procutils.PrvComms.Timeout as exc ->
        restart "Restarting SPASS because of timeout.";
        if !Omega.is_omega_running then Omega.restart "Restarting Omega because of timeout.";
        (* failwith "spass timeout"; *)
        raise exc
  in res

let check_problem_through_stdin (input: string) (timeout: float) : prover_output_t =
  Debug.no_1 "check_problem_through_stdin"
    (fun s -> s) string_of_prover_validity_output
    (fun f -> check_problem_through_stdin f timeout) input
;;
(***************************************************************
   GENERATE SMT INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
 **************************************************************)

(* spass: output for dfg format *)
let to_spass_dfg (ante: Cpure.formula) (conseq: Cpure.formula): string =
  let (ante_str, func_list1, pred_list1) = spass_dfg_of_formula ante in
  let (conseq_str, func_list2, pred_list2) = spass_dfg_of_formula conseq in
  let func_list = Gen.BList.remove_dups_eq (=) (func_list1 @ func_list2) in
  let pred_list = Gen.BList.remove_dups_eq (=) (pred_list1 @ pred_list2) in
  let dfg_description =
    ( "list_of_descriptions.\n"
      ^ "  name({*sleek-problem*}).\n"
      ^ "  author({*sleek*}).\n"
      ^ "  status(unknown).\n"
      ^ "  description({*This is an problem generated by sleek prover.*}).\n"
      ^ "end_of_list.\n\n") in
  let dfg_symbols =
    let create_symbol (sym : string) : string = "(" ^ sym ^ ", 0)" in
    let func_list = List.map create_symbol func_list in
    let dfg_func = String.concat ", " func_list in
    let pred_list = List.map create_symbol pred_list in
    let dfg_pred = String.concat ", " pred_list in
    ( "list_of_symbols.\n"
      ^ (if dfg_func <> "" then "  functions[" ^ dfg_func ^ "].\n" else "")
      ^ (if dfg_pred <> "" then "  predicates[" ^ dfg_pred ^ "].\n" else "")
      ^ "end_of_list.\n\n") in
  let dfg_formulae_axioms =
    let axiom_label = "axiom1" in
    ( "list_of_formulae(axioms).\n"
      ^ "  formula(" ^ ante_str ^ ", " ^ axiom_label ^ ").\n"
      ^ "end_of_list.\n\n") in
  let dfg_formulae_conjectures =
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
      ^ "end_problem.\n\n") in
  result

let to_spass_tptp (ante: Cpure.formula) (conseq: Cpure.formula) : string =
  let fof_ante = "fof(ante, axiom, (" ^ (spass_tptp_of_formula ante) ^ ") ).\n" in
  let fof_conseq = "fof(conseq, conjecture, (" ^ (spass_tptp_of_formula conseq) ^ ") ).\n" in
  let result = fof_ante ^ "\n" ^ fof_conseq in
  result

let to_spass (ante : Cpure.formula) (conseq : Cpure.formula option) : string =
  (* debug *)
  (* let () = print_endline "** In function to_spass:" in *)
  let conseq = match conseq with
    (* We don't have conseq part in is_sat checking *)
    | None   -> Cpure.mkFalse no_pos
    | Some f -> f
  in
  let res = 
    if (spass_input_format = "dfg") then (
      (* if sending problem in DFG format to SPASS *)
      let dfg_res = to_spass_dfg ante conseq
      (* let () = print_endline ("-- Input problem in DFG format:\n" ^ dfg_res) in *)
      in dfg_res
    ) 
    else if (spass_input_format = "tptp") then (
      (* if sending problem in TPTP format to SPASS *)
      let tptp_res = to_spass_tptp ante conseq in
      (* let () = print_endline ("-- Input problem in TPTP format:\n" ^ tptp_res) in *)
      tptp_res
    ) 
    else illegal_format "[spass.ml] The value of spass_input_format is invalid!" in

  (* use for debug: print formula in Omega format *)
  (* let omega_temp_f = Cpure.mkOr (mkNot ante None no_pos) conseq None no_pos in
     let omega_ante = x_add Omega.omega_of_formula ante in
     let omega_conseq = x_add Omega.omega_of_formula conseq in
     let omega_pvars = Omega.get_vars_formula omega_temp_f in
     let omega_vstr = Omega.omega_of_var_list (Gen.BList.remove_dups_eq (=) omega_pvars) in
     let omega_formula  =  "complement {[" ^ omega_vstr ^ "] : (" ^ omega_ante ^ "  ==>  " ^ omega_conseq ^ ")}" ^ ";" ^ Gen.new_line_str in
     let omega_temp_str = x_add Omega.omega_of_formula omega_temp_f in
     let omega_temp_formula  =  "complement {[" ^ omega_vstr ^ "] : (" ^ omega_temp_str ^ ")}" ^ ";" ^ Gen.new_line_str in
     let () = print_endline ("-- Input problem in Omega format - omega_temp_str:\n" ^ omega_formula) in
     let () = print_endline ("-- Input problem in Omega format - omega_temp_formula:\n" ^ omega_temp_formula) in *)
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
  (* let () = "** In function Spass.spass_imply" in *)
  let pr = Cprinter.string_of_pure_formula in
  let result = 
    Debug.no_2(* _loop *) "spass_imply" (pr_pair pr pr) string_of_float string_of_bool
      (fun _ _ -> spass_imply_x ante conseq timeout) (ante, conseq) timeout in
  (* let omega_result = Omega.imply ante conseq "" timeout in
     let () = print_endline ("-- spass_imply result: " ^ (if result then "TRUE" else "FALSE")) in
     let () = print_endline ("-- omega_imply result: " ^ (if omega_result then "TRUE" else "FALSE")) in *)
  result;


and spass_imply_x (ante : Cpure.formula) (conseq : Cpure.formula) timeout : bool =
  (* let () = "** In function Spass.spass_imply_x" in *)
  let res, should_run_spass =
    if not ((can_spass_handle_formula ante) && (can_spass_handle_formula conseq)) then
      (* for debug *)
      (* let fomega_ante = x_add Omega.omega_of_formula ante in
         let () = print_endline ("can_spass_handle_formula ante:" ^ fomega_ante ^ ": " ^ 
              (if (can_spass_handle_formula ante) then "true" else "false")) in
         let fomega_conseq = x_add Omega.omega_of_formula conseq in
         let () = print_endline ("can_spass_handle_formula conseq:" ^ fomega_conseq^ ": " ^ 
              (if (can_spass_handle_formula conseq) then "true" else "false")) in *)
      try
        let () = print_endline_quiet "-- use Omega.imply_..." in
        let (pr_w, pr_s) = Cpure.drop_complex_ops in
        match (Omega.imply_with_check pr_w pr_s ante conseq "" timeout) with
        | None -> (false, (* true*) false)
        | Some r -> (r, false)
      with exc -> match exc with 
        | Procutils.PrvComms.Timeout -> 
          if not (!dis_provers_timeout) then (false, (* true *) false)
          else raise exc (* Timeout exception of a higher-level function *)
        | _ -> (false, (* true *) false) (* TrungTQ: Maybe BUG: in the exception case, it should return UNKNOWN *)
    else (false, true) in
  if (should_run_spass) then
    (* let () = print_endline "-- use Spass.check_problem" in *)
    let spass_input = to_spass ante (Some conseq) in
    let validity =
      if (spass_input_mode = "file") then
        check_problem_through_file spass_input timeout
      else if (spass_input_mode = "stdin") then
        check_problem_through_stdin spass_input timeout
      else illegal_format "[spass.ml] The value of spass_input_mode is invalid!" in
    (* let prover_output = String.concat "\n" output.original_output_text in *)
    (* debug let () = print_endline ("** prover output:" ^              *)
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
  (* let () = print_endline "** In function Spass.imply:" in *)
  let result = spass_imply ante conseq timeout in
  (* let () = print_endline ("-- imply result: " ^ (if result then "true" else "false" )) in *)
  result

let imply_with_check (ante : Cpure.formula) (conseq : Cpure.formula) (imp_no : string) (timeout: float) : bool option =
  (* let () = print_endline "** In function Spass.imply_with_check:" in *)
  Cpure.do_with_check2 "" (fun a c -> imply a c timeout) ante conseq

let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let () = print_endline "** In function Spass.imply:" in *)
  try
    let result = imply ante conseq timeout in
    result
  with Illegal_Prover_Format s -> (
      print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :" ^ s);
      print_endline_quiet ("Apply Spass.imply on ante Formula :" ^ (Cprinter.string_of_pure_formula ante));
      print_endline_quiet ("and conseq Formula :" ^ (Cprinter.string_of_pure_formula conseq));
      flush stdout;
      failwith s
    )

let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let () = print_endline "** In function Spass.imply:" in *)
  Debug.no_1(* _loop *) "smt.imply" string_of_float string_of_bool
    (fun _ -> imply ante conseq timeout) timeout

(**
 * Test for satisfiability
 * We also consider unknown is the same as sat
*)

let spass_is_sat (f : Cpure.formula) (sat_no : string) timeout : bool =
  (* debug *)
  (* let () = print_endline "** In function Spass.spass_is_sat:" in *)
  (* anything that SPASS counldn't handle will be transfer to Omega *)
  let res, should_run_spass =
    if not (can_spass_handle_formula f) then
      (* for debug *)
      (* let fomega = x_add Omega.omega_of_formula f in
         let () = print_endline ("can_spass_handle_formula f: " ^ fomega ^ ": " ^ 
              (if (can_spass_handle_formula f) then "true" else "false")) in
         let () = print_endline "-- use Omega.is_sat..." in *)
      try
        let (pr_w, pr_s) = Cpure.drop_complex_ops in
        let optr = (Omega.is_sat_with_check pr_w pr_s f sat_no) in
        match optr with
        | Some r -> (r, false)
        | None -> (true, false)
      with exc -> match exc with 
        | Procutils.PrvComms.Timeout -> 
          if not (!dis_provers_timeout) then (true, false)
          else raise exc (* Timeout exception of a higher-level function *)
        | _ -> (true, false) (* TrungTQ: Maybe BUG: Why res = true in the exception case? It should return UNKNOWN *)
    else (false, true) in
  if (should_run_spass) then
    (* let () = print_endline "-- use Spass.check_problem..." in *)
    (* to check sat of f, spass check the validity of negative(f) or (f => None) *)
    let spass_input = to_spass f None in
    let validity =
      if (spass_input_mode = "file") then
        check_problem_through_file spass_input timeout
      else if (spass_input_mode = "stdin") then
        check_problem_through_stdin spass_input timeout
      else illegal_format "[spass.ml] The value of spass_input_mode is invalid!" in
    (* let validity = check_problem_through_file spass_input timeout in *)
    let res =
      match validity.validity_result with
      | Invalid -> true      (* if neg(f) invalid ==> f sat *) 
      | Valid   -> false     (* if neg(f) valid   ==> f unsat *)
      | _       -> true in  (* other, consider f unsat *)
    res
  else
    res

(* spass *)
let spass_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  spass_is_sat f sat_no spass_timeout_limit

(* spass *)
let spass_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  let result = Debug.no_1 "spass_is_sat" pr string_of_bool (fun _ -> spass_is_sat f sat_no) f in
  (* let omega_result = Omega.is_sat f sat_no in
     let () = print_endline ("-- spass_is_sat result: " ^ (if result then "TRUE" else "FALSE")) in
     let () = print_endline ("-- Omega.is_sat result: " ^ (if omega_result then "TRUE" else "FALSE")) in *)
  result

(* see imply *)
let is_sat (f: Cpure.formula) (sat_no: string) : bool =
  (* debug *)
  (* let () = print_endline "** In function Spass.is_sat: " in *)
  let result = spass_is_sat f sat_no in
  (* let () = print_endline ("-- is_sat result: " ^ (if result then "true" else "false")) in *)
  result

let is_sat_with_check (pe : Cpure.formula) sat_no : bool option =
  Cpure.do_with_check "" (fun x -> is_sat x sat_no) pe

(* let is_sat f sat_no = Debug.loop_2_no "is_sat" (!print_pure) (fun x->x) *)
(* string_of_bool is_sat f sat_no                                          *)

let is_sat (pe : Cpure.formula) (sat_no: string) : bool =
  (* let () = print_endline "** In function Spass.is_sat: " in *)
  try
    is_sat pe sat_no;
  with Illegal_Prover_Format s -> (
      print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :" ^ s);
      print_endline_quiet ("Apply Spass.is_sat on formula :" ^ (Cprinter.string_of_pure_formula pe));
      flush stdout;
      failwith s
    )

(**
 * To be implemented
*)
let simplify (f: Cpure.formula) : Cpure.formula =
  (* debug *)
  (* let () = print_endline "** In function Spass.simplify" in *)
  try (x_add_1 Omega.simplify f) with _ -> f

let simplify (pe : Cpure.formula) : Cpure.formula =
  match (Cpure.do_with_check "" simplify pe) with
  | None -> pe
  | Some f -> f

let hull (f: Cpure.formula) : Cpure.formula = f

let pairwisecheck (f: Cpure.formula): Cpure.formula = f
