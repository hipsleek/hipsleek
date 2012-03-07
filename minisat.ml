open Globals
open Gen.Basic
open Cpure

module StringSet = Set.Make(String)

(* Global settings *)
let minisat_timeout_limit = 15.0


let test_number = ref 0
let last_test_number = ref 0
let minisat_restart_interval = ref (-1)
let log_all_flag = ref false
let is_minisat_running = ref false
let in_timeout = ref 15.0 (* default timeout is 15 seconds *)
let minisat_call_count: int ref = ref 0
let log_file = open_out ("allinput.minisat")
let minisat_input_mode = "file"    (* valid value is: "file" or "stdin" *) 

(*minisat*)
let minisat_path = "/usr/local/bin/minisat"
let minisat_name = "minisat"
let minisat_arg = ""
let minisat_input_format = "cnf"   (* valid value is: cnf *)
let number_clauses = ref 0
let number_var = ref 0
let minisat_process = ref {  name = "minisat";
                           pid = 0;
                           inchannel = stdin;
                           outchannel = stdout;
                           errchannel = stdin 
                          }
(***************************************************************
TRANSLATE CPURE FORMULA TO PROBLEM IN CNF FORMAT
**************************************************************)
(*minisat*)
let de_morgan f=match f with 
  |Not (And(f1,f2,_),l1,l2)-> Or(Not(f1,l1,l2), Not (f2,l1,l2),l1,l2)
  |Not (Or(f1,f2,_,_),l1,l2)-> And(Not(f1,l1,l2),Not(f2,l1,l2),l2)  
  |_->f
let double_negative f= match f with
  |Not (Not(f1,_,_),_,_)->f1
  |_->f

let minisat_cnf_of_spec_var sv = let ident=Cpure.name_of_spec_var sv in ident

let  minisat_cnf_of_p_formula (pf : Cpure.p_formula) =
  match pf with
  | LexVar _        -> ""
  | BConst (c, _)   -> if c then "true" else "false"
  | BVar (sv, _)    -> minisat_cnf_of_spec_var sv
  | Lt _            -> ""
  | Lte _           ->""
  | Gt _            -> ""
  | Gte _           -> ""
  | SubAnn _        -> ""
  | Eq (e1, e2, _)  ->""
  | Neq (e1, e2, _) -> ""
  | EqMax _         -> ""
  | EqMin _         -> ""
  (* bag formulas *)
  | BagIn _
  | BagNotIn _
  | BagSub _
  | BagMin _
  | BagMax _        -> ""
  (* list formulas *)
  | ListIn _
  | ListNotIn _
  | ListAllN _
  | ListPerm _
  | RelForm _       -> ""

let minisat_cnf_of_b_formula (bf : Cpure.b_formula) =
  match bf with
  | (pf, _) -> minisat_cnf_of_p_formula pf

let return_pure bf f= match bf with
  | (pf,_)-> match pf with 
             |BConst(_,_)->f
	     |BVar(_,_)->f

let rec minisat_cnf_of_formula f =
  match f with
  | BForm (b, _)         -> return_pure b f
  | And (f1, f2, l1)      ->   And(minisat_cnf_of_formula f1,minisat_cnf_of_formula f2,l1)  
  | Or (f1, f2, l1, l2)    ->   Or(minisat_cnf_of_formula f1,minisat_cnf_of_formula f2,l1,l2)    
  | Not (BForm(b,_), _, _) -> return_pure b f
  | _ -> minisat_cnf_of_formula (de_morgan (double_negative f));;
 
let rec cnf_to_string f = 
  match f with
  |BForm (b,_)-> minisat_cnf_of_b_formula b
  |Not (f1,_,_)->"-"^cnf_to_string f1
  |And (f1, f2, _) -> "("^(cnf_to_string f1)^"&"^(cnf_to_string f2)^")"
  |Or  (f1, f2, _, _)->"("^(cnf_to_string f1)^"v"^(cnf_to_string f2)^")"
let incr_cls= number_clauses:=1 + !number_clauses
let check_inmap var map :string= let index= ref 0 in
				 begin
				 for i=0 to (List.length map)-1 do
                                     (
				       if var=(minisat_cnf_of_spec_var (List.nth map i)) then (index:=i+1)
				     )
				 done;
				  string_of_int !index
				 end   
let rec cnf_to_string_to_file f (map: spec_var list)= 
  match f with
  |BForm (b,_)-> let var=minisat_cnf_of_b_formula b in check_inmap var map 
  |Not (f1,_,_)->"-"^cnf_to_string_to_file f1 map
  |And (f1, f2, _) -> let _= incr_cls in (cnf_to_string_to_file f1 map)^" 0"^"\n"^(cnf_to_string_to_file f2 map)
  |Or  (f1, f2, _, _)-> (cnf_to_string_to_file f1 map)^" "^(cnf_to_string_to_file f2 map)
(* distributive law 1 - (f & k) v (g & h) -> (f v g) & (f v h) & (k v g) & (k v h) *)
let dist_1 f = 
  match f with
    Or(And(f1, f2,_), And(f3, f4,_),l1,l2) ->And(And(Or(f1, f3,l1,l2), Or(f1, f4,l1,l2),l2), And(Or(f2, f3,l1,l2), Or(f2, f4,l1,l2),l2),l2)
  | Or(f1, And(f2, f3,_),l1,l2) -> And(Or(f1, f2,l1,l2), Or(f1, f3,l1,l2),l2)
  | Or(And(f2, f3,_), f1,l1,l2) -> And(Or(f1, f2,l1,l2), Or(f1, f3,l1,l2),l2)
  | _ -> f

let rec nnf_to_xxx f rule =
  let nf = match f with
    BForm (b,_) -> return_pure b f 
  | Not (f1,l1,l2) -> Not ((nnf_to_xxx f1 rule),l1,l2)
  | And (f1, f2,l1) -> And (nnf_to_xxx f1 rule, nnf_to_xxx f2 rule,l1)
  | Or (f1, f2,l1,l2) -> Or (nnf_to_xxx f1 rule, nnf_to_xxx f2 rule,l1,l2)
  in
    rule nf

let nnf_to_cnf f= nnf_to_xxx f dist_1 

let to_cnf f = nnf_to_cnf (minisat_cnf_of_formula f)

let minisat_cnf_of_formula f =
  Debug.no_1 "minisat_of_formula" Cprinter.string_of_pure_formula pr_id minisat_cnf_of_formula f
	   
(*bach-minisat*)

(*************************************************************)
(* Check whether minisat can handle the expression, formula... *)
let rec can_minisat_handle_expression (exp: Cpure.exp) : bool =
  match exp with
  | Cpure.Null _         -> false
  | Cpure.Var _          -> false
  | Cpure.IConst _       -> false
  | Cpure.FConst _       -> false
  | Cpure.AConst _       -> false
  (* arithmetic expressions *)
  | Cpure.Add _
  | Cpure.Subtract _
  | Cpure.Mult _
  | Cpure.Div _
  | Cpure.Max _
  | Cpure.Min _          -> false
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
  | Cpure.Func _ ->  false 


and can_minisat_handle_p_formula (pf : Cpure.p_formula) : bool =
  match pf with
  | LexVar _             -> false
  | BConst _             -> true
  | BVar _               -> true
  | Lt _                 -> false
  | Lte _                -> false
  | Gt _                 -> false
  | Gte _                -> false
  | SubAnn (ex1, ex2, _) -> false
  | Eq (ex1, ex2, _)     -> false
  | Neq (ex1, ex2, _)    -> false
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

and can_minisat_handle_b_formula (bf : Cpure.b_formula) : bool =
  match bf with
  | (pf, _) -> can_minisat_handle_p_formula pf

and can_minisat_handle_formula (f: Cpure.formula) : bool =
  match f with
  | BForm (bf, _)       -> can_minisat_handle_b_formula bf
  | And (f1, f2, _)     -> (can_minisat_handle_formula f1) && (can_minisat_handle_formula f2)
  | Or (f1, f2, _, _)   -> (can_minisat_handle_formula f1) && (can_minisat_handle_formula f2)
  | Not (f, _, _)       -> can_minisat_handle_formula f
  | Forall (_, f, _, _) -> can_minisat_handle_formula f
  | Exists (_, f, _, _) -> can_minisat_handle_formula f

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

let string_of_minisat_output output =
  (String.concat "\n" output.original_output_text)

(* collect the output information of a process
   return : a string list of output and running state of process: "true" if still running, otherwise "false" *)
let rec collect_output (chn: in_channel) (accumulated_output: string list) : (string list * bool) =
  try
    let line = input_line chn in
    let _ = print_endline (line) in 
    if line = "SATISFIABLE" then(
      print_endline ("ket qua ne:"^ line);
      (accumulated_output, true)
    )
    else
      collect_output chn (accumulated_output @ [line])
  with 
  | End_of_file ->  (accumulated_output, false)

(* read the output stream of minisat prover, return (conclusion * reason)    *)
(* TODO: this function need to be optimized                                *)
let get_prover_result (output : string list) : validity_t =
  (* debug *)
  (* let _ = print_endline "** In functin get_prover_result:" in *)
  (* List.iter (fun x -> print_endline x) output; *)
  let rec is_start_with (subtext: string) (text: string) : bool =
    let len = String.length subtext in
    try 
      if (String.sub text 0 len = subtext) then true
      else false
    with _ -> false in
  let conclusion_line = try List.find (is_start_with "minisat beiseite:") output
                        with Not_found -> "Unknown" in
  (* debug *)
  (* let _ = print_endline ("-- get_prover_result: " ^ conclusion_line) in *)
  let validity =
    if (conclusion_line = "minisat beiseite: Completion found.") then
      Invalid
    else if (conclusion_line = "minisat beiseite: Proof found.") then
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

let set_process (proc: Globals.prover_process_t) =
  minisat_process := proc

let start () =
  if not !is_minisat_running then (
    print_endline ("Starting Minisat... \n");
    last_test_number := !test_number;
    let prelude () = () in
    if (minisat_input_format = "cnf") then (
      Procutils.PrvComms.start !log_all_flag log_file (minisat_name, minisat_path, [|minisat_arg|]) set_process prelude;
      is_minisat_running := true;
      print_endline ("minisat called... \n");
    )
  )

(* stop minisat system *)
let stop () =
  if !is_minisat_running then (
    let num_tasks = !test_number - !last_test_number in
    print_string ("Stop Minisat... " ^ (string_of_int !minisat_call_count) ^ " invocations "); flush stdout;
    let _ = Procutils.PrvComms.stop !log_all_flag log_file !minisat_process num_tasks Sys.sigkill (fun () -> ()) in
    is_minisat_running := false;
  )

(* restart Omega system *)
let restart reason =
  if !is_minisat_running then (
    let _ = print_string (reason ^ " Restarting minisat after ... " ^ (string_of_int !minisat_call_count) ^ " invocations ") in
    Procutils.PrvComms.restart !log_all_flag log_file reason "minisat" start stop
  )
  else (
    let _ = print_string (reason ^ " not restarting minisat ... " ^ (string_of_int !minisat_call_count) ^ " invocations ") in ()
  )
    
(* Runs the specified prover and returns output *)
let check_problem_through_file (input: string) (timeout: float) : prover_output_t =
  (* debug *)
  (* let _ = print_endline "** In function minisat.check_problem" in *)
  let file_suffix = Random.int 1000000 in
  let infile = "/tmp/in" ^ (string_of_int file_suffix) ^ ".cnf" in
  let _ = print_endline ("-- input: \n" ^ input) in 
  let out_stream = open_out infile in
  output_string out_stream input;
  close_out out_stream;
  let minisat_result="minisatres.txt" in
  let set_process proc = minisat_process := proc in
  let fnc () =
    if (minisat_input_format = "cnf") then (
      print_string "Solving by minisat...";
      Procutils.PrvComms.start false stdout (minisat_name, minisat_path, [|minisat_arg;infile;minisat_result|]) set_process (fun () -> ());
      minisat_call_count := !minisat_call_count + 1;
      let (prover_output, running_state) = get_answer !minisat_process.inchannel in
      is_minisat_running := running_state;
      prover_output;
    )
    else illegal_format "[minisat.ml] The value of minisat_input_format is invalid!" in
  let res =
    try
      let res = Procutils.PrvComms.maybe_raise_timeout fnc () timeout in
      res
    with _ -> ((* exception : return the safe result to ensure soundness *)
      Printexc.print_backtrace stdout;
      print_endline ("WARNING: Restarting prover due to timeout");
      Unix.kill !minisat_process.pid 9;
      ignore (Unix.waitpid [] !minisat_process.pid);
      { original_output_text = []; validity_result = Aborted; }
    ) in
  let _ = Procutils.PrvComms.stop false stdout !minisat_process 0 9 (fun () -> ()) in
  remove_file infile;
  res

let check_problem_through_file (input: string) (timeout: float) : prover_output_t =
  Debug.no_1 "check_problem_through_file"
    (fun s -> s) string_of_prover_validity_output
    (fun f -> check_problem_through_file f timeout) input
    
(* Runs the specified prover and returns output *)
let check_problem_through_stdin (input: string) (timeout: float) : prover_output_t =
  (* debug *)
  (*let _ = print_endline "** In function minisat.check_problem_through_stdin" in 
  let _ = print_endline ("  -- input: \n" ^ input) in*)
  if not !is_minisat_running then (
    (*let _ = print_endline "  -- start minisat" in*)
    start ()
  )
  else if (!minisat_call_count = !minisat_restart_interval) then (
    (*let _ = print_endline "  -- restart minisat" in
    restart("Regularly restart:1 ");*)
    minisat_call_count := 0;
  );
  (*let _ = print_endline (" -- minisat_process_pid: " ^ string_of_int(!minisat_process.pid)) in*)
  let fnc f =
    output_string (!minisat_process.outchannel) f;
    flush (!minisat_process.outchannel);
    let _ = incr minisat_call_count in
    let (prover_output, running_state) = get_answer !minisat_process.inchannel in
    is_minisat_running := running_state;
    prover_output in
  let res =
    try
      let res = Procutils.PrvComms.maybe_raise_timeout fnc input timeout in
      res
    with 
    | _ -> ((* exception : return the safe result to ensure soundness *)
        Printexc.print_backtrace stdout;
        print_endline ("WARNING: Restarting prover due to timeout");
        Unix.kill !minisat_process.pid 9;
        ignore (Unix.waitpid [] !minisat_process.pid);
        { original_output_text = []; validity_result = Aborted; }
      ) in
  res

let check_problem_through_stdin (input: string) (timeout: float) : prover_output_t =
  Debug.no_1 "check_problem_through_stdin"
    (fun s -> s) string_of_prover_validity_output
    (fun f -> check_problem_through_stdin f timeout) input
;;
(***************************************************************
GENERATE CNF INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
**************************************************************)
(* minisat: output for cnf format *)
let to_minisat_cnf (ante: Cpure.formula) (conseq: Cpure.formula)(mapvar: spec_var list) : string =
  let ante_str = cnf_to_string_to_file (to_cnf ante) mapvar 
  and conseq_str = cnf_to_string_to_file (to_cnf conseq) mapvar in
		  let result = "p cnf "^(string_of_int !number_var)^" "^ (string_of_int !number_clauses)
		    ^"\n"
 		    ^ante_str^" 0"
		  in result 
		
(*bach*) 
(***************************************************************
GENERATE CNF INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
**************************************************************)
let return_number_var nbv = number_var:= nbv
let to_minisat (ante : Cpure.formula) (conseq : Cpure.formula option) : string =
  (* debug *)
  (* let _ = print_endline "** In function to_minisat:" in *)
  let conseq = match conseq with
    (* We don't have conseq part in is_sat checking *)
    | None   -> Cpure.mkFalse no_pos
    | Some f -> f
  in
  let res = 
    if (minisat_input_format = "cnf") then (
	    (* if sending problem in cnf format to minisat *)
	    let ante_fv = Cpure.fv ante in
	    let conseq_fv = Cpure.fv conseq in
	    let all_fv = Gen.BList.remove_dups_eq (=) (ante_fv @ conseq_fv) in	
	    let _= return_number_var (List.length all_fv) in
	    let cnf_res = to_minisat_cnf ante conseq all_fv
      (* let _ = print_endline ("-- Input problem in cnf format:\n" ^ cnf_res) in *)
      in cnf_res
    ) 
    else illegal_format "[minisat.ml] The value of minisat_input_format is invalid!" in

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

let rec minisat_imply (ante : Cpure.formula) (conseq : Cpure.formula) timeout : bool =
  (* let _ = "** In function minisat.minisat_imply" in *)
  let pr = Cprinter.string_of_pure_formula in
  let result = 
    Debug.no_2_loop "minisat_imply" (pr_pair pr pr) string_of_float string_of_bool
    (fun _ _ -> minisat_imply_x ante conseq timeout) (ante, conseq) timeout in
  (* let omega_result = Omega.imply ante conseq "" timeout in
  let _ = print_endline ("-- minisat_imply result: " ^ (if result then "TRUE" else "FALSE")) in
  let _ = print_endline ("-- omega_imply result: " ^ (if omega_result then "TRUE" else "FALSE")) in *)
  result;
    

and minisat_imply_x (ante : Cpure.formula) (conseq : Cpure.formula) timeout : bool =
  let _ = "** In function minisat.minisat_imply_x" in
  let res, should_run_minisat =
    if not ((can_minisat_handle_formula ante) && (can_minisat_handle_formula conseq)) then
      (* for debug *)
      (* let fomega_ante = Omega.omega_of_formula ante in
      let _ = print_endline ("can_minisat_handle_formula ante:" ^ fomega_ante ^ ": " ^ 
              (if (can_minisat_handle_formula ante) then "true" else "false")) in
      let fomega_conseq = Omega.omega_of_formula conseq in
      let _ = print_endline ("can_minisat_handle_formula conseq:" ^ fomega_conseq^ ": " ^ 
              (if (can_minisat_handle_formula conseq) then "true" else "false")) in *)
      try
        let _ = print_endline "-- use Omega.imply_..." in
        let (pr_w,pr_s) = Cpure.drop_complex_ops in
        match (Omega.imply_with_check pr_w pr_s ante conseq "" timeout) with
        | None -> (false, true)
        | Some r -> (r, false)
      with _ -> (false, true) (* TrungTQ: Maybe BUG: in the exception case, it should return UNKNOWN *)
    else (false, true) in
  if (should_run_minisat) then
    (* let _ = print_endline "-- use minisat.check_problem" in *)
    let minisat_input = to_minisat ante (Some conseq) in
    let validity =
      if (minisat_input_mode = "file") then
        check_problem_through_file minisat_input timeout
      else if (minisat_input_mode = "stdin") then
        check_problem_through_stdin minisat_input timeout
      else illegal_format "[minisat.ml] The value of minisat_input_mode is invalid!" in
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
  (* let _ = print_endline "** In function minisat.imply:" in *)
  let result = minisat_imply ante conseq timeout in
  (* let _ = print_endline ("-- imply result: " ^ (if result then "true" else "false" )) in *)
  result

let imply_with_check (ante : Cpure.formula) (conseq : Cpure.formula) (imp_no : string) (timeout: float) : bool option =
  (* let _ = print_endline "** In function minisat.imply_with_check:" in *)
  Cpure.do_with_check2 "" (fun a c -> imply a c timeout) ante conseq

let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let _ = print_endline "** In function minisat.imply:" in *)
  try
    let result = imply ante conseq timeout in
    result
  with Illegal_Prover_Format s -> (
    print_endline ("\nWARNING : Illegal_Prover_Format for :" ^ s);
    print_endline ("Apply minisat.imply on ante Formula :" ^ (Cprinter.string_of_pure_formula ante));
    print_endline ("and conseq Formula :" ^ (Cprinter.string_of_pure_formula conseq));
    flush stdout;
    failwith s
  )

let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let _ = print_endline "** In function minisat.imply:" in *)
  Debug.no_1_loop "smt.imply" string_of_float string_of_bool
    (fun _ -> imply ante conseq timeout) timeout

(**
* Test for satisfiability
* We also consider unknown is the same as sat
*)

let minisat_is_sat (f : Cpure.formula) (sat_no : string) timeout : bool =
  (* debug *)
  (* let _ = print_endline "** In function minisat.minisat_is_sat:" in *)
  (* anything that minisat counldn't handle will be transfer to Omega *)
  let res, should_run_minisat =
    if not (can_minisat_handle_formula f) then
      (* for debug *)
      (* let fomega = Omega.omega_of_formula f in
      let _ = print_endline ("can_minisat_handle_formula f: " ^ fomega ^ ": " ^ 
              (if (can_minisat_handle_formula f) then "true" else "false")) in
      let _ = print_endline "-- use Omega.is_sat..." in *)
      try
        let (pr_w,pr_s) = Cpure.drop_complex_ops in
        let optr = (Omega.is_sat_with_check pr_w pr_s f sat_no) in
        match optr with
        | Some r -> (r, false)
        | None -> (true, false)
      with _ -> (true, false) (* TrungTQ: Maybe BUG: Why res = true in the exception case? It should return UNKNOWN *)
    else (false, true) in
  if (should_run_minisat) then
    (* let _ = print_endline "-- use minisat.check_problem..." in *)
    (* to check sat of f, minisat check the validity of negative(f) or (f => None) *)
    let minisat_input = to_minisat f None in
    let validity =
      if (minisat_input_mode = "file") then
        check_problem_through_file minisat_input timeout
      else if (minisat_input_mode = "stdin") then
        check_problem_through_stdin minisat_input timeout
      else illegal_format "[minisat.ml] The value of minisat_input_mode is invalid!" in
    (* let validity = check_problem_through_file minisat_input timeout in *)
    let res =
      match validity.validity_result with
      | Invalid -> true      (* if neg(f) invalid ==> f sat *) 
      | Valid   -> false     (* if neg(f) valid   ==> f unsat *)
      | _       -> true in  (* other, consider f unsat *)
    res
  else
    res

(* minisat *)
let minisat_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  minisat_is_sat f sat_no minisat_timeout_limit

(* minisat *)
let minisat_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  let result = Debug.no_1 "minisat_is_sat" pr string_of_bool (fun _ -> minisat_is_sat f sat_no) f in
  (* let omega_result = Omega.is_sat f sat_no in
  let _ = print_endline ("-- minisat_is_sat result: " ^ (if result then "TRUE" else "FALSE")) in
  let _ = print_endline ("-- Omega.is_sat result: " ^ (if omega_result then "TRUE" else "FALSE")) in *)
  result

(* see imply *)
let is_sat (f: Cpure.formula) (sat_no: string) : bool =
  (* debug *)
  (* let _ = print_endline "** In function minisat.is_sat: " in *)
  let result = minisat_is_sat f sat_no in
  (* let _ = print_endline ("-- is_sat result: " ^ (if result then "true" else "false")) in *)
  result

let is_sat_with_check (pe : Cpure.formula) sat_no : bool option =
  Cpure.do_with_check "" (fun x -> is_sat x sat_no) pe

(* let is_sat f sat_no = Debug.loop_2_no "is_sat" (!print_pure) (fun x->x) *)
(* string_of_bool is_sat f sat_no                                          *)

let is_sat (pe : Cpure.formula) (sat_no: string) : bool =
  (* let _ = print_endline "** In function minisat.is_sat: " in *)
  try
    is_sat pe sat_no;
  with Illegal_Prover_Format s -> (
    print_endline ("\nWARNING : Illegal_Prover_Format for :" ^ s);
    print_endline ("Apply minisat.is_sat on formula :" ^ (Cprinter.string_of_pure_formula pe));
    flush stdout;
    failwith s
  )

(**
* To be implemented
*)
let simplify (f: Cpure.formula) : Cpure.formula =
  (* debug *)
  (* let _ = print_endline "** In function minisat.simplify" in *)
  try (Omega.simplify f) with _ -> f

let simplify (pe : Cpure.formula) : Cpure.formula =
  match (Cpure.do_with_check "" simplify pe) with
  | None -> pe
  | Some f -> f

let hull (f: Cpure.formula) : Cpure.formula = f

let pairwisecheck (f: Cpure.formula): Cpure.formula = f
