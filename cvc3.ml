#include "xdebug.cppo"
open Globals
open VarGen
open GlobProver
open Gen.Basic
module CP = Cpure

let log_cvc3_formula = ref false
let _valid = true
let _invalid = false
let _sat = true
let _unsat = false
let cvc3_log = ref stdout
let infilename = !tmp_files_path ^ "input.cvc3." ^ (string_of_int (Unix.getpid ()))
let resultfilename = !tmp_files_path ^ "result.txt." ^ (string_of_int (Unix.getpid()))
let cvc3_command = "cvc3 " ^ infilename ^ " > " ^ resultfilename

let print_pure = ref (fun (c:CP.formula)-> " printing not initialized")
let test_number = ref 0

(* let set_log_file fn = *)
(*   log_cvc3_formula := true; *)
(*   if fn = "" then *)
(* 	cvc3_log := open_out "formula.cvc" *)
(*   else (\*if Sys.file_exists fn then *)
(* 	failwith "--log-cvc3: file exists" *)
(*   else*\) *)
(* 	begin *)
(* 		cvc3_log := open_out fn (\* opens fn for writing and returns an output channel for fn - cvc3_log is the output channel*\); *)
(* 		(\* output_string !cvc3_log cvc3_command *\) *)
(* 	end *)

let set_log_file () :  unit=
  log_cvc3_formula := true;
  cvc3_log := open_log_out "allinput.cvc3"

let run_cvc3 (input : string) : unit =
  begin
    let chn = open_out infilename in
    output_string chn input;
    close_out chn;
    ignore (Sys.command cvc3_command)
  end

let log_answer_cvc3 (answer : string) : unit =
  if !log_cvc3_formula then
    begin
      output_string !cvc3_log answer;
      flush !cvc3_log
    end

let return_answer (inchn: in_channel) (answer_to_log: string) (answer:bool option): bool option =
  let () = close_in inchn in
  let () = log_answer_cvc3 ("%%%Res: " ^ answer_to_log ^ "\n\n") in
  answer

let rec cvc3_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (_, v, p) -> v ^ (if CP.is_primed sv then "PRMD" else "")

and cvc3_of_exp a = match a with
  | CP.Null _ -> "0"
  | CP.Var (sv, _) -> cvc3_of_spec_var sv
  | CP.IConst (i, _) -> string_of_int i
  | CP.FConst _ -> failwith ("[cvc3ite.ml]: ERROR in constraints (float should not appear here)")
  | CP.Add (a1, a2, _) ->  (cvc3_of_exp a1) ^ " + " ^ (cvc3_of_exp a2)
  | CP.Subtract (a1, a2, _) ->  (cvc3_of_exp a1) ^ " - " ^ (cvc3_of_exp a2)
  | CP.Mult (a1, a2, _) -> (cvc3_of_exp a1) ^ " * " ^ (cvc3_of_exp a2)
  | CP.Div (a1, a2, _) -> failwith ("[cvc3.ml]: divide is not supported.")
  | CP.Max _ 
  | CP.Min _ -> failwith ("cvc3_of_exp: min/max should not appear here")
  | CP.TypeCast _ -> failwith "cvc3_of_exp : TypeCast cannot be handled"
  | CP.Bag ([], _) -> ""
  | CP.Bag _ | CP.BagUnion _ | CP.BagIntersect _ | CP.BagDiff _ ->
    failwith ("[cvc3.ml]: ERROR in constraints (set should not appear here)");
  | CP.List _ | CP.ListCons _ | CP.ListHead _ | CP.ListTail _ | CP.ListLength _ | CP.ListAppend _ | CP.ListReverse _ ->
    failwith ("Lists are not supported in cvc3")
  | CP.Func _ -> failwith ("Functions are not supported in cvc3")
  | CP.ArrayAt _ -> (* An Hoa *)
    failwith ("Arrays are not supported in cvc3")
  | CP.AConst _ -> failwith ("aconst not supported in cvc3")
  | CP.Level _ -> failwith ("level should not be here in cvc3")
  | CP.Tsconst _ -> failwith ("tsconst not supported in cvc3")
  | CP.Bptriple _ -> failwith ("cvc3.cvc3_of_exp: Bptriple should not appear here")
  | CP.Tup2 _ -> failwith ("cvc3.cvc3_of_exp: Tup2 should not appear here")
  | CP.InfConst _ 
  |CP.NegInfConst _ -> failwith ("[cvc3ite.ml]: ERROR in constraints (\inf should not appear here)")
  | CP.Template t -> cvc3_of_exp (CP.exp_of_template t)

and cvc3_of_b_formula b =
  let (pf,_) = b in
  match pf with
  | CP.Frm (sv, _) -> (cvc3_of_spec_var sv) ^ " > 0"
  (* | CP.BConst (c, _) -> if c then "(TRUE)" else "(FALSE)" *)
  | CP.BConst (c, _) -> if c then "(0 = 0)" else "( 0 > 0)"
  (* | CP.BVar (sv, _) -> cvc3_of_spec_var sv *)
  | CP.BVar (sv, _) -> (cvc3_of_spec_var sv) ^ " > 0"
  | CP.Lt (a1, a2, _) -> (cvc3_of_exp a1) ^ " < " ^ (cvc3_of_exp a2)
  | CP.Lte (a1, a2, _) -> (cvc3_of_exp a1) ^ " <= " ^ (cvc3_of_exp a2)
  | CP.Gt (a1, a2, _) -> (cvc3_of_exp a1) ^ " > " ^ (cvc3_of_exp a2)
  | CP.Gte (a1, a2, _) -> (cvc3_of_exp a1) ^ " >= " ^ (cvc3_of_exp a2)
  | CP.Eq (a1, a2, _) -> 
    if CP.is_null a2 then 
      (cvc3_of_exp a1) ^ " < 1"
    else if CP.is_null a1 then 
      (cvc3_of_exp a2) ^ " < 1"
    else 
      (cvc3_of_exp a1) ^ " = " ^ (cvc3_of_exp a2)
  | CP.Neq (a1, a2, _) -> 
    if CP.is_null a2 then 
      (cvc3_of_exp a1) ^ " > 0"
    else if CP.is_null a1 then 
      (cvc3_of_exp a2) ^ " > 0"
    else
      (cvc3_of_exp a1) ^ " /= " ^ (cvc3_of_exp a2)
  | CP.EqMax (a1, a2, a3, _) ->
    let a1str = cvc3_of_exp a1 in
    let a2str = cvc3_of_exp a2 in
    let a3str = cvc3_of_exp a3 in
    "((" ^ a2str ^ " >= " ^ a3str ^ " AND " ^ a1str ^ " = " ^ a2str ^ ") OR (" 
    ^ a3str ^ " > " ^ a2str ^ " AND " ^ a1str ^ " = " ^ a3str ^ "))"
  | CP.EqMin (a1, a2, a3, _) ->
    let a1str = cvc3_of_exp a1 in
    let a2str = cvc3_of_exp a2 in
    let a3str = cvc3_of_exp a3 in
    "((" ^ a2str ^ " >= " ^ a3str ^ " AND " ^ a1str ^ " = " ^ a3str ^ ") OR (" 
    ^ a3str ^ " > " ^ a2str ^ " AND " ^ a1str ^ " = " ^ a2str ^ "))"
  | CP.BagIn (v, e, l)			-> " in(" ^ (cvc3_of_spec_var v) ^ ", " ^ (cvc3_of_exp e) ^ ")"
  | CP.BagNotIn (v, e, l)	-> " NOT(in(" ^ (cvc3_of_spec_var v) ^ ", " ^ (cvc3_of_exp e) ^"))"
  | CP.BagSub (e1, e2, l)	-> " subset(" ^ cvc3_of_exp e1 ^ ", " ^ cvc3_of_exp e2 ^ ")"
  | CP.BagMax _ | CP.BagMin _ -> failwith ("cvc3_of_b_formula: BagMax/BagMin should not appear here.\n")
  (* | CP.VarPerm _ -> failwith ("VarPerm are not supported in cvc3") *)
  | CP.ListIn _
  | CP.ListNotIn _
  | CP.ListAllN _
  | CP.ListPerm _ -> failwith ("Lists are not supported in cvc3")
  | CP.RelForm _ -> failwith ("Relations are not supported in cvc3") (* An Hoa *)
  | CP.SubAnn _ -> failwith ("SubAnn not supported in cvc3")
  | CP.LexVar _ -> failwith ("LexVar not supported in cvc3")
  | CP.ImmRel _ -> failwith ("ImmRel not supported in cvc3")
  | CP.XPure _  -> Error.report_no_pattern ()
and cvc3_of_sv_type sv = match sv with
  | CP.SpecVar ((BagT _), _, _) -> "SET"
  | CP.SpecVar ( Bool, _, _) -> "INT" (* "BOOLEAN" *)
  | _ -> "INT"

and cvc3_of_formula f = match f with
  | CP.BForm (b,_) -> 
    begin
      match (fst CP.drop_complex_ops) (fst b) with
      | None -> "(" ^ (cvc3_of_b_formula b) ^ ")"
      | Some f -> cvc3_of_formula f
    end
  | CP.And (p1, p2, _) -> "(" ^ (cvc3_of_formula p1) ^ " AND " ^ (cvc3_of_formula p2) ^ ")"
  | CP.AndList _ -> Gen.report_error no_pos "cvc3.ml: encountered AndList, should have been already handled"
  | CP.Or (p1, p2,_, _) -> "(" ^ (cvc3_of_formula p1) ^ " OR " ^ (cvc3_of_formula p2) ^ ")"
  | CP.Not (p,_, _) ->
    begin
      match p with
      | CP.BForm ((CP.BVar (bv, _), _), _) -> (cvc3_of_spec_var bv) ^ " <= 0"
      | _ -> "(NOT (" ^ (cvc3_of_formula p) ^ "))"
    end
  | CP.Forall (sv, p,_, _) ->
    let typ_str = cvc3_of_sv_type sv in
    "(FORALL (" ^ (cvc3_of_spec_var sv) ^ ": " ^ typ_str ^ "): " ^ (cvc3_of_formula p) ^ ")"
  | CP.Exists (sv, p, _,_) -> 
    let typ_str = cvc3_of_sv_type sv in
    "(EXISTS (" ^ (cvc3_of_spec_var sv) ^ ": " ^ typ_str ^ "): " ^ (cvc3_of_formula p) ^ ")"

and remove_quantif f quant_list  = match f with
  | CP.BForm (b,_) -> 
    (*let () = print_string ("\n#### BForm: " ^ Cprinter.string_of_pure_formula f ) in*)
    (f, quant_list)
  | CP.AndList _ -> Gen.report_error no_pos "cvc3.ml: encountered AndList, should have been already handled"
  | CP.And (p1, p2, pos) -> 
    begin
      let (tmp1, quant_list) = remove_quantif p1 quant_list in
      let (tmp2, quant_list) = remove_quantif p2 quant_list in
      (*let () = print_string ("\n#### and: " ^ Cprinter.string_of_pure_formula tmp1 ) in
        			let () = print_string ("\n#### and: " ^ Cprinter.string_of_pure_formula tmp2 ) in*)
      ((CP.mkAnd tmp1 tmp2 pos), quant_list)
    end
  | CP.Or (p1, p2, lbl, pos) -> 
    begin
      let (tmp1, quant_list) = remove_quantif p1 quant_list in
      let (tmp2, quant_list) = remove_quantif p2 quant_list in
      (*let () = print_string ("\n#### Or: " ^ Cprinter.string_of_pure_formula tmp1 ) in*)
      (*let () = print_string ("\n#### Or: " ^ Cprinter.string_of_pure_formula tmp2 ) in*)
      ((CP.mkOr tmp1 tmp2 lbl pos), quant_list)
    end
  | CP.Not (p, lbl, pos) -> 
    begin
      let (tmp, quant_list) = remove_quantif p quant_list in
      (*let () = print_string ("\n#### NOT: " ^ Cprinter.string_of_pure_formula tmp ) in*)
      ((CP.mkNot tmp lbl pos), quant_list)
    end
  | CP.Forall (sv, p, lbl, pos) -> 
    begin
      let (tmp, quant_list) = remove_quantif p quant_list in
      (*let () = print_string ("\n#### Forall: " ^ Cprinter.string_of_pure_formula tmp ) in*)
      ((CP.mkForall [sv] tmp lbl pos), quant_list)
    end
  | CP.Exists (sv, p, lbl, pos) -> 
    begin
      let new_name = (CP.name_of_spec_var sv)^"_flatten" in 
      let new_sv = CP.SpecVar (CP.type_of_spec_var sv, new_name, if CP.is_primed sv then Primed else Unprimed) in
      let new_list = [] in
      let new_list = new_sv :: new_list in
      let old_list = [] in
      let old_list = sv :: old_list in
      let new_formula = CP.subst_avoid_capture old_list new_list p in
      let quant_list_modif = new_sv :: quant_list in
      let (tmp, quant_list_modif) = remove_quantif new_formula quant_list_modif in
      (*let () = print_string ("\n#### Exists: " ^ Cprinter.string_of_pure_formula tmp ) in*)
      (tmp , quant_list_modif)
    end

(*
  split a list of spec_vars to three lists:
  - int vars
  - boolean vars
  - set/bag vars
*)

and split_vars (vars : CP.spec_var list) = 
  if Gen.is_empty vars then 
    begin
      ([], [], [])
    end
  else 
    begin
      let ints, bools, bags = split_vars (List.tl vars) in
      (*let () = print_string ("!!!!!!! " ^ string_of_int (List.length ints) ^ "   " ^ string_of_int (List.length vars) ^ "\n" ) (*^ (String.concat ", " (List.map cvc3_of_spec_var ints)) ^ "/n" *)in*)
      let var = List.hd vars in
      match var with
      | CP.SpecVar ((BagT _), _, _) -> (ints, bools, var :: bags)
      | CP.SpecVar (Bool, _, _) -> (var :: ints, bools, bags)
      | _ -> (var :: ints, bools, bags)
    end

(*#########################################################################################*)
(*interactively start - stop process *)

let log_text_to_cvc3 (str : string) : unit =
  if !log_cvc3_formula then
    begin
      output_string !cvc3_log str
    end

(* return the answer from Globals.prover_process*)
let rec get_answer (process: GlobProver.prover_process_t) : string =
  try
    let chr = input_char process.inchannel in
    match chr with
    |'\n' ->  "" (*end answer reading when meeting the first "\n"*)
    | 'a'..'z' | 'A'..'Z' -> (Char.escaped chr) ^ get_answer process (*save only alpha characters.*)
    | _ -> "" ^ get_answer process (*ignore non-alpha characters*)
  with
    _ ->   (print_string ("\nexception getting the answer from cvc3: \n" ); flush stdout); ""

(*reads the prompt that cvc3 outputs when running in incremental mode *)
let rec read_prompt (process: GlobProver.prover_process_t) : string =
  try
    let chr = input_char process.inchannel in
    match chr with
    |'>' -> "" 
    | _ -> (Char.escaped chr) ^ read_prompt process
  with
  |  _ ->   (print_string ("\nexception while reading cvc3 promp \n" ); flush stdout); ""

(*send one command to cvc3 process without expecting any answer*)
let send_cmd (process: GlobProver.prover_process_t) (cmd: string): unit = 
  try
    let todo_unk = read_prompt process in
    let () = output_string process.outchannel cmd in
    let () = log_text_to_cvc3  cmd in    
    let () = flush process.outchannel in
    ()
  with
    _ ->  (print_string ("\nerror when sending a command: \n" ); flush stdout); ()

(*send one command to cvc3 process and waits for its answer*)
let send_cmd_with_answer (process: prover_process_t) (cmd: string): string = 
  try
    let () = send_cmd process cmd in
    let answ = get_answer process in
    answ
  with
    _ ->  (print_string ("\nerror when sending a command and receiveing the answer \n" ); flush stdout); ""

(*saves the current state in the active context of cvc3process*)
let cvc3_push (process: prover_process_t) = 
  let cmd = "PUSH;\n" in
  send_cmd process cmd

(*returns to the state before the last call of PUSH*)
let cvc3_pop (process: prover_process_t) = 
  let cmd = "POP;\n" in
  send_cmd process cmd

(*returns to the state before the last call of PUSH made from stack level n*)
let cvc3_popto (process: prover_process_t) (n: int) = 
  let cmd = "POPTO " ^ (string_of_int n)  ^ ";\n" in
  send_cmd process cmd

(*creates a new "cvc3 +int" process*)
let start () : prover_process_t =
  let () = print_string ("\nStarting CVC3\n") in
  let proc = ref {name = "cvc3"; pid = 0;  inchannel = stdin; outchannel = stdout; errchannel = stdin} in
  let set_process nproc = proc := nproc in
  let () = Procutils.PrvComms.start !log_cvc3_formula !cvc3_log ("cvc3", "cvc3", [|"cvc3"; "+int";(* "+printResults"*)|]) set_process (fun ()->()) in
  let () = cvc3_push !proc in
  !proc

(*stop the "cvc3 +int" process*)
let stop (process: prover_process_t) : unit = 
  let () = Procutils.PrvComms.stop !log_cvc3_formula !cvc3_log process !test_number 9 (fun () -> ()) in
  let () = print_string_if !Globals.enable_count_stats ("\nCVC3 stop process: " ^ (string_of_int !test_number) ^ " invocations \n") in 
  ()

(*all the formulas that shall be send to cvc3 process have to be transformed in cvc3 input language *)
let prepare_formula_for_sending (f : CP.formula) : string =
  cvc3_of_formula f 

(*declares the set of variables included in vars (list of variables) *)
let cvc3_declare_list_of_vars (process: prover_process_t) (vars: CP.spec_var list) =
  let int_vars, bool_vars, bag_vars = split_vars vars in
  let bag_var_decls = 
    if Gen.is_empty bag_vars then "" 
    else (String.concat ", " (List.map cvc3_of_spec_var bag_vars)) ^ ": SET;" in
  let int_var_decls = 
    if Gen.is_empty int_vars then "" 
    else (String.concat ", " (List.map cvc3_of_spec_var int_vars)) ^ ": INT;" in
  let bool_var_decls =
    if Gen.is_empty bool_vars then ""
    else (String.concat ", " (List.map cvc3_of_spec_var bool_vars)) ^ ": INT;" in (* BOOLEAN *)
  let var_decls = bool_var_decls ^ bag_var_decls ^ int_var_decls in
  if var_decls = "" then ()
  else 
    let cmd_var_decls = var_decls ^ "\n" in
    let () = send_cmd process cmd_var_decls in
    ()

(*declares the set of variables included in f formula*)
let cvc3_declare_vars_of_formula (process: prover_process_t) (f: CP.formula) = 
  let all_fv = CP.remove_dups_svl (CP.fv f) in
  cvc3_declare_list_of_vars process all_fv

(*asserts a condition to the context active in prover_process_t*)
let cvc3_assert (process: prover_process_t) (f : CP.formula) =
  (* let () = print_string ("\nCvc3.ml: cvc3_assert ") in *)
  let f_str = prepare_formula_for_sending f in
  let cmd = "ASSERT " ^ f_str ^ ";\n" in
  send_cmd process cmd

(*checks for implication*)
let cvc3_query (process: prover_process_t) (f : CP.formula) : bool option * string = 
  (* let () = print_string ("\nCvc3.ml: cvc3_query ") in *)
  let n_formula = prepare_formula_for_sending f in
  let conseq_str =  "QUERY ( " ^ n_formula ^ ");\n" in
  let answer = send_cmd_with_answer process conseq_str in
  let r = match answer with
    | "Valid" -> Some _valid
    | "Invalid" -> Some _invalid
    | "Unknown" -> None
    | _ -> None
  in
  (r, answer)

(*checks the satisfiability of formula f in the active context of prover_process_t*)
let cvc3_checksat (process: prover_process_t) (f : CP.formula): bool option * string= 
  let n_f = prepare_formula_for_sending f in 
  let checksat_str = "CHECKSAT (" ^ n_f ^ ");\n" in
  let answer = send_cmd_with_answer process checksat_str in
  let r = match answer with
    | "Satisfiable" ->  Some _sat
    | "Unsatisfiable" ->  Some _unsat
    | "Unknown" ->  None
    | _ -> None 
  in  (r, answer)

(*restarts an invalid QUERY or satisfiable CHECKSAT with an additional assumption represented by f, using what it has been learnt by now*)
let cvc3_restart_query (process: prover_process_t) (f: CP.formula) : bool option = 
  let () = log_text_to_cvc3 ("%%% restart " ^ (*sat_no ^*) "\n") in
  let n_f = prepare_formula_for_sending f in 
  let restart_str = "RESTART ( "^ n_f ^ " );\n" in 
  let () = log_text_to_cvc3 restart_str in
  let answer = send_cmd_with_answer process restart_str in
  let () = (log_text_to_cvc3  ("%%% Res: " ^ answer ^ " \n\n");  flush !cvc3_log) in
  let r = match answer with
    | "Valid" -> Some _valid
    | "Invalid" -> Some _invalid
    | "Satisfiable" ->  Some _sat
    | "Unsatisfiable" ->  Some _unsat
    | "Unknown" ->  None
    | _ -> None
  in r

(*simplify f formula and return the simplified formula *)
let cvc3_transform (process: prover_process_t) (f: CP.formula) (*: CP.formula*) = ()

(*sends the query command to "process" and returns the answer given by cvc3*)
let imply_helper (process: prover_process_t) (send_ante: bool) (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool option =
  (* let () = print_string ("\nCvc3.ml: imply ") in *)
  incr test_number;
  let () = log_text_to_cvc3  ("%%% imply " ^ imp_no  ^ "\n") in
  let () = 
    if (send_ante) then
      let () = cvc3_popto process 0 in
      let () = cvc3_push process in
      let ante_fv = CP.fv ante in
      let conseq_fv = CP.fv conseq in
      let () = cvc3_declare_list_of_vars process (ante_fv @ conseq_fv) in
      cvc3_assert process ante
    else cvc3_declare_vars_of_formula process (conseq) in
  let (answer, answer_str) = cvc3_query process conseq in
  let () = (log_text_to_cvc3  ("%%% Res: " ^ answer_str ^ " \n\n");  flush !cvc3_log) in
  answer

(*creates a new cvc3 process, sends the query command to the freshly created"process", stops the process and returns the answer given by cvc3*)
let imply_helper_separate_process (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool option =
  let process = start () in  
  let answer = imply_helper process true ante conseq imp_no in
  let () = stop process in
  answer

(*checks implication when in incremental running mode.*)
let imply_increm (process: (prover_process_t option * bool) option) (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  let result0 = match process with
    | Some (Some proc, send_ante) -> imply_helper proc send_ante ante conseq imp_no
    | None | _ -> imply_helper_separate_process ante conseq imp_no in
  let result = match result0 with
    | Some f -> f
    | None -> begin
        (log_text_to_cvc3   "%%% imply --> invalid (from unknown)\n\n";  flush !cvc3_log); 
        _invalid  (* unknown is assumed to be false *)
        (*failwith "CVC3 is unable to perform implication check"*)
      end
  in
  result

(*checks implication when in non-incremental running mode.*)
let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  imply_increm None ante conseq imp_no

let is_sat_helper (process: prover_process_t) (f : CP.formula) (sat_no : string) : bool option =
  incr test_number;
  let () = log_text_to_cvc3 ("%%% is_sat " ^ sat_no ^ "\n") in
  let () = cvc3_popto process 0 in
  let () = cvc3_push process in
  let () = cvc3_declare_vars_of_formula process f in
  let (answer, answer_str) = cvc3_checksat process f in
  let () = (log_text_to_cvc3  ("%%% Res: " ^ answer_str ^ " \n\n");  flush !cvc3_log) in
  answer

let is_sat_helper_separate_process (f : CP.formula) (sat_no : string) : bool option =
  let process = start () in
  let answer = is_sat_helper process f sat_no in
  let () = stop process in 
  answer

let is_sat_increm (process: prover_process_t option) (f : CP.formula) (sat_no : string) : bool =
  let result0 = 
    match process with
    |Some proc -> is_sat_helper proc f sat_no
    | None -> is_sat_helper_separate_process f sat_no  in
  let result = match result0 with
    | Some f -> f
    | None -> begin
        (log_text_to_cvc3   "%%% is_sat --> true (from unknown)\n\n";  flush !cvc3_log);
        (*failwith "CVC3 is unable to perform satisfiability check"*)
        _sat
      end
  in
  result

let  is_sat (f : CP.formula) (sat_no : string) : bool =
  is_sat_increm None f sat_no

(*#########################################################################################*)
