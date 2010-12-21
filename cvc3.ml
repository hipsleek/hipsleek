open Globals
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

let set_log_file fn =
  log_cvc3_formula := true;
  if fn = "" then
	cvc3_log := open_out "formula.cvc"
  else (*if Sys.file_exists fn then
	failwith "--log-cvc3: file exists"
  else*)
	begin
		cvc3_log := open_out fn (* opens fn for writing and returns an output channel for fn - cvc3_log is the output channel*);
		(* output_string !cvc3_log cvc3_command *)
	end

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
  let _ = close_in inchn in
  let _ = log_answer_cvc3 ("%%%Res: " ^ answer_to_log ^ "\n\n") in
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
  | CP.Min _ -> failwith ("cvc3.cvc3_of_exp: min/max should not appear here")
  | CP.Bag ([], _) -> ""
  | CP.Bag _ | CP.BagUnion _ | CP.BagIntersect _ | CP.BagDiff _ ->
  	    failwith ("[cvc3.ml]: ERROR in constraints (set should not appear here)");
  | CP.List _ | CP.ListCons _ | CP.ListHead _ | CP.ListTail _ | CP.ListLength _ | CP.ListAppend _ | CP.ListReverse _ ->
        failwith ("Lists are not supported in cvc3")

and cvc3_of_b_formula b = match b with
  | CP.BConst (c, _) -> if c then "(TRUE)" else "(FALSE)"
      (* | CP.BVar (sv, _) -> cvc3_of_spec_var sv *)
  | CP.BVar (sv, _) -> (cvc3_of_spec_var sv) ^ " > 0"
  | CP.Lt (a1, a2, _) -> (cvc3_of_exp a1) ^ " < " ^ (cvc3_of_exp a2)
  | CP.Lte (a1, a2, _) -> (cvc3_of_exp a1) ^ " <= " ^ (cvc3_of_exp a2)
  | CP.Gt (a1, a2, _) -> (cvc3_of_exp a1) ^ " > " ^ (cvc3_of_exp a2)
  | CP.Gte (a1, a2, _) -> (cvc3_of_exp a1) ^ " >= " ^ (cvc3_of_exp a2)
  | CP.Eq (a1, a2, _) -> 
    if CP.is_null a2 then 
		(cvc3_of_exp a1) ^ " <= 0"
	  else if CP.is_null a1 then 
		(cvc3_of_exp a2) ^ " <= 0"
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
  | CP.ListIn _
  | CP.ListNotIn _
  | CP.ListAllN _
  | CP.ListPerm _ -> failwith ("Lists are not supported in cvc3")
	    
and cvc3_of_sv_type sv = match sv with
  | CP.SpecVar (CP.Prim Bag, _, _) -> "SET"
  | CP.SpecVar (CP.Prim Bool, _, _) -> "INT" (* "BOOLEAN" *)
  | _ -> "INT"

and cvc3_of_formula f = match f with
  | CP.BForm (b,_) -> "(" ^ (cvc3_of_b_formula b) ^ ")"
  | CP.And (p1, p2, _) -> "(" ^ (cvc3_of_formula p1) ^ " AND " ^ (cvc3_of_formula p2) ^ ")"
  | CP.Or (p1, p2,_, _) -> "(" ^ (cvc3_of_formula p1) ^ " OR " ^ (cvc3_of_formula p2) ^ ")"
  | CP.Not (p,_, _) ->
	    begin
		  match p with
		    | CP.BForm (CP.BVar (bv, _),_) -> (cvc3_of_spec_var bv) ^ " <= 0"
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
		(*let _ = print_string ("\n#### BForm: " ^ Cprinter.string_of_pure_formula f ) in*)
		(f, quant_list)
  | CP.And (p1, p2, pos) -> 
		begin
		  let (tmp1, quant_list) = remove_quantif p1 quant_list in
		  let (tmp2, quant_list) = remove_quantif p2 quant_list in
		  (*let _ = print_string ("\n#### and: " ^ Cprinter.string_of_pure_formula tmp1 ) in
			let _ = print_string ("\n#### and: " ^ Cprinter.string_of_pure_formula tmp2 ) in*)
		  ((CP.mkAnd tmp1 tmp2 pos), quant_list)
		end
  | CP.Or (p1, p2, lbl, pos) -> 
		begin
		  let (tmp1, quant_list) = remove_quantif p1 quant_list in
		  let (tmp2, quant_list) = remove_quantif p2 quant_list in
		  (*let _ = print_string ("\n#### Or: " ^ Cprinter.string_of_pure_formula tmp1 ) in*)
		  (*let _ = print_string ("\n#### Or: " ^ Cprinter.string_of_pure_formula tmp2 ) in*)
		  ((CP.mkOr tmp1 tmp2 lbl pos), quant_list)
		end
  | CP.Not (p, lbl, pos) -> 
		begin
		  let (tmp, quant_list) = remove_quantif p quant_list in
		  (*let _ = print_string ("\n#### NOT: " ^ Cprinter.string_of_pure_formula tmp ) in*)
		  ((CP.mkNot tmp lbl pos), quant_list)
		end
  | CP.Forall (sv, p, lbl, pos) -> 
		begin
		  let (tmp, quant_list) = remove_quantif p quant_list in
		  (*let _ = print_string ("\n#### Forall: " ^ Cprinter.string_of_pure_formula tmp ) in*)
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
		  (*let _ = print_string ("\n#### Exists: " ^ Cprinter.string_of_pure_formula tmp ) in*)
		  (tmp , quant_list_modif)
		end

(*
  split a list of spec_vars to three lists:
  - int vars
  - boolean vars
  - set/bag vars
*)

and split_vars (vars : CP.spec_var list) = 
  if Util.empty vars then 
	begin
	  ([], [], [])
	end
  else 
	begin
	  let ints, bools, bags = split_vars (List.tl vars) in
	  (*let _ = print_string ("!!!!!!! " ^ string_of_int (List.length ints) ^ "   " ^ string_of_int (List.length vars) ^ "\n" ) (*^ (String.concat ", " (List.map cvc3_of_spec_var ints)) ^ "/n" *)in*)
	  let var = List.hd vars in
	  match var with
		| CP.SpecVar (CP.Prim Bag, _, _) -> (ints, bools, var :: bags)
		| CP.SpecVar (CP.Prim Bool, _, _) -> (var :: ints, bools, bags)
		| _ -> (var :: ints, bools, bags)
	end
		
(*filter quatified variables of the same type*)
and flatten_output ints bools bags : string =  
  if (Util.empty ints && Util.empty bools && Util.empty bags) then ""
  else
	let ints_vars_list =
	  if Util.empty ints then []
	  else let ints_str = (String.concat ", " (List.map cvc3_of_spec_var ints)) ^ " : INT" in				
	  ints_str :: [] in
	let bags_vars_list =
	  if Util.empty bags then ints_vars_list
	  else let bags_str = (String.concat ", " (List.map cvc3_of_spec_var bags)) ^ " : SET" in				
	  bags_str :: ints_vars_list in
	let all_quantif_vars_list =
	  if Util.empty bools then bags_vars_list
	  else let bools_str = (String.concat ", " (List.map cvc3_of_spec_var bools)) ^ " : INT" in
	  bools_str :: bags_vars_list in 
	"EXISTS (" ^ (String.concat ", " all_quantif_vars_list) ^ ") : "
	    
and imply_raw (ante : CP.formula) (conseq : CP.formula) : bool option =
  let ante_fv = CP.fv ante in
  let conseq_fv = CP.fv conseq in
  let all_fv = Util.remove_dups (ante_fv @ conseq_fv) in
  let int_vars, bool_vars, bag_vars = split_vars all_fv in
  let bag_var_decls = 
	if Util.empty bag_vars then "" 
	else (String.concat ", " (List.map cvc3_of_spec_var bag_vars)) ^ ": SET;\n" in
  let int_var_decls = 
	if Util.empty int_vars then "" 
	else (String.concat ", " (List.map cvc3_of_spec_var int_vars)) ^ ": INT;\n" in
  let bool_var_decls =
	if Util.empty bool_vars then ""
	else (String.concat ", " (List.map cvc3_of_spec_var bool_vars)) ^ ": INT;\n" in 
  let var_decls = bool_var_decls ^ bag_var_decls ^ int_var_decls in
  let ante_str =
	if (String.compare (cvc3_of_formula ante) "TRUE") == 0 then 
	  "a_dummy, b_dummy: INT;\nASSERT a_dummy = b_dummy; \n" (*strange case: in order to give a valid answer, in some cases, cvc3 needs a dummy assertion *)
	else "ASSERT (" ^ (cvc3_of_formula ante) ^ ");\n" in
  let (flatted_conseq, quant_list) = remove_quantif conseq [] in
  (*let _ = print_string ("\n ~~~~~ " ^ string_of_int(List.length quant_list) ^ String.concat ", " (List.map cvc3_of_spec_var quant_list)) in*)
  let ints, bools, bags = split_vars quant_list in 
  let quantif_vars_str = flatten_output ints bools bags in
  let conseq_str =  "QUERY (" ^ quantif_vars_str ^ " ( " ^ (cvc3_of_formula flatted_conseq) ^ "));\n" in
  (* talk to CVC3 *)
  let f_cvc3 = Util.break_lines ((*predicates ^*) var_decls ^ ante_str ^ conseq_str) in

  
  if !log_cvc3_formula then begin
	output_string !cvc3_log "%%% imply\n";
	output_string !cvc3_log (!print_pure ante);
  output_string !cvc3_log (!print_pure flatted_conseq);
	output_string !cvc3_log "\n";
	output_string !cvc3_log (!print_pure conseq);
	output_string !cvc3_log "\n";
	output_string !cvc3_log f_cvc3;
	flush !cvc3_log
  end;
  run_cvc3 f_cvc3;
  let chn = open_in resultfilename in
  let res_str = input_line chn in
  let n = String.index res_str '.' in
  let l = String.length res_str in
  let _ = String.fill res_str n (l-n) '.' in
  let r = match res_str with
    | "Valid." ->  return_answer chn "Valid" (Some _valid)
    | "Invalid." ->  return_answer chn "Invalid" (Some _invalid)
    | "Unknown." ->  return_answer chn "Unknown" None
    | _ -> return_answer chn "Unknown" None
  in r
		 

and imply_old (ante : CP.formula) (conseq : CP.formula) : bool =
  let result0 = imply_raw ante conseq in
  let result = match result0 with
	| Some f -> f
	| None -> begin
		_invalid  (* unknown is assumed to be false *)
		    (*failwith "CVC3 is unable to perform implication check"*)
	  end
  in
  begin
	try
	  ignore (Sys.remove infilename);
	    ignore (Sys.remove resultfilename)
	with
	  | e -> ignore e
  end;
  result

and is_sat_raw (f : CP.formula) (sat_no : string) : bool option =
  let all_fv = Util.remove_dups (CP.fv f) in
  let int_vars, bool_vars, bag_vars = split_vars all_fv in
  let bag_var_decls = 
	if Util.empty bag_vars then "" 
	else (String.concat ", " (List.map cvc3_of_spec_var bag_vars)) ^ ": SET;\n" in
  let int_var_decls = 
	if Util.empty int_vars then "" 
	else (String.concat ", " (List.map cvc3_of_spec_var int_vars)) ^ ": INT;\n" in
  let bool_var_decls =
	if Util.empty bool_vars then ""
	else (String.concat ", " (List.map cvc3_of_spec_var bool_vars)) ^ ": INT;\n" in (* BOOLEAN *)
  let var_decls = bool_var_decls ^ bag_var_decls ^ int_var_decls in
  (* let quant_list = [] in *)
  let f_str = cvc3_of_formula f in
  let query_str = "CHECKSAT (" ^ f_str ^ ");\n" in
  (* talk to CVC3 *)
  let f_cvc3 = Util.break_lines ( (*predicates ^*) var_decls (* ^ f_str *) ^ query_str) in

  
  if !log_cvc3_formula then begin
	output_string !cvc3_log ("%%% is_sat " ^ sat_no ^ "\n");
	output_string !cvc3_log f_cvc3;
	flush !cvc3_log
  end;
  run_cvc3 f_cvc3;
  let chn = open_in resultfilename in
  let res_str = input_line chn in
  let n = String.index res_str '.' in
  let l = String.length res_str in
  let _ = String.fill res_str n (l-n) '.' in (*having the prover string answer remove all the unnecessary information from it *)
  let r = match res_str with
    | "Satisfiable." ->  return_answer chn "Satisfiable" (Some _sat)
    | "Unsatisfiable." ->  return_answer chn "Unsatisfiable" (Some _unsat)
    | "Unknown." ->  return_answer chn "Unknown" None
    | _ -> return_answer chn "Unknown" None
  in r
	     
and is_sat_old (f : CP.formula) (sat_no : string) : bool =
  let result0 = is_sat_raw f sat_no in
  let result = match result0 with
	| Some f -> f
	| None -> begin
	  	if !log_cvc3_formula then begin
	  	  output_string !cvc3_log "%%% is_sat --> true (from unknown)\n"
	  	end;
	  	(*failwith "CVC3 is unable to perform satisfiability check"*)
	  	_sat
	  end
  in
  begin
	try
	  ignore (Sys.remove infilename); 
		ignore (Sys.remove resultfilename)
	with
	  | e -> ignore e
  end;
  result

(*#########################################################################################*)
(*multithreading - no log yet (to be implemented) *)

type cvc3process = { pid: int; inchannel: in_channel; outchannel: out_channel; errchannel: in_channel }

let cvc3_create_process () : cvc3process =
  let inchn, outchn, errchn, npid = Unix_add.open_process_full "cvc3" [|"cvc3"; "+int";(* "+printResults"*)|] in
  let ncvc3process = {inchannel = inchn; outchannel = outchn; errchannel = errchn; pid = npid } in
  ncvc3process

let cvc3_stop_process (process: cvc3process) : unit = 
  let _ = flush process.outchannel in
  let _ = flush stdout in
  let _ = Unix.close (Unix.descr_of_out_channel process.outchannel) in
  let _ = Unix.close (Unix.descr_of_in_channel process.errchannel) in
  let _ = Unix.close (Unix.descr_of_in_channel process.inchannel) in
  let _ = Unix.kill process.pid 9 in
  let _ =  ignore (Unix.waitpid [] process.pid) in
  ()

let log_text_to_cvc3 (str : string) : unit =
	 if !log_cvc3_formula then
	  begin
		output_string !cvc3_log str
	  end

(* return the answer from cvc3process*)
let rec get_answer (process: cvc3process) : string =
  try
    let chr = input_char process.inchannel in
    match chr with
      |'\n' ->  ""
      | 'a'..'z' | 'A'..'Z' -> (Char.escaped chr) ^ get_answer process (*save only alpha characters*)
      | _ -> "" ^ get_answer process
  with
      _ ->   (print_string ("\nexception getting the answer from cvc3: \n" ); flush stdout); ""

let rec read_prompt (process: cvc3process) : string =
  try
    let chr = input_char process.inchannel in
    match chr with
      |'>' -> "" 
      | _ -> (Char.escaped chr) ^ read_prompt process
  with
    |  _ ->   (print_string ("\nexception while reading cvc3 promp \n" ); flush stdout); ""

(*send one command to cvc3 process*)
let send_cmd (process: cvc3process) (cmd: string): unit = 
  try
    let _ = read_prompt process in
    let _ = output_string process.outchannel cmd in
    let _ = log_text_to_cvc3  cmd in    
    let _ = flush process.outchannel in
    ()
  with
      _ ->  (print_string ("\nerror when sending a command: \n" ); flush stdout); ()

let send_cmd_with_answer (process: cvc3process) (cmd: string): string = 
 try
  let _ = send_cmd process cmd in
  let answ = get_answer process in
  answ
 with
      _ ->  (print_string ("\nerror when sending a command and receiveing the answer \n" ); flush stdout); ""


(*all the formulas that shall be send to cvc3 process have to be transformed in cvc3 input language *)
let prepare_formula_for_sending (f : CP.formula) : string =
  cvc3_of_formula f 

(*declares the set of variables included in vars (list of variables) *)
let cvc3_declare_list_of_vars (process: cvc3process) (vars: CP.spec_var list) =
  let int_vars, bool_vars, bag_vars = split_vars vars in
  let bag_var_decls = 
	if Util.empty bag_vars then "" 
	else (String.concat ", " (List.map cvc3_of_spec_var bag_vars)) ^ ": SET;" in
  let int_var_decls = 
	if Util.empty int_vars then "" 
	else (String.concat ", " (List.map cvc3_of_spec_var int_vars)) ^ ": INT;" in
  let bool_var_decls =
	if Util.empty bool_vars then ""
	else (String.concat ", " (List.map cvc3_of_spec_var bool_vars)) ^ ": INT;" in (* BOOLEAN *)
  let var_decls = bool_var_decls ^ bag_var_decls ^ int_var_decls in
 if var_decls = "" then ()
 else 
   let cmd_var_decls = var_decls ^ "\n" in
  let _ = send_cmd process cmd_var_decls in
  ()

(*declares the set of variables included in f formula*)
let cvc3_declare_vars_of_formula (process: cvc3process) (f: CP.formula) = 
  let all_fv = Util.remove_dups (CP.fv f) in
  cvc3_declare_list_of_vars process all_fv

(*asserts a condition to the context active in cvc3process*)
let cvc3_assert (process: cvc3process) (f : CP.formula) =
  let f_str = prepare_formula_for_sending f in
  let cmd = "ASSERT " ^ f_str ^ ";\n" in
  send_cmd process cmd

(*checks for implication*)
let cvc3_query (process: cvc3process) (ante : CP.formula) (conseq : CP.formula) : bool option = 
  (* let _ = (print_string ("\nquery "); flush stdout; ) in  *)
  let _ = log_text_to_cvc3  "%%% imply\n" in
  let ante_fv = CP.fv ante in  
  let conseq_fv = CP.fv conseq in  
  let _ = cvc3_declare_list_of_vars process (ante_fv @ conseq_fv) in
  let _ =  cvc3_assert process ante in
  (*next 3 steps are for flattering the consequent: all the quantified variables are moved in front of the consequent formula separated by type*)
  let (flatted_conseq, quant_list) = remove_quantif conseq [] in
  let ints, bools, bags = split_vars quant_list in 
  let quantif_vars_str = flatten_output ints bools bags in
  (**)
  let n_conseq = prepare_formula_for_sending flatted_conseq in
  let conseq_str =  "QUERY (" ^ quantif_vars_str ^ " ( " ^ n_conseq ^ "));\n" in
  let answer = send_cmd_with_answer process conseq_str in
  let _ = (log_text_to_cvc3  ("%%% Res: " ^ answer ^ " \n\n");  flush !cvc3_log) in
  let r = match answer with
    | "Valid" -> Some _valid
    | "Invalid" -> Some _invalid
    | "Unknown" -> None
    | _ -> None
  in
  r

(*checks the satisfiability of formula f in the active context of cvc3process*)
let cvc3_checksat (process: cvc3process) (f : CP.formula) : bool option = 
  let _ = log_text_to_cvc3 ("%%% is_sat " ^ (*sat_no ^*) "\n") in
  let _ = cvc3_declare_vars_of_formula process f in
  let n_f = prepare_formula_for_sending f in 
  let checksat_str = "CHECKSAT (" ^ n_f ^ ");\n" in
  let answer = send_cmd_with_answer process checksat_str in
  let _ = (log_text_to_cvc3  ("%%% Res: " ^ answer ^ " \n\n");  flush !cvc3_log) in
  let r = match answer with
    | "Satisfiable" ->  Some _sat
    | "Unsatisfiable" ->  Some _unsat
    | "Unknown" ->  None
    | _ -> None 
  in  r

(*restarts an invalid QUERY or satisfiable CHECKSAT with an additional assumption represented by f, using what it has been learnt by now*)
let cvc3_restart_query (process: cvc3process) (f: CP.formula) : bool option = 
  let _ = log_text_to_cvc3 ("%%% restart " ^ (*sat_no ^*) "\n") in
  let n_f = prepare_formula_for_sending f in 
  let restart_str = "RESTART ( "^ n_f ^ " );\n" in 
  let _ = log_text_to_cvc3 restart_str in
  let answer = send_cmd_with_answer process restart_str in
  let _ = (log_text_to_cvc3  ("%%% Res: " ^ answer ^ " \n\n");  flush !cvc3_log) in
  let r = match answer with
    | "Valid" -> Some _valid
    | "Invalid" -> Some _invalid
    | "Satisfiable" ->  Some _sat
    | "Unsatisfiable" ->  Some _unsat
    | "Unknown" ->  None
    | _ -> None
  in r

(*saves the current state in the active context of cvc3process*)
let cvc3_push (process: cvc3process) = 
  let cmd = "PUSH;\n" in
  send_cmd process cmd

(*returns to the state before the last call of PUSH*)
let cvc3_pop (process: cvc3process) = 
  let cmd = "POP;\n" in
  send_cmd process cmd

(*returns to the state before the last call of PUSH made from stack level n*)
let cvc3_popto (process: cvc3process) (n: int) = 
  let cmd = "POPTO " ^ (string_of_int n)  ^ ";\n" in
  send_cmd process cmd

(*simplify f formula and return the simplified formula *)
let cvc3_transform (process: cvc3process) (f: CP.formula) (*: CP.formula*) = ()
  
let imply_helper (ante : CP.formula) (conseq : CP.formula) : bool option =
  let process = cvc3_create_process () in  
  let answer = cvc3_query process ante conseq in
  let _ = cvc3_stop_process process in
  answer

let imply (ante : CP.formula) (conseq : CP.formula) : bool =
  let result0 = imply_helper ante conseq in
  let result = match result0 with
	| Some f -> f
	| None -> begin
		_invalid  (* unknown is assumed to be false *)
		    (*failwith "CVC3 is unable to perform implication check"*)
	  end
  in
  result


let is_sat_helper (f : CP.formula) (sat_no : string) : bool option =
  let process = cvc3_create_process () in
  let answer = cvc3_checksat process f in
  let _ = cvc3_stop_process process in 
  answer
	     
let  is_sat (f : CP.formula) (sat_no : string) : bool =
  let result0 = is_sat_helper f sat_no in
  let result = match result0 with
	| Some f -> f
	| None -> begin
        (log_text_to_cvc3   "%%% is_sat --> true (from unknown)\n\n";  flush !cvc3_log) 
	  end;
	  	  (*failwith "CVC3 is unable to perform satisfiability check"*)
	  	  _sat
  in  result

(*#########################################################################################*)
