#include "xdebug.cppo"
open VarGen
open Globals
open VarGen
open GlobProver

module CP = Cpure

let log_cvcl_formula = ref false

(*
let cvcl_in = ref stdin
let cvcl_out = ref stdout
*)

let cvcl_log = ref stdout

let set_log_file fn =
  log_cvcl_formula := true;
  if fn = "" then
	cvcl_log := open_out "formula.cvc"
  else if Sys.file_exists fn then
	failwith "--log-cvcl: file exists"
  else
	cvcl_log := open_out fn

(* 
   Call start at beginning of method, stop at end of method
   to avoid variables clashes (variables with same name but
   different types).
*)

(*
let start () = 
  let tmp_in, tmp_out = Unix.open_process "cvcl +int" in
	cvcl_in := tmp_in;
	cvcl_out := tmp_out

let stop () = Unix.close_process (!cvcl_in, !cvcl_out)

let send_to_cvcl (fstr : string)  = 
  if !log_cvcl_formula then begin
	output_string !cvcl_log fstr;
	flush !cvcl_log
  end;
  output_string !cvcl_out fstr;
  flush !cvcl_out
	
let read_from_cvcl () : string =
  print_string ("here 1\n");
  let resp = input_line !cvcl_in in
	print_string ("here 2\n");
	resp
*)

let predicates = "SET: TYPE;\nTYPE1:TYPE=(INT,SET)->BOOLEAN;
member_uninterpreted:TYPE1;
union: (SET,SET,SET)->BOOLEAN =
    LAMBDA(S1:SET,S2:SET,S:SET):
    FORALL(x:INT):(member_uninterpreted(x, S) <=> (member_uninterpreted(x, S1) OR member_uninterpreted(x, S2)));

subset: (SET,SET)->BOOLEAN=LAMBDA(S1:SET,S2:SET):
    FORALL(x: INT):(member_uninterpreted(x, S1)=>member_uninterpreted(x, S2));

equal: (SET, SET) -> BOOLEAN = LAMBDA(S1:SET,S2:SET):
    subset(S1, S2) AND subset(S2, S1);
		
singleton: (INT, SET) -> BOOLEAN = LAMBDA(v:INT, S:SET):
    FORALL(x:INT): (x=v <=> member_uninterpreted(x, S));

empty: (SET) -> BOOLEAN = LAMBDA(S:SET):
    FORALL(x:INT): (NOT(member_uninterpreted(x, S)));

ASSERT(EXISTS(A: SET): empty(A)); 
ASSERT(FORALL(x: INT): EXISTS(A: SET): singleton(x, A));\n" 

let infilename = !tmp_files_path ^ "input.cvcl." ^ (string_of_int (Unix.getpid ()))

let resultfilename = (!tmp_files_path) ^ "result.txt." ^ (string_of_int (Unix.getpid()))

let cvcl_command = "cvcl " ^ infilename ^ " > " ^ resultfilename

let run_cvcl (input : string) : unit =
  begin
	let chn = open_out infilename in
	  output_string chn input;
	  close_out chn;
	  ignore (Sys.command cvcl_command)
  end

(* printing *)

let rec cvcl_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (_, v, p) -> v ^ (if CP.is_primed sv then "PRMD" else "")

and cvcl_of_exp a = match a with
  | CP.Null _ -> "0"
  | CP.Var (sv, _) -> cvcl_of_spec_var sv
  | CP.IConst (i, _) -> string_of_int i
  | CP.FConst _ -> failwith ("[cvclite.ml]: ERROR in constraints (float should not appear here)")
  | CP.Add (a1, a2, _) ->  (cvcl_of_exp a1) ^ " + " ^ (cvcl_of_exp a2)
  | CP.Subtract (a1, a2, _) ->  (cvcl_of_exp a1) ^ " - " ^ (cvcl_of_exp a2)
  | CP.Mult (a1, a2, _) -> (cvcl_of_exp a1) ^ " * " ^ (cvcl_of_exp a2)
  | CP.Div (a1, a2, _) -> failwith ("[cvclite.ml]: divide is not supported.")
  | CP.Max _ 
  | CP.Min _ -> failwith ("Cvclite.cvcl_of_exp: min/max should not appear here")
  | CP.TypeCast _ -> failwith ("Cvclite.cvcl_of_exp: TypeCast should not appear here")
  | CP.Bag ([], _) -> ""
  | CP.Bag _ | CP.BagUnion _ | CP.BagIntersect _ | CP.BagDiff _ ->
  	  failwith ("[cvcLite.ml]: ERROR in constraints (set should not appear here)");
  | CP.List _ | CP.ListCons _ | CP.ListHead _ | CP.ListTail _ | CP.ListLength _ | CP.ListAppend _ | CP.ListReverse _ ->
      failwith ("Lists are not supported in cvclite")
	| CP.ArrayAt _ ->
      failwith ("Arrays are not supported in cvclite")
	| CP.Func _ ->
      failwith ("Func are not supported in cvclite")
	| CP.AConst _ ->
      failwith ("Aconst not supported in cvclite")
	| CP.Level _ ->
      failwith ("level should not appear in cvclite")
	| CP.Tsconst _ ->
      failwith ("Tsconst not supported in cvclite")
    | CP.NegInfConst _
	| CP.InfConst _ -> failwith ("Infconst not supported in cvclite")
	| CP.Template t -> cvcl_of_exp (CP.exp_of_template t)
	| CP.Bptriple _ ->
      failwith ("cvcl_of_exp: Bptriple not supported in cvclite")
	| CP.Tup2 _ ->
      failwith ("cvcl_of_exp: Tup2 not supported in cvclite")

  
and cvcl_of_b_formula b =
  let (pf,_) = b in
  match pf with
    | CP.Frm (sv, _) -> (cvcl_of_spec_var sv) ^ " = 1"
  | CP.BConst (c, _) -> if c then "(TRUE)" else "(FALSE)"
  | CP.XPure _ -> "(TRUE)" (* WN : weakening *)
  (* | CP.BVar (sv, _) -> cvcl_of_spec_var sv *)
  | CP.BVar (sv, _) -> (cvcl_of_spec_var sv) ^ " = 1"
  | CP.Lt (a1, a2, _) -> (cvcl_of_exp a1) ^ " < " ^ (cvcl_of_exp a2)
  | CP.Lte (a1, a2, _) -> (cvcl_of_exp a1) ^ " <= " ^ (cvcl_of_exp a2)
  | CP.Gt (a1, a2, _) -> (cvcl_of_exp a1) ^ " > " ^ (cvcl_of_exp a2)
  | CP.Gte (a1, a2, _) -> (cvcl_of_exp a1) ^ " >= " ^ (cvcl_of_exp a2)
  | CP.Eq (a1, a2, _) -> (cvcl_of_exp a1) ^ " = " ^ (cvcl_of_exp a2)
  | CP.Neq (a1, a2, _) -> 
	  if CP.is_null a2 then 
		(cvcl_of_exp a1) ^ " > 0"
	  else if CP.is_null a1 then 
		(cvcl_of_exp a2) ^ " > 0"
	  else
		(cvcl_of_exp a1) ^ " /= " ^ (cvcl_of_exp a2)
  | CP.EqMax (a1, a2, a3, _) ->
	  let a1str = cvcl_of_exp a1 in
	  let a2str = cvcl_of_exp a2 in
	  let a3str = cvcl_of_exp a3 in
		"((" ^ a2str ^ " >= " ^ a3str ^ " AND " ^ a1str ^ " = " ^ a2str ^ ") OR (" 
		^ a3str ^ " > " ^ a2str ^ " AND " ^ a1str ^ " = " ^ a3str ^ "))"
  | CP.EqMin (a1, a2, a3, _) ->
	  let a1str = cvcl_of_exp a1 in
	  let a2str = cvcl_of_exp a2 in
	  let a3str = cvcl_of_exp a3 in
		"((" ^ a2str ^ " >= " ^ a3str ^ " AND " ^ a1str ^ " = " ^ a3str ^ ") OR (" 
		^ a3str ^ " > " ^ a2str ^ " AND " ^ a1str ^ " = " ^ a2str ^ "))"
  | CP.BagIn (v, e, l)			-> " in(" ^ (cvcl_of_spec_var v) ^ ", " ^ (cvcl_of_exp e) ^ ")"
  | CP.BagNotIn (v, e, l)	-> " NOT(in(" ^ (cvcl_of_spec_var v) ^ ", " ^ (cvcl_of_exp e) ^"))"
  | CP.BagSub (e1, e2, l)	-> " subset(" ^ cvcl_of_exp e1 ^ ", " ^ cvcl_of_exp e2 ^ ")"
  | CP.BagMax _ | CP.BagMin _ -> failwith ("cvcl_of_b_formula: BagMax/BagMin should not appear here.\n")
  (* | CP.VarPerm _ -> failwith ("cvcl_of_b_formula: VarPerm should not appear here.\n") *)
  | CP.ListIn _
  | CP.ListNotIn _
  | CP.ListAllN _
  | CP.ListPerm _ -> failwith ("Lists are not supported in cvclite")
	| CP.RelForm _ -> failwith ("Relations are not supported in cvclite") 
	| CP.LexVar _ -> failwith ("LexVar are not supported in cvclite") 
	| CP.SubAnn _ -> failwith ("SubAnn are not supported in cvclite") 
	  
and cvcl_of_sv_type sv = match sv with
  | CP.SpecVar ((BagT _), _, _) -> "SET"
  | CP.SpecVar (Bool, _, _) -> "INT" (* "BOOLEAN" *)
  | _ -> "INT"

and cvcl_of_formula f = match f with
  | CP.BForm (b,_) -> "(" ^ (cvcl_of_b_formula b) ^ ")" 
  | CP.And (p1, p2, _) -> "(" ^ (cvcl_of_formula p1 ) ^ " AND " ^ (cvcl_of_formula p2 ) ^ ")"
  | CP.AndList _ -> Gen.report_error no_pos "cvclite.ml: encountered AndList, should have been already handled"
  | CP.Or (p1, p2,_, _) -> "(" ^ (cvcl_of_formula p1 ) ^ " OR " ^ (cvcl_of_formula p2 ) ^ ")"
  | CP.Not (p,_, _) ->
(*	  "(NOT (" ^ (cvcl_of_formula p) ^ "))" *)
	  begin
		match p with
		  | CP.BForm ((CP.BVar (bv, _), _),_) -> (cvcl_of_spec_var bv) ^ " = 0" 
		  | _ -> "(NOT (" ^ (cvcl_of_formula p ) ^ "))"
	  end
  | CP.Forall (sv, p,_, _) ->
	  let typ_str = cvcl_of_sv_type sv in
  		"(FORALL (" ^ (cvcl_of_spec_var sv) ^ ": " ^ typ_str ^ "): " ^ (cvcl_of_formula p ) ^ ")"
  | CP.Exists (sv, p, _,_) -> 
	  let typ_str = cvcl_of_sv_type sv in
  		"(EXISTS (" ^ (cvcl_of_spec_var sv) ^ ": " ^ typ_str ^ "): " ^ (cvcl_of_formula p ) ^ ")"

(*
  split a list of spec_vars to three lists:
  - int vars
  - boolean vars
  - set/bag vars
*)
and split_vars (vars : CP.spec_var list) = (vars, [], [])
(*
and split_vars (vars : CP.spec_var list) = match vars with
  | v :: rest -> begin
	  let ivars, bvars, svars = split_vars rest in
		match v with 
		  | CP.SpecVar (CP.Prim Bool, _, _) -> (ivars, v :: bvars, svars)
		  | CP.SpecVar (CP.Prim Bag, _, _) -> (ivars, bvars, v :: svars)
		  | _ -> (v :: ivars, bvars, svars)
	end
  | [] -> ([], [], [])
*)

and imply_raw (ante : CP.formula) (conseq : CP.formula) : bool option =
  let ante_fv = CP.fv ante in
  let conseq_fv = CP.fv conseq in
  let all_fv = Gen.BList.remove_dups_eq CP.eq_spec_var (ante_fv @ conseq_fv) in
  let int_vars, bool_vars, bag_vars = split_vars all_fv in
  let bag_var_decls = 
	if Gen.is_empty bag_vars then "" 
	else (String.concat ", " (List.map cvcl_of_spec_var bag_vars)) ^ ": SET;\n" in
  let int_var_decls = 
	if Gen.is_empty int_vars then "" 
	else (String.concat ", " (List.map cvcl_of_spec_var int_vars)) ^ ": INT;\n" in
  let bool_var_decls =
	if Gen.is_empty bool_vars then ""
	else (String.concat ", " (List.map cvcl_of_spec_var bool_vars)) ^ ": INT;\n" in (* BOOLEAN *)
  let var_decls = bool_var_decls ^ bag_var_decls ^ int_var_decls in
  let ante_str = (* (cvcl_of_formula_decl ante) ^ (cvcl_of_formula_decl conseq) ^ *)
	"ASSERT (" ^ (cvcl_of_formula ante ) ^ ");\n" in
	(*  let conseq_str =  "QUERY (FORALL (S1: SET): FORALL (S2: SET): EXISTS (S3: SET): union(S1, S2, S3)) 
		=> (" ^ (cvcl_of_formula conseq) ^ ");\n" in *)
  let conseq_str =  "QUERY (" ^ (cvcl_of_formula conseq ) ^ ");\n" in
	(* talk to CVC Lite *)
  let f_cvcl = Gen.break_lines ((*predicates ^*) var_decls ^ ante_str ^ conseq_str) in
	if !log_cvcl_formula then begin
	  output_string !cvcl_log "%%% imply\n";
	  output_string !cvcl_log f_cvcl;
	  flush !cvcl_log
	end;
	run_cvcl f_cvcl;
	let chn = open_in resultfilename in
	let res_str = input_line chn in
	let n = String.length "Valid." in
	let l = String.length res_str in
	  if l >= n then
		let tmp = String.sub res_str 0 n in
		  if tmp = "Valid." then 
			(close_in chn; Some true)
		  else
			let n1 = String.length "Invalid." in
			  if l >= n1 then
				let tmp1 = String.sub res_str 0 n1 in
				  if tmp1 = "Invalid." then
					begin
					  (*
						if Omega.imply ante conseq then
						print_string ("\nimply_raw:inconsistent result for:\n" ^ f_cvcl ^ "\n\n"); 
					  *)
					  (close_in chn; 
					   Some false)
					end
				  else
					((*print_string "imply_raw:Unknown 1";
					   print_string ("\n\n" ^ f_cvcl ^ "\n\n");*)
					  close_in chn; 
					  None)
			  else
				((*print_string "imply_raw:Unknown 2";*) 
				  close_in chn; 
				  None)
	  else 
		((*print_string "imply_raw:Unknown 3";*) 
		  close_in chn; 
		  None)
		  
and imply (ante : CP.formula) (conseq : CP.formula) : bool =
  let result0 = imply_raw ante conseq in
  let result = match result0 with
	| Some f -> f
	| None -> begin
		false  (* unknown is assumed to be false *)
		  (*failwith "CVC Lite is unable to perform implication check"*)
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
  let all_fv = Gen.BList.remove_dups_eq CP.eq_spec_var (CP.fv f) in
  let int_vars, bool_vars, bag_vars = split_vars all_fv in
  let bag_var_decls = 
	if Gen.is_empty bag_vars then "" 
	else (String.concat ", " (List.map cvcl_of_spec_var bag_vars)) ^ ": SET;\n" in
  let int_var_decls = 
	if Gen.is_empty int_vars then "" 
	else (String.concat ", " (List.map cvcl_of_spec_var int_vars)) ^ ": INT;\n" in
  let bool_var_decls =
	if Gen.is_empty bool_vars then ""
	else (String.concat ", " (List.map cvcl_of_spec_var bool_vars)) ^ ": INT;\n" in (* BOOLEAN *)
  let var_decls = bool_var_decls ^ bag_var_decls ^ int_var_decls in
(*
  let f_str = (* (cvcl_of_formula_decl f)  ^ *) 
	"ASSERT (" ^ (cvcl_of_formula f) ^ ");\n" in
  let query_str = "QUERY (1<0);\n" in
*)
  let f_str = cvcl_of_formula f  in
  let query_str = "CHECKSAT (" ^ f_str ^ ");\n" in
	(* talk to CVC Lite *)
  let f_cvcl = Gen.break_lines ( (*predicates ^*) var_decls (* ^ f_str *) ^ query_str) in
	if !log_cvcl_formula then begin
	  output_string !cvcl_log ("%%% is_sat " ^ sat_no ^ "\n");
	  output_string !cvcl_log f_cvcl;
	  flush !cvcl_log
	end;
	run_cvcl f_cvcl;
	let chn = open_in resultfilename in
	let res_str = input_line chn in
	  begin
		let n = String.length "Satisfiable." in
		let l = String.length res_str in
		  if l >= n then
			let tmp = String.sub res_str 0 n in
			  if tmp = "Satisfiable." then 
				begin
				  (*
					if not (Omega.is_sat f) then
					print_string ("\ninconsistent result for:\n" ^ f_cvcl ^ "\n\n");
				  *)
				  close_in chn;
				  Some true
				end
			  else
				let n1 = String.length "Unsatisfiable." in
				  if l >= n1 then
					let tmp1 = String.sub res_str 0 n1 in
					  if tmp1 = "Unsatisfiable." then
						(close_in chn; 
						 Some false)
					  else begin
						(* print_string ("is_sat_raw: Unknown 1\n"); *)
						(close_in chn; 
						 None)
					  end
				  else begin
					(* print_string ("is_sat_raw: Unknown 2\n"); *)
					(close_in chn; 
					 None)
				  end
		  else begin
			(* print_string ("is_sat_raw: Unknown 3\n");
			   print_string ("\n\n" ^ f_cvcl ^ "\n\n"); *)
			(close_in chn; 
			 None)
		  end
	  end
	  
and is_sat (f : CP.formula) (sat_no : string) : bool =
  let result0 = is_sat_raw f sat_no in
  let result = match result0 with
	  | Some f -> f
	  | None -> begin
	  	  if !log_cvcl_formula then begin
	  		output_string !cvcl_log "%%% is_sat --> true (from unknown)\n"
	  	  end;
	  	  (*failwith "CVC Lite is unable to perform satisfiability check"*)
	  	  true
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

(*
and cvcl_of_formula f =
  let body = Gen.break_lines (cvcl_of_formula_helper f) in
  let fvars = Presburger.fv f in
	if List.length fvars > 0 then
	  let fvarsstr = String.concat ", " (List.map string_of_spec_var fvars) in
		"QUERY (FORALL (" ^ fvarsstr ^ ": INT): " ^ body ^ ");\n"
	else
	  "QUERY (" ^ body ^ ");\n"

let write_CVCLite (f : Presburger.pConstr) = 
  let str = cvcl_of_formula f in
	output_string cvcl_log str;
	flush cvcl_log
*)
