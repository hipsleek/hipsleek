open Globals
open Gen.Basic
open Cpure

module StringSet = Set.Make(String)

(* Global settings *)
let sugar_timeout_limit = 15.0


let test_number = ref 0
let last_test_number = ref 0
let sugar_restart_interval = ref (-1)
let log_all_flag = ref false
let is_sugar_running = ref false
let in_timeout = ref 15.0 (* default timeout is 15 seconds *)
let sugar_call_count: int ref = ref 0
let log_file = open_out ("allinput.sugar")
let sugar_input_mode = "file"    (* valid value is: "file" or "stdin" *) 
let null_flag = ref false
(*sugar*)
let sugar_path = "sugar"
let sugar_name = "sugar"
let sugar_arg = "sugar -solver \"minisat -pre\""
let sugar_input_format = "csp"   (* valid value is: csp *)
let number_clauses = ref 1
let number_var = ref 0
let sugar_process = ref {  name = "sugar";
                           pid = 0;
                           inchannel = stdin;
                           outchannel = stdout;
                           errchannel = stdin 
                          }
type domainVar = {
	mutable var: string;
	mutable lb: int;
	mutable ub: int;
	}
let listVar = ref ([]: domainVar list)
let numVar = ref 0
let flag = -10000
let execute_with= "eq_neq" (*Or all is for >=,<=,=,!= but we need to assign domains for variables*)
(***************************************************************
TRANSLATE CPURE FORMULA TO PROBLEM IN CSP FORMAT
**************************************************************)
(*sugar*)
let sugar_csp_of_spec_var sv = let ident=Cpure.name_of_spec_var sv in ident

let asign_domain_null lv =
  let domain_null={var="null";lb=1;ub= 1 + (List.length lv)} in  [domain_null] @ lv

let get_list_var f = let fvar=Cpure.fv f in 
	let all_fv = Gen.BList.remove_dups_eq (=) (fvar) in
	let listVarTemp = ref ([]: domainVar list) in
	let mk_domain sv={var=sugar_csp_of_spec_var sv;
			  lb = flag;
			  ub = flag;
			 } 
	in let _= List.map (fun x-> (let domain=mk_domain x in listVarTemp:=[domain] @ !listVarTemp)) all_fv 
	   in  !listVarTemp
													     
let get_list_var_eq_logic f = let fvar=Cpure.fv f in 
	let all_fv = Gen.BList.remove_dups_eq (=) (fvar) in
	let listVarTemp = ref ([]: domainVar list) in
	let mk_domain sv={var=sugar_csp_of_spec_var sv;
			  lb = 1;
			  ub= 1+(List.length all_fv);
			 } 
	in let _= List.map (fun x-> (let domain=mk_domain x in listVarTemp:=[domain] @ !listVarTemp)) all_fv 
	   in  !listVarTemp
						
let asign_domain_lowerbound sv value= 
	let var=sugar_csp_of_spec_var sv in 
	List.map (fun x->if (var=x.var && x.lb=flag) then x.lb<-value )	!listVar
	
let asign_domain_upperbound sv value= 
	let var=sugar_csp_of_spec_var sv in 
	List.map (fun x->if var=x.var && x.ub=flag then x.ub<-value )	!listVar

let rec sugar_of_exp e0 = match e0 with
  | Null _ -> "null"
  | Var (sv, _) -> sugar_csp_of_spec_var sv
  | IConst (i, _) -> string_of_int i 
  | AConst (i, _) -> illegal_format ("sugar.sugar_of_exp: array, bag or list constraint")
  | Add (a1, a2, _) -> "(+ "^(sugar_of_exp a1)^ "  "^(sugar_of_exp a2)^")"
  | Subtract (a1, a2, _) -> "(- "^(sugar_of_exp a1)^ "  "^(sugar_of_exp a2)^")"
  | Mult (a1, a2, l) ->
      let r = match a1 with
        | IConst (i, _) -> "(* "^(string_of_int i) ^ " " ^ (sugar_of_exp a2) ^ " "^")"
        | _ -> let rr = match a2 with
            | IConst (i, _) -> "(* "^(string_of_int i) ^ " " ^ (sugar_of_exp a1) ^ " "^")"
            | _ -> illegal_format "[sugar.ml] Non-linear arithmetic is not supported by sugar."
                (* Error.report_error { *)
                (*   Error.error_loc = l; *)
                (*   Error.error_text = "[sugar.ml] Non-linear arithmetic is not supported by sugar." *)
                (* } *)
            in rr
      in r
  | Div (a1, a2, l) -> 
		let r = match a2 with
        | IConst (i, _) -> "(/ "^(sugar_of_exp a2) ^ " " ^ (string_of_int i) ^ " "^")"
        | _ -> illegal_format "[sugar.ml] Non-linear arithmetic is not supported by sugar."
      in r
      (* Error.report_error { *)
      (*   Error.error_loc = l; *)
      (*   Error.error_text ="[sugar.ml] Divide is not supported." *)
      (* } *)
  | Max _
  | Min _ -> illegal_format ("sugar.sugar_of_exp: min/max should not appear here")
  | FConst _ -> illegal_format ("sugar.sugar_of_exp: FConst")
  | Func _ -> "0" (* TODO: Need to handle *)
  | _ -> illegal_format ("sugar.sugar_of_exp: array, bag or list constraint")
(*
(ArrayAt _|ListReverse _|ListAppend _|ListLength _|ListTail _|ListHead _|
ListCons _|List _|BagDiff _|BagIntersect _|BagUnion _|Bag _|FConst _)
*)

and  sugar_of_b_formula b =
  let (pf, _) = b in
  match pf with
  | BConst (c, _) -> if c then "true" else "false"
  | BVar (bv, _) ->  "bool "^(sugar_csp_of_spec_var bv) (* easy to track boolean var *)
  | Lt (a1, a2, _) ->"(< "^(sugar_of_exp a1) ^ "  " ^ (sugar_of_exp a2)^")"
  | Lte (a1, a2, _) -> "(<= "^(sugar_of_exp a1) ^ " " ^ (sugar_of_exp a2)^")"
  | Gt (a1, a2, _) ->  "(> "^(sugar_of_exp a1) ^ "  " ^ (sugar_of_exp a2)^")"
  | Gte (a1, a2, _) ->  "(>= "^(sugar_of_exp a1) ^ "  " ^ (sugar_of_exp a2)^")"
  | SubAnn (a1, a2, _) -> illegal_format ("sugar.sugar_of_exp: bag or list constraint")
  (* | LexVar (_, a1, a2, _) -> "(0=0)" *)
  | Eq (a1, a2, _) -> begin
         							 "(= "^(sugar_of_exp a1) ^ "  " ^ (sugar_of_exp a2)^")"
  										end
  | Neq (a1, a2, _) -> begin
        							 "(!= "^(sugar_of_exp a1)^ "  " ^ (sugar_of_exp a2)^")"
    									 end
  | EqMax (a1, a2, a3, _) ->illegal_format ("sugar.sugar_of_exp: LexVar 3")
      
  | EqMin (a1, a2, a3, _) ->illegal_format ("sugar.sugar_of_exp: LexVar 3")
  | RelForm _ -> illegal_format ("sugar.sugar_of_exp: RelForm")
  | LexVar _ -> illegal_format ("sugar.sugar_of_exp: LexVar 3")
  | _ -> illegal_format ("sugar.sugar_of_exp: bag or list constraint")

and domain_of_variables b =
	let (pf, _) = b in
  match pf with
  | Lte (a1, a2, _) -> begin
		match (a1,a2) with
		| (IConst (i, _),Var(sv,_)) -> asign_domain_lowerbound sv i; true
		| (Var(sv,_),IConst (i,_)) ->  	 asign_domain_upperbound sv i ; true
		|_ -> true 
	end
  | Gte (a1, a2, _) ->  begin 
		 match (a1,a2) with
		| (IConst (i, _),Var(sv,_)) ->  asign_domain_upperbound sv i; true
		| (Var(sv,_),IConst (i,_)) ->	 asign_domain_lowerbound sv i ; true
		|_-> true 
		end 
  | Eq (a1, a2, _) -> begin 
		match (a1,a2) with
		| (IConst (i, _),Var(sv,_)) (*do sth*)
		| (Var(sv,_),IConst (i,_)) -> (asign_domain_lowerbound sv i; asign_domain_upperbound sv i);true
(*		| (Var(sv,_),Var(sv,_))-> *)
	  |_ ->  false 
	end
	| _-> false
 
			
and sugar_of_formula f  =
  let rec helper f = 
    match f with
  | BForm ((b,_) as bf,_) -> 		
        begin
						if(execute_with<>"eq_neq") then 
					     (domain_of_variables bf;
							  sugar_of_b_formula bf)
								else 
									 sugar_of_b_formula bf
        end
  | And (p1, p2, _) -> 	"(and" ^ (helper p1) ^ "  " ^ (helper p2 ) ^ ")"
  | Or (p1, p2,_ , _) -> 	"(or" ^ (helper p1) ^ "  " ^ (helper p2) ^ ")"
  | Not (p,_ , _) ->       " (not (" ^ (helper p) ^ ")) "	
  | Forall (sv, p,_ , _) -> illegal_format ("sugar.sugar_of_exp: bag or list constraint")
  | Exists (sv, p,_ , _) -> illegal_format ("sugar.sugar_of_exp: bag or list constraint")
  in 
  try
	helper f
  with _ as e -> (print_string ((!print_formula f)^"\n"); raise e)

let sugar_of_formula f =
  Debug.no_1 "sugar_of_formula" Cprinter.string_of_pure_formula pr_id sugar_of_formula f
	   
(*bach-sugar*)

(*************************************************************)
(* Check whether sugar can handle the expression, formula... *)
let rec can_sugar_handle_expression (exp: Cpure.exp) : bool =
  match exp with
  | Cpure.Null _         -> true
  | Cpure.Var _          -> true
  | Cpure.IConst _       -> true
  | Cpure.FConst _       -> false
  | Cpure.AConst _       -> false
  (* arithmetic expressions *)
  | Cpure.Add _
  | Cpure.Subtract _
  | Cpure.Mult _          
  | Cpure.Div _           ->true       
  | Cpure.Max _
  | Cpure.Min _           -> false
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


and can_sugar_handle_p_formula (pf : Cpure.p_formula) : bool =
  match pf with
  | LexVar _             -> false
  | BConst _             -> true
  | BVar _               -> true
  | Lt _                 -> true
  | Lte _                -> true
  | Gt _                 -> true
  | Gte _                -> true
  | SubAnn (ex1, ex2, _) -> false
  | Eq (ex1, ex2, _)     -> true
  | Neq (ex1, ex2, _)    -> true
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

and can_sugar_handle_b_formula (bf : Cpure.b_formula) : bool =
  match bf with
  | (pf, _) -> can_sugar_handle_p_formula pf

and can_sugar_handle_formula (f: Cpure.formula) : bool =
  match f with
  | BForm (bf, _)       -> can_sugar_handle_b_formula bf
  | And (f1, f2, _)     -> (can_sugar_handle_formula f1) && (can_sugar_handle_formula f2)
  | Or (f1, f2, _, _)   -> (can_sugar_handle_formula f1) && (can_sugar_handle_formula f2)
  | Not (f, _, _)       -> can_sugar_handle_formula f
  | Forall (_, f, _, _) -> can_sugar_handle_formula f
  | Exists (_, f, _, _) -> can_sugar_handle_formula f

(***************************************************************
INTERACTION
**************************************************************)

let rec collect_output (chn: in_channel)  : (string * bool) =
  try
    let line = input_line chn in
(* let _ = print_endline ("  -- output: " ^ line) in*)
		if line = "s SATISFIABLE" then
      (line, true)
    else
      collect_output chn 
  with 
  | End_of_file ->  ("", false)

(* read the output stream of sugar prover, return (conclusion * reason)    *)
(* TODO: this function need to be optimized                                *)
let get_prover_result (output : string) :bool =
  let validity =
    if (output="s SATISFIABLE") then
      true
    else
      false in 
  validity

(* output:  - prover_output 
            - the running status of prover: true if running, otherwise false *)
let get_answer (chn: in_channel) : (bool * bool)=
  let (output, running_state) = collect_output chn  in
  let
    validity_result = get_prover_result output;
   in
  (validity_result, running_state)  

let remove_file filename =
  try Sys.remove filename;
  with e -> ignore e

let set_process (proc: Globals.prover_process_t) =
  sugar_process := proc

let start () =
  if not !is_sugar_running then (
(*    print_endline ("Starting sugar... \n");*)
    last_test_number := !test_number;
    let prelude () = () in
    if (sugar_input_format = "csp") then (
      Procutils.PrvComms.start !log_all_flag log_file (sugar_name, sugar_path, [|sugar_arg|]) set_process prelude;
      is_sugar_running := true;
			print_endline ("Starting sugar... \n")
    )
  )

(* stop sugar system *)
let stop () =
  if !is_sugar_running then (
    let num_tasks = !test_number - !last_test_number in
    print_string ("\nStop sugar... " ^ (string_of_int !sugar_call_count) ^ " invocations "); flush stdout;
    let _ = Procutils.PrvComms.stop !log_all_flag log_file !sugar_process num_tasks Sys.sigkill (fun () -> ()) in
    is_sugar_running := false;
  )

(* restart sugar system *)
let restart reason =
  if !is_sugar_running then (
    let _ = print_string (reason ^ " Restarting sugar after ... " ^ (string_of_int !sugar_call_count) ^ " invocations ") in
    Procutils.PrvComms.restart !log_all_flag log_file reason "sugar" start stop
  )
  else (
    let _ = print_string (reason ^ " not restarting sugar ... " ^ (string_of_int !sugar_call_count) ^ " invocations ") in ()
  )
    
(* Runs the specified prover and returns output *)
let check_problem_through_file (input: string list) (timeout: float) : bool =
  (* debug *)
  (* let _ = print_endline "** In function sugar.check_problem" in *)
  let file_suffix = "sg" in
  let infile = "/tmp/in" ^ (file_suffix) ^ ".csp" in
  (*let _ = print_endline ("-- input: \n" ^ input) in*) 
  let out_stream = open_out infile in
  List.map (fun x-> output_string out_stream x) input;
  close_out out_stream;
  let sugar_result="sugarres.txt" in
  let set_process proc = sugar_process := proc in
  let fnc () =
    if (sugar_input_format = "csp") then (
      Procutils.PrvComms.start false stdout (sugar_name, sugar_path, [|sugar_arg;infile|]) set_process (fun () -> ());
      sugar_call_count := !sugar_call_count + 1;
      let (prover_output, running_state) = get_answer !sugar_process.inchannel in
      is_sugar_running := running_state;
      prover_output;
    )
    else illegal_format "[sugar.ml] The value of sugar_input_format is invalid!" in
  let res =
    if not (!dis_provers_timeout) then
    try
      let res = Procutils.PrvComms.maybe_raise_timeout fnc () timeout in
      res
    with _ -> ((* exception : return the safe result to ensure soundness *)
      Printexc.print_backtrace stdout;
      print_endline ("WARNING: Restarting prover due to timeout");
      Unix.kill !sugar_process.pid 9;
      ignore (Unix.waitpid [] !sugar_process.pid);
      false
    )
    else 
      try fnc ()
      with exc -> 
        restart "Restarting Sugar because of timeout.";
        if !Omega.is_omega_running then Omega.restart "Restarting Omega because of timeout.";
        (* failwith "spass timeout"; *)
        remove_file infile;
        raise exc
  in
  let _ = Procutils.PrvComms.stop false stdout !sugar_process 0 9 (fun () -> ()) in
  remove_file infile;
  res
    
(***************************************************************
GENERATE csp INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
**************************************************************)
let domain_to_string list=
	let mk_string record= "(int "^record.var^" "^(string_of_int record.lb) ^" "^ (string_of_int record.ub)^")\n" in
			let str= ref ([]: string list) in
			let _= List.map (fun x-> (*let _=print_endline (mk_string x) in*) str:= [(mk_string x)] @ !str)  list in !str

(* sugar: output for csp format *)
let to_sugar_csp (ante: Cpure.formula)  : string list=
  (*let _ = "** In function Spass.to_sugar_csp" in*)
 (*let _=print_endline ("imply Final Formula :" ^ (Cprinter.string_of_pure_formula ante))in*)
	let func = if(execute_with<>"eq_neq") then listVar := get_list_var ante else listVar := get_list_var_eq_logic ante in 
	(*print_endline "null has been assigned";*)
	let _= listVar := asign_domain_null !listVar in
	let result=sugar_of_formula ante in
	let domain=domain_to_string !listVar in
	let res= domain @ [result] in 
	(*let _= List.map (fun x-> print_endline x) domain in*)
	res
   
(*bach*) 
(***************************************************************
GENERATE csp INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
**************************************************************)
let return_number_var nbv = number_var:= nbv
let to_sugar (ante : Cpure.formula): string list=
  (* debug *)
  (*let _ = print_endline "** In function to_sugar:" in *)
 
  let res = 
    if (sugar_input_format = "csp") then (
	    (* if sending problem in csp format to sugar *)
	    let csp_res = to_sugar_csp ante 
      (* let _ = print_endline ("-- Input problem in csp format:\n" ^ csp_res) in *)
      in csp_res
    ) 
    else illegal_format "[sugar.ml] The value of sugar_input_format is invalid!" in
  res

(**************************************************************
MAIN INTERFACE : CHECKING IMPLICATION AND SATISFIABILITY
*************************************************************)

(**
* Test for satisfiability
* We also consider unknown is the same as sat
*)

let sugar_is_sat (f : Cpure.formula) (sat_no : string) timeout : bool =
  let res, should_run_sugar =
    if not (can_sugar_handle_formula f) then
      try
        let (pr_w,pr_s) = Cpure.drop_complex_ops in
        let optr= Redlog.is_sat f sat_no(*(sugar.is_sat f sat_no)*) in
        match optr with
        | true -> (true, false)
        | false -> (false, false)
      with _ -> (false,false) (* TrungTQ: Maybe BUG: Why res = true in the exception case? It should return UNKNOWN *)
    else (false, true) in
  if (should_run_sugar) then
(*	let _ = print_endline "-- use sugar.check_problem..." in*)
    (* to check sat of f, sugar check the validity of negative(f) or (f => None) *)
    let sugar_input = to_sugar f in
    let validity =
      if (sugar_input_mode = "file") then
        check_problem_through_file sugar_input timeout
      else illegal_format "[sugar.ml] The value of sugar_input_mode is invalid!" in
    (* let validity = check_problem_through_file sugar_input timeout in *)
    let res =validity in
    res
  else
    res
(* sugar *)
let sugar_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  sugar_is_sat f sat_no sugar_timeout_limit

(* sugar *)
let sugar_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  let result = Debug.no_1 "sugar_is_sat" pr string_of_bool (fun _ -> sugar_is_sat f sat_no) f in
  (* let sugar_result = sugar.is_sat f sat_no in
  let _ = print_endline ("-- sugar_is_sat result: " ^ (if result then "TRUE" else "FALSE")) in
  let _ = print_endline ("-- sugar.is_sat result: " ^ (if sugar_result then "TRUE" else "FALSE")) in *)
  result

(* see imply *)
let is_sat (f: Cpure.formula) (sat_no: string) : bool =
  (* debug *)
  (* let _ = print_endline "** In function sugar.is_sat: " in *)
  let result = sugar_is_sat f sat_no in
  (*let _ = print_endline ("-- is_sat result: " ^ (if result then "true" else "false")) in *)
  result

let is_sat_with_check (pe : Cpure.formula) sat_no : bool option =
  Cpure.do_with_check "" (fun x -> is_sat x sat_no) pe

(* let is_sat f sat_no = Debug.loop_2_no "is_sat" (!print_pure) (fun x->x) *)
(* string_of_bool is_sat f sat_no                                          *)

let is_sat (pe : Cpure.formula) (sat_no: string) : bool =
  (* let _ = print_endline "** In function sugar.is_sat: " in *)
  try
    is_sat pe sat_no;
  with Illegal_Prover_Format s -> (
    print_endline ("\nWARNING : Illegal_Prover_Format for :" ^ s);
    print_endline ("Apply sugar.is_sat on formula :" ^ (Cprinter.string_of_pure_formula pe));
    flush stdout;
    failwith s
  )

(**
* Test for validity
* To check the implication P -> Q, we check the satisfiability of
* P /\ not Q
* If it is satisfiable, then the original implication is false.
* If it is unsatisfiable, the original implication is true.
* We also consider unknown is the same as sat
*)
                       
let imply (ante: Cpure.formula) (conseq: Cpure.formula) (timeout: float) : bool =
(*let _ = print_endline "** In function sugar.imply:" in*)
  let ante_fv = Cpure.fv ante in
	let conseq_fv = Cpure.fv conseq in
  let all=Gen.BList.remove_dups_eq (=) (ante_fv @ conseq_fv) in
(* let _=List.map (fun x-> print_endline (sugar_csp_of_spec_var x)) all in*)
  let cons=  (mkNot_s conseq) in
    let imply_f= mkAnd ante cons no_pos  in
(*		let _=print_endline ("Apply sugar.imply on ante Formula :" ^ (Cprinter.string_of_pure_formula imply_f)) in*)
    let res =is_sat imply_f ""
    in if(res) then false else true
  
let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let _ = print_endline "** In function sugar.imply:" in *)
  try
    let result = imply ante conseq timeout in
    (*bach-test*)
      result
    
  with Illegal_Prover_Format s -> (
    print_endline ("\nWARNING : Illegal_Prover_Format for :" ^ s);
    print_endline ("Apply sugar.imply on ante Formula :" ^ (Cprinter.string_of_pure_formula ante));
    print_endline ("and conseq Formula :" ^ (Cprinter.string_of_pure_formula conseq));
    flush stdout;
    failwith s
  )

let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let _ = print_endline "** In function sugar.imply:" in *)
  Debug.no_1_loop "smt.imply" string_of_float string_of_bool
    (fun _ -> imply ante conseq timeout) timeout

let imply_with_check (ante : Cpure.formula) (conseq : Cpure.formula) (imp_no : string) (timeout: float) : bool option =
  (* let _ = print_endline "** In function sugar.imply_with_check:" in *)
  Cpure.do_with_check2 "" (fun a c -> imply a c timeout) ante conseq
(**
* To be implemented
*)

let simplify (f: Cpure.formula) : Cpure.formula =
  (* debug *)
  (* let _ = print_endline "** In function sugar.simplify" in *)
  try (Omega.simplify f) with _ -> f

let simplify (pe : Cpure.formula) : Cpure.formula =
  match (Cpure.do_with_check "" simplify pe) with
  | None -> pe
  | Some f -> f

let hull (f: Cpure.formula) : Cpure.formula = f

let pairwisecheck (f: Cpure.formula): Cpure.formula = f

