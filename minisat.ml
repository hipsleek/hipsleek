open Globals
open Gen.Basic
open Cpure

module StringSet = Set.Make(String)

(* Global settings *)
let eq_logic_timeout_limit = 15.0


let test_number = ref 0
let last_test_number = ref 0
let eq_logic_restart_interval = ref (-1)
let log_all_flag = ref false
let is_eq_logic_running = ref false
let in_timeout = ref 15.0 (* default timeout is 15 seconds *)
let eq_logic_call_count: int ref = ref 0
let log_file = open_out ("allinput.eq_logic")
let eq_logic_input_mode = "file"    (* valid value is: "file" or "stdin" *) 

(*eq_logic*)
let eq_logic_path = "equality_logic"
let eq_logic_name = "equality_logic"
let eq_logic_arg = "equality_logic"

let eq_logic_input_format = "cnf"   (* valid value is: cnf *)
let number_clauses = ref 1
let number_var = ref 0
let eq_logic_process = ref {  name = "eq_logic";
                           pid = 0;
                           inchannel = stdin;
                           outchannel = stdout;
                           errchannel = stdin 
                          }
(***************************************************************
TRANSLATE CPURE FORMULA TO PROBLEM IN CNF FORMAT
**************************************************************)
(*eq_logic*)
let de_morgan f=match f with 
  |Not (And(f1,f2,_),l1,l2)-> Or(Not(f1,l1,l2), Not (f2,l1,l2),l1,l2)
  |Not (Or(f1,f2,_,_),l1,l2)-> And(Not(f1,l1,l2),Not(f2,l1,l2),l2)  
  |_->f
let double_negative f= match f with
  |Not (Not(f1,_,_),_,_)->f1
  |_->f
let eq_logic_cnf_of_spec_var sv = let ident=Cpure.name_of_spec_var sv in ident

let rec eq_logic_of_exp e0 = match e0 with
  | Null _ -> "null_var"
  | Var (sv, _) -> eq_logic_cnf_of_spec_var sv
  | IConst (i, _) -> string_of_int i
  | AConst (i, _) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Add (a1, a2, _) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Subtract (a1, a2, _) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Mult (a1, a2, l) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Div (a1, a2, l) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Max _
  | Min _ -> illegal_format ("eq_logic.eq_logic_of_exp: min/max should not appear here")
  | FConst _ -> illegal_format ("eq_logic.eq_logic_of_exp: FConst")
  | Func _ -> "0" (* TODO: Need to handle *)
  | _ -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
	
	
let  eq_logic_cnf_of_p_formula (pf : Cpure.p_formula) =
  match pf with
  | LexVar _        -> ""
  | BConst (c, _)   -> if c then "true" else "false"
  | BVar (sv, _)    -> eq_logic_cnf_of_spec_var sv
  | Lt _            -> ""
  | Lte _           ->""
  | Gt _            -> ""
  | Gte _           -> ""
  | SubAnn _        -> ""
  | Eq (e1, e2, _)  -> begin
         							 (eq_logic_of_exp e1) ^ " = " ^ (eq_logic_of_exp e2)
  										end
  | Neq (e1, e2, _) -> begin
         							 (eq_logic_of_exp e1) ^ " != " ^ (eq_logic_of_exp e2)
  										end
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

let eq_logic_cnf_of_b_formula (bf : Cpure.b_formula) =
  match bf with
  | (pf, _) -> eq_logic_cnf_of_p_formula pf

let return_pure bf f= match bf with
  | (pf,_)-> match pf with 
             |BConst(_,_)->f
	           |BVar(_,_)->f
						 | Eq _ -> f
						 | Neq _ -> f   

let rec eq_logic_cnf_of_formula f =
  match f with
  | BForm (b, _)         -> return_pure b f
  | And (f1, f2, l1)      ->   And(eq_logic_cnf_of_formula f1,eq_logic_cnf_of_formula f2,l1)  
  | Or (f1, f2, l1, l2)    ->   Or(eq_logic_cnf_of_formula f1,eq_logic_cnf_of_formula f2,l1,l2)    
  | Not (BForm(b,_), _, _) -> return_pure b f
  | _ -> eq_logic_cnf_of_formula (de_morgan (double_negative f));; 

let rec cnf_to_string f = 
  match f with
  |BForm (b,_)-> eq_logic_cnf_of_b_formula b
  |Not (f1,_,_)->"-"^cnf_to_string f1
  |And (f1, f2, _) -> "("^(cnf_to_string f1)^"&"^(cnf_to_string f2)^")"
  |Or  (f1, f2, _, _)->"("^(cnf_to_string f1)^"v"^(cnf_to_string f2)^")"
let incr_cls= number_clauses:=1 + !number_clauses
let check_inmap var map :string= let index= ref 0 in
				 begin
				 for i=0 to (List.length map)-1 do
                                     (
				       if var=(eq_logic_cnf_of_spec_var (List.nth map i)) then (index:=i+1)
				     )
				 done;
				  string_of_int !index
				 end   
let rec cnf_to_string_to_file f (map: spec_var list)= 
  match f with
  |BForm (b,_)-> let var=eq_logic_cnf_of_b_formula b in check_inmap var map 
  |Not (f1,_,_)->"-"^cnf_to_string_to_file f1 map
  |And (f1, f2, _) -> let _= incr_cls in (cnf_to_string_to_file f1 map)^" 0"^"\n"^(cnf_to_string_to_file f2 map)
  |Or  (f1, f2, _, _)-> (cnf_to_string_to_file f1 map)^" "^(cnf_to_string_to_file f2 map)

let rec dnf_to_string_to_orList f = 
  match f with
	|BForm (b,_)->let var=eq_logic_cnf_of_b_formula b in var
	|Not (f1,_,_)->"!"^dnf_to_string_to_orList f1
  |And (f1, f2, _) -> let var= dnf_to_string_to_orList f1 ^" & "^dnf_to_string_to_orList f2  in var  
  |Or  (f1, f2, _, _)-> let _= "" in
																	   begin 
																		let var1= dnf_to_string_to_orList f1  and 
																		var2 = dnf_to_string_to_orList f2 in 
																		var1 ^" | " ^var2  
																     end
(* distributive law 2 - (f | k) & (g | h) -> (f & g) | (f & h) | (k & g) | (k & h) *)

let dist_2 f = 
  match f with
    And(Or(f1, f2,_,_), Or(f3, f4,_,_),_) ->Or(mkOr (mkAnd f1 f3 no_pos) (mkAnd f1  f4 no_pos) None no_pos, mkOr (mkAnd f2 f3 no_pos) (mkAnd f2  f4 no_pos) None no_pos,None,no_pos)
  | And(f1, Or(f2, f3,_,_),_) -> Or(And(f1, f2,no_pos), And(f1, f3,no_pos),None,no_pos)
  | And(Or(f2, f3,_,_), f1,_) -> Or(And(f1, f2,no_pos), And(f1, f3,no_pos),None,no_pos)
  | _ -> f

let rec has_or f =
	match f with
	|BForm _ -> false 
	| Or(_,_,_,_)->true
	|And(f1,f2,_) -> if(has_or f1) then true else if (has_or f2) then true else false
	| _->false

and is_dnf f = 
  match f with
	| BForm _ -> true
	| And (f1,f2,_)-> if(has_or f1) then false  else if (has_or f2) then false else true
	| Or (f1,f2,_,_)-> if(is_dnf f1) then is_dnf f2 else false

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
let nnf_to_dnf f= nnf_to_xxx f dist_2
 
let to_cnf f = nnf_to_cnf (eq_logic_cnf_of_formula f)
let rec to_dnf f = let dnf_form=(nnf_to_dnf (eq_logic_cnf_of_formula f) ) in
 if(is_dnf dnf_form) then dnf_form  else to_dnf dnf_form(*(to_dnf dnf_form)*)

let eq_logic_cnf_of_formula f =
  Debug.no_1 "eq_logic_of_formula" Cprinter.string_of_pure_formula pr_id eq_logic_cnf_of_formula f
	   
(*bach-eq_logic*)

(*************************************************************)
(* Check whether eq_logic can handle the expression, formula... *)
let rec can_eq_logic_handle_expression (exp: Cpure.exp) : bool =
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


and can_eq_logic_handle_p_formula (pf : Cpure.p_formula) : bool =
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

and can_eq_logic_handle_b_formula (bf : Cpure.b_formula) : bool =
  match bf with
  | (pf, _) -> can_eq_logic_handle_p_formula pf

and can_eq_logic_handle_formula (f: Cpure.formula) : bool =
  match f with
  | BForm (bf, _)       -> can_eq_logic_handle_b_formula bf
  | And (f1, f2, _)     -> (can_eq_logic_handle_formula f1) && (can_eq_logic_handle_formula f2)
  | Or (f1, f2, _, _)   -> (can_eq_logic_handle_formula f1) && (can_eq_logic_handle_formula f2)
  | Not (f, _, _)       -> can_eq_logic_handle_formula f
  | Forall (_, f, _, _) -> can_eq_logic_handle_formula f
  | Exists (_, f, _, _) -> can_eq_logic_handle_formula f

(***************************************************************
INTERACTION
**************************************************************)

let rec collect_output (chn: in_channel)  : (string * bool) =
  try
    let line = input_line chn in
(* let _ = print_endline ("  -- output: " ^ line) in*)
    if(line = "SAT") then 
		  (line, true)  
	  else
      collect_output chn 
  with 
  | End_of_file ->  ("", false)

(* read the output stream of eq_logic prover, return (conclusion * reason)    *)
(* TODO: this function need to be optimized                                *)
let get_prover_result (output : string) :bool =
  let validity =
    if (output="SAT") then
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
  eq_logic_process := proc

let start () =
  if not !is_eq_logic_running then (
    print_endline ("Starting eq_logic... \n");
    last_test_number := !test_number;
    let prelude () = () in
    if (eq_logic_input_format = "cnf") then (
(*      Procutils.PrvComms.start !log_all_flag log_file (eq_logic_name, eq_logic_path, [|eq_logic_arg|]) set_process prelude;*)
(*          let ch = Unix.open_process_in "/home/bachle/slicing_minisat/sleekex/equality_logic eqtest_file.txt" in *)
			is_eq_logic_running := true;
    )
  )

(* stop eq_logic system *)
let stop () =
  if !is_eq_logic_running then (
    let num_tasks = !test_number - !last_test_number in
    print_string ("\nStop eq_logic... " ^ (string_of_int !eq_logic_call_count) ^ " invocations "); flush stdout;
    let _ = Procutils.PrvComms.stop !log_all_flag log_file !eq_logic_process num_tasks Sys.sigkill (fun () -> ()) in
    is_eq_logic_running := false;
  )

(* restart Omega system *)
let restart reason =
  if !is_eq_logic_running then (
    let _ = print_string (reason ^ " Restarting eq_logic after ... " ^ (string_of_int !eq_logic_call_count) ^ " invocations ") in
    Procutils.PrvComms.restart !log_all_flag log_file reason "eq_logic" start stop
  )
  else (
    let _ = print_string (reason ^ " not restarting eq_logic ... " ^ (string_of_int !eq_logic_call_count) ^ " invocations ") in ()
  )
    
let check_problem_through_file_eq_logic (input: string list) (timeout: float) : bool =
  (* debug *)
  (* let _ = print_endline "** In function eq_logic.check_problem" in *)
  let infile = "eqtest_file.txt" in
	let result = ref false in
(*  let _ = print_endline ("-- ---------------------------------------------------input: \n" ) in*)
  let check s = if(s="true") then (result := true) else if (s="false")  then ()
	else let out_stream = open_out infile in
											begin
											  output_string out_stream s;
											  close_out out_stream;
(*												let _ = print_endline ("bach: "^s) in*)
												let ch = Unix.open_process_in "/home/bachle/slicing_minisat/sleekex/equality_logic eqtest_file.txt" in 
														 begin
											      eq_logic_call_count := !eq_logic_call_count + 1;
											      let (prover_output, running_state) = get_answer ch in
														is_eq_logic_running := running_state;
(*														remove_file infile;*)
														let status = Unix.close_process_in ch in if(prover_output=true) then result := true
														end
											end in
  let set_process proc = eq_logic_process := proc in
  let _ = 
    if (eq_logic_input_format = "cnf") then (
(*			let _ = print_endline "xuan bach" in*)
		 	let rec check_dnf l = match l with
				|[]->true
				| q::qs->let _= check q in if (!result) then true else check_dnf qs  
				 in  check_dnf input
    )
    else illegal_format "[eq_logic.ml] The value of eq_logic_input_format is invalid!" in
		remove_file infile;
  if (!result=false) then false else true   
(***************************************************************
GENERATE CNF INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
**************************************************************)
(* eq_logic: output for cnf format *)
	  
(*bach*) 
(***************************************************************
GENERATE CNF INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
**************************************************************)
let to_eq_logic (ante : Cpure.formula): string list=
  (* debug *)
  (*let _ = print_endline "** In function to_eq_logic:" in *)
(*		let _= exit 0 in*)
(*		let _= print_endline ("pure: "^Cprinter.string_of_pure_formula ante) in                 *)
(*			let _= print_endline ("pure_dnf: "^Cprinter.string_of_pure_formula ((to_dnf ante))) in*)
	    let anter_str= dnf_to_string_to_orList ((to_dnf ante)) in
(*				let _= print_endline ("dnf: "^anter_str) in*)
(*				let _= List.map (fun x -> print_endline x) !orList in*)
	    let andlist = Str.split((Str.regexp "|"))  anter_str in andlist
(*							let _= List.map (fun x -> print_endline ("andlist:"^x)) andlist in andlist*)

(**************************************************************
MAIN INTERFACE : CHECKING IMPLICATION AND SATISFIABILITY
*************************************************************)

(**
* Test for satisfiability
* We also consider unknown is the same as sat
*)
(*testing decision procedure*)
let eq_logic_is_sat (f : Cpure.formula) (sat_no : string) timeout : bool =                                             
  let res, should_run_eq_logic =
    (false,true) in
  if (should_run_eq_logic) then
    (*let _ = print_endline "-- use eq_logic.check_problem..." in *)
    (* to check sat of f, eq_logic check the validity of negative(f) or (f => None) *)
    let eq_logic_input= to_eq_logic f in
(*		let _ = List.map print_endline eq_logic_input in*)
    let validity =
      if (eq_logic_input_mode = "file") then
        check_problem_through_file_eq_logic eq_logic_input timeout
      else illegal_format "[eq_logic.ml] The value of eq_logic_input_mode is invalid!" in
    (* let validity = check_problem_through_file eq_logic_input timeout in *)
    let res =validity in
    res
  else
    res
		
let eq_logic_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  eq_logic_is_sat f sat_no eq_logic_timeout_limit

(* eq_logic *)
let eq_logic_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  let result = Debug.no_1 "eq_logic_is_sat" pr string_of_bool (fun _ -> eq_logic_is_sat f sat_no) f in
  (* let omega_result = Omega.is_sat f sat_no in
  let _ = print_endline ("-- eq_logic_is_sat result: " ^ (if result then "TRUE" else "FALSE")) in
  let _ = print_endline ("-- Omega.is_sat result: " ^ (if omega_result then "TRUE" else "FALSE")) in *)
  result

(* see imply *)
let is_sat (f: Cpure.formula) (sat_no: string) : bool =
  (* debug *)
  (* let _ = print_endline "** In function eq_logic.is_sat: " in *)
  let result = eq_logic_is_sat f sat_no in
  (*let _ = print_endline ("-- is_sat result: " ^ (if result then "true" else "false")) in *)
  result

let is_sat_with_check (pe : Cpure.formula) sat_no : bool option =
  Cpure.do_with_check "" (fun x -> is_sat x sat_no) pe

(* let is_sat f sat_no = Debug.loop_2_no "is_sat" (!print_pure) (fun x->x) *)
(* string_of_bool is_sat f sat_no                                          *)

let is_sat (pe : Cpure.formula) (sat_no: string) : bool =
  (* let _ = print_endline "** In function eq_logic.is_sat: " in *)
  try
    is_sat pe sat_no;
  with Illegal_Prover_Format s -> (
    print_endline ("\nWARNING : Illegal_Prover_Format for :" ^ s);
    print_endline ("Apply eq_logic.is_sat on formula :" ^ (Cprinter.string_of_pure_formula pe));
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
  (*let _ = print_endline "** In function eq_logic.imply:" in *)
  let ante_fv = Cpure.fv ante in
  let all=Gen.BList.remove_dups_eq (=) (ante_fv) in
(*  let _=List.map (fun x-> print_endline (eq_logic_cnf_of_spec_var x)) all in*)
  let cons=  (mkNot_s conseq) in
    let imply_f= mkAnd ante cons no_pos  in
    let res =is_sat imply_f ""
    in if(res) then false else true
  
let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let _ = print_endline "** In function eq_logic.imply:" in *)
  try
    let result = imply ante conseq timeout in
    (*bach-test*)
      result
    
  with Illegal_Prover_Format s -> (
    print_endline ("\nWARNING : Illegal_Prover_Format for :" ^ s);
    print_endline ("Apply eq_logic.imply on ante Formula :" ^ (Cprinter.string_of_pure_formula ante));
    print_endline ("and conseq Formula :" ^ (Cprinter.string_of_pure_formula conseq));
    flush stdout;
    failwith s
  )

let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let _ = print_endline "** In function eq_logic.imply:" in *)
  Debug.no_1_loop "smt.imply" string_of_float string_of_bool
    (fun _ -> imply ante conseq timeout) timeout

let imply_with_check (ante : Cpure.formula) (conseq : Cpure.formula) (imp_no : string) (timeout: float) : bool option =
  (* let _ = print_endline "** In function eq_logic.imply_with_check:" in *)
  Cpure.do_with_check2 "" (fun a c -> imply a c timeout) ante conseq
(**
* To be implemented
*)

let simplify (f: Cpure.formula) : Cpure.formula =
  (* debug *)
  (* let _ = print_endline "** In function eq_logic.simplify" in *)
  try (Omega.simplify f) with _ -> f

let simplify (pe : Cpure.formula) : Cpure.formula =
  match (Cpure.do_with_check "" simplify pe) with
  | None -> pe
  | Some f -> f

let hull (f: Cpure.formula) : Cpure.formula = f

let pairwisecheck (f: Cpure.formula): Cpure.formula = f

