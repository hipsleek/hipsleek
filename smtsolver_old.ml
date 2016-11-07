open Globals
module CP = Cpure

module StringSet = Set.Make(String)


(***************************************************************
                  GLOBAL VARIABLES & TYPES                      
 **************************************************************)

(* Types for relations and axioms*)
type rel_def = {
		rel_name : ident;
		rel_vars : CP.spec_var list;
		related_rels : ident list;
		related_axioms : int list;
		rel_cache_smt_declare_fun : string;
	}

(* TODO use hash table for fast retrieval *)
let global_rel_defs = ref ([] : rel_def list)

type axiom_type = 
	| IMPLIES
	| IFF

type axiom_def = {
		axiom_direction	 : axiom_type;
		axiom_hypothesis	: CP.formula;
		axiom_conclusion	: CP.formula;
		related_relations : ident list;
		axiom_cache_smt_assert : string;
	}

(* TODO use hash table for fast retrieval *)
let global_axiom_defs = ref ([] : axiom_def list)

(* Record of information on a formula *)
type formula_info = {
		is_linear          : bool;
		is_quantifier_free : bool;
		contains_array     : bool;
		relations          : ident list; (* list of relations that the formula mentions *)
		axioms             : int list; (* list of related axioms (in form of position in the global list of axiom definitions) *)
	}


(***************************************************************
            TRANSLATE CPURE FORMULA TO SMT FORMULA              
 **************************************************************)

let rec smt_of_typ t = 
	match t with
		| Bool -> "Int" (* Use integer to represent Bool : 0 for false and > 0 for true. *)
		| Float -> "Int" (* Currently, do not support real arithmetic! *)
		| Int -> "Int"
		| UNK -> 	
			Error.report_error {Error.error_loc = no_pos; 
			Error.error_text = "unexpected UNKNOWN type"}
		| NUM -> "Int" (* Use default Int for NUM *)
		| Void | (BagT _) | (TVar _) | List _ ->
			Error.report_error {Error.error_loc = no_pos; 
			Error.error_text = "spec not supported for SMT"}
		| Named _ -> "Int" (* objects and records are just pointers *)
		| Array (et, _) -> "(Array Int " ^ smt_of_typ et ^ ")"

let smt_of_spec_var sv =
	(CP.name_of_spec_var sv) ^ (if CP.is_primed sv then "_primed" else "")

let smt_typed_var_of_spec_var sv =
	"(" ^ (smt_of_spec_var sv) ^ " " ^ (smt_of_typ (CP.type_of_spec_var sv)) ^ ")"

let rec smt_of_exp a =
	match a with
	| CP.Null _ -> "0"
	| CP.Var (sv, _) -> smt_of_spec_var sv
	| CP.IConst (i, _) -> if i >= 0 then string_of_int i else "(- 0 " ^ (string_of_int (0-i)) ^ ")"
	| CP.FConst _ -> failwith ("[smtsolver.ml]: ERROR in constraints (float should not appear here)")
	| CP.Add (a1, a2, _) -> "(+ " ^(smt_of_exp a1)^ " " ^ (smt_of_exp a2)^")"
	| CP.Subtract (a1, a2, _) -> "(- " ^(smt_of_exp a1)^ " " ^ (smt_of_exp a2)^")"
	| CP.Mult (a1, a2, _) -> "( * " ^ (smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
	(* UNHANDLED *)
	| CP.Div _ -> failwith "[smtsolver.ml]: divide is not supported."
	| CP.Bag ([], _) -> "0"
	| CP.Max _
	| CP.Min _ -> failwith ("Smtsolver.smt_of_exp: min/max should not appear here")
  | CP.TypeCast _ -> failwith ("Smtsolver.smt_of_exp: TypeCast should not appear here")
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
		"(select " ^ (smt_of_spec_var a) ^ " " ^ (String.concat " " (List.map smt_of_exp i)) ^ ")"

let rec smt_of_b_formula b =
	let (pf,_) = b in
	match pf with
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
	| CP.BagIn (v, e, l)		-> " in(" ^ (smt_of_spec_var v) ^ ", " ^ (smt_of_exp e) ^ ")"
	| CP.BagNotIn (v, e, l) -> " NOT(in(" ^ (smt_of_spec_var v) ^ ", " ^ (smt_of_exp e) ^"))"
	| CP.BagSub (e1, e2, l) -> " subset(" ^ smt_of_exp e1 ^ ", " ^ smt_of_exp e2 ^ ")"
	| CP.BagMax _ | CP.BagMin _ -> 
			failwith ("smt_of_b_formula: BagMax/BagMin should not appear here.\n")
	| CP.ListIn _ | CP.ListNotIn _ | CP.ListAllN _ | CP.ListPerm _ -> 
			failwith ("smt_of_b_formula: ListIn ListNotIn ListAllN ListPerm should not appear here.\n")
	| CP.RelForm (r, args, l) ->
		let smt_args = List.map smt_of_exp args in 
		(* special relation 'update_array' translate to smt primitive store in array theory *)
		if (r = "update_array") then
			let orig_array = List.nth smt_args 0 in
			let index = List.nth smt_args 1 in
			let value = List.nth smt_args 2 in
			let new_array = List.nth smt_args 3 in
				"(= " ^ new_array ^ " (store " ^ orig_array ^ " " ^ index ^ " " ^ value ^ "))"
		else
			"(" ^ r ^ " " ^ (String.concat " " smt_args) ^ ")"

let rec smt_of_formula f =
	match f with
	| CP.BForm (b,_) -> (smt_of_b_formula b)
	| CP.And (p1, p2, _) -> "(and " ^ (smt_of_formula p1) ^ " " ^ (smt_of_formula p2) ^ ")"
	| CP.Or (p1, p2,_, _) -> "(or " ^ (smt_of_formula p1) ^ " " ^ (smt_of_formula p2) ^ ")"
	| CP.Not (p,_, _) -> "(not " ^ (smt_of_formula p) ^ ")"
	| CP.Forall (sv, p, _,_) ->
		"(forall (" ^ (smt_typed_var_of_spec_var sv) ^ ") " ^ (smt_of_formula p) ^ ")"
	| CP.Exists (sv, p, _,_) ->
		"(exists (" ^ (smt_typed_var_of_spec_var sv) ^ ") " ^ (smt_of_formula p) ^ ")"


(***************************************************************
                       FORMULA INFORMATION                      
 **************************************************************)

(* Default info, returned in most cases *)
let default_formula_info = { 
	is_linear = true; 
	is_quantifier_free = true; 
	contains_array = false; 
	relations = []; 
	axioms = []; }

(* Collect information about a formula f or combined information about 2 formulas *)
let rec collect_formula_info f = 
	let info = collect_formula_info_raw f in
	let indirect_relations = List.flatten (List.map (fun x -> if (List.mem x.rel_name info.relations) then x.related_rels else []) !global_rel_defs) in
	let all_relations = Gen.BList.remove_dups_eq (=) (info.relations @ indirect_relations) in
	let all_axioms = List.flatten (List.map (fun x -> if (List.mem x.rel_name all_relations) then x.related_axioms else []) !global_rel_defs) in
	let all_axioms = Gen.BList.remove_dups_eq (=) all_axioms in
		{info with relations = all_relations; axioms = all_axioms;}

and collect_combine_formula_info f1 f2 = 
	compact_formula_info (combine_formula_info (collect_formula_info f1) (collect_formula_info f2))

(* Recursively collect the information based on the structure of 
 * the formula. This information might not be complete due to cross reference.
 * For instance, a relation definition might refers to other relations. This
 * function is only used mainly in pre-computing information of relation and
 * axiom definition.
 * The information is to be corrected by the function collect_formula_info.
 *)
and collect_formula_info_raw f = match f with
	| CP.BForm ((b,_),_) -> collect_bformula_info b
	| CP.And (f1,f2,_) | CP.Or (f1,f2,_,_) -> 
		collect_combine_formula_info_raw f1 f2
	| CP.Not (f1,_,_) -> collect_formula_info_raw f1
	| CP.Forall (svs,f1,_,_) | CP.Exists (svs,f1,_,_) -> 
		let if1 = collect_formula_info_raw f1 in { if1 with is_quantifier_free = false; }

and collect_combine_formula_info_raw f1 f2 = 
	combine_formula_info (collect_formula_info_raw f1) (collect_formula_info_raw f2)

and collect_bformula_info b = match b with
	| CP.BConst _ | CP.BVar _ -> default_formula_info
	| CP.Lt (e1,e2,_) | CP.Lte (e1,e2,_) | CP.Gt (e1,e2,_) 
	| CP.Gte (e1,e2,_) | CP.Eq (e1,e2,_) | CP.Neq (e1,e2,_) -> 
		let ef1 = collect_exp_info e1 in
		let ef2 = collect_exp_info e2 in
			combine_formula_info ef1 ef2
	| CP.EqMax (e1,e2,e3,_) | CP.EqMin (e1,e2,e3,_) ->
		let ef1 = collect_exp_info e1 in
		let ef2 = collect_exp_info e2 in
		let ef3 = collect_exp_info e3 in
			combine_formula_info (combine_formula_info ef1 ef2) ef3
	| CP.BagIn _ 
	| CP.BagNotIn _ 
	| CP.BagSub _
	| CP.BagMin _
	| CP.BagMax _ 
	| CP.ListIn _
	| CP.ListNotIn _
	| CP.ListAllN _
	| CP.ListPerm _ -> default_formula_info (* Unsupported bag and list; but leave this default_formula_info instead of a fail_with *)
	| CP.RelForm (r,args,_) ->
		if r = "update_array" then
			default_formula_info 
		else let rinfo = { default_formula_info with relations = [r]; } in
			let args_infos = List.map collect_exp_info args in
				combine_formula_info_list (rinfo :: args_infos) (* check if there are axioms then change the quantifier free part *)

and collect_exp_info e = match e with
	| CP.Null _ | CP.Var _ | CP.IConst _ | CP.FConst _ -> default_formula_info
	| CP.Add (e1,e2,_) | CP.Subtract (e1,e2,_) | CP.Max (e1,e2,_) | CP.Min (e1,e2,_) -> 
		let ef1 = collect_exp_info e1 in
		let ef2 = collect_exp_info e2 in
			combine_formula_info ef1 ef2
	| CP.Mult (e1,e2,_) | CP.Div (e1,e2,_) ->
		let ef1 = collect_exp_info e1 in
		let ef2 = collect_exp_info e2 in
		let result = combine_formula_info ef1 ef2 in
			{ result with is_linear = false; }
	| CP.Bag _
	| CP.BagUnion _
	| CP.BagIntersect _
	| CP.BagDiff _
	| CP.List _
	| CP.ListCons _
	| CP.ListHead _
	| CP.ListTail _
	| CP.ListLength _
	| CP.ListAppend _
	| CP.ListReverse _ -> default_formula_info (* Unsupported bag and list; but leave this default_formula_info instead of a fail_with *)
	| CP.ArrayAt (_,i,_) -> combine_formula_info_list (List.map collect_exp_info i)

and combine_formula_info if1 if2 =
	{is_linear = if1.is_linear && if2.is_linear;
	is_quantifier_free = if1.is_quantifier_free && if2.is_quantifier_free;
	contains_array = if1.contains_array || if2.contains_array;
	relations = List.append if1.relations if2.relations;
	axioms = List.append if1.axioms if2.axioms;}

and combine_formula_info_list infos =
	{is_linear = List.fold_left (&&) true 
								(List.map (fun x -> x.is_linear) infos);
	is_quantifier_free = List.fold_left (fun x y -> x && y) true 
								(List.map (fun x -> x.is_quantifier_free) infos);
	contains_array = List.fold_left (fun x y -> x || y) false 
								(List.map (fun x -> x.contains_array) infos);
	relations = List.flatten (List.map (fun x -> x.relations) infos);
	axioms = List.flatten (List.map (fun x -> x.axioms) infos);}

and compact_formula_info info =
	{ info with relations = Gen.BList.remove_dups_eq (=) info.relations;
	            axioms = Gen.BList.remove_dups_eq (=) info.axioms; }


(***************************************************************
                      AXIOMS AND RELATIONS                      
 **************************************************************)

(* Interface function to add a new axiom *)
let add_axiom h dir c =
	let info = collect_combine_formula_info_raw h c in 
	let aindex = List.length !global_axiom_defs in
	begin
		(* Modifying every relations appearing in h and c by
		   1)   Add reference to 'h dir c' as a related axiom
		   2)   Add all other relations (appearing in h and c) to the list of related relations *)
		global_rel_defs := List.map (fun x -> if (List.mem x.rel_name info.relations) then
			let rs = Gen.BList.remove_dups_eq (=) (x.related_rels @ info.relations) in
			let rs = List.filter (fun y -> not (y = x.rel_name)) rs in
			{ x with 
				related_rels = rs;
				related_axioms = x.related_axioms @ [aindex]; }
			else x) !global_rel_defs;
		(* Cache the SMT input for 'h dir c' so that we do not have to generate this over and over again *)
		let cache_smt_input = 
			let params = List.append (CP.fv h) (CP.fv c) in
			let params = Gen.BList.remove_dups_eq CP.eq_spec_var params in
			let smt_params = String.concat " " (List.map smt_typed_var_of_spec_var params) in
			let op = match dir with | IMPLIES -> "=>" | IFF -> "=" in
				"(assert (forall (" ^ smt_params ^ ") (" ^ op ^ " " ^ (smt_of_formula h) ^ " " ^ (smt_of_formula c) ^ ")))\n" in
		(* Add 'h dir c' to the global axioms *)
		let new_axiom = { axiom_direction = dir;
						axiom_hypothesis = h;
						axiom_conclusion = c;
						related_relations = info.relations (* TODO must we compute closure ? *);
						axiom_cache_smt_assert = cache_smt_input; } in
		global_axiom_defs := !global_axiom_defs @ [new_axiom];
	end

(* Interface function to add a new relation *)
let add_relation rname rargs rform =
	if (rname = "update_array") then () else
	(* Cache the declaration for this relation *)
	let cache_smt_input = 
		let signature = List.map CP.type_of_spec_var rargs in
		let smt_signature = String.concat " " (List.map smt_of_typ signature) in
		(* Declare the relation in form of a function --> Bool *)
		"(declare-fun " ^ rname ^ " (" ^ smt_signature ^ ") Bool)\n" in
	let rdef = { rel_name = rname; 
				rel_vars = rargs;
				related_rels = []; (* to be filled up by add_axiom *)
				related_axioms = []; (* to be filled up by add_axiom *)
				rel_cache_smt_declare_fun = cache_smt_input; } in
	begin
		global_rel_defs := !global_rel_defs @ [rdef];
		(* Note that this axiom must be NEW i.e. no relation with this name is added earlier so that add_axiom is correct *)
		match rform with
		| CP.BForm ((CP.BConst (true, no_pos), None), None) (* no definition supplied *) -> (* do nothing *) ()
		| _ -> (* add an axiom to describe the definition *)
			let h = CP.BForm ((CP.RelForm (rname, List.map (fun x -> CP.mkVar x no_pos) rargs, no_pos), None), None) in
				add_axiom h IFF rform;
	end
	

(***************************************************************
                            INTERACTION                         
 **************************************************************)

type sat_type = 
	| Sat		(* solver returns sat *)
	| UnSat		(* solver returns unsat *)
	| Unknown	(* solver returns unknown or there is an exception *)

(* Record structure to store information parsed from the output 
 * of the SMT solver.
 * This change is to make development extensible in later stage.
 *)
type smt_output = {
		original_output_text : string list;	 (* original (command line) output text of the solver; included in order to support printing *)
		sat_result : sat_type; (* satisfiability information *)
		(* expand with other information : proof, time, error, warning, ... *)
	}
	
let string_of_smt_output output =
	match output.sat_result with
	| Sat -> "sat"
	| UnSat -> "unsat"
	| Unknown -> "unknown|timeout"

(* Collect all Z3's output into a list of strings *)
let rec collect_output chn accumulated_output : string list =
	let output = try
					let line = input_line chn in
						collect_output chn (accumulated_output @ [line])
				with
					| End_of_file -> accumulated_output in
		output

let sat_type_from_string r =
	if (r = "sat") then Sat
	else if (r = "unsat") then UnSat
	else Unknown
	
let get_answer chn =
	let output = collect_output chn [] in
	let solver_sat_result = List.nth output (List.length output - 1) in
		{ original_output_text = output;
		sat_result = sat_type_from_string solver_sat_result; }

let remove_file filename =
	try
		Sys.remove filename;
	with
		| e -> ignore e

type smtprover =
	| Z3
	| Cvc3
	| Yices

(* Global settings *)
let infile = "/tmp/in" ^ (string_of_int (Unix.getpid ())) ^ ".smt2"
let outfile = "/tmp/out" ^ (string_of_int (Unix.getpid ()))
let timeout = ref 15.0
let prover_pid = ref 0
let prover_process = ref {
	name = "smtsolver";
	pid = 0;
	inchannel = stdin;
	outchannel = stdout;
	errchannel = stdin 
}

let path_to_z3 = "/home/chanhle/hg/slicing_z3/sleekex/z3/z3/bin/z3" (*"z3"*)
  
let command_for prover =
	match prover with
	| Z3 -> ("z3", path_to_z3, [|"z3"; "-smt2"; infile; ("> "^ outfile)|] )
	| Cvc3 -> ("cvc3", "cvc3", [|"cvc3"; " -lang smt"; infile; ("> "^ outfile)|])
	| Yices -> ("yices", "yices", [|"yices"; infile; ("> "^ outfile)|])

(* Runs the specified prover and returns output *)
let run prover input =
	let out_stream = open_out infile in
	output_string out_stream input;
	close_out out_stream;
	let (cmd, path, cmd_arg) = command_for prover in
	let set_process proc = prover_process := proc in
	let fnc () = 
		let _ = Procutils.PrvComms.start false stdout (cmd, path, cmd_arg) set_process (fun () -> ()) in
			get_answer !prover_process.inchannel in
	let res = try
			Procutils.PrvComms.maybe_raise_timeout fnc () !timeout 
		with
			| _ -> begin (* exception : return the safe result to ensure soundness *)
				Printexc.print_backtrace stdout;
				Unix.kill !prover_process.pid 9;
				ignore (Unix.waitpid [] !prover_process.pid);
				{ original_output_text = []; sat_result = Unknown; }
				end 
	in
	let _ = Procutils.PrvComms.stop false stdout !prover_process 0 9 (fun () -> ()) in
	remove_file infile;
	remove_file outfile;
		res
		

(***************************************************************
   GENERATE SMT INPUT FOR IMPLICATION/SATISFIABILITY CHECKING   
 **************************************************************)


(**
 * Logic types for smt solvers
 * based on smt-lib benchmark specs
 *)
type smtlogic =
	| QF_LIA		(* quantifier free linear integer arithmetic *)
	| QF_NIA		(* quantifier free nonlinear integer arithmetic *)
	| AUFLIA		(* arrays, uninterpreted functions and linear integer arithmetic *)
	| UFNIA		 (* uninterpreted functions and nonlinear integer arithmetic *)

let string_of_logic logic =
	match logic with
	| QF_LIA -> "QF_LIA"
	| QF_NIA -> "QF_NIA"
	| AUFLIA -> "AUFLIA"
	| UFNIA -> "UFNIA"

let logic_for_formulas f1 f2 =
	let finfo = combine_formula_info (collect_formula_info_raw f1) (collect_formula_info_raw f2) in
	let linear = finfo.is_linear in
	let quantifier_free = finfo.is_quantifier_free in
	match linear, quantifier_free with
	| true, true -> QF_LIA 
	| false, true -> QF_NIA 
	| true, false -> AUFLIA (* should I use UFNIA instead? *)
	| false, false -> UFNIA

(* output for smt-lib v2.0 format *)
let to_smt_v2 ante conseq logic fvars info =
  (*let _ = print_endline ("ante = " ^ (!print_pure ante)) in
  let _ = print_endline ("cons = " ^ (!print_pure conseq)) in*)
  
	(* Variable declarations *)
	let smt_var_decls = List.map (fun v -> "(declare-fun " ^ (smt_of_spec_var v) ^ " () " ^ (smt_of_typ (CP.type_of_spec_var v)) ^ ")\n") fvars in
	let smt_var_decls = String.concat "" smt_var_decls in
	(* Relations that appears in the ante and conseq *)
	let used_rels = info.relations in
	let rel_decls = String.concat "" (List.map (fun x -> if (List.mem x.rel_name used_rels) then x.rel_cache_smt_declare_fun else "") !global_rel_defs) in
	(* Necessary axioms *)
	let axiom_asserts = String.concat "" (List.map (fun ax_id -> let ax = List.nth !global_axiom_defs ax_id in ax.axiom_cache_smt_assert) info.axioms) in
	(* Antecedent and consequence : split /\ into small asserts for easier management *)
	let ante_clauses = CP.split_conjunctions ante in
	let ante_clauses = Gen.BList.remove_dups_eq CP.equalFormula ante_clauses in
	let ante_strs = List.map (fun x -> "(assert " ^ (smt_of_formula x) ^ ")\n") ante_clauses in
	let ante_str = String.concat "" ante_strs in
	let conseq_str = smt_of_formula conseq in
		("(set-logic AUFNIA" (* ^ (string_of_logic logic) *) ^ ")\n" ^ 
			";Variables declarations\n" ^ 
				smt_var_decls ^
			";Relations declarations\n" ^ 
				rel_decls ^
			";Axioms assertions\n" ^ 
				axiom_asserts ^
			";Antecedent\n" ^ 
				ante_str ^
			";Negation of Consequence\n" ^ "(assert (not " ^ conseq_str ^ "))\n" ^
			"(check-sat)\n")
	
(* output for smt-lib v1.2 format *)
and to_smt_v1 ante conseq logic fvars =
	let rec defvars vars = match vars with
		| [] -> ""
		| var::rest -> "(" ^ (smt_of_spec_var var) ^ " Int) " ^ (defvars rest)
	in
	let ante = smt_of_formula ante in
	let conseq = smt_of_formula conseq in
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

(* Converts a core pure formula into SMT-LIB format which can be run through various SMT provers. *)
let to_smt (ante : CP.formula) (conseq : CP.formula option) (prover: smtprover) : string =
	let conseq = match conseq with
		(* We don't have conseq part in is_sat checking *)
		| None -> CP.mkFalse no_pos
		| Some f -> f
	in
	let conseq_info = collect_formula_info conseq in
	(* remove occurences of dom in ante if conseq has nothing to do with dom *)
	let ante = if (not (List.mem "dom" conseq_info.relations)) then CP.remove_primitive (fun x -> match x with | CP.RelForm ("dom", _ , _) -> true | _ -> false) ante else ante in
	let ante_info = collect_formula_info ante in
	let info = combine_formula_info ante_info conseq_info in
	let ante_fv = CP.fv ante in
	let conseq_fv = CP.fv conseq in
	let all_fv = Gen.BList.remove_dups_eq (=) (ante_fv @ conseq_fv) in
	let logic = logic_for_formulas ante conseq in
	let res = match prover with
		| Z3 ->	to_smt_v2 ante conseq logic all_fv info
		| Cvc3 | Yices ->	to_smt_v1 ante conseq logic all_fv
	in res
	
	
(***************************************************************
                         CONSOLE OUTPUT                         
 **************************************************************)

type output_configuration = {
		print_input	                 : bool ref; (* print generated SMT input *)
		print_original_solver_output : bool ref; (* print solver original output *)
		print_implication            : bool ref; (* print the implication problems sent to this smt_imply *)
		suppress_print_implication   : bool ref; (* temporary suppress all printing *)
	}

(* Global collection of printing control switches, set by scriptarguments *)
let outconfig = {
		print_input = ref false;
		print_original_solver_output = ref false;
		print_implication = ref false; 
		suppress_print_implication = ref false;
	}

(* Pure formula printing function, to be intialized by cprinter module *)

let print_pure = ref (fun (c:CP.formula) -> " printing not initialized")

(* Function to suppress and unsuppress all output of this modules *)

let suppress_all_output () = outconfig.suppress_print_implication := true

let unsuppress_all_output () = outconfig.suppress_print_implication := false

let process_stdout_print ante conseq input output res =
	if (not !(outconfig.suppress_print_implication)) then
	begin
		if !(outconfig.print_implication) then 
			print_string ("CHECK IMPLICATION:\n" ^ (!print_pure ante) ^ " |- " ^ (!print_pure conseq) ^ "\n");
		if !(outconfig.print_input) then 
			print_string ("Generated SMT input :\n" ^ input);
		if !(outconfig.print_original_solver_output) then
			print_string ("==> SMT output : " ^ (string_of_smt_output output) ^ "\n");
	end
	
	
(**************************************************************
   MAIN INTERFACE : CHECKING IMPLICATION AND SATISFIABILITY    
 *************************************************************)

let try_induction = ref false
let max_induction_level = ref 0

(** 
 * Select the candidates to do induction on. Just find all
 * relation dom(_,low,high) that appears and collect the 
 * { high - low } such that ante |- low <= high.
 *)
let rec collect_induction_value_candidates (ante : CP.formula) (conseq : CP.formula) : (CP.exp list) =
	(*let _ = print_string ("collect_induction_value_candidates :: ante = " ^ (!print_pure ante) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in*)
	match conseq with
		| CP.BForm (b,_) -> (let (p, _) = b in match p with
			| CP.RelForm ("induce",[value],_) -> [value]
			(* | CP.RelForm ("dom",[_;low;high],_) -> (* check if we can prove ante |- low <= high? *) [CP.mkSubtract high low no_pos] *)
			| _ -> [])
		| CP.And (f1,f2,_) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
		| CP.Or (f1,f2,_,_) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
		| CP.Not (f,_,_) -> (collect_induction_value_candidates ante f)
		| CP.Forall _ | CP.Exists _ -> []
	 
(** 
 * Select the value to do induction on.
 * A simple approach : induct on the length of an array.
 *)
and choose_induction_value (ante : CP.formula) (conseq : CP.formula) (vals : CP.exp list) : CP.exp =
	(* TODO Implement the main heuristic here! *)	
	List.hd vals

(** 
 * Create a variable totally different from the ones in vlist.
 *)
and create_induction_var (vlist : CP.spec_var list) : CP.spec_var =
	(*let _ = print_string "create_induction_var\n" in*)
	(* We select the appropriate variable with name "omg_i"*)
	(* with i minimal natural number such that omg_i is not in vlist *)
	let rec create_induction_var_helper vlist i = match vlist with
		| [] -> i
		| hd :: tl -> 
			let v = CP.SpecVar (Int,"omg_" ^ (string_of_int i),Unprimed) in
			if List.mem v vlist then
				create_induction_var_helper tl (i+1)
			else 
				create_induction_var_helper tl i
	in let i = create_induction_var_helper vlist 0 in
		CP.SpecVar (Int,"omg_" ^ (string_of_int i),Unprimed)
		
(** 
 * Generate the base case, induction hypothesis and induction case
 * for a formula phi(v,v_1,v_2,...) with new induction variable v.
 * v = expression of v_1,v_2,...
 *)
(*and gen_induction_formulas (f : formula) (indval : exp) : 
													 (formula * formula * formula) =
	let p = fv f in (* collect free variables in f *)
	let v = create_induction_var p in (* create induction variable *)
	let fv = mkAnd f (mkEqExp (mkVar v no_pos) indval no_pos) no_pos in (* fv(v) = f /\ (v = indval) *)
	let f0 = apply_one_term (v, mkIConst 0 no_pos) fv in (* base case fv[v/0] *)
	let fhyp = mkForall p fv None no_pos in (* induction hypothesis, add universal quantifiers to all free variables in f *)
	let fvp1 = apply_one_term (v, mkAdd (mkVar v no_pos) (mkIConst 1 no_pos) no_pos) fv in (* inductive case fv[v/v+1], we try to prove fhyp --> fv[v/v+1] *)
		(f0, fhyp, fvp1)*)

(** 
 * Generate the base case, induction hypothesis and induction case
 * for Ante -> Conseq
 *)
and gen_induction_formulas (ante : CP.formula) (conseq : CP.formula) (indval : CP.exp) : 
													 ((CP.formula * CP.formula) * (CP.formula * CP.formula)) =
	(*let _ = print_string "gen_induction_formulas\n" in*)
	let p = CP.fv ante @ CP.fv conseq in
	let v = create_induction_var p in 
	(* let _ = print_string ("Inductiom variable = " ^ (CP.string_of_spec_var v) ^ "\n") in *)
	let ante = CP.mkAnd (CP.mkEqExp (CP.mkVar v no_pos) indval no_pos) ante no_pos in
	(* base case ante /\ v = 0 --> conseq *)
	let ante0 = CP.apply_one_term (v, CP.mkIConst 0 no_pos) ante in
	(* let _ = print_string ("Base case: ante = "	^ (!print_pure ante0) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in *)
	(* ante --> conseq *)
	let aimpc = (CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos) in
	(* induction hypothesis = \forall {v_i} : (ante -> conseq) with v_i in p *)
	let indhyp = CP.mkForall p aimpc None no_pos in
	(* let _ = print_string ("Induction hypothesis: ante = "	^ (!print_pure indhyp) ^ "\n") in *)
	let vp1 = CP.mkAdd (CP.mkVar v no_pos) (CP.mkIConst 1 no_pos) no_pos in
	(* induction case: induction hypothesis /\ ante(v+1) --> conseq(v+1) *)
	let ante1 = CP.mkAnd indhyp (CP.apply_one_term (v, vp1) ante) no_pos in
	let conseq1 = CP.apply_one_term (v, vp1) conseq in
	(* let _ = print_string ("Inductive case: ante = "	^ (!print_pure ante1) ^ "\nconseq = " ^ (!print_pure conseq1) ^ "\n") in *)
		((ante0,conseq),(ante1,conseq1))
	
		
(** 
 * Check implication with induction heuristic.
 *)
and smt_imply_with_induction (ante : CP.formula) (conseq : CP.formula) (prover: smtprover) : bool =
	(*let _ = print_string (" :: smt_imply_with_induction : ante = "	^ (!print_pure ante) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in*)
	let vals = collect_induction_value_candidates ante (CP.mkAnd ante conseq no_pos) in
	if (vals = []) then false (* No possible value to do induction on *)
	else
		let indval = choose_induction_value ante conseq vals in
		let bc,ic = gen_induction_formulas ante conseq indval in
		let a0 = fst bc in
		let c0 = snd bc in
		(* check the base case first *)
		let bcv = smt_imply a0 c0 prover in
			if bcv then (* base case is valid *)
				let a1 = fst ic in
				let c1 = snd ic in
				smt_imply a1 c1 prover (* check induction case *)
			else false

(**
 * Test for validity
 * To check the implication P -> Q, we check the satisfiability of
 * P /\ not Q
 * If it is satisfiable, then the original implication is false.
 * If it is unsatisfiable, the original implication is true.
 * We also consider unknown is the same as sat
 *)
and smt_imply (ante : Cpure.formula) (conseq : Cpure.formula) (prover: smtprover) : bool =
	let res, should_run_smt = if (has_exists conseq) then
		try (Omega.imply ante conseq "" !timeout, false) with | _ -> (false, true)
	else (false, true) in
	if (should_run_smt) then
		let input = to_smt ante (Some conseq) prover in
		let output = run prover input in
		let res = match output.sat_result with
			| Sat -> false
			| UnSat -> true
			| Unknown -> try Omega.imply ante conseq "" !timeout with | _ -> false in
		let _ = process_stdout_print ante conseq input output res in
			res
	else
		res
		
and has_exists conseq = match conseq with
	| CP.Exists _ -> true
	| _ -> false

(* For backward compatibility, use Z3 as default *
 * Probably, a better way is modify the tpdispatcher.ml to call imply with a
 * specific smt-prover argument as well *)
let imply ante conseq = 
	smt_imply ante conseq Z3

(**
 * Test for satisfiability
 * We also consider unknown is the same as sat
 *)
let smt_is_sat (f : Cpure.formula) (sat_no : string) (prover: smtprover) : bool =
	let input = to_smt f None prover in
	let output = run prover input in
	let res = match output.sat_result with
		| UnSat -> false
		| _ -> true in
	(*let _ = process_stdout_print f (CP.mkFalse no_pos) input output res in*)
		res

let smt_is_sat (f : Cpure.formula) (sat_no : string) (prover: smtprover) : bool =
	let pr = !print_pure in
	Debug.no_1 "smt_is_sat" pr string_of_bool (fun _ -> smt_is_sat f sat_no prover) f

(* see imply *)
let is_sat f sat_no = smt_is_sat f sat_no Z3

(* let is_sat f sat_no = Debug.loop_2_no "is_sat" (!print_pure) (fun x->x) string_of_bool is_sat f sat_no *)


(**
 * To be implemented
 *)
let simplify (f: CP.formula) : CP.formula = f
let hull (f: CP.formula) : CP.formula = f
let pairwisecheck (f: CP.formula): CP.formula = f
