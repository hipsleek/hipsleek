open Globals
open Gen.Basic
module CP = Cpure

module StringSet = Set.Make(String)

let set_generated_prover_input = ref (fun _ -> ())
let set_prover_original_output = ref (fun _ -> ())

(* Pure formula printing function, to be intialized by cprinter module *)

let print_pure = ref (fun (c:Cpure.formula) -> " printing not initialized")
let print_ty_sv = ref (fun (c:Cpure.spec_var) -> " printing not initialized")

(***************************************************************
                  GLOBAL VARIABLES & TYPES
 **************************************************************)

(* Types for relations and axioms*)
type rel_def = {
		rel_name : ident;
		rel_vars : Cpure.spec_var list;
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
		axiom_hypothesis	: Cpure.formula;
		axiom_conclusion	: Cpure.formula;
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

let print_pure = ref (fun (c:Cpure.formula)-> " printing not initialized")

(***************************************************************
            TRANSLATE CPURE FORMULA TO SMT FORMULA              
 **************************************************************)

(* Construct [f(1) ... f(n)] *)
let rec generate_list n f =
	if (n = 0) then []
	else (generate_list (n-1) f) @ [f n]

(* Compute the n-th element of the sequence f0, f1, ..., fn defined by f0 = b and f_n = f(f_{n-1}) *)
let rec compute f n b = if (n = 0) then b else f (compute f (n-1) b)
	
let rec smt_of_typ t = 
	match t with
		| Bool -> "Int" (* Use integer to represent Bool : 0 for false and > 0 for true. *)
		| Float -> "Int" (* Currently, do not support real arithmetic! *)
		| Tree_sh -> "Int"
		| Int -> "Int"
		| AnnT -> "Int"
		| UNK -> 
			illegal_format "z3.smt_of_typ: unexpected UNKNOWN type"
		| NUM -> "Int" (* Use default Int for NUM *)
		| Void | (BagT _) | (TVar _) | List _ ->
			illegal_format "z3.smt_of_typ: spec not supported for SMT"
		| Named _ -> "Int" (* objects and records are just pointers *)
		| Array (et, d) -> compute (fun x -> "(Array Int " ^ x  ^ ")") d (smt_of_typ et)
        | RelT -> illegal_format "z3.smt_of_typ: relt not supported for SMT"

let smt_of_spec_var sv =
	(Cpure.name_of_spec_var sv) ^ (if Cpure.is_primed sv then "_primed" else "")

let smt_of_typed_spec_var sv =
  try
	"(" ^ (smt_of_spec_var sv) ^ " " ^ (smt_of_typ (Cpure.type_of_spec_var sv)) ^ ")"
  with _ ->
		illegal_format ("z3.smt_of_typed_spec_var: problem with type of"^(!print_ty_sv sv))


let rec smt_of_exp a =
	match a with
	| Cpure.Null _ -> "0"
	| Cpure.Var (sv, _) -> smt_of_spec_var sv
	| Cpure.IConst (i, _) -> if i >= 0 then string_of_int i else "(- 0 " ^ (string_of_int (0-i)) ^ ")"
	| Cpure.AConst (i, _) -> string_of_heap_ann i
	| Cpure.FConst _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (float should not appear here)")
	| Cpure.Add (a1, a2, _) -> "(+ " ^(smt_of_exp a1)^ " " ^ (smt_of_exp a2)^")"
	| Cpure.Subtract (a1, a2, _) -> "(- " ^(smt_of_exp a1)^ " " ^ (smt_of_exp a2)^")"
	| Cpure.Mult (a1, a2, _) -> "( * " ^ (smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
	(* UNHANDLED *)
	| Cpure.Div _ -> illegal_format ("z3.smt_of_exp: divide is not supported.")
	| Cpure.Bag ([], _) -> "0"
	| Cpure.Max _
	| Cpure.Min _ -> illegal_format ("z3.smt_of_exp: min/max should not appear here")
	| Cpure.Bag _
	| Cpure.BagUnion _
	| Cpure.BagIntersect _
	| Cpure.BagDiff _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (set should not appear here)")
	| Cpure.List _ 
	| Cpure.ListCons _
	| Cpure.ListHead _
	| Cpure.ListTail _
	| Cpure.ListLength _
	| Cpure.ListAppend _
	| Cpure.ListReverse _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (lists should not appear here)")
	| Cpure.Func _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (func should not appear here)")
	| Cpure.Tsconst _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (tsconst should not appear here)")
	| Cpure.ArrayAt (a, idx, l) -> 
		List.fold_left (fun x y -> "(select " ^ x ^ " " ^ (smt_of_exp y) ^ ")") (smt_of_spec_var a) idx

let rec smt_of_b_formula b =
	let (pf,_) = b in
	match pf with
	| Cpure.BConst (c, _) -> if c then "true" else "false"
	| Cpure.BVar (sv, _) -> "(> " ^(smt_of_spec_var sv) ^ " 0)"
	| Cpure.Lt (a1, a2, _) -> "(< " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
	| Cpure.SubAnn (a1, a2, _) -> "(<= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
	| Cpure.Lte (a1, a2, _) -> "(<= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
	| Cpure.Gt (a1, a2, _) -> "(> " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
	| Cpure.Gte (a1, a2, _) -> "(>= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
	| Cpure.Eq (a1, a2, _) -> 
			if Cpure.is_null a2 then
				"(< " ^(smt_of_exp a1)^ " 1)"
			else if Cpure.is_null a1 then
				"(< " ^(smt_of_exp a2)^ " 1)"
			else
				"(= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
	| Cpure.Neq (a1, a2, _) ->
			if Cpure.is_null a2 then
				"(> " ^(smt_of_exp a1)^ " 0)"
			else if Cpure.is_null a1 then
				"(> " ^(smt_of_exp a2)^ " 0)"
			else
				"(not (= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ "))"
	| Cpure.EqMax (a1, a2, a3, _) ->
			let a1str = smt_of_exp a1 in
			let a2str = smt_of_exp a2 in
			let a3str = smt_of_exp a3 in
			"(or (and (= " ^ a1str ^ " " ^ a2str ^ ") (>= "^a2str^" "^a3str^")) (and (= " ^ a1str ^ " " ^ a3str ^ ") (< "^a2str^" "^a3str^")))"
	| Cpure.EqMin (a1, a2, a3, _) ->
			let a1str = smt_of_exp a1 in
			let a2str = smt_of_exp a2 in
			let a3str = smt_of_exp a3 in
			"(or (and (= " ^ a1str ^ " " ^ a2str ^ ") (< "^a2str^" "^a3str^")) (and (= " ^ a1str ^ " " ^ a3str ^ ") (>= "^a2str^" "^a3str^")))"
			(* UNHANDLED *)
	| Cpure.BagIn (v, e, l)		-> " in(" ^ (smt_of_spec_var v) ^ ", " ^ (smt_of_exp e) ^ ")"
	| Cpure.BagNotIn (v, e, l) -> " NOT(in(" ^ (smt_of_spec_var v) ^ ", " ^ (smt_of_exp e) ^"))"
	| Cpure.BagSub (e1, e2, l) -> " subset(" ^ smt_of_exp e1 ^ ", " ^ smt_of_exp e2 ^ ")"
	| Cpure.BagMax _ | Cpure.BagMin _ -> 
			illegal_format ("z3.smt_of_b_formula: BagMax/BagMin should not appear here.\n")
	| Cpure.ListIn _ | Cpure.ListNotIn _ | Cpure.ListAllN _ | Cpure.ListPerm _ -> 
			illegal_format ("z3.smt_of_b_formula: ListIn ListNotIn ListAllN ListPerm should not appear here.\n")
	| Cpure.LexVar _ -> 
			illegal_format ("z3.smt_of_b_formula: LexVar should not appear here.\n")
	| Cpure.VarPerm _ -> 
			illegal_format ("z3.smt_of_b_formula: VarPerm should not appear here.\n")
	| Cpure.RelForm (r, args, l) ->
		let smt_args = List.map smt_of_exp args in 
		(* special relation 'update_array' translate to smt primitive store in array theory *)
		if is_update_array_relation r then
			let orig_array = List.nth smt_args 0 in
			let new_array = List.nth smt_args 1 in
			let value = List.nth smt_args 2 in
			let index = List.rev (List.tl (List.tl (List.tl smt_args))) in
			let last_index = List.hd index in
			let rem_index = List.rev (List.tl index) in
			let arr_select = List.fold_left (fun x y -> let k = List.hd x in ("(select " ^ k ^ " " ^ y ^ ")") :: x) [orig_array] rem_index in
			let arr_select = List.rev arr_select in
			let fl = List.map2 (fun x y -> (x,y)) arr_select (rem_index @ [last_index]) in
			let result = List.fold_right (fun x y -> "(store " ^ (fst x) ^ " " ^ (snd x) ^ " " ^ y ^ ")") fl value in
				"(= " ^ new_array ^ " " ^ result ^ ")"
		else
			"(" ^ (!CP.print_sv r) ^ " " ^ (String.concat " " smt_args) ^ ")"
			
and is_update_array_relation r =
   let r = CP.name_of_spec_var r in
	let udrel = "update_array" in
	let udl = String.length udrel in
		(String.length r) >= udl && (String.sub r 0 udl) = udrel
		
let rec smt_of_formula f =
	match f with
	| Cpure.BForm (b,_) -> (smt_of_b_formula b)
	| Cpure.And (p1, p2, _) -> "(and " ^ (smt_of_formula p1) ^ " " ^ (smt_of_formula p2) ^ ")"
	| CP.AndList _ -> Gen.report_error no_pos "spass.ml: encountered AndList, should have been already handled"
	| Cpure.Or (p1, p2,_, _) -> "(or " ^ (smt_of_formula p1) ^ " " ^ (smt_of_formula p2) ^ ")"
	| Cpure.Not (p,_, _) -> "(not " ^ (smt_of_formula p) ^ ")"
	| Cpure.Forall (sv, p, _,_) ->
		"(forall (" ^ (smt_of_typed_spec_var sv) ^ ") " ^ (smt_of_formula p) ^ ")"
	| Cpure.Exists (sv, p, _,_) ->
		"(exists (" ^ (smt_of_typed_spec_var sv) ^ ") " ^ (smt_of_formula p) ^ ")"

let smt_of_formula f =
  Debug.no_1 "smt_of_formula" !print_pure pr_id smt_of_formula f 

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
	| Cpure.BForm ((b,_),_) -> collect_bformula_info b
	| CP.AndList _ -> Gen.report_error no_pos "spass.ml: encountered AndList, should have been already handled"
	| Cpure.And (f1,f2,_) | Cpure.Or (f1,f2,_,_) -> 
		collect_combine_formula_info_raw f1 f2
	| Cpure.Not (f1,_,_) -> collect_formula_info_raw f1
	| Cpure.Forall (svs,f1,_,_) | Cpure.Exists (svs,f1,_,_) -> 
		let if1 = collect_formula_info_raw f1 in { if1 with is_quantifier_free = false; }

and collect_combine_formula_info_raw f1 f2 = 
	combine_formula_info (collect_formula_info_raw f1) (collect_formula_info_raw f2)

and collect_bformula_info b = match b with
	| Cpure.BConst _ | Cpure.BVar _ -> default_formula_info
	| Cpure.Lt (e1,e2,_) | Cpure.Lte (e1,e2,_) | Cpure.SubAnn (e1,e2,_) | Cpure.Gt (e1,e2,_) 
	| Cpure.Gte (e1,e2,_) | Cpure.Eq (e1,e2,_) | Cpure.Neq (e1,e2,_) -> 
		let ef1 = collect_exp_info e1 in
		let ef2 = collect_exp_info e2 in
			combine_formula_info ef1 ef2
	| Cpure.EqMax (e1,e2,e3,_) | Cpure.EqMin (e1,e2,e3,_) ->
		let ef1 = collect_exp_info e1 in
		let ef2 = collect_exp_info e2 in
		let ef3 = collect_exp_info e3 in
			combine_formula_info (combine_formula_info ef1 ef2) ef3
	| Cpure.BagIn _ 
	| Cpure.BagNotIn _ 
	| Cpure.BagSub _
	| Cpure.BagMin _
	| Cpure.BagMax _ 
	| Cpure.ListIn _
	| Cpure.ListNotIn _
	| Cpure.ListAllN _
	| Cpure.VarPerm _
	| Cpure.ListPerm _ -> default_formula_info (* Unsupported bag and list; but leave this default_formula_info instead of a fail_with *)
	| Cpure.LexVar _ -> default_formula_info
	| Cpure.RelForm (r,args,_) ->
          let r = CP.name_of_spec_var r in
		if r = "update_array" then
			default_formula_info 
		else let rinfo = { default_formula_info with relations = [r]; } in
			let args_infos = List.map collect_exp_info args in
				combine_formula_info_list (rinfo :: args_infos) (* check if there are axioms then change the quantifier free part *)

and collect_exp_info e = match e with
	| Cpure.Null _ | Cpure.Var _ | Cpure.AConst _ | Cpure.IConst _ | Cpure.FConst _ -> default_formula_info
	| Cpure.Add (e1,e2,_) | Cpure.Subtract (e1,e2,_) | Cpure.Max (e1,e2,_) | Cpure.Min (e1,e2,_) -> 
		let ef1 = collect_exp_info e1 in
		let ef2 = collect_exp_info e2 in
			combine_formula_info ef1 ef2
	| Cpure.Mult (e1,e2,_) | Cpure.Div (e1,e2,_) ->
		let ef1 = collect_exp_info e1 in
		let ef2 = collect_exp_info e2 in
		let result = combine_formula_info ef1 ef2 in
			{ result with is_linear = false; }
	| Cpure.Bag _
	| Cpure.BagUnion _
	| Cpure.BagIntersect _
	| Cpure.BagDiff _
	| Cpure.List _
	| Cpure.ListCons _
	| Cpure.ListHead _
	| Cpure.ListTail _
	| Cpure.ListLength _
	| Cpure.ListAppend _
	| Cpure.ListReverse _ -> default_formula_info (* Unsupported bag and list; but leave this default_formula_info instead of a fail_with *)
	| Cpure.Tsconst _ -> default_formula_info
	| Cpure.Func _ -> default_formula_info
	| Cpure.ArrayAt (_,i,_) -> combine_formula_info_list (List.map collect_exp_info i)

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
	(* let _ = print_endline ("Add axiom : " ^ (!print_pure h) ^ (match dir with |IFF -> " <==> " | _ -> " ==> ") ^ (!print_pure c)) in *)
	let info = collect_combine_formula_info_raw h c in
	(* let _ = print_endline ("Directly related relations : " ^ (String.concat "," info.relations)) in *)
	(* assumption: at the time of adding this axiom, all relations in global_rel_defs has their related axioms computed *)
	let indirectly_related_relations = List.filter (fun x -> List.mem x.rel_name info.relations) !global_rel_defs in
	let indirectly_related_relations = List.map (fun x -> x.related_rels) indirectly_related_relations in
	let related_relations = info.relations @ (List.flatten indirectly_related_relations) in
	let related_relations = Gen.BList.remove_dups_eq (=) related_relations in
	(* let _ = print_endline ("All related relations found : " ^ (String.concat ", " related_relations) ^ "\n") in *)
	let aindex = List.length !global_axiom_defs in
	begin
		(* Modifying every relations appearing in h and c by
		   1)   Add reference to 'h dir c' as a related axiom
		   2)   Add all other relations (appearing in h and c) to the list of related relations *)
		global_rel_defs := List.map (fun x ->
			if (List.mem x.rel_name related_relations) then
			let rs = Gen.BList.remove_dups_eq (=) (x.related_rels @ related_relations) in
			{ x with 
				related_rels = rs;
				related_axioms = x.related_axioms @ [aindex]; }
			else x) !global_rel_defs;
		(* Cache the SMT input for 'h dir c' so that we do not have to generate this over and over again *)
		let params = List.append (Cpure.fv h) (Cpure.fv c) in
		let params = Gen.BList.remove_dups_eq Cpure.eq_spec_var params in
		let smt_params = String.concat " " (List.map smt_of_typed_spec_var params) in
		let op = match dir with 
					| IMPLIES -> "=>" 
					| IFF -> "=" in
		let cache_smt_input = "(assert " ^ 
				(if params = [] then "" else "(forall (" ^ smt_params ^ ")\n") ^
				"\t(" ^ op ^ " " ^ (smt_of_formula h) ^ 
				"\n\t" ^ (smt_of_formula c) ^ ")" ^ (* close the main part of the axiom *)
				(if params = [] then "" else ")") (* close the forall if added *) ^ ")\n" (* close the assert *) in
		(* Add 'h dir c' to the global axioms *)
		let new_axiom = { axiom_direction = dir;
						axiom_hypothesis = h;
						axiom_conclusion = c;
						related_relations = related_relations (* info.relations TODO must we compute closure ? *);
						axiom_cache_smt_assert = cache_smt_input; } in
		global_axiom_defs := !global_axiom_defs @ [new_axiom];
	end

(* Interface function to add a new relation *)
let add_relation rname_sv rargs rform =
  if (is_update_array_relation rname_sv) then () else
	(* Cache the declaration for this relation *)
    let rname = CP.name_of_spec_var rname_sv in
	let cache_smt_input = 
	  let signature = List.map Cpure.type_of_spec_var rargs in
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
		| Cpure.BForm ((Cpure.BConst (true, no_pos), None), None) (* no definition supplied *) -> (* do nothing *) ()
		| _ -> (* add an axiom to describe the definition *)
			  let h = Cpure.BForm ((Cpure.RelForm (rname_sv, List.map (fun x -> Cpure.mkVar x no_pos) rargs, no_pos), None), None) in
			  add_axiom h IFF rform;
	end
	

(***************************************************************
                            INTERACTION
 **************************************************************)

type sat_type = 
	| Sat		(* solver returns sat *)
	| UnSat		(* solver returns unsat *)
	| Unknown	(* solver returns unknown or there is an exception *)
	| Aborted (* solver returns an exception *)

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
  (String.concat "\n" output.original_output_text)

(* Collect all Z3's output into a list of strings *)
let rec icollect_output chn accumulated_output : string list =
	let output = try
					 let line = input_line chn in
                    (* let _ = print_endline ("locle2" ^ line) in*)
                     if ((String.length line) > 7) then (*something diff to sat/unsat/unknown, retry-may lead to timeout here*)
					 icollect_output chn (accumulated_output @ [line])
                    else accumulated_output @ [line]
				with
					| End_of_file -> accumulated_output in
		output

let rec collect_output chn accumulated_output : string list =
	let output = try
					let line = input_line chn in
                    (*let _ = print_endline ("locle: " ^ line) in*)
						collect_output chn (accumulated_output @ [line])
				with
					| End_of_file -> accumulated_output in
		output

let sat_type_from_string r input=
	if (r = "sat") then Sat
	else if (r = "unsat") then UnSat
	else
		try
             let _ = Str.search_forward (Str.regexp "unexpected") r 0 in
              (print_string "Z3 translation failure!";
              Error.report_error { Error.error_loc = no_pos; Error.error_text =("Z3 translation failure!!\n"^r^"\n input: "^input)})
            with
              | Not_found -> Unknown

let iget_answer chn input=
	let output = icollect_output chn [] in
    let solver_sat_result = List.nth output (List.length output - 1) in
	{ original_output_text = output;
	  sat_result = sat_type_from_string solver_sat_result input; }

let get_answer chn input=
	let output = collect_output chn [] in
	let solver_sat_result = List.nth output (List.length output - 1) in
		{ original_output_text = output;
		sat_result = sat_type_from_string solver_sat_result input; }

let remove_file filename =
	try
		Sys.remove filename;
	with
		| e -> ignore e

type smtprover = Z3

(* Global settings *)
let infile = "/tmp/in" ^ (string_of_int (Unix.getpid ())) ^ ".smt2"
let outfile = "/tmp/out" ^ (string_of_int (Unix.getpid ()))
(* let sat_timeout = ref 2.0
let imply_timeout = ref 15.0 *)
let z3_sat_timeout_limit = 2.0
let prover_pid = ref 0
let prover_process = ref {
	name = "z3";
	pid = 0;
	inchannel = stdin;
	outchannel = stdout;
	errchannel = stdin 
}

let smtsolver_name = ref ("z3": string)

let z3_call_count: int ref = ref 0
let is_z3_running = ref false


(***********)
let test_number = ref 0
let last_test_number = ref 0
let log_all_flag = ref false
let z3_restart_interval = ref (-1)
let log_all = open_log_out ("allinput.spass")

let path_to_z3 = "z3" (*"z3"*)
let smtsolver_name = ref ("z3": string)
(*let command_for prover ("z3", path_to_z3, [|"z3"; "-smt2"; infile; ("> "^ outfile)|] )*)

let set_process (proc: Globals.prover_process_t) = 
  prover_process := proc

(*for z3-2.19*)
let command_for prover =
(*	match prover with
	| Z3 -> *)
  (match !smtsolver_name with
    | "z3" -> ("z3", [|!smtsolver_name; "-smt2"; infile; ("> "^ outfile) |] )
    | "z3-2.19" -> ("z3-2.19", [|!smtsolver_name; "-smt2"; infile; ("> "^ outfile) |] )
    | _ -> failwith ("unexpected z3 version in spass.ml command_for")
    )
(*	| Cvc3 -> ("cvc3", [|"cvc3"; " -lang smt"; infile; ("> "^ outfile)|])
	| Yices -> ("yices", [|"yices"; infile; ("> "^ outfile)|])
*)

(* Runs the specified prover and returns output *)
let run st prover input timeout =
  (*let _ = print_endline "z3-2.19" in*)
	let out_stream = open_out infile in
    (*let _ = print_endline ("input: " ^ input) in*)
	output_string out_stream input;
	close_out out_stream;
	let (cmd, cmd_arg) = command_for prover in
	let set_process proc = prover_process := proc in
	let fnc () = 
		let _ = Procutils.PrvComms.start false stdout (cmd, cmd, cmd_arg) set_process (fun () -> ()) in
			get_answer !prover_process.inchannel input in
	let res = try
			Procutils.PrvComms.maybe_raise_timeout fnc () timeout
		with
			| _ -> begin (* exception : return the safe result to ensure soundness *)
				Printexc.print_backtrace stdout;
                print_endline ("WARNING for "^st^" : Restarting prover due to timeout");
				Unix.kill !prover_process.pid 9;
				ignore (Unix.waitpid [] !prover_process.pid);
				{ original_output_text = []; sat_result = Aborted; }
				end 
	in
	let _ = Procutils.PrvComms.stop false stdout !prover_process 0 9 (fun () -> ()) in
	remove_file infile;
	remove_file outfile;
		res

(*for z3-3.2*)
let rec prelude () = ()
(*
let init_str = "(set-option :PULL_NESTED_QUANTIFIERS true)\n" in
   output_string (!prover_process.outchannel) init_str;
   flush (!prover_process.outchannel);
*)
(*
  begin
 (* let line = input_line (! prover_process.inchannel) in
	  let _ = print_endline line in
	(if !log_all_flag then
          output_string log_all ("[z3.ml]: >> " ^ line ^ "\nz3 is running\n") ); *)
  (*set logic*)
   let init_str = "(set-logic AUFNIA)\n" in
(set-option :PULL_NESTED_QUANTIFIERS true)
   output_string (!prover_process.outchannel) init_str;
   flush (!prover_process.outchannel);

 (* let finished = ref false in
  while not !finished do
 *)
 (*   let line = input_line (! prover_process.inchannel) in
	  let _ = print_endline line in
	(if !log_all_flag then
          output_string log_all ("[z3.ml]: >> " ^ line ^ "\nz3 is running\n") );*)
(*
    if ((String.length line)>=0) then finished := true;
  done
*)
 end
*)

(* start z3 system in a separated process and load redlog package *)
and start() =
  if not !is_z3_running then begin
      print_string "Starting z3... \n"; flush stdout;
      last_test_number := !test_number;
      (*("z312", path_to_z3, [|path_to_z3; "-smt2";"-si"|])*)
      let _ = if !smtsolver_name = "z3-2.19" then
            Procutils.PrvComms.start !log_all_flag log_all (!smtsolver_name, !smtsolver_name, [|!smtsolver_name;"-smt2"|]) set_process (fun () -> ())
          else
           Procutils.PrvComms.start !log_all_flag log_all (!smtsolver_name, !smtsolver_name, [|!smtsolver_name;"-smt2"; "-si"|]) set_process prelude
      in
      is_z3_running := true;
   (*   let  _ = print_endline "locle: start" in ()*)
  end

(* stop Z3 system *)
let stop () =
  if !is_z3_running then begin
    let num_tasks = !test_number - !last_test_number in
    print_string ("Stop z3... "^(string_of_int !z3_call_count)^" invocations "); flush stdout;
    let _ = Procutils.PrvComms.stop !log_all_flag log_all !prover_process num_tasks Sys.sigkill (fun () -> ()) in
    is_z3_running := false;
  end

(* restart Z3 system *)
let restart reason =
  if !is_z3_running then begin
    let _ = print_string (reason^" Restarting z3 after ... "^(string_of_int !z3_call_count)^" invocations ") in
    Procutils.PrvComms.restart !log_all_flag log_all reason "z3" start stop
  end
  else begin
    let _ = print_string (reason^" not restarting z3 ... "^(string_of_int !z3_call_count)^" invocations ") in ()
    end


(* send formula to z3 and receive result -true/false/unknown*)
let check_formula f timeout =
  (*  try*)
  begin
      if not !is_z3_running then start ()
      else if (!z3_call_count = !z3_restart_interval) then
        begin
	        restart("Regularly restart:1 ");
	        z3_call_count := 0;
        end;
      let fnc f = 
        (*let _ = print_endline "check" in*)
        let _ = incr z3_call_count in
        (*due to global stack - incremental, push current env into a stack before working and
        removing it after that. may be improved *)
        let new_f =
          "(push)\n" ^ f ^ "(pop)\n"
        in
        (*let _ = print_endline ("locle: check\n " ^ new_f) in*)
        output_string (!prover_process.outchannel) new_f;
        flush (!prover_process.outchannel);

        iget_answer (!prover_process.inchannel) f
      in
      let fail_with_timeout () = 
        restart ("[z3.ml]Timeout when checking sat!" ^ (string_of_float timeout));
        { original_output_text = []; sat_result = Unknown; } in
      let res = Procutils.PrvComms.maybe_raise_and_catch_timeout fnc f timeout fail_with_timeout in
      res
  end

let check_formula f timeout =
  Debug.no_2 "Z3:check_formula" (fun x-> x) string_of_float string_of_smt_output
      check_formula f timeout


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
	let smt_var_decls = List.map (fun v -> "(declare-fun " ^ (smt_of_spec_var v) ^ " () " ^ (smt_of_typ (Cpure.type_of_spec_var v)) ^ ")\n") fvars in
	let smt_var_decls = String.concat "" smt_var_decls in
	(* Relations that appears in the ante and conseq *)
	let used_rels = info.relations in
	(* let rel_decls = String.concat "" (List.map (fun x -> x.rel_cache_smt_declare_fun) !global_rel_defs) in *)
	let rel_decls = String.concat "" (List.map (fun x -> if (List.mem x.rel_name used_rels) then x.rel_cache_smt_declare_fun else "") !global_rel_defs) in
	(* Necessary axioms *)
	(* let axiom_asserts = String.concat "" (List.map (fun x -> x.axiom_cache_smt_assert) !global_axiom_defs) in *) (* Add all axioms; in case there are bugs! *)
	let axiom_asserts = String.concat "" (List.map (fun ax_id -> let ax = List.nth !global_axiom_defs ax_id in ax.axiom_cache_smt_assert) info.axioms) in
	(* Antecedent and consequence : split /\ into small asserts for easier management *)
	let ante_clauses = Cpure.split_conjunctions ante in
	let ante_clauses = Gen.BList.remove_dups_eq Cpure.equalFormula ante_clauses in
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
			"(check-sat)")
	
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
let to_smt (ante : Cpure.formula) (conseq : Cpure.formula option) (prover: smtprover) : string =
	let conseq = match conseq with
		(* We don't have conseq part in is_sat checking *)
		| None -> Cpure.mkFalse no_pos
		| Some f -> f
	in
	let conseq_info = collect_formula_info conseq in
	(* remove occurences of dom in ante if conseq has nothing to do with dom *)
	let ante = if (not (List.mem "dom" conseq_info.relations)) then Cpure.remove_primitive (fun x -> 
        match x with 
          | Cpure.RelForm (v, _ , _) -> (CP.name_of_spec_var v = "dom")
          | _ -> false) ante else ante in
	let ante_info = collect_formula_info ante in
	let info = combine_formula_info ante_info conseq_info in
	let ante_fv = Cpure.fv ante in
	let conseq_fv = Cpure.fv conseq in
	let all_fv = Gen.BList.remove_dups_eq (=) (ante_fv @ conseq_fv) in
	let logic = logic_for_formulas ante conseq in
	let res = to_smt_v2 ante conseq logic all_fv info in
  print_endline "<=== in function to_smt ";
  print_endline "res:";
  print_endline res;
  print_endline "===>";
  res
	(*	| Cvc3 | Yices ->	to_smt_v1 ante conseq logic all_fv*)

(* trungtq: function convert from cpure to DFG format *)
let to_dfg (ante: Cpure.formula) (conseq: Cpure.formula option) : string =
  (*let conseq = match conseq with
    | None   -> Cpure.mkFalse no_pos
    | Some f -> f
  in*)
  ""
	
	
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

(* Function to suppress and unsuppress all output of this modules *)

let suppress_all_output () = outconfig.suppress_print_implication := true

let unsuppress_all_output () = outconfig.suppress_print_implication := false

let process_stdout_print ante conseq input output res =
	if (not !(outconfig.suppress_print_implication)) then
	begin
		if !(outconfig.print_implication) then 
			print_endline ("CHECKING IMPLICATION:\n\n" ^ (!print_pure ante) ^ " |- " ^ (!print_pure conseq) ^ "\n");
		if !(outconfig.print_input) then 
            begin
			  print_endline (">>> GENERATED SMT INPUT:\n\n" ^ input);
              flush stdout;
            end;
		if !(outconfig.print_original_solver_output) then
		begin
			print_endline (">>> Z3 OUTPUT RECEIVED:\n" ^ (string_of_smt_output output));
			print_endline (match output.sat_result with
				| UnSat -> ">>> VERDICT: UNSAT/VALID!"
				| Sat -> ">>> VERDICT: FAILED!"
				| Unknown -> ">>> VERDICT: UNKNOWN! CONSIDERED AS FAILED."
	            | Aborted -> ">>> VERDICT: ABORTED! CONSIDERED AS FAILED.");
            flush stdout;
		end;
		if (!(outconfig.print_implication) || !(outconfig.print_input) || !(outconfig.print_original_solver_output)) then
			print_string "\n";
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
let rec collect_induction_value_candidates (ante : Cpure.formula) (conseq : Cpure.formula) : (Cpure.exp list) =
  (*let _ = print_string ("collect_induction_value_candidates :: ante = " ^ (!print_pure ante) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in*)
  match conseq with
	| Cpure.BForm (b,_) -> (let (p, _) = b in match p with
		| Cpure.RelForm (v,[value],_) -> 
              if "induce"=CP.name_of_spec_var v then [value] else []
			  (* | Cpure.RelForm ("dom",[_;low;high],_) -> (* check if we can prove ante |- low <= high? *) [Cpure.mkSubtract high low no_pos] *)
		| _ -> [])
	| Cpure.And (f1,f2,_) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
	| CP.AndList _ -> Gen.report_error no_pos "spass.ml: encountered AndList, should have been already handled"
	| Cpure.Or (f1,f2,_,_) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
	| Cpure.Not (f,_,_) -> (collect_induction_value_candidates ante f)
	| Cpure.Forall _ | Cpure.Exists _ -> []
	      
(** 
    * Select the value to do induction on.
    * A simple approach : induct on the length of an array.
*)
and choose_induction_value (ante : Cpure.formula) (conseq : Cpure.formula) (vals : Cpure.exp list) : Cpure.exp =
  (* TODO Implement the main heuristic here! *)	
  List.hd vals

(** 
    * Create a variable totally different from the ones in vlist.
*)
and create_induction_var (vlist : Cpure.spec_var list) : Cpure.spec_var =
  (*let _ = print_string "create_induction_var\n" in*)
  (* We select the appropriate variable with name "omg_i"*)
  (* with i minimal natural number such that omg_i is not in vlist *)
  let rec create_induction_var_helper vlist i = match vlist with
	| [] -> i
	| hd :: tl -> 
		  let v = Cpure.SpecVar (Int,"omg_" ^ (string_of_int i),Unprimed) in
		  if List.mem v vlist then
			create_induction_var_helper tl (i+1)
		  else 
			create_induction_var_helper tl i
  in let i = create_induction_var_helper vlist 0 in
  Cpure.SpecVar (Int,"omg_" ^ (string_of_int i),Unprimed)
	  
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
and gen_induction_formulas (ante : Cpure.formula) (conseq : Cpure.formula) (indval : Cpure.exp) : 
	  ((Cpure.formula * Cpure.formula) * (Cpure.formula * Cpure.formula)) =
  (*let _ = print_string "gen_induction_formulas\n" in*)
  let p = Cpure.fv ante @ Cpure.fv conseq in
  let v = create_induction_var p in 
  (* let _ = print_string ("Inductiom variable = " ^ (Cpure.string_of_spec_var v) ^ "\n") in *)
  let ante = Cpure.mkAnd (Cpure.mkEqExp (Cpure.mkVar v no_pos) indval no_pos) ante no_pos in
  (* base case ante /\ v = 0 --> conseq *)
  let ante0 = Cpure.apply_one_term (v, Cpure.mkIConst 0 no_pos) ante in
  (* let _ = print_string ("Base case: ante = "	^ (!print_pure ante0) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in *)
  (* ante --> conseq *)
  let aimpc = (Cpure.mkOr (Cpure.mkNot ante None no_pos) conseq None no_pos) in
  (* induction hypothesis = \forall {v_i} : (ante -> conseq) with v_i in p *)
  let indhyp = Cpure.mkForall p aimpc None no_pos in
  (* let _ = print_string ("Induction hypothesis: ante = "	^ (!print_pure indhyp) ^ "\n") in *)
  let vp1 = Cpure.mkAdd (Cpure.mkVar v no_pos) (Cpure.mkIConst 1 no_pos) no_pos in
  (* induction case: induction hypothesis /\ ante(v+1) --> conseq(v+1) *)
  let ante1 = Cpure.mkAnd indhyp (Cpure.apply_one_term (v, vp1) ante) no_pos in
  let conseq1 = Cpure.apply_one_term (v, vp1) conseq in
  (* let _ = print_string ("Inductive case: ante = "	^ (!print_pure ante1) ^ "\nconseq = " ^ (!print_pure conseq1) ^ "\n") in *)
  ((ante0,conseq),(ante1,conseq1))
	  
	  
(** 
    * Check implication with induction heuristic.
*)
and smt_imply_with_induction (ante : Cpure.formula) (conseq : Cpure.formula) (prover: smtprover) : bool =
  (*let _ = print_string (" :: smt_imply_with_induction : ante = "	^ (!print_pure ante) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in*)
  let vals = collect_induction_value_candidates ante (Cpure.mkAnd ante conseq no_pos) in
  if (vals = []) then false (* No possible value to do induction on *)
  else
	let indval = choose_induction_value ante conseq vals in
	let bc,ic = gen_induction_formulas ante conseq indval in
	let a0 = fst bc in
	let c0 = snd bc in
	(* check the base case first *)
	let bcv = smt_imply a0 c0 prover 15.0 in
	if bcv then (* base case is valid *)
	  let a1 = fst ic in
	  let c1 = snd ic in
	  smt_imply a1 c1 prover 15.0 (* check induction case *)
	else false

(**
   * Test for validity
   * To check the implication P -> Q, we check the satisfiability of
   * P /\ not Q
   * If it is satisfiable, then the original implication is false.
   * If it is unsatisfiable, the original implication is true.
   * We also consider unknown is the same as sat
*)

and smt_imply (ante : Cpure.formula) (conseq : Cpure.formula) (prover: smtprover) timeout : bool =
  let pr = !print_pure in
  Debug.no_2_loop "smt_imply" (pr_pair pr pr) string_of_float string_of_bool
      (fun _ _ -> smt_imply_x ante conseq prover timeout) (ante,conseq) timeout

and smt_imply_x (ante : Cpure.formula) (conseq : Cpure.formula) (prover: smtprover) timeout : bool =
  (* let _ = print_endline ("smt_imply : " ^ (!print_pure ante) ^ " |- " ^ (!print_pure conseq) ^ "\n") in *)
  let res, should_run_smt = if (has_exists conseq) then
        let (pr_w,pr_s) = Cpure.drop_complex_ops in
	try (match (Omega.imply_with_check_ops pr_w pr_s ante conseq "" timeout) with
	  | None -> (false, true)
	  | Some r -> (r, false)
	)
	with | _ -> (false, true)
  else (false, true) in
  if (should_run_smt) then
	let input = to_smt ante (Some conseq) prover in
	let _ = !set_generated_prover_input input in
        let output = if !smtsolver_name = "z3-2.19" then
              run "is_imply" prover input timeout
            else
              check_formula input timeout
        in
        let _ = !set_prover_original_output (String.concat "\n" output.original_output_text) in
	let res = match output.sat_result with
	  | Sat -> false
	  | UnSat -> true
	  | Unknown -> false
	  | Aborted -> false
            (* try Omega.imply ante conseq "" !imply_timeout  *)
            (* with | _ -> false *)
    in
	let _ = process_stdout_print ante conseq input output res in
	res
  else
	res
and has_exists conseq = match conseq with
  | Cpure.Exists _ -> true
  | _ -> false

(* For backward compatibility, use Z3 as default *
 * Probably, a better way is modify the tpdispatcher.ml to call imply with a
 * specific smt-prover argument as well *)
let imply ante conseq timeout =
  (*let _ = print_endline ("imply :" ^ (string_of_float timeout)) in*)
	smt_imply ante conseq Z3 timeout

let imply_with_check (ante : Cpure.formula) (conseq : Cpure.formula) (imp_no : string) timeout: bool option =
  Cpure.do_with_check2 "" (fun a c -> imply a c timeout) ante conseq

let imply (ante : Cpure.formula) (conseq : Cpure.formula) timeout: bool =
  try
      (* let timeo = match timeout with *)
      (*   | 0. -> z3_timeout *)
      (*   |_ -> timeout *)
      (* in *)
    imply ante conseq timeout
  with Illegal_Prover_Format s -> 
      begin
        print_endline ("\nWARNING : Illegal_Prover_Format for :"^s);
        print_endline ("Apply z3.imply on ante Formula :"^(!print_pure ante));
		print_endline ("and conseq Formula :"^(!print_pure conseq));
        flush stdout;
        failwith s
      end

let imply (ante : Cpure.formula) (conseq : Cpure.formula) timeout: bool =
  Debug.no_1_loop "smt.imply" string_of_float string_of_bool
      (fun _ -> imply ante conseq timeout) timeout

(**
 * Test for satisfiability
 * We also consider unknown is the same as sat
 *)
let smt_is_sat (f : Cpure.formula) (sat_no : string) (prover: smtprover) timeout : bool = 
	(* let _ = print_endline ("smt_is_sat : " ^ (!print_pure f) ^ "\n") in *)
  let res, should_run_smt = if ((*has_exists*)Cpure.contains_exists f)   then
		try
             let (pr_w,pr_s) = Cpure.drop_complex_ops in
            let optr= (Omega.is_sat_with_check_ops pr_w pr_s f sat_no) in
        ( match optr with
          | Some r -> (r, false)
          | None -> (true, false)
        )
        with | _ -> (true, false)
	else (false, true) in
	if (should_run_smt) then
	let input = to_smt f None prover in
(*    let new_input =
    if (Cpure.contains_exists f) then
      ("(set-option :mbqi true)\n" ^ input)
    else input in *)
	let output =
      if !smtsolver_name = "z3-2.19" then run "is_unsat" prover input timeout
      else check_formula input timeout
    in
	let res = match output.sat_result with
		| UnSat -> false
		| _ -> true in
	let _ = process_stdout_print f (Cpure.mkFalse no_pos) input output res in
		res
    else res

(*let default_is_sat_timeout = 2.0*)

let smt_is_sat (f : Cpure.formula) (sat_no : string) (prover: smtprover) : bool =
  smt_is_sat f sat_no prover z3_sat_timeout_limit

let smt_is_sat (f : Cpure.formula) (sat_no : string) (prover: smtprover): bool =
	let pr = !print_pure in
	Debug.no_1 "smt_is_sat" pr string_of_bool (fun _ -> smt_is_sat f sat_no prover) f

(* see imply *)
let is_sat f sat_no =
  smt_is_sat f sat_no Z3

let is_sat_with_check (pe : Cpure.formula) sat_no : bool option =
  Cpure.do_with_check "" (fun x -> is_sat x sat_no) pe 

(* let is_sat f sat_no = Debug.loop_2_no "is_sat" (!print_pure) (fun x->x) string_of_bool is_sat f sat_no *)

let is_sat (pe : Cpure.formula) sat_no : bool =
  try
    is_sat pe sat_no
  with Illegal_Prover_Format s -> 
      begin
        print_endline ("\nWARNING : Illegal_Prover_Format for :"^s);
        print_endline ("Apply z3.is_sat on formula :"^(!print_pure pe));
        flush stdout;
        failwith s
      end



(**
 * To be implemented
 *)
let simplify (f: Cpure.formula) : Cpure.formula = (*f*)
  (*let _ = print_endline "locle: simplify" in*)
  try (Omega.simplify f) with | _ -> f


let simplify (pe : Cpure.formula) : Cpure.formula =
  match (Cpure.do_with_check "" simplify pe)
  with 
    | None -> pe
    | Some f -> f

let hull (f: Cpure.formula) : Cpure.formula = f
let pairwisecheck (f: Cpure.formula): Cpure.formula = f

