(*
  Create the input file for Coq
*)

open Globals
module CP = Cpure

let coq_file_number = ref 0
let result_file_name = "res"
let log_all_flag = ref false
let log_file = open_out "allinput.v"
let max_flag = ref false
let choice = ref 1
let bag_flag = ref false
let coq_running = ref false
let coq_channels = ref (stdin, stdout)

let default_var_0 = CP.SpecVar (CP.OType "Obj", "hd", Unprimed)
let default_var_1 = CP.SpecVar (CP.Prim Int, "ex", Unprimed)
let default_var_2 = CP.SpecVar (CP.Prim Int, "n", Unprimed)

let double_exists_flag = ref false
let pre = ref ""
let post = ref ""

(* pretty printing for primitive types *)
let coq_of_prim_type = function
  | Bool          -> "int"
  | Float         -> "float"	(* all types will be ints. *)
  | Int           -> "int"
  | Void          -> "unit" 	(* all types will be ints. *)
  | Bag		        -> "int set"
  | List		      -> "list"
;;

(* pretty printing for spec_vars *)
let coq_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (_, v, p) -> v ^ (if CP.is_primed sv then Oclexer.primed_str else "")

let coq_null_string (t : CP.typ) = "0"

let coq_type_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (t, id, _) -> begin match t with
    | CP.Prim List -> "list (prod Z Z)"
    | _ -> "Z"
	end

let coq_sign exp = begin match exp with
	| CP.IConst _ -> true
	| CP.ListMin _ -> false
	| CP.ListHead _ -> false
  | CP.Null (typ, _) -> true (*coq_null_cond typ*)
	| CP.Var (sv, _) -> begin match sv with
	  | CP.SpecVar (t, id, _) -> begin match t with
	    | CP.Prim List -> false
			| CP.OType i -> (*begin match id with
			| "self"
			| "res" -> true
			| _ -> *)false 
				(*end*)
	    | _ -> true
		end
(*		| _ -> true*)
	end
	| _ -> true
end

(*----------------------------------*)
(* checking if exp contains bags *)
let rec is_bag_exp e0 = match e0 with
  | CP.Var (CP.SpecVar(t, _, _), _) ->
	if (CP.is_int_type t) then true
	else false
  | CP.Bag (_, _)
  | CP.BagUnion (_, _)
  | CP.BagIntersect (_, _)
  | CP.BagDiff (_, _, _) -> true
  | _ -> false


(* checking if b formula contains bags *)
and is_bag_b_formula b = match b with
  | CP.Eq (a1, a2, _)
  | CP.Neq (a1, a2, _) -> ((is_bag_exp a1) || (is_bag_exp a2))
  | CP.BagIn (_, _, _)
  | CP.BagNotIn (_, _, _)
  | CP.BagSub (_, _, _)
  | CP.BagMin (_, _, _)
  | CP.BagMax (_, _, _) -> true
  | _ -> false

(*----------------------------------*)

(* pretty printing for expressions *)
and coq_of_exp e0 =
  match e0 with
  | CP.Null (typ, _) -> coq_null_string typ
  | CP.Var (sv, _) -> coq_of_spec_var sv
  | CP.IConst (i, _) -> string_of_int i
  | CP.FConst (f, _) -> failwith ("coq.coq_of_exp: float can never appear here")
  | CP.Add (a1, a2, _) ->  " ( " ^ (coq_of_exp a1) ^ " + " ^ (coq_of_exp a2) ^ ")" 
  | CP.Subtract (a1, a2, _) ->  " ( " ^ (coq_of_exp a1) ^ " - " ^ (coq_of_exp a2) ^ ")"
  | CP.Mult (a1, a2, _) ->  "(" ^ (coq_of_exp a1) ^ " * " ^ (coq_of_exp a2) ^ ")" 
  | CP.Div  (a1, a2, _) -> "(" ^ (coq_of_exp a1) ^ " / " ^ (coq_of_exp a2) ^ ")"
  | CP.Max _ -> failwith ("coq.coq_of_exp: min/max can never appear here")
  | CP.Min (a1, a2, _) -> "(kmin " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ ")"
  (* lists *)
	| CP.Fst (a, pos) -> "(fst " ^ (coq_of_exp a) ^ ")"
  | CP.Snd (a, pos) -> "(snd " ^ (coq_of_exp a) ^ ")"
  | CP.List (alist, pos) -> 
    begin match alist with
    | [] -> "(@nil (prod Z Z))"
	  | a::t -> "(" ^ change_const (coq_of_exp a) ^ " :: " ^ (coq_of_exp (CP.List (t, pos))) ^ ")"
	  end
  | CP.ListAppend (alist, pos) ->
    begin match alist with
    | [] -> "(@nil (prod Z Z))"
	  | a::[] -> coq_of_exp a
	  | a::t -> "(" ^ change_const (coq_of_exp a) ^ " ++ " ^ (coq_of_exp (CP.ListAppend (t, pos))) ^ ")"
	  end
  | CP.ListCons (a1, a2, _) ->  "(" ^ change_const (coq_of_exp a1) ^ " :: " ^ (coq_of_exp a2) ^ ")"
  | CP.ListConsP (a1, a2, a3, _) -> "((" ^ (coq_of_exp a1) ^ ", " ^ (coq_of_exp a2) ^ ") :: " ^ (coq_of_exp a3) ^ ")"
  | CP.ListRemove (a1, a2, a3, _) -> "(StsortZZ.remove (" ^ (coq_of_exp a1) ^ ", " ^ (coq_of_exp a2) ^ ") " ^ (coq_of_exp a3) ^ ")"
	| CP.ListKins (a1, a2, a3, _) -> "(kinsert (" ^ (coq_of_exp a1) ^ ", " ^ (coq_of_exp a2) ^ ") " ^ (coq_of_exp a3) ^ ")"
	| CP.ListPartition (a1, a2, a3, _) -> "(StsortZZ.partition (" ^ (coq_of_exp a1) ^ ", " ^ (coq_of_exp a2) ^ ") " ^ (coq_of_exp a3) ^ ")"
	| CP.ListHead (a, _) ->
		let def_var = coq_of_spec_var (CP.fresh_spec_var default_var_0) in
		pre := !pre ^ "(forall " ^ def_var ^ ": (prod Z Z), ";
		post := !post ^ ")";
	  "(hd " ^ def_var ^ " " ^ (coq_of_exp a) ^ ")"
  | CP.ListLength (a, _) -> "(Z_of_nat (length " ^ (coq_of_exp a) ^ "))"
  | CP.ListMin (a1, a2, _) -> "(kminl2 " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ ")"
  | CP.ListTail (a, _) -> "(tail " ^ (coq_of_exp a) ^ ")"
  | CP.ListReverse (a, _) -> "(rev " ^ (coq_of_exp a) ^ ")"
	| CP.ListQSorted (a, _) -> " (qsort " ^ (coq_of_exp a) ^ ")"
	| CP.ListQSortedH (a1, a2, _) ->
		 let def_var = coq_of_spec_var (CP.fresh_spec_var default_var_2) in
		 "forall " ^ def_var ^ ", (Z_of_nat " ^ def_var ^ " = " ^ (coq_of_exp a2) ^ ") -> (qsorth " ^ (coq_of_exp a1) ^ " " ^ def_var ^ ")"
	| CP.ListSSorted (a, _) -> " (selsort " ^ (coq_of_exp a) ^ ")"
	| CP.ListISorted (a, _) -> " (insertion_sort " ^ (coq_of_exp a) ^ ")"
  (* bags *)
  | CP.Bag (alist, pos) -> 
    begin match alist with
    | [] -> "ZSets.empty"
	  | a::t -> "( ZSets.add " ^ (coq_of_exp a) ^ " " ^ (coq_of_exp (CP.Bag (t, pos))) ^ ")"
	  end
  | CP.BagUnion (alist, pos) ->
    begin match alist with
    | [] -> "ZSets.empty"
	  | a::[] -> coq_of_exp a
	  | a::t -> "( ZSets.union " ^ (coq_of_exp a) ^ " " ^ (coq_of_exp (CP.BagUnion (t, pos))) ^ ")"
	  end
  | CP.BagIntersect (alist, pos) ->
    begin match alist with
    | [] -> "ZSets.empty"
	  | a::[] -> coq_of_exp a
	  | a::t -> "( ZSets.inter " ^ (coq_of_exp a) ^ " " ^ (coq_of_exp (CP.BagIntersect (t, pos))) ^ ")"
	  end
  | CP.BagDiff (a1, a2, _) -> " ( ZSets.diff " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ ")"

(* pretty printing for a list of expressions *)
and coq_of_formula_exp_list l = match l with
  | []         -> ""
  | h::[]      -> coq_of_exp h
  | h::t       -> (coq_of_exp h) ^ ", " ^ (coq_of_formula_exp_list t)

and change_const (exp : string) =
	begin match String.get exp 0 with
    | 'v' | 'k' | 'a'                 (*hard code: the most used patterns for representing integers; to be rewritten*) 
(*    | '0' | '1' | '2'| '3' | '4' | '5' | '6' | '7' | '8' | '9'*) -> "(" ^ exp ^ ", " ^ exp ^ ")"
    | _ -> exp 
	end

and add_extra_quantifiers exp =
  begin match exp with
    | CP.Null (CP.OType id, _) -> true
    | _ -> false
  end

and coq_sign_exp exp1 exp2 str =
  let coq_of_exp1 = coq_of_exp exp1 in
	let coq_of_exp2 = coq_of_exp exp2 in
	if (coq_sign exp1) then
		if (coq_sign exp2) then
			coq_of_exp1 ^ str ^ coq_of_exp2
		else
			(change_const coq_of_exp1) ^ str ^ coq_of_exp2
	else
		if (coq_sign exp2) then
			coq_of_exp1 ^ str ^ (change_const coq_of_exp2)
		else
 			coq_of_exp1(* ^ "&"*) ^ str ^ coq_of_exp2
			 
(* pretty printing for boolean vars *)
and coq_of_b_formula b = 
  match b with
  | CP.BConst (c, _) -> begin match c with
		| true -> "True"
		| false -> "False"
			end
  | CP.BVar (bv, _) -> " (" ^ (coq_of_spec_var bv) ^ " = 1)"
  | CP.Lt (a1, a2, _) -> coq_sign_exp a1 a2 "<"
  | CP.Lte (a1, a2, _) -> coq_sign_exp a1 a2 "<="
  | CP.Gt (a1, a2, _) -> coq_sign_exp a1 a2 ">"
  | CP.Gte (a1, a2, _) -> coq_sign_exp a1 a2 ">="
  | CP.Eq (a1, a2, _) -> (coq_sign_exp a1 a2 "=")
  | CP.Neq (a1, a2, _) -> (coq_sign_exp a1 a2 "<>")
  | CP.EqMax (a1, a2, a3, _) ->
	  let a1str = coq_of_exp a1 in
	  let a2str = coq_of_exp a2 in
	  let a3str = coq_of_exp a3 in
	      " (*the maximum*) ((" ^ a1str ^ (coq_sign_exp a1 a3 "=") ^ a3str ^ " /\\ " ^ a3str ^(coq_sign_exp a3 a2 ">") ^ a2str ^ ") \\/ ("
	      ^ a2str ^ (coq_sign_exp a2 a3 ">=") ^ a3str ^ " /\\ " ^ a1str ^ (coq_sign_exp a1 a2 "=") ^ a2str ^ "))"
  | CP.EqMin (a1, a2, a3, _) ->
	  let a1str = coq_of_exp a1 in
	  let a2str = coq_of_exp a2 in
	  let a3str = coq_of_exp a3 in
          " (*the minimum*) ((" ^ a1str ^ (coq_sign_exp a1 a3 "=") ^ a3str ^ " /\\ " ^ a2str ^ (coq_sign_exp a2 a3 ">=") ^ a3str ^ ") \\/ ("
		  ^ a2str ^ (coq_sign_exp a2 a3 "<=") ^ a3str ^ " /\\ " ^ a1str ^ (coq_sign_exp a1 a2 "=") ^ a2str ^ "))"
  (* lists *)
  | CP.ListIn (a1, a2, _) -> " (In " ^ change_const (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ ")"
  | CP.ListNotIn (a1, a2, _) ->  " (not (In " ^ change_const (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ "))"
  | CP.ListAllN (a1, a2, _) -> " (alln " ^ (coq_of_exp a2) ^ " " ^ (coq_of_exp a1) ^ ")"
	| CP.ListFirstOcc (a1, a2, a3, _) ->
		let first_occ_var = (coq_of_exp a1) ^ "," ^ (coq_of_exp a3) in
		   "(first_occurrence (" ^ first_occ_var ^ ") " ^ (coq_of_exp a2) ^ " (" ^ first_occ_var ^ "))"
  | CP.ListPerm (a1, a2, _) -> " (Permutation " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ ")"
  | CP.ListStable (a1, a2, _) -> " (stable " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ ")"
  (* bags *)
  | CP.BagIn (sv, a, _) -> " (ZSets.mem " ^ (coq_of_spec_var sv) ^ " " ^ (coq_of_exp a) ^ " = true)"
  | CP.BagNotIn (sv, a, _) -> " (ZSets.mem " ^ (coq_of_spec_var sv) ^ " " ^ (coq_of_exp a) ^ " = false)"
  | CP.BagSub (a1, a2, _) -> " (ZSets.subset " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ " = true)"
  | CP.BagMin _
  | CP.BagMax _ -> failwith ("No bags in Coq yet")

(* pretty printing for formulas *)
and coq_of_formula f =
    match f with
    | CP.BForm (b,_) -> "(" ^ (coq_of_b_formula b) ^ ")"
    | CP.Not (p, _,_) ->
	    begin match p with
		| CP.BForm (CP.BVar (bv, _),_) -> (coq_of_spec_var bv) ^ " = 0"
		| _ -> " (~ (" ^ (coq_of_formula p) ^ ")) "
        end
    | CP.Forall (sv, p, _, _) ->
	    " (forall " ^ (coq_of_spec_var sv) ^ "," ^ (coq_of_formula p) ^ ") "
    | CP.Exists (sv, p,  _,_) ->
	    " (exists " ^ (coq_of_spec_var sv) ^ ":" ^ (coq_type_of_spec_var sv) ^"," ^ (coq_of_formula p) ^ ") "
    | CP.And (p1, p2, _) ->
	    "(" ^ (coq_of_formula p1) ^ " /\\ " ^ (coq_of_formula p2) ^ ")"
    | CP.Or (p1, p2, _, _) ->
	    "(" ^ (coq_of_formula p1) ^ " \\/ " ^ (coq_of_formula p2) ^ ")"
			
and is_double_exists f =
  begin match f with
    | CP.Exists (sv, p,  _,_) ->
			begin match p with
				| CP.Exists _ ->
					true
				| _ -> false
			end
		| _ -> false
	end

(* checking the result given by Coq *)
let rec check fd coq_file_name : bool=
  try while true do
    let line = input_line fd in
    if line = "No subgoals!" then raise Exit else ()
  done; false
  with Exit -> 
    if !log_all_flag==true then
      output_string log_file ("[coq.ml]: --> SUCCESS\n");
    (*ignore (Sys.remove coq_file_name);*)
    true
  | _ ->
	  if !log_all_flag==true then
		output_string log_file ("[coq.ml]: --> Error in file " ^ coq_file_name ^ "\n");
	  (*ignore (Sys.remove coq_file_name);	*)
	  false
;;
let coq_of_var_list l = String.concat "" (List.map (fun sv -> "forall " ^ (coq_of_spec_var sv) ^ ": " ^ (coq_type_of_spec_var sv) ^ ", ") l)

(* starting Coq in interactive mode *)
let start_prover () =
  coq_channels := Unix.open_process "coqtop -require stsort -require decidez 2> /dev/null";
  coq_running := true;
  print_string "Coq started\n"; flush stdout

(* stopping Coq *)
let stop_prover () =
  output_string (snd !coq_channels) ("Quit.\n"); flush (snd !coq_channels);
  ignore (Unix.close_process !coq_channels);
  coq_running := false;
  print_string "Coq stopped\n"; flush stdout

(* sending Coq a formula; nr = nr. of retries *)
let rec send_formula (f : string) (nr : int) : bool =
  try
	  output_string (snd !coq_channels) f;
		if (!double_exists_flag)
		  then output_string (snd !coq_channels) ("decidex.\nQed.\n")
			else output_string (snd !coq_channels) ("decidez.\nQed.\n");
	  flush (snd !coq_channels);
	  
	  let result = ref false in
	  let finished = ref false in  
	  while not !finished do 
        let line = input_line (fst !coq_channels) in
        if !log_all_flag==true then output_string log_file ("[coq.ml]: >>"^line^"\n");
        if line = "test" ^ string_of_int !coq_file_number ^ " is defined" then begin
          result := true;
          finished := true;
          if !log_all_flag==true then output_string log_file ("[coq.ml]: --> SUCCESS\n");
        end else if String.length line > 5 && String.sub line 0 5 = "Error" then begin
          result := false;
          finished := true;
          output_string (snd !coq_channels) ("Abort.\n");
          flush (snd !coq_channels);
          if !log_all_flag==true then output_string log_file ("[coq.ml]: --> FAIL\n");
        end;
	  done;
	  !result
  with
	_ -> ignore (Unix.close_process !coq_channels);
		coq_running := false;
		print_string "\nCoq crashed\n"; flush stdout;
		start_prover ();
		if nr > 1 then send_formula f (nr - 1) else false
  
(* writing the Coq file *)
let write (ante : CP.formula) (conseq : CP.formula) : bool =
(*  print_string "*"; flush stdout; *)
(*  print_endline ("formula " ^ string_of_int !coq_file_number ^ ": " ^ (Cprinter.string_of_pure_formula ante) ^ " -> " ^ (Cprinter.string_of_pure_formula conseq)); *)
  let vstr = coq_of_var_list (Util.remove_dups ((CP.fv ante) @ (CP.fv conseq))) in

  let cstr = coq_of_formula conseq in
	let cstr_pre = !pre in
  let cstr_post = !post in
	double_exists_flag := is_double_exists conseq;
	
	pre := "";
	post := "";

	let astr = coq_of_formula ante in
	let astr_pre = !pre in
  let astr_post = !post in
	 
  coq_file_number.contents <- !coq_file_number + 1;
  if !coq_running == false then start_prover ();

  (* if log_all_flag is on -> writing the formula in the coq log file  *)
  if !log_all_flag == true then	begin
    output_string log_file ("Lemma test" ^ string_of_int !coq_file_number ^ " : (" ^ cstr_pre ^ vstr ^ astr_pre ^ astr ^ astr_post ^ " -> " ^ cstr ^ cstr_post ^ ")%Z.\n");
	flush log_file;
  end;

  send_formula ("Lemma test" ^ string_of_int !coq_file_number ^ " : (" ^ cstr_pre ^ vstr ^ astr_pre ^ astr ^ astr_post ^ " -> " ^ cstr ^ cstr_post ^ ")%Z.\n") 2
  
let imply (ante : CP.formula) (conseq : CP.formula) : bool =
  if !log_all_flag == true then
	output_string log_file "\n[coq.ml]: #imply\n";
  max_flag := false;
  choice := 1;
    write ante conseq
    (*write (CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos)*)

let is_sat (f : CP.formula) (sat_no : string) : bool =
  if !log_all_flag == true then
	output_string log_file ("\n[coq.ml]: #is_sat " ^ sat_no ^ "\n");
  let tmp_form = (imply f (CP.BForm(CP.BConst(false, no_pos), None))) in
  match tmp_form with
  | true ->
	  if !log_all_flag == true then output_string log_file "[coq.ml]: is_sat --> false\n";
	  false
  | false ->
	  if !log_all_flag == true then output_string log_file "[coq.ml]: is_sat --> true\n";
	  true

let building_image _ = ()

(* TODO: implement the following procedures; now they are only dummies *)
let hull (pe : CP.formula) : CP.formula = begin
	if !log_all_flag == true then
	  output_string log_file "\n[coq.ml]: #hull\n";
	pe
	end
let pairwisecheck (pe : CP.formula) : CP.formula = begin
	if !log_all_flag == true then
	  output_string log_file "\n[coq.ml]: #pairwisecheck\n";
	pe
	end
let simplify (pe : CP.formula) : CP.formula = begin
	if !log_all_flag == true then
	  output_string log_file "\n[coq.ml]: #simplify\n";
	pe
	end
