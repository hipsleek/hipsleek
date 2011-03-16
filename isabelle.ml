(*
  Create the input file for Isabelle
*)

open Globals
module CP = Cpure

let isabelle_file_number = ref 0
let result_file_name = "res"
let log_all_flag = ref false
let log_file = open_out "allinput.thy"
let max_flag = ref false
let choice = ref 1
let bag_flag = ref false

(* pretty printing for primitive types *)
let isabelle_of_prim_type = function
  | Bool          -> "int"
  | Float         -> "int"	(* Can I really receive float? What do I do then? I don't have float in Isabelle. *)
  | Int           -> "int"
  | Void          -> "void" 	(* same as for float *)
  | Bag		  ->
      if !bag_flag then "int multiset"
      else "int set"
  | List           -> "list"	(* lists are not supported *)
;;

(* pretty printing for spec_vars *)
let isabelle_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (CP.Prim(t), v, p) -> "(" ^ v ^ (if CP.is_primed sv then Oclexer.primed_str else "") ^ "::" ^ isabelle_of_prim_type t ^ ")"
  | CP.SpecVar (CP.OType(id), v, p) -> v ^ (if CP.is_primed sv then Oclexer.primed_str else "")

(* pretty printing for spec_vars without types *)
(*let isabelle_of_spec_var_no_type (sv : CP.spec_var) = match sv with
  | CP.SpecVar (CP.Prim(t), v, p) -> v ^ (if CP.is_primed sv then Oclexer.primed_str else "")
  | CP.SpecVar (CP.OType(id), v, p) -> v ^ (if CP.is_primed sv then Oclexer.primed_str else "")
*)


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

(* checking if formula contains bags *)
and is_bag_formula f = true (*match f with
    | CP.BForm b -> (is_bag_b_formula b)
    | CP.And (p1, p2, _)
    | CP.Or (p1, p2, _) -> (is_bag_formula p1) || (is_bag_formula p2)
    | CP.Forall (_, p, _)
    | CP.Exists (_, p, _)
    | CP.Not (p, _) -> (is_bag_formula p)*)

(*----------------------------------*)

(* pretty printing for expressions *)
let rec isabelle_of_exp e0 = match e0 with
  | CP.Null _ -> "(0::int)"
  | CP.Var (sv, _) -> isabelle_of_spec_var sv
  | CP.IConst (i, _) -> "(" ^ string_of_int i ^ "::int)"
  | CP.FConst _ -> failwith ("[isabelle.ml]: ERROR in constraints (float should not appear here)")
  | CP.Add (a1, a2, _) ->  " ( " ^ (isabelle_of_exp a1) ^ " + " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Subtract (a1, a2, _) ->  " ( " ^ (isabelle_of_exp a1) ^ " - " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Mult (a1, a2, _) -> "(" ^ (isabelle_of_exp a1) ^ " * " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Div (a1, a2, _) -> failwith "[isabelle.ml]: divide is not supported."
  | CP.Max _
  | CP.Min _ -> failwith ("isabelle.isabelle_of_exp: min/max can never appear here")
  | CP.Bag (elist, _) ->
      if !bag_flag then "{#"^ (isabelle_of_formula_exp_list elist) ^ "}"
      else "{"^ (isabelle_of_formula_exp_list elist) ^ "}"
  | CP.BagUnion ([], _) -> ""
  | CP.BagUnion (e::[], _) -> (isabelle_of_exp e)
  | CP.BagUnion (e::rest, l) ->
      if !bag_flag then (isabelle_of_exp e) ^ "+" ^ (isabelle_of_exp (CP.BagUnion (rest, l)))
      else (isabelle_of_exp e) ^ "\\<union>" ^ (isabelle_of_exp (CP.BagUnion (rest, l)))
  | CP.BagIntersect ([], _) -> ""
  | CP.BagIntersect (e::[], _) -> (isabelle_of_exp e)
  | CP.BagIntersect (e::rest, l) ->(isabelle_of_exp e) ^ "\\<intersect>" ^ (isabelle_of_exp (CP.BagIntersect (rest, l)))
  | CP.BagDiff (e1, e2, _) -> (isabelle_of_exp e1) ^ "-" ^ (isabelle_of_exp e2)
  | CP.List _
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListAppend _
  | CP.ListReverse _ -> failwith ("Lists are not supported in Isabelle")
  
(* pretty printing for a list of expressions *)
and isabelle_of_formula_exp_list l = match l with
  | []         -> ""
  | h::[]      ->
      if !bag_flag then isabelle_of_exp h ^ "#"
      else isabelle_of_exp h
  | h::t       -> (isabelle_of_exp h) ^ ", " ^ (isabelle_of_formula_exp_list t)


(* pretty printing for boolean vars *)
and isabelle_of_b_formula b = match b with
  | CP.BConst (c, _) -> if c then "((0::int) = 0)" else "((0::int) > 0)"
  | CP.BVar (bv, _) -> "(" ^ (isabelle_of_spec_var bv) ^ " > 0)"
  | CP.Lt (a1, a2, _) -> " ( " ^ (isabelle_of_exp a1) ^ " < " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Lte (a1, a2, _) -> " ( " ^ (isabelle_of_exp a1) ^ " <= " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Gt (a1, a2, _) -> " ( " ^ (isabelle_of_exp a1) ^ " > " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Gte (a1, a2, _) -> "(" ^ (isabelle_of_exp a1) ^ " >= " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Eq (a1, a2, _) -> " ( " ^ (isabelle_of_exp a1) ^ " = " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Neq (a1, a2, _) -> "( " ^ (isabelle_of_exp a1) ^ " ~= " ^ (isabelle_of_exp a2) ^ ")"
 (* optimization below is not working for isabelle due to incompletness *)
  (*| CP.Eq (a1, a2, _) -> begin
        if CP.is_null a2 then	(isabelle_of_exp a1)^ " < 1"
        else if CP.is_null a1 then (isabelle_of_exp a2) ^ " < 1"
        else (isabelle_of_exp a1) ^ " = " ^ (isabelle_of_exp a2)
  end
  | CP.Neq (a1, a2, _) -> begin
        if CP.is_null a2 then
        	(isabelle_of_exp a1) ^ " > 0"
        else if CP.is_null a1 then						
        	(isabelle_of_exp a2) ^ " > 0"
        else (isabelle_of_exp a1)^ " ~= " ^ (isabelle_of_exp a2)
  end*)
  | CP.EqMax (a1, a2, a3, _) ->
	  let a1str = isabelle_of_exp a1 in
	  let a2str = isabelle_of_exp a2 in
	  let a3str = isabelle_of_exp a3 in
	  (*"((max " ^ a2str ^ " " ^ a3str ^ ") = " ^ a1str ^ ")\n" *)
	  (*"(" ^ a1str ^ " = " ^ a2str ^ ") | (" ^ a1str ^ " = " ^ a3str ^ ")" *)
	  (*"((" ^ a1str ^ " = " ^ a2str ^ ") | (" ^ a1str ^ " = " ^ a3str ^ ")) & ("
          ^ a1str ^ " >= " ^ a2str ^ ") & (" ^ a1str ^ " >= " ^ a3str ^ ")"*)
	  (*"((" ^ a1str ^ " = " ^ a3str ^ " & " ^ a1str ^ " >= " ^ a2str ^ ") | ("
	  ^ a1str ^ " = " ^ a2str ^ "))" ^ Gen.new_line_str*)
          (*"((" ^ a1str ^ " = " ^ a2str  ^ ") | ("
	  ^ a1str ^ " = " ^ a3str ^ " & " ^ a2str ^ " < " ^ a3str ^ "))" ^ Gen.new_line_str*)
	  (*if !max_flag = false then
	    max_flag := true;
	  if !choice = 1 then
	    begin*)
	      (*print_string ("found max in test" ^ (string_of_int !isabelle_file_number) ^ " \n");*)
	      "((" ^ a1str ^ " = " ^ a3str ^ " & " ^ a3str ^ " > " ^ a2str ^ ") | ("
	      ^ a2str ^ " >= " ^ a3str ^ " & " ^ a1str ^ " = " ^ a2str ^ "))" ^ Gen.new_line_str;

	      (*"((" ^ a2str ^ " < " ^ a3str ^ " | " ^ a1str ^ " = " ^ a2str  ^ ") & ("
	      ^ a2str ^ " >= " ^ a3str ^ " | " ^ a1str ^ " = " ^ a3str ^ "))" ^ Gen.new_line_str*)
	    (*end
	  else
	    begin
	      (*max_flag := false;*)
	      "((" ^ a1str ^ " = " ^ a3str ^ " & " ^ a3str ^ " >= " ^ a2str ^ ") | ("
	      ^ a1str ^ " = " ^ a2str ^ "))" ^ Gen.new_line_str;
	    end*)
  | CP.EqMin (a1, a2, a3, _) ->
	  let a1str = isabelle_of_exp a1 in
	  let a2str = isabelle_of_exp a2 in
	  let a3str = isabelle_of_exp a3 in
	  (*"((min " ^ a2str ^ " " ^ a3str ^ ") = " ^ a1str ^ ")\n" *)
	  (*"(" ^ a1str ^ " = " ^ a2str ^ ") | (" ^ a1str ^ " = " ^ a3str ^ ")" *)
          "((" ^ a1str ^ " = " ^ a3str ^ " & " ^ a2str ^ " >= " ^ a3str ^ ") | ("
	   ^ a2str ^ " <= " ^ a3str ^ " & " ^ a1str ^ " = " ^ a2str ^ "))" ^ Gen.new_line_str
          (*---"((" ^ a2str ^ " > " ^ a3str ^ " | " ^ a1str ^ " = " ^ a2str  ^ ") & ("
	   ^ a2str ^ " <= " ^ a3str ^ " | " ^ a1str ^ " = " ^ a3str ^ "))" ^ Gen.new_line_str*)
	  (* "((" ^ a3str ^ " <= " ^ a2str ^ " & " ^ a1str ^ " = " ^ a3str ^ ") | ("
		(*^ a2str ^ " < " ^ a3str ^ " & "*) ^ a1str ^ " = " ^ a2str ^ "))" ^ Gen.new_line_str*)
  | CP.BagIn (v, e, l)	->
      if !bag_flag then
	"(" ^  (isabelle_of_spec_var v) ^ ":#" ^ (isabelle_of_exp e) ^ ")"
	(*"(count " ^ (isabelle_of_exp e) ^ " " ^ (isabelle_of_spec_var v) ^ ") > 0"*)
	(*(isabelle_of_spec_var v) ^ " \\<in> set_of(" ^ (isabelle_of_exp e) ^")"*)
      else (isabelle_of_spec_var v) ^ " \\<in> " ^ (isabelle_of_exp e)
  | CP.BagNotIn (v, e, l) ->
      if !bag_flag then
	"~(" ^  (isabelle_of_spec_var v) ^ ":#" ^ (isabelle_of_exp e) ^ ")"
	(*"(count " ^ (isabelle_of_exp e) ^ " " ^ (isabelle_of_spec_var v) ^ ") = 0"*)
	(*"~(" ^ (isabelle_of_spec_var v) ^ " \\<in> set_of(" ^ (isabelle_of_exp e) ^"))"*)
      else "~(" ^ (isabelle_of_spec_var v) ^ " \\<in> " ^ (isabelle_of_exp e) ^")"
  | CP.BagSub (e1, e2, l) ->
      if !bag_flag then "(ALL x0. count (" ^ isabelle_of_exp e1 ^ ") x0 <= count (" ^ isabelle_of_exp e2 ^ ") x0)"
      else "(" ^ isabelle_of_exp e1 ^ " \\<subset>" ^ isabelle_of_exp e2 ^ ")"
	     (*"(ALL x0.(( x0 in " ^ isabelle_of_exp e1 ^ ") --> ( x0 in " ^ isabelle_of_exp e2 ^ "))"*)
  | CP.BagMin (v1, v2, l) ->
      if !bag_flag then
	(isabelle_of_spec_var v1) ^ " \\<in> set_of(" ^ (isabelle_of_spec_var v2) ^") & (ALL x0. x0:#" ^ (isabelle_of_spec_var v2) ^ " --> " ^ (isabelle_of_spec_var v1) ^ " <= x0)"
      else
	(isabelle_of_spec_var v1) ^ " \\<in> " ^ (isabelle_of_spec_var v2) ^" & (ALL x0. x0 \\<in>" ^ (isabelle_of_spec_var v2) ^ " --> " ^ (isabelle_of_spec_var v1) ^ " <= x0)"
  | CP.BagMax (v1, v2, l) ->
      if !bag_flag then
	(isabelle_of_spec_var v1) ^ " \\<in> set_of(" ^ (isabelle_of_spec_var v2) ^") & (ALL x0. x0:#" ^ (isabelle_of_spec_var v2) ^ " --> x0 <= " ^ (isabelle_of_spec_var v2) ^ ")"
      else
	(isabelle_of_spec_var v1) ^ " \\<in> " ^ (isabelle_of_spec_var v2) ^" & (ALL x0. x0 \\<in>" ^ (isabelle_of_spec_var v2) ^ " --> x0 <= " ^ (isabelle_of_spec_var v1) ^ " )"
  | CP.ListIn _
  | CP.ListNotIn _
  | CP.ListAllN _
  | CP.ListPerm _ -> failwith ("Lists are not supported in Isabelle")
  
(* pretty printing for formulas *)
and isabelle_of_formula f =
    match f with
    | CP.BForm (b,_) ->
	  if (is_bag_formula f) then
	    "(" ^ (isabelle_of_b_formula b) ^ ")"
	  else ""
    | CP.Not (p, _,_) -> " (~ (" ^ (isabelle_of_formula p) ^ ")) "
(*	begin
	  if (is_bag_formula f) then
	    match p with
		| CP.BForm (CP.BVar (bv, _)) -> (isabelle_of_spec_var bv) ^ " = 0"
		| _ -> 
          else ""
	end*)
    | CP.Forall (sv, p, _,_) ->
	  if (is_bag_formula f) then
	    " (ALL " ^ (isabelle_of_spec_var sv) ^ "." ^ (isabelle_of_formula p) ^ ") "
          else ""
    | CP.Exists (sv, p,_, _) ->
	  if (is_bag_formula f) then
	    " (EX " ^ (isabelle_of_spec_var sv) ^ "." ^ (isabelle_of_formula p) ^ ") "
          else ""
    | CP.And (p1, p2, _) ->
	  if (is_bag_formula p1) & (is_bag_formula p2) then
	    "(" ^ (isabelle_of_formula p1) ^ " & " ^ (isabelle_of_formula p2) ^ ")"
          else
	      if (is_bag_formula p1) then
		"(" ^ (isabelle_of_formula p1) ^ ")"
              else
		if (is_bag_formula p2) then
		  "(" ^ (isabelle_of_formula p2) ^ ")"
                else ""
    | CP.Or (p1, p2,_, _) ->
	if (is_bag_formula p1) & (is_bag_formula p2) then
	    "(" ^ (isabelle_of_formula p1) ^ " | " ^ (isabelle_of_formula p2) ^ ")"
          else
	      if (is_bag_formula p1) then
		"(" ^ (isabelle_of_formula p1) ^ ")"
              else
		if (is_bag_formula p2) then
		  "(" ^ (isabelle_of_formula p2) ^ ")"
                else ""


(* checking the result given by Isabelle *)
let rec check fd isabelle_file_name : bool=
  let stk = new Gen.stack "" (fun x -> x^"\n") in
  try while true do
    let line = input_line fd in
    stk#push line;
    if line = "No subgoals!" then raise Exit else ()
  done; false
  with Exit -> 
    if !log_all_flag==true then
      output_string log_file (" [isabelle.ml]: --> SUCCESS\n");
    (*ignore (Sys.remove isabelle_file_name);*)
    true
  | _ ->
	  if !log_all_flag==true then
		(output_string log_file (" [isabelle.ml]: --> Error in file " ^ isabelle_file_name ^ "\n");
        stk#reverse ; print_string (stk#string_of));
	  (*ignore (Sys.remove isabelle_file_name);	*)
	  false
;;

	(*
	try begin
		let line = input_line fd
		in
			begin
			match line with
			| "*** Failed to finish proof (after successful terminal method)" ->
				begin
				if !log_all_flag==true then
					output_string log_file (" [isabelle.ml]: --> Unable to prove theory " ^ isabelle_file_name ^ "\n");
				ignore (Sys.remove isabelle_file_name);
				false;
				end
			| "*** Type error in application: Incompatible operand type" ->
				begin
				if !log_all_flag==true then
					output_string log_file (" [isabelle.ml]: --> Type error in theory " ^ isabelle_file_name ^ "\n");
				print_string (" [isabelle.ml]: --> Type error in theory " ^ isabelle_file_name ^ "\n");
				ignore (Sys.remove isabelle_file_name);
				false;
				end
			| "Exception- ERROR raised" ->
				begin
				print_string ("\n [isabelle.ml]: --> Syntax error in file " ^ isabelle_file_name ^ "\n");
				if !log_all_flag==true then
					output_string log_file (" [isabelle.ml]: --> Syntax error in file " ^ isabelle_file_name ^ "\n");
				ignore (Sys.remove isabelle_file_name);
				false;
				end
			| "lemma" ->
				begin
      		if !log_all_flag==true then
      			output_string log_file (" [isabelle.ml]: --> SUCCESS\n");
      		ignore (Sys.remove isabelle_file_name);
      		true;
      	end
			| _ -> check fd isabelle_file_name
			end
		end
	with
      End_of_file ->
      	begin
      		if !log_all_flag==true then
      			output_string log_file (" [isabelle.ml]: --> SUCCESS\n");
      		ignore (Sys.remove isabelle_file_name);
      		true;
      	end
	*)

let get_vars_formula p = List.map isabelle_of_spec_var (CP.fv p)

let isabelle_of_var_list l = String.concat "" (List.map (fun s -> "ALL " ^ s ^ ". ") l)

let isabelle_command isabelle_file_name = ("isabelle-process -I -r MyImage < " ^ isabelle_file_name ^ " > res 2> /dev/null")

let set_timer tsecs =
  ignore (Unix.setitimer Unix.ITIMER_REAL
            { Unix.it_interval = 0.0; Unix.it_value = tsecs })

let continue f arg tsecs : bool =
  let oldsig = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Exit)) in
  try
    set_timer tsecs;
    ignore (f arg);
    set_timer 0.0;
    Sys.set_signal Sys.sigalrm oldsig; true
  with Exit ->
    Sys.set_signal Sys.sigalrm oldsig; false
	
(* writing the Isabelle's theory file *)
let write (pe : CP.formula) (timeout : float) : bool =
  begin
  		isabelle_file_number.contents <- !isabelle_file_number + 1;
  		let isabelle_file_name = "test" ^ string_of_int !isabelle_file_number ^ ".thy" in
  		let isabelle_file = open_out isabelle_file_name in
        let vstr = isabelle_of_var_list (Gen.BList.remove_dups_eq (=) (get_vars_formula pe)) in
		let fstr = vstr ^ isabelle_of_formula pe in
    		begin
    		(* creating the theory file *)

		if !bag_flag then
		  begin
		    output_string isabelle_file ("theory " ^ "test" ^ string_of_int !isabelle_file_number ^ " imports Multiset Main begin" ^ Gen.new_line_str);
    		    output_string isabelle_file ("declare union_ac [simp]\n");
		  end
		else
		  output_string isabelle_file ("theory " ^ "test" ^ string_of_int !isabelle_file_number ^ " imports Main begin" ^ Gen.new_line_str);
    		output_string isabelle_file ("lemma \"" ^ fstr ^ "\"\n" ^ " apply(auto)\n done\n end\n\n" );
		flush isabelle_file;
		close_out isabelle_file;

		(* if log_all_flag is on -> writing the formula in the isabelle log file  *)
		if !log_all_flag == true then
		begin
		   if !bag_flag then
		   begin
		     output_string log_file ("theory " ^ "test" ^ string_of_int !isabelle_file_number ^ " imports Multiset Main begin" ^ Gen.new_line_str);
		     output_string log_file ("declare union_ac [simp]\n");
		   end
		   else
		     output_string log_file ("theory " ^ "test" ^ string_of_int !isabelle_file_number ^ " imports Main begin" ^ Gen.new_line_str);
    		   output_string log_file ("lemma \"" ^ fstr ^ "\"\n" ^ " apply(auto)\n done\n end\n" );
		   flush log_file;
		end;


		(* running Isabelle for the newly created theory file *)
		(* creating the ROOT.ML file *)
		let root_file = open_out "ROOT.ML" in
		begin
		   (*output_string root_file ("use_thy \"multiset\"; \n");*)
		   output_string root_file ("use_thy " ^ "\"test" ^ string_of_int !isabelle_file_number ^ "\"\n");
		   flush root_file;
		   close_out root_file;
	        end;
		(*ignore(Sys.command "isabelle -u -q > res");*)
		(* We suppose there exists a so-called heap image called MyImage. This heap image contains the preloaded Multiset
 		and Main theories. When invoking Isabelle, everything that is already loaded is instantly available.*)
		(*ignore(Sys.command ("isabelle -I -r MyImage < " ^ isabelle_file_name ^ " > res 2> /dev/null"));*)

		if (continue Sys.command (isabelle_command isabelle_file_name) timeout) then  
			(* verifying the result returned by Isabelle *)
			let result_file = open_in (result_file_name) in
				check result_file isabelle_file_name
		else 
			let _ = print_string("Timeout while sat checking\n") in
				true	
		end
  end

let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  if !log_all_flag == true then
	output_string log_file ("\n\n[isabelle.ml]: imply#" ^ imp_no ^ "\n");
  max_flag := false;
  choice := 1;
  let tmp_form = CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos in
  let res =  write tmp_form 0. in
	res


let imply_sat (ante : CP.formula) (conseq : CP.formula) (timeout : float) (sat_no :  string) : bool =
  if !log_all_flag == true then
	output_string log_file ("\n\n[isabelle.ml]: imply#from sat#" ^ sat_no ^ "\n");
  max_flag := false;
  choice := 1;
  let tmp_form = CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos in
    (write tmp_form timeout)

let is_sat (f : CP.formula) (sat_no : string) : bool = begin
	if !log_all_flag == true then
				output_string log_file ("\n\n[isabelle.ml]: #is_sat " ^ sat_no ^ "\n");
	let tmp_form = (imply_sat f (CP.BForm(CP.BConst(false, no_pos), None)) !Globals.sat_timeout sat_no) in
		match tmp_form with
			| true ->
				begin
				if !log_all_flag == true then
					output_string log_file "[isabelle.ml]: is_sat --> false\n";
				false;
				end
			| false ->
				begin
				if !log_all_flag == true then
					output_string log_file "[isabelle.ml]: is_sat --> true\n";
				true;
				end
	end

(* building the multiset theory image -  so that it won't be loaded for each theory that needs to be proved *)
(* there is an option when running the system --build-image which creates the heap image *)
let building_image flag = begin
	if flag = "true" (*& !bag_flag*) then begin
	  let multiset_file = open_out "multiset.thy" in
	  begin
		output_string multiset_file ("theory multiset imports Multiset Main begin\n end");
		flush multiset_file;
		close_out multiset_file;
	  end;
	  let root_file = open_out "ROOT.ML" in
	  begin
		output_string root_file ("use_thy \"multiset\"\n");
		(*output_string root_file ("use_thy \"Main\"\n");*)
		flush root_file;
		close_out root_file;
	  end;
		ignore(Sys.command "isabelle usedir -b HOL MyImage");
	end
end

(* TODO: implement the following procedures; now they are only dummies *)
let hull (pe : CP.formula) : CP.formula = begin
	(*if !log_all_flag == true then
	  output_string log_file "\n\n[isabelle.ml]: #hull\n";*)
	pe
	end
let pairwisecheck (pe : CP.formula) : CP.formula = begin
	(*if !log_all_flag == true then
	  output_string log_file "\n\n[isabelle.ml]: #pairwisecheck\n";*)
	pe
	end
let simplify (pe : CP.formula) : CP.formula = begin
	(*if !log_all_flag == true then
	  output_string log_file "\n\n[isabelle.ml]: #simplify\n";*)
	pe
	end
