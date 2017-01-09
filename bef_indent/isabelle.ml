#include "xdebug.cppo"
(*
  Create the input file for Isabelle.

  !!! When running Isabelle for the first time, use --build-image option under hip/sleek

*)

open Globals
open VarGen
open GlobProver
open Gen.Basic
module CP = Cpure

let isabelle_file_number = ref 0
let result_file_name = "res"
let log_all_flag = ref false
let log_all = open_log_out "allinput.thy"
(* let image_path_lst = ["MyImage"; "/usr/local/bin/MyImage"] *)
let image_path_lst = ["/usr/local/bin/MyImage"]
let isabelle_image = ref "MyImage"
let max_flag = ref false
let choice = ref 1
let bag_flag = ref false

let process= ref {name="isabelle"; inchannel = stdin; outchannel = stdout; errchannel = stdin; pid = 0 }
let last_test_number = ref 0
let test_number = ref 0


(* pretty printing for primitive types *)
let rec isabelle_of_typ = function
  | Bool          -> "int"
  | Tree_sh 	  -> "int"
  | Float         -> "int"	(* Can I really receive float? What do I do then? I don't have float in Isabelle.*)
  | Int           -> "int"
  | Void          -> "void" 	(* same as for float *)
  | BagT	t	  ->
      if !bag_flag then "("^(isabelle_of_typ t) ^") multiset"
      else "("^(isabelle_of_typ t) ^") set"
  | UNK           -> 	
        Error.report_error {Error.error_loc = no_pos; 
        Error.error_text = "unexpected UNKNOWN type"}
  | List _    | FORM | Tup2 _     -> 	(* lists are not supported *)
        Error.report_error {Error.error_loc = no_pos; 
        Error.error_text = "list/FORM/Tup2 not supported for Isabelle"}
  | NUM
  | RelT _
  | FuncT _
  | UtT
  | HpT
  | AnnT->
        Error.report_error {Error.error_loc = no_pos; 
        Error.error_text = "NUM, RelT, HpT and AnnT not supported for Isabelle"}
  | TVar _ 
  (* | SLTyp *)
  | Named _ 
  | Array _ ->
        Error.report_error {Error.error_loc = no_pos; 
        Error.error_text = "type var, array and named type not supported for Isabelle"}
  | INFInt | Pointer _ -> Error.report_no_pattern ()  
  | Bptyp ->
        Error.report_error {Error.error_loc = no_pos; 
        Error.error_text = "Bptyp type not supported for Isabelle"}
;;

(* pretty printing for spec_vars *)
let isabelle_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (Named(id), v, p) -> v ^ (if CP.is_primed sv then Oclexer.primed_str else "")
  | CP.SpecVar (Array(id), v, p) -> v ^ (if CP.is_primed sv then Oclexer.primed_str else "") (* An Hoa *)
  | CP.SpecVar (t, v, p) -> "(" ^ v ^ (if CP.is_primed sv then Oclexer.primed_str else "") ^ "::" ^ isabelle_of_typ t ^ ")"

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
  | CP.Tsconst _ -> failwith ("[isabelle.ml]: ERROR in constraints (tsconst should not appear here)")
  | CP.Bptriple _ -> failwith ("[isabelle.ml]: ERROR in constraints (Bptriple should not appear here)")
  | CP.Tup2 _ -> failwith ("[isabelle.ml]: ERROR in constraints (Tup2 should not appear here)")
  | CP.NegInfConst _
  | CP.InfConst _ -> failwith ("[isabelle.ml]: ERROR in constraints (infconst should not appear here)")
  | CP.Add (a1, a2, _) ->  " ( " ^ (isabelle_of_exp a1) ^ " + " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Subtract (a1, a2, _) ->  " ( " ^ (isabelle_of_exp a1) ^ " - " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Mult (a1, a2, _) -> "(" ^ (isabelle_of_exp a1) ^ " * " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Div (a1, a2, _) -> failwith "[isabelle.ml]: divide is not supported."
  | CP.Max _
  | CP.Min _ -> failwith ("isabelle.isabelle_of_exp: min/max can never appear here")
  | CP.TypeCast _ -> failwith ("isabelle.isabelle_of_exp: TypeCast can never appear here")
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
  | CP.Func _ -> failwith ("Func are not supported in Isabelle")
  | CP.AConst _ -> failwith ("AConst are not supported in Isabelle")
	| CP.ArrayAt _ ->  failwith ("Arrays are not supported in Isabelle") (* An Hoa *)
	| CP.Level _ ->  failwith ("level should not appear in Isabelle")
  | CP.Template t -> isabelle_of_exp (CP.exp_of_template t)

  
(* pretty printing for a list of expressions *)
and isabelle_of_formula_exp_list l = match l with
  | []         -> ""
  | h::[]      ->
      if !bag_flag then isabelle_of_exp h ^ "#"
      else isabelle_of_exp h
  | h::t       -> (isabelle_of_exp h) ^ ", " ^ (isabelle_of_formula_exp_list t)


(* pretty printing for boolean vars *)
and isabelle_of_b_formula b =
  let (pf,_) = b in
  match pf with
    | CP.Frm (bv, _) -> "(" ^ (isabelle_of_spec_var bv) ^ " > 0)"
  | CP.BConst (c, _) -> if c then "((0::int) = 0)" else "((0::int) > 0)"
  | CP.XPure _ -> "((0::int) = 0)" (* WN : weakening *)
  | CP.BVar (bv, _) -> "(" ^ (isabelle_of_spec_var bv) ^ " > 0)"
  | CP.Lt (a1, a2, _) -> " ( " ^ (isabelle_of_exp a1) ^ " < " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Lte (a1, a2, _) -> " ( " ^ (isabelle_of_exp a1) ^ " <= " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Gt (a1, a2, _) -> " ( " ^ (isabelle_of_exp a1) ^ " > " ^ (isabelle_of_exp a2) ^ ")"
  | CP.Gte (a1, a2, _) -> "(" ^ (isabelle_of_exp a1) ^ " >= " ^ (isabelle_of_exp a2) ^ ")"
  (* | CP.Eq (a1, a2, _) -> " ( " ^ (isabelle_of_exp a1) ^ " = " ^ (isabelle_of_exp a2) ^ ")" *)
  (* | CP.Neq (a1, a2, _) -> "( " ^ (isabelle_of_exp a1) ^ " ~= " ^ (isabelle_of_exp a2) ^ ")" *)
  | CP.Eq (a1, a2, _) -> begin
        if CP.is_null a2 then	(isabelle_of_exp a1)^ " < (1::int)"
        else if CP.is_null a1 then (isabelle_of_exp a2) ^ " < (1::int)"
        else (isabelle_of_exp a1) ^ " = " ^ (isabelle_of_exp a2)
  end
  | CP.Neq (a1, a2, _) -> begin
        if CP.is_null a2 then
        	(isabelle_of_exp a1) ^ " > (0::int)"
        else if CP.is_null a1 then
        	(isabelle_of_exp a2) ^ " > (0::int)"
        else (isabelle_of_exp a1)^ " ~= " ^ (isabelle_of_exp a2)
  end
  | CP.EqMax (a1, a2, a3, _) ->
	  let a1str = isabelle_of_exp a1 in
	  let a2str = isabelle_of_exp a2 in
	  let a3str = isabelle_of_exp a3 in
      "((" ^ a1str ^ " = " ^ a3str ^ " & " ^ a3str ^ " > " ^ a2str ^ ") | (" ^ a2str ^ " >= " ^ a3str ^ " & " ^ a1str ^ " = " ^ a2str ^ "))" 
  | CP.EqMin (a1, a2, a3, _) ->
	  let a1str = isabelle_of_exp a1 in
	  let a2str = isabelle_of_exp a2 in
	  let a3str = isabelle_of_exp a3 in
	  "((" ^ a1str ^ " = " ^ a3str ^ " & " ^ a2str ^ " >= " ^ a3str ^ ") | (" ^ a2str ^ " <= " ^ a3str ^ " & " ^ a1str ^ " = " ^ a2str ^ "))"
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
  | CP.SubAnn _ -> failwith ("SubAnn are not supported in Isabelle")
  (* | CP.VarPerm _ -> failwith ("VarPerm not suported by Isabelle") *)
  | CP.LexVar _ -> failwith ("Lexvar are not supported in Isabelle")
	| CP.RelForm _ -> failwith ("Relations are not supported in Isabelle") (* An Hoa *)
  
(* pretty printing for formulas *)
and isabelle_of_formula f =
    match f with
    | CP.BForm (b,_) ->
	  if (is_bag_formula f) then
	    "(" ^ (isabelle_of_b_formula b) ^ ")"
	  else ""
    | CP.Not (p, _,_) -> " (~ (" ^ (isabelle_of_formula p) ^ ")) "
    | CP.Forall (sv, p, _,_) ->
	  if (is_bag_formula f) then
	    " (ALL " ^ (isabelle_of_spec_var sv) ^ "." ^ (isabelle_of_formula p) ^ ") "
          else ""
    | CP.Exists (sv, p,_, _) ->
	  if (is_bag_formula f) then
	    " (EX " ^ (isabelle_of_spec_var sv) ^ "." ^ (isabelle_of_formula p) ^ ") "
          else ""
	| CP.AndList _ -> Gen.report_error no_pos "isabelle.ml: encountered AndList, should have been already handled"
    | CP.And (p1, p2, _) ->
	  if (is_bag_formula p1) && (is_bag_formula p2) then
	    "(" ^ (isabelle_of_formula p1) ^ " & " ^ (isabelle_of_formula p2) ^ ")"
          else
	      if (is_bag_formula p1) then
		"(" ^ (isabelle_of_formula p1) ^ ")"
              else
		if (is_bag_formula p2) then
		  "(" ^ (isabelle_of_formula p2) ^ ")"
                else ""
    | CP.Or (p1, p2,_, _) ->
	if (is_bag_formula p1) && (is_bag_formula p2) then
	    "(" ^ (isabelle_of_formula p1) ^ " | " ^ (isabelle_of_formula p2) ^ ")"
          else
	      if (is_bag_formula p1) then
		"(" ^ (isabelle_of_formula p1) ^ ")"
              else
		if (is_bag_formula p2) then
		  "(" ^ (isabelle_of_formula p2) ^ ")"
                else ""


let get_vars_formula p = List.map isabelle_of_spec_var (CP.fv p)

let isabelle_of_var_list l = String.concat "" (List.map (fun s -> "ALL " ^ s ^ ". ") l)

let isabelle_command isabelle_file_name = ("isabelle-process -I -r /usr/local/bin/MyImage < " ^ isabelle_file_name ^ " > res 2> /dev/null")

(*creates a new "isabelle-process " process*)
let rec get_answer chn : string =
    let chr = input_char chn in
    match chr with
      |'\n' -> "\n"
      | '#' ->  "#"
      | _ -> (Char.escaped chr) ^get_answer chn

let rec read_until substr chn : string =
  let str = get_answer chn in
  try
      if (Str.search_forward (Str.regexp substr) str 0 >= 0) then str 
      else str ^ read_until substr chn
  with
    | Not_found ->  str^read_until substr chn
    | e -> ignore e; print_string "[isabelle.ml] -> Exception while reading initial prompt"; str

let read_prompt () = 
  let chn = !process.inchannel in 
  let (todo_unk:char) = input_char chn in (*reads '>'*)
  let (todo_unk:char) = input_char chn in (*reades space*)
  ()

let prelude ()  =
  let ichn = !process.inchannel in 
  let ochn = !process.outchannel in 
  let (todo_unk:string) = read_until "Welcome to Isabelle" ichn in (*welcome text*)
  let () = read_prompt () in
  if !bag_flag then
    ( output_string ochn "theory isabelle_proofs imports Multiset Main\n"; flush ochn;
      let (todo_unk:string) = get_answer ichn in (*reads "theory#"*)
      let (todo_unk:char) = input_char ichn in (*reads space*)
      output_string ochn "begin\n"; flush ochn;
      let (todo_unk:string) = get_answer ichn in (*reads "theory isabelle_proofs"*) 
      let () = read_prompt() in 
      output_string ochn ("declare union_ac [simp]\n");
      let (todo_unk:string) = read_until "declare#" ichn in (*declare#*)
      if!log_all_flag==true then
        output_string log_all ("theory isabelle_proofs imports Multiset Main\nbegin\ndeclare union_ac [simp]\n")
    )
  else
    (output_string ochn "theory isabelle_proofs imports Main\n"; flush ochn;
     let (todo_unk:string) = get_answer ichn in (*reads "theory#"*)
     let (todo_unk:char) = input_char ichn in (*reads space*)
     output_string ochn "begin\n"; flush ochn;
     let (todo_unk:string) = get_answer ichn in (*reads "theory isabelle_proofs"*) 
     let () = read_prompt() in 
     if!log_all_flag==true then
       output_string log_all ("theory isabelle_proofs imports Main\nbegin\n")
    )

let set_process proc =
  process := proc

let rec check_image_existence image_lst =
  match image_lst with
    | [] -> let () = print_string ("\n WARNING: Isabelle's Image was not found. Aborting execution ...\n") in 
            exit(0)
    | img::imgs ->   
        if Sys.file_exists img then 
          isabelle_image := img
        else 
          let () = print_string ("\n WARNING: " ^ img ^ " was not found. Searching for the image in the next path...\n") in 
          check_image_existence imgs

(* We suppose there exists a so-called heap image called MyImage. This heap image contains the preloaded Multiset
   and Main theories. When invoking Isabelle, everything that is already loaded is instantly available.*)
let start () =
  let () = check_image_existence image_path_lst in
  let () = Procutils.PrvComms.start !log_all_flag log_all ("isabelle", "isabelle-process", [|"isabelle-process"; "-I"; "-r"; !isabelle_image;"2> /dev/null"|]) set_process prelude in
  last_test_number := !test_number

let ending_remarks () = 
  output_string !process.outchannel "end\n"; 
  flush !process.outchannel

let stop () = 
  let num_tasks = !test_number - !last_test_number in
  let _  = Procutils.PrvComms.stop !log_all_flag log_all !process num_tasks 3 ending_remarks in
  print_string_if !Globals.enable_count_stats ("Stop Isabelle after ... "^(string_of_int num_tasks)^" invocations\n")


(* restart isabelle system *)
let restart reason =
  print_string ("Restarting Isabelle because of: "^reason^"\n");
  Procutils.PrvComms.restart !log_all_flag log_all "isabelle" reason start stop

(* checking the result given by Isabelle *)
let rec check str : bool=
  try
      let (todo_unk:int) = Str.search_forward (Str.regexp "No subgoals") str 0 in
      if!log_all_flag==true then
        output_string log_all (" [isabelle.ml]: --> SUCCESS\n");
      true
  with
    | Not_found -> 
        (if !log_all_flag==true then
		      output_string log_all (" [isabelle.ml]: --> fail \n"));
        false

let write (pe : CP.formula) (timeout : float) (is_sat_b: bool) : bool =
  begin
      incr test_number;
      let vstr = isabelle_of_var_list (Gen.BList.remove_dups_eq (=) (get_vars_formula pe)) in
	  let fstr = vstr ^ isabelle_of_formula pe in
      if !log_all_flag == true then
    	output_string log_all ("lemma \"" ^ fstr ^ "\"\n" ^ " apply(auto)\n oops\n" );
      let ichn = !process.inchannel in
      let ochn = !process.outchannel in

      let fnc () = 
        (* communication protocol with interactive isabelle *)
    	output_string ochn ("lemma \"" ^ fstr ^ "\"\n");flush ochn;
        let (todo_unk:string) = get_answer ichn in (*lemma#*)
        let (todo_unk:char) = input_char ichn in (*space*)

        output_string ochn "apply(auto)\n"; flush ochn;
        let (todo_unk:string) = read_until "apply#" ichn in (*proof...+goal+.....+apply#*)

        output_string ochn "oops\n"; flush ochn;
        let str = read_until "oops#" ichn in (*proof...+goal+.....+oops#*)
		check str
	  in
      let fail_with_timeout () =   
        print_string ("\n[isabelle.ml]:Timeout exception\n"); flush stdout;
        restart ("Timeout!");
        is_sat_b in
      let answ = Procutils.PrvComms.maybe_raise_and_catch_timeout_bool fnc () timeout fail_with_timeout in
      answ
  end

let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  if !log_all_flag == true then
	output_string log_all ("\n\nimply#" ^ imp_no ^ "\n");
  max_flag := false;
  choice := 1;
  let tmp_form = CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos in
  let res =  write tmp_form !Globals.sat_timeout_limit false in
  if !log_all_flag == true then
	output_string log_all ("[isabelle.ml]: imply --> "^(string_of_bool res)^"\n");
  res

let imply_sat (ante : CP.formula) (conseq : CP.formula) (timeout : float) (sat_no :  string) : bool =
  if !log_all_flag == true then
	output_string log_all ("imply#from sat#" ^ sat_no ^ "\n");
  max_flag := false;
  choice := 1;
  let tmp_form = CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos in
    (write tmp_form timeout false)

let is_sat (f : CP.formula) (sat_no : string) : bool = begin
	if !log_all_flag == true then
				output_string log_all ("\n\n#is_sat " ^ sat_no ^ "\n");
	let answ = (imply_sat f (CP.BForm((CP.BConst(false, no_pos), None), None)) !Globals.sat_timeout_limit sat_no) in
    if !log_all_flag == true then
	  output_string log_all ("[isabelle.ml]: is_sat --> "^(string_of_bool (not answ)) ^"\n");
    (not answ)
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
	  ignore(Sys.command "isabelle usedir -b HOL /usr/local/bin/MyImage");
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
