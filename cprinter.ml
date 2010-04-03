(* pretty printing for cast *)

open Format
open Globals 
open Lexing 
open Cast 
open Cformula

module P = Cpure

let fmt = ref (std_formatter)

let fmt_string x = pp_print_string (!fmt) x
let fmt_space x = pp_print_space (!fmt) x
let fmt_break x = pp_print_break (!fmt) x
let fmt_cut x = pp_print_cut (!fmt) x

let fmt_open_box n = pp_open_box (!fmt) n
let fmt_close_box x = pp_close_box (!fmt) x

let fmt_open x = fmt_open_box x
let fmt_close x = fmt_close_box x

(* let pr_bracket_one pr_elem e = *)
(*  (fmt_string "("; pr_elem e; fmt_string ")") *)

let pr_bracket isSimple pr_elem e =
 if (isSimple e) then pr_elem e
 else (fmt_string "("; pr_elem e; fmt_string ")")

let pr_list_open_sep (pr_open:unit -> unit) 
    (pr_close:unit -> unit) 
    (pr_sep:unit->unit)
    (pr_elem:'a -> unit) (xs:'a list) : unit =
  let rec helper xs = match xs with
    | [x] -> (pr_elem x)
    | y::ys -> (pr_elem y; pr_sep(); helper ys) 
  in match xs with
    | [] -> pr_open();pr_close()
    | xs -> pr_open(); (helper xs); pr_close() 

let pr_brk_after op = (fun () -> fmt_string (op); fmt_cut() )
let pr_brk_before op = (fun () -> fmt_cut() ; (fmt_string op))

let pr_list_sep x = pr_list_open_sep (fun x -> x) (fun x -> x) x 

let pr_list x = pr_list_sep fmt_space x;;

let pr_list_comma x = pr_list_sep (fun () -> fmt_string ","; fmt_space()) x 

let pr_list_args x = pr_list_open_sep 
  (fun () -> fmt_open 1; fmt_string "(")
  (fun () -> fmt_string ")"; fmt_close();) 
  fmt_space x

let pr_args open_str close_str sep_str = pr_list_open_sep 
  (fun () -> fmt_open 1; fmt_string open_str)
  (fun () -> fmt_string close_str; fmt_close();) 
  (pr_brk_after sep_str)

let pr_tuple xs = pr_args "(" ")" "," xs

let pr_set xs = pr_args "{" "}" "," xs

let pr_fn_args f op args = match args with
  | [x] -> f x
  | _ -> fmt_string op; (pr_tuple f args)

let pr_list_op op = pr_list_open_sep 
  (fun () -> fmt_open 1) fmt_close 
  (pr_brk_after op) 

let pr_op_sep  
    (pr_sep: unit -> unit ) 
    (isSimple: 'a -> bool)
    (pr_elem: 'a -> unit)
    (x:'a) (y:'a) 
    =  (pr_bracket isSimple pr_elem x); pr_sep(); 
       (pr_bracket isSimple pr_elem y)


let pr_op op = pr_op_sep (pr_brk_after op)

let pr_call  (isSimple:'a->bool) (pr_elem: 'a -> unit) (fn:string) (args:'a list)  
    = fmt_string fn; (pr_list_args pr_elem args)  

(* this op printing has no break *)
let pr_op f = pr_op_sep (fun () -> fmt_string " ") f

let pr_op_no f = pr_op_sep (fun () -> fmt_string " ") (fun x -> true) f

(* this op printing allows break *)
let pr_op_brk f = pr_op_sep fmt_space f

(* this op do not require bracket *)
let pr_op_brk_no f = pr_op_sep fmt_space (fun x -> true) f

let precedence (op:string) : int =
  match op with
  | "&" -> 0
  | _ -> -1
 
let is_no_bracket (op:string) (trivial:'a->bool) 
    (split:'a -> (string * 'a * 'a) option) (elem:'a) : bool  = 
  if (trivial elem) then true
  else 
    match (split elem) with
      | None -> false
      | Some (op2,_,_) -> 
         if (precedence op2) > (precedence op) then true
         else false
 
let string_of_specvar x = match x with
  | P.SpecVar (t, id, p) -> id ^ (match p with 
	  | Primed    -> "'" 
	  | Unprimed  -> "" )

let exp_assoc_op (e:P.exp) = match e with
  | P.Add (e1,e2,_) -> Some ("+",e1,e2)
  | P.Mult (e1,e2,_) -> Some ("*",e1,e2)
  | P.Max (e1,e2,_) -> Some ("max",e1,e2)
  | P.Min (e1,e2,_) -> Some ("min",e1,e2)
  | _ -> None

let exp_wo_paren (e:P.exp) = match e with
  | P.Null _ 
  | P.Var _ 
  | P.IConst _ 
  | P.FConst _ | P.Max _ | P.Min _ | P.BagUnion _ | P.BagIntersect _ 
    -> true
  | _ -> false

let rec pr_formula_exp (e:P.exp) =
  let pr_bk e =  pr_bracket exp_wo_paren pr_formula_exp e in
  match e with
  | P.Null l -> fmt_string "null"
  | P.Var (x, l) -> fmt_string (string_of_specvar x)
  | P.IConst (i, l) -> fmt_string (string_of_int i)
  | P.FConst (f, l) -> fmt_string (string_of_float f)
  | P.Add (e1, e2, l) -> 
      let args = bin_op_to_list "+" exp_assoc_op e in
      pr_list_op "+" pr_bk args
  | P.Mult (e1, e2, l) -> 
      let args = bin_op_to_list "*" exp_assoc_op e in
      pr_list_op "*" pr_bk  args
  | P.Max (e1, e2, l) -> 
      let args = bin_op_to_list "max" exp_assoc_op e in
      pr_fn_args pr_formula_exp "max"  args
  | P.Min (e1, e2, l) -> 
      let args = bin_op_to_list "min" exp_assoc_op e in
      pr_fn_args pr_formula_exp "min"  args
  | P.Bag (elist, l) 	-> pr_set pr_formula_exp elist
  | P.BagUnion (args, l) -> 
      let args = bin_op_to_list "union" exp_assoc_op e in
      pr_fn_args pr_formula_exp "union"  args
  | P.BagIntersect (args, l) -> 
      let args = bin_op_to_list "intersect" exp_assoc_op e in
      pr_fn_args pr_formula_exp "intersect"  args
  | P.Subtract (e1, e2, l) ->
      pr_bk e1; pr_brk_after "-"; pr_bk e2
  | P.Div (e1, e2, l) ->
      pr_bk e1; pr_brk_after "/"; pr_bk e2
  | P.BagDiff (e1, e2, l)     -> pr_formula_exp e1; pr_brk_after "-"; pr_formula_exp e2

let string_of_formula_exp (e:P.exp) =
  let old_fmt = !fmt in
  begin
    fmt := str_formatter;
    pr_formula_exp e;
    (let s = flush_str_formatter()in
    fmt := old_fmt; s)
  end    
  

(* function to print a list of strings *) 
let rec string_of_ident_list l c = match l with 
  | []               -> ""
  | h::[]            -> h 
  | h::t             -> h ^ c ^ (string_of_ident_list t c)
;;

(* pretty printing for primitive types *)
let string_of_prim_type = function 
  | Bool          -> "boolean"
  | Float         -> "float"
  | Int           -> "int"
  | Void          -> "void"
  | Bag           -> "multiset"
;;

(* pretty printing for types *)
let string_of_typ = function 
  | P.Prim t        -> string_of_prim_type t 
  | P.OType ot      -> if ((String.compare ot "") ==0) then "ptr" else ot
;;

let string_of_pos p = " "^(string_of_int p.start_pos.Lexing.pos_lnum)^":"^
				(string_of_int (p.start_pos.Lexing.pos_cnum - p.start_pos.Lexing.pos_bol));;

let string_of_int_label (i,s) s2:string = (string_of_int i)^s2
let string_of_int_label_opt h s2:string = match h with | None-> s2 | Some s -> string_of_int_label s s2
let string_of_formula_label (i,s) s2:string = ("("^(string_of_int i)^", "^s^"):"^s2) 
let string_of_formula_label_opt h s2:string = match h with | None-> s2 | Some s -> string_of_formula_label s s2
let string_of_control_path_id (i,s) s2:string = string_of_formula_label (i,s) s2
let string_of_control_path_id_opt h s2:string = string_of_formula_label_opt h s2

let string_of_constraint_relation m = match m with
  | Cpure.Unknown -> " ?  "
  | Cpure.Subsumed -> " <  "
  | Cpure.Subsuming -> " >  "
  | Cpure.Equal -> " =  "
  | Cpure.Contradicting -> "!= "
  
let string_of_spec_var sv = match sv with
  | P.SpecVar (_, v, p) -> v ^ (if p = Primed then "'" else "")

let rec string_of_h_formula h = match h with
  | Star ({h_formula_star_h1 = h1; h_formula_star_h2 = h2; h_formula_star_pos = pos}) -> 
      (string_of_h_formula h1) ^ " * " ^ (string_of_h_formula h2)
  | DataNode ({h_formula_data_node = sv; h_formula_data_name = c; h_formula_data_arguments = svs; h_formula_data_pos = pos;h_formula_data_label = pid})  ->
	  string_of_formula_label_opt pid ((string_of_spec_var sv) ^ "::" ^ c 
	  ^ "<" ^ (String.concat ", " (List.map string_of_spec_var svs)) ^ ">")
  | ViewNode ({h_formula_view_node = sv; 
			   h_formula_view_name = c; 
			   h_formula_view_arguments = svs; 
			   h_formula_view_origins = origins;
			   h_formula_view_label = pid;
			   h_formula_view_pos = pos}) ->
	  string_of_formula_label_opt pid ((string_of_spec_var sv) ^ "::" ^ c 
	  ^ "<" ^ (String.concat ", " (List.map string_of_spec_var svs)) ^ ">" )
	  (*^ "origins: " ^ (String.concat ";" origins) ^ "--"*)
  | HTrue -> "true"
  | HFalse -> "false"

let need_parenthesis = function 
    | P.Null _ | P.Var _ | P.IConst _ | P.Max _ | P.Min _  -> false 
    | _                                                    -> true
	(* _ -> false *)
;; 

(* pretty printing for an expression for a formula *)
let rec string_of_formula_exp_old = function 
  | P.Null l -> "null"
  | P.Var (x, l) -> (match x with 
					   | P.SpecVar (t, id, p) -> id ^ (match p with 
														 | Primed    -> "'" 
														 | Unprimed  -> "" ))
  | P.IConst (i, l)           -> string_of_int i
  | P.FConst (f, l) -> string_of_float f
  | P.Add (e1, e2, l) -> 
      (match e1 with 
      | P.Null _ | P.Var _ | P.IConst _ | P.FConst _ | P.Max _ | P.Min _ -> 
          (string_of_formula_exp_old e1) ^ "+"   			      
      | _ -> "(" ^ (string_of_formula_exp_old e1) ^ ")+") 
      ^ 
      (match e2 with 
      | P.Null _ | P.Var _ | P.IConst _ | P.FConst _ | P.Max _ | P.Min _ -> 
          string_of_formula_exp_old e2
	    | _ -> "(" ^ (string_of_formula_exp_old e2) ^ ")")
  | P.Subtract (e1, e2, l) ->
      if need_parenthesis e1 then 
        if need_parenthesis e2 then
          "(" ^ (string_of_formula_exp_old e1) ^ ")-(" ^ (string_of_formula_exp_old e2) ^ ")"  			      
	      else 
          "(" ^ (string_of_formula_exp_old e1) ^ ")-" ^ (string_of_formula_exp_old e2)
      else 
        (string_of_formula_exp_old e1) ^ "-" ^ (string_of_formula_exp_old e2)
  | P.Mult (e1, e2, l) ->
      (if need_parenthesis e1 then
        "(" ^ (string_of_formula_exp_old e1) ^ ")"
      else string_of_formula_exp_old e1)
      ^ "*" ^
      (if need_parenthesis e2 then
        "(" ^ (string_of_formula_exp_old e2) ^ ")"
      else string_of_formula_exp_old e2)
  | P.Div (e1, e2, l) -> 
      (if need_parenthesis e1 then
        "(" ^ (string_of_formula_exp_old e1) ^ ")"
      else string_of_formula_exp_old e1)
      ^ "/" ^
      (if need_parenthesis e2 then
        "(" ^ (string_of_formula_exp_old e2) ^ ")"
      else string_of_formula_exp_old e2)
  | P.Max (e1, e2, l)         -> "max(" ^ (string_of_formula_exp_old e1) ^ "," ^ (string_of_formula_exp_old e2) ^ ")"
  | P.Min (e1, e2, l)         -> "min(" ^ (string_of_formula_exp_old e1) ^ "," ^ (string_of_formula_exp_old e2) ^ ")" 
  | P.Bag (elist, l) 					-> "{" ^ (string_of_formula_exp_list elist) ^ "}"
  | P.BagUnion ([], l) 				-> ""
  | P.BagUnion (e::[], l)			-> (string_of_formula_exp_old e) 
  | P.BagUnion (e::rest, l) 	-> "(" ^ (string_of_formula_exp_old e) ^ " union " ^ (string_of_formula_exp_old (P.BagUnion (rest, l))) ^ ")"
  | P.BagIntersect ([], l) 		-> ""
  | P.BagIntersect (e::[], l)	-> (string_of_formula_exp_old e) 
  | P.BagIntersect (e::rest, l)->(string_of_formula_exp_old e) ^ "<intersect>" ^ (string_of_formula_exp_old (P.BagIntersect (rest, l)))
  | P.BagDiff (e1, e2, l)     -> (string_of_formula_exp_old e1) ^ "-" ^ (string_of_formula_exp_old e2) 

  
(* pretty printing for a list of pure formulae *)
and string_of_formula_exp_list l = match l with 
  | []                         -> ""
  | h::[]                      -> string_of_formula_exp h
  | h::t                       -> (string_of_formula_exp h) ^ ", " ^ (string_of_formula_exp_list t)
;;
  
(* pretty printing for boolean constraints *)
let string_of_b_formula = function 
  | P.BConst (b,l)              -> (*if b <> true then*) string_of_bool b (*else ""*)
  | P.BVar (x, l)               -> (match x with 
    | P.SpecVar (_, id, p) -> id ^ (match p with 
      | Primed    -> "'" 
      | Unprimed  -> "" ))
  | P.Lt (e1, e2, l)            -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") < (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") < " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " < " ^ (string_of_formula_exp e2)
  | P.Lte (e1, e2, l)           -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") <= (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") <= " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " <= " ^ (string_of_formula_exp e2)
  | P.Gt (e1, e2, l)            -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") > (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") > " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " > " ^ (string_of_formula_exp e2)
  | P.Gte (e1, e2, l)           -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") >= (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") >= " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " >= " ^ (string_of_formula_exp e2)
  | P.Eq (e1, e2, l)            -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") = (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") = " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " = " ^ (string_of_formula_exp e2)	
  | P.Neq (e1, e2, l)           -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") != (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") != " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " != " ^ (string_of_formula_exp e2)
  | P.EqMax (e1, e2, e3, l)     -> (string_of_formula_exp e1) ^" = max(" ^ (string_of_formula_exp e2) ^ "," ^ (string_of_formula_exp e3) ^ ")"
  | P.EqMin (e1, e2, e3, l)     -> (string_of_formula_exp e1) ^" = min(" ^ (string_of_formula_exp e2) ^ "," ^ (string_of_formula_exp e3) ^ ")"
	| P.BagIn (v, e, l)					-> (string_of_spec_var v) ^ " <in> " ^ (string_of_formula_exp e)
	| P.BagNotIn (v, e, l)			-> (string_of_spec_var v) ^ " <notin> " ^ (string_of_formula_exp e)
  | P.BagSub (e1, e2, l)			-> (string_of_formula_exp e1) ^ " <subset> " ^ (string_of_formula_exp e2)
	| P.BagMin (v1, v2, l)			-> (string_of_spec_var v1) ^ " = <min> (" ^ (string_of_spec_var v2) ^ ")"
	| P.BagMax (v1, v2, l)			-> (string_of_spec_var v1) ^ " = <max> (" ^ (string_of_spec_var v2) ^ ")"

;;

(* pretty printing for a list of pure formulas *)
let rec string_of_pure_formula_list l = match l with 
  | []               -> ""
  | h::t             -> (string_of_pure_formula h) ^ "\n" ^ (string_of_pure_formula_list t)
  
  
(* pretty printing for a pure formula *)
and string_of_pure_formula = function 
  | P.BForm (bf,lbl)              -> string_of_formula_label_opt lbl (string_of_b_formula bf)
  | P.And (f1, f2, l)             -> (string_of_pure_formula f1) ^ " & " ^ (string_of_pure_formula f2)
  | P.Or (f1, f2, lbl,l)          -> string_of_formula_label_opt lbl ("((" ^ (string_of_pure_formula f1) ^ ") | (" ^ (string_of_pure_formula f2) ^ "))")
  | P.Not (f, lbl, l)             -> string_of_formula_label_opt lbl ("!(" ^ (string_of_pure_formula f) ^ ")")
  | P.Forall (x, f,lbl, l)            -> 
	let s = "(all " ^ (match x with P.SpecVar (_, id, p) -> id ^ (match p with 
    | Primed    -> "'"
    | Unprimed  -> "")) ^ ". " ^ (string_of_pure_formula f) ^ ")" in
	string_of_formula_label_opt lbl s
  | P.Exists (x, f, lbl, l)            -> 
	let s = "(ex " ^ (match x with P.SpecVar (_, id, p) -> id ^ (match p with 
    | Primed    -> "'"
    | Unprimed  -> "")) ^ ". " ^ (string_of_pure_formula f) ^ ")" in
	string_of_formula_label_opt lbl s
and string_of_pure_formula_branches (f, l) =
  match l with
  | [] -> string_of_pure_formula f
  | _ -> string_of_pure_formula f ^ " & [" ^ (String.concat "; " (List.map (fun (l, f) -> "\"" ^ l ^ "\" : " ^ string_of_pure_formula f) l)) ^ "]"
;;

(* pretty printing for a cformula *)                                                         (*NOT DONE*)

let string_of_flow_store l = (String.concat " " (List.map (fun h-> (h.formula_store_name^"= "^
						(let rr = h.formula_store_value.formula_flow_interval in
							(string_of_int (fst rr))^"-"^(string_of_int (snd rr)))^" ")) l))

let rec string_of_flow_formula f c = 
	"{"^f^",("^(string_of_int (fst c.formula_flow_interval))^","^(string_of_int (snd c.formula_flow_interval))^
	")="^(Util.get_closest c.formula_flow_interval)^","^(match c.formula_flow_link with | None -> "" | Some e -> e)^"}"
	


and string_of_t_formula = function
(* commented on 09.06.08
 | TypeExact ({t_formula_sub_type_var = v;
				t_formula_sub_type_type = c}) -> 
	  (string_of_spec_var v) ^ " = " ^ c
  | TypeSub ({t_formula_sub_type_var = v;
			  t_formula_sub_type_type = c}) -> 
	  (string_of_spec_var v) ^ " <: " ^ c
  | TypeSuper ({t_formula_sub_type_var = v;
				t_formula_sub_type_type = c}) -> 
	  (string_of_spec_var v) ^ " > " ^ c*)
  | TypeAnd ({t_formula_and_f1 = f1;
			  t_formula_and_f2 = f2}) -> 
	  (string_of_t_formula f1) ^ " & " ^ (string_of_t_formula f2)
  | TypeTrue -> "TypeTrue"
  | TypeFalse -> "TypeFalse"

let rec string_of_formula = function 
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
      (string_of_formula f1) ^ "\nor " ^ (string_of_formula f2)
  | Base ({formula_base_heap = h; 
		   formula_base_pure = p; 
		   formula_base_branches = b; 
		   formula_base_type = t;
		   formula_base_flow = fl;
		   formula_base_pos = pos}) -> 
      (string_of_h_formula h) ^ " & " ^ (string_of_pure_formula_branches (p, b))^"&"^(string_of_flow_formula "FLOW" fl) (* ^ " & " ^ (string_of_t_formula t) *)
  | Exists ({formula_exists_qvars = svs; 
			 formula_exists_heap = h; 
			 formula_exists_pure = p; 
		     formula_exists_branches = b; 
			 formula_exists_type = t;
			 formula_exists_flow = fl;
			 formula_exists_pos = pos}) -> 
      "(EX " ^ (String.concat ", " (List.map string_of_spec_var svs)) 
      ^ " . " ^ (string_of_h_formula h) ^ " & " ^ (string_of_pure_formula_branches (p, b))^"&"^(string_of_flow_formula "FLOW" fl)
	  ^ (* " & " ^ (string_of_t_formula t)^ *) ")"

(* function to print a list of type F.formula * F.formula *)
let rec string_of_formulae_list l = match l with 
  | []               -> ""
  | (f1, f2)::[]     -> "\nrequires " ^ (string_of_formula f1) ^ "\nensures " ^ (string_of_formula f2)  
  | (f1, f2)::t      -> "\nrequires " ^ (string_of_formula f1) ^ "\nensures " ^ (string_of_formula f2) ^ (string_of_formulae_list t)
;;

(* pretty printing for a spec_var *)
let string_of_spec_var = function 
  | P.SpecVar (_, id, p) -> id ^ (match p with 
    | Primed   -> "'"
    | Unprimed -> "")

(* pretty printing for a spec_var list *)
let rec string_of_spec_var_list l = match l with 
  | []               -> ""
  | h::[]            -> string_of_spec_var h 
  | h::t             -> (string_of_spec_var h) ^ "," ^ (string_of_spec_var_list t)
;;


let rec string_of_ext_formula = function
	| ECase {
			formula_case_exists =ee;
			formula_case_branches  =  case_list ;
		} -> 
			let l3 = List.fold_left (fun a c -> a^" "^ (string_of_spec_var c)) "" ee in
			let impl = List.fold_left (fun a (c1,c2) -> a^"\n\t "^(string_of_pure_formula c1)^"->"^ 		
		( List.fold_left  (fun a c -> a ^" "^(string_of_ext_formula c )) "" c2)^"\n") "" case_list in
			("case ex.["^l3^"]{"^impl^"}")
	|EBase {
		 	formula_ext_implicit_inst = ii;
			formula_ext_explicit_inst = ei;
			formula_ext_exists = ee;
		 	formula_ext_base = fb;
		 	formula_ext_continuation = cont;	
		} -> 
				let l1 = List.fold_left (fun a c -> a^" "^ (string_of_spec_var c)) "" ii in
				let l2 = List.fold_left (fun a c -> a^" "^ (string_of_spec_var c)) "" ei in
				let l3 = List.fold_left (fun a c -> a^" "^ (string_of_spec_var c)) "" ee in
				let b = string_of_formula fb in
				let c = (List.fold_left (fun a d -> a^"\n"^(string_of_ext_formula d)) "{" cont)^"}" in
				"ex.["^l3^"]["^l1^"]["^l2^"]"^b^" "^c
	| EAssume (x,b,(_,y2))-> "EAssume "^y2^": ref["^(string_of_spec_var_list x)^"] "^(string_of_formula b)
;;

let string_of_struc_formula d =  List.fold_left  (fun a c -> a ^"\n "^(string_of_ext_formula c )) "" d 
;;

(*
let rec string_of_spec = function
	| SCase {scase_branches= br;} ->
		 (List.fold_left (fun a (c1,c2)->a^"\n"^(string_of_pure_formula c1)^"-> "^
		( List.fold_left  (fun a c -> a ^"\n "^(string_of_spec c )) "" c2)) "case { " br)^"}\n"
	| SRequires 	{
			srequires_implicit_inst = ii;
			srequires_explicit_inst = ei;
			srequires_base = fb;
			srequires_continuation = cont;
			}	 ->
				let l2 = List.fold_left (fun a c -> a^ " " ^(string_of_spec_var c)) "" ei in
				let l1 = List.fold_left (fun a c -> a^ " " ^(string_of_spec_var c)) "" ii in
				let b = string_of_formula fb in				
				"requires ["^l1^"]["^l2^"]"^b^" "^((List.fold_left (fun a d -> a^"\n"^(string_of_spec d)) "{" cont)^"}")
	| SEnsure{ sensures_base = fb } -> ("ensures "^(string_of_formula fb))
;;


let string_of_specs d =  List.fold_left  (fun a c -> a ^" "^(string_of_spec c )) "" d 
;;*)


(* functions to decide if an expression needs parenthesis *)
let need_parenthesis e = match e with 
  | BConst _ | Bind _ | FConst _ | IConst _ | Unit _ | Var _ -> false 
  | _                                                        -> true
;;

let string_of_sharp st = match st with
	| Sharp_ct t -> string_of_flow_formula "" t
	| Sharp_v  f -> "flow_var "^f
(* pretty printing for expressions *)
let rec string_of_exp = function 
  | Label l-> "LABEL! "^( (string_of_int_label_opt (fst  l.exp_label_path_id) (","^((string_of_int (snd l.exp_label_path_id))^": "^(string_of_exp l.exp_label_exp)))))
  | Java ({exp_java_code = code}) -> code
  | CheckRef _ -> ""
  | Assert ({exp_assert_asserted_formula = f1o; exp_assert_assumed_formula = f2o; exp_assert_pos = l; exp_assert_path_id = pid}) -> 
      let s = 
	begin
	  let str1 = 
	    match f1o with
	      | None -> ""
	      | Some f1 -> "assert " ^(string_of_control_path_id pid (":"^(string_of_struc_formula f1))) in
	  let str2 =
	    match f2o with
	      | None -> ""
	      | Some f2 -> "assume " ^ (string_of_formula f2) in
	    str1 ^ " " ^ str2
	end in
	string_of_formula_label pid s 
  | Assign ({exp_assign_lhs = id; exp_assign_rhs = e; exp_assign_pos = l}) -> 
      id ^ " = " ^ (string_of_exp e)
  | BConst ({exp_bconst_val = b; exp_bconst_pos = l}) -> 
      string_of_bool b 
  | Bind ({exp_bind_type = _; 
	   exp_bind_bound_var = (_, id); 
	   exp_bind_fields = idl;
	   exp_bind_body = e;
	   exp_bind_path_id = pid;
	   exp_bind_pos = l}) -> 
      string_of_control_path_id_opt pid ("bind " ^ id ^ " to (" ^ (string_of_ident_list (snd (List.split idl)) ",") ^ ") in \n{" ^ (string_of_exp e) ^ "\n}")
  | Block ({exp_block_type = _;
	    exp_block_body = e;
	    exp_block_local_vars = _;
	    exp_block_pos = _}) -> "{\n" ^ (string_of_exp e) ^ "\n}"
  | ICall ({exp_icall_type = _;
	    exp_icall_receiver = r;
	    exp_icall_method_name = id;
	    exp_icall_arguments = idl;
	    exp_icall_visible_names = _;
	    exp_icall_path_id = pid;
	    exp_icall_pos = l}) -> 
      string_of_control_path_id_opt pid (r ^ "." ^ id ^ "(" ^ (string_of_ident_list idl ",") ^ ")" )
  | Cast ({exp_cast_target_type = t;
	   exp_cast_body = body}) -> begin
      "(" ^ (string_of_typ t) ^ " )" ^ string_of_exp body
    end
  | Cond ({exp_cond_type = _;
	   exp_cond_condition = id;
	   exp_cond_then_arm = e1;
	   exp_cond_else_arm = e2;
	   exp_cond_path_id = pid;
	   exp_cond_pos = l}) -> 
      string_of_control_path_id_opt pid ("if (" ^ id ^ ") " ^(string_of_exp e1) ^ "\nelse " ^ (string_of_exp e2) ^ "\n" )
  | Debug ({exp_debug_flag = b; exp_debug_pos = l}) -> if b then "debug" else ""
  | Dprint _                   -> "dprint"
  | FConst ({exp_fconst_val = f; exp_fconst_pos = l}) -> string_of_float f 
      (*| FieldRead (_, (v, _), (f, _), _) -> v ^ "." ^ f*)
      (*| FieldWrite ((v, _), (f, _), r, _) -> v ^ "." ^ f ^ " = " ^ r*)
  | IConst ({exp_iconst_val = i; exp_iconst_pos = l}) -> string_of_int i 
  | New ({exp_new_class_name = id;
	  exp_new_arguments = idl;
	  exp_new_pos = l}) -> 
      "new" ^ id ^ "(" ^ (string_of_ident_list (snd (List.split idl)) ",") ^ ")"
  | Null l -> "null"
  | Print (i, l)-> "print " ^ (string_of_int i) 
  | Sharp ({exp_sharp_flow_type = st;
	    exp_sharp_val = eo;
	    exp_sharp_path_id =pid;
	    exp_sharp_pos = l}) ->begin
      string_of_control_path_id_opt pid (
	match st with
	  | Sharp_ct f ->  if (Cformula.equal_flow_interval f.formula_flow_interval !ret_flow_int) then
	      (match eo with 
		 |Sharp_prog_var e -> "return " ^ (snd e)
		 | _   -> "return")
	    else  (match eo with 
		     | Sharp_prog_var e -> "throw " ^ (snd e)
		     | Sharp_finally e -> "throw " ^ e ^":"^(string_of_sharp st)
		     | _   -> "throw "^(string_of_sharp st))
	  | _ -> (match eo with 
		    | Sharp_prog_var e -> "throw " ^ (snd e)
		    | Sharp_finally e -> "throw " ^ e ^":" ^(string_of_sharp st)
		    | _   -> "throw "^(string_of_sharp st)))end 
  | SCall ({exp_scall_type = _;
	    exp_scall_method_name = id;
	    exp_scall_arguments = idl;
	    exp_scall_visible_names = _;
	    exp_scall_path_id = pid;
	    exp_scall_pos = l}) -> 
      string_of_control_path_id_opt pid (id ^ "(" ^ (string_of_ident_list idl ",") ^ ")")
  | Seq ({exp_seq_type = _;
	  exp_seq_exp1 = e1;
	  exp_seq_exp2 = e2;
	  exp_seq_pos = l}) -> 
      (string_of_exp e1) ^ ";\n" ^ (string_of_exp e2)
  | This _ -> "this"
  | Var ({exp_var_type = _;
	  exp_var_name = id;
	  exp_var_pos = l}) -> id 
  | VarDecl ({exp_var_decl_type = t;
	      exp_var_decl_name = id;
	      exp_var_decl_pos = _}) -> 
      (string_of_typ t) ^" "^ id (*^ (string_of_exp e1) ^ ";\n" ^ (string_of_exp e2)*)
  | Unit l                     -> ""
  | While ({exp_while_condition = id;
	    exp_while_body = e;
	    exp_while_spec = fl;
	    exp_while_path_id = pid;
	    exp_while_pos = l})  -> 
      string_of_control_path_id_opt pid ("while " ^ id ^ (string_of_struc_formula fl) ^ "\n{\n" ^ (string_of_exp e) ^ "\n}\n")
  | Unfold ({exp_unfold_var = sv}) -> "unfold " ^ (string_of_spec_var sv)
  | Try b -> 
      let c = b.exp_catch_clause.exp_catch_flow_type in
	string_of_control_path_id_opt b.exp_try_path_id  
	  "try \n"^(string_of_exp b.exp_try_body)^"\n catch ("^ (string_of_int (fst c))^","^(string_of_int (snd c))^")="^(Util.get_closest c)^ 
	  (match b.exp_catch_clause.exp_catch_flow_var with 
	     | Some c -> (" @"^c^" ")
	     | _ -> " ")^
	  (match b.exp_catch_clause.exp_catch_var with 
	     | Some (a,b) -> ((string_of_typ a)^":"^b^" ")
	     | _ -> " ")^") \n\t"^(string_of_exp b.exp_catch_clause.exp_catch_body)
;;


(* pretty printing for one data declaration*)
let string_of_decl d = match d with 
 | (t, id)             -> (string_of_typ t) ^ " " ^ id 
;;           

(* function to print a list of typed_ident *) 
let rec string_of_decl_list l c = match l with 
  | []               -> ""
  | h::[]            -> "  " ^ string_of_decl h 
  | h::t             -> "  " ^ (string_of_decl h) ^ c ^ (string_of_decl_list t c)
;;

(* pretty printing for a data declaration *)
let string_of_data_decl d = "data " ^ d.data_name ^ " {\n" ^ (string_of_decl_list d.data_fields "\n") ^ "\n}"
;;


(* pretty printing for a view *)
let string_of_view_decl v = "view " ^ v.view_name ^ "<" ^ (string_of_spec_var_list v.view_vars) ^ ">=" ^
                            (string_of_struc_formula v.view_formula) 
  ^ "\n\tinv " ^ (string_of_pure_formula (fst v.view_user_inv))
  ^ "\n\tunstruc_f" ^(string_of_formula v.view_un_struc_formula)
  ^ "\n\txform " ^ (string_of_pure_formula (fst v.view_x_formula))
  ^ "\n\t view_base_case: "^
  (match v.view_base_case with 
	| None -> "none " 
	|Some (s1,(s3,s2)) -> ((string_of_pure_formula s1)^"->"^(string_of_pure_formula_branches (s3, s2))))
    

(* pretty printing for a procedure *)
let string_of_proc_decl p = 
  let locstr = (string_of_full_loc p.proc_loc)  
  in  (string_of_typ p.proc_return) ^ " " ^ p.proc_name ^ "(" ^ (string_of_decl_list p.proc_args ",") ^ ")\n" 
  ^ "static " ^ (string_of_struc_formula p.proc_static_specs) ^ "\n"
  ^ "dynamic " ^ (string_of_struc_formula p.proc_dynamic_specs) ^ "\n"
  ^ (if U.empty p.proc_by_name_params then "" 
	 else ("\nref " ^ (String.concat ", " (List.map string_of_spec_var p.proc_by_name_params)) ^ "\n"))
  ^ (match p.proc_body with 
       | Some e -> (string_of_exp e) ^ "\n\n"
	   | None   -> "\n") ^ locstr
;; 

(* pretty printing for a list of data_decl *)
let rec string_of_data_decl_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_data_decl h) 
 | h::t      -> (string_of_data_decl h) ^ "\n" ^ (string_of_data_decl_list t)
;;

(* pretty printing for a list of proc_decl *)
let rec string_of_proc_decl_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_proc_decl h) 
 | h::t      -> (string_of_proc_decl h) ^ "\n" ^ (string_of_proc_decl_list t)
;;

(* pretty printing for a list of view_decl *)
let rec string_of_view_decl_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_view_decl h) 
 | h::t      -> (string_of_view_decl h) ^ "\n" ^ (string_of_view_decl_list t)
;;

(* pretty printing for a program written in core language *)
let string_of_program p = "\n" ^ (string_of_data_decl_list p.prog_data_decls) ^ "\n\n" ^ 
                          (string_of_view_decl_list p.prog_view_decls) ^ "\n\n" ^ 
                          (string_of_proc_decl_list p.prog_proc_decls) ^ "\n"
;;


(*
  Created 22-Feb-2006

  Pretty printing fo the AST for the core language
*)

let string_of_prior_steps pt =
  (String.concat "\n " (List.rev pt))

let string_of_path_trace  pt =
  (String.concat ", " (List.map (fun (c1,c3)-> "("^(string_of_int_label c1 "")^","^(string_of_int c3)^")") pt))

let string_of_estate (es : entail_state) = 
  "es_formula: " ^ (string_of_formula es.es_formula)
  ^ "\nes_pure: " ^ (string_of_pure_formula_branches es.es_pure)
  ^ "\nes_orig_conseq: " ^ (string_of_struc_formula es.es_orig_conseq)
  ^ "\nes_heap: " ^ (string_of_h_formula es.es_heap)
  ^ "\nes_evars: " ^ (String.concat ", " (List.map string_of_spec_var es.es_evars))
  ^ "\nes_ivars: " ^ (String.concat ", " (List.map string_of_spec_var es.es_ivars))
  ^ "\nes_expl_vars: " ^ (String.concat ", " (List.map string_of_spec_var es.es_expl_vars))
  ^"\n es_gen_expl_vars:"^(String.concat ", " (List.map string_of_spec_var es.es_gen_expl_vars))
  ^"\n es_gen_impl_vars:"^(String.concat ", " (List.map string_of_spec_var es.es_gen_impl_vars))
  ^"\n es_success_pts:"^(String.concat ", " (List.map (fun (c1,c2)-> "("^(string_of_formula_label c1 "")^","^(string_of_formula_label c2 "")^")") es.es_success_pts))
  ^"\n es_residue_pts:"^(String.concat ", " (List.map (fun c-> string_of_formula_label c "") es.es_residue_pts))
  ^"\n es_path_label:"^ (string_of_path_trace es.es_path_label)
  
let string_of_fail_estate (es:fail_context) : string = "{"^
  "\n fc_prior_steps:\n "^(string_of_prior_steps es.fc_prior_steps)  ^
  "\n fc_message: "^es.fc_message ^
  "\n fc_current_lhs: "^ (string_of_estate es.fc_current_lhs) ^
  "\n fc_orig_conseq: "^ (string_of_struc_formula es.fc_orig_conseq )^ 
  "\n fc_failure_pts: ["^ (String.concat "," (List.map (fun c-> string_of_formula_label c "")es.fc_failure_pts))^"]}\n"

let rec string_of_context (ctx: context) = match ctx with
  | Ctx es -> string_of_estate es
  | OCtx (c1, c2) -> (string_of_context c1) ^ "\nCtxOR\n" ^ (string_of_context c2)

and string_of_context_list ctx = String.concat "\n;\n" (List.map string_of_context ctx)

and string_of_fail_type ft :string = 
  let f = (fun c l-> match c with
    | Trivial_Reason s -> " Trivial fail : "^s^"\n"
      | Basic_Reason br -> (string_of_fail_estate br)
      | Or_Reason _ -> "fail_Or(\n" ^(String.concat "\n,\n" l)^")\n"
      | And_Reason _ -> "fail_And(\n" ^(String.concat "\n,\n" l)^")\n") in
  (fold_fail_context f ft)
  
  
let string_of_list_context (ctx:list_context): string = match ctx with
    | FailCtx ft -> "fail context: \n" ^ (string_of_fail_type ft) ^
            (*"\n successful states within fail context: \n"^
             (string_of_context_list lc)^*)"\n"
    | SuccCtx sc -> "success context: ["^(string_of_context_list sc)^"]\n"
    
let string_of_partial_context (l1,l2) = 
  "failed states:[ "^ 
  String.concat "\n;\n"(List.map (fun (lbl,fs)-> "\n( lbl : "^(string_of_path_trace lbl)^"\n state:"^ (string_of_fail_type fs)) l1) ^
  "];\n Succesfull states:[ "^
  String.concat "\n;\n"(List.map (fun (lbl,fs)-> "\n( lbl : "^(string_of_path_trace lbl)^"\n state:"^ (string_of_context fs)) l2) ^"]\n"
 
   
let get_label_partial_context (fs,ss) : string =
if (U.empty fs) then "" else string_of_path_trace(fst(List.hd fs))

let get_label_list_partial_context (cl:Cformula.list_partial_context) : string =
if (U.empty cl) then "" else get_label_partial_context (List.hd cl)


let summary_list_path_trace l =  String.concat "; " (List.map  (fun (lbl,_) -> string_of_path_trace lbl) l)

let summary_partial_context (l1,l2) =  "("^string_of_int (List.length l1) ^", "^ string_of_int (List.length l2)^" "^(summary_list_path_trace l2)^")"
   
let summary_list_partial_context lc =  "["^(String.concat " " (List.map summary_partial_context lc))^"]"

let string_of_list_partial_context lc = "\n;List of Partial Context:"^(summary_list_partial_context lc)^"\n"^String.concat ("\n;;\n") (List.map string_of_partial_context lc)

let string_of_list_list_partial_context lc = "\n;List List of Partial
Context:"^string_of_int(List.length lc)^"\n"^String.concat ("\n;;\n")
  (List.map string_of_list_partial_context lc)


 
