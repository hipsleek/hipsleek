(* pretty printing for iast *)

(* open the needed modules *)
open Iast
open Globals
open Lexing

module F = Iformula
module P = Ipure

(* function to enclose a string s into parenthesis *)
let parenthesis s = "(" ^ s ^ ")"
;;

(* function to concatenate the elements of a list of strings and puts c betwwen then (for field access)*)
let rec concatenate_string_list l c = match l with 
 | [] -> ""
 | h::[] -> h 
 | h::t -> h ^ c ^ (concatenate_string_list t c)
;;

(* pretty printing for primitive types *)
let string_of_prim_type = function 
  | Bool          -> "boolean "
  | Float         -> "float "
  | Int           -> "int "
  | Void          -> "void "
  | Bag           -> "bag "
  | List          -> "list "
;;

(* pretty printing for types *)
let string_of_typ = function 
  | Prim t        -> string_of_prim_type t 
  | Named ot      -> ot ^ " "
  | Array _ -> "array"
;;

(* pretty printing for unary operators *)
let string_of_unary_op = function 
  | OpUMinus       -> "-"
  | OpPreInc       -> "++"
  | OpPreDec       -> "--"
  | OpPostInc      -> "++"
  | OpPostDec      -> "--"
  | OpNot          -> "!"                                   
;;    

(* pretty priting for binary operators *)
let string_of_binary_op = function 
  | OpPlus         -> " + "
  | OpMinus        -> " - "
  | OpMult         -> " * "
  | OpDiv          -> " / "
  | OpMod          -> " % "
  | OpEq           -> " == "
  | OpNeq          -> " != "                                 
  | OpLt           -> " < "
  | OpLte          -> " <= "
  | OpGt           -> " > "
  | OpGte          -> " >= "
  | OpLogicalAnd   -> " && "                                 
  | OpLogicalOr    -> " || "
  | OpIsNull       -> " == "
  | OpIsNotNull    -> " != "
;;

(* pretty printing for assign operators *)
let string_of_assign_op = function 
  | OpAssign      -> " = "
  | OpPlusAssign  -> " += "
  | OpMinusAssign -> " -= "
  | OpMultAssign  -> " *= "
  | OpDivAssign   -> " /= "
  | OpModAssign   -> " %= "
;;

let string_of_primed = function 
	| Unprimed -> ""
	| Primed -> "'";;

(* function used to decide if parentrhesis are needed or not *)
let need_parenthesis = function 
    | P.Null _ | P.Var _ | P.IConst _ | P.Max _ | P.Min _  -> false
    | _                                                    -> true
;; 

let string_of_label = function 
  | NoJumpLabel      -> ""
  | JumpLabel l  -> l^" : "
;;

let string_of_formula_label (i,s) s2:string = ("("^(string_of_int i)^", "^s^"):"^s2)
let string_of_formula_label_opt h s2:string = match h with | None-> s2 | Some s -> string_of_formula_label s s2
let string_of_control_path_id (i,s) s2:string = string_of_formula_label (i,s) s2
let string_of_control_path_id_opt h s2:string = string_of_formula_label_opt h s2



let string_of_var_list vl = (List.fold_left (fun a (c1,c2)-> a^" "^c1^(match c2 with | Primed -> "'"| _ -> "")) "" vl);;


(* pretty printing for an expression for a formula *)
let rec string_of_formula_exp = function 
  | P.Null l                  -> "null"
  | P.Var (x, l)        -> (match x with 
															|(id, p) -> id ^ (match p with 
																									| Primed    -> "'" 
																									| Unprimed  -> "" ))
  | P.IConst (i, l)           -> string_of_int i
  | P.FConst (f, _) -> string_of_float f
  | P.Add (e1, e2, l)	      -> (match e1 with 
																	| P.Null _ 
																	| P.Var _ 
																	| P.IConst _ 
																	| P.Max _ 
																	| P.Min _   -> (string_of_formula_exp e1) ^ "+"   			      
																	| _  -> "(" ^ (string_of_formula_exp e1) ^ ")+") 
			^ (match e2 with 
					 | P.Null _ | P.Var _ | P.IConst _ | P.Max _ | P.Min _ -> string_of_formula_exp e2
					 | _                                                   -> "(" ^ (string_of_formula_exp e2) ^ ")")
  | P.Subtract (e1, e2, l)    -> if need_parenthesis e1
    then 
      if need_parenthesis e2
      then  "(" ^ (string_of_formula_exp e1) ^ ")-(" ^ (string_of_formula_exp e2) ^ ")"  			      
		  else "(" ^ (string_of_formula_exp e1) ^ ")-" ^ (string_of_formula_exp e2)
    else 
			(string_of_formula_exp e1) 
			^ "-" ^ (string_of_formula_exp e2)										    
  | P.Mult (e1, e2, _) ->
      "(" ^ (string_of_formula_exp e1) ^ ") * (" ^ (string_of_formula_exp e2) ^ ")"
  | P.Div (e1, e2, _) ->
      "(" ^ (string_of_formula_exp e1) ^ ") / (" ^ (string_of_formula_exp e2) ^ ")"
  | P.Max (e1, e2, l)         -> "max(" ^ (string_of_formula_exp e1) ^ "," ^ (string_of_formula_exp e2) ^ ")"
  | P.Min (e1, e2, l)         -> "min(" ^ (string_of_formula_exp e1) ^ "," ^ (string_of_formula_exp e2) ^ ")" 
  | P.List (elist, l)		-> "[|" ^ (string_of_formula_exp_list elist) ^ "|]"
  | P.ListAppend (elist, l) -> "app(" ^ (string_of_formula_exp_list elist) ^ ")"
  | P.ListCons (e1, e2, l)	-> (string_of_formula_exp e1) ^ ":::" ^ (string_of_formula_exp e2)
  | P.ListHead (e, l)		-> "head(" ^ (string_of_formula_exp e) ^ ")"
  | P.ListTail (e, l)		-> "tail(" ^ (string_of_formula_exp e) ^ ")"
  | P.ListLength (e, l)		-> "len(" ^ (string_of_formula_exp e) ^ ")"
  | P.ListReverse (e, l)	-> "rev(" ^ (string_of_formula_exp e) ^ ")"
	| _ -> "bag constraint"

(* pretty printing for a list of pure formulae *)
and string_of_formula_exp_list l = match l with 
  | []                         -> ""
  | h::[]                      -> string_of_formula_exp h
  | h::t                       -> (string_of_formula_exp h) ^ ", " ^ (string_of_formula_exp_list t)
;;
  
(* pretty printing for boolean constraints *)
let string_of_b_formula = function 
  | P.BConst (b,l)              -> if b <> true then string_of_bool b else ""
  | P.BVar (x, l)               -> (match x with 
    |(id, p) -> id ^ (match p with 
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
  | P.ListIn (e1, e2, l)		-> (string_of_formula_exp e1) ^ " inlist " ^ (string_of_formula_exp e2)
  | P.ListNotIn (e1, e2, l)		-> (string_of_formula_exp e1) ^ " notinlist " ^ (string_of_formula_exp e2)
  | P.ListAllN (e1, e2, l)		-> "alln(" ^ (string_of_formula_exp e1) ^ ", " ^ (string_of_formula_exp e2) ^ ")"
  | P.ListPerm (e1, e2, l)		-> "perm(" ^ (string_of_formula_exp e1) ^ ", " ^ (string_of_formula_exp e2) ^ ")"
  | _ -> "bag constraint"
;;

(* pretty printing for a pure formula *)
let rec string_of_pure_formula = function 
  | P.BForm (bf,lbl)                    -> string_of_b_formula bf 
  | P.And (f1, f2, l)             -> "(" ^ (string_of_pure_formula f1) ^ ") & (" ^ (string_of_pure_formula f2) ^ ")"  
  | P.Or (f1, f2,lbl, l)              -> "(" ^ (string_of_pure_formula f1) ^ ") | (" ^ (string_of_pure_formula f2) ^ ")"
  | P.Not (f,lbl, l)                  -> "!(" ^ (string_of_pure_formula f) ^ ")"
  | P.Forall (x, f,lbl, l)            -> "all " ^ (match x with (id, p) -> id ^ (match p with 
    | Primed    -> "'"
    | Unprimed  -> "")) ^ " (" ^ (string_of_pure_formula f) ^ ")"
  | P.Exists (x, f,lbl, l)            -> "ex " ^ (match x with (id, p) -> id ^ (match p with 
    | Primed    -> "'"
    | Unprimed  -> "")) ^ " (" ^ (string_of_pure_formula f) ^ ")"
;;    

let is_bool_f = function 
  | F.HTrue | F.HFalse -> true 
  | _                  -> false 
;;

(* pretty printing for a heap formula *)
let rec string_of_h_formula = function 
  | F.Star ({F.h_formula_star_h1 = f1;
			 F.h_formula_star_h2 = f2;
			 F.h_formula_star_pos = l} ) -> 
	  if is_bool_f f1 then 
		if is_bool_f f2 then (string_of_h_formula f1) ^ " * " ^ (string_of_h_formula f2)
        else (string_of_h_formula f1) ^ " * (" ^ (string_of_h_formula f2) ^ ")" 
	  else
		"(" ^ (string_of_h_formula f1) ^ ") * (" ^ (string_of_h_formula f2) ^ ")"    
  | F.HeapNode ({F.h_formula_heap_node = x;
				 F.h_formula_heap_name = id;
				 F.h_formula_heap_arguments = pl;
				 F.h_formula_heap_label = pi;
				 F.h_formula_heap_pos = l}) -> 				 
				 string_of_formula_label_opt pi				 
				 ((fst x)^(if (snd x)=Primed then  "'" else "") ^ "::" ^ id ^ "<" ^ (string_of_formula_exp_list pl) ^ ">")
									
	| F.HeapNode2 ({F.h_formula_heap2_node = (v, p);
									F.h_formula_heap2_name = id;
									F.h_formula_heap2_label = pi;
									F.h_formula_heap2_arguments = args}) ->
			let tmp1 = List.map (fun (f, e) -> f ^ "=" ^ (string_of_formula_exp e)) args in
			let tmp2 = String.concat ", " tmp1 in
				string_of_formula_label_opt pi
				(v ^ (if p = Primed then "'" else "") ^ "::" ^ id ^ "<" ^ tmp2 ^ ">")
  | F.HTrue                         -> ""                                                                                                (* ?? is it ok ? *)
  | F.HFalse                        -> "false"
;;
 
let string_of_identifier (d1,d2) = d1^(match d2 with | Primed -> "'" | Unprimed -> "");; 

(* pretty printing for formulae *) 
let rec string_of_formula = function 
  | Iast.F.Base ({F.formula_base_heap = hf;
				  F.formula_base_pure = pf;
				  F.formula_base_flow = fl;
				  F.formula_base_pos = l}) ->  
	  if hf = F.HTrue then 
		string_of_pure_formula pf
      else if hf = F.HFalse then 
		let s = string_of_pure_formula pf in 
          (if s = "" then  (string_of_h_formula hf)
            else (string_of_h_formula hf) ^ "*(" ^ (string_of_pure_formula pf) ^ ")( FLOW "^fl^")")
	  else 
		let s = string_of_pure_formula pf in 
          (if s = "" then  (string_of_h_formula hf)
            else "(" ^ (string_of_h_formula hf) ^ ")*(" ^ (string_of_pure_formula pf) ^ ")( FLOW "^fl^")")
  | Iast.F.Or ({F.formula_or_f1 = f1;
				F.formula_or_f2 = f2;
				F.formula_or_pos = l}) -> (string_of_formula f1) ^ "\nor" ^ (string_of_formula f2)
	  (*  | Iast.F.Exists (x, f, l)                -> "ex " ^ (match x with 
		  | (id, p) -> match p with 
		  | Primed    -> id ^ "'"
		  | Unprimed  -> id ) ^ ".(" ^ (string_of_formula f) ^ ")" *)
  | Iast.F.Exists ({F.formula_exists_qvars = qvars;
					F.formula_exists_heap = hf;
					F.formula_exists_flow = fl;
					F.formula_exists_pure = pf}) ->
	  "(EX " ^ (String.concat ", " (List.map fst qvars)) ^ " . "
	  ^ (if hf = F.HTrue then 
		   string_of_pure_formula pf
		 else if hf = F.HFalse then 
		   let s = string_of_pure_formula pf in 
			 (if s = "" then  (string_of_h_formula hf)
              else (string_of_h_formula hf) ^ "*(" ^ (string_of_pure_formula pf) ^ ")( FLOW "^fl^")")
		 else 
		   let s = string_of_pure_formula pf in 
			 (if s = "" then  (string_of_h_formula hf)
              else "(" ^ (string_of_h_formula hf) ^ ")*(" ^ (string_of_pure_formula pf) ^ ")( FLOW "^fl^")"))
	  ^ ")"
;;

let rec string_of_ext_formula = function
	| Iformula.ECase {
			Iformula.formula_case_branches  =  case_list ;
		} -> 
			let impl = List.fold_left (fun a (c1,c2) -> a^"\n\t "^(string_of_pure_formula c1)^"->"^ 		
		( List.fold_left  (fun a c -> a ^" "^(string_of_ext_formula c )) "" c2)^"\n") "" case_list in
			("case{"^impl^"}")
	|Iformula.EBase {
		 	Iformula.formula_ext_implicit_inst = ii;
			Iformula.formula_ext_explicit_inst = ei;
		 	Iformula.formula_ext_base = fb;
		 	Iformula.formula_ext_continuation = cont;	
		} -> 
				let l1 = List.fold_left (fun a (c1,c2) -> a^" "^ c1) "" ii in
				let l2 = List.fold_left (fun a (c1,c2) -> a^" "^ c1) "" ei in
				let b = string_of_formula fb in
				let c = (List.fold_left (fun a d -> a^"\n"^(string_of_ext_formula d)) "{" cont)^"}" in
				"["^l1^"]["^l2^"]"^b^" "^c
	| Iformula.EAssume (b,(n1,n2))-> "EAssume "^(string_of_int n1)^","^n2^":"^(string_of_formula b)
;;

let string_of_struc_formula d =  List.fold_left  (fun a c -> a ^"\n "^(string_of_ext_formula c )) "" d 
;;
(*
let rec string_of_spec = function
	| SCase {scase_branches= br;} ->
		 (List.fold_left (fun a (c1,c2)->a^"\n"^(string_of_pure_formula c1)^"-> "^
		( List.fold_left  (fun a c -> a ^"\n "^(string_of_spec c )) "" c2)) "case { " br)^"}\n"
	| SRequires 	{
			(*srequires_exists_vars = ev;*)
			srequires_explicit_inst = ei;
			srequires_base = fb;
			srequires_continuation = cont;
			}	 ->
				(*let l1 = List.fold_left (fun a c -> a^ ","^(string_of_identifier c)) "" ev in*)
				let l2 = List.fold_left (fun a c -> a^ (string_of_identifier c)) "" ei in
				let b = string_of_formula fb in
				let c = (List.fold_left (fun a  c1-> a^"\n"^string_of_spec c1) "{" cont)^"}\n" in
				(*"["^l1^"],"*)"["^l2^"]"^b^" "^c
	| SEnsure{sensures_base = fb } ->(string_of_formula fb)
;;


let string_of_specs d =  List.fold_left  (fun a c -> a ^" "^(string_of_spec c )) "" d 
;;*)


(* pretty printing for a list of formulae (f * f) list *)
let rec string_of_form_list l = match l with 
 | []               -> ""
 | (f1, f2)::[]      -> let s = (string_of_formula f1) in
                          (match s with 
							| ""  -> "   ensures " ^ (string_of_formula f2) ^ "\n"
							| _   -> "   requires " ^ s ^ "\n   ensures " ^ (string_of_formula f2) ^ "\n" )
 | (f1, f2)::t      -> let s = (string_of_formula f1) in
                         (match s with 
						   | ""  -> (string_of_form_list t)
                           | _   -> "   requires " ^ s ^ "\n   ensures " ^ (string_of_formula f2) ^ ";\n" ^ (string_of_form_list t) )  
;;

(*  | Assert of F.formula * F.formula option * loc
  | While of exp * exp * F.formula * F.formula * loc *)

(* function used to decide if parentrhesis are needed or not *)
let need_parenthesis2 = function 
  | Var _ | BoolLit _ | IntLit _ | FloatLit _ | Member _ -> false
  | _  -> true
;; 


(* pretty printing for expressions *)
let rec string_of_exp = function 
  | Unfold ({exp_unfold_var = (v, p)}) -> "unfold " ^ v
  | Java ({exp_java_code = code}) -> code
  | Label ((pid,_),e) -> string_of_control_path_id_opt pid(string_of_exp e)
  | Bind ({exp_bind_bound_var = v;
		   exp_bind_fields = vs;
		   exp_bind_path_id = pid;
		   exp_bind_body = e})      -> string_of_control_path_id_opt pid ("bind " ^ v ^ " to (" ^ (String.concat ", " vs) ^ ") in { " ^ (string_of_exp e) ^ " }")
  | Block ({exp_block_body = e;})    -> "{" ^ (string_of_exp e) ^ "}\n"
  | Break b -> string_of_control_path_id_opt b.exp_break_path_id ("break "^(string_of_label b.exp_break_jump_label))
  | Cast e -> "(" ^ (string_of_typ e.exp_cast_target_type) ^ ")" ^ (string_of_exp e.exp_cast_body)
  | Continue b -> string_of_control_path_id_opt b.exp_continue_path_id ("continue "^(string_of_label b.exp_continue_jump_label))
  | Empty l                         -> ""
  | Unary ({exp_unary_op = o;
			exp_unary_exp = e;
			exp_unary_pos = l})     -> (match o with 
                                       | OpPostInc | OpPostDec -> (if need_parenthesis2 e 
                                                                  then (parenthesis (string_of_exp e)) ^ (string_of_unary_op o)
                                                                  else (string_of_exp e) ^ (string_of_unary_op o))                                                                
                                       | _         -> (if need_parenthesis2 e 
                                                                  then (string_of_unary_op o) ^ (parenthesis (string_of_exp e))
                                                                  else (string_of_unary_op o) ^ (string_of_exp e)))
  | Binary ({exp_binary_op = o;
			 exp_binary_oper1 = e1;
			 exp_binary_oper2 = e2;
			 exp_binary_pos = l})   -> if need_parenthesis2 e1 
                                       then if need_parenthesis2 e2 then (parenthesis (string_of_exp e1)) ^ (string_of_binary_op o) ^ (parenthesis (string_of_exp e2))
                                                                    else (parenthesis (string_of_exp e1)) ^ (string_of_binary_op o) ^ (string_of_exp e2)
                                       else  (string_of_exp e1) ^ (string_of_binary_op o) ^ (string_of_exp e2)
  | CallNRecv ({exp_call_nrecv_method = id;
				exp_call_nrecv_path_id = pid;
				exp_call_nrecv_arguments = el})
                                    -> string_of_control_path_id_opt pid (id ^ "(" ^ (string_of_exp_list el ",") ^ ")")
  | CallRecv ({exp_call_recv_receiver = recv;
			   exp_call_recv_method = id;
			   exp_call_recv_path_id = pid;
			   exp_call_recv_arguments = el})
                                    -> string_of_control_path_id_opt pid ( (string_of_exp recv) ^ "." ^ id ^ "(" ^ (string_of_exp_list el ",") ^ ")")
  | New ({exp_new_class_name = id;
		  exp_new_arguments = el})  -> "new " ^ id ^ "(" ^ (string_of_exp_list el ",") ^ ")" 
  | Var ({exp_var_name = v})        -> v
  | Member ({exp_member_base = e;
			 exp_member_fields = idl})
                                    -> (string_of_exp e) ^ "." ^ (concatenate_string_list idl ".")
  | Assign ({exp_assign_op = op;
			 exp_assign_lhs = e1;
			 exp_assign_rhs = e2})  -> (string_of_exp e1) ^ (string_of_assign_op op) ^ (string_of_exp e2)
  | Cond ({exp_cond_condition = e1;
		   exp_cond_then_arm = e2;
		   exp_cond_path_id = pid;
		   exp_cond_else_arm = e3}) -> string_of_control_path_id_opt pid ("if " ^ (parenthesis (string_of_exp e1)) ^ " { \n  " ^ (string_of_exp e2) ^ ";\n}" ^ 
                                        (match e3 with 
										  | Empty ll -> ""
                                          | _        -> "\nelse { \n  " ^ (string_of_exp e3) ^ ";\n}"))
  | While ({exp_while_condition = e1;
			exp_while_body = e2;
			exp_while_jump_label = lb;
			exp_while_specs = li}) -> (string_of_label lb)^" while " ^ (parenthesis (string_of_exp e1)) ^ " \n" ^ "{\n"
                                       ^ (string_of_exp e2) ^ "\n}"          
  | Return ({exp_return_val = v; exp_return_path_id = pid})  -> string_of_control_path_id_opt pid ("return " ^ (match v with 
	  | None   -> ""
	  | Some e -> (string_of_exp e)) )
  | Seq ({exp_seq_exp1 = e1;
		  exp_seq_exp2 = e2})      -> (string_of_exp e1) ^ ";\n" ^ (string_of_exp e2) ^ ";"  
  | VarDecl ({exp_var_decl_type = t;
			  exp_var_decl_decls = l})
                                   -> (string_of_typ t) ^ " " ^ (string_of_assigning_list l) ^ ";";
  | ConstDecl ({exp_const_decl_type = t;
				exp_const_decl_decls = l}) 
                                   -> "const " ^ (string_of_typ t) ^ " " ^ (string_of_cassigning_list l)
  | BoolLit ({exp_bool_lit_val = b})
                                   -> string_of_bool b 
  | IntLit ({exp_int_lit_val = i}) -> string_of_int i
  | FloatLit ({exp_float_lit_val = f})
                                   -> string_of_float f
  | Null l                         -> "null"
  | Assert l                       -> snd(l.exp_assert_path_id)^" :assert "
  | Dprint l                       -> "dprint" 
  | Debug ({exp_debug_flag = f})   -> "debug " ^ (if f then "on" else "off")
  | This _ -> "this"
  | Raise ({exp_raise_type = tb;
			exp_raise_path_id = pid;
			exp_raise_val = b;}) -> string_of_control_path_id_opt pid 
				("raise "^(match b with | None -> let r = match tb with | Const_flow cf-> cf | Var_flow cf -> cf in r | Some bs-> (string_of_exp bs))^ "\n")
  | Try ({	exp_try_block = bl;
			exp_catch_clauses = cl;
			exp_finally_clause = fl;})
				-> "try {"^(string_of_exp bl)^"\n}"^(List.fold_left (fun a b -> a^"\n"^(string_of_catch b)) "" cl)^
									(List.fold_left (fun a b -> a^"\n"^(string_of_finally b)) "" fl)
									
and string_of_catch c  = 
		("catch (" ^ (match c.exp_catch_var with | Some x-> x | None -> "") ^ ": " ^ c.exp_catch_flow_type ^")\n"^(string_of_exp c.exp_catch_body))

and string_of_finally c = ("finally "^(string_of_exp c.exp_finally_body))

and 
   (* function to transform a list of expression in a string *)
   string_of_exp_list l c = match l with  
     | []                          -> ""
     | h::[]                       -> string_of_exp h
     | h::t 	                   -> (string_of_exp h) ^ c ^ " " ^ (string_of_exp_list t c)			    
and 
   (* function to transform in a string such a list : ((ident * exp option * loc) list *)
   string_of_assigning_list l = match l with 
     | []                          -> ""
     | (id, eo, l)::[]             -> id ^ (match eo with 
       | None    -> ""
       | Some e  -> " = " ^ (string_of_exp e))
     | (id, eo, l)::t 	           -> id ^ (match eo with 
       | None    -> ""
       | Some e  -> " = " ^ (string_of_exp e)) ^ ", " ^ (string_of_assigning_list t)
and 
   string_of_cassigning_list l = match l with 
     | []                          -> ""
     | (id, e, l)::[]              -> id ^ "=" ^ (string_of_exp e)
     | (id, e, l)::t 	           -> id ^ "=" ^ (string_of_exp e) ^ ", " ^ (string_of_cassigning_list t)

;;

(* pretty printing for one data declaration*)
let string_of_decl (d, pos) = match d with 
  | (t, i)             -> (string_of_typ t) ^ " " ^ i 
;;           

(* function to print a list of typed _ident *) 
let rec string_of_decl_list l c = match l with 
  | []               -> ""
  | h::[]            -> "  " ^ string_of_decl h 
  | h::t             -> "  " ^ (string_of_decl h) ^ ";" ^ c ^ (string_of_decl_list t c)
;;

(* pretty printing for a data declaration *)
let string_of_data_decl d = "data " ^ d.data_name ^ " {\n" ^ (string_of_decl_list d.data_fields "\n") ^ "\n}"
;;

(* pretty printing for a global variable declaration *)
let string_of_global_var_decl d = "global " ^ (string_of_exp (VarDecl d))
;;

(* pretty printig for view declaration *)
let string_of_view_decl v = v.view_name ^ "<" ^ (concatenate_string_list v.view_vars ",") ^ "> == " ^ 
                            (string_of_struc_formula v.view_formula) ^ " inv " ^ (string_of_pure_formula (fst v.view_invariant))                    (* incomplete *)
;;

let string_of_coerc_decl c = "coerc "^c.coercion_name^"\n\t head: "^(string_of_formula c.coercion_head)^"\n\t body:"^
							 (string_of_formula c.coercion_body)^"\n" 

(* pretty printing for one parameter *) 
let string_of_param par = match par.param_mod with 
 | NoMod          -> (string_of_typ par.param_type) ^ " " ^ par.param_name
 | RefMod         -> "ref " ^ (string_of_typ par.param_type) ^ " " ^ par.param_name
;;

(* pretty printing for a list of parameters *)
let rec string_of_param_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_param h) 
 | h::t      -> (string_of_param h) ^ ", " ^ (string_of_param_list t)
;;


(* pretty printing for procedure *)                                                                                              
let string_of_proc_decl p = 
  let body = match p.proc_body with 
	| None     -> ""
	| Some e   -> "{\n" ^ (string_of_exp e) ^ "\n}" in
 (* let locstr = (string_of_full_loc p.proc_loc)  
  in	*)
    (if p.proc_constructor then "" else (string_of_typ p.proc_return) ^ " ")
	^ p.proc_name ^ "(" ^ (string_of_param_list p.proc_args) ^ ")\n" 
	^ ( "static " ^ (string_of_struc_formula  p.proc_static_specs)
		^ "\ndynamic " ^ (string_of_struc_formula  p.proc_dynamic_specs) ^ "\n" ^ body)
;;

(* proc_pre_post_list : (F.formula * F.formula) list; *)

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

(* pretty printing for a list of coerc_decl *)
let rec string_of_coerc_decl_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_coerc_decl h) 
 | h::t      -> (string_of_coerc_decl h) ^ "\n" ^ (string_of_coerc_decl_list t)
;;

(* pretty printing for an element of type (ident * int option) *)
let string_of_const_decl c = match c with 
 | (id, io)  -> id ^ (match io with 
   | Some i -> " = " ^ (string_of_int i) 
   | None   -> "" )
;;

(* pretty printing for a list of elements of type (ident * int option) *)
let rec string_of_const_decl_list l = match l with 
 | []       -> ""
 | h::[]    -> string_of_const_decl h 
 | h::t     -> (string_of_const_decl h) ^ "," ^ (string_of_const_decl_list t)
;;   

(* pretty printing for constants declaration (enum) *)
let string_of_enum_decl ed = "enum " ^ ed.enum_name ^ "{" ^ (string_of_const_decl_list ed.enum_fields) ^ "}"
;;

(* pretty printing for a list of constant declarations *)
let rec string_of_enum_decl_list l = match l with 
 | []       -> ""
 | h::[]    -> string_of_enum_decl h 
 | h::t     -> (string_of_enum_decl h) ^ "\n" ^ (string_of_enum_decl_list t)
;;   

(* pretty printing for a list of global variable declarations *)
let rec string_of_global_var_decl_list l = 
  match l with
  | []    -> ""
  | h::[] -> string_of_global_var_decl h
  | h::t  -> (string_of_global_var_decl h) ^ "\n" ^ (string_of_global_var_decl_list t)
;;

let string_of_data cdef = 
  let meth_str = String.concat "\n" (List.map string_of_proc_decl cdef.data_methods) in
  let field_str = String.concat ";\n" 
	(List.map (fun f -> ((string_of_typ (fst (fst f))) ^ " " ^ (snd (fst f)))) cdef.data_fields) in
  let inv_str = String.concat ";\n" (List.map (fun i -> "inv " ^ (string_of_formula i)) cdef.data_invs) in
	"class " ^ cdef.data_name ^ " extends " ^ cdef.data_parent_name ^ " {\n"
	^ field_str ^ "\n" ^ inv_str ^ "\n" ^ meth_str ^ "\n}"

(* pretty printing for program *)
let string_of_program p = (* "\n" ^ (string_of_data_decl_list p.prog_data_decls) ^ "\n\n" ^  *)
  (String.concat "\n\n" (List.map string_of_data p.prog_data_decls)) ^ "\n\n" ^
  (string_of_global_var_decl_list p.prog_global_var_decls) ^ "\n" ^
  (string_of_enum_decl_list p.prog_enum_decls) ^"\n" ^
  (string_of_view_decl_list p.prog_view_decls) ^"\n" ^
  (string_of_coerc_decl_list p.prog_coercion_decls) ^ "\n\n" ^ 
  (string_of_proc_decl_list p.prog_proc_decls) ^ "\n"
;;




