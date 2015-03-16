#include "xdebug.cppo"
open VarGen
(*
  Support to convert our code into Java code.
  
  Java fragments can be embedded into our code verbatimly using the
  java keyword. Java code fragments can refer to names in our source
  code. To ensures that the generated Java code is compilable, we need
  to ensure that names do not change when they are converted to Java.
  

  For now, java construct can only be used inside method bodies. But it
  should be supported outside of method bodies as well, so that optional
  "imports" or class declarations can be made.

  
*)

open Globals
open Iast

module CP = Cpure

let java_code = Buffer.create 1000

let rec convert_to_java (prog : prog_decl) (main_class : string) : string = 
  Error.report_error{Error.error_loc = no_pos; Error.error_text = "feature discontinued"}
  (*ignore (List.map convert_data prog.prog_data_decls);
  convert_methods main_class prog.prog_proc_decls;
  Buffer.contents java_code*)

and convert_data (ddef : data_decl) : unit = 
  if (not (ddef.data_name = "Object")) && (not (ddef.data_name = "String")) then begin
	(* This is a quick and dirty fix to make things work. *)
	(* Buffer.add_string java_code ("import java.util.*;\n\n"); *)
	Buffer.add_string java_code ("class " ^ ddef.data_name ^ " {\n");
	ignore (List.map convert_field ddef.data_fields);
	(* Another quick and dirty fix to add the "intersect" method. *)
	(*
	  Buffer.add_string java_code ("\n");
	  Buffer.add_string java_code ("boolean intersect(Set s1, Set s2) {\n");
	  Buffer.add_string java_code ("  Iterator it = s1.iterator(); \n");
	  Buffer.add_string java_code ("  while (it.hasNext()) { \n");
	  Buffer.add_string java_code ("    if (s2.contains(it.next())) return true;\n");
	  Buffer.add_string java_code ("  }\n");
	  Buffer.add_string java_code ("  return false;\n");
	  Buffer.add_string java_code ("}\n");
	*)
	ignore (List.map 
			  (fun pdef -> Buffer.add_string java_code ("\n\n" ^ (java_of_proc_decl pdef)))
			  ddef.data_methods);
	build_constructor ddef;
	Buffer.add_string java_code "\n}\n\n"
  end

and java_of_data (ddef : data_decl) (pbvars : CP.spec_var list) : string =
  Buffer.clear java_code;
  convert_data ddef;
  java_of_partially_bound_params pbvars;
  Buffer.contents java_code

and java_of_data2 (ddef : data_decl) : string =
  Buffer.clear java_code;
  convert_data ddef;
  Buffer.contents java_code

and java_of_partially_bound_params2 pbvars = 
  Buffer.clear java_code;
  java_of_partially_bound_params pbvars;
  Buffer.contents java_code

and java_of_data_defs (ddefs : data_decl list) : string =
  Buffer.clear java_code;
  ignore (List.map convert_data ddefs);
  Buffer.contents java_code

and java_of_partially_bound_params (pbvars : CP.spec_var list) : unit = match pbvars with
  | (CP.SpecVar (t, v, p)) :: rest -> begin
	  match t with
		| Named c ->
			Buffer.add_string java_code ("\n\n");
			(* class header and fields *)
			Buffer.add_string java_code ("final class " ^ c  ^ "Aug {\n");
			Buffer.add_string java_code ("\tboolean bound;\n");
			Buffer.add_string java_code ("\t" ^ c ^ " val;\n");
			(* constructor *)
			Buffer.add_string java_code ("\n\t" ^ c ^ "Aug(" ^ c ^ " p) {\n");
			Buffer.add_string java_code ("\t\tval = p;\n");
			Buffer.add_string java_code ("\t\tbound = true;\n");
			Buffer.add_string java_code ("\t}\n");
			(* another constructor *)
			Buffer.add_string java_code ("\n\t" ^ c ^ "Aug(" ^ c ^ "Aug p) {\n");
			Buffer.add_string java_code ("
\t\tval = p.val;
\t\tbound = p.bound;
\t}\n");
			(* yet another constructor: for the unbound case *)
			Buffer.add_string java_code ("\n\t" ^ c ^ "Aug() {\n");
			Buffer.add_string java_code ("
val = null;
bound = false;
}\n\n");
			(* EQ method *)
			Buffer.add_string java_code ("\tfinal boolean EQ(" ^ c ^ " p) {\n");
			Buffer.add_string java_code ("\t\tif (bound) return val == p;\n");
			Buffer.add_string java_code ("\t\tval = p;\n");
			Buffer.add_string java_code ("\t\tbound = true;\n");
			Buffer.add_string java_code ("\t\treturn true;\n");
			Buffer.add_string java_code ("\t}\n");
			(* overloaded EQ method *)
			Buffer.add_string java_code ("\tfinal boolean EQ(" ^ c ^ "Aug p) {\n");
			Buffer.add_string java_code (" 
if (bound && p.bound) return val == p.val; 
if (bound && !p.bound) { 
  p.bound = true;
  p.val = val;
  return true; 
} 
if (!bound && p.bound) {
  bound = true;
  val = p.val;
  return true; 
} 
bound = true;
p.bound = true; 
");
			Buffer.add_string java_code ("val = new " ^ c ^ "();\n");
			Buffer.add_string java_code ("p.val = val;\n");
			Buffer.add_string java_code ("return true;\n");
			Buffer.add_string java_code ("}\n");
			(* NEQ method *)
			Buffer.add_string java_code ("\tfinal boolean NEQ(" ^ c ^ " p) {\n");
			Buffer.add_string java_code ("\t\tif (bound) return val != p;\n");
			Buffer.add_string java_code ("\t\tval = new dnode();\n");
			Buffer.add_string java_code ("\t\tbound = true;\n");
			Buffer.add_string java_code ("\t\treturn true;\n");
			Buffer.add_string java_code ("\t}\n");
			(* overloaded NEQ method *)
			Buffer.add_string java_code ("\tfinal boolean NEQ(" ^ c ^ "Aug p) {\n");
			Buffer.add_string java_code (" 
if (bound && p.bound) return val != p.val; 
if (bound && !p.bound) { 
  p.bound = true;
  p.val = new " ^ c ^ "();
  return true; 
} 
if (!bound && p.bound) {
  bound = true;
  val = new " ^ c ^ "();
  return true; 
} 
bound = true;
p.bound = true; 
val = new " ^ c ^ "();
p.val = new " ^ c ^ "();
return true; 
");
			Buffer.add_string java_code ("\t}\n");
			(* end of class *)
			Buffer.add_string java_code ("}\n");
			java_of_partially_bound_params rest
		| _ -> 
			java_of_partially_bound_params rest
	end
  | [] -> ()

and build_constructor (ddef : data_decl) : unit =
  let n = List.length ddef.data_fields in
  let typs = List.map get_field_typ ddef.data_fields in
  let fnames = List.map get_field_name ddef.data_fields in
  let pnames = fresh_names n in
  let formals = List.map2 (fun t -> fun name -> 
							 (string_of_typ t) ^ " " ^ name) typs pnames in
  let assignments = List.map2 (fun f -> fun p -> (f ^ " = " ^ p ^ ";")) fnames pnames in
	Buffer.add_string java_code "\n\n";
	Buffer.add_string java_code ddef.data_name;
	Buffer.add_char java_code '(';
	Buffer.add_string java_code (String.concat ", " formals);
	Buffer.add_string java_code ") {\n";
	Buffer.add_string java_code (String.concat "\n" assignments);
	Buffer.add_string java_code "\n}\n";
	if not (Gen.is_empty ddef.data_fields) then begin
	  (* also add empty constructor *)
	  Buffer.add_char java_code '\n';
	  Buffer.add_string java_code ddef.data_name;
	  Buffer.add_string java_code "() {}\n"
	end
	


and convert_field ((t, v), l, _,_) =
  Buffer.add_string java_code (string_of_typ t);
  Buffer.add_string java_code (" " ^ v ^ ";\n")

(*
  make a main class, and add all methods as static methods
  of this class
*)
and convert_methods main_class (pdefs : proc_decl list) =
	Buffer.add_string java_code ("public class " ^ main_class ^ " {\n");
  ignore (List.map convert_method pdefs);
  Buffer.add_char java_code '}'

(*
  add a single method. If the method's name is main,
  make it the main method of the Main class.
*)

and convert_method (pdef : proc_decl) = 
  if (pdef.proc_name = "main") then begin
	if Gen.is_empty pdef.proc_args && pdef.proc_return = void_type then begin
	  Buffer.add_string java_code "public static void main(String[] args) {\n";
	  (match pdef.proc_body with
		| Some e -> Buffer.add_string java_code (java_of_exp e)
		| None -> ());
	  Buffer.add_string java_code "\n}\n";
	end else
	  failwith ("main's argument list must be empty and return type must be void\n");
  end else begin
	Buffer.add_string java_code "static ";
	Buffer.add_string java_code (java_of_proc_decl pdef);
	Buffer.add_string java_code "\n\n"
  end

and java_of_proc_decl p =
  let body = match p.proc_body with 
	| None     -> ""
	| Some e   -> "{\n" ^ (java_of_exp e) ^ "\n}" 
  in	
    (if p.proc_constructor then "" else (string_of_typ p.proc_return) ^ " ")
	^ p.proc_name 
	^ "(" 
	^ (String.concat ", " (List.map 
							 (fun pr -> (string_of_typ pr.param_type) 
								^ " " ^ pr.param_name) p.proc_args)) 
	^ ") "^
	"throws "^(String.concat "," p.proc_exceptions)
	^ "\n" ^ body

and java_of_exp = function
	| ArrayAt ({exp_arrayat_array_base = a;
	     exp_arrayat_index = idx;}) -> (java_of_exp a) ^ (String.concat "" (List.map (fun e -> "[" ^ (java_of_exp e) ^ "]") idx))
  | Label (_,b) -> java_of_exp b
  | Unfold _ -> ""
  | Java ({exp_java_code = code}) -> code
  | Barrier b -> "barrier "^b.exp_barrier_recv
  | Bind ({exp_bind_bound_var = v;
		   exp_bind_fields = vs;
		   exp_bind_body = e})      -> failwith "bind is not supported yet"
  | Block ({exp_block_body = e})    -> 
	  let str1 = java_of_exp e in
	  let str2 = add_semicolon str1 in
		"{ " ^ str2 ^ " }"
  | Break _ -> "break;"
  | Cast e -> 
	  "(" ^ (string_of_typ e.exp_cast_target_type) ^ ")" 
	  ^ (java_of_exp e.exp_cast_body)
  | Continue _ -> "continue;"
  | Empty l -> ""
  | Unary ({exp_unary_op = o;
			exp_unary_exp = e;
			exp_unary_pos = l}) -> begin
	  match o with 
        | OpPostInc | OpPostDec -> 
			if Iprinter.need_parenthesis2 e then 
			  (Iprinter.parenthesis (java_of_exp e)) ^ (Iprinter.string_of_unary_op o)
            else 
			  (java_of_exp e) ^ (Iprinter.string_of_unary_op o)
         | _ -> 
			 if Iprinter.need_parenthesis2 e then 
			   (Iprinter.string_of_unary_op o) ^ (Iprinter.parenthesis (java_of_exp e))
             else 
			   (Iprinter.string_of_unary_op o) ^ (java_of_exp e)
	end
  | Binary ({exp_binary_op = o;
			 exp_binary_oper1 = e1;
			 exp_binary_oper2 = e2;
			 exp_binary_pos = l}) -> 
	  if Iprinter.need_parenthesis2 e1 then 
		if Iprinter.need_parenthesis2 e2 then 
		  (Iprinter.parenthesis (java_of_exp e1)) ^ (Iprinter.string_of_binary_op o) 
		  ^ (Iprinter.parenthesis (java_of_exp e2))
        else 
		  (Iprinter.parenthesis (java_of_exp e1)) ^ (Iprinter.string_of_binary_op o) 
		  ^ (java_of_exp e2)
      else  
		(java_of_exp e1) ^ (Iprinter.string_of_binary_op o) ^ (java_of_exp e2)
  | CallNRecv ({exp_call_nrecv_method = id;
				exp_call_nrecv_arguments = el}) -> 
	  id ^ "(" ^ (String.concat "," (List.map java_of_exp el)) ^ ")"
  | CallRecv ({exp_call_recv_receiver = recv;
			   exp_call_recv_method = id;
			   exp_call_recv_arguments = el}) -> 
	  (java_of_exp recv) ^ "." ^ id ^ "(" ^ (String.concat ", " (List.map java_of_exp el)) ^ ")"
	| ArrayAlloc ({exp_aalloc_etype_name = elm_type;
		  exp_aalloc_dimensions = dims}) -> 
	  "new " ^ elm_type ^ "[" ^ (String.concat ", " (List.map java_of_exp dims)) ^ "]"
  | New ({exp_new_class_name = id;
		  exp_new_arguments = el}) -> 
	  "new " ^ id ^ "(" ^ (String.concat ", " (List.map java_of_exp el)) ^ ")" 
  | Var ({exp_var_name = v}) -> v
  | Member ({exp_member_base = e;
			 exp_member_fields = idl}) -> 
	  (java_of_exp e) ^ "." ^ (String.concat "." idl)
  | Assign ({exp_assign_op = op;
			 exp_assign_lhs = e1;
			 exp_assign_rhs = e2}) -> 
	  (java_of_exp e1) ^ (Iprinter.string_of_assign_op op) ^ (java_of_exp e2) ^ ";"
  | Cond ({exp_cond_condition = e1;
		   exp_cond_then_arm = e2;
		   exp_cond_else_arm = e3}) -> 
	  "if " ^ (Iprinter.parenthesis (java_of_exp e1)) 
	  ^ " {\n" ^ (add_semicolon (java_of_exp e2)) ^ "\n}" ^ 
        (match e3 with 
		   | Empty ll -> ""
           | _        -> "\nelse { \n  " ^ (add_semicolon (java_of_exp e3)) ^ "\n}")
  | While ({exp_while_condition = e1;
			exp_while_body = e2;
			exp_while_specs = li}) -> 
	  "while " ^ (Iprinter.parenthesis (java_of_exp e1)) ^ " \n" ^ "{\n"
      ^ (java_of_exp e2) ^ "\n}"          
  | Return ({exp_return_val = v}) -> 
	  "return " ^ (match v with 
					 | None   -> ""
					 | Some e -> (java_of_exp e) ^ ";")
  | Seq ({exp_seq_exp1 = e1;
		  exp_seq_exp2 = e2}) -> 
	  let e1str = java_of_exp e1 in
	  let e2str = java_of_exp e2 in
		if e2str = "" then e1str
		else (add_semicolon e1str) ^ "\n" ^ (add_semicolon e2str) ^ "\n"
  | VarDecl ({exp_var_decl_type = t;
			  exp_var_decl_decls = l}) -> 
	  (string_of_typ t) ^ " " ^ (Iprinter.string_of_assigning_list l) ^ ";";
  | ConstDecl ({exp_const_decl_type = t;
				exp_const_decl_decls = l}) -> 
	  "const " ^ (string_of_typ t) ^ " " ^ (Iprinter.string_of_cassigning_list l) ^ ";"
  | BoolLit ({exp_bool_lit_val = b})
                                   -> string_of_bool b 
  | IntLit ({exp_int_lit_val = i}) -> string_of_int i
  | FloatLit ({exp_float_lit_val = f})
                                   -> string_of_float f
  | Null l                         -> "null"
  | Assert _                       -> ""
  | Dprint l                       -> ""
  | Time _                         -> ""
  | Debug ({exp_debug_flag = f})   -> ""
  | This _ -> "this"
  | Raise b -> (match b.exp_raise_val with 
				| Some b1-> "throw "^(java_of_exp b1)
				| None -> Error.report_error{Error.error_loc = b.exp_raise_pos; Error.error_text = "can not translate properly into java code (raise with no expression)"})
  | Try b -> "translator is in need of reviews"
  | Catch b-> "translator is in need of reviews"
  | Finally b-> "translator is in need of reviews"
  | Par _ -> "translator is in need of reviews"
				
and add_semicolon (str : string) : string =
  let l = String.length str in
	if l = 0 then str
	else
	  let c = String.get str (l - 1) in
		if c = ';' || c = '}' || c = '\n' || c = '\r' then str
		else str ^ ";"
