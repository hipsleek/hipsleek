#include "xdebug.cppo"
open VarGen
(* 
   Pretty printing to Java for Cast.
*)

open Globals 
open Cast 

module CP = Cpure

module H = Hashtbl

type bind_map = (ident, (ident * ident)) H.t

type prim_map = (ident, (ident list -> string)) H.t

let binary_prim op args =
  String.concat op args

let is_null_prim args =
  (List.hd args) ^ " == null"

let is_not_null_prim args = 
  (List.hd args) ^ " != null"

let primitives_map = Hashtbl.create 19
let todo_unk = List.map (fun (op, func) -> Hashtbl.add primitives_map op func)
    [("add___", binary_prim " + ");
     ("minus___", binary_prim " - ");
     ("mult___", binary_prim " * ");
     ("div___", binary_prim " / ");
     ("mod___", binary_prim " % ");
     ("eq___", binary_prim " == ");
     ("neq___", binary_prim " != ");
     ("lt___", binary_prim " < ");
     ("lte___", binary_prim " <= ");
     ("gt___", binary_prim " > ");
     ("gte___", binary_prim " >= ");
     ("land___", binary_prim " && ");
     ("lor___", binary_prim " || ");
     ("is_null___", is_null_prim);
     ("is_not_null___", is_not_null_prim)]


(* (\* pretty printing for primitive types *\) *)
(* let string_of_prim_type = function  *)
(*   | Bool          -> "boolean " *)
(*   | Float         -> "float " *)
(*   | Int           -> "int " *)
(*   | Void          -> "void " *)
(*   | BagT t           -> "multiset("^(string_of_prim_type t)^")" *)
(*   | (TVar i) -> "TVar["^(string_of_int i)^"]" *)
(*   | List          -> "list" *)

(* (\* pretty printing for types *\) *)
(* let rec string_of_typ = function  *)
(*   | Prim t        -> string_of_prim_type t  *)
(*   | Named ot      -> ot ^ " " *)
(*   | Array (et, _)      -> string_of_typ et ^ "[]" (\* An Hoa *\) *)

(* functions to decide if an expression needs parenthesis *)
let need_parenthesis e = match e with 
  | BConst _ | Bind _ | FConst _ | IConst _ | Unit _ | Var _ -> false 
  | _                                                        -> true

module Ident = struct
  type t = ident
  let compare = compare
end

module IdentSet = Set.Make(Ident)

(*
  Handle block on the RHS of assignments, for example:
  node tmp;
  tmp = { .... ; new C(..); }

  push the assignment to "lhs" toward the end of the block.
  If lhs = "", do not make the assignment.

  null_vars : set of temporary variables introduced to hold null.

  Don't expect Java statements (if, ...) to appear in e0.

  Return values: 
*)
let rec remove_block_rhs prog (bmap : bind_map) (null_vars : IdentSet.t) (lhs : ident) (e0 : exp) java_code : IdentSet.t = match e0 with
  | Block ({exp_block_body = body}) -> 
    remove_block_rhs prog bmap null_vars lhs body java_code
  | Seq ({exp_seq_exp1 = e1;
          exp_seq_exp2 = e2}) ->
    (* do not make assignment to lhs in e1 *)
    let nvars1 = remove_block_rhs prog bmap null_vars "" e1 java_code in
    let () = add_semicolon java_code in
    let () = Buffer.add_string java_code ("\n") in
    let nvars2 = remove_block_rhs prog bmap nvars1 lhs e2 java_code in
    let () = add_semicolon java_code in
    nvars2
  | VarDecl  ({exp_var_decl_type = t;
               exp_var_decl_name = var}) ->
    if CP.name_of_type t = "" then
      (* the only reason why var has type "" is because 
         		   it was introduced to hold "null" *)
      IdentSet.add var null_vars
    else
      let () = Buffer.add_string java_code ((CP.name_of_type t) ^ " " ^ var ^ ";") in
      null_vars
  | Assign ({exp_assign_lhs = lhs;
             exp_assign_rhs = rhs}) ->
    if is_block rhs then
      let todo_unk = java_of_exp prog bmap null_vars e0 java_code in
      null_vars
    else if not(IdentSet.mem lhs null_vars) then begin
      let () = Buffer.add_string java_code (lhs ^ " = ") in
      let nvars = remove_block_rhs prog bmap null_vars "" rhs java_code in
      let () = Buffer.add_string java_code ";" in
      nvars
    end else
      (* in case lhs is a null var, just ignored the assignment *)
      null_vars
  | rest_e -> 
    if lhs = "" then
      let todo_unk = java_of_exp prog bmap null_vars rest_e java_code in
      null_vars
    else begin
      (* make the pushed in assignment to lhs *)
      Buffer.add_string java_code (lhs ^ " = ");
      let nvars = remove_block_rhs prog bmap null_vars "" e0 java_code in
      nvars
    end

and subst_name (bmap : bind_map) (null_vars : IdentSet.t) (name : ident) : ident =
  if IdentSet.mem name null_vars then "null"
  else
    try
      let (v, f) = H.find bmap name in
      (v ^ "." ^ f)
    with
    | Not_found -> name

and subst_names (bmap : bind_map) (null_vars : IdentSet.t) (names : ident list) : string =
  let tmp1 = List.map (fun n -> subst_name bmap null_vars n) names in
  let tmp2 = String.concat ", " tmp1 in
  tmp2

and add_semicolon java_code : unit = 
  let len = Buffer.length java_code in
  if len > 0 then
    let last_char = Buffer.nth java_code (len - 1) in
    if not (last_char = ';' || last_char = '}' || last_char = '\n') then
      Buffer.add_char java_code ';'

(* 
   Pretty printing for expressions.
   e0 : exp
   bmap : mapping from bind local vars to field accesses
   java_code : code buffer
*)
and java_of_exp prog (bmap : bind_map) (null_vars : IdentSet.t) (e0 : exp) java_code : IdentSet.t  = match e0 with
  | CheckRef ({exp_check_ref_var = v;
               exp_check_ref_pos = pos}) ->
    let pstr = (Debug.string_of_pos pos) ^ v ^ " is not accessible." in
    Buffer.add_string java_code ("\n");
    (* Buffer.add_string java_code ("if (" ^ v ^ " == null || " ^ v ^ ".color != RTC.curColor) {\n"); *)
    Buffer.add_string java_code ("if (" ^ v ^ " == null || " ^ v ^ ".color != RTC.curColor) {\n");
    Buffer.add_string java_code ("    System.err.println(\"" ^ pstr ^ "\");\n");
    Buffer.add_string java_code ("    System.exit(-1);\n");
    Buffer.add_string java_code ("}\n");
    null_vars
  | Java ({exp_java_code = code}) ->
    Buffer.add_char java_code '\n';
    Buffer.add_string java_code code;
    Buffer.add_char java_code '\n';
    null_vars
  | Assert ({exp_assert_asserted_formula = f1o; 
             exp_assert_assumed_formula = f2o}) -> null_vars
  | Assign ({exp_assign_lhs = lhs; 
             exp_assign_rhs = rhs}) ->
    if not(IdentSet.mem lhs null_vars) then begin
      let lhs = (* id can never be literal "null", so only need to look up bmap *)
        try
          let (v, f) = H.find bmap lhs in
          (v ^ "." ^ f)
        with
        | Not_found -> lhs
      in
      remove_block_rhs prog bmap null_vars lhs rhs java_code
   (*
			  Buffer.add_string java_code (lhs ^ " = ");
			  string_of_exp prog rhs bmap java_code;
			  Buffer.add_string java_code ";"
			*)
    end else
      null_vars
  | BConst ({exp_bconst_val = b}) -> 
    Buffer.add_string java_code (string_of_bool b);
    null_vars
  | Bind ({exp_bind_bound_var = (t, bvar); 
           exp_bind_fields = idl;
           exp_bind_body = e}) -> 
    let ddef = look_up_data_def no_pos prog.prog_data_decls (string_of_typ t) in
    let field_names = List.map snd idl in
    (* add local bind map *)
    let todo_unk = List.map2 
        (fun id -> fun fld -> H.add bmap id (bvar, Cast.get_field_name fld))
        field_names ddef.data_fields 
    in
    (* 
		   pretty print the body. Any null vars introduced by the bind
		   body is local. Therefore there's no need to propagate them.
		*)
    let todo_unk = java_of_exp prog bmap null_vars e java_code in
    (* clear local bind map *)
    ignore (List.map (fun id -> H.remove bmap id) field_names);
    null_vars
  | Var ({exp_var_name = vname}) -> 
    Buffer.add_string java_code (subst_name bmap null_vars vname);
    null_vars
  | SCall ({exp_scall_method_name = mn0;
            exp_scall_arguments = args}) -> begin
      let mn = unmingle_name mn0 in
      try
        let func = H.find primitives_map mn in
        let str = func args in
        Buffer.add_string java_code str;
        null_vars
      with
      | Not_found ->
        Buffer.add_string java_code mn;
        Buffer.add_string java_code ("(" ^ (subst_names bmap null_vars args) ^ ")");
        null_vars
    end
  | Cond ({exp_cond_condition = cond;
           exp_cond_then_arm = then_arm;
           exp_cond_else_arm = else_arm}) ->
    Buffer.add_string java_code ("if (" ^ cond ^ ") {\n");
    ignore (java_of_exp prog bmap null_vars then_arm java_code);
    add_semicolon java_code;
    Buffer.add_string java_code ("\n}\nelse {\n");
    ignore (java_of_exp prog bmap null_vars else_arm java_code);
    add_semicolon java_code;
    Buffer.add_string java_code ("\n}\n");
    null_vars
  | New ({exp_new_class_name = c;
          exp_new_arguments = tids}) ->
    let ids = List.map snd tids in
    let arg_str = subst_names bmap null_vars ids in
    Buffer.add_string java_code ("new " ^ c ^ "(" ^ arg_str ^ ")");
    null_vars
  | IConst ({exp_iconst_val = ic}) ->
    Buffer.add_string java_code (string_of_int ic);
    null_vars
  | Block ({exp_block_body = e}) -> 
    Buffer.add_string java_code "{\n";
    (* 
		 null vars introduced in e are local. No need to propagate. 
	  *)
    ignore (java_of_exp prog bmap null_vars e java_code);
    add_semicolon java_code;
    Buffer.add_string java_code "\n}";
    null_vars
  | ICall ({exp_icall_receiver = r;
            exp_icall_method_name = id;
            exp_icall_arguments = idl}) -> 
    let sr = subst_name bmap null_vars r in
    let arg_str = subst_names bmap null_vars idl in
    Buffer.add_string java_code (sr ^ "." ^ id ^ "(" ^ arg_str ^ ")");
    null_vars
  | Null l -> 
    Buffer.add_string java_code "null";
    null_vars
  | Sharp ({exp_sharp_val = eo}) -> begin
      Buffer.add_string java_code "return";
      match eo with 
      |Sharp_var e -> 
        Buffer.add_string java_code (" "^(snd e));
        (*ignore (java_of_exp prog bmap null_vars e java_code);*)
        Buffer.add_string java_code (";\n");
        null_vars
      | _ -> null_vars
    end
  | Seq ({exp_seq_exp1 = e1;
          exp_seq_exp2 = e2}) -> 
    let null_vars1 = java_of_exp prog bmap null_vars e1 java_code in
    let () = add_semicolon java_code in
    let () = Buffer.add_string java_code "\n" in
    let null_vars2 = java_of_exp prog bmap null_vars1 e2 java_code in
    let () = add_semicolon java_code in
    null_vars2
  | This _ -> 
    Buffer.add_string java_code "this";
    null_vars
  | VarDecl ({exp_var_decl_type = t;
              exp_var_decl_name = var}) -> 
    if string_of_typ t = "" then
      (* the only reason why var has type "" is because 
         		   it was introduced to hold "null" *)
      IdentSet.add var null_vars
    else
      let () = Buffer.add_string java_code ((string_of_typ t) ^ " " ^ var ^ ";") in
      null_vars
  | Unit l -> null_vars
  | While ({exp_while_condition = id;
            exp_while_body = e})  -> 
    Buffer.add_string java_code ("while (" ^ (subst_name bmap null_vars id) ^ ") {\n");
    let null_vars1 = java_of_exp prog bmap null_vars e java_code in
    Buffer.add_string java_code ("\n}");
    null_vars1
  | _ ->
    failwith ("java_of_exp: " ^ (Cprinter.string_of_exp e0) ^ " is not supported.")

(*
and string_of_param_list (params : CP.spec_var list) : string =
  let tmp1 = List.map
	(fun (CP.SpecVar (t, v, _)) -> (string_of_typ t) ^ " " ^ v)
	params in
  let tmp2 = String.concat ", " tmp1 in
	tmp2
*)

and params_of_typed_ident_list delim (params : typed_ident list) : string =
  let tmp1 = List.map
      (fun (t, v) -> (string_of_typ t) ^ " " ^ v)
      params in
  let tmp2 = String.concat delim tmp1 in
  tmp2

and fields_of_typed_ident_list (fields : typed_ident list) : string =
  let tmp1 = List.map
      (fun (t, v) -> (string_of_typ t) ^ " " ^ v ^ ";")
      fields in
  let tmp2 = String.concat "\n" tmp1 in
  tmp2

(* pretty printing for a procedure *)
and java_of_proc_decl prog p java_code = 
  if p.proc_name = "main" then
    Buffer.add_string java_code ("\npublic static void main(String args[])")
  else begin
    Buffer.add_string java_code ("\n\nstatic ");
    Buffer.add_string java_code (string_of_typ p.proc_return);
    Buffer.add_char java_code ' ';
    Buffer.add_string java_code p.proc_name;
    Buffer.add_char java_code '(';
    Buffer.add_string java_code (params_of_typed_ident_list ", " p.proc_args);
    Buffer.add_char java_code ')';
  end;
  match p.proc_body with 
  | Some e -> 
    Buffer.add_string java_code "\n";
    ignore (java_of_exp prog (H.create 103) (IdentSet.empty) e java_code)
  | None   -> Buffer.add_string java_code (";\n")

and java_of_data_decl prog ddef java_code = 
  Buffer.add_string java_code ("\nclass ");
  Buffer.add_string java_code ddef.data_name;
  Buffer.add_string java_code ("{\n");
  Buffer.add_string java_code ("long color;\n");
  Buffer.add_string java_code (fields_of_typed_ident_list (List.map fst ddef.data_fields));
  Buffer.add_string java_code "\n\n";
  build_constructor ddef java_code;
  Buffer.add_string java_code "\n\n";
  ignore (List.map (fun p -> java_of_proc_decl prog p java_code) ddef.data_methods);
  Buffer.add_string java_code "\n}\n"

and build_constructor (ddef : data_decl) java_code : unit =
  let n = List.length ddef.data_fields in
  let typs = List.map Cast.get_field_typ ddef.data_fields in
  let fnames = List.map Cast.get_field_name ddef.data_fields in
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
  Buffer.add_string java_code ("\ncolor = RTC.curColor;\n");
  Buffer.add_string java_code "\n}\n";
  if not (Gen.is_empty ddef.data_fields) then begin
    (* also add empty constructor *)
    Buffer.add_char java_code '\n';
    Buffer.add_string java_code ddef.data_name;
    Buffer.add_string java_code "() {}\n"
  end

and string_of_proc_decl prog p =
  let java_code = Buffer.create 1024 in
  java_of_proc_decl prog p java_code;
  Buffer.contents java_code

and convert_to_java prog main_class =
  Error.report_error {Error.error_loc = no_pos; Error.error_text = "malfunction conversion to java is no longer supported"}
(* let java_code = Buffer.create 10240 in
   	ignore (List.map (fun ddef -> java_of_data_decl prog ddef java_code) prog.prog_data_decls);
   	convert_methods prog prog.prog_proc_decls main_class java_code;
   	Buffer.contents java_code*)

and convert_methods prog (pdefs : proc_decl list) main_class java_code =
  Buffer.add_string java_code ("public class " ^ main_class ^ " {\n");
  ignore (List.map (fun pd -> convert_method prog pd java_code) pdefs);
  Buffer.add_char java_code '}'

and convert_method prog (pdef : proc_decl) java_code = 
  if pdef.proc_name = "main" then begin
    if Gen.is_empty pdef.proc_args && pdef.proc_return = Void then begin
      Buffer.add_string java_code "public static void main(String[] args) {\n";
      (match pdef.proc_body with
       | Some e -> 
         ignore (java_of_exp prog (H.create 103) (IdentSet.empty) e java_code)
       | None -> ());
      Buffer.add_string java_code "\n}\n";
    end else
      failwith ("main's argument list must be empty and return type must be void\n");
  end else begin
    Buffer.add_string java_code "\nstatic ";
    java_of_proc_decl prog pdef java_code;
    Buffer.add_string java_code "\n\n"
  end
