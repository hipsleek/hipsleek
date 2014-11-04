(* Joust: a Java lexer, parser, and pretty-printer written in OCaml
   Copyright (C) 2001  Eric C. Cooper <ecc@cmu.edu>
   Released under the GNU General Public License *)

open Format
open Syntax
module Env = Set.Make(String)

let env = ref Env.empty;;
(* Print a generic separated list.
   [pf] is a formatter for elements of the list.
   [sep] is a function to print the separator between elements. *)

let more_code = "
global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;";;


let print_more_code f =
  pp_print_string f more_code


let in_class = ref "";;
let in_static = ref false;;

let is_uppercase c =
  if Char.code c<91 && Char.code c>64 then true else false


let rec print_sep_list pf sep f list=
  match list with
  | [] -> ()
  | [x] -> pf f x
  | x :: rest -> fprintf f "%a%t%a" pf x sep (print_sep_list pf sep) rest

(* Print a generic option value.
   [pf] is a formatter for the value, if present.
   Prints a space before the value when present. *)

let print_option pf f opt =
  match opt with
  | Some x -> fprintf f " %a" pf x
  | None -> ()

(* Print a list of items with no additional separators.
   [pf] is a formatter for elements of the list. *)

let print_list pf =
  print_sep_list pf (fun f -> ())

(* Print a comma-separated list.
   [pf] is a formatter for elements of the list. *)

let print_comma_list pf =
  print_sep_list pf (fun f -> fprintf f ", ")

(* Print a space-separated list.
   [pf] is a formatter for elements of the list. *)

let print_space_list pf =
  print_sep_list pf (fun f -> fprintf f " ")

(* Print a newline-separated list.
   [pf] is a formatter for elements of the list. *)

let print_newline_list pf =
  print_sep_list pf (fun f -> fprintf f "@\n")

let print_ident f id =
  let name = if id_string id = "res" then "__res" else id_string id in
   pp_print_string f (name)

let print_ident_enhanced f id =
  let name = if id_string id = "res" then "__res" else id_string id in
  if Env.mem name !env then pp_print_string f (name) else pp_print_string f ("this."^name)






let rec split_decls d typeName =
  let get_type_information s =
    match s with
    | Method _ -> "Method"
    | Field _ -> "Field"
    | _ -> "No such type"
  in
  match d with
  | m::rest -> if (get_type_information m = typeName) then m::(split_decls rest typeName) else (split_decls rest typeName)
  | [] -> []

let type_table = Hashtbl.create 100;;(*class name -> field list*)
let local_type_table = Hashtbl.create 100;; (* var name -> type, scope of function*)
(* let class_type_table = Hashtbl.create 100;; *) (*var name -> type, scope of class*)


let rec construct_type_table d_list =
    match d_list with
    | (Class cl)::rest -> 
      let field_list = split_decls cl.cl_body "Field" in
      let _ = Hashtbl.add type_table cl.cl_name.id field_list in
      construct_type_table rest
    | [] ->()
    | _ -> failwith "construct_type_table: Unexpected"

let fields_of_class t =
  Hashtbl.find type_table t

let rec type_of_name (fl:decls) (n:ident) =
  (* print_endline("type_of_name "^n.id); *)
  match fl with
  | (Field head)::rest -> if (is_uppercase n.id.[0]) then  named_type n.id
                          else
                            if  head.f_var.v_name.id = n.id then head.f_var.v_type 
                            else type_of_name rest n
  | _ -> failwith "type_of_name: Not Found"

let str_of_type t = 
  match t with
  | TypeName tn -> (List.hd (fst tn)).id
  | _ -> "str_of_type: Unexpected" 

let rec type_of_name_chain_helper (n_chain:name) start_type=

  match n_chain with
  | head::rest -> 
              let fl = (fields_of_class (str_of_type start_type)) in 
                type_of_name_chain_helper rest (type_of_name fl head)
  | [] -> start_type
    



let type_of_name_chain (n_chain:ident list)  =
  (* let _ = print_endline ("here") in *)
  try
    if List.length n_chain = 0 then (* let _ = print_endline("length == 0") in *) named_type !in_class
    else
      (* let _ = print_endline ("type_of_name_chain"^(List.hd n_chain).id) in *)
      let start_type = Hashtbl.find local_type_table ((List.hd n_chain).id) in
      type_of_name_chain_helper (List.tl n_chain) start_type

  with
  | Not_found -> if is_uppercase (List.hd n_chain).id.[0] then named_type (List.hd n_chain).id 
                 else  named_type !in_class
  | hd -> failwith "type_of_name_chain: hd"

let rec print_name_simple name = 
  match name with
  | head::rest -> print_name_simple rest
  | [] -> ()

let adjust_call tn name =
  (* print_name_simple name; *)
  (* let _ = print_endline  ("length name:"^string_of_int (List.length name)) in
  let _ = print_endline  ("hd name:"^(List.hd name).id) in *)

  try
    if List.length name = 1 then [{ id=(!in_class); pos = -1}]@[List.hd (List.rev name)]
    else
      (* let pre_typ = type_of_name_chain (List.rev (List.tl (List.rev name))) in *)
      [{ id=(str_of_type tn); pos = -1}]@[List.hd (List.rev name)]
  with
  | hd -> failwith "adjust_call: hd"


let mk_paralist_to_str name = 
  let rec helper name=
    match name with
    | head::rest -> ("."^head.id^(helper rest))
    | [] -> ""
  in
  (List.hd name).id^helper (List.rev (List.tl (List.rev (List.tl name))))



let get_call_body call_name =
  match call_name with
  |Name (nl,m) ->
    if List.length nl = 1 && (not !in_static) then Some "_this"
    else
      if is_uppercase ((List.hd nl).id.[0]) then None
      else Some (mk_paralist_to_str nl)
  | _ -> failwith "get_call_body: Unexpected" 







let adjust_parameter call_name para_name =
  if !in_static then para_name (* Since in a static method, only static method can be called*)
  else 
   let call_body = get_call_body call_name in
    begin
      match call_body with
      | Some s -> (Name ([{ id = s;pos = -1}],None))::para_name
      | None -> para_name
    end


let print_name f =
  print_sep_list print_ident (fun f -> fprintf f ".") f


let adjust_var higher_name =
  match (fst higher_name) with
  | head::rest -> 
                  if Env.mem head.id !env then (head::rest)
                  else
                    if is_uppercase head.id.[0] then
                      begin
                        match rest with
                        | h1::r1 -> {id = head.id^"_"^h1.id;pos = head.pos}::r1
                        | [] -> failwith "higher_name: Unexpected"
                      end
                    else
                      if !in_static then {id = !in_class^"_"^head.id;pos = head.pos}::rest
                      else
                        {id = "_this."^head.id;pos = head.pos}::rest
  | [] -> failwith "higher_name: Empty"

let print_higher_name f higher_name =
  (* print_endline ("length name:"^string_of_int (List.length (fst higher_name))); *)
  match higher_name with
  | (name,Some MethodName) ->  let tn = type_of_name_chain (List.rev (List.tl (List.rev name))) in print_sep_list print_ident (fun f -> fprintf f "_") f ( adjust_call tn  name)
  | (name,Some VarName) -> print_sep_list print_ident (fun f -> fprintf f ".") f (adjust_var higher_name) 
  | (name,None) -> print_sep_list print_ident (fun f -> fprintf f ".") f name



let print_name_enhanced f =
  print_sep_list print_ident_enhanced (fun f -> fprintf f ".") f 

let rec print_type f t =
  match t with
  | TypeName n -> print_name f (fst n)
  | ArrayType t' -> fprintf f "%a[]" print_type t'

let modifier_to_string m =
  match m with
  | Public -> "public"
  | Protected -> "protected"
  | Private -> "private"
  | Abstract -> "abstract"
  | Static -> "static"
  | Final -> "final"
  | StrictFP -> "strictfp"
  | Transient -> "transient"
  | Volatile -> "volatile"
  | Synchronized -> "synchronized"
  | Native -> "native"

let rec whether_static_field f =
  let rec helper m_list =
    begin
      match m_list with
      | head::rest -> if modifier_to_string head = "static" then true else helper rest 
      | [] -> false
    end
  in
  helper (f.f_var.v_mods)
  

(* Operator precedence.
   Used by print_prec to eliminate unnecessary parentheses. *)

type precedence = Left of int | Right of int

let operator_precedence e =
  match e with
  | Literal _
  | ClassLiteral _
  | NewClass _
  | NewQualifiedClass _
  | NewArray _
  | Dot _
  | Call _
  | ArrayAccess _
  | Name _
    -> Left 16

  | Postfix _
    -> Left 15

  | Prefix ("++", _)
  | Prefix ("--", _)
  | Prefix ("+", _)
  | Prefix ("-", _)
    -> Right 14

  | Prefix ("~", _)
  | Prefix ("!", _)
  | Cast _
    -> Right 13

  | Infix (_, "*", _)
  | Infix (_, "/", _)
  | Infix (_, "%", _)
    -> Left 12

  | Infix (_, "+", _)
  | Infix (_, "-", _)
    -> Left 11

  | Infix (_, "<<", _)
  | Infix (_, ">>", _)
  | Infix (_, ">>>", _)
    -> Left 10

  | Infix (_, "<", _)
  | Infix (_, ">", _)
  | Infix (_, "<=", _)
  | Infix (_, ">=", _)
  | InstanceOf _
    -> Left 9

  | Infix (_, "==", _)
  | Infix (_, "!=", _)
    -> Left 8

  | Infix (_, "&", _) -> Left 7
  | Infix (_, "^", _) -> Left 6
  | Infix (_, "|", _) -> Left 5
  | Infix (_, "&&", _) -> Left 4
  | Infix (_, "||", _) -> Left 3

  | Conditional _ -> Left 2

  | Assignment _ -> Right 1

  | _ -> invalid_arg "precedence"

let precedence e =
  match operator_precedence e with
  | Left n -> (2*n, 2*n+1)
  | Right n -> (2*n+1, 2*n)

let comments = ref []

(* Print all comments that occur before position [n] in the source file.
   The global variable [comments] contains a list of comments
   in order of position.  [print] sets this to the entire list initially;
   [print_comments] removes the ones it prints, for efficiency. *)

let print_comments f n =
  let rec loop list =
    match list with
    | { Source.buffer = comment; Source.pos = m; Source.spec = sp } :: rest ->
  	   if m < n then
  	     begin
            if sp then
    	       fprintf f "%s@\n" (String.sub comment 3 (String.length comment-5));
  	       loop rest
  	     end
  	   else
  	     comments := list
    | [] ->
    	comments := []
  in
  loop !comments

let print_comments_list f=
    let rec loop list =
    match list with
    | { Source.buffer = comment; Source.pos = m; Source.spec = sp } :: rest ->
         begin
          fprintf f "%s:%s@\n" (string_of_int m) comment;
          fprintf f "Length:%s@\n" (string_of_int (String.length comment));
          loop rest
         end
    | [] -> ()
  in
  loop !comments






let print_id_comments f id = print_comments f (id_pos id)

let print_stmt_comments f stmt = print_comments f (stmt_pos stmt)

let print_remaining_comments f =
  List.iter (fun c -> if c.Source.spec then fprintf f "%s@\n" c.Source.buffer) !comments;
  comments := []

let rec print f comp =
  pp_set_margin f 0;
  pp_open_box f 0;
  comments := comp.comments;
  (* print_comments_list f; *)
  begin
    match comp.package with
    | Some pkg ->
	print_id_comments f (List.hd pkg)
	(*fprintf f "package %a;@\n@\n" print_name pkg*)
    | None -> ()
  end;
  if comp.imports <> [] then
    begin
      (* print_newline_list (fun f -> fprintf f "import %a;" print_name)
	f comp.imports; *)
      fprintf f "@\n@\n";
    end;
  construct_type_table comp.decls;
  print_decls "" f comp.decls;
  pp_print_newline f ();
  print_more_code f;
  print_remaining_comments f;

and print_decls class_name f=
  print_sep_list (print_decl class_name) (fun f -> fprintf f "@\n@\n") f

and print_decl class_name f d=
  match d with
  | Class c -> print_class f c
  | Interface i -> print_interface f i
  | Field fld -> fprintf f "%a;" print_field fld
  | Method m -> print_method f m class_name
  | InstanceInit st -> fprintf f "%a" print_stmt st
  | StaticInit st -> fprintf f "static %a" print_stmt st
  | Constructor m -> print_method f m class_name




and mk_global_field class_name f=
  let f_var = {v_mods = [];v_type = f.f_var.v_type;v_name = {id = class_name^"_"^f.f_var.v_name.id;pos =f.f_var.v_name.pos }} in
  {f_var = f_var; f_init = f.f_init}

and mk_global_fields class_name flist = 
  match flist with
  | head::rest -> (mk_global_field  class_name head)::(mk_global_fields  class_name rest)
  | [] -> []

and print_global_fields class_name f=
  print_sep_list (print_global_field class_name) (fun f -> fprintf f "@\n@\n") f

and print_global_field class_name f d = 
  fprintf f "global %a;" print_field d


and extract_data_list d =
  match d with
  | (Field head)::rest -> if not (whether_static_field head) then (Field head)::(extract_data_list rest) else extract_data_list rest
  | [] -> []
  | _ -> failwith "extract_data_list: Unexpected"

and extract_global_list d =
  match d with
  | (Field head)::rest -> if whether_static_field head then head::(extract_global_list rest) else extract_global_list rest
  | [] -> []
  | _ -> failwith "extract_global_list: Unexpected"

and print_data f c =
  let field_list = split_decls c.cl_body "Field" in
  let global_list = extract_global_list field_list in
  fprintf f "@\n%a@\n"  (print_global_fields c.cl_name.id) (mk_global_fields c.cl_name.id global_list);
  let data_list = extract_data_list field_list in
  fprintf f "data %a@\n{@\n%a@\n}@\n" pp_print_string (c.cl_name.id) (print_decls c.cl_name.id) data_list

and print_class f c =
  in_class := c.cl_name.id;
  print_id_comments f c.cl_name;
  print_data f c;
  (* fprintf f "%aclass %a%a"
    print_modifiers c.cl_mods print_ident c.cl_name
    (print_option (fun f -> fprintf f "extends %a" print_name)) c.cl_super; *)
  (* if c.cl_impls <> [] then
    fprintf f " implements %a" (print_comma_list print_name) c.cl_impls; *)
  fprintf f " %a" (print_class_body c.cl_name.id) c.cl_body

and print_modifiers f mods =
  print_space_list (fun f m -> fprintf f "%s" (modifier_to_string m)) f mods;
  if mods <> [] then
    fprintf f " "

and print_class_body class_name f body =
  fprintf f "%a" (print_decls class_name) (split_decls body "Method")

and print_interface f i =
  print_id_comments f i.if_name;
  fprintf f "%ainterface %a" print_modifiers i.if_mods print_ident i.if_name;
  (* if i.if_exts <> [] then
    fprintf f " extends %a" (print_comma_list print_name) i.if_exts; *)
  fprintf f " %a" (print_class_body "") i.if_body

and print_field f fld =
  (* print_endline("print_field: "^fld.f_var.v_name.id); *)
  (* Hashtbl.add type_env fld.f_var.v_name.id fld.f_var.v_type; *)
  Hashtbl.add local_type_table fld.f_var.v_name.id fld.f_var.v_type;
  fprintf f "%a%a" print_var fld.f_var
    (print_option (fun f -> fprintf f "= %a" print_init)) fld.f_init

and print_init f init =
  match init with
  | ExprInit e -> print_expr f e
  | ArrayInit inits ->
      fprintf f "{ %a }" print_inits inits


and print_prec prec f e =
  (* let _ = print_endline ("print_prec") in *)
  let (left, right) = precedence e in
  if prec > min left right then
    fprintf f "(%a)" print_expr e
  else
    match e with
    | Literal s ->
	     fprintf f "%s" s
    | ClassLiteral t ->
	     fprintf f "%a.class" print_type t
    | NewClass (t, args, opt) ->
	     fprintf f "new %a(%a)%a"
	       print_type t print_exprs args (print_option (print_class_body "")) opt
    | NewQualifiedClass (e, id, args, opt) ->
	     fprintf f "%a.new %a(%a)%a"
      	  (print_prec left) e print_ident id print_exprs args
      	  (print_option (print_class_body "")) opt
    | NewArray (t, dims, n, opt) ->
	     fprintf f "new %a%a%a%a"
      	  print_type t print_dimensions dims print_extra_dimensions n
      	  (print_option print_init) opt
    | Dot (e, id,method_or_not) ->
        if method_or_not then
    	   fprintf f "%a.%a" (print_prec left) e print_ident id
        else
          fprintf f "%a_%a" (print_prec left) e print_ident id
    | Call (e, args) ->
      (* let _ = print_endline("Call") in  *)
	     fprintf f "%a(%a)" (print_prec left) e print_exprs (adjust_parameter e args)
    | ArrayAccess (e1, e2) ->
      (* let _ = print_endline("ArrayAccess") in  *)
	     fprintf f "%a[%a]" (print_prec left) e1 print_expr e2
    | Postfix (e, op) ->
        fprintf f "%a%s" (print_prec left) e op
    | Prefix (op, e) ->
        fprintf f "%s%a" op (print_prec right) e
    | Cast (t, e) ->
        fprintf f "(%a)%a" print_type t (print_prec right) e
    | Infix (e1, op, e2) ->
        fprintf f "%a %s %a" (print_prec left) e1 op (print_prec right) e2
    | InstanceOf (e, t) ->
        fprintf f "%a instanceof %a" (print_prec left) e print_type t
    | Conditional (e1, e2, e3) ->
        fprintf f "%a ? %a : %a"
	         (print_prec left) e1 (print_prec left) e2 (print_prec right) e3
    | Assignment (e1, op, e2) ->
        fprintf f "%a %s %a" (print_prec left) e1 op (print_prec right) e2
    | Name n ->
        (* let _ = print_endline("Name") in  *)
    	   print_higher_name f n

and print_expr f = print_prec 0 f

and print_exprs f =
  print_comma_list print_expr f

and print_dimensions f =
  print_list (fun f -> fprintf f "[%a]" print_expr) f

and print_extra_dimensions f n =
  if n > 0 then
    fprintf f "[]%a" print_extra_dimensions (n-1)

and print_inits f =
  print_comma_list print_init f

and print_method f m class_name=
  (*let new_formals = enhance_formals m.m_formals class_name in*)
  env := Env.empty;
  Hashtbl.clear local_type_table;
  (* Hashtbl.add local_type_table class_name (named_type class_name); *)

  if whether_static_field {f_var = m.m_var;f_init = None} 
  then 
    in_static :=  true 
  else 
    in_static :=  false; 

  let new_formals = if not !in_static 
                    then 
                          (* let _ = print_endline("new_formals") in *)
                          {v_mods =[];
                          v_type = (TypeName ([{id = class_name;pos = -1}],None));
                          v_name = {id = "_this";pos= -1}}::m.m_formals
                    else m.m_formals 
  in
  let _ = List.iter (fun f -> env:=Env.add f.v_name.id !env) new_formals in
  let _ = List.iter (fun f -> Hashtbl.add local_type_table f.v_name.id f.v_type) new_formals in
  fprintf f "%a(%a)"
      (print_method_name_ss class_name) m.m_var (print_comma_list print_var) new_formals;
  (* if m.m_throws <> [] then
    fprintf f " throws %a" (print_comma_list print_name) m.m_throws; *)
  fprintf f "@\n%a" print_stmt m.m_body (* It must be a block *)

and print_method_name_ss class_name f v =
  if v.v_type <> no_type then (* special case for constructor *)
    fprintf f "%a " print_type v.v_type;
  
  pp_print_string f (class_name^"_"^v.v_name.id)




and print_var f v =
  print_id_comments f v.v_name;
  (* print_modifiers f v.v_mods; *)
  if v.v_type <> no_type then (* special case for constructor *)
    fprintf f "%a " print_type v.v_type;
  print_ident f v.v_name


and combine_stmt o_stmt stmt_to_add =
  match o_stmt with
    | Block stmts ->
          Block (stmts@stmt_to_add)
    | _ -> Block ([o_stmt]@stmt_to_add)




and for_to_while for_stmt =
  match for_stmt with
    | For (init, Some test, update, st) ->
          
          let new_st = combine_stmt st update in
          let new_while = While (test,new_st) in
          init@[new_while]
    | _ -> failwith "for_to_while: Unexpected"

and print_stmt f stmt =
  match stmt with
  | Block [] ->
      print_stmt_comments f stmt;
      fprintf f "{@\n}"
  | Block stmts ->
      print_stmt_comments f stmt;
      fprintf f "{@\n@[<2>  %a@]@\n}" print_stmts stmts
  | LocalVar fld ->
      env:= Env.add fld.f_var.v_name.id !env ;fprintf f "%a;" print_field fld
  | LocalClass c ->
      print_class f c
  | Empty ->
      fprintf f ";"
  | Label (lbl, st) ->
      fprintf f "%a: %a" print_ident lbl print_stmt st
  | Expr e ->
      fprintf f "%a;" print_expr e
  | If (e, st, None) ->
      fprintf f "if (%a)%a" print_expr e print_body st
  | If (e, s1, Some s2) ->
      begin
	fprintf f "if (%a)%a" print_expr e print_body s1;
	(match s1 with
	| Block (_ :: _) -> fprintf f " "
	| _ -> fprintf f "@\n");
	fprintf f "else";
	(match s2 with
	| If _ -> fprintf f " %a" print_stmt s2
	| _ -> print_body f s2)
      end
  | Switch (e, sw) ->
      fprintf f "switch (%a) %a" print_expr e print_switch sw
  | While (e, st) ->
      fprintf f "while (%a)%a" print_expr e print_body st
  | Do (st, e) ->
      fprintf f "do%a while (%a);" print_body st print_expr e
  | For (init, test, update, st) ->
        fprintf f "@\n%a@\n" print_stmts (for_to_while stmt)
      (*
          fprintf f "for (%a;%a;%t%a)%a"
	  print_for_clause init
	  (print_option print_expr) test
	  (fun f -> if update <> [] then fprintf f " ")
	  print_for_clause update
	  print_body st
      *)
        
  | Break opt ->
      fprintf f "break%a;" (print_option print_ident) opt
  | Continue opt ->
      fprintf f "continue%a;" (print_option print_ident) opt
  | Return opt ->
      fprintf f "return%a;" (print_option print_expr) opt
  | Throw e ->
      fprintf f "throw %a;" print_expr e
  | Sync (e, st) ->
      fprintf f "synchronized (%a)%a" print_expr e print_body st
  | Try (st, catches, finally) ->
      begin
	fprintf f "try %a" print_stmt st;
	if catches <> [] then
	  fprintf f " %a" print_catches catches;
	print_option (fun f -> fprintf f "finally %a" print_stmt)
	  f finally;
      end

and print_stmts f =
  print_newline_list (fun f s -> print_stmt_comments f s; print_stmt f s) f

and print_body f st =
  match st with
  | Block (_ :: _) -> fprintf f " %a" print_stmt st
  | _ -> fprintf f "@\n@[<2>  %a@]" print_stmt st

and print_switch f sw =
  fprintf f "{@\n@[<2>  %a@]@\n}" (print_newline_list print_sw) sw

and print_sw f (cases, stmts) =
  fprintf f "%a@\n@[<2>  %a@]"
    (print_newline_list print_case) cases print_stmts stmts

and print_case f c =
  match c with
  | Case e -> fprintf f "case %a:" print_expr e
  | Default -> fprintf f "default:"

and print_for_clause f list =
  match list with
  | Expr _ :: _ -> print_comma_list print_expr_stmt f list
  | [LocalVar fld] -> print_field f fld
  | LocalVar fld :: rest ->
      fprintf f "%a, %a" print_field fld
	(print_comma_list (print_for_local_var fld.f_var.v_type)) rest
  | [] -> ()
  | _ -> invalid_arg "print_for_clause"

and print_expr_stmt f stmt =
  match stmt with
  | Expr e -> print_expr f e
  | _ -> invalid_arg "print_expr_stmt"

and print_for_local_var t f st =
  let rec convert typ id =
    if typ = t then id
    else match typ with
    | ArrayType typ' -> convert typ' (synth_id (id_string id ^ "[]"))
    | TypeName _ -> failwith "print_for_local_var: convert"
  in
  match st with
  | LocalVar fld ->
      fprintf f "%a%a"
	print_ident (convert fld.f_var.v_type fld.f_var.v_name)
	(print_option (fun f -> fprintf f "= %a" print_init)) fld.f_init
  | _ -> failwith "print_for_local_var"

and print_catches f  =
  print_space_list print_catch f

and print_catch f (v, st) =
  fprintf f "catch (%a) %a" print_var v print_stmt st

let print_to_file input_filename outputfilename = 
  let channelf = open_in (input_filename) in
  let lexbuf = Lexing.from_channel channelf in
  let outputchannel = open_out (outputfilename) in
    try
      let result = Jparser.goal(Jlexer.token) lexbuf in
      let _ = print (Format.formatter_of_out_channel outputchannel) result in
      let _ = close_out outputchannel in
      close_in channelf
    with
      End_of_file ->  exit 0

let print_out_str_to_file input_filename outputfilename=
  (* let _ = print_endline input_filename in *)
  let channelf = open_in (input_filename) in
  let lexbuf = Lexing.from_channel channelf in
  let outputchannel = open_out (outputfilename) in
  try
      let result = Jparser.goal(Jlexer.token) lexbuf in
      let finalStr = Format.flush_str_formatter(print Format.str_formatter result) in
      let _ = Printf.fprintf outputchannel "%s" finalStr in
      (*let _ = print_endline(finalStr) in*)
      let _ = close_in channelf in
      let _ = close_out outputchannel in
      finalStr
    with
      End_of_file ->  exit 0 

let print_out_str input_filename =
  let channelf = open_in (input_filename) in
  let lexbuf = Lexing.from_channel channelf in
  try
      let result = Jparser.goal(Jlexer.token) lexbuf in
      let finalStr = Format.flush_str_formatter(print Format.str_formatter result) in
      let _ = print_endline(finalStr) in 
      let _ = close_in channelf in
      finalStr
    with
      End_of_file ->  exit 0 

let print_out_str_from_files input_list outputfilename = 
  let rec helper input_list = 
    match input_list with
    | fname::rest ->  (print_out_str fname)^"\n"^(helper rest)
    | [] -> ""
  in
  let outputchannel = open_out(outputfilename) in
  let finalStr = helper input_list in
  let _ = Printf.fprintf outputchannel "%s" finalStr in
  let _ = print_endline(finalStr) in
  finalStr


let combine_two_java_compile_unit c1 c2 =
  match c1,c2 with
    | {package = _;imports = _;decls=d1;comments=com1},{package = _;imports = _;decls=d2;comments=com2} -> 
          let new_decls = d1@d2 in
          let new_comments = com1@com2 in
          {package = None;imports = [];decls = new_decls;comments = new_comments}
   

let empty_compile_unit = {package=None;imports = [];decls = [];comments = []};;

(* let print_out_str_from_files_new input_list outputfilename =                         *)
(*   let file_to_string input_filename =                                                *)
(*     let channelf = open_in (input_filename) in                                       *)
(*     let n = in_channel_length channelf in                                            *)
(*     let s = String.create n in                                                       *)
(*     really_input channelf s 0 n;                                                     *)
(*     close_in channelf;                                                               *)
(*     s                                                                                *)
(*   in                                                                                 *)
(*   let big_s = List.fold_left (fun s i -> s^"\n"^(file_to_string i)) "" input_list in *)
(*   let tmpOutChannel = open_out ("combined_tmp.java") in                              *)
(*   Printf.fprintf tmpOutChannel "%s" big_s;                                           *)
(*   close_out tmpOutChannel;                                                           *)
(*   print_out_str_to_file "combined_tmp.java" outputfilename;                          *)
(*   Sys.remove "combined_tmp.java"                                                     *)

let print_out_str_from_files_new input_list outputfilename = 
  let helper filename =
    let channelf = open_in (filename) in
    let lexbuf = Lexing.from_channel channelf in
    try
      let result = Jparser.goal(Jlexer.token) lexbuf in
      let _ = close_in channelf in
      result
    with
      End_of_file ->  exit 0
  in
  let bigResult = List.fold_left (fun c1 c2 -> combine_two_java_compile_unit c1 (helper c2))
    {package=None;imports = [];decls = [];comments = []} input_list
  in
  let outputchannel = open_out outputfilename in
  let _ = print (Format.formatter_of_out_channel outputchannel) bigResult in
  close_out outputchannel
