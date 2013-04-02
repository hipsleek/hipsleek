module DD=Debug (* which Debug is this? *)
open Camlp4
open Globals
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Iast
open Jimtoken
open Sleekcommons
open Gen.Basic
open Label_only

open Perm

module F = Iformula
module P = Ipure
module E1 = Error
module I = Iast
module Ts = Tree_shares.Ts

module SHGram = Camlp4.Struct.Grammar.Static.Make(Jimlexer.Make(Token))

(* some variables and functions decide which parser will be used *)
let parser_name = ref "unknown"

let set_parser name =
  parser_name := name

let test str= print_endline (str)
(* type definitions *)

type type_decl =
  | Data of data_decl
  | Enum of enum_decl
  | View of view_decl
  | Hopred of hopred_decl
  | Barrier of barrier_decl

		
type decl = 
  | Type of type_decl
  | Func of func_decl
  | Rel of rel_decl (* An Hoa *)
  | Hp of hp_decl
  | Axm of axiom_decl (* An Hoa *)
  | Global_var of exp_var_decl
  | Logical_var of exp_var_decl (* Globally logical vars *)
  | Proc of proc_decl
  | Coercion of coercion_decl
		| Include of string
		

type member = 
  | Field of (typed_ident * loc)
  | Inv of F.formula
  | Method of proc_decl

type spec_qualifier =
  | Static
  | Dynamic 

type ann =
  | AnnMode of mode
  | AnnType of typ

type file_offset =
  {
    line_num: int;
    line_start: int;
    byte_num: int;
  }

let jimprog = SHGram.Entry.mk "jimprog" 

let list_to_string ls space=
	let str=List.fold_left (fun a x-> a^space^x) "" ls in str

let opt_to_string t = 
	match t with Some v -> v | None -> "" 	

let return_result s= s
  	
EXTEND SHGram
  GLOBAL: jimprog;
	jimprog:[[md = modifier_list_star; ft = file_type; cln = class_name; ex = extends_clause; imp = implements_clause; fb = file_body -> 
		print_endline ("Parsing Jimple...\n"^(list_to_string md "")^ft^" "^cln^" "^ex^" "^imp^" \n{"^fb^"\n}")]];
	
	modifier_list_star:
	  [[ t = LIST0 modifier -> t ]];
	
	modifier:
    [[  `ABSTRACT -> return_result " {Abstract} "
		  | `FINAL -> return_result " {Final} "
			| `NATIVE -> return_result "{Native}"
			| `PUBLIC  -> return_result "{Public}"	
			| `PROTECTED -> return_result " {Protected}"
			| `PRIVATE -> return_result "{Private}"
			| `STATIC -> return_result " {Jparsetree.Static}"
			| `SYNCHRONIZED -> return_result "{Synchronized}"
			| `TRANSIENT -> return_result " {Transient}"
			| `VOLATILE -> return_result " {Volatile}"
			| `STRICTFP -> return_result " {Strictfp}"
			| `ENUM -> return_result "{Enum}"
			| `ANNOTATION ->  return_result " {Annotation}" (*TODO...*)
		]];
			
	file_type:
	  [[  `CLASS -> return_result "class"
			| `INTERFACE -> return_result "inferface" (*TODO...*) 
		]];
		
	class_name:
	  [[ 	 t=quoted_name -> t  (*TODO*)
		   | `IDENTIFIER s -> s (*"Identifier_clname $1"*)           
			 | t=full_identifier -> t  (*TODO*)
		]];	
	
	quoted_name:
	  [[ `QUOTED_NAME qt-> qt ]];	
	
	extends_clause:
	  [[ t = OPT extends_class_list -> opt_to_string t ]];
	
	extends_class_list:
	  [[ `EXTENDS; t = LIST1 elem SEP `COMMA -> return_result "extends" ^(list_to_string t ",")]];
		
	implements_clause:
	  [[ t = OPT implements_class_list -> opt_to_string t]];
		
	implements_class_list:
	  [[ `IMPLEMENTS; t = LIST1 elem SEP `COMMA -> return_result "implements" ^(list_to_string t ",")]];
			
	elem:
	  [[ `IDENTIFIER s -> s]];
	
	file_body:
	  [[ `L_BRACE; t=member_list_star ;`R_BRACE -> t]];
	
	member_list_star:
	  [[ t=LIST0 member -> return_result (list_to_string t "") ]];
	
  member:
	  [[  md=modfifier_list_star; tp=jtype; nm=name; `SEMICOLON -> exit(0); return_result md^tp^nm (*FIELD...*)
		  | modifier_list_star; jtype; name; `L_PAREN; parameter_list_question_mark; `R_PAREN;
			  throws_clause; requires_clause; old_clauses; ensures_clause; method_body -> return_result "METHODS..."
		]];
		
  modfifier_list_star:
	  [[ t=LIST0 modifier -> return_result (list_to_string t "")]];
	
	jtype:
	  [[ `VOID -> return_result "{Void}"
		  | t=nonvoid_type -> t
		]];
  
	nonvoid_type:
	  [[  bt=base_type_no_name; brks=array_brackets_list_star -> bt^brks
		  | quoted_name; array_brackets_list_star -> "{Quoted($1,$2)}" (*TODO*)
			| identifier; array_brackets_list_star -> "{Ident_NVT($1,$2)}" (*TODO*)
			| full_identifier; array_brackets_list_star -> "{Full_ident_NVT($1,$2)}" (*TODO*)
		]];
  
	base_type_no_name:
	  [[ `BOOLEAN -> return_result "{Boolean}"  
     | `BYTE -> return_result "{Byte}"     
     | `CHAR -> return_result "{Char}"     
     | `SHORT -> return_result "{Short}"   
     | `INT -> return_result "{Int}"      
     | `LONG -> return_result "{Long}"    
     | `FLOAT -> return_result "{Float}"  
     | `DOUBLE -> return_result "{Double}" 
     | `NULL -> return_result "{Null_type}"			
		]];
  
	array_brackets_list_star:
	  [[ t=LIST0 arr_brk_lstar -> return_result (list_to_string t "")]];
		
	arr_brk_lstar:
	  [[ `L_BRACKET; `R_BRACKET -> return_result "[]"]];	
	
	name:
	  [[ t=quoted_name -> t
		 | t=identifier -> t 
		]];
			
	parameter_list_question_mark:
	  [[t= OPT parameter_list ->  match t with Some v -> v | None -> [] ]];
  
	parameter_list:
	  [[  t= LIST1 parameter SEP `COMMA  -> t ]];
	
	parameter:
	  [[t= nonvoid_type -> t]];
	
	identifier:
    [[ `IDENTIFIER s -> s]];
		
  full_identifier:
	  [[ `FULL_IDENTIFIER s -> s]];
		
	throws_clause:
	  [[ t=OPT cln_list -> match t with Some v->v | None -> [] ]];
	
	cln_list:
	  [[ `THROWS; t=class_name_list -> t ]];	

  class_name_list:
    [[ t=LIST1 class_name -> t]];
	
	requires_clause:
	  [[ t=OPT req_mth_body -> match t with Some v->v | None -> return_result "" ]]; (*TODO*)
	
	req_mth_body:
	  [[ `REQUIRES; t=method_body -> t]];	
 		
	method_body:
	  [[ `SEMICOLON -> return_result ";"
		  |`L_BRACE; declaration_or_statement_list_star; catch_clause_list_star; `R_BRACE -> return_result "method_body" 
		]];

  declaration_or_statement_list_star:
	  [[ t=LIST0 declaration_or_statement -> t]];
 
  declaration_or_statement:
	  [[ t=declaration -> t 
		 (* | statement; source_pos_tag_option -> return_result "dcl_stm_2" *)
		]];
  
	declaration:
	  [[ jimple_type; local_name_list; `SEMICOLON -> return_result "dcl_stm_1"]];
	
	jimple_type:
	  [[ `UNKNOWN -> return_result "{None}" 
     | t=nonvoid_type -> t 
     | `NULL_TYPE -> return_result "{None}"
		]];

  local_name:
	  [[t= name -> t]];
 
  local_name_list:
    [[ t=LIST1 local_name SEP `COMMA -> t]]; 
		
	catch_clause_list_star:
	  [[ t=LIST0 catch_clause -> t]];

  catch_clause:
	  [[ `CATCH; class_name; `FROM; label_name; `TO; label_name; `WITH; label_name; `SEMICOLON -> return_result "catch_clause"]];

  label_name:
	  [[ t=identifier -> t]];
  
	old_clauses:
	  [[ t=LIST0 old_clause -> t]];
  
	old_clause:
	  [[ `OLD; t=method_body -> t]];
  
	ensures_clause:
	  [[ t=OPT ens_mth_body -> match t with Some v-> v | None -> return_result "" ]]; (*TODO*)
		
	ens_mth_body:
	  [[ `ENSURES; t=method_body -> t]];	

  (* statement:                                                                                                            *)
	(*   [[  label_name COLON  {Label_stmt($1)}                                                                              *)
  (*    | BREAKPOINT SEMICOLON  {Breakpoint_stmt}                                                                          *)
  (*    | ENTERMONITOR immediate SEMICOLON {Entermonitor_stmt($2)}                                                         *)
  (*    | EXITMONITOR immediate SEMICOLON  {Exitmonitor_stmt($2)}                                                          *)
  (*    | TABLESWITCH L_PAREN immediate R_PAREN L_BRACE case_stmt_list_plus R_BRACE SEMICOLON {Tableswitch_stmt($3,$6)}    *)
  (*    | LOOKUPSWITCH L_PAREN immediate R_PAREN L_BRACE case_stmt_list_plus R_BRACE SEMICOLON {Lookupswitch_stmt($3,$6)}  *)
  (*    | local_name COLON_EQUALS at_identifier SEMICOLON {Identity_no_type_stmt($1,$3)}                                   *)
  (*    | local_name COLON_EQUALS at_identifier jtype SEMICOLON  {Identity_stmt($1,$3,$4)}                                 *)
  (*    | variable EQUALS expression SEMICOLON  {Assign_stmt($1,$3)}                                                       *)
  (*    | IF bool_expr goto_stmt     {If_stmt($2,$3)}                                                                      *)
  (*    | goto_stmt {Goto_stmt($1)}                                                                                        *)
  (*    | NOP SEMICOLON     {Nop_stmt}                                                                                     *)
  (*    | RET immediate_question_mark SEMICOLON     {Ret_stmt($2)}                                                         *)
  (*    | RETURN immediate_question_mark SEMICOLON  {Return_stmt($2)}                                                      *)
  (*    | THROW immediate SEMICOLON     {Throw_stmt($2)}                                                                   *)
  (*    | invoke_expr SEMICOLON     {Invoke_stmt($1)}                                                                      *)
  (* 	 | L_BRACE lvariable_list R_BRACE COLON spec SEMICOLON {Spec_stmt($2,$5)}		                                       *)
	(* 	]];                                                                                                                 *)

  (* jimprog:[[ t = command_list-> print_endline ("Testing jim...") ]]; *)
	(* command_list: [[`VOID -> ()]];                                     *)
 
END;;

let parse_hip n s =
  SHGram.parse jimprog (PreCast.Loc.mk n) s

let parse_hip n s =
  DD.no_1_loop "parse_hip" (fun x -> x) (fun _ -> "?") (fun n -> parse_hip n s) n

let parse_hip_string n s =
  SHGram.parse_string jimprog (PreCast.Loc.mk n) s

let parse_hip_string n s = 
  let pr x = x in
  let pr_no x = "?" in DD.no_2 "parse_hip_string" pr pr pr_no parse_hip_string n s


