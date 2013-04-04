(*BACHLE: Jimple Parser 03/04/2013, comprising jimparser.ml (see also _tags), jimtoken.ml, jimlexer.mll*)
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

(* Peek functions to resolve ambiguity in the grammar rules*)

let peek_declaration = 
 SHGram.Entry.of_parser "peek_declaration" 
     (fun strm ->
       match Stream.npeek 3 strm with
			    | [GOTO,_;_;_] -> raise Stream.Failure 	
          | [_;_;SEMICOLON,_] -> () (*One field declaration*)
					| [_;_;COMMA,_] -> () (*Multiple fields declaration*)
					| [_; L_BRACKET,_;R_BRACKET,_]-> () (*Array declaration*)
					| _ -> raise Stream.Failure ) 

let peek_label_name = 
 SHGram.Entry.of_parser "peek_label_name" 
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_;COLON,_] -> ()
					| _ -> raise Stream.Failure ) 

let peek_identity_commons = 
 SHGram.Entry.of_parser "peek_identity_commons" 
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_;COLON_EQUALS,_] -> ()
					| _ -> raise Stream.Failure ) 

let peek_reference = 
 SHGram.Entry.of_parser "peek_reference" 
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_; DOT,_] -> ()
					| [_; L_BRACKET,_]-> ()
					| _ -> raise Stream.Failure ) 				

let peek_array_ref = 
 SHGram.Entry.of_parser "peek_array_ref" 
     (fun strm ->
       match Stream.npeek 4 strm with
					| [_; L_BRACKET,_;_;R_BRACKET,_]-> ()
					| _ -> raise Stream.Failure ) 	
					
let peek_binop = 
 SHGram.Entry.of_parser "peek_binop" 
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_;AND,_] -> ()  
          | [_;OR,_]  ->  ()   
          | [_;XOR,_] ->  ()   
          | [_;MOD,_] ->  ()   
          | [_;CMP,_] ->  ()   
          | [_;CMPG,_] ->  () 
          | [_;CMPL,_] ->  () 
          | [_;CMPEQ,_] -> ()
          | [_;CMPNE,_] -> ()
          | [_;CMPGT,_] ->  ()
          | [_;CMPGE,_] ->  () 
          | [_;CMPLT,_] ->  ()
          | [_;CMPLE,_] ->  ()   
          | [_;SHL,_] ->  ()  
          | [_;SHR,_] ->  ()  
          | [_;USHR,_] ->  ()
          | [_;PLUS,_] ->  () 
          | [_;MINUS,_] ->  () 
          | [_;DIV,_] ->  ()
					| [_;MULT,_] -> ()
					| _ -> raise Stream.Failure ) 	
					
let jimprog = SHGram.Entry.mk "jimprog" 
let x=Parser.hprog

let list_to_string ls space=
	let str=List.fold_left (fun a x-> a^space^x) "" ls in str

let opt_to_string t = 
	match t with Some v -> v | None -> "" 	

let return_result s= s
  	
EXTEND SHGram
  GLOBAL:  jimprog ;
			
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
	  [LEFTA [ `QUOTED_NAME qt-> qt ]];
	
	extends_clause:
	  [[ t = OPT extends_class_list -> opt_to_string t ]];
	
	extends_class_list:
	  [[ `EXTENDS; t = LIST1 class_name SEP `COMMA -> return_result "extends" ^(list_to_string t ",")]];
		
	implements_clause:
	  [[ t = OPT implements_class_list -> opt_to_string t]];
		
	implements_class_list:
	  [[ `IMPLEMENTS; t = LIST1 class_name SEP `COMMA -> return_result "implements" ^(list_to_string t ",")]];
	
	file_body:
	  [[ `L_BRACE; t=member_list_star ;`R_BRACE -> t]];
	
	member_list_star:
	  [[ t=LIST0 member -> return_result (list_to_string t "") ]];
	
  member:
	  [[   (md,tp,nm)= commons; `SEMICOLON -> return_result md^tp^nm (*Class FIELD...*)
		  |  (md,tp,nm)= commons; `L_PAREN; prl=parameter_list_question_mark; `R_PAREN;
			   thr=throws_clause; req=requires_clause; oldc=old_clauses; ensc=ensures_clause; mthbd=method_body -> return_result "Class METHODS..."
		]];
	
  commons: (*This is the common (similar) parts between fields and methods declations*)
	  [[md=modfifier_list_star; tp=jtype; nm=name -> (md,tp,nm)]];
			
  modfifier_list_star:
	  [[ t=LIST0 modifier -> return_result (list_to_string t "")]];
		
	jtype:
	  [[ `VOID -> return_result "{Void}"
		  | t=nonvoid_type -> t
		]];
  
	nonvoid_type: (*BACHLE*)
	  [[  bt=base_type_no_name; brks=array_brackets_list_star -> bt^brks
		  | quoted_name; array_brackets_list_star -> return_result "{Quoted($1,$2)}" (*TODO*)
			| identifier; array_brackets_list_star -> return_result "{Ident_NVT($1,$2)}" (*TODO*)
			| full_identifier; array_brackets_list_star -> return_result "{Full_ident_NVT($1,$2)}" (*TODO*)
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
	
	name: (*BACHLE*)
	  [[ t=identifier -> t
		 | t=quoted_name -> t
		]];
			
	parameter_list_question_mark:
	  [[t= OPT parameter_list ->  match t with Some v -> v | None -> [] ]];
  
	parameter_list:
	  [[  t= LIST1 parameter SEP `COMMA  -> t ]];
	
	parameter:
	  [[t= nonvoid_type -> t]];
	
	identifier:
    [LEFTA [ `IDENTIFIER s -> s]];
		
  full_identifier:
	  [LEFTA [ `FULL_IDENTIFIER s -> s]];
		
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
	  [[ peek_declaration; t=declaration -> t (*DOING BACHLE*) (*need a peek here to resolve the ambiguity*)
		  | stm=statement; spt=source_pos_tag_option -> return_result "dcl_stm_2"  (*DOING BACHLE*)
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

  statement: (*DOING BACHLE*)
	  [[  peek_label_name; t=label_name; `COLON -> t
     | `BREAKPOINT; `SEMICOLON  -> return_result "{Breakpoint_stmt}"
     | `ENTERMONITOR; immediate; `SEMICOLON -> return_result "{Entermonitor_stmt($2)}" (*DOING1*)
     | `EXITMONITOR; immediate; `SEMICOLON -> return_result "{Exitmonitor_stmt($2)}"
     | `TABLESWITCH; `L_PAREN; immediate; `R_PAREN; `L_BRACE; case_stmt_list_plus; `R_BRACE; `SEMICOLON -> return_result "{Tableswitch_stmt($3,$6)}"
     | `LOOKUPSWITCH; `L_PAREN; immediate;`R_PAREN; `L_BRACE; case_stmt_list_plus; `R_BRACE; `SEMICOLON -> return_result "{Lookupswitch_stmt($3,$6)}"
     | peek_identity_commons; (lcn,aid)=identity_commons; `SEMICOLON -> return_result "{Identity_no_type_stmt($1,$3)}"
     | peek_identity_commons; (lcn,aid)=identity_commons; jtype; `SEMICOLON -> return_result  "{Identity_stmt($1,$3,$4)}"
     | variable; `EQUALS; expression; `SEMICOLON -> return_result  "{Assign_stmt($1,$3)}"
     | `IF; bool_expr; goto_stmt -> return_result "{If_stmt($2,$3)}"
     | t=goto_stmt -> t
     | `NOP; `SEMICOLON -> return_result "{Nop_stmt}"
     | `RET; immediate_question_mark; `SEMICOLON -> return_result "{Ret_stmt($2)}"
     | `RETURN; immediate_question_mark; `SEMICOLON -> return_result "{Return_stmt($2)}"
     | `THROW; immediate; `SEMICOLON  -> return_result "{Throw_stmt($2)}"
     | invoke_expr; `SEMICOLON -> return_result "{Invoke_stmt($1)}"
  	 (* | `L_BRACE; lvariable_list; `R_BRACE COLON; spec; `SEMICOLON -> return_result "{Spec_stmt($2,$5)}" *)
		]];
   
	 identity_commons:
	  [[ lcn=local_name; `COLON_EQUALS; aid=at_identifier -> (lcn,aid) ]];
		
	 at_identifier:
	  [LEFTA [ `AT_IDENTIFIER t -> t ]];

	 immediate:
	  [[ t=local_name -> t
     | t=constant   -> t
		]];
		
	 constant:
	  [[ minus_question_mark; integer_constant -> return_result "{Int_const($1,$2)}"
     | minus_question_mark; integer_constant_long -> return_result "{Int_const_long($1,$2)}"
     | minus_question_mark; float_constant -> return_result "{Float_const($1,$2)}"
     | string_constant    -> return_result "{String_const($1)}"
     | `CLASS; string_constant -> return_result "{Clzz_const($2)}"
     | `NULL -> return_result "{Null_const}"
		]];
  
	 minus_question_mark:
	  [[ t=OPT minus -> match t with Some v-> return_result "minus" | None -> return_result "plus" ]];
	
	 minus:
	  [[ `MINUS -> "minus" ]];
		
	 integer_constant:
	  [[ `INTEGER_CONSTANT t -> t]];
	 
	 integer_constant_long:
	  [[ `INTEGER_CONSTANT_LONG t -> t]];
   
   float_constant:
	  [[ `FLOAT_CONSTANT t -> t  ]];
		
	 string_constant:
	  [[ `STRING_CONSTANT t -> t ]];
   
	 case_stmt_list_plus:
	  [[ t= LIST1 case_stmt -> t ]];

   case_stmt:
	  [[ case_label; `COLON; goto_stmt -> return_result "{Case_stmt($1,$3)}" ]];
	
   case_label:
	  [[ `CASE; minus_question_mark; integer_constant ->  return_result "{Case_label($2,$3)}"
     | `DEFAULT     -> return_result "{Case_label_default}"
		]];
   	
   goto_stmt:
	  [[ `GOTO; t=label_name; `SEMICOLON -> t ]];
		
	 variable:
	  [[ peek_reference; t=reference -> t
     | t=local_name -> t
		]];
  
	 reference:
	  [[ peek_array_ref; t=array_ref  -> t 
     | t=field_ref -> t 
	  ]];
  
	 array_ref:
	  [[ identifier; fixed_array_descriptor -> return_result "{Array_ref($1,$2)}" ]];
  
	 fixed_array_descriptor:
	  [[ `L_BRACKET; t=immediate; `R_BRACKET -> t]];
   
   field_ref:
	  [[ local_name; `DOT; field_signature ->  return_result "{ Field_local_ref($1,$3)}" 
     | t=field_signature -> t   
	  ]];
   
	 field_signature:
	  [[ `CMPLT; class_name; `COLON; jtype; name; `CMPGT -> return_result "{Field_signature($2,$4,$5)}"]];
   
	 expression:
	  [[ t=new_expr  -> t         
     | `L_PAREN; nonvoid_type; `R_PAREN; immediate -> return_result "{Cast_exp($2,$4)}"        
     | immediate; `INSTANCEOF; nonvoid_type -> return_result  "{Instanceof_exp($1,$3)}"  
     | t=invoke_expr -> t      
     | peek_reference; t=reference -> t
     | peek_binop; t=binop_expr -> t
     | t=unop_expr -> t
     | t=immediate -> t 
		]];

	 new_expr:
	  [[ `NEW; t=base_type -> t 
     | `NEWARRAY; `L_PAREN;  nonvoid_type; `R_PAREN;  fixed_array_descriptor -> return_result "{New_array_exp($3,$5)}"  
     | `NEWMULTIARRAY; `L_PAREN; base_type; `R_PAREN; array_descriptor_list_plus -> return_result  "{New_multiarray_exp($3,$5)}"  
		]];
 
   base_type:
    [[ t=base_type_no_name -> t
     | t=class_name -> t
	  ]];
		
	 array_descriptor_list_plus:
	  [[ t=LIST1 array_descriptor -> t ]];
   
	 array_descriptor:
    [[ `L_BRACKET; t=immediate_question_mark; `R_BRACKET -> t]];
		
	 immediate_question_mark:
    [[ t=LIST0 immediate -> t ]];
		
	 invoke_expr:
	  [[ nonstatic_invoke; local_name; `DOT; method_signature; `L_PAREN; arg_list_question_mark; `R_PAREN 
       -> return_result "{Invoke_nostatic_exp($1,$2,$4,$6)}"
     | `STATICINVOKE; method_signature; `L_PAREN; arg_list_question_mark; `R_PAREN  
       -> return_result "{Invoke_static_exp($2,$4)}"    		
		]];
  
	 nonstatic_invoke:  
    [[ `SPECIALINVOKE      -> return_result "{Special_invoke}"   
     | `VIRTUALINVOKE      -> return_result "{Virtual_invoke}"   
     | `INTERFACEINVOKE    -> return_result "{Interface_invoke}"
		]];  
		
	 method_signature:
    [[ `CMPLT; class_name; `COLON; jtype; name; `L_PAREN; parameter_list_question_mark; `R_PAREN; `CMPGT
       -> return_result "{Method_signature($2,$4,$5,$7)}"
		]];	
		
	 parameter_list_question_mark:
	  [[ t= parameter_list -> t ]];
		
	 arg_list_question_mark:
	  [[ t=LIST0 arg_list -> t ]];
		
	 arg_list:
	  [[ t=LIST1 immediate SEP `COMMA -> t ]];
	 
   binop_expr:
    [[ immediate; binop; immediate -> return_result "{Binop_exp($2,$1,$3)}" ]];
	
   binop: 
    [[ t=binop_no_mult -> t 
     | `MULT -> return_result "{ Mult }"
	  ]];
		
   binop_no_mult:
    [[ `AND -> return_result "{And}"   
     | `OR  ->  return_result "{Jparsetree.Or}"    
     | `XOR ->  return_result "{Xor}"   
     | `MOD ->  return_result "{Mod}"   
     | `CMP ->  return_result "{Cmp}"   
     | `CMPG ->  return_result "{Cmpg}"  
     | `CMPL ->  return_result "{Cmpl}"  
     | `CMPEQ ->  return_result "{Cmpeq}" 
     | `CMPNE ->  return_result "{Cmpne}" 
     | `CMPGT ->  return_result "{Cmpgt}" 
     | `CMPGE ->  return_result "{Cmpge}" 
     | `CMPLT ->  return_result "{Cmplt}" 
     | `CMPLE ->  return_result "{Cmple}"   
     | `SHL ->  return_result "{Shl}"   
     | `SHR ->  return_result "{Shr}"   
     | `USHR ->  return_result "{Ushr}"  
     | `PLUS ->  return_result "{Plus}"  
     | `MINUS ->  return_result "{Minus}" 
     | `DIV ->  return_result "{Div}" 
	  ]];

   unop_expr:
    [[ unop; immediate -> return_result "{Unop_exp($1,$2)}" ]];	
	 
	 unop:
    [[ `LENGTHOF  -> return_result "{Lengthof}" 
     | `NEG -> return_result "{Neg}"
		]];
		
   bool_expr:
   [[ t=binop_expr -> t  
    | t=unop_expr   -> t
	 ]];  	
																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																												 																																										
   source_pos_tag:
	  [[ `SOURCE_POS_TAG; `COLON; identifier; `COLON; integer_constant; identifier; `COLON; integer_constant; identifier; `COLON; integer_constant; identifier; `COLON; integer_constant; identifier; `COLON; full_identifier; `SOURCE_POS_TAG_CLOSE
       -> return_result "{ {begin_line=$5; begin_column=$11; end_line=$8; end_column=$14} }"
		]];

   source_pos_tag_option:
	  [[ t=OPT source_pos_tag -> match t with Some v->v | None -> return_result "none_pos_tag"]];
																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																											    																																																								   								 	
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


