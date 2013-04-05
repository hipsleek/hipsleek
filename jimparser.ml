(*BACHLE: Jimple Parser 03/04/2013, comprising jimparser.ml (see also _tags), jimtoken.ml, jimlexer.mll*)
(*BACHLE: see the helper about Jimple grammar https://github.com/safdariqbal/soot/blob/master/src/jimple.scc*)
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
open Jimple_global_types
open Jparsetree

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

(* BACHLE: Peek functions to resolve ambiguity in the grammar rules*)
(* Peek functions are used to look ahead tokens, raising Strean.Failure helps to backtrack to another cases*)

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

let list_to_string ls space=
	let str=List.fold_left (fun a x-> a^space^x) "" ls in str

let opt_to_list t = 
	match t with Some v -> v | None -> [] 	

let return_result s= s

let str_of str t= 
  if ((List.length t)=0) then " "
	else
	 return_result (str^(if ((List.length t)>1) then (list_to_string t ",") else list_to_string t " "))

let pp_list_members mbl=
	List.map ( fun (fm,md,tp,nm,_,_,_,_,_,mth)->
		  if(fm="FIELDS") then print_endline ((list_to_string md "")^" "^tp^" "^nm)
	    else  print_endline ((list_to_string md "")^" "^tp^" "^nm ^" {"^mth^" }")
		) mbl
(* let _= print_endline ("Parsing Jimple...\n=======\n"^(list_to_string md "")^ft^" "^cln^" "^(str_of "extends" ex)^" "^(str_of "implements" imp)) in *)
(* pp_list_members fb                                                                                                                                 *)					

EXTEND SHGram
  GLOBAL:  jimprog ;
			
	jimprog:[[md = modifier_list_star; ft = file_type; cln = class_name; ex = extends_clause; imp = implements_clause; fb = file_body 
	          -> JFile (md,ft,cln,ex,imp,fb)
		]];
	
	modifier_list_star:
	  [[ t = LIST0 modifier -> t ]];
	
	modifier:
    [[  `ABSTRACT -> Abstract 
		  | `FINAL ->  Final 
			| `NATIVE -> Native
			| `PUBLIC  -> Public
			| `PROTECTED -> Protected
			| `PRIVATE -> Private
			| `STATIC -> Jparsetree.Static
			| `SYNCHRONIZED -> Synchronized
			| `TRANSIENT ->  Transient
			| `VOLATILE ->  Volatile
			| `STRICTFP -> Strictfp
			| `ENUM ->  Enum
			| `ANNOTATION -> Annotation (*TODO...*)
		]];
			
	file_type:
	  [[  `CLASS -> ClassFile
			| `INTERFACE -> InterfaceFile (*TODO...*)
		]];
		
	class_name:
	  [[ 	 t=quoted_name -> Quoted_clname t  (*TODO*)
		   | `IDENTIFIER s -> Identifier_clname s
			 | t=full_identifier -> Full_identifier_clname t  (*TODO*)
		]];
	
	quoted_name:
	  [LEFTA [ `QUOTED_NAME qt-> qt ]];
	
	extends_clause:
	  [[ t = OPT extends_class_list -> opt_to_list t ]];
	
	extends_class_list:
	  [[ `EXTENDS; t = LIST1 class_name SEP `COMMA -> t]];
	
	implements_clause:
	  [[ t = OPT implements_class_list -> opt_to_list t]];
		
	implements_class_list:
	  [[ `IMPLEMENTS; t = LIST1 class_name SEP `COMMA -> t]];
	
	file_body:
	  [[ `L_BRACE; t=member_list_star ;`R_BRACE -> t]];
	
	member_list_star:
	  [[ t=LIST0 member -> t]];
	
  member:
	  [[   (modif,typ,nm)= commons; `SEMICOLON ->  Field (modif,typ,nm) (*Class FIELD...*)
		  |  (modif,typ,nm)= commons; `L_PAREN; prl=parameter_list_question_mark; `R_PAREN;
			   thr=throws_clause; req=requires_clause; oldc=old_clauses; ensc=ensures_clause; mthbd=method_body 
				 -> Method (modif,typ,nm,prl,thr,req,oldc,ensc,mthbd) (*Class METHOD...*)
		]];

  commons: (*This is the common (similar) parts between fields and methods declarations*)
	  [[md=modfifier_list_star; tp=jtype; nm=name -> (md,tp,nm)]];
			
  modfifier_list_star:
	  [[ t=LIST0 modifier -> t ]];
		
	jtype:
	  [[ `VOID -> Void
		  | t=nonvoid_type -> Non_void t
		]];
  
	nonvoid_type: (*BACHLE*)
	  [[  bt=base_type_no_name; brks=array_brackets_list_star -> Base(bt,brks)
		  | qtn=quoted_name; brks=array_brackets_list_star -> Quoted(qtn,brks) (*TODO*)
			| id=identifier; brks=array_brackets_list_star -> Ident_NVT(id,brks) (*TODO*)
			| fid=full_identifier; brks=array_brackets_list_star -> Full_ident_NVT(fid,brks) (*TODO*)
		]];
  
	base_type_no_name:
	  [[ `BOOLEAN -> Boolean
     | `BYTE -> Byte
     | `CHAR -> Char
     | `SHORT -> Short
     | `INT -> Int
     | `LONG -> Long
     | `FLOAT -> Float
     | `DOUBLE -> Double
     | `NULL -> Null_type
		]];
  
	array_brackets_list_star:
	  [[ t=LIST0 arr_brk_lstar -> t ]];
		
	arr_brk_lstar:
	  [[ `L_BRACKET; `R_BRACKET -> "[]"]];
	
	name: (*BACHLE*)
	  [[ t=quoted_name -> Quoted_name t
		 | t=identifier -> Identifier_name t
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
	  [[ t=OPT cln_list -> t]];
	
	cln_list:
	  [[ `THROWS; t=class_name_list -> t ]];

  class_name_list:
    [[ t=LIST1 class_name -> t]];
	
	requires_clause:
	  [[ t=OPT req_mth_body -> match t with None -> None | Some v -> v]]; (*TODO*)
	
	req_mth_body:
	  [[ `REQUIRES; t=method_body -> t]];
 		
	method_body:
	  [[ `SEMICOLON -> None
		  |`L_BRACE; ds=declaration_or_statement_list_star; cc=catch_clause_list_star; `R_BRACE -> Some (ds,cc)
		]];

  declaration_or_statement_list_star:
	  [[ t=LIST0 declaration_or_statement -> t]];
 
  declaration_or_statement: (*DOING BACHLE*)
	  [[ peek_declaration; t=declaration -> DOS_dec t  (*need a peek here to resolve the ambiguity between the two branchs*)
		  | stm=statement; spt=source_pos_tag_option -> DOS_stm (stm,spt)
		]];
  
	declaration:
	  [[ jt=jimple_type; lcl=local_name_list; `SEMICOLON -> Declaration(jt,lcl) ]];
	
	jimple_type:
	  [[ `UNKNOWN -> None
     | t=nonvoid_type -> Some(Non_void t)
     | `NULL_TYPE -> None
		]];

  local_name:
	  [[t= name -> t]];
 
  local_name_list:
    [[ t=LIST1 local_name SEP `COMMA -> t]];
		
	catch_clause_list_star:
	  [[ t=LIST0 catch_clause -> t]];

  catch_clause:
	  [[ `CATCH; cln=class_name; `FROM; lb1=label_name; `TO; lb2=label_name; `WITH; lb3=label_name; `SEMICOLON -> Catch_clause (cln,lb1,lb2,lb3)]];

  label_name:
	  [[ t=identifier -> t]];
  
	old_clauses:
	  [[ t=LIST0 old_clause -> t]];
  
	old_clause:
	  [[ `OLD; t=method_body -> t]];
  
	ensures_clause:
	  [[ t=OPT ens_mth_body -> match t with None -> None | Some v -> v ]]; (*TODO*)
		
	ens_mth_body:
	  [[ `ENSURES; t=method_body -> t]];

  statement: (*DOING BACHLE*)
	  [[  peek_label_name; t=label_name; `COLON -> Label_stmt t
     | `BREAKPOINT; `SEMICOLON  -> Breakpoint_stmt
     | `ENTERMONITOR; imm=immediate; `SEMICOLON -> Entermonitor_stmt(imm) 
     | `EXITMONITOR; imm=immediate; `SEMICOLON -> Exitmonitor_stmt(imm)
     | `TABLESWITCH; `L_PAREN; imm=immediate; `R_PAREN; `L_BRACE; cst=case_stmt_list_plus; `R_BRACE; `SEMICOLON -> Tableswitch_stmt(imm,cst)
     | `LOOKUPSWITCH; `L_PAREN; imm=immediate;`R_PAREN; `L_BRACE; cst=case_stmt_list_plus; `R_BRACE; `SEMICOLON -> Lookupswitch_stmt(imm,cst)
     | peek_identity_commons; (lcn,aid)=identity_commons; `SEMICOLON -> Identity_no_type_stmt(lcn,aid)
     | peek_identity_commons; (lcn,aid)=identity_commons; jt=jtype; `SEMICOLON -> Identity_stmt(lcn,aid,jt)
     | var=variable; `EQUALS; exp=expression; `SEMICOLON -> Assign_stmt(var,exp)
     | `IF; ble=bool_expr; gts=goto_stmt -> If_stmt(ble,gts)
     | t=goto_stmt -> Goto_stmt t
     | `NOP; `SEMICOLON -> Nop_stmt
     | `RET; imm=immediate_question_mark; `SEMICOLON -> Ret_stmt(imm)
     | `RETURN; imm=immediate_question_mark; `SEMICOLON -> Return_stmt(imm)
     | `THROW; imm=immediate; `SEMICOLON  -> Throw_stmt(imm)
     | ivk=invoke_expr; `SEMICOLON -> Invoke_stmt(ivk)
  	 (* | `L_BRACE; lvariable_list; `R_BRACE COLON; spec; `SEMICOLON -> return_result "Spec_stmt($2,$5)" *)
		]];
   
	 identity_commons:
	  [[ lcn=local_name; `COLON_EQUALS; aid=at_identifier -> (lcn,aid) ]];
		
	 at_identifier:
	  [LEFTA [ `AT_IDENTIFIER t -> t ]];

	 immediate:
	  [[ t=local_name -> Immediate_local_name t
     | t=constant   -> Immediate_constant t
		]];
		
	 constant:
	  [[ mn=minus_question_mark; ic=integer_constant -> Int_const(mn,ic)
     | mn=minus_question_mark; ic=integer_constant_long -> Int_const_long(mn,ic)
     | mn=minus_question_mark; fc=float_constant -> Float_const(mn,fc)
     | sc=string_constant    -> String_const(sc)
     | `CLASS; sc=string_constant -> Clzz_const(sc)
     | `NULL -> Null_const
		]];
  
	 minus_question_mark:
	  [[ t=OPT minus -> match t with Some v-> Negative | None -> Positive ]];
	
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
	  [[ cl=case_label; `COLON; gts=goto_stmt -> Case_stmt(cl,gts) ]];
	
   case_label:
	  [[ `CASE; mn=minus_question_mark; ic=integer_constant ->  Case_label(mn,ic)
     | `DEFAULT     -> Case_label_default
		]];
   	
   goto_stmt:
	  [[ `GOTO; t=label_name; `SEMICOLON -> t ]];
		
	 variable:
	  [[ peek_reference; t=reference -> Var_ref t
     | t=local_name -> Var_name t
		]];
  
	 reference:
	  [[ peek_array_ref; t=array_ref  -> t 
     | t=field_ref -> t 
	  ]];
  
	 array_ref:
	  [[ id=identifier; fad=fixed_array_descriptor -> Array_ref(id,fad) ]];
  
	 fixed_array_descriptor:
	  [[ `L_BRACKET; t=immediate; `R_BRACKET -> t]];
   
   field_ref:
	  [[ ln=local_name; `DOT; fs=field_signature ->  Field_local_ref(ln,fs) 
     | t=field_signature -> Field_sig_ref t   
	  ]];
   
	 field_signature:
	  [[ `CMPLT; cln=class_name; `COLON; jt=jtype; nm=name; `CMPGT -> Field_signature(cln,jt,nm)]];
   
	 expression:
	  [[ t=new_expr  -> t         
     | `L_PAREN; nvt=nonvoid_type; `R_PAREN; imm=immediate -> Cast_exp(nvt,imm)        
     | imm=immediate; `INSTANCEOF; nvt=nonvoid_type -> Instanceof_exp(imm,nvt)  
     | t=invoke_expr -> Invoke_exp t      
     | peek_reference; t=reference -> Reference_exp t
     | peek_binop; t=binop_expr -> t
     | t=unop_expr -> t
     | t=immediate -> Immediate_exp t 
		]];

	 new_expr:
	  [[ `NEW; t=base_type -> New_simple_exp t 
     | `NEWARRAY; `L_PAREN;  nvt=nonvoid_type; `R_PAREN;  fad=fixed_array_descriptor -> New_array_exp(nvt,fad)  
     | `NEWMULTIARRAY; `L_PAREN; bst=base_type; `R_PAREN; adl=array_descriptor_list_plus -> New_multiarray_exp(bst,adl)  
		]];
 
   base_type:
    [[ t=base_type_no_name -> t
     | t=class_name -> Class_name t
	  ]];
		
	 array_descriptor_list_plus:
	  [[ t=LIST1 array_descriptor -> t ]];
   
	 array_descriptor:
    [[ `L_BRACKET; t=immediate_question_mark; `R_BRACKET -> t]];
		
	 immediate_question_mark:
    [[ t=OPT immediate -> t ]];
		
	 invoke_expr:
	  [[ ni=nonstatic_invoke; ln=local_name; `DOT; ms=method_signature; `L_PAREN; alq=arg_list_question_mark; `R_PAREN 
       -> Invoke_nostatic_exp(ni,ln,ms,alq)
     | `STATICINVOKE; ms=method_signature; `L_PAREN; alq=arg_list_question_mark; `R_PAREN  
       -> Invoke_static_exp(ms,alq)    		
		]];
  
	 nonstatic_invoke:  
    [[ `SPECIALINVOKE      -> Special_invoke   
     | `VIRTUALINVOKE      -> Virtual_invoke   
     | `INTERFACEINVOKE    -> Interface_invoke
		]];  
		
	 method_signature:
    [[ `CMPLT; cln=class_name; `COLON; jt=jtype; nm=name; `L_PAREN; plq=parameter_list_question_mark; `R_PAREN; `CMPGT
       -> Method_signature(cln,jt,nm,plq)
		]];	
		
	 parameter_list_question_mark:
	  [[ t= parameter_list -> t ]];
		
	 arg_list_question_mark:
	  [[ t=OPT arg_list -> match t with None -> [] | Some v -> v ]];
		
	 arg_list:
	  [[ t=LIST1 immediate SEP `COMMA -> t ]];
	 
   binop_expr:
    [[ imm1=immediate; bn=binop; imm2=immediate -> Binop_exp(bn,imm1,imm2) ]];
	
   binop: 
    [[ t=binop_no_mult -> t 
     | `MULT -> Mult 
	  ]];
		
   binop_no_mult:
    [[ `AND -> And   
     | `OR  ->  Jparsetree.Or    
     | `XOR ->  Xor   
     | `MOD ->  Mod   
     | `CMP ->  Cmp   
     | `CMPG ->  Cmpg  
     | `CMPL ->  Cmpl  
     | `CMPEQ ->  Cmpeq 
     | `CMPNE ->  Cmpne 
     | `CMPGT ->  Cmpgt 
     | `CMPGE ->  Cmpge
     | `CMPLT ->  Cmplt
     | `CMPLE ->  Cmple 
     | `SHL ->  Shl
     | `SHR ->  Shr
     | `USHR ->  Ushr
     | `PLUS ->  Plus
     | `MINUS ->  Minus
     | `DIV ->  Div
	  ]];

   unop_expr:
    [[ un=unop; imm=immediate -> Unop_exp(un,imm) ]];	
	 
	 unop:
    [[ `LENGTHOF  -> Lengthof 
     | `NEG -> Neg
		]];
		
   bool_expr:
   [[ t=binop_expr -> t  
    | t=unop_expr   -> t
	 ]];  	
																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																												 																																										
   source_pos_tag:
	  [[ `SOURCE_POS_TAG; `COLON; identifier; `COLON; ic1=integer_constant; identifier; `COLON; ic2=integer_constant; identifier; `COLON; ic3=integer_constant; identifier; `COLON; ic4=integer_constant; identifier; `COLON; full_identifier; `SOURCE_POS_TAG_CLOSE
       -> {begin_line=ic1; begin_column=ic3; end_line=ic2; end_column=ic4} 
		]];

   source_pos_tag_option:
	  [[ t=OPT source_pos_tag -> t]];
																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																											    																																																								   								 	
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


