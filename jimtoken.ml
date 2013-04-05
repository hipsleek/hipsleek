open Camlp4.PreCast

type jim_token =
 ABDUCTION | ABS | ABSRULE | ABSTRACT | AND | ANDALSO | ANNOTATION 
| AS | ASSIGN | AT_IDENTIFIER of string | AXIOMS 
| BANG | BIMP | BOOLEAN  | BREAKPOINT  | BYTE 
| CASE | CATCH | CHAR | CLASS | CLS | CMP 
| CMPEQ | CMPG | CMPGE | CMPGT | CMPL | CMPLE | CMPLT | CMPNE 
| COLON | COLON_EQUALS | COMMA | CONSTRUCTOR
| DASHV | DEFAULT | DEFINE| DIV | DOT | DOUBLE 
| EMP | EMPRULE | END | ENSURES | ENTERMONITOR | ENUM | EOF| EQUALS 
| EQUIV | EXITMONITOR | EXPORT| EXPORTS| EXTENDS 
| FALSE | FINAL | FLOAT | FLOAT_CONSTANT of float | FRAME
| FROM  | FULL_IDENTIFIER of string | GARBAGE | GOTO 
| IDENTIFIER of string | IF | IMP | IMPLEMENTS  | IMPLICATION | IMPORT 
| INCONSISTENCY | INSTANCEOF  | INT | INTEGER_CONSTANT of int
| INTEGER_CONSTANT_LONG of int | INTERFACE  | INTERFACEINVOKE | INVARIANT
| L_BRACE | L_BRACKET | L_PAREN | LABEL| LEADSTO | LENGTHOF | LONG | LOOKUPSWITCH 
| MAPSTO | MINUS | MOD | MULT 
| NATIVE | NEG | NEW | NEWARRAY | NEWMULTIARRAY | NOP | NOTIN| NOTINCONTEXT | NULL | NULL_TYPE 
| OLD | OR | OROR | ORTEXT
| PLUS | PRED | PRIVATE | PROTECTED | PUBLIC | PUREGUARD| PURERULE
| QUESTIONMARK | QUOTE | QUOTED_NAME of string
| R_BRACE | R_BRACKET | R_PAREN  | REQUIRES | RET | RETURN | REWRITERULE | RULE
| SEMICOLON | SHL | SHORT | SHR | SOURCE_POS_TAG | SOURCE_POS_TAG_CLOSE | SPECIALINVOKE 
| SPECIFICATION | SPECTEST | STATIC | STATICINVOKE | STRICTFP | STRING_CONSTANT of string | SYNCHRONIZED 
| TABLESWITCH   | THROW  | THROWS | TO | TRANSIENT | TRUE
| UNDERSCORE | UNKNOWN | USHR 
| VDASH | VIRTUALINVOKE | VOID | VOLATILE 
| WAND | WHERE | WITH | WITHOUT
| XOR 


module type JimTokenS = Camlp4.Sig.Token with type t = jim_token
  
module Token = struct
  open Format
  module Loc = Loc
  type t = jim_token
  type token = t

  let sf = Printf.sprintf

  let to_string k = match k with 
  (*BACHLE: TODO*)
	VOID -> "VOID"
	| _-> "TODO..."


  let print ppf x = pp_print_string ppf (to_string x)

  let match_keyword kwd _ = false 
    
  let extract_string t = match t with
     | _ -> "" (*BACHLE: TODO*)
     
    
  module Error = struct
    type t = string
    exception E of string
    let print = pp_print_string
    let to_string x = x
  end

  module Filter = struct
    type token_filter = (t, Loc.t) Camlp4.Sig.stream_filter

    type t =
      { is_kwd : string -> bool;
        mutable filter : token_filter }

    let mk is_kwd =
      { is_kwd = is_kwd;
        filter = (fun s -> s) }

    let filter x = fun strm -> x.filter strm

    let define_filter x f = x.filter <- f x.filter

    let keyword_added _ _ _ = ()
    let keyword_removed _ _ = ()
  end

end
module Error = Camlp4.Struct.EmptyError
