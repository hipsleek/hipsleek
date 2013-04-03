{
open Globals
open Exc.ETABLE_NFLOW
open Lexing

open Jimtoken
(** A signature for specialized tokens. *)
module Sig = Camlp4.Sig

module Make (Token : JimTokenS) 
= struct
  module Loc = Token.Loc
  module Token = Token

  open Lexing
  

  (* Error report *)
  module Error = struct

    type t =
     | Illegal_character of char
     | Unterminated_comment

    exception E of t

    open Format

    let print ppf =
      function
      | Illegal_character c -> fprintf ppf "Illegal character (%s)" (Char.escaped c)
      | Unterminated_comment -> fprintf ppf "Comment not terminated"
     

    let to_string x =
      let b = Buffer.create 50 in
      let () = bprintf b "%a" print x in Buffer.contents b
  end;;

  let module M = Camlp4.ErrorHandler.Register(Error) in ()

  open Error

  type context =
  { loc        : Loc.t    ;
    in_comment : bool     ;
    lexbuf     : lexbuf   ;
    buffer     : Buffer.t }

  let default_context lb =
  { loc        = Loc.ghost ;
    in_comment = false     ;
    lexbuf     = lb        ;
    buffer     = Buffer.create 256 }

  (* To buffer string literals *)

  let store c = Buffer.add_string c.buffer (Lexing.lexeme c.lexbuf)
  let istore_char c i = Buffer.add_char c.buffer (Lexing.lexeme_char c.lexbuf i)
  let buff_contents c =
    let contents = Buffer.contents c.buffer in
    Buffer.reset c.buffer; contents

  let loc c = Loc.merge c.loc (Loc.of_lexbuf c.lexbuf)
  let is_in_comment c = c.in_comment
  let in_comment c = { (c) with in_comment = true }
  let set_start_p c = c.lexbuf.lex_start_p <- Loc.start_pos c.loc
  let move_start_p shift c =
    let p = c.lexbuf.lex_start_p in
    c.lexbuf.lex_start_p <- { (p) with pos_cnum = p.pos_cnum + shift }

  let update_loc c = { (c) with loc = Loc.of_lexbuf c.lexbuf }
  let with_curr_loc f c = f (update_loc c) c.lexbuf
  let parse_nested f c =   with_curr_loc f c;   set_start_p c;    buff_contents c
  let shift n c = { (c) with loc = Loc.move `both n c.loc }
  let store_parse f c = store c ; f c c.lexbuf
  let parse f c = f c c.lexbuf
  
  (* Update the current location with file name and line number. *)

  let update_loc c file line absolute chars =
    let lexbuf = c.lexbuf in
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with
                  | None -> pos.pos_fname
                  | Some s -> s  in
    lexbuf.lex_curr_p <- { pos with
      pos_fname = new_file;
      pos_lnum = if absolute then line else pos.pos_lnum + line;
      pos_bol = pos.pos_cnum - chars;
    }

  let err error loc = raise(Loc.Exc_located(loc, Error.E error))

  let warn error loc = Format.eprintf "Warning: %a: %a@." Loc.print loc Error.print error
	
 (*==========================================================================================*)
	type error =
  | Illegal_character of char
  | Unterminated_comment

  exception Error of error * Lexing.lexbuf
  
  let nest_depth = ref 0
  let nest_start_pos = ref dummy_pos
  let nest x =
    nest_depth := !nest_depth + 1; nest_start_pos := (x.lex_curr_p)
  let unnest x = 
    nest_depth := !nest_depth - 1; (!nest_depth)!=0 
  
  
  let error_message e lb = 
    match e with 
      Illegal_character c -> 
        Printf.sprintf "Illegal character %c found at line %d character %d.\n" 
  	c 
  	lb.lex_curr_p.pos_lnum 
  	(lb.lex_curr_p.pos_cnum - lb.lex_curr_p.pos_bol)
    | Unterminated_comment -> Printf.sprintf "Unterminated comment started at line %d character %d in %s.\n"
  	!nest_start_pos.pos_lnum 
  	(!nest_start_pos.pos_cnum  - !nest_start_pos.pos_bol)
  	lb.lex_curr_p.pos_fname
 
 let kwd_or_else = 
  let keyword_table = Hashtbl.create 53 in
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok) [
    "Abduction", ABDUCTION;
    "abstract", ABSTRACT;
    "abstraction", ABSRULE;
    "andalso", ANDALSO;
    "annotation", ANNOTATION;
    "as", AS;
    "assign", ASSIGN;
    "axioms", AXIOMS;
    "boolean", BOOLEAN;
    "breakpoint", BREAKPOINT;
    "byte", BYTE;
    "case", CASE;
    "catch", CATCH;
    "char", CHAR;
    "class", CLASS;
    "cls", CLS;
    "constructor", CONSTRUCTOR;
    "define", DEFINE;
    "double", DOUBLE;
    "Emp", EMP;
    "emprule", EMPRULE;
    "end", END;
    "ensures", ENSURES;
    "enum", ENUM;
    "equiv", EQUIV;
    "export", EXPORT;
    "exports", EXPORTS;
    "extends", EXTENDS;
    "False", FALSE;
    "final", FINAL;
    "float", FLOAT;
    "Frame", FRAME;
    "from", FROM;
    "goto", GOTO;
    "if", IF;
    "implements", IMPLEMENTS;
    "Implication", IMPLICATION;
    "import", IMPORT;
    "Inconsistency", INCONSISTENCY;
    "instanceof", INSTANCEOF;
    "int", INT;
    "interface", INTERFACE;
    "interfaceinvoke", INTERFACEINVOKE;
    "label", LABEL;
    "lengthof", LENGTHOF;
    "long", LONG;
    "lookupswitch", LOOKUPSWITCH;
    "native", NATIVE;
    "new", NEW;
    "newarray", NEWARRAY;
    "newmultiarray", NEWMULTIARRAY;
    "nop", NOP;
    "notin", NOTIN;
    "notincontext", NOTINCONTEXT;
    "pureguard", PUREGUARD;
    "null", NULL;
    "null_type", NULL_TYPE;
    "old", OLD;
    "or", ORTEXT;
    "private", PRIVATE;
    "protected", PROTECTED;
    "public", PUBLIC;
    "purerule", PURERULE;
    "requires", REQUIRES;
    "return", RETURN;
    "rewrite", REWRITERULE;
    "rule", RULE;
    "short", SHORT;
    "specialinvoke", SPECIALINVOKE;
    "Specification", SPECIFICATION;
    "SpecTest", SPECTEST; 
    "static", STATIC;
    "staticinvoke", STATICINVOKE;
    "strictfp", STRICTFP;
    "synchronized", SYNCHRONIZED;
    "tableswitch", TABLESWITCH;
    "throw", THROW;
    "throws", THROWS;
    "to", TO;
    "transient", TRANSIENT;
    "True", TRUE;
    "unknown", UNKNOWN;
    "virtualinvoke", VIRTUALINVOKE;
    "void", VOID;
    "volatile", VOLATILE;
    "where", WHERE;
    "with", WITH;
    "without", WITHOUT;
  ];
  fun d s ->
  try Hashtbl.find keyword_table s with Not_found -> d
	
	open Format

  let report_error = function
    | Illegal_character c ->
        Format.printf  "Illegal character (%s)@\n" (Char.escaped c)
    | Unterminated_comment ->
        Format.printf "Comment not terminated@\n"

}
  
  
(* ====================================================================== *)

(* translation from Helpers's section in jimple.scc  *)

	let  all = _

	let  dec_digit = ['0' - '9']
	let  dec_nonzero = ['1' - '9']
	let  dec_constant = dec_digit+

	let  hex_digit = dec_digit | ['a' - 'f'] | ['A' - 'F']
  let  hex_constant = '0' ('x' | 'X') hex_digit+
  
  let  oct_digit = ['0' - '7']
  let  oct_constant = '0' oct_digit+
  	
  let  quote = '\''
  
  let  escapable_char = '\\' | ' ' | quote | '.' | '#' | '\"' | 'n' | 't' | 'r' | 'b' | 'f'
  let  escape_code = 'u' hex_digit hex_digit hex_digit hex_digit
  let  escape_char = '\\' (escapable_char | escape_code)  
  
  let  not_cr_lf = [ ^ '\010' '\013']
  let  not_star = [ ^ '*']
  let  not_star_slash = [^ '*' '/']
  
  let  alpha_char = ['a' - 'z'] | ['A' - 'Z']
    
  let  simple_id_char = alpha_char | dec_digit | '_' | '$'
  
  let  first_id_char = alpha_char | '_' | '$'
    
  let  quotable_char = [^ '\010' '\013' '\'']
  
  let  string_char = escape_char | ['\000' - '\033'] | ['\035' - '\091'] | ['\093' - '\127']   
  
  let  line_comment = "//" not_cr_lf*
  (*let  long_comment = "/*" not_star* '*'+ (not_star_slash not_star* '*'+)* '/'*)
  
  let  blank = (' ' | '\009')+  
  let  ignored_helper = (blank | line_comment)+
  
  let  newline = ('\013' | '\010' | "\010\013")
  
  let full_identifier =
         ((first_id_char | escape_char) (simple_id_char | escape_char)* '.')+  '$'? (first_id_char | escape_char) (simple_id_char | escape_char)*
  
  let identifier = 
        (first_id_char | escape_char) (simple_id_char | escape_char)* | "<clinit>" | "<init>"
  
  (*let identifier =
      (first_id_char | escape_char) (simple_id_char | escape_char)* | '<' (first_id_char | escape_char) (simple_id_char | escape_char)* '>'*)
  
  let quoted_name = quote quotable_char+ quote
  
  let at_identifier = 
    '@' (
      ("parameter" dec_digit+ ':') 
      | "this" ':' 
      | "caughtexception" 
      | "caller") 
  	
  let integer_constant = (dec_constant | hex_constant | oct_constant) 'L'? 
  
  let float_constant = ((dec_constant '.' dec_constant) (('e'|'E') ('+'|'-')? dec_constant)? ('f'|'F')?)  | ('#' (('-'? "Infinity") | "NaN") ('f' | 'F')? ) 
  
	(* Translation of section Tokens of jimple.scc *)

  rule token fn = parse
    | newline { Lexing.new_line lexbuf; token fn lexbuf }
    | "/*Source Line Pos Tag" { SOURCE_POS_TAG }
    | "*/" { SOURCE_POS_TAG_CLOSE }
    | "/*" { nest lexbuf; comment lexbuf; token fn lexbuf } 
    | ignored_helper  { token fn lexbuf }
    | "," { COMMA }
    | "{" { L_BRACE }
    | "}" { R_BRACE }
    | ";" { SEMICOLON }
    | "[" { L_BRACKET }
    | "]" { R_BRACKET }
    | "(" { L_PAREN }
    | ")" { R_PAREN }
    | ":" { COLON}
    | "." { DOT }
    | "'" { QUOTE }
    | ":=" { COLON_EQUALS }
    | "=" { EQUALS }
    | "&" { AND }
    | "|" { OR }
    | "||" { OROR }
    | "|->" { MAPSTO }
    | "^" { XOR }
    | "%" { MOD }
    | "cmp" { CMP }
    | "cmpl" { CMPL }
    | "cmpg" { CMPG }
    | "==" { CMPEQ }
    | "!=" { CMPNE }
    | ">" { CMPGT }
    | ">=" { CMPGE }
    | "=>" { IMP }
    | "<=>" { BIMP }
    | "<" { CMPLT }
    | "<=" { CMPLE }
    | "<<" { SHL }
    | ">>" { SHR }
    | ">>>" { USHR }
    | "+" { PLUS }
    | "-" { MINUS }
    | "*" { MULT }
    | "-*" { WAND }
    | "/" { DIV }
    | "?" { QUESTIONMARK }
    | "!" { BANG }
    | "|-" { VDASH }
    | "-|" { DASHV }
    | "~~>" {LEADSTO}
    | eof { EOF }
  
    | at_identifier as s {  kwd_or_else (AT_IDENTIFIER s) s }
    | full_identifier as s {  kwd_or_else (FULL_IDENTIFIER s) s }
    | quoted_name as s { kwd_or_else (QUOTED_NAME s) s }
    | identifier as s {  kwd_or_else (IDENTIFIER s) s }
  
    | integer_constant {
        let s=Lexing.lexeme lexbuf in
        if (String.get s (String.length s -1)) = 'L' then
  	 INTEGER_CONSTANT_LONG(int_of_string(String.sub s 0 (String.length s - 1)))
        else 
  	 INTEGER_CONSTANT(int_of_string(s))}
  
    | float_constant   { FLOAT_CONSTANT(float_of_string(Lexing.lexeme lexbuf))}
  
    (* FIXME: What is the right lexing of string constants? *)
    | '"' (string_char* as s) '"' { STRING_CONSTANT s }
    | _ { failwith (error_message (Illegal_character ((Lexing.lexeme lexbuf).[0])) lexbuf)}
  and comment = parse 
    | "/*"  { nest lexbuf; comment lexbuf }
    | "*/"  { if unnest lexbuf then comment lexbuf }
    | newline  { Lexing.new_line lexbuf; comment lexbuf }
    | eof      { failwith (error_message Unterminated_comment lexbuf)}
    | _     { comment lexbuf; }
  	
{	
	 let lexing_store s buff max =
    let rec self n s =
      if n >= max then n
      else
        match Stream.peek s with
        | Some x ->
            Stream.junk s;
            buff.[n] <- x;
            succ n
        | _ -> n
    in
    self 0 s

  let from_context c =
    let next _ =
      let tok = with_curr_loc token c in
      let loc = Loc.of_lexbuf c.lexbuf in
      Some ((tok, loc))
    in Stream.from next

  let from_lexbuf lb =
    let c = { (default_context lb) with  loc = Loc.of_lexbuf lb}
    in from_context c

  let setup_loc lb loc =
    let start_pos = Loc.start_pos loc in
    lb.lex_abs_pos <- start_pos.pos_cnum;
    lb.lex_curr_p  <- start_pos

  let from_string loc str =
    let lb = Lexing.from_string str in
    setup_loc lb loc;
    from_lexbuf lb

  let from_stream loc strm =
    let lb = Lexing.from_function (lexing_store strm) in
    setup_loc lb loc;
    from_lexbuf lb
		
	let mk () loc strm = from_stream loc strm
end
}


