{
  open Ocparser

(*  let ovar_id_table = ref (Hashtbl.create 100 ) *)

  let incr_linenum file_name lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- 
	{ pos with
	    Lexing.pos_fname = file_name;
	    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
	    Lexing.pos_bol = pos.Lexing.pos_cnum;
	}

  let primed_str = "PRMD"
  
  let primed_length = String.length primed_str

}

let alpha = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let intnum = digit+
let fnum = digit*('.')digit+
let ovaridmarker = '$'
let ovarid = ovaridmarker(alpha)(alpha | digit)*
let whitespace = [' ' '\t']

rule tokenizer file_name = parse
  | "#" { line_comment file_name lexbuf }
  | '&' { AND }
  | "&&" { AND }
  | "and" { AND }
  | '}' { CBRACE }
  | ':' { COLON }
  | ',' { COMMA }
  | ')' { CPAREN }
  | ']' { CSQUARE }
  | "." { DOT }
  | "=" { EQ }
  | "==" { EQEQ }
  | "exists" { EXISTS }
  | "Exists" { EXISTS }
  | "false" { FALSE }
  | "FALSE" { FALSE }
  | "forall" { FORALL }
  | "Forall" { FORALL }
  | '>' { GT }
  | ">=" { GTE }
  | '<' { LT }
  | "<=" { LTE }
  | "-" { MINUS }
  | "!=" { NEQ }
  | "not" { NOT }
  | '{' { OBRACE }
  | '(' { OPAREN }
  | '[' { OSQUARE }
  | '|' { OR }
  | "||" { OR }
  | "or" { OR }
  | '+' { PLUS }
  | ';' { SEMICOLON }
  | '*' { TIMES }
  | "true" { TRUE }
  | "TRUE" { TRUE } 
  | "union" { UNION }
  | intnum as numstr { ICONST (int_of_string numstr) }
  | alpha(alpha | digit)* as idstr { 
	  let n = String.length idstr in
		if n > primed_length then
		  let tmp = String.sub idstr (n - primed_length) primed_length in
			if tmp = primed_str then
			  IDPRIMED (String.sub idstr 0 (n - primed_length))
			else
			  ID idstr
		else
		  ID idstr 
	}
  | whitespace { tokenizer file_name lexbuf }
  | '\n' { incr_linenum file_name lexbuf; tokenizer file_name lexbuf }
  | '\r' { incr_linenum file_name lexbuf; tokenizer file_name lexbuf }
  | "\r\n" { incr_linenum file_name lexbuf; tokenizer file_name lexbuf }
  | eof { EOF }

and line_comment file_name = parse
  | '\r' | '\n' | "\r\n" { incr_linenum file_name lexbuf; tokenizer file_name lexbuf }
  | _ { line_comment file_name lexbuf }
