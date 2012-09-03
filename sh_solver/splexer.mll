{
	open Spparser

	let incr_linenum file_name lexbuf =
		let pos = lexbuf.Lexing.lex_curr_p in
		lexbuf.Lexing.lex_curr_p <- { pos with
			Lexing.pos_fname = file_name;
			Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
			Lexing.pos_bol = pos.Lexing.pos_cnum;
			}
}
    
  let newline = ('\010' | '\013' | "\013\010")
  let blank = [' ' '\009' '\012']
  let alpha = ['a'-'z' 'A'-'Z' '\223'-'\246' '\248'-'\255' '_']
  let identchar = ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '0'-'9']
  let identseq = alpha identchar* 
  let ident = (identseq | identseq ''') ('.' identseq)* 
  
rule tokenizer file_name = parse
  | newline                            {incr_linenum file_name lexbuf; tokenizer file_name lexbuf }
  | blank+                                                  { tokenizer file_name lexbuf }
  | ',' { COMMA }
  | ')' { CPAREN }
  | "." { DOT }
  | "=" { EQ }
  | '#' { HASH }
  | '(' { OPAREN }
  | '*' { STAR }
  | "SAT" { SAT }
  | "IMPL"{ IMPL }
  | ident as ids {IDENTIFIER ids}
  | eof { EOF }
 
