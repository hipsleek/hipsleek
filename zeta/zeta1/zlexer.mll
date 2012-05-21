{
open Ztoken

module Sig = Camlp4.Sig

module Make (Token : ZTokenS)
= struct
  module Loc = Token.Loc
  module Token = Token

  open Lexing
	
  (* Error report *)
  module Error = struct

    type t =
      | Illegal_character of char
      | Illegal_escape of string
      | Unterminated_comment
      | Unterminated_string
      | Unterminated_java
      | Comment_start
      | Comment_not_end
      | Literal_overflow of string

    exception E of t

    open Format

    let print ppf =
      function
      | Illegal_character c -> fprintf ppf "Illegal character (%s)" (Char.escaped c)
      | Illegal_escape s -> fprintf ppf "Illegal backslash escape in string or character (%s)" s
      | Unterminated_comment -> fprintf ppf "Comment not terminated"
      | Unterminated_string -> fprintf ppf "String literal not terminated"
      | Unterminated_java -> fprintf ppf "java code not terminated"
      | Literal_overflow ty -> fprintf ppf "Integer literal exceeds the range of representable integers of type %s" ty
      | Comment_start -> fprintf ppf "this is the start of a comment"
      | Comment_not_end -> fprintf ppf "this is not the end of a comment"

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

 let zeta_keywords = Hashtbl.create 100

 let comment_level = ref 0

 let _ = List.map (fun ((k,t):(string * zeta_token)) ->
	Hashtbl.add zeta_keywords k t)
	[	("let", LET);
		("axiom", AXIOM);
		("theorem", THEOREM);
		("be", BE);
		("such", SUCH);
		("that", THAT);
		("induction", INDUCTION);
		("exists", EXISTS);
		("forall", FORALL);
		("false", FALSE);
		("true", TRUE);
	]
}
  
let newline = ('\010' | '\013' | "\013\010")
let blank = [' ' '\009' '\012']
let alpha = ['a'-'z' 'A'-'Z' '\223'-'\246' '\248'-'\255' '_']
let identchar = ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '0'-'9']
let ident = alpha identchar*
let digitseq = ['0'-'9'] ['0'-'9' '_']*
let int_literal = digitseq
	
rule tokenizer file_name = parse
  | newline { update_loc file_name None 1 false 0; 
			tokenizer file_name lexbuf }
  | blank+ { tokenizer file_name lexbuf }
  | int_literal as i {
			try
				NUMERAL (int_of_string i)
    	with
				Failure _ -> err (Literal_overflow "int") (Loc.of_lexbuf lexbuf) }
  | "/*" { comment_level := 0; comment file_name lexbuf }
  | "//" { line_comment file_name lexbuf }
  | "/*/"
        { warn Comment_start (Loc.of_lexbuf lexbuf);   
          comment_level := 0;
          comment file_name lexbuf}
  | "*/"
        { warn Comment_not_end (Loc.of_lexbuf lexbuf);
          move_start_p (-1) file_name; STAR }
  | '&' { AND }
  | '}' { CBRACE }
  | ':' { COLON }
  | ',' { COMMA }
	| '.' { DOT }
  | ')' { CPAREN }
  | ']' { CSQUARE }
	| ":=" { DEFEQ }
  | "=" { EQ }
	| "->" { RIGHTARROW }
  | "<->" { LEFTRIGHTARROW }
  | '>' { GT }
  | ">=" { GTE }
  | '<' { LT }
  | "<=" { LTE }
  | "-" { MINUS }
  | "!=" { NEQ }
  | "!" { NOT }
  | '{' { OBRACE }
  | '(' { OPAREN }
  | '|' { OR }
  | '[' { OSQUARE }
  | '+' { PLUS }
  | ';' { SEMICOLON }
  | '*' { STAR }
  | '/' { DIV }
	| '%' { MOD }
  | ident as idstr
	  {
		  try 
(*				let _ = print_endline ("id::"^idstr) in*)
				Hashtbl.find zeta_keywords idstr
		  with
				| _ -> IDENTIFIER idstr
	  }
  | eof
      { let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { pos with pos_bol  = pos.pos_bol  + 1 ;
                                        pos_cnum = pos.pos_cnum + 1 }; EOF      }
  | _ as c { err (Illegal_character c) (Loc.of_lexbuf lexbuf) }

and comment file_name = parse
  | "*/" { 
	  if !comment_level = 0 then
		tokenizer file_name lexbuf 
	  else begin
		comment_level := !comment_level - 1;
		comment file_name lexbuf
	  end	}
  | "/*" {
	  comment_level := !comment_level + 1;
	  comment file_name lexbuf}
  | newline { update_loc file_name None 1 false 0; comment file_name lexbuf }
  | _  { comment file_name lexbuf }

and line_comment file_name = parse
  | newline { update_loc file_name None 1 false 0; tokenizer file_name lexbuf }
  | _ { line_comment file_name lexbuf } 
  
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
      let tok = with_curr_loc tokenizer c in
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
