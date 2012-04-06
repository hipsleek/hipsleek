{
open Sp_parser.Token
(** A signature for specialized tokens. *)
module Sig = Camlp4.Sig

module Make (Token : Sp_parser.SPTokenS) 
= struct
  module Loc = Token.Loc
  module Token = Token

  open Lexing
  

  (* Error report *)
  module Error = struct

    type t = | Illegal_character of char      
    exception E of t
    open Format
    let print ppf = function | Illegal_character c -> fprintf ppf "Illegal character (%s)" (Char.escaped c)
      
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

  let istore_char c i = Buffer.add_char c.buffer (Lexing.lexeme_char c.lexbuf i)
  let loc c = Loc.merge c.loc (Loc.of_lexbuf c.lexbuf)
  let update_loc c = { (c) with loc = Loc.of_lexbuf c.lexbuf }
  let with_curr_loc f c = f (update_loc c) c.lexbuf
  let shift n c = { (c) with loc = Loc.move `both n c.loc }
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
}
    
  let newline = ('\010' | '\013' | "\013\010")
  let blank = [' ' '\009' '\012']
  let alpha = ['a'-'z' 'A'-'Z' '\223'-'\246' '\248'-'\255' '_']
  let identchar = ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '0'-'9']
  let identseq = alpha identchar* 
  let ident = (identseq | identseq ''') ('.' identseq)* 
  
rule tokenizer file_name = parse
  | newline                            { update_loc file_name None 1 false 0; tokenizer file_name lexbuf }
  | blank+                                                  { tokenizer file_name lexbuf }
  | ',' { COMMA }
  | ')' { CPAREN }
  | "." { DOT }
  | "=" { EQ }
  | '#' { HASH }
  | '(' { OPAREN }
  | ';' { SEMICOLON }
  | '*' { STAR }
  | ident as idstr 
	  {
		if idstr = "_" then
		  IDENTIFIER ("Anon" ^ fresh_trailer ())
		else IDENTIFIER idstr
		}
  | eof
      { let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { pos with pos_bol  = pos.pos_bol  + 1 ;
                                        pos_cnum = pos.pos_cnum + 1 }; EOF      }
    | _ as c                 { err (Illegal_character c) (Loc.of_lexbuf lexbuf) }
 
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
