{
(* Modified from https://github.com/mmjb/T2/blob/master/src/absflex.fsl *)

(* // Copyright (c) Microsoft Corporation                                          *)
(* //                                                                              *)
(* // All rights reserved.                                                         *)
(* //                                                                              *)
(* // Permission is hereby granted, free of charge, to any person obtaining a copy *)
(* // of this software and associated documentation files (the ""Software""), to   *)
(* // deal in the Software without restriction, including without limitation the   *)
(* // rights to use, copy, modify, merge, publish, distribute, sublicense, and/or  *)
(* // sell copies of the Software, and to permit persons to whom the Software is   *)
(* // furnished to do so, subject to the following conditions:                     *)
(* //                                                                              *)
(* // The above copyright notice and this permission notice shall be included      *)
(* // in all copies or substantial portions of the Software.                       *)
(* //                                                                              *)
(* // THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR   *)
(* // IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,     *)
(* // FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL      *)
(* // THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER   *)
(* // LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING      *)
(* // FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER          *)
(* // DEALINGS IN THE SOFTWARE.                                                    *)

open Iparser
open Lexing
  
let comment_level = ref 0

let update_loc lexbuf line absolute chars =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with
    pos_lnum = if absolute then line else pos.pos_lnum + line;
    pos_bol = pos.pos_cnum - chars;
  }
}

let digit = ['0'-'9']
let letdig = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '.' ]
let letdigpling = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '!']
let alphlet = ['A'-'Z' 'a'-'z' '_' '$' '\'' ]
let whitespace = [' ' '\009' '\012']
let newline = ('\010' | '\013' | "\013\010")

rule tokenizer = parse
  | newline { update_loc lexbuf 1 false 0; tokenizer lexbuf }
  | "//" { line_comment lexbuf }
  | "/*" { comment_level := 0; comment lexbuf }
  | whitespace { tokenizer lexbuf }

  | "TO" { TO }
  | "FROM" { FROM }
  | "CUTPOINT" { CUTPOINT }
  | "nondet" { NONDET }
  | "NONDET" { NONDET }
  | "SHADOW" { SHADOW }
  | "START" { START }
  | "AT" { AT }

  | ',' { COMMA }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '+' { PLUS }
  | '-' { MINUS }
  | "*" { STAR }
  | '/' { DIV }
  | '!' { NOT }
  | '%' { REM }
  | ';' { SEMICOLON }
  | ":" { COLON }
  | "<" { LT }
  | ">" { GT }
  | "<=" { LE }
  | ">=" { GE }
  | "==" { EQ }
  | "=" { EQ }
  | "!=" { NE }
  | ":=" { ASSIGN }
  | "assume" { ASSUME }
  | "&&" { AND_OP }
  | "||" { OR_OP }
  | (digit)+ as numstr { Num (int_of_string numstr) }
  | (alphlet)(letdig)*('!' letdig+)* as idstr { Id idstr }
  | '"'[^'\n''"']*'"' as strstr { String (String.sub strstr 1 ((String.length strstr) - 2)) }
  | eof { EOF }

and line_comment = parse
  | newline 
  | eof { update_loc lexbuf 1 false 0; tokenizer lexbuf }
  | _ { line_comment lexbuf }

and comment = parse
  | "*/" 
    { 
      if !comment_level = 0 then
        tokenizer lexbuf 
      else begin
        comment_level := !comment_level - 1;
        comment lexbuf end
    }
  | "/*" 
    {
      comment_level := !comment_level + 1;
      comment lexbuf
    }
  | newline { update_loc lexbuf 1 false 0; comment lexbuf }
  | _  { comment lexbuf }