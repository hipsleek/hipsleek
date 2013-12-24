{
  open Lpparser
}

let alpha = ['a'-'z' 'A'-'Z' '_' '!']
let digit = ['0'-'9']
let id = alpha(alpha|digit)*
let intnum = digit+
let whitespace = [' ' '\t' '\n']

rule tokenizer = parse
    "optimal" { OPTIMAL }
  | "Objective value" { OVAL }
  | '-' { MINUS }
	| eof { EOF }
  | intnum as numstr { INT_LIT (int_of_string numstr) }
  | id as idstr { ID idstr }
  | whitespace { tokenizer lexbuf }


