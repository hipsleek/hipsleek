{
  open Z3mparser
}

let alpha = ['a'-'z' 'A'-'Z' '_' '!']
let digit = ['0'-'9']
let dot = '.'
let id = alpha(alpha|digit)*
let intnum = digit+
let floatnum = (digit+)dot(digit*)
let whitespace = [' ' '\t' '\n']

rule tokenizer = parse
    "model" { MODEL }
  | '(' { OPAREN }
  | ')' { CPAREN }
  | "define-fun" { DEFFUN }
  | "to_int" { TOINT }
  | "Int" { INT }
  | '-' { MINUS }
  | '/' { DIV }
  | '*' { MULT }
	| eof { EOF }
  | intnum as numstr { INT_LIT (int_of_string numstr) }
  | floatnum as numstr { FLOAT_LIT (float_of_string numstr) }
  | id as idstr { ID idstr }
  | whitespace { tokenizer lexbuf }


