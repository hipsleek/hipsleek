{
  open Rlparser
}

let alpha = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let id = alpha(alpha|digit)*
let intnum = digit+
let whitespace = [' ' '\t']

rule tokenizer = parse
    "or" { OR }
  | "and" { AND }
  | "impl" { IMPLY }
  | "all" { FORALL }
  | "ex" { EXISTS }
  | "true" { TRUE }
  | "false" { FALSE }
  | "**" { POW }
  | ',' { COMMA }
  | ')' { CPAREN }
  | '(' { OPAREN }
  | '=' { EQ }
  | "<>" { NEQ }
  | '>' { GT }
  | ">=" { GTE }
  | '<' { LT }
  | "<=" { LTE }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { STAR }
  | '$' { ENDF }
  | intnum as numstr { INT_LIT (int_of_string numstr) }
  | id as idstr { ID idstr }
  | whitespace { tokenizer lexbuf }

