{
  open Parser
  exception Eof
  let comment = ref false;;
}




rule token = parse
    [' ' '\t' '\n'] { token lexbuf}
   | "|-" { IMPLY }
   | eof { EOF }
   | "Ex" { EXIST }
   | '.' { DOT }
   | "//" { comment lexbuf }
   | "->" { POINTTO }
   | "Array" {ARRAY}
   | ',' { COMMA }
   | '(' { LPAREN }
   | ')' { RPAREN }
   | '*' { STAR }
   | '&' { AND }
   | '|' { VBAR }
   | '=' { EQUAL }
   | "=/" { NEQ }
   | '<' { LT }
   | "<=" { LTE }
   | '>' { GT }
   | ">=" { GTE }
   | '+' { ADD }
   | '-' { MINUS }
   | ['a'-'z']['a'-'z' '0'-'9']* as name { VAR name }
   | ['0'-'9']|['1'-'9']['0'-'9']+ as num { CONST (int_of_string num) }


   and comment = parse
     "RESULT:Valid" { VALID }
   | "RESULT:Invalid" { INVALID }
   | ['\n'] { token lexbuf }
   | _ { comment lexbuf }
