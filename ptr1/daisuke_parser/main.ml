let _ =
  try
    let file = open_in Sys.argv.(1) in
    let lexbuf = Lexing.from_channel file in
    let result = Parser.main Lexer.token lexbuf in
    print_endline (Array_pred.str_entailment result);
    flush stdout                                             
  with Lexer.Eof ->
    exit 0
