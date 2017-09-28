let _ =
    let file_list = Sys.readdir Sys.argv.(1) in
    print_endline "pred_prim Aseg<start:int, end:int>.
                   pred_prim AsegNE<start:int, end:int>.
                   pred_prim Elem<start:int,value:int>.";

    Array.iteri
      (fun i file_name->
        let full_name = Sys.argv.(1) ^ file_name in
        print_endline ("// " ^ (string_of_int (i+1)));
        print_endline ("// " ^ full_name);
        let file = open_in full_name in
        let lexbuf = Lexing.from_channel file in
        try
          let (result, entailment) = Parser.main Lexer.token lexbuf in
          print_endline (Array_pred.str_entailment entailment);
          print_endline ("expect " ^ result ^ ".");
          print_endline "";
          flush stdout
        with _ -> print_endline "expection")
      file_list

