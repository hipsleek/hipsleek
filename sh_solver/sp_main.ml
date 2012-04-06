module M = Lexer.Make(Token.Token)

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let source_file = ref ("" : string)
let print_version_flag = ref false
let trace_failure = ref false
let set_source_file arg =  source_file := arg

let print_version () =
  print_endline ("TREE SHARE PROVER");
  print_endline ("Version 1.0");
  print_endline ("THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.");
  print_endline ("IT IS FREE FOR NON-COMMERCIAL USE");
  print_endline ("Copyright @ Cristian Gherghina @ NUS")
 
let parse_file_full file_name = 
  let org_in_chnl = open_in file_name in
    try
      (*let prog = Parser.parse_sleek file_name (Stream.of_channel org_in_chnl) in*)
	  let prog = Parser.parse_eq_syst file_name (Stream.of_channel org_in_chnl) in
		  close_in org_in_chnl;
  		prog
    with
		End_of_file -> exit 0
    | M.Loc.Exc_located (l,t)->
      (print_string ((Camlp4.PreCast.Loc.to_string l)^"\n --error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
      raise t)

let solve_prog prog = ()
	  
let _ = 
  try
     Arg.parse [("-version", Arg.Set print_version_flag,"current version of software");] set_source_file usage_msg;
	 if !print_version_flag then print_version () ;
	 if !source_file = "" then print_string "Source file(s) not specified\n" ;
	 flush stdout;
	 Printexc.record_backtrace !trace_failure;
	 let prog = parse_file_full !source_file in
	 Tpdispatcher.start_prover ();
	 solve_prog prog;
	 Tpdispatcher.stop_prover ()
  with _ as e -> begin
    Tpdispatcher.stop_prover ();
    print_string "caught\n"; Printexc.print_backtrace stdout;
    print_string ("\nException occurred: " ^ (Printexc.to_string e));
    print_string ("\nError(s) detected at main \n");
  end


  
