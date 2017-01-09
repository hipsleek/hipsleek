(* arguments/flags that might be used both by sleek and hip *)
(* arguments/flags used only by hip *)	
let run_specific_arguments = [ 
        ("-n", Arg.String Globals.set_number_exec, "The number of execution");
	("-gent", Arg.String Globals.set_do_generate_test,"Generate tests with provided NUMBER");
	("-imp", Arg.Set Globals.use_imp, "Generate imperative (subtitute 1=one,4=four) inputs");
        ("-boogie", Arg.Set Globals.use_boogie, "Generate boogie inputs");
	("-frama-c", Arg.Set Globals.use_frama_c, "Generate Frama-C inputs");
        ("-prog-if-else", Arg.Set Globals.if_else, "Generate the ELSE branch additionally");
        ("-run-boogie", Arg.Set Globals.run_boogie, "Run Z3 with boogie inputs");
        ("-tp", Arg.String Globals.set_tp,"Collect result");
				("-sp", Arg.String Globals.set_sp,"Number of Spring tests");
        ("-dir", Arg.String Globals.set_dir, "Directory of logs")
  ] 

(* all hip's arguments and flags *)	
let run_arguments = run_specific_arguments 
