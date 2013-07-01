(* arguments/flags that might be used both by sleek and hip *)
(* arguments/flags used only by hip *)	
let run_specific_arguments = [ 
  ("-n", Arg.String Globals.set_number_exec, 
   "The number of execution");
	("-genif", Arg.String Globals.set_do_generate_test, 
   "Automatically generate tests for if with provided number");
	("-genif-el", Arg.String Globals.set_generate_with_else, 
   "Automatically generate tests for if_else with provided number");
	("-gen-if-range",Arg.Unit Globals.set_generate_if_range,
   "Automatically generate tests for if with provided number of: min max off-set");
	("-gen-ifel-range",Arg.Unit Globals.set_generate_if_else_range,
   "Automatically generate tests for if_else with provided number of: min max off-set");
	("-boogie", Arg.Set Globals.use_boogie, "generate boogie inputs");
	("-run-boogie", Arg.Set Globals.run_boogie, "Run boogie inputs");
	("-frama-c", Arg.Set Globals.use_frama_c, "generate Frama-C inputs");
  ] 

(* all hip's arguments and flags *)	
let run_arguments = run_specific_arguments 
