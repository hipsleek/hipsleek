(* arguments/flags that might be used both by sleek and hip *)
(* arguments/flags used only by hip *)	
let run_specific_arguments = [ 
  ("-n", Arg.String Globals.set_number_exec, 
   "The number of execution");
  ] 

(* all hip's arguments and flags *)	
let run_arguments = run_specific_arguments 
