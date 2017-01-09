#include "xdebug.cppo"
let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

(* let source_files = ref ([] : string list) *)

let set_source_file arg = ()

let process_cmd_line () = 
  Arg.parse Scriptarguments.sleek_arguments set_source_file usage_msg;;

process_cmd_line ();;

let rec fact_x n = 
  if (n==0) then 1
  else n*(x_add_1 fact(n-2))

and fact n =
  let pr = string_of_int in
  Debug.no_1 "fact" pr pr fact_x n;;

let n = 6;;


Printf.printf ("Fact of %d = %d\n") n (x_add_1 fact n);;
