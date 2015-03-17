#include "xdebug.cppo"
(** TRUNGTQ: this file is for testing purpose only **)


(** main function **)
let main () =
  let () = print_endline ("--------------------------------------------") in 
  let () = print_endline ("!!! This is testing module for cilparser !!!") in
  let () = print_endline ("--------------------------------------------") in
  (* write code here *)
  let cmdline = Sys.argv in
  let filename = 
    if (Array.length cmdline <= 1) then
      let () = print_endline "Error: No input file!!!" in
      let () = print_endline "        Usage: ./test_cilparser input-file-name" in
      exit 1;
    else
      cmdline.(1) in
  let cilfile = Cilparser.parse_one_file filename in
  Cilparser.process_one_file cilfile

let () = 
  main ()
