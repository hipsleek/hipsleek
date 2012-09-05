(** TRUNGTQ: this file is for testing purpose only **)


(** main function **)
let main () =
  let _ = print_endline ("--------------------------------------------") in 
  let _ = print_endline ("!!! This is testing module for cilparser !!!") in
  let _ = print_endline ("--------------------------------------------") in
  
  (* write code here *)
  let _ = Cilparser.print_helper " abc" in
  ()

let _ = 
  main ()
