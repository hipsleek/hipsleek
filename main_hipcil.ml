(** TRUNGTQ: this file is for testing purpose only **)


(** main function **)
let mainHipcil () =
  let _ = print_endline ("---------------------------") in 
  let _ = print_endline ("!!! This is main_hipcil !!!") in
  let _ = print_endline ("---------------------------") in
  
  (* write code here *)
  let _ = Hipcil.print_helper " abc" in
  ()

let _ = 
  mainHipcil()
