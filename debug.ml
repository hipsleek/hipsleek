
let debug_on = ref false
let devel_debug_on = ref false

(* debugging facility for user *)

let string_of_pos pos =
  pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.Lexing.pos_lnum) ^ ": "

let print s = if !debug_on then (print_string ("\n\n!!!" ^ s); flush stdout) else ()

let pprint msg pos = 
  let tmp = pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.Lexing.pos_lnum) ^ ": " ^ msg in
	print tmp

(* system development debugging *)
let devel_print s = if !devel_debug_on then (print_string ("\n\n!!!" ^ s); flush stdout) else ()

let devel_pprint msg pos = 
  let tmp = pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.Lexing.pos_lnum) ^ ": " ^ msg in
	devel_print tmp

let print_info prefix str pos = 
  let tmp = "\n" ^ prefix ^ ":" ^ pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.Lexing.pos_lnum) ^ ": " ^ str ^ "\n" in
	print_string tmp; flush stdout
