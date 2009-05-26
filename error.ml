(*
  Created 22-Feb-2006

  For error handling
*)

open Globals

type error = { error_loc : loc;
			   error_text : string }

(*
let all_errors : error list ref = ref []

let add_error e = all_errors := e :: !all_errors
*)

let report_error e =
  print_string ("\nFile \"" ^ e.error_loc.start_pos.Lexing.pos_fname 
				^ "\", line " ^ (string_of_int e.error_loc.start_pos.Lexing.pos_lnum) ^", col "^
				(string_of_int (e.error_loc.start_pos.Lexing.pos_cnum - e.error_loc.start_pos.Lexing.pos_bol))^ ": "
				^ e.error_text ^ "\n");flush stdout;
  failwith "Error detected"
