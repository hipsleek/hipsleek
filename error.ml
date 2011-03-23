(*
  Created 22-Feb-2006

  For error handling
*)

open Globals

type error = {
  error_loc : loc;
  error_text : string
}

(*
let all_errors : error list ref = ref []

let add_error e = all_errors := e :: !all_errors
*)

let report_error e =
  Printf.printf "\nFile \"%s\", line %d, col %d : %s \n"
      e.error_loc.start_pos.Lexing.pos_fname
      e.error_loc.start_pos.Lexing.pos_lnum
      (e.error_loc.start_pos.Lexing.pos_cnum - e.error_loc.start_pos.Lexing.pos_bol)
      e.error_text;
  flush stdout;
  failwith "Error detected - error.ml A"

let report_warning e =
  if (not !suppress_warning_msg) then begin
    Printf.printf "\nFile \"%s\", line %d, col %d: %s \n"
        e.error_loc.start_pos.Lexing.pos_fname
        e.error_loc.start_pos.Lexing.pos_lnum
        (e.error_loc.start_pos.Lexing.pos_cnum - e.error_loc.start_pos.Lexing.pos_bol)
        e.error_text;
    flush stdout
  end else ();
  failwith "Error detected : error.ml B"
