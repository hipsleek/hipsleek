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

(* let report_error e = *)
(*   (match !proving_loc with *)
(*     | Some p -> *)
(*           Printf.printf "\nLast Proving Location: File \"%s\", line %d, col %d " *)
(*                p.start_pos.Lexing.pos_fname *)
(*                p.start_pos.Lexing.pos_lnum *)
(*               (p.start_pos.Lexing.pos_cnum - p.start_pos.Lexing.pos_bol) *)
(*     | None -> ()); *)
(*   Printf.printf "\nERROR: File \"%s\", line %d, col %d : %s \n" *)
(*       e.error_loc.start_pos.Lexing.pos_fname *)
(*       e.error_loc.start_pos.Lexing.pos_lnum *)
(*       (e.error_loc.start_pos.Lexing.pos_cnum - e.error_loc.start_pos.Lexing.pos_bol) *)
(*       e.error_text; *)
(*   flush stdout; *)
(*   failwith e.error_text *)

  
let report_error e =
 (if post_pos#is_avail then
       Printf.printf "\nContext of Verification Failure: %s"            
           post_pos#string_of);
 (if proving_loc#is_avail then
       Printf.printf "\nLast Proving Location: %s\n"
           proving_loc#string_of);
 (Printf.printf "\nERROR: at %s \nMessage: %s\n " 
    (string_of_loc e.error_loc)
    e.error_text);
  flush stdout;
  failwith e.error_text

let report_warning e =
  if (not !suppress_warning_msg) then begin
    Printf.printf "\nWARNING: %s:%s\n"
        (string_of_loc e.error_loc)
        e.error_text;
    flush stdout
  end else ()
  (* failwith "Error detected : error.ml B" *)
