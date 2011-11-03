(*
  Created 22-Feb-2006

  For error handling
*)

open Globals

type error = {
  error_loc : loc;
  error_text : string
}

exception Theorem_prover of (string * string)

(*
let all_errors : error list ref = ref []

let add_error e = all_errors := e :: !all_errors
*)

let report_error e =
  (match !proving_loc with
    | Some p ->
          Printf.printf "\nLast Proving Location: File \"%s\", line %d, col %d "
               p.start_pos.Lexing.pos_fname
               p.start_pos.Lexing.pos_lnum
              (p.start_pos.Lexing.pos_cnum - p.start_pos.Lexing.pos_bol)
    | None -> ());
  Printf.printf "\nERROR: File \"%s\", line %d, col %d : %s \n"
      e.error_loc.start_pos.Lexing.pos_fname
      e.error_loc.start_pos.Lexing.pos_lnum
      (e.error_loc.start_pos.Lexing.pos_cnum - e.error_loc.start_pos.Lexing.pos_bol)
      e.error_text;
  flush stdout;
  failwith e.error_text

let report_warning e =
  if (not !suppress_warning_msg) then begin
    Printf.printf "\nWARNING: File \"%s\", line %d, col %d: %s \n"
        e.error_loc.start_pos.Lexing.pos_fname
        e.error_loc.start_pos.Lexing.pos_lnum
        (e.error_loc.start_pos.Lexing.pos_cnum - e.error_loc.start_pos.Lexing.pos_bol)
        e.error_text;
    flush stdout
  end else ()
  (* failwith "Error detected : error.ml B" *)


let process_exct e=
  begin
      (match !proving_loc with
        | Some p ->
            Printf.printf "\nLast Proving Location: File \"%s\", line %d, col %d "
                p.start_pos.Lexing.pos_fname
                p.start_pos.Lexing.pos_lnum
                (p.start_pos.Lexing.pos_cnum - p.start_pos.Lexing.pos_bol)
        | None -> ());
      (match e with
        | Theorem_prover (prover_name, msg) ->
            Printf.printf "\nException:\"%s\",\n message: \"%s\" \n"
                ("theorem prover: " ^ prover_name) msg
        | _ -> print_endline (Printexc.to_string e)
      );
      Printexc.print_backtrace stdout;
      dummy_exception() ;
  end
