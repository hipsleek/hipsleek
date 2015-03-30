#include "xdebug.cppo"
(*
  Created 22-Feb-2006

  For error handling
*)

(* open Globals *)
open VarGen

type error = {
  error_loc : loc;
  error_text : string
}

(*exception Theorem_prover of (string * string) *)
 exception Ppf of (error * int * int) (*Proving_pre_fails*)

 let get_error_type_str ie=
   match ie with
     | 0 -> "bind failure exception"
     | 1 -> "Proving precond failed"
     | _ -> ""

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

(* report error and don't care about the position *)
let report_error_msg (error_msg: string) =
  print_endline_q ("\nERROR MESSAGE: " ^ error_msg);
  (* flush stdout; *)
  failwith error_msg

let report_error e =
  if post_pos#is_avail then
    print_endline_q ("\nContext of Verification Failure: " ^ post_pos#string_of);
  if proving_loc#is_avail then
    print_endline_q ("\nLast Proving Location: " ^  proving_loc#string_of);
  print_endline_q ("\nERROR: at " ^ (string_of_loc e.error_loc)
                   ^ "\nMessage: " ^  e.error_text);
  (* flush stdout; *)
  failwith e.error_text

let report_no_pattern () = report_error {error_loc=no_pos; error_text="HIP/SLEEK error, unhandled pattern"}
(*asankhs: Lets not use such wording in external errors and exceptions - very poor coding, lazy programmers !!!*)

let report_error1 e s=
  print_endline_q e.error_text;
  if post_pos#is_avail then
    print_endline_q ("\nContext of Verification Failure: " ^ post_pos#string_of);
  if proving_loc#is_avail then
    print_endline_q ("\nLast Proving Location: " ^ proving_loc#string_of);
  (* flush stdout; *)
  failwith s

let report_warning e =
  if (!VarGen.suppress_warning_msg) then ()
  else if (not !VarGen.en_warning_msg) then report_error1 e "Warning->ERROR"
  else (
    print_endline_q ("\nWARNING: "
                     ^  (string_of_loc e.error_loc) ^ ":"
                     ^ e.error_text);
    (* flush stdout; *)
  )

exception Malformed_barrier of string
(*
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
      dummy_exception() ;
  end
*)
