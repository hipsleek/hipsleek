#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module F =Iformula

type transmission = Send | Receive

(* ======= base formula for session type ====== *)
(* ============================================ *)
module type Session_base = sig
  type t
  val print_session_base : t -> string
end;;

type protocol_base_formula = {
  protocol_base_formula_sender   : ident;
  protocol_base_formula_receiver : ident;
  protocol_base_formula_message  : F.formula;
} ;;

type projection_base_formula = {
  projection_base_formula_op      : transmission;
  projection_base_formula_channel : ident;
  projection_base_formula_message : F.formula;
} ;;

module Protocol_base : Session_base = struct
  type t = protocol_base_formula
  let print_session_base f = "Protocol_base: to be implemented"
end;;

module Projection_base : Session_base = struct
  type t = projection_base_formula
  let print_session_base f = "Projection_base: to be implemented"
end;;

(* ============== session type ================ *)
(* ============================================ *)
module Make_Session (Base: Session_base) = struct
  type t = Base.t

  type session =
    | SSeq  of session_seq_formula
    | SOr   of session_or_formula
    | SStar of session_star_formula
    | SBase of t

  and session_seq_formula = {
    session_seq_formula_head: session;
    session_seq_formula_tail: session;
    session_seq_formula_pos:  loc;
  }

  and session_or_formula = {
    session_seq_formula_or1: session;
    session_seq_formula_or2: session;
    session_seq_formula_pos:  loc;
  }

  and session_star_formula = {
    session_seq_formula_star1: session;
    session_seq_formula_star2: session;
    session_seq_formula_pos:  loc;
  }

  let rec print_session = function
    | SSeq s -> print_session_seq s
    | SOr s -> print_session_or s
    | SStar s -> print_session_star s
    | SBase s -> print_session_base s

  and print_session_base = Base.print_session_base

  and print_session_seq s = begin
          print_session s.session_seq_formula_head;
          Printf.printf " %s " ";;";
          print_session s.session_seq_formula_tail;
  end

  and print_session_or s = begin
          print_session s.session_seq_formula_or1;
          Printf.printf " %s " "or";
          print_session s.session_seq_formula_or2;
  end

  and print_session_star s = begin
          print_session s.session_seq_formula_star1;
          Printf.printf " %s " "*";
          print_session s.session_seq_formula_star2;
  end

end;;

(* =========== Protocol / Projection ========== *)
(* ============================================ *)
module Protocol = Make_Session(Protocol_base);;
module Projection = Make_Session(Projection_base);;

type session_type = ProtocolSession of Protocol.session | ProjectionSession of Projection.session

let foo =
  let () = print_endline "!!!!! SESSION!!!!!!!" in
  ()
;;