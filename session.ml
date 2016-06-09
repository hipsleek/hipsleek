#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module F = Iformula

type transmission = Send | Receive

(* ======= base formula for session type ====== *)
(* ============================================ *)
module type Session_base = sig
  type t
  type a
  type b
  type c

  val print_session_base : t -> unit
  val mk_base : a -> b -> c -> t
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

module Protocol_base (* : Session_base *) = struct
  type t = protocol_base_formula
  type a = ident
  type b = ident
  type c = F.formula

  let print_session_base f = begin
          Printf.printf "%s -> %s : " f.protocol_base_formula_sender f.protocol_base_formula_receiver;
          Printf.printf "%s" (!F.print_formula f.protocol_base_formula_message);
  end

  let mk_base sender receiver formula = { 
    protocol_base_formula_sender    = sender;
    protocol_base_formula_receiver  = receiver; 
    protocol_base_formula_message   = formula;
  }

end;;

module Projection_base (* : Session_base *) = struct
  type t = projection_base_formula
  type a = transmission
  type b = ident
  type c = F.formula

  let print_session_base f = match f.projection_base_formula_op with
    | Send -> let () = Printf.printf "%s!(%s)" f.projection_base_formula_channel (!F.print_formula f.projection_base_formula_message) in ()
    | Receive -> let () = Printf.printf "%s?(%s)" f.projection_base_formula_channel (!F.print_formula f.projection_base_formula_message) in ()

  let mk_base transmission channel formula = {
    projection_base_formula_op      = transmission;
    projection_base_formula_channel = channel;
    projection_base_formula_message = formula;
  }

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

  let rec print_session s = begin
          print_one_session s;
          print_newline ();
  end

  and print_one_session s = match s with
    | SSeq s -> print_session_seq s
    | SOr s -> print_session_or s
    | SStar s -> print_session_star s
    | SBase s -> print_session_base s

  and print_session_base = Base.print_session_base

  and print_session_seq s = begin
          Printf.printf "(";
          print_one_session s.session_seq_formula_head;
          Printf.printf ") %s (" ";;";
          print_one_session s.session_seq_formula_tail;
          Printf.printf ")";
  end

  and print_session_or s = begin
          Printf.printf "(";
          print_one_session s.session_seq_formula_or1;
          Printf.printf ") %s (" "or";
          print_one_session s.session_seq_formula_or2;
          Printf.printf ")";
  end

  and print_session_star s = begin
          Printf.printf "(";
          print_one_session s.session_seq_formula_star1;
          Printf.printf ") %s (" "*";
          print_one_session s.session_seq_formula_star2;
          Printf.printf ")";
  end

  let mk_base a b c = SBase (Base.mk_base a b c)

  and mk_session_seq_formula session1 session2 loc = SSeq {
      session_seq_formula_head = session1;
      session_seq_formula_tail = session2;
      session_seq_formula_pos  = loc;
    }

  and mk_session_or_formula session1 session2 loc = SOr {
    session_seq_formula_or1 = session1;
    session_seq_formula_or2 = session2;
    session_seq_formula_pos = loc;
    }

  and mk_session_star_formula session1 session2 loc = SStar {
    session_seq_formula_star1 = session1;
    session_seq_formula_star2 = session2;
    session_seq_formula_pos   = loc;
    }
      
end;;

(* =========== Protocol / Projection ========== *)
(* ============================================ *)
module Protocol = Make_Session(Protocol_base);;
module Projection = Make_Session(Projection_base);;

type session_type = ProtocolSession of Protocol.session | ProjectionSession of Projection.session

(* =========== Make Methods ========== *)
(* ============================================ *)


let boo () =
  let prot = Protocol.mk_base "" "" (F.mkTrue_nf no_pos) in
  Protocol.print_session prot
  ;;


let foo =
  let () = print_endline "!!!!! SESSION!!!!!!!" in
  ()
;;
