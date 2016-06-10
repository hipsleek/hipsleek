#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module F = Iformula
module CF = Cformula 



type transmission = Send | Receive

let string_of_seq  = ";;"
let string_of_transmission t =
  match t with
  | Send    -> "!"
  | Receive -> "?"
    

(* ======= base formula for session type ====== *)
(* ============================================ *)
module type Message_type = sig
  type t

  val is_emp : t -> bool
  val print  : t -> string
end;;

(* inst for iformula & cformula *)
module Protocol_base_formula =
  functor  (Msg: Message_type) ->
  struct
    type t = Msg.t
    type a = ident * ident
    type base = {
      protocol_base_formula_sender   : ident;
      protocol_base_formula_receiver : ident;
      protocol_base_formula_message  : t;
    }

    let print_message f = Msg.print f.protocol_base_formula_message

    let print_session_base f = begin
      Printf.printf "%s -> %s : " f.protocol_base_formula_sender f.protocol_base_formula_receiver;
      Printf.printf "%s" (print_message f);
    end

    let mk_base (sender, receiver) formula = {
      protocol_base_formula_sender    = sender;
      protocol_base_formula_receiver  = receiver;
      protocol_base_formula_message   = formula;
    }

  end;;

(* inst for iformula & cformula *)
module Projection_base_formula =
  functor  (Msg: Message_type) ->
  struct
    type t = Msg.t
    type a = transmission * ident
    type base = {
      projection_base_formula_op      : transmission;
      projection_base_formula_channel : ident;
      projection_base_formula_message : t;
    }

    let print_message f = Msg.print f.projection_base_formula_message

    let print_session_base f =
      Printf.printf "%s%s(%s)"
        f.projection_base_formula_channel
        (string_of_transmission f.projection_base_formula_op )
        (print_message f)

    let mk_base (transmission, channel) formula = {
      projection_base_formula_op      = transmission;
      projection_base_formula_channel = channel;
      projection_base_formula_message = formula;
    }

  end;;

module type Session_base =
  sig
    type t
    type a
    type base

    val print_session_base : base -> unit
    val mk_base : a -> t -> base
  end;;

module IForm = struct
  type t = F.formula
  let is_emp f = failwith x_tbi
  let print    = !F.print_formula
end;;

module CForm = struct
  type t = CF.formula
  let is_emp f = failwith x_tbi
  let print    = !CF.print_formula
end;;


(* ============== session type ================ *)
(* ============================================ *)
module Make_Session (Base: Session_base) = struct
  type t = Base.base
  
  type session =
    | SSeq  of session_seq_formula
    | SOr   of session_or_formula
    | SStar of session_star_formula
    | SBase of t
    | SEmp

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
    | SSeq s  -> print_session_seq s
    | SOr s   -> print_session_or s
    | SStar s -> print_session_star s
    | SBase s -> print_session_base s
    | SEmp    -> print_session_emp

  and print_session_base = Base.print_session_base

  and print_session_emp = print_string "emp"
  
  and print_session_seq s = begin
          Printf.printf "(";
          print_one_session s.session_seq_formula_head;
          Printf.printf ") %s (" string_of_seq;
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

  let mk_base a b = SBase (Base.mk_base a b)

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

  (* let is_emp f = *)
  (*   match f with *)
  (*   | SSeq  _ *)
  (*   | SOr   _ *)
  (*   | SStar _ -> false *)
  (*   | SBase f -> Base.is_emp f *)

  (* let rec norm_emp sf = *)
  (*   match sf with *)
  (*   | SSeq  f -> *)
  (*     begin *)
  (*       let first_emp  = is_emp f.session_seq_formula_head in *)
  (*       let second_emp = is_emp f.session_seq_formula_tail in *)
  (*       match first_emp,second_emp with *)
  (*       | true, true  -> emp *)
  (*       | true, false -> f.session_seq_formula_head *)
  (*       | false, true -> f.session_seq_formula_tail *)
  (*       | _ -> f *)
  (*     end *)
  (*   | SOr   f -> f *)
  (*   | SStar f -> f *)
  (*   | SBase f -> f *)
end;;

(* =========== Protocol / Projection ========== *)
(* ============================================ *)

module IProtocol_base = Protocol_base_formula(IForm) ;;
module CProtocol_base = Protocol_base_formula(CForm) ;;
module IProjection_base = Projection_base_formula(IForm) ;;
module CProjection_base = Projection_base_formula(CForm) ;;

module IProtocol = Make_Session(IProtocol_base);;
module CProtocol = Make_Session(CProtocol_base);;

module IProjection = Make_Session(IProjection_base);;
module CProjection = Make_Session(CProjection_base);;

type session_type = ProtocolSession of IProtocol.session | ProjectionSession of IProjection.session

(* =========== Make Methods ========== *)
(* ============================================ *)


let boo () =
  let prot = IProtocol.mk_base ("", "") (F.mkTrue_nf no_pos) in
  IProtocol.print_session prot
  ;;
