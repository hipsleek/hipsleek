
module F =Iformula
(* Protocol *)
(* Projection *)

type transmission = Send | Receive

type protocol_base_formula = {
  protocol_base_formula_sender   : id;
  protocol_base_formula_receiver : id;
  protocol_base_formula_message  : F.formula;
}

and projection_base_bormula = {
  projection_base_bormula_op      : transmission;
  projection_base_bormula_channel : id;
  projection_base_bormula_message : F.formula;
}
;;

module type Session = sig
  type t
    
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
  
end;;
