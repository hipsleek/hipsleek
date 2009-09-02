(** Type inference module 
	Created 2-Sep-2009 *)

open Globals

module I = Iast

module IF = Iformula

(** Type constraint *)
type typ_constr = { 
	left_hand_side : I.typ;
	right_hand_side : I.typ; 
  }

(** Collect type constraints in a program 
	@param prog program declaration 
	@return list of type constraints for the input program *)
let collect_type_constraints_prog (prog : I.prog_decl) : typ_constr list =
  []
;;



