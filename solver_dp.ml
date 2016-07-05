#include "xdebug.cppo"
module CF = Cformula
module CP = Cpure

exception Solver_exception of string


(* and heap_entail_conjunct_x (prog : prog_decl) (is_folding : bool)   *)
(*               (ctx0 : context) (conseq : formula)                   *)
(*               rhs_matched_set pos : (list_context * proof) =        *)




let compute_address (hf: CF.h_formula) : CP.formula =
  match hf with
  | CF.Star _
  | CF.StarMinus _
  | CF.Conj _
  | CF.ConjStar _
  | CF.ConjConj _
  | CF.Phase _
  | CF.ThreadNode _
  | CF.Hole _
  | CF.HRel _
  | CF.DataNode of h_formula_data
  | CF.ViewNode of h_formula_view
  | CF.HTrue -> 
  | CF.HFalse
  | CF.HEmp (* emp for classical logic *)


let compute_well_formed_condition (f: CF.formula) : CF.formula =




  (* 
 * Checking the validity of an entailment.
 * The antecedent and consequent must be conjunctive formula. 
 *)
  let prove_entailment (ante: CF.formula) (conseq: CF.formula) : bool =


    true
