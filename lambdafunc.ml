(*
  Created 08-July-2009

  Library for lambda functions
*)

open Globals

module P = Ipure
module I = Iformula

type ext_exp =
  | Pure P.exp
  | Lambda lambda_formula

and lambda_formula = {
	lambda_formula_name : ident;
	lambda_formula_arguments : ext_exp list;
	lambda_formula_exp : lambda_exp
	h_formula_lambda_pos : loc;
  }

and lambda_exp = {
	lambda_exp_vars : ident list;
	lambda_exp_body : I.struc_formula;
  }
