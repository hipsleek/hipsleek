#include "xdebug.cppo"
open VarGen
open Globals
module DD = Debug
open Gen
open Context
open Cpure

module Err = Error
module CP = Cpure
module MCP = Mcpure
module TP = Tpdispatcher

type rel_typ =
  | PosConst of formula
  | NegConst of formula
  | Zero
  | Var of formula
  | Undefined

let do_nothing = ()

(*let compute_rel (v1: spec_var) (v2: spec_var) (fml: formula) : rel_typ =
  let eq_fml = mkEqExp (mkVar v1 no_pos) (mkVar v2 no_pos) no_pos in
  let check_zero = TP.imply_raw fml eq_fml in
  if check_zero then Zero
  else
    let fml_ls = list_of_conjs fml in
    let var_of_interest = v1::[v2] in
    let fml_of_interest = 
      List.filter (fun f -> subset var_of_interest (fv f)(* && is_eq_fml f *)) fml_ls in
    match fml_of_interest with
      | [] -> Undefined
      | [f] -> 
        let sv = SpecVar (Int, "Unknown", Unprimed) in
        let res = Omega.simplify_raw (CP.mkAnd f (mkEqExp (mkVar v1 no_pos) (mkAdd (mkVar v2 no_pos) (mkVar sv no_pos) no_pos) no_pos) no_pos) in
        PosConst res
      | _ -> Undefined*)
