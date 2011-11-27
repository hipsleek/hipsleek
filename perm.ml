open Gen
open Globals
open Ipure
open Cpure



(* type iperm = Ipure.exp option *)
type iperm = Cperm.iperm

type cperm = Cperm.cperm

type cperm_var = Cpure.spec_var

let cperm_typ = Cperm.cperm_typ
let empty_iperm = Cperm.empty_iperm
let empty_perm = Cperm.empty_perm
let full_iperm = Cperm.full_iperm

(*LDK: a specvar to indicate FULL permission*)
let full_perm_name = Cperm.full_perm_name

let perm_name = Cperm.perm_name

let full_perm = Cperm.full_perm

let fv_iperm = Cperm.fv_iperm

let get_iperm = Cperm.get_iperm

let apply_one_iperm = Cperm.apply_one_iperm


let full_perm_var = Cperm.full_perm_var

(*LDK: a constraint to indicate FULL permission = 1.0*)
let full_perm_constraint = Cperm.full_perm_constraint

let mkFullPerm_pure = Cperm.mkFullPerm_pure

let mkFullPerm_pure_from_ident = Cperm.mkFullPerm_pure_from_ident

(*create fractional permission invariant 0<f<=1*)
let mkPermInv = Cperm.mkPermInv

let mkPermWrite = Cperm.mkPermWrite

let float_out_iperm = Cperm.float_out_iperm

let float_out_mix_max_iperm = Cperm.float_out_mix_max_iperm

let fv_cperm = Cperm.fv_cperm

let get_cperm = Cperm.get_cperm

let subst_var_perm = Cperm.subst_var_perm

let fresh_cperm_var = Cperm.fresh_cperm_var

let mkEq_cperm = Cperm.mkEq_cperm

(*can't not do it modularly because 
we do not separate between printers for ipure and iformula*)
(* let string_of_iperm perm = *)
(*   match perm with *)
(*     | None -> "" *)
(*     | Some f -> Cpure.string_of_formula_exp f *)


