open Gen
open Globals
open Ipure
open Cpure

type perm_type =
  | Frac (*fractional permissions*)
  | Count (*counting permissions*)
  | No

type iperm = Ipure.exp option

type cperm = Cpure.spec_var option

type cperm_var = Cpure.spec_var

let perm = ref No

let set_perm perm_str = 
  if perm_str = "fperm" then perm:=Frac
  else if perm_str = "cperm" then perm:=Count
  else perm:= No

let allow_perm :bool = 
  match !perm with
    | Frac
    | Count -> true
    | No -> false

let cperm_typ = if (!allow_cperm) then Cperm.cperm_typ
    else Fperm.cperm_typ

let empty_iperm = if (!allow_cperm) then Cperm.empty_iperm
    else Fperm.empty_iperm

let empty_perm = if (!allow_cperm) then Cperm.empty_perm
    else Fperm.empty_perm

let full_iperm = if (!allow_cperm) then Cperm.full_iperm
    else Fperm.full_iperm

(*LDK: a specvar to indicate FULL permission*)
let full_perm_name = if (!allow_cperm) then Cperm.full_perm_name
    else Fperm.full_perm_name

let perm_name = if (!allow_cperm) then Cperm.perm_name
    else Fperm.perm_name

let full_perm = if (!allow_cperm) then Cperm.full_perm
    else Fperm.full_perm

let fv_iperm = if (!allow_cperm) then Cperm.fv_iperm
    else Fperm.fv_iperm

let get_iperm = if (!allow_cperm) then Cperm.get_iperm
    else Fperm.get_iperm

let apply_one_iperm = if (!allow_cperm) then Cperm.apply_one_iperm
    else Fperm.apply_one_iperm

let full_perm_var = if (!allow_cperm) then Cperm.full_perm_var
    else Fperm.full_perm_var

(*LDK: a constraint to indicate FULL permission = 1.0*)
let full_perm_constraint = 
  let _ =   print_string ("perm.ml: cperm = " ^ string_of_bool !Globals.allow_cperm  
                          ^ " fperm =" ^ string_of_bool !Globals.allow_fperm
                          ^ "\n") in
  if (!Globals.allow_cperm==true) then Cperm.full_perm_constraint
    else Fperm.full_perm_constraint

let mkFullPerm_pure = if (!allow_cperm) then Cperm.mkFullPerm_pure
    else Fperm.mkFullPerm_pure

let mkFullPerm_pure_from_ident = if (!allow_cperm) then Cperm.mkFullPerm_pure_from_ident
    else Fperm.mkFullPerm_pure_from_ident

(*create fractional permission invariant 0<f<=1*)
let mkPermInv = if (!allow_cperm) then Cperm.mkPermInv
    else Fperm.mkPermInv

let mkPermWrite = if (!allow_cperm) then Cperm.mkPermWrite
    else Fperm.mkPermWrite

let float_out_iperm = if (!allow_cperm) then Cperm.float_out_iperm
    else Fperm.float_out_iperm

let float_out_mix_max_iperm = if (!allow_cperm) then Cperm.float_out_mix_max_iperm
    else Fperm.float_out_mix_max_iperm

let fv_cperm =if (!allow_cperm) then  Cperm.fv_cperm
    else Fperm.fv_cperm

let get_cperm = if (!allow_cperm) then Cperm.get_cperm
     else Fperm.get_cperm

let subst_var_perm = if (!allow_cperm) then Cperm.subst_var_perm
    else Fperm.subst_var_perm

let fresh_cperm_var = if (!allow_cperm) then Cperm.fresh_cperm_var
    else Fperm.fresh_cperm_var

let mkEq_cperm = if (!allow_cperm) then Cperm.mkEq_cperm
    else Fperm.mkEq_cperm

(*can't not do it modularly because 
we do not separate between printers for ipure and iformula*)
(* let string_of_iperm perm = *)
(*   match perm with *)
(*     | None -> "" *)
(*     | Some f -> Cpure.string_of_formula_exp f *)

(* module PERM_const = *)
(* struct *)
(*   let full_perm_name = ("Anon_"^"full_perm") *)
(*   let perm_name = ("perm_") *)
(* end;; *)

(* module type PERM = *)
(*   sig *)
(*     type iperm *)
(*     type cperm *)
(*     type cperm_var *)
(*       (\* type fe = (ident * ident * t) *\) *)
(*     val cperm_typ :typ *)
(*     val empty_iperm : iperm *)
(*     val empty_perm : cperm *)
(*     val full_iperm : iperm *)
(*     val full_perm : cperm *)
(*     val fv_iperm : iperm -> (ident * primed) list *)
(*     val get_iperm : iperm -> Ipure.exp list *)
(*     val apply_one_iperm : ((ident * primed) ) * (ident*prime)) -> Ipure.exp -> Ipure.exp *)
(*     val full_perm_var : cperm_var *)
(*     val full_perm_constraint : Mcpure.mix_formula *)
(*     val mkFullPerm_pure : cperm -> Cpure.formula  *)
(*     val mkFullPerm_pure_from_ident : ident -> Cpure.formula *)
(*     val mkPermInv : cperm -> Cpure.formula *)
(*     val mkPermWrite : cperm -> Cpure.formula *)
(*     val float_out_iperm : iperm -> loc -> (iperm * ( (ident * Ipure.exp)list) ) *)
(*     val float_out_mix_max_iperm : iperm -> loc -> (iperm * (Ipure.exp * ((formula * (string list) option)))) *)
(*     val fv_cperm : cperm -> cperm_var list *)
(*     val get_cperm : cperm -> cperm_var list *)
(*     val subst_var_perm : (cperm_var * cperm_var) -> cperm -> cperm *)
(*     val fresh_cperm_var : cperm_var -> cperm_var *)
(*     val mkEq_cperm : cperm_var -> cperm_var -> Cpure.formula *)
(*     end *)
(*    end;; *)


