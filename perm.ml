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

let string_of_perm_type t =
  match t with
    | Frac -> "Frac"
    | Count -> "Count"
    | No -> "No"

let perm = ref Frac

let allow_perm ():bool = 
  let _ = print_string ("perm.ml: allow_perm (): " ^ (string_of_perm_type !perm) ^ "\n\n") in
  match !perm with
    | Frac -> true
    | Count -> true
    | No -> false

let set_perm perm_str = 
  let _ = print_string ("perm.ml : set_perm: " ^ perm_str ^ "\n") in
  let _ = if perm_str = "fperm" then perm:=Frac
  else if perm_str = "cperm" then perm:=Count
  else perm:= No in
  print_string ((string_of_perm_type !perm) ^ (string_of_bool (allow_perm ())))

let cperm_typ () = 
  match !perm with
    | Count -> Cperm.cperm_typ
    | _ -> Fperm.cperm_typ

let empty_iperm () = 
  match !perm with
    | Count -> Cperm.empty_iperm
    | _ ->Fperm.empty_iperm

let empty_perm () =   match !perm with
    | Count -> Cperm.empty_perm
    | _ -> Fperm.empty_perm

let full_iperm () =   match !perm with
    | Count -> Cperm.full_iperm
    | _ -> Fperm.full_iperm

(*LDK: a specvar to indicate FULL permission*)
let full_perm_name () =   match !perm with
    | Count -> Cperm.full_perm_name
    | _ -> Fperm.full_perm_name

let perm_name ()=   match !perm with
    | Count -> Cperm.perm_name
    | _ -> Fperm.perm_name

let full_perm ()=   match !perm with
    | Count -> Cperm.full_perm
    | _ -> Fperm.full_perm

let fv_iperm =   match !perm with
    | Count -> Cperm.fv_iperm
    | _ -> Fperm.fv_iperm

let get_iperm p =  match !perm with
    | Count -> Cperm.get_iperm p
    | _ -> Fperm.get_iperm p

let apply_one_iperm =   match !perm with
    | Count -> Cperm.apply_one_iperm
    | _ -> Fperm.apply_one_iperm

let full_perm_var =  match !perm with
    | Count -> Cperm.full_perm_var
    | _ -> Fperm.full_perm_var

(*LDK: a constraint to indicate FULL permission = 1.0*)
let full_perm_constraint () =   match !perm with
    | Count -> Cperm.full_perm_constraint
    | _ -> Fperm.full_perm_constraint

let mkFullPerm_pure =   match !perm with
    | Count -> Cperm.mkFullPerm_pure
    | _ -> Fperm.mkFullPerm_pure

let mkFullPerm_pure_from_ident =   match !perm with
    | Count -> Cperm.mkFullPerm_pure_from_ident
    | _ -> Fperm.mkFullPerm_pure_from_ident

(*create fractional permission invariant 0<f<=1*)
let mkPermInv =   match !perm with
    | Count -> Cperm.mkPermInv
    | _ -> Fperm.mkPermInv

let mkPermWrite =   match !perm with
    | Count -> Cperm.mkPermWrite
    | _ -> Fperm.mkPermWrite

let float_out_iperm =   match !perm with
    | Count -> Cperm.float_out_iperm
    | _ -> Fperm.float_out_iperm

let float_out_mix_max_iperm =   match !perm with
    | Count -> Cperm.float_out_mix_max_iperm
    | _ -> Fperm.float_out_mix_max_iperm

let fv_cperm p = match !perm with
    | Count -> Cperm.fv_cperm p
    | _ -> Fperm.fv_cperm p

let get_cperm p = match !perm with
    | Count -> Cperm.get_cperm p
    | _ -> Fperm.get_cperm p

let subst_var_perm =   match !perm with
    | Count -> Cperm.subst_var_perm
    | _ -> Fperm.subst_var_perm

let fresh_cperm_var =   match !perm with
    | Count -> Cperm.fresh_cperm_var
    | _ -> Fperm.fresh_cperm_var

let mkEq_cperm =   match !perm with
    | Count ->  Cperm.mkEq_cperm
    | _ -> Fperm.mkEq_cperm


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


