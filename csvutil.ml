#include "xdebug.cppo"
open VarGen
open Globals
open Gen.Basic
(* open Exc.GTable *)
module LO=Label_only.LOne
open Label


open Cpure

(* computes must-alias sets from equalities, maintains the invariant *)
(* that these sets form a partition. *)
let rec alias_x (ptr_eqs : (spec_var * spec_var) list) : spec_var list list = 
  match ptr_eqs with
  | (v1, v2) :: rest -> begin
	  let rest_sets = alias_x rest in
	  let search (v : spec_var) (asets : spec_var list list) = List.partition (fun aset -> mem v aset) asets in
	  let av1, rest1 = search v1 rest_sets in
	  let av2, rest2 = search v2 rest1 in
	  let v1v2_set = remove_dups_svl (List.concat ([v1; v2] :: (av1 @ av2))) in
	  v1v2_set :: rest2
	end
  | [] -> []

let alias_nth i (ptr_eqs : (spec_var * spec_var) list) : spec_var list list = 
  let psv = Cprinter.string_of_spec_var in
  let pr1 l = pr_list (pr_pair psv psv) l in
  let pr2 l = pr_list (pr_list psv) l in
  Debug.no_1_num i "alias" pr1 pr2 alias_x ptr_eqs

let get_aset (aset : spec_var list list) (v : spec_var) : spec_var list =
  let tmp = List.filter (fun a -> mem v a) aset in
  match tmp with
	| [] -> []
	| [s] -> s
	| _ -> failwith ((string_of_spec_var v) ^ " appears in more than one alias sets")

let get_aset (aset : spec_var list list) (v : spec_var) : spec_var list =
let psv = !print_sv in
 let pr1 = (pr_list psv) in
 let pr2 = pr_list pr1 in
 Debug.no_2 "get_aset" pr2  psv pr1 get_aset aset v


let comp_aliases_x (rhs_p:Mcpure.mix_formula) : (spec_var) list list =
    let eqns = Mcpure.ptr_equations_without_null rhs_p in
    alias_nth 1 eqns 

let comp_aliases (rhs_p:Mcpure.mix_formula) : (spec_var) list list =
 let psv = Cprinter.string_of_spec_var in
 let pr2 = (pr_list (pr_list psv)) in
 let pr1 = Cprinter.string_of_mix_formula in
 Debug.no_1 "comp_aliase" pr1 pr2 comp_aliases_x rhs_p


let comp_alias_part r_asets a_vars = 
    (* let a_vars = lhs_fv @ posib_r_aliases in *)
    let fltr = List.map (fun c-> Gen.BList.intersect_eq (eq_spec_var) c a_vars) r_asets in
    let colaps l = List.fold_left (fun a c -> match a with 
      | [] -> [(c,c)]
      | h::_-> (c,(fst h))::a) [] l in
    List.concat (List.map colaps fltr) 
