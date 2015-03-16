#include "xdebug.cppo"
open VarGen
open Globals
open Gen

module DD = Debug
module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module C = Cast
module I = Iast

let get_equations_sets_x (f0 : CP.formula) (interest_vars:Cpure.spec_var list): (CP.b_formula list) =
  let rec helper f =match f with
  | CP.And (f1, f2, pos) -> 
        let l1 = helper f1 in
        let l2 = helper f2 in
        l1@l2
  | CP.AndList lfs -> List.fold_left (fun r (_,f) -> r@(helper f )) [] lfs
  | CP.BForm (bf,_) -> begin
      let (pf,il) = bf in
      match pf with
        | Cpure.BVar (v,l)-> [bf]
        | Cpure.Lt (e1,e2,l)-> 
	      if (Cpure.of_interest e1 e2 interest_vars) then [(Cpure.Lt(e1,e2,l), il)]
	      else []
        | Cpure.Lte (e1,e2,l) -> 
	      if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Lte(e1,e2,l), il)]
	      else []
        | Cpure.Gt (e1,e2,l) -> 
	      if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Lt(e2,e1,l), il)]
	      else []
        | Cpure.Gte(e1,e2,l)-> 
	      if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Lte(e2,e1,l), il)]
	      else []
        | Cpure.Eq (e1,e2,l) -> 
	      if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Eq(e1,e2,l), il)]
	      else []
        | Cpure.Neq (e1,e2,l)-> 
	      if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Neq(e1,e2,l), il)]
	      else []
        | _ -> []
    end	
  | CP.Not (f1,_,_) -> List.fold_left (fun r c ->
	let (pf,il) = c in 
	let ps = match pf with
          | Cpure.BVar (v,l)-> [c]
          | Cpure.Lt (e1,e2,l)-> [(Cpure.Lt (e2,e1,l), il)]
          | Cpure.Lte (e1,e2,l) -> [(Cpure.Lte (e2,e1,l), il)]
          | Cpure.Eq (e1,e2,l) -> [(Cpure.Neq (e1,e2,l) , il)]
          | Cpure.Neq (e1,e2,l)-> [(Cpure.Eq (e1,e2,l), il)]
          |_ -> []
               (* Error.report_error { *)
	       (*     Error.error_loc = no_pos; *)
	       (*     Error.error_text ="malfunction:get_equations_sets must return only bvars, inequalities and equalities"} *)
        in
        r@ps
    ) [] (helper f1)
  | _ -> []
        (* Error.report_error { *)
        (* Error.error_loc = no_pos; *)
        (* Error.error_text ="malfunction:get_equations_sets can be called only with conjuncts and without quantifiers"} *)
  in
  helper f0

let get_equations_sets (f : CP.formula) (interest_vars:Cpure.spec_var list): (CP.b_formula list)=
  let pr1 = !CP.print_formula in
  Debug.no_2 "Solver.get_equations_sets" pr1 !CP.print_svl pr_none
      (fun _ _ -> get_equations_sets_x f interest_vars) f interest_vars

let transform_null (eqs) :(CP.b_formula list) = List.map (fun c ->
    let (pf,il) = c in
    match pf with
      | Cpure.BVar _ 
      | Cpure.Lt _
      | Cpure.Lte _ -> c
      | Cpure.Eq (e1,e2,l) -> 
	    if (Cpure.exp_is_object_var e1)&&(Cpure.is_num e2) then
	      if (Cpure.is_zero_int e2) then (Cpure.Eq (e1,(Cpure.Null l),l), il)
	      else (Cpure.Neq (e1,(Cpure.Null l),l), il)
	    else if (Cpure.exp_is_object_var e2)&&(Cpure.is_num e1) then
	      if (Cpure.is_zero_int e1) then (Cpure.Eq (e2,(Cpure.Null l),l), il)
	      else (Cpure.Neq (e2,(Cpure.Null l),l), il)
	    else c
      | Cpure.Neq (e1,e2,l)-> 
	    if (Cpure.exp_is_object_var e1)&&(Cpure.is_num e2) then
	      if (Cpure.is_zero_int e2) then (Cpure.Neq (e1,(Cpure.Null l),l), il)
	      else c
	    else if (Cpure.exp_is_object_var e2)&&(Cpure.is_num e1) then
	      if (Cpure.is_zero_int e1) then (Cpure.Neq (e2,(Cpure.Null l),l), il)
	      else c
	    else c
      | _ -> c
) eqs
