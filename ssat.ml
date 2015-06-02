#include "xdebug.cppo"
open Globals
open VarGen

open Gen.Basic

open Cpure
open VarGen

module CP=Cpure

module SS=
   struct

     let rec find_close_neq_x (a:CP.EMapSV.emap) neqs res=
       if CP.EMapSV.is_empty a then neqs else
         match neqs with
           | [] -> Gen.BList.remove_dups_eq (fun (sv11,sv12) (sv21,sv22) -> CP.eq_spec_var sv11 sv21 && CP.eq_spec_var sv12 sv22) res
           | (sv1,sv2)::rest ->
                 let cl_svl1 = CP.EMapSV.find_equiv_all_new sv1 a in
                 let cl_svl2 = CP.EMapSV.find_equiv_all_new sv2 a in
                 let n_res =res@(List.fold_left (fun r sv1 -> r@(List.map (fun sv2 -> (sv1,sv2) ) cl_svl2)) [] cl_svl1) in
                 find_close_neq_x a rest n_res

     let find_close_neq (a:CP.EMapSV.emap) neqs res=
       let pr1 =pr_list (pr_pair !CP.print_sv !CP.print_sv) in
       Debug.no_2 "find_close_neq" CP.string_of_var_eset pr1 pr1
           (fun _ _ -> find_close_neq_x (a:CP.EMapSV.emap) neqs res) a neqs

     let find_closure_svl a svl=
       if CP.EMapSV.is_empty a then svl else
         CP.find_eq_closure a svl


     let rec poss_pair_of_list svl res=
       match svl with
         | sv1::rest -> let prs = List.map (fun sv2 -> (sv1,sv2)) rest in
           poss_pair_of_list rest (res@prs)
         | [] -> res


     let is_inconsistent_x ptos eqs neqs cl_eqNulls cl_neqNulls=
       let rec is_intersect ls1 ls2 cmp_fn=
         match ls1 with
           | [] -> false
           | sv1::rest -> if Gen.BList.mem_eq cmp_fn sv1 ls2 then true else
               is_intersect rest ls2 cmp_fn
       in
       let pr_sv_cmp (sv11,sv12) (sv21,sv22) = ((CP.eq_spec_var sv11 sv21) && (CP.eq_spec_var sv12 sv22)) ||
         ((CP.eq_spec_var sv11 sv22) && (CP.eq_spec_var sv12 sv21))
       in
       let (neqs, cl_neqNulls)= if ptos=[] then (neqs, cl_neqNulls) else
         let neqs2 = poss_pair_of_list ptos [] in
         let a = CP.EMapSV.build_eset eqs in
         let cl_neqNulls1 = find_closure_svl a ptos in
         let neqs3 = find_close_neq a (neqs2) [] in
         let neqs = neqs3@neqs in
         let cl_neqNulls = cl_neqNulls@cl_neqNulls1 in
         (neqs, cl_neqNulls)
       in
       is_intersect eqs neqs pr_sv_cmp ||
           is_intersect cl_eqNulls cl_neqNulls CP.eq_spec_var

     let is_inconsistent ptos eqs neqs cl_eqNulls cl_neqNulls=
       let pr1 = !CP.print_svl in
       let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
       Debug.no_5 "is_inconsistent" pr1 pr2 pr2 pr1 pr1 string_of_bool
           (fun _ _ _ _ _ -> is_inconsistent_x ptos eqs neqs cl_eqNulls cl_neqNulls)
           ptos eqs neqs cl_eqNulls cl_neqNulls

     let is_s_unsat_x baga p=
       let mf = Mcpure.mix_of_pure p in
       let eqs = (Mcpure.ptr_equations_without_null mf) in
       let neqs = CP.get_neqs_new p in
       let eqNulls = CP.remove_dups_svl (Mcpure.get_null_ptrs mf) in
       let neqNulls = CP.get_neq_null_svl p in
       is_inconsistent baga eqs neqs eqNulls neqNulls

     let is_s_unsat baga p=
       let pr1 = !CP.print_svl in
       let pr2 = !CP.print_formula in
       Debug.no_2 "is_s_unsat" pr1 pr2 string_of_bool
           (fun _ _ -> is_s_unsat_x baga p) baga p

   end;;
