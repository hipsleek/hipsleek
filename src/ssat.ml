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


     let elim_exists quans0 p0=
       (* subst quans by non-quans*)
       let rec rearr_sst quans sst res=
         match sst with
           | [] -> res
           | (sv1,sv2)::rest -> begin
               let new_res =
                 match mem_svl sv1 quans, mem_svl sv2 quans with
                   | false,true -> res@[(sv2,sv1)]
                   | true,false -> res@[(sv1,sv2)]
                   | _ -> res
                 in
                 rearr_sst quans rest new_res
                 end
       in
       let rec recf quans p= match p with
         | Cpure.BForm _ ->
               x_add Cpure.filter_var p (Cpure.diff_svl (Cpure.remove_dups_svl (Cpure.fv p)) quans)
         | Cpure.Exists (sv, p1, l, pos) ->
               let quans1 = CP.remove_dups_svl (sv::quans) in
               let () = Debug.tinfo_hprint (add_str "p1" !Cpure.print_formula) p1 no_pos in
               let sst0 = (Mcpure.ptr_equations_without_null (Mcpure.mix_of_pure p1)) in
               let rearr_p = if sst0 = [] || quans1 = [] then p1 else
                 let rearr_sst = rearr_sst quans1 sst0 [] in
                 let () = Debug.tinfo_hprint (add_str "rearr_sst" (pr_list (pr_pair !Cpure.print_sv !Cpure.print_sv))) rearr_sst no_pos in
                 CP.subst rearr_sst p1
               in
               let () = Debug.tinfo_hprint (add_str "rearr_p" !Cpure.print_formula) rearr_p no_pos in
               let n_p1 = recf (quans1) rearr_p in
               let () = Debug.tinfo_hprint (add_str "quans1" !Cpure.print_svl) quans1 no_pos in
               let () = Debug.tinfo_hprint (add_str "n_p1" !Cpure.print_formula) n_p1 no_pos in
               let res = if Cpure.intersect_svl (Cpure.fv n_p1) quans1 != [] then Cpure.mkTrue pos
               else
                 if Cpure.mem_svl sv (Cpure.fv n_p1) then
                   Cpure.Exists (sv, n_p1, l, pos)
                 else n_p1
               in
               let () = Debug.tinfo_hprint (add_str "res" !Cpure.print_formula) res no_pos in
               res
         | Cpure.And (p1,p2,pos) -> (
               let n_p1 = recf quans p1 in
               let n_p2 = recf quans p2 in
               match Cpure.isConstTrue n_p1, Cpure.isConstTrue n_p2 with
                 | false, false ->  (match CP.remove_redundant_helper [n_p1;n_p2] [] with
                     | [] -> CP.mkTrue pos
                     | [p] -> p
                     | _ -> Cpure.And (n_p1,n_p2,pos)
                   )
                 | false,true -> n_p1
                 | _ -> n_p2
           )
         | _ -> p
       in
       recf quans0 p0


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
       if baga = [] && CP.isConstFalse p then true else
         let mf = Mcpure.mix_of_pure p in
         let eqs = (Mcpure.ptr_equations_without_null mf) in
         let neqs = CP.get_neqs_new p in
         let eqNulls = CP.remove_dups_svl (get_eq_null_svl p) (* (Mcpure.get_null_ptrs mf) *) in
         let neqNulls = CP.get_neq_null_svl p in
         is_inconsistent baga eqs neqs eqNulls neqNulls

     let is_s_unsat baga p=
       let pr1 = !CP.print_svl in
       let pr2 = !CP.print_formula in
       Debug.no_2 "is_s_unsat" pr1 pr2 string_of_bool
           (fun _ _ -> is_s_unsat_x baga p) baga p

   end;;
