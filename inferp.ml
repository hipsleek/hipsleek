open Globals
open Sleekcommons
open Gen.Basic
open Exc.GTable
open Cpure

module C = Cast
module CF = Cformula
module LP = Lemproving
module AS = Astsimp
module DD = Debug

(*should move to cformula*)
(*res=(ind,base) list *)
(*ind=(pure,(data,rec-pred,inductive formula i.g n=n-1))*)
let partition_cases_x (vname:string) (inv:Cpure.formula) (lfl:(CF.formula * formula_label) list):
(*base cases*)((CF.h_formula_data list * Cpure.formula) list *
(*inductive cases*)((CF.h_formula_view*Cpure.formula) list * CF.h_formula_data list * Cpure.formula) list)=
  let partition_cases_helper f=
    let h, mf,_,_,_ = CF.split_components f in
    let vs = CF.fv f in
    let p = Mcpure.pure_of_mix mf in
    let hs = CF.split_star_conjunctions h in
    let rec check_is_rec hs ir rviews dats rvs=
      match hs with
        | [] -> (ir, rviews, dats, rvs)
        | h::ss ->
            (match h with
              |  CF.ViewNode hv -> if hv.CF.h_formula_view_name = vname then
                    (*recursive - get pure formula*)
                    let rv = hv.CF.h_formula_view_arguments in
                    let rvp = Cpure.filter_var p rv in
                    check_is_rec ss true (rviews@[(hv,rvp)]) dats (rvs@rv)
                  else check_is_rec ss ir rviews dats rvs
              | CF.DataNode hd -> check_is_rec ss ir rviews (dats@[hd]) rvs
              | _ -> check_is_rec ss ir rviews dats rvs
            )
    in
    let (ir, rviews, dats, rvs) = check_is_rec hs false [] [] [] in
    let nvs = List.filter (fun x -> List.mem x rvs) vs in
    let p1 = Cpure.filter_var p nvs in
                (*mkAnd with inv*)
    let p1 = Cpure.mkAnd p1 inv no_pos in
    (ir, rviews, dats, rvs, p1)
  in
  let rec helper2 pl bl indl=
    (
        match pl with
          | [] -> (bl,indl)
          | (ir, rviews, dats, rvs, p1)::ss ->
              if ir then
                helper2 ss bl (indl@ [(rviews, dats, p1)])
              else
                helper2 ss (bl@[(dats,p1)]) indl
    )
  in
  let lf = fst (List.split lfl) in
  let tmp = List.map partition_cases_helper lf in
  helper2 tmp [] []

let partition_cases (vname:string) (inv:Cpure.formula) (lfl:(CF.formula * formula_label) list):
 (*base cases*)((CF.h_formula_data list * Cpure.formula) list *
(*inductive cases*)((CF.h_formula_view*Cpure.formula) list * CF.h_formula_data list * Cpure.formula) list)=
   let pr1 = (fun o -> o) in
   let pr4 = (fun (f,_) -> Cprinter.string_of_formula f) in
   let pr2 = pr_list Cprinter.string_of_formula in
   let pr5 = pr_list (fun x -> Cprinter.string_of_h_formula (CF.DataNode x)) in
   let pr6 = pr_list (pr_pair pr5 Cprinter.string_of_pure_formula) in
   let pr7 = pr_list (pr_pair (fun x -> Cprinter.string_of_h_formula (CF.ViewNode x)) Cprinter.string_of_pure_formula) in
   let pr8 = pr_list (pr_triple pr7 pr5 Cprinter.string_of_pure_formula) in
   let pr3 = pr_pair pr6 pr8 in
   (* let pr3 = (fun x -> "OUT") in *)
   Debug.ho_2 "partition_cases" pr1 (pr_list pr4) pr3
       (fun _ _ -> partition_cases_x vname inv lfl) vname lfl

(*generate 2 branches for each pair*)
(*(CF.h_formula_view*Cpure.formula) list * CF.h_formula_data list * Cpure.formula*)
let synthesize_one_inductive_pair_x ( (uvl, ud,up) ,(vl, d,p)):CF.struc_formula=


let synthesize_one_inductive_pair ( (uvl, ud,up) ,(vl, d,p)):CF.struc_formula=
  let pr1 = pr_list (fun x -> Cprinter.string_of_h_formula (CF.DataNode x)) in
  let pr2 = pr_list (pr_pair (fun x -> Cprinter.string_of_h_formula (CF.ViewNode x)) Cprinter.string_of_pure_formula) in
  let pr3 = pr_triple pr2 pr1 Cprinter.string_of_pure_formula in
  Debug.ho_1 "synthesize_one_inductive_pair" (pr_pair pr3 pr3) (Cprinter.string_of_struc_formula)
       (fun _ > synthesize_inductive_one_pair_x ((uvl, ud,up) ,(vl, d,p))) ((uvl, ud,up) ,(vl, d,p))

let synthesize_neg_view_def_x vd_u vd=
  (*partition into base_case and inductive case*)
  (*we have two kinds of varibales: inductive vars and non-inductive vars (pure formulas)*)
  (**************************)
(*each formula is a case*)
  (*get pure formula ==> slice with non-inductive vars*)
  (*mkAnd (pure formula, inv)*)
  (*heap formulas: partition into data_formula and view_formula*)
  DD.devel_pprint ">>>>>> *partition into base_case and inductive case <<<<<<" no_pos;
  (*DD.devel_hprint (add_str "LHS pure       : " !print_formula) lhs_xpure_orig pos; *)
(**************************)
  let (idc_us,bc_us) = partition_cases vd_u.C.view_name (Mcpure.pure_of_mix vd_u.C.view_user_inv) vd_u.C.view_un_struc_formula in
  let (idcs,bcs) = partition_cases vd.C.view_name (Mcpure.pure_of_mix vd.C.view_user_inv) vd.C.view_un_struc_formula in
  let neg_name = "_n_" ^ vd.C.view_name in
  (*base case*)

  (*CF.data_of_h_formula CF.split_star_conjunctions*)

  (*inductive case*)
  (*each universal-each ele*)
  let pr_f = List.combine idc_us idcs in
  vd

let synthesize_neg_view_def vd_u vd=
  let pr1 = Cprinter.string_of_view_decl in
   Debug.no_2 "synthesize_neg_view_def" pr1 pr1 pr1
       (fun _ _ -> synthesize_neg_view_def_x vd_u vd) vd_u vd
