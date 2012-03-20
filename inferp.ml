open Globals
open Sleekcommons
open Gen.Basic
open Exc.GTable

module I = Iast
module C = Cast
module IF = Iformula
module CF = Cformula
module IP = Ipure
module CP = Cpure
module LP = Lemproving
module AS = Astsimp
module DD = Debug

(*should move to cformula*)
(*res=(ind,base) list *)
let partition_cases_x (vname:string) (lfl:(CF.formula * formula_label) list): (CF.formula list * CF.formula list)=
  let partition_cases_helper f=
    let h, _,_,_,_ = CF.split_components f in
    let hs = CF.split_star_conjunctions h in
    let rec check_is_rec hs=
      match hs with
        | [] -> false
        | h::ss -> (match h with
              |  CF.ViewNode hv -> if hv.CF.h_formula_view_name = vname then true
                  else check_is_rec ss
              | _ -> check_is_rec ss
        )
    in
    check_is_rec hs
  in
  let lf = fst (List.split lfl) in
  List.partition partition_cases_helper lf

let partition_cases (vname:string) (lfl:(CF.formula * formula_label) list): (CF.formula list * CF.formula list)=
   let pr1 = (fun o -> o) in
   let pr4 = (fun (f,_) -> Cprinter.string_of_formula f) in
   let pr2 = pr_list Cprinter.string_of_formula in
   let pr3 = pr_pair pr2 pr2 in
   Debug.ho_2 "partition_cases" pr1 (pr_list pr4) pr3
       (fun _ _ -> partition_cases_x vname lfl) vname lfl

(*res=(pure,data,rec-pred)*)
let partition_f (inv:MP.mix_formula) (f:CF.formula): (MP.mix_formula*(CF.h_formula_data option) * (CF.h_formula_view list))=
  (*we have two kinds of varibales: inductive vars and non-inductive vars (pure formulas)*)

let synthesize_neg_view_def_x vd_u vd=
  (*partition into base_case and inductive case*)
  (*we have two kinds of varibales: inductive vars and non-inductive vars (pure formulas)*)
  let (idc_u,bc_u) = partition_cases vd_u.C.view_name vd_u.C.view_un_struc_formula in
  let (idc,bc) = partition_cases vd.C.view_name vd.C.view_un_struc_formula in
(**************************)
(*each formula is a case*)
  (*get pure formula ==> slice with non-inductive vars*)
  (*mkAnd (pure formula, inv)*)
  (*heap formulas: partition into data_formula and view_formula*)
(**************************)
  (*base case*)

  (*CF.data_of_h_formula CF.split_star_conjunctions*)

  (*inductive case*)

  vd

let synthesize_neg_view_def vd_u vd=
  let pr1 = Cprinter.string_of_view_decl in
   Debug.ho_2 "synthesize_neg_view_def" pr1 pr1 pr1
       (fun _ _ -> synthesize_neg_view_def_x vd_u vd) vd_u vd
