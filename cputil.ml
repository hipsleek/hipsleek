(* This module provides util for cpure *)
open Globals
open Gen.Basic
open Exc.GTable
module LO=Label_only.LOne
open Label

open Cpure


(*************************************************)
 (*****************PRED UTIL********************)
(*************************************************)
let hloc_enum_to_symb_pf pf0=
  let rec recf pf = match pf with
    | Gt (e1, e2,l) -> begin
        match e1,e2 with
          | Var _, IConst (i, l1) -> if i>=0 then
              let n_e2 = Null l1 in
              Neq (e1, n_e2, l)
            else pf
          | _ -> pf
      end
    | Eq (e1, e2,l) -> begin
        match e1,e2 with
          | Var _, IConst (i, l1) -> if i!=0 then
              let n_e2 = Null l1 in
              Neq (e1, n_e2, l)
            else pf
          | _ -> pf
      end
    | _ -> pf
  in
  recf pf0

let hloc_enum_to_symb_x f0: formula=
  let rec recf f= match f with
    | BForm  ((pf, bfa), lbl) -> BForm ((hloc_enum_to_symb_pf pf,bfa), lbl)
    | And (f1, f2, l) -> And (recf f1, recf f2, l)
    | AndList fs -> AndList (List.map (fun (a, f1) -> (a, recf f1)) fs)
    | Or (f1, f2 , lbl, l) ->
          let sym_f1 = recf f1 in
          let sym_f2 = recf f2 in
          if is_eq_null_exp sym_f1 && is_neq_null_exp sym_f2 then
            mkTrue l
          else
            Or (sym_f1, sym_f2 , lbl, l)
    | Not (f1, lbl, l) -> Not (recf f1, lbl, l)
    | Forall (sv, f1, lbl, l) -> Forall (sv, recf f1, lbl, l)
    | Exists (sv, f1, lbl, l) -> Exists (sv, recf f1, lbl, l)
  in
  recf f0

let hloc_enum_to_symb f0: formula=
  let pr1 = !print_formula in
  Debug.no_1 "hloc_enum_to_symb" pr1 pr1
      (fun _ -> hloc_enum_to_symb_x f0) f0



(*************************************************)
 (****************END PRED UTIL******************)
(*************************************************)
