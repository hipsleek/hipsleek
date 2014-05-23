open Globals
open Wrapper
open Others
open Stat_global
open Global_var
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Cast
open Gen.Basic

open Label

open Cpure

(* extended pure formula *)
type ef_pure = ( 
    spec_var list (* baga *)
    * formula (* pure formula *)
    )

(* disjunctive extended pure formula *)
(* [] denotes false *)
type ef_pure_disj = ef_pure list

(* compute fixpoint iteration *)
(* strict upper bound 100 *)
(* fix_ef : [view_defn] -> disjunct_num (0 -> precise) -> [ef_pure_disj] *)


(* sel_hull_ef : f:[ef_pure_disj] -> disj_num (0 -> precise) 
   -> [ef_pure_disj] *)
(* pre: 0<=disj_num<=100 & disj_num=0 -> len(f)<=100  *)

(* fix_test :  view:[view_defn] -> inv:[ef_pure_disj] -> bool *)
(* does view(inv) --> inv *)
 
(* ef_imply :  ante:ef_pure_disj -> conseq:ef_pure_disj -> bool *)
(* does ante --> conseq *)

(* ef_unsat :  ef_pure_disj -> ef_pure_disj *)
(* remove unsat terms *)

(* ef_find_equiv :  (spec_var) list -> formula -> (spec_var) list *)
(* find equivalent id in the formula *)

(* ef_elim_exists :  (spec_var) list -> ef_pure -> ef_pure *)
(* remove unsat terms *)


