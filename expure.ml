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

(* in cpure.ml *)

  (* extended pure formula *)
  (* type ef_pure = (  *)
  (*     spec_var list (\* baga *\) *)
  (*     * formula (\* pure formula *\) *)
  (*     ) *)

  (* disjunctive extended pure formula *)
  (* [] denotes false *)
  (* type ef_pure_disj = ef_pure list *)

(* convert ptr to integer constraints *)
(* ([a,a,b]  --> a!=a & a!=b & a!=b & a>0 & a>0 & b>0 *)
let baga_conv (baga : spec_var list) : formula
   = mkTrue no_pos

(* ef_conv :  ef_pure -> formula *)
(* conseq must use this *)
(* ([a,a,b],pure)  --> baga[a,ab] & a>0 & a>0 & b>01 & pure *)
let ef_conv ((baga,f) : ef_pure) : formula
   = let bf = baga_conv baga in
     mkAnd bf f no_pos

(* ([a,a,b]  --> a=1 & a=2 & b=3 *)
let baga_enum (baga : spec_var list) : formula
   = mkTrue no_pos

(* ef_conv_enum :  ef_pure -> formula *)
(* provide an enumeration that can be used by ante *)
(* ([a,a,b],pure)  --> a=1 & a=2 & a=3 & pure *)
let ef_conv_enum ((baga,f) : ef_pure) : formula
   = let bf = baga_enum baga in
     mkAnd bf f no_pos

let ef_conv_disj (disj : ef_pure_disj) : formula
   = mkTrue no_pos

let ef_conv_enum_disj (disj : ef_pure_disj) : formula
   = mkTrue no_pos


(* ef_imply :  ante:ef_pure_disj -> conseq:ef_pure_disj -> bool *)
(* does ante --> conseq *)
(* convert ante with ef_conv_enum *)
(* convert conseq with ef_conv *)

let ef_imply  (ante:ef_pure_disj) (conseq:ef_pure_disj) : bool = 
  let a_f = ef_conv_enum_disj ante in
  let c_f = ef_conv_disj conseq in
  (* a_f --> c_f *)
  true

(* ef_unsat :  ef_pure -> bool *)
(* remove unsat terms *)
(* convert unsat with ef_conv_enum *)
let ef_unsat  (f:ef_pure) : bool = 
  (* use ef_conv_enum *)
  let cf = ef_conv_enum f in
  (* if unsat(cf) return true *)
  true

(* ef_unsat_disj :  ef_pure_disj -> ef_pure_disj *)
(* remove unsat terms *)
(* convert unsat with ef_conv_enum *)
let ef_unsat_disj  (disj:ef_pure_disj) : ef_pure_disj = 
  List.filter (fun f -> not(ef_unsat f)) disj

(* using Cast *)


(* build : map -> view_decl -->  map --> ef_pure_disj *)
(* view  ls<self,p> == cformula *)
(* map   ls<self,p> == [([],true)] *)
(*       ls1<self,p> == [([],true)] *)


(* fix_test :  map -> view_list:[view_decl] -> inv_list:[ef_pure_disj] -> bool *)
(* does view(inv) --> inv *)
(* ls<self,p> == .... *)
(* inv<self,p> == ([],true) *)
(* let lhs_list = List.map (build map) view_list in *)
(* let rhs_list = inv_list in *)
(* let pair_list = List.combine lhs_list rhs_list in *)
(* let r_list = List.map (fun (a,c) -> ef_imply a c) pair_list in *)



(* ef_find_equiv :  (spec_var) list -> ef_pure -> (spec_var) list *)
(* find equivalent id in the formula *)
(* e.g. [a,b] -> ([a,b,c], b=c ---> [a,c] *)
(*      to rename b with c *)


(* ef_elim_exists :  (spec_var) list -> ef_pure -> ef_pure *)
(* remove unsat terms *)


(* sel_hull_ef : f:[ef_pure_disj] -> disj_num (0 -> precise) 
   -> [ef_pure_disj] *)
(* pre: 0<=disj_num<=100 & disj_num=0 -> len(f)<=100  *)


(* compute fixpoint iteration *)
(* strict upper bound 100 *)
(* fix_ef : [view_defn] -> disjunct_num (0 -> precise) -> [ef_pure_disj] *)


