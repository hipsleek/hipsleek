(* Ultilities for bounded permissions *)

open Gen
open Globals
open Ipure
open Cpure

(*0<=c<=t+a & t>=0*)
let mkBpermInv ((c,t,a) : Cpure.exp * Cpure.exp * Cpure.exp) : Cpure.formula = 
  let zero_exp = Cpure.IConst (0,no_pos) in
  let t_plus_a = mkAdd t a no_pos in
  let f1 = Cpure.mkGteExp c zero_exp no_pos in
  let f2 = Cpure.mkGteExp t_plus_a c no_pos in
  let f3 = Cpure.mkGteExp t zero_exp no_pos in
  let f12 = Cpure.mkAnd f1 f2 no_pos in
  let f123 = Cpure.mkAnd f12 f3 no_pos in
  f123
