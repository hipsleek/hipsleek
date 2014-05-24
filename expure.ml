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
(* type ef_pure = ( *)
(*     spec_var list (\* baga *\) *)
(*     * formula (\* pure formula *\) *)
(* ) *)

(* disjunctive extended pure formula *)
(* [] denotes false *)
(* type ef_pure_disj = ef_pure list *)

(* convert ptr to integer constraints *)
(* ([a,a,b]  --> a!=a & a!=b & a!=b & a>0 & a>0 & b>0 *)
let baga_conv (baga : spec_var list) : formula =
  if (List.length baga = 0) then
    mkTrue no_pos
  else if (List.length baga = 1) then
    mkGtVarInt (List.hd baga) 0 no_pos
  else
    let rec helper i j baga len fl =
      if i = len - 2 && j = len - 1 then
        fl@[(mkNeqVar (List.nth baga i) (List.nth baga j) no_pos)]
      else if j = len - 1 then
        helper (i + 1) (i + 2) baga len (fl@[(mkNeqVar (List.nth baga i) (List.nth baga j) no_pos)])
      else
        helper i (j + 1) baga len (fl@[(mkNeqVar (List.nth baga i) (List.nth baga j) no_pos)])
    in
    let fl1 = helper 0 1 baga (List.length baga) [] in
    let f1 = List.fold_left (fun f1 f2 -> mkAnd f1 f2 no_pos) (List.hd fl1) (List.tl fl1) in
    let fl2 = List.map (fun sv -> mkGtVarInt sv 0 no_pos) baga in
    let f2 = List.fold_left (fun f1 f2 -> mkAnd f1 f2 no_pos) (List.hd fl2) (List.tl fl2) in
    mkAnd f1 f2 no_pos

(* ef_conv :  ef_pure -> formula *)
(* conseq must use this *)
(* ([a,a,b],pure)  --> baga[a,ab] & a>0 & a>0 & b>01 & pure *)
let ef_conv ((baga,f) : ef_pure) : formula =
  let bf = baga_conv baga in
  mkAnd bf f no_pos

(* ([a,a,b]  --> a=1 & a=2 & b=3 *)
let baga_enum (baga : spec_var list) : formula =
  if (List.length baga = 0) then mkTrue no_pos else
    let i = ref 0 in
    let fl = List.map (fun sv ->
        i := !i + 1; mkEqVarInt sv !i no_pos) baga in
    List.fold_left (fun f1 f2 -> mkAnd f1 f2 no_pos) (List.hd fl) (List.tl fl)

(* ef_conv_enum :  ef_pure -> formula *)
(* provide an enumeration that can be used by ante *)
(* ([a,a,b],pure)  --> a=1 & a=2 & a=3 & pure *)
let ef_conv_enum ((baga,f) : ef_pure) : formula =
  let bf = baga_enum baga in
  mkAnd bf f no_pos

let ef_conv_disj (disj : ef_pure_disj) : formula =
  if (List.length disj = 0) then mkFalse no_pos else
    let fl = List.map (fun epf -> ef_conv epf) disj in
    List.fold_left (fun f1 f2 -> mkOr f1 f2 None no_pos) (List.hd fl) (List.tl fl)

let ef_conv_enum_disj (disj : ef_pure_disj) : formula =
  if (List.length disj = 0) then mkFalse no_pos else
    let fl = List.map (fun epf -> ef_conv_enum epf) disj in
    List.fold_left (fun f1 f2 -> mkOr f1 f2 None no_pos) (List.hd fl) (List.tl fl)

(* ef_imply :  ante:ef_pure_disj -> conseq:ef_pure_disj -> bool *)
(* does ante --> conseq *)
(* convert ante with ef_conv_enum *)
(* convert conseq with ef_conv *)

let ef_imply (ante:ef_pure_disj) (conseq:ef_pure_disj) : bool =
  let a_f = ef_conv_enum_disj ante in
  let c_f = ef_conv_disj conseq in
  (* a_f --> c_f *)
  let f = mkAnd a_f (mkNot_s c_f) no_pos in
  not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f))

(* ef_unsat :  ef_pure -> bool *)
(* remove unsat terms *)
(* convert unsat with ef_conv_enum *)
let ef_unsat  (f:ef_pure) : bool =
  (* use ef_conv_enum *)
  let cf = ef_conv_enum f in
  (* if unsat(cf) return true *)
  not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure cf))

(* ef_unsat_disj :  ef_pure_disj -> ef_pure_disj *)
(* remove unsat terms *)
(* convert unsat with ef_conv_enum *)
let ef_unsat_disj  (disj:ef_pure_disj) : ef_pure_disj =
  List.filter (fun f -> not(ef_unsat f)) disj

(* using Cformula *)

let build_ef_ef_pures (efp1 : ef_pure) (efp2 : ef_pure) : ef_pure =
  let (baga1, pure1) = efp1 in
  let (baga2, pure2) = efp2 in
  (baga1@baga2, mkAnd pure1 pure2 no_pos)

let build_ef_ef_pure_disjs (efpd1 : ef_pure_disj) (efpd2 : ef_pure_disj) : ef_pure_disj =
  List.fold_left (fun refpd1 efp1 ->
      let refpd2 = List.fold_left (fun refpd2 efp2 ->
          refpd2@[build_ef_ef_pures efp1 efp2]
      ) [] efpd2 in
      refpd1@refpd2
  ) [] efpd1

let rec build_ef_heap_formula (map : (ident, ef_pure_disj) Hashtbl.t) (hf : Cformula.h_formula) : ef_pure_disj =
  match hf with
    | Cformula.Star sf ->
          let efpd1 = build_ef_heap_formula map sf.Cformula.h_formula_star_h1 in
          let efpd2 = build_ef_heap_formula map sf.Cformula.h_formula_star_h2 in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.StarMinus smf ->
          let efpd1 = build_ef_heap_formula map smf.Cformula.h_formula_starminus_h1 in
          let efpd2 = build_ef_heap_formula map smf.Cformula.h_formula_starminus_h2 in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.Conj cf ->
          let efpd1 = build_ef_heap_formula map cf.Cformula.h_formula_conj_h1 in
          let efpd2 = build_ef_heap_formula map cf.Cformula.h_formula_conj_h2 in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.ConjStar csf ->
          let efpd1 = build_ef_heap_formula map csf.Cformula.h_formula_conjstar_h1 in
          let efpd2 = build_ef_heap_formula map csf.Cformula.h_formula_conjstar_h2 in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.ConjConj ccf ->
          let efpd1 = build_ef_heap_formula map ccf.Cformula.h_formula_conjconj_h1 in
          let efpd2 = build_ef_heap_formula map ccf.Cformula.h_formula_conjconj_h2 in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.Phase pf ->
          let efpd1 = build_ef_heap_formula map pf.Cformula.h_formula_phase_rd in
          let efpd2 = build_ef_heap_formula map pf.Cformula.h_formula_phase_rw in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.DataNode dnf ->
          let sv = dnf.Cformula.h_formula_data_node in
          [([sv], mkTrue no_pos)]
    | Cformula.ViewNode vnf ->
          let efpd = Hashtbl.find map vnf.Cformula.h_formula_view_name in
          efpd
    | Cformula.ThreadNode tnf ->
          let sv = tnf.Cformula.h_formula_thread_node in
          [([sv], mkTrue no_pos)]
    | Cformula.Hole _
    | Cformula.FrmHole _
    | Cformula.HRel _
    | Cformula.HTrue -> [([], mkTrue no_pos)]
    | Cformula.HFalse
    | Cformula.HEmp -> [([], mkFalse no_pos)]

(* let rec build_ef_p_formula (map : (Cast.view_decl, ef_pure_disj) Hashtbl.t) (pf : p_formula) : ef_pure_disj = *)
(*   [([], mkFalse no_pos)] *)

(* let build_ef_b_formula (map : (Cast.view_decl, ef_pure_disj) Hashtbl.t) (bf : b_formula) : ef_pure_disj = *)
(*   let (pf, _) = bf in *)
(*   build_ef_p_formula map pf *)

let rec build_ef_pure_formula (map : (ident, ef_pure_disj) Hashtbl.t) (pf : formula) : ef_pure_disj =
  (* match pf with *)
  (*   | BForm (bf, _) -> *)
  (*         build_ef_b_formula map bf *)
  (*   | And (f1, f2, _) *)
  (*   | Or (f1, f2, _, _) -> *)
  (*         let efpd1 = build_ef_pure_formula map f1 in *)
  (*         let efpd2 = build_ef_pure_formula map f2 in *)
  (*         build_ef_ef_pure_disjs efpd1 efpd2 *)
  (*   | AndList fl -> *)
  (*         let (_, f) = List.hd fl in *)
  (*         let efpd1 = build_ef_pure_formula map f in *)
  (*         List.fold_left (fun efpd1 (_, f) -> *)
  (*             let efpd2 = build_ef_pure_formula map f in *)
  (*             build_ef_ef_pure_disjs efpd1 efpd2) efpd1 (List.tl fl) *)
  (*   | Not (f, _, _) *)
  (*   | Forall (_, f, _, _) *)
  (*   | Exists (_, f, _, _) -> *)
  (*         build_ef_pure_formula map f *)
  [([],pf)]


(* build_ef_formula : map -> cformula --> ef_pure_disj *)
(* (b1,p1) * (b2,p2) --> (b1 U b2, p1/\p2) *)
(* (b1,p1) & ([],p2) --> (b1, p1/\p2) *)
(* x->node(..)       --> ([x],true) *)
(* p(...)            --> inv(p(..)) *)
let rec build_ef_formula (map : (ident, ef_pure_disj) Hashtbl.t) (cf : Cformula.formula) : ef_pure_disj =
  match cf with
    | Cformula.Base bf ->
          let bh = bf.Cformula.formula_base_heap in
          let bp = (Mcpure.pure_of_mix bf.Cformula.formula_base_pure) in
          let efpd1 = build_ef_heap_formula map bh in
          let efpd2 = build_ef_pure_formula map bp in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.Or orf ->
          let efpd1 = build_ef_formula map orf.Cformula.formula_or_f1 in
          let efpd2 = build_ef_formula map orf.Cformula.formula_or_f2 in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.Exists ef ->
          let eh = ef.Cformula.formula_exists_heap in
          let ep = (Mcpure.pure_of_mix ef.Cformula.formula_exists_pure) in
          let efpd1 = build_ef_heap_formula map eh in
          let efpd2 = build_ef_pure_formula map ep in
          build_ef_ef_pure_disjs efpd1 efpd2

(* using Cast *)

(* build_ef_view : map -> view_decl --> ef_pure_disj *)
(* view  ls1<self,p> == ..ls1<..>..ls2<..>... *)
(* map   ls1<self,p> == [(b1,f1)] *)
(*       ls2<self,p> == [(b2,f2)] *)
let build_ef_view (map : (ident, ef_pure_disj) Hashtbl.t) (view_decl : Cast.view_decl) : ef_pure_disj =
  List.flatten (List.map (fun (cf,_) -> build_ef_formula map cf) view_decl.Cast.view_un_struc_formula)

(* fix_test :  map -> view_list:[view_decl] -> inv_list:[ef_pure_disj] -> bool *)
(* does view(inv) --> inv *)
(* ls<self,p> == .... *)
(* inv<self,p> == ([],true) *)
(* let lhs_list = List.map (build map) view_list in *)
(* let rhs_list = inv_list in *)
(* let pair_list = List.combine lhs_list rhs_list in *)
(* let r_list = List.map (fun (a,c) -> ef_imply a c) pair_list in *)
let fix_test (map : (ident, ef_pure_disj) Hashtbl.t) (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list) : bool =
  let lhs_list = List.map (fun vd ->
      Hashtbl.find map vd.Cast.view_name) view_list in
  let rhs_list = inv_list in
  let pair_list = List.combine lhs_list rhs_list in
  let r_list = List.map (fun (a, c) -> ef_imply a c) pair_list in
  try
    let _ = List.find (fun r -> r = false) r_list in
    false
  with Not_found -> true

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
let fix_ef (view_list : Cast.view_decl list) (disjunct_num : int) : ef_pure_disj list =
  let map = Hashtbl.create 1 in
  let _ = List.iter (fun vd -> Hashtbl.add map vd.Cast.view_name []) view_list in
  let inv_list = List.fold_left (fun inv_list vd ->
      inv_list@[(build_ef_view map vd)]) [] view_list in
  let rec helper map view_list inv_list =
    if fix_test map view_list inv_list
    then
      inv_list
    else
      let _ = List.iter (fun (vd,inv) ->
          Hashtbl.replace map vd.Cast.view_name inv) (List.combine view_list inv_list) in
      let inv_list = List.fold_left (fun inv_list vd ->
          inv_list@[(build_ef_view map vd)]) [] view_list in
      helper map view_list inv_list
  in
  helper map view_list inv_list
