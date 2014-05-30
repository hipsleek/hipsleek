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
open Cprinter

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
let baga_conv_x (baga : spec_var list) : formula =
  if (List.length baga = 0) then
    mkTrue no_pos
  else if (List.length baga = 1) then
    mkGtVarInt (List.hd baga) 0 no_pos
  else
    let rec helper i j baga len =
      let f1 = mkNeqVar (List.nth baga i) (List.nth baga j) no_pos in
      if i = len - 2 && j = len - 1 then
        f1
      else if j = len - 1 then
        let f2 = helper (i + 1) (i + 2) baga len in
        mkAnd f1 f2 no_pos
      else
        let f2 = helper i (j + 1) baga len in
        mkAnd f1 f2 no_pos
    in
    let f1 = helper 0 1 baga (List.length baga) in
    let f2 = List.fold_left (fun f sv -> mkAnd f1 (mkGtVarInt sv 0 no_pos) no_pos)
      (mkGtVarInt (List.hd baga) 0 no_pos) (List.tl baga) in
    mkAnd f1 f2 no_pos

let baga_conv (baga : spec_var list) : formula =
  Debug.no_1 "baga" (pr_list string_of_typed_spec_var) string_of_pure_formula
      baga_conv_x baga

(* ef_conv :  ef_pure -> formula *)
(* conseq must use this *)
(* ([a,a,b],pure)  --> baga[a,ab] & a>0 & a>0 & b>01 & pure *)
let ef_conv_x ((baga,f) : ef_pure) : formula =
  let bf = baga_conv baga in
  mkAnd bf f no_pos

let ef_conv ((baga,f) : ef_pure) : formula =
  Debug.no_1 "ef_conv" string_of_ef_pure string_of_pure_formula
      ef_conv_x (baga,f)

(* ([a,a,b]  --> a=1 & a=2 & b=3 *)
let baga_enum_x (baga : spec_var list) : formula =
  if (List.length baga = 0) then
    mkTrue no_pos
  else
    let i = ref 1 in
    List.fold_left (fun f sv ->
        i := !i + 1;
        mkAnd f (mkEqVarInt sv !i no_pos) no_pos
    ) (mkEqVarInt (List.hd baga) !i no_pos) (List.tl baga)

let baga_enum (baga : spec_var list) : formula =
  Debug.no_1 "baga_enum" (pr_list string_of_typed_spec_var) string_of_pure_formula
      baga_enum_x baga

(* ef_conv_enum :  ef_pure -> formula *)
(* provide an enumeration that can be used by ante *)
(* ([a,a,b],pure)  --> a=1 & a=2 & a=3 & pure *)
let ef_conv_enum_x ((baga,f) : ef_pure) : formula =
  let bf = baga_enum baga in
  mkAnd bf f no_pos

let ef_conv_enum ((baga,f) : ef_pure) : formula =
  Debug.no_1 "ef_conv_enum" string_of_ef_pure string_of_pure_formula
      ef_conv_enum_x (baga,f)

let ef_conv_disj_x (disj : ef_pure_disj) : formula =
  if (List.length disj = 0) then
    mkFalse no_pos
  else
    let rf = List.fold_left (fun f1 efp ->
        (* let f2 = ef_conv efp in *)
        (* if isConstTrue f2 then *)
        (*   f1 *)
        (* else *)
        mkOr f1 (ef_conv efp) None no_pos
    ) (ef_conv (List.hd disj)) (List.tl disj) in
    rf

let ef_conv_disj (disj : ef_pure_disj) : formula =
  Debug.no_1 "ef_conv_disj" string_of_ef_pure_disj string_of_pure_formula
      ef_conv_disj_x disj

let ef_conv_enum_disj_x (disj : ef_pure_disj) : formula =
  if (List.length disj = 0) then
    mkFalse no_pos
  else
    List.fold_left (fun f efp ->
        mkOr f (ef_conv_enum efp) None no_pos
    ) (ef_conv_enum (List.hd disj)) (List.tl disj)

let ef_conv_enum_disj (disj : ef_pure_disj) : formula =
  Debug.no_1 "ef_conv_enum_disj" string_of_ef_pure_disj string_of_pure_formula
      ef_conv_enum_disj_x disj

(* ef_imply_disj :  ante:ef_pure_disj -> conseq:ef_pure_disj -> bool *)
(* does ante --> conseq *)
(* convert ante with ef_conv_enum_disj *)
(* convert conseq with ef_conv_disj *)

let ef_imply_disj_x (ante : ef_pure_disj) (conseq : ef_pure_disj) : bool =
  let a_f = ef_conv_enum_disj ante in
  let c_f = ef_conv_disj conseq in
  (* a_f --> c_f *)
  let f = mkAnd a_f (mkNot_s c_f) no_pos in
  not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f))

let ef_imply_disj (ante : ef_pure_disj) (conseq : ef_pure_disj) : bool =
  Debug.no_2 "ef_imply_disj" string_of_ef_pure_disj string_of_ef_pure_disj string_of_bool
      ef_imply_disj_x ante conseq

(* ef_imply :  ante:ef_pure -> conseq:ef_pure -> bool *)
(* does ante --> conseq *)
(* convert ante with ef_conv_enum *)
(* convert conseq with ef_conv *)

let ef_imply_x (ante : ef_pure) (conseq : ef_pure) : bool =
  let a_f = ef_conv_enum ante in
  let c_f = ef_conv conseq in
  (* a_f --> c_f *)
  let f = mkAnd a_f (mkNot_s c_f) no_pos in
  not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f))

let ef_imply (ante : ef_pure) (conseq : ef_pure) : bool =
  Debug.no_2 "ef_imply" string_of_ef_pure string_of_ef_pure string_of_bool
      ef_imply_x ante conseq

(* ef_unsat :  ef_pure -> bool *)
(* remove unsat terms *)
(* convert unsat with ef_conv_enum *)
let ef_unsat_x (f : ef_pure) : bool =
  (* use ef_conv_enum *)
  let cf = ef_conv_enum f in
  (* if unsat(cf) return true *)
  not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure cf))

let ef_unsat (f : ef_pure) : bool =
  Debug.no_1 "ef_unsat" string_of_ef_pure string_of_bool
      ef_unsat_x f

(* ef_unsat_disj :  ef_pure_disj -> ef_pure_disj *)
(* remove unsat terms *)
(* convert unsat with ef_conv_enum *)
let elim_unsat_disj_x (disj : ef_pure_disj) : ef_pure_disj =
  List.filter (fun f -> not(ef_unsat f)) disj

let elim_unsat_disj (disj : ef_pure_disj) : ef_pure_disj =
  Debug.no_1 "elim_unsat_disj" string_of_ef_pure_disj string_of_ef_pure_disj
      elim_unsat_disj_x disj

let ef_trivial_x (f : ef_pure) : bool =
  isConstTrue (ef_conv f)

let ef_trivial (f : ef_pure) : bool =
  Debug.no_1 "ef_trivial" string_of_ef_pure string_of_bool
      ef_trivial_x f

(* remove trivial term in disj *)
let elim_trivial_disj_x (disj : ef_pure_disj) : ef_pure_disj =
  List.filter (fun ep -> not (ef_trivial ep)) disj

let elim_trivial_disj (disj : ef_pure_disj) : ef_pure_disj =
  Debug.no_1 "elim_trivial_disj" string_of_ef_pure_disj string_of_ef_pure_disj
      elim_trivial_disj_x disj

(* elim clause with not relevant spec var *)
(* self > 0 & x = y -> [self,y] -> self > 0 *)
let elim_clause_x (pf : formula) (args : spec_var list) : formula =
  (* let svl = fv pf in *)
  (* let filtered_svl = List.filter (fun sv -> *)
  (*     let SpecVar(_,name,_) = sv in *)
  (*     not (name="self" or (List.mem sv args))) svl in *)
  (* let _ = Debug.tinfo_hprint (pr_list (string_of_typed_spec_var)) filtered_svl no_pos in *)
  (* drop_svl_pure pf filtered_svl *)
  let conj_list = list_of_conjs pf in
  let filtered_conj_list = List.filter (fun pf ->
      let svl = fv pf in
      try
        let _ = List.find (fun sv ->
            let SpecVar(_, name, _)  = sv in
            (not (name = "self")) && (not (List.mem sv args))
        ) svl in false
      with Not_found -> true
  ) conj_list in
  List.fold_left (fun r pf -> mkAnd r pf no_pos) (mkTrue no_pos) filtered_conj_list

let elim_clause (pf : formula) (args : spec_var list) : formula =
  Debug.no_2 "elim_clause" string_of_pure_formula (pr_list string_of_typed_spec_var) string_of_pure_formula
      elim_clause_x pf args

(* elim not relevant spec var from baga *)
(* [a,b,c] -> [a,d] -> [a] *)
let elim_baga_x (svl : spec_var list) (args : spec_var list) : spec_var list =
  List.filter (fun sv ->
      let SpecVar(_, name, _) = sv in
      (name = "self") || (List.mem sv args)) svl

let elim_baga (svl : spec_var list) (args : spec_var list) : spec_var list =
  Debug.no_2 "elim_baga" (pr_list string_of_typed_spec_var) (pr_list string_of_typed_spec_var) (pr_list string_of_typed_spec_var)
      elim_baga_x svl args

(* ef_elim_exists :  (spec_var) list -> ef_pure -> ef_pure *)
(* exists [u1,u2]. (baga,pf) *)
(*
  ex [u] :([u],u=self)
   ==> ([self],ex u. u=self)
   ==> ([self],true)
  ex [u,a] :([u,a],u=self)
   ==> ex [u,a] ([self,a], u=self)
   ==> (ex [u,a] [self,a], ex [u,a]. u=self)
   ==> ([self], true)

*)
(* remove unsat terms *)
let ef_elim_exists (svl : spec_var list) (epf : ef_pure) : ef_pure =
  let (baga,pure) = epf in
  (* let _ = Debug.binfo_pprint "ef_elim_exists" no_pos in *)
  (* let _ = Debug.binfo_pprint "==============" no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "svl" string_of_spec_var_list) svl no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "baga" string_of_spec_var_list) baga no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "pure" Cprinter.string_of_pure_formula) pure no_pos in *)
  let p_aset = pure_ptr_equations pure in
  (* let _ = Debug.binfo_hprint (add_str "pure_ptr_eq" (pr_list (pr_pair string_of_typed_spec_var string_of_typed_spec_var))) p_aset no_pos in *)
  let p_aset = EMapSV.build_eset p_aset in
  (* let eset2 = EMapSV.elim_elems p_aset svl in *)
  (* let _ = Debug.binfo_hprint (add_str "eqmap" EMapSV.string_of) p_aset no_pos in *)
  (* let new_pure = EMapSV.domain eset2 in *)
  let eq_all = List.map (fun v ->
      let lst = EMapSV.find_equiv_all v p_aset in
      let lst = if (List.length lst > 0) then lst else [v] in
      List.filter (fun v -> not(List.exists (eq_spec_var v) svl)) lst
  ) baga in
  let new_baga = List.fold_left (fun acc lst -> match lst with
    | [] -> acc
    | h::_ -> h::acc) [] eq_all in
  (* let _ = Debug.binfo_hprint (add_str "new baga" string_of_spec_var_list) new_baga no_pos in *)
  let new_pure = elim_clause pure new_baga in
  (* let _ = Debug.binfo_hprint (add_str "new pure" string_of_pure_formula) new_pure no_pos in *)
  (new_baga, new_pure)

let ef_elim_exists (svl : spec_var list) (epf : ef_pure) : ef_pure =
  Debug.no_2 "ef_elim_exists" string_of_typed_spec_var_list string_of_ef_pure string_of_ef_pure
      ef_elim_exists svl epf

(* substitute baga *)
(* [self,y] -> [x,y] -> [self] -> [x] *)
let subst_baga_x (sst : (spec_var * spec_var) list) (baga : spec_var list) : spec_var list =
  let r = List.map (fun sv1 ->
      try
        let (_,sv2) = List.find (fun (arg,_) ->
            let SpecVar(_,id1,_) = sv1 in
            let SpecVar(_,arg_name,_) = arg in
            id1 = arg_name) sst
        in sv2
      with Not_found -> sv1
  ) baga in
  r

let subst_baga (sst : (spec_var * spec_var) list) (baga : spec_var list) : spec_var list =
  Debug.no_2 "subst_baga" (pr_list (pr_pair string_of_typed_spec_var string_of_typed_spec_var)) (pr_list string_of_typed_spec_var) (pr_list string_of_typed_spec_var)
      subst_baga_x sst baga

let rec norm_ef_pure_disj_x (disj : ef_pure_disj) : ef_pure_disj =
  match disj with
    | [] -> []
    | hd::tl -> hd::(norm_ef_pure_disj_x (
          List.filter (fun f ->
              not ((ef_imply f hd) && (ef_imply hd f))
          ) tl
      ))

let norm_ef_pure_disj (disj : ef_pure_disj) : ef_pure_disj =
  Debug.no_1 "norm_ef_pure_disj" string_of_ef_pure_disj string_of_ef_pure_disj
      norm_ef_pure_disj_x disj

(* using Cformula *)

let build_ef_ef_pures (efp1 : ef_pure) (efp2 : ef_pure) : ef_pure =
  let (baga1, pure1) = efp1 in
  let (baga2, pure2) = efp2 in
  (baga1@baga2, mkAnd pure1 pure2 no_pos)

let build_ef_ef_pure_disjs_x (efpd1 : ef_pure_disj) (efpd2 : ef_pure_disj) : ef_pure_disj =
  if (List.length efpd1 = 0) then
    elim_trivial_disj (elim_unsat_disj efpd2)
  else if (List.length efpd2 = 0) then
    elim_trivial_disj (elim_unsat_disj efpd1)
  else
    List.fold_left (fun refpd1 efp1 ->
        let refpd2 = List.fold_left (fun refpd2 efp2 ->
            let new_ef_pure = build_ef_ef_pures efp1 efp2 in
            if (ef_unsat new_ef_pure) then
              refpd2
            else if (ef_trivial new_ef_pure) then
              refpd2
            else
              refpd2@[new_ef_pure]
        ) [] efpd2 in
        refpd1@refpd2
    ) [] efpd1

let build_ef_ef_pure_disjs (efpd1 : ef_pure_disj) (efpd2 : ef_pure_disj) : ef_pure_disj =
  Debug.no_2 "build_ef_ef_pure_disjs" string_of_ef_pure_disj string_of_ef_pure_disj string_of_ef_pure_disj
      build_ef_ef_pure_disjs_x efpd1 efpd2

let rec build_ef_heap_formula_x (map : (ident, ef_pure_disj) Hashtbl.t) (hf : Cformula.h_formula)
      (args : spec_var list) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj =
  match hf with
    | Cformula.Star sf ->
          let efpd1 = build_ef_heap_formula map sf.Cformula.h_formula_star_h1 args args_map init_map in
          let efpd2 = build_ef_heap_formula map sf.Cformula.h_formula_star_h2 args args_map init_map in
          let efpd = build_ef_ef_pure_disjs efpd1 efpd2 in
          efpd
    | Cformula.StarMinus smf ->
          let efpd1 = build_ef_heap_formula map smf.Cformula.h_formula_starminus_h1 args args_map init_map in
          let efpd2 = build_ef_heap_formula map smf.Cformula.h_formula_starminus_h2 args args_map init_map in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.Conj cf ->
          let efpd1 = build_ef_heap_formula map cf.Cformula.h_formula_conj_h1 args args_map init_map in
          let efpd2 = build_ef_heap_formula map cf.Cformula.h_formula_conj_h2 args args_map init_map in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.ConjStar csf ->
          let efpd1 = build_ef_heap_formula map csf.Cformula.h_formula_conjstar_h1 args args_map init_map in
          let efpd2 = build_ef_heap_formula map csf.Cformula.h_formula_conjstar_h2 args args_map init_map in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.ConjConj ccf ->
          let efpd1 = build_ef_heap_formula map ccf.Cformula.h_formula_conjconj_h1 args args_map init_map in
          let efpd2 = build_ef_heap_formula map ccf.Cformula.h_formula_conjconj_h2 args args_map init_map in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.Phase pf ->
          let efpd1 = build_ef_heap_formula map pf.Cformula.h_formula_phase_rd args args_map init_map in
          let efpd2 = build_ef_heap_formula map pf.Cformula.h_formula_phase_rw args args_map init_map in
          build_ef_ef_pure_disjs efpd1 efpd2
    | Cformula.DataNode dnf ->
          let sv = dnf.Cformula.h_formula_data_node in
          (* [(elim_baga [sv] args, mkTrue no_pos)] *)
          [([sv], mkTrue no_pos)]
    | Cformula.ViewNode vnf ->
          let svl = vnf.Cformula.h_formula_view_node::vnf.Cformula.h_formula_view_arguments in
          let efpd =
            try Hashtbl.find map vnf.Cformula.h_formula_view_name
            with Not_found -> Hashtbl.find init_map vnf.Cformula.h_formula_view_name
          in
          let view_args = Hashtbl.find args_map vnf.Cformula.h_formula_view_name in
          List.map (fun (baga, pf) ->
              let new_baga = (* elim_baga *) (subst_baga (List.combine view_args svl) baga) (* args *) in
              let new_pf = (* elim_clause *) (subst (List.combine view_args svl) pf) (* args *) in
              (new_baga, new_pf)
          ) efpd
    | Cformula.ThreadNode tnf ->
          let sv = tnf.Cformula.h_formula_thread_node in
          [(elim_baga [sv] args, mkTrue no_pos)]
    | Cformula.Hole _
    | Cformula.FrmHole _
    | Cformula.HRel _
    | Cformula.HTrue
    | Cformula.HEmp -> [([], mkTrue no_pos)]
    | Cformula.HFalse -> [([], mkFalse no_pos)]

(* let rec build_ef_p_formula (map : (Cast.view_decl, ef_pure_disj) Hashtbl.t) (pf : p_formula) : ef_pure_disj = *)
(*   [([], mkFalse no_pos)] *)

(* let build_ef_b_formula (map : (Cast.view_decl, ef_pure_disj) Hashtbl.t) (bf : b_formula) : ef_pure_disj = *)
(*   let (pf, _) = bf in *)
(*   build_ef_p_formula map pf *)

and build_ef_heap_formula (map : (ident, ef_pure_disj) Hashtbl.t) (cf : Cformula.h_formula)
      (args : spec_var list) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj =
  Debug.no_1 "build_ef_heap_formula" Cprinter.string_of_h_formula
      Cprinter.string_of_ef_pure_disj (fun _ ->
      build_ef_heap_formula_x map cf args args_map init_map) cf

let rec build_ef_pure_formula (map : (ident, ef_pure_disj) Hashtbl.t) (pf : formula) (args : spec_var list) : ef_pure_disj =
  [([], elim_clause pf args)]
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

(* build_ef_formula : map -> cformula --> ef_pure_disj *)
(* (b1,p1) * (b2,p2) --> (b1 U b2, p1/\p2) *)
(* (b1,p1) & ([],p2) --> (b1, p1/\p2) *)
(* x->node(..)       --> ([x],true) *)
(* p(...)            --> inv(p(..)) *)
let rec build_ef_formula_x (map : (ident, ef_pure_disj) Hashtbl.t) (cf : Cformula.formula)
      (args : spec_var list) (args_map : (ident, spec_var list) Hashtbl.t)
      (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj =
  match cf with
    | Cformula.Base bf ->
          let bh = bf.Cformula.formula_base_heap in
          let bp = (Mcpure.pure_of_mix bf.Cformula.formula_base_pure) in
          let efpd1 = build_ef_heap_formula map bh args args_map init_map in
          let efpd2 = build_ef_pure_formula map bp args in
          let efpd = build_ef_ef_pure_disjs efpd1 efpd2 in
          efpd
    | Cformula.Or orf ->
          let efpd1 = build_ef_formula map orf.Cformula.formula_or_f1 args args_map init_map in
          let efpd2 = build_ef_formula map orf.Cformula.formula_or_f2 args args_map init_map in
          let efpd = build_ef_ef_pure_disjs efpd1 efpd2 in
          efpd
    | Cformula.Exists ef ->
          let eh = ef.Cformula.formula_exists_heap in
          let ep = (Mcpure.pure_of_mix ef.Cformula.formula_exists_pure) in
          let efpd1 = build_ef_heap_formula map eh args args_map init_map in
          let efpd2 = build_ef_pure_formula map ep args in
          let efpd = build_ef_ef_pure_disjs efpd1 efpd2 in
          let efpd = List.map (fun efp ->
              ef_elim_exists ef.Cformula.formula_exists_qvars efp) efpd in
          elim_trivial_disj (elim_unsat_disj efpd)

and build_ef_formula (map : (ident, ef_pure_disj) Hashtbl.t) (cf : Cformula.formula)
      (args : spec_var list) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj =
  Debug.no_1 "build_ef_formula" Cprinter.string_of_formula
      Cprinter.string_of_ef_pure_disj (fun _ ->
      build_ef_formula_x map cf args args_map init_map) cf

(* using Cast *)

(* build_ef_view : map -> view_decl --> ef_pure_disj *)
(* view  ls1<self,p> == ..ls1<..>..ls2<..>... *)
(* map   ls1<self,p> == [(b1,f1)] *)
(*       ls2<self,p> == [(b2,f2)] *)
let build_ef_view_x (map : (ident, ef_pure_disj) Hashtbl.t) (args_map : (ident, spec_var list) Hashtbl.t) (view_decl : Cast.view_decl) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj =
  let self_var = SpecVar(UNK, self, Unprimed) in
  let args = self_var::view_decl.Cast.view_vars in
  let disj = List.flatten (List.map (fun (cf,_) ->
      let disj = build_ef_formula map cf args args_map init_map in
      (* let _ = Debug.binfo_hprint (add_str "epd" string_of_ef_pure_disj) epd no_pos in *)
      norm_ef_pure_disj disj
  ) view_decl.Cast.view_un_struc_formula) in
  norm_ef_pure_disj disj

let build_ef_view (map : (ident, ef_pure_disj) Hashtbl.t) (args_map : (ident, spec_var list) Hashtbl.t) (view_decl : Cast.view_decl) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj =
  let pr_view_name vd = vd.Cast.view_name in
  Debug.no_1 "build_ef_view" pr_view_name string_of_ef_pure_disj (fun _ ->
      build_ef_view_x map args_map view_decl init_map) view_decl

(* fix_test :  map -> view_list:[view_decl] -> inv_list:[ef_pure_disj] -> bool *)
(* does view(inv) --> inv *)
(* ls<self,p> == .... *)
(* inv<self,p> == ([],true) *)
(* let lhs_list = List.map (build map) view_list in *)
(* let rhs_list = inv_list in *)
(* let pair_list = List.combine lhs_list rhs_list in *)
(* let r_list = List.map (fun (a,c) -> ef_imply_disj a c) pair_list in *)
let fix_test (map : (ident, ef_pure_disj) Hashtbl.t) (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list) : bool =
  let lhs_list = inv_list in
  let rhs_list = List.map (fun vd ->
      Hashtbl.find map vd.Cast.view_name) view_list in
  let pair_list = List.combine lhs_list rhs_list in
  let r_list = List.map (fun (a, c) ->
      ef_imply_disj a c) pair_list in
  not (List.exists (fun r -> r = false) r_list)

(* ef_find_equiv :  (spec_var) list -> ef_pure -> (spec_var) list *)
(* find equivalent id in the formula *)
(* e.g. [a,b] -> ([a,b,c], b=c ---> [a,c] *)
(*      to rename b with c *)

(* sel_hull_ef : f:[ef_pure_disj] -> disj_num (0 -> precise)
   -> [ef_pure_disj] *)
(* pre: 0<=disj_num<=100 & disj_num=0 -> len(f)<=100  *)
let sel_hull_ef (f : ef_pure_disj list) (disj_num : int) : ef_pure_disj list =
  let rec helper epd =
    if (List.length epd) > disj_num
    then
      let f1 = List.hd epd in
      let f2 = List.nth epd 1 in
      let fl = List.tl (List.tl epd) in
      helper ((build_ef_ef_pures f1 f2)::fl)
    else
      epd
  in
  List.map (fun epd -> elim_unsat_disj (helper epd)) f

(* compute fixpoint iteration *)
(* strict upper bound 100 *)
(* fix_ef : [view_defn] -> disjunct_num (0 -> precise) -> [ef_pure_disj] *)
let fix_ef (view_list : Cast.view_decl list) (disj_num : int) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj list =
  let map = Hashtbl.create 1 in
  let _ = List.iter (fun vd ->
      Hashtbl.add map vd.Cast.view_name [];
  ) view_list in
  let inv_list = List.fold_left (fun inv_list vd ->
      let _ = Debug.tinfo_hprint (pr_list (pr_pair string_of_formula (fun _ -> ""))) vd.Cast.view_un_struc_formula no_pos in
      inv_list@[(build_ef_view map args_map vd init_map)]) [] view_list in
  (* let inv_list = List.map (fun epd -> elim_unsat_disj epd) inv_list in *)
  (* let inv_list = List.map (fun epd -> elim_trivial_disj epd) inv_list in *)
  let inv_list = sel_hull_ef inv_list disj_num in
  let _ = Debug.tinfo_hprint (pr_list string_of_ef_pure_disj) inv_list no_pos in
  let rec helper map view_list inv_list =
    if fix_test map view_list inv_list
    then
      inv_list
      (* let r_list = List.fold_left (fun r_list vd -> *)
      (*     r_list@[Hashtbl.find map vd.Cast.view_name]) [] view_list in *)
      (* r_list *)
    else
      let _ = List.iter (fun (vd,inv) ->
          Hashtbl.replace map vd.Cast.view_name inv) (List.combine view_list inv_list) in
      let inv_list = List.fold_left (fun inv_list vd ->
          inv_list@[(build_ef_view map args_map vd init_map)]) [] view_list in
      (* let inv_list = List.map (fun epd -> elim_unsat_disj epd) inv_list in *)
      (* let inv_list = List.map (fun epd -> elim_trivial_disj epd) inv_list in *)
      let inv_list = sel_hull_ef inv_list disj_num in
      let _ = Debug.tinfo_hprint (pr_list string_of_ef_pure_disj) inv_list no_pos in
      helper map view_list inv_list
  in
  let inv_list = helper map view_list inv_list in
  inv_list

let fix_ef (view_list : Cast.view_decl list) (disj_num : int) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj list =
  let pr_1 = pr_list (fun v -> v.Cast.view_name)  in
  Debug.no_2 "fix_ef" pr_1 string_of_int (pr_list Cprinter.string_of_ef_pure_disj)
      (fun _ _ -> fix_ef view_list disj_num args_map init_map) view_list disj_num

