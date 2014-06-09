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

let disj_num = ref 0

(* let is_null_const_exp_for_expure (e : exp) : bool = *)
(*   match e with *)
(*     | Null _ -> true *)
(*     | Var (v,_) -> (name_of_spec_var v) = "null" *)
(*     | _ -> false *)

let rec remove_redundant_helper_for_expure ls rs =
  match ls with
    | [] -> rs
    | f::fs -> if List.exists (equalFormula f) fs then
        remove_redundant_helper_for_expure fs rs
      else
        remove_redundant_helper_for_expure fs rs@[f]
(*         else (match f with *)
(*           | BForm ((Eq(e1, e2, _), _) ,_) -> if (eq_exp_no_aset e1 e2) (\* || (is_null_const_exp_for_expure e1 && is_null_const_exp_for_expure e2) *\) then *)
(*                 remove_redundant_helper_for_expure fs rs *)
(*               else remove_redundant_helper_for_expure fs rs@[f] *)
(*           | BForm ((Lte(IConst (0,_), IConst (0,_), _), _) ,_) -> remove_redundant_helper_for_expure fs rs *)
(*           | _ -> remove_redundant_helper_for_expure fs rs@[f] *)
(*         ) *)

let remove_redundant_for_expure (f:formula):formula =
  let l_conj = split_conjunctions f in
  let prun_l = remove_redundant_helper_for_expure l_conj [] in
  join_conjunctions prun_l

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
  match baga with
    | [] -> mkTrue no_pos
    | h::ts ->
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

let ef_conv_disj_ho conv disj : formula =
  List.fold_left (fun f ep ->
      mkOr f (conv ep) None no_pos
  ) (mkFalse no_pos) disj
  (* match disj with *)
  (*   | [] -> mkFalse no_pos *)
  (*   | h::ts -> *)
  (*         let rf = List.fold_left (fun f1 efp -> *)
  (*             mkOr f1 (conv efp) None no_pos *)
  (*         ) (conv h) ts in *)
  (*         rf *)

let ef_conv_disj_x (disj : ef_pure_disj) : formula =
  ef_conv_disj_ho ef_conv disj

let ef_conv_disj (disj : ef_pure_disj) : formula =
  Debug.no_1 "ef_conv_disj" string_of_ef_pure_disj string_of_pure_formula
      ef_conv_disj_x disj

let ef_conv_enum_disj_x (disj : ef_pure_disj) : formula =
  ef_conv_disj_ho ef_conv_enum disj

let ef_conv_enum_disj (disj : ef_pure_disj) : formula =
  Debug.no_1 "ef_conv_enum_disj" string_of_ef_pure_disj string_of_pure_formula
      ef_conv_enum_disj_x disj

(* ef_imply_disj :  ante:ef_pure_disj -> conseq:ef_pure_disj -> bool *)
(* does ante --> conseq *)
(* convert ante with ef_conv_enum_disj *)
(* convert conseq with ef_conv_disj *)

(* ef_unsat_disj :  ef_pure_disj -> ef_pure_disj *)
(* remove unsat terms *)
(* convert unsat with ef_conv_enum *)
(* let elim_unsat_disj_x (disj : ef_pure_disj) : ef_pure_disj = *)
(*   List.filter (fun f -> not(ef_unsat f)) disj *)

(* let elim_unsat_disj (disj : ef_pure_disj) : ef_pure_disj = *)
(*   Debug.no_1 "elim_unsat_disj" string_of_ef_pure_disj string_of_ef_pure_disj *)
(*       elim_unsat_disj_x disj *)

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

(*
    x = x -> true
    x != x -> false (exception)
    x = ev -> true
*)
let filter_formula ex_vars lst  =
  try
    Some (List.filter
        (fun pf ->
            let flag =
              match pf with
                | BForm((p,_),_) ->
                      (match p with
                        | Eq (e1,e2,_) -> eqExp e1 e2
                        | Neq(e1,e2,_) ->
                              if eqExp e1 e2 then failwith "exception -> mkFalse"
                              else false
                        | _ -> false)
                | _ -> false in
            if flag then false
            else
              let svl = fv pf in
              not(List.exists (fun v -> List.exists (eq_spec_var v) ex_vars) svl)
        ) lst)
  with _ -> None

(*
    ex v. x=v & v!=y  --> x!=y
    ex v. x=v & v=k & v!=y  --> x=k & x!=y
*)

(* elim clause with not relevant spec var *)
(* self > 0 & x = y -> [self,y] -> self > 0 *)
let elim_clause (pf : formula) (ex_vars : spec_var list) : formula =
  (* let svl = fv pf in *)
  (* let filtered_svl = List.filter (fun sv -> *)
  (*     let SpecVar(_,name,_) = sv in *)
  (*     not (name="self" or (List.mem sv args))) svl in *)
  (* let _ = Debug.tinfo_hprint (pr_list (string_of_typed_spec_var)) filtered_svl no_pos in *)
  (* drop_svl_pure pf filtered_svl *)
  let conj_list = list_of_conjs pf in
  match filter_formula ex_vars conj_list with
    | None -> mkFalse no_pos
    | Some lst ->
          List.fold_left (fun r pf -> mkAnd r pf no_pos) (mkTrue no_pos) lst
 (* let filtered_conj_list = List.filter (fun pf -> *)
 (*      let svl = fv pf in *)
 (*      not(List.exists (fun v -> List.exists (eq_spec_var v) ex_vars) svl) *)
 (*      (\* try *\) *)
 (*      (\*   let _ = List.find (fun sv -> *\) *)
 (*      (\*       let SpecVar(_, name, _)  = sv in *\) *)
 (*      (\*       (not (name = "self")) && (not (List.mem sv args)) *\) *)
 (*      (\*   ) svl in false *\) *)
 (*      (\* with Not_found -> true *\) *)
 (*  ) conj_list in *)
 (*   (\* WN : should we use Omega? will x!=y cause disjunct *\) *)
 (*  arith_simplify_new f *)
 (*  (\* Omega.simplify f *\) *)

let elim_clause (pf : formula) (args : spec_var list) : formula =
  Debug.no_2 "elim_clause" string_of_pure_formula (pr_list string_of_typed_spec_var) string_of_pure_formula
      elim_clause pf args

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
let ef_elim_exists_1 (svl : spec_var list) (epf : ef_pure) : ef_pure =
  let (baga,pure) = epf in
  (* let _ = Debug.binfo_pprint "ef_elim_exists" no_pos in *)
  (* let _ = Debug.binfo_pprint "==============" no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "svl" string_of_spec_var_list) svl no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "old baga" string_of_spec_var_list) baga no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "pure" Cprinter.string_of_pure_formula) pure no_pos in *)
  let p_aset = pure_ptr_equations pure in
  (* let _ = Debug.binfo_hprint (add_str "pure_ptr_eq" (pr_list (pr_pair string_of_typed_spec_var string_of_typed_spec_var))) p_aset no_pos in *)
  let p_aset = EMapSV.build_eset p_aset in
  let new_paset = EMapSV.elim_elems p_aset svl in
  (* let _ = Debug.binfo_hprint (add_str "eqmap" EMapSV.string_of) p_aset no_pos in *)
  (* let new_pure = EMapSV.domain eset2 in *)
  let mk_subs =
      List.map
        (fun v ->
            let lst = EMapSV.find_equiv_all v p_aset in
            let free = List.filter (fun v -> not(List.exists (eq_spec_var v) svl)) lst in
            match free with
              | [] -> (v,v)
              | f::_ -> (v,f)
        ) svl in
  (* let mk_subs = List.filter (fun (a,b) -> not(a==b)) mk_subs in *)
  (* let eq_all = List.map (fun v -> *)
  (*     let lst = EMapSV.find_equiv_all v p_aset in *)
  (*     let lst = if (List.length lst > 0) then lst else [v] in *)
  (*     List.filter (fun v -> not(List.exists (eq_spec_var v) svl)) lst *)
  (* ) baga in *)
  let new_baga = List.fold_left (fun acc v ->
      try
        let (a,b) = List.find (fun (vv,_) -> eq_spec_var v vv) mk_subs in
        if a==b then acc
        else b::acc
      with _ -> v::acc) [] baga in
  (* let _ = Debug.binfo_hprint (add_str "new baga" string_of_spec_var_list) new_baga no_pos in *)
  let equiv_pairs = EMapSV.get_equiv new_paset in
  let ps = string_of_spec_var in
  (* Debug.binfo_hprint (add_str "equiv_pairs" (pr_list (pr_pair ps ps))) equiv_pairs no_pos; *)
  let pure1 = apply_subs mk_subs pure in
  let new_pure = remove_redundant_for_expure (elim_clause pure1 svl) in
  (* let _ = Debug.binfo_hprint (add_str "pure" string_of_pure_formula) pure no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "pure1" string_of_pure_formula) pure1 no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "new pure" string_of_pure_formula) new_pure no_pos in *)
  (List.sort compare_sv new_baga, new_pure)

let ef_elim_exists_1 (svl : spec_var list) (epf : ef_pure) : ef_pure =
  Debug.no_2 "ef_elim_exists" string_of_typed_spec_var_list string_of_ef_pure string_of_ef_pure
      ef_elim_exists_1 svl epf

(* substitute baga *)
(* [self,y] -> [x,y] -> [self] -> [x] *)
(* let subst_baga_x (sst : (spec_var * spec_var) list) (baga : spec_var list) : spec_var list = *)
(*   let r = List.map (fun sv1 -> *)
(*       try *)
(*         let (_,sv2) = List.find (fun (arg,_) -> *)
(*             let SpecVar(_,id1,_) = sv1 in *)
(*             let SpecVar(_,arg_name,_) = arg in *)
(*             id1 = arg_name) sst *)
(*         in sv2 *)
(*       with Not_found -> sv1 *)
(*   ) baga in *)
(*   r *)

(* let subst_baga (sst : (spec_var * spec_var) list) (baga : spec_var list) : spec_var list = *)
(*   Debug.no_2 "subst_baga" (pr_list (pr_pair string_of_typed_spec_var string_of_typed_spec_var)) (pr_list string_of_typed_spec_var) (pr_list string_of_typed_spec_var) *)
(*       subst_baga_x sst baga *)

(* let rec norm_ef_pure_disj_x (disj : ef_pure_disj) : ef_pure_disj = *)
(*   match disj with *)
(*     | [] -> [] *)
(*     | hd::tl -> hd::(norm_ef_pure_disj_x ( *)
(*           List.filter (fun f -> *)
(*               not ((ef_imply f hd) && (ef_imply hd f)) *)
(*           ) tl *)
(*       )) *)

(* let norm_ef_pure_disj_1 (disj : ef_pure_disj) : ef_pure_disj = *)
(*   Debug.no_1 "norm_ef_pure_disj" string_of_ef_pure_disj string_of_ef_pure_disj *)
(*       norm_ef_pure_disj_x disj *)

(* using Cformula *)

(* let compare_prime v1 v2 = *)
(*   if v1==v2 then 0 *)
(*   else if v1==Unprimed then -1 *)
(*   else 1 *)

(* let compare_ident v1 v2 = String.compare v1 v2 *)

(* let compare_spec_var (sv1 : spec_var) (sv2 : spec_var) = match (sv1, sv2) with *)
(*   | (SpecVar (t1, v1, p1), SpecVar (t2, v2, p2)) -> *)
(*         let c = compare_ident v1 v2 in *)
(*         if c=0 then *)
(*           compare_prime p1 p2  *)
(*         else c *)

(* let rec merge_baga b1 b2 = *)
(*   match b1,b2 with *)
(*     | [],b | b,[] -> b *)
(*     | x1::t1, x2::t2 -> *)
(*           let c = compare_spec_var x1 x2 in *)
(*           if c<0 then x1::(merge_baga t1 b2) *)
(*           else if c>0 then x2::(merge_baga b1 t2) *)
(*           else failwith "detected false" *)

(* denote false/contradiction *)
(* ([], [], ("_"!="_")) *)
(* let false_ef_pure = ([], mkFalse no_pos)  *)

(* let star_ef_pures (efp1 : ef_pure) (efp2 : ef_pure) : ef_pure = *)
(*   if (efp1 == false_ef_pure) || (efp2==false_ef_pure) then false_ef_pure *)
(*   else *)
(*     let (baga1, pure1) = efp1 in *)
(*     let (baga2, pure2) = efp2 in *)
(*     try *)
(*       (merge_baga baga1 baga2, mkAnd pure1 pure2 no_pos) *)
(*     with _ -> false_ef_pure *)

(* let or_ef_pure_disjs (efpd1 : ef_pure_disj) (efpd2 : ef_pure_disj) : ef_pure_disj = *)
(*   List.filter (fun e -> not(e==false_ef_pure)) (efpd1@efpd2) *)

(* let star_ef_pure_disjs_x (efpd1 : ef_pure_disj) (efpd2 : ef_pure_disj) : ef_pure_disj = *)
(*   let res = *)
(*     List.map (fun efp1 -> List.map (fun efp2 -> star_ef_pures efp1 efp2) efpd2) efpd1 in *)
(*   let res = List.concat res in  *)
(*   List.filter (fun v -> not(ef_unsat v)) res *)
(*   (\* if (List.length efpd1 = 0) then *\) *)
(*   (\*   elim_trivial_disj (elim_unsat_disj efpd2) *\) *)
(*   (\* else if (List.length efpd2 = 0) then *\) *)
(*   (\*   elim_trivial_disj (elim_unsat_disj efpd1) *\) *)
(*   (\* else *\) *)
(*   (\*   List.fold_left (fun refpd1 efp1 -> *\) *)
(*   (\*       let refpd2 = List.fold_left (fun refpd2 efp2 -> *\) *)
(*   (\*           let new_ef_pure = star_ef_pures efp1 efp2 in *\) *)
(*   (\*           if (ef_unsat new_ef_pure) then *\) *)
(*   (\*             refpd2 *\) *)
(*   (\*           else if (ef_trivial new_ef_pure) then *\) *)
(*   (\*             refpd2 *\) *)
(*   (\*           else *\) *)
(*   (\*             refpd2@[new_ef_pure] *\) *)
(*   (\*       ) [] efpd2 in *\) *)
(*   (\*       refpd1@refpd2 *\) *)
(*   (\*   ) [] efpd1 *\) *)

(* let star_ef_pure_disjs (efpd1 : ef_pure_disj) (efpd2 : ef_pure_disj) : ef_pure_disj = *)
(*   Debug.no_2 "star_ef_pure_disjs" string_of_ef_pure_disj string_of_ef_pure_disj string_of_ef_pure_disj *)
(*       star_ef_pure_disjs_x efpd1 efpd2 *)

module type SV_TYPE =
sig
  type t
  val zero : t
  val is_zero : t -> bool
  val eq : t -> t -> bool
  val compare : t -> t -> int
  val string_of : t -> string
  val conv_var : t list -> spec_var list
  val from_var : spec_var list -> t list
  val merge_baga : t list -> t list -> t list
  val is_eq_baga : t list -> t list -> bool
end;;

module EPURE =
    functor (Elt : SV_TYPE) ->
struct
  type elem = Elt.t
  (* type epure = (elem list * (elem * elem) list * (elem * elem) list) *)
  type epure = (elem list * formula)
  type epure_disj = epure list
  (* let mk_spec_var e = SpecVar (UNK,Elt.string_of e,Unprimed) *)
  (* type baga_ty = .. *)
  let mk_false = ([], mkFalse no_pos)
  let is_false (e:epure) = (e == mk_false)
  let string_of (x:epure) = pr_pair (pr_list Elt.string_of) Cprinter.string_of_pure_formula x
  let string_of_disj lst = pr_list string_of lst
  let merge_baga b1 b2 = Elt.merge_baga b1 b2

  let mk_star efp1 efp2 =
    if (is_false efp1) || (is_false efp2) then mk_false
    else
      let (baga1, pure1) = efp1 in
      let (baga2, pure2) = efp2 in
      try
        let new_baga = merge_baga baga1 baga2 in
        let new_pure = mkAnd pure1 pure2 no_pos in
        (new_baga, new_pure)
        (* (merge_baga baga1 baga2, mkAnd pure1 pure2 no_pos) *)
      with _ -> mk_false

  let mk_star_disj_x (efpd1:epure_disj) (efpd2:epure_disj)  =
    let res =
      List.map (fun efp1 -> List.map (fun efp2 -> mk_star efp1 efp2) efpd2) efpd1 in
    let res = List.concat res in
    res
    (* List.filter (fun v -> not(is_false v)) res *)

  let mk_star_disj (efpd1:epure_disj) (efpd2:epure_disj) =
    Debug.no_2 "mk_star_disj" string_of_disj string_of_disj string_of_disj
        mk_star_disj_x efpd1 efpd2

  let mk_or_disj t1 t2 = t1@t2

  let conv_enum ((baga,f):epure) : formula =
    ef_conv_enum (Elt.conv_var baga,f)

  (* let conv_disj_ho conv (disj : epure list) : formula = *)
  (*   match disj with *)
  (*     | [] -> mkFalse no_pos *)
  (*     | h::ts -> *)
  (*           let rf = List.fold_left (fun f1 efp -> *)
  (*               mkOr f1 (conv efp) None no_pos *)
  (*           ) (conv h) ts in *)
  (*           rf *)
  (* let conv_disj_enum = conv_disj_ho conv_enum *)

  (* ef_unsat : ef_pure -> bool *)
  (* remove unsat terms *)
  (* convert unsat with ef_conv_enum *)
  let ef_unsat_0 (f : ef_pure) : bool =
    (* use ef_conv_enum *)
  let cf = ef_conv_enum f in
  (* if unsat(cf) return true *)
  not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure cf))

  (* DO NOT CALL DIRECTLY *)
  let ef_unsat_0 (f : ef_pure) : bool =
    Debug.no_1 "ef_unsat" string_of_ef_pure string_of_bool
        ef_unsat_0 f

  let unsat (b,f) = ef_unsat_0 (Elt.conv_var b, f)

  let norm (efp) =
    if unsat efp then mk_false
    else efp

  let elim_unsat_disj disj =
    List.filter (fun f -> not(unsat f)) disj

  let is_false_disj disj = disj==[]

  let mk_false_disj = []

  (* let unsat_disj disj = is_false_disj (norm_disj disj) *)

  let elim_exists (svl:spec_var list) (b,f) : epure =
    let (b,f) = ef_elim_exists_1 svl (Elt.conv_var b,f) in
    (Elt.from_var b, f)

  (* ef_imply : ante:ef_pure -> conseq:ef_pure -> bool *)
  (* does ante --> conseq *)
  (* convert ante with ef_conv_enum *)
  (* convert conseq with ef_conv *)

  let ef_imply_0 (ante : ef_pure) (conseq : ef_pure) : bool =
    let a_f = ef_conv_enum ante in
    let c_f = ef_conv conseq in
    (* a_f --> c_f *)
    let f = mkAnd a_f (mkNot_s c_f) no_pos in
    not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f))

  let ef_imply_0 (ante : ef_pure) (conseq : ef_pure) : bool =
    Debug.no_2 "ef_imply" string_of_ef_pure string_of_ef_pure string_of_bool
        ef_imply_0 ante conseq

  let imply ((b1,f1) as ante : epure) ((b2,f2) as conseq : epure) : bool =
    ef_imply_0 (Elt.conv_var b1,f1) (Elt.conv_var b2,f2)

  let is_eq_epure ((b1,f1) as ep1) ((b2,f2) as ep2) =
    if Elt.is_eq_baga b1 b2 then
      (imply ep1 ([],f2)) && (imply ep2 ([],f1))
    else false

  (* reducing duplicate? *)
  let norm_disj disj =
    let rec remove_duplicate (disj : epure_disj) : epure_disj =
      match disj with
        | [] -> []
        | hd::tl ->
              let new_tl = remove_duplicate (List.filter (fun ep ->
                  not (is_eq_epure hd ep)) tl) in
              hd::new_tl
    in
    remove_duplicate (List.filter (fun v -> not(is_false v)) (List.map norm disj))

  let ef_imply_disj_x (ante : ef_pure_disj) (conseq : ef_pure_disj) : bool =
    let a_f = ef_conv_enum_disj ante in
    let c_f = ef_conv_disj conseq in
    (* a_f --> c_f *)
    let f = mkAnd a_f (mkNot_s c_f) no_pos in
    not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f))

  let ef_imply_disj_0 (ante : ef_pure_disj) (conseq : ef_pure_disj) : bool =
    Debug.no_2 "ef_imply_disj" string_of_ef_pure_disj string_of_ef_pure_disj string_of_bool
        ef_imply_disj_x ante conseq

  let imply_disj (ante : epure_disj) (conseq : epure_disj) : bool =
    let f = List.map (fun (b,f) -> (Elt.conv_var b,f)) in
    ef_imply_disj_0 (f ante) (f conseq)

end

(* this is meant as more efficient baga module *)
module EPUREN =
    functor (Elt : SV_TYPE) ->
struct
  module EM = Gen.EqMap(Elt)
  type elem = Elt.t
  type emap = EM.emap
  (* baga, eq_map, ineq_list *)
  (* type epure = (elem list * (elem * elem) list * (elem * elem) list) *)
  type epure = (elem list * emap * (elem * elem) list)
  type epure_disj = epure list

  let mk_false = ([Elt.zero], EM.mkEmpty, [])
  let is_false (e:epure) = (e == mk_false)
  let pr1 = pr_list Elt.string_of
  let pr2 = pr_list (pr_pair Elt.string_of Elt.string_of)
  let string_of (x:epure) =
    pr_triple (add_str "BAGA" pr1) (add_str "EQ" EM.string_of) (add_str "INEQ" pr2) x

  let string_of_disj (x:epure_disj) = pr_list string_of x

  let merge_baga b1 b2 = Elt.merge_baga b1 b2

  let mk_star efp1 efp2 =
    if (is_false efp1) || (is_false efp2) then mk_false
    else
      let (baga1, eq1, neq1) = efp1 in
      let (baga2, eq2, neq2) = efp2 in
      try
        (merge_baga baga1 baga2, EM.merge_eset eq1 eq2, neq1@neq2)
      with _ -> mk_false

  let mk_star_disj (efpd1:epure_disj) (efpd2:epure_disj)  =
    let res =
      List.map (fun efp1 -> List.map (fun efp2 -> mk_star efp1 efp2) efpd2) efpd1 in
    List.concat res

  let mk_or_disj t1 t2 = t1@t2

  (* to be completed *)
  (* [(a,[b,c])] --> a=b & a=c *)
  let conv_eq (eq : emap) : formula =
    let fl = List.map (fun (e,k) ->
        let svl = Elt.conv_var (e::k) in
        if (List.length svl <= 1) then (* do we need this condition *)
          mkTrue no_pos
        else
          let v1 = List.hd svl in
          let eql = List.map (fun v2 ->
              mkEqVar v1 v2 no_pos
          ) (List.tl svl)
          in
          List.fold_left (fun f1 f2 ->
              mkAnd f1 f2 no_pos
          ) (mkTrue no_pos) eql
    ) eq in
    List.fold_left (fun f1 f2 ->
        mkAnd f1 f2 no_pos
    ) (mkTrue no_pos) fl

  (* to be completed *)
  (* [(a,b);(b,c)] --> a!=b & b!=c *)
  let conv_ineq (ieq : (elem * elem) list) : formula  =
    List.fold_left (fun f1 (v1, v2) ->
        let svl = Elt.conv_var (v1::[v2]) in
        let f2 = mkNeqVar (List.hd svl) (List.nth svl 1) no_pos in
        mkAnd f1 f2 no_pos
    ) (mkTrue no_pos) ieq

  let conv_enum ((baga,eq,inq) : epure) : formula =
    let f1 = conv_eq eq in
    let f2 = conv_ineq inq in
    let bf = baga_enum (Elt.conv_var baga) in
    mkAnd bf (mkAnd f1 f2 no_pos) no_pos

  let conv ((baga,eq,inq) : epure) : formula =
    let f1 = conv_eq eq in
    let f2 = conv_ineq inq in
    let bf = baga_conv (Elt.conv_var baga) in
    mkAnd bf (mkAnd f1 f2 no_pos) no_pos

  (* naive implementation *)
  let unsat (f : epure) : bool =
    let (baga,eq,ieq) = f in
    let baga_svl = Elt.conv_var baga in
    (* check if baga contains null *)
    if List.exists (fun sv -> (name_of_spec_var sv) = "null") baga_svl then
      true
    else
      (* check if there exists (a,b) in inq and eq *)
      List.exists (fun (e1, e2) ->
          List.exists (fun (e, k) ->
              let eq_el = (e::k) in
              List.mem e1 eq_el && List.mem e2 eq_el
          ) eq
      ) ieq
    (* let cf = conv_enum f in *)
    (* (\* if unsat(cf) return true *\) *)
    (* not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure cf)) *)

(*
    given (baga,eq,inq)
    contra if
       null \in baga
       duplicate (in baga - detected by merge)
       exists (a,b) in inq & eq
       exists (a,a) in eq (detected by norm,subs )

  how to detect:
       ([b], b=null, ..)?

*)

  let norm (efp) =
    if unsat efp then mk_false
    else efp

  let elim_unsat_disj disj =
    List.filter (fun f -> not(unsat f)) disj

  (* (\* reducing duplicate? *\) *)
  let norm_disj disj =
    List.filter (fun v -> not(is_false v)) (List.map norm disj)

  let is_false_disj disj = disj==[]

  let mk_false_disj = []

  (* to be completed *)
  let elim_exists (qel : elem list) (f : epure) : epure =
    let (baga,eq,ieq) = f in
    let new_eq = List.map (fun (e,k) ->
        let el = e::k in
        let filt_el = List.filter (fun e ->
            not (List.mem e qel)
        ) el in
        (* if List.length filt_el <= 1 then *)
        (*   () *)
        (* else *)
        (List.hd filt_el, List.tl filt_el) (* need to revised, maybe List.length filt_ef <= 1 *)
    ) eq in
    let new_ieq = List.filter (fun (e1, e2) ->
        not (List.mem e1 qel || List.mem e2 qel) (* need to revised, maybe we have to subs with new element in new_eq *)
    ) ieq in
    let new_baga = List.filter (fun e ->
        not (List.mem e qel)
    ) baga in (* need to revised, maybe we have to subs with new element in new_eq *)
    (new_baga,new_eq,new_ieq)

  (* let elim_exists (svl:spec_var list) (b,f) : epure = *)
  (*   let (b,f) = ef_elim_exists_1 svl (Elt.conv_var b,f) in *)
  (*   (Elt.from_var b,f) *)

  let imply (ante : epure) (conseq : epure) : bool =
    let a_f = conv_enum ante in
    let c_f = conv conseq in
    (* a_f --> c_f *)
    let f = mkAnd a_f (mkNot_s c_f) no_pos in
    not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f))

  let conv_enum_disj = ef_conv_disj_ho conv_enum
  let conv_disj      = ef_conv_disj_ho conv

  let imply_disj (ante : epure_disj) (conseq : epure_disj) : bool =
    let a_f = conv_enum_disj ante in
    let c_f = conv_disj conseq in
    (* a_f --> c_f *)
    let f = mkAnd a_f (mkNot_s c_f) no_pos in
    not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f))

(* TODO

  1. complete conv_eq & conv_neq
  2. complete elim_exists
  3. eq_epure ep1 ep2 (detect if two epures are equal, after norm)
  4. sort_epure_disj  (baga,...)
  5. strong_norm_epure (* must detect false, no x=x *)

*)
end

module EPureI = EPURE(SV)

type ef_pure_disj = EPureI.epure_disj

(* sel_hull_ef : f:[ef_pure_disj] -> disj_num (0 -> precise)
   -> [ef_pure_disj] *)
(* pre: 0<=disj_num<=100 & disj_num=0 -> len(f)<=100  *)
let sel_hull_ef_pure_disj (epd : ef_pure_disj) (disj_num : int) : ef_pure_disj =
  let rec helper epd n = 
    if n = 0 then
      []
    else
      (List.hd epd)::(helper (List.tl epd) (n - 1))
  in
  if (List.length epd < disj_num) then
    epd
  else
    helper epd disj_num
  (* let rec helper epd = *)
  (*   if (List.length epd) > disj_num *)
  (*   then *)
  (*     let f1 = List.hd epd in *)
  (*     let f2 = List.nth epd 1 in *)
  (*     let fl = List.tl (List.tl epd) in *)
  (*     helper ((EPureI.mk_star f1 f2)::fl) *)
  (*   else *)
  (*     epd *)
  (* in *)
  (* EPureI.norm_disj (helper epd) *)

let sel_hull_ef_pure_disj_list (epdl : ef_pure_disj list) (disj_num : int) : ef_pure_disj list =
  List.map (fun epd ->
      sel_hull_ef_pure_disj epd disj_num) epdl

(* WN : what is the purpose of args and args_map? *)
(*      why do we need init_map? can we assume false at beginning? *)
(* let rec build_ef_heap_formula_x (map : (ident, ef_pure_disj) Hashtbl.t) (hf : Cformula.h_formula) *)
(*       (args : spec_var list) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj = *)
(*   let helper (hfl : Cformula.h_formula list) : ef_pure_disj = *)
(*     List.fold_left (fun efpd hf -> *)
(*         let efpd_h = build_ef_heap_formula map hf args args_map init_map in *)
(*         let efpd_s = EPureI.mk_star_disj efpd efpd_h in *)
(*         let efpd_n = EPureI.norm_disj efpd_s in *)
(*         let _ = print_endline (string_of_int (List.length efpd_n)) in *)
(*         efpd_n *)
(*     ) [([], mkTrue no_pos)] hfl *)
(*   in *)
(*   match hf with *)
(*     | Cformula.Star sf -> *)
(*           helper (Cformula.split_star_conjunctions hf) *)
(*           (\* let efpd1 = build_ef_heap_formula map sf.Cformula.h_formula_star_h1 args args_map init_map in *\) *)
(*           (\* let efpd2 = build_ef_heap_formula map sf.Cformula.h_formula_star_h2 args args_map init_map in *\) *)
(*           (\* let efpd = EPureI.mk_star_disj efpd1 efpd2 in *\) *)
(*           (\* let _ = print_endline ("length before norm heap: " ^ string_of_int((List.length efpd))) in *\) *)
(*           (\* let efpd = EPureI.norm_disj efpd in *\) *)
(*           (\* let _ = print_endline ("length after norm heap: " ^ string_of_int((List.length efpd))) in *\) *)
(*           (\* let efpd = sel_hull_ef_pure_disj efpd !disj_num in *\) *)
(*           (\* let _ = print_endline ("length after hull heap: " ^ string_of_int((List.length efpd))) in *\) *)
(*           (\* efpd *\) *)
(*           (\* sel_hull_ef_pure_disj (EPureI.norm_disj efpd) !disj_num *\) *)
(*     | Cformula.StarMinus smf -> *)
(*           let efpd1 = build_ef_heap_formula map smf.Cformula.h_formula_starminus_h1 args args_map init_map in *)
(*           let efpd2 = build_ef_heap_formula map smf.Cformula.h_formula_starminus_h2 args args_map init_map in *)
(*           let efpd = EPureI.mk_star_disj efpd1 efpd2 in *)
(*           sel_hull_ef_pure_disj (EPureI.norm_disj efpd) !disj_num *)
(*     | Cformula.Conj cf -> *)
(*           let efpd1 = build_ef_heap_formula map cf.Cformula.h_formula_conj_h1 args args_map init_map in *)
(*           let efpd2 = build_ef_heap_formula map cf.Cformula.h_formula_conj_h2 args args_map init_map in *)
(*           let efpd = EPureI.mk_star_disj efpd1 efpd2 in *)
(*           sel_hull_ef_pure_disj (EPureI.norm_disj efpd) !disj_num *)
(*     | Cformula.ConjStar csf -> *)
(*           let efpd1 = build_ef_heap_formula map csf.Cformula.h_formula_conjstar_h1 args args_map init_map in *)
(*           let efpd2 = build_ef_heap_formula map csf.Cformula.h_formula_conjstar_h2 args args_map init_map in *)
(*           let efpd = EPureI.mk_star_disj efpd1 efpd2 in *)
(*           sel_hull_ef_pure_disj (EPureI.norm_disj efpd) !disj_num *)
(*     | Cformula.ConjConj ccf -> *)
(*           let efpd1 = build_ef_heap_formula map ccf.Cformula.h_formula_conjconj_h1 args args_map init_map in *)
(*           let efpd2 = build_ef_heap_formula map ccf.Cformula.h_formula_conjconj_h2 args args_map init_map in *)
(*           let efpd = EPureI.mk_star_disj efpd1 efpd2 in *)
(*           sel_hull_ef_pure_disj (EPureI.norm_disj efpd) !disj_num *)
(*     | Cformula.Phase pf -> *)
(*           let efpd1 = build_ef_heap_formula map pf.Cformula.h_formula_phase_rd args args_map init_map in *)
(*           let efpd2 = build_ef_heap_formula map pf.Cformula.h_formula_phase_rw args args_map init_map in *)
(*           let efpd = EPureI.mk_star_disj efpd1 efpd2 in *)
(*           sel_hull_ef_pure_disj (EPureI.norm_disj efpd) !disj_num *)
(*     | Cformula.DataNode dnf -> *)
(*           let sv = dnf.Cformula.h_formula_data_node in *)
(*           (\* [(elim_baga [sv] args, mkTrue no_pos)] *\) *)
(*           [([sv], mkTrue no_pos)] *)
(*     | Cformula.ViewNode vnf -> *)
(*           let svl = vnf.Cformula.h_formula_view_node::vnf.Cformula.h_formula_view_arguments in *)
(*           let efpd = *)
(*             try Hashtbl.find map vnf.Cformula.h_formula_view_name *)
(*             with Not_found -> *)
(*                 try *)
(*                   Hashtbl.find init_map vnf.Cformula.h_formula_view_name *)
(*                 with Not_found -> failwith "cannot find in init_map too" *)
(*           in *)
(*           let view_args = Hashtbl.find args_map vnf.Cformula.h_formula_view_name in *)
(*           List.map (fun (baga, pf) -> *)
(*               (\* let new_baga = (\\* elim_baga *\\) (subst_baga (List.combine view_args svl) baga) (\\* args *\\) in *\) *)
(*               let new_baga = subst_var_list (List.combine view_args svl) baga in *)
(*               let new_pf = (\* elim_clause *\) (subst (List.combine view_args svl) pf) (\* args *\) in *)
(*               (new_baga, new_pf) *)
(*           ) efpd *)
(*     | Cformula.ThreadNode tnf -> *)
(*           let sv = tnf.Cformula.h_formula_thread_node in *)
(*           (\* [(elim_baga [sv] args, mkTrue no_pos)] *\) *)
(*           [([sv], mkTrue no_pos)] *)
(*     | Cformula.Hole _ *)
(*     | Cformula.FrmHole _ *)
(*     | Cformula.HRel _ *)
(*     | Cformula.HTrue *)
(*     | Cformula.HEmp -> [([], mkTrue no_pos)] *)
(*     | Cformula.HFalse -> [([], mkFalse no_pos)] *)

(* let rec build_ef_p_formula (map : (Cast.view_decl, ef_pure_disj) Hashtbl.t) (pf : p_formula) : ef_pure_disj = *)
(*   [([], mkFalse no_pos)] *)

(* let build_ef_b_formula (map : (Cast.view_decl, ef_pure_disj) Hashtbl.t) (bf : b_formula) : ef_pure_disj = *)
(*   let (pf, _) = bf in *)
(*   build_ef_p_formula map pf *)

(* and build_ef_heap_formula (map : (ident, ef_pure_disj) Hashtbl.t) (cf : Cformula.h_formula) *)
(*       (args : spec_var list) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj = *)
(*   Debug.no_1 "build_ef_heap_formula" Cprinter.string_of_h_formula *)
(*       Cprinter.string_of_ef_pure_disj (fun _ -> *)
(*       build_ef_heap_formula_x map cf args args_map init_map) cf *)

let rec build_ef_heap_formula_new_x1 (map : (ident, ef_pure_disj) Hashtbl.t) (cf : Cformula.h_formula)
      (args : spec_var list) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) (pure_efpd : ef_pure_disj) : ef_pure_disj =
  match cf with
    | Cformula.Star _ ->
          let hfl = Cformula.split_star_conjunctions cf in
          List.fold_left (fun f hf ->
              let efpd_h = build_ef_heap_formula_new_x1 map hf args args_map init_map pure_efpd in
              let efpd_f = EPureI.mk_star_disj f efpd_h in
              (* let _ = print_endline ("length before norm heap: " ^ string_of_int(List.length efpd_f)) in *)
              let efpd_n = EPureI.norm_disj efpd_f in
              (* let _ = print_endline ("length after norm heap: " ^ string_of_int((List.length efpd_n))) in *)
              efpd_n) pure_efpd hfl
    | Cformula.DataNode dnf ->
          let sv = dnf.Cformula.h_formula_data_node in
          let heap_efpd = [([sv], mkTrue no_pos)] in
          let efpd = EPureI.mk_star_disj pure_efpd heap_efpd in
          let efpd_n = EPureI.norm_disj efpd in
          efpd_n
    | Cformula.ViewNode vnf ->
          let svl = vnf.Cformula.h_formula_view_node::vnf.Cformula.h_formula_view_arguments in
          let efpd =
            try Hashtbl.find map vnf.Cformula.h_formula_view_name
            with Not_found ->
                try
                  Hashtbl.find init_map vnf.Cformula.h_formula_view_name
                with Not_found -> failwith "cannot find in init_map too"
          in
          let view_args = Hashtbl.find args_map vnf.Cformula.h_formula_view_name in
          let heap_efpd = List.map (fun (baga, pf) ->
              let new_baga = subst_var_list (List.combine view_args svl) baga in
              let new_pf = (subst (List.combine view_args svl) pf) in
              (new_baga, new_pf)
          ) efpd in
          let efpd = EPureI.mk_star_disj pure_efpd heap_efpd in
          let efpd_n = EPureI.norm_disj efpd in
          efpd_n
    | _ -> pure_efpd (* [([], mkTrue no_pos)] *)

(* let rec build_ef_heap_formula_new_x (map : (ident, ef_pure_disj) Hashtbl.t) (cf : Cformula.h_formula) *)
(*       (args : spec_var list) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) (pure_efpd : ef_pure_disj) : ef_pure_disj = *)
(*   match cf with *)
(*     | Cformula.Star sf -> *)
(*           let efpd1 = build_ef_heap_formula_new map sf.Cformula.h_formula_star_h1 args args_map init_map pure_efpd in *)
(*           let efpd1_new = EPureI.mk_star_disj efpd1 pure_efpd in *)
(*           let efpd1_norm = EPureI.norm_disj efpd1_new in *)
(*           let efpd2 = build_ef_heap_formula_new map sf.Cformula.h_formula_star_h2 args args_map init_map pure_efpd in *)
(*           let efpd2_new = EPureI.mk_star_disj efpd2 pure_efpd in *)
(*           let efpd2_norm = EPureI.norm_disj efpd2_new in *)
(*           let efpd = EPureI.mk_star_disj efpd1_norm efpd2_norm in *)
(*           let _ = print_endline ("length before norm heap: " ^ string_of_int((List.length efpd))) in *)
(*           let efpd = EPureI.norm_disj efpd in *)
(*           let _ = print_endline ("length after norm heap: " ^ string_of_int((List.length efpd))) in *)
(*           let efpd = sel_hull_ef_pure_disj efpd !disj_num in *)
(*           let _ = print_endline ("length after hull heap: " ^ string_of_int((List.length efpd))) in *)
(*           efpd *)
(*     | Cformula.DataNode dnf -> *)
(*           let sv = dnf.Cformula.h_formula_data_node in *)
(*           (\* [(elim_baga [sv] args, mkTrue no_pos)] *\) *)
(*           let heap_efpd = [([sv], mkTrue no_pos)] in *)
(*           let efpd = EPureI.mk_star_disj pure_efpd heap_efpd in *)
(*           let efpd_n = EPureI.norm_disj efpd in *)
(*           efpd_n *)
(*     | Cformula.ViewNode vnf -> *)
(*           let svl = vnf.Cformula.h_formula_view_node::vnf.Cformula.h_formula_view_arguments in *)
(*           let efpd = *)
(*             try Hashtbl.find map vnf.Cformula.h_formula_view_name *)
(*             with Not_found -> *)
(*                 try *)
(*                   Hashtbl.find init_map vnf.Cformula.h_formula_view_name *)
(*                 with Not_found -> failwith "cannot find in init_map too" *)
(*           in *)
(*           let view_args = Hashtbl.find args_map vnf.Cformula.h_formula_view_name in *)
(*           let heap_efpd = List.map (fun (baga, pf) -> *)
(*               let new_baga = subst_var_list (List.combine view_args svl) baga in *)
(*               let new_pf = (subst (List.combine view_args svl) pf) in *)
(*               (new_baga, new_pf) *)
(*           ) efpd in *)
(*           let efpd = EPureI.mk_star_disj pure_efpd heap_efpd in *)
(*           let efpd_n = EPureI.norm_disj efpd in *)
(*           efpd_n *)
(*     | _ -> (\* [([], mkTrue no_pos)] *\) pure_efpd *)

and build_ef_heap_formula_new (map : (ident, ef_pure_disj) Hashtbl.t) (cf : Cformula.h_formula)
      (args : spec_var list) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) (pure_efpd : ef_pure_disj) : ef_pure_disj =
        build_ef_heap_formula_new_x1 map cf args args_map init_map pure_efpd

let rec build_ef_pure_formula (map : (ident, ef_pure_disj) Hashtbl.t) (pf : formula) (args : spec_var list) : ef_pure_disj =
  [([], pf)]

let build_ef_pure_formula (map : (ident, ef_pure_disj) Hashtbl.t) (pf : formula) (args : spec_var list) : ef_pure_disj =
  Debug.no_1 "build_ef_pure_formula" Cprinter.string_of_pure_formula
      Cprinter.string_of_ef_pure_disj (fun _ ->
      build_ef_pure_formula map pf args) pf

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
          let bp = (Mcpure.pure_of_mix bf.Cformula.formula_base_pure) in
          let bh = bf.Cformula.formula_base_heap in
          (* let efpd1 = build_ef_heap_formula map bh args args_map init_map in *)
          let efpd1 = build_ef_pure_formula map bp args in
          let efpd2 = build_ef_heap_formula_new map bh args args_map init_map efpd1 in
          efpd2
          (* let efpd = EPureI.mk_star_disj efpd1 efpd2 in *)
          (* EPureI.norm_disj efpd *)
    | Cformula.Or orf ->
          let efpd1 = build_ef_formula map orf.Cformula.formula_or_f1 args args_map init_map in
          let efpd2 = build_ef_formula map orf.Cformula.formula_or_f2 args args_map init_map in
          let efpd = EPureI.mk_or_disj efpd1 efpd2 in
          EPureI.norm_disj efpd
    | Cformula.Exists ef ->
          let ep = (Mcpure.pure_of_mix ef.Cformula.formula_exists_pure) in
          let eh = ef.Cformula.formula_exists_heap in
          (* let efpd1 = build_ef_heap_formula map eh args args_map init_map in *)
          let efpd1 = build_ef_pure_formula map ep args in
          let efpd2 = build_ef_heap_formula_new map eh args args_map init_map efpd1 in
          (* let efpd = EPureI.mk_star_disj efpd1 efpd2 in *)
          (* let _ = print_endline ("length before norm exists: " ^ string_of_int((List.length efpd))) in *)
          (* let efpd_n = EPureI.norm_disj efpd in *)
          (* let _ = print_endline ("length after norm exists: " ^ string_of_int((List.length efpd_n))) in *)
          let efpd_e = List.map (fun efp ->
              (EPureI.elim_exists ef.Cformula.formula_exists_qvars efp)) (* efpd_n *) efpd2 in
          (* let _ = print_endline ("length after elim exists: " ^ string_of_int((List.length efpd_e))) in *)
          let efpd_f = EPureI.norm_disj efpd_e in
          (* let _ = print_endline ("length final exists: " ^ string_of_int((List.length efpd_f))) in *)
          efpd_f

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
  let self_var = SpecVar(Named view_decl.Cast.view_data_name, self, Unprimed) in
  let args = self_var::view_decl.Cast.view_vars in
  let disj = List.flatten (List.map (fun (cf,_) ->
      (* let _ = print_endline (Cprinter.string_of_formula cf) in *)
      let disj = build_ef_formula map cf args args_map init_map in
      (* let _ = Debug.binfo_hprint (add_str "epd" string_of_ef_pure_disj) epd no_pos in *)
      disj
  ) view_decl.Cast.view_un_struc_formula) in
  (* let _ = print_endline ("disj = " ^ (EPureI.string_of_disj disj)) in *)
  disj

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
      EPureI.imply_disj a c) pair_list in
  not (List.exists (fun r -> r = false) r_list)

let fix_test (map : (ident, ef_pure_disj) Hashtbl.t) (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list) : bool =
  let pr1 x = string_of_int (List.length x) in
  let pr2 = pr_list Cprinter.string_of_ef_pure_disj in
  Debug.no_2 "fix_test" pr1 pr2 string_of_bool (fun _ _ -> (fix_test (map : (ident, ef_pure_disj) Hashtbl.t) (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list))) view_list inv_list

(* ef_find_equiv :  (spec_var) list -> ef_pure -> (spec_var) list *)
(* find equivalent id in the formula *)
(* e.g. [a,b] -> ([a,b,c], b=c ---> [a,c] *)
(*      to rename b with c *)

(* compute fixpoint iteration *)
(* strict upper bound 100 *)
(* fix_ef : [view_defn] -> disjunct_num (0 -> precise) -> [ef_pure_disj] *)
let fix_ef_x (view_list : Cast.view_decl list) (num : int) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj list =
  let map = Hashtbl.create 1 in
  let _ = disj_num := 100 in
  let _ = List.iter (fun vd ->
      Hashtbl.add map vd.Cast.view_name [];
  ) view_list in
  let inv_list = List.fold_left (fun inv_list vd ->
      let _ = Debug.tinfo_hprint (pr_list (pr_pair string_of_formula (fun _ -> ""))) vd.Cast.view_un_struc_formula no_pos in
      inv_list@[(build_ef_view map args_map vd init_map)]) [] view_list in
  (* let inv_list = List.map (fun epd -> elim_unsat_disj epd) inv_list in *)
  (* let inv_list = List.map (fun epd -> elim_trivial_disj epd) inv_list in *)
  (* let inv_list = sel_hull_ef inv_list disj_num in *)
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
      (* let inv_list = sel_hull_ef inv_list disj_num in *)
      let _ = Debug.tinfo_hprint (pr_list string_of_ef_pure_disj) inv_list no_pos in
      helper map view_list inv_list
  in
  let inv_list = helper map view_list inv_list in
  inv_list

let fix_ef (view_list : Cast.view_decl list) (disj_num : int) (args_map : (ident, spec_var list) Hashtbl.t) (init_map : (ident, ef_pure_disj) Hashtbl.t) : ef_pure_disj list =
  let pr_1 = pr_list (fun v -> v.Cast.view_name)  in
  Debug.no_2 "fix_ef" pr_1 string_of_int (pr_list Cprinter.string_of_ef_pure_disj)
      (fun _ _ -> fix_ef_x view_list disj_num args_map init_map) view_list disj_num

(* check whether the view has arithmetic or not *)
let is_ep_exp_arith_x (e : Cpure.exp) : bool =
  match e with
    | Var (sv,_) ->
          if (name_of_spec_var sv = Globals.waitlevel_name) then true else false
    | Null _ -> false
    | _ -> true
    (* | IConst _ *)
    (* | AConst _ *)
    (* | InfConst _ *)
    (* | FConst _ *)
    (* | Level _ *)
    (* | Add _ *)
    (* | Subtract _ *)
    (* | Mult _ *)
    (* | Div _ *)
    (* | Max _ *)
    (* | Min _ *)
    (* | TypeCast _ *)
    (* | Bag _ *)
    (* | BagUnion _ *)
    (* | BagIntersect _ *)
    (* | BagDiff _ *)
    (* | List _ *)
    (* | ListCons _ *)
    (* | ListHead _ *)
    (* | ListTail _ *)
    (* | ListLength _ *)
    (* | ListAppend _ *)
    (* | ListReverse _ *)
    (* | Tsconst _ *)
    (* | Bptriple _ *)
    (* | Func _ *)
    (* | ArrayAt _ -> true *)

let is_ep_exp_arith (e : Cpure.exp) : bool =
  Debug.no_1 "is_ep_exp_arith" string_of_formula_exp string_of_bool
      is_ep_exp_arith_x e

let is_ep_b_form_arith_x (b: b_formula) :bool =
  let (pf,_) = b in
  match pf with
    | Eq (e1,e2,_)
    | Neq (e1,e2,_) -> (is_ep_exp_arith e1) || (is_ep_exp_arith e2)
    | BConst _ -> false
    | _ -> true
    (* | Frm _ *)
    (* | BVar _ *)
    (* | SubAnn _ *)
    (* | LexVar _ *)
    (* | XPure _ *)
    (* | Lt _ *)
    (* | Lte _ *)
    (* | Gt _ *)
    (* | Gte _ *)
    (* | Eq _ *)
    (* | Neq _ *)
    (* | EqMax _ *)
    (* | EqMin _ *)
    (* | BagIn _ *)
    (* | BagNotIn _ *)
    (* | BagSub _ *)
    (* | BagMin _ *)
    (* | BagMax _ *)
    (* | VarPerm _ *)
    (* | ListIn _ *)
    (* | ListNotIn _ *)
    (* | ListAllN _ *)
    (* | ListPerm _ *)
    (* | RelForm _ -> true *)

let is_ep_b_form_arith (b: b_formula) : bool =
  Debug.no_1 "is_ep_b_form_arith" string_of_b_formula string_of_bool
      is_ep_b_form_arith_x b

let rec is_ep_pformula_arith_x (pf : Cpure.formula) : bool =
  match pf with
    | BForm (b,_) -> is_ep_b_form_arith b
    | And (f1,f2,_)
    | Or (f1,f2,_,_) -> (is_ep_pformula_arith f1) || (is_ep_pformula_arith f2)
    | Not (f,_,_)
    | Forall (_,f,_,_)
    | Exists (_,f,_,_) -> (is_ep_pformula_arith f)
    | AndList l -> List.exists (fun (_,pf) -> is_ep_pformula_arith pf) l

and is_ep_pformula_arith (pf : Cpure.formula) : bool =
  Debug.no_1 "is_ep_pformula_arith" string_of_pure_formula string_of_bool
      is_ep_pformula_arith_x pf

let rec is_ep_cformula_arith_x (f : Cformula.formula) : bool =
  match f with
    | Cformula.Base bf ->
          let bp = (Mcpure.pure_of_mix bf.Cformula.formula_base_pure) in
          is_ep_pformula_arith bp
    | Cformula.Or orf ->
          (is_ep_cformula_arith orf.Cformula.formula_or_f1) || (is_ep_cformula_arith orf.Cformula.formula_or_f2)
    | Cformula.Exists ef ->
          let ep = (Mcpure.pure_of_mix ef.Cformula.formula_exists_pure) in
          is_ep_pformula_arith ep

and is_ep_cformula_arith (f : Cformula.formula) : bool =
  Debug.no_1 "is_ep_cformula_arith" Cprinter.string_of_formula string_of_bool
      is_ep_cformula_arith_x f

let is_ep_view_arith_x (cv : Cast.view_decl) : bool =
  List.exists (fun (cf,_) -> is_ep_cformula_arith cf)
      cv.Cast.view_un_struc_formula

let is_ep_view_arith (cv : Cast.view_decl) : bool =
  let pr_1 = fun cv -> cv.Cast.view_name in
  let pr_1 = Cprinter.string_of_view_decl_short in
  Debug.no_1 "is_ep_view_arith" pr_1 string_of_bool
      is_ep_view_arith_x cv
