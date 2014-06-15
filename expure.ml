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

(* let ef_trivial_x (f : ef_pure) : bool = *)
(*   isConstTrue (ef_conv f) *)

(* let ef_trivial (f : ef_pure) : bool = *)
(*   Debug.no_1 "ef_trivial" string_of_ef_pure string_of_bool *)
(*       ef_trivial_x f *)

(* (\* remove trivial term in disj *\) *)
(* let elim_trivial_disj_x (disj : ef_pure_disj) : ef_pure_disj = *)
(*   List.filter (fun ep -> not (ef_trivial ep)) disj *)

(* let elim_trivial_disj (disj : ef_pure_disj) : ef_pure_disj = *)
(*   Debug.no_1 "elim_trivial_disj" string_of_ef_pure_disj string_of_ef_pure_disj *)
(*       elim_trivial_disj_x disj *)

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
let ef_elim_exists_1 (svl : spec_var list) epf  =
  let (baga,pure) = epf in
  (* let _ = Debug.binfo_pprint "ef_elim_exists" no_pos in *)
  (* let _ = Debug.binfo_pprint "==============" no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "svl" string_of_spec_var_list) svl no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "old baga" string_of_spec_var_list) baga no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "pure" Cprinter.string_of_pure_formula) pure no_pos in *)
  let p_aset = pure_ptr_equations pure in
  (* let _ = Debug.binfo_hprint (add_str "pure_ptr_eq" (pr_list (pr_pair string_of_typed_spec_var string_of_typed_spec_var))) p_aset no_pos in *)
  let p_aset = EMapSV.build_eset p_aset in
  (* let new_paset = EMapSV.elim_elems p_aset svl in *)
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
  (* let equiv_pairs = EMapSV.get_equiv new_paset in *)
  (* let ps = string_of_spec_var in *)
  (* Debug.binfo_hprint (add_str "equiv_pairs" (pr_list (pr_pair ps ps))) equiv_pairs no_pos; *)
  let pure1 = apply_subs mk_subs pure in
  let new_pure = remove_redundant_for_expure (elim_clause pure1 svl) in
  (* let _ = Debug.binfo_hprint (add_str "pure" string_of_pure_formula) pure no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "pure1" string_of_pure_formula) pure1 no_pos in *)
  (* let _ = Debug.binfo_hprint (add_str "new pure" string_of_pure_formula) new_pure no_pos in *)
  (List.sort compare_sv new_baga, new_pure)

let ef_elim_exists_1 (svl : spec_var list) epf =
  (* Debug.no_2 "ef_elim_exists" string_of_typed_spec_var_list string_of_ef_pure string_of_ef_pure *)
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
  val conv_var_pairs : (t*t) list -> (spec_var * spec_var) list
  val from_var : spec_var list -> t list
  val from_var_pairs : (spec_var * spec_var) list -> (t*t) list
  val merge_baga : t list -> t list -> t list
  val is_eq_baga : t list -> t list -> bool
  val mk_elem : spec_var -> t
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
  let mk_true = [([], mkTrue no_pos)]

  let is_false (e:epure) = (e == mk_false)
  let string_of (x:epure) = pr_pair (pr_list Elt.string_of) Cprinter.string_of_pure_formula x
  let string_of_disj lst = pr_list string_of lst
  let mk_data sv = [([sv], mkTrue no_pos)] 

  let merge_baga b1 b2 = Elt.merge_baga b1 b2


  (* convert ptr to integer constraints *)
  (* ([a,a,b]  --> a!=a & a!=b & a!=b & a>0 & a>0 & b>0 *)
  let baga_conv baga : formula =
    let baga = Elt.conv_var baga in
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

  (* ef_conv :  ef_pure -> formula *)
  (* conseq must use this *)
  (* ([a,a,b],pure)  --> baga[a,ab] & a>0 & a>0 & b>01 & pure *)
  let ef_conv ((baga,f)) : formula =
    let bf = baga_conv baga in
    mkAnd bf f no_pos

  (* ([a,a,b]  --> a=1 & a=2 & b=3 *)
  let baga_enum baga : formula =
    let baga = Elt.conv_var baga in
    match baga with
      | [] -> mkTrue no_pos
      | h::ts ->
            let i = ref 1 in
            List.fold_left (fun f sv ->
                i := !i + 1;
              mkAnd f (mkEqVarInt sv !i no_pos) no_pos
            ) (mkEqVarInt (List.hd baga) !i no_pos) (List.tl baga)

  (* ef_conv_enum :  ef_pure -> formula *)
  (* provide an enumeration that can be used by ante *)
  (* ([a,a,b],pure)  --> a=1 & a=2 & a=3 & pure *)
  let ef_conv_enum ((baga,f)) : formula =
    let bf = baga_enum baga in
    mkAnd bf f no_pos

  let ef_conv_disj_ho conv disj : formula =
    List.fold_left (fun f ep ->
        mkOr f (conv ep) None no_pos
    ) (mkFalse no_pos) disj

  let ef_conv_disj_x disj : formula =
    ef_conv_disj_ho ef_conv disj

  let ef_conv_disj disj : formula =
    (* Debug.no_1 "ef_conv_disj" string_of_ef_pure_disj string_of_pure_formula *)
    ef_conv_disj_x disj

  let ef_conv_enum_disj_x disj : formula =
    ef_conv_disj_ho ef_conv_enum disj

  let ef_conv_enum_disj disj : formula =
    (* Debug.no_1 "ef_conv_enum_disj" string_of_ef_pure_disj string_of_pure_formula *)
      ef_conv_enum_disj_x disj

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

  let conv_enum (f:epure) : formula =
    ef_conv_enum f

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
  let ef_unsat_0 (f : epure) : bool =
    (* use ef_conv_enum *)
    let cf = ef_conv_enum f in
    (* if unsat(cf) return true *)
    not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure cf))

  (* DO NOT CALL DIRECTLY *)
  let ef_unsat_0 (f : epure) : bool =
    (* Debug.no_1 "ef_unsat" string_of_ef_pure string_of_bool *)
        ef_unsat_0 f

  let unsat (b,f) = ef_unsat_0 (b, f)

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

  let ef_imply_0 (ante : epure) (conseq : epure) : bool =
    let a_f = ef_conv_enum ante in
    let c_f = ef_conv conseq in
    (* a_f --> c_f *)
    let f = mkAnd a_f (mkNot_s c_f) no_pos in
    not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f))

  let ef_imply_0 (ante : epure) (conseq : epure) : bool =
    (* Debug.no_2 "ef_imply" string_of_ef_pure string_of_ef_pure string_of_bool *)
        ef_imply_0 ante conseq

  let imply (ante : epure) (conseq : epure) : bool =
    ef_imply_0 ante conseq

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

  let ef_imply_disj_x (ante : epure_disj) (conseq : epure_disj) : bool =
    let a_f = ef_conv_enum_disj ante in
    let c_f = ef_conv_disj conseq in
    (* a_f --> c_f *)
    let f = mkAnd a_f (mkNot_s c_f) no_pos in
    not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f))

  let ef_imply_disj_0 (ante : epure_disj) (conseq : epure_disj) : bool =
    (* Debug.no_2 "ef_imply_disj" string_of_ef_pure_disj string_of_ef_pure_disj string_of_bool *)
        ef_imply_disj_x ante conseq

  let imply_disj (ante : epure_disj) (conseq : epure_disj) : bool =
    let f = List.map (fun (b,f) -> (b,f)) in
    ef_imply_disj_0 (f ante) (f conseq)

  let pair_cmp (x1,x2) (y1,y2) = 
    let c = Elt.compare x1 y1 in
    if c==0 then Elt.compare x2 y2
    else c

  let subst_elem sst v =
    if Elt.is_zero v then v
    else try
      let (_,t) = List.find (fun (w,_) -> Elt.eq w v) sst in
      t
    with _ -> failwith ("subst_elem : cannot find elem "^Elt.string_of v)

  let subst_epure sst ((baga,f) as ep) = 
    let subs_fn = subst_elem sst in
    let new_baga = List.map (subs_fn) baga in
    let new_f = subst (Elt.conv_var_pairs sst) f in
    (new_baga,new_f)

  let subst_epure_disj sst (lst:epure_disj) =
    List.map (subst_epure sst) lst

(*
            List.map (fun (baga, eq, ineq) ->
              let new_baga = subst_var_list sst baga in
              let eqf = EPureI.conv_eq eq in
              let new_eqf = subst sst eqf in
              let p_aset = pure_ptr_equations new_eqf in
              let new_eq = EMapSV.build_eset p_aset in
              let ineqf = EPureI.conv_ineq ineq in
              let new_ineqf = subst sst ineqf in
              let new_ineq = get_ineq new_ineqf in
              (* let new_pf = subst (List.combine view_args svl) pf in *)
              (new_baga, new_eq, new_ineq)
          ) efpd in
*)

  let mk_epure (pf:formula) = 
    [([], pf)]

  let to_cpure (ep : epure) = ep

  let to_cpure_disj (epd : epure_disj) = epd

  let from_cpure (ep : ef_pure) = ep

  let from_cpure_disj (epd : ef_pure_disj) = epd

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
  let mk_true = [([], EMapSV.mkEmpty, [])]

  let is_false (e:epure) = (e == mk_false)
  let pr1 = pr_list Elt.string_of
  let pr2 = pr_list (pr_pair Elt.string_of Elt.string_of)
  let string_of (x:epure) =
    pr_triple (add_str "BAGA" pr1) (add_str "EQ" EM.string_of) (add_str "INEQ" pr2) x

  let string_of_disj (x:epure_disj) = pr_list_ln string_of x
  let mk_data sv = [([sv], EM.mkEmpty, [])] 

  (* let baga_conv baga : formula = *)
  (*   let baga = Elt.conv_var baga in *)
  (*   if (List.length baga = 0) then *)
  (*     mkTrue no_pos *)
  (*   else if (List.length baga = 1) then *)
  (*     mkGtVarInt (List.hd baga) 0 no_pos *)
  (*   else *)
  (*     let rec helper i j baga len = *)
  (*       let f1 = mkNeqVar (List.nth baga i) (List.nth baga j) no_pos in *)
  (*       if i = len - 2 && j = len - 1 then *)
  (*         f1 *)
  (*       else if j = len - 1 then *)
  (*         let f2 = helper (i + 1) (i + 2) baga len in *)
  (*         mkAnd f1 f2 no_pos *)
  (*       else *)
  (*         let f2 = helper i (j + 1) baga len in *)
  (*         mkAnd f1 f2 no_pos *)
  (*     in *)
  (*     let f1 = helper 0 1 baga (List.length baga) in *)
  (*     let f2 = List.fold_left (fun f sv -> mkAnd f1 (mkGtVarInt sv 0 no_pos) no_pos) *)
  (*       (mkGtVarInt (List.hd baga) 0 no_pos) (List.tl baga) in *)
  (*     mkAnd f1 f2 no_pos *)


  let baga_enum baga : formula =
    let baga = Elt.conv_var baga in
    match baga with
      | [] -> mkTrue no_pos
      | h::ts ->
            let i = ref 1 in
            List.fold_left (fun f sv ->
                i := !i + 1;
                mkAnd f (mkEqVarInt sv !i no_pos) no_pos
            ) (mkEqVarInt (List.hd baga) !i no_pos) (List.tl baga)

  let merge_baga b1 b2 = Elt.merge_baga b1 b2

  let merge cmp b1 b2 =
    let rec aux b1 b2 =
    match b1,b2 with
      | [],b | b,[] -> b
      | x1::t1, x2::t2 ->
            let c = cmp x1 x2 in
            if c<0 then x1::(aux t1 b2)
            else if c>0 then x2::(aux b1 t2)
            else x1::(aux t1 t2) in
    aux b1 b2

  (* pre : v1 < v2 *)
  (* baga ==> v1!=v2 *)
  let baga_imp baga v1 v2 =
    let rec find lst v =
      match lst with
        | [] -> None
        | x::xs -> if Elt.eq v x then Some xs
          else find xs v in
    match find baga v1 with
      | None -> false
      | Some rst -> not((find rst v2) == None)

  let pair_cmp (x1,x2) (y1,y2) =
    let c = Elt.compare x1 y1 in
    if c==0 then Elt.compare x2 y2
    else c

  let merge_ineq baga eq i1 i2 =
    let norm ((x,y) as p) =
      if baga_imp baga x y then []
      else if EM.is_equiv eq x y then failwith "contra with eqset"
      else [p] in
    let rec aux i1 i2 = match i1,i2 with
      | [],ineq | ineq,[] -> ineq
      | x::xs,y::ys ->
            let c = pair_cmp x y in
            if c==0 then (norm x) @ (aux xs ys)
            else if c<0 then (norm x) @ (aux xs i2)
            else (norm y) @ (aux i1 ys)
    in aux i1 i2

  (* DONE : norm ineq1@ineq2 *)
  let mk_star efp1 efp2 =
    if (is_false efp1) || (is_false efp2) then mk_false
    else
      let (baga1, eq1, neq1) = efp1 in
      let (baga2, eq2, neq2) = efp2 in
      try
        let new_baga = merge_baga baga1 baga2 in
        let new_eq = EM.merge_eset eq1 eq2 in
        let new_neq = merge_ineq new_baga new_eq neq1 neq2 in
        (new_baga, new_eq, new_neq)
      with _ -> mk_false

  let mk_or_disj t1 t2 = t1@t2

  (* [(a,[b,c])] --> a=b & a=c *)
  (* [(a,[b,c]),(d,[e])] --> a=b & a=c & d=e *)
  let conv_eq (eq : emap) : formula =
    let pairs = Elt.conv_var_pairs (EM.get_equiv eq)  in
    let fl = List.map (fun (v1,v2) ->
        if Globals.is_null (name_of_spec_var v1) then CP.mkEqNull v2 v1 no_pos
        else mkEqVar v1 v2 no_pos
    ) pairs in
    List.fold_left (fun f1 f2 ->
        mkAnd f1 f2 no_pos
    ) (mkTrue no_pos) fl

  (* [(a,b);(b,c)] --> a!=b & b!=c *)
  let conv_ineq (ieq : (elem * elem) list) : formula  =
    let pairs = Elt.conv_var_pairs ieq  in
    List.fold_left (fun f1 (v1, v2) ->
        let f2 = mkNeqVar v1 v2 no_pos in
        mkAnd f1 f2 no_pos
    ) (mkTrue no_pos) pairs

  let conv_enum ((baga,eq,inq) : epure) : formula =
    let f1 = conv_eq eq in
    let f2 = conv_ineq inq in
    let bf = baga_enum baga in
    mkAnd bf (mkAnd f1 f2 no_pos) no_pos

  (* let conv ((baga,eq,inq) : epure) : formula = *)
  (*   let f1 = conv_eq eq in *)
  (*   let f2 = conv_ineq inq in *)
  (*   let bf = baga_conv baga in *)
  (*   mkAnd bf (mkAnd f1 f2 no_pos) no_pos *)

  let is_zero b = match b with
    | [] -> false
    | x::_ -> Elt.is_zero x

  (* assume normalized *)
  let unsat ((baga,eq,ieq) : epure) : bool =
    let zf = is_zero baga in
    (* zf *)
    if zf then true
    else List.exists (fun (v1,v2) -> EM.is_equiv eq v1 v2) ieq (* need it to remove (null,null) in ineq *)

(*
    given (baga,eq,inq)
    contra if
       null \in baga
       duplicate (in baga - detected by merge)
       exists (a,b) in inq & eq
       exists (a,a) in inq (detected by norm,subs )

  how to detect:
       ([b], b=null, ..)?
  null is captured as _ which is the smallest
  value that is always used in baga.

*)

  let norm (efp) =
    if unsat efp then mk_false
    else efp

  let elim_unsat_disj disj =
    List.filter (fun f -> not(unsat f)) disj

  let is_false_disj disj = disj==[]

  let mk_false_disj = []

  (* this should follow ef_elim_exists_1 closely *)
  let elim_exists (svl : elem list) (f : epure) : epure =
    (* let subs_pair sst (e1,e2) = *)
    (*   let new_e1 = try *)
    (*     let (_, new_e1) = List.find (fun (v1,_) -> *)
    (*         Elt.eq e1 v1 *)
    (*     ) sst in *)
    (*     new_e1 *)
    (*   with Not_found -> e1 in *)
    (*   let new_e2 = try *)
    (*     let (_, new_e2) = List.find (fun (v1,_) -> *)
    (*         Elt.eq e2 v1 *)
    (*     ) sst in *)
    (*     new_e2 *)
    (*   with Not_found -> e2 in *)
    (*   if Elt.compare new_e1 new_e2 < 0 then *)
    (*     (new_e1, new_e2) *)
    (*   else *)
    (*     (new_e2, new_e1) *)
    (* in *)
    (* let filter_pairs svl eq ieq = *)
    (*   let new_eq = EM.build_eset (List.filter (fun (e1, e2) -> *)
    (*       not ((Elt.eq e1 e2) || *)
    (*           (List.exists (Elt.eq e1) svl) || *)
    (*           (List.exists (Elt.eq e2) svl)) *)
    (*   ) eq) in *)
    (*   let new_ieq = List.filter (fun (e1, e2) -> *)
    (*       if Elt.eq e1 e2 then failwith "exception -> mkFalse" *)
    (*       else *)
    (*         not ((List.exists (Elt.eq e1) svl) || *)
    (*             (List.exists (Elt.eq e2) svl)) *)
    (*   ) ieq in *)
    (*   (new_eq, new_ieq) *)
    (* in *)
    try
      let (baga, eq, neq) = f in
      let p_aset = eq in
      let mk_subs =
        List.map
            (fun v ->
                let lst = EM.find_equiv_all v p_aset in
                let lst = List.sort Elt.compare lst in
                let free = List.filter (fun v -> not(List.exists (Elt.eq v) svl)) lst in
                match free with
                  | [] -> (v,v)
                  | f::_ -> (v,f)
            ) svl in
      let mk_subs = Elt.conv_var_pairs mk_subs in
      let svl_lst = Elt.conv_var svl in
      let locate v =
        (* throws exception if existential present *)
        if List.exists (fun e -> eq_spec_var e v) svl_lst then
          let (a,b) = List.find (fun (vv,_) -> eq_spec_var v vv) mk_subs in
          if a = b then
            failwith "exist var"
          else
            b
        else v (* free *) in
      let new_baga0 = Elt.from_var (List.fold_left (fun acc v ->
          try
            let b = locate v in
            b::acc
          with _ -> acc) [] (Elt.conv_var baga)) in
      (* duplicates possible? *)
      let duplicate baga =
        let rec aux p baga =
        match baga with
          | [] -> false
          | b::bl -> (Elt.eq p b) || (aux b bl)
        in match baga with
          | [] -> false
          | b::bl -> aux b bl
      in
      let new_baga = List.sort Elt.compare new_baga0 in
      let _ = if duplicate new_baga then failwith "duplicate baga" else () in
      let new_eq = EM.elim_elems eq svl in
      (* let eq_pairs = EM.get_equiv eq in *)
      (* let subs_eq = List.map (subs_pair mk_subs) eq_pairs in *)
      let new_neq = Elt.from_var_pairs (List.fold_left (fun acc (v1,v2) ->
          let ans =
            try
              let b1 = locate v1 in
              let b2 = locate v2 in
              Some (b1,b2)
            with _ -> None in
          match ans with
            | None -> acc
            | Some (b1,b2) ->
                  (* re-order? *)
                  let c = compare_spec_var b1 b2 in
                  if c < 0 then (b1,b2)::acc
                  else if c==0 then failwith "INEQ contra detected"
                  else (b2,b1)::acc
          ) [] (Elt.conv_var_pairs neq)) in
      let new_neq = List.sort pair_cmp new_neq in
      let rec remove_duplicate ineq =
        match ineq with
          | [] -> []
          | [hd] -> [hd]
          | hd1::hd2::tl ->
                if pair_cmp hd1 hd2 = 0 then
                  remove_duplicate (hd2::tl)
                else
                  hd1::(remove_duplicate(hd2::tl))
      in
      let new_neq = remove_duplicate new_neq in
      (* let subs_neq = List.map (subs_pair mk_subs) neq in *)
      (* let (new_eq, new_neq0) = filter_pairs svl subs_eq subs_neq in *)
      (* let new_neq = List.filter (fun (e1, e2) -> *)
      (*     not (List.exists (Elt.eq e1) new_baga && List.exists (Elt.eq e2) new_baga)) new_neq0 in *)
      (new_baga, new_eq, new_neq)
    with _ -> mk_false

  let elim_exists (svl : elem list) (f : epure) : epure =
    let pr1 = pr_list Elt.string_of in
    Debug.no_2 "elim_exists_new" pr1 (string_of) (string_of)
        (fun _ _ -> elim_exists svl f) svl f

  (* let imply (ante : epure) (conseq : epure) : bool = *)
  (*   let a_f = conv_enum ante in *)
  (*   let c_f = conv conseq in *)
  (*   (\* a_f --> c_f *\) *)
  (*   let f = mkAnd a_f (mkNot_s c_f) no_pos in *)
  (*   not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f)) *)

  let ef_conv_disj_ho conv disj : formula =
    List.fold_left (fun f ep ->
        mkOr f (conv ep) None no_pos
    ) (mkFalse no_pos) disj

  (* needed in cvutil.ml *)
  let ef_conv_enum_disj = ef_conv_disj_ho conv_enum
  (* let ef_conv_disj      = ef_conv_disj_ho conv *)

  (* let eq_epure (ante : epure) (conseq : epure) : bool = *)
  (*   imply ante conseq && imply conseq ante *)

  let compare_list cmp b1 b2 =
    let rec aux b1 b2 =
    match b1,b2 with
      | [],[] -> 0
      | [],_ -> -1
      | _,[] ->1
      | (x::xs),(y::ys) ->
            let c = cmp x y in
            if c==0 then aux xs ys
            else c
    in aux b1 b2

  let eq_list f b1 b2 =
    let rec aux b1 b2 =
    match b1,b2 with
      | [],[] -> true
      | [],_ -> false
      | _,[] -> false
      | (x::xs),(y::ys) ->
            if f x y then aux xs ys
            else false
    in aux b1 b2

  let rec baga_eq b1 b2 = eq_list Elt.eq b1 b2

  let rec baga_cmp b1 b2 = compare_list Elt.compare b1 b2
    (* match b1,b2 with *)
    (*   | [],[] -> true *)
    (*   | [],_ -> false *)
    (*   | _,[] -> false *)
    (*   | (x::xs),(y::ys) ->  *)
    (*         if Elt.eq x y then baga_eq xs ys *)
    (*         else false *)

  let compare_partition cmp p1 p2 =
    let rec aux p1 p2 =
      match p1,p2 with
        | [],[] -> 0
        | [],_ -> -1
        | _,[] -> 1
        | x1::p1,x2::p2 ->
              let c1=compare_list cmp x1 x2 in
              if c1==0 then aux p1 p2
              else c1
    in aux p1 p2

  let emap_compare e1 e2 =
    (* DONE : is get_equiv in sorted order? *)
    let lst1 = EM.partition e1 in
    let lst2 = EM.partition e2 in
    (* let lst1 = List.sort pair_cmp lst1 in *)
    (* let lst2 = List.sort pair_cmp lst2 in *)
    compare_partition Elt.compare lst1 lst2

  let emap_eq em1 em2 = (emap_compare em1 em2) == 0
    (* let ps1 = EM.get_equiv em1 in *)
    (* let ps2 = EM.get_equiv em2 in *)
    (* let imp em ps = *)
    (*   List.for_all (fun (v1,v2) -> EM.is_equiv em v1 v2) ps in *)
    (*   imp em1 ps2 && imp em2 ps1 *)

  (* assumes ine2 is non-redundant *)
  (* let ineq_imp (\* b1 *\) ine1 ine2 = *)
  (*   List.for_all (fun (v1,v2) -> *)
  (*   (\* (baga_imp b1 v1 v2) || *\)  *)
  (*       List.exists (fun (a1,a2) -> (Elt.eq a1 v1) && (Elt.eq a2 v2) ) ine1) ine2 *)

  (* let ineq_eq (\* b1 b2 *\) ine1 ine2 = *)
  (*   ineq_imp (\* b1 *\) ine1 ine2 && ineq_imp (\* b2 *\) ine2 ine1 *)

  let eq_diff (x1,x2) (y1,y2) = Elt.eq x1 y1 && Elt.eq x2 y2

  let ineq_compare (* b1 b2 *) ine1 ine2 = compare_list pair_cmp ine1 ine2

  (* more efficient in_eq assuming diff list is sorted *)
  let ineq_eq (* b1 b2 *) ine1 ine2 = (ineq_compare ine1 ine2) == 0
    (* eq_list eq_diff ine1 ine2 *)
    (* match ine1,ine2 with *)
    (*   | [], [] -> true *)
    (*   | [], _ -> false *)
    (*   | _,[] -> false *)
    (*   | x::xs,y::ys ->  *)
    (*         if eq_diff x y then ineq_eq xs ys *)
    (*         else false *)

  let eq_epure_syn ((b1,e1,in1) as ep1 : epure) ((b2,e2,in2) as ep2 : epure) : bool =
    (* assume non-false *)
      (baga_eq b1 b2) && (emap_eq e1 e2) && (ineq_eq in1 in2)

  (* get norm_eq from eqmap *)
  (* get domain; choose smallest *)
  (* filter as they are taken out *)
  (* let emap_extract e1 e2 = [] *)

  let epure_compare ((b1,e1,in1) as ep1 : epure) ((b2,e2,in2) as ep2 : epure) : int =
    (* assume non-false *)
    let c1 = baga_cmp b1 b2 in
    if c1==0 then
      let c2 = emap_compare e1 e2  in
      if c2==0 then
        ineq_compare in1 in2
      else c2
    else c1

  let merge_disj lst1 lst2 =
    merge epure_compare lst1 lst2

  let add_star ep lst =
    let xs = List.map (fun v -> mk_star ep v) lst in
    let zs = List.filter (fun x -> not(unsat x)) xs in
    List.sort epure_compare zs

  (* xs --> ys? *)
  let lst_imply cmp xs ys =
    let rec aux xs ys =
      match xs,ys with
        | _,[] -> true
        | [],_ -> false
        | x::xs2,y::ys2 ->
              let c = cmp x y in
              if c==0 then aux xs2 ys2
              else if c<0 then aux xs2 ys
              else false
    in aux xs ys

  (* let pair_compare cmp (a1,a2) (b1,b2) = *)
  (*   let c = cmp a1 b1 in *)
  (*   if c==0 then cmp a2 b2 *)
  (*   else c *)

  let emap_imply e1 e2 =
    let lst1 = EM.get_equiv e1 in
    let lst2 = EM.get_equiv e2 in
    lst_imply pair_cmp lst1 lst2

  (* epure syntactic imply *)
  let epure_syn_imply (b1,e1,i1) (b2,e2,i2) =
    let f1 = lst_imply Elt.compare b1 b2 in
    if f1 then
      let null_el = Elt.zero (* mk_elem (mk_spec_var "null") *) in
      let i1_new = List.fold_left (fun i1 el ->
          let c = Elt.compare el null_el in
          if c < 0 then
            i1@[(el, null_el)]
          else if c > 0 then
            i1@[(null_el, el)]
          else
            failwith "fail in epure_syn_imply"
      ) i1 b1 in
      let i1_new = List.sort pair_cmp i1_new in
      let f2 = lst_imply pair_cmp i1_new i2 in
      if f2 then emap_imply e1 e2 (* DONE: e1 --> e2? *)
      else false
    else false

  let syn_imply ep lst =
    List.exists (fun ep2 -> epure_syn_imply ep ep2) lst

  let syn_imply ep lst =
    let pr1 = string_of in
    let pr2 = string_of_disj in
    Debug.no_2 "syn_imply" pr1 pr2 string_of_bool syn_imply ep lst

  let epure_disj_syn_imply lst1 lst2 =
    List.for_all (fun ep -> syn_imply ep lst2) lst1

  let epure_disj_syn_imply lst1 lst2 =
    let pr1 = string_of_disj in
    Debug.no_2 "epure_disj_syn_imply" pr1 pr1 string_of_bool epure_disj_syn_imply lst1 lst2

  let imply_disj (ante : epure_disj) (conseq : epure_disj) : bool =
    epure_disj_syn_imply ante conseq

  let imply_disj (ante : epure_disj) (conseq : epure_disj) : bool =
    let pr1 = string_of_disj in
    Debug.no_2 "imply_disj" pr1 pr1 string_of_bool imply_disj ante conseq


  (* let mk_star_disj (efpd1:epure_disj) (efpd2:epure_disj)  = *)
  (*   let res = *)
  (*     List.map (fun efp1 -> List.map (fun efp2 -> mk_star efp1 efp2) efpd2) efpd1 in *)
  (*   List.concat res *)

  let mk_star_disj (efpd1:epure_disj) (efpd2:epure_disj)  =
    let res =
      List.map (fun efp1 -> add_star efp1 efpd2) efpd1 in
    List.fold_left merge_disj [] res
    (* List.concat res *)

  (* let imply_disj (ante : epure_disj) (conseq : epure_disj) : bool = *)
  (*   let a_f = conv_enum_disj ante in *)
  (*   let c_f = conv_disj conseq in *)
  (*   (\* a_f --> c_f *\) *)
  (*   let f = mkAnd a_f (mkNot_s c_f) no_pos in *)
  (*   not (Tpdispatcher.is_sat_raw (Mcpure.mix_of_pure f)) *)

  (* reducing duplicate? *)
  let norm_disj disj =
    let rec remove_duplicate (disj : epure_disj) : epure_disj =
      match disj with
        | [] -> []
        | hd::tl ->
              let new_tl = remove_duplicate (List.filter (fun ep ->
                  not (eq_epure_syn hd ep)) tl) in
              hd::new_tl
    in
    let disj0 = List.filter (fun v -> not(is_false v)) (List.map norm disj) in
    remove_duplicate disj0

(*
            List.map (fun (baga, eq, ineq) ->
              let new_baga = subst_var_list sst baga in
              let eqf = EPureI.conv_eq eq in
              let new_eqf = subst sst eqf in
              let p_aset = pure_ptr_equations new_eqf in
              let new_eq = EMapSV.build_eset p_aset in
              let ineqf = EPureI.conv_ineq ineq in
              let new_ineqf = subst sst ineqf in
              let new_ineq = get_ineq new_ineqf in
              (* let new_pf = subst (List.combine view_args svl) pf in *)
              (new_baga, new_eq, new_ineq)
          ) efpd in
*)

  let subst_elem sst v =
    if Elt.is_zero v then v
    else try
      let (_,t) = List.find (fun (w,_) -> Elt.eq w v) sst in
      t
    with _ -> v (* should return v, not all elt have subst *) (* failwith ("subst_elem : cannot find elem "^Elt.string_of v) *)

  let subst_epure sst ((baga,eq,ineq) as ep) = 
    let new_eq = EM.subs_eset_par sst eq in
    let subs_fn = subst_elem sst in
    let new_baga = List.map (subs_fn) baga in
    let new_ineq = List.map (fun (a,b) -> (subs_fn a,subs_fn b)) ineq in
    (new_baga,new_eq,new_ineq)

  let subst_epure_disj sst (lst:epure_disj) =
    List.map (subst_epure sst) lst

  let get_ineq (pf : formula) =
    let rec helper lconj = match lconj with
      | [] -> []
      | hd::tl -> ( match hd with
          | BForm ((Neq (e1, e2, _), _), _) ->
              ( match (e1,e2) with
                | (Var (sv1, _), Var (sv2, _)) ->
                      let c = compare_spec_var sv1 sv2 in
                      if c < 0 then
                        (sv1, sv2)::(helper tl)
                      else if c > 0 then
                        (sv2, sv1)::(helper tl)
                      else
                        failwith "fail in ineq"
                | (Var (sv, _), Null _)
                | (Null _, Var (sv, _)) ->
                      let null_var = List.hd (Elt.conv_var [Elt.zero]) (* mk_spec_var "null" *) in
                      let c = compare_spec_var null_var sv in
                      if c < 0 then
                        (null_var, sv)::(helper tl)
                      else if c > 0 then
                        (sv, null_var)::(helper tl)
                      else
                        failwith "fail in ineq"
                | (Null _, Null _) ->
                      failwith "fail in get_ineq"
                | _ -> helper tl
              )
          | _ -> helper tl
        )
    in
    List.sort pair_cmp (Elt.from_var_pairs (helper (split_conjunctions pf)))

  (* let get_baga (pf : formula) = *)
  (*   let rec helper lconj = match lconj with *)
  (*     | [] -> [] *)
  (*     | hd::tl -> ( match hd with *)
  (*         | BForm ((Neq (e1, e2, _), _), _) -> *)
  (*             ( match (e1,e2) with *)
  (*               | (Var (sv, _), Null _) *)
  (*               | (Null _, Var (sv, _)) -> *)
  (*                     sv::(helper tl) *)
  (*               | (Null _, Null _) -> *)
  (*                     failwith "fail in get_baga" *)
  (*               | _ -> helper tl *)
  (*             ) *)
  (*         | _ -> helper tl *)
  (*       ) *)
  (*   in *)
  (*   List.sort Elt.compare (Elt.from_var (helper (split_conjunctions pf))) *)

  let mk_epure (pf:formula) =
    let p_aset = pure_ptr_equations pf in
    let p_aset = EM.build_eset (Elt.from_var_pairs p_aset) in
    let baga = (* get_baga pf in *) [] in
    let ineq = get_ineq pf in
    (* [([], pf)] *)
    [(baga, p_aset, ineq)] (* new expure, need to add ineq : DONE *)

  (* let to_cpure ((baga,eq,ineq) : epure) = *)
  (*   let f1 = conv_eq eq in *)
  (*   let f2 = conv_ineq ineq in *)
  (*   (baga, mkAnd f1 f2 no_pos) *)

  (* let to_cpure_disj (epd : epure_disj) = *)
  (*   List.map (fun ep -> to_cpure ep) epd *)

  let to_cpure (ep : epure) = ep

  let to_cpure_disj (epd : epure_disj) = epd

  (* let from_cpure ((baga,pf) : ef_pure) = *)
  (*   let p_aset = pure_ptr_equations pf in *)
  (*   let p_aset = EMapSV.build_eset p_aset in *)
  (*   let ineq = get_ineq pf in *)
  (*   (baga, p_aset, ineq) *)

  (* let from_cpure_disj (epd : ef_pure_disj) = *)
  (*   List.map (fun ep -> from_cpure ep) epd *)

  let from_cpure (ep : ef_pure) = ep

  let from_cpure_disj (epd : ef_pure_disj) = epd

(* TODO

  1. complete conv_eq & conv_neq
  2. complete elim_exists
  3. eq_epure ep1 ep2 (detect if two epures are equal, after norm)
  4. sort_epure_disj  (baga,...)
  5. strong_norm_epure (* must detect false, no x=x *)

*)

end

(* module EPureI = EPUREN(SV) *)

module EPureI = EPUREN(SV)

type ef_pure_disj = EPureI.epure_disj

let rec build_ef_heap_formula_x (cf : Cformula.h_formula) (all_views : Cast.view_decl list) : ef_pure_disj =
  match cf with
    (* | Cformula.Star _ -> *)
    (*       let hfl = Cformula.split_star_conjunctions cf in *)
    (*       let efpd_n = List.fold_left (fun f hf -> *)
    (*           let efpd_h = build_ef_heap_formula hf all_views in *)
    (*           let efpd_s = EPureI.mk_star_disj f efpd_h in *)
    (*           let efpd_n = EPureI.norm_disj efpd_s in *)
    (*           efpd_n *)
    (*       ) (build_ef_heap_formula (List.hd hfl) all_views) (List.tl hfl) in *)
    (*       efpd_n *)
    | Cformula.DataNode dnf ->
          let sv = dnf.Cformula.h_formula_data_node in
          let efpd_h = EPureI.mk_data sv in
          efpd_h
    | Cformula.ViewNode vnf ->
          let svl = vnf.Cformula.h_formula_view_node::vnf.Cformula.h_formula_view_arguments in
          let efpd =
            try Hashtbl.find map_baga_invs vnf.Cformula.h_formula_view_name
            with Not_found -> failwith "cannot find in init_map too"
          in
          let efpd = EPureI.from_cpure_disj efpd in
          (* need substitue variable *)
          let view = List.find (fun vc -> vnf.Cformula.h_formula_view_name = vc.Cast.view_name) all_views in
          let self_var = Cpure.SpecVar (Named view.Cast.view_data_name, self, Unprimed) in
          let view_args = self_var::view.Cast.view_vars in
          let sst = List.combine view_args svl in
          (* TODO : below should be done using EPureI : DONE *)
          let efpd_h = EPureI.subst_epure_disj sst efpd in
          let efpd_n = EPureI.norm_disj efpd_h in
          efpd_n
    | _ -> EPureI.mk_true

and build_ef_heap_formula (cf : Cformula.h_formula) (all_views : Cast.view_decl list) : ef_pure_disj =
  Debug.no_1 "build_ef_heap_formula" Cprinter.string_of_h_formula
      EPureI.string_of_disj (fun _ ->
          build_ef_heap_formula_x cf all_views) cf

let build_ef_heap_formula_with_pure_x (cf : Cformula.h_formula) (efpd_p : ef_pure_disj) (all_views : Cast.view_decl list) : ef_pure_disj =
  match cf with
    | Cformula.Star _ ->
          let hfl = Cformula.split_star_conjunctions cf in
          let efpd_n = List.fold_left (fun f hf ->
              let efpd_h = build_ef_heap_formula hf all_views in
              let efpd_s = EPureI.mk_star_disj f efpd_h in
              let efpd_n = EPureI.norm_disj efpd_s in
              efpd_n
          ) efpd_p hfl in
          efpd_n
    | Cformula.DataNode _
    | Cformula.ViewNode _ ->
          let efpd_h = build_ef_heap_formula cf all_views in
          let efpd_s = EPureI.mk_star_disj efpd_p efpd_h in
          let efpd_n = EPureI.norm_disj efpd_s in
          efpd_n
    | _ -> efpd_p

let build_ef_heap_formula_with_pure (cf : Cformula.h_formula) (efpd_p : ef_pure_disj) (all_views : Cast.view_decl list) : ef_pure_disj =
  Debug.no_1 "build_ef_heap_formula_with_pure" Cprinter.string_of_h_formula
      EPureI.string_of_disj (fun _ ->
          build_ef_heap_formula_with_pure_x cf efpd_p all_views) cf

(* this need to be moved to EPURE module : DONE *)
let rec build_ef_pure_formula_x (pf : formula) : ef_pure_disj =
  EPureI.mk_epure pf

let build_ef_pure_formula (pf : formula) : ef_pure_disj =
  Debug.no_1 "build_ef_pure_formula" Cprinter.string_of_pure_formula
      EPureI.string_of_disj (fun _ ->
          build_ef_pure_formula_x pf) pf

(* build_ef_formula : map -> cformula --> ef_pure_disj *)
(* (b1,p1) * (b2,p2) --> (b1 U b2, p1/\p2) *)
(* (b1,p1) & ([],p2) --> (b1, p1/\p2) *)
(* x->node(..)       --> ([x],true) *)
(* p(...)            --> inv(p(..)) *)
let rec build_ef_formula_x (cf : Cformula.formula) (all_views : Cast.view_decl list) : ef_pure_disj =
  match cf with
    | Cformula.Base bf ->
          let bp = (Mcpure.pure_of_mix bf.Cformula.formula_base_pure) in
          let bh = bf.Cformula.formula_base_heap in
          let efpd_p = build_ef_pure_formula bp in
          (* let efpd_h = build_ef_heap_formula bh all_views in *)
          (* let efpd = EPureI.norm_disj (EPureI.mk_star_disj efpd_p efpd_h) in *)
          let efpd = build_ef_heap_formula_with_pure bh efpd_p all_views in
          efpd
    | Cformula.Or orf ->
          let efpd1 = build_ef_formula orf.Cformula.formula_or_f1 all_views in
          let efpd2 = build_ef_formula orf.Cformula.formula_or_f2 all_views in
          let efpd = EPureI.mk_or_disj efpd1 efpd2 in
          let efpd_n = EPureI.norm_disj efpd in
          efpd_n
    | Cformula.Exists ef ->
          let ep = (Mcpure.pure_of_mix ef.Cformula.formula_exists_pure) in
          let eh = ef.Cformula.formula_exists_heap in
          let efpd_p = build_ef_pure_formula ep in
          (* let efpd_h = build_ef_heap_formula eh all_views in *)
          (* let efpd = EPureI.norm_disj (EPureI.mk_star_disj efpd_p efpd_h) in *)
          let efpd = build_ef_heap_formula_with_pure eh efpd_p all_views in
          let efpd_e = List.map (fun efp ->
              (EPureI.elim_exists ef.Cformula.formula_exists_qvars efp)) efpd in
          let efpd_n = EPureI.norm_disj efpd_e in
          efpd_n

and build_ef_formula (cf : Cformula.formula) (all_views : Cast.view_decl list) : ef_pure_disj =
  Debug.no_1 "build_ef_formula" Cprinter.string_of_formula
      EPureI.string_of_disj (fun _ ->
          build_ef_formula_x cf all_views) cf

(* using Cast *)

(* build_ef_view : map -> view_decl --> ef_pure_disj *)
(* view  ls1<self,p> == ..ls1<..>..ls2<..>... *)
(* map   ls1<self,p> == [(b1,f1)] *)
(*       ls2<self,p> == [(b2,f2)] *)
let build_ef_view_x (view_decl : Cast.view_decl) (all_views : Cast.view_decl list) : ef_pure_disj =
  let disj = List.flatten (List.map (fun (cf,_) ->
      let disj = build_ef_formula cf all_views in
      disj
  ) view_decl.Cast.view_un_struc_formula) in
  let disj_n = EPureI.norm_disj disj in
  disj_n

let build_ef_view (view_decl : Cast.view_decl) (all_views : Cast.view_decl list) : ef_pure_disj =
  let pr_view_name vd = vd.Cast.view_name in
  Debug.no_1 "build_ef_view" pr_view_name EPureI.string_of_disj (fun _ ->
      build_ef_view_x view_decl all_views) view_decl

(* fix_test :  map -> view_list:[view_decl] -> inv_list:[ef_pure_disj] -> bool *)
(* does view(inv) --> inv *)
(* ls<self,p> == .... *)
(* inv<self,p> == ([],true) *)
(* let lhs_list = List.map (build map) view_list in *)
(* let rhs_list = inv_list in *)
(* let pair_list = List.combine lhs_list rhs_list in *)
(* let r_list = List.map (fun (a,c) -> ef_imply_disj a c) pair_list in *)
let fix_test (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list) : bool =
  let lhs_list = inv_list in
  let rhs_list = List.map (fun vd ->
      Hashtbl.find map_baga_invs vd.Cast.view_name) view_list in
  let rhs_list = List.map (fun epd -> EPureI.from_cpure_disj epd) rhs_list in
  let pair_list = List.combine lhs_list rhs_list in
  let r_list = List.map (fun (a, c) ->
      EPureI.imply_disj a c) pair_list in
  not (List.exists (fun r -> r = false) r_list)

let fix_test (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list) : bool =
  let pr1 x = string_of_int (List.length x) in
  let pr2 = pr_list EPureI.string_of_disj in
  Debug.no_2 "fix_test" pr1 pr2 string_of_bool (fun _ _ -> (fix_test (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list))) view_list inv_list

(* compute fixpoint iteration *)
(* strict upper bound 100 *)
(* fix_ef : [view_defn] -> disjunct_num (0 -> precise) -> [ef_pure_disj] *)
let fix_ef_x (view_list : Cast.view_decl list) (all_views : Cast.view_decl list) : ef_pure_disj list =
  let inv_list = List.fold_left (fun inv_list vc ->
      inv_list@[(build_ef_view vc all_views)]) [] view_list in
  let rec helper view_list inv_list =
    if fix_test view_list inv_list
    then
      inv_list
    else
      let _ = List.iter (fun (vc,inv) ->
          Hashtbl.replace map_baga_invs vc.Cast.view_name (EPureI.to_cpure_disj inv)
      ) (List.combine view_list inv_list) in
      let inv_list = List.fold_left (fun inv_list vc ->
          inv_list@[(build_ef_view vc all_views)]
      ) [] view_list in
      helper view_list inv_list
  in
  let inv_list = helper view_list inv_list in
  let _ = List.iter (fun (vc,inv) ->
      (* this version is being printed *)
      let _ = Debug.binfo_hprint (add_str ("baga inv("^vc.Cast.view_name^")") (EPureI.string_of_disj)) inv no_pos in
      let _ = print_string_quiet "\n" in
      Hashtbl.replace map_baga_invs vc.Cast.view_name (EPureI.to_cpure_disj inv)
  ) (List.combine view_list inv_list) in
  inv_list

let fix_ef (view_list : Cast.view_decl list) (all_views : Cast.view_decl list) : ef_pure_disj list =
  let pr_1 = pr_list (fun v -> v.Cast.view_name)  in
  Debug.no_1 "fix_ef_x" pr_1 (pr_list EPureI.string_of_disj)
      (fun _ -> fix_ef_x view_list all_views) view_list

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
