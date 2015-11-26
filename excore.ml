#include "xdebug.cppo"
open Globals
open VarGen
(* open Wrapper *)
(* open Others *)
(* open Stat_global *)
(* open Global_var *)
(* open Exc.ETABLE_NFLOW *)
(* open Exc.GTable *)
open Gen.Basic
(* open Label *)

open Cpure
open VarGen
(* open Cprinter *)

module CP = Cpure

module UnCa=
   struct
     let unsat_cache = Hashtbl.create 200
     let hit_cache = ref (0:int)
     let miss_cache = ref (0:int)

     let init_cache () =
       let () = Hashtbl.add unsat_cache "self.false" true in
       Hashtbl.add unsat_cache "self.true" false

     let reset_cache () =
       let () =  Hashtbl.clear unsat_cache in
       init_cache ()

     let find f=
       let str = !print_formula f in
       Hashtbl.find unsat_cache str

     let is_unsat_cache str_f f unsat_fnc=
       try
         let res = Hashtbl.find unsat_cache str_f in
         let _ = hit_cache := !hit_cache + 1 in
         res
       with Not_found ->
           let res = unsat_fnc f in
           let () = Hashtbl.add unsat_cache str_f res in
           let _ = miss_cache := !miss_cache + 1 in
           res
   end;;

let h_2_mem_obj = object (self)
  val mutable state = CP.mkTrue no_pos
  val mutable list = []
  method logging s =
    (* let () = print_endline_quiet ("XXXX "^(s)) in *)
    ()
  method init =
    self # logging "init" ; 
    let () = state <- CP.mkTrue no_pos in
    let () = list <- [] in
    ()
  method notempty = list!=[]
  method add_pure p = 
    self # logging ((add_str "add_pure" !CP.print_formula) p); 
    let () = state <- CP.mkAnd state p no_pos in
    ()
  method get_id v e = 
    self # logging "get_id";
    let eq_v = try
        fst(List.find (fun (_,e2) ->
            let rhs = (CP.mk_eq_exp e e2) in
            let () = self # logging ((add_str "lhs" !CP.print_formula) state) in 
            let () =  self # logging ((add_str "rhs" !CP.print_formula) rhs) in 
            !CP.tp_imply state rhs
          ) list)
      with _ ->  
        let x = CP.fresh_spec_var v in
        let () = list <- (x,e)::list in
        x
    in eq_v
  method string_of =
    let s1 = (add_str "state" !CP.print_formula) state in
    let s2 = (add_str "\nlist" (pr_list (pr_pair !CP.print_sv !CP.print_exp))) list in
    s1^s2
end;;

let wrap_h_2_mem loc f x =
  let self = h_2_mem_obj in
  let () = self # init in
  (* let () = print_endline_quiet ("init h_2_mem "^loc) in *)
  try
    let r = f x in
    let () = if self # notempty then self # logging ((add_str "\nh_2_mem" pr_id) (self # string_of)) in
    r
  with e ->
    let () = if self # notempty then self # logging ((add_str "\nh_2_mem" pr_id) (self # string_of)) in
    raise e

let is_sat_raw = Mcpure.is_sat_raw
(* ref(fun (c:Mcpure.mix_formula) -> true) *)
let simplify_raw = ref(fun (c:Cpure.formula) -> mkTrue no_pos)
let pairwisecheck = ref(fun (c:Cpure.formula) -> mkTrue no_pos)


(* let print_mix_formula = ref (fun (c:MP.mix_formula) -> "cpure printer has not been initialized") *)
let print_h_formula = ref (fun (c:Cformula.h_formula) -> "cpure printer has not been initialized")
let print_formula = ref (fun (c:Cformula.formula) -> "cform printer has not been initialized")
let print_pure_formula = ref (fun (c:Cpure.formula) -> "cform printer has not been initialized")

let simplify_conj simp f =
  match f with
  | AndList ls -> AndList (List.map (fun (l,f) -> (l,simp f)) ls)
  | rest -> simp rest

let simplify_with_label simp (f:formula) =
  let ls = split_disjunctions f in
  let ls = List.map (simplify_conj simp) ls in
  join_disjunctions ls

let simplify_with_label_omega_x (f:formula) =
  (*  let simp = x_add_1 Omega.simplify 2 in  *)
  let simp = (* x_add_1 Omega.simplify *) !simplify_raw in
  simplify_with_label simp f

let simplify_with_label_omega (f:formula) =
  Debug.no_1 "simplify_with_label_omega" !print_pure_formula !print_pure_formula
    simplify_with_label_omega_x f

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
  (* let () = x_tinfo_hp (pr_list (string_of_typed_spec_var)) filtered_svl no_pos in *)
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
(*      (\*   let todo_unk = List.find (fun sv -> *\) *)
(*      (\*       let SpecVar(_, name, _)  = sv in *\) *)
(*      (\*       (not (name = "self")) && (not (List.mem sv args)) *\) *)
(*      (\*   ) svl in false *\) *)
(*      (\* with Not_found -> true *\) *)
(*  ) conj_list in *)
(*   (\* WN : should we use Omega? will x!=y cause disjunct *\) *)
(*  arith_simplify_new f *)
(*  (\* x_add_1 Omega.simplify f *\) *)

let elim_clause (pf : formula) (args : spec_var list) : formula =
  Debug.no_2 "ex_elim_clause" !print_pure_formula (pr_list string_of_typed_spec_var) !print_pure_formula
    elim_clause pf args

(* elim not relevant spec var from baga *)
(* [a,b,c] -> [a,d] -> [a] *)
let elim_baga_x (svl : spec_var list) (args : spec_var list) : spec_var list =
  List.filter (fun sv ->
      let SpecVar(_, name, _) = sv in
      (name = "self") || (List.mem sv args)) svl

let elim_baga (svl : spec_var list) (args : spec_var list) : spec_var list =
  Debug.no_2 "ex_elim_baga" (pr_list string_of_typed_spec_var) (pr_list string_of_typed_spec_var) (pr_list string_of_typed_spec_var)
    elim_baga_x svl args

let subs_null f0 =
  let rec helper f = match f with
    | BForm (bf,a) ->
      (match bf with
       | (Eq (sv1, sv2, b), c) ->
         (match (sv1, sv2) with
          | (_, Null l) ->
            BForm ((Eq (sv1, Var(mk_zero,l), b), c), a)
          | (Null l, _) ->
            BForm ((Eq (Var(mk_zero,l), sv2, b), c), a)
          | _ -> f
         )
       | (Neq (sv1, sv2, b), c) ->
         (match (sv1, sv2) with
          | (_, Null l) ->
            BForm ((Neq (sv1, Var(mk_zero, l), b), c), a)
          | (Null l, _) ->
            BForm ((Neq (Var(mk_zero,l), sv2, b), c), a)
          | _ -> f
         )
       | _ -> f)
    | And (f1, f2, l) ->
      And (helper f1, helper f2, l)
    | AndList fl ->
      AndList (List.map (fun (t, f) -> (t, helper f)) fl)
    | Or (f1, f2, c, l) ->
      Or (helper f1, helper f2, c, l)
    | Not (f, c, l) ->
      Not (helper f, c, l)
    | Exists (a, f, c, l) ->
      Exists (a, helper f, c, l)
    | Forall (a, f, c, l) ->
      Forall (a, helper f, c, l)
  in
  helper f0

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
  let () = x_tinfo_pp ("Omega call before simplify: " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
  let (baga,pure0) = epf in
  (* let () = Debug.ninfo_pprint "ef_elim_exists" no_pos in *)
  (* let () = Debug.ninfo_pprint "==============" no_pos in *)
  let () = x_dinfo_hp (add_str "svl" string_of_spec_var_list) svl no_pos in
  (* let () = Debug.ninfo_hprint (add_str "old baga" string_of_spec_var_list) baga no_pos in *)
  (* let () = Debug.ninfo_hprint (add_str "pure" !print_pure_formula) pure no_pos in *)
  let p_aset = pure_ptr_equations pure0 in
  let () = x_tinfo_hp (add_str "pure = " !print_pure_formula) pure0 no_pos in
  let pure = wrap_exists_svl pure0 svl in
  let () = x_tinfo_hp (add_str "pure1 = " !print_pure_formula) pure no_pos in
  let pure = (* match pure with *)
    (* | Cpure.AndList _ -> simplify_with_label_omega (\* x_add_1 Omega.simplify *\) pure *)
    (* | _ -> *)
          if !Globals.delay_eelim_baga_inv && Cpure.is_shape pure0 then
            let is_unsat = Ssat.SS.is_s_unsat baga pure0 in
            if is_unsat then mkFalse (pos_of_formula pure0) else
            let ps = Cpure.list_of_conjs pure in
            let ps1 = List.map (Ssat.SS.elim_exists svl) ps in
            Cpure.conj_of_list ps1 (Cpure.pos_of_formula pure)
          else
            simplify_with_label_omega (* x_add_1 Omega.simplify *) pure
  in
  let () = x_tinfo_hp (add_str "pure2 = " !print_pure_formula) pure no_pos in
  let () = x_tinfo_hp (add_str "pure_ptr_eq" (pr_list (pr_pair string_of_typed_spec_var string_of_typed_spec_var))) p_aset no_pos in
  let p_aset = EMapSV.build_eset p_aset in
  (* let new_paset = EMapSV.elim_elems p_aset svl in *)
  let () = Debug.ninfo_hprint (add_str "eqmap = " EMapSV.string_of) p_aset no_pos in
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
  (* let () = Debug.ninfo_hprint (add_str "new baga" string_of_spec_var_list) new_baga no_pos in *)
  (* let equiv_pairs = EMapSV.get_equiv new_paset in *)
  (* let ps = string_of_spec_var in *)
  (* Debug.ninfo_hprint (add_str "equiv_pairs" (pr_list (pr_pair ps ps))) equiv_pairs no_pos; *)
  let pure1 = apply_subs mk_subs pure in
  (* let pure1 = subs_null pure1 in *)
  let new_pure = remove_redundant_for_expure (elim_clause pure1 svl) in
  let () = Debug.ninfo_hprint (add_str "pure" !print_pure_formula) pure no_pos in
  let () = Debug.ninfo_hprint (add_str "pure1" !print_pure_formula) pure1 no_pos in
  let () = x_tinfo_hp (add_str "new pure" !print_pure_formula) new_pure no_pos in
  let res = (List.sort compare_sv new_baga, new_pure) in
  let () = x_tinfo_pp ("Omega call after simplify: " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
  res

(* let ef_elim_exists_1 (svl : spec_var list) epf = *)
(*   (\* let pr = string_of_ef_pure in *\) *)
(*   (\* Debug.no_2 "ef_elim_exists" string_of_typed_spec_var_list pr pr *\) *)
(*   ef_elim_exists_1 svl epf *)

let calc_fix_pure (svl : spec_var list) pf =
  let pf_base = x_add_1 Omega.simplify pf in
  let conjs = split_conjunctions pf in
  let conjs = List.filter (fun conj ->
      not(List.exists (fun sv -> List.mem sv svl) (fv conj))
    ) conjs in
  let pf_indu = List.fold_left (fun pf1 pf -> mkAnd pf1 pf no_pos) (mkTrue no_pos) conjs in
  let pf_fix = x_add_1 Omega.simplify (mkOr pf_base pf_indu None no_pos) in
  pf_fix

(* let ef_elim_exists_2 (svl : spec_var list) epf = *)
(*   let (baga, pf) = epf in *)
(*   let svl1 = List.filter (fun sv -> not(is_node_typ sv)) svl in *)
(*   let svl2 = List.filter (fun sv -> is_node_typ sv) svl in *)
(*   let pf1 = calc_fix_pure svl1 (filter_var pf svl1) in *)
(*   let (baga, pf2) = ef_elim_exists_1 svl2 (baga, (filter_var pf svl2)) in *)
(*   (baga, mkAnd pf1 pf2 no_pos) *)

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
  val subst : (spec_var * spec_var) list -> t -> t
  val merge_baga : t list -> t list -> t list
  val hull_baga : t list -> t list -> t list
  val is_eq_baga : t list -> t list -> bool
  val mk_elem_from_sv : spec_var -> t
  val get_pure : ?enum_flag:bool -> ?neq_flag:bool -> t list -> Cpure.formula
  val conv_var : t list -> spec_var list
  val get_interval : t -> (spec_var * (Cpure.exp * Cpure.exp)) option
  val from_var : spec_var list -> t list
  (* val conv_var_pairs : (t*t) list -> (spec_var * spec_var) list *)
  (* val from_var_pairs : (spec_var * spec_var) list -> (t*t) list *)
end;;

module type FORM_TYPE =
sig
  type t
  val mk_false : t
  val mk_true : t
  val unsat : t -> bool
  val imply : t -> t -> bool
end;;

(* module type for EPURE, what methods to expose? *)
module type EPURE_TYPE =
sig
  type t
  val zero : t
  val is_zero : t -> bool
  val eq : t -> t -> bool
  val compare : t -> t -> int
  val string_of : t -> string
  val subst : (spec_var * spec_var) list -> t -> t
  val merge_baga : t list -> t list -> t list
  val hull_baga : t list -> t list -> t list
  val is_eq_baga : t list -> t list -> bool
  val mk_elem_from_sv : spec_var -> t
  val norm_baga : CP.formula -> t list -> t list
      (* may throw an exception if false detected *)
  val get_pure : ?enum_flag:bool -> ?neq_flag:bool -> t list -> Cpure.formula
  val conv_var : t list -> spec_var list
  val from_var : spec_var list -> t list
  (* val conv_var_pairs : (t*t) list -> (spec_var * spec_var) list *)
  (* val from_var_pairs : (spec_var * spec_var) list -> (t*t) list *)
end;;

module EPURE =
  functor (Elt : SV_TYPE)  ->
  struct
    type elem = Elt.t
    type spec_var = Cpure.spec_var
    type subs_type = (spec_var * spec_var) list
    (* type epure = (elem * elem option list * formula *)
    type epure = (elem list * formula)
    type epure_disj = epure list
    (* let mk_spec_var e = SpecVar (UNK,Elt.string_of e,Unprimed) *)
    (* type baga_ty = .. *)
    let mk_false = ([], mkFalse no_pos)
    let mk_false_disj = []
    let mk_true = [([], mkTrue no_pos)]

    let is_false (e:epure) = (e == mk_false)
    let string_of (x:epure) = pr_pair (pr_list Elt.string_of) !print_pure_formula x
    let string_of_disj lst = pr_list (* pr_list_ln *) string_of lst
    let mk_data sv = let e = Elt.mk_elem_from_sv sv in
      [([e], mkTrue no_pos)]

    let merge_baga b1 b2 = Elt.merge_baga b1 b2

    let is_eq_baga (b1,_) (b2,_) = Elt.is_eq_baga b1 b2

    let conv_var_sv (lst:elem list) = Elt.conv_var lst

    (* convert ptr to integer constraints *)
    (* ([a,a,b]  --> a!=a & a!=b & a!=b & a>0 & a>0 & b>0 *)
    let baga_conv ?(neq_flag=false) baga : formula =
      Elt.get_pure ~neq_flag:neq_flag baga
      (* let choose hd pos = *)
      (*   if neq_flag then mkNeqNull hd pos *)
      (*   else mkGtVarInt hd 0 pos in *)
      (* let baga = Elt.conv_var baga in *)
      (* if (List.length baga = 0) then *)
      (*   mkTrue no_pos *)
      (* else if (List.length baga = 1) then *)
      (*   choose (List.hd baga) no_pos *)
      (* else *)
      (*   let rec helper i j baga len = *)
      (*     let f1 = mkNeqVar (List.nth baga i) (List.nth baga j) no_pos in *)
      (*     if i = len - 2 && j = len - 1 then *)
      (*       f1 *)
      (*     else if j = len - 1 then *)
      (*       let f2 = helper (i + 1) (i + 2) baga len in *)
      (*       mkAnd f1 f2 no_pos *)
      (*     else *)
      (*       let f2 = helper i (j + 1) baga len in *)
      (*       mkAnd f1 f2 no_pos *)
      (*   in *)
      (*   let f1 = helper 0 1 baga (List.length baga) in *)
      (*   let f2 = List.fold_left (fun f sv -> mkAnd f (choose sv no_pos) no_pos) *)
      (*       (choose (List.hd baga) no_pos) (List.tl baga) in *)
      (*   mkAnd f1 f2 no_pos *)

    (* ef_conv :  ef_pure -> formula *)
    (* conseq must use this *)
    (* ([a,a,b],pure)  --> baga[a,a,b] & a>0 & a>0 & b>0 & pure *)
    let ef_conv ((baga,f)) : formula =
      let bf = baga_conv baga in
      mkAnd bf f no_pos

    (* ef_conv :  ef_pure -> formula *)
    (* conseq must use this *)
    (* ([a,a,b],pure)  --> baga[a,a,b] & a!=null & a!=null & b!=null & pure *)
    let ef_conv_neq ((baga,f)) : formula =
      let bf = baga_conv ~neq_flag:true baga in
      mkAnd bf f no_pos

    (* ([a,a,b]  --> a=1 & a=2 & b=3 *)
    let baga_enum baga : formula =
      Elt.get_pure ~enum_flag:true baga
      (* let baga = Elt.conv_var baga in *)
      (* match baga with *)
      (* | [] -> mkTrue no_pos *)
      (* | h::ts -> *)
      (*   (\* let i = ref 1 in *\) *)
      (*   let f,_= List.fold_left (fun (f,i) sv -> *)
      (*       (\* i := !i + 1; *\) *)
      (*       let i = i + 1 in *)
      (*       (mkAnd f (mkEqVarInt sv (\* !i *\)i no_pos) no_pos, i) *)
      (*     ) ((mkEqVarInt (List.hd baga) (\* !i *\)1 no_pos),1) (List.tl baga) *)
      (*   in f *)


    (* ef_conv_enum :  ef_pure -> formula *)
    (* provide an enumeration that can be used by ante *)
    (* ([a,a,b],pure)  --> a=1 & a=2 & a=3 & pure *)
    let ef_conv_enum ((baga,f)) : formula =
      let bf = baga_enum baga in
      mkAnd bf f no_pos

    let ef_conv_enum baga : formula =
      Debug.no_1 "ef_conv_enum" string_of !Cpure.print_formula
        ef_conv_enum baga

    let ef_conv_disj_ho conv disj : formula =
      let f = List.fold_left (fun f ep ->
          mkOr f (conv ep) None no_pos
        ) (mkFalse no_pos) disj in
      !simplify_raw f

    let ef_conv_disj_x disj : formula =
      ef_conv_disj_ho ef_conv_neq disj

    let ef_conv_disj disj : formula =
      Debug.no_1 "ef_conv_disj" string_of_disj !Cpure.print_formula
        ef_conv_disj_x disj

    let ef_conv_enum_disj disj : formula =
      ef_conv_disj_ho ef_conv_enum disj

    let ef_has_intv_baga ((baga,f)) =
      List.exists (fun b -> (Elt.get_interval b)!=None) baga

    let ef_has_intv_baga_disj disj =
      List.exists ef_has_intv_baga disj

    (* code has bug for ex25m5d.slk *)
    let ef_conv_enum_disj disj : formula =
      Debug.no_1 "ef_conv_enum_disj" string_of_disj !Cpure.print_formula
        (* ef_conv_disj_x disj *)
        ef_conv_enum_disj disj

    let mk_star_wrap efp1 efp2 =
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

    let mk_star efp1 efp2 =
      let res = mk_star_wrap efp1 efp2 in
      res

    let conv_intv_disj (efpd1:epure_disj)  =
      let proc (baga,f) =
        let () = h_2_mem_obj # add_pure f in
        let (lst1,lst2) = List.partition (fun e -> Elt.get_interval e==None) baga in
        let lst2 = List.map (fun e -> 
            let v =  Elt.get_interval e in
            match v with 
            | Some (id,d) -> (id,d)
            | _  -> failwith x_tbi
          ) lst2 in
        let lst2 = List.filter (fun (id,(_,d)) -> 
            let rhs = Cpure.mk_exp_geq d 1 in
            !Cpure.tp_imply f rhs) lst2 in
        let lst2 = List.concat (List.map (fun (id,(e_ind,_)) -> 
            let nid = h_2_mem_obj # get_id id e_ind in
            Elt.from_var [nid]) lst2) in
        (lst1@lst2,f)
      in
      List.map proc efpd1 

    let mk_star_disj_x (efpd1:epure_disj) (efpd2:epure_disj)  =
      let () = x_tinfo_pp ("Omega mk_star_disj:start " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
      let res =
        List.map (fun efp1 -> List.map (fun efp2 -> mk_star efp1 efp2) efpd2) efpd1 in
      let res = List.concat res in
      let () = x_tinfo_pp ("Omega mk_star_disj:end " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
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
    let unsat_call p=
      not (!is_sat_raw (Mcpure.mix_of_pure p))

    let ef_unsat_0 ?(shape=false) ((b,p) as f : epure) : bool =
      (* use ef_conv_enum *)
      if shape then Ssat.SS.is_s_unsat (Elt.conv_var b) p else
      let cf = ef_conv_enum f in
      (* if !Globals.delay_eelim_baga_inv then *)
      (*   (\* if unsat(cf) return true *\) *)
      (*   let ps = list_of_conjs p in *)
      (*   if List.length ps < 42 then *)
      (*     let str_f = ((pr_list Elt.string_of) b) ^ "." ^ (!print_pure_formula p) in *)
      (*     UnCa.is_unsat_cache str_f cf unsat_call *)
      (*   else unsat_call cf *)
      (* else *)
      (* not (!is_sat_raw (Mcpure.mix_of_pure cf)) *)
        unsat_call cf

    (* DO NOT CALL DIRECTLY *)
    let ef_unsat_0 ?(shape=false) (f : epure) : bool =
      Debug.no_1 "ef_unsat" string_of(* _ef_pure *) string_of_bool
          (fun _ ->  ef_unsat_0 ~shape:shape f) f

    let unsat is_shape (b,f) = ef_unsat_0 ~shape:is_shape (b, f)

    let norm is_shape (efp) =
      if unsat is_shape efp then mk_false
      else efp

    let elim_unsat_disj is_shape disj =
      List.filter (fun f -> not(unsat is_shape f)) disj

    (* assumes that baga is sorted *)
    let hull_memset disj =
      let rec aux m disj =
        match disj with
          | [] -> m
          | (m2,_)::lst -> Elt.hull_baga m (aux m2 lst) 
      in match disj with
        | [] -> []
        | (m,_)::lst -> aux m lst

    let hull_memset_sv disj =
      let r = hull_memset disj in
      Elt.conv_var r

    let is_false_disj_x is_shape disj =
      let () = x_tinfo_pp ("Omega is_false_disj:start " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
      let res = List.for_all (fun epf -> unsat is_shape epf) disj in
      (* disj==[] *)
      let () = x_tinfo_pp ("Omega is_false_disj:end " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
      res

    let is_false_disj is_shape disj=
      Debug.no_2 "is_false_disj" string_of_bool string_of_disj string_of_bool
          is_false_disj_x is_shape disj

    let mk_false_disj = []

    (* let unsat_disj disj = is_false_disj (norm_disj disj) *)

    let elim_exists (svl:spec_var list) (b,f) : epure =
      let (b,f) = ef_elim_exists_1 svl (Elt.conv_var b,f) in
      (Elt.from_var b, f)

    let elim_exists (svl:spec_var list) (b,f) : epure =
      let pr = string_of_typed_spec_var_list in
      Debug.no_2 "ef_elim_exists_a" pr string_of string_of elim_exists svl (b,f)

     let wrap_exists (svl:spec_var list) l p (b,f) : epure =
       let b_svl = Elt.conv_var b in
       let new_svl = diff_svl b_svl svl in
       let nf = let svl = intersect_svl svl (fv f) in
       match svl with
         | [] -> f
         | sv::_ -> Exists (sv, f, l, p)
       in
       (Elt.from_var new_svl, nf)

    (* TODO-WN : why ins't elem used instead of spec_var *)
    let elim_exists_disj (svl : spec_var list) (lst : epure_disj) : epure_disj =
       let () = x_tinfo_pp ("Omega call elim_exists_disj-before: " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
      let r = List.map (fun e -> elim_exists svl e) lst in
      let () = x_tinfo_pp ("Omega call elim_exists_disj-end: " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in

      r
    let wrap_exists_disj (svl : spec_var list) l p (lst : epure_disj) : epure_disj =
      let r = List.map (fun e -> wrap_exists svl l p e) lst in
      r

    (* ef_imply : ante:ef_pure -> conseq:ef_pure -> bool *)
    (* does ante --> conseq *)
    (* convert ante with ef_conv_enum *)
    (* convert conseq with ef_conv *)

    let ef_imply_0 (ante : epure) (conseq : epure) : bool =
      let a_f = ef_conv_enum ante in
      let c_f = ef_conv conseq in
      (* a_f --> c_f *)
      let f = mkAnd a_f (mkNot_s c_f) no_pos in
      not (!is_sat_raw (Mcpure.mix_of_pure f))

    let ef_imply_0 (ante : epure) (conseq : epure) : bool =
      Debug.no_2 "ef_imply" string_of(* _ef_pure *) string_of(* _ef_pure *) string_of_bool
        ef_imply_0 ante conseq

    let imply (ante : epure) (conseq : epure) : bool =
      ef_imply_0 ante conseq

    let is_eq_epure ((b1,f1) as ep1) ((b2,f2) as ep2) =
      if Elt.is_eq_baga b1 b2 then
        (imply ep1 ([],f2)) && (imply ep2 ([],f1))
      else false

    let is_eq_epure_syn ((b1,f1) as ep1) ((b2,f2) as ep2) =
      if Elt.is_eq_baga b1 b2 then
        (* Cpure.checkeq (List.map Cpure.name_of_spec_var (Elt.conv_var b1))  f1 f2 [] *)
        Cpure.equalFormula f1 f2
      else false

    (* reducing duplicate? *)
    let norm_disj is_shape disj =
      let pure_cmp_fnc = (* if syn then is_eq_epure_syn else *) is_eq_epure in
      let rec remove_duplicate (disj : epure_disj) : epure_disj =
        match disj with
        | [] -> []
        | hd::tl ->
          let new_tl = remove_duplicate (List.filter (fun ep ->
              not ((* is_eq_epure *)pure_cmp_fnc hd ep)) tl) in
          hd::new_tl
      in
      let () = x_tinfo_pp ("Omega call norm_disj-before: " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
      let sat_disj = (* if syn then disj else *) (List.filter (fun v -> not(is_false v)) (List.map (norm is_shape) disj)) in
      let res = remove_duplicate sat_disj (* (List.filter (fun v -> not(is_false v)) (List.map norm disj)) *) in
      let () = x_tinfo_pp ("Omega call norm_disj-after: " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
      res

    let ef_imply_disj_x (ante : epure_disj) (conseq : epure_disj) : bool =
      let a_f = ef_conv_enum_disj ante in
      let c_f = ef_conv_disj conseq in
      (* a_f --> c_f *)
      let f = mkAnd a_f (mkNot_s c_f) no_pos in
      not (x_add_1 !is_sat_raw (Mcpure.mix_of_pure f))

    let ef_imply_disj_0 (ante : epure_disj) (conseq : epure_disj) : bool =
      (* Debug.no_2 "ef_imply_disj" string_of_ef_pure_disj string_of_ef_pure_disj string_of_bool *)
      ef_imply_disj_x ante conseq

    let imply_disj (ante : epure_disj) (conseq : epure_disj) : bool =
      let () = x_tinfo_pp ("Omega call before imply disj: " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
      let f = List.map (fun (b,f) -> (b,f)) in
      let r = ef_imply_disj_0 (f ante) (f conseq) in
      let () = x_tinfo_pp ("Omega call after imply disj: " ^ (string_of_int !Omega.omega_call_count) ^ " invocations") no_pos in
      r

    let pair_cmp (x1,x2) (y1,y2) =
      let c = Elt.compare x1 y1 in
      if c==0 then Elt.compare x2 y2
      else c

    (* TODO : sst should be of type (sv,sv) list  and not (elem,elem) list *)
    let subst_elem sst v =
      Elt.subst sst v
      (* if Elt.is_zero v then v *)
      (* else try *)
      (*     let (_,t) = List.find (fun (w,_) -> Elt.eq w v) sst in *)
      (*     t *)
      (*   with _ -> failwith ("subst_elem : cannot find elem "^Elt.string_of v ) *)

    (* TODO : sst should be of type (sv,sv) list  and not (elem,elem) list *)
    let subst_epure sst ((baga,f) as ep) =
      try
        let subs_fn = subst_elem sst in
        let new_baga = List.map (subst_elem sst) baga in
        let new_f = subst (sst) f in
        (new_baga,new_f)
      with _ -> ep

    (* TODO : sst should be of type (sv,sv) list  and not (elem,elem) list *)
    let subst_epure_disj sst (lst:epure_disj) =
      List.map (subst_epure sst) lst

    let simplify_disj (disj : epure_disj) : epure_disj =
      let r =
        List.map (fun (baga,pf) -> (baga,simplify_with_label_omega pf)) disj in
      let () = y_binfo_hp (add_str "before" string_of_disj) disj in
      let () = y_binfo_hp (add_str "after" string_of_disj) r in
      r


    let pairwisecheck_disj (disj : epure_disj) : epure_disj =
      List.map (fun (baga,pf) -> (baga,!pairwisecheck pf)) disj

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

    let get_baga (epd : epure_disj) =
      if List.length epd = 0 then []
      else
        List.fold_left (fun acc (baga,_) ->
            Gen.BList.intersect_eq Elt.eq acc baga
        ) (fst (List.hd epd)) (List.tl epd)

    let get_baga_sv (epd : epure_disj) =
      let lst = get_baga epd in
      Elt.conv_var lst

    let mk_epure (pf:formula) =
      [([], (* subs_null *) pf)]

    let to_cpure (ep : epure) = ep

    let to_cpure_disj (epd : epure_disj) = epd

    let from_cpure (ep) = ep

    let from_cpure_disj (epd : epure_disj) = epd

  end


module EPureIOld = EPURE(SV)
module EPureI = EPURE(SV_INTV)

(* module EPureI = EPUREN(SV) *)

type ef_pure_disj = EPureI.epure_disj

class ['a] inv_store name (pr:'a->string) =
  object (self)
    val tab = Hashtbl.create 10
    val mutable pr = pr
    method set_pr pp = pr <- pp
    method find vn =
      Hashtbl.find tab vn
    method replace m vn (fix:'a) =
      if not(name="") then y_tinfo_hp (add_str ("replace("^name^m^")") (pr_pair pr_id pr)) (vn,fix);
      Hashtbl.replace tab vn fix
    method string_of =
      let lst = Hashtbl.fold (fun a b lst -> (a,b)::lst) tab [] in
      pr_list (pr_pair pr_id pr) lst 
  end;;

let map_baga_invs : ((string, ef_pure_disj) Hashtbl.t) = Hashtbl.create 10
let map_num_invs : ((string, (Cpure.spec_var list * Cpure.formula)) Hashtbl.t) = Hashtbl.create 10
let map_precise_invs : ((string, bool) Hashtbl.t) = Hashtbl.create 10

let map_baga_invs 
  = new inv_store  "XXXBAGAXXX "  EPureI.string_of_disj
let map_num_invs 
  = new inv_store  "XXXNUMXXX " (pr_pair !Cpure.print_svl !Cpure.print_formula) 
let map_precise_invs 
  = new inv_store "XXXprecise " string_of_bool
