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
open Excore
open Cprinter

let rec build_ef_heap_formula_x (cf : Cformula.h_formula) (all_views : Cast.view_decl list) : ef_pure_disj =
  match cf with
    | Cformula.Star _ ->
          let hfl = Cformula.split_star_conjunctions cf in
          let efpd_n = List.fold_left (fun f hf ->
              let efpd_h = build_ef_heap_formula hf all_views in
              let efpd_s = EPureI.mk_star_disj f efpd_h in
              let efpd_n = EPureI.norm_disj efpd_s in
              efpd_n
          ) (build_ef_heap_formula (List.hd hfl) all_views) (List.tl hfl) in
          efpd_n
    | Cformula.DataNode dnf ->
          let sv = dnf.Cformula.h_formula_data_node in
          let efpd_h = EPureI.mk_data sv in
          efpd_h
    | Cformula.ViewNode vnf ->
          let svl = vnf.Cformula.h_formula_view_node::vnf.Cformula.h_formula_view_arguments in
          let efpd =
            if !Globals.gen_baga_inv then
              try
                Hashtbl.find map_baga_invs vnf.Cformula.h_formula_view_name
              with Not_found -> failwith "cannot find in init_map too"
            else
              let view = List.find (fun v -> v.Cast.view_name = vnf.Cformula.h_formula_view_name) all_views in
              match view.Cast.view_baga_inv with
                | Some efpd -> efpd
                | None -> failwith "cannot find baga inv"
          in
          let _ = Debug.ninfo_hprint (add_str "vnf.Cformula.h_formula_view_name" pr_id) vnf.Cformula.h_formula_view_name no_pos in
          let _ = Debug.ninfo_hprint (add_str "efpd" (EPureI.string_of_disj)) efpd no_pos in
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
  Debug.no_1 "build_ef_heap_formula" string_of_h_formula
      EPureI.string_of_disj (fun _ ->
          build_ef_heap_formula_x cf all_views) cf

let build_ef_heap_formula_with_pure_x (cf : Cformula.h_formula) (efpd_p : ef_pure_disj) (all_views : Cast.view_decl list) : ef_pure_disj =
  match cf with
    | Cformula.Star _ ->
          let hfl = Cformula.split_star_conjunctions cf in
          let efpd_n = List.fold_left (fun f hf ->
              (* let lim = !Globals.epure_disj_limit in *)
              (* let _ = if (lim!=0 && List.length f > lim) then *)
              (*   Globals.dis_inv_baga () *)
              (* in *)
              (* if (!Globals.gen_baga_inv) then *)
                let efpd_h = build_ef_heap_formula hf all_views in
                let efpd_s = EPureI.mk_star_disj f efpd_h in
                let efpd_n = EPureI.norm_disj efpd_s in
                efpd_n
              (* else *)
              (*   f *)
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
  Debug.no_1 "build_ef_heap_formula_with_pure" string_of_h_formula
      EPureI.string_of_disj (fun _ ->
          build_ef_heap_formula_with_pure_x cf efpd_p all_views) cf

(* this need to be moved to EPURE module : DONE *)
let rec build_ef_pure_formula_x (pf : formula) : ef_pure_disj =
  match pf with
    | Or _ ->
          let pf_list = split_disjunctions pf in
          List.fold_left (fun efpd pf ->
              EPureI.mk_or_disj efpd (build_ef_pure_formula pf)
          ) [] pf_list
    | Forall (sv, pf, _, _)
    | Exists (sv, pf, _, _) ->
          let efpd = build_ef_pure_formula pf in
          EPureI.elim_exists_disj [sv] efpd
    (* | Not -> ??? *) 
    | _ -> EPureI.mk_epure pf

and build_ef_pure_formula (pf : formula) : ef_pure_disj =
  Debug.no_1 "build_ef_pure_formula" string_of_pure_formula
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
          (* let efpd_e = List.map (fun efp -> *)
          (*     (EPureI.elim_exists ef.Cformula.formula_exists_qvars efp)) efpd in *)
          let efpd_e = EPureI.elim_exists_disj ef.Cformula.formula_exists_qvars efpd in
          let efpd_n = EPureI.norm_disj efpd_e in
          efpd_n

and build_ef_formula (cf : Cformula.formula) (all_views : Cast.view_decl list) : ef_pure_disj =
  Debug.no_1 "build_ef_formula" string_of_formula
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
  (* NOTE : should be already sorted/normalized! *)
  (* let disj = List.sort EPureI.epure_compare disj in *)
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
      (* let _ = Debug.ninfo_hprint (add_str ("baga inv("^vc.Cast.view_name^")") (EPureI.string_of_disj)) inv no_pos in *)
      (* let _ = print_string_quiet "\n" in *)
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
  Debug.no_1 "is_ep_cformula_arith" string_of_formula string_of_bool
      is_ep_cformula_arith_x f

let is_ep_view_arith_x (cv : view_decl) : bool =
  List.exists (fun (cf,_) -> is_ep_cformula_arith cf)
      cv.view_un_struc_formula

let is_ep_view_arith (cv : view_decl) : bool =
  let pr_1 = fun cv -> cv.view_name in
  let pr_1 = !print_view_decl_short in
  Debug.no_1 "is_ep_view_arith" pr_1 string_of_bool
      is_ep_view_arith_x cv
