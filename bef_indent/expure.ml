#include "xdebug.cppo"
open VarGen
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

let find_baga_inv view  =
  if !Globals.is_inferring (* !Globals.gen_baga_inv *) then
    Hashtbl.find Excore.map_baga_invs view.Cast.view_name
  else
    match view.Cast.view_baga_inv with
      | Some efpd -> efpd
      | None ->
            match view.Cast.view_baga_x_over_inv with
              | Some efpd -> efpd
              | None -> failwith "cannot find baga inv 2"

let find_baga_under_inv view =
  match view.Cast.view_baga_under_inv with
    | Some efpd -> efpd
    | None -> Excore.EPureI.mk_false_disj

let simplify lst =
  let group lst =
    let rec grouping acc = function
      | [] -> acc
      | hd::_ as l ->
            let l1,l2 = List.partition (Excore.EPureI.is_eq_baga hd) l in
            grouping (l1::acc) l2
    in
    grouping [] lst
  in
  let groups = group lst in
  let lst = List.map (fun l ->
      List.fold_left (fun (baga,f1) (_,f2) ->
          (baga,Tpdispatcher.tp_pairwisecheck2 f1 f2)
      ) (List.hd l) (List.tl l)
  ) groups in
  lst

let wrap_up_exists_index_var inv_list =
  let sv = mk_typed_spec_var Int "idx" in
  let svl = [sv] in
  List.map (fun inv ->
      List.map (fun (baga,pf) ->
          let new_pf = wrap_exists_svl pf svl in
          (baga,new_pf)
      ) inv
  ) inv_list

let add_index_to_pure_formula pf =
  let sv = mk_typed_spec_var Int "idx" in
  let zero = mkIConst 0 no_pos in
  let var = mkVar sv no_pos in
  let pf0 = mkEqExp var zero no_pos in
  mkAnd pf pf0 no_pos

let rec add_index_to_heap_formula hf =
  match hf with
    | Cformula.Star s ->
          let h1 = s.Cformula.h_formula_star_h1 in
          let h2 = s.Cformula.h_formula_star_h2 in
          Cformula.Star {s with
              Cformula.h_formula_star_h1 = add_index_to_heap_formula h1;
              Cformula.h_formula_star_h2 = add_index_to_heap_formula h2;}
    | Cformula.ViewNode vn ->
          let sv = mk_typed_spec_var Int (fresh_any_name "idx") in
          let svl = vn.Cformula.h_formula_view_arguments in
          let args = vn.Cformula.h_formula_view_args_orig in
          Cformula.ViewNode {vn with
              Cformula.h_formula_view_arguments = svl@[sv];
              Cformula.h_formula_view_args_orig = args@[(SVArg sv, 1)];}
    | _ -> hf

let rec add_index_to_formula (cf : Cformula.formula) : Cformula.formula =
    match cf with
    | Cformula.Base bf ->
          let bp = (Mcpure.pure_of_mix bf.Cformula.formula_base_pure) in
          let bh = bf.Cformula.formula_base_heap in
          let (new_bp, new_bh) =
            if not(Cformula.is_inductive cf) then
              (* if Cformula.is_empty_heap bh then *)
              (add_index_to_pure_formula bp, bh)
            else
              let new_bh = add_index_to_heap_formula bh in
              let sv1 = mk_typed_spec_var Int "idx" in
              let new_svl = Gen.BList.difference_eq eq_spec_var (Cformula.h_fv new_bh) (Cformula.h_fv bh) in
              let sv2 = if (List.length new_svl) > 0 then List.hd new_svl else mk_typed_spec_var Int "idx1" in
              let v1 = mkVar sv1 no_pos in
              let v2 = mkVar sv2 no_pos in
              let one = mkIConst 1 no_pos in
              let pf0 = mkEqExp v1 (mkAdd v2 one no_pos) no_pos in
              let new_bp = mkAnd bp pf0 no_pos in
              (new_bp, new_bh)
          in
          Cformula.Base {bf with
              Cformula.formula_base_pure = Mcpure.mix_of_pure new_bp;
              Cformula.formula_base_heap = new_bh;}
    | Cformula.Or orf ->
          let f1 = orf.Cformula.formula_or_f1 in
          let f2 = orf.Cformula.formula_or_f2 in
          let new_f1 = add_index_to_formula f1 in
          let new_f2 = add_index_to_formula f2 in
          Cformula.Or {orf with
              Cformula.formula_or_f1 = new_f1;
              Cformula.formula_or_f2 = new_f2;}
    | Cformula.Exists ef ->
          let ep = (Mcpure.pure_of_mix ef.Cformula.formula_exists_pure) in
          let eh = ef.Cformula.formula_exists_heap in
          (* let sv = mk_typed_spec_var Int "idx" in *)
          let svl0 = ef.Cformula.formula_exists_qvars in
          let (new_svl, new_ep, new_eh) =
            if not(Cformula.is_inductive cf) then
              (* if Cformula.is_empty_heap eh then *)
              (svl0, add_index_to_pure_formula ep, eh)
            else
              let new_eh = add_index_to_heap_formula eh in
              let sv1 = mk_typed_spec_var Int "idx" in
              let new_svl = Gen.BList.difference_eq eq_spec_var (Cformula.h_fv new_eh) (Cformula.h_fv eh) in
              let sv2 = if (List.length new_svl) > 0 then List.hd new_svl else mk_typed_spec_var Int "idx1" in
              let v1 = mkVar sv1 no_pos in
              let v2 = mkVar sv2 no_pos in
              let one = mkIConst 1 no_pos in
              let pf0 = mkEqExp v1 (mkAdd v2 one no_pos) no_pos in
              let new_ep = mkAnd ep pf0 no_pos in
              (svl0@new_svl, new_ep, new_eh)
          in
          Cformula.Exists {ef with
              Cformula.formula_exists_qvars = new_svl;
              Cformula.formula_exists_pure = Mcpure.mix_of_pure new_ep;
              Cformula.formula_exists_heap = new_eh;}

let add_index_to_view view =
  if List.exists is_int_typ view.Cast.view_vars then
    let sv = mk_typed_spec_var Int "idx" in
    let svl0 = view.Cast.view_vars in
    let new_un_sf = List.map (fun (cf,lbl) ->
        (add_index_to_formula cf,lbl)
    ) view.Cast.view_un_struc_formula in
    {view with Cast.view_vars = svl0@[sv];
        Cast.view_un_struc_formula = new_un_sf
    }
  else
    view

let add_index_to_views view_list =
  List.map (fun v -> add_index_to_view v) view_list

let widen_disj_x disj1 disj2 =
  let pair_list = List.combine disj1 disj2 in
  List.map (fun ((b1,f1), (b2,f2)) ->
      (b1,Fixcalc.widen f1 f2)
  ) pair_list

let widen_disj disj1 disj2 =
  let pr = EPureI.string_of_disj in
  Debug.no_2 "widen_disj" pr pr
  pr (fun _ _ ->
      widen_disj_x disj1 disj2) disj1 disj2

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
            let view = List.find (fun v -> v.Cast.view_name = vnf.Cformula.h_formula_view_name) all_views in
            if !do_under_baga_approx then find_baga_under_inv view
            else find_baga_inv view
            (* if !Globals.gen_baga_inv then *)
            (*   try *)
                (* let disj = Hashtbl.find map_baga_invs vnf.Cformula.h_formula_view_name in *)
                (* let () = x_binfo_hp (add_str "disj" Excore.EPureI.string_of_disj) disj no_pos in *)
            (*     disj *)
            (*   with Not_found -> failwith "cannot find in init_map too" *)
            (* else *)
            (*   let view = List.find (fun v -> v.Cast.view_name = vnf.Cformula.h_formula_view_name) all_views in *)
            (*   if !do_under_baga_approx then find_baga_under_inv view *)
            (*   else find_baga_inv view *)
          in
          let () = Debug.ninfo_hprint (add_str "vnf.Cformula.h_formula_view_name" pr_id) vnf.Cformula.h_formula_view_name no_pos in
          let () = Debug.ninfo_hprint (add_str "efpd" (EPureI.string_of_disj)) efpd no_pos in
          let efpd = EPureI.from_cpure_disj efpd in
          (* need substitue variable *)
          let view = List.find (fun vc -> vnf.Cformula.h_formula_view_name = vc.Cast.view_name) all_views in
          let self_var = Cpure.SpecVar (Named view.Cast.view_data_name, self, Unprimed) in
          let view_args = self_var::view.Cast.view_vars in
          let () = Debug.ninfo_hprint (add_str "view_args" (pr_list Cprinter.string_of_typed_spec_var)) view_args no_pos in
          let () = Debug.ninfo_hprint (add_str "svl" (pr_list Cprinter.string_of_typed_spec_var)) svl no_pos in
          let sst = List.combine view_args svl in
          (* TODO : below should be done using EPureI : DONE *)
          let efpd_h = EPureI.subst_epure_disj sst efpd in
          let efpd_n = EPureI.norm_disj efpd_h in
          let () = Debug.ninfo_hprint (add_str "efpd_n" (EPureI.string_of_disj)) efpd_n no_pos in
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
              (* let () = if (lim!=0 && List.length f > lim) then *)
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
          let () = Debug.ninfo_hprint (add_str "efpd_n1" (EPureI.string_of_disj)) efpd no_pos in
          efpd
    | Cformula.Or orf ->
          let efpd1 = build_ef_formula orf.Cformula.formula_or_f1 all_views in
          let efpd2 = build_ef_formula orf.Cformula.formula_or_f2 all_views in
          let efpd = EPureI.mk_or_disj efpd1 efpd2 in
          let () = Debug.ninfo_hprint (add_str "efpd" (EPureI.string_of_disj)) efpd no_pos in
          let efpd_n = EPureI.norm_disj efpd in
          let () = Debug.ninfo_hprint (add_str "efpd_n2" (EPureI.string_of_disj)) efpd_n no_pos in
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
          let () = Debug.ninfo_hprint (add_str "efpd" (EPureI.string_of_disj)) efpd no_pos in
          let efpd_e = EPureI.elim_exists_disj ef.Cformula.formula_exists_qvars efpd in
          let () = Debug.ninfo_hprint (add_str "efpd_e" (EPureI.string_of_disj)) efpd_e no_pos in
          let efpd_n = EPureI.norm_disj efpd_e in
          let () = Debug.ninfo_hprint (add_str "efpd_n3" (EPureI.string_of_disj)) efpd_n no_pos in
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
  let () = Debug.ninfo_hprint (add_str "before norm" (EPureI.string_of_disj)) disj no_pos in
  let disj_n = EPureI.norm_disj disj in
  let () = Debug.ninfo_hprint (add_str "after norm" (EPureI.string_of_disj)) disj_n no_pos in
  simplify disj_n

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
let fix_test num (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list) : (ef_pure_disj list * bool) =
  let lhs_list = inv_list in
  let rhs_list = List.map (fun vd ->
      Hashtbl.find map_baga_invs vd.Cast.view_name) view_list in
  let rhs_list = List.map (fun epd -> EPureI.from_cpure_disj epd) rhs_list in
  let pair_list = List.combine lhs_list rhs_list in
  let inv_r_list = List.map (fun (a, c) ->
      let r = EPureI.imply_disj a c in
      if r || (num > 0) then
        (a, r)
      else
        (widen_disj c a, r)
  ) pair_list in
  let (new_inv_list, r_list) = List.split inv_r_list in
  (new_inv_list, not (List.exists (fun r -> r = false) r_list))

let fix_test num (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list) : (ef_pure_disj list * bool) =
  let pr1 x = string_of_int (List.length x) in
  let pr2 = pr_list EPureI.string_of_disj in
  Debug.no_2 "fix_test" pr1 pr2 (pr_pair pr2 string_of_bool) (fun _ _ -> (fix_test num (view_list : Cast.view_decl list) (inv_list : ef_pure_disj list))) view_list inv_list

(* compute fixpoint iteration *)
(* strict upper bound 100 *)
(* fix_ef : [view_defn] -> disjunct_num (0 -> precise) -> [ef_pure_disj] *)
let fix_ef_x (view_list : Cast.view_decl list) (all_views : Cast.view_decl list) : ef_pure_disj list =
  let () = Debug.ninfo_hprint (add_str "view_list" (pr_list Cprinter.string_of_view_decl)) view_list no_pos in
  let inv_list = List.fold_left (fun inv_list vc ->
      inv_list@[(build_ef_view vc all_views)]) [] view_list in
  let rec helper num view_list inv_list =
    let () = Debug.ninfo_hprint (add_str "baga inv" (pr_list (pr_pair pr_id EPureI.string_of_disj)))
      (List.combine (List.map (fun vc -> vc.Cast.view_name) view_list) inv_list) no_pos in
    let (inv_list, fixed) = fix_test num view_list inv_list in
    if fixed
    then
      inv_list
    else
      let () = List.iter (fun (vc,inv) ->
          Hashtbl.replace map_baga_invs vc.Cast.view_name (EPureI.to_cpure_disj inv)
      ) (List.combine view_list inv_list) in
      let inv_list = List.fold_left (fun inv_list vc ->
          inv_list@[(build_ef_view vc all_views)]
      ) [] view_list in
      helper (num - 1) view_list inv_list
  in
  let inv_list = helper 5 view_list inv_list in
  let inv_list = wrap_up_exists_index_var inv_list in
  let () = List.iter (fun (vc,inv) ->
      (* this version is being printed *)
      (* let () = Debug.ninfo_hprint (add_str ("baga inv("^vc.Cast.view_name^")") (EPureI.string_of_disj)) inv no_pos in *)
      (* let () = print_string_quiet "\n" in *)
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
  let pr_1 = !print_view_decl_short in
  Debug.no_1 "is_ep_view_arith" pr_1 string_of_bool
      is_ep_view_arith_x cv
