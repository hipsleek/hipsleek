open Globals
open Sleekcommons
open Gen.Basic
open Exc.GTable
open Cpure

module C = Cast
module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module LP = Lemproving
module AS = Astsimp
module DD = Debug

(*should move to cformula*)
(*res=(ind,base) list *)
(*ind=(pure,(data,rec-pred,inductive formula i.g n=n-1))*)
let partition_cases_x (vname:string) (inv:Cpure.formula) (lfl:(CF.formula * formula_label) list):
(*base cases*)((CF.h_formula_data list * Cpure.formula) list *
(*inductive cases*)((CF.h_formula_view*Cpure.formula) list * CF.h_formula_data list * Cpure.formula) list)=
  let partition_cases_helper f=
    let h, mf,_,_,_ = CF.split_components f in
    let p = Mcpure.pure_of_mix mf in
    let vs = CP.fv p in
    let hs = CF.split_star_conjunctions h in
    let rec check_is_rec hs ir rviews dats rvs conjs=
      match hs with
        | [] -> (ir, rviews, dats, rvs, conjs)
        | h::ss ->
            (match h with
              |  CF.ViewNode hv -> if hv.CF.h_formula_view_name = vname then
                    (*recursive - get pure formula*)
                    let rv = hv.CF.h_formula_view_arguments in
                    let rvp = Cpure.filter_var p rv in
                    check_is_rec ss true (rviews@[(hv,rvp)]) dats (rvs@rv) (conjs@(CP.split_conjunctions rvp))
                  else check_is_rec ss ir rviews dats rvs conjs
              | CF.DataNode hd -> check_is_rec ss ir rviews (dats@[hd]) rvs conjs
              | _ -> check_is_rec ss ir rviews dats rvs conjs
            )
    in
    let (ir, rviews, dats, rvs, conjs) = check_is_rec hs false [] [] [] [] in
    let nvs = List.filter (fun x -> not (List.mem x rvs)) vs in
    (* let _ = print_endline ("vars" ^ (!CP. print_svl vs)) in *)
    (* let _ = print_endline ("rec vars" ^ (!CP. print_svl rvs)) in *)
    (* let _ = print_endline ("non-rec vars" ^ (!CP. print_svl nvs)) in *)
    let p1 = Cpure.filter_var p nvs in
                (*mkAnd with inv*)
    (* let p1 = Cpure.mkAnd p1 inv no_pos in*)
    (* Gen.BList.remove_dups_eq*)
    let remain_conjs = List.filter (fun p -> not(List.mem p conjs)) (CP.split_conjunctions p1)  in
    let p1 = CP.join_conjunctions remain_conjs in
    (ir, rviews, dats, rvs, p1)
  in
  let rec helper2 pl bl indl=
    (
        match pl with
          | [] -> (bl,indl)
          | (ir, rviews, dats, rvs, p1)::ss ->
              if ir then
                helper2 ss bl (indl@ [(rviews, dats, p1)])
              else
                helper2 ss (bl@[(dats,p1)]) indl
    )
  in
  let lf = fst (List.split lfl) in
  let tmp = List.map partition_cases_helper lf in
  helper2 tmp [] []

let partition_cases (vname:string) (inv:Cpure.formula) (lfl:(CF.formula * formula_label) list):
 (*base cases*)((CF.h_formula_data list * Cpure.formula) list *
(*inductive cases*)((CF.h_formula_view*Cpure.formula) list * CF.h_formula_data list * Cpure.formula) list)=
   let pr1 = (fun o -> o) in
   let pr4 = (fun (f,_) -> Cprinter.string_of_formula f) in
   (* let pr2 = pr_list Cprinter.string_of_formula in *)
   let pr5 = pr_list (fun x -> Cprinter.string_of_h_formula (CF.DataNode x)) in
   let pr6 = pr_list (pr_pair pr5 Cprinter.string_of_pure_formula) in
   let pr7 = pr_list (pr_pair (fun x -> Cprinter.string_of_h_formula (CF.ViewNode x)) Cprinter.string_of_pure_formula) in
   let pr8 = pr_list (pr_triple pr7 pr5 Cprinter.string_of_pure_formula) in
   let pr3 = pr_pair pr6 pr8 in
   (* let pr3 = (fun x -> "OUT") in *)
   Debug.no_2 "partition_cases" pr1 (pr_list pr4) pr3
       (fun _ _ -> partition_cases_x vname inv lfl) vname lfl

let synthesize_struc_f (hf:CF.h_formula) (mf:Mcpure.mix_formula):CF.struc_formula=
let f= CF.Base {
     CF.formula_base_heap = hf;
     CF.formula_base_pure = mf;
     CF.formula_base_type = CF.TypeTrue;(*??*)
     CF.formula_base_and = [];
     CF.formula_base_flow = CF.mkNormalFlow ();
     CF.formula_base_label = None;(*should be improved*)
     CF.formula_base_pos = no_pos;
} in
  let sbf = {
      CF.formula_struc_explicit_inst = [];
      CF.formula_struc_implicit_inst = [];
      CF.formula_struc_exists = [];
      CF.formula_struc_base = f;
      CF.formula_struc_continuation = None;
      CF.formula_struc_pos = no_pos;
}
  in (CF.EBase sbf)

(*********Auxs methods for synthesize_one_inductive_pair************************)
  let rec combine_hviews vl hview=
    match vl with
      | [] -> hview
      | hv::hss -> let vh2 = CF.Star {  CF.h_formula_star_h1 = hview;
                       CF.h_formula_star_h2 = CF.ViewNode hv;
                       h_formula_star_pos = no_pos
                    } in
                   combine_hviews hss vh2

  let rec combine_hdatas vl vdata=
    match vl with
      | [] -> vdata
      | hd::hss -> let vh2 = CF.Star {  CF.h_formula_star_h1 = vdata;
                       CF.h_formula_star_h2 = CF.DataNode hd;
                       h_formula_star_pos = no_pos
                    } in
                   combine_hdatas hss vh2
(*********END of Auxs methods for synthesize_one_inductive_pair*********************)

(*generate 2 branches (disjunctions) for each pair*)
(*(CF.h_formula_view*Cpure.formula) list * CF.h_formula_data list * Cpure.formula*)
let synthesize_one_inductive_pair_x neg_view_name ((uvl, ud,up) ,(vl, d,p)):CF.struc_formula=
  let rec combine_rename_hviews vl vheap=
    match vl with
      | [] -> vheap
      | hv::hss -> let tmp = { hv with CF.h_formula_view_name= neg_view_name} in
                   let new_vheap = CF.Star { CF.h_formula_star_h1 = vheap;
                                             CF.h_formula_star_h2 = CF.ViewNode tmp;
                                             h_formula_star_pos = no_pos
                                           } in
                   combine_rename_hviews hss new_vheap
  in
(********************)
 (*neg of vl*)
 (*heap formula*)
  let hvs,p_hvs = List.split uvl in
  let vh1 = combine_hviews (List.tl hvs) (CF.ViewNode (List.hd hvs)) in
  let dh1 = combine_hdatas (List.tl ud) (CF.DataNode (List.hd ud)) in
  let hf1 = CF.Star {  CF.h_formula_star_h1 = dh1;
                       CF.h_formula_star_h2 = vh1;
                       h_formula_star_pos = no_pos
                    } in
 (*pure formula*)
  let p_hv = CP.join_conjunctions p_hvs in
  let p1 = CP.mkAnd p_hv up no_pos in
  (*neg of pure of p*)
  let _ = print_endline ("pure1:" ^ (Cprinter.string_of_pure_formula p)) in
  let p12 = CP.Not (p, None, no_pos) in
  (*mkAnd*)
  let p1 = CP.mkAnd p1 p12 no_pos in
  let sf1 = synthesize_struc_f hf1 (Mcpure.OnePF p1) in
(********************)
 (*non-neg - universal pure*)
 (*heap formula*)
  let hvs,p_hvs = List.split vl in
  let new_first_hv = {(List.hd hvs) with CF.h_formula_view_name= neg_view_name} in
  let vh2 = combine_rename_hviews (List.tl hvs) (CF.ViewNode new_first_hv) in
  let dh2 = combine_hdatas (List.tl d) (CF.DataNode (List.hd d)) in
  (*add data node*)
  let hf2 = CF.Star {  CF.h_formula_star_h1 = dh2;
                       CF.h_formula_star_h2 = vh2;
                       h_formula_star_pos = no_pos
                    } in

 (*pure formula*)
  let p_hv = CP.join_conjunctions p_hvs in
  (* let p2= Mcpure.mix_of_pure_formula up in *)
  (*may need unify names*)
  (*mkAnd p_hvs, p2*)
  let p2 = CP.mkAnd p_hv up no_pos in
  let sf2 = synthesize_struc_f hf2 (Mcpure.OnePF p2) in
  CF.mkEList_no_flatten [(Label_only.empty_spec_label_def,sf1);(Label_only.empty_spec_label_def, sf2)]

let synthesize_one_inductive_pair neg_view_name ((uvl, ud,up) ,(vl, d,p)):CF.struc_formula=
  let pr1 = pr_list (fun x -> Cprinter.string_of_h_formula (CF.DataNode x)) in
  let pr2 = pr_list (pr_pair (fun x -> Cprinter.string_of_h_formula (CF.ViewNode x)) Cprinter.string_of_pure_formula) in
  let pr3 = pr_triple pr2 pr1 Cprinter.string_of_pure_formula in
  Debug.no_1 "synthesize_one_inductive_pair" (pr_pair pr3 pr3) (Cprinter.string_of_struc_formula)
       (fun _ -> synthesize_one_inductive_pair_x neg_view_name ((uvl, ud,up) ,(vl, d,p))) ((uvl, ud,up) ,(vl, d,p))

(*(CF.h_formula_data list * Cpure.formula)*)
let synthesize_one_base (hds,p):CF.struc_formula=
  let combine_hdatas_empty hds=
    match hds with
      | [] -> CF.HTrue
      | _ -> combine_hdatas (List.tl hds) (CF.DataNode (List.hd hds))
  in
  let hf = combine_hdatas_empty hds in
  synthesize_struc_f hf (Mcpure.OnePF p)

let synthesize_neg_view_def_x vd_u vd=
  let rec mkEOr fs f=
    match fs with
      | [] -> f
      | f1::fss ->
            let ls = List.map (fun f -> (Label_only.empty_spec_label_def, f)) (f::fs) in
            CF.mkEList_no_flatten ls
  in
  (*partition into base_case and inductive case*)
  (*we have two kinds of varibales: inductive vars and non-inductive vars (pure formulas)*)
  (**************************)
(*each formula is a case*)
  (*get pure formula ==> slice with non-inductive vars*)
  (*mkAnd (pure formula, inv)*)
  (*heap formulas: partition into data_formula and view_formula*)
  DD.devel_pprint ">>>>>> *partition into base_case and inductive case <<<<<<" no_pos;
  (*DD.devel_hprint (add_str "LHS pure       : " !print_formula) lhs_xpure_orig pos; *)
(**************************)
  let (bc_us,idc_us) = partition_cases vd_u.C.view_name (Mcpure.pure_of_mix vd_u.C.view_user_inv) vd_u.C.view_un_struc_formula in
  let (bcs,idcs) = partition_cases vd.C.view_name (Mcpure.pure_of_mix vd.C.view_user_inv) vd.C.view_un_struc_formula in
  let neg_name = "_n_" ^ vd.C.view_name in
  (*base case*)
  (*should be improved here*)
  (*now just simply add base case of the universal*)
  let b_fs = List.map synthesize_one_base bc_us in
  let f1 = mkEOr (List.tl b_fs) (List.hd b_fs) in
  (*inductive case*)
  (*each universal-each ele*)
  let pr_f = List.combine idc_us idcs in
  let fs = List.map (fun pr -> synthesize_one_inductive_pair neg_name pr) pr_f in
  let f2 = mkEOr fs f1 in
(*  vd *)

  let n_un_str = CF.get_view_branches f2 in
  let rec f_tr_base f = 
    let mf f h fl pos = if (CF.is_complex_heap h) then (CF.mkFalse fl pos)  else f in
    match f with
      | CF.Base b -> mf f b.CF.formula_base_heap b.CF.formula_base_flow b.CF.formula_base_pos
      | CF.Exists b -> mf f b.CF.formula_exists_heap b.CF.formula_exists_flow b.CF.formula_exists_pos
      | CF.Or b -> CF.mkOr (f_tr_base b.CF.formula_or_f1) (f_tr_base b.CF.formula_or_f2) no_pos in
  let rbc = List.fold_left (fun a (c,l)-> 
      let fc = f_tr_base c in
      if (CF.isAnyConstFalse fc) then a 
      else match a with 
        | Some f1  -> Some (CF.mkOr f1 fc no_pos)
        | None -> Some fc) None n_un_str in
  (*let sf = find_pred_by_self vdef data_name in*)
  let sf = [] in
  { C.view_name = neg_name;
    C.view_vars= vd.C.view_vars; (*todo: fresh vars and unifier*)
    C.view_case_vars = [];
    C.view_uni_vars = [];
    C.view_labels = [];
    C.view_modes = vd.C.view_modes;
    C.view_is_prim = false;
    C.view_kind = C.View_NORM;
    C.view_partially_bound_vars= [];
    C.view_materialized_vars = [];
    C.view_data_name = vd.C.view_data_name;
    C.view_formula = f2;
    C.view_user_inv = MCP.OnePF (CP.mkTrue no_pos);(*todo:*)
    C.view_mem = None;
    C.view_xpure_flag = false;
    C.view_inv_lock = None;
    C.view_x_formula = MCP.OnePF (CP.mkTrue no_pos);(*todo:*)
    C.view_baga = vd.C.view_baga;
    C.view_addr_vars = vd.C.view_addr_vars;
    C.view_complex_inv = None;
    C.view_un_struc_formula = n_un_str;
    C.view_base_case = None;
    C.view_prune_branches = [];
    C.view_is_rec = (List.length fs) != 0;
    C.view_pt_by_self = sf; (*todo:*)
    C.view_prune_conditions = [];
    C.view_prune_conditions_baga = [];
    C.view_prune_invariants = [] ;
    C.view_raw_base_case = rbc;
  }

let synthesize_neg_view_def vd_u vd=
  let pr1 = Cprinter.string_of_view_decl in
   Debug.no_2 "synthesize_neg_view_def" pr1 pr1 pr1
       (fun _ _ -> synthesize_neg_view_def_x vd_u vd) vd_u vd
