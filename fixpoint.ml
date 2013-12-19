module DD = Debug
open Globals
open Wrapper
open Others
open Stat_global
open Global_var
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Solver
open Cast
open Gen.Basic

open Label
module CF = Cformula
module CP = Cpure
module TP = Tpdispatcher
module I = Iast
module AS = Astsimp
module Inf = Infer
module SO = Solver


let rec simplify_post post_fml post_vars prog subst_fml pre_vars inf_post evars ref_vars = match post_fml with
  | CF.Or _ ->
    let disjs = CF.list_of_disjs post_fml in
    let res = List.map (fun f -> simplify_post f post_vars prog subst_fml pre_vars inf_post evars ref_vars) disjs in
    let res = remove_dups_imply (fun (f1,pre1) (f2,pre2) -> rev_imply_formula f1 f2) res in
    Debug.tinfo_hprint (add_str "RES (simplified post)" (pr_list (pr_pair !CF.print_formula pr_no))) res no_pos;
    let fs,pres = List.split res in
    (CF.disj_of_list fs no_pos, List.concat pres)
  | CF.Exists e ->
    let h,p,pre,bag_vars = helper e.CF.formula_exists_heap e.CF.formula_exists_pure post_fml post_vars prog subst_fml pre_vars inf_post ref_vars in
    (*print_endline ("VARS: " ^ Cprinter.string_of_spec_var_list pre_vars);*)
    (CF.Exists {e with CF.formula_exists_qvars = e.CF.formula_exists_qvars @ bag_vars;
        CF.formula_exists_heap = h; CF.formula_exists_pure = MCP.mix_of_pure p},pre)
  | CF.Base b ->
    let h,p,pre,bag_vars = helper b.CF.formula_base_heap b.CF.formula_base_pure post_fml post_vars prog subst_fml pre_vars inf_post ref_vars in
    (*print_endline ("VARS: " ^ Cprinter.string_of_spec_var_list pre_vars);*)
    let exists_h_vars = if pre_vars = [] then [] else 
      List.filter (fun x -> not (CP.is_res_spec_var x || CP.is_hprel_typ x)) (CP.diff_svl (CF.h_fv h) (pre_vars @ ref_vars @ (List.map CP.to_primed ref_vars))) in
    let fml = CF.mkExists (CP.remove_dups_svl (evars @ bag_vars @ exists_h_vars))
        h (MCP.mix_of_pure p) b.CF.formula_base_type b.CF.formula_base_flow b.CF.formula_base_and
        b.CF.formula_base_pos
    in (fml,pre)

let simplify_post post_fml post_vars prog subst_fml pre_vars inf_post evars ref_vars = 
  let pr = Cprinter.string_of_formula in
  let pr2 = Cprinter.string_of_spec_var_list in
  Debug.no_2 "simplify_post" pr pr2 (pr_pair pr (pr_list !CP.print_formula))
      (fun _ _ -> simplify_post post_fml post_vars prog subst_fml pre_vars inf_post evars ref_vars) post_fml post_vars

let rec simplify_pre pre_fml lst_assume = match pre_fml with
  | CF.Or _ ->
    let disjs = CF.list_of_disjs pre_fml in
    let res = List.map (fun f -> simplify_pre f lst_assume) disjs in
    let res = remove_dups_imply rev_imply_formula res in
    CF.disj_of_list res no_pos
(*    let f1 = simplify_pre f1 in*)
(*    let f2 = simplify_pre f2 in*)
(*    if f1 = f2 then f1*)
(*    else Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}*)
  | _ ->
    let h, p, fl, t, a = CF.split_components pre_fml in
    let p1,p2 = List.partition CP.is_lexvar (CP.list_of_conjs (CP.remove_dup_constraints (MCP.pure_of_mix p))) in
    let p = if !do_infer_inc then TP.pairwisecheck_raw (Inf.simplify_helper (CP.conj_of_list p2 no_pos))
      else CP.mkAnd (TP.pairwisecheck_raw (Inf.simplify_helper (CP.conj_of_list p2 no_pos))) (CP.conj_of_list p1 no_pos) no_pos
    in
    let p = if lst_assume = [] then p
      else
        let rels = CP.get_RelForm p in
        let p = CP.drop_rel_formula p in
        let ps = List.filter (fun x -> not (CP.isConstTrue x)) (CP.list_of_conjs p) in
        let pres = List.concat (List.map (fun (a1,a2,a3) ->
          if Gen.BList.mem_eq CP.equalFormula a2 rels then [a3] else []) lst_assume) in
        let pre = CP.conj_of_list (ps@pres) no_pos in
        pre
    in
    CF.mkBase h (MCP.mix_of_pure p) t fl a no_pos

let simplify_pre pre_fml lst_assume =
	let pr = !CF.print_formula in
	Debug.no_1 "simplify_pre" pr pr (fun _ -> simplify_pre pre_fml lst_assume)  pre_fml

let rec simplify_relation_x (sp:CF.struc_formula) subst_fml pre_vars post_vars prog inf_post evars lst_assume
  : CF.struc_formula * CP.formula list =
  match sp with
  | CF.ECase b ->
    let r = map_l_snd (fun s->
        let new_s, pres = simplify_relation s subst_fml pre_vars post_vars prog inf_post evars lst_assume in
        if pres = [] then new_s
        else
	  let lpre = List.map (fun x -> CF.formula_of_pure_formula x no_pos) pres in
	  CF.merge_struc_pre new_s lpre) b.CF.formula_case_branches in
    (CF.ECase {b with CF.formula_case_branches = r},[])
  | CF.EBase b ->
    let r,pres = match b.CF.formula_struc_continuation with
      | None -> (None,[])
      | Some l ->
            let pre_vars = pre_vars @ (CF.fv b.CF.formula_struc_base) in
            let r1,r2 = simplify_relation l subst_fml pre_vars post_vars prog inf_post evars lst_assume
            in (Some r1, r2)
    in
    let base =
      if pres = [] then simplify_pre b.CF.formula_struc_base lst_assume
      else
      let pre = CP.conj_of_list pres no_pos in 
          let xpure_base,_,_ = SO.xpure prog b.CF.formula_struc_base in
      let check_fml = MCP.merge_mems xpure_base (MCP.mix_of_pure pre) true in
      if TP.is_sat_raw check_fml then
        simplify_pre (CF.normalize 1 b.CF.formula_struc_base (CF.formula_of_pure_formula pre no_pos) no_pos) lst_assume
      else b.CF.formula_struc_base in
    (CF.EBase {b with CF.formula_struc_base = base; CF.formula_struc_continuation = r}, [])
  | CF.EAssume b ->
	let pvars = CP.remove_dups_svl (CP.diff_svl (CF.fv b.CF.formula_assume_simpl) post_vars) in
        let (new_f,pres) = simplify_post b.CF.formula_assume_simpl pvars prog subst_fml pre_vars inf_post evars b.CF.formula_assume_vars in
        let (new_f_struc,_) = simplify_relation b.CF.formula_assume_struc subst_fml post_vars post_vars prog inf_post evars lst_assume in
	(CF.EAssume{b with
	    CF.formula_assume_simpl = new_f;
	    CF.formula_assume_struc = new_f_struc;}, pres)
  | CF.EInfer b -> report_error no_pos "Do not expect EInfer at this level"
  | CF.EList b ->
	let new_sp, pres = map_l_snd_res (fun s-> simplify_relation s subst_fml pre_vars post_vars prog inf_post evars lst_assume) b in
	(CF.EList new_sp, List.concat pres)

and simplify_relation sp subst_fml pre_vars post_vars prog inf_post evars lst_assume =
	let pr = !print_struc_formula in
	Debug.no_1 "simplify_relation" pr (pr_pair pr (pr_list !CP.print_formula))
      (fun _ -> simplify_relation_x sp subst_fml pre_vars post_vars prog inf_post evars lst_assume) sp

(*let deep_split f1 f2 =*)
(*  let f1 = TP.simplify_raw f1 in*)
(*  if CP.is_disjunct f1 then*)
(*    let fs = CP.split_disjunctions_deep f1 in*)
(*    List.map (fun f -> (f,f2)) fs*)
(*  else [(f1,f2)]*)

let subst_rel pre_rel pre rel = match rel,pre_rel with
  | CP.BForm ((CP.RelForm (name1,args1,_),_),_), CP.BForm ((CP.RelForm (name2,args2,_),_),_) ->
    if name1 = name2 then
      let subst_args = List.combine (List.map CP.exp_to_spec_var args2) 
                                    (List.map CP.exp_to_spec_var args1) in
      CP.subst subst_args pre
    else rel
  | _ -> report_error no_pos "subst_rel: Expecting a relation"

let subst_fml pre_rel pre fml =
  let conjs = CP.list_of_conjs fml in
  let rels,others = List.partition CP.is_RelForm conjs in
  let rels = List.map (fun r -> subst_rel pre_rel pre r) rels in
  CP.conj_of_list (others@rels) no_pos

let check_defn pre_rel pre rel_dfn =
  List.for_all (fun (lhs,rhs) ->
    let lhs = subst_fml pre_rel pre lhs in
    let _ = Debug.ninfo_hprint (add_str "lhs" !CP.print_formula) lhs no_pos in
    let rhs = subst_fml pre_rel pre rhs in
    let _ = Debug.ninfo_hprint (add_str "rhs" !CP.print_formula) rhs no_pos in
    TP.imply_raw lhs rhs
  ) rel_dfn

let check_oblg pre_rel pre reloblgs pre_rel_df =
  let check1 = TP.imply_raw pre reloblgs in
  let check2 = check_defn pre_rel pre pre_rel_df in
  check1 & check2

let filter_disj (p:CP.formula) (t:CP.formula list) =
  let ps = CP.list_of_disjs p in
  let t = CP.conj_of_list t no_pos in
  let ps = List.concat (List.map (fun x -> 
    if TP.is_sat_raw (MCP.mix_of_pure (CP.mkAnd x t no_pos))
    then
      let xs = CP.list_of_conjs x in
      let xs = List.filter (fun x -> not(TP.imply_raw t x)) xs in
      [CP.conj_of_list xs no_pos]
    else []
    ) ps) in
  CP.disj_of_list ps no_pos

let pre_calculate fp_func input_fml pre_vars proc_spec
  pre pure_oblg_to_check (rel_posts,pre_rel) 
  pre_fmls pre_rel_vars pre_rel_df =
  let pr = Cprinter.string_of_pure_formula in
  let constTrue = CP.mkTrue no_pos in

  let top_down_fp = fp_func 1 input_fml pre_vars proc_spec in
  let _ = Debug.devel_hprint (add_str "top_down_fp" (pr_list (pr_pair pr pr))) top_down_fp no_pos in

  match top_down_fp with
  | [(_,rec_inv)] -> 
    let args = List.map (fun a -> (a,CP.add_prefix_to_spec_var "REC" a)) pre_rel_vars in
    let to_check = CP.subst args pure_oblg_to_check in
    let _ = Debug.ninfo_hprint (add_str "to check" !CP.print_formula) to_check no_pos in
    let fml = CP.mkOr (CP.mkNot_s rec_inv) to_check None no_pos in
    let quan_vars = CP.diff_svl (CP.fv fml) pre_rel_vars in
    let fml = CP.mkForall quan_vars fml None no_pos in
    let _ = Debug.ninfo_hprint (add_str "pre_rec_raw" !CP.print_formula) fml no_pos in
    let pre_rec = TP.simplify fml in
    let _ = Debug.ninfo_hprint (add_str "pre_rec" !CP.print_formula) pre_rec no_pos in

    let list_pre = [pre;pre_rec;pure_oblg_to_check] in
    let final_pre0 = List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue list_pre in
    let final_pre1 = TP.simplify final_pre0 in
    let final_pre2 = filter_disj final_pre1 pre_fmls in
    let final_pre3 = TP.pairwisecheck_raw final_pre2 in
    let final_pre = final_pre3 in
    let _ = Debug.devel_hprint (add_str "final_pre0" !CP.print_formula) final_pre0 no_pos in
    let _ = Debug.devel_hprint (add_str "final_pre1" !CP.print_formula) final_pre1 no_pos in
    let _ = Debug.devel_hprint (add_str "final_pre2" !CP.print_formula) final_pre2 no_pos in
    let _ = Debug.devel_hprint (add_str "final_pre3" !CP.print_formula) final_pre3 no_pos in
    (* let _ = Debug.devel_hprint (add_str "final_pre" !CP.print_formula) final_pre no_pos in *)
    let checkpoint2 = check_defn pre_rel final_pre pre_rel_df in
    if checkpoint2 then 
      List.map (fun (rel,post) -> (rel,post,pre_rel,final_pre)) rel_posts
    else List.map (fun (rel,post) -> (rel,post,constTrue,constTrue)) rel_posts
  | [] -> List.map (fun (rel,post) -> (rel,post,constTrue,constTrue)) rel_posts
  | _ -> report_error no_pos "Error in top-down fixpoint calculation"

let update_rel rel pre_rel new_args old_rhs =
  match old_rhs, pre_rel, rel with
  | CP.BForm ((CP.RelForm (name,args,o1),o2),o3), 
    CP.BForm ((CP.RelForm (name1,_,_),_),_),
    CP.BForm ((CP.RelForm (name2,_,_),_),_) ->
    if name=name1 & name=name2 then
      CP.BForm ((CP.RelForm (name,args@new_args,o1),o2),o3)
    else report_error no_pos "Not support topdown fixpoint for mutual recursion"
  | _,_,_ -> report_error no_pos "Expecting a relation"

let compute_td_one (lhs,old_rhs) (rhs,new_args) pre_rel =
  let lhs_conjs = CP.list_of_conjs lhs in
  let rels,others = List.partition CP.is_RelForm lhs_conjs in
  let new_rels = List.map (fun x -> update_rel x pre_rel new_args old_rhs) rels in
  let lhs = CP.conj_of_list (new_rels @ others) no_pos in
  (lhs,rhs)

let compute_td_fml pre_rel_df pre_rel = 
  let rhs = match pre_rel with
    | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->
      let new_args = List.map (fun x -> CP.mkVar 
        (CP.add_prefix_to_spec_var "p" (CP.exp_to_spec_var x)) no_pos) args in
      CP.BForm ((CP.RelForm (name,args@new_args,o1),o2),o3),new_args
    | _ -> report_error no_pos "Expecting a relation"
  in
  List.map (fun x -> compute_td_one x rhs pre_rel) pre_rel_df

(*from update_with_td_fp, in case post-fixpoint is empty.
 compute fix-point for one pre-relation*)
let pre_rel_fixpoint_x pre_rel pre_fmls fp_func reloblgs pre_vars proc_spec pre_rel_df=
  let constTrue = CP.mkTrue no_pos in
  let pre_rel_vars = List.filter (fun x -> not (CP.is_rel_typ x)) (CP.fv pre_rel) in
  let rel_oblg_to_check = List.filter (fun (_,lhs,_) -> CP.equalFormula lhs pre_rel) reloblgs in
  let pure_oblg_to_check = 
    List.fold_left (fun p (_,_,rhs) -> CP.mkAnd p rhs no_pos) constTrue rel_oblg_to_check in
  let _ = Debug.ninfo_hprint (add_str "oblg to check" !CP.print_formula) pure_oblg_to_check no_pos in
  let checkpoint1 = check_oblg pre_rel constTrue pure_oblg_to_check pre_rel_df in
  if checkpoint1 then [(constTrue,constTrue,pre_rel,constTrue)]
  else 
    let input_fml = compute_td_fml pre_rel_df pre_rel in
    let pr = Cprinter.string_of_pure_formula in
    let _ = Debug.ninfo_hprint (add_str "input_fml" (pr_list (pr_pair pr pr))) input_fml no_pos in
    pre_calculate fp_func input_fml pre_vars proc_spec 
        constTrue pure_oblg_to_check ([constTrue,constTrue],pre_rel) pre_fmls pre_rel_vars pre_rel_df

let pre_rel_fixpoint pre_rel pre_fmls fp_func reloblgs pre_vars proc_spec pre_rel_df=
  let pr1 = Cprinter.string_of_pure_formula in
  let pr2 = pr_pair pr1 pr1 in
  let pr3 = CP.print_rel_cat in
  let pr4 = pr_list (pr_quad pr1 pr1 pr1 pr1) in
  Debug.no_5 "pre_rel_fixpoint" pr1 (pr_list pr1) (pr_list (pr_triple pr3 pr1 pr1)) !CP.print_svl (pr_list pr2) pr4
      (fun _ _ _ _ _ -> pre_rel_fixpoint_x pre_rel pre_fmls fp_func reloblgs pre_vars proc_spec pre_rel_df)
      pre_rel pre_fmls reloblgs pre_vars pre_rel_df

let update_with_td_fp_x bottom_up_fp pre_rel_fmls pre_fmls fp_func 
  preprocess_fun reloblgs pre_rel_df post_rel_df_new post_rel_df 
  pre_vars proc_spec grp_post_rel_flag = 
  let pr = Cprinter.string_of_pure_formula in
  let constTrue = CP.mkTrue no_pos in
  match bottom_up_fp, pre_rel_fmls with
  | [], [pre_rel] ->
        pre_rel_fixpoint pre_rel (*formula of pre_rel_var*) pre_fmls fp_func reloblgs pre_vars proc_spec pre_rel_df
(*     let rel_oblg_to_check = List.filter (fun (_,lhs,_) -> CP.equalFormula lhs pre_rel) reloblgs in *)
(*     let pure_oblg_to_check =  *)
(*       List.fold_left (fun p (_,_,rhs) -> CP.mkAnd p rhs no_pos) constTrue rel_oblg_to_check in *)
(*     let _ = Debug.ninfo_hprint (add_str "oblg to check" !CP.print_formula) pure_oblg_to_check no_pos in *)

(*     let checkpoint1 = check_oblg pre_rel constTrue pure_oblg_to_check pre_rel_df in *)
(*     if checkpoint1 then [(constTrue,constTrue,pre_rel,constTrue)] *)
(*     else  *)
(* (\*      [(constTrue,constTrue,constTrue,constTrue)]*\) *)
(*       let input_fml = compute_td_fml pre_rel_df pre_rel in *)
(*       let _ = Debug.ninfo_hprint (add_str "input_fml" (pr_list (pr_pair pr pr))) input_fml no_pos in *)
(*       pre_calculate fp_func input_fml pre_vars proc_spec  *)
(*         constTrue pure_oblg_to_check ([constTrue,constTrue],pre_rel) pre_fmls pre_rel_vars pre_rel_df *)
  | rel_posts, [pre_rel] ->
  if grp_post_rel_flag = 2 then List.map (fun (p1,p2) -> (p1,p2,constTrue,constTrue)) bottom_up_fp
  else
    let rel,post =
      let rels,posts = List.split rel_posts in
      List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue rels,
      List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue posts
    in
    let pre_rel_vars = List.filter (fun x -> not (CP.is_rel_typ x)) (CP.fv pre_rel) in
    let exist_vars = CP.diff_svl (CP.fv_wo_rel rel) pre_rel_vars in
    let pre = TP.simplify_exists_raw exist_vars post in
    let _ = Debug.info_hprint (add_str "pure pre" !CP.print_formula) pre no_pos in

    let rel_oblg_to_check = List.filter (fun (_,lhs,_) -> CP.equalFormula lhs pre_rel) reloblgs in
    let pure_oblg_to_check = 
      List.fold_left (fun p (_,_,rhs) -> CP.mkAnd p rhs no_pos) constTrue rel_oblg_to_check in
    let _ = Debug.tinfo_hprint (add_str "oblg to check" !CP.print_formula) pure_oblg_to_check no_pos in

    let checkpoint1 = check_oblg pre_rel pre pure_oblg_to_check pre_rel_df in
    if checkpoint1 then
      let pre = TP.simplify pre in
      let pre = filter_disj pre pre_fmls in
      let pre = TP.pairwisecheck_raw pre in
      let _ = Debug.devel_hprint (add_str "pre" !CP.print_formula) pre no_pos in
      List.map (fun (rel,post) -> (rel,post,pre_rel,pre)) rel_posts
    else
      let input_fml = List.map (fun (f1,f2) -> (CP.mkAnd f1 pre no_pos,f2)) post_rel_df_new in
      pre_calculate fp_func input_fml pre_vars proc_spec
        pre pure_oblg_to_check (rel_posts,pre_rel) pre_fmls pre_rel_vars pre_rel_df
  | [(rel,post)],[] ->
    let rels_in_pred = List.filter CP.is_rel_var pre_vars in
    let _ = Debug.tinfo_hprint (add_str "rels_in_pred" !print_svl) rels_in_pred no_pos in
    let post_rel_df = List.filter (fun (f1,_) -> CP.intersect (CP.fv f1) rels_in_pred<>[]) post_rel_df in
(*    let _ = Debug.tinfo_hprint (add_str "pre_rel_df(b4 deep split)" (pr_list (pr_pair pr pr))) post_rel_df no_pos in*)
(*    let new_pre_rel_df = List.concat (List.map (fun (f1,f2) -> deep_split f1 f2) post_rel_df) in*)
(*    let _ = Debug.tinfo_hprint (add_str "pre_rel_df(after deep split)" (pr_list (pr_pair pr pr))) new_pre_rel_df no_pos in*)
    let new_pre_rel_df = List.map (fun (f1,f2) -> (subst_fml rel post f1, subst_fml rel post f2)) post_rel_df in
    let _ = Debug.tinfo_hprint (add_str "new_pre_rel_df" (pr_list (pr_pair pr pr))) new_pre_rel_df no_pos in
    let es = CF.empty_es (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
    let es = {es with CF.es_infer_vars_rel = rels_in_pred} in
    let rel_ass = List.concat (List.map (fun (f1_orig,f2) ->
      let f1 = MCP.mix_of_pure f1_orig in
      let f2 = MCP.mix_of_pure f2 in
(*      let (i_res1,_,_),_ = *)
(*        if (MCP.isConstMTrue f2)  then ((true,[],None),None)*)
(*        else *)
(*          (imply_mix_formula 3 f1 f1 f2 imp_no {mem_formula_mset = []}) in*)
      let lst =
(*        if i_res1 then *)
(*          let rels_fml = List.filter CP.is_RelForm (CP.list_of_conjs f1_orig) in*)
(*          [(constTrue, List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue rels_fml)]*)
(*        else *)
          let _,_,l = Infer.infer_pure_m 3 [] es f1 f1 f1 f2 no_pos in
          List.concat (List.map (fun (_,x,_) -> List.map (fun (a,b,c) -> (c,b)) x) l)
      in lst
(*      if lst=[] then*)
(*        let rels_fml = List.filter CP.is_RelForm (CP.list_of_conjs f1_orig) in*)
(*        [(CP.mkFalse no_pos,List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue rels_fml)]*)
(*      else lst*)
      ) new_pre_rel_df) in
    let _ = Debug.tinfo_hprint (add_str "rel_ass" (pr_list (pr_pair pr pr))) rel_ass no_pos in
    let pairs = preprocess_fun rel_ass in
    let _ = Debug.tinfo_hprint (add_str "pairs" (pr_list (pr_pair pr (pr_list pr)))) pairs no_pos in
    (match pairs with
      | [] -> [(rel,post,constTrue,constTrue)]
      | [(r,lst)] ->
            let final_pre = List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue lst in
            let final_pre = TP.simplify_raw final_pre in
            let final_pre = filter_disj final_pre pre_fmls in
            let final_pre = TP.pairwisecheck_raw final_pre in
            let _ = Debug.devel_hprint (add_str "final_pre(pred)" !CP.print_formula) final_pre no_pos in
            let checkpoint1 = check_defn r final_pre new_pre_rel_df in
            if checkpoint1 then [(rel,post,r,final_pre)]
            else [(rel,post,constTrue,constTrue)]
      | _ -> [(rel,post,constTrue,constTrue)])
        (*      let checkpoint = check_defn r final_pre pre_rel_df in*)
        (*      if checkpoint then [(rel,post,pre_rel,final_pre)]*)
        (*      else [(rel,post,constTrue,constTrue)])*)
  | _,_ -> List.map (fun (p1,p2) -> (p1,p2,constTrue,constTrue)) bottom_up_fp

let update_with_td_fp bottom_up_fp pre_rel_fmls pre_fmls fp_func
  preprocess_fun reloblgs pre_rel_df post_rel_df_new post_rel_df
  pre_vars proc_spec grp_post_rel_flag =
  let pr1 = Cprinter.string_of_pure_formula in
  let pr2 = pr_pair pr1 pr1 in
  let pr2a = pr_list pr2 in
  let pr3 = CP.print_rel_cat in
  let pr3a = pr_list_ln (pr_triple pr3 pr1 pr1) in
  let pr4 = pr_list (pr_quad pr1 pr1 pr1 pr1) in
  Debug.no_7 "update_with_td_fp" (pr_list_ln pr1) (pr_list_ln pr1)
      pr3a pr2a pr2a pr2a !CP.print_svl pr4
      (fun _ _ _ _ _ _ _ -> update_with_td_fp_x bottom_up_fp pre_rel_fmls pre_fmls fp_func
          preprocess_fun reloblgs pre_rel_df post_rel_df_new post_rel_df
          pre_vars proc_spec grp_post_rel_flag)
      pre_rel_fmls pre_fmls reloblgs pre_rel_df post_rel_df_new post_rel_df pre_vars
