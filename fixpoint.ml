#include "xdebug.cppo"
open VarGen
module DD = Debug
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
open Expure
module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module TP = Tpdispatcher
(* module I = Iast *)
(* module C = Cast *)
(* module AS = Astsimp *)
(* module Inf = Infer *)
(* module SO = Solver *)

let get_inv_x prog sel_vars vnode=
  let inv = look_up_view_inv prog.prog_view_decls (vnode.CF.h_formula_view_node::vnode.CF.h_formula_view_arguments)
      vnode.CF.h_formula_view_name (x_add_3 Fixcalc.compute_inv) in
  CP.filter_var inv sel_vars

let get_inv prog sel_vars vnode=
  let pr1 vn = Cprinter.string_of_h_formula (CF.ViewNode vn) in
  Debug.no_2 "get_inv" !CP.print_svl pr1 !CP.print_formula 
    (fun _ _ -> get_inv_x prog sel_vars vnode)
    sel_vars vnode


let rec eqHeap h1 h2 = match (h1,h2) with
  | (CF.Star _, CF.Star _) -> 
    let lst1 = CF.split_star_conjunctions h1 in
    let lst2 = CF.split_star_conjunctions h2 in
    List.for_all (fun x -> Gen.BList.mem_eq eqHeap x lst2) lst1 
    && List.for_all (fun x -> Gen.BList.mem_eq eqHeap x lst1) lst2
  | _ -> h1 = h2

let rev_imply_formula f1 f2 = match (f1,f2) with
  | (CF.Base _, CF.Base _) | (CF.Exists _, CF.Exists _) -> 
    let h1,p1,vp1,fl1,b1,t1 = CF.split_components f1 in
    let h2,p2,vp2,fl2,b2,t2 = CF.split_components f2 in
    (*    let p1 = MCP.pure_of_mix p1 in*)
    (*    let p2 = MCP.pure_of_mix p2 in*)
    let res = eqHeap h1 h2 && fl1=fl2 && b1=b2 && t1=t2 in
    let res1 = x_add TP.imply_raw_mix p1 p2 in
    if res then
      if res1 then true
      else false
      (*        let p_hull = TP.hull (CP.mkOr p1 p2 None no_pos) in*)
      (*        CP.no_of_disjs p_hull == 1*)
    else false
  | _ -> f1=f2

let remove_dups_imply imply lst =
  let res = Gen.BList.remove_dups_eq imply lst in
  Gen.BList.remove_dups_eq imply (List.rev res)

let rec elim_heap h p pre_vars heap_vars aset ref_vars = 
  match h with
  | CF.Star {CF.h_formula_star_h1 = h1;
             CF.h_formula_star_h2 = h2;
             CF.h_formula_star_pos = pos} -> 
    let heap_vars = CF.h_fv h1 @ CF.h_fv h2 in
    let h1 = elim_heap h1 p pre_vars heap_vars aset ref_vars in
    let h2 = elim_heap h2 p pre_vars heap_vars aset ref_vars in
    CF.mkStarH h1 h2 pos
  | CF.Conj {CF.h_formula_conj_h1 = h1;
             CF.h_formula_conj_h2 = h2;
             CF.h_formula_conj_pos = pos} -> 
    let h1 = elim_heap h1 p pre_vars heap_vars aset ref_vars in
    let h2 = elim_heap h2 p pre_vars heap_vars aset ref_vars in
    CF.mkConjH h1 h2 pos
  | CF.Phase { CF.h_formula_phase_rd = h1;
               CF.h_formula_phase_rw = h2;
               CF.h_formula_phase_pos = pos} -> 
    let h1 = elim_heap h1 p pre_vars heap_vars aset ref_vars in
    let h2 = elim_heap h2 p pre_vars heap_vars aset ref_vars in
    CF.mkPhaseH h1 h2 pos
  | CF.ViewNode v ->
    let v_var = v.CF.h_formula_view_node in
    if Gen.BList.mem_eq CP.eq_spec_var_x v_var ref_vars && CP.is_unprimed v_var 
    then CF.HEmp
    else
      let alias = (CP.EMapSV.find_equiv_all v_var aset) @ [v_var] in
      if List.exists CP.is_null_const alias then CF.HEmp 
      else
        let cond = (CP.intersect_x (CP.eq_spec_var_x) alias pre_vars = []) 
                   && not (List.exists (fun x -> CP.is_res_spec_var x) alias)
                   && List.length (List.filter (fun x -> x = v_var) heap_vars) <= 1 in 
        if cond then CF.HEmp else h
  | CF.DataNode d ->
    let d_var = d.CF.h_formula_data_node in
    if Gen.BList.mem_eq CP.eq_spec_var_x d_var ref_vars && CP.is_unprimed d_var 
    then CF.HEmp
    else
      let alias = (CP.EMapSV.find_equiv_all d_var aset) @ [d_var] in
      let cond = (CP.intersect_x (CP.eq_spec_var_x) alias pre_vars = []) 
                 && not (List.exists (fun x -> CP.is_res_spec_var x) alias)
                 && List.length (List.filter (fun x -> x = d_var) heap_vars) <= 1
      in if cond then CF.HEmp else h
  | _ -> h

let elim_heap h p pre_vars heap_vars aset ref_vars =
  let pr = Cprinter.string_of_h_formula in
  let pr2 = Cprinter.string_of_pure_formula in
  let pr3 = !print_svl in
  Debug.no_4 "elim_heap" pr pr2 pr3 pr3 pr
    (fun _ _ _ _ -> elim_heap h p pre_vars heap_vars aset ref_vars) h p pre_vars heap_vars

let helper heap pure post_fml post_vars prog subst_fml pre_vars inf_post ref_vars =
  let h, p, _, _, _, _ = CF.split_components post_fml in
  let p = MCP.pure_of_mix p in
  (* WN : why is there a need to weaken the post-condition?? *)
  (* let h = if pre_vars = [] || not(inf_post) then h else ( *)
  (*     enulalias := true; *)
  (*     let node_als = MCP.ptr_equations_with_null (MCP.mix_of_pure p) in *)
  (*     enulalias := false; *)
  (*     let node_aset = CP.EMapSV.build_eset node_als in *)
  (*     elim_heap h p pre_vars (CF.h_fv h) node_aset ref_vars) *)
  (* in *)
  let p,pre,bag_vars = begin
    match subst_fml with
    | None ->
      let post_vars = CP.remove_dups_svl (List.filter (fun x -> not (CP.is_res_spec_var x))
                                            (CP.diff_svl post_vars ((CF.h_fv h) @ pre_vars @ ref_vars @ (List.map CP.to_primed ref_vars)))) in
      (*      let p = if TP.is_bag_constraint p && pre_vars!=[] then*)
      (*        let als = MCP.ptr_bag_equations_without_null (MCP.mix_of_pure p) in*)
      (*        let aset = CP.EMapSV.build_eset als in*)
      (*        let alias = create_alias_tbl post_vars aset in*)
      (*        let subst_lst = List.concat (List.map (fun vars -> if vars = [] then [] else *)
      (*            let hd = List.hd vars in List.map (fun v -> (v,hd)) (List.tl vars)) alias) in*)
      (*        CP.subst subst_lst p *)
      (*      else p in*)
      let bag_vars, post_vars = List.partition CP.is_bag_typ post_vars in
      let p = x_add_1 TP.simplify (CP.mkExists post_vars p None no_pos) in
      (p,[],bag_vars)
    | Some triples (*(rel, post, pre)*) ->
      let process_tables results =
        let sd = Fixcalc.get_reorder () in
        List.map (fun (r,post,pre) -> match r with
            | CP.BForm ((CP.RelForm (name,args,_),_),_) -> 
              let (_,pc,_) = List.find (fun (n,_,_) -> n=name) sd in
              (name,args,pc,post,pre)
            | _ -> failwith (* report_error no_pos *) ("process_tables expecting relation but got:"^(!CP.print_formula r))
          ) results 
      in
      (* type: (CP.formula * 'd * 'e) list -> *)
      (*   (CP.spec_var * CP.exp list * bool list option * 'd * 'e) list *)
      let process_tables results =
        let pr = pr_list (fun (f,_,_) -> !CP.print_formula f) in
        let pr2 = pr_list (fun (sv,args,blst,_,_) -> pr_triple !CP.print_sv (pr_list !CP.print_exp) 
                              (pr_option (pr_list string_of_bool))  (sv,args,blst)) in
        Debug.no_1 "process_tables" pr pr2 process_tables results
      in
      if inf_post then
        try
          let res_table = process_tables triples in
          (* let rels = CP.get_RelForm p in *)
          let pr = !CP.print_formula in
          let () = x_tinfo_hp (add_str "triples" (pr_list (pr_triple pr pr pr)) ) triples no_pos in
          let p = x_add_1 CP.subs_rel_formula res_table p in
          (* let ps = List.filter (fun x -> not (CP.isConstTrue x)) (CP.list_of_conjs p) in  *)
          (* WN : code below seems redundant *)
          (* let pres,posts = List.split (List.concat (List.map (fun (a1,a2,a3) ->  *)
          (*     if Gen.BList.mem_eq CP.equalFormula a1 rels *)
          (*     then [(a3,a2)] else []) triples)) in *)
          let post = p in
          let pre = CP.conj_of_list (List.map (fun (_,_,pre) -> pre) triples) no_pos in
          let () = x_tinfo_hp (add_str "pre" (!CP.print_formula)) pre no_pos in
          let () = x_tinfo_hp (add_str "post" (!CP.print_formula)) post no_pos in
          (post,[pre],[])
        with _ -> (CP.mkTrue no_pos,[],[])
      else
        let rels = CP.get_RelForm p in
        let pres,posts = List.split (List.concat (List.map (fun (a1,a2,a3) -> 
            if Gen.BList.mem_eq CP.equalFormula a1 rels
            then [(a3,a2)] else []) triples)) in
        let pre = CP.conj_of_list pres no_pos in
        (p,[pre],[])
  end
  in
  (h, p, pre, bag_vars)

(* type: 'a -> *)
(*   'b -> *)
  (* CF.formula -> *)
  (* CP.spec_var list -> *)
  (* 'c -> *)
  (* (CP.formula * CP.formula * CP.formula) list option -> *)
  (* Cast.P.spec_var list -> *)
  (* bool -> *)
  (* CP.spec_var list -> *)
  (* CF.h_formula * TP.CP.formula * CP.formula list * CP.spec_var list *)

let helper heap pure post_fml post_vars prog subst_fml pre_vars inf_post ref_vars =
  let pr_h_f = !CF.print_h_formula in
  let pr_pf = !CP.print_formula in
  let pr_svl = !CP.print_svl in
  let pr1 = !CF.print_formula in
  let pr_3 = pr_option (pr_list (pr_triple pr_pf pr_pf pr_pf)) in
  let pr_r = pr_quad pr_h_f pr_pf (pr_list pr_pf) pr_svl in
  Debug.no_3 "simplify_post_helper" pr1 (add_str "post_vars" pr_svl) 
    (add_str "subst_fml" pr_3) pr_r (fun _ _ _ -> helper heap pure post_fml post_vars prog subst_fml pre_vars inf_post ref_vars)
    post_fml post_vars subst_fml

let rec simplify_post post_fml post_vars prog subst_fml pre_vars inf_post evars ref_vars = match post_fml with
  | CF.Or _ ->
    let disjs = CF.list_of_disjs post_fml in
    let res = List.map (fun f -> simplify_post f post_vars prog subst_fml pre_vars inf_post evars ref_vars) disjs in
    let res = remove_dups_imply (fun (f1,pre1) (f2,pre2) -> rev_imply_formula f1 f2) res in
    x_tinfo_hp (add_str "RES (simplified post)" (pr_list (pr_pair !CF.print_formula pr_no))) res no_pos;
    let fs,pres = List.split res in
    (CF.disj_of_list fs no_pos, List.concat pres)
  | CF.Exists e ->
    let h,p,pre,bag_vars = x_add helper e.CF.formula_exists_heap e.CF.formula_exists_pure post_fml post_vars prog subst_fml pre_vars inf_post ref_vars in
    (*print_endline ("VARS: " ^ Cprinter.string_of_spec_var_list pre_vars);*)
    (CF.Exists {e with CF.formula_exists_qvars = e.CF.formula_exists_qvars @ bag_vars;
                       CF.formula_exists_heap = h; CF.formula_exists_pure = MCP.mix_of_pure p},pre)
  | CF.Base b ->
    let h,p,pre,bag_vars = x_add helper b.CF.formula_base_heap b.CF.formula_base_pure post_fml post_vars prog subst_fml pre_vars inf_post ref_vars in
    (*print_endline ("VARS: " ^ Cprinter.string_of_spec_var_list pre_vars);*)
    let exists_h_vars = if pre_vars = [] then [] else 
        List.filter (fun x -> not (CP.is_res_spec_var x || CP.is_hprel_typ x)) (CP.diff_svl (CF.h_fv h) (pre_vars @ ref_vars @ (List.map CP.to_primed ref_vars))) in
    let fml = CF.mkExists (CP.remove_dups_svl (evars @ bag_vars @ exists_h_vars))
        h (MCP.mix_of_pure p) b.CF.formula_base_vperm b.CF.formula_base_type b.CF.formula_base_flow b.CF.formula_base_and
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
    let h, p, vp, fl, t, a = CF.split_components pre_fml in
    let p1,p2 = List.partition CP.is_lexvar (CP.list_of_conjs (CP.remove_dup_constraints (MCP.pure_of_mix p))) in
    let p = if !do_infer_inc then TP.pairwisecheck_raw (Infer.simplify_helper (CP.conj_of_list p2 no_pos))
      else CP.mkAnd (TP.pairwisecheck_raw (Infer.simplify_helper (CP.conj_of_list p2 no_pos))) (CP.conj_of_list p1 no_pos) no_pos
    in
    let p = if lst_assume = [] then x_add_1 CP.drop_rel_formula p (* need to recheck *)
      else
        let rels = CP.get_RelForm p in
        let p = x_add_1 CP.drop_rel_formula p in
        let ps = List.filter (fun x -> not (CP.isConstTrue x)) (CP.list_of_conjs p) in
        let pres = List.concat (List.map (fun (a1,a2,a3) ->
            if Gen.BList.mem_eq CP.equalFormula a2 rels then [a3] else []) lst_assume) in
        let pfl = ps@pres in
        let pre = CP.conj_of_list pfl no_pos in
        let pre = Wrapper.wrap_exception pre CF.simplify_aux pre in
        pre
    in
    CF.mkBase h (MCP.mix_of_pure p) vp t fl a no_pos

let simplify_pre pre_fml lst_assume =
  let pr = !CF.print_formula in
  let pr_f = !CP.print_formula in
  let pr1 = pr_list (fun (_,f1,f2) -> (pr_pair pr_f pr_f) (f1,f2)) in
  Debug.no_2 "simplify_pre" pr pr1 pr (fun _ _ -> simplify_pre pre_fml lst_assume) pre_fml lst_assume

let rec simplify_relation (sp:CF.struc_formula) subst_fml pre_vars post_vars prog inf_post evars lst_assume
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
        let xpure_base,_,_ = x_add Cvutil.xpure 16 prog b.CF.formula_struc_base in
        let check_fml = MCP.merge_mems xpure_base (MCP.mix_of_pure pre) true in
        if TP.is_sat_raw check_fml then
          simplify_pre (x_add CF.normalize 1 b.CF.formula_struc_base (CF.formula_of_pure_formula pre no_pos) no_pos) lst_assume
        else b.CF.formula_struc_base in
    (CF.EBase {b with CF.formula_struc_base = base; CF.formula_struc_continuation = r}, [])
  | CF.EAssume b ->
    let pvars = CP.remove_dups_svl (CP.diff_svl (CF.fv b.CF.formula_assume_simpl) post_vars) in
    let (new_f,pres) = simplify_post b.CF.formula_assume_simpl pvars prog subst_fml pre_vars inf_post evars b.CF.formula_assume_vars in
    (* let (new_f_struc,_) = simplify_relation b.CF.formula_assume_struc subst_fml post_vars post_vars prog inf_post evars lst_assume in *)
    let new_f_struc = CF.mkEBase new_f None no_pos in
    (CF.EAssume {b with
                 CF.formula_assume_simpl = new_f;
                 CF.formula_assume_struc = new_f_struc;}, pres)
  | CF.EInfer b -> (* report_error no_pos "Do not expect EInfer at this level" *)
    let cont, pres = simplify_relation b.CF.formula_inf_continuation subst_fml pre_vars post_vars prog inf_post evars lst_assume in
    CF.EInfer { b with CF.formula_inf_continuation = cont; }, pres
  | CF.EList b ->
    let new_sp, pres = map_l_snd_res (fun s-> simplify_relation s subst_fml pre_vars post_vars prog inf_post evars lst_assume) b in
    (CF.EList new_sp, List.concat pres)

let simplify_relation sp subst_fml pre_vars post_vars prog inf_post evars lst_assume =
  let pr = !print_struc_formula in
  let pr_f = !CP.print_formula in
  let pr1 = pr_option (pr_list (pr_triple pr_f pr_f pr_f)) in
  let pr2 = pr_list (fun (_,f1,f2) -> (pr_pair pr_f pr_f) (f1,f2)) in
  Debug.no_3 "simplify_relation" pr pr1 (add_str "lst_assume" pr2) (pr_pair pr (pr_list pr_f))
    (fun _ _ _ -> simplify_relation sp subst_fml pre_vars post_vars prog inf_post evars lst_assume) sp subst_fml lst_assume

(*let deep_split f1 f2 =*)
(*  let f1 = TP.simplify_raw f1 in*)
(*  if CP.is_disjunct f1 then*)
(*    let fs = CP.split_disjunctions_deep f1 in*)
(*    List.map (fun f -> (f,f2)) fs*)
(*  else [(f1,f2)]*)

let subst_rel_x pre_rel pre rel = match rel,pre_rel with
  | CP.BForm ((CP.RelForm (name1,args1,_),_),_), CP.BForm ((CP.RelForm (name2,args2,_),_),_) ->
    if name1 = name2 then
      (* args1 may have extra flow arg at the end *)
      let subst_args = (* List.combine *) CF.combine_length_leq (List.map CP.exp_to_spec_var args2)
          (List.map CP.exp_to_spec_var args1) [] in
      CP.subst subst_args pre
    else rel
  | _ -> report_error no_pos "subst_rel: Expecting a relation"

let subst_rel pre_rel pre rel =
  let pr1 = !CP.print_formula in
  Debug.no_3 "subst_rel" pr1 pr1 pr1 pr1
    (fun _ _ _ -> subst_rel_x pre_rel pre rel)
    pre_rel pre rel

let subst_fml pre_rel pre fml =
  let conjs = CP.list_of_conjs fml in
  let rels,others = List.partition CP.is_RelForm conjs in
  let rels = List.map (fun r -> subst_rel pre_rel pre r) rels in
  CP.conj_of_list (others@rels) no_pos

let check_defn pre_rel pre rel_dfn =
  List.for_all (fun (lhs,rhs) ->
      let lhs = subst_fml pre_rel pre lhs in
      let () = Debug.ninfo_hprint (add_str "lhs" !CP.print_formula) lhs no_pos in
      let rhs = subst_fml pre_rel pre rhs in
      let () = Debug.ninfo_hprint (add_str "rhs" !CP.print_formula) rhs no_pos in
      TP.imply_raw lhs rhs
    ) rel_dfn

let check_defn pre_rel pre rel_dfn =
  let pr = !CP.print_formula in
  Debug.no_3 "check_defn" pr pr (pr_list (pr_pair pr pr)) string_of_bool
    (fun _ _ _ -> check_defn pre_rel pre rel_dfn) pre_rel pre rel_dfn

let check_oblg pre_rel pre reloblgs pre_rel_df =
  let check1 = TP.imply_raw pre reloblgs in
  let check2 = check_defn pre_rel pre pre_rel_df in
  check1 && check2

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

let filter_disj (p:CP.formula) (t:CP.formula list) =
  let pr = !CP.print_formula in
  Debug.no_2 "filter_disj" pr (pr_list pr) pr filter_disj p t 

let pre_calculate fp_func input_fml pre_vars proc_spec
    pre pure_oblg_to_check (rel_posts,pre_rel)
    pre_fmls pre_rel_vars pre_rel_df =
  let pr = Cprinter.string_of_pure_formula in
  let constTrue = CP.mkTrue no_pos in

  let top_down_fp = fp_func 1 input_fml pre_vars proc_spec in
  let () = Debug.binfo_hprint (add_str "top_down_fp" (pr_list (pr_pair pr pr))) top_down_fp no_pos in

  match top_down_fp with
  | [(_,rec_inv)] ->
    let args = List.map (fun a -> (a,CP.add_prefix_to_spec_var "REC" a)) pre_rel_vars in
    let to_check = CP.subst args pure_oblg_to_check in
    let fml = CP.mkOr (CP.mkNot_s rec_inv) to_check None no_pos in
    let quan_vars = CP.diff_svl (CP.fv fml) pre_rel_vars in
    (* let quan_vars = CP.diff_svl (CP.fv fml) (pre_rel_vars@(List.map (fun (_,x) -> x) args)) in *) (*TODOIMM remove this line*)
    let fml = CP.mkForall quan_vars fml None no_pos in
    let () =  x_dinfo_hp (add_str "to check" !CP.print_formula) to_check no_pos in
    let () =  x_dinfo_hp (add_str "rec_inv" !CP.print_formula) rec_inv no_pos in
    let () =  x_dinfo_hp (add_str "pre_rec_raw (fml) " !CP.print_formula) fml no_pos in
    let pre_rec = x_add_1 TP.simplify fml in
    let () = x_dinfo_hp (add_str "pre_rec" !CP.print_formula) pre_rec no_pos in

    (*NEW procedure: not add pre_inv at the begining*)
    let list_pre = [pre_rec;pure_oblg_to_check] in
    let final_pre0 = List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue list_pre in
    let final_pre1 = x_add_1 TP.simplify final_pre0 in
    let final_pre2 = filter_disj final_pre1 (pre_fmls) in
    (* NEW procedure# Form pre-condition given invariant:  D:=gist Pre given Inv;*)
    (* let final_pre2 = pure_oblg_to_check in  *)(* TODOIMM to remove this line *)
    let final_pre3 = x_add TP.om_gist final_pre2 pre in
    (* let final_pre3 = final_pre2 in (\* TODOIMM to remove this line *\) *)
    (* let final_pre3a = CP.mkAnd final_pre2 pre no_pos in (\* TODOIMM to remove this line *\) *)
    let final_pre3a = CP.mkAnd final_pre3 pre no_pos in
    (* let final_pre4a = TP.pairwisecheck_raw final_pre3 in *)
    let final_pre4b = TP.pairwisecheck_raw final_pre3a in
    let final_pre = x_add TP.om_gist final_pre4b pre in
    (* let final_pre = final_pre4b in (\* TODOIMM to remove this line *\) *)

    let () = x_dinfo_hp (add_str "final_pre0" !CP.print_formula) final_pre0 no_pos in
    let () = x_dinfo_hp (add_str "final_pre1" !CP.print_formula) final_pre1 no_pos in
    let () = x_dinfo_hp (add_str "final_pre2" !CP.print_formula) final_pre2 no_pos in
    let () = x_dinfo_hp (add_str "final_pre3" !CP.print_formula) final_pre3 no_pos in
    let () = x_dinfo_hp (add_str "final_pre3a" !CP.print_formula) final_pre3a no_pos in
    (* let () = x_dinfo_hp (add_str "final_pre4a" !CP.print_formula) final_pre4a no_pos in *)
    let () = x_dinfo_hp (add_str "final_pre4b" !CP.print_formula) final_pre4b no_pos in
    (* let () = x_dinfo_hp (add_str "final_pre" !CP.print_formula) final_pre no_pos in *)
    let checkpoint2 = check_defn pre_rel final_pre pre_rel_df in
    if checkpoint2 then
      List.map (fun (rel,post) -> (rel,post,pre_rel,final_pre)) rel_posts
    else List.map (fun (rel,post) -> (rel,post,pre_rel (* constTrue *),constTrue)) rel_posts (* need to recheck, why constTrue *)
  | [] -> List.map (fun (rel,post) -> (rel,post,constTrue,constTrue)) rel_posts
  | _ -> report_error no_pos "Error in top-down fixpoint calculation"

let calculate_gfp fp_func input_fml pre_vars proc_spec
    pre pure_oblg_to_check (rel_posts,pre_rel)
    pre_fmls pre_rel_vars pre_rel_df =
  let pr = Cprinter.string_of_pure_formula in
  let constTrue = CP.mkTrue no_pos in
  let top_down_fp = fp_func 1 input_fml pre_vars proc_spec in
  let () = Debug.binfo_hprint (add_str "top_down_fp" (pr_list (pr_pair pr pr))) top_down_fp no_pos in

  match top_down_fp with
  | [(_,rec_inv)] ->
    let args = List.map (fun a -> (a,CP.add_prefix_to_spec_var "REC" a)) pre_rel_vars in
    let to_check = CP.subst args pure_oblg_to_check in
    let fml = CP.mkOr (CP.mkNot_s rec_inv) to_check None no_pos in
    let quan_vars = CP.diff_svl (CP.fv fml) pre_rel_vars in
    (* let quan_vars = CP.diff_svl (CP.fv fml) (pre_rel_vars@(List.map (fun (_,x) -> x) args)) in *) (*TODOIMM remove this line*)
    let fml = CP.mkForall quan_vars fml None no_pos in
    let () =  x_binfo_hp (add_str "to check" !CP.print_formula) to_check no_pos in
    let () =  x_binfo_hp (add_str "rec_inv" !CP.print_formula) rec_inv no_pos in
    let () =  x_binfo_hp (add_str "pre_rec_raw (fml) " !CP.print_formula) fml no_pos in
    let pre_rec = x_add_1 TP.simplify fml in
    let () = x_binfo_hp (add_str "pre_rec" !CP.print_formula) pre_rec no_pos in

    (*NEW procedure: not add pre_inv at the begining*)
    let list_pre = [pre_rec;pure_oblg_to_check] in
    let final_pre0 = List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue list_pre in
    let final_pre1 = x_add_1 TP.simplify final_pre0 in
    let final_pre2 = filter_disj final_pre1 (pre_fmls) in
    (* NEW procedure# Form pre-condition given invariant:  D:=gist Pre given Inv;*)
    (* let final_pre2 = pure_oblg_to_check in  *)(* TODOIMM to remove this line *)
    let final_pre3 = x_add TP.om_gist final_pre2 pre in
    (* let final_pre3 = final_pre2 in (\* TODOIMM to remove this line *\) *)
    (* let final_pre3a = CP.mkAnd final_pre2 pre no_pos in (\* TODOIMM to remove this line *\) *)
    let final_pre3a = CP.mkAnd final_pre3 pre no_pos in
    (* let final_pre4a = TP.pairwisecheck_raw final_pre3 in *)
    let final_pre4b = TP.pairwisecheck_raw final_pre3a in
    let final_pre = x_add TP.om_gist final_pre4b pre in
    (* let final_pre = final_pre4b in (\* TODOIMM to remove this line *\) *)

    let () = x_dinfo_hp (add_str "final_pre0" !CP.print_formula) final_pre0 no_pos in
    let () = x_dinfo_hp (add_str "final_pre1" !CP.print_formula) final_pre1 no_pos in
    let () = x_dinfo_hp (add_str "final_pre2" !CP.print_formula) final_pre2 no_pos in
    let () = x_dinfo_hp (add_str "final_pre3" !CP.print_formula) final_pre3 no_pos in
    let () = x_dinfo_hp (add_str "final_pre3a" !CP.print_formula) final_pre3a no_pos in
    (* let () = x_dinfo_hp (add_str "final_pre4a" !CP.print_formula) final_pre4a no_pos in *)
    let () = x_dinfo_hp (add_str "final_pre4b" !CP.print_formula) final_pre4b no_pos in
    (* let () = x_dinfo_hp (add_str "final_pre" !CP.print_formula) final_pre no_pos in *)
    let checkpoint2 = check_defn pre_rel final_pre pre_rel_df in
    if checkpoint2 then
      List.map (fun (rel,post) -> (rel,post,pre_rel,final_pre)) rel_posts
    else List.map (fun (rel,post) -> (rel,post,pre_rel (* constTrue *),constTrue)) rel_posts (* need to recheck, why constTrue *)
  | [] -> List.map (fun (rel,post) -> (rel,post,constTrue,constTrue)) rel_posts
  | _ -> report_error no_pos "Error in top-down fixpoint calculation"

(*
let pre_calculate fp_func input_fml pre_vars proc_spec
    pre pure_oblg_to_check (rel_posts,pre_rel)
    pre_fmls pre_rel_vars pre_rel_df =
  let pr1 = Cprinter.string_of_pure_formula in
  let pr2 = pr_list_ln pr1 in
  let pr3 = pr_list_ln (pr_pair pr1 pr1) in
  let pr4 = pr_list_ln (pr_quad pr1 pr1 pr1 pr1) in
  Debug.no_7 "pre_calculate" pr3 !CP.print_svl pr1 pr1 (pr_pair pr3 pr1) pr2 (pr_pair !CP.print_svl pr3) pr4
    (fun _ _ _ _ _ _ _ -> pre_calculate fp_func input_fml pre_vars proc_spec
        pre pure_oblg_to_check (rel_posts,pre_rel)  pre_fmls pre_rel_vars pre_rel_df)
    input_fml pre_vars pre pure_oblg_to_check (rel_posts,pre_rel) pre_fmls (pre_rel_vars, pre_rel_df)
*)

(* let pre_calculate fp_func input_fml pre_vars proc_spec *)
(*     pre pure_oblg_to_check (rel_posts,pre_rel) *)
(*     pre_fmls pre_rel_vars pre_rel_df = *)
(*   let pr1 = Cprinter.string_of_pure_formula in *)
(*   let pr2 = pr_list_ln pr1 in *)
(*   let pr3 = pr_list_ln (pr_pair pr1 pr1) in *)
(*   let pr4 = pr_list_ln (pr_quad pr1 pr1 pr1 pr1) in *)
(*   Debug.no_7 "pre_calculate"  *)
(*     (add_str "input_fml" pr3) *)
(*     (add_str "pre_vars" !CP.print_svl) *)
(*     (add_str "pre" pr1) *)
(*     (add_str "pure_oblg_to_check" pr1)  *)
(*     (add_str "(rel_posts,pre_rel)" (pr_pair pr3 pr1)) *)
(*     (add_str "pre_fmls" pr2) *)
(*     (fun _ _ _ _ _ _ _ -> pre_calculate fp_func input_fml pre_vars proc_spec *)
(*         pre pure_oblg_to_check (rel_posts,pre_rel)  pre_fmls pre_rel_vars pre_rel_df) *)
(*     input_fml pre_vars pre pure_oblg_to_check (rel_posts,pre_rel) pre_fmls (pre_rel_vars, pre_rel_df) *)

let pre_calculate fp_func input_fml pre_vars proc_spec
    pre pure_oblg_to_check (rel_posts,pre_rel)
    pre_fmls pre_rel_vars pre_rel_df =
  let pr1 = Cprinter.string_of_pure_formula in
  let pr2 = pr_list_ln pr1 in
  let pr3 = pr_list_ln (pr_pair pr1 pr1) in
  let pr4 = pr_list_ln (pr_quad pr1 pr1 pr1 pr1) in
  Debug.no_7 "pre_calculate" 
    (add_str "input_fml" pr3)
    (add_str "pre_vars" !CP.print_svl)
    (add_str "pre" pr1)
    (add_str "pure_oblg_to_check" pr1) 
    (add_str "(rel_posts,pre_rel)" (pr_pair pr3 pr1))
    (add_str "pre_fmls" pr2)
    (pr_pair (add_str "pre_rel_vars" !CP.print_svl) (add_str "pre_rel_df" pr3)) pr4
    (fun _ _ _ _ _ _ _ -> pre_calculate fp_func input_fml pre_vars proc_spec
        pre pure_oblg_to_check (rel_posts,pre_rel)  pre_fmls pre_rel_vars pre_rel_df)
    input_fml pre_vars pre pure_oblg_to_check (rel_posts,pre_rel) pre_fmls (pre_rel_vars, pre_rel_df)

let update_rel rel pre_rel new_args old_rhs =
  match old_rhs, pre_rel, rel with
  | CP.BForm ((CP.RelForm (name,args,o1),o2),o3), 
    CP.BForm ((CP.RelForm (name1,_,_),_),_),
    CP.BForm ((CP.RelForm (name2,_,_),_),_) ->
    if name=name1 && name=name2 then
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
  let pr = Cprinter.string_of_pure_formula in
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
let pre_rel_fixpoint pre_rel pre_fmls pre_invs fp_func reloblgs pre_vars proc_spec pre_rel_df=
  let constTrue = CP.mkTrue no_pos in
  let pre_inv = CP.disj_of_list pre_invs no_pos in
  (* List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) constTrue pre_invs in *)
  let pre_rel_vars = List.filter (fun x -> not (CP.is_rel_typ x)) (CP.fv pre_rel) in
  let rel_oblg_to_check = List.filter (fun (_,lhs,_) -> CP.equalFormula lhs pre_rel) reloblgs in
  let pure_oblg_to_check =
    List.fold_left (fun p (_,_,rhs) -> CP.mkAnd p rhs no_pos) constTrue rel_oblg_to_check in
  let () = Debug.ninfo_hprint (add_str "oblg to check" !CP.print_formula) pure_oblg_to_check no_pos in
  let pr = Cprinter.string_of_pure_formula in
  let () = Debug.binfo_hprint (add_str "pre_rel_df: " (pr_list (pr_pair pr pr))) pre_rel_df no_pos in
  let checkpoint1 = check_oblg pre_rel constTrue pure_oblg_to_check pre_rel_df in
  if checkpoint1 (* && false *) then [(constTrue,constTrue,pre_rel,constTrue)]
  else
    let input_fml = pre_rel_df in
  (*  let input_fml = compute_td_fml pre_rel_df pre_rel in *)
(*    let () = Debug.binfo_hprint (add_str "input_fml" (pr_list (pr_pair pr pr))) input_fml no_pos in *)
    x_add calculate_gfp fp_func input_fml pre_vars proc_spec
      pre_inv (* constTrue *) pure_oblg_to_check ([constTrue,constTrue],pre_rel) pre_fmls pre_rel_vars pre_rel_df



let pre_rel_fixpoint pre_rel pre_fmls pre_invs fp_func reloblgs pre_vars proc_spec pre_rel_df=
  let pr1 = Cprinter.string_of_pure_formula in
  let pr2 = pr_pair pr1 pr1 in
  let pr3 = CP.print_rel_cat in
  let pr4 = pr_list (pr_quad pr1 pr1 pr1 pr1) in
  Debug.no_5 "pre_rel_fixpoint" pr1 (pr_list pr1) (pr_list (pr_triple pr3 pr1 pr1)) !CP.print_svl (pr_list pr2) pr4
    (fun _ _ _ _ _ -> pre_rel_fixpoint pre_rel pre_fmls pre_invs fp_func reloblgs pre_vars proc_spec pre_rel_df)
    pre_rel pre_fmls reloblgs pre_vars pre_rel_df

let update_with_td_fp bottom_up_fp pre_rel_fmls pre_fmls pre_invs fp_func
    preprocess_fun reloblgs pre_rel_df post_rel_df_new post_rel_df
    pre_vars proc_spec grp_post_rel_flag =
  let pr = Cprinter.string_of_pure_formula in
  let constTrue = CP.mkTrue no_pos in
  let () = Debug.ninfo_pprint ("inside update_with_td") no_pos in
  match bottom_up_fp, pre_rel_fmls with
  | [], [pre_rel] ->
    pre_rel_fixpoint pre_rel (*formula of pre_rel_var*) pre_fmls pre_invs fp_func reloblgs pre_vars proc_spec pre_rel_df
  (*     let rel_oblg_to_check = List.filter (fun (_,lhs,_) -> CP.equalFormula lhs pre_rel) reloblgs in *)
  (*     let pure_oblg_to_check =  *)
  (*       List.fold_left (fun p (_,_,rhs) -> CP.mkAnd p rhs no_pos) constTrue rel_oblg_to_check in *)
  (*     let () = Debug.ninfo_hprint (add_str "oblg to check" !CP.print_formula) pure_oblg_to_check no_pos in *)

  (*     let checkpoint1 = check_oblg pre_rel constTrue pure_oblg_to_check pre_rel_df in *)
  (*     if checkpoint1 then [(constTrue,constTrue,pre_rel,constTrue)] *)
  (*     else  *)
  (* (\*      [(constTrue,constTrue,constTrue,constTrue)]*\) *)
  (*       let input_fml = compute_td_fml pre_rel_df pre_rel in *)
  (*       let () = Debug.ninfo_hprint (add_str "input_fml" (pr_list (pr_pair pr pr))) input_fml no_pos in *)
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
      let () = Debug.ninfo_hprint (add_str "pure pre" !CP.print_formula) pre no_pos in

      let rel_oblg_to_check = List.filter (fun (_,lhs,_) -> CP.equalFormula lhs pre_rel) reloblgs in (* TODOIMM uncomment this line *)
      (* let rel_oblg_to_check = reloblgs in *) (* TODOIMM this is just temp - TO REMOVE *)
      let pure_oblg_to_check =
        List.fold_left (fun p (_,_,rhs) -> CP.mkAnd p rhs no_pos) constTrue rel_oblg_to_check in
      (* let pure_oblg_to_check =  TP.simplify_tp pure_oblg_to_check in (\* TODOIMM this is just temp - TO REMOVE *\) *)
      let () = x_tinfo_hp (add_str "oblg to check" !CP.print_formula) pure_oblg_to_check no_pos in
      let checkpoint1 = check_oblg pre_rel pre pure_oblg_to_check pre_rel_df in
      if checkpoint1 && false then
        let pre = x_add_1 TP.simplify pre in
        let pre = filter_disj pre pre_fmls in
        let pre = TP.pairwisecheck_raw pre in
        let () = x_binfo_hp (add_str "update_with_td_fp pre" !CP.print_formula) pre no_pos in
        List.map (fun (rel,post) -> (rel,post,pre_rel,pre)) rel_posts
      else
        let input_fml = List.map (fun (f1,f2) -> (CP.mkAnd f1 pre no_pos,f2)) post_rel_df_new in
        x_add pre_calculate fp_func input_fml pre_vars proc_spec
            pre pure_oblg_to_check (rel_posts,pre_rel) pre_fmls pre_rel_vars pre_rel_df
  | [(rel,post)],[] ->
    let rels_in_pred = List.filter CP.is_rel_var pre_vars in
    let () = x_tinfo_hp (add_str "rels_in_pred" !print_svl) rels_in_pred no_pos in
    let post_rel_df = List.filter (fun (f1,_) -> CP.intersect (CP.fv f1) rels_in_pred<>[]) post_rel_df in
    (*    let () = x_tinfo_hp (add_str "pre_rel_df(b4 deep split)" (pr_list (pr_pair pr pr))) post_rel_df no_pos in*)
    (*    let new_pre_rel_df = List.concat (List.map (fun (f1,f2) -> deep_split f1 f2) post_rel_df) in*)
    (*    let () = x_tinfo_hp (add_str "pre_rel_df(after deep split)" (pr_list (pr_pair pr pr))) new_pre_rel_df no_pos in*)
    let new_pre_rel_df = List.map (fun (f1,f2) -> (subst_fml rel post f1, subst_fml rel post f2)) post_rel_df in
    let () = x_tinfo_hp (add_str "new_pre_rel_df" (pr_list (pr_pair pr pr))) new_pre_rel_df no_pos in
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
          (* TODO WN : need to use lhs_heap_xpure1 only *)
          let lhs_heap_xpure1 = MCP.mkMTrue no_pos in
          let () = x_binfo_pp "TODO : fix lhs_heap_xpure1" no_pos in
          let _,_,l = x_add Infer.infer_pure_m 3 [] es lhs_heap_xpure1 f1 f1 f1 f2 no_pos in
          List.concat (List.map (fun (_,x,_) -> List.map (fun (a,b,c) -> (c,b)) x) l)
        in lst
        (*      if lst=[] then*)
        (*        let rels_fml = List.filter CP.is_RelForm (CP.list_of_conjs f1_orig) in*)
        (*        [(CP.mkFalse no_pos,List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue rels_fml)]*)
        (*      else lst*)
      ) new_pre_rel_df) in
    let () = x_tinfo_hp (add_str "rel_ass" (pr_list (pr_pair pr pr))) rel_ass no_pos in
    let pairs = preprocess_fun rel_ass in
    let () = x_tinfo_hp (add_str "pairs" (pr_list (pr_pair pr (pr_list pr)))) pairs no_pos in
    (match pairs with
     | [] -> [(rel,post,constTrue,constTrue)]
     | [(r,lst)] ->
       let final_pre = List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) constTrue lst in
       let final_pre = x_add_1 TP.simplify_raw final_pre in
       let final_pre = filter_disj final_pre pre_fmls in
       let final_pre = x_add_1 TP.pairwisecheck_raw final_pre in
       let () = x_dinfo_hp (add_str "final_pre(pred)" !CP.print_formula) final_pre no_pos in
       let checkpoint1 = check_defn r final_pre new_pre_rel_df in
       if checkpoint1 then [(rel,post,r,final_pre)]
       else [(rel,post,constTrue,constTrue)]
     | _ -> [(rel,post,constTrue,constTrue)])
  (*      let checkpoint = check_defn r final_pre pre_rel_df in*)
  (*      if checkpoint then [(rel,post,pre_rel,final_pre)]*)
  (*      else [(rel,post,constTrue,constTrue)])*)
  | _,_ ->
    try
      let () = Debug.ninfo_hprint (add_str "pr_rel_fmls" (pr_list Cprinter.string_of_pure_formula)) pre_rel_fmls no_pos in
      List.map (fun ((p1,p2),pr) -> (p1,p2,pr,constTrue)) (List.combine (List.rev bottom_up_fp) pre_rel_fmls)
    with _ -> List.map (fun (p1,p2) -> (p1,p2,constTrue,constTrue)) bottom_up_fp

let update_with_td_fp bottom_up_fp pre_rel_fmls pre_fmls pre_invs fp_func
    preprocess_fun reloblgs pre_rel_df post_rel_df_new post_rel_df
    pre_vars proc_spec grp_post_rel_flag =
  let pr1 = Cprinter.string_of_pure_formula in
  let pr2 = pr_pair pr1 pr1 in
  let pr2a = pr_list_ln pr2 in
  let pr3 = CP.print_rel_cat in
  let pr3a = pr_list_ln (pr_triple pr3 pr1 pr1) in
  let pr4 = pr_list_ln (pr_quad pr1 pr1 pr1 pr1) in
  Debug.no_7 "update_with_td_fp" (pr_pair pr2a (pr_list_ln pr1)) (pr_pair (pr_list_ln pr1) (pr_list_ln pr1))
    pr3a pr2a pr2a pr2a (pr_pair !CP.print_svl string_of_int) pr4
    (fun _ _ _ _ _ _ _ -> update_with_td_fp bottom_up_fp pre_rel_fmls pre_fmls pre_invs fp_func
        preprocess_fun reloblgs pre_rel_df post_rel_df_new post_rel_df
        pre_vars proc_spec grp_post_rel_flag)
    (bottom_up_fp,pre_rel_fmls) (pre_fmls,pre_invs) reloblgs pre_rel_df post_rel_df_new post_rel_df (pre_vars,grp_post_rel_flag)


let rel_fixpoint_wrapper pre_invs0 pre_fmls0 pre_rel_constrs post_rel_constrs pre_rel_ids post_rels
    proc_spec grp_post_rel_flag =
  (*******************)
  let rec look_up_rel_form obgs rel_var=
    match obgs with
    | [] -> report_error no_pos "SE.process_rel_infer"
    | (lhs,rhs)::rest -> begin
        let rel_args = (CP.get_list_rel_args lhs)@(CP.get_list_rel_args rhs) in
        try
          let _,args = List.find (fun (rel,_) -> CP.eq_spec_var rel rel_var) rel_args in
          args
        with _ -> look_up_rel_form rest rel_var
      end
  in
  let is_post_rel fml pvars =
    let rhs_rel_defn = List.concat (List.map CP.get_rel_id_list (CP.list_of_conjs fml)) in
    List.for_all (fun x -> List.mem x pvars) rhs_rel_defn
  in
  let subs_inv rel_id rel_args inv=
    let ls_relargs = CP.get_list_rel_args inv in
    let ls_relargs1 = List.filter (fun (rel_id1,_) -> CP.eq_spec_var rel_id rel_id1) ls_relargs in
    match ls_relargs1 with
    | [] -> inv
    | [(_,args)] -> let ss = List.combine args rel_args in
      CP.subst ss inv
    | _ -> report_error no_pos "SE.process_rel_infer: multiple pre-rel in lhs, how to handle?"
  in
  let normalize_pre_oblgs args0 rel_var oblgs0=
    let rec_process (rec_oblgs,init_oblgs) args0 lhs rhs=
      let r_rel_args_opt = CP.get_relargs_opt rhs in
      match r_rel_args_opt with
      | Some (r_rel,_) -> begin
          let l_rel_args = CP.get_list_rel_args lhs in
          let sel_l_rel_args = List.filter (fun (rel,_) -> CP.eq_spec_var rel rel_var) l_rel_args in
          match sel_l_rel_args with
          | [] -> rec_oblgs,init_oblgs
          | [(_,args)] ->
            let ss = List.combine args args0 in
            let n_lhs = CP.subst ss lhs in
            let n_rhs = CP.subst ss rhs in
            (rec_oblgs@[(n_lhs,n_rhs)],init_oblgs)
          | _ -> report_error no_pos "SE.process_rel_infer: >=2 rec in gfp is not supported yet"
        end
      | None -> rec_oblgs,init_oblgs
    in
    let rec helper args0 (rec_oblgs,init_oblgs) oblgs=
      match oblgs with
      | [] -> rec_oblgs,init_oblgs
      | (lhs,rhs)::rest -> begin
          let rel_var1_opt =  CP.get_relargs_opt lhs in
          let n_rec_oblgs,n_init_oblgs=
            match rel_var1_opt with
            | Some (rel_var1, args) ->
              if CP.eq_spec_var rel_var rel_var1 then
                let ss = List.combine args args0 in
                let n_lhs = CP.subst ss lhs in
                let n_rhs = CP.subst ss rhs in
                (rec_oblgs,init_oblgs@[(CP.RelAssume [rel_var], n_lhs,n_rhs)])
              else
                rec_process (rec_oblgs,init_oblgs) args0 lhs rhs
            | None ->
              rec_process (rec_oblgs,init_oblgs) args0 lhs rhs
          in
          helper args0 (n_rec_oblgs,n_init_oblgs) rest
        end
    in
    helper args0 ([],[]) oblgs0
  in
  let pre_rel_process rel_name rel_args pre_oblgs=
    let pre_rel = CP.mkRel rel_name (List.map (fun sv -> CP.mkVar sv no_pos) rel_args) no_pos in
    let rec_oblgs,ini_oblgs = normalize_pre_oblgs rel_args rel_name pre_oblgs in
    (pre_rel, rec_oblgs,ini_oblgs)
  in
  (*******************)
  let post_rel_df0 = List.filter (fun (_,x) -> is_post_rel x post_rels) post_rel_constrs in
  (*norm pre-rel*)
  let pre_invs, pre_fmls, pre_rel_fmls,pre_rel_df, reloblgs , pre_vars,post_rel_df  = List.fold_left (fun (pre_invs,pre_fmls,r1,r2,r3,r4,post_rel_df) pre_rel_sv ->
      let args = look_up_rel_form pre_rel_constrs pre_rel_sv in
      let rel_args = (* CP.fresh_spec_vars *) args in
      let pre_invs1 = List.map (subs_inv pre_rel_sv rel_args) pre_invs in
      let pre_fmls1 = List.map (subs_inv pre_rel_sv rel_args) pre_fmls in
      let post_rel_df1 = List.map (fun (lhs,rhs) -> (subs_inv pre_rel_sv rel_args lhs, subs_inv pre_rel_sv rel_args rhs)) post_rel_df in
      let pre_rel,rec_oblgs,ini_oblgs  = pre_rel_process pre_rel_sv rel_args pre_rel_constrs in
      (pre_invs1,pre_fmls1, r1@[pre_rel],r2@rec_oblgs, r3@ini_oblgs ,r4@rel_args, post_rel_df1)
      (* compute_fixpoint_pre_rel pre_rel_sv rel_args pre_rel_constrs proc_spec *)
    ) (pre_invs0,pre_fmls0,[],[],[],[],post_rel_df0) pre_rel_ids in
  (*norm post-rel also*)
  let post_rel_df_new =
    if pre_rel_ids=[] then post_rel_df
    else List.concat (List.map (fun (f1,f2) -> 
        if TP.is_bag_constraint f1 then [(CP.remove_cnts pre_rel_ids f1,f2)]
        else
          let tmp = List.filter (fun x -> CP.intersect 
                                    (CP.get_rel_id_list x) pre_rel_ids=[]) (CP.list_of_conjs f1) in
          if tmp=[] then [] else [(CP.conj_of_list tmp no_pos,f2)]
      ) post_rel_df)
  in
  (*post fix-point*)
  let bottom_up_fp = x_add Fixcalc.compute_fixpoint 3 post_rel_df_new pre_vars proc_spec in
  let bottom_up_fp = List.map (fun (r,p) -> (r,TP.pairwisecheck_raw p)) bottom_up_fp in
  (****pre fixpoint***********)
  let r= x_add update_with_td_fp bottom_up_fp (pre_rel_fmls) pre_fmls pre_invs
      (x_add Fixcalc.compute_fixpoint_td) Fixcalc.fixc_preprocess
      reloblgs pre_rel_df post_rel_df_new post_rel_df (pre_vars@pre_rel_ids) proc_spec grp_post_rel_flag
  in
  r

let rel_fixpoint_wrapper pre_invs0 pre_fmls0 pre_rel_constrs post_rel_constrs pre_rel_ids post_rels proc_spec grp_post_rel_flag =
  let pr = Cprinter.string_of_pure_formula in
  let pr1 = Cprinter.string_of_spec_var in
  Debug.no_7 "rel_fixpoint_wrapper" (pr_list pr) (pr_list pr) (pr_list (pr_pair pr pr)) (pr_list (pr_pair pr pr)) (pr_list pr1) (pr_list pr1) Cprinter.string_of_struc_formula (pr_list (pr_quad pr pr pr pr)) (fun _ _ _ _ _ _ _ -> rel_fixpoint_wrapper pre_invs0 pre_fmls0 pre_rel_constrs post_rel_constrs pre_rel_ids post_rels proc_spec grp_post_rel_flag) pre_invs0 pre_fmls0 pre_rel_constrs post_rel_constrs pre_rel_ids post_rels proc_spec

(*
val Fixpoint.gen_slk_file_4fix: Cast.prog_decl ->
                                string ->
                                CP.spec_var list ->
                                CP.spec_var list ->
                                ('a * CP.formula * CP.formula) list -> unit
*)

(*GEN SLEEK FILE --gsl*)
let gen_slk_file_4fix prog file_name pre_rel_ids post_rel_ids rel_oblgs=
  (************INTERNAL************)
  let to_str_one_constr (_,lhs,rhs)=
    "\nrelAssume \n" ^ (!CP.print_formula lhs) ^ " --> " ^ (!CP.print_formula rhs)
  in
  (***********END**INTERNAL******************)
  let all_rel_vars0, all_data_used0 = List.fold_left (fun (r1,r2) (_,lhs,rhs) ->
      let l_svl = CP.fv lhs in
      let r_svl = CP.fv rhs in
      let ptrs = l_svl@r_svl in
      let ptrs_node_used = List.fold_left (fun r t ->
          match t with
          | Named ot -> if ((String.compare ot "") ==0) then r else r@[ot]
          | _ -> r
        ) [] (List.map CP.type_of_spec_var ptrs) in
      let nr1 = r1@(List.filter (fun sv -> CP.is_rel_typ sv) ptrs) in
      let nr2 = r2@ptrs_node_used in
      (nr1,nr2)
    ) ([],[]) rel_oblgs in
  (*data declare*)
  let all_data_used = Gen.BList.remove_dups_eq (fun s1 s2 -> String.compare s1 s2 = 0) all_data_used0 in
  let all_data_decls = List.fold_left (fun ls data_name ->
      try
        let data_decl = Cast.look_up_data_def no_pos prog.Cast.prog_data_decls data_name in
        ls@[data_decl]
      with _ -> ls
    ) [] all_data_used
  in
  let str_data_decls = List.fold_left (fun s s1 -> s^ s1 ^ ".\n") "" (List.map Cprinter.string_of_data_decl all_data_decls) in
  (*rels decl*)
  let all_rel_vars = CP.remove_dups_svl all_rel_vars0 in
  let all_rel_decls = List.fold_left (fun ls rel_sv ->
      try
        let rel_decl = Cast.look_up_rel_def_raw (prog.Cast.prog_rel_decls # get_stk) (CP.name_of_spec_var rel_sv) in
        ls@[rel_decl]
      with _ -> ls
    ) [] all_rel_vars
  in
  let str_rel_decl = String.concat "\n" (List.map Cprinter.string_of_rel_decl all_rel_decls) in
  (*relational assumptions decl*)
  let str_constrs = List.fold_left (fun s s1 -> s ^ s1 ^ ".\n") "" (List.map to_str_one_constr rel_oblgs) in
  let str_infer_cmd = ("relation_infer ") ^
                      (!CP.print_svl (CP.remove_dups_svl  pre_rel_ids ) )^
                      (!CP.print_svl post_rel_ids) ^"." in
  (*write to file*)
  let out_chn =
    (* TODO : Warning 14: illegal backslash escape in string *)
    let reg = Str.regexp "\.ss" in
    let file_name1 = "logs/gen_" ^ (Str.global_replace reg ".slk" file_name) in
    (* let () = print_endline (file_name1 ^ ".slk") in *)
    let () = print_endline_quiet ("\n generating sleek file : " ^ file_name1) in
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    open_out (file_name1)
  in
  let str_slk = str_data_decls ^ "\n" ^ str_rel_decl ^
                "\n"  ^ str_constrs ^ "\n\n" ^ str_infer_cmd in
  let () = output_string out_chn str_slk in
  let () = close_out out_chn in
  ()
