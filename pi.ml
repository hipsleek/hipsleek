module DD = Debug
open Globals
open Wrapper
open Others
open Stat_global
open Global_var
open Exc.GTable
open Solver
open Cast
open Gen.Basic
open Perm
open Label
module CF = Cformula
module CP = Cpure
module TP = Tpdispatcher
module PTracer = Prooftracer
module I = Iast
module CEQ = Checkeq
module M = Lexer.Make(Token.Token)
module H = Hashtbl
module LO2 = Label_only.Lab2_List

let solve (prog : prog_decl) (scc : proc_decl list) =
  let _ = print_endline "pure inference" in
  let pr = !Cpure.print_formula in
  let proc = List.hd scc in
  let pres,posts_wo_rel,all_posts,inf_vars,pre_fmls,grp_post_rel_flag =
    List.fold_left (fun (pres_acc,posts_wo_rel_acc,all_posts_acc,inf_vars_acc,pre_fmls_acc,grp_post_rel_flag) proc ->
        let pres,posts_wo_rel,all_posts,inf_vars,pre_fmls,grp_post_rel_flag =
          Cformula.get_pre_post_vars [] Cvutil.xpure_heap (proc.proc_static_specs) prog in
        (pres_acc@pres,posts_wo_rel_acc@posts_wo_rel,all_posts_acc@all_posts,inf_vars_acc@inf_vars,pre_fmls_acc@pre_fmls,grp_post_rel_flag)) ([],[],[],[],[],0) scc
  in
  (* let all_posts = Cpure.remove_dups_svl (inf_vars@all_posts) in *)
  let pre_rel_fmls = List.concat (List.map Cformula.get_pre_rels pre_fmls) in
  let pre_rel_fmls = List.filter (fun x -> Cpure.intersect (Cpure.get_rel_id_list x) inf_vars != []) pre_rel_fmls in
  let pre_vars = Cpure.remove_dups_svl (pres @ (List.map
      (fun (t,id) -> Cpure.SpecVar (t,id,Unprimed)) proc.proc_args)) in
  let post_vars_wo_rel = Cpure.remove_dups_svl posts_wo_rel in
  let post_vars = Cpure.remove_dups_svl all_posts in
  let proc_spec = proc.proc_stk_of_static_specs # top in
  let tuples =
    let rels = Infer.infer_rel_stk # get_stk in
    let rels = Gen.Basic.remove_dups rels in
    if rels!=[] then
      begin
        print_endline "\n*************************************";
        print_endline "*******pure relation assumption ******";
        print_endline "*************************************";
        print_endline (Gen.Basic.pr_list_ln (Cpure.string_of_infer_rel) (List.rev rels));
        print_endline "*************************************";
      end;
    let _ = if !Globals.sa_gen_slk then
      try
        let pre_rel_ids = List.filter (fun sv -> Cpure.is_rel_typ sv
            && not(Cpure.mem_svl sv post_vars)) pre_vars in
        let post_rel_ids = List.filter (fun sv -> Cpure.is_rel_typ sv) post_vars in
        Fixpoint.gen_slk_file_4fix prog (List.hd !Globals.source_files)
            pre_rel_ids post_rel_ids rels
      with _ -> ()
    else ()
    in
    let reloblgs, reldefns = List.partition (fun (rt,_,_) -> Cpure.is_rel_assume rt) rels in
    let reldefns = List.map (fun (_,f1,f2) -> (f1,f2)) reldefns in
    let is_post_rel fml pvars =
      let rhs_rel_defn = List.concat (List.map Cpure.get_rel_id_list (Cpure.list_of_conjs fml)) in
      List.for_all (fun x -> List.mem x pvars) rhs_rel_defn
    in
    let _ = Debug.binfo_hprint (add_str "post_vars" !Cpure.print_svl) post_vars no_pos in
    let post_rel_df,pre_rel_df = List.partition (fun (_,x) -> is_post_rel x post_vars) reldefns in
    let pre_rel_ids = List.filter (fun x -> Cpure.is_rel_typ x
        && not(Gen.BList.mem_eq Cpure.eq_spec_var x post_vars)) pre_vars in
    let post_rel_ids = List.filter (fun sv -> Cpure.is_rel_typ sv) post_vars in
    let post_rel_df_new =
      if pre_rel_ids=[] then post_rel_df
      else List.concat (List.map (fun (f1,f2) ->
          if Tpdispatcher.is_bag_constraint f1 then [(Cpure.remove_cnts pre_rel_ids f1,f2)]
          else
            let tmp = List.filter (fun x -> Cpure.intersect
                (Cpure.get_rel_id_list x) pre_rel_ids=[]) (Cpure.list_of_conjs f1) in
            if tmp=[] then [] else [(Cpure.conj_of_list tmp no_pos,f2)]
      ) post_rel_df)
    in
    let pre_invs,post_invs =
      Cformula.get_pre_post_invs pre_rel_ids post_rel_ids (Fixpoint.get_inv prog) (proc.proc_stk_of_static_specs # top) in
    let post_inv = Cpure.join_disjunctions post_invs in
    let bottom_up_fp0 = Fixcalc.compute_fixpoint 2 post_rel_df_new pre_vars proc_spec in
    let bottom_up_fp = List.map (fun (r,p) ->
        let p1 = Tpdispatcher.om_gist p post_inv in
        let p2 = Tpdispatcher.pairwisecheck_raw p1 in
        (r,p2)
    ) bottom_up_fp0 in
    Fixpoint.update_with_td_fp bottom_up_fp pre_rel_fmls pre_fmls pre_invs
        Fixcalc.compute_fixpoint_td
        Fixcalc.fixc_preprocess reloblgs pre_rel_df post_rel_df_new post_rel_df pre_vars proc_spec grp_post_rel_flag;
  in
  let _ = print_endline (string_of_int (List.length tuples)) in
  Infer.fixcalc_rel_stk # push_list tuples;
    if not(Infer.fixcalc_rel_stk # is_empty) then
      begin
        print_endline "\n*************************************";
        print_endline "*******fixcalc of pure relation *******";
        print_endline "*************************************";
        print_endline (Infer.fixcalc_rel_stk # string_of_reverse);
        print_endline "*************************************"
      end;
