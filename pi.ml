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

let rec add_relation prog proc sf rel_name rel_type = match sf with
  | CF.EBase eb ->
        let cont = eb.CF.formula_struc_continuation in (
            match cont with
              | None -> sf
              | Some cont -> CF.EBase {eb with CF.formula_struc_continuation = Some (add_relation prog proc cont rel_name rel_type)} )
  | CF.EAssume ea ->
        let rel_vars = (List.map (fun (t,id) -> CP.mk_typed_spec_var t id) proc.proc_args)@[CP.mk_typed_spec_var proc.proc_return res_name] in
        let rel_formula = CP.mkTrue no_pos in
        let rel_decl = {rel_name = rel_name; rel_vars = rel_vars; rel_formula = rel_formula} in
        let _ = prog.prog_rel_decls <- prog.prog_rel_decls@[rel_decl] in
        let rel_spec_var = CP.mk_typed_spec_var rel_type rel_name in
        let rel_args = (List.map (fun (_,id) -> CP.mkVar (CP.mk_spec_var id) no_pos) proc.proc_args)@[CP.mkVar (CP.mk_spec_var res_name) no_pos] in
        let new_rel = CP.mkRel rel_spec_var rel_args no_pos in
        let old_f = ea.CF.formula_assume_simpl in
        let h,p,fl,t,a = CF.split_components old_f in
        let new_p = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix p) new_rel no_pos) in
        let new_f = CF.mkBase h new_p t fl a no_pos in
        let new_struc_f = CF.mkEBase new_f None no_pos in
        CF.EAssume {ea with
            CF.formula_assume_simpl = new_f;
            CF.formula_assume_struc = new_struc_f}
  | _ -> sf

let rec is_infer_post prog proc sf = match sf with
  | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
        (lbl,is_infer_post prog proc sf)) el)
  | CF.EInfer ei ->
        let inf_obj = ei.CF.formula_inf_obj in
        if (inf_obj # is_post) then
          let rel_name = fresh_any_name "post" in
          let rel_type = RelT ((List.map (fun (t,_) -> t) proc.proc_args)@[proc.proc_return]) in
          CF.EInfer {ei with
              CF.formula_inf_vars = ei.CF.formula_inf_vars@[CP.mk_typed_spec_var rel_type rel_name];
              CF.formula_inf_continuation = add_relation prog proc ei.CF.formula_inf_continuation rel_name rel_type}
        else sf
  | _ -> sf

let solve (prog : prog_decl) (scc : proc_decl list) =
  let pr = !CP.print_formula in
  let proc_specs = List.fold_left (fun acc proc -> acc@[CF.simplify_ann (proc.proc_stk_of_static_specs # top)]) [] scc in
  let rels = Infer.infer_rel_stk # get_stk in
  let (rels,rest) = (List.partition (fun (a1,a2,a3) -> match a1 with | CP.RelDefn _ -> true | _ -> false) rels) in
  let (lst_assume,lst_rank) = (List.partition (fun (a1,a2,a3) -> match a1 with | CP.RelAssume _ -> true | _ -> false) rest) in
  let new_specs = if rels = [] then proc_specs
  else
    let rels = Infer.infer_rel_stk # get_stk in
    let _ = Infer.infer_rel_stk # reset in
    let pres,posts_wo_rel,all_posts,inf_vars,pre_fmls,grp_post_rel_flag =
      List.fold_left (fun (pres_acc,posts_wo_rel_acc,all_posts_acc,inf_vars_acc,pre_fmls_acc,grp_post_rel_flag) proc ->
          let pres,posts_wo_rel,all_posts,inf_vars,pre_fmls,grp_post_rel_flag =
            CF.get_pre_post_vars [] Cvutil.xpure_heap (proc.proc_stk_of_static_specs # top) prog in
          (pres_acc@pres,posts_wo_rel_acc@posts_wo_rel,all_posts_acc@all_posts,inf_vars_acc@inf_vars,pre_fmls_acc@pre_fmls,grp_post_rel_flag)) ([],[],[],[],[],0) scc
    in
    let pre_rel_fmls = List.concat (List.map CF.get_pre_rels pre_fmls) in
    let pre_rel_fmls = List.filter (fun x -> CP.intersect (CP.get_rel_id_list x) inf_vars != []) pre_rel_fmls in
    let pre_vars = CP.remove_dups_svl (List.fold_left (fun pres proc ->
        pres @ (List.map (fun (t,id) -> CP.SpecVar (t,id,Unprimed)) proc.proc_args)) pres scc) in
    let post_vars_wo_rel = CP.remove_dups_svl posts_wo_rel in
    let post_vars = CP.remove_dups_svl all_posts in
    try
      begin
        let _ = DD.ninfo_pprint ">>>>>> do_compute_fixpoint <<<<<<" no_pos in
        let tuples =
          let rels = Gen.Basic.remove_dups rels in
          if rels!=[] then
            begin
              print_endline "\n*************************************";
              print_endline "*******pure relation assumption ******";
              print_endline "*************************************";
              print_endline (Gen.Basic.pr_list_ln (CP.string_of_infer_rel) (List.rev rels));
              print_endline "*************************************";
            end;
          let _ = if !Globals.sa_gen_slk then
            try
              let pre_rel_ids = List.filter (fun sv -> CP.is_rel_typ sv
                  && not(CP.mem_svl sv post_vars)) pre_vars in
              let post_rel_ids = List.filter (fun sv -> CP.is_rel_typ sv) post_vars in
              Fixpoint.gen_slk_file_4fix prog (List.hd !Globals.source_files)
                  pre_rel_ids post_rel_ids rels
            with _ -> ()
          else ()
          in
          let reloblgs, reldefns = List.partition (fun (rt,_,_) -> CP.is_rel_assume rt) rels in
          let reldefns = List.map (fun (_,f1,f2) -> (f1,f2)) reldefns in
          let is_post_rel fml pvars =
            let rhs_rel_defn = List.concat (List.map CP.get_rel_id_list (CP.list_of_conjs fml)) in
            List.for_all (fun x -> List.mem x pvars) rhs_rel_defn
          in
          let post_rel_df,pre_rel_df = List.partition (fun (_,x) -> is_post_rel x post_vars) reldefns in
          let pre_rel_ids = List.filter (fun x -> CP.is_rel_typ x
              && not(Gen.BList.mem_eq CP.eq_spec_var x post_vars)) pre_vars in
          let post_rel_ids = List.filter (fun sv -> CP.is_rel_typ sv) post_vars in
          let post_rel_df_new =
            if pre_rel_ids=[] then post_rel_df
            else List.concat (List.map (fun (f1,f2) ->
                if Tpdispatcher.is_bag_constraint f1 then [(CP.remove_cnts pre_rel_ids f1,f2)]
                else
                  let tmp = List.filter (fun x -> CP.intersect
                      (CP.get_rel_id_list x) pre_rel_ids=[]) (CP.list_of_conjs f1) in
                  if tmp=[] then [] else [(CP.conj_of_list tmp no_pos,f2)]
            ) post_rel_df)
          in
          let proc = List.hd scc in
          let pre_invs,post_invs =
            List.fold_left (fun (pre_invs,post_invs) proc ->
                let new_pre_invs,new_post_invs =
                  CF.get_pre_post_invs pre_rel_ids post_rel_ids (Fixpoint.get_inv prog) (proc.proc_stk_of_static_specs # top) in
                (pre_invs@new_pre_invs,post_invs@new_post_invs)
            ) ([],[]) scc
          in
          let post_inv = CP.join_disjunctions post_invs in
          let bottom_up_fp0 = Fixcalc.compute_fixpoint 2 post_rel_df_new pre_vars (List.hd proc_specs) in
          (* let bottom_up_fp0 = List.fold_left (fun acc proc_spec -> acc@(Fixcalc.compute_fixpoint 2 post_rel_df_new pre_vars proc_spec)) [] proc_specs in *)
          let bottom_up_fp = List.map (fun (r,p) ->
              let p1 = Tpdispatcher.om_gist p post_inv in
              let p2 = Tpdispatcher.pairwisecheck_raw p1 in
              (r,p2)
          ) bottom_up_fp0 in
          let proc_spec = List.hd proc_specs in
          Fixpoint.update_with_td_fp bottom_up_fp pre_rel_fmls pre_fmls pre_invs
              Fixcalc.compute_fixpoint_td
              Fixcalc.fixc_preprocess reloblgs pre_rel_df post_rel_df_new post_rel_df pre_vars proc_spec grp_post_rel_flag;
        in
        Infer.fixcalc_rel_stk # push_list tuples;
        if not(Infer.fixcalc_rel_stk # is_empty) then
          begin
            print_endline "\n*************************************";
            print_endline "*******fixcalc of pure relation *******";
            print_endline "*************************************";
            print_endline (Infer.fixcalc_rel_stk # string_of_reverse);
            print_endline "*************************************"
          end;
        Infer.fixcalc_rel_stk # reset;
        let tuples = List.map (fun (rel_post,post,rel_pre,pre) ->
            let pre_new = if CP.isConstTrue rel_pre then
              let exist_vars = CP.diff_svl (CP.fv_wo_rel rel_post) inf_vars in
              TP.simplify_exists_raw exist_vars post
            else pre in
            (rel_post,post,rel_pre,pre_new)) tuples in
        let evars = stk_evars # get_stk in
        let _ = List.iter (fun (rel_post,post,rel_pre,pre) ->
            Debug.ninfo_zprint (lazy (("REL POST : "^Cprinter.string_of_pure_formula rel_post))) no_pos;
            Debug.ninfo_zprint (lazy (("POST: "^Cprinter.string_of_pure_formula post))) no_pos;
            Debug.ninfo_zprint (lazy (("REL PRE : "^Cprinter.string_of_pure_formula rel_pre))) no_pos;
            Debug.ninfo_zprint (lazy (("PRE : "^Cprinter.string_of_pure_formula pre))) no_pos
        ) tuples in
        let triples = List.map (fun (a,b,c,d) -> (a,b,d)) tuples in
        if triples = [] then
          List.map (fun old_spec -> fst (Fixpoint.simplify_relation old_spec None
              pre_vars post_vars_wo_rel prog true (* inf_post_flag *) evars lst_assume)) proc_specs
        else
          let new_specs1 = List.map (fun proc_spec -> CF.transform_spec proc_spec (CF.list_of_posts proc_spec)) proc_specs in
          List.map (fun new_spec1 -> fst (Fixpoint.simplify_relation new_spec1
              (Some triples) pre_vars post_vars_wo_rel prog true (* inf_post_flag *) evars lst_assume)
          ) new_specs1
      end
    with ex ->
        begin
          Debug.info_pprint "PROBLEM with fix-point calculation" no_pos;
          raise ex
        end
  in
  (* let new_specs = List.map (fun new_spec -> CF.norm_struc_with_lexvar new_spec false) new_specs in *)
  let new_specs = List.map (fun new_spec -> CF.flatten_struc_formula new_spec) new_specs in
  let _ = List.iter (fun (proc,new_spec) ->
      let _ = proc.proc_stk_of_static_specs # push new_spec in
      print_endline "\nPost Inference result:";
      print_endline proc.proc_name;
      print_endline (Cprinter.string_of_struc_formula_for_spec new_spec);
  ) (List.combine scc new_specs) in
  ()
