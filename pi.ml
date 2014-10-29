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

let rec add_relation_to_formula f rel =
  match f with
    | CF.Base b ->
          let h,p,fl,t,a = CF.split_components f in
          let new_p = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix p) rel no_pos) in
          CF.mkBase h new_p t fl a no_pos
    | CF.Or o ->
          let f1 = add_relation_to_formula o.CF.formula_or_f1 rel in
          let f2 = add_relation_to_formula o.CF.formula_or_f2 rel in
          CF.Or { o with
              CF.formula_or_f1 = f1;
              CF.formula_or_f2 = f2 }
    | CF.Exists e ->
          let h,p,fl,t,a = CF.split_components f in
          let new_p = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix p) rel no_pos) in
          (* CF.mkBase h new_p t fl a no_pos *)
          CF.mkExists e.CF.formula_exists_qvars h new_p t fl a no_pos

let add_relation_to_formula f rel =
  let pr = Cprinter.string_of_formula in
  Debug.no_1 "add_relation_to_formula" pr pr (fun _ -> add_relation_to_formula f rel) f

let rec add_post_relation prog proc sf rel_name rel_type rel_vars = match sf with
  | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
        (lbl,add_post_relation prog proc sf rel_name rel_type rel_vars)) el)
  | CF.EBase eb ->
        let cont = eb.CF.formula_struc_continuation in (
            match cont with
              | None -> sf
              | Some cont -> CF.EBase {eb with CF.formula_struc_continuation = Some (add_post_relation prog proc cont rel_name rel_type rel_vars)} )
  | CF.EAssume ea ->
        (* let rel_vars = (List.map (fun (t,id) -> CP.mk_typed_spec_var t id) proc.proc_args)@[CP.mk_typed_spec_var proc.proc_return res_name] in *)
        let rel_formula = CP.mkTrue no_pos in
        let rel_decl = {rel_name = rel_name; rel_vars = rel_vars; rel_formula = rel_formula} in
        let _ = prog.prog_rel_decls <- prog.prog_rel_decls@[rel_decl] in
        let rel_spec_var = CP.mk_typed_spec_var rel_type rel_name in
        (* let rel_args = (List.map (fun (_,id) -> CP.mkVar (CP.mk_spec_var id) no_pos) proc.proc_args)@[CP.mkVar (CP.mk_spec_var res_name) no_pos] in *)
        let rel_args = List.map (fun sv -> CP.mkVar sv no_pos) rel_vars in
        let new_rel = CP.mkRel rel_spec_var rel_args no_pos in
        let old_f = ea.CF.formula_assume_simpl in
        let new_f = add_relation_to_formula old_f new_rel in
        let new_struc_f = CF.mkEBase new_f None no_pos in
        CF.EAssume {ea with
            CF.formula_assume_simpl = new_f;
            CF.formula_assume_struc = new_struc_f}
  | CF.EInfer ei ->
        let rel_name = fresh_any_name "post" in
        let fvs = CF.struc_all_vars sf in
        let _ = DD.ninfo_hprint (add_str "vars" Cprinter.string_of_typed_spec_var_list) fvs no_pos in
        let proc_args = List.map (fun (t,id) -> CP.mk_typed_spec_var t id) (proc.proc_args@[(proc.proc_return,res_name)]) in
        let proc_primed_args = List.map (fun sv -> match sv with
          | CP.SpecVar (t,id,_) -> CP.SpecVar (t,id,Primed)) proc.proc_by_name_params in
        let rel_vars = List.filter (fun sv -> match sv with
          | CP.SpecVar (t,_,_) -> t = Int) (fvs@proc_args@proc_primed_args) in
        let rel_vars = CP.remove_dups_svl rel_vars in
        let rel_vars = if ei.CF.formula_inf_obj # is_add_flow then rel_vars@[CP.mk_typed_spec_var Int "flow"] else rel_vars in
        let _ = DD.ninfo_hprint (add_str "rel_args" Cprinter.string_of_typed_spec_var_list) rel_vars no_pos in
        let rel_type = RelT (List.map (fun sv -> match sv with
          | CP.SpecVar (t,_,_) -> t) rel_vars) in
        let new_cont = add_post_relation prog proc ei.CF.formula_inf_continuation rel_name rel_type rel_vars in
        let new_infer_vars = List.filter (fun sv -> CP.is_rel_var sv) (CF.struc_fv new_cont) in
        CF.EInfer { ei with
            (* CF.formula_inf_vars = CP.remove_dups_svl (ei.CF.formula_inf_vars@[CP.mk_typed_spec_var rel_type rel_name]); *)
            (* CF.formula_inf_continuation = add_post_relation prog proc ei.CF.formula_inf_continuation rel_name rel_type rel_vars} *)
            CF.formula_inf_vars = CP.remove_dups_svl (ei.CF.formula_inf_vars@new_infer_vars);
            CF.formula_inf_continuation = new_cont}
  | CF.ECase ec -> CF.ECase { ec with
        CF.formula_case_branches = List.map (fun (pf,sf) ->
            let rel_name = fresh_any_name rel_name in
            (pf,add_post_relation prog proc sf rel_name rel_type rel_vars)
        ) ec.CF.formula_case_branches
    }

let add_post_relation prog proc sf =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "add_post_relation" pr pr (fun _ -> add_post_relation prog proc sf "" UNK []) sf

let rec add_pre_relation prog proc sf rel_name rel_type rel_vars = match sf with
  | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
        (lbl,add_pre_relation prog proc sf rel_name rel_type rel_vars)) el)
  | CF.EBase eb ->
        let rel_formula = CP.mkTrue no_pos in
        let rel_decl = {rel_name = rel_name; rel_vars = rel_vars; rel_formula = rel_formula} in
        let _ = prog.prog_rel_decls <- prog.prog_rel_decls@[rel_decl] in
        let rel_spec_var = CP.mk_typed_spec_var rel_type rel_name in
        let rel_args = List.map (fun sv -> CP.mkVar sv no_pos) rel_vars in
        let new_rel = CP.mkRel rel_spec_var rel_args no_pos in
        CF.EBase {eb with
            CF.formula_struc_base = add_relation_to_formula eb.CF.formula_struc_base new_rel}
  | CF.EAssume ea -> sf
  | CF.EInfer ei ->
        let rel_name = fresh_any_name "pre" in
        let fvs = CF.struc_all_vars_except_post sf in
        let _ = DD.ninfo_hprint (add_str "vars" Cprinter.string_of_typed_spec_var_list) fvs no_pos in
        let proc_args = List.map (fun (t,id) -> CP.mk_typed_spec_var t id) proc.proc_args in
        let proc_primed_args = List.map (fun sv -> match sv with
          | CP.SpecVar (t,id,_) -> CP.SpecVar (t,id,Primed)) proc.proc_by_name_params in
        let rel_vars = List.filter (fun sv -> match sv with
          | CP.SpecVar (t,_,_) -> t = Int) (fvs@proc_args@proc_primed_args) in
        let rel_vars = CP.remove_dups_svl rel_vars in
        let _ = DD.ninfo_hprint (add_str "rel_args" Cprinter.string_of_typed_spec_var_list) rel_vars no_pos in
        let rel_type = RelT (List.map (fun sv -> match sv with
          | CP.SpecVar (t,_,_) -> t) rel_vars) in
        let new_cont = add_pre_relation prog proc ei.CF.formula_inf_continuation rel_name rel_type rel_vars in
        let new_infer_vars = List.filter (fun sv -> CP.is_rel_var sv) (CF.struc_fv new_cont) in
        CF.EInfer {ei with
            (* CF.formula_inf_vars = CP.remove_dups_svl (ei.CF.formula_inf_vars@[CP.mk_typed_spec_var rel_type rel_name]); *)
            (* CF.formula_inf_continuation = add_pre_relation prog proc ei.CF.formula_inf_continuation rel_name rel_type rel_vars} *)
            CF.formula_inf_vars = CP.remove_dups_svl (ei.CF.formula_inf_vars@new_infer_vars);
            CF.formula_inf_continuation = new_cont}
  | CF.ECase ec -> CF.ECase { ec with
        CF.formula_case_branches = List.map (fun (pf,sf) ->
            let rel_name = fresh_any_name rel_name in
            (pf,add_pre_relation prog proc sf rel_name rel_type rel_vars)
        ) ec.CF.formula_case_branches
    }

let add_pre_relation prog proc sf =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "add_pre_relation" pr pr (fun _ -> add_pre_relation prog proc sf "" UNK []) sf

let rec is_need_to_add_post_rel sf = match sf with
  | CF.EList el -> List.exists (fun (lbl,sf) ->
        is_need_to_add_post_rel sf) el
  | CF.EInfer ei ->
        let inf_obj = ei.CF.formula_inf_obj in
        let inf_vars = ei.CF.formula_inf_vars in
        (inf_obj # is_post)
  | _ -> false

let rec is_infer_shape sf = match sf with
  | CF.EList el -> List.exists (fun (lbl,sf) ->
        is_infer_shape sf) el
  | CF.EInfer ei ->
        let inf_obj = ei.CF.formula_inf_obj in
        let inf_vars = ei.CF.formula_inf_vars in
        (inf_obj # is_shape) || (List.length (List.filter (fun sv -> Cpure.is_hprel_typ sv) inf_vars) > 0)
  | _ -> false

let is_infer_shape sf =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "is_infer_shape" pr string_of_bool is_infer_shape sf

let is_infer_shape_scc scc =
  List.exists (fun proc -> is_infer_shape (proc.proc_stk_of_static_specs # top)) scc

let rec is_infer_post sf = match sf with
  | CF.EList el -> List.exists (fun (lbl,sf) ->
        is_infer_post sf) el
  | CF.EInfer ei ->
        let inf_obj = ei.CF.formula_inf_obj in
        let inf_vars = ei.CF.formula_inf_vars in
        (inf_obj # is_post) || (List.length (List.filter (fun sv -> (Cpure.is_rel_typ sv)) inf_vars) > 0)
  | _ -> false

let is_infer_post sf =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "is_infer_post" pr string_of_bool is_infer_post sf

let is_infer_post_scc scc =
  List.exists (fun proc -> is_infer_post (proc.proc_stk_of_static_specs # top)) scc

let rec is_infer_pre sf = match sf with
  | CF.EList el -> List.exists (fun (lbl,sf) ->
        is_infer_post sf) el
  | CF.EInfer ei ->
        let inf_obj = ei.CF.formula_inf_obj in
        let inf_vars = ei.CF.formula_inf_vars in
        (inf_obj # is_pre)
  | _ -> false

let is_infer_pre sf =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "is_infer_pre" pr string_of_bool is_infer_pre sf

let is_infer_pre_scc scc =
  List.exists (fun proc -> is_infer_pre (proc.proc_stk_of_static_specs # top)) scc

let rec is_infer_others sf = match sf with
  | CF.EList el -> List.exists (fun (lbl,sf) ->
        is_infer_post sf) el
  | CF.EInfer ei ->
        let inf_obj = ei.CF.formula_inf_obj in
        let inf_vars = ei.CF.formula_inf_vars in
        (inf_obj # is_term) (* || (inf_obj # is_shape) || (inf_obj # is_imm) *)
  | _ -> false

let is_infer_others sf =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "is_infer_others" pr string_of_bool is_infer_others sf

let is_infer_others_scc scc =
  List.exists (fun proc -> is_infer_others (proc.proc_stk_of_static_specs # top)) scc

let rec modify_infer_vars sf infer_vars = match sf with
  | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
        (lbl,modify_infer_vars sf infer_vars)) el)
  | CF.EBase eb ->
        let cont = eb.CF.formula_struc_continuation in (
            match cont with
              | None -> sf
              | Some cont -> CF.EBase {eb with CF.formula_struc_continuation = Some (modify_infer_vars cont infer_vars)} )
  | CF.EAssume ea ->
        sf
  | CF.EInfer ei ->
        CF.EInfer {ei with
            CF.formula_inf_vars = CP.remove_dups_svl (ei.CF.formula_inf_vars@infer_vars)}
  | CF.ECase ec -> CF.ECase { ec with
        CF.formula_case_branches = List.map (fun (pf,sf) ->
            (pf,modify_infer_vars sf infer_vars)
        ) ec.CF.formula_case_branches
    }

let add_post_relation_scc prog scc =
  let _ = List.iter (fun proc ->
      let spec = proc.proc_stk_of_static_specs # top in
      let _ = if is_need_to_add_post_rel spec then
        let new_spec = add_post_relation prog proc spec in
        proc.proc_stk_of_static_specs # push new_spec
      in ()
  ) scc in
  let _ = if List.length scc > 1 then
    let infer_vars = List.fold_left (fun acc proc ->
        let spec = proc.proc_stk_of_static_specs # top in
        acc@(CF.struc_infer_relation spec)
    ) [] scc in
    List.iter (fun proc ->
        let spec = proc.proc_stk_of_static_specs # top in
        let new_spec = modify_infer_vars spec infer_vars in
        proc.proc_stk_of_static_specs # push new_spec
    ) scc
  in ()

let add_pre_relation_scc prog scc =
  let _ = List.iter (fun proc ->
      let spec = proc.proc_stk_of_static_specs # top in
      let new_spec = add_pre_relation prog proc spec in
      proc.proc_stk_of_static_specs # push new_spec
  ) scc in
  let _ = if List.length scc > 1 then
    let infer_vars = List.fold_left (fun acc proc ->
        let spec = proc.proc_stk_of_static_specs # top in
        acc@(CF.struc_infer_relation spec)
    ) [] scc in
    List.iter (fun proc ->
        let spec = proc.proc_stk_of_static_specs # top in
        let new_spec = modify_infer_vars spec infer_vars in
        proc.proc_stk_of_static_specs # push new_spec
    ) scc
  in ()

(* let rec is_infer_post prog proc sf = match sf with *)
(*   | CF.EList el -> CF.EList (List.map (fun (lbl,sf) -> *)
(*         (lbl,is_infer_post prog proc sf)) el) *)
(*   | CF.EInfer ei -> *)
(*         let inf_obj = ei.CF.formula_inf_obj in *)
(*         if (inf_obj # is_post) then *)
(*           let rel_name = fresh_any_name "post" in *)
(*           let rel_type = RelT ((List.map (fun (t,_) -> t) proc.proc_args)@[proc.proc_return]) in *)
(*           CF.EInfer {ei with *)
(*               CF.formula_inf_vars = ei.CF.formula_inf_vars@[CP.mk_typed_spec_var rel_type rel_name]; *)
(*               CF.formula_inf_continuation = add_relation prog proc ei.CF.formula_inf_continuation rel_name rel_type} *)
(*         else *)
(*           sf *)
(*   | _ -> sf *)

let rec turn_off_infer_pure spec old_spec =
    match (spec,old_spec) with
    | (CF.EList el1,CF.EList el2) -> CF.EList (List.map (fun ((lbl,sf1),(_,sf2)) ->
          (lbl,turn_off_infer_pure sf1 sf2)) (List.combine el1 el2))
    (* | (CF.EBase eb1,CF.EBase eb2) -> *)
    (*       let cont1 = eb1.CF.formula_struc_continuation in *)
    (*       let cont2 = eb2.CF.formula_struc_continuation in ( *)
    (*           match (cont1,cont2) with *)
    (*             | (None,_) -> spec *)
    (*             | (Some cont1,Some cont2) -> CF.EBase {eb1 with CF.formula_struc_continuation = Some (turn_off_infer_pure cont1 cont2)} *)
    (*             | _ -> failwith "turn off infer pure ebase" ) *)
    (* | (CF.EAssume ea,_) -> spec *)
    (* | (CF.EInfer ei1,CF.EInfer ei2) -> *)
    (*       let old_inf_obj = ei2.CF.formula_inf_obj # clone in *)
    (*       let _ = old_inf_obj # reset INF_POST in *)
    (*       let _ = old_inf_obj # reset INF_PRE in *)
    (*       CF.EInfer {ei1 with *)
    (*           CF.formula_inf_obj = old_inf_obj; *)
    (*           CF.formula_inf_vars = []} *)
    (* | (CF.ECase ec1,CF.ECase ec2) -> CF.ECase { ec1 with *)
    (*     CF.formula_case_branches = List.map (fun ((pf,sf1),(_,sf2)) -> *)
    (*         (pf,turn_off_infer_pure sf1 sf2) *)
    (*     ) (List.combine ec1.CF.formula_case_branches ec2.CF.formula_case_branches) *)
    (*   } *)
    | (_,CF.EInfer ei) ->
          let old_inf_obj = ei.CF.formula_inf_obj # clone in
          let _ = old_inf_obj # reset INF_POST in
          let _ = old_inf_obj # reset INF_PRE in
          let _ = old_inf_obj # reset INF_SHAPE in
          CF.EInfer {ei with
              CF.formula_inf_obj = old_inf_obj;
              CF.formula_inf_vars = [];
              CF.formula_inf_continuation = spec}
    | _ -> spec (* failwith "turn off infer pure other" *)

let resume_infer_obj_proc proc old_spec =
  let spec = turn_off_infer_pure (proc.proc_stk_of_static_specs # top) old_spec in
  let _ = DD.ninfo_hprint (add_str "spec" Cprinter.string_of_struc_formula) spec no_pos in
  let _ = proc.proc_stk_of_static_specs # push spec in
  proc

let resume_infer_obj_scc scc old_specs =
  let tmp = List.combine scc old_specs in
  List.map (fun (proc,old_spec) -> resume_infer_obj_proc proc old_spec) tmp

let rec filter_infer_pure_struc_formula sf =
  match sf with
    | CF.EList el -> CF.EList (List.map (fun (lbl,sf) ->
          (lbl,filter_infer_pure_struc_formula sf)) el)
    | CF.EBase eb ->
          let cont = eb.CF.formula_struc_continuation in (
              match cont with
                | None -> sf
                | Some cont -> CF.EBase {eb with CF.formula_struc_continuation = Some (filter_infer_pure_struc_formula cont)} )
    | CF.EAssume ea -> sf
    | CF.EInfer ei ->
          let inf_obj = ei.CF.formula_inf_obj in
          let new_inf_obj = inf_obj # clone in
          let _ = new_inf_obj # reset INF_TERM in
          let _ = new_inf_obj # reset INF_IMM in
          let _ = new_inf_obj # reset INF_SHAPE in
          CF.EInfer {ei with
              CF.formula_inf_obj = new_inf_obj}
    | CF.ECase ec -> CF.ECase { ec with
        CF.formula_case_branches = List.map (fun (pf,sf) ->
            (pf,filter_infer_pure_struc_formula sf)
        ) ec.CF.formula_case_branches
      }

let filter_infer_pure_proc proc =
  let spec = proc.proc_stk_of_static_specs # top in
  let _ = DD.ninfo_hprint (add_str "spec" Cprinter.string_of_struc_formula) spec no_pos in
  let new_spec = filter_infer_pure_struc_formula spec in
  let _ = proc.proc_stk_of_static_specs # push new_spec in
  let _ = DD.ninfo_hprint (add_str "spec" Cprinter.string_of_struc_formula) spec no_pos in
  let _ = DD.ninfo_hprint (add_str "new_spec" Cprinter.string_of_struc_formula) new_spec no_pos in
  (proc,spec)

let filter_infer_pure_scc scc =
  List.map (fun proc -> filter_infer_pure_proc proc) scc

let is_post_rel fml pvars =
  let _ = Debug.ninfo_hprint (add_str "fml" Cprinter.string_of_pure_formula) fml no_pos in
  let rhs_rel_defn = List.concat (List.map CP.get_rel_id_list (CP.list_of_conjs fml)) in
  let _ = Debug.ninfo_hprint (add_str "rhs_rel_defn" (pr_list Cprinter.string_of_typed_spec_var)) rhs_rel_defn no_pos in
  let _ = Debug.ninfo_hprint (add_str "pvars" (pr_list Cprinter.string_of_typed_spec_var)) pvars no_pos in
  List.for_all (fun x -> List.mem x pvars) rhs_rel_defn

let is_infer_flow reldefns =
  List.exists (fun (cat,_,_) ->
      match cat with
        | CP.RelDefn(_,Some _) -> true
        | _ -> false
  ) reldefns

let add_flow reldefns =
  List.map (fun (cat,f1,f2) ->
      let (f1,f2) = (CP.add_flow_var f1,CP.add_flow_var f2) in
      match cat with
        | CP.RelDefn(_,Some s) ->
              let s = try
                let idx = String.index s '#' in
                String.sub s 0 idx
              with _ -> s
              in
              let nf = exlist # get_hash s in
              let is_top = exlist # is_top_flow nf in
              if is_top then (f1,f2) (* top flow *)
              else                   (* other flow *)
                let (s,b) = exlist # get_min_max nf in
                (CP.add_flow_interval f1 s b,f2)
        | _ ->                       (* norm flow *)
              (* let (s,b) = exlist # get_min_max !norm_flow_int in *)
              (f1,f2)
  ) reldefns

let infer_pure (prog : prog_decl) (scc : proc_decl list) =
  let proc_specs = List.fold_left (fun acc proc -> acc@[CF.simplify_ann (proc.proc_stk_of_static_specs # top)]) [] scc in
  let _ = DD.binfo_hprint (add_str "proc_specs" (pr_list Cprinter.string_of_struc_formula)) proc_specs no_pos in
  let rels = Infer.infer_rel_stk # get_stk in
  let (rels,rest) = (List.partition (fun (a1,a2,a3) -> match a1 with | CP.RelDefn _ -> true | _ -> false) rels) in
  let (lst_assume,lst_rank) = (List.partition (fun (a1,a2,a3) -> match a1 with | CP.RelAssume _ -> true | _ -> false) rest) in
  let lst_assume = Gen.Basic.remove_dups lst_assume in
  if rels = [] then ()
  else
    let new_specs =
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
            let rels = List.filter (fun (_,pf,_) -> not(CP.is_False pf)) rels in
            if rels !=[] then
              begin
                print_endline "\n*************************************";
                print_endline "******pure relation assumption*******";
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
            let is_infer_flow = is_infer_flow reldefns in
            let reldefns = if is_infer_flow then add_flow reldefns else List.map (fun (_,f1,f2) -> (f1,f2)) reldefns in
            (* let reldefns = List.map (fun (_,f1,f2) -> (f1,f2)) reldefns in *)
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
                Fixcalc.fixc_preprocess reloblgs pre_rel_df post_rel_df_new post_rel_df pre_vars proc_spec grp_post_rel_flag
          in
          Infer.fixcalc_rel_stk # push_list tuples;
          if not(Infer.fixcalc_rel_stk # is_empty || !Globals.print_min) then
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
              Debug.binfo_zprint (lazy (("REL POST : "^Cprinter.string_of_pure_formula rel_post))) no_pos;
              Debug.binfo_zprint (lazy (("POST: "^Cprinter.string_of_pure_formula post))) no_pos;
              Debug.binfo_zprint (lazy (("REL PRE : "^Cprinter.string_of_pure_formula rel_pre))) no_pos;
              Debug.binfo_zprint (lazy (("PRE : "^Cprinter.string_of_pure_formula pre))) no_pos
          ) tuples in
          let triples = List.map (fun (a,b,c,d) -> (a,b,d)) tuples in
          let new_specs = if triples = [] then
            List.map (fun old_spec -> fst (Fixpoint.simplify_relation old_spec None
                pre_vars post_vars_wo_rel prog true (* inf_post_flag *) evars lst_assume)) proc_specs
          else
            let new_specs1 = List.map (fun proc_spec -> CF.transform_spec proc_spec (CF.list_of_posts proc_spec)) proc_specs in
            List.map (fun new_spec1 -> fst (Fixpoint.simplify_relation new_spec1
                (Some triples) pre_vars post_vars_wo_rel prog true (* inf_post_flag *) evars lst_assume)) new_specs1
          in new_specs
        end
      with ex ->
          begin
            Debug.info_pprint "PROBLEM with fix-point calculation" no_pos;
            raise ex
          end
    in
    (* let new_specs = List.map (fun new_spec -> CF.norm_struc_with_lexvar new_spec false) new_specs in *)
    let new_specs = List.map (fun new_spec -> CF.flatten_struc_formula new_spec) new_specs in
    let new_specs = List.map (fun new_spec -> CF.trans_flow new_spec) new_specs in
    let _ = List.iter (fun (proc,new_spec) ->
        let _ = proc.proc_stk_of_static_specs # push new_spec in
        print_endline "\nPost Inference result:";
        print_endline proc.proc_name;
        print_endline (Cprinter.string_of_struc_formula_for_spec new_spec);
    ) (List.combine scc new_specs) in
    ()

