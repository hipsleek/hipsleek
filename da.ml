#include "xdebug.cppo"
open VarGen
(*
 This module performs data analysis
*)

open Globals
open Gen.Basic

open Cast

module CF= Cformula

module CP=Cpure


let string_cmp s1 s2= String.compare s1 s2 =0
(*
find distinct case spec
*)

type sympath = {
    sp_id: int list;
    sp_constr: CP.formula;
    sp_alias: CP.EMapSV.emap;
    sp_tobe_cond: (ident * CP.formula) list;
    sp_rec_context: CP.formula option;
}

let print_sympath sp=
  ((pr_list string_of_int) sp.sp_id) ^
      "\n" ^ (!CP.print_formula sp.sp_constr) ^
      "\n" ^ (CP.string_of_var_eset sp.sp_alias) ^
      "\n" ^ ((pr_list (pr_pair pr_id !CP.print_formula)) sp.sp_tobe_cond)^
      "\n" ^ ((pr_option !CP.print_formula) sp.sp_rec_context)

let init_alias targs=
  CP.EMapSV.mkEmpty

let get_type v svl=
  let orig_sv = List.find (fun sv -> String.compare (CP.name_of_spec_var sv) v = 0) svl in
  CP.type_of_spec_var orig_sv


let case_analysis_x proc targs (e0:exp) ctx_p :sympath list =
  let arg_svl = List.map (fun (t, id) -> CP.SpecVar (t, id, Unprimed)) targs in
  let rec collect_aliasing svl e=
    match e with
      | Assign {exp_assign_lhs = id;
        exp_assign_rhs = rhs;
        exp_assign_pos = pos;
        } -> begin
          let t0 = Gen.unsome (type_of_exp rhs) in
          let t = if is_null_type t0 then
            try
               get_type id svl
            with _ -> t0
          else t0
          in
          let () =  Debug.ninfo_hprint (add_str "t1" string_of_typ) t no_pos in
          let () =  Debug.ninfo_hprint (add_str "rhs" !print_prog_exp) rhs no_pos in
          match rhs with
             | Var {exp_var_name = rid} ->
                   let vsv = CP.SpecVar (t, id, Unprimed) in (* rhs must be non-void *)
                   let tmp_vsv = CP.fresh_spec_var vsv in
                   let sst = [(vsv, tmp_vsv)] in
                   let rvsv = CP.SpecVar (t, rid, Unprimed) in
                   (Some ((vsv,rvsv),(sst, CP.mkEqVar vsv rvsv pos)), [])
             | Block {exp_block_body = sc} -> begin
                 (* match seq with *)
                 (*   | Seq {exp_seq_exp2 = sc} -> begin *)
                 match sc with
                   |  SCall {exp_scall_type=st;
                      exp_scall_method_name = mn;
                      exp_scall_arguments = cargs;
                      } -> begin (*1*)
                        try
                          let () =  Debug.ninfo_hprint (add_str "st" string_of_typ) st no_pos in
                          if st==Bool then
                            match cargs with
                              | [sv] ->begin (*2*)
                                  try
                                    let t = get_type sv svl in
                                    let () =  Debug.ninfo_hprint (add_str "t2" string_of_typ) t no_pos in
                                    let () =  Debug.ninfo_hprint (add_str "mn" pr_id) mn no_pos in
                                    if (String.compare mn ("is_null___$"^(string_of_typ t)) ==0) then
                                      let p = CP.mkNull ( CP.SpecVar (t, sv, Unprimed)) pos in
                                      let () =  Debug.ninfo_hprint (add_str "id" pr_id) id no_pos in
                                      (None , [(id, p)])
                                    else if (String.compare mn ("is_not_null___$"^(string_of_typ t)) ==0) then
                                      let p = CP.mkNeqNull ( CP.SpecVar (t, sv, Unprimed)) pos in
                                      (None, [(id, p)])
                                    else (None, [])
                                  with _ -> (None,[])
                                end (*2*)
                              | _ -> (None,[])
                          else (None,[])
                        with _ -> (None,[])
                      end (*1*)
                   | _ -> (None, [])
               end
            (*  | _ -> None,[] *)
        (* end *)
             | _ -> None,[]
        end
      | _ -> None,[]
  in
  let args = List.map snd targs in
  (***************************************************************)
  (***************************************************************)
  let rec helper (e:exp) (path_conds:sympath list):sympath list=
    match e with
      | Assert _   | Java _
      | CheckRef _ | BConst _
      | Debug _    | Dprint _
      | FConst _   | ICall _
      | IConst _   | New _
      | Null _  | EmptyArray _ (* An Hoa *)
      | Print _ | Barrier _
      | This _   | Time _
      | Var _   | VarDecl _
      | Unfold _  | Unit _
      | Par _
      | Sharp _  -> path_conds
      | Label b ->  helper b.exp_label_exp path_conds
      | Assign b -> begin (*to update aliasing *)
          let svl = List.fold_left (fun r pc -> r@(CP.fv pc.sp_constr)) arg_svl path_conds in
          let eqs_opt, sst_cond = collect_aliasing svl e in
          let () =  Debug.ninfo_hprint (add_str "sst_cond" (pr_list (pr_pair pr_id !CP.print_formula))) sst_cond no_pos in
          let path_conds1 = List.map (fun pc -> {pc with sp_tobe_cond = pc.sp_tobe_cond@sst_cond}) path_conds in
          let () =  Debug.ninfo_hprint (add_str "path_conds1" (pr_list print_sympath)) path_conds1 no_pos in
          let n_path_conds= match eqs_opt with
            | None -> path_conds1
            | Some ((lsv,rsv), (sst, ass_p)) ->
                  let path_conds2 = List.map (fun pc ->
                      (*kill*)
                      let n_aliasing1 = CP.EMapSV.elim_elems_one pc.sp_alias lsv in
                      (*gen*)
                      let n_aliasing2 = CP.EMapSV.add_equiv n_aliasing1 rsv lsv in
                      let p1 =CP.subst sst pc.sp_constr in
                      let p2 = CP.mkAnd p1 ass_p no_pos in
                      {pc with sp_constr = p2; sp_alias= n_aliasing2}
                  ) path_conds1 in
                  path_conds2
          in
          let () =  Debug.ninfo_hprint (add_str "n_path_conds" (pr_list print_sympath)) n_path_conds no_pos in
	  helper b.exp_assign_rhs n_path_conds
        end
      | Bind b -> helper b.exp_bind_body path_conds
      | Block b -> helper b.exp_block_body path_conds
      | Cond b -> (*to update path condition*)
            let pos = b.exp_cond_pos in
            let () =  Debug.ninfo_hprint (add_str "path_conds" (pr_list print_sympath)) path_conds no_pos in
            let init_then_paths,init_else_paths = List.fold_left (fun (r1,r2) pc ->
                let n_p_then, n_p_else = try
                  let () =  Debug.ninfo_hprint (add_str "sst_conds" (pr_list (pr_pair pr_id !CP.print_formula))) pc.sp_tobe_cond no_pos in
                  let _,then_cond = List.find (fun (sv,_) -> String.compare sv b.exp_cond_condition ==0) pc.sp_tobe_cond in
                  let else_cond =  CP.mkNot then_cond None pos in
                  CP.mkAnd pc.sp_constr then_cond pos, CP.mkAnd pc.sp_constr else_cond pos
                with _ -> pc.sp_constr,pc.sp_constr
                in
                let then_pc= {pc with sp_id = 1::pc.sp_id;
                    sp_constr = n_p_then;
                    sp_tobe_cond = [];
                } in
                let else_pc= {pc with sp_id = 2::pc.sp_id;
                    sp_constr = n_p_else;
                    sp_tobe_cond = [];
                } in
                (r1@[then_pc],r2@[else_pc])
            ) ([],[]) path_conds in
	    let then_path = helper b.exp_cond_then_arm init_then_paths in
            (*else path*)
            let else_path = helper b.exp_cond_else_arm  init_else_paths in
            then_path@else_path
      | Cast b -> helper b.exp_cast_body path_conds
      | Catch b -> helper b.exp_catch_body path_conds
      | Seq b ->
	    let res1 = helper b.exp_seq_exp1 path_conds in
	    helper b.exp_seq_exp2 res1
      | While b ->
	    helper b.exp_while_body path_conds
      | Try b ->
            let res1 = helper b.exp_try_body path_conds in
            helper b.exp_catch_clause res1
      | SCall {exp_scall_type=st;
        exp_scall_method_name = mn;
        exp_scall_arguments = args;
        } ->
            let () =  Debug.ninfo_hprint (add_str "cur_procn" pr_id) proc.Cast.proc_name no_pos in
             let () =  Debug.ninfo_hprint (add_str "mn" pr_id) mn no_pos in
            if String.compare proc.Cast.proc_name mn !=0 then
              path_conds
            else
              let svl = List.fold_left (fun r pc -> r@(CP.fv pc.sp_constr)) arg_svl path_conds in
              let larg_svl = List.fold_left (fun r sv ->
                  try
                    let t = get_type sv svl in
                    let n_sv = CP.SpecVar (t, sv, Unprimed) in
                    r@[n_sv]
                  with _ -> r
              ) [] args in
              let path_conds1 = if larg_svl=[] then
                let ptrue = CP.mkTrue no_pos in
                List.map (fun pc -> {pc with sp_rec_context = Some ptrue}) path_conds
              else
                List.map (fun pc ->
                    let rec_ctx = CP.filter_var pc.sp_constr larg_svl in
                    let rec_ctx1 = try
                      (*fresh cur arguments*)
                      let fr_arg_svl = CP.fresh_spec_vars arg_svl in
                      let sst0 = List.combine arg_svl fr_arg_svl in
                      let rec_ctxa = CP.subst sst0 rec_ctx in
                      (*subst callee args by current args*)
                      let sst1 = List.combine larg_svl arg_svl in
                      CP.subst sst1 rec_ctxa
                    with _ -> rec_ctx
                    in
                    {pc with sp_rec_context = Some rec_ctx1}) path_conds
              in
              let () =  Debug.ninfo_hprint (add_str "path_conds1" (pr_list print_sympath) ) path_conds1 no_pos in
              path_conds1
  in
  (***************************************************************)
  let rec context_sen_case_analysis e pcs=
    let path_conds = helper e pcs in
    (*keep args only*)
    let r_pcs = List.map (fun pc ->
        let sst = List.fold_left (fun r arg ->
            let eqs = CP.EMapSV.find_equiv_all arg pc.sp_alias in
            r@(List.map (fun sv -> (sv,arg)) eqs)
        ) [] arg_svl in
        {pc with sp_constr = CP.remove_redundant (CP.subst sst pc.sp_constr)}
    ) path_conds
    in
    (*classify path conds: rec (poss terminated, nonterminated), not rec*)
    let ter_rec_pcs,nter_rec_pcs, nrec_pcs = List.fold_left (fun (ter_rec, nter_rec, nrec) pc ->
        match pc.sp_rec_context with
          | None -> (ter_rec, nter_rec, nrec@[pc])
          | Some p -> if CP.isConstTrue p then (ter_rec, nter_rec@[pc], nrec)
            else (ter_rec@[pc], nter_rec, nrec)
    ) ([],[],[]) r_pcs in
    if nter_rec_pcs = [] then
      (*to do context sensitive here to combine paths*)
      r_pcs
    else []
  in
  (***************************************************************)
  (***************************************************************)
  (*init context*)
  let ini_pc = { sp_id = [0];
  sp_constr = ctx_p;
  sp_alias = init_alias targs;
  sp_tobe_cond = [];
  sp_rec_context = None;
  } in
  let path_conds = context_sen_case_analysis e0 [ini_pc] in
  path_conds

let case_analysis proc targs (e0:exp) ctx_p :sympath list =
  let pr1 = !print_prog_exp in
  let pr2 = pr_list_ln print_sympath in
  Debug.no_2 "case_analysis" pr1 !CP.print_formula pr2
      (fun _ _ -> case_analysis_x proc targs e0 ctx_p) e0 ctx_p

let get_spec_cases_x prog proc e0: (Cpure.formula list) =
  (****************INTERNAL****************)
  (*get all path conditions with context-sensitive*)
  let path_conds =  case_analysis proc proc.proc_args e0 (CP.mkTrue no_pos) in
  (**************END**INTERNAL****************)
  List.filter (fun p -> not (CP.isConstTrue p))
      (CP.remove_redundant_helper (List.map (fun sp -> sp.sp_constr) path_conds) [])

let get_spec_cases prog proc e0: (Cpure.formula list) =
  let pr1 = !print_prog_exp in
  let pr2 = pr_list !CP.print_formula in
  Debug.no_1 "get_spec_cases" pr1 pr2
      (fun _ -> get_spec_cases_x prog proc e0) e0

(***************************************************************)
(***************************************************************)

let find_rel_args_groups_x prog proc e0=
  (****************************INTERNAL****************************)
    (********************************************************)
  (********************************************************)
  let rec lookup_sv_from_id id svl=
    match svl with
      | [] -> raise Not_found
      | sv::rest -> if string_cmp (CP.name_of_spec_var sv) id then sv else
          lookup_sv_from_id id rest
  in
  let rec find_must_neq_helper (e:exp) (neqs:(ident*ident) list):(ident*ident) list=
    match e with
      | Assert _   | Java _
      | CheckRef _ | BConst _
      | Debug _    | Dprint _
      | FConst _   | ICall _
      | IConst _   | New _
      | Null _  | EmptyArray _ (* An Hoa *)
      | Print _ | Barrier _
      | This _   | Time _
      | Var _   | VarDecl _
      | Unfold _  | Unit _
      | Par _
      | Sharp _  -> neqs
      | Label b ->  find_must_neq_helper b.exp_label_exp neqs
      | Assign b -> (*to handle alias*) neqs
      | Bind  {exp_bind_bound_var = (_,id);
        exp_bind_body = b;
        exp_bind_read_only = is_read;
        } -> begin
          match b with
            | Assign {exp_assign_lhs = id2;
              exp_assign_rhs = rhs;
              exp_assign_pos = pos;
              } -> begin
                match rhs with
                  | Var {exp_var_name = rid} ->
                        neqs@[(id,rid)]
                  | _ -> neqs
              end
            | _ -> neqs
        end
      | Block b -> find_must_neq_helper b.exp_block_body neqs
      | Cond b -> (*to update neqs*)
            let pos = b.exp_cond_pos in
            let () =  Debug.ninfo_hprint (add_str "neqs" (pr_list (pr_pair pr_id pr_id))) neqs no_pos in
            let then_eqs = find_must_neq_helper b.exp_cond_then_arm neqs in
            (*else path*)
            let else_eqs = find_must_neq_helper b.exp_cond_else_arm neqs in
            Gen.BList.remove_dups_eq (fun (s11,s12) (s21, s22) ->
                (string_cmp s11 s21 && string_cmp s12 s22) ||
                    (string_cmp s11 s22 && string_cmp s12 s21)
            ) (then_eqs@else_eqs)
      | Cast b -> find_must_neq_helper b.exp_cast_body neqs
      | Catch b -> find_must_neq_helper b.exp_catch_body neqs
      | Seq b ->
	    let res1 = find_must_neq_helper b.exp_seq_exp1 neqs in
	    find_must_neq_helper b.exp_seq_exp2 res1
      | While b ->
	    find_must_neq_helper b.exp_while_body neqs
      | Try b ->
            let res1 = find_must_neq_helper b.exp_try_body neqs in
            let res2 = find_must_neq_helper b.exp_catch_clause neqs in
            res1@res2
      | SCall {exp_scall_type=st;
        exp_scall_method_name = mn;
        exp_scall_arguments = args;
        } ->
            let () =  Debug.ninfo_hprint (add_str "SCall neqs" (pr_list (pr_pair pr_id pr_id))) neqs no_pos in
            neqs
  in
  let rec split_args svl split non_split neqs=
    match svl with
      | [] -> (split, non_split)
      | sv::rest ->
            let sv_neqs = List.fold_left (fun r (id1,id2) ->
                let id = CP.name_of_spec_var sv in
                if string_cmp id id1 then r@[id2] else
                  if string_cmp id id2 then r@[id1] else r
            ) [] neqs in
            let rem_ids = List.map CP.name_of_spec_var (rest@non_split) in
            if Gen.BList.difference_eq string_cmp rem_ids sv_neqs = [] then
              split_args rest (split@[sv]) non_split neqs
            else split_args rest split (non_split@[sv]) neqs
  in
  (**************END**INTERNAL****************)
  (********************************************************)
  (********************************************************)
  let maybe_root_args, id_ni_args = List.partition (fun (_, inst) -> inst = I) proc.Cast.proc_args_wi in
  let () =  Debug.ninfo_hprint (add_str "maybe_root_args" (pr_list (fun (id,_) -> pr_id id)))
    maybe_root_args no_pos in
  let () =  Debug.ninfo_hprint (add_str "proc.Cast.proc_is_recursive" string_of_bool)
    proc.Cast.proc_is_recursive no_pos in
  if not (proc.Cast.proc_is_recursive && List.length maybe_root_args > 1) then
    false,[]
  else
    (*look up unknown preds in pre-condition => separation *)
    let pre_unk_hpargs = CF.get_hp_rel_pre_struc_formula proc.Cast.proc_static_specs in
    if List.length pre_unk_hpargs >= 1 then
      let arg_groups = List.map snd pre_unk_hpargs in
      let grouped_args = List.fold_left (@) [] arg_groups in
      let id_grouped_args = List.map CP.name_of_spec_var grouped_args in
      let rem = List.filter (fun (sv,_) -> not (Gen.BList.mem_eq  string_cmp sv id_grouped_args)) maybe_root_args in
      (* if rem = [] then *)
        try
          let () =  Debug.ninfo_hprint (add_str "arg_groups" (pr_list !CP.print_svl))
            arg_groups no_pos in
          let ni_args = List.map (fun (id,_) ->
              lookup_sv_from_id id grouped_args
          ) id_ni_args in
          (* analysize the source code to find x = y.next ==> x # y*)
          let neqs = find_must_neq_helper e0 [] in
          let () =  Debug.ninfo_hprint (add_str "neqs" (pr_list (pr_pair pr_id pr_id)))
            neqs no_pos in
          let args_split_conf = List.fold_left (fun r (hp,svl) ->
              if List.length svl <= 1 then r else
                (*split at arg that diff all rem*)
                let svl_i, svl_ni = List.partition (fun sv -> not (CP.mem_svl sv ni_args)) svl in
                let split_args, rem_i = split_args svl_i [] [] neqs in
                if split_args = [] then r else
                  (* let rem_i, rem_ni = List.partition (fun sv -> not (CP.mem_svl sv ni_args)) rem in *)
                  let n_rels = List.map (fun sv -> ([sv], svl_ni)) split_args in
                  let splits = if rem_i = [] then n_rels else ((rem_i, svl_ni)::n_rels) in
                  r@[((hp,svl), splits)]
          ) [] pre_unk_hpargs in
          if args_split_conf = [] then false,[] else
            true,args_split_conf
        with _ -> false,[]
      (* else false,[] *)
    else false,[]


(*
 - partition parameters into relevant groups.
 - now only focus on
    + NOT (must eq)

out: list of need to split unknown preds
 ((pred_name, pred args), ((args inst, args noninst) list) list
*)
let find_rel_args_groups prog proc e0 =
  let pr1 = !print_prog_exp in
  let pr2 = pr_list (pr_pair (pr_pair !CP.print_sv !CP.print_svl)
      (pr_list (pr_pair !CP.print_svl !CP.print_svl))) in
  Debug.no_1 "find_rel_args_groups" pr1 (pr_pair string_of_bool pr2)
      (fun _ -> find_rel_args_groups_x prog proc e0) e0


let find_rel_args_groups_scc prog scc0 =
  (*************************************************)
  (*************************************************)
  let process_split ((hp,args), ls_sep_args)=
    let ls_inst_args = List.map (fun (i_args, ni_args) ->
        (List.map (fun sv -> (sv,I)) i_args)@(List.map (fun sv -> (sv,NI)) ni_args)) ls_sep_args in
    let n_hf, n_hps = List.fold_left (fun (hf, r) args ->
        let nhf, nhp = Cast.add_raw_hp_rel prog true false args no_pos in
        (CF.mkStarH hf nhf no_pos, r@[nhp])
    ) (CF.HEmp,[]) ls_inst_args in
    let f = CF.formula_of_heap n_hf no_pos in
    (*form the def for hp*)
    let hf = CF.HRel (hp, List.map (fun v -> CP.mkVar v no_pos) args, no_pos) in
    let def = {CF.hprel_def_kind = CP.HPRelDefn (hp, List.hd args, List.tl args);
      CF.hprel_def_hrel = hf;
      CF.hprel_def_guard = None;
      CF.hprel_def_body = [([], Some f, None)];
      CF.hprel_def_body_lib = [];
      CF.hprel_def_flow = None;
    }
    in
    (hp, def, n_hf,n_hps)
  in
  let rec update_spec drop_hps add_hps sf=
    let recf = update_spec drop_hps add_hps in
     match sf with
       | CF.EInfer b ->
             (* let () =  Debug.info_hprint (add_str "EInfer" pr_id) "EInfer" no_pos in *)
             CF.EInfer {b with CF.formula_inf_vars =
                     add_hps@(CP.diff_svl b.CF.formula_inf_vars drop_hps);
                 CF.formula_inf_continuation = CF.struc_formula_drop_infer drop_hps b.CF.formula_inf_continuation;
             }
       | CF.EList l-> (* let () =  Debug.info_hprint (add_str "EList" pr_id) "EList" no_pos in *)
          CF.EList (Gen.map_l_snd recf l)
       | _ -> sf
  in
  (*************************************************)
  (*************************************************)
  let process_scc scc=
    match scc with
      | [proc] -> begin
          match proc.Cast.proc_body with
            | Some p -> begin
                  let b,splits = find_rel_args_groups prog proc p in
                  if b then
                    (*generate new unk preds*)
                    let splitted_hps, defs, n_hfs, n_hps = List.fold_left (fun (r1,r2,r3, r4) split ->
                        let hp, def, hf, n_hps =  process_split split in
                        (r1@[hp], r2@[def], r3@[hf], r4@n_hps)
                    ) ([],[],[],[]) splits in
                    let sspec1 = proc.Cast.proc_static_specs in
                    let () =  Debug.ninfo_hprint (add_str "sspec1" (Cprinter.string_of_struc_formula)) sspec1 no_pos in
                    let sspec2 = update_spec  splitted_hps n_hps sspec1 in
                    let nf =  CF.formula_of_heap (CF.join_star_conjunctions n_hfs) no_pos in
                    let sspec3 = CF.mkAnd_pre_struc_formula sspec2 nf in
                    let stk = proc.proc_stk_of_static_specs in
                    let _ = stk # pop in
                    let _ = stk # push sspec3 in
                    let n_proc = {proc with Cast.proc_static_specs = sspec3;
                        Cast.proc_stk_of_static_specs = stk;
                    } in
                    let  ()=  Debug.ninfo_hprint (add_str "sspec3" (Cprinter.string_of_struc_formula)) sspec3 no_pos in
                    (* let _ = List.iter (fun hp_def -> CF.rel_def_stk # push hp_def) defs in *)
                    let bug = Cast.update_sspec_proc prog.Cast.new_proc_decls proc.Cast.proc_name sspec3 in
                    [n_proc],defs
                  else [proc],[]
              end
            | _ -> [proc],[]
        end
      | _ -> scc,[]
  in
  process_scc scc0
  (* List.map process_scc sccs *)
(*	r1@[nscc],r2@defs *)
(*	) ([],[]) sccs *)
