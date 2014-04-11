(*
 This module performs data analysis
*)

open Globals
open Gen.Basic

open Cast

module CP=Cpure

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
          let _ =  Debug.ninfo_hprint (add_str "t1" string_of_typ) t no_pos in
          let _ =  Debug.ninfo_hprint (add_str "rhs" !print_prog_exp) rhs no_pos in
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
                          let _ =  Debug.ninfo_hprint (add_str "st" string_of_typ) st no_pos in
                          if st==Bool then
                            match cargs with
                              | [sv] ->begin (*2*)
                                  try
                                    let t = get_type sv svl in
                                    let _ =  Debug.ninfo_hprint (add_str "t2" string_of_typ) t no_pos in
                                    let _ =  Debug.ninfo_hprint (add_str "mn" pr_id) mn no_pos in
                                    if (String.compare mn ("is_null___$"^(string_of_typ t)) ==0) then
                                      let p = CP.mkNull ( CP.SpecVar (t, sv, Unprimed)) pos in
                                      let _ =  Debug.ninfo_hprint (add_str "id" pr_id) id no_pos in
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
      | Sharp _  -> path_conds
      | Label b ->  helper b.exp_label_exp path_conds
      | Assign b -> begin (*to update aliasing *)
          let svl = List.fold_left (fun r pc -> r@(CP.fv pc.sp_constr)) arg_svl path_conds in
          let eqs_opt, sst_cond = collect_aliasing svl e in
          let _ =  Debug.ninfo_hprint (add_str "sst_cond" (pr_list (pr_pair pr_id !CP.print_formula))) sst_cond no_pos in
          let path_conds1 = List.map (fun pc -> {pc with sp_tobe_cond = pc.sp_tobe_cond@sst_cond}) path_conds in
          let _ =  Debug.ninfo_hprint (add_str "path_conds1" (pr_list print_sympath)) path_conds1 no_pos in
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
          let _ =  Debug.ninfo_hprint (add_str "n_path_conds" (pr_list print_sympath)) n_path_conds no_pos in
	  helper b.exp_assign_rhs n_path_conds
        end
      | Bind b -> helper b.exp_bind_body path_conds
      | Block b -> helper b.exp_block_body path_conds
      | Cond b -> (*to update path condition*)
            let pos = b.exp_cond_pos in
            let _ =  Debug.ninfo_hprint (add_str "path_conds" (pr_list print_sympath)) path_conds no_pos in
            let init_then_paths,init_else_paths = List.fold_left (fun (r1,r2) pc ->
                let n_p_then, n_p_else = try
                  let _ =  Debug.ninfo_hprint (add_str "sst_conds" (pr_list (pr_pair pr_id !CP.print_formula))) pc.sp_tobe_cond no_pos in
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
            let _ =  Debug.ninfo_hprint (add_str "cur_procn" pr_id) proc.Cast.proc_name no_pos in
             let _ =  Debug.ninfo_hprint (add_str "mn" pr_id) mn no_pos in
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
              let _ =  Debug.info_hprint (add_str "path_conds1" (pr_list print_sympath) ) path_conds1 no_pos in
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
   List.map (fun sp -> sp.sp_constr) path_conds

let get_spec_cases prog proc e0: (Cpure.formula list) =
  let pr1 = !print_prog_exp in
  let pr2 = pr_list !CP.print_formula in
  Debug.no_1 "get_spec_cases" pr1 pr2
      (fun _ -> get_spec_cases_x prog proc e0) e0
