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

let init_alias targs=
  CP.EMapSV.mkEmpty

let get_type v svl=
  let orig_sv = List.find (fun sv -> String.compare (CP.name_of_spec_var sv) v = 0) svl in
  CP.type_of_spec_var orig_sv


let case_analysis targs (e0:exp) ctx_p :(CP.formula * CP.EMapSV.emap * (ident * CP.formula) list) list =
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
  let rec helper (e:exp) (path_conds:(CP.formula * CP.EMapSV.emap * (ident * CP.formula) list) list):
        (CP.formula * CP.EMapSV.emap * (ident * CP.formula) list) list=
    match e with
      | Assert _   | Java _
      | CheckRef _ | BConst _
      | Debug _    | Dprint _
      | FConst _   | ICall _
      | IConst _   | New _
      | Null _  | EmptyArray _ (* An Hoa *)
      | Print _ | Barrier _
      | SCall _
      | This _   | Time _
      | Var _   | VarDecl _
      | Unfold _  | Unit _
      | Sharp _  -> path_conds
      | Label b ->  helper b.exp_label_exp path_conds
      | Assign b -> begin (*to update aliasing *)
          let svl = List.fold_left (fun r (p,_,_) -> r@(CP.fv p)) arg_svl path_conds in
          let eqs_opt, sst_cond = collect_aliasing svl e in
          let _ =  Debug.ninfo_hprint (add_str "sst_cond" (pr_list (pr_pair pr_id !CP.print_formula))) sst_cond no_pos in
          let path_conds1 = List.map (fun (p, a, l_sst_cond) -> (p, a, l_sst_cond@sst_cond)) path_conds in
          let pr = pr_list (pr_triple !CP.print_formula pr_none (pr_list (pr_pair pr_id !CP.print_formula))) in
          let _ =  Debug.ninfo_hprint (add_str "path_conds1" pr) path_conds1 no_pos in
          let n_path_conds= match eqs_opt with
            | None -> path_conds1
            | Some ((id,rid), (sst, ass_p)) ->
                  let path_conds2 = List.map (fun (p, aliasing, sst_cond) ->
                      (*kill*)
                      let n_aliasing1 = CP.EMapSV.elim_elems_one aliasing id in
                      (*gen*)
                      let n_aliasing2 = CP.EMapSV.add_equiv n_aliasing1 rid id in
                      let p1 =CP.subst sst p in
                      let p2 = CP.mkAnd p1 ass_p no_pos in
                      (p2, n_aliasing2,sst_cond)
                  ) path_conds1 in
                  path_conds2
          in
          let _ =  Debug.ninfo_hprint (add_str "n_path_conds" pr) n_path_conds no_pos in
	  helper b.exp_assign_rhs n_path_conds
        end
      | Bind b -> helper b.exp_bind_body path_conds
      | Block b -> helper b.exp_block_body path_conds
      | Cond b -> (*to update path condition*)
            let pos = b.exp_cond_pos in
            let pr = pr_list (pr_triple !CP.print_formula pr_none (pr_list (pr_pair pr_id !CP.print_formula))) in
            let _ =  Debug.ninfo_hprint (add_str "path_conds" pr) path_conds no_pos in
            let init_then_paths,init_else_paths = List.fold_left (fun (r1,r2) (p, aliasing, sst_conds) ->
                let n_p_then, n_p_else = try
                  let _ =  Debug.ninfo_hprint (add_str "sst_conds" (pr_list (pr_pair pr_id !CP.print_formula))) sst_conds no_pos in
                  let _,then_cond = List.find (fun (sv,_) -> String.compare sv b.exp_cond_condition ==0) sst_conds in
                  let else_cond =  CP.mkNot then_cond None pos in
                  CP.mkAnd p then_cond pos, CP.mkAnd p else_cond pos
                with _ -> p,p
                in
                (r1@[(n_p_then, aliasing, [])],r2@[(n_p_else, aliasing, [])])
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
  in
  (*init context*)
  let path_conds = helper e0 [(ctx_p,init_alias targs,[])] in
  (*keep args only*)
  List.map (fun (p, emap,c) ->
      let sst = List.fold_left (fun r arg ->
          let eqs = CP.EMapSV.find_equiv_all arg emap in
          r@(List.map (fun sv -> (sv,arg)) eqs)
      ) [] arg_svl in
      CP.remove_redundant (CP.subst sst p)
  ) path_conds


let get_spec_cases_x prog proc e0: (Cpure.formula list) =
  (****************INTERNAL****************)
  (*get all path conditions with context-sensitive*)
  let path_conds =  case_analysis proc.proc_args e0 (CP.mkTrue no_pos) in
  (**************END**INTERNAL****************)
   List.map (fun (a,b,c) -> a) path_conds

let get_spec_cases prog proc e0: (Cpure.formula list) =
  let pr1 = !print_prog_exp in
  let pr2 = pr_list !CP.print_formula in
  Debug.no_1 "get_spec_cases" pr1 pr2
      (fun _ -> get_spec_cases_x prog proc e0) e0
