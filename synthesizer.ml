#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure

open Synthesis

module CA = Cast
module IA = Iast
module CF = Cformula
module CP = Cpure
module SB = Songbird

(*********************************************************************
 * Data structures and exceptions
 *********************************************************************)

exception EStree of synthesis_tree

let raise_stree st = raise (EStree st)
(*********************************************************************
 * Choosing rules
 *********************************************************************)

let rec find_sub_var sv cur_vars pre_pf =
  match pre_pf with
  | CP.BForm (b, _) ->
    let bvars = CP.bfv b in
    if List.exists (fun x -> CP.eq_spec_var x sv) bvars then
      let (pf, _) = b in
      (match pf with
       | Eq (e1, e2, _) ->
         begin
           match e1, e2 with
           | Var (sv1, _), Var (sv2, _) ->
             if CP.eq_spec_var sv1 sv
             && List.exists (fun x -> CP.eq_spec_var x sv2) cur_vars
             then Some sv2
             else if CP.eq_spec_var sv2 sv
                  && List.exists (fun x -> CP.eq_spec_var x sv1) cur_vars
             then Some sv1
             else None
           | _ -> None
         end
       | _ -> None
      )
    else None
  | CP.And (f1, f2, _) ->
    let res1 = find_sub_var sv cur_vars f1 in
    if res1 = None then find_sub_var sv cur_vars f2
        else res1
  | _ -> None

(* implement simple rules first *)
(* {x -> enode{a} * y -> node{b}}{x -> node{y} * y -> node{b}} --> x.next = b *)
let rec find_eq_var var (formula:CP.formula) = match formula with
  | CP.BForm (bf, _) -> let pf, _ = bf in
    begin
      match pf with
      | CP.Eq (e1, e2, _) ->
        let eq_e1 = match e1 with
         | CP.Var (sv,_) -> if CP.eq_sv sv var then [e2] else []
         | _ -> [] in
        let eq_e2 = match e2 with
         | CP.Var (sv,_) -> if CP.eq_sv sv var then [e1] else []
         | _ -> [] in
        eq_e1@eq_e2
      | _ -> []
    end
  | CP.Or (f1, f2, _,_)
  | CP.And (f1, f2, _) -> (find_eq_var var f1) @ (find_eq_var var f2)
  | CP.AndList list ->
    list |> List.map snd |> List.map (find_eq_var var) |> List.concat
  | Not (f, _, _)   | Forall (_, f, _, _)
  | Exists (_, f,_,_) -> find_eq_var var f

let choose_rassign_pure_x var goal : rule list =
  let pre_vars = goal.gl_pre_cond |> CF.fv in
  if CP.mem var pre_vars then []
  else
    let varf = extract_var_f goal.gl_post_cond var in
    match varf with
    | None -> []
    | Some var_f -> if CF.is_emp_formula var_f then
        let pf = CF.get_pure var_f in
        let eq_vars = find_eq_var var pf in
        if List.length eq_vars = 1 then
          let rhs = List.hd eq_vars in
          let rhs_vars = CP.afv rhs in
          if CP.subset rhs_vars goal.gl_vars then
            let rule = RlAssign {
                ra_lhs = var;
                ra_rhs = rhs;
              } in [rule]
          else []
        else []
      else []

let choose_rassign_pure var goal =
  Debug.no_2 "choose_rassign_pure" pr_var pr_goal pr_rules
    (fun _ _ -> choose_rassign_pure_x var goal) var goal

let find_equal_var_x goal var =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let all_vars = CF.fv pre |> List.filter is_node_var in
  let pf1, pf2 = CF.get_pure pre, CF.get_pure post in
  let ante = CP.mkAnd pf1 pf2 no_pos |> remove_exists_vars_pf in
  let () = x_tinfo_hp (add_str "ante" pr_pf) ante no_pos in
  let helper_pure var1 var2 =
    let conseq = CP.mkEqVar var1 var2 no_pos in
    let () = x_tinfo_hp (add_str "conseq" pr_pf) conseq no_pos in
    SB.check_pure_entail ante conseq in
  let helper f1 f2 = match f1, f2 with
    | CF.Exists bf1, CF.Base bf2 ->
      let hf1 = bf1.CF.formula_exists_heap in
      let hf2 = bf2.CF.formula_base_heap in
      begin
        match hf1, hf2 with
        | CF.ViewNode vnode1, CF.ViewNode vnode2 ->
          let args1 = vnode1.CF.h_formula_view_arguments in
          let args2 = vnode2.CF.h_formula_view_arguments in
          List.exists2 (fun x y -> helper_pure x y) args1 args2
        | _ -> false
      end
    | _ -> false in
  let compare_two_vars_x var1 var2 =
    let var1_f = extract_var_f post var1 in
    let var2_f = extract_var_f pre var2 in
    match var1_f, var2_f with
    | Some f1, Some f2 ->
      let () = x_tinfo_hp (add_str "var1" pr_var) var1 no_pos in
      let () = x_tinfo_hp (add_str "var2" pr_var) var2 no_pos in
      let () = x_tinfo_hp (add_str "eq-v f1" pr_formula) f1 no_pos in
      let () = x_tinfo_hp (add_str "eq-v f2" pr_formula) f2 no_pos in
      helper f1 f2
    | _ -> false in
  let compare_two_vars var1 var2 =
    Debug.no_4 "compare_two_vars" pr_var pr_var pr_formula pr_formula string_of_bool
      (fun _ _ _ _ -> compare_two_vars_x var1 var2) var1 var2 pre post in
  let () = x_tinfo_hp (add_str "all vars" pr_vars) all_vars no_pos in
  let equal_vars = List.filter (fun x -> compare_two_vars var x) all_vars in
  equal_vars

let find_equal_var goal var =
  Debug.no_2 "find_equal_var" pr_goal pr_var pr_vars
    (fun _ _ -> find_equal_var_x goal var) goal var

let choose_rule_field_dnode dn1 dn2 var goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let var_list, prog = goal.gl_vars, goal.gl_prog in
  let data_decls = prog.Cast.prog_data_decls in
  let () = x_tinfo_hp (add_str "pre-dnode" pr_formula) pre no_pos in
  let () = x_tinfo_hp (add_str "post-dnode" pr_formula) post no_pos in
  let bef_args = dn1.CF.h_formula_data_arguments in
  let aft_args = dn2.CF.h_formula_data_arguments in
  let name = dn1.CF.h_formula_data_name in
  let data = List.find (fun x -> x.Cast.data_name = name) data_decls in
  let () = x_tinfo_hp (add_str "data" Cprinter.string_of_data_decl) data no_pos in
  let pre_post = List.combine bef_args aft_args in
  let fields = List.map fst data.Cast.data_fields in
  let triple = List.combine pre_post fields in
  let triple = List.filter (fun ((pre,post),_) -> not(CP.eq_spec_var pre post)) triple in
  let () = x_tinfo_hp (add_str "triple" string_of_int) (List.length triple)
      no_pos in
  let mkRlBind (var, field, n_var) = RlBind {
      rb_bound_var = var;
      rb_field = field;
      rb_other_var = n_var;
    } in
  let helper dif_field =
    let pre_post = fst dif_field in
    let n_var = snd pre_post in
    let () = x_tinfo_hp (add_str "var" (pr_pair pr_var pr_var)) pre_post no_pos in
    let field = snd dif_field in
    if List.exists (fun x -> CP.eq_sv x n_var) goal.gl_vars then
      [(var,field, n_var)]
    else [] in
  let eq_triple (v1, f1, nv1) (v2, f2, nv2) =
    CP.eq_sv v1 v2 && CP.eq_sv nv1 nv2 && f1 = f2 in
  let eq_var_rules = triple |> List.map helper |> List.concat in
  eq_var_rules |> (Gen.BList.remove_dups_eq eq_triple)
  |> List.map mkRlBind

let subtract_var var formula = match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let rec helper hf = match hf with
      | CF.DataNode dnode ->
        let dnode_var = dnode.CF.h_formula_data_node in
        if CP.eq_spec_var dnode_var var then CF.HEmp
        else hf
      | Star sf ->
        let f1 = sf.CF.h_formula_star_h1 in
        let f2 = sf.CF.h_formula_star_h2 in
        let n_f1 = helper f1 in
        let n_f2 = helper f2 in
        Star {sf with h_formula_star_h1 = n_f1;
                      h_formula_star_h2 = n_f2}
      | _ -> hf in
    let n_hf = helper hf in
    CF.Base {bf with formula_base_heap = n_hf}
  | _ -> formula

let rec choose_rassign_data goal cur_var =
  let pre,post = goal.gl_pre_cond, goal.gl_post_cond in
  let () = x_tinfo_hp (add_str "var" pr_sv) cur_var no_pos in
  let () = x_tinfo_hp (add_str "PRE" pr_formula) pre no_pos in
  let () = x_tinfo_hp (add_str "POST" pr_formula) post no_pos in
  let aux_bf hf1 hf2 goal f_var1 f_var2 =
    let var_list = goal.gl_vars in
    let prog = goal.gl_prog in
    match hf1, hf2 with
    | CF.DataNode dnode1, CF.DataNode dnode2 ->
      choose_rule_field_dnode dnode1 dnode2 cur_var goal
    | _ -> [] in
  let aux f_var1 f_var2 goal =
    let var_list = goal.gl_vars in
    let field_rules = match f_var1, f_var2 with
      | CF.Base bf1, CF.Base bf2 ->
        let hf1, hf2 = bf1.CF.formula_base_heap, bf2.CF.formula_base_heap in
        aux_bf hf1 hf2 goal f_var1 f_var2
      | CF.Base bf1, CF.Exists bf2 ->
        let hf1, hf2 = bf1.CF.formula_base_heap, bf2.CF.formula_exists_heap in
        aux_bf hf1 hf2 goal f_var1 f_var2
      | _ -> [] in
    field_rules in
  match pre, post with
  | CF.Base _, CF.Base _    | CF.Base _, CF.Exists _
  | CF.Exists _, CF.Base _  | CF.Exists _, CF.Exists _ ->
    let f_var1 = extract_var_f pre cur_var in
    let f_var2 = extract_var_f post cur_var in
    if f_var1 != None && f_var2 != None then
      let f_var1, f_var2 = Gen.unsome f_var1, Gen.unsome f_var2 in
      let () = x_tinfo_hp (add_str "fvar1" pr_formula) f_var1 no_pos in
      let () = x_tinfo_hp (add_str "fvar2" pr_formula) f_var2 no_pos in
      aux f_var1 f_var2 goal
    else []
  | CF.Base _, CF.Or disjs ->
    let f1, f2 = disjs.CF.formula_or_f1, disjs.CF.formula_or_f2 in
    let goal1 = {goal with gl_post_cond = f1} in
    let goal2 = {goal with gl_post_cond = f2} in
    let rule1 = choose_rassign_data goal1 cur_var in
    let rule2 = choose_rassign_data goal2 cur_var in
    rule1@rule2
  | _ -> []

let choose_rule_assign_x goal : rule list =
  let vars = goal.gl_vars in
  let pr_sv = Cprinter.string_of_spec_var in
  let () = x_tinfo_hp (add_str "vars: " (pr_list pr_sv)) vars no_pos in
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let choose_rule var = match CP.type_of_sv var with
    | TVar _ | Int -> choose_rassign_pure var goal
    | Named _ -> choose_rassign_data goal var
    | _ -> let () = x_tinfo_pp "marking" no_pos in
      []  in
  vars |> List.map choose_rule |> List.concat

let choose_rule_assign goal =
  Debug.no_1 "choose_rule_assign" pr_goal pr_rules
    (fun _ -> choose_rule_assign_x goal) goal

(*********************************************************************
 * Choose function call rules
 *********************************************************************)
let get_hf (f:CF.formula) = match f with
  | Base bf -> bf.formula_base_heap
  | Exists bf -> bf.formula_exists_heap
  | Or _ -> report_error no_pos "get_hf unhandled"

let check_same_shape (f1:CF.formula) (f2:CF.formula) =
  let check_hf (hf1:CF.h_formula) (hf2:CF.h_formula) =
    match hf1, hf2 with
    | CF.HEmp, HEmp -> (true, [])
    | DataNode dn1, DataNode dn2 ->
      let arg1 = dn1.h_formula_data_arguments in
      let arg2 = dn2.h_formula_data_arguments in
      if List.length arg1 = List.length arg2
      then (true, List.combine arg1 arg2)
      else (false, [])
    | ViewNode vn1, ViewNode vn2 ->
      let arg1 = vn1.h_formula_view_arguments in
      let arg2 = vn2.h_formula_view_arguments in
      if List.length arg1 = List.length arg2
      then (true, List.combine arg1 arg2)
      else (false, [])
    | _ -> (false, []) in
  let hf1,hf2 = get_hf f1, get_hf f2 in
  check_hf hf1 hf2

let find_substs (f1:CF.formula) (f2:CF.formula) =
  let () = x_tinfo_hp (add_str "f1" pr_formula) f1 no_pos in
  let () = x_tinfo_hp (add_str "f2 " pr_formula) f2 no_pos in
  let hf1, hf2 = f1 |> get_hf, f2 |> get_hf in
  match hf1, hf2 with
  | DataNode dn1, DataNode dn2 ->
    let args1 = dn1.h_formula_data_arguments in
    let args2 = dn2.h_formula_data_arguments in
    begin
      try List.combine args1 args2
      with _ -> []
    end
  | ViewNode vn1, ViewNode vn2 ->
    let args1 = vn1.h_formula_view_arguments in
    let args2 = vn2.h_formula_view_arguments in
    begin
      try List.combine args1 args2
      with _ -> []
    end
  | _ -> []

let unify_pair arg lvar goal proc_decl =
  let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
  let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
  let pre_proc = specs |> get_pre_cond |> rm_emp_formula in
  let post_proc = specs |> get_post_cond |> rm_emp_formula in
  let a_pre = arg |> extract_var_f pre_proc in
  let l_pre = lvar |> extract_var_f pre_cond in
  match a_pre, l_pre with
  | Some apre_f, Some lpre_f ->
    check_same_shape apre_f lpre_f
  | _ -> false, []

let find_var_field var goal =
  let pre_cond, cprog = goal.gl_pre_cond, goal.gl_prog in
  let rec extract_hf (hf:CF.h_formula) = match hf with
    | DataNode dnode -> let args = dnode.CF.h_formula_data_arguments in
      if List.exists (fun x -> CP.eq_spec_var x var) args then
        let data_decl = List.find
            (fun x -> x.Cast.data_name = dnode.CF.h_formula_data_name)
            cprog.Cast.prog_data_decls in
        let data_args = data_decl.Cast.data_fields |> List.map fst in
        let pairs = List.combine args data_args in
        let field = List.find (fun (x,y) -> CP.eq_spec_var x var) pairs in
        [snd field]
      else []
    | Star sf -> (extract_hf sf.CF.h_formula_star_h1)
                 @ (extract_hf sf.CF.h_formula_star_h2)
    | _ -> [] in
  let rec helper f = match (f:CF.formula) with
  | Base bf -> extract_hf bf.CF.formula_base_heap
  | Or bf -> let f1,f2 = bf.formula_or_f1, bf.formula_or_f2 in
    (helper f1) @ helper f2
  | Exists bf -> extract_hf bf.CF.formula_exists_heap
  in helper pre_cond

let unify (pre_proc, post_proc) goal =
  let proc_decl = goal.gl_proc_decls |> List.hd in
  let proc_args = proc_decl.Cast.proc_args |>
             List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let unify_var arg goal =
    let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
    let arg_typ = CP.type_of_sv arg in
    let () = x_tinfo_hp (add_str "all vars" pr_vars) (CF.fv pre_cond) no_pos in
    let l_vars = CF.fv pre_cond |> List.filter (fun x -> CP.type_of_sv x = arg_typ) in
    let () = x_tinfo_hp (add_str "vars" pr_vars) l_vars no_pos in
    let ss_vars = List.map (fun lvar ->
        let (x,y) = unify_pair arg lvar goal proc_decl in
        (lvar, x, y)) l_vars in
    let ss_vars = List.filter (fun (_,x,_) -> x) ss_vars in
    let ss_vars = List.map (fun (x,_,y) -> (x,y)) ss_vars in
    ss_vars in
  let ss_args = proc_args |> List.map (fun arg -> unify_var arg goal) in
  let rec mk_args_input args = match args with
    | [] -> []
    | [h] -> List.map (fun x -> [x]) h
    | h::t -> let tmp = mk_args_input t in
      let head_added = List.map (fun x -> List.map (fun y -> [x]@y) tmp) h in
      List.concat head_added in
  let ss_args = mk_args_input ss_args in
  let contain_res = CF.fv post_proc |> List.map (fun x -> CP.name_of_sv x)
                     |> List.exists (fun x -> x = res_name) in
  let ss_args = List.filter(fun list_and_subst ->
      let list = List.map fst list_and_subst in
      let n_list = CP.remove_dups_svl list in
      List.length n_list = List.length list
    ) ss_args in
  if ss_args != [] then
    ss_args |> List.map (fun args_and_substs ->
        let args = List.map fst args_and_substs in
        let substs = List.map snd args_and_substs |> List.concat in
        let is_cur_vars = List.for_all (fun x ->
            List.exists (fun y -> CP.eq_spec_var x y) goal.gl_vars) args in
        if is_cur_vars then
          let combine_args = List.combine args proc_args in
          let eq_args = List.for_all (fun (x,y) -> CP.eq_sv x y) combine_args in
          if not eq_args then
            let r_var = if contain_res then
                let res = List.find (fun x -> CP.name_of_sv x = res_name)
                    (CF.fv post_proc) in
                let n_var = CP.mk_typed_sv (CP.type_of_sv res)
                    ("rs" ^ (string_of_int !res_num)) in
                let () = res_num := !res_num + 1 in
                Some n_var
              else None in
            let fc_rule = (* RlFuncCall *) {
                rfc_func_name = proc_decl.Cast.proc_name;
                rfc_params = args;
                rfc_substs = substs;
                rfc_return = r_var;
              } in
            [fc_rule] else []
        else []
      ) |> List.concat
    |> Gen.BList.remove_dups_eq
      (fun r1 r2 -> CP.eq_spec_var_list r1.rfc_params r2.rfc_params)
    |> List.map (fun x -> RlFuncCall x)
  else []

let choose_func_call goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let procs = goal.gl_proc_decls in
  if procs = [] || has_fcall_trace goal.gl_trace then []
  else
    let proc_decl = List.hd procs in
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let () = x_tinfo_hp (add_str "specs" pr_struc_f) specs no_pos in
    let pre_cond = specs |> get_pre_cond |> rm_emp_formula in
    let () = x_tinfo_hp (add_str "pre_cond " pr_formula) pre_cond no_pos in
    let post_cond = specs |> get_post_cond |> rm_emp_formula in
    let () = x_tinfo_hp (add_str "post_cond " pr_formula) post_cond no_pos in
    let rules = unify (pre_cond, post_cond) goal in
    rules

let choose_rule_fread_x goal =
  let vars, pre_cond = goal.gl_vars, goal.gl_pre_cond in
  let () = x_tinfo_hp (add_str "pre_cond " pr_formula) pre_cond no_pos in
  let rec helper_hf (hf:CF.h_formula) = match hf with
    | DataNode dnode -> let dn_var = dnode.CF.h_formula_data_node in
      if List.exists (fun x -> CP.eq_spec_var x dn_var) vars then
        let dn_name = dnode.CF.h_formula_data_name in
        let dn_args = dnode.CF.h_formula_data_arguments in
        [(dn_var, dn_name, dn_args)]
      else []
    | Star sf -> let hf1, hf2 = sf.h_formula_star_h1, sf.h_formula_star_h2 in
      (helper_hf hf1) @ (helper_hf hf2)
    | _ -> [] in
  let rec helper_f (f:CF.formula) = match f with
    | Base bf -> helper_hf bf.CF.formula_base_heap
    | Or bf -> let f1,f2 = bf.formula_or_f1, bf.formula_or_f2 in
      (helper_f f1) @ (helper_f f2)
    | Exists bf -> helper_hf bf.formula_exists_heap in
  let triples = helper_f pre_cond in
  let pr_triples = pr_list (pr_triple pr_var pr_id pr_vars) in
  let () = x_tinfo_hp (add_str "triples" pr_triples) triples no_pos in
  let helper_triple (var, data, args) =
    let prog = goal.gl_prog in
    let data = List.find (fun x -> x.Cast.data_name = data)
        prog.Cast.prog_data_decls in
    let d_args = data.Cast.data_fields |> List.map fst in
    let d_arg_pairs = List.combine args d_args in
    let d_arg_pairs = List.filter (fun (x,_) -> not(CP.mem x vars)) d_arg_pairs in
    let helper_arg (arg, field) =
      let rbind = RlFRead {
          rbr_bound_var = var;
          rbr_field = field;
          rbr_value = arg;
        } in [rbind] in
    d_arg_pairs |> List.map helper_arg |> List.concat in
  List.map helper_triple triples |> List.concat

let choose_rule_fread goal =
  Debug.no_1 "choose_rule_fread" pr_goal pr_rules
    (fun _ -> choose_rule_fread_x goal) goal

let choose_rule_unfold_pre goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let () = x_tinfo_hp (add_str "pre" pr_formula) pre no_pos in
  let vnodes = get_unfold_view goal.gl_vars pre in
  let () = x_tinfo_hp (add_str "vnode" (pr_list pr_hf)) (vnodes |> List.map (fun x -> CF.ViewNode x)) no_pos in
  let helper vnode =
    let pr_views, args = need_unfold_rhs goal.gl_prog vnode in
    let () = x_tinfo_hp (add_str "args" pr_vars) args no_pos in
    let nf = do_unfold_view_vnode goal.gl_prog pr_views args pre in
    let pre_list = List.filter (fun x -> not(SB.check_unsat goal.gl_prog x)) nf in
    let pre_list = pre_list |> List.map remove_exists
                 |> List. map (fun x -> CF.simplify_formula x goal.gl_vars)in
    let () = x_tinfo_hp (add_str "nf" (pr_list pr_formula)) pre_list no_pos in
    if pre_list = [] then []
    else let rule = RlUnfoldPre { n_pre_formulas = pre_list } in
      [rule] in
  if has_unfold_pre goal.gl_trace then []
  else vnodes |> List.map helper |> List.concat

let choose_rule_unfold_post goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let vnodes = get_unfold_view goal.gl_vars post in
  let helper vnode =
    let pr_views, args = need_unfold_rhs goal.gl_prog vnode in
    let nf = do_unfold_view_vnode goal.gl_prog pr_views args post in
    let rules = nf |> List.map (fun f -> RlUnfoldPost { rp_case_formula = f}) in
    rules in
  if has_unfold_post goal.gl_trace then []
  else vnodes |> List.map helper |> List.concat

let choose_rule_numeric_x goal =
  let vars = goal.gl_vars |> List.filter is_int_var in
  let post_vars = CF.fv goal.gl_post_cond in
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let () = x_tinfo_hp (add_str "pre" pr_formula) pre no_pos in
  let () = x_tinfo_hp (add_str "post" pr_formula) post no_pos in
  let pre_vars, post_vars = CF.fv pre, CF.fv post in
  let () = x_tinfo_hp (add_str "gl_vars" pr_vars) goal.gl_vars no_pos in
  let () = x_tinfo_hp (add_str "vars" pr_vars) vars no_pos in
  let () = x_tinfo_hp (add_str "post vars" pr_vars) post_vars no_pos in
  let vars_lhs = List.filter (fun x -> CP.mem x vars
                                     || CP.is_res_spec_var x) post_vars in
  let () = x_tinfo_hp (add_str "vars lhs" pr_vars) vars_lhs no_pos in
  let create_templ all_vars cur_var =
    let other_vars = List.filter (fun x -> not(CP.eq_sv x cur_var)) all_vars in
    let var_formula = extract_var_f post cur_var in
    match var_formula with
    | Some var_f ->
      let () = x_tinfo_hp (add_str "nf" pr_formula) var_f no_pos in
      let pure_pre, var_pf = CF.get_pure pre, CF.get_pure var_f in
      let tmpl_args = List.map (fun x -> CP.mkVar x no_pos) other_vars in
      let templ = CP.Template (CP.mkTemplate tmpl_name tmpl_args no_pos) in
      let n_pf = CP.mkEqExp (CP.mkVar cur_var no_pos) templ no_pos in
      let n_pre = CP.mkAnd pure_pre n_pf no_pos in
      let () = x_tinfo_hp (add_str "n_pre" pr_pf) n_pre no_pos in
      let () = x_tinfo_hp (add_str "n_post" pr_pf) var_pf no_pos in
      let defn = SB.infer_templ_defn goal.gl_prog n_pre var_pf tmpl_name other_vars in
      begin
        match defn with
        | Some def -> let rule = RlAssign {
            ra_lhs = cur_var;
            ra_rhs = def;
          } in [rule]
        | _ -> []
      end
    | None -> [] in
  let rules = vars_lhs |> List.map (fun x -> create_templ vars x) in
  rules |> List.concat

let choose_rule_numeric goal =
  Debug.no_1 "choose_rule_numeric" pr_goal pr_rules
    (fun _ -> choose_rule_numeric_x goal) goal

let check_eq_pre_post prog (pre:CF.formula) (post:CF.formula) var =
  let pre_f, post_f = extract_var_f pre var, extract_var_f post var in
  match pre_f, post_f with
  | Some pre_f, Some post_f ->
    let () = x_tinfo_hp (add_str "pre_f" pr_formula) pre_f no_pos in
    let () = x_tinfo_hp (add_str "post_f" pr_formula) post_f no_pos in
    (SB.check_equal prog pre_f post_f) && (CF.isEmpFormula pre_f)
  | _ -> false

let framing_var_goal goal (var:CP.spec_var) : goal =
  let n_pre = frame_var_formula goal.gl_pre_cond var in
  let n_post = frame_var_formula goal.gl_post_cond var in
  {goal with gl_pre_cond = fst n_pre;
             gl_post_cond = fst n_post;}

let framing_rule goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let pre_vars = CF.fv pre |> List.filter (fun x -> match CP.type_of_sv x with
      | Named _ -> true
      | _ -> false) in
  let eq_vars = List.filter (check_eq_pre_post goal.gl_prog pre post) pre_vars in
  let () = x_tinfo_hp (add_str "eq_vars" pr_vars) eq_vars no_pos in
  let n_goal = List.fold_left (fun x y -> framing_var_goal x y) goal eq_vars in
  n_goal

let choose_rule_instantiate goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let () = x_tinfo_hp (add_str "post" pr_formula) post no_pos in
  let exists_vars = CF.get_exists post |> List.filter is_node_var in
  let () = x_tinfo_hp (add_str "exists_vars" pr_vars) exists_vars no_pos in
  let helper var =
    let eq_vars = find_equal_var goal var in
    eq_vars |> List.map (fun x -> RlInstantiate {
        rli_lhs = var;
        rli_rhs = x}) in
  exists_vars |> List.map helper |> List.concat

let extract_frame_info var (formula:CF.formula) =
  match formula with
  | CF.Base bf -> let hf = bf.CF.formula_base_heap in
    extract_hf_var hf var
  | CF.Exists bf -> let hf = bf.CF.formula_exists_heap in
    extract_hf_var hf var
  | CF.Or _ -> None

let add_eq_vars formula eq_var_list =
  let eq_vars = List.map (fun (x,y) -> CP.mkEqVar x y no_pos) eq_var_list in
  let rec aux list cur = match list with
    | [] -> cur
    | h::t -> let cur = CP.mkAnd h cur no_pos in
      aux t cur in
  let n_pf = aux eq_vars (CP.mkTrue no_pos) in
  CF.add_pure_formula_to_formula n_pf formula

let is_frame_var goal post_var pre_var =
  let pre_info = extract_frame_info pre_var goal.gl_pre_cond in
  let post_info = extract_frame_info post_var goal.gl_post_cond in
  match pre_info, post_info with
  | Some (_, vars1, name1), Some (_, vars2, name2) ->
    if eq_str name1 name2 then
      let () = x_tinfo_hp (add_str "var1" pr_vars) vars1 no_pos in
      let () = x_tinfo_hp (add_str "var2" pr_vars) vars2 no_pos in
      let n_pre = remove_heap_var_f pre_var goal.gl_pre_cond in
      let n_post = remove_heap_var_f post_var goal.gl_post_cond in
      let n_post = add_eq_vars n_post (List.combine vars1 vars2) in
      let () = x_tinfo_hp (add_str "n_pre" pr_formula) n_pre no_pos in
      let () = x_tinfo_hp (add_str "n_post" pr_formula) n_post no_pos in
      let rule = RlFraming {
          rf_n_pre = n_pre;
          rf_n_post = n_post;
        } in
      [rule]
    else []
  | _ -> []

let find_framing_vars goal var =
  let pre = goal.gl_pre_cond in
  let pre_vars = (CF.fv pre) @ (CF.get_exists pre)|> List.filter is_node_var in
  pre_vars |> List.map (is_frame_var goal var)
                    |> List.concat

let choose_rule_framing goal =
  let post = goal.gl_post_cond in
  let vars = (CF.fv post) @ (CF.get_exists post) |> List.filter is_node_var in
  let () = x_tinfo_hp (add_str "vars" (pr_list Cprinter.string_of_typed_spec_var)) vars no_pos in
  vars |> List.map (find_framing_vars goal) |> List.concat

let choose_rule_return_x goal =
  let post = goal.gl_post_cond in
  let post_vars = CF.fv post |> List.map CP.name_of_sv in
  if List.exists (fun x -> eq_str x "res") post_vars then
    let res = List.find (fun x -> eq_str (CP.name_of_sv x) "res") (CF.fv post) in
    let is_return rule = match rule with
      | RlAssign rl -> CP.eq_sv res rl.ra_lhs
      | _ -> false in
    let n_goal = {goal with gl_vars = res::goal.gl_vars} in
    let rules = choose_rule_assign n_goal in
    let () = x_tinfo_hp (add_str "rules" (pr_list pr_rule)) rules no_pos in
    rules |> List.filter is_return
  else []

let choose_rule_return goal =
  Debug.no_1 "choose_rule_return" pr_goal pr_rules
    (fun _ -> choose_rule_return_x goal) goal

let rec choose_rule_interact goal rules =
  if rules = [] then
    let () = x_binfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
    rules
  else
    let str = pr_list_ln pr_rule rules in
    let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
    let () = x_binfo_hp (add_str "Choose rule" pr_id) str no_pos in
    let choice = String.uppercase_ascii (String.trim (read_line ())) in
    let rule_id = int_of_string (choice) in
    let rules_w_ids = List.mapi (fun i x -> (i+1, x)) rules in
    let chosen_rules, other_rules =
      List.partition (fun (x, _) -> x = rule_id) rules_w_ids in
    if chosen_rules = [] then
      let err_str = "Wrong choose, please choose again" in
      let () = x_binfo_hp (add_str "Error" pr_id) err_str no_pos in
      choose_rule_interact goal rules
    else
      let rules = chosen_rules @ other_rules in
      List.map snd rules

let choose_synthesis_rules_x goal : rule list =
  let goal = simplify_goal goal in
  let rs = [] in
  let rs = rs @ (choose_rule_unfold_post goal) in
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_numeric goal) in
  let rs = rs @ (choose_rule_assign goal) in
  let rs = rs @ (choose_rule_return goal) in
  let rs = rs @ choose_rule_instantiate goal in
  let rs = rs @ (choose_func_call goal) in
  let rs = eliminate_useless_rules goal rs in
  let rs = reorder_rules goal rs in
  let rs = if !enable_i then choose_rule_interact goal rs
    else rs in
  rs

let choose_synthesis_rules goal =
  Debug.no_1 "choose_synthesis_rule" pr_goal pr_rules
    (fun _ -> choose_synthesis_rules_x goal) goal

(*********************************************************************
 * Processing rules
 *********************************************************************)
let process_rule_assign goal rassign =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let lhs, rhs = rassign.ra_lhs, rassign.ra_rhs in
  let n_pf = CP.mkEqExp (CP.mkVar lhs no_pos) rhs no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_pf pre in
  let post_vars = CF.fv post in
  let () = x_tinfo_hp (add_str "n_pre" pr_formula) n_pre no_pos in
  if List.exists CP.is_res_spec_var post_vars then
    if CP.is_res_spec_var lhs then
      let ent_check, _ = SB.check_entail goal.gl_prog n_pre post in
      match ent_check with
      | true -> mk_derivation_success goal (RlAssign rassign)
      | false -> mk_derivation_fail goal (RlAssign rassign)
    else
      let ent_check, _ = SB.check_entail goal.gl_prog n_pre post in
      match ent_check with
      | true -> mk_derivation_fail goal (RlAssign rassign)
      | false ->
        let sub_goal = {goal with gl_pre_cond = n_pre} in
        mk_derivation_subgoals goal (RlAssign rassign) [sub_goal]
  else
    let ent_check, _ = SB.check_entail goal.gl_prog n_pre post in
    if ent_check then mk_derivation_success goal (RlAssign rassign)
    else
      let sub_goal = {goal with gl_pre_cond = n_pre} in
      mk_derivation_subgoals goal (RlAssign rassign) [sub_goal]

let subs_bind_write formula var field new_val data_decls =
  match (formula:CF.formula) with
  | Base bf ->
    let hf = bf.CF.formula_base_heap in
    let () = x_tinfo_hp (add_str "hf" Cprinter.string_of_h_formula) hf no_pos in
    let rec helper (hf:CF.h_formula) = match hf with
      | DataNode dnode -> let data_var = dnode.h_formula_data_node in
        let () = x_tinfo_hp (add_str "hf" Cprinter.string_of_h_formula) hf
            no_pos in
        if CP.eq_spec_var data_var var then
          let n_dnode = set_field dnode field new_val data_decls in
          (CF.DataNode n_dnode)
        else hf
      | Star sf -> let n_h1 = helper sf.CF.h_formula_star_h1 in
        let n_h2 = helper sf.CF.h_formula_star_h2 in
        Star {sf with h_formula_star_h1 = n_h1;
                      h_formula_star_h2 = n_h2}
      | _ -> hf
    in CF.Base {bf with formula_base_heap = helper hf}
  | _ -> formula

let process_rule_bind goal (bind:rule_bind) =
  let pre, var = goal.gl_pre_cond, bind.rb_bound_var in
  let field, prog = bind.rb_field, goal.gl_prog in
  let rhs, data_decls = bind.rb_other_var, prog.prog_data_decls in
  let n_post = subs_bind_write pre var field rhs data_decls in
  let () = x_tinfo_hp (add_str "after applied:" pr_formula) n_post no_pos in
  let ent_check,_ = SB.check_entail goal.gl_prog n_post goal.gl_post_cond in
  match ent_check with
  | true -> mk_derivation_success goal (RlBind bind)
  | false -> mk_derivation_fail goal (RlBind bind)

let process_rule_f_read goal (rule:rule_bind_read) =
    let vars = [rule.rbr_value] @ goal.gl_vars |> CP.remove_dups_svl in
    let n_goal = {goal with gl_vars = vars} in
    mk_derivation_subgoals goal (RlFRead rule) [n_goal]

let process_func_call goal rcore : derivation =
  let fun_name, params = rcore.rfc_func_name, rcore.rfc_params in
  let proc_decl = goal.gl_proc_decls
                  |> List.find (fun x -> eq_str x.Cast.proc_name fun_name) in
  let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
  let pre_proc = specs |> get_pre_cond |> rm_emp_formula in
  let post_proc = specs |> get_post_cond |> rm_emp_formula in
  let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
  let fun_args = proc_decl.Cast.proc_args
                 |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let substs = List.combine fun_args params in
  let substs = substs @ rcore.rfc_substs in
  let () = x_tinfo_hp (add_str "subst" pr_substs) substs no_pos in
  let params_pre = CF.subst substs pre_proc in
  let exists_vars = CF.fv params_pre
                    |> List.filter (fun x -> CP.not_mem x params) in
  let fresh_evars = List.map CP.mk_fresh_sv exists_vars in
  let params_pre = CF.subst (List.combine exists_vars fresh_evars) params_pre in
  let params_pre = CF.wrap_exists fresh_evars params_pre in
  let () = x_tinfo_hp (add_str "pre_cond" pr_formula) pre_cond no_pos in
  let () = x_tinfo_hp (add_str "params_pre" pr_formula) params_pre no_pos in
  let ent_check, residue = SB.check_entail ~residue:true goal.gl_prog
      pre_cond params_pre in
  match ent_check, residue with
  | true, Some red ->
    let params_post = CF.subst substs post_proc in
    let evars = CF.get_exists params_post in
    let post_state = add_formula_to_formula red params_post in
    let np_vars = CF.fv post_state in
    let contain_res = np_vars |> List.map (fun x -> CP.name_of_sv x)
                      |> List.exists (fun x -> x = res_name) in
    let post_state, n_vars = if rcore.rfc_return != None then
        let res = List.find (fun x -> CP.name_of_sv x = res_name) np_vars in
        let n_var = Gen.unsome rcore.rfc_return in
        let n_f = CF.subst [(res, n_var)] post_state in
        (n_f, goal.gl_vars @ [n_var])
      else post_state, goal.gl_vars in
    let () = x_tinfo_hp (add_str "post_state" pr_formula) post_state no_pos in
    let () = x_tinfo_hp (add_str "post_cond" pr_formula) post_cond no_pos in
    let post_check, _ = SB.check_entail goal.gl_prog post_state post_cond in
    if post_check then
      mk_derivation_success goal (RlFuncCall rcore)
    else let eq_heap = SB.eq_h_formula goal.gl_prog pre_proc post_proc in
      let already_call = List.exists (fun args ->
          if (List.length args = List.length params) then
            List.for_all2 (fun x y -> CP.eq_spec_var x y) args params
          else false
        ) !fc_args in
      (* if already_call && eq_heap then *)
      if already_call then
        mk_derivation_fail goal (RlFuncCall rcore)
      else
        let () = x_tinfo_hp (add_str "fc_args" (pr_list pr_vars)) (!fc_args) no_pos in
        let () = fc_args := params::(!fc_args) in
        let sub_goal = {goal with gl_vars = n_vars;
                                     gl_trace = (RlFuncCall rcore)::goal.gl_trace;
                                     gl_pre_cond = post_state} in
        mk_derivation_subgoals goal (RlFuncCall rcore) [sub_goal]
  | _ -> mk_derivation_fail goal (RlFuncCall rcore)

and process_rule_unfold_pre goal rule =
  let n_pres = rule.n_pre_formulas in
  let create_new_rule n_pre =
    {goal with gl_pre_cond = n_pre;
               gl_trace = goal.gl_trace @ [RlUnfoldPre rule]} in
  let n_goals = n_pres |> List.map create_new_rule in
  mk_derivation_subgoals goal (RlUnfoldPre rule) n_goals

let process_rule_instantiate goal rule =
  let n_pre, pre_vars = frame_var_formula goal.gl_pre_cond rule.rli_rhs in
  let n_post, post_vars = frame_var_formula goal.gl_post_cond rule.rli_lhs in
  if List.length pre_vars = List.length post_vars then
    let qvars, post_bf = CF.split_quantifiers n_post in
    let pre_vars = rule.rli_rhs::pre_vars in
    let post_vars = rule.rli_lhs::post_vars in
    let () = x_tinfo_hp (add_str "pre vars" pr_vars) pre_vars no_pos in
    let () = x_tinfo_hp (add_str "post vars" pr_vars) post_vars no_pos in
    let n_post = CF.subst (List.combine post_vars pre_vars) post_bf in
    let qvars = qvars |> List.filter (fun x -> not(CP.mem x post_vars)) in
    let n_post = CF.add_quantifiers qvars n_post in
    (* let rm_vars = [rule.rli_lhs; rule.rli_rhs] in
     * let n_vars = goal.gl_vars |> List.filter (fun x-> not(CP.mem x rm_vars)) in *)
    let subgoal = {goal with gl_post_cond = n_post;
                             (* gl_vars = n_vars; *)
                             gl_pre_cond = n_pre} in
    mk_derivation_subgoals goal (RlInstantiate rule) [subgoal]
  else mk_derivation_fail goal (RlInstantiate rule)

and process_rule_unfold_post goal rule =
  let n_goal = {goal with gl_post_cond = rule.rp_case_formula;
                          gl_trace = (RlUnfoldPost rule)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlUnfoldPost rule) [n_goal]

let process_rule_framing goal rule =
  let n_goal = {goal with gl_pre_cond = rule.rf_n_pre;
                          gl_post_cond = rule.rf_n_post} in
  mk_derivation_subgoals goal (RlFraming rule) [n_goal]

(*********************************************************************
 * The search procedure
 *********************************************************************)
let rec synthesize_one_goal goal : synthesis_tree =
  let rules = choose_synthesis_rules goal in
  process_all_rules goal rules

and process_all_rules goal rules : synthesis_tree =
  let rec process atrees rules =
    match rules with
    | rule::other_rules ->
      let drv = process_one_rule goal rule in
      let stree = process_one_derivation drv in
      let atrees = atrees @ [stree] in
      if is_synthesis_tree_success stree then
        let pts = get_synthesis_tree_status stree in
        mk_synthesis_tree_search goal atrees pts
      else process atrees other_rules
    | [] ->
      let () = x_tinfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
      mk_synthesis_tree_fail goal atrees "no rule can be applied" in
  process [] rules

and process_one_rule goal rule : derivation =
  match rule with
  | RlFuncCall rcore -> process_func_call goal rcore
  | RlAssign rassign -> process_rule_assign goal rassign
  | RlBind bind -> process_rule_bind goal bind
  | RlUnfoldPre rule -> process_rule_unfold_pre goal rule
  | RlUnfoldPost rule -> process_rule_unfold_post goal rule
  | RlFRead rule -> process_rule_f_read goal rule
  | RlInstantiate rule -> process_rule_instantiate goal rule
  | RlFraming rule -> process_rule_framing goal rule

and process_conjunctive_subgoals goal rule (sub_goals: goal list) : synthesis_tree =
  let rec helper goals subtrees st_cores =
    match goals with
    | sub_goal::other_goals ->
      let syn_tree = synthesize_one_goal sub_goal in
      let status = get_synthesis_tree_status syn_tree in
      begin
        match status with
        | StUnkn _ -> mk_synthesis_tree_fail goal [] "one of subgoals failed"
        | StValid st_core ->
          helper other_goals (subtrees@[syn_tree]) (st_cores@[st_core])
      end
    | [] -> let st_core = mk_synthesis_tree_core goal rule st_cores in
      mk_synthesis_tree_derive goal rule subtrees (StValid st_core)
  in helper sub_goals [] []

and process_one_derivation drv : synthesis_tree =
  let goal, rule = drv.drv_goal, drv.drv_rule in
  match drv.drv_kind with
  | DrvStatus false -> mk_synthesis_tree_fail goal [] "unknown"
  | DrvStatus true -> mk_synthesis_tree_success goal rule
  | DrvSubgoals gs -> process_conjunctive_subgoals goal rule gs

(*********************************************************************
 * The main synthesis algorithm
 *********************************************************************)
let synthesize_program goal =
  let () = fc_args := [] in
  let () = x_tinfo_hp (add_str "goal" pr_goal) goal no_pos in
  let st = synthesize_one_goal goal in
  let st_status = get_synthesis_tree_status st in
  match st_status with
  | StValid st_core ->
    let () = x_tinfo_hp (add_str "tree_core " pr_st_core) st_core no_pos in
    let i_exp = synthesize_st_core st_core in
    let () = x_binfo_hp (add_str "iast exp" pr_iast_exp) i_exp no_pos in
    Some i_exp
  | StUnkn _ -> let () = x_binfo_pp "SYNTHESIS PROCESS FAILED" no_pos in
    None

let synthesize_wrapper iprog prog proc pre_cond post_cond vars =
  let goal = mk_goal_w_procs prog [proc] pre_cond post_cond vars in
  let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
  let iast_exp = synthesize_program goal in
  let pname, i_procs = proc.Cast.proc_name, iprog.Iast.prog_proc_decls in
  let i_proc = List.find (fun x -> contains pname x.Iast.proc_name) i_procs in
  let n_proc, res = match iast_exp with
    | None -> (i_proc, false)
    | Some exp0 -> (replace_exp_proc exp0 i_proc, true) in
  let n_iprocs = List.map (fun x -> if contains pname x.Iast.proc_name
                            then n_proc else x) i_procs in
  ({iprog with I.prog_proc_decls = n_iprocs}, res)

let synthesize_entailments iprog prog proc =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments prog entailments in
  match hps with
  | None -> ()
  | Some hps ->
    let iproc = List.find (fun x -> contains proc.CA.proc_name x.IA.proc_name)
        iprog.IA.prog_proc_decls in
    let decl_vars = match iproc.IA.proc_body with
      | None -> []
      | Some exp -> get_var_decls (Gen.unsome !repair_pos) exp in
    let syn_vars = proc.Cast.proc_args
                   |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
    if !syn_pre != None && hps != [] then
      let post_hp = List.find (fun x -> x.Cast.hp_name = "Q") hps in
      let pre = !syn_pre |> Gen.unsome |> unprime_formula in
      let post = post_hp.Cast.hp_formula in
      let () = x_tinfo_hp (add_str "post" pr_formula) post no_pos in
      let (n_iprog, res) = synthesize_wrapper iprog prog proc pre post syn_vars in
      if res then repair_res := Some n_iprog else ()
    else ()
