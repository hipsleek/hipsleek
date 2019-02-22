#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure
open Cformula

open Synthesis

module CA = Cast
module CF = Cformula
module CP = Cpure

(*********************************************************************
 * Data structures and exceptions
 *********************************************************************)

exception EStree of synthesis_tree

let raise_stree st = raise (EStree st)
let pr_formula = Cprinter.string_of_formula
let pr_struc_f = Cprinter.string_of_struc_formula
let pr_hf = Cprinter.string_of_h_formula
let pr_pf = Cprinter.string_of_pure_formula
let pr_sv = Cprinter.string_of_spec_var
let pr_var = Cprinter.string_of_spec_var
let pr_vars = pr_list pr_var

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
(* {x -> node{a} * y -> node{b}}{x -> node{y} * y -> node{b}} --> x.next = b *)
let choose_rassign_pure var goal : rule list =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let cur_vars = goal.gl_vars in
  let () = x_binfo_hp (add_str "var" pr_sv) var no_pos in
  let () = x_binfo_hp (add_str "vars" (pr_list pr_sv)) cur_vars no_pos in
  let pre_pf = CF.get_pure pre in
  let () = x_binfo_hp (add_str "pre_pf" pr_pf) pre_pf no_pos in
  let post_pf = CF.get_pure post in
  let () = x_binfo_hp (add_str "post_pf" pr_pf) post_pf no_pos in
  let pre_f = extract_var_pf pre_pf var in
  let pr_exp = Cprinter.string_of_formula_exp in
  let post_f = extract_var_pf post_pf var in
  match pre_f, post_f with
  | Some e1, Some e2 ->
    (match e2 with
     | Var (sv, _) ->
       let () = x_binfo_pp "marking" no_pos in
       if List.exists (fun x -> CP.eq_spec_var x sv) cur_vars then
         let rule = RlAssign {
             ra_lhs = var;
             ra_rhs = sv;
           } in
         [rule]
       else
         let () = x_binfo_pp "marking \n" no_pos in
         let cur_vars = List.filter (fun x -> x != var) cur_vars in
         let () = x_binfo_hp (add_str "vars: " pr_vars) cur_vars no_pos in
         let () = x_binfo_hp (add_str "var: " pr_var) sv no_pos in
         let find_var = find_sub_var sv cur_vars pre_pf in
         begin
           match find_var with
           | None -> []
           | Some sub_var ->
             let rule = RlAssign {
                 ra_lhs = var;
                 ra_rhs = sub_var;
               } in
             [rule]
         end
     | _ -> []
    )
  | _ -> []

let find_equal_var var goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let all_vars = goal.gl_vars in
  let helper_pure var1 var2 exists_vars pf1 pf2 =
    let ante = CP.mkAnd pf1 pf2 no_pos in
    let conseq = CP.mkEqVar var1 var2 no_pos in
    let () = x_binfo_hp (add_str "ante" pr_pf) ante no_pos in
    let () = x_binfo_hp (add_str "conseq" pr_pf) conseq no_pos in
    Songbird.check_pure_entail ante conseq in
  let helper f1 f2 = match f1, f2 with
    | CF.Exists bf1, CF.Base bf2 ->
      let hf1 = bf1.CF.formula_exists_heap in
      let hf2 = bf2.CF.formula_base_heap in
      let exists_vars = bf1.CF.formula_exists_qvars in
      let pf1 = Mcpure.pure_of_mix bf1.CF.formula_exists_pure in
      let pf2 = Mcpure.pure_of_mix bf2.CF.formula_base_pure in
      begin
        match hf1, hf2 with
        | CF.ViewNode vnode1, CF.ViewNode vnode2 ->
          let args1 = vnode1.CF.h_formula_view_arguments in
          let args2 = vnode2.CF.h_formula_view_arguments in
          List.for_all2 (fun x y -> helper_pure x y exists_vars pf1 pf2) args1 args2
        | _ -> false
      end
    | _ -> false in
  let compare_two_vars var1 var2 pre post =
    let var1_f = extract_var_f post var1 in
    let var2_f = extract_var_f pre var2 in
    match var1_f, var2_f with
    | Some f1, Some f2 ->
      let () = x_binfo_hp (add_str "equal-var f1" pr_formula) f1 no_pos in
      let () = x_binfo_hp (add_str "equal-var f2" pr_formula) f2 no_pos in
      helper f1 f2
    | _ -> false
  in
  let () = x_binfo_hp (add_str "equal-var vars" pr_vars) all_vars no_pos in
  let equal_vars = List.filter (fun x -> compare_two_vars var x pre post) all_vars in
  equal_vars

let choose_rule_field_dnode dn1 dn2 var goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let var_list = goal.gl_vars in
  let prog = goal.gl_prog in
  let data_decls = prog.Cast.prog_data_decls in
  let () = x_binfo_hp (add_str "pre-dnode" pr_formula) pre no_pos in
  let () = x_binfo_hp (add_str "post-dnode" pr_formula) post no_pos in
  let bef_args = dn1.CF.h_formula_data_arguments in
  let aft_args = dn2.CF.h_formula_data_arguments in
  let name = dn1.CF.h_formula_data_name in
  let data = List.find (fun x -> x.Cast.data_name = name) data_decls in
  let () = x_tinfo_hp (add_str "data" Cprinter.string_of_data_decl) data no_pos in
  let pre_post = List.combine bef_args aft_args in
  let fields = List.map fst data.Cast.data_fields in
  let triple = List.combine pre_post fields in
  let triple = List.filter (fun ((pre,post),_) -> not(CP.eq_spec_var pre post)) triple in
  let () = x_binfo_hp (add_str "triple" string_of_int) (List.length triple)
      no_pos in
  let helper dif_field =
    let pre_post = fst dif_field in
    let post_val_var = snd pre_post in
    let eq_vars = find_equal_var post_val_var goal in
    let eq_vars = List.filter (fun x -> not(CP.eq_spec_var x var)) eq_vars in
    if eq_vars != [] then
      let eq_var = List.hd eq_vars in
      let field = snd dif_field in
      let () = x_binfo_hp (add_str "eq_var" pr_var) eq_var no_pos in
      let rule = RlBind {
          rb_bound_var = var;
          rb_field = field;
          rb_other_var = eq_var;
          rb_write = false;
        } in
      [rule]
    else [] in
  let pure_rules dif_field =
    let df_name = dif_field |> snd in
    let n_name = snd df_name in
    let n_var = CP.mk_typed_spec_var (fst df_name) n_name in
    let var_list = var_list @ [n_var] in
    let pre_val = dif_field |> fst |> fst in
    let post_val = dif_field |> fst |> snd in
    let n_pre_pure = CP.mkEqVar n_var pre_val no_pos in
    let n_post_pure = CP.mkEqVar n_var post_val no_pos in
    let n_pre = CF.add_pure_formula_to_formula n_pre_pure pre in
    let n_post = CF.add_pure_formula_to_formula n_post_pure post in
    let n_goal = mk_goal prog n_pre n_post var_list in
    let n_rule = choose_rassign_pure n_var n_goal in
    if n_rule = [] then []
    else
      let () = x_binfo_hp (add_str "rules" (pr_list pr_rule)) n_rule no_pos in
      let eq_rule = List.hd n_rule in
      match eq_rule with
      | RlAssign rassgn ->
        let rule = RlBind {
            rb_bound_var = var;
            rb_field = (fst df_name, n_name);
            rb_other_var = rassgn.ra_rhs;
            rb_write = true;
          }
        in [rule]
      | _ -> []
  in
  (* let pure_rules = triple |> List.map pure_rules |> List.concat in *)
  let pure_rules = [] in
  let eq_var_rules = triple |> List.map helper |> List.concat in
  pure_rules @ eq_var_rules


let subtract_var var formula = match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let rec helper hf = match hf with
      | CF.DataNode dnode ->
        let dnode_var = dnode.CF.h_formula_data_node in
        if CP.eq_spec_var dnode_var var then HEmp
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

let rec choose_rassign_data cur_var goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let () = x_binfo_hp (add_str "var" pr_sv) cur_var no_pos in
  let () = x_binfo_hp (add_str "PRE" pr_formula) pre no_pos in
  let () = x_binfo_hp (add_str "POST" pr_formula) post no_pos in
  let aux_bf hf1 hf2 goal f_var1 f_var2 =
    let var_list = goal.gl_vars in
    let prog = goal.gl_prog in
    match hf1, hf2 with
    | CF.DataNode dnode1, CF.DataNode dnode2 ->
      choose_rule_field_dnode dnode1 dnode2 cur_var goal
    | CF.DataNode dnode, CF.ViewNode vnode ->
      let () = x_binfo_pp "ViewNode case" no_pos in
      let view_name = vnode.CF.h_formula_view_name in
      let views = prog.Cast.prog_view_decls in
      let n_f2 = do_unfold_view_vnode prog f_var2 in
      let () = x_binfo_hp (add_str "n_f2" (pr_list pr_formula)) n_f2 no_pos in
      let case_rules case =
        let n_goal = {goal with gl_post_cond = case} in
        choose_rassign_data cur_var n_goal in
      let rules = n_f2 |> List.map case_rules |> List.concat in
      let () = x_binfo_hp (add_str "cases rules" pr_rules) rules no_pos in
      rules
    | _ -> [] in
  let aux f_var1 f_var2 goal =
    let var_list = goal.gl_vars in
    let field_rules = match f_var1, f_var2 with
      | CF.Base bf1, CF.Base bf2 ->
        let hf1 = bf1.CF.formula_base_heap in
        let hf2 = bf2.CF.formula_base_heap in
        aux_bf hf1 hf2 goal f_var1 f_var2
      | CF.Base bf1, CF.Exists bf2 ->
        let hf1 = bf1.CF.formula_base_heap in
        let hf2 = bf2.CF.formula_exists_heap in
        aux_bf hf1 hf2 goal f_var1 f_var2
      | _ -> [] in
    field_rules in
  match pre, post with
  | CF.Base _, CF.Base _
  | CF.Base _, CF.Exists _
  | CF.Exists _, CF.Base _
  | CF.Exists _, CF.Exists _ ->
    let f_var1 = extract_var_f pre cur_var in
    let f_var2 = extract_var_f post cur_var in
    if f_var1 != None && f_var2 != None then
      let f_var1 = Gen.unsome f_var1 in
      let f_var2 = Gen.unsome f_var2 in
      let () = x_binfo_hp (add_str "fvar1" pr_formula) f_var1 no_pos in
      let () = x_binfo_hp (add_str "fvar2" pr_formula) f_var2 no_pos in
      aux f_var1 f_var2 goal
    else []
  | CF.Base _, CF.Or disjs ->
    let f1 = disjs.CF.formula_or_f1 in
    let f2 = disjs.CF.formula_or_f2 in
    let goal1 = {goal with gl_post_cond = f1} in
    let goal2 = {goal with gl_post_cond = f2} in
    let rule1 = choose_rassign_data cur_var goal1 in
    let rule2 = choose_rassign_data cur_var goal2 in
    rule1@rule2
  | _ -> []

let frame_var var formula prog = match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let rec helper hf = match hf with
      | CF.DataNode dnode ->
        let dnode_var = dnode.CF.h_formula_data_node in
        if CP.eq_spec_var dnode_var var then
          let args = dnode.CF.h_formula_data_arguments in
          let data_name = dnode.CF.h_formula_data_name in
          let data_decls = prog.Cast.prog_data_decls in
          let data = List.find (fun x -> x.Cast.data_name = data_name)
              data_decls in
          let data_fields = data.Cast.data_fields |> List.split |> fst in
          let args_w_fields = List.combine args data_fields in
          let args_w_fields = List.filter (fun (x,y) -> is_named_type_var x)
              args_w_fields in
          (CF.HEmp, args_w_fields)
        else (hf, [])
      | CF.Star sf ->
        let n_f1, vars1 = helper sf.CF.h_formula_star_h1 in
        let n_f2, vars2 = helper sf.CF.h_formula_star_h2 in
        (Star {sf with h_formula_star_h1 = n_f1;
                      h_formula_star_h2 = n_f2}, vars1@vars2)
      | _ -> (hf, []) in
    let n_hf, vars = helper hf in
    (CF.Base {bf with formula_base_heap = n_hf}, vars)
  | _ -> (formula, [])

let choose_rule_assign goal : rule list =
  let vars = goal.gl_vars in
  let pr_sv = Cprinter.string_of_spec_var in
  let () = x_tinfo_hp (add_str "vars: " (pr_list pr_sv)) vars no_pos in
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  (* let n_post = process_exists_var pre post in *)
  (* let goal = {goal with gl_post_cond = n_post} in *)
  let choose_rule var = match CP.type_of_sv var with
    | Int -> choose_rassign_pure var goal
    | Named _ ->
      choose_rassign_data var goal
    | _ -> let () = x_binfo_pp "marking \n" no_pos in
      []  in
  let rules = List.map choose_rule vars in
  List.concat rules

(*********************************************************************
 * Choose function call rules
 *********************************************************************)
let get_hf (f:CF.formula) = match f with
  | Base bf -> bf.formula_base_heap
  | Exists bf -> bf.formula_exists_heap
  | Or _ -> report_error no_pos "get_hf unhandled"

let check_same_shape (f1:CF.formula) (f2:CF.formula) =
  let check_hf hf1 hf2 =
    match hf1, hf2 with
    | HEmp, HEmp
    | DataNode _, DataNode _
    | ViewNode _, ViewNode _ -> true
    | _ -> false in
  let hf1,hf2 = get_hf f1, get_hf f2 in
  check_hf hf1 hf2

let check_same_shape_pair (pre_f, post_f) (pre_proc, post_proc) =
  (check_same_shape pre_f pre_proc) && (check_same_shape post_f post_proc)

let find_substs (f1:CF.formula) (f2:CF.formula) =
  let () = x_binfo_hp (add_str "f1" pr_formula) f1 no_pos in
  let () = x_binfo_hp (add_str "f2 " pr_formula) f2 no_pos in
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
  let a_pre, a_post = arg |> extract_var_f pre_proc,
                      arg |> extract_var_f post_proc in
  let l_pre, l_post = lvar |> extract_var_f pre_cond,
                      lvar |> extract_var_f post_cond in
  match a_pre, l_pre with
  | Some apre_f, Some lpre_f ->
    check_same_shape apre_f lpre_f
  | _ -> false

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

let rec filter_args_input (args:CP.spec_var list list) = match args with
  | [] -> []
  | [h] -> List.map (fun x -> [x]) h
  | h::t -> let tmp = filter_args_input t in
    let head_added = List.map (fun x -> List.map (fun y -> [x]@y) tmp) h in
    List.concat head_added

let unify (pre_proc, post_proc) goal =
  let proc_decl = goal.gl_proc_decls |> List.hd in
  let args = proc_decl.Cast.proc_args |>
             List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let unify_var arg goal =
    let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
    let arg_typ = CP.type_of_sv arg in
    let l_vars = CF.fv pre_cond |>
                 List.filter (fun x -> CP.type_of_sv x = arg_typ) in
    let ss_vars = List.filter (fun lvar -> unify_pair arg lvar goal proc_decl) l_vars in
    let () = x_binfo_hp (add_str "arg" pr_var) arg no_pos in
    let () = x_binfo_hp (add_str "arg vars" pr_vars) ss_vars no_pos in
    ss_vars in
  let ss_args = args |> List.map (fun arg -> unify_var arg goal) in
  let () = x_binfo_hp (add_str "tuple before" (pr_list pr_vars)) ss_args no_pos in
  let ss_args = filter_args_input ss_args in
  let ss_args = List.filter(fun list ->
      let n_list = CP.remove_dups_svl list in
      List.length n_list = List.length list
    ) ss_args in
  let () = x_binfo_hp (add_str "tuple" (pr_list pr_vars)) ss_args no_pos in
  if ss_args != [] then
    ss_args |> List.map (fun args ->
        let fc_rule = RlFuncCall {
            rfc_func_name = proc_decl.Cast.proc_name;
            rfc_params = args;
          } in
        [fc_rule]
      ) |> List.concat
  else []

let choose_func_call goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let procs = goal.gl_proc_decls in
  if procs = [] then []
  else
    let proc_decl = List.hd procs in
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let () = x_tinfo_hp (add_str "specs" pr_struc_f) specs no_pos in
    let pre_cond = specs |> get_pre_cond |> rm_emp_formula in
    let () = x_binfo_hp (add_str "pre_cond " pr_formula) pre_cond no_pos in
    let post_cond = specs |> get_post_cond |> rm_emp_formula in
    let () = x_binfo_hp (add_str "post_cond " pr_formula) post_cond no_pos in
    let rules = unify (pre_cond, post_cond) goal in
    rules

let choose_rule_rbind goal =
  let vars, pre_cond = goal.gl_vars, goal.gl_pre_cond in
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
  let () = x_binfo_hp (add_str "triples" pr_triples) triples no_pos in
  let helper_triple (var, data, args) =
    let prog = goal.gl_prog in
    let data = List.find (fun x -> x.Cast.data_name = data)
        prog.Cast.prog_data_decls in
    let d_args = data.Cast.data_fields |> List.map fst in
    let d_arg_pairs = List.combine args d_args in
    let helper_arg (arg, field) = let arg_f = extract_var_f pre_cond arg in
      match arg_f with
      | None -> []
      | Some arg_f -> if CF.is_emp_formula arg_f then []
        else let rbind = RlBind {
            rb_bound_var = var;
            rb_field = field;
            rb_other_var = arg;
            rb_write = false;
          } in [rbind] in
    d_arg_pairs |> List.map helper_arg |> List.concat in
  let rules = List.map helper_triple triples |> List.concat in
  let () = x_tinfo_hp (add_str "rbind rules" (pr_list pr_rule)) rules no_pos in
  rules

let choose_synthesis_rules goal : rule list =
  (* let rs = choose_rule_assign goal in
   * let rs = List.filter not_identity_assign_rule rs in *)
  (* let rs = choose_func_call goal in *)
  let rs = choose_rule_rbind goal in
  rs

let split_hf (f: CF.formula) = match f with
  | Base bf -> let hf = bf.CF.formula_base_heap in
    let rec helper hf =
      match hf with
      | CF.DataNode dnode ->
        [(dnode.CF.h_formula_data_node, hf)]
      | CF.ViewNode vnode ->
        [(vnode.CF.h_formula_view_node, hf)]
      | CF.Star sf ->
        let f1 = helper sf.CF.h_formula_star_h1 in
        let f2 = helper sf.CF.h_formula_star_h2 in
        f1@f2
      | _ -> []
    in helper hf
  | _ -> []

(*********************************************************************
 * Processing rules
 *********************************************************************)
let process_rule_assign goal rassign =
  let pre = goal.gl_pre_cond in
  let lhs = rassign.ra_lhs in
  let rhs = rassign.ra_rhs in
  let res_var = CP.mkRes (CP.type_of_sv lhs) in
  let n_rhs = CP.mkEqExp (CP.mkVar res_var no_pos) (CP.mkVar rhs no_pos) no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_rhs pre in
  let tmp_lhs = CP.fresh_spec_var lhs in
  let n_post = CF.subst [(lhs, tmp_lhs); (res_var, lhs)] n_pre in
  let () = x_binfo_hp (add_str "post_cond " pr_formula) n_post no_pos in
  let ent_check, _ = Songbird.check_entail goal.gl_prog n_post goal.gl_post_cond in
  match ent_check with
  | true -> mk_derivation_success goal (RlAssign rassign)
  | false -> mk_derivation_fail goal (RlAssign rassign)
    (* let post = goal.gl_post_cond in
     * let sub_goal = mk_goal goal.gl_prog n_post post goal.gl_vars in
     * mk_derivation_sub_goals goal (RlAssign rassign) [sub_goal] *)

let subs_bind_write formula var field new_val data_decls =
  match formula with
  | Base bf ->
    let hf = bf.CF.formula_base_heap in
    let () = x_binfo_hp (add_str "hf" Cprinter.string_of_h_formula) hf no_pos in
    let rec helper hf =
      match hf with
      | DataNode dnode ->
        let data_var = dnode.h_formula_data_node in
        let () = x_binfo_hp (add_str "hf" Cprinter.string_of_h_formula) hf
            no_pos in
        if CP.eq_spec_var data_var var then
          let n_dnode = set_field dnode field new_val data_decls in
          (DataNode n_dnode)
        else hf
      | Star sf ->
        let n_h1 = helper sf.CF.h_formula_star_h1 in
        let n_h2 = helper sf.CF.h_formula_star_h2 in
        Star {sf with h_formula_star_h1 = n_h1;
                      h_formula_star_h2 = n_h2}
      | _ -> hf
    in Base {bf with formula_base_heap = helper hf}
  | _ -> formula

let process_rule_wbind goal (wbind:rule_bind) =
  let pre = goal.gl_pre_cond in
  let var = wbind.rb_bound_var in
  let field = wbind.rb_field in
  let rhs = wbind.rb_other_var in
  let prog = goal.gl_prog in
  let data_decls = prog.prog_data_decls in
  let n_post = subs_bind_write pre var field rhs data_decls in
  let () = x_binfo_hp (add_str "after applied:" pr_formula) n_post no_pos in
  let ent_check,_ = Songbird.check_entail goal.gl_prog n_post goal.gl_post_cond in
  match ent_check with
  | true -> mk_derivation_success goal (RlBind wbind)
  | false -> mk_derivation_fail goal (RlBind wbind)

let process_rule_func_call goal rcore : derivation =
  let fname = rcore.rfc_func_name in
  let proc_decl = goal.gl_proc_decls |> List.find (fun x -> x.Cast.proc_name = fname) in
  let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
  let pre_proc = specs |> get_pre_cond |> rm_emp_formula in
  let post_proc = specs |> get_post_cond |> rm_emp_formula in
  let () = x_binfo_hp (add_str "pre_proc" pr_formula) pre_proc no_pos in
  let () = x_binfo_hp (add_str "post proc" pr_formula) post_proc no_pos in
  let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
  let fun_args = proc_decl.Cast.proc_args
                 |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let substs = List.combine fun_args rcore.rfc_params in
  let n_pre_proc = CF.subst substs pre_proc in
  let pre_vars = CF.fv n_pre_proc |> List.filter (fun x ->
      not(List.exists (fun y -> CP.eq_spec_var x y) rcore.rfc_params)) in
  let n_pre_proc = CF.wrap_exists pre_vars n_pre_proc in
  let () = x_binfo_hp (add_str "n_pre_proc" pr_formula) n_pre_proc no_pos in
  let () = x_binfo_hp (add_str "pre_cond" pr_formula) pre_cond no_pos in
  let ent_check, residue = Songbird.check_entail ~residue:true goal.gl_prog
      pre_cond n_pre_proc in
  match ent_check, residue with
  | true, Some red ->
    let () = x_binfo_pp "checking pre_cond successfully" no_pos in
    let () = x_binfo_hp (add_str "residue" pr_formula) red no_pos in
    let n_post_proc = CF.subst substs post_proc in
    let n_post_state = CF.mkStar red n_post_proc CF.Flow_combine no_pos in
    let () = x_binfo_hp (add_str "post_state" pr_formula) n_post_state no_pos in
    let () = x_binfo_hp (add_str "post_cond" pr_formula) post_cond no_pos in
    let post_check, _ = Songbird.check_entail goal.gl_prog n_post_state post_cond in
    if post_check then
      let () = x_binfo_pp "checking post_cond successfully" no_pos in
      mk_derivation_success goal (RlFuncCall rcore)
    else mk_derivation_fail goal (RlFuncCall rcore)
  | _ ->
    mk_derivation_fail goal (RlFuncCall rcore)

let process_one_rule goal rule : derivation =
  match rule with
  | RlFuncCall rcore -> process_rule_func_call goal rcore
  | RlAssign rassign -> process_rule_assign goal rassign
  | RlBind wbind -> process_rule_wbind goal wbind

(*********************************************************************
 * Rule utilities
 *********************************************************************)

(* check useless *)

let is_rule_func_call_useless r =
  (* TODO *)
  false

let is_rule_asign_useless r =
  (* TODO *)
  false

let is_rule_wbind_useless r =
  (* TODO *)
  false

let eliminate_useless_rules goal rules =
  List.filter (fun rule ->
    match rule with
    | RlFuncCall r -> is_rule_func_call_useless r
    | RlAssign r -> is_rule_asign_useless r
    | RlBind r -> is_rule_wbind_useless r) rules

(* compare func_call with others *)

let compare_rule_func_call_vs_func_call r1 r2 =
  (* TODO *)
  PriEqual

let compare_rule_func_call_vs_assign r1 r2 =
  (* TODO *)
  PriEqual

let compare_rule_func_call_vs_wbind r1 r2 =
  (* TODO *)
  PriEqual

let compare_rule_func_call_vs_other r1 r2 =
  match r2 with
  | RlFuncCall r2 -> compare_rule_func_call_vs_func_call r1 r2
  | RlAssign r2 -> compare_rule_func_call_vs_assign r1 r2
  | RlBind r2 -> compare_rule_func_call_vs_wbind r1 r2

(* compare assign with others *)

let compare_rule_assign_vs_func_call r1 r2 =
  negate_priority (compare_rule_func_call_vs_assign r2 r1)

let compare_rule_assign_vs_assign r1 r2 =
  (* TODO *)
  PriEqual

let compare_rule_assign_vs_wbind r1 r2 =
  (* TODO *)
  PriEqual

let compare_rule_assign_vs_other r1 r2 =
  match r2 with
  | RlFuncCall r2 -> compare_rule_assign_vs_func_call r1 r2
  | RlAssign r2 -> compare_rule_assign_vs_assign r1 r2
  | RlBind r2 -> compare_rule_assign_vs_wbind r1 r2

(* compare wbind with others *)

let compare_rule_wbind_vs_func_call r1 r2 =
  negate_priority (compare_rule_func_call_vs_wbind r2 r1)

let compare_rule_wbind_vs_assign r1 r2 =
  negate_priority (compare_rule_assign_vs_wbind r2 r1)

let compare_rule_wbind_vs_wbind r1 r2 =
  (* TODO *)
  PriEqual

let compare_rule_wbind_vs_other r1 r2 =
  match r2 with
  | RlFuncCall r2 -> compare_rule_wbind_vs_func_call r1 r2
  | RlAssign r2 -> compare_rule_wbind_vs_assign r1 r2
  | RlBind r2 -> compare_rule_wbind_vs_wbind r1 r2

(* reordering rules *)

let compare_rule r1 r2 =
  match r1 with
  | RlFuncCall r1 -> compare_rule_func_call_vs_other r1 r2
  | RlAssign r1 -> compare_rule_assign_vs_other r1 r2
  | RlBind r1 -> compare_rule_wbind_vs_other r1 r2

let reorder_rules goal rules =
  let cmp_rule r1 r2 =
    let prio = compare_rule r1 r2 in
    match prio with
    | PriEqual -> 0
    | PriLow -> -1
    | PriHigh -> +1 in
  List.sort cmp_rule rules

(*********************************************************************
 * The search procedure
 *********************************************************************)


let rec synthesize_one_goal goal : synthesis_tree =
  let rules = choose_synthesis_rules goal in
  let rules = eliminate_useless_rules goal rules in
  let rules = reorder_rules goal rules in
  let () = x_binfo_hp (add_str "rules" (pr_list pr_rule)) rules no_pos in
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
    | [] -> mk_synthesis_tree_fail goal atrees "no rule can be applied" in
  process [] rules

and process_conjunctive_subgoals goal rule sub_goals : synthesis_tree =
  (* TODO *)
  mk_synthesis_tree_success goal rule

and process_one_derivation drv : synthesis_tree =
  let goal, rule = drv.drv_goal, drv.drv_rule in
  match drv.drv_kind with
  | DrvStatus false -> mk_synthesis_tree_fail goal [] "unknown"
  | DrvStatus true -> mk_synthesis_tree_success goal rule
  | DrvSubgoals gs -> process_conjunctive_subgoals goal rule gs

(*********************************************************************
 * The main synthesis algorithm
 *********************************************************************)
let exp_to_cast (exp: CP.exp) = match exp with
  | Var (sv, loc) ->
    Cast.Var {
      exp_var_type = CP.type_of_sv sv;
      exp_var_name = CP.name_of_sv sv;
      exp_var_pos = loc
    }
  | IConst (num, loc) ->
    Cast.IConst {
      exp_iconst_val = num;
      exp_iconst_pos = loc;
    }
  | _ -> report_error no_pos "exp_to_cast: not handled"

let synthesize_st_core st =
  let rule = st.stc_rule in
  match rule with
  | RlAssign rassign ->
    let lhs = rassign.ra_lhs in
    let rhs = rassign.ra_rhs in
    let c_exp = exp_to_cast (CP.mkVar rhs no_pos) in
    let assign = Cast.Assign {
        exp_assign_lhs = CP.name_of_sv lhs;
        exp_assign_rhs = c_exp;
        exp_assign_pos = no_pos;
      }
    in Some assign
  | RlBind rbind ->
    let bvar = rbind.rb_bound_var in
    let bfield = rbind.rb_field in
    let rhs = rbind.rb_other_var in
    let typ = CP.type_of_sv rhs in
    let rhs_var = Cast.Var {
        Cast.exp_var_type = CP.type_of_sv rhs;
        Cast.exp_var_name = CP.name_of_sv rhs;
        Cast.exp_var_pos = no_pos;
      } in
    let (typ, f_name) = bfield in
    let body = Cast.Assign {
        Cast.exp_assign_lhs = f_name;
        Cast.exp_assign_rhs = rhs_var;
        Cast.exp_assign_pos = no_pos;
      } in
    let bexp = Cast.Bind {
        exp_bind_type = typ;
        exp_bind_bound_var = (CP.type_of_sv bvar, CP.name_of_sv bvar);
        exp_bind_fields = [bfield];
        exp_bind_body = body;
        exp_bind_imm = CP.NoAnn;
        exp_bind_param_imm = [];
        exp_bind_read_only = false;
        exp_bind_path_id = (-1, "bind");
        exp_bind_pos = no_pos;
      } in
    Some bexp
  | _ -> None

let synthesize_program goal : CA.exp option =
  let st = synthesize_one_goal goal in
  let () = x_binfo_hp (add_str "syn_tree: " pr_st) st no_pos in
  let st_status = get_synthesis_tree_status st in
  match st_status with
  | StValid st_core ->
    let res = synthesize_st_core st_core in
    let () = x_binfo_hp (add_str "res" pr_exp_opt) res no_pos in
    res
  | StUnkn _ -> None
