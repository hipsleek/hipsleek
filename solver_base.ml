#include "xdebug.cppo"

open VarGen

open Globals
open Others
open Stat_global
module DD = Debug
open Exc.GTable
open Cast
open Cformula
open Prooftracer
open Gen.Basic
open Immutable
open Perm
open Mcpure_D
open Mcpure
open Cvutil

module CP = Cpure
module CF = Cformula
module CFU = Cfutil
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher
module VP = Vperm
module CVP = CvpermUtils

(******************************************
   Utilities for existential quantifier elimination:
   - before we were only searching for substitutions of the form v1 = v2 and
   then substitute ex v1. P(v1) --> P(v2)
   - now, we want to be more aggressive and search for substitutions of the form
  v1 = exp2; however, we can only apply these substitutions to the pure part
   (due to the way shape predicates are recorded --> root pointer and args are
  suppose to be spec vars)
   - also check that v1 is not contained in FV(exp2)
 ************************************)

let elim_exists_exp_loop_x (f0 : formula) : (formula * bool) =
  let rec helper f0 =
    match f0 with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      let ef1, flag1 = helper f1 in
      let ef2, flag2 = helper f2 in
      (mkOr ef1 ef2 pos, flag1 && flag2)
    | Base _ -> (f0, false)
    | Exists ({ formula_exists_qvars = qvar :: rest_qvars;
                formula_exists_heap = h;
                formula_exists_pure = p;
                formula_exists_vperm = vp;
                formula_exists_type = t;
                formula_exists_and = a;
                formula_exists_flow = fl;
                formula_exists_pos = pos}) ->
      let fvh = h_fv h in
      if  not(List.exists (fun sv -> CP.eq_spec_var sv qvar) fvh) then
        let st, pp1 = MCP.get_subst_equation_mix_formula p qvar false in
        if List.length st > 0 then
          (* if there exists one substitution -
             actually we only take the first one -> therefore, the list should only have
             one elem *)
          (* basically we only apply one substitution *)
          let one_subst = List.hd st in
          let tmp = mkBase h pp1 vp t fl a pos in
          let new_baref = x_add subst_exp [one_subst] tmp in
          let tmp2 = add_quantifiers rest_qvars new_baref in
          let tmp3, _ = helper tmp2 in
          (tmp3, true)
        else (* if qvar is not equated to any variables, try the next one *)
          let tmp1 = mkExists rest_qvars h p vp t fl a pos in
          let tmp2, flag = helper tmp1 in
          let tmp3 = add_quantifiers [qvar] tmp2 in
          (tmp3, flag)
      else (* anyway it's going to stay in the heap part so we can't eliminate
              --> try eliminate the rest of them, and then add it back to the exist
              quantified vars *)
        let tmp1 = mkExists rest_qvars h p vp t fl a pos in
        let tmp2, flag = helper tmp1 in
        let tmp3 = add_quantifiers [qvar] tmp2 in
        ((push_exists [qvar] tmp3), flag)

    | Exists _ -> report_error no_pos ("Solver.elim_exists: Exists with an empty
  list of quantified variables")
  in helper f0


(* apply elim_exist_exp_loop until no change *)
let elim_exists_exp_loop (f0 : formula) : (formula*bool) =
  let pr_out = (pr_pair Cprinter.string_of_formula string_of_bool) in
  Debug.no_1 "elim_exists_exp_loop"
    Cprinter.string_of_formula pr_out
    elim_exists_exp_loop_x f0

let rec elim_exists_exp_x (f0 : formula) : (formula) =
  let f, flag = elim_exists_exp_loop f0 in
  if flag then (elim_exists_exp_x f)
  else f

let elim_exists_exp (f0 : formula) : (formula) =
  Debug.no_1 "elim_exists_exp"
    Cprinter.string_of_formula Cprinter.string_of_formula
    elim_exists_exp_x f0

(* check whether target appears in rhs *)
(* we need lhs_pure to compute the alias set of target *)
let check_one_target_x prog node (target : CP.spec_var)
    (lhs_pure : MCP.mix_formula) (target_rhs_p : MCP.mix_formula)
    (target_rhs_h : CF.h_formula) (coer_rhs_h : CF.h_formula) rhs_eqset  : bool =
  let lhs_eqns = MCP.ptr_equations_with_null lhs_pure in
  let rhs_eqns = (MCP.ptr_equations_with_null target_rhs_p)@rhs_eqset in
  let lhs_asets = Csvutil.alias_nth 7 (lhs_eqns@rhs_eqns) in
  let lhs_targetasets1 = x_add Csvutil.get_aset lhs_asets target in
  let lhs_targetasets =
    if CP.mem target lhs_targetasets1 then lhs_targetasets1
    else target :: lhs_targetasets1 in
  let n_l_v = CF.get_ptrs target_rhs_h in
  let l = Gen.BList.intersect_eq CP.eq_spec_var lhs_targetasets n_l_v in
  (l!=[])

let check_one_target prog node (target : CP.spec_var)
    (lhs_pure : MCP.mix_formula) (target_rhs_p : MCP.mix_formula)
    (target_rhs_h : CF.h_formula) (coer_rhs_h : CF.h_formula) rhs_eqset  : bool =
  let pr1 = Cprinter.string_of_spec_var in
  let pr2 = Cprinter.string_of_mix_formula in
  let pr3 = Cprinter.string_of_h_formula in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_4 "check_one_target" pr1 pr2 pr3 pr4 string_of_bool
    (fun _ _ _ _ -> check_one_target_x prog node (target : CP.spec_var) (lhs_pure : MCP.mix_formula) (target_rhs_p : MCP.mix_formula) (target_rhs_h : CF.h_formula) (coer_rhs_h : CF.h_formula) rhs_eqset) target target_rhs_p target_rhs_h rhs_eqset

(* this checks if node is being applied a second time with same coercion rule *)
let is_cycle_coer_a (c:coercion_decl) (origs:ident list) : bool =  List.mem
    c.coercion_name origs

let is_cycle_coer (c:coercion_decl) (origs:ident list) : bool =
  Debug.no_2 "is_cycle_coer" Cprinter.string_of_coercion Cprinter.str_ident_list
    string_of_bool is_cycle_coer_a c origs


(* lhs <==> rhs: instantiate any high-order variables in rhs
   Currently assume that only HVar is in the rhs
*)
let match_one_ho_arg_simple_x ((lhs,rhs) : CF.rflow_formula * CF.rflow_formula):
  (CP.spec_var * CF.formula) list =
  let lhs = lhs.CF.rflow_base in
  let rhs = rhs.CF.rflow_base in
  let hvars = CF.extract_hvar_f rhs in
  [List.hd hvars, lhs]

let match_one_ho_arg_simple ((lhs, rhs) : CF.rflow_formula * CF.rflow_formula):
  (CP.spec_var * CF.formula) list =
  let pr_rf = Cprinter.string_of_rflow_formula in
  let pr1 = (pr_pair pr_rf pr_rf) in
  let pr_out = pr_list (pr_pair Cprinter.string_of_spec_var
                          Cprinter.string_of_formula) in
  Debug.no_1 "match_one_ho_arg_simple" pr1 pr_out
    match_one_ho_arg_simple_x (lhs,rhs)

let solve_ineq_b_formula sem_eq memset conseq : Cpure.formula =
  let (pf,il) = conseq in
  match pf with
  | Cpure.Neq (e1, e2, pos) ->
    if (CP.is_var e1) && (CP.is_var e2) then
      let eq = (fun x y -> sem_eq x y) in
      let v1 = CP.to_var e1 in
      let v2 = CP.to_var e2 in
      let discharge = CP.DisjSetSV.is_disj eq memset.Cformula.mem_formula_mset v1 v2 in
      if discharge then
        (* remove the diseq from the conseq *)
        CP.mkTrue no_pos
      else
        (* leave the diseq as it is *)
        CP.BForm(conseq, None)
    else CP.BForm(conseq, None)
  | _ -> CP.BForm(conseq, None)
(* todo: could actually solve more types of b_formulae *)

let solve_ineq_pure_formula_x (ante : Cpure.formula) (memset : Cformula.mem_formula) (conseq : Cpure.formula) : Cpure.formula =
  let eqset = CP.EMapSV.build_eset (CP.pure_ptr_equations ante) in
  let rec helper (conseq : Cpure.formula) =
    match conseq with
    | Cpure.BForm (f, l) -> solve_ineq_b_formula (fun x y -> CP.EMapSV.is_equiv eqset x y) memset f
    | Cpure.And (f1, f2, pos) -> Cpure.And((helper f1), (helper f2), pos)
    | Cpure.AndList b -> Cpure.AndList (map_l_snd helper b)
    | Cpure.Or (f1, f2, l, pos) -> Cpure.mkOr (helper f1) (helper f2) l pos
    | _ -> conseq in
  helper conseq

let solve_ineq_pure_formula (ante : Cpure.formula) (memset : Cformula.mem_formula) (conseq : Cpure.formula) : Cpure.formula =
  Debug.no_3 "solve_ineq_pure_formula "
    (Cprinter.string_of_pure_formula)
    (Cprinter.string_of_mem_formula) 
    (Cprinter.string_of_pure_formula) (Cprinter.string_of_pure_formula)
    (fun ante memset conseq -> solve_ineq_pure_formula_x ante memset conseq ) ante memset conseq

let imply_formula_no_memo_x new_ante new_conseq imp_no memset =
  let new_conseq = solve_ineq_pure_formula new_ante memset new_conseq in
  let res,_,_ = x_add TP.imply_one 31  new_ante new_conseq ((string_of_int imp_no)) false None in
  let () = x_dinfo_pp ("asta6?") no_pos in
  x_dinfo_zp (lazy ("IMP #" ^ (string_of_int imp_no))) no_pos;
  res

let imply_formula_no_memo new_ante new_conseq imp_no memset =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "imply_formula_no_memo" pr pr string_of_bool (fun _ _ -> imply_formula_no_memo_x new_ante new_conseq imp_no memset) new_ante new_conseq

let rec normalize_formula_perm prog f = match f with
  | Or b -> mkOr (normalize_formula_perm prog b.formula_or_f1)
              (normalize_formula_perm prog b.formula_or_f2) b.formula_or_pos
  | Base b -> normalize_base_perm prog f
  | Exists e -> normalize_base_perm prog f

and normalize_base_perm_x prog (f:formula) =
  let rec m_find (f:h_formula list->bool) (l:h_formula list list) = match l with
    | [] -> ([],[])
    | h::t ->
      if (f h) then (h,t) 
      else let r,l = m_find f t in (r,h::l) in
  let rec h_a_grp_f aset l :(h_formula list list) = match l with
    | [] -> []
    | h::t ->
      let v = get_node_var h in
      let a = v::(Csvutil.get_aset aset v) in
      let t = h_a_grp_f aset t in
      let lha, lhna = m_find (fun c-> Gen.BList.mem_eq CP.eq_spec_var
                                 (get_node_var (List.hd c)) a) t in
      (h::lha):: lhna in
  let rec perm_folder (h,l) = match l with
    | v1::v2::[]-> CP.mkEqExp (CP.mkAdd (CP.mkVar v1 no_pos) (CP.mkVar v2 no_pos
                                                             ) no_pos)
                     (CP.mkVar h no_pos) no_pos,[]
    | v1::t->
      let n_e = CP.fresh_perm_var () in
      let rf,rev = perm_folder (n_e,t) in
      let join_fact = CP.mkEqExp (CP.mkAdd (CP.mkVar v1 no_pos)
                                    (CP.mkVar n_e no_pos) no_pos)
          (CP.mkVar h no_pos) no_pos in
      (CP.mkAnd rf join_fact no_pos, n_e::rev)
    | _-> report_error no_pos
            ("perm_folder: must have at least two nodes to merge")	in
  let comb_hlp pos (ih,ip,iqv) l= match l with
    | [] -> report_error no_pos
              ("normalize_frac_heap: must have at least one node in the aliased
  list")
    | h::[] -> (mkStarH h ih pos,ip,iqv)
    | h::dups -> 
      let get_l_perm h = match get_node_perm h with | None -> [] | Some v-> [v] in
      if (List.exists (fun c->get_node_perm c = None)l) then (HFalse,ip,iqv)
      else 
        let n_p_v = CP.fresh_perm_var () in
        let n_h = set_node_perm h (Some (Cpure.Var (n_p_v,no_pos))) in
        let v = get_node_var h in
        let args = v::(get_node_args h) in
        let p,lpr = List.fold_left (fun (a1,a2) c ->
            let lv = (get_node_var c)::(get_node_args c) in
            let lp = List.fold_left2  (fun a v1 v2->
                CP.mkAnd a (CP.mkEqVar v1 v2 pos) pos) a1 args lv in
            (lp,(List.map Cpure.get_var (get_l_perm c))
                @a2)) (ip,(List.map Cpure.get_var (get_l_perm h))) dups in
        let npr,n_e = perm_folder (n_p_v,lpr) in
        let n_h = mkStarH n_h ih pos in
        let npr = CP.mkAnd p npr pos in
        (n_h, npr, n_p_v::n_e@iqv) in
  let comb_hlp_l l f n_simpl_h :formula=
    let (qv, h, p, vp, t, fl, lbl, a, pos) = all_components f in
    let nh,np,qv = List.fold_left (comb_hlp pos) (n_simpl_h,CP.mkTrue pos,qv) l in
    let np =  MCP.memoise_add_pure_N p np in
    mkExists_w_lbl qv nh np vp t fl a pos lbl in

  let f =
    let (qv, h, p, vp, t, fl, a, lbl, pos) = all_components f in
    let aset = Csvutil.comp_aliases p in
    let l1 = split_star_conjunctions h in
    let simpl_h, n_simpl_h =
      List.partition (fun c-> match c with | DataNode _ -> true | _ -> false) l1
    in
    let n_simpl_h = join_star_conjunctions n_simpl_h in
    let h_alias_grp = h_a_grp_f aset simpl_h in
    let f = comb_hlp_l h_alias_grp f n_simpl_h in
    if List.exists (fun c-> (List.length c) >1) h_alias_grp
    then  normalize_formula_perm prog f else f in
  f

and normalize_base_perm prog f =
  let pr  =Cprinter.string_of_formula in
  Debug.no_1 "normalize_base_perm" pr pr (normalize_base_perm_x prog) f

(* returns the list of free vars from the rhs that do not appear in the lhs *)
let fv_rhs (lhs : CF.formula) (rhs : CF.formula) : CP.spec_var list =
  let lhs_fv = (CF.fv lhs) in
  let rhs_fv = (CF.fv rhs) in
  Gen.BList.difference_eq CP.eq_spec_var rhs_fv lhs_fv
(* ---------------------------------------- *)

