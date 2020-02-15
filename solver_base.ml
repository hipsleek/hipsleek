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

let normalize_frac_heap prog h p vp =  (*used after adding back the consumed heap*)
  if !perm=NoPerm then (h, p)
  else if !perm=Bperm then (h, p) (*TODO: this is not applicable to BPERM*)
  else
    let f = normalize_base_perm
        prog (mkBase h p vp TypeTrue (mkTrueFlow ()) [] no_pos) in
    match f with
    | Or _ -> Error.report_error {
        Err.error_loc = no_pos;
        Err.error_text = "normalize_frac_heap: adding the consumed heap should not yield OR"}
    | _ ->
      let (_, h, p, _, _, _, _, _, _) = all_components f in
      (h,p)

let rec normalize_context_perm prog ctx = match ctx with
  | OCtx (c1,c2)-> mkOCtx (normalize_context_perm prog c1)
                     (normalize_context_perm prog c2) no_pos
  | Ctx es -> Ctx{ es with es_formula = normalize_formula_perm prog
                               es.es_formula;}

let rec prune_ctx prog ctx = match ctx with
  | OCtx (c1,c2)-> mkOCtx (prune_ctx prog c1) (prune_ctx prog c2) no_pos
  | Ctx es -> Ctx {es with es_formula = prune_preds prog false es.es_formula}

(*  - count how many int constants are contained in one expression
  - if there are more than 1 --> means that we can simplify further (by
 *  performing the operation) *)
let count_br_specialized prog cl =
  let helper prog h_node = match h_node with
    | ViewNode v ->
      Gen.Profiling.inc_counter "consumed_nodes_counter";
      let vdef = look_up_view_def v.h_formula_view_pos prog.prog_view_decls
          v.h_formula_view_name in
      let i = match v.h_formula_view_remaining_branches with
        | None -> 0
        | Some s -> (List.length vdef.view_prune_branches)-(List.length s) in
      if i>0 then  Gen.Profiling.inc_counter "consumed_specialized_nodes" else ();
      Some h_node
    | _  -> None in
  let f_e_f e = None in
  let f_f e = None in
  let f_h_f e =  helper prog e in
  let f_memo e =  Some e in
  let f_aset e = Some e in
  let f_formula e = Some e in
  let f_b_formula e = Some e in
  let f_exp e = Some e in
  (*let f_fail e = e in*)
  let f_ctx e =
    let f = e.es_formula in
    let _todo_unk = transform_formula (f_e_f,f_f,f_h_f,(f_memo,f_aset, f_formula,
                                                       f_b_formula, f_exp)) f in
    Ctx e in
  let _todo_unk = transform_context f_ctx cl in
  ()

let prune_branch_ctx prog (pt,bctx,oft) =
  let r = prune_ctx prog bctx in
  let () = count_br_specialized prog r in
  (pt,r, oft)

let prune_list_ctx prog ctx = match ctx with
  | SuccCtx c -> SuccCtx (List.map (prune_ctx prog) c)
  | _ -> ctx

let prune_ctx_list prog ctx = List.map (fun (c1,c2)->(c1,List.map (prune_branch_ctx prog) c2)) ctx

(*
 * Trung, delete later:
 *   - This function is used to split the RHS. The split results will be used
 *     to compute actions
 *   - To do acc-fold, maybe need to interfere here
 *)
(* split h into (h1,h2) with one node from h1 and the rest in h2 *)
let split_linear_node_guided_x (vars : CP.spec_var list) (h : h_formula) :
  (h_formula * h_formula) list =
  let rec splitter h1 h2 constr pos =
    let l1 = sln_helper h1 in
    let l2 = sln_helper h2 in
    let l1r = List.map (fun (c1,c2)->(c1,constr c2 h2 pos)) l1 in
    let l2r = List.map (fun (c1,c2)->(c1,constr h1 c2 pos)) l2 in
    l1r@l2r
  and sln_helper h = match h with
    | HTrue -> [(HTrue, HEmp)]
    | HFalse -> [(HFalse, HFalse)]
    | HEmp -> [(HEmp,HEmp)]
    | Hole _ | FrmHole _ -> report_error no_pos "[solver.ml]: Immutability hole
  annotation encountered\n"
    | HRel _
    | ThreadNode _
    | DataNode _
    | ViewNode _  | HVar _ -> [(h,HEmp)] (* TODO:HO *)
    | Conj  h-> splitter h.h_formula_conj_h1 h.h_formula_conj_h2 mkConjH h.h_formula_conj_pos
    | ConjStar h -> splitter h.h_formula_conjstar_h1 h.h_formula_conjstar_h2
                      mkConjStarH h.h_formula_conjstar_pos
    | ConjConj h ->splitter h.h_formula_conjconj_h1 h.h_formula_conjconj_h2
                     mkConjConjH h.h_formula_conjconj_pos 
    | Phase h-> splitter h.h_formula_phase_rd h.h_formula_phase_rw mkPhaseH h.h_formula_phase_pos
    | Star  h-> splitter h.h_formula_star_h1 h.h_formula_star_h2 (fun a b c ->
        mkStarH a b c) h.h_formula_star_pos
    | StarMinus  h-> splitter h.h_formula_starminus_h1 h.h_formula_starminus_h2
                       (fun a b c -> mkStarMinusH a b h.h_formula_starminus_aliasing c 20)
                       h.h_formula_starminus_pos in

  let l = sln_helper h in
  List.filter (fun (c1,_)-> Cformula.is_complex_heap c1) l

let split_linear_node_guided (vars : CP.spec_var list) (h : h_formula) :
  (h_formula * h_formula) list =
  let prh = Cprinter.string_of_h_formula in
  let pr l= String.concat "," (List.map (fun (h1,h2)->"("^(prh h1)^","^(prh h2)
                                                      ^")") l) in
  Debug.no_2 "split_linear_node_guided" Cprinter.string_of_spec_var_list
    Cprinter.string_of_h_formula pr split_linear_node_guided_x vars h

let split_linear_node (h : h_formula) : (h_formula * h_formula) list =
  split_linear_node_guided [] h

let rec discard_uninteresting_constraint (f : CP.formula) (vvars: CP.spec_var list)
  : CP.formula =
  match f with
  | CP.BForm _ ->
    if CP.disjoint (CP.fv f) vvars then (CP.mkTrue no_pos)
    else f
  | CP.And(f1, f2, l) -> CP.mkAnd (discard_uninteresting_constraint f1 vvars)
                           (discard_uninteresting_constraint f2 vvars) l
  | CP.AndList b -> CP.AndList (map_l_snd (fun c-> discard_uninteresting_constraint c vvars) b)
  | CP.Or(f1, f2, lbl, l) -> CP.mkOr (discard_uninteresting_constraint f1 vvars)
                               (discard_uninteresting_constraint f2 vvars) lbl  l
  | CP.Not(f1, lbl, l) -> CP.Not(discard_uninteresting_constraint f1 vvars, lbl, l)
  | _ -> f

(*added 09-05-2008 , by Cristian, checks that after the RHS existential
 *elimination the newly introduced variables will no appear in the residue*)
let rec redundant_existential_check (svs : CP.spec_var list) (ctx0 : context) =
  match ctx0 with
  | Ctx es -> let free_var_list = (fv es.es_formula) in
    begin if (not ( CP.disjoint svs free_var_list)) then
        x_dinfo_zp (lazy ("Some variable introduced by existential elimination where found in the residue")) no_pos end
  | OCtx (c1, c2) ->
    let () = redundant_existential_check svs c1 in
    (redundant_existential_check svs c2)

and elim_exists_pure_formula (f0:CP.formula) =
  match f0 with
  | CP.Exists _ ->
    let sf= x_add TP.simplify_a 11 f0 in
    sf
  | _ -> f0

let elim_exists_pure_formula (f0:CP.formula) =
  match f0 with
  | CP.Exists _ ->
    let sf= x_add TP.simplify_a 11 f0 in
    sf
  | _ -> f0

let  elim_exists_pure_formula_debug (f0:CP.formula) =
  Debug.no_1_opt (fun r -> not(r==f0)) "elim_exists_pure_formula" 
    Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula
    elim_exists_pure_formula f0

(* this method will lift out free conjuncts prior to an elimination
   of existential variables w that were newly introduced;
   r denotes that free variables from f0 that overlaps with w 
*)
let elim_exists_pure_branch_x ?(revflag=false) (w : CP.spec_var list) (f0 :
  CP.formula) pos : CP.formula =
  let r=if (w==[]) then [] else CP.intersect w (CP.fv f0) in
  if (r==[]) then f0
  else
    let lc = CP.split_conjunctions f0 in
    let (fl,bl)=List.partition (fun e -> CP.intersect r (CP.fv e)==[]) lc in
    let be = CP.join_conjunctions bl in
    let f = CP.mkExists r be None pos in
    let sf = x_add TP.simplify_a 2 f  in
    (*remove true constraints, i.e. v=v*)
    let sf = CF.remove_true_conj_pure sf in
    (*remove duplicated conjs*)
    let sf = CF.remove_dupl_conj_eq_pure sf in
    let simplified_f = List.fold_left (fun be e -> CP.mkAnd e be no_pos) sf fl in
    simplified_f

let elim_exists_pure_branch (i:int) (w : CP.spec_var list) (f0 : CP.formula) pos : CP.formula =
  let pf = Cprinter.string_of_pure_formula in
  Debug.no_2 ("elim_exists_pure_branch"^(string_of_int i)) Cprinter.string_of_spec_var_list pf pf 
    (fun w f0 -> elim_exists_pure_branch_x w f0 pos) w f0

(*
  PROBLEM : exists_elim NOT deep enough
  entail_state_elim_exists@1
  entail_state_elim_exists inp1 : es_formula: 
  emp&exists(tmi:n=1+flted_7_12 & mi=min(d,tmi) & mx=max(d,tmx) & 0<((\inf)+
  d) & d<(\inf) & self!=null & ((p=null & flted_7_12=0 & tmi=\inf & (\inf)+
  tmx=0) | (p!=null & 1<=flted_7_12 & tmi<=tmx & 0<((\inf)+tmi))))&
  {FLOW,(19,20)=__norm}[]
  entail_state_elim_exists@1 EXIT out : es_formula: 
  emp&exists(tmi:n=1+flted_7_12 & mi=min(d,tmi) & mx=max(d,tmx) & 0<((\inf)+
  d) & d<(\inf) & self!=null & ((p=null & flted_7_12=0 & tmi=\inf & (\inf)+
  tmx=0) | (p!=null & 1<=flted_7_12 & tmi<=tmx & 0<((\inf)+tmi))))&
  {FLOW,(19,20)=__norm}[]
*)
let entail_state_elim_exists_x es =
  let pr_f = Cprinter.string_of_formula in
  let _pr_h = Cprinter.string_of_h_formula in
  let ff = es.es_formula in
  let f_prim = elim_exists_es_his ff in
  (* we also try to eliminate exist vars for which a find a substitution of the
  form v = exp from the pure part *)
  (* EXAMPLE
     @5! f(b4 elim_exists_es_his):
     (exists mi_15: x::cell<mi_15>@M[Orig]&mi_15=v&{FLOW,(19,20)=__norm})[]
     @5! f(b4 elim_exists_es_his):
     x::cell<v>@M[Orig]&true&{FLOW,(19,20)=__norm}[]
  *)
  x_tinfo_hp (add_str "XXX f(before) elim_exists_es_his)" pr_f) ff no_pos;
  x_tinfo_hp (add_str "XXX f(after) elim_exists_es_his)" pr_f) f_prim no_pos;
  let f =
    (* TNT: Do not eliminate exists when doing TNT inference *)
    if es.es_infer_obj # is_term then
      let tuid_fv = collect_term_ann_fv f_prim in
      let ex_tuid_fv = Gen.BList.difference_eq CP.eq_spec_var tuid_fv (fv f_prim) in
      let nf = pop_exists ex_tuid_fv f_prim in
      let elim_ex_nf = elim_exists_exp nf in
      push_exists ex_tuid_fv elim_ex_nf
    else elim_exists_exp f_prim
  in
  let qvar, base = CF.split_quantifiers f in
  let h, p, vp, fl, t, a = CF.split_components base in
  let simpl_p =
    if !Globals.simplify_pure then
      MCP.simpl_memo_pure_formula simpl_b_formula simpl_pure_formula p (x_add TP.simplify_a 1)
    else p in
  let simpl_fl = fl in
  let simpl_f = CF.mkExists qvar h simpl_p vp t simpl_fl
      (CF.formula_and_of_formula base) (CF.pos_of_formula base) in (*TO CHECK*)
  Ctx{es with es_formula = simpl_f;}   (*assuming no change in cache formula*)

let entail_state_elim_exists es =
  let pr1 = Cprinter.string_of_formula in
  let pr2 es = pr1 es.CF.es_formula in
  let pr3 = Cprinter.string_of_context in
  Debug.no_1 "entail_state_elim_exists" pr2 pr3
    (fun _ -> entail_state_elim_exists_x es) es

