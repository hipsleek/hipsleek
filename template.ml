open Globals
open Gen
open Cpure

module MCP = Mcpure
module CF = Cformula
module C = Cast
module TP = Tpdispatcher
module TU = Tlutils

type term = {
  term_coe: exp;
  term_var: (spec_var * int) list; (* [(x, 2)] -> x^2; [(x, 1), (y, 1)] -> xy *)
}

type solver_res =
  | Unsat
  | Sat of (string * int) list
  | Unknown
  | Aborted

type solver = 
  | Z3
  | Clp
  | LPSolve
  | Glpk

let lp_solver = ref Z3

let set_solver solver_name =
  if solver_name = "clp" then lp_solver := Clp
  else if solver_name = "lps" then lp_solver := LPSolve
  else if solver_name = "glpk" then lp_solver := Glpk
  else lp_solver := Z3

let print_term (t: term) =
  List.fold_left (fun s (v, d) -> s ^ "*" ^ 
    (!print_sv v) ^ "^" ^ (string_of_int d)) 
    ("(" ^ (!print_exp t.term_coe) ^ ")") t.term_var

(* Stacks of generated constraints and the unknown vars of templates *)
let templ_constr_stk: formula Gen.stack = new Gen.stack

let templ_unknown_var_stk: spec_var Gen.stack = new Gen.stack

(* Stack for SLEEK generation per scc *)
let templ_sleek_scc_stk: (spec_var list * formula * formula) Gen.stack = new Gen.stack

(* Stack for SLEEK generation whole program *)
let templ_sleek_stk: string Gen.stack = new Gen.stack

(* Stack of template assumption per scc *)
let templ_assume_scc_stk: (formula * formula) Gen.stack = new Gen.stack

type simpl_templ_assume = {
  ass_vars: spec_var list;
  ass_ante: term list list;
  ass_cons: formula;
  ass_orig_ante: formula;
  ass_orig_cons: formula;
  ass_pos: loc;
}

(* Stack of simplified template assumption per scc *)
let simpl_templ_assume_scc_stk: simpl_templ_assume Gen.stack = new Gen.stack 

let rec print_term_list (tl: term list) =
  match tl with
  | [] -> ""
  | t::[] -> print_term t
  | t::ts -> (print_term t) ^ " + " ^ (print_term_list ts)

(* Functions for normalizing constraints *)
let normalize_ineq (b: b_formula): b_formula =
  let (pf, il) = b in
  let pf = match pf with
  | Lt (e1, e2, pos) -> 
      (* e1 < e2 --> e1 - e2 + 1 <= 0 *)
      mkLte (mkAdd (mkSubtract e1 e2 pos) (mkIConst 1 pos) pos) (mkIConst 0 pos) pos
  | Lte (e1, e2, pos) -> 
      (* e1 <= e2 --> e1 - e2 <= 0 *)
      mkLte (mkSubtract e1 e2 pos) (mkIConst 0 pos) pos
  | Gt (e1, e2, pos) ->
      (* e1 > e2 --> e2 - e1 + 1 <= 0 *)
      mkLte (mkAdd (mkSubtract e2 e1 pos) (mkIConst 1 pos) pos) (mkIConst 0 pos) pos
  | Gte (e1, e2, pos) ->
      (* e1 >= e2 --> e2 - e1 <= 0 *)
      mkLte (mkSubtract e2 e1 pos) (mkIConst 0 pos) pos
  | _ -> pf
  in (pf, il)

let rec normalize_sub (e: exp): exp =
  let f e = match e with
  | Subtract (e1, e2, pos) -> 
      (* e1 - e2 --> e1 + (-1)*e2 *)
      let e1 = normalize_sub e1 in
      let e2 = mkMult (mkIConst (-1) pos) (normalize_sub e2) (pos_of_exp e2) in
      Some (mkAdd e1 e2 pos)
  | _ -> None
  in transform_exp f e

and normalize_mult (e: exp): exp =
  let pr = !print_exp in
  Debug.no_1 "tl_normalize_mult" pr pr normalize_mult_x e

and normalize_mult_x (e: exp): exp =
  let rec helper (e: exp): exp * bool =
    (* Return TRUE means there is a transformation from Mult to Add *)
    let f_e _ e = match e with
    | Mult (e1, e2, pos) ->
      begin match e1 with
      | Add (e11, e12, _) ->
        (* (e11 + e12)*e2 --> e11*e2 + e12*e2 *)
        let e2, _ = helper e2 in
        let e11, _ = helper (mkMult e11 e2 (pos_of_exp e11)) in
        let e12, _ = helper (mkMult e12 e2 (pos_of_exp e12)) in
        Some ((mkAdd e11 e12 pos), true)
      | _ -> 
        begin match e2 with
        | Add (e21, e22, _) ->
          (* e1*(e21 + e22) --> e1*e21 + e1*e22 *)
          let e1, _ = helper e1 in
          let e21, _ = helper (mkMult e1 e21 (pos_of_exp e21)) in
          let e22, _ = helper (mkMult e1 e22 (pos_of_exp e22)) in
          Some ((mkAdd e21 e22 pos), true)
        | _ -> 
          let e1, f1 = helper e1 in
          let e2, f2 = helper e2 in
          if f1 || f2 then Some (helper (mkMult e1 e2 pos))
          else Some (e, false)
        end 
      end
    | _ -> None
    in 
    let f_a arg _ = arg in
    let f_c cl = List.fold_left (fun a c -> a || c) false cl in
    trans_exp e () f_e f_a f_c 
  (* 
  and helper (e: exp): exp * bool =
    let pr = !print_exp in
    Debug.no_1 "normalize_mult_helper" pr (pr_pair pr string_of_bool)
    helper_x e
  *)
  in fst (helper e)

(* 2*z*3 --> 6*z *) 
and normalize_const_mult (el: exp list) pos: exp list =
  let pr = pr_list !print_exp in
  Debug.no_1 "tl_normalize_const_mult" pr pr 
  (fun _ -> normalize_const_mult_x el pos) el

and normalize_const_mult_x (el: exp list) pos: exp list =
  let cl, el = List.partition is_int el in
  let c = List.fold_left (fun a c -> a * (to_int_const c Ceil)) 1 cl in
  (mkIConst c pos)::el

and normalize_const_add (el: exp list) pos: exp list =
  let cl, el = List.partition is_int el in
  let c = List.fold_left (fun a c -> a + (to_int_const c Ceil)) 0 cl in
  (mkIConst c pos)::el

and mkTerm coes vars = 
  let vars_w_deg = List.fold_left (fun a v ->
    try
      let v_deg = List.assoc v a in
      (v, v_deg + 1)::(List.remove_assoc v a)
    with Not_found -> (v, 1)::a
  ) [] vars in 
  let vars_w_deg = List.sort (fun (v1, d1) (v2, d2) ->
    let n_comp = String.compare (name_of_spec_var v1) (name_of_spec_var v2) in
    if n_comp == 0 then d1 - d2 else n_comp) vars_w_deg in
  { term_coe = coes;
    term_var = vars_w_deg; }

and split_add (e: exp): exp list =
  match e with 
  | Add (e1, e2, _) -> (split_add e1) @ (split_add e2)
  | _ -> [e]

and split_mult (e: exp): exp list =
  match e with
  | Mult (e1, e2, _) -> (split_mult e1) @ (split_mult e2)
  | _ -> [e]

and term_of_mult_exp svl (e: exp): term =
  let pos = pos_of_exp e in
  let el = split_mult e in
  let cl, el = List.partition is_int el in
  let vl, vcl = List.partition (fun e -> Gen.BList.subset_eq eq_spec_var (afv e) svl) el in
  let vl = List.concat (List.map afv vl) in
  let c = List.fold_left (fun a c -> a * (to_int_const c Ceil)) 1 cl in
  let coe = List.fold_left (fun a vc -> mkMult a vc pos) (mkIConst c pos) vcl in
  mkTerm coe vl

and is_same_degree (t1: term) (t2: term): bool =
  let pr = print_term in
  Debug.no_2 "tl_is_same_degree" pr pr string_of_bool
    is_same_degree_x t1 t2

and is_same_degree_x (t1: term) (t2: term): bool =
  let d1 = t1.term_var in
  let d2 = t2.term_var in
  (* d1 and d2 are sorted *)
  let rec helper (d1: (spec_var * int) list) (d2: (spec_var * int) list) =
    match d1, d2 with
    | [], [] -> true
    | (v1, d1)::ds1, (v2, d2)::ds2 -> 
        if (eq_spec_var v1 v2) && (d1 == d2) then helper ds1 ds2 else false
    | _ -> false
  in helper d1 d2 

and merge_term_list (tl: term list) deg pos: term =
  let coes = List.map (fun t -> t.term_coe) tl in
  let cl, vcl = List.partition is_int coes in
  let c = List.fold_left (fun a c -> a + (to_int_const c Ceil)) 0 cl in
  let coe = match vcl with
  | [] -> mkIConst c pos
  | vc::vcs -> 
    if c == 0 then List.fold_left (fun a vc -> mkAdd a vc pos) vc vcs
    else List.fold_left (fun a vc -> mkAdd a vc pos) (mkIConst c pos) vcl in
  { term_coe = coe; term_var = deg; }

(* Syntactic check only *)
and is_zero_exp (e: exp) =
  match e with
  | IConst (0, _) -> true
  | Mult (e1, e2, _) -> (is_zero_exp e1) || (is_zero_exp e2)
  | Div (e1, _, _) -> is_zero_exp e1
  | Add (e1, e2, _) -> (is_zero_exp e1) && (is_zero_exp e2)
  | Subtract (e1, e2, _) -> (is_zero_exp e1) && (is_zero_exp e2)
  | _ -> false

and remove_zero_term (tl: term list): term list =
  List.filter (fun t -> not (is_zero_exp t.term_coe)) tl

and partition_term_list (tl: term list) pos: term list =
  let merged_tl = match tl with
  | [] -> []
  | t::ts -> 
    let t_same, t_notsame = List.partition (fun tm -> is_same_degree t tm) ts in
    (merge_term_list (t::t_same) t.term_var pos)::(partition_term_list t_notsame pos)
  in remove_zero_term merged_tl

and restore_mult_add (el: exp list list) pos: exp =
  let restore_mult (el: exp list): exp =
    match el with
    | [] -> mkIConst 1 pos
    | e::es -> List.fold_left (fun a e -> mkMult a e pos) e es
  in
  let restore_add (el: exp list): exp = 
    match el with
    | [] -> mkIConst 0 pos
    | e::es -> List.fold_left (fun a e -> mkAdd a e pos) e es 
  in restore_add (List.map restore_mult el)

and exp_of_var_deg (v, d) pos =
  match d with
  | 0 -> mkIConst 1 pos
  | 1 -> mkVar v pos
  | _ -> mkMult (mkVar v pos) (exp_of_var_deg (v, d-1) pos) pos

and exp_of_term (t: term) pos: exp =
  let vl = List.map (fun vd -> exp_of_var_deg vd pos) t.term_var in
  List.fold_left (fun a v -> mkMult a v pos) t.term_coe vl

and exp_of_term_list (tl: term list) pos: exp = 
  match tl with
  | [] -> mkIConst 0 pos
  | t::ts -> List.fold_left (fun a t -> 
      mkAdd a (exp_of_term t pos) pos) (exp_of_term t pos) ts

(* svl is the list of variables, it is used 
 * to distinguish the list of unknowns *)
and term_list_of_exp svl (e: exp): term list =
  let pos = pos_of_exp e in

  let e = normalize_sub e in
  let e = normalize_mult e in
  
  let el = split_add e in
  let tl = List.map (fun e -> term_of_mult_exp svl e) el in
  partition_term_list tl (pos_of_exp e)

and normalize_arith_exp (e: exp): exp =
  let tl = term_list_of_exp (afv e) e in
  exp_of_term_list tl (pos_of_exp e)

and is_arith_exp (e: exp): bool =
  let f_e e = match e with
  | Null _
  | Var _ 
  | IConst _
  | FConst _ -> Some true
  | Add _
  | Subtract _ 
  | Mult _
  | Div _ -> None
  | _ -> Some false in
  let f_c bl = List.for_all (fun b -> b) bl in
  fold_exp e f_e f_c

and normalize_exp (e: exp): exp =
  if (is_arith_exp e) then normalize_arith_exp e
  else e

let normalize_b_formula (b: b_formula): b_formula =
  let b = normalize_ineq b in
  let f_e e = Some (normalize_exp e) in
  transform_b_formula (nonef, f_e) b

let normalize_b_formula (b: b_formula): b_formula =
  let pr = !print_b_formula in
  Debug.no_1 "tl_normalize_b_formula" pr pr normalize_b_formula b

let find_eq_subst_exp svl (f: formula): (spec_var * exp) option =
  match f with
  | BForm (bf, _) -> (match bf with
    | Eq (e1, e2, pos), _ -> 
      if (is_arith_exp e1) && (is_arith_exp e2) then
        let tl = term_list_of_exp svl (mkSubtract e1 e2 pos) in
        let eq_vars, eq_exp = List.fold_left (fun (a1, a2) t ->
          match t.term_var with
          | (v, 1)::[] -> begin match t.term_coe with
            | IConst (1, _) -> (a1 @ [(v, true, t)], a2)
            | IConst (-1, _) -> (a1 @ [(v, false, t)], a2)
            | _ -> (a1, a2 @ [t])
            end
          | _ -> (a1, a2 @ [t])
        ) ([], []) tl in
        match eq_vars with
        | [] -> None
        | (v, sign, _)::vs -> 
          let eq_v_term = (List.map (fun (_, _, t) -> t) vs) @ eq_exp in
          let eq_v_exp = exp_of_term_list eq_v_term pos in
          if not sign then Some (v, eq_v_exp)
          else Some (v, mkSubtract (mkIConst 0 pos) eq_v_exp pos) 
      else None
    | _ -> None)
  | _ -> None

let find_eq_subst_formula svl (f: formula): formula * (spec_var * exp) list =
  let fl = split_conjunctions f in
  let fl, subst = List.fold_left (fun (fa, sa) f ->
    match find_eq_subst_exp svl f with
    | None -> (fa @ [f], sa)
    | Some s -> (fa, sa @ [s])) ([], []) fl in
  let subst = List.map (fun (v, e) -> (v, a_apply_par_term subst e)) subst in
  (apply_par_term subst (join_conjunctions fl), subst)

let normalize_formula (f: formula): formula =
  let f_b b = Some (normalize_b_formula b) in
  transform_formula (nonef, nonef, nonef, f_b, nonef) f

let term_list_of_b_formula svl (bf: b_formula): term list =
  let (pf, _) = normalize_ineq bf in
  match pf with
  | Lte (e, IConst (0, _), _) -> term_list_of_exp svl e
  | _ -> []

(* We only support BForm formula here *)  
let term_list_of_formula svl (f: formula): term list =
  match f with
  | BForm (bf, _) -> term_list_of_b_formula svl bf
  | _ -> []

let unk_lambda_sv num =
  let name = List.fold_left (fun a i -> a ^ "_" ^ (string_of_int i)) "lambda" num in
  SpecVar (Int, name, Unprimed)

let collect_unk_constrs (ante: term list) (cons: term list) pos: formula list =
  (* let _ = print_endline ("ANTE: " ^ (print_term_list ante)) in *)
  (* let _ = print_endline ("CONS: " ^ (print_term_list cons)) in *)

  let rem_cons, constrs = List.fold_left (fun (cons, fl) at -> 
    let cons_same_deg, cons_notsame_deg = 
      List.partition (fun t -> is_same_degree t at) cons in
    (* let constr_exp = List.fold_left (fun a ct -> mkAdd a ct.term_coe pos)     *)
    (*   (mkMult (mkIConst (-1) pos) at.term_coe pos) cons_same_deg in           *)
    (* let constr =                                                              *)
    (*   if at.term_var = [] then mkPure (mkLte constr_exp (mkIConst 0 pos) pos) *)
    (*   else mkPure (mkEq constr_exp (mkIConst 0 pos) pos)                      *)
    let a_exp = at.term_coe in
    let c_exp = match cons_same_deg with
    | [] -> mkIConst 0 pos
    | c::cs -> List.fold_left (fun a ct -> mkAdd a ct.term_coe pos) c.term_coe cs
    in
    let constr = mkPure (mkEq a_exp c_exp pos)
      (* if at.term_var = [] then mkPure (mkGte a_exp c_exp pos) *)
      (* else mkPure (mkEq a_exp c_exp pos)                      *)
    in (cons_notsame_deg, fl @ [constr])) (cons, []) ante in
  let rem_constrs = List.map (fun ct -> 
    mkPure (mkEq ct.term_coe (mkIConst 0 pos) pos)) rem_cons in
  constrs @ rem_constrs

let templ_entail_num = ref 0

let infer_template_rhs_farkas num (ante_tl: term list list) (cons_t: term list) pos: formula list =
  let constrs = 
    let ante_w_unks, unks, _ = List.fold_left (fun (a, unks, i) tl ->
      let unk_lambda = mkVar (unk_lambda_sv (num @ [i])) pos in
      let tl = List.map (fun t -> { t with term_coe = mkMult t.term_coe unk_lambda pos; }) tl in
      (a @ [tl], unks @ [unk_lambda], i+1)) ([], [], 0) ante_tl in
    let ante_sum_t = partition_term_list (List.concat ante_w_unks) pos in
    (List.map (fun unk -> mkPure (mkGte unk (mkIConst 0 pos) pos)) unks) @
    (collect_unk_constrs ante_sum_t cons_t pos) in
  constrs

(* cons is a base formula and cnum is its order in the original consequent *)
let infer_template_rhs num (es: CF.entail_state) (ante: formula) (cons: formula) pos: 
    CF.entail_state * formula list =
  let ante = find_rel_constraints ante (fv cons) in
  let es =  { es with 
    CF.es_infer_templ_assume = es.CF.es_infer_templ_assume @ [(ante, cons)]; } in
  let _ = templ_assume_scc_stk # push (ante, cons) in

  let orig_ante = ante in
  let orig_cons = cons in

  let inf_templs = es.CF.es_infer_vars_templ in
  let ante, ante_unks = trans_formula_templ inf_templs ante in
  let cons, cons_unks = trans_formula_templ inf_templs cons in
  let vars = Gen.BList.difference_eq eq_spec_var 
    ((fv ante) @ (fv cons)) (ante_unks @ cons_unks) in

  let ante, subst = find_eq_subst_formula vars ante in
  let cons = apply_par_term subst cons in
  
  let true_f = mkPure (mkLte (mkIConst (-1) pos) (mkIConst 0 pos) pos) in
  let ante_fl = true_f::(split_conjunctions ante) in
  let ante_tl = List.map (term_list_of_formula vars) ante_fl in
  let cons_t = term_list_of_formula vars (normalize_formula cons) in

  let _ = templ_unknown_var_stk # push_list (ante_unks @ cons_unks) in
  let _ = simpl_templ_assume_scc_stk # push 
    { ass_vars = vars;
      ass_ante = ante_tl;
      ass_cons = cons;
      ass_orig_ante = orig_ante;
      ass_orig_cons = orig_cons;
      ass_pos = pos; } in

  let farkas_contrs = infer_template_rhs_farkas num ante_tl cons_t pos in
  es, farkas_contrs

let infer_template_rhs num (es: CF.entail_state) (ante: formula) (cons: formula) pos: 
    CF.entail_state * formula list =
  let pr1 = !CF.print_entail_state in
  let pr2 = !print_formula in
  let pr3 = pr_list !print_formula in
  Debug.no_3 "infer_template_rhs" pr1 pr2 pr2 (pr_pair pr1 pr3)
    (fun _ _ _ -> infer_template_rhs num es ante cons pos) es ante cons

let exp_of_templ_decl (tdef: C.templ_decl): exp =
  let pos = tdef.C.templ_pos in
  let func_typ = List.fold_right (fun v r_typ -> FuncT (type_of_spec_var v, r_typ))
    tdef.C.templ_params tdef.C.templ_ret_typ in 
  let tid = SpecVar (func_typ, tdef.C.templ_name, Unprimed) in
  let targs = List.map (fun v -> mkVar v pos) tdef.C.templ_params in
  Template {
    templ_id = tid; templ_args = targs; templ_unks = []; 
    templ_body = tdef.C.templ_body; templ_pos = pos; }

let replace_eq_conseq (cons: formula): formula =
  let f_f f = match f with
    | BForm (bf, lbl) -> (match bf with
      | Eq (e1, e2, pos), il -> 
        let f1 = BForm ((Gte (e1, e2, pos), il), lbl) in
        let f2 = BForm ((Lte (e1, e2, pos), il), lbl) in
        Some (mkAnd f1 f2 pos)
      | _ -> Some f)
    | _ -> None 
  in transform_formula (nonef, nonef, f_f, nonef, nonef) cons

let replace_eq_conseq (cons: formula): formula =
  let pr = !print_formula in
  Debug.no_1 "replace_eq_conseq" pr pr replace_eq_conseq cons

let simplify_templ_conseq (should_simpl_untempl: bool) (cons: formula) =
  let cons = replace_eq_conseq cons in
  let cons_l = split_conjunctions cons in
  let cons_l = 
    if not (should_simpl_untempl) then List.filter has_template_formula cons_l 
    else cons_l
  in cons_l

let infer_template_conjunct_rhs num (es: CF.entail_state) (ante: formula) (cons: formula) pos =
  let cons_l = simplify_templ_conseq (has_template_formula ante) cons in
  let es, constrs, _ = List.fold_left (fun (es, ac, cnum) cons ->
    let es, cl = infer_template_rhs (num @ [cnum]) es ante cons pos in
    (es, ac @ cl, cnum+1)) (es, [], 0) cons_l in
  (es, constrs)

let infer_template_conjunct_rhs num (es: CF.entail_state) (ante: formula) (cons: formula) pos =  
  let pr1 = !CF.print_entail_state in
  let pr2 = !print_formula in
  Debug.no_3 "infer_template_conjunct_rhs" pr1 pr2 pr2 (fun (es, _) -> pr1 es)
    (fun _ _ _ -> infer_template_conjunct_rhs num es ante cons pos) es ante cons

let simplify_templ_ante (ante: formula) =
  let ante_l = split_disjunctions_deep ante in
  List.map (fun f -> snd (elim_exists_with_fresh_vars f)) ante_l

let simplify_templ_ante (ante: formula) =
  let pr = !print_formula in
  Debug.no_1 "simplify_templ_ante" pr (pr_list pr)
  simplify_templ_ante ante
  
let infer_template_disjunct_lhs num (es: CF.entail_state) (ante: formula) (cons: formula) pos = 
  let ante_l = simplify_templ_ante ante in
  let es, constrs, _ = List.fold_left (fun (es, ac, anum) ante ->
    let es, cl = infer_template_conjunct_rhs (num @ [anum]) es ante cons pos in
    (es, ac @ cl, anum+1)) (es, [], 0) ante_l in
  (es, constrs)

let infer_template_disjunct_lhs num (es: CF.entail_state) (ante: formula) (cons: formula) pos =  
  let pr1 = !CF.print_entail_state in
  let pr2 = !print_formula in
  Debug.no_3 "infer_template_disjunct_lhs" pr1 pr2 pr2 (fun (es, _) -> pr1 es)
    (fun _ _ _ -> infer_template_disjunct_lhs num es ante cons pos) es ante cons

let infer_template_init (es: CF.entail_state) (ante: formula) (cons: formula) pos =
  let inf_templs = es.CF.es_infer_vars_templ in
  let _ = 
    if !gen_templ_slk then 
      templ_sleek_scc_stk # push (inf_templs, ante, cons)
    else () 
  in
  let es, constrs = infer_template_disjunct_lhs [!templ_entail_num] es ante cons pos in
  templ_entail_num := !templ_entail_num + 1;
  templ_constr_stk # push_list constrs;
  Some es

let infer_template (es: CF.entail_state) (ante: MCP.mix_formula) (cons: formula) pos =
  let pr1 = !MCP.print_mix_formula in
  let pr2 = !print_formula in
  let pr3 = string_of_loc in
  Debug.no_3 "infer_template" pr1 pr2 pr3 (pr_opt !CF.print_entail_state) 
    (fun _ _ _ -> infer_template_init es (MCP.pure_of_mix ante) cons pos) ante cons pos 

let gen_slk_infer_templ_scc () =
  let inp = List.rev (templ_sleek_scc_stk # get_stk) in
  let _ = templ_sleek_stk # reset in

  let out = List.map (fun (templ_vars, ante, cons) ->
    "infer " ^ (!print_svl templ_vars) ^ " " ^ 
    (!print_formula ante) ^ " |- " ^ (!print_formula cons) ^ ".") inp in
  let str = (String.concat "\n\n" out) ^ "\n\ntemplate_solve.\n" in
  templ_sleek_stk # push str

let gen_slk_file prog =
  let file_name_ss = List.hd !Globals.source_files in
  let out_chn =
    let reg = Str.regexp "\.ss" in
    let file_name_slk = "logs/templ_" ^ (Str.global_replace reg ".slk" file_name_ss) in
    let _ = print_endline ("\n Generating sleek file: " ^ file_name_slk) in
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    open_out (file_name_slk)
  in

  let templ_decl_str = (String.concat ".\n" 
    (List.map Cprinter.string_of_templ_decl prog.C.prog_templ_decls)) ^ ".\n"
  in

  let templ_infer_str = String.concat "\n\n" (List.rev (templ_sleek_stk # get_stk)) in
  
  let slk_output = templ_decl_str ^ "\n\n" ^ templ_infer_str in
  let _ = output_string out_chn slk_output in
  let _ = close_out out_chn in
  ()

(********************)
(* MODEL GENERATION *)
(********************)
let rec most_common_nonlinear_vars nl = 
  match nl with
  | [] -> []
  | _ -> 
    let flatten_nl = List.concat nl in
    let app_nl = List.fold_left (fun a v ->
      try
        let v_cnt = List.assoc v a in
        (v, v_cnt + 1)::(List.remove_assoc v a)
      with Not_found -> (v, 1)::a
      ) [] flatten_nl in
    (* List of the most appearance variables *)
    let v, v_cnt = List.hd (List.sort (fun (_, c1) (_, c2) -> c2 - c1) app_nl) in
    let same_v_cnt = List.find_all (fun (_, c) -> c == v_cnt) (List.tl app_nl) in
    let most_common_v = match same_v_cnt with
    | [] -> v
    | _ -> 
      let l_candidate = v::(List.map (fun (v, _) -> v) same_v_cnt) in
      let candidate_rank = List.fold_left (fun a vl ->
        if Gen.BList.subset_eq eq_spec_var vl l_candidate then a
        else 
          let inc_v = Gen.BList.intersect_eq eq_spec_var vl l_candidate in
          List.fold_left (fun a v ->
            try
              let v_rank = List.assoc v a in
              (v, v_rank + 1)::(List.remove_assoc v a)
            with Not_found -> a) a inc_v) 
            (List.map (fun v -> (v, 0)) l_candidate) nl in 
      (* The variable appears in the most other group *)
      let v, _ = List.hd (List.sort (fun (_, c1) (_, c2) -> c2 - c1) candidate_rank) in
      v
    in
    let rm_nl = List.map (fun vl -> List.filter (fun v1 -> not (eq_spec_var most_common_v v1)) vl) nl in
    most_common_v::(most_common_nonlinear_vars (List.filter (fun vl -> (List.length vl) >= 2) rm_nl))

let most_common_nonlinear_vars nl = 
  let pr1 = !print_svl in
  let pr2 = pr_list pr1 in
  Debug.no_1 "most_common_nonlinear_vars" pr2 pr1
  most_common_nonlinear_vars nl

let get_model_z3 is_linear templ_unks vars assertions =
  let res = Smtsolver.get_model is_linear vars assertions in
  match res with
  | Z3m.Unsat -> Unsat
  | Z3m.Sat_or_Unk m ->
    match m with
    | [] -> Unknown
    | _ -> 
      let model = Smtsolver.norm_model (List.filter (fun (v, _) -> 
        List.exists (fun sv -> v = (name_of_spec_var sv)) templ_unks) m) in
      Sat model

let get_model_lp solver is_linear templ_unks vars assertions =
  let res = Lp.get_model solver templ_unks assertions in
  match res with
  | Lp.Sat m -> Sat m
  | Lp.Unsat -> Unsat
  | Lp.Unknown -> Unknown
  | Lp.Aborted -> Aborted

let get_model solver is_linear templ_unks vars assertions =
  match solver with
  | Z3 -> get_model_z3 is_linear templ_unks vars assertions
  | Clp -> get_model_lp Lp.Clp is_linear templ_unks vars assertions
  | Glpk -> get_model_lp Lp.Glpk is_linear templ_unks vars assertions
  | LPSolve -> get_model_lp Lp.LPSolve is_linear templ_unks vars assertions

let get_opt_model is_linear templ_unks vars assertions =
  if is_linear then get_model !lp_solver is_linear templ_unks vars assertions
  else
    (* Linearize constraints *)
    let res = Smtsolver.get_model true vars assertions in
    match res with
    | Z3m.Unsat -> Unsat
    | Z3m.Sat_or_Unk model -> 
      let nl_var_list = List.concat (List.map nonlinear_var_list_formula assertions) in
      let subst_nl_vars = most_common_nonlinear_vars nl_var_list in
      let nl_vars_w_z3m_val = List.map (fun v -> 
        let v_name = name_of_spec_var v in
        List.find (fun (vm, _) -> v_name = vm) model) subst_nl_vars in
      let nl_vars_w_int_val = Smtsolver.norm_model nl_vars_w_z3m_val in
      let sst = List.map (fun v -> 
        let v_name = name_of_spec_var v in
        let v_val = List.assoc v_name nl_vars_w_int_val in
        (v, mkIConst v_val no_pos)) subst_nl_vars in
      let assertions = List.map (fun f -> apply_par_term sst f) assertions in
      (* let res2 = Lp.get_model Lp.LPSolve *)
      (*   (Gen.BList.difference_eq eq_spec_var templ_unks subst_nl_vars) assertions in *)
      (* match res2 with *)
      (* | Lp.Sat model2 -> Sat (nl_vars_w_int_val @ model2) *)
      (* | _ -> *)
      (*   let model = Smtsolver.norm_model (List.filter (fun (v, _) -> *)
      (*     List.exists (fun sv -> v = (name_of_spec_var sv)) templ_unks) model) in *)
      (*   Sat model *)
      let res2 = get_model !lp_solver true 
        (Gen.BList.difference_eq eq_spec_var templ_unks subst_nl_vars) 
        (Gen.BList.difference_eq eq_spec_var vars subst_nl_vars)
        assertions in
      match res2 with
      | Sat model2 -> Sat (nl_vars_w_int_val @ model2)
      | _ -> 
        let model = Smtsolver.norm_model (List.filter (fun (v, _) ->
          List.exists (fun sv -> v = (name_of_spec_var sv)) templ_unks) model) in
        Sat model

let get_model is_linear templ_unks vars assertions =
  get_opt_model is_linear templ_unks vars assertions

let subst_model_to_templ_decls inf_templs templ_unks templ_decls model =
  let unk_subst = List.map (fun v -> 
    let v_val = try List.assoc (name_of_spec_var v) model with _ -> 0 in
    (v, mkIConst v_val no_pos)) templ_unks in
  let inf_templ_decls = match inf_templs with
  | [] -> templ_decls
  | _ -> List.find_all (fun tdef -> List.exists (fun id -> 
      id = tdef.C.templ_name) inf_templs) templ_decls
  in
  let res_templ_decls = List.map (fun tdef -> { tdef with
    C.templ_body = map_opt (fun e -> a_apply_par_term unk_subst e) tdef.C.templ_body; 
  }) inf_templ_decls in
  res_templ_decls

(***************************)
(* LEXICOGRAPHIC INFERENCE *)
(***************************)
exception Lex_Infer_Failure of string 

(* e1 > e2 --> e1 >= 0 *)
let trans_dec_to_bnd_constr (f: formula) =
  let f_b b = 
    let (p, _) = b in match p with
    | Gt (e1, e2, pos) -> Some (Gte (e1, mkIConst 0 (pos_of_exp e2), pos), None)
    | _ -> Some (mkTrue_b (pos_of_b_formula b)) 
  in transform_formula (nonef, nonef, nonef, f_b, nonef) f

(* e1 > e2 --> e1 >= e2 *)
let trans_dec_to_unaff_constr (f: formula) =
  let f_b b = 
    let (p, _) = b in match p with
    | Gt (e1, e2, pos) -> Some (Gte (e1, e2, pos), None)
    | _ -> Some (mkTrue_b (pos_of_b_formula b)) 
  in transform_formula (nonef, nonef, nonef, f_b, nonef) f

let rec powerset l =
  match l with 
  | [] -> [[]]
  | x::xs ->
    let powerset_xs = powerset xs in
    powerset_xs @ (List.map (fun e -> x::e) powerset_xs) 

let powerset l = 
  List.stable_sort (fun l1 l2 -> 
    (List.length l2) - (List.length l1)) (powerset l)

let find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs unaff_constrs =
  let unaff_il, unaff_ctrs = List.split unaff_constrs in
  
  let constrs, _ = List.fold_left (fun (ac, cnum) ta ->
    let cons_t = term_list_of_formula ta.ass_vars (normalize_formula ta.ass_cons) in
    let cl = infer_template_rhs_farkas [cnum] ta.ass_ante cons_t ta.ass_pos in
    (ac @ cl, cnum+1)) ([], 0) (rank_constrs @ unaff_ctrs) in
  if constrs = [] then None
  else
    let unks = Gen.BList.remove_dups_eq eq_spec_var 
      (List.concat (List.map fv constrs)) in
    let res = get_model (List.for_all is_linear_formula constrs) templ_unks unks constrs in
    match res with
    | Sat model -> 
      let res_templ_decls = subst_model_to_templ_decls inf_templs templ_unks prog.C.prog_templ_decls model in
      Some (List.concat (List.map (fun tdef -> 
        fold_opt (fun e -> [e]) tdef.C.templ_body) res_templ_decls), 
        (i, unaff_il))
    | _ -> None

let find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs unaff_constrs =
  let pr_ctr = fun ta -> pr_pair string_of_loc (pr_pair !print_formula !print_formula)
    (ta.ass_pos, (ta.ass_orig_ante, ta.ass_cons)) in
  let pr1 = pr_list pr_ctr in
  let pr2 = pr_list (fun (i, ta) -> (string_of_int i) ^ "@" ^ (string_of_loc ta.ass_pos)) in
  let pr3 = pr_pair string_of_int (pr_list string_of_int) in
  let pr4 = pr_opt (pr_pair (pr_list !print_exp) pr3) in
  Debug.no_2 "find_potential_lex_single_rank" pr1 pr2 pr4
  (fun _ _ -> find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs unaff_constrs)
  rank_constrs unaff_constrs

let find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs unaff_constrs =
  let rec search_rank ls = 
    match ls with
    | [] -> None
    | u::us ->
      let r = find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs u in 
      match r with
      | Some _ -> r
      | None -> search_rank us
  in search_rank (powerset unaff_constrs) 

(* [1; 2; 3] --> [[1; 2; 3]; [2; 3; 1]; [3; 1; 2]] *)
let rec rotate_head_list ls =
  match ls with
  | [] -> []
  | x::xs -> ls::(List.map (fun xs -> xs @ [x]) (rotate_head_list xs))

let find_lex_rank prog inf_templs templ_unks dec_assumes =
  match dec_assumes with
  | [] 
  | _::[] -> raise (Lex_Infer_Failure 
      "Nothing to do with Lexicographic Inference (less than 2 call contexts).")
  | c::cs -> 
    let i, c_templ_assume = c in
    let bnd = trans_dec_to_bnd_constr c_templ_assume.ass_cons in
    let rank = find_potential_lex_single_rank prog inf_templs templ_unks i 
      [c_templ_assume; { c_templ_assume with ass_cons = bnd; }]
      (List.map (fun (i, cs_templ_assume) -> 
        (i, { cs_templ_assume with ass_cons = trans_dec_to_unaff_constr cs_templ_assume.ass_cons; })) cs)
    in match rank with
    | None -> raise (Lex_Infer_Failure 
        "Cannot find a potential ranking function")
    | Some r -> r

let rec sort_rank_list num rank_l =
  if num < 0 then []
  else
    let hd, tl = List.partition (fun (r, (_, unaff_l)) -> 
      (List.length unaff_l) == num) rank_l in
    match hd with
    | [] -> raise (Lex_Infer_Failure 
        "Cannot find suitable lexicographic ranking function")
    | (r, (i, _))::xs -> (* TODO: Backtracking here *) 
      let r_tl = List.map (fun (r, (j, unaff_l)) -> (r, (j, List.filter (fun k -> k != i) unaff_l))) (xs @ tl) in
      r::(sort_rank_list (num-1) r_tl)

(*************************************)
(* CONDITIONAL TERMINATION INFERENCE *)
(*************************************)
type term_status = 
  | Loop
  | Term
  | MayLoop

exception Cond_Infer_Failure of string 

let string_of_term_status = function
  | Loop -> "Loop"
  | Term -> "Term"
  | MayLoop -> "MayLoop"

let get_loop_trans_templ (f: formula) =
  let f_b b = 
    let (p, _) = b in match p with
    | Gt (Template t1, Template t2, _) -> Some [(t1, t2)]
    | _ -> Some []
  in fold_formula f (nonef, f_b, nonef) List.concat

let get_loop_cond_templ_assume (ta: simpl_templ_assume) =
  let dec_cons = ta.ass_orig_cons in
  let src_templ, dst_templ = match (get_loop_trans_templ dec_cons) with
  | (s, d)::[] -> (s, d)
  | _ -> raise (Cond_Infer_Failure "There are more than one decreasing constraints") 
  in
  let fv_call_ctx = List.concat (List.map afv src_templ.templ_args) in 
  let call_ctx = ta.ass_orig_ante in
  let rec_cond = mkExists_with_simpl idf (* TP.simplify *) 
    (Gen.BList.difference_eq eq_spec_var (fv call_ctx) fv_call_ctx) 
    call_ctx None (pos_of_formula call_ctx) in
  (src_templ.templ_id, (fv_call_ctx, rec_cond))

let merge_loop_cond loop_cond_list = 
  match loop_cond_list with
  | [] -> None
  | (id, (sv, rc))::xs ->
    let pos = pos_of_formula rc in
    let rc_xs = List.map (fun (id, (svx, rcx)) -> 
      subst_avoid_capture svx sv rcx) xs in
    Some (id, (sv, TP.hull (List.fold_left (fun a c -> mkOr a c None pos) rc rc_xs)))

let trans_dec_to_loop_cond loop_cond_list (f: formula) = 
  let f_f f =
    match f with
    | BForm (b, _) ->
      let (p, _) = b in begin match p with
      | Gt (Template _, Template t, _) ->
        let sv, loop_cond = List.assoc t.templ_id loop_cond_list in 
        let subs_loop_cond = apply_par_term (List.combine sv t.templ_args) loop_cond in 
        Some subs_loop_cond
      | _ -> Some f end
    | _ -> Some f
  in transform_formula (nonef, nonef, f_f, nonef, nonef) f

let infer_loop_status ctx loop_cond = 
  let imply ante cons = 
    let (r, _, _) = TP.imply_one 0 ante cons "0" true None in r 
  in
  let r1 = imply ctx loop_cond in
  if r1 then Loop
  else 
    let r2 = imply ctx (mkNot loop_cond None (pos_of_formula loop_cond)) in
    if r2 then Term else MayLoop

let infer_loop_template_init prog (templ_assumes: simpl_templ_assume list) = 
  let loop_cond_list = List.map get_loop_cond_templ_assume templ_assumes in
  let grouped_loop_cond = TU.partition_by_assoc eq_spec_var loop_cond_list in
  let merged_loop_cond = List.concat (List.map (fun lc -> 
    fold_opt (fun rc -> [rc]) (merge_loop_cond lc)) grouped_loop_cond) in
  let _ = print_endline ("REC CTX: " ^ (pr_list (fun (id, rc) -> 
    (name_of_spec_var id) ^ ": " ^ (pr_pair !print_svl !print_formula rc)) merged_loop_cond)) in

  let loop_imply_check = List.map (fun ta -> 
    (ta.ass_orig_ante, trans_dec_to_loop_cond merged_loop_cond ta.ass_orig_cons)) templ_assumes in
  let _ = print_endline ("IMPLY: " ^ (pr_list (fun (a, c) -> 
    (pr_pair !print_formula !print_formula (a, c)) ^ " --> " ^
    (string_of_term_status (infer_loop_status a c))) loop_imply_check)) in
  ()

(******************)
(* MAIN FUNCTIONS *)
(******************)  

(* We reuse the term-form of the antecedents 
 * from prior normal termination inference *)
let infer_term_template_init prog (inf_templs: ident list) 
    templ_unks (templ_assumes: simpl_templ_assume list) =
  let dec_templ_assumes = List.filter (fun ta -> is_Gt_formula ta.ass_cons) templ_assumes in
  let num_call_ctx = List.length dec_templ_assumes in
  let _ = print_endline "**** LEXICOGRAPHIC RANK INFERENCE RESULT ****" in

  if num_call_ctx == 1 then begin
    print_endline ("Nothing to do with Lexicographic Inference (only one call context).");
    print_endline ("Trying to infer conditional termination and/or non-termination ...");
    infer_loop_template_init prog dec_templ_assumes
  end
  else try
    let num_dec_templ_assumes, _ = List.fold_left (fun (a, i) dta -> a @ [(i, dta)], i+1) ([], 1) dec_templ_assumes in
    let dec_templ_assumes_l = rotate_head_list num_dec_templ_assumes in
    let rank_l = List.map (find_lex_rank prog inf_templs templ_unks) dec_templ_assumes_l in
    let res = sort_rank_list (num_call_ctx-1) rank_l in
    print_endline (pr_list (pr_list !print_exp) res)
  with Lex_Infer_Failure reason -> 
    print_endline reason;
    print_endline ("Trying to infer conditional termination and/or non-termination ...");
    infer_loop_template_init prog dec_templ_assumes

let collect_and_solve_templ_constrs prog (inf_templs: ident list) = 
  let constrs = templ_constr_stk # get_stk in
  let _ = templ_constr_stk # reset in

  let templ_unks = templ_unknown_var_stk # get_stk in
  let templ_unks = Gen.BList.remove_dups_eq eq_spec_var templ_unks in
  let _ = templ_unknown_var_stk # reset in

  let _ = 
    if !gen_templ_slk then gen_slk_infer_templ_scc () 
    else ()
  in

  let templ_assumes = templ_assume_scc_stk # get_stk in
  let _ = templ_assume_scc_stk # reset in

  let simpl_templ_assumes = List.rev (simpl_templ_assume_scc_stk # get_stk) in
  let _ = simpl_templ_assume_scc_stk # reset in

  let _ = 
    if !print_relassume then
      if templ_assumes = [] then ()
      else begin
        print_endline "**** TEMPLATE ASSUMPTION ****";
        print_endline (pr_list 
          (fun a -> (Cprinter.string_of_templ_assume a) ^ "\n") templ_assumes)
      end
    else ()
  in

  if constrs = [] then ()
  else
    let unks = Gen.BList.remove_dups_eq eq_spec_var 
      (List.concat (List.map fv constrs)) in
    let res = get_model (List.for_all is_linear_formula constrs) templ_unks unks constrs in
    match res with
    | Unsat -> 
      let _ = print_endline ("TEMPLATE INFERENCE: Unsat.") in
      if !Globals.templ_term_inf then
        let _ = print_endline ("Trying to infer lexicographic termination arguments ...") in 
        infer_term_template_init prog inf_templs templ_unks simpl_templ_assumes 
      else ()
    | Sat model ->
      let templ_decls = prog.C.prog_templ_decls in
      let res_templ_decls = subst_model_to_templ_decls inf_templs templ_unks templ_decls model in
      print_endline "**** TEMPLATE INFERENCE RESULT ****";
      print_endline (pr_list Cprinter.string_of_templ_decl res_templ_decls)
    | _ -> print_endline ("TEMPLATE INFERENCE: No result.")



