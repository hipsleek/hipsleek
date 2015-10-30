#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Cpure

(* module C = Cast *)
(* module TP = Tpdispatcher *)
(* module DD = Debug *)

let diff = Gen.BList.difference_eq eq_spec_var
let mem = Gen.BList.mem_eq eq_spec_var
let subset = Gen.BList.subset_eq eq_spec_var
let intersect = Gen.BList.intersect_eq eq_spec_var
let overlap = Gen.BList.overlap_eq eq_spec_var

let pr_formula = Cprinter.string_of_pure_formula
let pr_exp = Cprinter.string_of_formula_exp
let pr_spec_var = Cprinter.string_of_spec_var

let is_sat f = 
  (* Tpdispatcher.is_sat_sub_no 0 f (ref 0)  *)
  let (pr_weak, pr_strong) = drop_complex_ops in
  Omega.is_sat_ops pr_weak pr_strong f ""

(***********************************)
(* PREPROCESSING FOR PURE FORMULAE *)
(***********************************)

(* Functions for normalizing integral constraints *)
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

let normalize_mult (e: exp): exp =
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
    (* and helper (e: exp): exp * bool =                                   *)
    (*   let pr = !print_exp in                                            *)
    (*   Debug.no_1 "normalize_mult_helper" pr (pr_pair pr string_of_bool) *)
    (*   helper_x e                                                        *)
  in fst (helper e)

let normalize_mult (e: exp): exp =
  let pr = !print_exp in
  Debug.no_1 "tl_normalize_mult" pr pr normalize_mult e

(* 2*z*3 --> 6*z *) 
let normalize_const_mult (el: exp list) pos: exp list =
  let cl, el = List.partition is_int el in
  let c = List.fold_left (fun a c -> a * (to_int_const c Ceil)) 1 cl in
  (mkIConst c pos)::el

let normalize_const_mult (el: exp list) pos: exp list =
  let pr = pr_list !print_exp in
  Debug.no_1 "tl_normalize_const_mult" pr pr 
    (fun _ -> normalize_const_mult el pos) el

let normalize_const_add (el: exp list) pos: exp list =
  let cl, el = List.partition is_int el in
  let c = List.fold_left (fun a c -> a + (to_int_const c Ceil)) 0 cl in
  (mkIConst c pos)::el

let restore_mult_add (el: exp list list) pos: exp =
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

(****************************************************)
(* INTERNAL STRUCTURE FOR FARKAS' LEMMA APPLICATION *)
(****************************************************)

type term = {
  term_coe: exp;
  term_var: (spec_var * int) list; (* [(x, 2)] -> x^2; [(x, 1), (y, 1)] -> xy *)
}

type linear_term = {
  linear_term_coe: int;
  linear_term_var: spec_var option;
}

let print_term (t: term) =
  List.fold_left (fun s (v, d) -> s ^ "*" ^ 
                                  (!print_sv v) ^ "^" ^ (string_of_int d)) 
    ("(" ^ (!print_exp t.term_coe) ^ ")") t.term_var

let rec print_term_list (tl: term list) =
  match tl with
  | [] -> ""
  | t::[] -> print_term t
  | t::ts -> (print_term t) ^ " + " ^ (print_term_list ts)

let rec split_add (e: exp): exp list =
  match e with 
  | Add (e1, e2, _) -> (split_add e1) @ (split_add e2)
  | _ -> [e]

let rec split_mult (e: exp): exp list =
  match e with
  | Mult (e1, e2, _) -> (split_mult e1) @ (split_mult e2)
  | _ -> [e]

let mkTerm coes vars = 
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

let term_of_mult_exp svl (e: exp): term =
  let pos = pos_of_exp e in
  let el = split_mult e in
  let cl, el = List.partition is_int el in
  let vl, vcl = List.partition (fun e -> subset (afv e) svl) el in
  let vl = List.concat (List.map afv vl) in
  let c = List.fold_left (fun a c -> a * (to_int_const c Ceil)) 1 cl in
  let coe = List.fold_left (fun a vc -> mkMult a vc pos) (mkIConst c pos) vcl in
  mkTerm coe vl

let rec int_of_exp (e: exp) =
  match e with
  | IConst (i, _) -> i
  | Add (e1, e2, _) -> (int_of_exp e1) + (int_of_exp e2)
  | Subtract (e1, e2, _) -> (int_of_exp e1) - (int_of_exp e2)
  | Mult (e1, e2, _) -> (int_of_exp e1) * (int_of_exp e2)
  | Div (e1, e2, _) -> (int_of_exp e1) / (int_of_exp e2)
  | Max (e1, e2, _) -> 
    let i1 = int_of_exp e1 in
    let i2 = int_of_exp e2 in
    if i1 > i2 then i1 else i2
  | Min (e1, e2, _) -> 
    let i1 = int_of_exp e1 in
    let i2 = int_of_exp e2 in
    if i1 > i2 then i2 else i1
  | _ -> report_error (pos_of_exp e) ("int_of_exp: Unexpected exp " ^ (!print_exp e))

let linear_term_of_term t = 
  let coe = int_of_exp t.term_coe in
  let var = 
    match t.term_var with 
    | [] -> None
    | (v, d)::[] -> 
      if d = 1 then Some v 
      else if d = 0 then None 
      else report_error no_pos ("linear_term_of_term: Unexpected non-linear term " ^ (print_term t))
    | _ -> report_error no_pos ("linear_term_of_term: Unexpected non-linear term " ^ (print_term t))
  in 
  { linear_term_coe = coe; linear_term_var = var }

let exp_of_linear_term t pos = 
  let coe_exp = mkIConst t.linear_term_coe pos in
  match t.linear_term_var with
  | None -> coe_exp
  | Some v -> mkMult coe_exp (mkVar v pos) pos 

let exp_of_linear_term_list tl pos: exp = 
  match tl with
  | [] -> mkIConst 0 pos
  | t::ts -> List.fold_left (fun a t -> 
      mkAdd a (exp_of_linear_term t pos) pos) (exp_of_linear_term t pos) ts

let eq_linear_term_var v1 v2 =
  match v1, v2 with
  | None, None -> true
  | Some v1, Some v2 -> eq_spec_var v1 v2
  | _ -> false

let rec add_linear_terms tl1 tl2 = 
  match tl1 with
  | [] -> tl2
  | t1::rt1 -> 
    try
      let same_t1, rt2 = List.partition (fun t2 -> 
          eq_linear_term_var t1.linear_term_var t2.linear_term_var) tl2 in
      let nt1 = { t1 with 
          linear_term_coe = List.fold_left (fun i t -> i + t.linear_term_coe) t1.linear_term_coe same_t1 }
      in nt1::(add_linear_terms rt1 rt2)
    with _ -> t1::(add_linear_terms rt1 tl2)

let subt_linear_terms ts1 ts2 = 
  add_linear_terms ts1 (List.map (fun t2 -> { t2 with linear_term_coe = -t2.linear_term_coe }) ts2)

(* Syntactic check only *)
let rec is_zero_exp (e: exp) =
  match e with
  | IConst (0, _) -> true
  | Mult (e1, e2, _) -> (is_zero_exp e1) || (is_zero_exp e2)
  | Div (e1, _, _) -> is_zero_exp e1
  | Add (e1, e2, _) -> (is_zero_exp e1) && (is_zero_exp e2)
  | Subtract (e1, e2, _) -> (is_zero_exp e1) && (is_zero_exp e2)
  | _ -> false

let remove_zero_term (tl: term list): term list =
  List.filter (fun t -> not (is_zero_exp t.term_coe)) tl

let is_same_degree (t1: term) (t2: term): bool =
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

let is_same_degree (t1: term) (t2: term): bool =
  let pr = print_term in
  Debug.no_2 "tl_is_same_degree" pr pr string_of_bool
    is_same_degree t1 t2

let merge_term_list (tl: term list) deg pos: term =
  let tl = remove_zero_term tl in
  let coes = List.map (fun t -> t.term_coe) tl in
  let cl, vcl = List.partition is_int coes in
  let c = List.fold_left (fun a c -> a + (to_int_const c Ceil)) 0 cl in
  let coe = match vcl with
    | [] -> mkIConst c pos
    | vc::vcs -> 
      if c == 0 then List.fold_left (fun a vc -> mkAdd a vc pos) vc vcs
      else List.fold_left (fun a vc -> mkAdd a vc pos) (mkIConst c pos) vcl in
  { term_coe = coe; term_var = deg; }

let rec partition_term_list (tl: term list) pos: term list =
  let merged_tl = match tl with
    | [] -> []
    | t::ts -> 
      let t_same, t_notsame = List.partition (fun tm -> is_same_degree t tm) ts in
      (merge_term_list (t::t_same) t.term_var pos)::(partition_term_list t_notsame pos)
  in remove_zero_term merged_tl

(* svl is the list of variables, it is used 
 * to distinguish the list of unknowns *)
let term_list_of_exp svl (e: exp): term list =
  let e = normalize_sub e in
  let e = normalize_mult e in

  let el = split_add e in
  let tl = List.map (fun e -> term_of_mult_exp svl e) el in
  partition_term_list tl (pos_of_exp e)

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

let term_list_of_formula svl (f: formula): term list =
  let pr1 = !print_svl in
  let pr2 = !print_formula in
  let pr3 = print_term_list in
  Debug.no_2 "term_list_of_formula" pr1 pr2 pr3
    term_list_of_formula svl f

let rec exp_of_var_deg (v, d) pos =
  match d with
  | 0 -> mkIConst 1 pos
  | 1 -> mkVar v pos
  | _ -> mkMult (mkVar v pos) (exp_of_var_deg (v, d-1) pos) pos

let exp_of_term (t: term) pos: exp =
  let vl = List.map (fun vd -> exp_of_var_deg vd pos) t.term_var in
  List.fold_left (fun a v -> mkMult a v pos) t.term_coe vl

let exp_of_term_list (tl: term list) pos: exp = 
  match tl with
  | [] -> mkIConst 0 pos
  | t::ts -> List.fold_left (fun a t -> 
      mkAdd a (exp_of_term t pos) pos) (exp_of_term t pos) ts

let rec normalize_exp (e: exp): exp =
  if (is_arith_exp e) then normalize_arith_exp e
  else e

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

let normalize_b_formula (b: b_formula): b_formula =
  let b = normalize_ineq b in
  let f_e e = Some (normalize_exp e) in
  transform_b_formula (nonef, f_e) b

let normalize_b_formula (b: b_formula): b_formula =
  let pr = !print_b_formula in
  Debug.no_1 "tl_normalize_b_formula" pr pr normalize_b_formula b

let normalize_formula (f: formula): formula =
  let f_b b = Some (normalize_b_formula b) in
  transform_formula (nonef, nonef, nonef, f_b, nonef) f

let normalize_eq_formula (f: formula): formula = 
  let f_f f = match f with
    | BForm ((Eq (e1, e2, pos), _), _) ->
      let f1 = mkPure (mkLte e1 e2 pos) in
      let f2 = mkPure (mkLte e2 e1 pos) in
      Some (mkAnd f1 f2 pos)
    | _ -> None
  in transform_formula (nonef, nonef, f_f, nonef, nonef) f

(********************)
(* MODEL GENERATION *)
(********************)
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

let oc_solver = ref false

let rec set_solver solver_name =
  if (Str.first_chars solver_name 1) = "o" then
    (oc_solver := true;
     set_solver (Str.string_after solver_name 1))
  else
  if solver_name = "clp" then lp_solver := Clp
  else if solver_name = "lps" then lp_solver := LPSolve
  else if solver_name = "glpk" then lp_solver := Glpk
  else lp_solver := Z3

let is_z3_solver _ = 
  match !lp_solver with
  | Z3 -> true
  | _ -> false

let print_solver_res = function
  | Unsat -> "Unsat"
  | Sat m -> "Sat" ^ (pr_list (pr_pair idf string_of_int) m)
  | Unknown -> "Unknown"
  | Aborted -> "Aborted"

let is_sat_model r = match r with Sat _ -> true | _ -> false

let is_unsat_model r = match r with Unsat -> true | _ -> false

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
            if subset vl l_candidate then a
            else 
              let inc_v = intersect vl l_candidate in
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
  | Z3m.Unsat _ -> Unsat
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
  let all_vars_assertions = List.concat (List.map fv assertions) in
  let irrel_templ_unks = List.filter (fun v -> 
      not (Gen.BList.mem_eq eq_spec_var v all_vars_assertions)) templ_unks in
  let model = match solver with
    | Z3 -> get_model_z3 is_linear templ_unks vars assertions
    | Clp -> get_model_lp Lp.Clp is_linear templ_unks vars assertions
    | Glpk -> get_model_lp Lp.Glpk is_linear templ_unks vars assertions
    | LPSolve -> get_model_lp Lp.LPSolve is_linear templ_unks vars assertions
  in
  match model with
  | Sat m -> Sat (m @ (List.map (fun v -> (name_of_spec_var v, 0)) irrel_templ_unks))
  | _ -> model

let get_model solver is_linear templ_unks vars assertions =
  let pr1 = !print_svl in
  let pr2 = pr_list !print_formula in
  Debug.no_4 "tl_get_model" string_of_bool pr1 pr1 pr2 print_solver_res
    (get_model solver) is_linear templ_unks vars assertions

let get_opt_model is_linear templ_unks vars assertions =
  if is_linear || is_z3_solver () && !Globals.dis_ln_z3 then 
    get_model !lp_solver is_linear templ_unks vars assertions
  else
    (* Linearize constraints *)
    let res = Smtsolver.get_model true vars assertions in
    match res with
    | Z3m.Unsat _ -> Unsat
    | Z3m.Sat_or_Unk model -> if model = [] then Unknown else 
        let nl_var_list = List.concat (List.map nonlinear_var_list_formula assertions) in
        let subst_nl_vars = most_common_nonlinear_vars nl_var_list in

        (* let () = print_endline ("MOST COMMON NL VARS: " ^ (pr_list pr_spec_var subst_nl_vars)) in         *)
        (* let () = print_endline ("Z3m MODEL: " ^ (pr_list (pr_pair pr_id Z3m.string_of_z3m_val) model)) in *)

        let nl_vars_w_z3m_val = List.map (fun v -> 
            let v_name = name_of_spec_var v in
            List.find (fun (vm, _) -> v_name = vm) model) subst_nl_vars in
        let nl_vars_w_int_val = Smtsolver.norm_model nl_vars_w_z3m_val in
        let sst = List.map (fun v -> 
            let v_name = name_of_spec_var v in
            let v_val = List.assoc v_name nl_vars_w_int_val in
            (v, mkIConst v_val no_pos)) subst_nl_vars in
        let assertions = List.map (fun f -> apply_par_term sst f) assertions in
        (* let res2 = Lp.get_model Lp.LPSolve                                          *)
        (*   (diff templ_unks subst_nl_vars) assertions in                             *)
        (* match res2 with                                                             *)
        (* | Lp.Sat model2 -> Sat (nl_vars_w_int_val @ model2)                         *)
        (* | _ ->                                                                      *)
        (*   let model = Smtsolver.norm_model (List.filter (fun (v, _) ->              *)
        (*     List.exists (fun sv -> v = (name_of_spec_var sv)) templ_unks) model) in *)
        (*   Sat model                                                                 *)
        let res2 = get_model !lp_solver true 
            (diff templ_unks subst_nl_vars) 
            (diff vars subst_nl_vars)
            assertions in
        match res2 with
        | Sat model2 -> Sat (nl_vars_w_int_val @ model2)
        | _ -> 
          let model = Smtsolver.norm_model (List.filter (fun (v, _) ->
              List.exists (fun sv -> v = (name_of_spec_var sv)) templ_unks) model) in
          Sat model

let get_model is_linear templ_unks vars assertions =
  get_opt_model is_linear templ_unks vars assertions

(* a*b*c -> a_b*c -> a_b_c *)
let linearize_nonlinear_formula f = 
  let f_arg arg _ = arg in
  let rec helper (e: exp): exp * (spec_var * exp) list =
    let f_e _ e = 
      match e with
      | Mult (_, _, pos) -> begin
          let el = split_mult e in
          let nel, sst = List.split (List.map helper el) in
          let var_nel, rem_nel = List.fold_left (fun (ve, re) e ->
              match e with 
              | Var (v, _) -> (ve @ [(v, e)], re) 
              | _ -> (ve, re @ [e])) ([], []) nel in
          match var_nel with
          | [] -> Some (List.fold_left (fun a e -> mkMult a e pos) 
                          (List.hd rem_nel) (List.tl rem_nel), List.concat sst)
          | (_, x)::[] -> Some (List.fold_right (fun e a -> mkMult e a pos) 
                                  rem_nel x, List.concat sst)
          (* Nonlinear Mult has more than one variables *)
          | (vx, x)::xs ->
            let vars = List.map fst var_nel in
            let vn = String.concat "_" (List.map name_of_spec_var vars) in
            let v = SpecVar (type_of_spec_var vx, vn, Unprimed) in
            let ve = List.fold_left (fun a e -> mkMult a e pos) x (List.map snd xs) in
            let ne = List.fold_right (fun e a -> mkMult e a pos) rem_nel (mkVar v pos) in
            Some (ne, (v, ve)::(List.concat sst)) end
      | _ -> None
    in trans_exp (normalize_mult e) () f_e f_arg List.concat
  in 
  trans_formula f () (nonef2, nonef2, (fun _ e -> Some (helper e))) 
    (f_arg, f_arg, f_arg) List.concat

let linearize_nonlinear_formula f = 
  let pr1 = !print_formula in
  let pr2 = pr_pair !print_sv !print_exp in
  let pr3 = pr_pair pr1 (pr_list pr2) in
  Debug.no_1 "linearize_nonlinear_formula" pr1 pr3
    linearize_nonlinear_formula f

(* forall x. x >= 0 & y >= 0 -> a*x + b*y + c > 0 --> a >= 0 & b >= 0 & c > 0 *)
let gen_templ_unk_constr (tl: term list): formula =
  if not (List.exists (fun t -> t.term_var = []) tl) then
    mkTrue no_pos
  else
    let templ_unk_constrs = List.map (fun t ->
        let pos = pos_of_exp t.term_coe in
        if t.term_var = [] then mkGt t.term_coe (mkIConst 0 pos) pos
        else mkGte t.term_coe (mkIConst 0 pos) pos) tl in
    mkNot (join_conjunctions (List.map mkPure templ_unk_constrs)) None no_pos

let split ls = 
  let rec helper ls = 
    match ls with
    | [] -> [([], [])]
    | x::xs ->
      let splitted_xs = helper xs in
      List.concat (List.map (fun (s1, s2) -> 
          [(x::s1, s2); (s1, x::s2)]) splitted_xs)
  in 
  List.sort (fun (p1, _) (p2, _) -> (List.length p1) - (List.length p2)) (helper ls)

(* Determine the constraint on nonlinear lambda variable lbd 
 * lbd >= 0 or lbd = 0 or lbd > 0 *)
let partition_nln_vars nln_vars sst asserts =
  let must_be_positive_var v sst asserts =
    (* If v = 0 causes UNSAT *)
    let v_sst = List.filter (fun (_, e) -> mem v (afv e)) sst in
    let zero = mkIConst 0 no_pos in
    let v_zero_sst = List.map (fun (x, _) -> (x, zero)) v_sst in
    let v_zero_sst = (v, zero)::v_zero_sst in
    let v_zero_asserts = List.map (fun f -> apply_par_term v_zero_sst f) asserts in
    let is_sat = is_sat (join_conjunctions v_zero_asserts) in 
    not is_sat
  in
  List.partition (fun v -> must_be_positive_var v sst asserts) nln_vars

(* Only when v is integer (not rational) *)  
let norm_sst_pos vl sst =
  (* (x, a*v) with v > 0 --> [(x, a*(v0+1)); (v, v0+1)] with v0 = v-1 >= 0 *)
  let p = no_pos in
  let vl0 = List.map fresh_spec_var vl in 
  let vl_exp = List.map (fun v0 -> mkAdd (mkVar v0 p) (mkIConst 1 p) p) vl0 in (* v = v0 + 1 *)
  let vl_sst = List.combine vl vl_exp in
  let vl0_sst = List.map (fun (x, e) -> 
      (x, a_apply_par_term (List.combine vl vl_exp) e)) sst in
  vl0, vl_sst @ vl0_sst

let norm_sst_pos vl sst =
  let pr1 = !print_svl in
  let pr2 = pr_list (pr_pair !print_sv !print_exp) in
  Debug.no_2 "norm_sst_pos" pr1 pr2 (pr_pair pr1 pr2)
    norm_sst_pos vl sst

let norm_sst_zero vl sst =
  let zero = mkIConst 0 no_pos in
  let vl_sst = List.filter (fun (_, e) -> overlap vl (afv e)) sst in
  let vl_zero_sst = List.map (fun (x, _) -> (x, zero)) vl_sst in
  let vl_zero_sst = (List.map (fun v -> (v, zero)) vl) @ vl_zero_sst in
  vl_zero_sst

(* Change rational lambda variables to integer by 
 * multiplying the RHS of assertions to an lcm integer *)  
let norm_rational_asserts asserts = 
  let lcm_denom = SpecVar (Int, "lcm", Unprimed) in 
  let f_b b =
    let (pf, _) = b in
    match pf with
    | Eq (e1, e2, pos) -> 
      if is_zero e1 || is_zero e2 then Some b
      else
        Some (Eq (e1, (mkMult (mkVar lcm_denom pos) e2 pos), pos), None)
    | _ -> None
  in 
  lcm_denom, List.map (transform_formula (nonef, nonef, nonef, f_b, nonef)) asserts

(* If v = vp - vm then |v| = vp + vm *)
let get_abs_model is_linear templ_unks vars assertions = 
  let pos = no_pos in
  let abs_obj_vars = List.map (fun v ->
      let typ = type_of_spec_var v in
      let name = name_of_spec_var v in
      let vp = SpecVar (typ, name ^ "p", Unprimed) in
      let vm = SpecVar (typ, name ^ "m", Unprimed) in
      (v, (vp, vm))) templ_unks in 
  let sst = List.map (fun (v, (vp, vm)) -> 
      (v, mkSubtract (mkVar vp pos) (mkVar vm pos) pos)) abs_obj_vars in
  let abs_vars = List.fold_left (fun a (_, (vp, vm)) -> a @ [vp; vm]) [] abs_obj_vars in
  let n_asserts = List.map (fun a -> apply_par_term sst a) assertions in
  let nneg_asserts = List.map (fun v -> mkPure (mkGte (mkVar v pos) (mkIConst 0 pos) pos)) abs_vars in
  let r = get_model is_linear abs_vars (vars @ abs_vars) (nneg_asserts @ n_asserts) in
  r

let get_abs_model is_linear templ_unks vars assertions = 
  let pr1 = pr_list !print_formula in
  let pr2 = print_solver_res in
  Debug.no_1 "get_abs_model" pr1 pr2
    (fun _ -> get_abs_model is_linear templ_unks vars assertions) assertions

let get_abs_model_disj is_linear templ_unks vars assertion =
  (* The result from Omega is in DNF *)
  let conj_assertions = split_disjunctions assertion in
  let ls_res = List.map (fun a -> 
      get_abs_model is_linear templ_unks vars (split_conjunctions a)) conj_assertions in
  let sat_abs_model = List.fold_left (fun a r -> 
      match r with Sat m -> a @ [m] | _ -> a) [] ls_res in
  match sat_abs_model with
  | [] ->
    if (List.for_all is_unsat_model ls_res) then Unsat else Unknown
  | m1::ms -> 
    (* Find the smallest model abs_m *)
    let sum_model m = List.fold_left (fun a (_, i) -> a + i) 0 m in
    let rec find_min (m1, v1) ms = match ms with 
      | [] -> m1
      | (m2, v2)::ms -> 
        if v1 > v2 then find_min (m2, v2) ms 
        else find_min (m1, v1) ms
    in
    let abs_m = find_min (m1, sum_model m1) (List.map (fun m -> (m, sum_model m)) ms) in
    let m = List.map (fun v -> 
        let vm = name_of_spec_var v in
        (vm, (List.assoc (vm ^ "p") abs_m) - ((List.assoc (vm ^ "m") abs_m)))
      ) templ_unks in Sat m

let is_feasible_model m asserts =
  let subst_asserts = List.map (fun a -> apply_par_term m a) asserts in
  is_sat (join_conjunctions subst_asserts)

let is_feasible_model m asserts =
  let pr1 = pr_list (pr_pair !print_sv !print_exp) in
  let pr2 = pr_list !print_formula in
  let pr3 = string_of_bool in
  Debug.no_2 "is_feasible_model" pr1 pr2 pr3
    is_feasible_model m asserts

let rec search_model_ln pos_zero_vars bnd_vars nln_vars templ_unks sst asserts =
  let pr1 = pr_list !print_formula in
  let pr2 = print_solver_res in
  let pr3 = pr_pair !print_svl !print_svl in
  Debug.no_2 "search_model_ln" (pr_list pr3) pr1 pr2 
    (fun _ _ -> search_model_ln_x pos_zero_vars bnd_vars nln_vars templ_unks sst asserts)
    pos_zero_vars asserts

and search_model_ln_x pos_zero_vars bnd_vars nln_vars templ_unks sst asserts =
  let p = no_pos in
  match pos_zero_vars with
  | [] -> Unsat
  | (pos_vars, zero_vars)::rem ->
    let n_asserts = 
      (List.map (fun v -> mkPure (mkGt (mkVar v p) (mkIConst 0 p) p)) pos_vars) 
      @ asserts in
    let rep_pos_vars, pos_sst = norm_sst_pos pos_vars sst in
    let zero_sst = norm_sst_zero zero_vars sst in
    let n_asserts = List.map (fun f -> apply_par_term zero_sst f) n_asserts in

    let ln_r = Omega.get_model bnd_vars n_asserts in

    let () = 
      x_tinfo_pp ">>>>>>> search_model_ln <<<<<<<" no_pos;
      x_tinfo_hp (add_str "asserts: " (pr_list !print_formula)) n_asserts no_pos;
      x_tinfo_hp (add_str "linear constrs: " !print_formula) ln_r no_pos 
    in

    if is_False ln_r then
      search_model_ln rem bnd_vars nln_vars templ_unks sst asserts
    else
      let nln_r = apply_par_term pos_sst ln_r in
      let nln_r = normalize_eq_formula nln_r in

      let term_l = List.map (fun f -> term_list_of_formula (nln_vars @ rep_pos_vars)
                                (normalize_formula f)) (split_conjunctions nln_r) in
      let templ_unk_constrs = List.map gen_templ_unk_constr term_l in
      let r = Omega.get_model bnd_vars templ_unk_constrs in

      let () = 
        x_tinfo_hp (add_str "nonlinear constrs: " !print_formula) ln_r no_pos;
        x_tinfo_hp (add_str "unk constrs: " (pr_list !print_formula)) templ_unk_constrs no_pos;
        x_tinfo_hp (add_str "simpl unk constrs: " !print_formula) r no_pos 
      in

      if is_False r then
        search_model_ln rem bnd_vars nln_vars templ_unks sst asserts
      else
        let res = get_abs_model_disj true templ_unks (templ_unks @ bnd_vars) r in
        match res with
        | Sat m -> 
          (* Check feasible model here *) 
          let unk_m = List.map (fun v -> 
              let vval = mkIConst (List.assoc (name_of_spec_var v) m) no_pos in
              (v, vval)) templ_unks in
          let nln_asserts = List.map (apply_par_term sst) asserts in
          if is_feasible_model unk_m nln_asserts then res
          else
            (* Find another model - Early eliminate infeasible model branches for fast searching *)
            search_model_ln rem bnd_vars nln_vars templ_unks sst asserts
        | _ -> search_model_ln rem bnd_vars nln_vars templ_unks sst asserts

let get_model_ln is_linear templ_unks vars assertions =
  let p = no_pos in
  let bnd_vars = diff vars templ_unks in
  let lcm, asserts = norm_rational_asserts assertions in
  let ln_asserts, sst = List.split (List.map linearize_nonlinear_formula asserts) in
  let sst = List.concat sst in
  let bnd_nln_vars = intersect bnd_vars (List.concat (List.map (fun (_, e) -> afv e) sst)) in
  let pos_vars, nneg_vars = partition_nln_vars bnd_nln_vars sst ln_asserts in
  let pos_vars = lcm::pos_vars in

  let () = 
    x_tinfo_pp ">>>>>>> get_model_ln <<<<<<<" no_pos;
    x_tinfo_hp (add_str "asserts: " (pr_list !print_formula)) assertions no_pos; 
    x_tinfo_hp (add_str "linearized asserts: " (pr_list !print_formula)) ln_asserts no_pos;
    x_tinfo_hp (add_str "pos vars: " !print_svl) pos_vars no_pos;
    x_tinfo_hp (add_str "nneg: " !print_svl) nneg_vars no_pos
  in

  let ln_asserts = 
    (List.map (fun v -> mkPure (mkGt (mkVar v p) (mkIConst 0 p) p)) pos_vars) 
    @ ln_asserts in
  let rep_pos_vars, sst = norm_sst_pos pos_vars sst in
  let splitted_nneg_vars = split nneg_vars in (* (pos, zero) list *)
  let r = search_model_ln splitted_nneg_vars 
      (lcm::bnd_vars) ((lcm::bnd_nln_vars) @ rep_pos_vars) templ_unks sst ln_asserts in
  r

let get_model_ln is_linear templ_unks vars assertions =
  let pr = pr_list !print_formula in
  Debug.no_1 "get_model_ln" pr print_solver_res
    (fun _ -> get_model_ln is_linear templ_unks vars assertions) assertions

let get_model is_linear templ_unks vars assertions =
  if !oc_solver then
    get_model_ln is_linear templ_unks vars assertions
  else
    get_opt_model is_linear templ_unks vars assertions

let get_model is_linear templ_unks vars assertions =
  let pr1 = !print_svl in
  let pr2 = pr_list !print_formula in
  Debug.no_3 "tl_get_model" pr1 pr1 pr2 print_solver_res
    (fun _ _ _ -> get_model is_linear templ_unks vars assertions)
    templ_unks vars assertions

(*****************)
(* GENERAL UTILS *)
(*****************)
let rec partition_by_assoc eq ls =
  match ls with
  | [] -> []
  | ((k, _) as x)::xs -> 
    let k_xs, nk_xs = List.partition (fun (ks, _) -> eq k ks) xs in
    (x::k_xs)::(partition_by_assoc eq nk_xs)

let rec partition_by_assoc_to_pair eq ls =
  match ls with
  | [] -> []
  | ((k, v) as x)::xs -> 
    let k_xs, nk_xs = List.partition (fun (ks, _) -> eq k ks) xs in
    (k, v::(snd (List.split k_xs)))::(partition_by_assoc_to_pair eq nk_xs)

let eq_templ t1 t2 = eq_spec_var t1.templ_id t2.templ_id

let rec combine_ls xs =
  match xs with
  | [] -> []
  | x::xs -> 
    let rs = combine_ls xs in
    List.concat (List.map (fun e -> List.map (fun r -> e @ r) rs) x)

(* We should not simplify when inferring ranking *)
(* functions for mutual recursive methods        *)
let subst_model_to_exp should_simplify sst e =
  let efv = afv e in
  let rel_sst = List.filter (fun (v, _) -> mem v efv) sst in
  let e_sst =
    if should_simplify then
      let mi = List.map (fun (_, i) -> i) rel_sst in
      let gcd_mi = abs (gcd_l mi) in
      List.map (fun (v, i) -> (v, mkIConst (i / gcd_mi) no_pos)) rel_sst
    else List.map (fun (v, i) -> (v, mkIConst i no_pos)) rel_sst
  in a_apply_par_term e_sst e

let subst_model_to_templ_decls inf_templs templ_unks templ_decls model =
  let unk_subst = List.map (fun v -> 
      let v_val = try List.assoc (name_of_spec_var v) model with _ -> 0 in
      (v, v_val)) templ_unks in
  let inf_templ_decls = match inf_templs with
    | [] -> templ_decls
    | _ -> List.find_all (fun tdef -> List.exists (fun id -> 
        id = tdef.Cast.templ_name) inf_templs) templ_decls
  in
  let res_templ_decls = List.map (fun tdef -> { tdef with
                                                Cast.templ_body = map_opt (fun e -> subst_model_to_exp true unk_subst e) tdef.Cast.templ_body; 
                                              }) inf_templ_decls in
  res_templ_decls

let subst_model_to_formula sst f =
  let f_e e =
    match e with
    | Template t ->
      let t_exp = exp_of_template t in
      Some (subst_model_to_exp true sst t_exp)
    | _ -> None
  in
  transform_formula (nonef, nonef, nonef, nonef, f_e) f

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

let norm_subst svl subst =
  let rec helper subst = 
    let grouped_subst = partition_by_assoc eq_spec_var subst in
    if (List.length grouped_subst) == (List.length subst) then subst
    else
      (* (x, e1), (x, e2) --> (e1 = e2) *)
      helper (List.fold_left (fun a s -> match s with
          | [] -> a
          | x::[] -> a @ [x]
          | (v, e)::xs -> 
            let pos = pos_of_exp e in
            let n_xs = List.concat (List.map (fun (vs, es) -> 
                let f = mkPure (mkEq e es pos)  in
                let s = find_eq_subst_exp svl f in
                match s with
                | None -> []
                | Some s -> [s]) xs) in
            a @ ((v, e)::n_xs)) [] grouped_subst) 
  in
  let normalized_subst = helper subst in
  (* let () = print_endline ("norm_subst: normalized_subst: " ^ (pr_list (pr_pair !print_sv !print_exp) normalized_subst)) in *)
  (* We assume that trivial and cyclic substs like 
   * (x1, x2) and (x2, x1) have been removed by simplify *)
  (* let sorted_subst = List.sort (fun (v1, e1) (v2, e2) ->                                                          *)
  (*   if Gen.BList.mem_eq eq_spec_var v1 (afv e2) then -1                                                           *)
  (*   else if Gen.BList.mem_eq eq_spec_var v2 (afv e1) then 1                                                       *)
  (*   else 0) normalized_subst in                                                                                   *)
  (* let () = print_endline ("norm_subst: sorted_subst: " ^ (pr_list (pr_pair !print_sv !print_exp) sorted_subst)) in *)
  (* List.fold_left (fun subst (v, e) ->                                                                             *)
  (*   (List.remove_assoc v subst) @ [(v, a_apply_par_term subst e)]) sorted_subst sorted_subst                      *)
  let vl = List.map fst normalized_subst in
  List.fold_left (fun subst v ->
      let e = List.assoc v subst in
      List.map (fun (vs, es) -> (vs, a_apply_par_term [(v, e)] es)) subst) normalized_subst vl

let find_eq_subst_formula svl (f: formula): formula * (spec_var * exp) list =
  let fl = split_conjunctions f in
  let fl, subst = List.fold_left (fun (fa, sa) f ->
      match find_eq_subst_exp svl f with
      | None -> (fa @ [f], sa)
      | Some s -> (fa, sa @ [s])) ([], []) fl in
  (* let subst = List.map (fun (v, e) -> (v, a_apply_par_term subst e)) subst in *)
  let subst = norm_subst svl subst in
  (apply_par_term subst (join_conjunctions fl), subst)

let find_eq_subst_formula svl (f: formula): formula * (spec_var * exp) list =
  let pr1 = !print_formula in
  let pr2 = pr_list (pr_pair !print_sv !print_exp) in
  let pr3 = pr_pair pr1 pr2 in
  Debug.no_1 "find_eq_subst_formula" pr1 pr3 
    (fun _ -> find_eq_subst_formula svl f) f

(* Stack for SLEEK generation per scc *)
let templ_sleek_scc_stk: (spec_var list * formula * formula) Gen.stack = new Gen.stack

(* Stack for SLEEK generation whole program *)
let templ_sleek_stk: string Gen.stack = new Gen.stack

type templ_assume = {
  (* Arguments of templates *)
  ass_vars: spec_var list;
  (* Unknown of templates *)
  ass_unks: spec_var list;
  (* Antecendent of template assumption *)
  ass_ante: formula;
  (* Consequent of template assumption *)
  ass_cons: formula;
  (* Antecedent in the polynomial form *)
  ass_ante_tl: term list list;
  (* Consequent without template *)
  ass_cons_no_templ: formula;
  (* Pos of the assumption *)
  ass_pos: loc;
}

(* Stack of template assumption per scc *)
let templ_assume_scc_stk: templ_assume Gen.stack = new Gen.stack

let pr_templ_assume ta = 
  Cprinter.string_of_templ_assume (ta.ass_ante, ta.ass_cons)

let templ_decl_of_templ_exp texp =
  let pos = texp.templ_pos in
  let tname = name_of_spec_var texp.templ_id in
  let ftype = type_of_spec_var texp.templ_id in
  let rtype = ret_typ_of_FuncT ftype in
  let ptypes = param_typ_of_FuncT ftype in
  let ptypes_with_id = snd (List.fold_left (fun (i, a) t -> 
      (i + 1, a @ [(i + 1, t)])) (0, []) ptypes) in 
  let params = List.map (fun (i, t) -> 
      SpecVar (t, tname ^ "_p_" ^ (string_of_int i), Unprimed)) ptypes_with_id in
  let unk_coes = List.map (fun (i, t) -> 
      SpecVar (t, tname ^ "_" ^ (string_of_int i), Unprimed)) ptypes_with_id in
  let unk_const = SpecVar (Int, tname ^ "_" ^ (string_of_int 0), Unprimed) in
  let unk_exps = List.map (fun v -> mkVar v pos) (unk_const::unk_coes) in
  let body = List.fold_left (fun a (c, v) -> mkAdd a (mkMult c (mkVar v pos) pos) pos)
      (List.hd unk_exps) (List.combine (List.tl unk_exps) params) in
  { Cast.templ_name = tname;
    Cast.templ_ret_typ = rtype;
    Cast.templ_params = params;
    Cast.templ_body = Some body;
    Cast.templ_pos = pos; }
