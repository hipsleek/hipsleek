open Globals
open Gen
open Cpure

module MCP = Mcpure
module CF = Cformula
module C = Cast

type term = {
  term_coe: exp;
  term_var: (spec_var * int) list; (* [(x, 2)] -> x^2; [(x, 1), (y, 1)] -> xy *)
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

let unk_lambda_sv enum i j = 
  SpecVar (Int, "lambda_" ^ (string_of_int enum) ^ "_" ^ 
          (string_of_int i) ^ "_" ^ (string_of_int j), Unprimed) 

let collect_unk_constrs (ante: term list) (cons: term list) pos: formula list =
  (* let _ = print_endline ("ANTE: " ^ (print_term_list ante)) in *)
  (* let _ = print_endline ("CONS: " ^ (print_term_list cons)) in *)

  let rem_cons, constrs = List.fold_left (fun (cons, fl) at -> 
    let cons_same_deg, cons_notsame_deg = 
      List.partition (fun t -> is_same_degree t at) cons in
    let constr_exp = List.fold_left (fun a ct -> mkAdd a ct.term_coe pos) 
      (mkMult (mkIConst (-1) pos) at.term_coe pos) cons_same_deg in
    let constr = 
      if at.term_var = [] then mkPure (mkLte constr_exp (mkIConst 0 pos) pos)
      else mkPure (mkEq constr_exp (mkIConst 0 pos) pos)
    in (cons_notsame_deg, fl @ [constr])) (cons, []) ante in
  let rem_constrs = List.map (fun ct -> 
    mkPure (mkEq ct.term_coe (mkIConst 0 pos) pos)) rem_cons in
  constrs @ rem_constrs

let gen_unk_constrs enum vars (ante: formula) (cons: formula): formula list =
  let pos = pos_of_formula ante in
  let ante, subst = find_eq_subst_formula vars ante in
  let cons = normalize_formula (apply_par_term subst cons) in 

  let true_f = mkPure (mkLte (mkIConst (-1) pos) (mkIConst 0 pos) pos) in
  let ante_fl = true_f::(split_conjunctions ante) in
  let ante_tl = List.map (term_list_of_formula vars) ante_fl in
    
  let cons_fl = split_conjunctions cons in
  let cons_tl = List.map (term_list_of_formula vars) cons_fl in

  (* let _ = print_endline ("ANTE: " ^ (pr_list print_term_list ante_tl)) in *)
  (* let _ = print_endline ("CONS: " ^ (pr_list print_term_list cons_tl)) in *)

  let cons_tl = snd (List.fold_left (fun (i, a) t -> 
    (i+1, a @ [(i, t)])) (0, []) cons_tl) in

  let constrs = List.concat (List.map (fun (i, cons_t) ->
    let _, ante_w_unks, unks = List.fold_left (fun (j, a, unks) tl ->
      let unk_lambda = mkVar (unk_lambda_sv enum i j) pos in
      let tl = List.map (fun t -> { t with term_coe = mkMult unk_lambda t.term_coe pos; }) tl in
      (j+1, a @ [tl], unks @ [unk_lambda])) (0, [], []) ante_tl in
    let ante_sum_t = partition_term_list (List.concat ante_w_unks) pos in
    (List.map (fun unk -> mkPure (mkGte unk (mkIConst 0 pos) pos)) unks) @
    collect_unk_constrs ante_sum_t cons_t pos) cons_tl) in
  (* let _ = print_endline ("CONSTR: " ^ (pr_list !print_formula constrs)) in *)
  constrs

let exp_of_templ_decl (tdef: C.templ_decl): exp =
  let pos = tdef.C.templ_pos in
  let func_typ = List.fold_right (fun v r_typ -> FuncT (type_of_spec_var v, r_typ))
    tdef.C.templ_params tdef.C.templ_ret_typ in 
  let tid = SpecVar (func_typ, tdef.C.templ_name, Unprimed) in
  let targs = List.map (fun v -> mkVar v pos) tdef.C.templ_params in
  Template {
    templ_id = tid; templ_args = targs; templ_unks = []; 
    templ_body = tdef.C.templ_body; templ_pos = pos; }

let templ_constr_stk: formula Gen.stack = new Gen.stack

let templ_sleek_scc_stk: (spec_var list * formula * formula) Gen.stack = new Gen.stack

let templ_sleek_stk: string Gen.stack = new Gen.stack

let templ_entail_num = ref 0

let infer_template (es: CF.entail_state) (ante: MCP.mix_formula) (cons: formula) pos =
  let inf_templs = es.CF.es_infer_vars_templ in

  let _ = 
    if !gen_templ_slk then 
      templ_sleek_scc_stk # push (inf_templs, MCP.pure_of_mix ante, cons)
    else () 
  in

  let ante = MCP.find_rel_constraints ante (fv cons) in
  let n_ante, ante_unks = trans_formula_templ inf_templs (MCP.pure_of_mix ante) in
  let n_cons, cons_unks = trans_formula_templ inf_templs cons in

  (* let _ = print_endline ("ANTE: " ^ (!print_formula n_ante)) in *)
  (* let _ = print_endline ("CONS: " ^ (!print_formula n_cons)) in *)

  let constrs = gen_unk_constrs !templ_entail_num 
    (Gen.BList.difference_eq eq_spec_var ((fv n_ante) @ (fv n_cons)) (ante_unks @ cons_unks)) 
    n_ante n_cons in
  templ_entail_num := !templ_entail_num + 1;
  templ_constr_stk # push_list constrs;
  Some es

let infer_template (es: CF.entail_state) (ante: MCP.mix_formula) (cons: formula) pos =
  let pr1 = !MCP.print_mix_formula in
  let pr2 = !print_formula in
  Debug.no_2 "infer_template" pr1 pr2 (pr_opt !CF.print_entail_state) 
    (fun _ _ -> infer_template es ante cons pos) ante cons

let gen_slk_infer_templ_scc () =
  let inp = List.rev (templ_sleek_scc_stk # get_stk) in
  let _ = templ_sleek_stk # reset in

  let out = List.map (fun (templ_vars, ante, cons) ->
    "infer " ^ (!print_svl templ_vars) ^ " " ^ 
    (!print_formula ante) ^ " |- " ^ (!print_formula cons) ^ ".") inp in
  let str = (String.concat "\n" out) ^ "\ntemplate_solve.\n" in
  templ_sleek_stk # push str

let gen_slk_file prog =
  let file_name_ss = List.hd !Globals.source_files in
  let out_chn =
    let reg = Str.regexp "\.ss" in
    let file_name_slk = "logs/rank_" ^ (Str.global_replace reg ".slk" file_name_ss) in
    let _ = print_endline ("\n Generating sleek file: " ^ file_name_slk) in
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    open_out (file_name_slk)
  in

  let templ_decl_str = String.concat "\n" 
    (List.map Cprinter.string_of_templ_decl prog.C.prog_templ_decls)
  in

  let templ_infer_str = String.concat "\n" (List.rev (templ_sleek_stk # get_stk)) in
  
  let slk_output = templ_decl_str ^ "\n\n" ^ templ_infer_str in
  let _ = output_string out_chn slk_output in
  let _ = close_out out_chn in
  ()

let collect_and_solve_templ_constrs inf_templs prog = 
  let constrs = templ_constr_stk # get_stk in
  let _ = templ_constr_stk # reset in

  let _ = 
    if !gen_templ_slk then gen_slk_infer_templ_scc () 
    else ()
  in

  if constrs == [] then ()
  else
    let unks = Gen.BList.remove_dups_eq eq_spec_var 
      (List.concat (List.map fv constrs)) in
    let model = Smtsolver.get_model (List.for_all is_linear_formula constrs) unks constrs in
    match model with
    | [] -> print_endline ("TEMPLATE INFERENCE: No result.")
    | _ ->
      let templ_decls = prog.C.prog_templ_decls in
      let templ_params = List.concat (List.map (fun tdef -> tdef.C.templ_params) templ_decls) in
      let templ_fv = List.concat (List.map (fun tdef -> fold_opt afv tdef.C.templ_body) templ_decls) in
      let unk_subst = List.map (fun v -> 
          let v_val = try List.assoc (name_of_spec_var v) model with _ -> 0 in
          (v, mkIConst v_val no_pos)) 
        (Gen.BList.difference_eq eq_spec_var templ_fv templ_params) in
      let inf_templ_decls = match inf_templs with
      | [] -> templ_decls
      | _ -> List.find_all (fun tdef -> List.exists (fun id -> 
          id = tdef.C.templ_name) inf_templs) templ_decls
      in
      let res_templ_decls = List.map (fun tdef -> { tdef with
        C.templ_body = map_opt (fun e -> a_apply_par_term unk_subst e) tdef.C.templ_body; 
      }) inf_templ_decls in
      print_string "TEMPLATE INFERENCE RESULT: ";
      print_endline (pr_list Cprinter.string_of_templ_decl res_templ_decls)



