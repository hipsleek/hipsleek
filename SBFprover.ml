open SBGlobals
open SBCast

module DB = SBDebug
module TL = SBTemplate
module TP = SBPuretp
module Z3b = SBZ3bin
(* module Z3l = Z3lib *)
module Z3l = SBZ3bin

type model = (var * exp) list

module type Z3_p = sig
  val check_sat: pure_form -> mvlogic
  val check_sat_and_get_model: pure_form list -> var list -> mvlogic * model
  val check_imply: pure_form -> pure_form -> mvlogic
end

let choose_z3 = function
  | TP.PpZ3lib -> (module Z3l: Z3_p)
  | _ -> (module Z3b: Z3_p)

let mk_sum_of_exp (es: exp list): exp =
  match es with
  | [] -> zero
  | e::es -> List.fold_left (fun a e -> mk_bin_op Add a e) e es

let mk_sum_of_abs (es: exp list): exp =
  let abs_es = List.map (fun e -> mk_func Abs [e]) es in
  mk_sum_of_exp abs_es

let rec mk_conj_constrs pair_f vs =
    match vs with
    | [] | _::[] -> []
    | v::vs ->
      let dist_v = List.map (fun s -> pair_f v s) vs |> mk_pconj in
      dist_v::(mk_conj_constrs pair_f vs)

let check_sat = TP.check_sat

let rec check_sat_and_get_opt_model (tk: TL.templ_kind) (unk_coes: unk_coes_rel list)
    (f: pure_form) : (mvlogic * model) =
  Debug.trace_1 "check_sat_and_get_opt_model"
    (pr_pf, fun (_, m) -> pr_model m) f
    (fun () -> check_sat_and_get_opt_model_x tk unk_coes f)

and check_sat_and_get_opt_model_x (tk: TL.templ_kind) (unk_coes: unk_coes_rel list)
    (f: pure_form) : (mvlogic * model) =
  let param_coes = unk_coes |> List.map TL.get_unk_param_coes |> List.concat in
  let base_coes = unk_coes |> List.map TL.get_unk_base_coes |> List.concat in
  let opt_vars = param_coes in
  let obj_vars = param_coes @ base_coes in

  let module Z3 = (val (choose_z3 !TP.pure_prover): Z3_p) in

  let mk_diff_cond vs1 vs2 =
    (* List.map2 (fun v1 v2 -> mk_eq_var v1 v2) vs1 vs2 |> *)
    (* mk_pconj |> mk_pneg *)
    (*************************)
    (* let div_es = List.map2 (fun v1 v2 -> mk_bin_op Div (mk_exp_var v1) (mk_exp_var v2)) vs1 vs2 in *)
    (* match div_es with *)
    (* | [] | _::[] -> mk_true no_pos *)
    (* | d::ds -> *)
    (*   List.fold_left (fun a e -> a @ [mk_eq_exp d e]) [] ds |> *)
    (*   mk_pconj |> mk_pneg *)
    (*************************)
    let mk_mul e1 e2 = mk_bin_op Mul e1 e2 in
    let div_es = List.map2 (fun v1 v2 -> (mk_exp_var v1), (mk_exp_var v2)) vs1 vs2 in
    match div_es with
    | [] | _::[] -> mk_true no_pos
    | (d1, d2)::ds ->
      List.fold_left (fun a (e1, e2) -> a @ [mk_eq_exp (mk_mul d1 e2) (mk_mul d2 e1)]) [] ds |>
      mk_pconj |> mk_pneg
  in

  let abs_opt unk_coes =
    let opt_constrs =
      List.map (fun uc ->
        List.map (fun coe ->
          let abs_sum = mk_sum_of_abs (List.map mk_exp_var coe.uc_param_coes) in
          mk_bin_rel Gt abs_sum zero) uc.uc_coes_conjs
      ) unk_coes |> List.concat
    in
    let diff_constrs =
      List.map (fun uc ->
        uc.uc_coes_conjs |>
        List.map (fun coe -> coe.uc_param_coes @ coe.uc_base_coes) |>
        mk_conj_constrs mk_diff_cond) unk_coes |> List.concat
    in
    Z3.check_sat_and_get_model ([f] @ opt_constrs @ diff_constrs) obj_vars
  in

  match tk with
  | TL.EqArithT ->
    (* let opt_constr = List.map (fun v -> mk_neq_iconst_var v 0) opt_vars in *)
    (* TRUNG: use abs(x) > 0 to denote x!=0 *)
    let opt_constr = List.map (fun v -> mk_rel_gt (mk_abs_var v) zero) opt_vars in
    let res, model = Z3.check_sat_and_get_model ([f] @ opt_constr) obj_vars in
    if not (is_empty_model model) then res, model
    else abs_opt unk_coes
  | _ -> abs_opt unk_coes

let rec check_sat_and_get_ptr_model (tk: TL.templ_kind) (unk_coes: unk_coes_rel list)
    (f: pure_form) : (mvlogic * model) =
  DB.trace_1 "check_sat_and_get_ptr_model" (pr_pf, fun (_, m) -> pr_model m) f
    (fun () -> check_sat_and_get_ptr_model_x tk unk_coes f)

and gen_ptr_unk_coe_constr (tk: TL.templ_kind) (uc: unk_coes_rel) =
  let param_es = List.map mk_exp_var (TL.get_unk_param_coes uc) in
  let param_coes_cs =
    (* -1 <= c <= 1 *)
    List.map (fun c ->
      [mk_bin_rel Ge c (mk_iconst (-1)); mk_bin_rel Le c (mk_iconst 1)]
    ) param_es |>
    List.concat
  in

  let base_coes_cs =
    (* LinearT -> c = -1 *)
    (* EqT -> c = 0 *)
    let const = match tk with
      | TL.EqPtrT -> zero
      | _ -> mk_iconst (-1) in
    List.map (fun c -> mk_eq_exp (mk_exp_var c) const)
      (TL.get_unk_base_coes uc)
  in

  let abs_sum = mk_sum_of_abs param_es in
  let sum = mk_sum_of_exp param_es in
  [mk_bin_rel Ge abs_sum (mk_iconst 1); mk_bin_rel Le abs_sum (mk_iconst 2)] @
    [mk_bin_rel Ge sum (mk_iconst 0); mk_bin_rel Le sum (mk_iconst 1)] @
    param_coes_cs @ base_coes_cs

and check_sat_and_get_ptr_model_x (tk: TL.templ_kind) (unk_coes: unk_coes_rel list)
    (f: pure_form) : (mvlogic * model) =
  let coe_constrs =
    unk_coes |> List.map (gen_ptr_unk_coe_constr tk) |> List.concat in
  let expl_vars =
    unk_coes |> List.map TL.get_all_unk_coes |>
    List.concat |> dedup_vs in
  let module Z3 = (val (choose_z3 !TP.pure_prover): Z3_p) in
  Z3.check_sat_and_get_model (coe_constrs @ [f]) expl_vars
