open SBGlobals
open SBCast
open SBLib
open SBLib.Basic

module NO = SBNormalize
module Z3b = SBZ3bin
(* module Z3l = Z3lib *)
module Z3l = SBZ3bin

let time_checking = ref 0.1

let sat_cache: (string, mvlogic) Hashtbl.t = Hashtbl.create 200
let sat_cache_hit_cnt = ref 0
let sat_check_cnt = ref 0

let imply_cache: (string, mvlogic) Hashtbl.t = Hashtbl.create 200
let imply_cache_hit_cnt = ref 0
let imply_check_cnt = ref 0


type pure_prover_t =
  | PpOmega
  | PpZ3lib
  | PpZ3bin

let pure_prover = ref PpZ3bin

let set_prover name =
  if (eq_s name "oc") then
    pure_prover := PpOmega
  else if (eq_s name "z3lib") then
    pure_prover := PpZ3lib
  else if (eq_s name "z3bin") then
    pure_prover := PpZ3bin
  else ()

let pr_prover prover = match prover with
  | PpOmega -> "Omega"
  | PpZ3lib -> "Z3lib"
  | PpZ3bin -> "Z3bin"

let stop_all_provers () =
  match !pure_prover with
  | PpZ3bin -> Z3b.stop_prover ()
  | _ -> ()

(****************************************************************)
(**********************      check sat      *********************)

let check_sat_core f =
  let check_sat = match !pure_prover with
    | PpZ3bin -> Z3b.check_sat
    | PpZ3lib -> Z3l.check_sat
    | _ -> error ("check_sat_core: unsupported prover: \
                  " ^ (pr_prover !pure_prover)) in
  let tbegin = get_time () in
  let res = check_sat f in
  let tend = get_time () in
  let _ = time_checking := !time_checking +. (tend -. tbegin) in
  res

let rec check_sat ?(prog=None) f : mvlogic =
  Debug.trace_1 "check_sat" (pr_pf, pr_mvl) f
    (fun () -> check_sat_x ~prog:prog f)

and check_sat_x ?(prog=None) f : mvlogic =
  let f = match prog with
    | None -> f
    | Some _ -> NO.simplify_all_pf ~prog:prog f in
  if !puretp_use_cache then
    let () = sat_check_cnt := !sat_check_cnt + 1 in
    let str = (pr_pf f) in
    try
      let res = Hashtbl.find sat_cache str in
      let () = sat_cache_hit_cnt := !sat_cache_hit_cnt + 1 in
      res
    with Not_found ->
      let res = check_sat_core f in
      let () = Hashtbl.add sat_cache str res in
      res
  else check_sat_core f

let rec check_sat_get_model ?(prog=None) f vs : mvlogic * model =
  let pr_res = pr_pair pr_mvl (pr_list (pr_pair pr_var pr_exp )) in
  Debug.trace_2 "check_sat_get_model" (pr_pf, pr_vs, pr_res) f vs
    (fun () -> check_sat_get_model_x ~prog:prog f vs)

and check_sat_get_model_x ?(prog=None) f vs : mvlogic * model =
  let check = match !pure_prover with
    | PpZ3bin -> Z3bin.check_sat_and_get_model
    | PpZ3lib -> Z3l.check_sat_and_get_model
    | _ -> error ("check_sat_core: unsupported prover: \
                  " ^ (pr_prover !pure_prover)) in
  let f = match prog with
    | None -> f
    | Some _ -> NO.simplify_all_pf ~prog:prog f in
  let tbegin = get_time () in
  let res = match vs with
    | [] -> (check_sat ~prog:prog f, [])
    | _ -> check [f] vs in
  let tend = get_time () in
  let _ = time_checking := !time_checking +. (tend -. tbegin) in
  res

let rec has_unique_model ?(prog=None) f vs : bool =
  Debug.trace_2 "has_unique_model" (pr_pf, pr_vs, pr_bool) f vs
    (fun () -> has_unique_model_x ~prog:prog f vs)

and has_unique_model_x ?(prog=None) f vs : bool =
  let f = match prog with
    | None -> f
    | Some _ -> NO.simplify_all_pf ~prog:prog f in
  let sat, model = check_sat_get_model f vs in
  if sat = MvlTrue then
    let neg_model = model |> List.map (fun (v, e) -> mk_neq_var_exp v e) |>
                    mk_pdisj in
    let nf = mk_pconj [f; neg_model] in
    check_sat nf = MvlFalse
  else false

let rec has_unique_model_all_vars ?(prog=None) f : bool =
  let vs = fv_pf f in
  has_unique_model ~prog:prog f vs

let rec has_unique_model_one_var ?(prog=None) f : bool =
  let vs = fv_pf f in
  List.exists (fun v -> has_unique_model ~prog:prog f [v]) vs

let rec unsat_or_has_unique_model ?(prog=None) ?(constr=IctAll) f vs : bool =
  Debug.trace_2 "unsat_or_has_unique_model" (pr_pf, pr_vs, pr_bool) f vs
    (fun () -> unsat_or_has_unique_model_x ~prog:prog ~constr:constr f vs)

and unsat_or_has_unique_model_x ?(prog=None) ?(constr=IctAll) f vs : bool =
  let vs = List.filter (check_ict_var constr) vs in
  let f = match prog with
    | None -> f
    | Some _ -> NO.simplify_all_pf ~prog:prog f in
  let sat, model = check_sat_get_model f vs in
  if (sat = MvlFalse || sat = MvlUnkn) then true
  else if (vs = []) then false
  else
    let neg_model = model |> List.map (fun (v, e) -> mk_neq_var_exp v e) |>
                    mk_pdisj in
    let nf = mk_pconj [f; neg_model] in
    check_sat nf = MvlFalse

let rec unsat_or_has_unique_model_all_vars ?(prog=None) ?(constr=IctAll) f : bool =
  let vs = fv_pf f in
  unsat_or_has_unique_model ~prog:prog ~constr:constr f vs

let rec unsat_or_has_unique_model_one_var ?(prog=None) ?(constr=IctAll) f : bool =
  let vs = fv_pf f in
  List.exists (fun v -> unsat_or_has_unique_model ~prog:prog ~constr:constr f [v]) vs


(****************************************************************)
(******************     check inconsistency     *****************)

let rec check_consistency f1 f2 : mvlogic =
  Debug.trace_2 "check_consistency" (pr_pf, pr_pf, pr_mvl) f1 f2
    (fun () -> check_consistency_x f1 f2)

and check_consistency_x f1 f2 : mvlogic =
  let lvs, rvs = fv_pf f1, fv_pf f2 in
  let cvs = intersect_vs lvs rvs in
  let nf1 = collect_pure_conjuncts_pf f1 |>
            List.filter (fun x -> intersected_vs cvs (fv_pf x)) |>
            mk_pconj in
  let nf2 = collect_pure_conjuncts_pf f2 |>
            List.filter (fun x -> intersected_vs cvs (fv_pf x)) |>
            mk_pconj in
  check_sat (mk_pconj [nf1; nf2])


(****************************************************************)
(**********************     check imply     *********************)

let check_imply_core lhs rhs =
  let check_imply = match !pure_prover with
    | PpZ3bin -> Z3b.check_imply
    | PpZ3lib -> Z3l.check_imply
    | _ -> error ("check_sat_core: unsupported prover: \
                  " ^ (pr_prover !pure_prover)) in
  check_imply lhs rhs

let rec check_imply ?(prog=None) ?(norm=false) lhs rhs =
  Debug.trace_2 "check_imply" (pr_pf, pr_pf, pr_mvl) lhs rhs
    (fun () -> check_imply_x ~prog:prog ~norm:norm lhs rhs)

and check_imply_x ?(prog=None) ?(norm=false) lhs rhs =
  let lhs, rhs = match norm with
    | true -> NO.simplify_all_lhs_rhs_pf ~prog:prog lhs rhs
    | _ -> lhs, rhs in
  if !puretp_use_cache then
    let () = imply_check_cnt := !imply_check_cnt + 1 in
    let imply_str = (pr_pf lhs) ^ " |- " ^ (pr_pf rhs) in
    try
      let res = Hashtbl.find imply_cache imply_str in
      let () = imply_cache_hit_cnt := !imply_cache_hit_cnt + 1 in
      res
    with Not_found ->
      let res = check_imply_core lhs rhs in
      let () = Hashtbl.add imply_cache imply_str res in
      res
  else check_imply_core lhs rhs

let rec check_imply_slice_lhs ?(prog=None) lhs rhs : mvlogic =
  Debug.trace_2 "check_imply_slice_lhs" (pr_pf, pr_pf, pr_mvl) lhs rhs
    (fun () -> check_imply_slice_lhs_x ~prog:prog lhs rhs)

and check_imply_slice_lhs_x ?(prog=None) lhs rhs : mvlogic =
  let rvs = fv_pf rhs in
  let lvs_involved = NO.collect_closure_vars_pf rvs lhs in
  let patoms =
    collect_pure_conjuncts_pf lhs |>
    List.filter (fun x ->
      let xvs = fv_pf x in
      (List.length xvs = 0) || (intersected_vs lvs_involved xvs)) in
  let lhs = mk_pconj patoms in
  check_imply lhs rhs

let check_equiv (f1: pure_form) (f2: pure_form) =
  (check_imply f1 f2 = MvlTrue) &&
  (check_imply f2 f1 = MvlTrue)

let reset_cache () =
  DB.npprint "PureTP: reset cache!";
  Hashtbl.reset sat_cache;
  sat_cache_hit_cnt := 0;
  sat_check_cnt := 0;
  Hashtbl.reset imply_cache;
  DB.nhprint "SAT-CACHE length: " pr_int (Hashtbl.length sat_cache);
  DB.nhprint "IMPLY-CACHE length: " pr_int (Hashtbl.length imply_cache);
  imply_cache_hit_cnt := 0;
  imply_check_cnt := 0

let restart_prover () =
  match !pure_prover with
  | PpZ3bin -> Z3bin.restart_prover ()
  | _ -> ()


(****************************************************************)
(*******************     check pure entail     ******************)

let rec check_pure_entail ?(prog=None) ?(norm=true) pent =
  Debug.trace_1 "check_pure_entail" (pr_pent, pr_mvl) pent
    (fun () -> check_pure_entail_x ~prog:prog ~norm:norm pent)

and check_pure_entail_x ?(prog=None) ?(norm=true) pent =
  let lhs, rhs = pent.pent_lhs, pent.pent_rhs in
  check_imply ~prog:prog ~norm:norm lhs rhs

let rec check_pure_entails ?(prog=None) ?(norm=true) pents =
  Debug.trace_1 "check_pure_entails" (pr_pents, pr_mvl) pents
    (fun () -> check_pure_entails_x ~prog:prog ~norm:norm pents)

and check_pure_entails_x ?(prog=None) ?(norm=true) pents =
  let ress = pents |> List.map (check_pure_entail ~prog:prog ~norm:norm) in
  if (List.for_all (fun x -> x = MvlTrue) ress) then MvlTrue
  else  if (List.exists (fun x -> x = MvlFalse) ress) then MvlFalse
  else MvlUnkn
