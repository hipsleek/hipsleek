open SBGlobals
open SBCast

module DB = SBDebug
module TL = SBTemplate
module NO = SBNormalize
module TP = SBPuretp
module FP = SBFprover

let pr_ents xs = match xs with
    | [] -> "[]"
    | _ -> "\n" ^ (pr_items ~bullet:"  #" pr_pent xs)

let pr_rels rs = match rs with
    | [] -> "[]"
    | _ -> "\n" ^ (pr_items ~bullet:"  #" pr_rel_defn rs)


(*************************************************)
(*** Internal data structure for Farkas' lemma ***)

type tvar = (var * int) list (* (var, degree) list - [] means 1 *)

type term = {
  term_coe: exp;
  term_var: tvar; }

type fterm = term list (* [] means 0 *)

type fform = fterm list

type farkas_solution_type =
  | FstPrecise
  | FstPartial of pure_entail list
  | FstNoSolution

type farkas_solution = {
  fs_type : farkas_solution_type;
  fs_rel_defns : rel_defn list;
}

let pr_model = pr_list (pr_pair pr_var pr_exp)

let pr_tvar (vs: tvar) =
  vs |>
  List.map (fun (v, i) ->
    let v_str = pr_var v in
    if i == 1 then v_str else v_str ^ "^" ^ (string_of_int i)) |>
  String.concat "."

let pr_term (t: term) =
  "(" ^ (pr_exp t.term_coe) ^ ")" ^
    (if t.term_var != [] then ("." ^ (pr_tvar t.term_var)) else "")

let pr_fterm (ft: fterm) =
  ft |> List.map pr_term |> String.concat " + "

let pr_fform (ff: fform) =
  ff |>
  List.map (fun ft -> "(" ^ (pr_fterm ft) ^ ")") |>
  String.concat " /\\ "

let pr_fsol fsol =
  let styp = match fsol.fs_type with
    | FstPrecise -> "precise solution: "
    | FstPartial _ -> "partial solution: "
    | FstNoSolution -> "no solution" in
  let srels = pr_rels fsol.fs_rel_defns in
  styp ^ srels

let mk_term c v = { term_coe = c; term_var = v }

let mk_fsol_precise rdefns =
  { fs_type = FstPrecise;
    fs_rel_defns = rdefns; }

let mk_fsol_partial rdefns pents =
  { fs_type = FstPartial pents;
    fs_rel_defns = rdefns; }

let mk_fsol_no_solution () =
  { fs_type = FstNoSolution;
    fs_rel_defns = []; }

let remove_term_zero (f: fterm): fterm =
  List.filter (fun t -> not (is_zero_exp t.term_coe)) f

let degree_of_term_var (vs: (var * int) list): int =
  List.fold_left (fun acc (v, i) -> acc + i) 0 vs

let compare_term_var (vs1: tvar) (vs2: tvar): int =
  let ds1 = degree_of_term_var vs1 in
  let ds2 = degree_of_term_var vs2 in
  if ds1 != ds2 then ds1 - ds2
  else
    let rec compare_same_degree vs1 vs2 =
      match vs1, vs2 with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | (v1, d1)::vs1, (v2, d2)::vs2 ->
        if eq_var v1 v2 then
          if d1 == d2 then compare_same_degree vs1 vs2
          else d1 - d2
        else compare_var v1 v2
    in
    compare_same_degree vs1 vs2

let compare_term_var (vs1: tvar) (vs2: tvar): int =
  DB.trace_2 "compare_term_var" (pr_tvar, pr_tvar, string_of_int) vs1 vs2
    (fun () -> compare_term_var vs1 vs2)

let mk_mul_term_var (vs1: tvar) (vs2: tvar): tvar =
  let rec product vs1 vs2 =
    match vs1, vs2 with
    | [], _ -> vs2
    | _, [] -> vs1
    | (v1, i1)::vr1, (v2, i2)::vr2 ->
      let cmp = compare_var v1 v2 in
      if cmp == 0 then
        (v1, i1 + i2)::(product vr1 vr2)
      else if cmp < 0 then
        (v1, i1)::(product vr1 vs2)
      else
        (v2, i2)::(product vs1 vr2)
  in product vs1 vs2

let term_of_int i = mk_term (mk_iconst i) []

let term_of_var (vs: var list) (v: var) =
  if (mem_vs v vs) then mk_term (mk_iconst 1) [(v, 1)]
  else mk_term (mk_exp_var v) []

let mk_add_fterm (ts1: fterm) (ts2: fterm): fterm =
  let rec sum ts1 ts2 =
    match ts1, ts2 with
    | [], _ -> ts2
    | _, [] -> ts1
    | t1::tr1, t2::tr2 ->
      let cmp = compare_term_var t1.term_var t2.term_var in
      if cmp == 0 then
        let sum_tr = sum tr1 tr2 in
        let coe = mk_bin_op Add t1.term_coe t2.term_coe in
        if is_zero_exp coe then sum_tr
        else
          let sum_t = mk_term coe t1.term_var in
          sum_t::sum_tr
      else if cmp > 0 then t2::(sum ts1 tr2)
      else t1::(sum tr1 ts2)
  in
  sum (remove_term_zero ts1) (remove_term_zero ts2)

let mk_add_fterm (ts1: fterm) (ts2: fterm): fterm =
  DB.trace_2 "mk_add_fterm" (pr_fterm, pr_fterm, pr_fterm) ts1 ts2
    (fun () -> mk_add_fterm ts1 ts2)

let mk_mul_term (t1: term) (t2: term): term =
  let c = mk_bin_op Mul t1.term_coe t2.term_coe in
  let v = mk_mul_term_var t1.term_var t2.term_var in
  mk_term c v

let mk_mul_fterm (ts1: fterm) (ts2: fterm): fterm =
  let product = List.concat (List.map (fun t1 ->
    List.map (fun t2 -> mk_mul_term t1 t2) ts2) ts1) in
  List.fold_left (fun acc t -> mk_add_fterm acc [t]) [] product

let rec fterm_of_exp (vs: var list) (e: exp): fterm =
  DB.trace_2 "fterm_of_exp" (pr_vs, pr_e, pr_fterm) vs e
    (fun () -> fterm_of_exp_x vs e)

and fterm_of_exp_x (vs: var list) (e: exp): fterm =
  match e with
  | IConst (i, _) -> [term_of_int i]
  | Var (v, _) -> [term_of_var vs v]
  | LTerm (t, _) ->
    let ts, c = t in
    let ts, c = List.fold_left (fun (ts, cs) (i, v) ->
      if mem_vs v vs then (ts @ [mk_term (mk_iconst i) [(v, 1)]], cs)
      else (ts, mk_bin_op Add (mk_bin_op Mul (mk_iconst i) (mk_exp_var v)) cs)
    ) ([], (mk_iconst c)) ts in
    [mk_term c []] @ ts
  | BinOp (Add, e1, e2, p) ->
    let ts1 = fterm_of_exp vs e1 in
    let ts2 = fterm_of_exp vs e2 in
    mk_add_fterm ts1 ts2
  | BinOp (Sub, e1, e2, p) ->
    let ne = mk_bin_op Add e1 (mk_bin_op Mul (mk_iconst (-1)) e2) ~pos:p in
    fterm_of_exp vs ne
  | BinOp (Mul, e1, e2, p) ->
    let ts1 = fterm_of_exp vs e1 in
    let ts2 = fterm_of_exp vs e2 in
    mk_mul_fterm ts1 ts2
  | _ -> fhwarning "fterm_of_exp: Unexpected exp " pr_e e

(* f = conj of (aX + b >= 0) *)
let rec fterm_of_pf (vs: var list) (f: pure_form): fterm list =
  match f with
  | BConst (b, _) -> if b then [] else [fterm_of_exp vs (mk_iconst (-1))]
  | BinRel (Ge, e1, e2, _) when is_zero_exp e2 ->
    [fterm_of_exp vs e1]
  | PConj (fs, _) -> fs |> List.map (fterm_of_pf vs) |> List.concat
  | _ -> fhwarning "fterm_of_pf: Unexpected pure formula " pr_pf f

let fterm_of_pf (vs: var list) (f: pure_form): fterm list =
  DB.trace_2 "fterm_of_pf" (pr_vs, pr_pf, pr_fform) vs f
    (fun () -> fterm_of_pf vs f)

(******************************************)
(*** Transform formula to a normal form ***)

exception UnexpectedOp

let norm_bin_rel_ineq ?(pos=no_pos) rel e1 e2 =
  let zero = mk_iconst 0 in
  try
    let norm_e =
      match rel with
      | Lt -> mk_bin_op Sub (mk_bin_op Sub e2 e1) (mk_iconst 1)
      | Le -> mk_bin_op Sub e2 e1
      | Gt -> mk_bin_op Sub (mk_bin_op Sub e1 e2) (mk_iconst 1)
      | Ge -> if is_zero_exp e2 then e1 else mk_bin_op Sub e1 e2
      | _ -> raise UnexpectedOp
    in
    mk_bin_rel Ge norm_e zero ~norm:false ~pos:pos
  with _ -> mk_bin_rel rel e1 e2 ~pos:pos

let norm_p_ineq (p: pure_form): pure_form =
  let fp p =
    match p with
    | BinRel (rel, e1, e2, pos) -> Some (norm_bin_rel_ineq rel e1 e2 ~pos:pos)
    | _ -> None
  in
  map_p (fp, fnone) p

let norm_p_eq (p: pure_form): pure_form =
  let fp p =
    match p with
    | BinRel (Eq, e1, e2, pos) ->
      let f1 = mk_bin_rel Ge (mk_bin_op Sub e1 e2) (mk_iconst 0) ~pos:pos in
      let f2 = mk_bin_rel Ge (mk_bin_op Sub e2 e1) (mk_iconst 0) ~pos:pos in
      Some (mk_pconj [f1; f2] ~pos:pos)
    | _ -> None
  in
  map_p (fp, fnone) p

let norm_p_neq (p: pure_form): pure_form =
  let fp p =
    match p with
    | BinRel (Ne, e1, e2, pos) ->
      let f1 = mk_bin_rel Gt e1 e2 ~pos:pos in
      let f2 = mk_bin_rel Lt e1 e2 ~pos:pos in
      Some (mk_pdisj [f1; f2] ~pos:pos)
    | _ -> None
  in
  map_p (fp, fnone) p

let norm_p_null (p: pure_form): pure_form =
  let fp p =
    match p with
    | BinRel (Eq, e, (Null _), pos)
    | BinRel (Eq, (Null _), e, pos) ->
      Some (mk_bin_rel Eq e (mk_iconst 0) ~pos:pos)
    | BinRel (Ne, e, (Null _), pos)
    | BinRel (Ne, (Null _), e, pos) ->
      Some (mk_bin_rel Gt e (mk_iconst 0) ~pos:pos)
    | _ -> None
  in
  map_p (fp, fnone) p

let norm_p (p: pure_form) =
  p |> norm_p_null |>
  norm_p_eq |> norm_p_neq |>
  norm_p_ineq

let norm_p (p: pure_form) =
  DB.trace_1 "norm_p" (pr_pf, pr_pf) p
    (fun () -> norm_p p)

let norm_pent (pe: pure_entail): pure_entail =
  { pe with
    pent_lhs = norm_p pe.pent_lhs;
    pent_rhs = norm_p pe.pent_rhs; }

let rec elim_exists_ante (f: pure_form): pure_form =
  match f with
  | PExists (vs, pf, _) -> elim_exists_ante (rename_all_qvars_pf f)
  | _ -> f

(* let norm_pentails (pents: pure_entail list): pure_entail list = *)
(*   let pents = List.map (fun pent -> *)
(*     { pent with pent_lhs = elim_exists_ante pent.pent_lhs }) *)
(*     pents in *)
(*   pents |> List.map NO.transform_horn_entails |> List.concat *)


(************************************)
(*** Horn entailment in term form ***)

type fent = {
  fent_id: int;
  fent_vars: var list;
  fent_unk_coes: unk_coes_rel list;
  fent_lhs: fform;
  fent_rhs: fterm;
  fent_pos: pos; }

let pr_fent (fe: fent) =
  (pr_fform fe.fent_lhs) ^ " --> " ^ (pr_fterm fe.fent_rhs)

(* Assume that pe is already a Horn-clause *)
let mk_fent prog (pe: pure_entail): fent list =
  let ante = pe.pent_lhs in
  let cons = pe.pent_rhs in
  let vs = [ante; cons] |> List.map fv_pf |>
           List.concat |> dedup_vs in
  let f_unk_coes =
    (TL.get_unk_coes_pf prog ante) @ (TL.get_unk_coes_pf prog cons) |>
    TL.dedup_unk_coes_rels in
  let ante = unfold_rform_pf prog.prog_rels ante in
  let cons = unfold_rform_pf prog.prog_rels cons in
  let sante =
    ante |> NO.simplify_all_pf |>
    norm_p |> NO.transform_dnf in
  let scons =
    cons |> NO.simplify_all_pf |>
    norm_p |> NO.transform_cnf in
  let ante_disj = match sante with
    | PDisj (fs, _) -> fs
    | _ -> [sante] in
  let () = DB.nhprint "ante_disj: \n" (pr_items ~bullet:"  #" pr_pf) ante_disj in
  let cons_conj = match scons with
    | PConj (fs, _) -> fs
    | _ -> [scons] in
  List.map (fun a ->
    List.map (fun c ->
      let fa = fterm_of_pf vs a in
      let fa, fc =
        match c with
        | PDisj (cs, _) -> (
          match cs with
          | [] -> fa, []
          | f::[] -> fa, fterm_of_pf vs f
          | f::fs ->
            let neg_fs = List.map (fun f ->
              (* !(e>=0) <-> -e-1>=0 *)
              let ft = fterm_of_pf vs f in
              let m_one = [term_of_int (-1)] in
              List.map (fun t ->
                mk_add_fterm (mk_mul_fterm t m_one) m_one) ft
            ) fs |> List.concat in
            fa @ neg_fs, fterm_of_pf vs f)
        | _ -> fa, fterm_of_pf vs c
      in
      List.map (fun tc ->
        { fent_id = pe.pent_id;
          fent_vars = vs;
          fent_unk_coes = f_unk_coes;
          fent_lhs = fa;
          fent_rhs = tc;
          fent_pos = pe.pent_pos; }) fc
    ) cons_conj
  ) ante_disj |> List.concat |> List.concat

let mk_fent prog (pe: pure_entail): fent list =
  DB.trace_1 "mk_fent" (pr_pent, pr_list pr_fent) pe
    (fun () -> mk_fent prog pe)

type pfent = {
  pfent_id: int;
  pfent_vars: var list;
  pfent_unk_coes: unk_coes_rel list;
  pfent_f: fform;
  pfent_pos: pos; }

let pr_pfent (fe: pfent) = (pr_fform fe.pfent_f)

let mk_pfent prog (pe: pure_entail): pfent list =
  let ante = pe.pent_lhs |> NO.simplify_all_pf in
  let cons = pe.pent_rhs |> NO.simplify_all_pf in
  let vs = [ante; cons] |> List.map fv_pf |>
           List.concat |> dedup_vs in
  let f_unk_coes =
    (TL.get_unk_coes_pf prog ante) @ (TL.get_unk_coes_pf prog cons) |>
    TL.dedup_unk_coes_rels in
  let sante = unfold_rform_pf prog.prog_rels ante in
  let scons = unfold_rform_pf prog.prog_rels cons in
  let () = DB.nhprint "sante: " pr_pf sante in
  let () = DB.nhprint "scons: " pr_pf scons in
  let f =
    mk_pconj [sante; mk_pneg scons] |>
    NO.simplify_all_pf |> norm_p |>
    NO.transform_dnf in
  let f_disj = match f with
    | PDisj (fs, _) -> fs
    | _ -> [f] in
  List.map (fun f_conj ->
    { pfent_id = pe.pent_id;
      pfent_vars = vs;
      pfent_unk_coes = f_unk_coes;
      pfent_f = fterm_of_pf vs f_conj;
      pfent_pos = pe.pent_pos; }) f_disj

(**********************)
(*** Farkas's Lemma ***)

let index_lambda_farkas = ref 0

let lambda_var_prefix = "lambda_"

let fresh_lambda_index () =
  index_lambda_farkas := !index_lambda_farkas + 1;
  !index_lambda_farkas

let fresh_lambda_var () =
  mk_var (lambda_var_prefix ^ (string_of_int (fresh_lambda_index ()))) TInt

let gen_farkas_constr_fent (fe: fent): pure_form list * var list =
  let vs = fe.fent_vars in
  let fante = fe.fent_lhs @ [fterm_of_exp vs (mk_iconst 1)] in
  let lambda_fante, lambda_vs = List.map (fun ft ->
    let lambda_v = fresh_lambda_var () in
    let lambda_t = term_of_var vs lambda_v in
    (mk_mul_fterm [lambda_t] ft, lambda_v)) fante |> List.split in
  let neg_fcons = List.map (fun t ->
    { t with term_coe = mk_bin_op Mul (mk_iconst (-1)) t.term_coe}
  ) fe.fent_rhs in
  let () = DB.nhprint "neg_fcons: " pr_fterm neg_fcons in
  let sum_lambda_fante = List.fold_right (fun ft s ->
    mk_add_fterm ft s) lambda_fante neg_fcons in
  let () = DB.nhprint "sum_lambda_fante: " pr_fterm sum_lambda_fante in
  let constrs =
    let zero = mk_iconst 0 in
    let c1 = sum_lambda_fante |>
             List.map (fun t -> mk_bin_rel Eq t.term_coe zero) in
    let c2 = lambda_vs |>
             List.map (fun v -> mk_bin_rel Ge (mk_exp_var v) zero) in
    c1 @ c2 in
  constrs, lambda_vs

let gen_farkas_constr_pfent (fe: pfent): pure_form list * var list =
  let vs = fe.pfent_vars in
  let lambda_f, lambda_vs = List.map (fun ft ->
    let lambda_v = fresh_lambda_var () in
    let lambda_t = term_of_var vs lambda_v in
    (mk_mul_fterm [lambda_t] ft, lambda_v)) fe.pfent_f |> List.split in
  let lambda_pos_v = fresh_lambda_var () in
  let sum_lambda_f = List.fold_left (fun s ft ->
    mk_add_fterm ft s) [term_of_var vs lambda_pos_v] lambda_f in
  let constrs =
    let zero = mk_iconst 0 in
    let c1 = sum_lambda_f |>
             List.map (fun t -> mk_bin_rel Eq t.term_coe zero) in
    let c2 = lambda_vs |>
             List.map (fun v -> mk_bin_rel Ge (mk_exp_var v) zero) in
    let c3 = mk_bin_rel Gt (mk_exp_var lambda_pos_v) zero in
    c1 @ c2 @ [c3] in
  constrs, lambda_vs @ [lambda_pos_v]

let is_feasible_model rdefns (pents: pure_entail list) model : bool =
  let ssts = model in
  let unfold_and_subst rdefns ssts f =
    f |> unfold_rform_pf rdefns |> subst_pf ssts in
  let non_contra_pents = List.filter (fun pe ->
    FP.check_sat (mk_pconj [pe.pent_lhs; pe.pent_rhs]) != MvlFalse) pents in
  if non_contra_pents = [] then true
  else
    List.exists (fun pe ->
      let ante = unfold_and_subst rdefns ssts pe.pent_lhs in
      FP.check_sat ante != MvlFalse) non_contra_pents

let is_feasible_rel_defn (rel: rel_defn) model : bool =
  let body =
    (match rel.rel_body with
     | RbTemplate tmpl -> tmpl.templ_body
     | RbForm f -> f
     | RbUnknown -> error "is_feasible_rel_defn: not expect Unknown relation") |>
    rename_all_qvars_pf |> subst_pf model in
  FP.check_sat body != MvlFalse

let rec find_feasible_model f_sat prog pents constrs =
  let is_sat, model = f_sat constrs in
  match is_sat with
  | MvlTrue ->
    let rel_defns = find_rel_defn_pents prog.prog_rels pents in
    if List.exists (fun rel -> not (is_feasible_rel_defn rel model)) rel_defns then MvlUnkn, []
    else if is_feasible_model prog.prog_rels pents model then is_sat, model
    else
      let () = DB.dhprint "infeasible model: " pr_model model in
      let neg_model =
        (* List.map (fun (v, e) -> mk_eq_exp (mk_exp_var v) e) model |> *)
        (* mk_pconj |> mk_pneg *)
        List.map (fun (v, e) -> (mk_exp_var v, e)) model |>
        FP.mk_conj_constrs (fun (v1, e1) (v2, e2) ->
          mk_eq_exp (mk_bin_op Mul v1 e2) (mk_bin_op Mul v2 e1)) |>
        mk_pconj |> mk_pneg
      in
      let n_constrs = mk_pconj [constrs; neg_model] in
      find_feasible_model f_sat prog pents n_constrs
  | _ -> is_sat, model

let gen_templ (tk: TL.templ_kind) prog rnames : program =
    (match tk with
   | TL.LinearT -> (new TL.LinearTempl.templ) # update_rel_defn
   | TL.EqArithT -> (new TL.EqArithTempl.templ) # update_rel_defn
   | TL.ConjT n -> (new TL.ConjTempl.templ n) # update_rel_defn
   | TL.EqArithConjT n -> (new TL.EqArithConjTempl.templ n) # update_rel_defn
   | TL.EqPtrConjT n -> (new TL.EqPtrConjTempl.templ n) # update_rel_defn
   | TL.EqPtrT -> (new TL.EqPtrTempl.templ) # update_rel_defn
   | TL.NePtrT -> (new TL.NePtrTempl.templ) # update_rel_defn
   | TL.IncrT (t, _) -> (new TL.IncrTempl.templ t) # update_rel_defn)
    tk prog rnames

let solve_pentails_templ (tk: TL.templ_kind) prog rnames
    (pents: pure_entail list) : (mvlogic * model * program) =
  let prog = gen_templ tk prog rnames in
  let fents = pents |> List.map (mk_fent prog) |> List.concat in
  let fents_unk_coes =
    fents |> List.map (fun fent -> fent.fent_unk_coes) |>
    List.concat |> TL.dedup_unk_coes_rels in
  let farkas_constrs, _ =
    fents |> List.map gen_farkas_constr_fent |>
    List.split |>
    (fun (fc, fvs) -> (List.concat fc), (List.concat fvs)) in
  let () = DB.nhprint "pents: " (pr_list pr_pent) pents in
  let () = DB.nhprint "fents: "  (pr_list pr_fent) fents in
  let () = DB.nhprint "farkas_constrs: " (pr_list pr_pf) farkas_constrs in
  let is_sat, farkas_model =
    let constrs = mk_pconj farkas_constrs in
    let fp_sat = FP.check_sat_and_get_opt_model tk fents_unk_coes in
    find_feasible_model fp_sat prog pents constrs in
  is_sat, farkas_model, prog

let solve_pentails_ptr_templ (tk: TL.templ_kind) prog rnames
    (pents: pure_entail list) : (mvlogic * model * program) =
  let prog = gen_templ tk prog rnames in
  let fents = pents |> List.map (mk_pfent prog) |> List.concat in
  let fents_unk_coes =
    fents |> List.map (fun fent -> fent.pfent_unk_coes) |>
    List.concat |> TL.dedup_unk_coes_rels in
  let farkas_constrs, _ =
    fents |> List.map gen_farkas_constr_pfent |>
    List.split |>
    (fun (fc, fvs) -> (List.concat fc), (List.concat fvs)) in
  let () = DB.nhprint "pents: " (pr_list pr_pent) pents in
  let () = DB.nhprint "fents: "  (pr_items ~bullet:"\n" pr_pfent) fents in
  let () = DB.nhprint "farkas_constrs: " (pr_list pr_pf) farkas_constrs in
  let is_sat, farkas_model =
    let constrs = mk_pconj farkas_constrs in
    let fp_sat = FP.check_sat_and_get_ptr_model tk fents_unk_coes in
    find_feasible_model fp_sat prog pents constrs
  in
  is_sat, farkas_model, prog

let normalize_ptr (f: pure_form) : pure_form =
  let extract_vars (e: exp) : var list =
    match e with
    | Var (u, _) -> [u]
    | BinOp (Sub, Var (u, _), Var (v, _), _) -> [u; v]
    | LTerm (([(1, u); (-1, v)], 0), _) -> [u; v]
    | LTerm (([(-1, u); (1, v)], 0), _) -> [u; v]
    | _ -> [] in
  let pfs = f |> collect_pure_conjuncts_pf in
  pfs |>
  List.map (fun pf -> match pf with
    | BinRel (Eq, e, IConst (i, _), _)
    | BinRel (Eq, IConst (i, _), e, _) ->
      let vs = fv_exp e in
      if (List.exists (fun v -> is_ptr_typ (typ_of_var v)) vs) then
        let vs = extract_vars e in
        match vs, i with
        | [], _ -> pf
        | [v], 0 -> mk_eq_null_var v
        | [v], _ -> mk_neq_null_var v
        | [u; v], 0 -> mk_eq_var u v
        | [u; v], _ -> mk_neq_var u v
        | _ -> pf
      else pf
    | BinRel (Ne, e, IConst (i, _), _)
    | BinRel (Ne, IConst (i, _), e, _) ->
      let vs = fv_exp e in
      if (List.exists (fun v -> is_ptr_typ (typ_of_var v)) vs) then
        let vs = extract_vars e in
        match vs, i with
        | [v], 0 -> mk_neq_null_var v
        | [u; v], 0 -> mk_neq_var u v
        | _ -> pf
      else pf
    | _ -> pf) |>
  mk_pconj

let rec sst_model_rels?(norm_ptr=false) prog pents model =
  let pr_model = pr_list (pr_pair pr_var pr_exp) in
  DB.trace_1 "sst_model_rels" (pr_model, pr_rels) model
    (fun () -> sst_model_rels_x ~norm_ptr:norm_ptr prog pents model)

and sst_model_rels_x ?(norm_ptr=false) prog pents model =
  let () = DB.nhprint "MODEL: " pr_model model in
  let ssts = model in
  (* let solved_coes = List.map fst ssts in *)
  let solved_rel_defns =
    pents |>
    List.map (fun p -> [p.pent_lhs; p.pent_rhs]) |> List.concat |>
    find_rel_defn_pfs prog.prog_rels |>
    List.fold_left (fun acc rd ->
      DB.nhprint "rel_name: " pr_id rd.rel_name;
      match rd.rel_body with
      | RbUnknown ->
        error ("is_feasible_rel_defn: unknown relation: " ^ (pr_rd rd))
      | RbForm _ -> acc
      | RbTemplate tmpl ->
        let rbody = match tmpl.templ_dummy with
          | true -> RbUnknown
          | _ ->
            let body = tmpl.templ_body |> subst_pf ssts in
            let nbody = NO.simplify_all_pf body in
            let nbody =
              if norm_ptr then NO.simplify_all_pf (normalize_ptr nbody)
              else nbody in
            let () = DB.nhprint "body: " pr_pf body in
            let () = DB.nhprint "nbody: " pr_pf nbody in
            RbForm nbody in
        let nrd = {rd with rel_body = rbody} in
        nrd :: acc) [] in
  solved_rel_defns

let solve_pentails_ptr (tk: TL.templ_kind) prog rnames pents cont =
  let is_sat, model, nprog = solve_pentails_ptr_templ tk prog rnames pents in
  if is_sat = MvlTrue then
    sst_model_rels ~norm_ptr:true nprog pents model
  else cont ()

let solve_pentails_arith (tk: TL.templ_kind) prog rnames pents cont =
  (* DB.pprint "solve_pentails_templ: Starting ..."; *)
  let is_sat, farkas_model, nprog = solve_pentails_templ tk prog rnames pents in
  if is_sat = MvlTrue then sst_model_rels nprog pents farkas_model
  else cont ()

let rec solve_pentails_arith_weak prog (n: int) rnames pents : rel_defn list =
  if (n < 1 || n > !thd_max_templ_conj) then []
  else
    let tk =
      if (n == 1) then TL.LinearT
      else TL.ConjT n in
    solve_pentails_arith tk prog rnames pents
      (fun () -> solve_pentails_arith_weak prog (n+1) rnames pents)

let solve_pentails_arith_strong prog rnames pents : rel_defn list =
  (* Try EqTempl first *)
  let rels = solve_pentails_arith TL.EqArithT prog rnames pents (fun () -> []) in
  if rels = [] then
    solve_pentails_arith (TL.EqArithConjT 1) prog rnames pents (fun () -> [])
  else rels
    (* let apents = List.fold_left (fun acc rel -> *)
    (*   match rel.rel_body with *)
    (*   | RbForm f -> *)
    (*     let ante = *)
    (*       let args = (List.map mk_exp_var rel.rel_params) in *)
    (*       mk_prel (mk_rform rel.rel_name args) in *)
    (*     acc @ [mk_pure_entail ante f] *)
    (*   | _ -> acc) [] rels in *)
    (* let () = DB.hprint "additional pents: " pr_ents apents in *)
    (* solve_pentails_arith (TL.EqArithConjT 1) prog rnames (pents @ apents) (fun () -> rels) *)

(* strong: returns as strong as possible solution *)
let rec solve_pentails_precise prog ?(rnames=[]) strong pents : rel_defn list =
  let pr_inf b = if b then "Infer Strong" else "Infer Weak" in
  DB.trace_2 "solve_pentails_precise" (pr_ents, pr_inf, pr_rels) pents strong
    (fun () -> solve_pentails_precise_x prog ~rnames:rnames strong pents)

and solve_pentails_precise_x prog ?(rnames=[]) strong pents : rel_defn list =
  let rnames =
    if rnames = [] then find_template_rel_names prog.prog_rels pents
    else rnames in
  if List.exists is_ptr_pure_entail pents then
    solve_pentails_ptr TL.NePtrT prog rnames pents
      (fun () -> solve_pentails_ptr (TL.EqPtrConjT 2) prog rnames pents
          (fun () -> solve_pentails_ptr (TL.EqPtrConjT 2) prog rnames pents (fun () -> [])))
  else if (not strong) then
    solve_pentails_arith_weak prog 1 rnames pents
  else solve_pentails_arith_strong prog rnames pents

let rec solve_pentails_partial prog rnames strong pents : rel_defn list =
  let pr_inf b = if b then "Infer Strong" else "Infer Weak" in
  DB.trace_2 "solve_pentails_partial" (pr_ents, pr_inf, pr_rels) pents strong
    (fun () -> solve_pentails_partial_x prog rnames strong pents)

and solve_pentails_partial_x prog rnames strong pents : rel_defn list =
  let rec solve_subset cand_pents other_pents =
    let rdefns = solve_pentails_precise prog ~rnames:rnames strong cand_pents in
    if rdefns != [] then rdefns
    else match other_pents with
      | [] -> rdefns
      | pe::pes -> solve_subset (cand_pents @ [pe]) pes in
  solve_subset [] pents

(* strong: returns as strong as possible solution *)
let rec solve_pentails prog (strong: bool) (pents: pure_entail list)
  : farkas_solution =
  let pr_inf b = if b then "Infer Strong" else "Infer Weak" in
  DB.trace_2 "solve_pentails" (pr_ents, pr_inf, pr_fsol) pents strong
    (fun () -> solve_pentails_x prog strong pents)

and solve_pentails_x prog strong pents : farkas_solution =
  let rnames =
    pents |>
    List.map (fun pent -> [pent.pent_lhs; pent.pent_rhs]) |> List.concat |>
    find_rel_defn_pfs prog.prog_rels |>
    List.filter (fun rdefn -> is_unk_rdefn rdefn) |>
    List.map (fun rdefn -> rdefn.rel_name) |> dedup_ss in
  if (rnames = []) then
    error "solve_pentails: expect 1 but found 0 unknown relation"
  else if (List.length rnames > 1) then
    error "solve_pentails: expect 1 but found many unknown relations"
  else  (* there is only 1 unknown relation *)
    let rdefns = solve_pentails_precise prog ~rnames:rnames strong pents in
    match rdefns with
    | [] ->
      let pents = List.sort compare_pure_entail_by_size pents in
      let rdefns = solve_pentails_partial prog rnames strong pents in
      if (rdefns = []) then mk_fsol_no_solution ()
      else mk_fsol_partial rdefns pents
    | _ -> mk_fsol_precise rdefns
