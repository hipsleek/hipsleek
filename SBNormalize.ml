open SBGlobals
open SBLib
open SBLib.Func
open SBMath
open SBCast

module LA = SBLinarith
module TL = SBTemplate
module DB = SBDebug

let time_simplify_all = ref 0.
let time_simplify_all_pf = ref 0.

(***************************************************************)
(***************   rename shadowed variables   *****************)


(** push quantified variables inward *)
let rec push_qvars_inward_pf (f: pure_form) : pure_form =
  DB.trace_1 "push_qvars_inward_pf" (pr_pf, pr_pf) f
    (fun () -> push_qvars_inward_pf_x f)

and push_qvars_inward_pf_x (f: pure_form) : pure_form =
  let rec push g = match g with
    | BConst _ | BinRel _ | PRel _ -> g
    | PNeg (g0, p) -> mk_pneg (push g0) ~pos:p
    | PConj (gs, p) -> PConj (List.map push gs, p)
    | PDisj (gs, p) -> PDisj (List.map push gs, p)
    | PForall (vs, g0, p) -> let ng0 = push g0 in push_forall vs ng0 p
    | PExists (vs, g0, p) -> let ng0 = push g0 in push_exists vs ng0 p
  and push_forall vs g p = match g with
    | BConst _ | BinRel _ | PRel _ -> PForall (vs, g, p)
    | PExists _ | PNeg _ -> PForall (vs, g, p)
    | PConj (gs, p0) ->
      let gs = gs |> List.map (fun x -> PForall (vs, x, pos_of_pf x)) in
      PConj (gs, p0)
    | PDisj (gs, p0) ->
      let gs1, gs2 =
        List.partition (fun x -> intersected_vs (fv_pf x) vs) gs in
      if gs1 = [] then PDisj (gs2, p)
      else if gs2 = [] then PForall (vs, PDisj (gs1, p), p)
      else PDisj ((PForall (vs, (PDisj (gs1, p)), p)) :: gs2, p)
    | PForall (vs0, g0, p0) -> push_forall (dedup_vs (vs @ vs0)) g0 p0
  and push_exists vs g p = match g with
    | BConst _ | BinRel _ | PRel _ -> mk_pexists vs g ~pos:p
    | PForall _ | PNeg _ -> mk_pexists vs g ~pos:p
    | PDisj (gs, p0) ->
      let gs = gs |> List.map (fun x -> mk_pexists vs x ~pos:(pos_of_pf x)) in
      PDisj (gs, p0)
    | PConj (gs, p0) ->
      let gs1, gs2 =
        List.partition (fun x -> intersected_vs (fv_pf x) vs) gs in
      if gs1 = [] then PConj (gs2, p)
      else if gs2 = [] then PExists (vs, PConj (gs1, p), p)
      else PConj ((PExists (vs, (PConj (gs1, p)), p)) :: gs2, p)
    | PExists (vs0, g0, p0) -> push_exists (dedup_vs (vs @ vs0)) g0 p0 in
  push f

(** push quantified variables inward *)
let rec push_qvars_inward (f: formula) : formula =
  DB.trace_1 "push_qvars_inward" (pr_f, pr_f) f
    (fun () -> push_qvars_inward_x f)

and push_qvars_inward_x (f: formula) : formula =
  let rec push f = match f with
    | FBase (hf, pf, p) -> FBase (hf, push_qvars_inward_pf pf, p)
    | FExists (vs, g, p) ->
      let ng = push g in
      let hvs = fv_hf (extract_hf ng) in
      let qvs, pqvs = List.partition (fun x -> mem_vs x hvs) vs in
      if (qvs = []) then (mk_fexists pqvs ng)
      else FExists (qvs, mk_fexists pqvs ng, p)
    | FForall (vs, g, p) ->
      let ng = push g in
      let hvs = fv_hf (extract_hf ng) in
      let qvs, pqvs = List.partition (fun x -> mem_vs x hvs) vs in
      if (qvs = []) then (mk_fforall pqvs ng)
      else FForall (qvs, mk_fforall pqvs ng, p) in
  (* TODO: to implement  *)
  push f

(***************************************************************)
(***************   rename shadowed variables   *****************)

let create_unshadowing_renaming vs used_vars =
  let shadowed_vs, other_vs = List.partition (fun x ->
    mem_vs x used_vars) vs in
  let new_vs = List.map fresh_var shadowed_vs in
  let rnms = List.combine shadowed_vs new_vs in
  let nvs = new_vs @ other_vs in
  (nvs, rnms)

let rec rename_shadowing_var_pf used_vars f = match f with
  | BConst _ | BinRel _ | PRel _ -> f
  | PNeg (f0, p) ->
    mk_pneg (rename_shadowing_var_pf used_vars f0) ~pos:p
  | PConj (fs, p) ->
    PConj (List.map (rename_shadowing_var_pf used_vars) fs, p)
  | PDisj (fs, p) ->
    PDisj (List.map (rename_shadowing_var_pf used_vars) fs, p)
  | PForall (vs, f0, p) ->
    let nvs, rnms = create_unshadowing_renaming vs used_vars in
    let nf0 = rename_var_pf rnms f0 in
    let nf0 = rename_shadowing_var_pf (nvs @ used_vars) nf0 in
    PForall (nvs, nf0, p)
  | PExists (vs, f0, p) ->
    let nvs, rnms = create_unshadowing_renaming vs used_vars in
    let nf0 = rename_var_pf rnms f0 in
    let nf0 = rename_shadowing_var_pf (nvs @ used_vars) nf0 in
    PExists (nvs, nf0, p)

let rec rename_shadowing_var used_vars f = match f with
  | FBase (hf, pf, p) ->
    let nused_vars = used_vars@(av_hf hf) in
    FBase (hf, rename_shadowing_var_pf nused_vars pf, p)
  | FExists (vs, f0, p) ->
    let nvs, rnms = create_unshadowing_renaming vs used_vars in
    let nf0 = rename_var_f rnms f0 in
    let nf0 = rename_shadowing_var (nvs @ used_vars) nf0 in
    FExists (nvs, nf0, p)
  | FForall (vs, f0, p) ->
    let nvs, rnms = create_unshadowing_renaming vs used_vars in
    let nf0 = rename_var_f rnms f0 in
    let nf0 = rename_shadowing_var (nvs @ used_vars) nf0 in
    FForall (nvs, nf0, p)

let rename_shadowing_var_ent entail =
  let ante = rename_shadowing_var [] entail.ent_lhs in
  let conseq = rename_shadowing_var (av ante) entail.ent_rhs in
  {entail with ent_lhs = ante; ent_rhs = conseq}

let rename_shadowing_var_vdefn view =
  let used_vars = view.view_params in
  let ndefn_cases, nused_vars = List.fold_left (
    fun (acc_cases, acc_uvars) vdc ->
      let nf = rename_shadowing_var acc_uvars vdc.vdc_form in
      let nvdc = {vdc with vdc_form = nf} in
      let nacc_cases = nvdc :: acc_cases in
      let nacc_uvars = dedup_vs (acc_uvars @ (av nf)) in
      nacc_cases, nacc_uvars) ([], used_vars) view.view_defn_cases in
  {view with view_defn_cases = ndefn_cases}

(******************************************************)
(***************   simplify redundant *****************)
let rec simplify_redundant_pf f =
  SBDebug.trace_1 "simplify_redundant_pf" (pr_pf, pr_pf) f
    (fun () -> simplify_redundant_pf_x f)

and simplify_redundant_pf_x f =
  let remove_redundant pfs =
    List.fold_left (fun acc x ->
      if (List.exists (eq_patom x) acc) then acc
      else x :: acc) [] pfs in
  let rec simplify g = match g with
    | BConst _ | BinRel _ | PRel _ -> g
    | PConj (gs, p) ->
      let ngs = List.map simplify gs in
      let ngs =
        if (List.for_all is_patom ngs) then remove_redundant ngs
        else ngs in
      PConj (ngs, p)
    | PDisj (gs, p) ->
      let ngs = List.map simplify gs in
      let ngs =
        if (List.for_all is_patom ngs) then remove_redundant ngs
        else ngs in
      PDisj (ngs, p)
    | PNeg (g, p) -> mk_pneg (simplify g) ~pos:p
    | PForall (vs, g, p) -> PForall (vs, simplify g, p)
    | PExists (vs, g, p) -> PExists (vs, simplify g, p) in
  simplify f

let rec simplify_redundant f =
  SBDebug.trace_1 "simplify_redundant" (pr_f, pr_f) f
    (fun () -> simplify_redundant_x f)

and simplify_redundant_x f =
  let rec simplify f = match f with
    | FBase (hf, pf, pos) -> FBase (hf, simplify_redundant_pf pf, pos)
    | FExists (vs, f, pos) -> FExists (vs, simplify f, pos)
    | FForall (vs, f, pos) -> FForall (vs, simplify f, pos) in
  simplify f


(************************************************************************)
(***************   simplify tautology & contradiction   *****************)

let rec check_patom_tauto pf =
  SBDebug.trace_1 "check_patom_tauto" (pr_pf, pr_bool) pf
    (fun () -> check_patom_tauto_x pf)

and check_patom_tauto_x pf = match pf with
  | BConst (true, _) -> true
  | BConst (false, _) -> false
  | BinRel (rel, e1, e2, p) ->
    if (is_int_exp e1) || (is_int_exp e2) then
      let diff = mk_bin_op Sub e1 e2 in
      match rel with
      | Lt -> is_negative_exp diff
      | Le -> is_non_positive_exp diff
      | Gt -> is_positive_exp diff
      | Ge -> is_non_negative_exp diff
      | Eq -> is_zero_exp diff
      | Ne -> is_non_zero_exp diff
    else if (rel = Eq) && (eq_exp e1 e2) then true
    else false
  | _ -> error ("check_patom_tauto: not a pure atom" ^ (pr_pf pf))

let check_patom_contra pf = match pf with
  | BConst (true, _) -> true
  | BConst (false, _) -> false
  | BinRel (rel, e1, e2, p) ->
    if (eq_t (typ_of_exp e1) TInt) then
      let diff = mk_bin_op Sub e1 e2 in
      match rel with
      | Lt -> is_non_negative_exp diff
      | Le-> is_positive_exp diff
      | Gt -> is_non_positive_exp diff
      | Ge -> is_negative_exp diff
      | Eq -> is_non_zero_exp diff
      | Ne -> is_zero_exp diff
    else if (rel = Ne) && (eq_exp e1 e2) then true
    else false
  | _ -> error ("check_patom_contra: not a pure atom" ^ (pr_pf pf))

let rec simplify_tauto_contra_pf f =
  SBDebug.trace_1 "simplify_tauto_contra_pf" (pr_pf, pr_pf) f
    (fun () -> simplify_tauto_contra_pf_x f)

and simplify_tauto_contra_pf_x f =
  let rec simplify g = match g with
    | BConst _ -> g
    | BinRel _ ->
      if (check_patom_tauto g) then BConst(true, pos_of_pf g)
      else if (check_patom_contra g) then BConst(false, pos_of_pf g)
      else g
    | PRel _ -> g
    | PNeg (g0, p) ->
      let ng0 = simplify g0 in
      if (is_true_pf ng0) then BConst (false, p)
      else if (is_false_pf ng0) then BConst (true, p)
      else mk_pneg ng0 ~pos:p
    | PConj (gs, p) ->
      let gs = List.map simplify gs in
      if (List.exists is_false_pf gs) then BConst (false, p)
      else
        let gs = List.filter (fun x -> not (is_true_pf x)) gs in
        if (gs = []) then BConst (true, p) else PConj (gs, p)
    | PDisj (gs, p) ->
      let gs = List.map simplify gs in
      if (List.exists is_true_pf gs) then BConst (true, p)
      else
        let gs = List.filter (fun x -> not (is_false_pf x)) gs in
        if (gs = []) then BConst (false, p) else PDisj (gs, p)
    | PForall (vs, g, p) ->
      let ng = simplify g in
      if (is_true_pf ng) || (is_false_pf ng) then ng
      else
        let qvs = intersect_vs vs (fv_pf ng) in
        if (qvs = []) then ng else PForall (qvs, ng, p)
    | PExists (vs, g, p) ->
      let ng = simplify g in
      if (is_true_pf ng) || (is_false_pf ng) then ng
      else
        let qvs = intersect_vs vs (fv_pf ng) in
        if (qvs = []) then ng else PExists (qvs, ng, p) in
  simplify f

let rec simplify_tauto_contra f =
  SBDebug.trace_1 "simplify_tauto_contra" (pr_f, pr_f) f
    (fun () -> simplify_tauto_contra_x f)

and simplify_tauto_contra_x f =
  let rec simplify g = match g with
    | FBase (hg, pg, p) ->
      FBase (hg, simplify_tauto_contra_pf pg, p)
    | FExists (vs, g, p) ->
      let ng = simplify g in
      let qvs = intersect_vs vs (fv ng) in
      if (qvs = []) then ng
      else FExists (qvs, ng, p)
    | FForall (vs, g, p) ->
      let ng = simplify g in
      let qvs = intersect_vs vs (fv ng) in
      if (qvs = []) then ng
      else FForall (qvs, ng, p) in
  simplify f

(*********************************************************)
(***************   simplify arithmetic   *****************)

let simplify_arith_exp exp  =
  if (typ_of_exp exp = TInt) then
    let pos = pos_of_exp exp in
    match (convert_exp_to_lterm exp) with
    | ([], c), None -> IConst (c, pos)
    | t, None -> LTerm (t, pos)
    | _ -> exp
  else exp

let rec simplify_arith_pf f =
  SBDebug.trace_1 "simplify_arith_pf" (pr_pf, pr_pf) f
    (fun () -> simplify_arith_pf_x f)

and simplify_arith_pf_x f =
  let mk_bin_rel brel lterm const p =
    let cvars, k = lterm in
    let coeffs, vars = List.split cvars in
    match coeffs with
    | [] -> BinRel (brel, LTerm (lterm, p), IConst (const, p), p)
    | c::_  ->
      if (c > 0) then BinRel (brel, LTerm (lterm, p), IConst (const, p), p)
      else
        let ncoeffs = List.map (fun i -> -i) coeffs in
        let nlterm = List.combine ncoeffs vars, k in
        let nbrel = match brel with
          | Eq | Ne -> brel
          | Lt -> Ge | Le -> Gt
          | Gt -> Le | Ge -> Lt in
        BinRel (nbrel, LTerm (nlterm, p), IConst (-const, p), p) in
  let simplify_brel brel e1 e2 p =
    let lterm, eopt = convert_exp_to_lterm (mk_bin_op Sub e1 e2) in
    match eopt with
    | None ->
      let cvars, const = lterm in
      if (cvars != []) then
        let coeffs, vars = cvars |> List.split in
        let k = coeffs |> gcd |> abs in
        if (k != 1) then
          let ncoeffs = coeffs |> List.map (fun x -> x / k) in
          let ncvars = List.combine ncoeffs vars in
          if (const mod k) = 0 then
            let nlterm = (ncvars, const / k) in
            mk_bin_rel brel nlterm 0 p
          else match brel with
            | Eq | Ne -> BinRel (brel, e1, e2, p)
            | Lt | Le ->
              let nlterm = (ncvars, 0) in
              let nconst =
                let nc = (-const / k) in
                if nc >= 0 then nc + 1 else nc in
              mk_bin_rel Lt nlterm nconst p
            | Gt | Ge ->
              let nlterm = (ncvars, 0) in
              let nconst =
                let nc = (-const / k) in
                if nc >= 0 then nc else nc + 1 in
              mk_bin_rel Lt nlterm nconst p
        else BinRel (brel, e1, e2, p)
      else BinRel (brel, e1, e2, p)
    |  _ -> BinRel (brel, e1, e2, p) in
  let rec simplify g = match g with
    | BConst _ | PRel _ -> g
    | BinRel (brel, e1, e2, p) ->
      let e1 = simplify_arith_exp e1 in
      let e2 = simplify_arith_exp e2 in
      if (typ_of_exp e1 = TInt) then simplify_brel brel e1 e2 p
      else g
    | PNeg (g, p) -> PNeg (simplify g, p)
    | PConj (gs, p) -> PConj (List.map simplify gs, p)
    | PDisj (gs, p) -> PDisj (List.map simplify gs, p)
    | PForall (vs, g, p) -> PForall (vs, simplify g, p)
    | PExists (vs, g, p) -> PExists (vs, simplify g, p) in
  simplify f


let rec simplify_arith_hf hf =
  SBDebug.trace_1 "simplify_arith_hf" (pr_hf, pr_hf) hf
    (fun () -> simplify_arith_hf_x hf)

and simplify_arith_hf_x hf =
  let rec simplify g = match g with
    | HEmp _ -> g
    | HAtom (dfs, vfs, p) ->
      let dfs = dfs |> List.map (fun df ->
        let nargs = List.map simplify_arith_exp df.dataf_args in
        {df with dataf_args = nargs}) in
      let vfs = vfs |> List.map (fun vf ->
        let nargs = List.map simplify_arith_exp vf.viewf_args in
        {vf with viewf_args = nargs}) in
      HAtom (dfs, vfs, p)
    | HStar (g1, g2, p) -> HStar (simplify g1, simplify g2, p)
    | HWand (g1, g2, p) -> HWand (simplify g1, simplify g2, p) in
  simplify hf

let rec simplify_arith f =
  SBDebug.trace_1 "simplify_arith" (pr_f, pr_f) f
    (fun () -> simplify_arith_x f)

and simplify_arith_x f =
  let rec simplify g = match g with
    | FBase (hg, pg, p) ->
      (* FBase (simplify_arith_hf hg, simplify_arith_pf pg, p) *)
      FBase (simplify_arith_hf hg, simplify_arith_pf pg, p)
    | FExists (vs, g, p) ->
      let ng = simplify g in
      let qvs = intersect_vs vs (fv ng) in
      if (qvs = []) then ng
      else FExists (qvs, ng, p)
    | FForall (vs, g, p) ->
      let ng = simplify g in
      let qvs = intersect_vs vs (fv ng) in
      if (qvs = []) then ng
      else FForall (qvs, ng, p) in
  simplify f

(**************************************************************************)
(*****************           collect substitution         *****************)

let collect_substs_from_equal_pf (f: pure_form) : substs =
  let fv acc v = Some acc in
  let fe acc e = Some acc in
  let fp acc p = match p with
    | BinRel (Eq, Var (v1, p1), Var (v2, p2), _) ->
      if (eq_var v1 v2) then Some acc
      else Some ((v1, Var (v2, p2)) :: (v2, Var (v1, p1)) :: acc)
    | BinRel (Eq, Var (v1, _), e2, _) when (typ_of_var v1 != TInt) ->
      Some ((v1, e2) :: acc)
    | BinRel (Eq, e1, Var (v2, _), _) when (typ_of_var v2 != TInt) ->
      Some ((v2, e1) :: acc)
    | BinRel (Eq, e1, e2, _) ->
      if (typ_of_exp e1 = TInt) then
        let lterm, eopt = convert_exp_to_lterm (mk_bin_op Sub e1 e2) in
        match (fst lterm), eopt with
        | [], _ -> Some acc
        | _, None ->
          let coeff_vars, const =
            let cvs, c = lterm in
            let cs, vs = List.split cvs in
            let gcd =
              if (c != 0) then Math.gcd (c::cs)
              else Math.gcd cs in
            let cs = List.map (fun x -> x / gcd) cs in
            let c = c / gcd in
            (List.combine cs vs, c) in
          let mk_sum cvs const = List.fold_left (fun acc (c, v) ->
            let tmp = mk_bin_op Mul (mk_iconst c) (mk_exp_var v) in
            mk_bin_op Add acc tmp) (mk_iconst const) cvs in
          let rec create_ssts head tail const acc =
            match tail with
            | [] -> acc
            | (c, v)::ntail ->
              let ssts =
                if (c = 1) then
                  let tmp = mk_sum (head @ ntail) const in
                  let exp = mk_bin_op Sub (mk_iconst 0) tmp in
                  [(v, exp)]
                else if (c = -1) then
                  let exp = mk_sum (head @ ntail) const in
                  [(v, exp)]
                else [] in
              (create_ssts (head @ [(c, v)]) ntail const acc) @ ssts in
          let ssts = create_ssts [] coeff_vars const [] in
          Some (acc @ ssts)
        | _, Some _ -> Some acc
      else Some acc
    | BinRel _ -> Some acc
    | PRel _ -> Some acc
    | PConj _ -> None
    | BConst _ | PNeg _ | PDisj _ | PForall _ | PExists _ -> Some acc in
  let ssts = fold_p (fp, fe, fv) [] f in
  ssts

let rec collect_substs_from_equal (f: formula) : substs =
  SBDebug.trace_1 "collect_substs_from_equal" (pr_f, pr_ssts) f
    (fun () -> (collect_substs_from_equal_x f))

and collect_substs_from_equal_x (f: formula) : substs =
  match f with
  | FBase (_, p, _) -> collect_substs_from_equal_pf p
  | FForall _ | FExists _ -> []

let rec collect_substs_var_var_from_equal (f: formula) : substs =
  SBDebug.trace_1 "collect_substs_var_var_from_equal" (pr_f, pr_ssts) f
    (fun () -> (collect_substs_var_var_from_equal_x f))

and collect_substs_var_var_from_equal_x (f: formula) : substs =
  let ssts = match f with
    | FBase (_, p, _) -> collect_substs_from_equal_pf p
    | FForall _ | FExists _ -> [] in
  List.filter (fun (v, e) -> match e with
    | Var _ -> true
    | _ -> false) ssts

(***************************************************************************)
(*****************           simplify equalities           *****************)

(* simplify both the lhs and the rhs of an entailment
   using equalities in the lhs.
   Return the new lhs, rhs and whether the entailment is updated *)
let rec simplify_equal_lhs_rhs lhs rhs : formula * formula =
  SBDebug.trace_2 "simplify_equal_lhs_rhs" (pr_f, pr_f, pr_pair pr_f pr_f) lhs rhs
    (fun () -> (simplify_equal_lhs_rhs_x lhs rhs))

and simplify_equal_lhs_rhs_x lhs rhs : formula * formula =
  let rec remove_equal lhs rhs =
    let ssts = collect_substs_from_equal lhs in
    match ssts with
    | [] -> lhs, rhs
    | _ ->
      DB.nhprint "SSTS: " pr_ssts ssts;
      let lptrvs = lhs |> fhv |> List.filter is_ptr_var in
      DB.nhprint "LPTRVS: " pr_vs lptrvs;
      let lhvs = lhs |> fhv in
      let lvs, rvs = fv lhs, fv rhs in
      let (v, e) =
        try List.find (fun (_, e) -> subset_vs (fv_exp e) lptrvs) ssts with _ ->
        try List.find (fun (v, e) ->
          (mem_vs v rvs) && not (intersected_vs (fv_exp e) rvs)) ssts with _ ->
        try List.find (fun (v, _) -> mem_vs v lhvs) ssts
        with _ -> List.hd ssts in
      DB.nhprint "SSTS EQ LEFT: " pr_ssts [(v, e)];
      let lhs, rhs = Pair.fold (subst [(v, e)]) lhs rhs in
      let lhs, rhs = Pair.fold simplify_tauto_contra lhs rhs in
      remove_equal lhs rhs in
  remove_equal lhs rhs

(* simplify both the lhs and the rhs of an entailment
   using equalities in the lhs.
   Return the new lhs, rhs and whether the entailment is updated *)
let simplify_equal_lhs_rhs_pf lhs rhs : pure_form * pure_form =
  let rec remove_equal lhs rhs =
    let ssts = collect_substs_from_equal_pf lhs in
    match ssts with
    | [] -> lhs, rhs
    | _ ->
      (* DB.hprint "SSTS: " pr_ssts ssts; *)
      let lvs, rvs = fv_pf lhs, fv_pf rhs in
      let (v, e) =
        try List.find (fun (v, e) ->
          (mem_vs v rvs) && not (intersected_vs (fv_exp e) rvs)) ssts
        with _ -> List.hd ssts in
      let lhs, rhs = Pair.fold (subst_pf [(v, e)]) lhs rhs in
      let lhs, rhs = Pair.fold simplify_tauto_contra_pf lhs rhs in
      remove_equal lhs rhs in
  remove_equal lhs rhs


(*********************************************************************)
(*****************           combine qvars           *****************)

let rec combine_qvars_pf (f: pure_form) : pure_form =
  SBDebug.trace_1 "combine_qvars" (pr_pf, pr_pf) f
    (fun () -> combine_qvars_pf_x f)

and combine_qvars_pf_x (f: pure_form) : pure_form =
  let rec combine g = match g with
    | BConst _ | BinRel _ | PRel _ -> g
    | PNeg (g0, pos) -> mk_pneg (combine g0) ~pos:pos
    | PDisj (gs, pos) -> PDisj (List.map combine gs, pos)
    | PConj (gs, pos) -> PConj (List.map combine gs, pos)
    | PForall (vs, g0, pos) -> (
        let ng0 = combine g0 in
        match ng0 with
        | PForall (us, ng1, _) -> PForall (vs @ us, ng1, pos)
        | _ -> PForall (vs, ng0, pos))
    | PExists (vs, g0, pos) -> (
        let ng0 = combine g0 in
        match ng0 with
        | PExists (us, ng1, _) -> PExists (vs @ us, ng1, pos)
        | _ -> PExists (vs, ng0, pos)) in
  combine f

let rec combine_qvars (f: formula) : formula =
  SBDebug.trace_1 "combine_qvars" (pr_f, pr_f) f
    (fun () -> combine_qvars_x f)

and combine_qvars_x (f: formula) : formula =
  let rec combine g = match g with
    | FBase (h, p, pos) -> FBase (h, combine_qvars_pf p, pos)
    | FForall (vs, g0, pos) -> (
        let ng0 = combine g0 in
        match ng0 with
        | FForall (us, ng1, _) -> FForall (vs @ us, ng1, pos)
        | _ -> FForall (vs, ng0, pos))
    | FExists (vs, g0, pos) -> (
        let ng0 = combine g0 in
        match ng0 with
        | FExists (us, ng1, _) -> FExists (vs@us, ng1, pos)
        | _ -> FExists (vs, ng0, pos)) in
  combine f


(****************************************************************************)
(*****************           simplify quantifiers           *****************)

let rec simplify_exists_var_by_equal_pf (f: pure_form) : pure_form =
  SBDebug.trace_1 "simplify_exists_var_by_equal_pf" (pr_pf, pr_pf) f
    (fun () -> simplify_exists_var_by_equal_pf_x f)

and simplify_exists_var_by_equal_pf_x (f: pure_form) : pure_form =
  let rec simplify g = match g with
    | BConst _ | BinRel _ | PRel _ -> g
    | PNeg (g0, pos) -> (
        let x = simplify g0 in
        match x with
        | PNeg (y, _) -> y
        | _ -> mk_pneg x ~pos:pos)
    | PConj (gs, pos) -> PConj (List.map simplify gs, pos)
    | PDisj (gs, pos) -> PDisj (List.map simplify gs, pos)
    | PForall (vs, g0, pos) -> PForall (vs, simplify g0, pos)
    | PExists (vs, g0, p) -> (
        let g0 = simplify g0 in
        let ssts = collect_substs_from_equal_pf g0 in
        let ssts = List.fold_left (fun acc (x, e) ->
          if (mem_vs x vs) then (x, e) :: acc else acc) [] ssts in
        match ssts with
        | [] -> g
        | sst::_ ->
          let nvs = diff_vs vs [(fst sst)] in
          let ng0 = subst_pf [sst] g0 in
          if (nvs = []) then ng0
          else simplify (PExists (nvs, ng0, p))) in
  f |> simplify |> simplify_tauto_contra_pf

let rec simplify_exists_var_by_equal (f: formula) : formula =
  SBDebug.trace_1 "simplify_exists_var_by_equal" (pr_f, pr_f) f
    (fun () -> simplify_exists_var_by_equal_x f)

and simplify_exists_var_by_equal_x (f: formula) : formula =
  let rec simplify g = match g with
    | FBase (h, p, pos) -> FBase (h, simplify_exists_var_by_equal_pf p, pos)
    | FForall (vs, g0, pos) -> FForall (vs, simplify g0, pos)
    | FExists (vs, g0, pos) -> (
        let g0 = simplify g0 in
        let eq_vars = collect_substs_from_equal g0 in
        let ssts = List.fold_left (fun acc (x, e) ->
          if (mem_vs x vs) then (x, e) :: acc else acc) [] eq_vars in
        if (ssts = []) then g
        else
          let sst = List.hd ssts in
          let nvs = diff_vs vs [(fst sst)] in
          let ng0 = subst [sst] g0 in
          if (nvs = []) then ng0
          else simplify (FExists (nvs, ng0, pos))) in
  f |> simplify |> simplify_tauto_contra

let remove_all_heap_exists_vars (f: formula) : formula =
  match f with
  | FBase _ | FForall _ -> f
  | FExists (_, f0, _) -> f0

let remove_all_exists_vars_pf (f: pure_form) : pure_form =
  let rec remove g = match g with
    | BConst _ | BinRel _ | PRel _ -> g
    | PNeg _ -> g
    | PConj (gs, p) -> PConj (List.map remove gs, p)
    | PDisj (gs, p) -> PDisj (List.map remove gs, p)
    | PForall _ -> g
    | PExists (_, ng, _) -> remove ng in
  remove f

let remove_all_exists_vars (f: formula) : formula =
  let rec remove g = match g with
    | FBase (hf, pf, p) -> FBase (hf, remove_all_exists_vars_pf pf, p)
    | FForall _ -> g
    | FExists (_, g, _) -> remove g in
  remove f

let remove_all_qvars_pf (f: pure_form) : pure_form =
  let rec remove g = match g with
    | BConst _ | BinRel _ | PRel _ -> g
    | PNeg (g, p) -> PNeg (remove g, p)
    | PConj (gs, p) -> PConj (List.map remove gs, p)
    | PDisj (gs, p) -> PDisj (List.map remove gs, p)
    | PForall (_, g, _) -> remove g
    | PExists (_, g, _) -> remove g in
  remove f

let remove_all_qvars (f: formula) : formula =
  let rec remove g = match g with
    | FBase (hf, pf, p) -> FBase (hf, remove_all_qvars_pf pf, p)
    | FForall (_, g, _) -> remove g
    | FExists (_, g, _) -> remove g in
  remove f

let remove_heap_exists_vars (f: formula) vs : formula =
  let rec remove g = match g with
    | FBase _ | FForall _ -> g
    | FExists (us, g0, p) ->
      let ng = remove g0 in
      let nus = diff_vs us vs in
      if nus = [] then ng else FExists (nus, ng, p) in
  remove f

let rec remove_rform_exists_vars_pf (f: pure_form) : pure_form =
  SBDebug.trace_1 "remove_rform_exists_vars_pf" (pr_pf, pr_pf) f
    (fun () -> remove_rform_exists_vars_pf_x f)

and remove_rform_exists_vars_pf_x (f: pure_form) : pure_form =
  let rfvs = f |> collect_rform_pf |> fv_rfs in
  let rec remove g = match g with
    | BConst _ | BinRel _ | PRel _ -> g
    | PNeg _ -> g
    | PConj (gs, p) -> PConj (List.map remove gs, p)
    | PDisj (gs, p) -> PDisj (List.map remove gs, p)
    | PForall _ -> g
    | PExists (vs, ng, p) ->
      let ng = remove ng in
      let nvs = diff_vs vs rfvs in
      if nvs = [] then ng
      else PExists (nvs, ng, p) in
  remove f

let rec simplify_unused_quantifiers_pf (f: pure_form) : pure_form =
  SBDebug.trace_1 "simplify_unused_quantifiers_pf" (pr_pf, pr_pf) f
    (fun () -> simplify_unused_quantifiers_pf_x f)

and simplify_unused_quantifiers_pf_x pf : pure_form =
  let rec simplify g = match g with
    | BConst _ | BinRel _ | PRel _ -> g
    | PForall (vs, g0, pos) ->
      let g0 = simplify g0 in
      let nvs = intersect_vs vs (fv_pf g0) in
      if nvs = [] then g0
      else PForall (nvs, g0, pos)
    | PExists (vs, g0, pos) ->
      let g0 = simplify g0 in
      let nvs = intersect_vs vs (fv_pf g0) in
      if nvs = [] then g0
      else PExists (nvs, g0, pos)
    | PNeg (g0, p) -> mk_pneg (simplify g0) ~pos:p
    | PConj (gs, pos) -> PConj (List.map simplify gs, pos)
    | PDisj (gs, pos) -> PDisj (List.map simplify gs, pos) in
  simplify pf

let rec simplify_quantifiers_pf f =
  SBDebug.trace_1 "simplify_quantifiers_pf_x" (pr_pf, pr_pf) f
    (fun _ -> simplify_quantifiers_pf_x f)

and simplify_quantifiers_pf_x pf =
  pf |>
  simplify_unused_quantifiers_pf |>
  simplify_exists_var_by_equal_pf

(****************************************************************************)
(*****************           push negation inward           *****************)

let rec push_negation_inward_pf (f: pure_form) : pure_form =
  SBDebug.trace_1 "push_negation_inward_pf" (pr_pf,  pr_pf) f
    (fun () -> push_negation_inward_pf_x f)

and push_negation_inward_pf_x (f: pure_form) : pure_form =
  let np = no_pos in
  let rec push g = match g with
    | BConst _ | BinRel _ | PRel _ -> g
    | PConj (gs, _) -> PConj (List.map push gs, np)
    | PDisj (gs, _) -> PDisj (List.map push gs, np)
    | PForall (vs, g0, _) -> PForall (vs, push g0, np)
    | PExists (vs, g0, _) -> PExists (vs, push g0, np)
    | PNeg (BConst _ as g0, p) -> mk_pneg g0 ~pos:p
    | PNeg (BinRel _ as g0, p) -> mk_pneg g0 ~pos:p
    | PNeg (PRel _, _) -> g
    | PNeg (PNeg (g0, _), _) -> push g0
    | PNeg (PConj (gs, _), _) ->
      PDisj (List.map (fun x -> push (mk_pneg x ~pos:np)) gs, np)
    | PNeg (PDisj (gs, _), _) ->
      PConj (List.map (fun x -> push (mk_pneg x ~pos:np)) gs, np)
    | PNeg (PForall (vs, g0, _), _) ->
      PExists (vs, push (mk_pneg g0 ~pos:np), np)
    | PNeg (PExists (vs, g0, _), _) ->
      PForall (vs, push (mk_pneg g0 ~pos:np), np) in
  push f

let rec push_negation_inward (f: formula) : formula =
  SBDebug.trace_1 "push_negation_inward" (pr_f,  pr_f) f
    (fun () -> push_negation_inward_x f)

and push_negation_inward_x (f: formula) : formula =
  let rec push = function
    | FBase (hf, pf, p) -> FBase (hf, push_negation_inward_pf pf , p)
    | FExists (vs, g, p) -> FExists (vs, push g, p)
    | FForall (vs, g, p) -> FForall (vs, push g, p) in
  push f

(****************************************************************************)
(*****************              unfold relation             *****************)

let rec unfold_relation_pf rdefns (f: pure_form) : pure_form =
  SBDebug.trace_1 "unfold_relation_pf" (pr_pf,  pr_pf) f
    (fun () -> unfold_relation_pf_x rdefns f)

and unfold_relation_pf_x rdefns (f: pure_form) : pure_form =
  let np = no_pos in
  let rec unfold g = match g with
    | BConst _ | BinRel _ -> g
    | PRel rf -> (try unfold_rform_rf rdefns rf with _ -> g)
    | PConj (gs, _) -> PConj (List.map unfold gs, np)
    | PDisj (gs, _) -> PDisj (List.map unfold gs, np)
    | PForall (vs, g0, _) -> PForall (vs, unfold g0, np)
    | PExists (vs, g0, _) -> PExists (vs, unfold g0, np)
    | PNeg (BConst _ as g0, p) -> mk_pneg g0 ~pos:p
    | PNeg (BinRel _ as g0, p) -> mk_pneg g0 ~pos:p
    | PNeg (PRel _, _) -> g
    | PNeg (PNeg (g0, _), _) -> unfold g0
    | PNeg (PConj (gs, _), _) ->
      PDisj (List.map (fun x -> unfold (mk_pneg x ~pos:np)) gs, np)
    | PNeg (PDisj (gs, _), _) ->
      PConj (List.map (fun x -> unfold (mk_pneg x ~pos:np)) gs, np)
    | PNeg (PForall (vs, g0, _), _) ->
      PExists (vs, unfold (mk_pneg g0 ~pos:np), np)
    | PNeg (PExists (vs, g0, _), _) ->
      PForall (vs, unfold (mk_pneg g0 ~pos:np), np) in
  unfold f

let rec unfold_relation rdefns (f: formula) : formula =
  SBDebug.trace_1 "unfold_relation" (pr_f,  pr_f) f
    (fun () -> unfold_relation_x rdefns f)

and unfold_relation_x rdefns (f: formula) : formula =
  let rec unfold = function
    | FBase (hf, pf, p) -> FBase (hf, unfold_relation_pf rdefns pf , p)
    | FExists (vs, g, p) -> FExists (vs, unfold g, p)
    | FForall (vs, g, p) -> FForall (vs, unfold g, p) in
  unfold f

(********************************************************************)
(*****************           simplify hemp           ****************)

(* simplify empty heap,
   return new formula and whether it is simplified *)
let simplify_emp_hf (f: heap_form) : heap_form =
  let rec simplify h = match h with
    | HEmp _ -> h
    | HAtom ([], [], p) -> HEmp p
    | HAtom _ -> h
    | HStar (h1, h2, p) -> (
        let nh1, nh2 = Pair.fold simplify h1 h2 in
        match nh1, nh2 with
        | HEmp _, _ -> nh2
        | _, HEmp _ -> nh1
        | _ -> HStar (nh1, nh2, p))
    | HWand _ -> error "simplify_emp_hf: handle Wand later" in
  simplify f

(* simplify empty heap,
   return new formula and whether it is simplified *)
let simplify_emp (f: formula) : formula =
  let rec simplify g = match g with
    | FBase (h, p, pos) -> FBase (simplify_emp_hf h, p, pos)
    | FExists (v, g0, pos) -> FExists (v, simplify g0, pos)
    | FForall (v, g0, pos) -> FForall (v, simplify g0, pos) in
  simplify f

(********************************************************************)
(****************         simplify equations         ****************)

let rec simplify_equality_pf (f: pure_form) : pure_form =
  DB.trace_1 "simplify_equality_pf" (pr_pf, pr_pf) f
    (fun () -> simplify_equality_pf_x f)

and simplify_equality_pf_x (f: pure_form) : pure_form =
  let ltermss, other_pfss =
    f |> collect_pure_conjuncts_pf |>
    List.map (fun pf ->
      match pf with
      | BinRel (Eq, (Var _ as e1), (Var _ as e2), _) ->
        let t, e = convert_exp_to_lterm (mk_bin_op Sub e1 e2) in
        if (e = None) then ([t], []) else ([], [pf])
      | BinRel (Eq, e1, e2, _) ->
        if (typ_of_exp e1 = TInt) || (typ_of_exp e2 = TInt) then
          let t, e = convert_exp_to_lterm (mk_bin_op Sub e1 e2) in
          if (e = None) then ([t], []) else ([], [pf])
        else ([], [pf])
      | _ -> [], [pf]) |>
    List.split in
  let lterms = ltermss |> List.concat in
  let tvs = lterms |> List.map fv_lterm |> List.concat |> dedup_vs in
  let mrow, mcol = List.length lterms, (List.length tvs) + 1 in
  let matrix = Array.make_matrix mrow mcol 0 in
  List.iteri (fun i t ->
    List.iteri (fun j v ->
      try matrix.(i).(j) <- fst (List.find (fun u -> eq_var (snd u) v) (fst t))
      with _ -> matrix.(i).(j) <- 0
    ) tvs;
    matrix.(i).(mcol - 1) <- - (snd t);
  ) lterms;
  let matrix = Matrix.gauss_transform_augmented_matrix matrix in
  let npfs =
    matrix |>
    Array.fold_left (fun acc row ->
      tvs |>
      List.mapi (fun i v -> if row.(i) = 0 then [] else [(row.(i), v)]) |>
      List.concat |>
      (fun t -> acc @ [(t, - row.(mcol -1))])) [] |>
    List.map (fun t -> match t with
      | [(-1, x); (1, y)], 0 -> mk_eq_var x y
      | [(1, x); (-1, y)], 0 -> mk_eq_var x y
      | _ -> mk_eq_iconst (mk_lterm_exp t) 0) in
  let pfs = npfs @ (List.concat other_pfss) in
  pfs |> mk_pconj |> simplify_tauto_contra_pf

let simplify_equality (f: formula) : formula =
  let qvs, hf, pf = extract_components_f f in
  let npf = simplify_equality_pf pf in
  mk_qform qvs (mk_fbase hf npf)

(********************************************************************)
(*****************           simplify all           *****************)

(* simplify formula,
   return new formula and whether it is simplified *)
let rec simplify_all_pf ?(prog=None) ?(infer=false) f =
  SBDebug.trace_1 "simplify_all_pf"
    (pr_pf, pr_pf) f
    (fun _ -> simplify_all_pf_x ~prog:prog ~infer:infer f)

and simplify_all_pf_x ?(prog=None) ?(infer=false) f =
  let rdefns = match prog with
    | None -> []
    | Some prog -> prog.prog_rels in
  match infer with
  | true ->
    f |> unfold_relation_pf rdefns |>
    simplify_quantifiers_pf |>
    push_negation_inward_pf |>
    combine_qvars_pf |>
    simplify_arith_pf |>
    simplify_tauto_contra_pf |>
    simplify_redundant_pf
  | false ->
    f |> unfold_relation_pf rdefns |>
    simplify_quantifiers_pf |>
    push_negation_inward_pf |>
    combine_qvars_pf |>
    simplify_arith_pf |>
    simplify_tauto_contra_pf |>
    simplify_equality_pf |>
    simplify_redundant_pf

let simplify_all_pfs ?(infer=false) fs =
  List.map (simplify_all_pf ~infer:infer) fs

let rec simplify_all ?(prog=None) ?(infer=false) f =
  SBDebug.trace_1 "simplify_all"
    (pr_f, pr_f) f
    (fun () -> simplify_all_x ~prog:prog ~infer:infer f)

and simplify_all_x ?(prog=None) ?(infer=false) f =
  let rdefns = match prog with
    | None -> []
    | Some prog -> prog.prog_rels in
  match infer with
  | true ->
    f |> simplify_emp |>
    unfold_relation rdefns |>
    push_qvars_inward |>
    simplify_exists_var_by_equal |>
    push_negation_inward |>
    simplify_exists_var_by_equal |>
    combine_qvars |>
    simplify_arith |>
    simplify_tauto_contra
  | false ->
    f |> simplify_emp |>
    unfold_relation rdefns |>
    push_qvars_inward |>
    simplify_exists_var_by_equal |>
    push_negation_inward |>
    simplify_exists_var_by_equal |>
    combine_qvars |>
    simplify_arith |>
    simplify_tauto_contra |>
    simplify_equality |>
    simplify_redundant

let rec simplify_all_lhs_rhs_pf ?(prog=None) ?(infer=false) lhs rhs =
  SBDebug.trace_2
    "simplify_all_lhs_rhs_pf" (pr_pf, pr_pf, pr_pair pr_pf pr_pf) lhs rhs
    (fun () ->  simplify_all_lhs_rhs_pf_x ~prog:prog ~infer:infer lhs rhs)

and simplify_all_lhs_rhs_pf_x ?(prog=None) ?(infer=false) lhs rhs =
  let lhs = simplify_all_pf ~prog:prog ~infer:infer lhs in
  let rhs = simplify_all_pf ~prog:prog ~infer:infer rhs in
  (lhs, rhs)

let rec simplify_all_lhs_rhs ?(infer=false) prog lhs rhs  =
  SBDebug.trace_2
    "simplify_all_lhs_rhs" (pr_f, pr_f, pr_pair pr_f pr_f) lhs rhs
    (fun () ->  simplify_all_lhs_rhs_x ~infer:infer prog lhs rhs)

and simplify_all_lhs_rhs_x ?(infer=false) prog lhs rhs =
  let lhs = unfold_relation prog.prog_rels lhs in
  let rhs = unfold_relation prog.prog_rels rhs in
  let lhs, rhs = simplify_equal_lhs_rhs lhs rhs in
  let lhs = simplify_all ~prog:(Some prog) ~infer:infer lhs in
  let rhs = simplify_all ~prog:(Some prog) ~infer:infer rhs in
  let lhs = remove_all_heap_exists_vars lhs in
  (lhs, rhs)

let rec simplify_all_ent ?(infer=false) prog ent =
  SBDebug.trace_1
    "simplify_all_ent" (pr_ent, pr_ent) ent
    (fun () -> simplify_all_ent_x ~infer:infer prog ent)

and simplify_all_ent_x ?(infer=false) prog ent =
  let lhs, rhs = simplify_all_lhs_rhs ~infer:infer prog ent.ent_lhs ent.ent_rhs in
  {ent with ent_lhs = lhs; ent_rhs = rhs}

(********************************************************************)
(*****************        horn entailments        *******************)

(* LHS of horn_entail = PConj of list of BinRel or BConst
   RHS of horn_entail = BinRel or BConst *)

let transform_ne (f: pure_form) : pure_form =
  let rec trans f = match f with
    | BConst _ | PRel _ -> f
    | BinRel (Ne, e1, e2, p) -> (match typ_of_exp e1 with
      | TData _ | TNull -> f
      | _ ->
        let f1 = BinRel (Lt, e1, e2, p) in
        let f2 = BinRel (Lt, e2, e1, p) in
        PDisj ([f1; f2], p))
    | BinRel _ -> f
    | PNeg (g, p) -> PNeg (trans g, p)
    | PConj (gs, p) -> PConj (List.map trans gs, p)
    | PDisj (gs, p) -> PDisj (List.map trans gs, p)
    | PForall (vs, g, p) -> PForall (vs, trans g, p)
    | PExists (vs, g, p) -> PExists (vs, trans g, p) in
  trans f

let flatten_conj (f: pure_form) : pure_form =
  let rec flatten f = match f with
    | BConst _ | PRel _ | BinRel _ -> f
    | PNeg (g, p) -> PNeg (flatten g, p)
    | PDisj (gs, p) -> PDisj (List.map flatten gs, p)
    | PForall (vs, g, p) -> PForall (vs, flatten g, p)
    | PExists (vs, g, p) -> PExists (vs, flatten g, p)
    | PConj (gs, p) ->
      let ngs = gs |>
                List.map (fun g ->
                  let ng = flatten g in
                  match ng with
                  | PConj (ks, _) -> ks
                  | _ -> [ng]) |>
                List.concat in
      PConj (ngs, p) in
  flatten f

let flatten_disj (f: pure_form) : pure_form =
  let rec flatten f = match f with
    | BConst _ | PRel _ | BinRel _ -> f
    | PNeg (g, p) -> PNeg (flatten g, p)
    | PConj (gs, p) -> PConj (List.map flatten gs, p)
    | PForall (vs, g, p) -> PForall (vs, flatten g, p)
    | PExists (vs, g, p) -> PExists (vs, flatten g, p)
    | PDisj (gs, p) ->
      let ngs = gs |>
                List.map (fun g ->
                  let ng = flatten g in
                  match ng with
                  | PDisj (ks, _) -> ks
                  | _ -> [ng]) |>
                List.concat in
      PDisj (ngs, p) in
  flatten f


let rec transform_cnf (f: pure_form) : pure_form =
  DB.trace_1 "transform_cnf" (pr_pf, pr_pf) f
    (fun () -> transform_cnf_x f)

and transform_cnf_x f =
  let rec trans f =
    match f with
    | BConst _ | BinRel _ | PRel _ -> f
    | PNeg (PRel _, p) -> f
    | PNeg _ -> error ("transform_cnf: PNeg ins't inward: " ^ (pr_pf f))
    | PConj (gs, p) ->
      let ngs = List.fold_left (fun acc g ->
        let ng = trans g in
        match ng with
        | PConj (xs, _) -> acc @ xs
        | _ -> acc @ [ng]) [] gs in
      PConj (ngs, p)
    | PDisj (gs, p) ->
      let ngss_dnf = List.map (fun g ->
        let g = trans g in
        match g with
        | PDisj _ -> error ("transform_dnf: not expect PDisj inside PDisj: \
                            " ^ (pr_pf g))
        | PConj (xs, _) -> xs
        | _ -> [g]) gs in
      let ngss_cnf = Comb.gen_cartesian ngss_dnf in
      let ngs = List.map (fun xs -> mk_pdisj xs) ngss_cnf in
      mk_pconj ngs
    | PForall _ | PExists _ -> f in
  let f = f |>
          simplify_all_pf |>
          push_negation_inward_pf |>
          flatten_disj in
  trans f

let rec transform_dnf (f: pure_form) : pure_form =
  DB.trace_1 "transform_dnf" (pr_pf, pr_pf) f
    (fun () -> transform_dnf_x f)

and transform_dnf_x f =
  let rec trans f =
    match f with
    | BConst _ | BinRel _ | PRel _ -> f
    | PNeg (PRel _, p) -> f
    | PNeg _ -> error ("transform_dnf: PNeg isn't inward : " ^ (pr_pf f))
    | PConj (gs, p) ->
      let ngss_cnf = List.map (fun g ->
        let g = trans g in
        match g with
        | PConj _ -> error ("transform_dnf: not expect PConj inside PConj: \
                            " ^ (pr_pf g) ^ " inside " ^ (pr_pf f))
        | PDisj (xs, _) -> xs
        | _ -> [g]) gs in
      (* let _ = DB.hprint "NGSS_CNF: " *)
      (*     (pr_list_cbrace (pr_list_cbrace pr_pf)) ngss_cnf in *)
      let ngss_dnf = Comb.gen_cartesian ngss_cnf in
      (* let _ = DB.hprint "NGSS_DNF: " *)
      (*     (pr_list_cbrace (pr_list_cbrace pr_pf)) ngss_dnf in *)
      let ngs = List.map (fun xs -> mk_pconj xs) ngss_dnf in
      mk_pdisj ngs
    | PDisj (gs, p) ->
      let ngs = List.fold_left (fun acc g ->
        let ng = trans g in
        match ng with
        | PDisj (xs, _) -> acc @ xs
        | _ -> acc @ [ng]) [] gs in
      PDisj (ngs, p)
    | PForall _ | PExists _ -> f in
  let f = f |>
          simplify_all_pf |>
          push_negation_inward_pf |>
          transform_ne |>
          flatten_conj in
  (* DB.hprint "before trans_dnf: " pr_pf f; *)
  trans f

(*****************************************************************************)
(**********************        slicing functions       ***********************)

let filter_constr_pf (filter: pure_form -> bool) (f: pure_form) : pure_form =
  let rec do_filter g =
    match g with
    | BConst _ | BinRel _ | PRel _ ->
      if (filter g) then [g]
      else []
    | PNeg _ | PDisj _ -> [g]
    | PConj (gs, p) ->
      let ngs = gs |> List.map do_filter |> List.concat in
      if (ngs = []) then []
      else [PConj (ngs, p)]
    | PForall (vs, g, p) ->
      let ng = do_filter g in
      if ng = [] then []
      else [PForall (vs, List.hd ng, p)]
    | PExists (vs, g, p) ->
      let ng = do_filter g in
      if ng = [] then []
      else [PExists (vs, List.hd ng, p)] in
  match (do_filter f) with
  | [] -> mk_true no_pos
  | nf::_ -> nf

(****************************************************************************)
(**********************       encoding functions      ***********************)

let rec encode_view_inv_vf ?(constr=IctAll) vdefns vform : pure_form =
  DB.trace_1 "encode_view_inv_vf" (pr_vf, pr_pf) vform
    (fun () -> encode_view_inv_vf_x vdefns vform ~constr:constr)

and encode_view_inv_vf_x ?(constr=IctAll) vdefns vform : pure_form =
  let vdefn = find_view_defn vdefns vform.viewf_name in
  let ssts = List.combine vdefn.view_params vform.viewf_args in
  let vinv = vdefn.view_inv in
  let orig_invs = match constr with
    | IctArith -> [vinv.vinv_arith]
    | IctPointer -> [vinv.vinv_pointer]
    | IctAll -> [vinv.vinv_arith; vinv.vinv_pointer; vinv.vinv_all]
    | IctAuto -> [] in
  let orig_iform = orig_invs |>
                   List.map (fun x -> match x with
                     | None -> []
                     | Some pf -> [pf]) |>
                   List.concat |>
                   mk_pconj in
  (subst_pf ssts orig_iform)

(** encode heap atoms to pure formula *)
let rec encode_hatoms ?(constr=IctAll) ?(simplify=true)
    prog (has: heap_atom list) : pure_form =
  DB.trace_2 "encode_hatoms" (pr_has, pr_ict, pr_pf) has constr
    (fun () -> encode_hatoms_x prog has ~simplify:simplify ~constr:constr)

and encode_hatoms_x ?(constr=IctAll) ?(simplify=true)
      prog (has : heap_atom list) : pure_form =
  let alloc_exps =
    match constr with
    | IctPointer | IctAll ->
      has |> List.map (get_alloc_exps prog.prog_views) |> List.concat
    | _ -> [] in
  let not_null_cond = alloc_exps |> List.map (fun x ->
    mk_pimpl x.al_cond (mk_neq_null x.al_addr)) |> mk_pconj in
  let distinct_cond =
    alloc_exps |>
    (* consider distinct of only data nodes *)
    Comb.gen_combinations 2 |> List.map (function
      | x::y::[] ->
        let cond = mk_pconj [x.al_cond; y.al_cond] in
        let distinct = mk_neq_exp x.al_addr y.al_addr in
        (mk_pimpl cond distinct)
      | _ -> error "encode_hatoms: expect combination of 2") |> mk_pconj in
  let invariant_cond =
    has |> List.map (function
      | HData _ -> []
      | HView vf -> [(encode_view_inv_vf prog.prog_views vf ~constr:constr)]) |>
    List.concat |> mk_pconj in
  let pf = mk_pconj [not_null_cond; distinct_cond; invariant_cond] in
  (* NOTE: call simplify_all only once *)
  if simplify then simplify_all_pf pf
  else pf

(* encode a heap formula to pure *)
let rec encode_hformula ?(constr=IctAll) prog (f: heap_form) : pure_form =
  DB.trace_2 "encode_hformula" (pr_hf, pr_ict, pr_pf) f constr
    (fun () -> encode_hformula_x prog f ~constr:constr)

and encode_hformula_x ?(constr=IctAll) prog hf : pure_form =
  encode_hatoms ~constr:constr prog (collect_hatom_hf hf)

(* encode formula for formula and consumed heap to pure *)
let rec encode_formula_hconsumed ?(constr=IctAll) prog f hconsumed : pure_form =
  DB.trace_3 "encode_formula_hconsumed" (pr_f, pr_has, pr_ict, pr_pf)
    f hconsumed constr
    (fun () -> encode_formula_hconsumed_x ~constr:constr prog f hconsumed)

and encode_formula_hconsumed_x ?(constr=IctAll) prog f hconsumed : pure_form =
  match f with
  | FBase _ ->
    let hf1 = collect_hatom f in
    let hf2 = hconsumed in
    let pf1 = encode_hatoms ~constr:constr prog (hf1 @ hf2) in
    let pf2 = extract_pf f in
    mk_pconj [pf1; pf2] |> simplify_all_pf
  | FExists _ -> encode_formula ~constr:constr prog f
  | _ -> error ("encode_formula_hconsumed: expect FBase or FExists: " ^ (pr_f f))

(* encode a formula to pure *)
and encode_formula ?(constr=IctAll) prog (f: formula) : pure_form =
  DB.trace_2 "encode_formula" (pr_f, pr_ict, pr_pf) f constr
    (fun () -> encode_formula_x ~constr:constr prog f)

and encode_formula_x ?(constr=IctAll) prog (f: formula) : pure_form =
  let rec encode g = match g with
    | FBase (hf, pf, _) ->
      let pf2 = encode_hatoms ~constr:constr prog (collect_hatom_hf hf) in
      mk_pconj [pf; pf2]
    | FExists (vs, g, p) -> mk_pexists vs (encode g)
    | FForall _ -> error ("encode_formula: expect FBase: " ^ (pr_f g)) in
  f |> simplify_all ~prog:(Some prog) |> encode

(* (\* encode a formula to pure *\) *)
(* and encode_invariant ?(constr=IctAll) prog (f: formula) : pure_form = *)
(*   DB.trace_2 "encode_invariant" (pr_f, pr_ict, pr_pf) f constr *)
(*     (fun () -> encode_invariant_x ~constr:constr prog f) *)

(* and encode_invariant_x ?(constr=IctAll) prog (f: formula) : pure_form = *)
(*   let rec encode g = match g with *)
(*     | FBase (hf, pf, _) -> *)
(*       let invariant_cond = *)
(*         (collect_hatom_hf hf) |> *)
(*         List.map (function *)
(*           | HData df -> [(mk_neq_null df.dataf_root)] *)
(*           | HView vf -> [(encode_view_inv_vf prog vf ~constr:constr)]) |> *)
(*         List.concat |> mk_pconj in *)
(*       mk_pconj [pf; invariant_cond] *)
(*     | FExists (vs, g, p) -> mk_pexists vs (encode g) *)
(*     | FForall _ -> error ("encode_formula: expect FBase: " ^ (pr_f g)) in *)
(*   encode f *)

(* encode a formula to pure *)
and encode_view_inv_f ?(constr=IctAll) vdefns (f: formula) : pure_form =
  DB.trace_2 "encode_view_inv_f" (pr_f, pr_ict, pr_pf) f constr
    (fun () -> encode_view_inv_f_x ~constr:constr vdefns f)

and encode_view_inv_f_x ?(constr=IctAll) vdefns (f: formula) : pure_form =
  let rec encode g = match g with
    | FBase (hf, pf, _) ->
      let invariant_cond =
        (collect_hatom_hf hf) |>
        List.map (function
          | HData df -> []
          | HView vf -> [(encode_view_inv_vf vdefns vf ~constr:constr)]) |>
        List.concat |> mk_pconj in
      mk_pconj [pf; invariant_cond]
    | FExists (vs, g, p) -> mk_pexists vs (encode g)
    | FForall _ -> error ("encode_formula: expect FBase: " ^ (pr_f g)) in
  encode f

(* encode a formula to pure *)
and encode_view_inv_hf ?(constr=IctAll) vdefns (hf: heap_form) : pure_form =
  DB.trace_2 "encode_view_inv_hf" (pr_hf, pr_ict, pr_pf) hf constr
    (fun () -> encode_view_inv_hf_x ~constr:constr vdefns hf)

and encode_view_inv_hf_x ?(constr=IctAll) vdefns (hf: heap_form) : pure_form =
  hf |>
  collect_hatom_hf |>
  List.map (function
    | HData df -> []
    | HView vf -> [(encode_view_inv_vf vdefns vf ~constr:constr)]) |>
  List.concat |> mk_pconj

let encode_infer_lhs ?(constr=IctAll) vdefns f hconsumed : pure_form =
  match f with
  | FBase (hf, pf, _) ->
    let ptr_pfs =
      if (constr = IctArith || constr = IctAll) then []
      else (collect_hatom_hf hf) @ hconsumed |>
           List.map (fun ha -> match ha with
             | HData df -> [mk_neq_null df.dataf_root]
             | HView vf -> [(encode_view_inv_vf vdefns vf ~constr:IctPointer)]) |>
           List.concat in
    let arith_pfs =
      if (constr = IctPointer || constr = IctAll) then []
      else (collect_hatom_hf hf) @ hconsumed |>
           List.map (fun ha -> match ha with
             | HView vf -> [(encode_view_inv_vf vdefns vf ~constr:IctArith)]
             | HData _ -> []) |>
           List.concat in
    mk_pconj ([pf] @ arith_pfs @ ptr_pfs)
  | FExists _
  | FForall _ -> error ("encode_infer_lhs: expect FBase: " ^ (pr_f f))

let encode_infer_rhs ?(constr=IctAll) prog f : pure_form =
  extract_pf f


(**********************************************)
(**********       transformation    ***********)

let currify_exp ?(constr=IctAll) exp : (exp * pure_form list) =
  let fresh_exp typ = mk_exp_var (fresh_var_new_name (), typ) in
  match exp with
  | Var _ -> (exp, [])
  | _ ->
    let typ = typ_of_exp exp in
    let nexp = match constr, typ with
      | IctAll, _
      | IctArith, TInt
      | IctPointer, TNull
      | IctPointer, TData _ -> Some (fresh_exp typ)
      | _ -> None in
    match nexp with
    | Some x -> (x, [mk_eq_exp exp x])
    | None -> (exp, [])

let currify_prel_null_ptr (pf: pure_form) : pure_form * pure_form =
  let rec currify g = match g with
    | BConst _ | BinRel _ -> (g, [])
    | PRel rf ->
      let args, pfss = List.map (currify_exp ~constr:IctPointer) rf.prel_args |>
                       List.split in
      let pfs = pfss |> List.concat in
      let nrf = {rf with prel_args = args} in
      (PRel nrf, pfs)
    | PConj (gs, p) ->
      let pfs, npfss = gs |> List.map currify |> List.split in
      (mk_pconj pfs, List.concat npfss)
    | PDisj (gs, p) ->
      let pfs, npfss = gs |> List.map currify |> List.split in
      (mk_pdisj pfs, List.concat npfss)
    | PNeg (g, p) ->
      let pf, pfs = currify g in
      (PNeg (pf, p), pfs)
    | PForall (vs, g, p) ->
      let pf, pfs = currify g in
      (PForall (vs, pf, p), pfs)
    | PExists (vs, g, p) ->
      let pf, pfs = currify g in
      (PExists (vs, pf, p), pfs) in
  let npf, npfs = currify pf in
  (npf, mk_pconj npfs)

let currify_df ?(constr=IctAll) (df: data_form) : (data_form * pure_form) =
  let args, pfss = df.dataf_args
                   |> List.map (currify_exp ~constr:constr) |> List.split in
  let npf = pfss |> List.concat |> mk_pconj in
  let ndf = {df with dataf_args = args} in
  (ndf, npf)

let currify_vf ?(constr=IctAll) (vf: view_form) : (view_form * pure_form) =
  let args, pfss = vf.viewf_args
                   |> List.map (currify_exp ~constr:constr) |> List.split in
  let npf = pfss |> List.concat |> mk_pconj in
  let nvf = {vf with viewf_args = args} in
  (nvf, npf)

let rec currify_f ?(constr=IctAll) f =
  DB.trace_1 "currify_f" (pr_f, pr_f) f
    (fun () -> currify_f_x ~constr:constr f)

and currify_f_x ?(constr=IctAll) f =
  let rec currify_hf hf = match hf with
    | HEmp _ -> hf, []
    | HAtom (dfs, vfs, p) ->
      let ndfs, pfs1 = dfs |> List.map (currify_df ~constr:constr) |>
                       List.split in
      let nvfs, pfs2 = vfs |> List.map (currify_vf ~constr:constr) |>
                       List.split in
      HAtom (ndfs, nvfs, p), (pfs1 @ pfs2)
    | HStar (h1, h2, p) ->
      let nh1, pfs1 = currify_hf h1 in
      let nh2, pfs2 = currify_hf h2 in
      HStar (nh1, nh2, p), (pfs1 @ pfs2)
    | HWand _ -> error ("currify_f: not expect: " ^ (pr_hf hf)) in
  let rec currify g = match g with
    | FBase (hf, pf, p) ->
      let nhf, npfs = currify_hf hf in
      FBase (nhf, mk_pconj (pf::npfs), p)
    | FExists (vs, g, p) -> FExists (vs, currify g, p)
    | FForall (vs, g, p) -> FForall (vs, currify g, p) in
  let nf = currify f in
  let fvs, nfvs = fv f, fv nf in
  let qvs = diff_vs nfvs fvs in
  mk_fexists qvs nf

let currify_lhs f =
  f |>
  currify_f |>
  remove_all_heap_exists_vars

let rec collect_closure_vars_pf (vs: var list) (f: pure_form) : var list =
  DB.trace_2 "collect_closure_vars_pf" (pr_vs, pr_pf, pr_vs) vs f
    (fun () -> collect_closure_vars_pf_x vs f)

and collect_closure_vars_pf_x (vs: var list) (f: pure_form) : var list =
  let vss = collect_pure_conjuncts_pf f |> List.map fv_pf in
  let tbl_vars = Hashtbl.create 10 in
  let _ = List.iter (fun v -> Hashtbl.add tbl_vars v true) vs in
  let is_collected v =
    try let _ = Hashtbl.find tbl_vars v in true
    with _ -> false in
  let collect v =
    try let _ = Hashtbl.find tbl_vars v in ()
    with _ -> Hashtbl.add tbl_vars v true in
  let rec update_closure () =
    let updated = ref false in
    let _ = List.iter (fun vs ->
      let need_update =
        (List.exists (fun v -> is_collected v) vs) &&
        (List.exists (fun v -> not (is_collected v)) vs) in
      if (need_update) then
        let _ = List.iter collect vs in
        updated := true
      else ()) vss in
    if (!updated = true) then update_closure ()
    else () in
  let _ = update_closure () in
  Hashtbl.fold (fun v e acc -> v :: acc) tbl_vars []

let rec collect_closure_vars (vs: var list) (f: formula) : var list =
  DB.trace_2 "collect_closure_vars" (pr_vs, pr_f, pr_vs) vs f
    (fun () -> collect_closure_vars_x vs f)

and collect_closure_vars_x (vs: var list) (f: formula) : var list =
  let pf = extract_pf f in
  let pf = push_qvars_inward_pf pf in
  collect_closure_vars_pf vs pf
