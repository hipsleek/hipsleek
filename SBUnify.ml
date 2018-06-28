open SBGlobals
open SBCast
open SBLib
open SBLib.Basic

module PT = SBPuretp
module NO = SBNormalize

type unification = {
  unf_correct_ssts : subst list;
  unf_conflict_ssts : subst list;
  unf_ununifed_exps : (exp * exp) list;
  unf_residue : heap_atom list;
  unf_hatom_pairs : (heap_atom * heap_atom) list;
}

exception EUnfs of unification list

let time_unify = ref 0.

(****************************************************************)
(**************           Constructors           ****************)


let mk_unification correct conflict ununified residue pairs =
  {unf_correct_ssts = correct;
   unf_conflict_ssts = conflict;
   unf_ununifed_exps = ununified;
   unf_residue = residue;
   unf_hatom_pairs = pairs;}

let update_unification ?(correct=None) ?(conflict=None) ?(ununified=None)
      ?(residue=None) ?(pairs=None) unf =
  let unf = match correct with
    | None -> unf | Some ssts -> {unf with unf_correct_ssts = ssts} in
  let unf = match conflict with
    | None -> unf | Some ssts -> {unf with unf_conflict_ssts = ssts} in
  let unf = match ununified with
    | None -> unf | Some exps -> {unf with unf_ununifed_exps = exps} in
  let unf = match residue with
    | None -> unf | Some hatoms -> {unf with unf_residue = hatoms} in
  let unf = match pairs with
    | None -> unf | Some ps -> {unf with unf_hatom_pairs = ps} in
  unf

(**************************************************************)
(*******************        Printing        *******************)

let pr_exp_pairs exp_pairs =
  pr_list_sbrace (pr_pair pr_exp pr_exp) exp_pairs

let pr_hatom_pairs hatom_pairs =
  pr_list_sbrace (pr_pair pr_ha pr_ha) hatom_pairs

let pr_unf unf =
  "Unification:\n"
  ^ "  - correct ssts: " ^ (pr_ssts unf.unf_correct_ssts) ^ "\n"
  ^ "  - ununified exps: " ^ (pr_exp_pairs unf.unf_ununifed_exps) ^ "\n"
  ^ "  - conflict ssts: " ^ (pr_ssts unf.unf_conflict_ssts) ^ "\n"
  ^ "  - source target pair: " ^ (pr_hatom_pairs unf.unf_hatom_pairs) ^ "\n"
  ^ "  - residue: " ^ (pr_has unf.unf_residue)

let pr_unfs = pr_items ~bullet:"  #" pr_unf

(*****************************************************************)
(*******************        Unification        *******************)

let get_unf_success unfs =
  unfs |> List.filter (fun unf ->
    unf.unf_conflict_ssts = [] && unf.unf_ununifed_exps = [])

let get_unf_failure unfs =
  unfs |> List.filter (fun unf ->
    unf.unf_conflict_ssts != [] && unf.unf_ununifed_exps != [])

let split_unf_success_failure unfs =
  unfs |> List.partition (fun unf ->
    unf.unf_conflict_ssts = [] && unf.unf_ununifed_exps = [])

let compare_unfs unf1 unf2 =
  let lcorrect1 = List.length unf1.unf_correct_ssts in
  let lcorrect2 = List.length unf2.unf_correct_ssts in
  let lconflict1 = List.length unf1.unf_conflict_ssts in
  let lconflict2 = List.length unf2.unf_conflict_ssts in
  if lcorrect1 > lcorrect2 then 1
  else if lcorrect1 < lcorrect2 then -1
  else if lconflict1 < lconflict2 then 1
  else if lconflict1 > lconflict2 then -1
  else 0

and dedup_unfs (unfs: unification list) =
  let rec compare_sorted_ssts ssts1 ssts2 =
    match ssts1, ssts2 with
    | [], [] -> true
    | [], _ | _, [] -> false
    | x::xs, y::ys ->
      if (compare_sst x y = 0) then compare_sorted_ssts xs ys
      else false in
  let rec compare_residues rsds1 rsds2 =
    let str1 = rsds1 |> List.sortd compare_ha |> pr_has in
    let str2 = rsds2 |> List.sortd compare_ha |> pr_has in
    eq_s str1 str2 in
  let compare_unf unf1 unf2 =
    let ssts1_correct = List.sort compare_sst unf1.unf_correct_ssts in
    let ssts2_correct = List.sort compare_sst unf2.unf_correct_ssts in
    let cmp1 = compare_sorted_ssts ssts1_correct ssts2_correct in
    let ssts1_conflict = List.sort compare_sst unf1.unf_conflict_ssts in
    let ssts2_conflict = List.sort compare_sst unf2.unf_conflict_ssts in
    let cmp2 = compare_sorted_ssts ssts1_conflict ssts2_conflict in
    let cmp3 = compare_residues unf1.unf_residue unf2.unf_residue in
    cmp1 && cmp2 && cmp3 in
  EList.unique ~cmp:compare_unf unfs

let rec unify_var v e vars unf : unification list =
  Debug.trace_4 "unify_var" (pr_v, pr_e, pr_vs, pr_unf, pr_unfs) v e vars unf
    (fun () -> unify_var_x v e vars unf)

and unify_var_x v e vars unf : unification list =
  if (mem_vs v vars) then
    let correct_ssts, conflict_ssts =
      let correct_ssts = unf.unf_correct_ssts in
      let conflict_ssts = unf.unf_conflict_ssts in
      let v_correct_ssts, other_correct_ssts =
        correct_ssts |> List.partition (fun (u, _) -> eq_var u v) in
      let v_conflict_ssts, other_conflict_ssts =
        conflict_ssts |> List.partition (fun (u, _) -> eq_var u v) in
      match v_correct_ssts, v_conflict_ssts with
      | [], [] -> (((v, e)::correct_ssts), conflict_ssts)
      | [], _ ->
        if List.exists (eq_sst (v, e)) conflict_ssts then
          (correct_ssts, conflict_ssts)
        else (other_correct_ssts, (v, e)::conflict_ssts)
      | [(v, ve)], [] ->
        if eq_exp e ve then (correct_ssts, conflict_ssts)
        else (other_correct_ssts, (v, e)::conflict_ssts)
      | _, [] -> error ("unify_var: too many correct ssts for: " ^
                        (pr_v v) ^ ": " ^ pr_ssts v_correct_ssts)
      | _ -> error ("unify_var: unexpected both correct sst and\
                     conflict sst for: " ^ (pr_v v)) in
    [update_unification unf ~correct:(Some correct_ssts)
       ~conflict:(Some conflict_ssts)]
  else []

let rec unify_lterm lterm1 lterm2 vars unf : unification list =
  Debug.trace_4 "unify_lterm"
    (pr_lt, pr_lt, pr_vs, pr_unf, pr_unfs) lterm1 lterm2 vars unf
    (fun () -> unify_lterm_x lterm1 lterm2 vars unf)

(* TODO FIXME: THIS IS VERY TEMPORARY
   need to improve the lterm unification algo *)
and unify_lterm_x lterm1 lterm2 vars unf : unification list =
  let vs2 = lterm2 |> fst |> List.split |> snd in
  let cvs1, cvs1_moved =
    lterm1 |> fst |> List.partition (fun (c, v) ->
      abs(c) <= 1 && not (mem_vs v vs2)) in
  (* DB.hprint "LTERM1: " pr_lterm (cvs1, 0); *)
  let cvs2, i2 = mk_subt_lterm lterm2 (cvs1_moved, snd lterm1) in
  (* DB.hprint "LTERM2: " pr_lterm (cvs2, i2); *)
  if (List.length cvs1 = List.length cvs2) then
    let expss =
      let acc = ref [] in
      for index = 0 to (List.length cvs2) - 1 do
        let exps = List.mapi (fun d (c, v) ->
          let ec, ev = mk_iconst c, mk_exp_var v in
          if (d != index) then mk_bin_op Mul ec ev
          else mk_bin_op Add (mk_bin_op Mul ec ev) (mk_iconst i2)) cvs2 in
        acc := !acc @ [exps]
      done;
      !acc in
    expss |> List.map (fun exps -> List.map2 (fun (c, v) e ->
      (v, mk_bin_op Div e (mk_iconst c))) cvs1 exps) |>
    List.map (fun nssts -> unf.unf_correct_ssts @ nssts) |>
    List.map (fun ssts -> update_unification unf ~correct:(Some ssts))
  else []

(** unify the expression exp1 into the expression exp2 *)
let rec unify_exp exp1 exp2 vars unf : unification list =
  Debug.trace_4 "unify_exp"
    (pr_e, pr_e, pr_vs, pr_unf, pr_unfs) exp1 exp2 vars unf
    (fun () -> unify_exp_x exp1 exp2 vars unf)

and unify_exp_x exp1 exp2 vars unf : unification list =
  DB.nsprint ["UNIFY-EXP: "; pr_e exp1; "  --  "; pr_e exp2; "\n"];
  let vs1 = fv_exp exp1 in
  let correct_ssts = unf.unf_correct_ssts in
  let conflict_ssts = unf.unf_conflict_ssts in
  let new_exp1 = subst_exp correct_ssts exp1 in
  let unified_vars = correct_ssts |> List.split |> fst in
  DB.nsprint ["conflict ssts: "; pr_ssts conflict_ssts; "\n"];
  if (eq_exp new_exp1 exp2) then
    (* successful unification *)
    [unf]
  else if List.length conflict_ssts > 3 then
    (* too many conflict ssts *)
    []
  else if vs1 != [] && subset_vs vs1 unified_vars then
    (* failed unification *)
    match exp1, exp2 with
    | Var (v, _), e ->
      let conflict_ssts =
        if List.exists (eq_sst (v, e)) conflict_ssts then conflict_ssts
        else (v, exp2)::conflict_ssts in
      DB.nsprint ["NEW conflict ssts: "; pr_ssts conflict_ssts; "\n"];
      [update_unification unf ~correct:(Some correct_ssts)
         ~conflict:(Some conflict_ssts)]
    | _ -> [unf]
  else
    (* in-progress unification *)
    match new_exp1, exp2 with
    | IConst _, _ | Null _, _ ->
      let ununified_exps = (new_exp1, exp2)::unf.unf_ununifed_exps in
      [update_unification ~ununified:(Some ununified_exps) unf]
    | Var (v, _), _ -> unify_var v exp2 vars unf
    | LTerm (([(1,v)], c), _), _ ->
      let nexp = mk_bin_op Sub exp2 (mk_iconst c) in
      unify_var v nexp vars unf
    | LTerm (([(k,v)], c1), _), IConst (c2, _) ->
      if (k != 0) && (((c2 - c1) mod k) = 0) then
        let nc = mk_iconst ((c2 - c1) / k) in
        unify_var v nc vars unf
      else []
    | LTerm ((xs, c1), _), LTerm ((ys, c2), _) when
        List.length xs = List.length ys ->
      unify_lterm (xs, c1) (ys, c2) vars unf
    | LTerm ((((_::_) as xs), c), _), _ ->
      let rec create_sstss acc us vs = match vs with
        | [] -> acc
        | (1,v)::vs ->
          let nexp = mk_bin_op Sub exp2 (mk_lterm_exp (us@vs, c)) in
          let acc = acc @ (unify_var v nexp vars unf) in
          create_sstss acc (us @ [(1,v)]) vs
        | (-1,v)::vs ->
          let nexp = mk_bin_op Sub (mk_lterm_exp (us@vs, c)) exp2 in
          let acc = acc @ (unify_var v nexp vars unf) in
          create_sstss acc (us @ [(-1,v)]) vs
        | cv::vs -> create_sstss acc (us @ [cv]) vs in
      create_sstss [] [] xs
    | _ -> []

(** unify the heap atom htom1 into the heap atom hatom2 *)
let rec unify_hatom prog hatom1 hatom2 vars unf : unification list =
  Debug.trace_4 "unify_hatom"
    (pr_ha, pr_ha, pr_vs, pr_unf, pr_unfs) hatom1 hatom2 vars unf
    (fun () -> unify_hatom_x prog hatom1 hatom2 vars unf)

and unify_hatom_x prog hatom1 hatom2 vars unf : unification list =
  DB.nsprint ["UNIFY-HATOM: "; pr_ha hatom1; "  --  "; pr_ha hatom2; "\n"];
  let args_pairs = match hatom1, hatom2 with
    | HData df1, HData df2 when (eq_s df1.dataf_name df2.dataf_name) ->
      let args1 = df1.dataf_root::df1.dataf_args in
      let args2 = df2.dataf_root::df2.dataf_args in
      List.combine args1 args2
    | HView vf1, HView vf2 when (eq_s vf1.viewf_name vf2.viewf_name) ->
      (* reorder vars with inductive-vars have higher priority *)
      let weights =
        let vd = find_view_defn prog.prog_views vf1.viewf_name in
        vd.view_params |> List.map (fun v ->
          if mem_vs v vd.view_inductive_vars then 1 else 0) in
      weights |> List.combine3 vf1.viewf_args vf2.viewf_args |>
      List.sortd (fun (_,_,x) (_,_,y) -> x - y) |>
      List.map (fun (a,b,c) -> (a,b))
    | _ -> [] in
  let unfs =
    let clustered_pairs = List.cluster (fun (a1, a2) (b1, b2) ->
      String.compare (pr_e a1) (pr_e b1)) args_pairs in
    let pairingss =
      clustered_pairs |>
      List.map (fun groups -> Comb.gen_permutations groups) |>
      Comb.gen_cartesian |> List.map List.concat in
    pairingss |> List.map (fun pairings ->
      List.fold_left (fun asubsts (a1, a2) ->
        asubsts |> List.map (unify_exp a1 a2 vars) |>
        List.concat) [unf] pairings) |>
    List.concat in
  unfs

(** unify the heap atoms hatoms1 into into the heap atoms hatoms2 *)
and unify_hatoms prog hatoms1 hatoms2 pairs vars unf : unification list =
  let pr_pairs = pr_list_sbrace (pr_pair pr_ha pr_ha) in
  Debug.trace_5 "unify_hatoms"
    (pr_has, pr_has, pr_pairs, pr_vs, pr_unf, pr_unfs)
    hatoms1 hatoms2 pairs vars unf
    (fun () -> unify_hatoms_x prog hatoms1 hatoms2 pairs vars unf)

and unify_hatoms_x prog hatoms1 hatoms2 pairs vars unf : unification list =
  let rec split_one_hatom filter acc head tail = match tail with
    | [] -> acc
    | u::us ->
      let nacc = if (filter u) then acc @ [(u, head @ us)] else acc in
      split_one_hatom filter nacc (head @ [u]) us in
  match hatoms1 with
  | [] -> [update_unification unf ~residue:(Some hatoms2) ~pairs:(Some pairs)]
  | x::xs ->
    hatoms2 |> split_one_hatom (is_hatom_same_type x) [] [] |>
    List.map (fun (y, ys) ->
      unf|> unify_hatom prog x y vars |>
      List.map (unify_hatoms prog xs ys ((x,y)::pairs) vars)) |>
    List.concat |> List.concat

(** unify the formula f1 into the formula f2 *)
let rec unify_heap prog (f1: formula) (f2: formula) : unification list =
  Debug.trace_2 "unify_heap"
    (pr_f, pr_f, pr_unfs) f1 f2
    (fun () -> unify_heap_x prog f1 f2)

and unify_heap_x prog (f1: formula) (f2: formula) : unification list =
  try
    match f1, f2 with
    | FBase (h1, p1, _), FBase (h2, p2, _) ->
      let dfs1, vfs1 = collect_data_form_hf h1, collect_view_form_hf h1 in
      let dfs2, vfs2 = collect_data_form_hf h2, collect_view_form_hf h2 in
      if (List.length dfs1 > List.length dfs2) then
        raise (EUnfs []);
      if (List.length vfs1 > List.length vfs2) then
        raise (EUnfs []);
      (* the order matters: unify views first *)
      let hfs1 =
        let vfs1 = vfs1 |> List.sorti (fun u v ->
          List.length (fv_vf u) - List.length (fv_vf v)) in
        (List.map mk_hatom_vf vfs1) @ (List.map mk_hatom_df dfs1) in
      let hfs2 =
        let vfs2 = vfs2 |> List.sorti (fun u v ->
          List.length (fv_vf u) - List.length (fv_vf v)) in
        (List.map mk_hatom_vf vfs2) @ (List.map mk_hatom_df dfs2) in
      let vars = diff_vs (fv f1) (fv f2) in  (* vars to be substituted *)
      let init_unf = mk_unification [] [] [] [] [] in
      let unfs = unify_hatoms prog hfs1 hfs2 [] vars init_unf |> dedup_unfs in
      let unfs_success, unfs_fail = List.partition (fun unf ->
        unf.unf_conflict_ssts = []) unfs in
      (* DB.hprint "UNFS FAIL: " pr_unfs unfs_fail; *)
      if (unfs_success != []) then raise (EUnfs unfs_success)
      else raise (EUnfs unfs_fail)
    | _ -> []
  with EUnfs res ->
    DB.nsprint ["UNIFY-HEAP:\n";
                "   - f1: "; (pr_f f1); "\n";
                "   - f2: "; (pr_f f2); "\n";
                "   - Result:\n"; (pr_unfs res); "\n"];
    res

(** extend unification unf with new unification from f1 to f2 *)
let extend_heap_unification prog unf f1 f2 =
  let nf1 = NO.remove_all_qvars (subst unf.unf_correct_ssts f1) in
  let nf2 = NO.remove_all_qvars f2 in
  let vs = dedup_vs ((fv f1) @ (fv f2)) in
  let sstss =
    unify_heap prog nf1 nf2 |> get_unf_success |>
    List.map (fun runf -> List.filter (fun (v, e) ->
      diff_vs (v :: (fv_exp e)) vs = []) runf.unf_correct_ssts) |>
    List.filter (fun ssts -> ssts != []) |> dedup_sstss |>
    (fun sstss -> []::sstss) in
  List.map (fun ssts ->
    {unf with unf_correct_ssts = unf.unf_correct_ssts @ ssts}) sstss

(** check if f1 can unify with f2 *)
let rec unify_pure mode prog (f1: formula) (f2: formula) unf : bool =
  Debug.trace_3 "unify_pure" (pr_f, pr_f, pr_unf, pr_b) f1 f2 unf
    (fun () -> unify_pure_x mode prog f1 f2 unf)

and unify_pure_x mode prog (f1: formula) (f2: formula) unf : bool =
  try (
    if unf.unf_conflict_ssts != [] then raise_bool false;
    let nf1 = subst unf.unf_correct_ssts f1 in
    let vs1, vs2 = fv nf1, fv f2 in
    match nf1, f2 with
    | FBase (_, p1, _), FBase (_, p2, _) ->
      let np1 =
        let evs = diff_vs vs1 vs2 in
        mk_pexists evs p1 in
      if (PT.check_imply_slice_lhs p2 np1 = MvlTrue) then true
      else false
    | _ -> false)
  with EBool res -> res
