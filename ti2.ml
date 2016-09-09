#include "xdebug.cppo"
open VarGen
(* module CP = Cpure    *)
(* module CF = Cformula *)
(* module MCP = Mcpure  *)

open Cprinter
open Globals
open Gen
open Tlutils
open Tid
open Ti3

let om_simplify f = 
  (* let () = x_tinfo_hp (add_str "om_simplify" !CP.print_formula) f no_pos in *)
  (* Tpdispatcher.simplify_raw f *)
  try
    if CP.is_linear_formula f then
      (* let () = x_binfo_hp (add_str "is_omega_running" string_of_bool) !Omega.is_omega_running no_pos in *)
      x_add_1 Omega.simplify f
    else if !VarGen.compete_mode then f
    else Redlog.simplify f
  with _ -> f

let om_simplify f =
  let pr = !CP.print_formula in
  Debug.no_1 "Ti2.om_simplify" pr pr om_simplify f

let eq_str s1 s2 = String.compare s1 s2 = 0

let simplify f args = 
  let bnd_vars = diff (CP.fv f) args in
  if bnd_vars == [] then f else
    CP.mkExists_with_simpl om_simplify (* Tpdispatcher.simplify_raw *)
      bnd_vars f None (CP.pos_of_formula f)

let simplify f args =
  let pr1 = !CP.print_formula in
  let pr2 = pr_list !CP.print_sv in
  Debug.no_2 "Ti2.simplify" pr1 pr2 pr1
    (fun _ _ -> simplify f args) f args

let is_sat f = 
  Tpdispatcher.is_sat_raw (MCP.mix_of_pure f)
  (* let (pr_weak, pr_strong) = CP.drop_complex_ops in *)
  (* Omega.is_sat_ops pr_weak pr_strong f ""           *)

let is_sat f = 
  let pr = !CP.print_formula in
  Debug.no_1 "Ti2.is_sat" pr string_of_bool is_sat f

let imply a c = Tpdispatcher.imply_raw a c

let imply a c =
  let pr = !CP.print_formula in
  Debug.no_2 "Ti2.imply" pr pr string_of_bool imply a c

let pairwisecheck = Tpdispatcher.tp_pairwisecheck

let simplify_disj f = 
  let f = om_simplify f in
  let f =
    if CP.is_disjunct f then pairwisecheck f
    else f 
  in f

let simplify_disj f =
  let pr = !CP.print_formula in
  Debug.no_1 "simplify_disj" pr pr
    simplify_disj f

let simplify_and_slit_disj f = 
  let f = simplify_disj f in
  let fs = CP.split_disjunctions f in
  List.filter is_sat fs

(* To be improved *)
let fp_imply f p =
  let _, pf, _, _, _, _ = CF.split_components f in
  let (res, _, _) = Tpdispatcher.mix_imply pf (MCP.mix_of_pure p) "999" in
  res

let fp_imply f p =
  Debug.no_2 "fp_imply" Cprinter.string_of_formula Cprinter.string_of_pure_formula string_of_bool fp_imply f p

(* let unsat_base_nth = ref (fun _ _ _ _ -> true) (* Solver.unsat_base_nth *) *)

(* let f_is_sat prog f =                                                      *)
(*   (* let _, pf, _, _, _, _ = CF.split_components f in *)                   *)
(*   (* Tpdispatcher.is_sat_raw pf                       *)                   *)
(*   not (!unsat_base_nth 1 prog (ref 0) f)                                   *)

let entail_inf = ref (fun _ _ _ -> None) (* Solver.heap_entail_one_context *)

let join_disjs f_lst = 
  if is_empty f_lst then CP.mkFalse no_pos
  else CP.join_disjunctions f_lst

let mkAnd f1 f2 = CP.mkAnd f1 f2 no_pos
let mkOr f1 f2 = CP.mkOr f1 f2 None no_pos
let mkNot f = CP.mkNot f None no_pos
let mkGt e1 e2 = CP.mkPure (CP.mkGt e1 e2 no_pos)
let mkGte e1 e2 = CP.mkPure (CP.mkGte e1 e2 no_pos)
let mkEq e1 e2 = CP.mkPure (CP.mkEq e1 e2 no_pos)

(* Partition a list of conditions into disjoint conditions *)
let rec partition_cond_list is_disj cond_list = 
  match cond_list with
  | [] -> []
  | c::cs ->
    let dcs = partition_cond_list is_disj cs in
    let rec helper c dcs =
      match dcs with
      | [] -> [c]
      | d::ds -> 
        if not (x_add_1 is_sat (mkAnd c d)) then d::(helper c ds)
        else if is_disj && (x_add imply c d) then dcs
        else (mkAnd c d)::(mkAnd (mkNot c) d)::(helper (mkAnd c (mkNot d)) ds)
    in helper c dcs

let partition_cond_list is_disj cond_list = 
  let pr = pr_list !CP.print_formula in
  Debug.no_1 "partition_cond_list" pr pr
    (fun _ -> partition_cond_list is_disj cond_list) cond_list

let get_full_disjoint_cond_list is_disj cond_list = 
  let disj_cond_lst = partition_cond_list is_disj cond_list in
  let () = x_tinfo_hp (add_str "disj_cond_lst" (pr_list !CP.print_formula)) disj_cond_lst no_pos in
  let rem_cond = mkNot (CP.join_disjunctions disj_cond_lst) in
  let rem_cond_lst =
    if x_add_1 is_sat rem_cond then CP.split_disjunctions (om_simplify rem_cond)
    else [] 
  in
  (* let rem_cond_lst = List.filter is_sat (CP.split_disjunctions (om_simplify rem_cond)) in *)
  let r = (List.map om_simplify disj_cond_lst) @ rem_cond_lst in
  let () = x_tinfo_hp (add_str "full_disjoint_cond_list" (pr_list !CP.print_formula)) r no_pos in
  r

let get_full_disjoint_cond_list is_disj cond_list = 
  let pr = pr_list !CP.print_formula in
  Debug.no_1 "get_full_disjoint_cond_list" pr pr
    (fun _ -> get_full_disjoint_cond_list is_disj cond_list) cond_list

let get_full_disjoint_cond_list_with_ctx ctx cond_list = 
  let disj_cond_lst = partition_cond_list true cond_list in
  let rem_cond = mkNot (CP.join_disjunctions disj_cond_lst) in
  let rem_cond_lst = List.filter (fun c -> is_sat (mkAnd ctx c)) 
      (CP.split_disjunctions (om_simplify rem_cond))
  in (List.map om_simplify disj_cond_lst) @ rem_cond_lst

let seq_num = ref 0    

let tnt_fresh_int () = 
  seq_num := !seq_num + 1;
  !seq_num

let reset_seq_num _ =
  seq_num := 0

let scc_num = ref 0    

let scc_fresh_int () = 
  scc_num := !scc_num + 1;
  !scc_num

let reset_scc_num _ =
  scc_num := 0

(* This method returns a unique number for (a, b) *)
(* It is used to generate num for new instantiated TermU *)    
let cantor_pair a b = (a + b) * (a + b + 1) / 2 + b

let assign_id_to_list ls = 
  snd (List.fold_left (fun (i, a) e -> 
      (i + 1, a @ [(i + 1, e)])) (0, []) ls)

(******************************************************************************)

(* Result for Return Relation Assumptions *)
type trrel_sol = 
  | Base of CP.formula
  | Rec of CP.formula (* Recursive case *)
  | MayTerm of CP.formula (* Both base and rec cases may be reachable from this case *)

let print_trrel_sol s = 
  let pr = !CP.print_formula in
  match s with
  | Base c -> (pr c) ^ "@B"
  | Rec c -> (pr c) ^ "@R"
  | MayTerm c -> (pr c) ^ "@ML"

let trans_trrel_sol f = function
  | Base c -> Base (f c)
  | Rec c -> Rec (f c)
  | MayTerm c -> MayTerm (f c)

let fold_trrel_sol f = function
  | Base c -> let cs = f c in List.map (fun c -> Base c) cs 
  | Rec c -> let cs = f c in List.map (fun c -> Rec c) cs 
  | MayTerm c -> let cs = f c in List.map (fun c -> MayTerm c) cs 

let simplify_trrel_sol = trans_trrel_sol om_simplify

let split_disj_trrel_sol s =
  fold_trrel_sol CP.split_disjunctions s

let is_base = function
  | Base _ -> true
  | _ -> false

let is_rec = function
  | Rec _ -> true
  | _ -> false

let is_mayterm = function
  | MayTerm _ -> true
  | _ -> false

let get_cond = function
  | Base c -> c
  | Rec c -> c
  | MayTerm c -> c

let get_rec_conds conds = 
  List.map get_cond (List.filter is_rec conds)  

let params_of_term_ann prog ann =
  match ann with
  | CP.TermU uid
  | CP.TermR uid ->
    let sid = uid.CP.tu_sid in
    begin try
        let ut_decl = List.find (fun utd -> 
            String.compare utd.Cast.ut_name sid == 0) prog.Cast.prog_ut_decls in
        ut_decl.Cast.ut_params
      with Not_found -> 
        report_error no_pos ("[TNT Inference]: Definition of " ^ sid ^ " cannot be found.")
    end
  | _ -> []

(* Solution substitution *)
let subst_sol_term_ann sol ann =
  match ann with
  | CP.TermU uid -> CP.TermU { uid with 
                               tu_sol = match uid.tu_sol with
                                 | None -> Some sol 
                                 | _ -> uid.CP.tu_sol }
  | CP.Term -> 
    begin match (fst sol) with
      | CP.Loop _
      | CP.MayLoop _ -> report_error no_pos 
                          "[TNT Inference]: A non-terminating program state is specified with Term."
      | _ -> ann
    end
  | _ -> ann

(******************************************************************************)

(* Specification *)

(* Stack for TNT case specs of all methods *)
let proc_case_specs: (ident, tnt_case_spec) Hashtbl.t = 
  Hashtbl.create 20

let case_spec_of_trrel_sol call_num pos sol =
  match sol with
  | Base c -> (c, Sol (CP.Term, 
                       [CP.mkIConst call_num pos; CP.mkIConst (scc_fresh_int ()) pos]))
  | Rec c -> (c, Unknown None)
  | MayTerm c -> (c, Sol (CP.MayLoop None, [])) 

let add_case_spec_of_trrel_sol_proc prog (fn, sols) =
  let call_num, proc_pos = 
    try
      let proc = Cast.look_up_proc_def_no_mingling no_pos prog.Cast.new_proc_decls fn in
      proc.Cast.proc_call_order, proc.Cast.proc_loc
    with _ -> 0, no_pos
  in
  let cases = List.map (case_spec_of_trrel_sol call_num proc_pos) sols in
  Hashtbl.add proc_case_specs fn (Cases cases)

let rec update_case_spec spec cond sol = 
  match spec with
  | Sol _ -> spec
  | Unknown _ -> sol
  | Cases cases -> 
    let rec helper cases =
      match cases with
      | [] -> cases
      | (c, case)::rem ->
        if x_add imply cond c then (c, (update_case_spec case cond sol))::rem
        else (c, case)::(helper rem)
    in Cases (helper cases)

let update_case_spec_proc fn cond sol = 
  try
    let spec = Hashtbl.find proc_case_specs fn in
    let nspec = update_case_spec spec cond sol in
    Hashtbl.replace proc_case_specs fn nspec
  with Not_found ->
    Hashtbl.add proc_case_specs fn sol

let add_sol_case_spec_proc fn cond sol = 
  update_case_spec_proc fn cond (Sol sol)

let update_case_spec_with_icond_proc fn cond icond = 
  update_case_spec_proc fn cond 
    (Cases [(icond, Unknown None); (mkNot icond, Unknown None)])

let update_case_spec_with_icond_list_proc fn cond icond_lst =
  if is_empty icond_lst then ()
  else update_case_spec_proc fn cond 
      (Cases (List.map (fun c -> (c, Unknown None)) icond_lst))

let rec merge_cases_tnt_case_spec spec = 
  match spec with
  | Cases cases ->
    let merged_cases = List.map (fun (c, sp) -> 
        (c, merge_cases_tnt_case_spec sp)) cases in
    let grouped_cases = partition_eq (fun (_, sp1) (_, sp2) ->
        eq_tnt_case_spec sp1 sp2) merged_cases in
    let grouped_cases = List.fold_left (fun acc cs ->
        match cs with
        | [] -> acc
        | (c, sp)::cs ->
          let nc = CP.join_disjunctions (c::(List.map fst cs)) in
          acc @ [(pairwisecheck nc, sp)]) [] grouped_cases in
    Cases grouped_cases
  | _ -> spec

let merge_cases_tnt_case_spec spec = 
  let pr = print_tnt_case_spec in
  Debug.no_1 "merge_cases_tnt_case_spec" pr pr
    merge_cases_tnt_case_spec spec

let rec merge_cond_tnt_case_spec spec = 
  match spec with
  | Cases cases ->
    List.concat (List.map (fun (c, sp) ->
        let flatten_sp = merge_cond_tnt_case_spec sp in
        List.map (fun (cond_lst, sp) -> (c::cond_lst, sp)) flatten_sp) cases)
  | _ -> [([], spec)]

let add_conds_to_cex conds cex =
  let assume_conds = List.map (fun c -> CP.TAssume c) conds in
  match cex with
  | None -> Some ({ CP.tcex_trace = assume_conds })
  | Some cex -> Some ({ cex with CP.tcex_trace = assume_conds @ cex.CP.tcex_trace })

let elim_nondet_vars f = 
  let fv_f = CP.fv f in
  let nondet_vars = List.find_all is_nondet_var fv_f in 
  let params = diff fv_f nondet_vars in
  x_add simplify f params, nondet_vars

let remove_nondet_vars svl = 
  List.filter (fun v -> not (is_nondet_var v)) svl

let merge_nondet_cases cases =
  let flatten_cases = merge_cond_tnt_case_spec (Cases cases) in 
  match flatten_cases with
  | [] -> []
  | (conds, sp)::_ ->
    if (List.for_all (fun (_, sp) -> is_Loop sp) flatten_cases) then
      match sp with
      | Sol (CP.Loop cex, []) -> 
        let loop_cond = pairwisecheck (CP.join_disjunctions (List.concat (List.map fst flatten_cases))) in
        let loop_cond, _ = elim_nondet_vars loop_cond in
        [(loop_cond, Sol (CP.Loop (add_conds_to_cex conds cex), []))]
      | _ -> report_error no_pos "[TNT Inference] merge_nondet_cases expects a Loop TNT spec"
    else if (List.for_all (fun (_, sp) -> is_Term sp) flatten_cases) then
      (* List.map (fun (c, sp) -> (elim_nondet_vars c, sp)) cases *)
      cases
    else (* MayLoop *)
      try
        let conds, loop_sp = List.find (fun (_, sp) -> is_Loop sp) flatten_cases in
        (match loop_sp with
         | Sol (CP.Loop cex, []) ->
           let cond = pairwisecheck (CP.join_disjunctions conds) in
           let mayloop_cond, _ = elim_nondet_vars cond in
           [(mayloop_cond, Sol (CP.MayLoop (add_conds_to_cex conds cex), []))]
         | _ -> report_error no_pos "[TNT Inference] merge_nondet_cases expects a Loop TNT spec"
        ) 
      with _ ->
        try
          let conds, mayloop_sp = List.find (fun (_, sp) -> is_cex_MayLoop sp) flatten_cases in
          (match mayloop_sp with
           | Sol (CP.MayLoop cex, []) ->
             let cond = pairwisecheck (CP.join_disjunctions conds) in
             let mayloop_cond, _ = elim_nondet_vars cond in
             [(mayloop_cond, Sol (CP.MayLoop (add_conds_to_cex conds cex), []))]
           | _ -> report_error no_pos "[TNT Inference] merge_nondet_cases expects a MayLoop TNT spec"
          )
        with _ ->
          let mayloop_cond = pairwisecheck (CP.join_disjunctions (List.concat (List.map fst flatten_cases))) in
          let mayloop_cond, _ = elim_nondet_vars mayloop_cond in
          [(mayloop_cond, Sol (CP.MayLoop None, []))]

let rec norm_nondet_tnt_case_spec spec = 
  match spec with
  | Cases cases ->
    let normed_cases = List.map (fun (c, sp) -> (c, norm_nondet_tnt_case_spec sp)) cases in
    let nondet_cases, normal_cases = List.partition (fun (c, _) -> is_nondet_cond c) normed_cases in
    let merged_nondet_cases = merge_nondet_cases nondet_cases in
    (match merged_nondet_cases with
     | [] -> Cases normal_cases
     | (c, sp)::[] ->
       if (is_empty normal_cases) then sp 
       else Cases (normal_cases @ [(c, sp)])
     | _ -> Cases (normal_cases @ merged_nondet_cases)
    )
  | _ -> spec

let rec flatten_one_case_tnt_spec c f = 
  match f with
  | Cases cases ->
    let cfv = CP.fv c in
    let should_flatten = List.for_all (fun (fc, _) ->
        subset (CP.fv fc) cfv) cases in
    if not should_flatten then [(c, f)]
    else
      List.fold_left (fun fac (fc, ff) ->
          let mc = mkAnd c fc in
          if is_sat mc then fac @ [(mc, ff)]
          else fac) [] cases
  | _ -> [(c, f)]

let rec flatten_case_tnt_spec f =
  match f with
  | Cases cases -> 
    let ncases = List.fold_left (fun ac (c, f) -> 
        let nf = flatten_case_tnt_spec f in
        let mf = flatten_one_case_tnt_spec c nf in 
        ac @ mf) [] cases in
    Cases ncases
  | _ -> f

let add_cex_by_cond for_loop turels c cex =
  let rec has_feasible_cex c turel =
    (* Due to over-approximation, the context call_ctx of turel *)
    (* might not be reachable from c though SAT(c /\ call_ctx)  *)
    (is_sat (mkAnd c turel.call_ctx)) &&
    not (is_None (CP.cex_of_term_ann turel.termu_rhs)) &&
    (if not for_loop && CP.is_Loop turel.termu_rhs then
       (is_nondet_cond c) || (is_nondet_cond turel.call_ctx) 
     else true)
  in
  try
    let turel = List.find (has_feasible_cex c) turels in
    let cpos = turel.termu_pos in
    let acex = CP.cex_of_term_ann turel.termu_rhs in
    let mcex = CP.merge_term_cex cex acex in
    begin match mcex with
      | None -> if for_loop then Some ({ CP.tcex_trace = [CP.TCall cpos] }) else mcex
      | Some t -> Some ({ t with CP.tcex_trace = (CP.TCall cpos)::t.CP.tcex_trace })
    end
  with Not_found ->
    if for_loop then
      try
        let turel = List.find (fun tur -> is_sat (mkAnd c tur.call_ctx)) turels in
        let cpos = turel.termu_pos in
        begin match cex with
          | None -> Some ({ CP.tcex_trace = [CP.TCall cpos] })
          | Some t -> Some ({ t with CP.tcex_trace = (CP.TCall cpos)::t.CP.tcex_trace })
        end
      with Not_found -> cex
    else cex

let rec add_cex_tnt_case_spec_cond turels c f =
  match f with
  | Cases cases ->
    let ncases = List.map (fun (sc, sf) ->
        (sc, add_cex_tnt_case_spec_cond turels (mkAnd c sc) sf)) cases in
    Cases ncases
  | Sol (s, r) ->
    let ns = match s with
      | CP.Loop cex -> CP.Loop (add_cex_by_cond true turels c cex)
      | CP.MayLoop cex -> CP.MayLoop (add_cex_by_cond false turels c cex)
      | _ -> s in
    Sol (ns, r)
  | Unknown cex -> Unknown (add_cex_by_cond false turels c cex)

let add_cex_tnt_case_spec f = 
  let turels = call_trel_stk # get_stk in
  add_cex_tnt_case_spec_cond turels (CP.mkTrue no_pos) f
  
let add_cex_tnt_case_spec f = 
  let pr = print_tnt_case_spec in
  Debug.no_1 "add_cex_tnt_case_spec" pr pr
    (fun _ -> add_cex_tnt_case_spec f) f

(* From TNT spec to struc formula *)
(* For SLEEK *)
let struc_formula_of_ann (ann, rnk) =
  let pos = no_pos in
  let p_pre = MCP.mix_of_pure (CP.mkLexVar_pure ann rnk []) in
  let p_post = match ann with
    | CP.Loop _ -> MCP.mkMFalse pos 
    | _ -> MCP.mkMTrue pos
  in
  let f_pre = CF.mkBase_simp CF.HEmp p_pre in
  let f_post = CF.mkBase_simp CF.HEmp p_post in
  let lbl = fresh_formula_label "" in
  let post = CF.mkEAssume [] f_post (CF.mkEBase f_post None pos) lbl None in
  let spec = CF.mkEBase f_pre (Some post) pos  in
  spec

(* For HIP with given specifications *)  
let struc_formula_of_ann_w_assume assume (ann, rnk) =
  let pos = no_pos in
  let p_pre = MCP.mix_of_pure (CP.mkLexVar_pure ann rnk []) in
  let f_pre = CF.mkBase_simp CF.HEmp p_pre in

  let post = match ann with
    | CP.Loop _ ->
      let f_post = CF.mkBase_simp CF.HEmp (MCP.mkMFalse pos) in
      CF.EAssume { assume with
                   CF.formula_assume_simpl = f_post;
                   CF.formula_assume_struc = CF.mkEBase f_post None pos; }
    | _ -> TermUtils.strip_lexvar_post false (CF.EAssume assume)
  in
  let spec = CF.mkEBase f_pre (Some post) pos in
  spec

let struc_formula_of_dead_path _ =
  let pos = no_pos in
  let pp = CF.mkBase_simp CF.HEmp (MCP.mkMFalse pos) in
  let lbl = fresh_formula_label "" in
  let post = CF.mkEAssume [] pp (CF.mkEBase pp None pos) lbl None in
  let spec = CF.mkEBase pp (Some post) pos  in
  spec

let struc_formula_of_dead_path _ =
  let pr = string_of_struc_formula in
  Debug.no_1 "struc_formula_of_dead_path" (fun _ -> "") pr
    struc_formula_of_dead_path ()

let rec struc_formula_of_tnt_case_spec spec =
  match spec with
  | Sol s -> struc_formula_of_ann s
  | Unknown cex -> struc_formula_of_ann (CP.MayLoop cex, [])
  | Cases cases -> CF.ECase {
      CF.formula_case_branches = List.map (fun (c, s) -> 
          (c, struc_formula_of_tnt_case_spec s)) cases;
      CF.formula_case_pos = no_pos; }

let print_tnt_case_spec spec =
  let struc = struc_formula_of_tnt_case_spec spec in
  string_of_struc_formula_for_spec struc 

let rec collect_term_ann_in_tnt_case_spec spec =
  match spec with
  | Sol (tann, _) -> [tann]
  | Unknown _ -> []
  | Cases fsl ->
    List.concat (List.map (fun (f,s) ->
        (Cpure.collect_term_ann f) @ (collect_term_ann_in_tnt_case_spec s)
      ) fsl)

let rec merge_tnt_case_spec_into_struc_formula prog ctx spec sf = 
  match sf with
  | CF.ECase ec -> CF.ECase { 
      ec with
        CF.formula_case_branches = List.map (fun (c, ef) ->
            let ctx, _ = CF.combine_and ctx (MCP.mix_of_pure c) in
            c, merge_tnt_case_spec_into_struc_formula prog ctx spec ef) ec.CF.formula_case_branches }
  | CF.EBase eb -> 
    let pos = eb.CF.formula_struc_pos in 
    let base = eb.CF.formula_struc_base in
    let cont = eb.CF.formula_struc_continuation in

    let update_ebase b = 
      if CF.isConstTrueFormula b then
        match cont with
        | None -> CF.EBase { eb with CF.formula_struc_base = b; }
        | Some c -> merge_tnt_case_spec_into_struc_formula prog ctx spec c
      else
        let nctx = x_add CF.normalize 16 ctx b pos in
        CF.EBase { eb with
                   CF.formula_struc_base = b;
                   CF.formula_struc_continuation = map_opt 
                       (merge_tnt_case_spec_into_struc_formula prog nctx spec) cont }
    in

    (* let has_lexvar, has_unknown_pre_lexvar = CF.has_unknown_pre_lexvar_formula base in *)
    (* if has_unknown_pre_lexvar then                                                     *)
    (*   let nbase = snd (TermUtils.strip_lexvar_formula base) in                         *)
    (*   update_ebase nbase                                                               *)
    (* else if has_lexvar then                                                            *)
    (*   CF.EBase { eb with                                                               *)
    (*     CF.formula_struc_continuation = map_opt                                        *)
    (*       TermUtils.strip_lexvar_post cont }                                           *)
    (* else update_ebase base                                                             *)
    let term_ann_base = CF.collect_term_ann base in 
    if is_empty term_ann_base then update_ebase base
    else if List.exists CP.is_TermU term_ann_base then (* has_unknown_pre_lexvar *)
      let nbase = snd (TermUtils.strip_lexvar_formula base) in
      update_ebase nbase
    else (* has_lexvar *)
      let has_loop = List.exists CP.is_Loop term_ann_base in
      CF.EBase { eb with
                 CF.formula_struc_continuation = map_opt
                     (TermUtils.strip_lexvar_post has_loop) cont } 
  | CF.EAssume af -> merge_tnt_case_spec_into_assume prog ctx spec af
  | CF.EInfer ei -> 
    let cont = merge_tnt_case_spec_into_struc_formula prog ctx spec ei.CF.formula_inf_continuation in
    let () = ei.CF.formula_inf_obj # reset INF_TERM in
    let () = ei.CF.formula_inf_obj # reset INF_TERM_WO_POST in
    if ei.CF.formula_inf_obj # is_empty then cont
    else CF.EInfer { ei with CF.formula_inf_continuation = cont }
  | CF.EList el -> 
    CF.mkEList_no_flatten (map_l_snd (merge_tnt_case_spec_into_struc_formula prog ctx spec) el)

and merge_tnt_case_spec_into_assume prog ctx spec af =
  match spec with
  | Sol s -> struc_formula_of_ann_w_assume af s
  | Unknown cex -> struc_formula_of_ann_w_assume af (CP.MayLoop cex, [])
  | Cases cases -> 
    try (* Sub-case of current context; all other cases are excluded *)
      let sub_case = List.find (fun (c, _) -> x_add fp_imply ctx c) cases in
      merge_tnt_case_spec_into_assume prog ctx (snd sub_case) af
    with _ -> 
      let merged_cases = List.fold_left (
          fun acc (c, s) ->
            let mix_ctx, _, _ = x_add Cvutil.xpure 100 prog ctx in
            let pure_ctx = MCP.pure_of_mix mix_ctx in
            let nc = Tpdispatcher.om_gist c pure_ctx in
            if is_sat nc then acc @ [(nc, merge_tnt_case_spec_into_assume prog ctx s af)]
            else acc) [] cases
      in
      CF.ECase {
        (* CF.formula_case_branches = List.map (fun (c, s) ->                                *)
        (*     let nctx, _ = CF.combine_and ctx (MCP.mix_of_pure c) in                       *)
        (*     if f_is_sat prog nctx then (c, merge_tnt_case_spec_into_assume prog ctx s af) *)
        (*     else (c, struc_formula_of_dead_path ())) cases;                               *)
        CF.formula_case_branches = merged_cases;
        CF.formula_case_pos = no_pos; }

let merge_tnt_case_spec_into_struc_formula prog ctx spec sf =
  let pr1 = print_tnt_case_spec in
  let pr2 = string_of_struc_formula_for_spec in
  Debug.no_2 "merge_tnt_case_spec_into_struc_formula" pr1 pr2 pr2
    (fun _ _ -> merge_tnt_case_spec_into_struc_formula prog ctx spec sf) spec sf

let rec flatten_one_case_struc c f = 
  match f with
  | CF.ECase fec ->
    let cfv = CP.fv c in
    let should_flatten = List.for_all (fun (fc, _) ->
        subset (CP.fv fc) cfv) fec.CF.formula_case_branches in
    if not should_flatten then [(c, f)]
    else
      List.fold_left (fun fac (fc, ff) ->
          let mc = mkAnd c fc in
          if is_sat mc then fac @ [(mc, ff)]
          else fac) [] fec.CF.formula_case_branches
  | CF.EList el -> begin match el with
      | (_, sf)::[] ->  begin match sf with
          | CF.ECase _ -> flatten_one_case_struc c sf
          | _ -> [(c, f)]
        end
      | _ -> [(c, f)]
    end
  | _ -> [(c, f)]

let rec flatten_case_struc struc_f =
  match struc_f with
  | CF.ECase ec -> 
    let nbranches = List.fold_left (fun ac (c, f) -> 
        let nf = flatten_case_struc f in
        let mf = flatten_one_case_struc c nf in 
        ac @ mf) [] ec.CF.formula_case_branches 
    in CF.ECase { ec with CF.formula_case_branches = nbranches }
  | CF.EBase eb -> CF.EBase { eb with CF.formula_struc_continuation = 
                                        map_opt flatten_case_struc eb.CF.formula_struc_continuation }
  | CF.EAssume _ -> struc_f
  | CF.EInfer ei -> CF.EInfer { ei with CF.formula_inf_continuation = 
                                          flatten_case_struc ei.CF.formula_inf_continuation }
  | CF.EList el -> CF.mkEList_no_flatten (map_l_snd flatten_case_struc el)

let flatten_case_struc struc_f = 
  let pr = string_of_struc_formula_for_spec in
  Debug.no_1 "flatten_case_struc" pr pr flatten_case_struc struc_f

let rec norm_struc struc_f = 
  match struc_f with
  | CF.ECase ec -> CF.ECase { ec with 
      CF.formula_case_branches = List.map (fun (c, f) -> (om_simplify c, f)) ec.CF.formula_case_branches }
  | CF.EBase eb -> CF.EBase { eb with 
      CF.formula_struc_continuation = map_opt norm_struc eb.CF.formula_struc_continuation }
  | CF.EAssume _ -> struc_f
  | CF.EInfer ei ->
    (* let () = ei.CF.formula_inf_obj # reset INF_TERM in *)
    CF.EInfer { ei with
      CF.formula_inf_continuation = norm_struc ei.CF.formula_inf_continuation }
  | CF.EList el -> CF.mkEList_no_flatten (map_l_snd norm_struc el)

let norm_struc struc_f = 
  let pr = !CF.print_struc_formula in
  Debug.no_1 "norm_struc" pr pr norm_struc struc_f

let tnt_spec_of_proc prog proc ispec =
  let ispec = add_cex_tnt_case_spec ispec in
  let ispec = 
    merge_cases_tnt_case_spec
      (flatten_case_tnt_spec 
         (norm_nondet_tnt_case_spec ispec)) 
  in
  let pr = string_of_struc_formula(*_for_spec*) in
  (* let spec = proc.Cast.proc_static_specs in *)
  let spec = proc.Cast.proc_stk_of_static_specs # top in
  let () = y_tinfo_hp (add_str "original spec" pr) spec in
  let spec = merge_tnt_case_spec_into_struc_formula prog
      (CF.mkTrue (CF.mkTrueFlow ()) no_pos) ispec spec in
  let () = y_tinfo_hp (add_str "merged spec" pr) spec in
  let spec = flatten_case_struc spec in
  let spec = CF.flatten_struc_formula spec in
  let () = y_tinfo_hp (add_str "flatten spec" pr) spec in
  let spec = norm_struc spec in
  let () = y_tinfo_hp (add_str "normed spec" pr) spec in
  spec

let tnt_spec_of_proc prog proc ispec =
  let pr1 = print_tnt_case_spec in
  let pr2 = string_of_struc_formula_for_spec in
  Debug.no_2 "tnt_spec_of_proc"
    (add_str "proc_spec" (fun proc -> pr2 (proc.Cast.proc_stk_of_static_specs # top))) 
    (add_str "ispec" pr1) pr2 
    (fun _ _ -> tnt_spec_of_proc prog proc ispec) proc ispec

let print_svcomp2015_result term_anns =
  let unknown_ans = "UNKNOWN" in
  let yes_ans = "TRUE" in
  let no_ans cex = "FALSE" ^ "\nCounterexample: " ^ cex in
  (* print_endline ("term_anns" ^ (pr_list string_of_term_ann term_anns)); *)
  (* no termination info --> UNKNOWN *)
  if (List.length term_anns = 0) then
    (* print_endline "UNKNOWN 1" *)
    unknown_ans
    (* all cases terminates --> TRUE *)
  else if (List.for_all Cpure.is_Term term_anns) then yes_ans
  (* all cases are Loop --> FALSE *)
  else if (List.exists Cpure.is_Loop term_anns) then
    let cex = Cpure.cex_of_term_ann_list term_anns in
    let cex_str = Cprinter.string_of_term_cex cex in
    no_ans cex_str
    (* some cases are MayLoop --> FALSE when having counterexamples, otherwise UNKNOWN *)
  else if (List.exists Cpure.is_MayLoop term_anns) then
    let cex = Cpure.cex_of_term_ann_list term_anns in
    match cex with
    | None -> unknown_ans
    | Some e when (e.Cpure.tcex_trace = []) -> unknown_ans
    | _ -> no_ans (Cprinter.string_of_term_cex cex)
    (* the rests are UNKNOWN *)
  else
    (* print_endline "UNKNOWN 2" *)
    unknown_ans

let print_svcomp2015_result term_anns =
  Debug.no_1 "print_svcomp2015_result" 
    (add_str "result" (fun lst -> string_of_int (List.length lst)))
    idf print_svcomp2015_result term_anns

let pr_proc_case_specs prog =
  Hashtbl.iter (fun mn ispec ->
      try
        let proc = Cast.look_up_proc_def_no_mingling no_pos prog.Cast.new_proc_decls mn in
        let nspec = tnt_spec_of_proc prog proc ispec in
        let svcomp_res = 
          let term_anns = Cformula.collect_term_ann_for_svcomp_competion nspec in
          print_svcomp2015_result term_anns
        in
        let () = print_web_mode ("Procedure " ^ mn ^ ": " ^ svcomp_res) in
        let () = print_web_mode (string_of_struc_formula_for_spec nspec) in
        (* print result for svcomp 2015 *)
        if !Globals.svcomp_compete_mode &&
           not !Globals.tnt_web_mode &&
           (eq_str (Cast.unmingle_name mn) "main") then (
          print_endline svcomp_res
        );
        (* Proc Decl is not found - SLEEK *)
      with _ -> (
          print_web_mode ("Procedure " ^ mn ^ ":\n" ^ (print_tnt_case_spec ispec));
          (* if !Globals.svcomp_compete_mode && (eq_str mn "main") then ( *)
          (*   let term_anns = collect_term_ann_in_tnt_case_spec ispec in *)
          (*   print_svcomp2015_result term_anns                          *)
          (* );                                                           *)
        )
    ) proc_case_specs

let pr_im_case_specs iter_num =
  if !Globals.tnt_verbosity == 0 then begin
    print_endline_quiet ("TNT @ ITER " ^ (string_of_int iter_num));
    Hashtbl.iter (fun mn ispec -> 
        print_endline_quiet (mn ^ ": " ^ (print_tnt_case_spec ispec))) proc_case_specs end
  else ()

let update_spec_proc prog proc =
  let mn = Cast.unmingle_name (proc.Cast.proc_name) in
  try
    let ispec = Hashtbl.find proc_case_specs mn in
    let nspec = tnt_spec_of_proc prog proc ispec in
    let () = proc.Cast.proc_stk_of_static_specs # push_pr x_loc nspec in 
    (* let proc = { proc with Cast.proc_static_specs = nspec; }  in *)
    (* let () = Cprinter.string_of_proc_decl_no_body nproc in *)
    proc
  with _ -> proc

let update_specs_prog prog = 
  let n_tbl = Cast.proc_decls_map (fun proc ->
      update_spec_proc prog proc) prog.Cast.new_proc_decls in
  (* Should not create a new prog object *)
  (* { prog with Cast.new_proc_decls = n_tbl } *)
  ()
  

(* TNT Graph *)
module TNTElem = struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module TNTEdge = struct
  type t = call_trel
  let compare = compare_trel
  let hash = Hashtbl.hash
  let equal = eq_trel
  let default = dummy_trel
end

module TG = Graph.Persistent.Digraph.ConcreteLabeled(TNTElem)(TNTEdge)    
module TGC = Graph.Components.Make(TG)

(* Exceptions to guide the main algorithm *)
exception Restart_with_Cond of (CP.formula list * TG.t)
exception Should_Finalize

let graph_of_trels trels =
  let tg = TG.empty in
  let tg = List.fold_left (fun g rel ->
      let src = CP.id_of_term_ann rel.termu_lhs in
      let dst = CP.id_of_term_ann rel.termu_rhs in
      let lbl = rel in
      TG.add_edge_e g (TG.E.create src lbl dst)) tg trels
  in tg

let print_graph_by_num g = 
  TG.fold_edges (fun s d a -> 
      (string_of_int s) ^ " -> " ^
      (string_of_int d) ^ "\n" ^ a)  g ""

let print_edge e = 
  let _, rel, _ = e in
  print_call_trel_debug rel

(* let print_graph_by_rel g =                             *)
(*   TG.fold_edges (fun s d a ->                          *)
(*     (print_edge (TG.find_edge g s d)) ^ "\n" ^ a) g "" *)

let print_graph_by_rel g = 
  TG.fold_edges_e (fun e a -> (print_edge e) ^ "\n" ^ a) g ""

let print_scc_num = pr_list string_of_int

let print_scc_list_num scc_list = 
  "scc size = " ^ (string_of_int (List.length scc_list)) ^ "\n" ^ 
  (pr_list (fun scc -> (print_scc_num scc) ^ "\n") scc_list)

let print_scc_array_num scc_array =
  print_scc_list_num (Array.to_list scc_array) 

(* A scc is acyclic iff it has only one node and *)
(* this node is not a successor of itself *) 
let is_acyclic_scc g scc =
  match scc with
  | v::[] -> 
    let succ = TG.succ g v in
    not (Gen.BList.mem_eq (==) v succ)
  | _ -> false

(* Returns a set of successors of a node *)
let succ_vertex g v =
  let succ = TG.succ g v in
  List.map (fun sc ->
      let _, rel, _ = TG.find_edge g v sc in
      rel.termu_rhs) succ 

(* Returns a set of successors of a scc *)  
let succ_scc g scc =
  List.concat (List.map (succ_vertex g) scc)

let succ_scc_num g scc =
  List.concat (List.map (TG.succ g) scc)

let outside_edges_scc_vertex g scc v =
  let succ = TG.succ g v in
  let outside_scc_succ = Gen.BList.difference_eq (==) succ scc in
  List.concat (List.map (fun sc -> TG.find_all_edges g v sc) outside_scc_succ)

let outside_scc_succ_vertex g scc v =
  let succ = TG.succ g v in
  let outside_scc_succ = Gen.BList.difference_eq (==) succ scc in
  List.map (fun sc ->
      let _, rel, _ = TG.find_edge g v sc in
      (sc, rel.termu_rhs)) outside_scc_succ
(* List.concat (List.map (fun sc ->                                       *)
(*   let edges = TG.find_all_edges g v sc in                              *)
(*   List.map (fun (_, rel, _) -> rel.termu_rhs) edges) outside_scc_succ) *)

let outside_succ_scc g scc =
  List.concat (List.map (outside_scc_succ_vertex g scc) scc)

let outside_succ_scc_num g scc =
  let succ_scc_num = succ_scc_num g scc in
  Gen.BList.difference_eq (==) succ_scc_num scc

let no_outgoing_edge_scc g scc =
  (outside_succ_scc_num g scc) = []   

(* Methods to update rels in graph *)
let update_trel f_ann rel =
  update_call_trel rel (f_ann rel.termu_lhs) (f_ann rel.termu_rhs)

let edges_of_scc_vertex g scc s =
  let succ = TG.succ g s in
  (* Remove destinations which are outside scc *)
  let succ_scc = List.filter (fun d -> List.mem d scc) succ in
  List.concat (List.map (fun d -> TG.find_all_edges g s d) succ_scc)

let edges_of_scc g scc =   
  let outgoing_scc_edges =
    List.concat (List.map (fun s ->
        let succ = TG.succ g s in
        List.concat (List.map (fun d ->
            TG.find_all_edges g s d) succ)) scc)
  in
  let incoming_scc_edges = 
    List.concat (List.map (fun d ->
        let pred = TG.pred g d in
        List.fold_left (fun a s ->
            if Gen.BList.mem_eq (==) s scc (* Excluding duplicate edges *)
            then a else a @ (TG.find_all_edges g s d)
          ) [] pred) scc)
  in (outgoing_scc_edges @ incoming_scc_edges)

let map_scc g scc f_edge = 
  let scc_edges = edges_of_scc g scc in
  List.fold_left (fun g e -> f_edge g e) g scc_edges

let update_edge g f_rel e =
  let s, rel, d = e in
  let nrel = f_rel rel in
  TG.add_edge_e (TG.remove_edge_e g e) (s, nrel, d)  

let map_ann_scc g scc f_ann = 
  let f_edge g e = update_edge g (update_trel f_ann) e in 
  map_scc g scc f_edge

(* This method returns all edges within a scc *)    
let find_scc_edges g scc = 
  let find_edges_vertex s =
    let succ = TG.succ g s in
    let scc_succ = Gen.BList.intersect_eq (==) succ scc in
    let scc_succ = Gen.BList.remove_dups_eq (==) scc_succ in
    List.concat (List.map (fun d -> TG.find_all_edges g s d) scc_succ)
  in List.concat (List.map (fun v -> find_edges_vertex v) scc)

let find_scc_edges g scc = 
  let pr1 = print_graph_by_rel in
  let pr2 = pr_list string_of_int in
  let pr3 = pr_list (fun e -> (print_edge e) ^ "\n") in
  Debug.no_2 "find_scc_edges" pr1 pr2 pr3
    find_scc_edges g scc

let get_term_ann_vertex g v =
  let edges_from_v = TG.succ_e g v in
  match edges_from_v with
  | [] ->
    let edges_to_v = TG.pred_e g v in
    begin match edges_to_v with
      | [] -> None
      | (_, rel, _)::_ -> Some (rel.termu_rhs)
    end
  | (_, rel, _)::_ -> Some (rel.termu_lhs) 

let is_unknown_vertex g v =
  let ann_of_v = get_term_ann_vertex g v in
  match ann_of_v with
  | None -> false
  | Some ann -> CP.is_unknown_term_ann ann

let is_unknown_scc g scc =
  List.exists (fun v -> is_unknown_vertex g v) scc

let partition_scc_list tg scc_list = 
  List.fold_left (fun scc_groups scc ->
      let scc_succ = succ_scc_num tg scc in
      if is_empty scc_succ then scc_groups @ [[scc]]
      else
        let scc_groups, other_groups = List.partition (fun scc_group ->
            List.exists (fun scc -> 
                List.exists (fun v -> 
                    List.mem v scc_succ) scc) scc_group) scc_groups in
        ((List.concat scc_groups) @ [scc])::other_groups) [] scc_list 

let partition_scc_list tg scc_list = 
  let pr = print_scc_list_num in
  Debug.no_1 "partition_scc_list" pr (pr_list pr)
    (fun _ -> partition_scc_list tg scc_list) scc_list

(* Only keep vertices in scc_list *)        
let sub_graph_of_scc_list tg scc_list =
  let scc_vertex = List.concat scc_list in
  TG.fold_vertex (fun v ntg -> 
      if (List.mem v scc_vertex) then ntg
      else TG.remove_vertex ntg v) tg tg

(* End of TNT Graph *)

(* Template Utilies *)
let wrap_oc_tl f arg =
  let oc = !Tlutils.oc_solver in (* Using oc to get optimal solution *)
  let () = Tlutils.oc_solver := true in
  let res = f arg in
  let () = Tlutils.oc_solver := oc in
  res

let templ_of_term_ann for_lex ann =
  match ann with
  | CP.TermR uid 
  | CP.TermU uid ->
    let templ_args = List.filter (fun e -> not (CP.exp_is_boolean_var e)) uid.CP.tu_args in
    let templ_id = "t_" ^ uid.CP.tu_fname ^ 
                   (if not for_lex then ("_" ^ (string_of_int uid.CP.tu_id)) else "") in 
    let templ_exp = CP.mkTemplate templ_id templ_args no_pos in
    CP.Template templ_exp, [templ_exp.CP.templ_id], 
    templ_args, Some (Tlutils.templ_decl_of_templ_exp templ_exp)
  | _ -> CP.mkIConst (-1) no_pos, [], [], None

let add_templ_assume ctx constr inf_templs =
  let es = CF.empty_es (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let es = { es with CF.es_infer_vars_templ = inf_templs } in
  Template.collect_templ_assume_init es ctx constr no_pos

let solve_templ_assume prog templ_decls inf_templs =
  (* let prog = { prog with                                                                            *)
  (*     Cast.prog_templ_decls =                                                                       *)
  (*       Gen.BList.remove_dups_eq Cast.eq_templ_decl (prog.Cast.prog_templ_decls @ templ_decls) } in *)
  let () = prog.Cast.prog_templ_decls <- 
      Gen.BList.remove_dups_eq Cast.eq_templ_decl (prog.Cast.prog_templ_decls @ templ_decls) in
  let res, _, _ = Template.collect_and_solve_templ_assumes_common true prog 
      (List.map CP.name_of_spec_var inf_templs) in
  res

let solve_templ_assume prog templ_decls inf_templs =
  Debug.no_1 "solve_templ_assume" !CP.print_svl Tlutils.print_solver_res
    (fun _ -> solve_templ_assume prog templ_decls inf_templs) inf_templs

(* Ranking function synthesis *)
let templ_rank_constr_of_rel for_lex rel =
  let src_rank, src_templ_id, _, src_templ_decl = templ_of_term_ann for_lex rel.termu_lhs in
  let dst_rank, dst_templ_id, _, dst_templ_decl = templ_of_term_ann for_lex rel.termu_rhs in
  let inf_templs = src_templ_id @ dst_templ_id in

  (* let ctx = mkAnd rel.call_ctx (CP.cond_of_term_ann rel.termu_lhs) in                           *)
  (* (* let ctx = if not for_lex then mkAnd ctx (CP.cond_of_term_ann rel.termu_rhs) else ctx in *) *)
  (* let dec = mkGt src_rank dst_rank in                                                           *)
  (* let bnd = mkGte src_rank (CP.mkIConst 0 no_pos) in                                            *)
  (* let constr = mkAnd dec bnd in                                                                 *)
  (* let todo_unk = add_templ_assume (MCP.mix_of_pure ctx) constr inf_templs in                    *)
  (* let () = print_endline_quiet ("Rank synthesis: vars: " ^ (!CP.print_svl inf_templs)) in       *)
  (* let () = print_endline_quiet ("Rank synthesis: ctx: " ^ (!CP.print_formula ctx)) in           *)
  (* let () = print_endline_quiet ("Rank synthesis: constr: " ^ (!CP.print_formula constr)) in     *)

  let ctx_bnd = mkAnd rel.call_ctx (CP.cond_of_term_ann rel.termu_lhs) in
  let bnd = mkGte src_rank (CP.mkIConst 0 no_pos) in
  let todo_unk = add_templ_assume (MCP.mix_of_pure ctx_bnd) bnd src_templ_id in
  let ctx_dec = if not for_lex then mkAnd ctx_bnd (CP.cond_of_term_ann rel.termu_rhs) else ctx_bnd in
  let dec = mkGt src_rank dst_rank in
  let todo_unk = add_templ_assume (MCP.mix_of_pure ctx_dec) dec inf_templs in
  (* let () = print_endline_quiet ("Rank synthesis: vars: " ^ (!CP.print_svl inf_templs)) in     *)
  (* let () = print_endline_quiet ("Rank synthesis: ctx_bnd: " ^ (!CP.print_formula ctx_bnd)) in *)
  (* let () = print_endline_quiet ("Rank synthesis: bnd: " ^ (!CP.print_formula bnd)) in         *)
  (* let () = print_endline_quiet ("Rank synthesis: ctx_dec: " ^ (!CP.print_formula ctx_dec)) in *)
  (* let () = print_endline_quiet ("Rank synthesis: dec: " ^ (!CP.print_formula dec)) in         *)

  inf_templs, (opt_to_list src_templ_decl) @ (opt_to_list dst_templ_decl)

let templ_rank_constr_of_rel for_lex rel =
  Debug.no_1 "templ_rank_constr_of_rel" print_call_trel_debug (fun _ -> "")
    (fun _ -> templ_rank_constr_of_rel for_lex rel) rel

(* Use a unique ranking function template for all node in scc *)    
let infer_lex_ranking_function_scc prog g scc_edges =
  let for_lex = true in (* by_fname *)
  let inf_templs, templ_decls = List.fold_left (fun (id_a, decl_a) (_, rel, _) -> 
      let id, decl = templ_rank_constr_of_rel for_lex rel in
      (id_a @ id, decl_a @ decl)) ([], []) scc_edges in
  let inf_templs = Gen.BList.remove_dups_eq CP.eq_spec_var inf_templs in 
  let inf_templs = List.map CP.name_of_spec_var inf_templs in

  (* let prog = { prog with                                                                          *)
  (*     Cast.prog_templ_decls =                                                                     *)
  (*       Gen.BList.remove_dups_eq Cast.eq_templ_decl (prog.Cast.prog_templ_decls @ templ_decls) }  *)
  (* in                                                                                              *)
  let () = prog.Cast.prog_templ_decls <-
        Gen.BList.remove_dups_eq Cast.eq_templ_decl (prog.Cast.prog_templ_decls @ templ_decls) in
  let res, templ_assumes, templ_unks = 
    Template.collect_and_solve_templ_assumes_common true prog inf_templs in
  match res with
  | Sat model ->
    let sst = List.map (fun (v, i) -> (CP.SpecVar (Int, v, Unprimed), i)) model in
    let rank_of_ann = fun ann ->
      let rank_templ, _, _, _ = templ_of_term_ann for_lex ann in
      let rank_exp = Tlutils.subst_model_to_exp true sst (CP.exp_of_template_exp rank_templ) in
      [rank_exp]
    in Some rank_of_ann
  | Unsat -> 
    let res = wrap_oc_tl (Terminf.infer_lex_template_res prog inf_templs templ_unks) templ_assumes in
    if is_empty res then None
    else 
      let res = Gen.BList.remove_dups_eq CP.eqExp res in
      (* let () = print_endline (pr_list !CP.print_exp res) in *)
      let rank_of_ann = fun ann ->
        let _, _, _, templ_decl = templ_of_term_ann for_lex ann in
        match templ_decl with
        | None -> []
        | Some tdecl -> 
          let params = tdecl.Cast.templ_params in
          let sst = List.combine params (CP.args_of_term_ann ann) in
          List.map (fun e -> CP.a_apply_par_term sst e) res
      in Some rank_of_ann
  | _ -> None

let infer_ranking_function_scc prog g scc =
  let scc_edges = find_scc_edges g scc in
  (* let () = print_endline (print_graph_by_rel g) in                               *)
  (* let () = print_endline (pr_list (fun e -> (print_edge e) ^ "\n") scc_edges) in *)
  let for_lex = false in
  let inf_templs, templ_decls = List.fold_left (fun (id_a, decl_a) (_, rel, _) -> 
      let id, decl = templ_rank_constr_of_rel for_lex rel in
      (id_a @ id, decl_a @ decl)) ([], []) scc_edges in
  let inf_templs = Gen.BList.remove_dups_eq CP.eq_spec_var inf_templs in
  let res = solve_templ_assume prog templ_decls inf_templs in
  (* let () = print_endline ("Rank synthesis: result: " ^ ( Tlutils.print_solver_res res) ^ "\n") in *)
  match res with
  | Sat model ->
    let sst = List.map (fun (v, i) -> (CP.SpecVar (Int, v, Unprimed), i)) model in
    let should_simplify = (List.length scc_edges <= 1) in
    let rank_of_ann = fun ann ->
      let rank_templ, _, _, _ = templ_of_term_ann for_lex ann in
      let rank_exp = Tlutils.subst_model_to_exp should_simplify
          sst (CP.exp_of_template_exp rank_templ) in
      [rank_exp]
    in Some rank_of_ann
  | _ ->
    (* Lexico inference is only for scc with the same function *) 
    let fname_scc = List.concat (List.map (fun (_, rel, _) ->
        [CP.fn_of_term_ann rel.termu_lhs; CP.fn_of_term_ann rel.termu_rhs]) scc_edges) in
    let fname_scc = Gen.BList.remove_dups_eq (fun fn1 fn2 -> String.compare fn1 fn2 == 0) fname_scc in
    (* TODO: Removing duplicate contexts might return a better result *)
    if !Globals.tnt_infer_lex && (List.length fname_scc == 1) && (List.length scc_edges > 1) then
      infer_lex_ranking_function_scc prog g scc_edges
    else None

(* f is a single formula *)
(* ctx -/-> f            *)
let subst_by_ctx vars ctx f = 
  let simpl_f = x_add simplify (mkAnd ctx f) vars in
  Tpdispatcher.om_gist simpl_f (x_add simplify ctx vars)
  (* try                                                                          *)
  (*   List.find (fun c -> x_add imply (mkAnd ctx c) f) (CP.split_conjunctions simpl_f) *)
  (* with _ -> simpl_f                                                            *)

(* Abductive Inference *)
let infer_abductive_cond_subtract_single args subtrahend_terms_lst ante cons =
  let triv_cons = subst_by_ctx args ante cons in
  let count_overlapping_terms ante_terms cons_terms =
    let overlapping_terms = List.find_all (
      fun ta -> List.exists (fun tc -> 
        (eq_linear_term_var ta.linear_term_var tc.linear_term_var) && 
        (ta.linear_term_coe * tc.linear_term_coe > 0)) 
        cons_terms) 
      ante_terms in 
    List.length overlapping_terms 
  in 
  let compare_overlapping_terms c a1 a2 = 
    (count_overlapping_terms a1 c) - (count_overlapping_terms a2 c) 
  in
  try 
    (* Search for a suitable subtrahend *)
    let cons_terms = List.map linear_term_of_term (term_list_of_formula (CP.fv triv_cons) triv_cons) in
    let subtrahend_terms = List.hd (List.rev (List.sort (compare_overlapping_terms cons_terms) subtrahend_terms_lst)) in
    let abd_terms = subt_linear_terms cons_terms subtrahend_terms in
    let abd_cond = CP.mkPure (CP.mkLte (exp_of_linear_term_list abd_terms no_pos) (CP.mkIConst 0 no_pos) no_pos) in
    [abd_cond]
  with _ -> [triv_cons]

let infer_abductive_cond_subtract args subtrahend_cond prog ann abd_ante abd_conseq =
  try
    let subtrahend_conds = CP.split_conjunctions subtrahend_cond in
    let subtrahend_terms_lst = List.map 
        (fun t -> List.map linear_term_of_term (term_list_of_formula (CP.fv t) t)) 
        subtrahend_conds 
    in
    
    let cons_conds = CP.split_conjunctions abd_conseq in
    let abd_conds = List.map (fun cons -> 
        infer_abductive_cond_subtract_single args subtrahend_terms_lst abd_ante cons) cons_conds 
    in
    Some (CP.join_conjunctions (List.concat abd_conds))
  with _ -> None

let infer_abductive_cond_templ prog ann abd_ante abd_conseq = 
  let abd_templ, abd_templ_id, abd_templ_args, abd_templ_decl = templ_of_term_ann true ann in
  let abd_cond = mkGte abd_templ (CP.mkIConst 0 no_pos) in
  let abd_ctx = mkAnd abd_ante abd_cond in
  
  (* let () = print_endline ("ABD LHS: " ^ (!CP.print_formula abd_ctx)) in    *)
  (* let () = print_endline ("ABD RHS: " ^ (!CP.print_formula abd_conseq)) in *)
  let todo_unk = add_templ_assume (MCP.mix_of_pure abd_ctx) abd_conseq abd_templ_id in
  
  (* let oc = !Tlutils.oc_solver in (* Using oc to get optimal solution *)          *)
  (* let () = Tlutils.oc_solver := true in                                          *)
  (* let res = solve_templ_assume prog (opt_to_list abd_templ_decl) abd_templ_id in *)
  (* let () = Tlutils.oc_solver := oc in                                            *)
  let res = wrap_oc_tl (solve_templ_assume prog (opt_to_list abd_templ_decl)) abd_templ_id in
  
  match res with
  | Sat model ->
    let sst = List.map (fun (v, i) -> (CP.SpecVar (Int, v, Unprimed), i)) model in
    let abd_exp = Tlutils.subst_model_to_exp true sst (CP.exp_of_template_exp abd_templ) in
    let icond = mkGte abd_exp (CP.mkIConst 0 no_pos) in
    let icond = om_simplify icond in
    (* let () = print_endline ("Abductive synthesis: result: " ^ (Tlutils.print_solver_res res)) in  *)
    (* let () = print_endline ("Abductive synthesis: icond: " ^ (!CP.print_formula icond) ^ "\n") in *)
  
    if is_sat (mkAnd abd_ante icond)
    then Some icond
    else
      (* Return trivial abductive condition *)
      let args = List.concat (List.map CP.afv abd_templ_args) in
      Some (x_add simplify (mkAnd abd_ante abd_conseq) args)
    (* let excl_args = CP.fv icond in                                                             *)
    (* let incl_args = diff args excl_args in                                                     *)
    (* let () = print_endline ("Abductive synthesis: args: " ^ (!CP.print_svl args)) in           *)
    (* let () = print_endline ("Abductive synthesis: excl_args: " ^ (!CP.print_svl excl_args)) in *)
    (* let () = print_endline ("Abductive synthesis: incl_args: " ^ (!CP.print_svl incl_args)) in *)
    (* let args = if is_empty incl_args then args else incl_args in                               *)
    (* let neg_icond = simplify 1 (mkAnd abd_ante (mkNot abd_conseq)) args in                     *)
    (* Some (mkNot neg_icond)                                                                     *)
  | _ -> None

let infer_abductive_cond abd_f prog ann ante conseq =
  if x_add imply ante conseq then Some (CP.mkTrue no_pos) (* None *)
  else
    (* Handle boolean formulas in consequent *)
    let bool_conseq, conseq = List.partition CP.is_bool_formula 
        (CP.split_conjunctions conseq) in
    if not (x_add imply ante (CP.join_conjunctions bool_conseq)) then None
    else
      let abd_ante = CP.join_conjunctions (List.filter (fun f -> 
          not (CP.is_bool_formula f)) (CP.split_conjunctions ante)) in
      let abd_conseq = CP.join_conjunctions conseq in
      abd_f prog ann abd_ante abd_conseq

let infer_abductive_cond abd_f prog ann ante conseq =
  let pr = !CP.print_formula in
  Debug.no_2 "infer_abductive_cond" pr pr (pr_option pr) 
    (fun _ _ -> infer_abductive_cond abd_f prog ann ante conseq) ante conseq

let infer_abductive_icond_edge prog g e =
  let _, rel, _ = e in
  match rel.termu_lhs with
  | TermU uid ->
    let tuc = uid.CP.tu_cond in
    let eh_ctx = mkAnd rel.call_ctx tuc in

    let tuic = uid.CP.tu_icond in
    (* let params = List.concat (List.map CP.afv uid.CP.tu_args) in *)
    let params = params_of_term_ann prog rel.termu_rhs in
    let args = CP.args_of_term_ann rel.termu_rhs in
    let abd_conseq = CP.subst_term_avoid_capture (List.combine params args) tuic in
    let ires = infer_abductive_cond infer_abductive_cond_templ prog rel.termu_lhs eh_ctx abd_conseq in
    begin match ires with
      | None -> None
      | Some ic -> Some (uid, ic) 
    end

    (* let bool_abd_conseq, abd_conseq = List.partition CP.is_bool_formula                      *)
    (*   (CP.split_conjunctions abd_conseq) in                                                  *)
  
    (* if not (x_add imply eh_ctx (CP.join_conjunctions bool_abd_conseq)) then None             *)
    (* else                                                                                     *)
    (*   let abd_conseq = CP.join_conjunctions abd_conseq in                                    *)
    (*   let abd_templ, abd_templ_id, _, abd_templ_decl = templ_of_term_ann rel.termu_lhs in    *)
    (*   let abd_cond = mkGte abd_templ (CP.mkIConst 0 no_pos) in                               *)
    (*   let abd_ctx = mkAnd eh_ctx abd_cond in                                                 *)
  
    (*   (* let () = print_endline ("ABD LHS: " ^ (!CP.print_formula abd_ctx)) in    *)         *)
    (*   (* let () = print_endline ("ABD RHS: " ^ (!CP.print_formula abd_conseq)) in *)         *)
  
    (*   if x_add imply eh_ctx abd_conseq then                                                  *)
    (*     let icond = CP.mkTrue no_pos in (* The node has an edge looping on itself *)         *)
    (*     Some (uid, icond)                                                                    *)
    (*   else                                                                                   *)
    (*     let todo_unk = add_templ_assume (MCP.mix_of_pure abd_ctx) abd_conseq abd_templ_id in *)
    (*     let oc = !Tlutils.oc_solver in (* Using oc to get optimal solution *)                *)
    (*     let () = Tlutils.oc_solver := true in                                                *)
    (*     let res = solve_templ_assume prog abd_templ_decl abd_templ_id in                     *)
    (*     let () = Tlutils.oc_solver := oc in                                                  *)
  
    (*     begin match res with                                                                 *)
    (*     | Sat model ->                                                                       *)
    (*       let sst = List.map (fun (v, i) -> (CP.SpecVar (Int, v, Unprimed), i)) model in     *)
    (*       let abd_exp = Tlutils.subst_model_to_exp sst (CP.exp_of_template_exp abd_templ) in *)
    (*       let icond = mkGte abd_exp (CP.mkIConst 0 no_pos) in                                *)
  
    (*       (* let () = print_endline ("ABD: " ^ (!CP.print_formula icond)) in *)              *)
  
    (*       (* Update TNT case spec with new abductive case *)                                 *)
    (*       (* if the abductive condition is feasible       *)                                 *)
    (*       if is_sat (mkAnd abd_ctx icond) then                                               *)
    (*         (* let () = update_case_spec_with_icond_proc uid.CP.tu_fname tuc icond in *)     *)
    (*         Some (uid, icond)                                                                *)
    (*       else None                                                                          *)
    (*     | _ -> None end                                                                      *)
  | _ -> None 

let infer_abductive_icond_vertex prog g v = 
  let self_loop_edges = TG.find_all_edges g v v in
  let abd_conds = List.fold_left (
    fun a e -> a @ opt_to_list (infer_abductive_icond_edge prog g e)) [] self_loop_edges in
  match abd_conds with
  | [] -> []
  | (uid, _)::_ -> 
    let icond_lst = List.map snd abd_conds in
    let full_disj_icond_lst = get_full_disjoint_cond_list true icond_lst in
    (* let () = print_endline ("full_disj_icond_lst: " ^      *)
    (*   (pr_list !CP.print_formula full_disj_icond_lst)) in *)
    let () = update_case_spec_with_icond_list_proc 
        uid.CP.tu_fname uid.CP.tu_cond full_disj_icond_lst
    in [(uid.CP.tu_id, full_disj_icond_lst)]

let infer_abductive_icond prog g scc =
  List.concat (List.map (fun v -> infer_abductive_icond_vertex prog g v) scc)

(* Update rels in graph with abductive conditions *)
let inst_lhs_trel_abd rel abd_conds =  
  let lhs_ann = rel.termu_lhs in
  let inst_lhs = match lhs_ann with
    | CP.TermU uid -> 
      begin try
          let tid = uid.CP.tu_id in
          let iconds = List.assoc tid abd_conds in
          let iconds_w_id = assign_id_to_list iconds in  

          let tuc = uid.CP.tu_cond in
          let eh_ctx = mkAnd rel.call_ctx tuc in
          List.concat (List.map (fun (i, c) -> 
              if (is_sat (mkAnd eh_ctx c)) then
                [ CP.TermU { uid with
                             CP.tu_id = cantor_pair tid i;
                             CP.tu_cond = mkAnd tuc c;
                             CP.tu_icond = c; }]
              else []) iconds_w_id)
        with Not_found -> [lhs_ann] end
    | _ -> [lhs_ann]
  in inst_lhs

let inst_lhs_trel_abd rel abd_conds =
  let pr1 = print_call_trel_debug in
  let pr2 = pr_list (pr_pair string_of_int (pr_list !CP.print_formula)) in
  let pr3 = pr_list string_of_term_ann in
  Debug.no_2 "inst_lhs_trel_abd" pr1 pr2 pr3
    inst_lhs_trel_abd rel abd_conds

let inst_rhs_trel_abd inst_lhs rel abd_conds = 
  let rhs_ann = rel.termu_rhs in
  let cond_lhs = CP.cond_of_term_ann inst_lhs in
  let ctx = mkAnd rel.call_ctx cond_lhs in
  let inst_rhs = match rhs_ann with
    | CP.TermU uid ->
      let tid = uid.CP.tu_id in
      let tuc = uid.CP.tu_cond in
      let eh_ctx = mkAnd ctx tuc in
      if not (is_sat eh_ctx) then []
      else
        begin try
            let iconds = List.assoc tid abd_conds in
            let params = rel.termu_rhs_params in
            let args = uid.CP.tu_args in
            let sst = List.combine params args in
            let iconds = List.map (CP.subst_term_avoid_capture sst) iconds in
            let iconds_w_id = assign_id_to_list iconds in 
            List.concat (List.map (fun (i, c) -> 
                if (is_sat (mkAnd eh_ctx c)) then
                  [ CP.TermU { uid with
                               CP.tu_id = cantor_pair tid i;
                               CP.tu_cond = mkAnd tuc c;
                               CP.tu_icond = c; }]
                else []) iconds_w_id)
          with Not_found -> [rhs_ann] end
    | _ -> [rhs_ann]
  in List.map (fun irhs -> update_call_trel rel inst_lhs irhs) inst_rhs

let inst_call_trel_abd rel abd_conds =
  let inst_lhs = inst_lhs_trel_abd rel abd_conds in
  let inst_rels = List.concat (List.map (fun ilhs -> 
      inst_rhs_trel_abd ilhs rel abd_conds) inst_lhs) in
  inst_rels

let update_graph_with_icond g scc abd_conds =
  let f_e g e =
    let _, rel, _ = e in
    let inst_rels = inst_call_trel_abd rel abd_conds in
    List.fold_left (fun g rel -> 
        let s = CP.id_of_term_ann rel.termu_lhs in
        let d = CP.id_of_term_ann rel.termu_rhs in
        TG.add_edge_e g (s, rel, d)) g inst_rels
  in  
  let scc_edges = edges_of_scc g scc in
  let g = List.fold_left (fun g v -> TG.remove_vertex g v) g scc in
  List.fold_left (fun g e -> f_e g e) g scc_edges

(* Only update nodes in scc *)  
let update_ann scc f ann = 
  let ann_id = CP.id_of_term_ann ann in
  if Gen.BList.mem_eq (==) ann_id scc 
  then f ann
  else ann

let subst sol ann =
  let fn = CP.fn_of_term_ann ann in
  let cond = CP.cond_of_term_ann ann in
  (* Add call number into the result *)
  let call_num = CP.call_num_of_term_ann ann in
  let sol = match (fst sol) with
    | CP.Term -> (fst sol, (CP.mkIConst call_num no_pos)::(snd sol))
    | _ -> sol 
  in
  (* Update TNT case spec with solution *)
  let () = add_sol_case_spec_proc fn cond sol in
  (* let () = print_endline ("Case spec @ scc " ^ (print_scc_num scc)) in *)
  (* let () = pr_proc_case_specs () in                                    *)  
  subst_sol_term_ann sol ann

(* Proving non-termination or infering abductive condition           *)
(* for case analysis from an interesting condition                   *)
(* For each return assumption, we will obtain three kinds of result: *)
(* - YES (A /\ true |- B)                                            *)
(* - Definite NO (A |- !B)                                           *)
(* - Possible NO with Abductive Condition (Otherwise: A /\ C |- B)   *)
type nt_res = 
  | NT_Yes
  | NT_Partial_Yes (* For mutual recursion *)
  | NT_No of (CP.formula list)
  | NT_Nondet_May of CP.tcex_cmd list (* For nondet non-termination *)

type nt_cond = {
  ntc_fn: string;
  ntc_id: int;
  ntc_cond: CP.formula;
}

let print_nt_res = function
  | NT_Yes -> "NT_Yes"
  | NT_Partial_Yes -> "NT_Partial_Yes"
  | NT_No ic -> "NT_No[" ^ (pr_list !CP.print_formula ic) ^ "]" 
  | NT_Nondet_May tcex -> "NT_Nondet_May[" ^ (pr_list Cprinter.string_of_tcex_cmd tcex) ^ "]"

let is_nt_yes = function
  | NT_Yes -> true
  | _ -> false

let is_nt_no = function
  | NT_No _ -> true
  | _ -> false

let is_nt_partial_yes = function
  | NT_Partial_Yes -> true
  | _ -> false

let is_nt_nondet_may = function
  | NT_Nondet_May _ -> true
  | _ -> false

let cond_of_nt_res = function
  | NT_No ic -> ic
  | _ -> []

let uid_of_loop trel = 
  match trel.termu_rhs with
  | TermU uid -> uid
  | Loop _ ->
    let args = trel.termu_rhs_args in
    let params = List.concat (List.map CP.afv args) in
    let cond = x_add simplify trel.call_ctx params in
    { CP.tu_id = CP.loop_id;
      CP.tu_sid = "";
      CP.tu_fname = trel.termu_cle;
      CP.tu_call_num = 0;
      CP.tu_args = trel.termu_rhs_args;
      CP.tu_cond = cond; 
      CP.tu_icond = cond;
      CP.tu_sol = Some (CP.Loop None, []);
      CP.tu_pos = no_pos; }
  | _ -> report_error no_pos ("[TNT Inference]: Unexpected non-Loop constraint @ uid_of_loop.")


(* let infer_abductive_cond_disj prog rhs_uid ante cond_list =                     *)
(*   let cl =                                                                      *)
(*     if (List.length cond_list) <= 2 then cond_list                              *)
(*     else CP.split_disjunctions (pairwisecheck (CP.join_disjunctions cond_list)) *)
(*   in                                                                            *)
(*   List.fold_left (fun acc c ->                                                  *)
(*     let ic = infer_abductive_cond prog (CP.TermU rhs_uid) ante c in             *)
(*     match ic with                                                               *)
(*     | None -> acc                                                               *)
(*     | Some c -> acc @ [c]) [] cl                                                *)

let infer_abductive_contra abd_f prog rhs_uid ante cons =
  let cl = CP.split_conjunctions cons in
  let cl = List.filter (fun c -> not (x_add imply ante c)) cl in
  if is_empty cl then [CP.mkTrue no_pos]
  else
    List.fold_left (
      fun acc c ->
        let ic = infer_abductive_cond abd_f prog (CP.TermU rhs_uid) ante c in
        match ic with
        | None -> acc
        | Some c -> acc @ [c]) [] cl

let rec infer_abductive_cond_list abd_f prog rhs_uid ante conds =
  match conds with
  | [] -> []
  | cl::cs -> 
    let cl = List.filter (fun c -> not (x_add imply ante (mkNot c.ntc_cond))) cl in
    if is_empty cl then infer_abductive_cond_list abd_f prog rhs_uid ante cs
    else
      try
        let self_c = List.find (fun c -> c.ntc_id == rhs_uid.CP.tu_id) cl in
        (* let self_ic = infer_abductive_cond prog (CP.TermU rhs_uid) ante self_c.ntc_cond in *)
        let icl = infer_abductive_contra abd_f prog rhs_uid ante self_c.ntc_cond in
        (* let icl = icl @ (opt_to_list self_ic) in *)
        if not (is_empty icl) then icl
        else infer_abductive_cond_list abd_f prog rhs_uid ante cs
      with Not_found -> 
        let rec helper cl = 
          match cl with
          | [] -> infer_abductive_cond_list abd_f prog rhs_uid ante cs
          | c::cl -> 
            let icl = infer_abductive_contra abd_f prog rhs_uid ante c.ntc_cond in
            if not (is_empty icl) then icl
            else helper cl
        in helper cl

let infer_abductive_cond_list abd_f prog rhs_uid ante conds =
  let pr1 = !CP.print_formula in
  let pr2 = pr_list pr1 in
  let pr3 = pr_list pr2 in
  Debug.no_2 "infer_abductive_cond_list" pr1 pr3 pr2
    (fun _ _ -> infer_abductive_cond_list abd_f prog rhs_uid ante conds) 
    ante (List.map (fun cl -> List.map (fun c -> c.ntc_cond) cl) conds)

let infer_loop_cond_list params ante conds =
  (* print_endline ("TO-LOOP: " ^ (pr_list !CP.print_formula conds)) *)
  match conds with
  | [] -> None
  | _ -> Some (mkNot (x_add simplify ante params))

let search_nt_cond_ann lhs_uids ann =
  let fn = CP.fn_of_term_ann ann in
  let uids = List.find_all (fun uid -> eq_str uid.CP.tu_fname fn) lhs_uids in
  let uids = Gen.BList.remove_dups_eq CP.eq_uid uids in
  List.map (fun uid ->
      let params = List.concat (List.map CP.afv uid.CP.tu_args) in
      let cond = subst_cond_with_ann params ann uid.CP.tu_cond in
      { ntc_fn = fn;
        ntc_id = if CP.is_Loop_uid uid then CP.loop_id else uid.CP.tu_id;
        ntc_cond = cond; }) uids 

let search_rec_icond_ann lhs_uids ann =
  let fn = CP.fn_of_term_ann ann in
  let uids = List.find_all (fun uid -> eq_str uid.CP.tu_fname fn) lhs_uids in
  let uids = Gen.BList.remove_dups_eq CP.eq_uid uids in
  List.map (fun uid ->
      let params = List.concat (List.map CP.afv uid.CP.tu_args) in
      let cond = subst_cond_with_ann params ann uid.CP.tu_icond in
      { ntc_fn = fn;
        ntc_id = uid.CP.tu_id;
        ntc_cond = cond; }) uids

(* Remove all constraints added from case specs *)
(* For tinf/paper/ex-2.ss vs Velroyen_false-termination.c *)    
let elim_irrel_formula irrel_vars_lst f =
  let is_irrel_f irrel_vars_lst f =
    let fv = CP.fv f in
    List.exists (fun irrel_vars -> subset fv irrel_vars) irrel_vars_lst
  in
  let fs = CP.split_conjunctions f in
  let rel_fs = List.filter (fun f -> not (is_irrel_f irrel_vars_lst f)) fs in
  CP.join_conjunctions rel_fs

let elim_irrel_formula irrel_vars_lst f =
  let pr1 = pr_list !CP.print_svl in
  let pr2 = !CP.print_formula in
  Debug.no_2 "elim_irrel_formula" pr1 pr2 pr2 
    elim_irrel_formula irrel_vars_lst f

let proving_non_termination_one_trrel prog lhs_uids rhs_uid trrel =
  let fn = rhs_uid.CP.tu_fname in
  let cond = rhs_uid.CP.tu_cond in 
  let ctx = trrel.ret_ctx in
  (* For tinf/paper/ex-2.ss vs Velroyen_false-termination.c *) 
  (* let irrel_vars_lst = List.map (fun ann -> CP.fv_of_term_ann ann) trrel.termr_lhs in *)
  (* let ctx = elim_irrel_formula irrel_vars_lst ctx in                                  *)
  let eh_ctx = mkAnd ctx cond in
  if not (is_sat eh_ctx) then 
    NT_Yes (* Everything is satisfied by false *) 
    (* NT_No [] (* No result for infeasible context *) *)
  else if is_empty trrel.termr_lhs then NT_No [] (* For base case *)
  else 
    (* let nt_conds = List.fold_left (fun ann -> search_nt_cond_ann lhs_uids ann) trrel.termr_lhs in *)
    (* We eliminate all un-interesting LHS nodes, e.g., nodes outside scc *)
    let nt_conds = List.fold_left (fun acc ann ->
        acc @ (search_nt_cond_ann lhs_uids ann)) [] trrel.termr_lhs in

    (* nt_res with candidates for abductive inference *)
    let ntres =
      let loop_conds, self_conds, other_conds = List.fold_left (fun (la, sa, oa) c ->
          if c.ntc_id == CP.loop_id then (la @ [c.ntc_cond]), sa, oa
          else if c.ntc_id == rhs_uid.CP.tu_id then la, (sa @ [c.ntc_cond]), oa
          else la, sa, (oa @ [c])) ([], [], []) nt_conds 
      in

      (* let () = print_endline_quiet ("loop_conds: " ^ (pr_list !CP.print_formula loop_conds)) in *)
      (* let () = print_endline_quiet ("self_conds: " ^ (pr_list !CP.print_formula self_conds)) in *)
      (* let () = print_endline_quiet ("eh_ctx: " ^ (!CP.print_formula eh_ctx)) in                 *)

      (* if List.exists (fun c -> (x_add imply eh_ctx c)) loop_conds then NT_Yes      *)
      (* (* For self loop on the same condition *)                                    *)
      (* else if List.exists (fun c -> (x_add imply eh_ctx c)) self_conds then NT_Yes *)
      (* else if (self_conds != []) &&                                                *)
      (*         (x_add imply eh_ctx (CP.join_disjunctions self_conds))               *)
      (*      then NT_Yes                                                             *)

      let disj_loop_conds = join_disjs (self_conds @ loop_conds) in
      if (x_add imply eh_ctx disj_loop_conds) then NT_Yes
      (* For relations to other methods' conditions *)
      else 
        let other_groups = partition_by_key (fun c -> c.ntc_fn) eq_str other_conds in
        if List.exists (fun (gn, gc) -> 
            (* not (eq_str fn gn) && (gc != []) && *)
            (x_add imply eh_ctx (join_disjs (List.map (fun c -> c.ntc_cond) gc)))) other_groups 
        then NT_Partial_Yes
        else 
          (* Infer the conditions for to-loop nodes *)
          let params = params_of_term_ann prog trrel.termr_rhs in
          let il = infer_loop_cond_list params eh_ctx loop_conds in
          (* Infer the conditions for self-looping nodes or mutual nodes *)
          let rec_iconds = List.fold_left (fun acc ann ->
              let icl = search_rec_icond_ann lhs_uids ann in
              if eq_str fn (CP.fn_of_term_ann ann) then icl::acc
              else acc @ [icl]) [] trrel.termr_lhs 
          in
          (* let rec_iconds = List.map (fun cl ->                                       *)
          (*   List.fold_left (fun acc c ->                                             *)
          (*     if (eq_str fn c.ntc_fn) && not (c.ntc_id == rhs_uid.CP.tu_id) then acc *)
          (*     else acc @ [c.ntc_cond]) [] cl) rec_iconds                             *)
          (* in                                                                         *)
          let abd_f = 
            if !Globals.tnt_abd_strategy = 1 then
              infer_abductive_cond_subtract params cond
            else infer_abductive_cond_templ
          in
          let ir = infer_abductive_cond_list abd_f prog rhs_uid eh_ctx rec_iconds in
          NT_No (ir @ (opt_to_list il))
    in ntres

let proving_non_termination_one_trrel prog lhs_uids rhs_uid trrel =
  let pr = Cprinter.string_of_term_id in
  Debug.no_3 "proving_non_termination_one_trrel" 
    (pr_list pr) pr print_ret_trel print_nt_res
    (fun _ _ _ -> proving_non_termination_one_trrel prog lhs_uids rhs_uid trrel)
    lhs_uids rhs_uid trrel

let is_nondet_rec rec_trrel base_trrels = 
  let base_ctx = List.map (fun btr ->
      x_add simplify btr.ret_ctx btr.termr_rhs_params) base_trrels in
  let rec_ctx = x_add simplify rec_trrel.ret_ctx rec_trrel.termr_rhs_params in
  List.exists (fun bctx -> is_sat (mkAnd rec_ctx bctx)) base_ctx

let norm_nondet_assume nd_vars ctx curr_case f = 
  let disj_fs = CP.split_disjunctions f in
  let disj_fs = List.filter (fun d ->
    if not (overlap nd_vars (CP.fv d)) then false
    else if not (is_sat (mkAnd curr_case d)) then false
    else true) disj_fs 
  in
  match disj_fs with
  | [] -> []
  | _ ->
    let filtered_disj_fs = List.filter (fun d -> is_sat (mkAnd ctx d)) disj_fs in
    if not (is_empty filtered_disj_fs) then filtered_disj_fs
    else disj_fs

let norm_nondet_assume nd_vars ctx curr_case f =
  let pr1 = pr_list !CP.print_sv in 
  let pr2 = !CP.print_formula in
  Debug.no_4 "norm_nondet_assume" pr1 pr2 pr2 pr2 (pr_list pr2) 
    norm_nondet_assume nd_vars ctx curr_case f
  
let proving_non_termination_nondet_trrel (prog: Cast.prog_decl) lhs_uids rhs_uid trrel =
  let pos = no_pos in
  let conseq = rhs_uid.CP.tu_cond in 
  let params = List.concat (List.map CP.afv rhs_uid.CP.tu_args) in
  let ctx = trrel.ret_ctx in
  let nd_vars = remove_dups (CP.collect_nondet_vars ctx) in
  let antes = List.fold_left (fun acc ann ->
      acc @ (search_nt_cond_ann lhs_uids ann)) [] trrel.termr_lhs 
  in
  let antes = List.map (fun a -> a.ntc_cond) antes in
  let assume_f = CP.join_conjunctions ([ctx] @ (List.map (fun a -> mkNot a) antes)) in
  let empty_es = CF.empty_es (CF.mkNormalFlow ()) Label_only.Lab2_List.unlabelled pos in
  let assume_ctx_es = { empty_es with
      CF.es_infer_vars = params @ nd_vars;
      CF.es_formula = CF.mkAnd_pure empty_es.CF.es_formula (Mcpure.mix_of_pure assume_f) pos }
  in
  let assume_ctx = CF.Ctx assume_ctx_es in
  let conseq_f = CF.mkAnd_pure empty_es.CF.es_formula (Mcpure.mix_of_pure (mkNot conseq)) pos in
  try
    let rs = x_add !entail_inf prog assume_ctx conseq_f in
    match rs with
    | None -> (false, [])
    | Some rs ->
      (match rs with
      | CF.FailCtx _ -> (false, [])
      | CF.SuccCtx lst -> 
        let infer_assume = List.concat (List.map CF.collect_pre_pure lst) in
        let infer_assume_nd = List.fold_left (fun acc c ->
            let norm_c = norm_nondet_assume nd_vars ctx conseq c in
            if is_empty norm_c then acc
            else acc @ [(join_disjs norm_c)]
          ) [] infer_assume
        in
        let () = x_tinfo_hp (add_str "assume_nondet" (pr_list !CP.print_formula)) infer_assume_nd pos in
        if is_empty infer_assume then (true, []) (* true means the entailment is successful *)
        else if is_empty infer_assume_nd then (false, [])
        else (true, [(join_disjs infer_assume_nd)]) 
      )
  with _ -> (false, [])

let proving_non_termination_nondet_trrel prog lhs_uids rhs_uid trrel =
  let pr = Cprinter.string_of_term_id in
  Debug.no_3 "proving_non_termination_nondet_trrel" 
    (pr_list pr) pr print_ret_trel (pr_pair string_of_bool (pr_list !CP.print_formula))
    (fun _ _ _ -> proving_non_termination_nondet_trrel prog lhs_uids rhs_uid trrel)
    lhs_uids rhs_uid trrel

let proving_non_termination_nondet_trrels prog lhs_uids rhs_uid trrels =
  if List.for_all (fun trrel -> is_empty trrel.termr_lhs) trrels then (false, [])
  else
    let lhs_uids = List.filter (fun lhs_uid -> lhs_uid.CP.tu_id == rhs_uid.CP.tu_id) lhs_uids in
    let infer_nd_res = List.map (proving_non_termination_nondet_trrel prog lhs_uids rhs_uid) trrels in
    if List.exists (fun (r, _) -> not r) infer_nd_res then (false, [])
    else 
      let infer_nd_conds = List.concat (List.map snd infer_nd_res) in
      if is_empty infer_nd_conds then (false, [])
      else 
        let curr_case = rhs_uid.CP.tu_cond in
        let params = List.concat (List.map CP.afv rhs_uid.CP.tu_args) in
        let infer_nd_cond = simplify (CP.join_conjunctions infer_nd_conds) params in
        let () = x_tinfo_hp (add_str "Nondet conditions: " (pr_list !CP.print_formula)) infer_nd_conds no_pos in
        let () = x_tinfo_hp (add_str "Simplified nondet condition: " !CP.print_formula) infer_nd_cond no_pos in
        let () = x_tinfo_hp (add_str "Current case: " !CP.print_formula) curr_case no_pos in
        if not (is_sat (mkAnd curr_case infer_nd_cond)) ||
           not (x_add imply curr_case infer_nd_cond)
        then (false, [])
        else (true, infer_nd_conds)

let proving_non_termination_nondet_trrels prog lhs_uids rhs_uid trrel =
  let pr = Cprinter.string_of_term_id in
  Debug.no_3 "proving_non_termination_nondet_trrels" 
    (pr_list pr) pr (pr_list print_ret_trel) (pr_pair string_of_bool (pr_list !CP.print_formula))
    (fun _ _ _ -> proving_non_termination_nondet_trrels prog lhs_uids rhs_uid trrel)
    lhs_uids rhs_uid trrel

let proving_non_termination_trrels prog lhs_uids rhs_uid trrels =
  let trrels = List.filter (fun trrel -> 
      eq_str (CP.fn_of_term_ann trrel.termr_rhs) rhs_uid.CP.tu_fname) trrels in
  if trrels = [] then NT_Yes (* No return *)
  else
    let ntres = List.map (proving_non_termination_one_trrel prog lhs_uids rhs_uid) trrels in
    let ntres_w_rel = List.combine ntres trrels in
    (* if ntres = [] then NT_No []                      *)
    (* else if List.for_all is_nt_yes ntres then NT_Yes *)
    if List.for_all is_nt_yes ntres then NT_Yes
    else if not (List.exists is_nt_no ntres) then NT_Partial_Yes
    else
      let gen_disj_conds ntres =
        let ic_list = List.concat (List.map (fun r -> cond_of_nt_res r) ntres) in
        let full_disj_ic_list = get_full_disjoint_cond_list true ic_list in
        (* We should terminate the analysis when there is no new inferred condition *)
        let cond = rhs_uid.CP.tu_cond in 
        let feasible_disj_ic_list = List.filter (fun c -> 
            (is_sat (mkAnd c cond)) && not (x_add imply cond c)) full_disj_ic_list in
        (* if is_empty feasible_disj_ic_list then NT_No []          *)
        (* else NT_No feasible_disj_ic_list (* full_disj_ic_list *) *)
        NT_No feasible_disj_ic_list
      in
      (* gen_disj_conds ntres *)

      let gen_disj_conds ntres =
        let pr = print_nt_res in
        Debug.no_1 "gen_disj_conds" (pr_list pr) pr
          gen_disj_conds ntres
      in

      if !Globals.tnt_infer_nondet then
        (* Attemp to infer_assume on nondet vars *)
        let res, assume_nondet = proving_non_termination_nondet_trrels prog lhs_uids rhs_uid trrels in
        let () = x_tinfo_hp (add_str "infer_nondet_res" string_of_bool) res no_pos in
        if res then 
          NT_Nondet_May (List.map (fun c -> CP.TAssume c) assume_nondet)
        else
          let () = x_tinfo_hp (add_str "gen_disj_conds" (pr_list print_nt_res)) ntres no_pos in 
          x_add_1 gen_disj_conds ntres
      else gen_disj_conds ntres

let proving_non_termination_trrels prog lhs_uids rhs_uid trrels =
  let pr = Cprinter.string_of_term_id in
  Debug.no_3 "proving_non_termination_trrels" 
    (pr_list pr) pr (pr_list print_ret_trel) print_nt_res
    (fun _ _ _ -> proving_non_termination_trrels prog lhs_uids rhs_uid trrels)
    lhs_uids rhs_uid trrels

(* Note that each vertex is a unique condition of a method (uid) *)        
(* let proving_non_termination_one_vertex prog trrels tg scc v =                                *)
(*   (* let loop_edges_from_v = TG.find_all_edges tg v CP.loop_id in                   *)       *)
(*   (* let loop_uids = List.map (fun (_, r, _) -> uid_of_loop r) loop_edges_from_v in *)       *)
(*   let out_edges_from_v = outside_edges_scc_vertex tg scc v in                                *)
(*   let loop_edges_from_v = List.filter (fun (_, r, _) ->                                      *)
(*     CP.is_Loop r.termu_rhs) out_edges_from_v in                                              *)
(*   let loop_uids = List.map (fun (_, r, _) -> uid_of_loop r) loop_edges_from_v in             *)

(*   (* let () = print_endline ("LOOP: " ^                                           *)         *)
(*   (*   (pr_list (fun (_, r, _) -> print_call_trel_debug r) loop_edges_from_v)) in *)         *)

(*   let scc_edges_from_v = edges_of_scc_vertex tg scc v in                                     *)
(*   let looping_edges, non_looping_edges =                                                     *)
(*     List.partition (fun (_, _, d) -> d = v) scc_edges_from_v in                              *)
(*   (* let () = print_endline ("LOOPING: " ^                                        *)         *)
(*   (*   (pr_list (fun (_, r, _) -> print_call_trel_debug r) looping_edges)) in     *)         *)
(*   (* let () = print_endline ("NON-LOOPING: " ^                                    *)         *)
(*   (*   (pr_list (fun (_, r, _) -> print_call_trel_debug r) non_looping_edges)) in *)         *)

(*   (* If the number of looping edges is > 1, it means there is          *)                    *)
(*   (* multiple recursive calls of the same function in the same context *)                    *)
(*   match looping_edges with                                                                   *)
(*   | (_, looping_rel, _)::_ ->                                                                *)
(*     begin match looping_rel.termu_lhs with                                                   *)
(*     | TermU uid -> (* the uid here is same as the one in RHS of trrel *)                     *)
(*       let rhs_uid = uid in                                                                   *)
(*       let other_non_looping_edges = List.filter (fun (_, rel, _) ->                          *)
(*         not (eq_str (CP.fn_of_term_ann rel.termu_rhs) uid.CP.tu_fname)) non_looping_edges in *)
(*       let lhs_uids = List.concat (List.map (fun (_, rel, _) -> opt_to_list                   *)
(*         (CP.uid_of_term_ann rel.termu_rhs)) other_non_looping_edges) in                      *)
(*       let ntres = proving_non_termination_trrels prog                                        *)
(*         ((uid::lhs_uids) @ loop_uids) rhs_uid trrels in                                      *)
(*       (Some uid, ntres)                                                                      *)
(*     | _ -> (None, NT_No [])                                                                  *)
(*     end                                                                                      *)
(*   | [] ->                                                                                    *)
(*     begin match (loop_edges_from_v @ non_looping_edges) with                                 *)
(*     | (_, rel, _)::_ ->                                                                      *)
(*       begin match rel.termu_lhs with                                                         *)
(*       | TermU uid ->                                                                         *)
(*         let rhs_uid = uid in                                                                 *)
(*         let lhs_uids = List.concat (List.map (fun (_, rel, _) -> opt_to_list                 *)
(*           (CP.uid_of_term_ann rel.termu_rhs)) non_looping_edges) in                          *)
(*         let ntres = proving_non_termination_trrels prog                                      *)
(*           ((uid::lhs_uids) @ loop_uids) rhs_uid trrels in                                    *)
(*         (Some uid, ntres)                                                                    *)
(*       | _ -> (None, NT_No [])                                                                *)
(*       end                                                                                    *)
(*     | [] -> (None, NT_No [])                                                                 *)
(*     end                                                                                      *)

let proving_non_termination_one_vertex prog trrels tg scc v =
  let out_edges_from_v = outside_edges_scc_vertex tg scc v in
  let loop_edges_from_v = List.filter (fun (_, r, _) -> 
      CP.is_Loop r.termu_rhs) out_edges_from_v in
  let loop_uids = List.map (fun (_, r, _) -> uid_of_loop r) loop_edges_from_v in
  let scc_edges_from_v = edges_of_scc_vertex tg scc v in
  match (scc_edges_from_v @ loop_edges_from_v) with
  | (_, rel, _)::_ ->
    begin match rel.termu_lhs with
      | TermU uid ->
        let rhs_uid = uid in
        let lhs_uids = List.concat (List.map (fun (_, rel, _) -> 
            opt_to_list (CP.uid_of_term_ann rel.termu_rhs)) scc_edges_from_v) in
        let ntres = proving_non_termination_trrels prog
            (lhs_uids @ loop_uids) rhs_uid trrels in
        (Some uid, ntres)
      | _ -> (None, NT_No [])
    end
  | [] -> (None, NT_No [])

let proving_trivial_termination_one_vertex prog tg scc v =
  let out_edges_from_v = outside_edges_scc_vertex tg scc v in
  let term_edges_from_v = List.filter (fun (_, r, _) -> 
      CP.is_Term r.termu_rhs) out_edges_from_v in
  match term_edges_from_v with
  | [] -> (None, [])
  | (_, rel, _)::_ ->
    match rel.termu_lhs with
    | TermU uid ->
      let params = params_of_term_ann prog rel.termu_lhs in
      let eh_ctx = mkAnd rel.call_ctx uid.CP.tu_cond in
      (* let term_conds = List.map (fun (_, r, _) ->                            *)
      (*   mkAnd eh_ctx (CP.cond_of_term_ann r.termu_rhs)) term_edges_from_v in *)
      let term_conds = List.map (fun (_, r, _) -> 
          mkAnd eh_ctx (mkNot (CP.cond_of_term_ann r.termu_rhs))) term_edges_from_v in
      (* let () = print_endline (pr_list !CP.print_formula term_conds) in *)
      let term_conds = List.map (fun f -> x_add simplify f params) term_conds in
      (* Only keep the new conditions *)
      let term_conds = List.filter (fun c -> not (x_add imply eh_ctx c)) term_conds in
      if (is_empty term_conds) then (None, [])
      else
        let term_conds = get_full_disjoint_cond_list_with_ctx eh_ctx term_conds in
        (* let term_conds = List.filter (fun c -> is_sat (mkAnd eh_ctx c)) term_conds in *)
        (Some uid, term_conds)
    | _ -> (None, [])

let proving_trivial_termination_one_vertex prog tg scc v =
  let pr = pr_pair (pr_opt string_of_term_id) (pr_list !CP.print_formula) in
  Debug.no_1 "proving_trivial_termination_one_vertex" string_of_int pr
    (fun _ -> proving_trivial_termination_one_vertex prog tg scc v) v

let rec proving_non_termination_scc prog trrels tg scc =
  let ntres_scc = List.map (fun v -> 
      proving_non_termination_one_vertex prog trrels tg scc v) scc in
  (* Removing all dummy nt_res (None, NT_No []) *)
  let ntres_scc = List.fold_left (fun acc (uid_opt, r) ->
      match uid_opt with 
      | None -> acc
      | Some uid -> acc @ [(uid, r)]) [] ntres_scc in
  if List.for_all (fun (_, r) -> (is_nt_yes r) || (is_nt_partial_yes r)) ntres_scc then
    update_ann scc (subst (CP.Loop None, []))
  else
    let nonterm_uids = List.map fst (List.filter (fun (uid, r) -> is_nt_yes r) ntres_scc) in
    let nd_nonterm_uids = List.fold_left (fun acc (uid, r) -> 
        match r with
        | NT_Nondet_May tcex -> acc @ [(uid, tcex)]
        | _ -> acc) [] ntres_scc in
    (* Update ann with nonterm_uid to Loop *)
    let subst_loop ann =
      match ann with
      | CP.TermU uid ->
        if Gen.BList.mem_eq (fun u1 u2 -> u1.CP.tu_id == u2.CP.tu_id) uid nonterm_uids
        then subst (CP.Loop None, []) ann
        else
          (* termination-crafted-lit/GulwaniJainKoskinen-PLDI2009-Fig1_true-termination.c *)
          begin
            try
              let _, nd_cex = List.find (fun (nd_uid, _) ->
                uid.CP.tu_id == nd_uid.CP.tu_id) nd_nonterm_uids in
              subst (CP.MayLoop (Some { CP.tcex_trace = nd_cex }), []) ann
              (* subst (CP.MayLoop None, []) ann *)
            with Not_found -> ann
          end
      | _ -> ann
    in
    let tg = match nonterm_uids, nd_nonterm_uids with
      | [], [] -> tg
      | _ -> map_ann_scc tg scc (update_ann scc subst_loop)
    in
    (* let () = print_endline (print_graph_by_rel tg) in *)
    let abd_conds = List.fold_left (fun acc (uid, r) ->
        match r with
        | NT_No ic ->
          if is_empty ic then acc
          else
            let () = update_case_spec_with_icond_list_proc uid.CP.tu_fname uid.CP.tu_cond ic in
            acc @ [(uid.CP.tu_id, ic)]
        | _ -> acc) [] ntres_scc in
    if not (is_empty abd_conds) then 
      let tg = update_graph_with_icond tg scc abd_conds in
      let n_conds = List.concat (List.map snd abd_conds) in
      let () = x_tinfo_hp (add_str "Restarting TNT analysis with new conds" (pr_list !CP.print_formula)) n_conds no_pos in
      raise (Restart_with_Cond (n_conds, tg))
    else 
      let term_conds_scc = List.fold_left (fun acc v ->
          let tres = proving_trivial_termination_one_vertex prog tg scc v in
          match tres with
          | (None, _) -> acc
          | (Some uid, tc) ->
            if is_empty tc then acc
            else
              let () = update_case_spec_with_icond_list_proc uid.CP.tu_fname uid.CP.tu_cond tc in
              acc @ [(uid.CP.tu_id, tc)]) [] scc in
      if not (is_empty term_conds_scc) then
        let tg = update_graph_with_icond tg scc term_conds_scc in
        let n_conds = List.concat (List.map snd term_conds_scc) in
        let () = x_tinfo_hp (add_str "Restarting TNT analysis with new conds" (pr_list !CP.print_formula)) n_conds no_pos in
        raise (Restart_with_Cond (n_conds, tg))
      else raise Should_Finalize

let proving_non_termination_scc prog trrels tg scc =
  let pr = print_graph_by_rel in
  let pr1 = pr_list string_of_int in
  Debug.no_2 "proving_non_termination_scc" pr pr1 (fun _ -> "")
    (fun _ _ -> proving_non_termination_scc prog trrels tg scc) tg scc

(* Auxiliary methods for main algorithms *)
let proving_termination_scc prog trrels tg scc =
  let () = x_tinfo_pp ("Analyzing scc: " ^ (pr_list string_of_int scc)) no_pos in
  (* Term with a ranking function for each scc's node *)
  let res = infer_ranking_function_scc prog tg scc in
  match res with
  | Some rank_of_ann ->
    let scc_num = CP.mkIConst (scc_fresh_int ()) no_pos in
    update_ann scc (fun ann ->
        let res = (CP.Term, scc_num::(rank_of_ann ann)) in 
        subst res ann)
  | None -> proving_non_termination_scc prog trrels tg scc

