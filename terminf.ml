(**** TERMINATION RANKING INFERENCE ****)

open Globals
open Gen
open Cformula
open Cpure

module C = Cast
module CF = Cformula
module MCP = Mcpure
module CP = Cpure


(*****************************)
(* Functions for creating ID *)
(*****************************)
let view_rank_id view_id =
  "r_" ^ view_id

let view_rank_sv view_id =
  SpecVar (Int, view_rank_id view_id, Unprimed)

let view_rank_sv_opt view_id =
  if !en_term_inf then [view_rank_sv view_id] else []

let view_rarg_id view_id =
  "r_" ^ view_id ^ "_" ^ (string_of_int (fresh_int ()))

let view_base_ragr view_id =
  let rarg_id = SpecVar (Int, view_rarg_id view_id, Unprimed) in
  mkRArg_const rarg_id

let view_var_ragr view_id =
  let rarg_id = SpecVar (Int, view_rarg_id view_id, Unprimed) in
  mkRArg_var rarg_id

(***************************************)
(* Function for collecting information *)
(***************************************)

(* TermInf: Collect data variables of DataNode and 
 * rank variables of ViewNode to build RankRel 
 * OUTPUT: Vars and Impl Vars for RRel and is_rec_case of view *)
let rec collect_rankrel_vars_h_formula_raw (h: CF.h_formula) (view_ids: string list)
  : (CF.h_formula * CP.rank_arg list * CP.spec_var list * bool) =
  match h with 
  | CF.Star s ->
      let h1, r1, e1, ir1 = collect_rankrel_vars_h_formula_raw s.h_formula_star_h1 view_ids in 
      let h2, r2, e2, ir2 = collect_rankrel_vars_h_formula_raw s.h_formula_star_h2 view_ids in
      (CF.Star { s with h_formula_star_h1 = h1; h_formula_star_h2 = h2; },
      r1 @ r2, e1 @ e2, ir1 || ir2)
  | CF.DataNode { h_formula_data_arguments = args } ->
      let iargs = List.filter (fun sv -> CP.is_int_var sv) args in
      let ragrs = List.map CP.mkRArg_var iargs in
      (h, ragrs, [], false)
  | CF.ViewNode v ->
      let ir = Gen.BList.mem_eq (=) v.h_formula_view_name view_ids in
      let rarg = view_var_ragr v.h_formula_view_name in
      let rarg_id = rarg.CP.rank_arg_id in
      let n_vn = CF.ViewNode { v with h_formula_view_rank = Some rarg_id; } in
      (n_vn, [rarg], [rarg_id], ir)
  | _ -> (h, [], [], false)

let collect_rankrel_vars_h_formula_raw (h: CF.h_formula) (view_ids: string list) 
  : (CF.h_formula * CP.rank_arg list * CP.spec_var list * bool) = 
  let pr1 = !print_h_formula in
  let pr2 = !print_svl in
  let pr3 = string_of_bool in
  let pr4 = pr_list (fun s -> s) in
  let pr5 = !print_rank_arg_list in
  Debug.no_2 "collect_rankrel_vars_h_formula" pr1 pr4 
  (fun (a, b, c, d) -> pr_pair (pr_triple pr1 pr5 pr2) pr3 ((a, b, c), d))
  collect_rankrel_vars_h_formula_raw h view_ids

let rec collect_rankrel_vars_h_formula (h: CF.h_formula) (rel_id: int) (view_ids: string list)
  : CP.formula list =
  match h with 
  | CF.Star s ->
      let rr1 = collect_rankrel_vars_h_formula s.h_formula_star_h1 rel_id view_ids in 
      let rr2 = collect_rankrel_vars_h_formula s.h_formula_star_h2 rel_id view_ids in
      rr1 @ rr2
  | CF.ViewNode v ->
      let ir = Gen.BList.mem_eq (=) v.CF.h_formula_view_name view_ids in
      if not ir then []
      else
        let rank_id = match v.h_formula_view_rank with
        | None -> CP.SpecVar (Int, view_rarg_id v.h_formula_view_name, Unprimed) 
        | Some v -> v in
        let rrel = CP.mkRankConstraint rel_id rank_id
          (List.map CP.mkRArg_var v.h_formula_view_arguments) None in
        [rrel]
  | _ -> []

let collect_view_rank_h_formula (h: CF.h_formula) : CP.spec_var list =
  let f h = match h with
    | ViewNode v -> map_opt (fun r -> [r]) v.h_formula_view_rank
    | _ -> None
  in fold_h_formula h f List.concat

let collect_view_rank_formula (f: CF.formula) : CP.spec_var list =
  let h, _, _, _, _ = split_components f in
  collect_view_rank_h_formula h

let collect_view_rank_es (es: CF.entail_state) : CP.spec_var list =
  (collect_view_rank_formula es.es_formula) @
  (collect_view_rank_h_formula es.es_heap)

(*
let rec collect_view_rank_context (ctx: context) : CP.spec_var list =
  match ctx with
  | Ctx es -> collect_view_rank_es es
  | OCtx (c1, c2) -> (collect_view_rank_context c1) @ (collect_view_rank_context c2)

let collect_view_rank_failesc_context (ctx: failesc_context) : CP.spec_var list =
  let _, _, bctx_l = ctx in
  List.concat (List.map (fun (_, ctx) -> collect_view_rank_context ctx) bctx_l)

let collect_view_rank_list_failesc_context (ctx: list_failesc_context) : CP.spec_var list =
  List.concat (List.map collect_view_rank_failesc_context ctx)
*)

let collect_view_rank_list_failesc_context (ctx: list_failesc_context) : CP.spec_var list =
  let f_c arg ctx = match ctx with
  | Ctx es -> Some (ctx, collect_view_rank_es es)
  | _ -> None
  in
  let f_arg arg ctx = arg in
  snd (trans_list_failesc_context ctx () f_c f_arg List.concat)

let collect_rrel_list_failesc_context (ctx: list_failesc_context) : CF.rrel list =
  let f_c arg ctx = match ctx with
  | Ctx es -> Some (ctx, es.es_rrel)
  | _ -> None
  in
  let f_arg arg ctx = arg in
  snd (trans_list_failesc_context ctx () f_c f_arg List.concat)

(****************************************)
(* Function for adding rank constraints *)
(****************************************)

(* TermInf: Add rank constraints into view and struc_formula *)
type rank_type =
  | VIEW of (string * CP.spec_var list * int)  (* view name * view's args * rel_id *)
  | PRE of C.typed_ident list
  | POST

let rec add_rank_constraint_view (vdef: C.view_decl): C.view_decl =
  let view_form = add_rank_constraint_struc_formula vdef.C.view_formula 
    (VIEW (vdef.C.view_name, vdef.C.view_vars, (fresh_rrel_id ()))) in
  let un_struc_f = CF.get_view_branches view_form in
  let rbc = match vdef.C.view_raw_base_case with
  | None -> None
  | Some _ ->
      let rec f_tr_base f = 
        let mf f h fl pos = if (CF.is_complex_heap h) then (CF.mkFalse fl pos) else f in
        match f with
        | CF.Base b -> mf f b.CF.formula_base_heap b.CF.formula_base_flow b.CF.formula_base_pos
        | CF.Exists b -> mf f b.CF.formula_exists_heap b.CF.formula_exists_flow b.CF.formula_exists_pos
        | CF.Or b -> CF.mkOr (f_tr_base b.CF.formula_or_f1) (f_tr_base b.CF.formula_or_f2) no_pos in
      List.fold_left (fun a (c, l) -> 
        let fc = f_tr_base c in
        if (CF.isAnyConstFalse fc) then a 
        else match a with 
        | Some f1  -> Some (CF.mkOr f1 fc no_pos)
        | None -> Some fc) None un_struc_f
  in { vdef with
    C.view_formula = view_form; 
    C.view_un_struc_formula = un_struc_f; 
    C.view_raw_base_case = rbc; }

and add_rank_constraint_struc_formula (f: CF.struc_formula) (rtyp: rank_type): CF.struc_formula =
  match f with
  | CF.EList l -> CF.EList (List.map (fun (lbl, sf) ->
      (lbl, add_rank_constraint_struc_formula sf rtyp)) l)
  | CF.ECase c -> CF.ECase { c with 
      CF.formula_case_branches = List.map (fun (cf, sf) -> 
        (cf, add_rank_constraint_struc_formula sf rtyp)) c.CF.formula_case_branches; }
  | CF.EBase b -> 
      let cont = match b.CF.formula_struc_continuation with
        | None -> None
        | Some sf -> Some (add_rank_constraint_struc_formula sf rtyp) in
      let base, ivars = add_rank_constraint_formula b.CF.formula_struc_base rtyp in
      CF.EBase { b with
        CF.formula_struc_implicit_inst = b.CF.formula_struc_implicit_inst @ ivars;
        CF.formula_struc_base = base;
        CF.formula_struc_continuation = cont; }
  | CF.EAssume a -> CF.EAssume { a with
      CF.formula_assume_simpl = fst (add_rank_constraint_formula a.CF.formula_assume_simpl POST);
      CF.formula_assume_struc = add_rank_constraint_struc_formula a.CF.formula_assume_struc POST; }
  | CF.EInfer i -> CF.EInfer { i with
      CF.formula_inf_continuation = add_rank_constraint_struc_formula i.CF.formula_inf_continuation rtyp; }

and add_rank_constraint_formula (f: CF.formula) (rtyp: rank_type): (CF.formula * CP.spec_var list) =
  let pr1 = !CF.print_formula in
  let pr2 = !CF.print_svl in
  Debug.no_1 "add_rank_constraint_formula" pr1 (pr_pair pr1 pr2)
  (fun _ -> add_rank_constraint_formula_x f rtyp) f

and add_rank_constraint_formula_x (f: CF.formula) (rtyp: rank_type): (CF.formula * CP.spec_var list) =
  let add_rank_constraint_pure hf pf rtyp =
    match rtyp with
    | VIEW (view_id, view_args, rel_id) ->
        let is_raw_view = view_args = [] in
        let rankrel_id = view_rank_sv view_id in
        let nhf_r, rrel_args_r, rrel_ivars_r, ir =
          collect_rankrel_vars_h_formula_raw hf [view_id] in
        let rrel_args_r, rrel_base_ivars_r = 
          if not ir (* Base case *) then
            (* Add constant rank arg for base case *)
            let base_ragr = view_base_ragr view_id in
            rrel_args_r @ [base_ragr], [base_ragr.CP.rank_arg_id] 
          else rrel_args_r, [] in
        if is_raw_view then
          nhf_r,
          MCP.memoise_add_pure_N pf (CP.mkRankConstraint_raw rankrel_id rrel_args_r),
          rrel_ivars_r @ rrel_base_ivars_r
        else
          let rrels = collect_rankrel_vars_h_formula nhf_r rel_id [view_id] in
          let rrel_raw = {
            CP.rel_id = fresh_rrel_id (); 
            CP.rank_id = rankrel_id;
            CP.rank_args = rrel_args_r;
            CP.rrel_raw = None;   
          } in
          let npf = MCP.memoise_add_pure_N pf (CP.mkRankConstraint rel_id rankrel_id 
            (List.map CP.mkRArg_var view_args) (Some rrel_raw)) in
          let npf = MCP.memoise_add_pure_N npf (CP.join_conjunctions rrels) in
          nhf_r, npf, rrel_ivars_r @ rrel_base_ivars_r
    | PRE proc_args ->
        let nhf, rankrel_vars, rankrel_ivars, _ = collect_rankrel_vars_h_formula_raw hf [] in
        (* Add Term[r] for PRE based on the args of proc *)
        let npf = MCP.memoise_add_pure_N pf (CP.mkPure (CP.mkLexVar 
          TermR [] (List.map (fun r -> CP.mkVar r no_pos) rankrel_ivars) no_pos )) in
        nhf, npf, rankrel_ivars
    | POST -> 
        let nhf, rankrel_vars, rankrel_ivars, _ = collect_rankrel_vars_h_formula_raw hf [] in
        nhf, pf, rankrel_ivars 
  in match f with
  | CF.Base b -> 
    begin
      let heap_base, rankrel_pure_base, rankrel_ivars = add_rank_constraint_pure
        b.CF.formula_base_heap b.CF.formula_base_pure rtyp in
      match rtyp with 
      | POST -> 
        if rankrel_ivars == [] then 
          CF.Base { b with 
            CF.formula_base_heap = heap_base;
            CF.formula_base_pure = rankrel_pure_base; }, []
        else
          CF.Exists {
            CF.formula_exists_qvars = rankrel_ivars;
            CF.formula_exists_heap = heap_base;
            CF.formula_exists_pure = rankrel_pure_base;
            CF.formula_exists_type = b.CF.formula_base_type;
            CF.formula_exists_and = b.CF.formula_base_and;
            CF.formula_exists_flow = b.CF.formula_base_flow;
            CF.formula_exists_label = b.CF.formula_base_label;
            CF.formula_exists_pos = b.CF.formula_base_pos; }, []

      | _ -> CF.Base { b with 
        CF.formula_base_heap = heap_base;
        CF.formula_base_pure = rankrel_pure_base; }, rankrel_ivars
    end
  | CF.Exists e -> 
      let heap_base, rankrel_pure_base, rankrel_ivars = add_rank_constraint_pure
        e.CF.formula_exists_heap e.CF.formula_exists_pure rtyp in
      CF.Exists { e with
        CF.formula_exists_qvars = e.CF.formula_exists_qvars;
        CF.formula_exists_heap = heap_base;
        CF.formula_exists_pure = rankrel_pure_base;
      }, rankrel_ivars
  | CF.Or o ->
      let f1, i1 = add_rank_constraint_formula_x o.CF.formula_or_f1 rtyp in
      let f2, i2 = add_rank_constraint_formula_x o.CF.formula_or_f2 rtyp in
      CF.Or { o with CF.formula_or_f1 = f1; CF.formula_or_f2 = f2; }, i1@i2

(*****************************************)
(* Function for solving rrel constraints *)
(*****************************************)

(* TermInf: Transform RankRel and LexVar (TermR) *)
let b_formula_of_rankrel (rr: rankrel) =
  let p = no_pos in
  let rank_var_args, rank_const_args = List.partition (fun ra ->
    match ra.rank_arg_type with | RVar -> true | _ -> false) rr.rank_args in
  let coe_prefix = "c_" ^ (string_of_int rr.rel_id) ^ "_" in
  let const_coes, nneg_const_coes = match rank_const_args with
  | [] -> [SpecVar (Int, coe_prefix ^ (string_of_int 0), Unprimed)], []
  | [c] -> 
      let cid = c.rank_arg_id in 
      [cid], if rank_var_args = [] then [cid] else []
  | _ -> List.map (fun ra -> ra.rank_arg_id) rank_const_args, [] in
  (* Assumption: const_coes has at least 1 element *)
  let const_exp = List.fold_left (fun a c -> mkAdd a (mkVar c p) p) 
    (mkVar (List.hd const_coes) p) (List.tl const_coes) in
  let rank_var_svs = List.map (fun ra -> ra.rank_arg_id) rank_var_args in
  let exp, var_coes = snd (List.fold_left (fun (i, (a, cs)) v ->
    let c = SpecVar (Int, coe_prefix ^ (string_of_int i), Unprimed) in
    (i+1, (mkAdd a (mkMult (mkVar c p) (mkVar v p) p) p, cs@[c])))
  (1, (const_exp, [])) rank_var_svs) in
  mkEq_b (mkVar rr.rank_id p) exp p, 
  const_coes @ var_coes, rr.rank_id::rank_var_svs, nneg_const_coes

let replace_rankrel_by_b_formula (is_raw: bool) (f: CP.formula) =
  let f_b_f arg b = 
    let (pf, _) = b in
    match pf with
    | RankRel rr -> 
      let nb, const_coes, arg_coes, nneg_coes = 
        if not is_raw then b_formula_of_rankrel rr
        else match rr.rrel_raw with
        | None -> mkTrue_b no_pos, [], [], [] 
        | Some rr_raw -> b_formula_of_rankrel rr_raw
      in Some (nb, (const_coes, arg_coes, nneg_coes))
    | _ -> Some (b, ([], [], [])) in
  let f_comb a bl = List.fold_left (fun (a1, a2, a3) (b1, b2, b3) -> 
    (a1@b1, a2@b2, a3@b3)) ([], [], []) bl in
  let f_arg = (voidf2, voidf2, voidf2) in
  foldr_formula f () (nonef2, f_b_f, nonef2) f_arg (f_comb, f_comb, f_comb)

let b_formula_of_rankrel_sol (rr: rankrel) subst =
  let p = no_pos in
  let rank_var_args, rank_const_args = List.partition (fun ra ->
    match ra.rank_arg_type with | RVar -> true | _ -> false) rr.rank_args in
  let coe_prefix = "c_" ^ (string_of_int rr.rel_id) ^ "_" in
    
  let find_val_of_c c subst = 
    try List.assoc (name_of_spec_var c) subst
    with _ -> 0
  in
  let const_coes = match rank_const_args with
  | [] -> [SpecVar (Int, coe_prefix ^ (string_of_int 0), Unprimed)]
  | _ -> List.map (fun ra -> ra.rank_arg_id) rank_const_args in
  let const_exp = mkIConst
    (List.fold_left (fun a c -> a + (find_val_of_c c subst)) 0 const_coes) p in

  let rank_var_svs = List.map (fun ra -> ra.rank_arg_id) rank_var_args in
  let exp = snd (List.fold_left (fun (i, a) v ->
    let c = SpecVar (Int, coe_prefix ^ (string_of_int i), Unprimed) in
    let c_val = find_val_of_c c subst in
    let s = if c_val == 0 then a
    else if c_val == 1 then mkAdd a (mkVar v p) p
    else mkAdd a (mkMult (mkIConst c_val p) (mkVar v p) p) p in
    (i+1, s)) (1, const_exp) rank_var_svs) in
  mkEq_b (mkVar rr.rank_id p) exp p 

let subst_rankrel_sol_p_formula raw_subst subst (f: CP.formula) =
  let f_b_f b = 
    let (pf, ann) = b in
    match pf with
    | RankRel rr -> 
        if not raw_subst then Some (b_formula_of_rankrel_sol rr subst) 
        else begin
          match rr.rrel_raw with
          | None -> Some (mkTrue_b no_pos) 
          | Some rr_raw -> Some (b_formula_of_rankrel_sol rr_raw subst) 
          end
    | LexVar lv -> begin
        match lv.lex_ann with
        | TermR -> Some ((LexVar { lv with lex_ann = Term; lex_exp = lv.lex_tmp; }), ann)
        | _ -> Some b
      end
    | _ -> Some b
  in transform_formula (nonef, nonef, nonef, f_b_f, somef) f

let subst_rankrel_sol_mix_formula raw_subst subst (f: MCP.mix_formula) =
  let f_p_f pf = Some (subst_rankrel_sol_p_formula raw_subst subst pf) in
  MCP.transform_mix_formula (nonef, nonef, f_p_f, nonef, nonef) f
  
let rec remove_redundant_implicit_inst (f: struc_formula) (vs: CP.spec_var list): struc_formula =
  match f with
  | EList l -> EList (List.map (fun (lbl, sf) ->
      (lbl, remove_redundant_implicit_inst sf vs)) l)
  | ECase c -> ECase { c with 
      formula_case_branches = List.map (fun (cf, sf) -> 
        (cf, remove_redundant_implicit_inst sf vs)) c.formula_case_branches; }
  | EBase b -> 
      let cont = match b.formula_struc_continuation with
        | None -> None
        | Some sf -> Some (remove_redundant_implicit_inst sf vs) in
      EBase { b with
        formula_struc_implicit_inst = Gen.BList.difference_eq CP.eq_spec_var
          b.formula_struc_implicit_inst vs;
        formula_struc_continuation = cont; }
  | EAssume a -> EAssume { a with
      formula_assume_struc = remove_redundant_implicit_inst a.formula_assume_struc vs; }
  | EInfer i -> EInfer { i with
      formula_inf_continuation = remove_redundant_implicit_inst i.formula_inf_continuation vs; }

let f_p_f raw_subst subst pf = Some (subst_rankrel_sol_p_formula raw_subst subst pf)

let f_h_f hf = match hf with
  | ViewNode vn -> Some (ViewNode { vn with
    CF.h_formula_view_rank = None;
    CF.h_formula_view_arguments = vn.h_formula_view_arguments @ (fold_opt (fun r -> [r]) vn.h_formula_view_rank)})
  | _ -> None

let subst_rankrel_sol_struc_formula raw_subst subst (f: struc_formula) =
  let trans_f = transform_struc_formula 
    (nonef, nonef, f_h_f, (nonef, nonef, (f_p_f raw_subst subst), nonef, nonef)) f in
  let vs = List.map (fun id -> CP.SpecVar (Int, id, Unprimed)) (fst (List.split subst)) in
  remove_redundant_implicit_inst trans_f vs  

let subst_rankrel_sol_formula raw_subst subst (f: CF.formula) =
  CF.transform_formula 
    (nonef, nonef, f_h_f, (nonef, nonef, (f_p_f raw_subst subst), nonef, nonef)) f

let solve_rrel rrel = 
  let solve raw_rrel ctx ctr = 
    let nctx, (const_c, var_c, nneg_c) = replace_rankrel_by_b_formula raw_rrel ctx in
    Redlog.solve_constr_by_elim nctx ctr const_c var_c nneg_c
  in
  let ctx = MCP.pure_of_mix rrel.rrel_ctx in
  let ctr = MCP.pure_of_mix rrel.rrel_ctr in
  let res = solve false ctx ctr in
  if not (CP.is_False res) then (res, false)
  else  
    let res = solve true ctx ctr in
    (* true means we have to substitute the model into raw rankrel *)
    (res, true)

let rec solve_rrel_list rrel_list =
  let c_constrs, is_raw = List.split (List.map solve_rrel rrel_list) in
  let is_linear = List.for_all Redlog.is_linear_formula c_constrs in
  let fv = Gen.BList.remove_dups_eq eq_spec_var 
    (List.concat (List.map CP.fv c_constrs)) in
  let model = Smtsolver.get_model is_linear fv c_constrs in 
  (model, List.exists (fun b -> b) is_raw)

(* Plug inferred result into views *)
let plug_rank_into_view (raw_subst_flag: bool) sol_for_rrel (vdef: C.view_decl) : C.view_decl =
  let p = no_pos in
  let vrank = view_rank_sv vdef.C.view_name in
  { vdef with
    C.view_vars = vdef.C.view_vars @ [vrank];
    C.view_labels = vdef.C.view_labels @ [Label_only.Lab_LAnn.unlabelled];
    C.view_formula = subst_rankrel_sol_struc_formula raw_subst_flag sol_for_rrel vdef.C.view_formula; 
    C.view_user_inv = MCP.memoise_add_pure_N vdef.C.view_user_inv 
      (CP.mkPure (CP.mkGte (CP.mkVar vrank p) (CP.mkIConst 0 p) p));
    C.view_un_struc_formula = List.map (fun (f, l) -> 
      (subst_rankrel_sol_formula raw_subst_flag sol_for_rrel f, l)) vdef.C.view_un_struc_formula; 
    C.view_raw_base_case = map_opt (fun f -> subst_rankrel_sol_formula raw_subst_flag sol_for_rrel f) vdef.C.view_raw_base_case;
    C.view_base_case = map_opt (fun (g, f) -> (g, subst_rankrel_sol_mix_formula raw_subst_flag sol_for_rrel f)) vdef.C.view_base_case; }

let trans_proc_specs (proc: C.proc_decl) : C.proc_decl =
  (* TermInf: transform TermR to Term *)
  let n_spec = subst_rankrel_sol_struc_formula false [] proc.C.proc_static_specs in
  proc.C.proc_stk_of_static_specs # push n_spec;
  { proc with C.proc_static_specs = n_spec; }

let plug_inf_info (prog: C.prog_decl) : C.prog_decl =
  let _ = Hashtbl.iter (fun id proc ->
    Hashtbl.remove prog.C.new_proc_decls id;
    Hashtbl.add prog.C.new_proc_decls id (trans_proc_specs proc)) prog.C.new_proc_decls in
  let inf_vdefs = Hashtbl.fold (fun _ v va -> va @ [v]) prog.C.prog_inf_view_decls [] in 
  { prog with C.prog_view_decls = inf_vdefs; }


