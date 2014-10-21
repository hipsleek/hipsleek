open Globals
open Debug
open Gen.Basic


module C = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module MCPD = Mcpure_D


(*
 ************************
 * various search types
 ************************
 *)
type search_res_t = 'a list

and search_formula_t = (CF.formula -> search_res_t option)
                       * search_heap_formula_t
                       * search_mix_formula_t

and search_heap_formula_t = (CF.h_formula -> search_res_t option)

and search_mix_formula_t = search_memo_pure_t
                           * search_var_aset_t
                           * search_pure_formula_t

and search_memo_formula_t = search_mix_formula_t

and search_memo_pure_t = (MCPD.memo_pure -> search_res_t option)

and search_var_aset_t = (MCPD.var_aset -> search_res_t option)

and search_pure_formula_t = (CP.formula -> search_res_t option)
                            * search_pure_bformula_t 

and search_pure_bformula_t = (CP.b_formula -> search_res_t option)
                             * search_pure_exp_t

and search_pure_exp_t = (CP.exp -> search_res_t option)


let combine_search_results (r1: search_res_t opt) (e2: search_res_t opt)
    : search_res_t =
  match e1, e2 with
  | None, None -> []
  | Some e1', None -> e1'
  | None, Some es' -> e2'
  | Some e1', Some e2' -> (e1' @ e2')


let combine_search_results_list (r_list: (search_res_t opt) list)
    : search_res_t =
  let res_list = List.map (fun r ->
    match r with
    | None -> []
    | Some r' -> r'
  ) r_list in
  List.concat res_list


let rec search_in_formula (searcher : search_formula_t) (f: CF.formula)
    : search_res_t =
  let (search_f, search_hf, search_mf) = searcher in
  let res = search_f f in
  match res with
  | Some res' -> res'
  | None -> 
      match f with
      | CF.Base b ->
          let r1 = search_in_heap_formula search_hf b.CF.formula_base_heap in
          let r2 = search_in_mix_formula search_mf b.CF.formula_base_pure in
          combine_list_opt r1 r2
      | CF.Or o ->
          let r1 = search_in_formula search_f o.CF.formula_or_f1 in
          let r2 = search_in_formula search_f o.CF.formula_or_f2 in
          combine_list_opt r1 r2
      | CF.Exists e -> 
          let r1 = search_in_heap_formula search_hf b.CF.formula_exists_heap in
          let r2 = search_in_mix_formula search_mf b.CF.formula_exists_pure in
          combine_list_opt r1 r2


and search_in_heap_formula (searcher: search_heap_formula_t) (f: CF.h_formula)
    : search_res_t =
  let res = search_hf hf in
  match res with
  | Some res' -> res'
  | None ->
      match hf with
      | Star x ->
          let r1 = search_in_heap_formula search_hf x.CF.h_formula_star_h1 in
          let r2 = search_in_heap_formula search_hf x.CF.h_formula_star_h2 in
          combine_list_opt r1 r2
      | StarMinus x ->
          let r1 = search_in_heap_formula search_hf x.CF.h_formula_starminus_h1 in
          let r2 = search_in_heap_formula search_hf x.CF.h_formula_starminus_h2 in
          combine_list_opt r1 r2
      | Conj x ->
          let r1 = search_in_heap_formula search_hf x.CF.h_formula_conj_h1 in
          let r2 = search_in_heap_formula search_hf x.CF.h_formula_conj_h2 in
          combine_list_opt r1 r2
      | ConjStar x ->
          let r1 = search_in_heap_formula search_hf x.CF.h_formula_conjstar_h1 in
          let r2 = search_in_heap_formula search_hf x.CF.h_formula_conjstar_h2 in
          combine_list_opt r1 r2
      | ConjConj x ->
          let r1 = search_in_heap_formula search_hf x.CF.h_formula_conjconj_h1 in
          let r2 = search_in_heap_formula search_hf x.CF.h_formula_conjconj_h2 in
          combine_list_opt r1 r2
      | Phase x ->
          let r1 = search_in_heap_formula search_hf x.CF.h_formula_phase_rd in
          let r2 = search_in_heap_formula search_hf x.CF.h_formula_phase_rw in
          combine_list_opt r1 r2
      | DataNode _ | ViewNode _ | ThreadNode _
      | HRel _ | Hole _ | FrmHole _
      | HTrue | HFalse | HEmp | HVar _ -> search_hf hf


and search_in_mix_formula (searcher: search_mix_formula_t) (mf: MCP.mix_formula)
    : search_res_t =
  match mf with
  | MCP.MemoF f -> search_in_memo_formula search_mf f
  | MCP.OnePF f -> search_in_pure_formula search_mf f


and search_in_memo_formula (searcher: search_memo_formula_t) (mf: MCPD.memo_pure)
    : search_res_t =
  let (search_m, search_a, search_f) = searcher in
  let search_b = snd search_f in
  let serach_e = snd serach_b in
  let res = search_m mf in
  match res with
  | Some res' -> res'
  | None ->
      let res_list = List.map (fun mg ->
        let res1 = search_in_pure_bformula search_b mg.MCPD.memo_formula in
        let res2 = search_in_pure_formula search_f mg.MCPD.memo_group_slide in
        let res3 = search_in_aset search_a mg.MCPD.memo_group_aset in
        combine_search_result_list [res1; res2; res3]
      ) mf in
      List.concat res_list 

and search_in_pure_formula (seacher: search_pure_formula_t) (f: CP.formula)
    : search_res_t =
  let (search_f, (search_bf, search_e)) = searcher in
  let res = search_f f in
  match res with
  | Some res' -> res'
  | None ->
      match f with
      | CP.BForm (bf, _) ->
          search_in_pure_bformula search_bf bf
      | CP.And (f1, f2, _) ->
          let r1 = search_in_pure_formula searcher f1 in
          let r2 = search_in_pure_formula searcher f2 in
          combine_search_results r1 r2 
      | CP.AndList f_list ->
          let res_list = List.map (fun (_,f) ->
            search_in_pure_formula searcher f
          ) f_list in
          List.concat res_list
      | CP.Or (f1, f2, _, _) ->
          let r1 = search_in_pure_formula searcher f1 in
          let r2 = search_in_pure_formula searcher f2 in
          combine_search_results r1 r2
      | CP.Not (f, _, _)
      | CP.Forall (_, f, _, _)
      | CP.Exists (_, f, _, _) ->
          search_in_pure_formula searcher f


and search_in_pure_bformula (searcher: search_pure_bformula_t) (f: CP.b_formula)
    : search_res_t =
  let (search_bf, search_e) = searcher in
  let res = search_bf f in
  match res with
  | Some res' -> res'
  | None ->
      let pf = fst f in
      match pf with
      | CP.Frm _ | CP.XPure _ | CP.BConst _ | CP.BVar _ -> []
      | CP.BagMin _ | CP.BagMax _ | CP.VarPerm _ -> []
      | CP.LexVar lvar ->
          let r1_list = List.map (search_in_pure_exp search_e) lvar.lex_exp in
          let r1 = List.concat r1_list in
          let r2_list = List.map (search_in_pure_exp search_e) lvar.lex_tmp in
          let r2 = List.concat r2_list in
          combine_search_result r1 r2
      | CP.Lt (e1, e2, _) | CP.Lte (e1, e2, _)
      | CP.Gt (e1, e2, _) | CP.Gte (e1, e2, _)
      | CP.Eq (e1, e2, _) | CP.Neq (e1, e2, _)
      | CP.SubAnn (e1, e2, _) | CP.BagSub (e1, e2, _)
      | CP.ListIn (e1, e2, _) | CP.ListNotIn (e1, e2, _)
      | CP.ListAllN (e1, e2, _) | CP.ListPerm (e1, e2, _) ->
          let r1 = search_in_pure_exp search_e e1 in
          let r2 = search_in_pure_exp search_e e2 in
          combine_search_result r1 r2
      | CP.EqMax (e1, e2, e3, _) | CP.EqMin (e1, e2, e3, _)  ->
          let r1 = search_in_pure_exp search_e e1 in
          let r2 = search_in_pure_exp search_e e2 in
          let r3 = search_in_pure_exp search_e e3 in
          combine_search_result_list [r1; r2; r3]
      | CP.BagIn (_, e, _) | CP.BagNotIn (_, e, _) ->
          search_in_pure_exp search_e e
      | CP.RelForm (_, elist, _) ->
          let r_list = List.map (search_in_pure_exp search_e) elist in
          List.concat r_list


and search_in_pure_exp (searcher: search_pure_exp_t) (e: CP.exp): search_res_t =
  let res = seacher e in
  match res with
  | Some res' -> res'
  | None ->
      match e with
      | CP.Null _ | CP.Var _ | CP.Level _
      | CP.IConst _ | CP.FConst _ | CP.AConst _
      | CP.InfConst _ | CP.Tsconst _ | CP.Bptriple _ ->
          []
      | CP.Tup2 ((e1, e2), _)
      | CP.Add (e1, e2, _) | CP.Subtract (e1, e2, _)
      | CP.Mult (e1, e2, _) | CP.Div (e1, e2, _)
      | CP.Max (e1, e2, _) | CP.Min (e1, e2, _)
      | CP.BagDiff (e1, e2, _) | CP.ListCons (e1, e2, _) ->
          let r1 = search_in_pure_exp searcher e1 in
          let r2 = search_in_pure_exp searcher e2 in
          combine_search_result r1 r2
      | CP.TypeCast (_, e, _) | CP.ListHead (e, _) | CP.ListTail (e, _)
      | CP.ListLength (e, _) | CP.ListReverse (e, _) ->
          search_in_pure_exp searcher e
      | CP.Bag (e_list, _) | CP.BagUnion (e_list, _)
      | CP.BagIntersect (e_list, _)
      | CP.List (e_list, _) | CP.ListAppend (e_list, _)
      | CP.ArrayAt (_, e_list, _) | CP.Func (_, e_list, _) ->
          let r_list = List.map (search_in_pure_exp searcher) e_list in
          List.concat r_list
      | CP.Template tpl ->
          let r1_list = List.map (search_in_pure_exp searcher) tpl.templ_args in
          let r1 = List.concat r1_list in
          let r2_list = List.map (search_in_pure_exp searcher) tpl.templ_unks in
          let r2 = List.concat r2_list in
          let r3 = match tpl.body with
            | None -> []
            | Some e -> search_in_pure_exp searcher e in
          combin_search_result_list [r1; r2; r3]
