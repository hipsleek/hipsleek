open Globals
open Debug
open Gen.Basic


module C = Cast
module CP = Cpure
module CF = Cformula
module I = Iast
module IP = Ipure
module IF = Iformula
module MCP = Mcpure
module MCPD = Mcpure_D


(*
 ************************
 * various search types
 ************************
 *)
type 'a search_formula_t = (CF.formula -> 'a list option)
                       * 'a search_heap_formula_t
                       * 'a search_mix_formula_t

and 'a search_heap_formula_t = (CF.h_formula -> 'a list option)

and 'a search_mix_formula_t = 'a search_memo_pure_t
                           * 'a search_var_aset_t
                           * 'a search_pure_formula_t

and 'a search_memo_formula_t = 'a search_mix_formula_t

and 'a search_memo_pure_t = (MCPD.memo_pure -> 'a list option)

and 'a search_var_aset_t = (MCPD.var_aset -> 'a list option)

and 'a search_pure_formula_t = (CP.formula -> 'a list option)
                            * 'a search_pure_bformula_t 

and 'a search_pure_bformula_t = (CP.b_formula -> 'a list option)
                             * 'a search_pure_exp_t

and 'a search_pure_exp_t = (CP.exp -> 'a list option)


let rec create_default_formula_searcher (go_down: bool) : 'a search_formula_t =
  let search_f f = if (go_down) then None else (Some []) in
  let search_hf = create_default_heap_formula_searcher go_down in
  let search_mf = create_default_mix_formula_searcher go_down in
  (search_f, search_hf, search_mf)


and create_default_heap_formula_searcher (go_down: bool) : 'a search_heap_formula_t =
  if go_down then (fun _ -> None) else (fun _ -> Some [])


and create_default_mix_formula_searcher (go_down: bool) : 'a search_mix_formula_t =
  let search_m = create_default_memo_pure_searcher go_down in
  let search_a = create_default_var_aset_searcher go_down in
  let search_p = create_default_pure_formula_searcher go_down in
  (search_m, search_a, search_p)


and create_default_memo_formula_searcher (go_down: bool) : 'a search_memo_formula_t =
  create_default_mix_formula_searcher go_down


and create_default_memo_pure_searcher (go_down: bool) : 'a search_memo_pure_t =
  if go_down then (fun _ -> None) else (fun _ -> Some [])


and create_default_var_aset_searcher (go_down: bool) : 'a search_var_aset_t =
  if (go_down) then (fun _ -> None) else (fun _ -> Some [])


and create_default_pure_formula_searcher (go_down: bool) : 'a search_pure_formula_t = 
  let search_pf pf = if go_down then None else (Some []) in
  let search_bf = create_default_pure_bformula_searcher go_down in
  (search_pf, search_bf)


and create_default_pure_bformula_searcher (go_down: bool) : 'a search_pure_bformula_t =
  let search_bf bf = if go_down then None else (Some []) in
  let search_e = create_default_pure_exp_searcher go_down in
  (search_bf, search_e)


and create_default_pure_exp_searcher (go_down: bool) : 'a search_pure_exp_t =
  if go_down then (fun _ -> None) else (fun _ -> Some [])


let rec search_in_formula (search : 'a search_formula_t) (f: CF.formula)
    : 'a list =
  let (search_f, search_hf, search_mf) = search in
  let res = search_f f in
  match res with
  | Some res' -> res'
  | None -> 
      match f with
      | CF.Base x ->
          let r1 = search_in_heap_formula search_hf x.CF.formula_base_heap in
          let r2 = search_in_mix_formula search_mf x.CF.formula_base_pure in
          r1 @ r2
      | CF.Or x ->
          let r1 = search_in_formula search x.CF.formula_or_f1 in
          let r2 = search_in_formula search x.CF.formula_or_f2 in
          r1 @ r2
      | CF.Exists x -> 
          let r1 = search_in_heap_formula search_hf x.CF.formula_exists_heap in
          let r2 = search_in_mix_formula search_mf x.CF.formula_exists_pure in
          r1 @ r2


and search_in_heap_formula (search: 'a search_heap_formula_t) (f: CF.h_formula)
    : 'a list =
  let search_hf = search in
  let res = search_hf f in
  match res with
  | Some res' -> res'
  | None ->
      match f with
      | CF.Star x ->
          let r1 = search_in_heap_formula search x.CF.h_formula_star_h1 in
          let r2 = search_in_heap_formula search x.CF.h_formula_star_h2 in
          r1 @ r2
      | CF.StarMinus x ->
          let r1 = search_in_heap_formula search x.CF.h_formula_starminus_h1 in
          let r2 = search_in_heap_formula search x.CF.h_formula_starminus_h2 in
          r1 @ r2
      | CF.Conj x ->
          let r1 = search_in_heap_formula search x.CF.h_formula_conj_h1 in
          let r2 = search_in_heap_formula search x.CF.h_formula_conj_h2 in
          r1 @ r2
      | CF.ConjStar x ->
          let r1 = search_in_heap_formula search x.CF.h_formula_conjstar_h1 in
          let r2 = search_in_heap_formula search x.CF.h_formula_conjstar_h2 in
          r1 @ r2
      | CF.ConjConj x ->
          let r1 = search_in_heap_formula search x.CF.h_formula_conjconj_h1 in
          let r2 = search_in_heap_formula search x.CF.h_formula_conjconj_h2 in
          r1 @ r2
      | CF.Phase x ->
          let r1 = search_in_heap_formula search x.CF.h_formula_phase_rd in
          let r2 = search_in_heap_formula search x.CF.h_formula_phase_rw in
          r1 @ r2
      | CF.DataNode _ | CF.ViewNode _ | CF.ThreadNode _
      | CF.HRel _ | CF.Hole _ | CF.FrmHole _
      | CF.HTrue | CF.HFalse | CF.HEmp | CF.HVar _ ->
          []


and search_in_mix_formula (search: 'a search_mix_formula_t) (mf: MCP.mix_formula)
    : 'a list =
  let (_, _, search_f) = search in
  match mf with
  | MCP.MemoF f -> search_in_memo_formula search f
  | MCP.OnePF f -> search_in_pure_formula search_f f


and search_in_memo_formula (search: 'a search_memo_formula_t) (mf: MCPD.memo_pure)
    : 'a list =
  let (search_m, search_a, search_f) = search in
  let search_b = snd search_f in
  let res = search_m mf in
  match res with
  | Some res' -> res'
  | None ->
      let res_list = List.map (fun mg ->
        let res1_list = List.map (fun x -> 
            search_in_pure_bformula search_b x.MCPD.memo_formula
        ) mg.MCPD.memo_group_cons in
        let res1 = List.concat res1_list in
        let res2_list = List.map (fun x ->
          search_in_pure_formula search_f x
        ) mg.MCPD.memo_group_slice in
        let res2 = List.concat res2_list in
        let res3 = search_in_aset search_a mg.MCPD.memo_group_aset in
        res1 @ res2 @ res3
      ) mf in
      List.concat res_list   


and search_in_aset (search: 'a search_var_aset_t) (va: MCPD.var_aset)
    : 'a list =
  let res = search va in
  match res with
  | Some res' -> res'
  | None -> []


and search_in_pure_formula (search: 'a search_pure_formula_t) (f: CP.formula)
    : 'a list =
  let (search_f, search_bf) = search in
  let res = search_f f in
  match res with
  | Some res' -> res'
  | None ->
      match f with
      | CP.BForm (bf, _) ->
          search_in_pure_bformula search_bf bf
      | CP.And (f1, f2, _) ->
          let r1 = search_in_pure_formula search f1 in
          let r2 = search_in_pure_formula search f2 in
          r1 @ r2 
      | CP.AndList f_list ->
          let res_list = List.map (fun (_,f) ->
            search_in_pure_formula search f
          ) f_list in
          List.concat res_list
      | CP.Or (f1, f2, _, _) ->
          let r1 = search_in_pure_formula search f1 in
          let r2 = search_in_pure_formula search f2 in
          r1 @ r2
      | CP.Not (f, _, _)
      | CP.Forall (_, f, _, _)
      | CP.Exists (_, f, _, _) ->
          search_in_pure_formula search f


and search_in_pure_bformula (search: 'a search_pure_bformula_t) (f: CP.b_formula)
    : 'a list =
  let (search_bf, search_e) = search in
  let res = search_bf f in
  match res with
  | Some res' -> res'
  | None ->
      let pf = fst f in
      match pf with
      | CP.Frm _ | CP.XPure _ | CP.BConst _ | CP.BVar _
      | CP.BagMin _ | CP.BagMax _ | CP.VarPerm _ ->
          []
      | CP.LexVar lvar ->
          let r1_list = List.map (fun x -> 
            search_in_pure_exp search_e x
          ) lvar.CP.lex_exp in
          let r1 = List.concat r1_list in
          let r2_list = List.map (fun x -> 
            search_in_pure_exp search_e x
          ) lvar.CP.lex_tmp in
          let r2 = List.concat r2_list in
          r1 @ r2
      | CP.Lt (e1, e2, _) | CP.Lte (e1, e2, _)
      | CP.Gt (e1, e2, _) | CP.Gte (e1, e2, _)
      | CP.Eq (e1, e2, _) | CP.Neq (e1, e2, _)
      | CP.SubAnn (e1, e2, _) | CP.BagSub (e1, e2, _)
      | CP.ListIn (e1, e2, _) | CP.ListNotIn (e1, e2, _)
      | CP.ListAllN (e1, e2, _) | CP.ListPerm (e1, e2, _) ->
          let r1 = search_in_pure_exp search_e e1 in
          let r2 = search_in_pure_exp search_e e2 in
          r1 @ r2
      | CP.EqMax (e1, e2, e3, _) | CP.EqMin (e1, e2, e3, _)  ->
          let r1 = search_in_pure_exp search_e e1 in
          let r2 = search_in_pure_exp search_e e2 in
          let r3 = search_in_pure_exp search_e e3 in
          r1 @ r2 @ r3
      | CP.BagIn (_, e, _) | CP.BagNotIn (_, e, _) ->
          search_in_pure_exp search_e e
      | CP.RelForm (_, elist, _) ->
          let r_list = List.map (fun x ->
            search_in_pure_exp search_e x
          ) elist in
          List.concat r_list


and search_in_pure_exp (search: 'a search_pure_exp_t) (e: CP.exp): 'a list =
  let res = search e in
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
          let r1 = search_in_pure_exp search e1 in
          let r2 = search_in_pure_exp search e2 in
          r1 @ r2
      | CP.TypeCast (_, e, _) | CP.ListHead (e, _) | CP.ListTail (e, _)
      | CP.ListLength (e, _) | CP.ListReverse (e, _) ->
          search_in_pure_exp search e
      | CP.Bag (e_list, _) | CP.BagUnion (e_list, _)
      | CP.BagIntersect (e_list, _)
      | CP.List (e_list, _) | CP.ListAppend (e_list, _)
      | CP.ArrayAt (_, e_list, _) | CP.Func (_, e_list, _) ->
          let r_list = List.map (fun x -> 
            search_in_pure_exp search x
          ) e_list in
          List.concat r_list
      | CP.Template tpl ->
          let r1_list = List.map (fun x ->
            search_in_pure_exp search x
          ) tpl.CP.templ_args in
          let r1 = List.concat r1_list in
          let r2_list = List.map (fun x -> 
            search_in_pure_exp search x
          ) tpl.CP.templ_unks in
          let r2 = List.concat r2_list in
          let r3 = match tpl.CP.templ_body with
            | None -> []
            | Some x -> search_in_pure_exp search x in
          r1 @ r2 @ r3


(* let make_simple_view_decl (view_name: ident) (view_vars: ident list) *)
(*     (view_body: IF.struct_formula) (pos: loc)                        *)
(*     : CF.view_decl =                                                 *)
(*   let vdecl = {                                                      *)
(*     I.view_name = vn;                                                *)
(*     I.view_pos = pos;                                                *)
(*     I.view_data_name = "";                                           *)
(*     I.view_imm_map = [];                                             *)
(*     I.view_type_of_self = None;                                      *)
(*     I.view_vars = view_vars;                                         *)
(*     I.view_ho_vars = [];                                             *)
(*     I.view_labels = br_labels,has_labels;                            *)
(*     I.view_parent_name = None;                                       *)
(*     I.view_derv = false;                                             *)
(*     I.view_modes = [];                                               *)
(*     I.view_typed_vars = [];                                          *)
(*     I.view_pt_by_self  = [];                                         *)
(*     I.view_formula = view_formula;                                   *)
(*     I.view_inv_lock = None;                                          *)
(*     I.view_is_prim = false;                                          *)
(*     I.view_kind = View_EXTN;                                         *)
(*     I.view_prop_extns = [];                                          *)
(*     I.view_derv_info = [];                                           *)
(*     I.view_invariant = P.mkTrue (get_pos_camlp4 _loc 1);             *)
(*     I.view_baga_inv = None;                                          *)
(*     I.view_baga_over_inv = None;                                     *)
(*     I.view_baga_under_inv = None;                                    *)
(*     I.view_mem = None;                                               *)
(*     I.view_materialized_vars = [];                                   *)
(*     I.try_case_inference = false;                                    *)
(*   } in                                                               *)
(*   vdecl                                                              *)

