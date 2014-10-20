open Globals
open Debug
open Gen.Basic


module C = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module MCPD = Mcpure_D


let combine_list_opt (e1: 'a list opt) (e2: 'a list opt) : 'a list opt =
  match e1, e2 with
  | None, None -> None
  | Some _, None -> e1
  | None, Some _ -> e2
  | Some e1', Some e2' -> Some (e1' @ e2')

(*
 ************************
 * various search types
 ************************
 *)
type search_res_t = 'a list

and search_formula_t =
    (CF.formula -> search_res_t option)
  * search_heap_formula_t
  * search_mix_formula_t

and search_heap_formula_t = (CF.h_formula -> search_res_t option)

and search_mix_formula_t = 
    (MCPD.memo_pure -> search_res_t option)
  * (MCPD.var_aset -> search_res_t option)
  * search_pure_formula_t
  * search_pure_bformula_t
  * search_pure_exp_t

and search_memo_formula_t = search_mix_formula_t

and search_pure_formula_t = (CP.formula -> search_res_t option) 

and search_pure_bformula_t = (CP.b_formula -> search_res_t option)

and search_pure_exp_t = (CP.exp -> search_res_t option)

let rec search_in_formula (searcher : search_formula_t) (f: CF.formula)
    : search_res_t =
  let (search_f, search_hf, search_mf) = searcher in
  let rec helper (search_f, search_hf, search_mf) f = (
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
  ) in
  helper (search_f, search_hf, search_mf) f


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
  let (search_m, search_a, search_f, search_b, search_e) = searcher in
  let res = search_m mf in
  match res with
  | Some res' -> res'
  | None ->
      (* memo_group_cons = List.map (fun c -> 
         {c with memo_formula = transform_b_formula (f_b_formula, f_exp) c.memo_formula}
        ) c.memo_group_cons; *)
      (* memo_group_slice = List.map (transform_formula f) c.memo_group_slice;                                                                        *)
      (* memo_group_aset = match (f_aset c.memo_group_aset) with | None -> c.memo_group_aset | Some s -> s;                                           *)

      List.concat (List.map (fun mg ->
        let res1 = search_in_pure_bformula
      ) mf) 

let transform_mix_formula f_p_t f = 
  match f with
    | MemoF f -> MemoF (transform_memo_formula f_p_t f)
    | OnePF f -> OnePF (transform_formula f_p_t f)
