open Hipsleek_common
open Common_util

type t = Iformula.h_formula

(* Building heap formula *)
let empty_heap_f = Iformula.HEmp
let false_heap_f = Iformula.HFalse
let true_heap_f  = Iformula.HTrue

let sep_conj_f h1 h2 = Iformula.mkStar h1 h2 no_pos

let points_to_int_f var_name i =
  Iformula.mkHeapNode_x (Identifier.to_sleek_ident var_name) "int_ptr" [] 0 false Globals.SPLIT0
    Ipure_D.NoAnn false false false None [Pure_expression.(to_sleek_expr (intl i))] [None] None no_pos

let points_to_f var_name ident exps =
  let imm_param = List.map (fun _ -> None) exps in
  Iformula.mkHeapNode_x (Identifier.to_sleek_ident var_name) ident [] 0 false
    Globals.SPLIT0 Ipure_D.NoAnn false false false None (List.map Pure_expression.to_sleek_expr exps) imm_param None no_pos

let emp = empty_heap_f
let true_h = true_heap_f
let false_h = false_heap_f

let sep = sep_conj_f

let points_to_int = points_to_int_f
let points_to = points_to_f

let to_sleek_formula f = f
let of_sleek_formula f = f
