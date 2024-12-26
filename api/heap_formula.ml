open Hipsleek_common
open Common_util

type t =
  | Empty
  | PointsTo of Identifier.t * string * Pure_expression.t list
  | SepConj of t * t

let emp = Empty
let points_to ident view fields = PointsTo (ident, view, fields)
let points_to_int ident n = points_to ident "int_ptr" [Pure_expression.intl n]

let sep lhs rhs = SepConj (lhs, rhs)

let rec to_sleek_formula = function
  | Empty -> Iformula.HEmp
  | SepConj (lhs, rhs) -> Iformula.mkStar (to_sleek_formula lhs) (to_sleek_formula rhs) no_pos
  | PointsTo (ident, view, fields) ->
    let imm_param = List.map (fun _ -> None) fields in
    Iformula.mkHeapNode_x (Identifier.to_sleek_ident ident) view [] 0 false
      Globals.SPLIT0 Ipure_D.NoAnn false false false None (List.map Pure_expression.to_sleek_expr fields) imm_param None no_pos

let rec of_sleek_formula = function
  | Iformula.HEmp -> Empty
  | Iformula.Star {h_formula_star_h1 = lhs; h_formula_star_h2 = rhs; _} -> sep (of_sleek_formula lhs) (of_sleek_formula rhs)
  | Iformula.HeapNode {h_formula_heap_node = ident;
    h_formula_heap_name = view;
    h_formula_heap_arguments = fields; _} -> PointsTo (Identifier.of_sleek_ident ident, view, List.map Pure_expression.of_sleek_expr fields)
  | _ -> failwith "Unsupported SLEEK heap formula found" (* TODO more descriptive error message *)


