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

let rec of_sleek_cformula = function
  | Cformula.HEmp -> Empty
  | Cformula.Star {h_formula_star_h1 = lhs; h_formula_star_h2 = rhs; _} -> sep (of_sleek_cformula lhs) (of_sleek_cformula rhs)
  (* This handling is mostly taken from Cprinter.pr_h_formula. *)
  | Cformula.DataNode {h_formula_data_node; h_formula_data_name; h_formula_data_arguments; _} ->
      let var_names = List.map (fun spec_var -> Pure_expression.var (Identifier.of_sleek_spec_var spec_var)) h_formula_data_arguments in
      points_to (Identifier.of_sleek_spec_var h_formula_data_node)
        h_formula_data_name
        var_names
  | Cformula.ViewNode _ -> failwith "TODO: Implement of_sleek_cformula on ViewNodes"
  | _ -> failwith "Unsupported SLEEK heap formula found" (* TODO more descriptive error message *)
