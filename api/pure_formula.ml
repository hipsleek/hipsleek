open Hipsleek_common

type t = Hipsleek_common.Ipure_D.formula
let no_pos = Common_util.no_pos
let to_expr = Pure_expression.to_sleek_expr

type bin_predicate_kind =
  | GreaterThan
  | GreaterThanEq
  | LessThan
  | LessThanEq
  | Equal

type t =
  | Constant of bool
  | BinPredicate of bin_predicate_kind * Pure_expression.t * Pure_expression.t
  | Not of t
  | And of t * t
  | Or of t * t

let true_f = Constant true
let false_f = Constant false

let gt lhs rhs = BinPredicate(GreaterThan, lhs, rhs)
let gte lhs rhs = BinPredicate(GreaterThanEq, lhs, rhs)
let lt lhs rhs = BinPredicate(LessThan, lhs, rhs)
let lte lhs rhs = BinPredicate(LessThanEq, lhs, rhs)
let eq lhs rhs = BinPredicate(Equal, lhs, rhs)

let rec to_sleek_formula =
  let no_pos = Common_util.no_pos in
  let to_expr = Pure_expression.to_sleek_expr in
  let bool_pure_f bool = Ipure_D.BForm ((Ipure_D.BConst (bool, no_pos), None), None) in
  function
    | Constant true -> bool_pure_f true
    | Constant false -> bool_pure_f false
    | BinPredicate (GreaterThan, lhs, rhs) -> Ipure_D.BForm ((Ipure_D.Gt (to_expr lhs, to_expr rhs, no_pos), None), None)
    | BinPredicate (GreaterThanEq, lhs, rhs) -> Ipure_D.BForm ((Ipure_D.Gte (to_expr lhs, to_expr rhs, no_pos), None), None)
    | BinPredicate (LessThan, lhs, rhs) -> Ipure_D.BForm ((Ipure_D.Lt (to_expr lhs, to_expr rhs, no_pos), None), None)
    | BinPredicate (LessThanEq, lhs, rhs) -> Ipure_D.BForm ((Ipure_D.Lte (to_expr lhs, to_expr rhs, no_pos), None), None)
    | BinPredicate (Equal, lhs, rhs) -> Ipure_D.BForm ((Ipure_D.Eq (to_expr lhs, to_expr rhs, no_pos), None), None)
    | Not f -> Ipure_D.Not (to_sleek_formula f, None, no_pos)
    | And (lhs, rhs) -> Ipure_D.And (to_sleek_formula lhs, to_sleek_formula rhs, no_pos)
    | Or (lhs, rhs) -> Ipure_D.Or (to_sleek_formula lhs, to_sleek_formula rhs, None, no_pos)

let rec of_sleek_formula = 
  let of_expr = Pure_expression.of_sleek_expr in
  function
  | Ipure_D.Not (f, _, _) -> Not (of_sleek_formula f)
  | Ipure_D.And (lhs, rhs, _) -> And (of_sleek_formula lhs, of_sleek_formula rhs)
  | Ipure_D.Or (lhs, rhs, _, _) -> Or (of_sleek_formula lhs, of_sleek_formula rhs)
  | Ipure_D.BForm ((Ipure_D.BConst (true, _), _), _) -> Constant (true)
  | Ipure_D.BForm ((Ipure_D.BConst (false, _), _), _) -> Constant (false)
  | Ipure_D.BForm ((Ipure_D.Gt (lhs, rhs, _), _), _) -> BinPredicate (GreaterThan, of_expr lhs, of_expr rhs)
  | Ipure_D.BForm ((Ipure_D.Gte (lhs, rhs, _), _), _) -> BinPredicate (GreaterThanEq, of_expr lhs, of_expr rhs)
  | Ipure_D.BForm ((Ipure_D.Lt (lhs, rhs, _), _), _) -> BinPredicate (LessThan, of_expr lhs, of_expr rhs)
  | Ipure_D.BForm ((Ipure_D.Lte (lhs, rhs, _), _), _) -> BinPredicate (LessThanEq, of_expr lhs, of_expr rhs)
  | Ipure_D.BForm ((Ipure_D.Eq (lhs, rhs, _), _), _) -> BinPredicate (Equal, of_expr lhs, of_expr rhs)
  | Ipure_D.BForm (_, _) -> failwith "Converted SLEEK formula with unsupported boolean formula" (* TODO more error info *)
  | _ -> failwith "Converted SLEEK formula with unsupported connective" (* TODO more error info *)
