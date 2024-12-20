open Hipsleek_common

type t =
  | Null
  | Var of Identifier.t
  | Intl of int
  | Floatl of float
  | Add of t * t
  | Sub of t * t
  | Mul of t * t
  | Div of t * t

let no_pos = Common_util.no_pos
let check_anon = Common_util.check_anon
let check_prime = Common_util.check_prime
let truncate_var = Common_util.truncate_var

let null = Null
let var s = Var s
let intl i = Intl i
let floatl f = Floatl f
let add a b = Add (a, b)
let sub a b = Sub (a, b)
let mul a b = Mul (a, b)
let div a b = Div (a, b)

let rec of_sleek_expr = function
  | Ipure_D.Null(_) -> Null
  | Ipure_D.Var(ident, _) -> Var (Identifier.of_sleek_ident ident)
  | Ipure_D.IConst(i, _) -> Intl(i)
  | Ipure_D.FConst(i, _) -> Floatl(i)
  | Ipure_D.Add(a, b, _) -> Add(of_sleek_expr a, of_sleek_expr b)
  | Ipure_D.Subtract(a, b, _) -> Sub(of_sleek_expr a, of_sleek_expr b)
  | Ipure_D.Mult(a, b, _) -> Mul(of_sleek_expr a, of_sleek_expr b)
  | Ipure_D.Div(a, b, _) -> Div(of_sleek_expr a, of_sleek_expr b)
  | _ -> failwith "Not supported"

let rec to_sleek_expr = function
  | Null -> Ipure_D.Null(no_pos)
  | Var(ident) -> Ipure_D.Var (Identifier.to_sleek_ident ident, no_pos)
  | Intl(i) -> Ipure_D.IConst(i, no_pos)
  | Floatl(f) -> Ipure_D.FConst(f, no_pos)
  | Add(a, b) -> Ipure_D.Add(to_sleek_expr a, to_sleek_expr b, no_pos)
  | Sub(a, b) -> Ipure.Subtract(to_sleek_expr a, to_sleek_expr b, no_pos)
  | Mul(a, b) -> Ipure_D.Mult(to_sleek_expr a, to_sleek_expr b, no_pos)
  | Div(a, b) -> Ipure_D.Div(to_sleek_expr a, to_sleek_expr b, no_pos)
