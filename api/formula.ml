type variable = 
    | Anonymous of string
    | Normal of string
    | Primed of string
  and pure_expr =
    | Null
    | Var of variable
    | Intl of int
    | Floatl of float
    | Add of pure_expr * pure_expr
    | Sub of pure_expr * pure_expr
    | Mul of pure_expr * pure_expr
    | Div of pure_expr * pure_expr
  and bin_predicate_kind =
    | GreaterThan
    | GreaterThanEq
    | LessThan
    | LessThanEq
    | Equal
  and pure_formula =
    | Constant of bool
    | BinPredicate of bin_predicate_kind * pure_expr * pure_expr
    | Not of pure_formula
    | And of pure_formula * pure_formula
    | Or of pure_formula * pure_formula
  and heap_formula =
  | Empty
  | PointsTo of variable * string * pure_expr list
  | SepConj of heap_formula * heap_formula
  and meta_formula = {meta_heap : heap_formula; meta_pure : pure_formula}
  and structured_meta_formula = {structured_heap : heap_formula; structured_pure : pure_formula}
  [@@deriving show]

module Identifier = struct
  type t = variable
  let make s = Normal s
  let anon () = Anonymous (Hipsleek_common.Globals.fresh_trailer ())
  let primed s = Primed s

  let is_primed = function
    | Primed _ -> true
    | _ -> false

  let is_anon = function
    | Anonymous  _ -> true
    | _ -> false

  let to_string = function
    | Anonymous s -> Printf.sprintf "[anon var %s]" s
    | Normal s -> s
    | Primed s -> s ^ "'"

  let to_sleek_ident = function
    | Anonymous s | Normal s -> (s, Hipsleek_common.VarGen.Unprimed)
    | Primed s -> (s, Hipsleek_common.VarGen.Primed)

  let of_sleek_spec_var spec_var =
    let open Hipsleek_common in
    match spec_var with
    | Cpure.SpecVar (_, name, VarGen.Primed) -> Primed name
    | Cpure.SpecVar (_, name, VarGen.Unprimed) when String.starts_with ~prefix:"Anon_" name -> Anonymous name
    | Cpure.SpecVar (_, name, VarGen.Unprimed) -> Normal name
end


module Pure_expression = struct
  open Hipsleek_common
  type t = pure_expr
  let no_pos = Common_util.no_pos

  let null = Null
  let var s = Var s
  let intl i = Intl i
  let floatl f = Floatl f
  let add a b = Add (a, b)
  let sub a b = Sub (a, b)
  let mul a b = Mul (a, b)
  let div a b = Div (a, b)

  let rec of_sleek_cexpr = function
    | Cpure.Null(_) -> Null
    | Cpure.Var(ident, _) -> Var (Identifier.of_sleek_spec_var ident)
    | Cpure.IConst(i, _) -> Intl(i)
    | Cpure.FConst(i, _) -> Floatl(i)
    | Cpure.Add(a, b, _) -> Add(of_sleek_cexpr a, of_sleek_cexpr b)
    | Cpure.Subtract(a, b, _) -> Sub(of_sleek_cexpr a, of_sleek_cexpr b)
    | Cpure.Mult(a, b, _) -> Mul(of_sleek_cexpr a, of_sleek_cexpr b)
    | Cpure.Div(a, b, _) -> Div(of_sleek_cexpr a, of_sleek_cexpr b)
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
end

module Pure_formula = struct
  type t = pure_formula
  open Hipsleek_common
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

  let not_f f = Not f
  let and_f lhs rhs = And (lhs, rhs)
  let or_f lhs rhs = Or (lhs, rhs)
  let implies lhs rhs = Or (Not lhs, rhs)
  let iff lhs rhs = And (implies lhs rhs, implies rhs lhs)

  let rec of_sleek_cformula =
    let of_expr = Pure_expression.of_sleek_cexpr in
    function
    | Cpure.Not (f, _, _) -> Not (of_sleek_cformula f)
    | Cpure.And (lhs, rhs, _) -> And (of_sleek_cformula lhs, of_sleek_cformula rhs)
    | Cpure.Or (lhs, rhs, _, _) -> Or (of_sleek_cformula lhs, of_sleek_cformula rhs)
    | Cpure.BForm ((Cpure.BConst (true, _), _), _) -> Constant (true)
    | Cpure.BForm ((Cpure.BConst (false, _), _), _) -> Constant (false)
    | Cpure.BForm ((Cpure.Gt (lhs, rhs, _), _), _) -> BinPredicate (GreaterThan, of_expr lhs, of_expr rhs)
    | Cpure.BForm ((Cpure.Gte (lhs, rhs, _), _), _) -> BinPredicate (GreaterThanEq, of_expr lhs, of_expr rhs)
    | Cpure.BForm ((Cpure.Lt (lhs, rhs, _), _), _) -> BinPredicate (LessThan, of_expr lhs, of_expr rhs)
    | Cpure.BForm ((Cpure.Lte (lhs, rhs, _), _), _) -> BinPredicate (LessThanEq, of_expr lhs, of_expr rhs)
    | Cpure.BForm ((Cpure.Eq (lhs, rhs, _), _), _) -> BinPredicate (Equal, of_expr lhs, of_expr rhs)
    | unknown -> raise (Invalid_argument ("Unknown SLEEK pure formula: " ^ (Cprinter.string_of_pure_formula unknown)))
end

module Heap_formula = struct
  open Hipsleek_common
  open Common_util
  type t = heap_formula

  let emp = Empty

  let int_pointer_view = "int_ptr"
  let points_to ident view fields = PointsTo (ident, view, fields)
  let points_to_int ident n = points_to ident int_pointer_view [Pure_expression.intl n]

  let sep lhs rhs = SepConj (lhs, rhs)
  (* Heap formulae *)
  let rec to_sleek_formula = function
    | Empty -> Iformula.HEmp
    | SepConj (lhs, rhs) -> Iformula.mkStar (to_sleek_formula lhs) (to_sleek_formula rhs) no_pos
    | PointsTo (ident, view, fields) ->
      let imm_param = List.map (fun _ -> None) fields in
      Iformula.mkHeapNode_x (Identifier.to_sleek_ident ident) view [] 0 false
        Globals.SPLIT0 Ipure_D.NoAnn false false false None (List.map Pure_expression.to_sleek_expr fields) imm_param None no_pos

  let rec of_sleek_cformula = function
    | Cformula.HEmp -> Empty
    | Cformula.Star {h_formula_star_h1 = lhs; h_formula_star_h2 = rhs; _} -> sep (of_sleek_cformula lhs) (of_sleek_cformula rhs)
    (* This handling is mostly taken from Cprinter.pr_h_formula. *)
    | Cformula.DataNode {h_formula_data_node; h_formula_data_name; h_formula_data_arguments; _} ->
        let var_names = List.map (fun spec_var -> Pure_expression.var (Identifier.of_sleek_spec_var spec_var)) h_formula_data_arguments in
        points_to (Identifier.of_sleek_spec_var h_formula_data_node)
          h_formula_data_name
          var_names
    | Cformula.ViewNode {h_formula_view_node; h_formula_view_name; h_formula_view_arguments; _} ->
        let var_names = List.map (fun spec_var -> Pure_expression.var (Identifier.of_sleek_spec_var spec_var)) h_formula_view_arguments in
        points_to (Identifier.of_sleek_spec_var h_formula_view_node)
          h_formula_view_name
          var_names
    | unknown -> raise (Invalid_argument ("Unknown SLEEK heap formula: " ^ (Cprinter.string_of_h_formula unknown)))
end

open Hipsleek_common


(* This API currently does not expose some underlying features of the prover, including:
   - Variable permissions
   - Flow constraints
   - Structured specifications (for consequents)
*)

module Meta_formula = struct
  type t = meta_formula
  let of_heap_and_pure meta_heap meta_pure = {meta_heap; meta_pure}
  let to_sleek_formula {meta_heap; meta_pure} =
    let open Iformula in
    Iformula.Base({
      formula_base_heap = Heap_formula.to_sleek_formula meta_heap;
      formula_base_pure = Pure_formula.to_sleek_formula meta_pure;
      formula_base_vperm = IvpermUtils.empty_vperm_sets;
      formula_base_flow = "__norm";
      formula_base_and = [];
      formula_base_pos = Common_util.no_pos})

  let of_sleek_cformula = function
    | Cformula.Base({ formula_base_heap; formula_base_pure = OnePF pure_f; _ }) ->
        of_heap_and_pure (Heap_formula.of_sleek_cformula formula_base_heap) (Pure_formula.of_sleek_cformula pure_f)
    | unknown -> raise (Invalid_argument ("Unknown SLEEK meta formula: "^ (Cprinter.string_of_formula unknown)))

  let pp = pp_meta_formula
end

module Structured = struct
  type t = structured_meta_formula
  let of_heap_and_pure structured_heap structured_pure = {structured_heap; structured_pure}

  let to_sleek_formula {structured_heap; structured_pure} =
    let base_formula = Meta_formula.to_sleek_formula (Meta_formula.of_heap_and_pure structured_heap structured_pure) in
    Iformula.EBase {Iformula.formula_struc_explicit_inst = [];
      Iformula.formula_struc_implicit_inst = [];
      Iformula.formula_struc_exists = [];
      Iformula.formula_struc_base = base_formula;
      Iformula.formula_struc_is_requires = false; (* Not sure what this is *)
      Iformula.formula_struc_continuation = None;
      Iformula.formula_struc_pos = Common_util.no_pos}

end
