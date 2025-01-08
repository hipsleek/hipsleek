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
  and base_formula = {base_heap : heap_formula; base_pure : pure_formula}
  and meta_formula = (variable list * base_formula) list
  (** Internally, meta formulas are represented as a disjunction of base_formulas,
  where each base formula may have an associated list of existentially quantified variables. *)
  and structured_meta_formula = {structured_base: meta_formula}
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

let no_pos = Common_util.no_pos

module Pure_expression = struct
  open Hipsleek_common
  type t = pure_expr

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

  let rec to_string = function
    | Null -> "null"
    | Var(ident) -> Identifier.to_string ident
    | Intl(i) -> string_of_int i
    | Floatl(f) -> string_of_float f
    | Add (a, b) -> Format.sprintf "(%s + %s)" (to_string a) (to_string b)
    | Sub (a, b) -> Format.sprintf "(%s - %s)" (to_string a) (to_string b)
    | Mul (a, b) -> Format.sprintf "(%s * %s)" (to_string a) (to_string b)
    | Div (a, b) -> Format.sprintf "(%s / %s)" (to_string a) (to_string b)
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
    | Cpure.And (lhs, rhs, _) -> And (of_sleek_cformula lhs, of_sleek_cformula rhs) | Cpure.Or (lhs, rhs, _, _) -> Or (of_sleek_cformula lhs, of_sleek_cformula rhs) | Cpure.BForm ((Cpure.BConst (true, _), _), _) -> Constant (true) | Cpure.BForm ((Cpure.BConst (false, _), _), _) -> Constant (false) | Cpure.BForm ((Cpure.Gt (lhs, rhs, _), _), _) -> BinPredicate (GreaterThan, of_expr lhs, of_expr rhs)
    | Cpure.BForm ((Cpure.Gte (lhs, rhs, _), _), _) -> BinPredicate (GreaterThanEq, of_expr lhs, of_expr rhs)
    | Cpure.BForm ((Cpure.Lt (lhs, rhs, _), _), _) -> BinPredicate (LessThan, of_expr lhs, of_expr rhs)
    | Cpure.BForm ((Cpure.Lte (lhs, rhs, _), _), _) -> BinPredicate (LessThanEq, of_expr lhs, of_expr rhs)
    | Cpure.BForm ((Cpure.Eq (lhs, rhs, _), _), _) -> BinPredicate (Equal, of_expr lhs, of_expr rhs)
    | unknown -> raise (Invalid_argument ("Unknown SLEEK pure formula: " ^ (Cprinter.string_of_pure_formula unknown)))

  let rec to_string = function
    | Constant true -> "true"
    | Constant false -> "false"
    | BinPredicate (pred, lhs, rhs) ->
        let pred_string = match pred with
          | GreaterThan -> ">"
          | GreaterThanEq -> ">="
          | LessThan -> "<"
          | LessThanEq -> "<="
          | Equal -> "=" in
        Format.sprintf "(%s %s %s)" (Pure_expression.to_string lhs) pred_string (Pure_expression.to_string rhs)
    | Not f -> "~"^(to_string f)
    | And (lhs, rhs) -> Format.sprintf "(%s & %s)" (to_string lhs) (to_string rhs)
    | Or (lhs, rhs) -> Format.sprintf "(%s | %s)" (to_string lhs) (to_string rhs)
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

  let rec to_string = function
    | Empty -> "emp"
    | SepConj (lhs, rhs) -> Format.sprintf "%s * %s" (to_string lhs) (to_string rhs)
    | PointsTo (ident, view, fields) ->
        let field_list = String.concat ", " (List.map Pure_expression.to_string fields) in
        Format.sprintf "%s::%s<%s>" (Identifier.to_string ident) view field_list
end

open Hipsleek_common


(* This API currently does not expose some underlying features of the prover, including:
   - Variable permissions
   - Flow constraints
   - Structured specifications (for consequents)
*)

module Base_formula = struct
  type t = base_formula

  let make ~heap ~pure = {base_heap = heap; base_pure = pure}
  let to_sleek_formula {base_heap; base_pure} =
    let open Iformula in
    {
      formula_base_heap = Heap_formula.to_sleek_formula base_heap;
      formula_base_pure = Pure_formula.to_sleek_formula base_pure;
      formula_base_vperm = IvpermUtils.empty_vperm_sets;
      formula_base_flow = "__norm";
      formula_base_and = [];
      formula_base_pos = Common_util.no_pos
  }

  let of_sleek_cformula cf =
    let open Cformula in
    match cf with
      | {formula_base_pure = OnePF pure_f;
        formula_base_heap = heap_f; _ } ->
        make ~heap:(Heap_formula.of_sleek_cformula heap_f)
          ~pure:(Pure_formula.of_sleek_cformula pure_f)
      | _ -> raise (Invalid_argument "Converting memoized formulas to API type is unsupported")

  let heap_formula {base_heap; _} = base_heap
  let pure_formula {base_pure; _} = base_pure

  let empty = make ~heap:Heap_formula.emp ~pure:Pure_formula.true_f
  let to_string {base_heap; base_pure} = Format.sprintf "%s & (%s)" (Pure_formula.to_string base_pure) (Heap_formula.to_string base_heap)
end

module Meta_formula = struct
  type t = meta_formula
  let of_base base = [([], base)]
  let make ~heap ~pure = of_base (Base_formula.make ~heap ~pure)

  let exists qvars base = [(qvars, base)]
  let disjunction = List.concat
  let to_list f = f

  let rec to_sleek_formula mf =
    let convert_one = function
      | ([], base) -> Iformula.Base(Base_formula.to_sleek_formula base)
      | (quantified, base) ->
        let sleek_base = Base_formula.to_sleek_formula base in
        Iformula.Exists({
            formula_exists_qvars = List.map Identifier.to_sleek_ident quantified;
            formula_exists_heap = sleek_base.formula_base_heap;
            formula_exists_pure = sleek_base.formula_base_pure;
            formula_exists_vperm = sleek_base.formula_base_vperm;
            formula_exists_flow = sleek_base.formula_base_flow;
            formula_exists_and = sleek_base.formula_base_and;
            formula_exists_pos = sleek_base.formula_base_pos})
    in
    match mf with
    | [] -> convert_one ([], Base_formula.empty)
    | [one] -> convert_one one
    | x::xs -> Iformula.Or({
      formula_or_f1 = convert_one x;
      formula_or_f2 = to_sleek_formula xs;
      formula_or_pos = no_pos
  })

  let of_sleek_cformula = function
    | Cformula.Base({ formula_base_heap; formula_base_pure = OnePF pure_f; _ }) ->
        make ~heap:(Heap_formula.of_sleek_cformula formula_base_heap) ~pure:(Pure_formula.of_sleek_cformula pure_f)
    | unknown -> raise (Invalid_argument ("Unknown SLEEK meta formula: "^ (Cprinter.string_of_formula unknown)))

  let pp = pp_meta_formula
  let to_string mf =
    let convert_one = function
      | ([], base) -> Base_formula.to_string base
      | (quantified, base) ->
          let var_list = String.concat ", " (List.map Identifier.to_string quantified) in
          Format.sprintf "exists (%s): %s" var_list (Base_formula.to_string base)
    in
    String.concat " | " (List.map convert_one mf)
end

module Structured = struct
  type t = structured_meta_formula
  let of_meta structured_base = {structured_base}
  let make ~heap ~pure = of_meta (Meta_formula.make ~heap ~pure)

  let to_sleek_formula {structured_base} =
    Iformula.EBase {Iformula.formula_struc_explicit_inst = [];
      Iformula.formula_struc_implicit_inst = [];
      Iformula.formula_struc_exists = [];
      Iformula.formula_struc_base = Meta_formula.to_sleek_formula structured_base;
      Iformula.formula_struc_is_requires = false; (* Not sure what this is *)
      Iformula.formula_struc_continuation = None;
      Iformula.formula_struc_pos = Common_util.no_pos}

  let to_string {structured_base} = Meta_formula.to_string structured_base
end
