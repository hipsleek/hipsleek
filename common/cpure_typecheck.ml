(**
   We want to implement some sort of type inference for Cpure.exps
   Options:
     - Implement a second type, typed_exp or something
     - Annotate using a hashmap from AST nodes to types*)

(** FIXME see how much of the currently 'unsupported' expressions we can implement *)



type loc = VarGen.loc [@opaque]
and spec_var = Cpure.spec_var [@opaque]
and ident = Globals.ident [@opaque]
and heap_ann = Globals.heap_ann [@opaque]
and typ = (* TODO translate to a Globals.typ) *)
  | Bool
  | Int
  | ListT of typ
  | TVar of int

  (* | Prim of prim_type *)
(* The following is a replica of types that represent the AST of Cpure.formulas,
   with a type parameter to support annotations. We use this annotation to store
   inferred types.*)
and 'a exp =
  | Null of loc
  | Var of (spec_var * loc)
    (* 'a *)
  | IConst of (int * loc)
    (* int *)
  | FConst of (float * loc)
  | Add of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Subtract of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Mult of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Div of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Max of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Min of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  (* 'a list, forces arguments to be 'a *)
  | List of ('a exp_annot list * loc)
  | ListCons of ('a exp_annot * 'a exp_annot * loc) (* 'a -> 'a list -> 'a list *' *)
  | ListHead of ('a exp_annot * loc) (* 'a list -> 'a *)
  | ListTail of ('a exp_annot * loc) (* 'a list -> 'a list *)
  | ListLength of ('a exp_annot * loc) (* 'a list -> int *)
  | ListAppend of ('a exp_annot list * loc) (*'a list list -> 'a list? *)
  | ListReverse of ('a exp_annot * loc) (* 'a list -> 'a list *)
  (* | StrConst of (string * loc) *)
  (* | StrAppend of ('a exp_annot list * loc) *)
  | ArrayAt of (spec_var * ('a exp_annot list) * loc)      (* An Hoa : array access *)
  | Func of (spec_var * ('a exp_annot list) * loc) (* 'a -> 'b, forces body to be 'b and forces any arguments applied to be 'a *)
  (* Template 'a exp_annot *)
  | Template of 'a template
  and 'a template = {
    (* a + bx + cy + dz *)
    templ_id: spec_var;
    templ_args: 'a exp_annot list; (*    [x, y, z] *)
    templ_unks: 'a exp_annot list; (* [a, b, c, d] *)
    templ_body: 'a exp_annot option;
    templ_pos: loc;
  }
and 'a exp_annot = ('a exp * 'a)

(** While p_formulas and formulas can be all annotated as having type Bool, we allow annotations
    on them for completeness. *)
and 'a p_formula =
  | BConst of (bool * loc)
  | BVar of (spec_var * loc)
  | Lt of ('a exp_annot * 'a exp_annot * loc)
  | Lte of ('a exp_annot * 'a exp_annot * loc)
  | Gt of ('a exp_annot * 'a exp_annot * loc)
  | Gte of ('a exp_annot * 'a exp_annot * loc)
  | Eq of ('a exp_annot * 'a exp_annot * loc) (* these two could be arithmetic or pointer or bag or list *)
  | Neq of ('a exp_annot * 'a exp_annot * loc)
  | EqMax of ('a exp_annot * 'a exp_annot * 'a exp_annot * loc) (* first is max of second and third *)
  | EqMin of ('a exp_annot * 'a exp_annot * 'a exp_annot * loc) (* first is min of second and third *)
  (* bag formulas *)
  | BagIn of (spec_var * 'a exp_annot * loc)
  | BagNotIn of (spec_var * 'a exp_annot * loc)
  | BagSub of ('a exp_annot * 'a exp_annot * loc)
  | BagMin of (spec_var * spec_var * loc)
  | BagMax of (spec_var * spec_var * loc)

  | ListIn of ('a exp_annot * 'a exp_annot * loc)
  | ListNotIn of ('a exp_annot * 'a exp_annot * loc)
  | ListAllN of ('a exp_annot * 'a exp_annot * loc)
  | ListPerm of ('a exp_annot * 'a exp_annot * loc)
  | RelForm of (spec_var * ('a exp_annot list) * loc)
  | ImmRel of ('a p_formula_annot * 'a imm_ann * loc) (* RelForm * cond * pos *)
  and 'a imm_ann =
    | PostImm of 'a p_formula_annot  (* unknown precondition, need to be inferred *)
    | PreImm of 'a p_formula_annot (* unknown postcondition, need to be inferred *)
  and 'a p_formula_annot = ('a p_formula * 'a)
  and formula_label = int * string
  and 'a formula =
    | BForm of ('a b_formula_annot * (formula_label option))
    (* | Pure_Baga of (spec_var list) *)
    (* ADDR[a,b] <==> a>0 & b>0 > a!=b *)
    (* | BagaF of (spec_var list * 'a formula_annot) *)
    | And of ('a formula_annot * 'a formula_annot * loc)
    | Or of ('a formula_annot * 'a formula_annot * (formula_label option) * loc)
    | Not of ('a formula_annot * (formula_label option) * loc)
    | Forall of (spec_var * 'a formula_annot * (formula_label option) * loc)
    | Exists of (spec_var * 'a formula_annot * (formula_label option) * loc)

  (** This type is part of the untyped AST's own annotations. For the annotated b_formula, use b_formula_annot. *)
  and 'a bf_annot = (bool * int * ('a exp_annot list))
  and 'a b_formula = ('a p_formula_annot * ('a bf_annot option))
  and 'a b_formula_annot = ('a b_formula * 'a)
  and 'a formula_annot = ('a formula * 'a)
  [@@deriving visitors { variety = "reduce"; name = "reduce_formula"},
    visitors { variety = "endo"; name = "endo_formula"}]


  (** take in a Cpure.exp (or maybe a typ option exp to allow for partial annotations)
  compute all the unknown_typs of the AST nodes 
  compute a list of unification constraints from the unknown_typs
  solve the unification constraints
  use the solution to convert the unknown_typ exp into an typ exp *)

let rec equal_types (t1 : typ) (t2 : typ) : bool 
= match (t1, t2) with
  | (Bool, Bool) | (Int, Int) -> true
  | (TVar x, TVar y) -> x = y
  | (ListT t1, ListT t2) -> equal_types t1 t2
  | _ -> false

let rec string_of_typ = function
  | Bool -> "Bool"
  | Int -> "Int"
  | TVar x -> Format.sprintf "[var %d]" x
  | ListT t -> Format.sprintf "List<%s>" (string_of_typ t)

let pp_typ out typ = Format.fprintf out "%s" (string_of_typ typ)

let fresh_tvar =
  let id = ref 0 in
  fun () -> 
    let var_id = !id in
    id := !id + 1; TVar var_id

let rec annotate_cpure_exp (exp : Cpure.exp) : typ exp_annot =
  match exp with
  | Cpure.Var (var, loc) -> Var (var, loc), fresh_tvar ()
  | Cpure.IConst (n, loc) -> IConst (n, loc), Int
  | Cpure.Add (lhs, rhs, loc) -> Add (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), fresh_tvar ()
  | Cpure.Subtract (lhs, rhs, loc) -> Subtract (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), fresh_tvar ()
  | Cpure.Mult (lhs, rhs, loc) -> Mult (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), fresh_tvar ()
  | Cpure.Div (lhs, rhs, loc) -> Div (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), fresh_tvar ()
  | Cpure.List (vs, loc) -> List (List.map annotate_cpure_exp vs, loc), ListT (fresh_tvar ())
  | Cpure.ListCons (v, vs, loc) -> ListCons (annotate_cpure_exp v, annotate_cpure_exp vs, loc), ListT (fresh_tvar()) 
  | Cpure.ListTail (vs, loc) -> ListTail (annotate_cpure_exp vs, loc), ListT (fresh_tvar()) 
  | Cpure.ListLength (vs, loc) -> ListLength (annotate_cpure_exp vs, loc), Int
  | Cpure.ListAppend (vs, loc) -> ListAppend (List.map annotate_cpure_exp vs, loc), ListT (fresh_tvar ())
  | Cpure.ListReverse (vs, loc) -> ListReverse (annotate_cpure_exp vs, loc), ListT (fresh_tvar ())
  | _ -> failwith "Unsupported Cpure expression"

let annotate_cpure_p_formula (pf : Cpure.p_formula) : typ p_formula_annot =
  match pf with
  | Cpure.BConst data -> BConst data, Bool
  | Cpure.BVar data -> BVar data, Bool
  | Cpure.Lt (lhs, rhs, loc) -> Lt (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Bool
  | Cpure.Lte (lhs, rhs, loc) -> Lte (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Bool
  | Cpure.Gt (lhs, rhs, loc) -> Gt (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Bool
  | Cpure.Gte (lhs, rhs, loc) -> Gte (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Bool
  | Cpure.Eq (lhs, rhs, loc) -> Eq (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Bool
  | Cpure.Neq (lhs, rhs, loc) -> Neq (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Bool
  | Cpure.EqMax (lhs, rhs1, rhs2, loc) -> EqMax (annotate_cpure_exp lhs, annotate_cpure_exp rhs1, annotate_cpure_exp rhs2, loc), Bool
  | Cpure.EqMin (lhs, rhs1, rhs2, loc) -> EqMin (annotate_cpure_exp lhs, annotate_cpure_exp rhs1, annotate_cpure_exp rhs2, loc), Bool
  | _ -> failwith "Unsupported Cpure p_formula"

let annotate_cpure_b_formula (bf : Cpure.b_formula) : typ b_formula_annot =
  let annotate_subexprs (e1, e2, exprs : Cpure.bf_annot) = (e1, e2, List.map annotate_cpure_exp exprs) in
  let (pf, subannot) = bf in
  (annotate_cpure_p_formula pf, Option.map annotate_subexprs subannot), Bool

let rec annotate_cpure_formula (f : Cpure.formula) : typ formula_annot =
  match f with
  | Cpure.BForm (bf, label) -> BForm (annotate_cpure_b_formula bf, label), Bool
  | Cpure.And (lhs, rhs, loc) -> And (annotate_cpure_formula lhs, annotate_cpure_formula rhs, loc), Bool
  | Cpure.Or (lhs, rhs, label, loc) -> Or (annotate_cpure_formula lhs, annotate_cpure_formula rhs, label, loc), Bool
  | Cpure.Not (f, label, loc) -> Not (annotate_cpure_formula f, label, loc), Bool
  | Cpure.Forall (binder, f, label, loc) -> Forall (binder, annotate_cpure_formula f, label, loc), Bool
  | Cpure.Exists (binder, f, label, loc) -> Exists (binder, annotate_cpure_formula f, label, loc), Bool
  | _ -> failwith "Typechecker currently does not support Cpure.AndLists"

(** A constraint on two type variables during unification. Currently, only equality
    between two types is supported. *)
type unification_constr = typ * typ

(** Given a formula annotated with type variables, compute a list of consraints necessary
  for the type variables to represent a valid type assignment. *)
let get_constraints (typed_formula : typ formula_annot) : unification_constr list =
  let go = object

    inherit [_] reduce_formula as super

    method zero = []
    method plus = (@)
    method visit_'a _ _ = []

    method! visit_exp_annot env = function
      | List (items, _), list_typ -> 
        let subconstraints = items |> List.map (super#visit_exp_annot env) |> List.concat in
        let element_constraints = items |> List.map (fun (_, element_typ) -> (ListT element_typ, list_typ)) in
        element_constraints @ subconstraints
      | ListCons ((_, x_typ) as x, ((_, xs_typ) as xs), _), list_typ ->
        (ListT x_typ, list_typ)::(xs_typ, list_typ)::(super#visit_exp_annot env x)@(super#visit_exp_annot env xs)
      | ListTail ((_, xs_typ) as xs, _), list_typ 
      | ListReverse ((_, xs_typ) as xs, _), list_typ ->
          (xs_typ, list_typ)::(super#visit_exp_annot env xs)
      | ListAppend (items, _), list_typ ->
        let subconstraints = items |> List.map (super#visit_exp_annot env) |> List.concat in
        let sublist_constraints = items |> List.map (fun (_, sublist_typ) -> (sublist_typ, list_typ)) in
        sublist_constraints @ subconstraints
      | Add ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), expr_typ
      | Subtract ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), expr_typ
      | Mult ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), expr_typ
      | Div ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), expr_typ ->
          (expr_typ, lhs_typ)::(expr_typ, rhs_typ)::(super#visit_exp_annot env lhs)@(super#visit_exp_annot env rhs)
      | exp -> super#visit_exp_annot env exp

    method! visit_p_formula_annot env = function
      | Lt ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), _
      | Lte ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), _
      | Gt ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), _ 
      | Gte ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), _ ->
          (lhs_typ, rhs_typ)::(rhs_typ, Int)::(super#visit_exp_annot env lhs)@(super#visit_exp_annot env rhs)
      | Eq ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), _
      | Neq ((_, lhs_typ) as lhs, ((_, rhs_typ) as rhs), _), _ ->
          (lhs_typ, rhs_typ)::(super#visit_exp_annot env lhs)@(super#visit_exp_annot env rhs)
      | EqMax ((_, lhs_typ) as lhs, ((_, rhs1_typ) as rhs1), ((_, rhs2_typ) as rhs2), _), _
      | EqMin ((_, lhs_typ) as lhs, ((_, rhs1_typ) as rhs1), ((_, rhs2_typ) as rhs2), _), _ ->
          (lhs_typ, rhs1_typ)::(rhs1_typ, rhs2_typ)::(rhs2_typ, Int)
            ::(super#visit_exp_annot env lhs)@(super#visit_exp_annot env rhs1)@(super#visit_exp_annot env rhs2)
      | f -> super#visit_p_formula_annot env f

  end in
  go#visit_formula_annot () typed_formula

let (let+) opt f = Option.map f opt
let (let*) = Option.bind

let lift_option_from_list (ls : 'a option list) : 'a list option =
  let rec go ?(acc=[]) = function
    | [] -> Some acc
    | (Some x)::xs -> go ~acc:(x::acc) xs
    | None::_ -> None
  in
  go ls |> Option.map List.rev

let rec substitute_vars substitutions = function
  | TVar x -> List.assoc_opt x substitutions |> Option.value ~default:(TVar x)
  | ListT x -> ListT (substitute_vars substitutions x)
  | typ -> typ

let rec expand_type ?(do_not_expand=[]) substitutions = function
  | TVar x when List.mem x do_not_expand -> None
  | TVar x -> begin
      match List.assoc_opt x substitutions with
      | None -> Some (TVar x)
      | Some substitute_typ -> expand_type ~do_not_expand:(x::do_not_expand) substitutions substitute_typ
  end
  | ListT typ -> let* expanded = expand_type ~do_not_expand substitutions typ in Some (ListT expanded)
  | typ -> Some typ

(* Checks that a solution meets the constraints. Raises an exception if the solution does not provide
values for all type variables. *)
let check_solution (constraints : unification_constr list) (solution : (int * typ) list) : bool =
  List.for_all (fun (t1, t2) -> equal_types (substitute_vars solution t1) (substitute_vars solution t2)) constraints

(* Solves a list of type equality constraints. *)
let solve_constraints (constraints : unification_constr list) : (int * typ) list option =
  (** First, reduce the constraints to all be of the form {TVar int = typ}. *)
  let rec simplify_to_base = function
      | (x, y) when equal_types x y -> Some []
      | (TVar x, other_typ)
      | (other_typ, TVar x) -> Some [(TVar x, other_typ)]
      | (ListT sub_typ1, ListT sub_typ2) -> simplify_to_base (sub_typ1, sub_typ2)
      | _ -> None
  in
  (* Find a sequence of substitutions that let us write down every type. *)
  let rec find_substitutions ?(acc=[]) (constraints : unification_constr list) =
    match constraints with
    | [] -> Some acc
    | (TVar x, other_typ)::others
    | (other_typ, TVar x)::others ->
        let new_subst = [(x, other_typ)] in
        find_substitutions ~acc:(new_subst @ acc) (List.map (fun (x, y) -> (substitute_vars new_subst x, substitute_vars new_subst y)) others)
    | constr::others -> begin
      let* simplified = simplify_to_base constr in
      find_substitutions ~acc (simplified @ others)
    end
  in
  let* substitutions = find_substitutions constraints in
  let* possible_solution : (int * typ) list = substitutions 
    |> List.map (fun (x, typ) -> let+ expanded = expand_type substitutions typ in (x, expanded))
    |> lift_option_from_list in
  if check_solution constraints possible_solution
  then Some possible_solution
  else None

let substitute_ast (substitutions : (int * typ) list) (ast : typ formula_annot) : typ formula_annot =
  let go = object (self)
    inherit [_] endo_formula
    (* Note that 'a = typ in this visitor. *)
    method visit_'a substitutions = function
      | TVar x -> List.assoc_opt x substitutions |> Option.value ~default:(TVar x)
      | ListT typ -> ListT (self#visit_'a substitutions typ)
      | typ -> typ
      
  end in
  go#visit_formula_annot substitutions ast

let infer_cpure_types (f: Cpure.formula) : typ formula_annot option =
  let annotated = annotate_cpure_formula f in
  let constraints = get_constraints annotated in
  let+ solution = solve_constraints constraints in
  substitute_ast solution annotated

let%expect_test "type deduction tests" =
  let print_solution solution = 
    match solution with
    | None -> Printf.printf "[no solution]";
    | Some sol -> sol
      |> List.sort compare
      |> List.iter (fun (i, typ) -> Printf.printf "[var %d] = %s\n" i (string_of_typ typ));
  in
  solve_constraints [(TVar 0, TVar 1); (TVar 1, TVar 2); (TVar 2, Bool)] |> print_solution;
  [%expect{| |}];

  solve_constraints [(TVar 0, TVar 1); (TVar 1, TVar 2); (TVar 2, Bool); (TVar 0, Int)] |> print_solution;
  [%expect{| |}];

  solve_constraints [(TVar 0, Int); (TVar 1, ListT (TVar 0)); (TVar 1, ListT (TVar 2))] |> print_solution;
  [%expect{| |}];

  (* circular construction *)
  solve_constraints [(TVar 0, ListT (TVar 1)); (TVar 1, ListT (TVar 0))] |> print_solution;
  [%expect{| |}];

  (* circular construction *)
  solve_constraints [(TVar 0, TVar 1); (TVar 2, TVar 3); (TVar 4, TVar 5); (TVar 7, ListT (TVar 6)); (TVar 8, ListT (TVar 0)); (TVar 6, Int);] |> print_solution;
  [%expect{| |}];
