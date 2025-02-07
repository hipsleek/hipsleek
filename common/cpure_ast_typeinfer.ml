(** 
  A fully typed version of a subset of the Cpure AST.
  While the current AST does support some type inference, it only
  annotates SpecVars. The types in this module are useful when
  full type information is needed (e.g. when converting a Cpure
  formula into SMTLIB format.)
 *)
open Globals

type loc = VarGen.loc [@opaque]
and spec_var = Cpure.spec_var [@opaque]
and typ = Globals.typ [@opaque]
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
  [@@deriving visitors { variety = "mapreduce" }, visitors {variety = "map"}]

let equal_types (t1 : typ) (t2 : typ) : bool = cmp_typ t1 t2

(** Assign an unused TVar label. This uses negative numbers to avoid overlapping with
    the TVar indices assigned during upstream typechecking. *)
let fresh_tvar =
  let id = ref (-1) in
  fun () -> 
    let var_id = !id in
    id := !id - 1; TVar var_id

let typeof (_, b) = b
let assign_type typ (expr, _) = (expr, typ)

(* This function already performs some type synthesis.
   Replace the type with None to let the check-infer loop later
   on compute the type of this expression. *)
let rec annotate_cpure_exp (exp : Cpure.exp) : typ option exp_annot =
  match exp with
  | Cpure.Null loc -> Null loc, Some Int
  | Cpure.Var (SpecVar (typ, _, _) as var, loc) -> 
      Var (var, loc), Some typ
  | Cpure.IConst (n, loc) -> 
      IConst (n, loc), Some Int
  | Cpure.Add (lhs, rhs, loc) -> 
      let lhs = annotate_cpure_exp lhs in 
      Add (lhs, annotate_cpure_exp rhs, loc), typeof lhs
  | Cpure.Subtract (lhs, rhs, loc) ->
      let lhs = annotate_cpure_exp lhs in 
      Subtract (lhs, annotate_cpure_exp rhs, loc), typeof lhs
  | Cpure.Mult (lhs, rhs, loc) ->
      let lhs = annotate_cpure_exp lhs in 
      Mult (lhs, annotate_cpure_exp rhs, loc), typeof lhs
  | Cpure.Div (lhs, rhs, loc) ->
      let _, lhs_typ as lhs_annot = annotate_cpure_exp lhs in 
      Div (lhs_annot, annotate_cpure_exp rhs, loc), lhs_typ
  | Cpure.List (vs, loc) -> 
      let subexprs = List.map annotate_cpure_exp vs in
      List (subexprs, loc), None
  | Cpure.ListCons (v, vs, loc) -> 
      let elem = annotate_cpure_exp v in 
      ListCons (elem, annotate_cpure_exp vs, loc), None
  | Cpure.ListTail (vs, loc) -> 
      let vs = annotate_cpure_exp vs in
      ListTail (vs, loc), (typeof vs)
  | Cpure.ListLength (vs, loc) -> ListLength (annotate_cpure_exp vs, loc), Some Int
  | Cpure.ListAppend (vs, loc) ->
      let subexprs = List.map annotate_cpure_exp vs in
      let list_typ : typ option = List.find_opt (fun exp -> match exp with | (_, Some _) -> true | _ -> false) subexprs 
        |> Option.map typeof
        |> Option.join
      in
      List (subexprs, loc), list_typ
  | Cpure.ListReverse (vs, loc) ->
      let vs = annotate_cpure_exp vs in
      ListReverse (vs, loc), (typeof vs)
  | _ -> raise (Invalid_argument "Unsupported Cpure expression")

let annotate_cpure_p_formula (pf : Cpure.p_formula) : typ option p_formula_annot =
  match pf with
  | Cpure.BConst data -> BConst data, Some Bool
  | Cpure.BVar data -> BVar data, Some Bool
  | Cpure.Lt (lhs, rhs, loc) -> Lt (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Some Bool
  | Cpure.Lte (lhs, rhs, loc) -> Lte (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Some Bool
  | Cpure.Gt (lhs, rhs, loc) -> Gt (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Some Bool
  | Cpure.Gte (lhs, rhs, loc) -> Gte (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Some Bool
  | Cpure.Eq (lhs, rhs, loc) -> Eq (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Some Bool
  | Cpure.Neq (lhs, rhs, loc) -> Neq (annotate_cpure_exp lhs, annotate_cpure_exp rhs, loc), Some Bool
  | Cpure.EqMax (lhs, rhs1, rhs2, loc) -> EqMax (annotate_cpure_exp lhs, annotate_cpure_exp rhs1, annotate_cpure_exp rhs2, loc), Some Bool
  | Cpure.EqMin (lhs, rhs1, rhs2, loc) -> EqMin (annotate_cpure_exp lhs, annotate_cpure_exp rhs1, annotate_cpure_exp rhs2, loc), Some Bool
  | Cpure.RelForm (ident, args, loc) -> RelForm (ident, List.map annotate_cpure_exp args, loc), Some Bool
  (* TODO: Currently, this AST is only being used for SMT translation, which does not
   need LexVars. Thus, we substitute a placeholder for now. *)
  | Cpure.LexVar {lex_loc; _}  -> BConst (true, lex_loc), Some Bool
  | _ -> raise (Invalid_argument "Unsupported Cpure p_formula ")

let annotate_cpure_b_formula (bf : Cpure.b_formula) : typ option b_formula_annot =
  let annotate_subexprs (e1, e2, exprs : Cpure.bf_annot) = (e1, e2, List.map annotate_cpure_exp exprs) in
  let (pf, subannot) = bf in
  (annotate_cpure_p_formula pf, Option.map annotate_subexprs subannot), Some Bool

let rec annotate_cpure_formula (f : Cpure.formula) : typ option formula_annot =
  try
    match f with
    | Cpure.BForm (bf, label) -> BForm (annotate_cpure_b_formula bf, label), Some Bool
    | Cpure.And (lhs, rhs, loc) -> And (annotate_cpure_formula lhs, annotate_cpure_formula rhs, loc), Some Bool
    | Cpure.Or (lhs, rhs, label, loc) -> Or (annotate_cpure_formula lhs, annotate_cpure_formula rhs, label, loc), Some Bool
    | Cpure.Not (f, label, loc) -> Not (annotate_cpure_formula f, label, loc), Some Bool
    | Cpure.Forall (binder, f, label, loc) -> Forall (binder, annotate_cpure_formula f, label, loc), Some Bool
    | Cpure.Exists (binder, f, label, loc) -> Exists (binder, annotate_cpure_formula f, label, loc), Some Bool
    | _ -> raise (Invalid_argument "Typechecker currently does not support Cpure.AndLists")
  with
    (* Rethrow, but attach the full formula as context *)
    | Invalid_argument e -> raise (Invalid_argument (Printf.sprintf "Formula marked as invalid: %s %s" e (Cpure.string_of_ls_pure_formula [f])))
  

let (let+) opt f = Option.map f opt
let (let*) = Option.bind

(** Propagate type information downward along the AST.
 The returned boolean indicates whether or not a checking rule was applied.*)
let check_types (exp: typ option formula_annot) : typ option formula_annot * bool = 
  let checker = object (self)
    inherit [_] mapreduce as super
    method visit_'a _ (x : typ option) = (x, false)
    method zero = false
    method plus = (||)

    method! visit_exp_annot typ exp =
      match typ, exp with
      (* List elimination rule : if a List has type (List T), its elements have type T. *)
      | (Some (Globals.List element_typ) as list_typ, (List (elements, loc), _)) 
        when List.exists (fun elem -> match elem with | (_, None) -> true | _ -> false) elements ->
          let subexprs, _ = List.map (self#visit_exp_annot (Some element_typ)) elements |> List.split in
          ((List (subexprs, loc), list_typ), true)
      (* ListCons elimination rule: if a ListCons has type (List T), the head has type T,
      and the tail has type (List T). *)
      | (Some (Globals.List element_typ) as list_typ, (ListCons (head, tail, loc), _))
        when Option.(is_none (typeof head) || is_none (typeof tail)) ->
        let subhead, _ = self#visit_exp_annot (Some element_typ) head in
        let subtail, _ = self#visit_exp_annot list_typ tail in
        ((ListCons (subhead, subtail, loc), list_typ), true)
      | _ -> 
        let (exp, applied) = super#visit_exp_annot typ exp in
        let typ = match typ with | None -> typeof exp | _ -> typ in
        (assign_type typ exp), applied


    method! visit_p_formula_annot ctx exp =
      match exp with
      (* Eq eliminination rule: If one side of an Eq has type T, so does the other. *)
      | (Eq (lhs, rhs, loc), eq_typ) ->
          begin match (typeof lhs, typeof rhs) with
          | (None, (Some _ as known_typ)) 
          | ((Some _ as known_typ), None) ->
            let lhs, _ = self#visit_exp_annot known_typ lhs in
            let rhs, _ = self#visit_exp_annot known_typ rhs in
            (Eq (lhs, rhs, loc), eq_typ), true
          | _ -> super#visit_p_formula_annot ctx exp
          end
      | _ -> super#visit_p_formula_annot ctx exp
  end in
  checker#visit_formula_annot (None) exp

(** Propagate type information upward/sideways along the AST. 
 The returned boolean indicates whether or not a synthesis rule was applied.*)
let synthesize_types (exp : typ option formula_annot) : typ option formula_annot * bool =
  let synth = object (self)
    inherit [_] mapreduce as super
    method visit_'a _ (x : typ option) = (x, false)
    method zero = false
    method plus = (||)

    method! visit_exp_annot ctx exp =
      match exp with
      (* List introduction rule: if one element of a list has type T, the list has type (List T). *)
      | (List (elements, loc), None) ->
        let subexprs, subrule_applied = List.map (self#visit_exp_annot ctx) elements |> List.split in
        let possible_list_typ = elements |> List.map (fun (_, typ) -> typ) |> List.find_opt Option.is_some |> Option.join in
        ((List (subexprs, loc), possible_list_typ),
          Option.is_some possible_list_typ || List.exists ((=) true) subrule_applied)
      (* ListCons introduction rule:
          - if a head has type T, its ListCons has type (List T).
          - if a tail has type (List T), so does its ListCons *)
      | (ListCons (head, tail, loc), None) ->
          let head, head_applied = self#visit_exp_annot ctx head in
          let tail, tail_applied = self#visit_exp_annot ctx tail in
          let subrules_applied = head_applied || tail_applied in
          begin match (typeof head, typeof tail) with
          | (Some head_typ, _) ->
            (ListCons (head, tail, loc), Some (Globals.List head_typ)), true
          | (_, Some tail_typ) ->
            (ListCons (head, tail, loc), Some tail_typ), true
          | _ ->
            (ListCons (head, tail, loc), None), subrules_applied
          end
      | _ -> super#visit_exp_annot ctx exp

  end in
  synth#visit_formula_annot () exp

let lift_option_from_list (ls : 'a option list) : 'a list option =
  let rec go ?(acc=[]) = function
    | [] -> Some acc
    | (Some x)::xs -> go ~acc:(x::acc) xs
    | None::_ -> None
  in
  go ls |> Option.map List.rev

let fill_missing_annotations (fill: unit -> 'a) (f : 'a option formula_annot) =
  let go = object
    inherit [_] map
    method visit_'a _ (typ : typ option) = Option.value typ ~default:(fill ())
  end in
  go#visit_formula_annot () f

let infer_cpure_types (f: Cpure.formula) : typ formula_annot =
  (* Printf.printf "Given formula %s to infer\n" (Cpure.string_of_ls_pure_formula [f]); *)
  let annotated = annotate_cpure_formula f in
  let rec do_further_inference (exp : typ option formula_annot) : typ option formula_annot =
    let exp, check_progress = check_types exp in
    let exp, infer_progress = synthesize_types exp in
    if check_progress || infer_progress
    then do_further_inference exp
    else exp
  in
  let result = do_further_inference annotated in
  (fill_missing_annotations fresh_tvar result)
