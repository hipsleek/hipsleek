open Cpure
open Globals
(*module type SV_TYPE =
sig
  type t
  val eq : t -> t -> bool
end;;

module SV = 
  functor (Elt:SV_TYPE) ->
struct
  let compare t1 t2 = String.compare
end;;*)

type coq_const = 
  | CFinConst of (int)
  | CInfConst
  | CNegInfConst

type coq_exp =
  | CVar of (string)
  | Cconst of coq_const
  | CAdd of (coq_exp * coq_exp)
  | CSubtract of (coq_exp * coq_exp)
  | CMult of (int * coq_exp)

type coq_b_formula =
  | CBConst of (bool)
  | CLt of (coq_exp * coq_exp)
  | CLte of (coq_exp * coq_exp)
  | CGt of (coq_exp * coq_exp)
  | CGte of (coq_exp * coq_exp)
  | CEq of (coq_exp * coq_exp) 
  | CNeq of (coq_exp * coq_exp)

type coq_formula =
  | CBForm of (coq_b_formula)
  | CAnd of (coq_formula * coq_formula)
  | COr of (coq_formula * coq_formula)
  | CNot of (coq_formula)
  | CForall of (string * coq_formula)
  | CExists of (string * coq_formula)

let rec cpure_to_coqpure_exp (e: exp) : coq_exp =
match e with
  | Null _ -> CVar("null")
  | Var(sv,_) -> CVar((string_of_spec_var sv))
  | IConst(i,_) -> Cconst(CFinConst(i))
  | InfConst _ -> Cconst(CInfConst)
  | Add(e1,e2,_) -> CAdd((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
  | Subtract(e1,e2,_) -> CSubtract((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
  | Mult(e1,e2,_) -> 
      (match e1 with
        | IConst (i, _) -> CMult(i,(cpure_to_coqpure_exp e2))
        | _ -> match e2 with
            | IConst (i, _) -> CMult(i,(cpure_to_coqpure_exp e1))
            | _ -> illegal_format "[coqinf.ml] Non-linear arithmetic is not supported by Omega.")
  | _ -> illegal_format "Cannot use the expression with CoqInf Solver" 

let rec cpure_to_coqpure_bformula (bf: b_formula) : coq_b_formula =
  let pf,_ = bf in
  match pf with
    | BConst(b,_) -> CBConst(b)
    | Lt(e1,e2,_) -> CLt((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Lte(e1,e2,_) -> CLte((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Gt(e1,e2,_) -> CGt((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Gte(e1,e2,_) -> CGte((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Eq(e1,e2,_) -> CEq ((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Neq(e1,e2,_) -> CNeq ((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | _ -> illegal_format "Cannot use the constraint with CoqInf Solver"

let rec cpure_to_coqpure (f: formula) : coq_formula =
match f with
  | BForm(bf,_) -> CBForm(cpure_to_coqpure_bformula bf)
  | And(f1,f2,_) -> CAnd ((cpure_to_coqpure f1),(cpure_to_coqpure f2))
  | Or(f1,f2,_,_) -> COr ((cpure_to_coqpure f1),(cpure_to_coqpure f2))
  | Not(f,_,_) -> CNot (cpure_to_coqpure f)
  | Forall(sv,f,_,_) -> CForall((string_of_spec_var sv),(cpure_to_coqpure f))
  | Exists(sv,f,_,_) -> CExists((string_of_spec_var sv),(cpure_to_coqpure f))
  | AndList _ -> illegal_format "Cannot use AndList for CoqInf Solver"

let string_to_spec_var str_sv = 
if ((String.get str_sv (String.length str_sv)) == '\'') then SpecVar(Int,str_sv,Primed)
else SpecVar(Int,str_sv,Unprimed)

let rec coqpure_to_cpure_exp (e:coq_exp) : exp =
  match e with 
    | CVar s -> Var((string_to_spec_var s),no_pos)
    | Cconst c -> 
        (match c with
          | CInfConst -> mkInfConst no_pos
          | CNegInfConst -> mkNegInfConst no_pos
          | CFinConst i -> IConst(i,no_pos)
        )
    | CAdd(e1,e2) -> Add((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),no_pos)
    | CSubtract(e1,e2) -> Subtract((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),no_pos)
    | CMult(i,e2) -> Mult((IConst(i,no_pos)),(coqpure_to_cpure_exp e2),no_pos)

let rec coqpure_to_cpure_bformula (cbf: coq_b_formula): b_formula =
  let pf = 
    match cbf with
      | CBConst b -> BConst(b,no_pos)
      | CLt(e1,e2) -> Lt((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),no_pos)
      | CLte(e1,e2) -> Lte((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),no_pos)
      | CGt(e1,e2) -> Gt((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),no_pos)
      | CGte(e1,e2) -> Gte((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),no_pos)
      | CEq(e1,e2) -> Eq((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),no_pos)
      | CNeq(e1,e2) -> Neq((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),no_pos)
  in (pf,None)


let rec coqpure_to_cpure (cf: coq_formula) : formula =
  match cf with
    | CBForm(cbf) -> BForm(coqpure_to_cpure_bformula cbf,None)
    | CAnd(e1,e2) -> And((coqpure_to_cpure e1),(coqpure_to_cpure e2),no_pos)
    | COr(e1,e2) -> Or((coqpure_to_cpure e1),(coqpure_to_cpure e2),None,no_pos)
    | CNot f -> Not((coqpure_to_cpure f),None,no_pos)
    | CForall(sv,f) -> Forall((string_to_spec_var sv),(coqpure_to_cpure f),None,no_pos)
    | CExists(sv,f) -> Exists((string_to_spec_var sv),(coqpure_to_cpure f),None,no_pos)
