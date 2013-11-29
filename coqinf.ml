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
module StrSV =
struct
(*  let is_eq s1 s2 = match s1, s2 with
    | Infsolver.string (String.compare s1 s2) == 0*)
end

module CoqInfSolver = Infsolver.InfSolver(StrSV)

open CoqInfSolver

let explode (s:string) : char list =
   let rec expl i l =
     if i < 0 then l else
       expl (i - 1) (s.[i] :: l) in
   expl (String.length s - 1) [];;

let implode (l:char list) : string =
   let result = String.create (List.length l) in
   let rec imp i = function
     | [] -> result
     | c :: l -> result.[i] <- c; imp (i + 1) l in
   imp 0 l;;

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

let coqpure_to_coqinfsolver_const (c: coq_const) : coq_ZE =
match c with
  | CFinConst i -> ZE_Fin (explode (string_of_int i))
  | CInfConst -> ZE_Inf
  | CNegInfConst -> ZE_NegInf

let rec coqpure_to_coqinfsolver_exp (e:coq_exp) : coq_ZE coq_ZExp  =
match e with
  | CVar v -> ZExp_Var (explode v)
  | Cconst c -> ZExp_Const (coqpure_to_coqinfsolver_const c)
  | CAdd(e1, e2) -> ZExp_Add((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CSubtract(e1,e2) -> ZExp_Sub((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CMult(i,e) -> ZExp_Mult((explode (string_of_int i)),(coqpure_to_coqinfsolver_exp e))

let rec coqpure_to_coq_infsolver_bf (bf: coq_b_formula) : coq_ZE coq_ZBF =
match bf with 
  | CBConst b -> ZBF_Const b 
  | CLt(e1,e2) -> ZBF_Lt((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CLte(e1,e2) -> ZBF_Lte((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CGt(e1,e2) -> ZBF_Gt((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CGte(e1,e2) -> ZBF_Gte((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CEq(e1,e2) -> ZBF_Eq((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2)) 
  | CNeq(e1,e2) -> ZBF_Neq((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))  

let rec coqpure_to_coq_infsolver_form (f: coq_formula) : coq_ZE coq_ZF = 
match f with
  | CBForm bf -> ZF_BF (coqpure_to_coq_infsolver_bf bf)
  | CAnd(f1,f2) -> ZF_And((coqpure_to_coq_infsolver_form f1),(coqpure_to_coq_infsolver_form f2))
  | COr(f1,f2) -> ZF_Or ((coqpure_to_coq_infsolver_form f1),(coqpure_to_coq_infsolver_form f2)) 
  | CNot f -> ZF_Not (coqpure_to_coq_infsolver_form f)
  | CForall(v,f) -> ZF_Forall((explode v),(coqpure_to_coq_infsolver_form f))
  | CExists(v,f) -> ZF_Exists((explode v),(coqpure_to_coq_infsolver_form f))

(*
let coqinfsolver_to_coqpure_const (c:coq_ZE) : coq_const =
match c with
  | ZE_Fin cl ->  CFinConst (int_of_string(implode cl))
  | ZE_Inf -> CInfConst
  | ZE_NegInf -> CNegInfConst
*)

let rec coq_infsolver_to_coqpure_exp (e: char list coq_ZExp) : coq_exp = 
match e with
  | ZExp_Var v -> CVar (implode v)
  | ZExp_Const c -> Cconst (CFinConst (int_of_string(implode c)))
  | ZExp_Add(e1,e2) -> CAdd((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZExp_Sub(e1,e2) -> CSubtract((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZExp_Mult(i,e) -> CMult(int_of_string (implode i),(coq_infsolver_to_coqpure_exp e))

let rec coq_infsolver_to_coqpure_bf (bf: char list coq_ZBF) : coq_b_formula =
match bf with
  | ZBF_Const b -> CBConst b
  | ZBF_Lt(e1,e2) -> CLt((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Lte(e1,e2) -> CLte((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Gt(e1,e2) -> CGt((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Gte(e1,e2) -> CGte((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Eq(e1,e2) -> CEq((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Neq(e1,e2) -> CNeq((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))

let rec coq_infsolver_to_coqpure_form (f: char list coq_ZF) : coq_formula = 
match f with
  | ZF_BF bf -> CBForm (coq_infsolver_to_coqpure_bf bf)
  | ZF_And(f1,f2) -> CAnd((coq_infsolver_to_coqpure_form f1),(coq_infsolver_to_coqpure_form f2))
  | ZF_Or(f1,f2) -> COr((coq_infsolver_to_coqpure_form f1),(coq_infsolver_to_coqpure_form f2))
  | ZF_Not g -> CNot (coq_infsolver_to_coqpure_form g)
  | ZF_Forall(s,f) -> CForall((implode s),(coq_infsolver_to_coqpure_form f))
  | ZF_Exists(s,f) -> CExists((implode s),(coq_infsolver_to_coqpure_form f))

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
    | BVar(sv,_) -> CGt(CVar(string_of_spec_var sv),Cconst(CFinConst(0)))
    | Lt(e1,e2,_) -> CLt((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Lte(e1,e2,_) -> CLte((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Gt(e1,e2,_) -> CGt((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Gte(e1,e2,_) -> CGte((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Eq(e1,e2,_) -> CEq ((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | Neq(e1,e2,_) -> CNeq ((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
    | _ -> illegal_format ("Cannot use the constraint with CoqInf Solver "^(Cprinter.string_of_b_formula bf))

let rec cpure_to_coqpure (f: formula) : coq_formula =
match f with
  | BForm(bf,_) ->let pf,_ = bf in (match pf with 
                   | EqMax(e1,e2,e3,_) -> 
                       let ce1 = cpure_to_coqpure_exp e1 in
                       let ce2 = cpure_to_coqpure_exp e2 in
                       let ce3 = cpure_to_coqpure_exp e3 in
                       COr(CAnd(CBForm(CGte(ce2,ce3)),CBForm(CEq(ce1,ce2))),
                           CAnd(CBForm(CGt(ce3,ce2)),CBForm(CEq(ce1,ce3))))
                   | EqMin(e1,e2,e3,_) -> 
                       let ce1 = cpure_to_coqpure_exp e1 in
                       let ce2 = cpure_to_coqpure_exp e2 in
                       let ce3 = cpure_to_coqpure_exp e3 in
                       COr(CAnd(CBForm(CGte(ce2,ce3)),CBForm(CEq(ce1,ce3))),
                           CAnd(CBForm(CGt(ce3,ce2)),CBForm(CEq(ce1,ce2))))
(*Added to handle min and max constraints *)
                   | _ -> CBForm(cpure_to_coqpure_bformula bf))
  | And(f1,f2,_) -> CAnd ((cpure_to_coqpure f1),(cpure_to_coqpure f2))
  | Or(f1,f2,_,_) -> COr ((cpure_to_coqpure f1),(cpure_to_coqpure f2))
  | Not(f,_,_) -> CNot (cpure_to_coqpure f)
  | Forall(sv,f,_,_) -> CForall((string_of_spec_var sv),(cpure_to_coqpure f))
  | Exists(sv,f,_,_) -> CExists((string_of_spec_var sv),(cpure_to_coqpure f))
  | AndList _ -> illegal_format "Cannot use AndList for CoqInf Solver"

let cpure_to_coqpure (f:formula) :coq_formula = 
Debug.no_1 "cpure_to_coqpure" Cprinter.string_of_pure_formula (fun _ -> "") cpure_to_coqpure f

let string_to_spec_var str_sv = 
if ((String.get str_sv ((String.length str_sv)-1)) == '\'') then SpecVar(Int,str_sv,Primed)
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

let coqpure_to_cpure (f:coq_formula) : formula = 
Debug.no_1 "coqpure_to_cpure" (fun _ -> "")  Cprinter.string_of_pure_formula coqpure_to_cpure f

let check_sat_inf_formula (f: formula) : formula = 
  coqpure_to_cpure (coq_infsolver_to_coqpure_form (transform_ZE_to_string (coqpure_to_coq_infsolver_form (cpure_to_coqpure f))))
