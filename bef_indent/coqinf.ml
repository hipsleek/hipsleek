open Cpure
open Globals
open Gen
open VarGen

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

module StrSV =
struct
(*let is_eq s1 s2 = String.compare (implode s1) (implode s2) = 0 *)
  type var = string
  let var_eq_dec = (=)
  let var2string = explode
  let string2var = implode
end

module CoqInfSolver = Infsolver.InfSolverExtract(StrSV)

open CoqInfSolver

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
  | CEqMax of (coq_exp * coq_exp * coq_exp) 
  | CEqMin of (coq_exp * coq_exp * coq_exp) 
  | CNeq of (coq_exp * coq_exp)

type coq_formula =
  | CBForm of (coq_b_formula)
  | CAnd of (coq_formula * coq_formula)
  | COr of (coq_formula * coq_formula)
  | CNot of (coq_formula)
  | CForall_Fin of (string * coq_formula)
  | CExists_Fin of (string * coq_formula)
  | CForall of (string * coq_formula)
  | CExists of (string * coq_formula)

let string_of_coq_const c = 
match c with
  | CFinConst i -> string_of_int i
  | CInfConst -> "\\inf"
  | CNegInfConst -> "~\\inf"

let rec string_of_coq_exp e =
match e with
  | CVar s -> s
  | Cconst c -> string_of_coq_const c 
  | CAdd(e1,e2) -> (string_of_coq_exp e1)^" + "^(string_of_coq_exp e2)
  | CSubtract(e1,e2) -> (string_of_coq_exp e1)^" - "^(string_of_coq_exp e2)
  | CMult(i,e) -> (string_of_int i)^" * "^(string_of_coq_exp e)

let string_of_coq_b_formula bf =
match bf with
  | CBConst b -> if b then "true" else "false"
  | CLt(e1,e2) -> (string_of_coq_exp e1)^" < "^(string_of_coq_exp e2)
  | CLte(e1,e2) -> (string_of_coq_exp e1)^" <= "^(string_of_coq_exp e2)
  | CGt(e1,e2) -> (string_of_coq_exp e1)^" > "^(string_of_coq_exp e2)
  | CGte(e1,e2) -> (string_of_coq_exp e1)^" >= "^(string_of_coq_exp e2)
  | CEq(e1,e2) -> (string_of_coq_exp e1)^" = "^(string_of_coq_exp e2)
  | CEqMax(e1,e2,e3) -> (string_of_coq_exp e1)^" = max("^(string_of_coq_exp e2)^","^(string_of_coq_exp e3)^")"
  | CEqMin(e1,e2,e3) -> (string_of_coq_exp e1)^" = min("^(string_of_coq_exp e2)^","^(string_of_coq_exp e3)^")"
  | CNeq(e1,e2) -> (string_of_coq_exp e1)^" != "^(string_of_coq_exp e2)

let rec string_of_coq_formula cf = 
match cf with
  | CBForm b -> "("^(string_of_coq_b_formula b)^")"
  | CAnd(cf1,cf2) -> (string_of_coq_formula cf1)^" & "^(string_of_coq_formula cf2)
  | COr(cf1,cf2) -> (string_of_coq_formula cf1)^" | "^(string_of_coq_formula cf2)
  | CNot(cf) -> "(!"^(string_of_coq_formula cf)^")"
  | CForall_Fin(s,cf) -> "forall_Z("^s^":"^(string_of_coq_formula cf)^")"
  | CExists_Fin(s,cf) -> "exists_Z("^s^":"^(string_of_coq_formula cf)^")"
  | CForall(s,cf) -> "forall_ZE("^s^":"^(string_of_coq_formula cf)^")"
  | CExists(s,cf) -> "exists_ZE("^s^":"^(string_of_coq_formula cf)^")"

let is_coqinf_const c =
match c with
  | CFinConst i -> false
  | CInfConst
  | CNegInfConst -> true

let is_coqinf_exp e =
match e with
  | Cconst c -> is_coqinf_const c
  | _ -> false

let is_var_exp e =
match e with
  | CVar _ -> true
  | _ -> false

let rec find_inf_quant_vars_exp e vl : string list =
match e with
  | CAdd(e1,e2) 
  | CSubtract(e1,e2) -> 
      let vl = find_inf_quant_vars_exp e1 vl in
      let vl = find_inf_quant_vars_exp e2 vl in
      (match e1, e2 with
      | CVar s1,CVar s2 -> if Gen.BList.mem_eq (=) s1 vl then s2::vl else if Gen.BList.mem_eq (=) s2 vl then s1::vl else vl
      | CVar s, Cconst c
      | Cconst c, CVar s -> if is_coqinf_const c then s::vl else vl
      | _ , _ -> vl )
  | _ -> vl

let find_inf_quant_vars_bform bf vl : string list =
match bf with 
  | CBConst _ -> vl
  | CLt(e1,e2)
  | CLte(e1,e2)
  | CGt(e1,e2)
  | CGte(e1,e2)
  | CEq(e1,e2)
  | CNeq(e1,e2) -> let vl = (find_inf_quant_vars_exp e1 vl) in
                   let vl = (find_inf_quant_vars_exp e2 vl) in
                   (match e1, e2 with
                     | CVar s1,CVar s2 -> if Gen.BList.mem_eq (=) s1 vl then s2::vl else if Gen.BList.mem_eq (=) s2 vl then s1::vl else vl
                     | CVar s, Cconst c
                     | Cconst c, CVar s -> if is_coqinf_const c then s::vl else vl
                     | CVar s, CAdd(a1,a2) 
                     | CAdd(a1,a2), CVar s
                     | CVar s, CSubtract(a1,a2) 
                     | CSubtract(a1,a2), CVar s -> (match a1,a2 with
                         | CVar r, x
                         | x , CVar r -> if Gen.BList.mem_eq (=) r vl then s::vl else if Gen.BList.mem_eq (=) s vl then r::vl 
                           else (match x with 
                             | Cconst c -> if is_coqinf_const c then r::s::vl else vl
                             | _ -> vl)
                         | _,_ -> vl)
                     | Cconst c, CAdd(a1,a2)
                     | CAdd(a1,a2), Cconst c
                     | Cconst c, CSubtract(a1,a2) 
                     | CSubtract(a1,a2), Cconst c -> (match a1, a2 with
                         | CVar s1, CVar s2 -> if is_coqinf_const c then s1::s2::vl else vl
                         | CVar s, _ 
                         | _, CVar s -> if is_coqinf_const c then s::vl else vl
                         | _, _ -> vl)
                     | _ , _ -> vl )
  | CEqMax(e1,e2,e3) 
  | CEqMin(e1,e2,e3) -> 
      let vl = (find_inf_quant_vars_exp e1 vl) in
      let vl = (find_inf_quant_vars_exp e2 vl) in
      let vl = (find_inf_quant_vars_exp e3 vl) in
      (match e1,e2,e3 with
        | CVar s1, CVar s2, CVar s3 -> 
            if Gen.BList.mem_eq (=) s1 vl then s2::s3::vl else 
              if Gen.BList.mem_eq (=) s2 vl then s1::s3::vl else 
                if Gen.BList.mem_eq (=) s3 vl then s1::s2::vl else vl
        | _ ,_, _ -> vl 
      )

let rec find_inf_quant_vars f vl : string list =
let sl = match f with
  | CBForm b -> find_inf_quant_vars_bform b vl
  | CAnd(f1,f2) 
  | COr(f1,f2) -> let vl = (find_inf_quant_vars f1 vl) in
                   (find_inf_quant_vars f2 vl)
  | CNot g -> find_inf_quant_vars g vl
  | CForall_Fin (_,g)
  | CExists_Fin (_,g) 
  | CForall(_,g) 
  | CExists(_,g) -> find_inf_quant_vars g vl
in Gen.BList.remove_dups_eq (=) sl

let get_inf_vars f = 
  let rec aux ls  = let ls2 = find_inf_quant_vars f ls in
                    if Gen.BList.list_equiv_eq (=) ls ls2 then ls2
                    else aux ls2
  in aux []

let get_inf_vars f = 
Debug.no_1 "get_inf_vars" (fun c -> "") (fun l -> "INF Vars:"^(String.concat "," l)) get_inf_vars f

let transform_ZE_to_string f =
if !Globals.allow_inf_qe_coq_simp then Gen.Profiling.do_1 "CoqSolverZE" transform_ZE_to_string_simplify f
else Gen.Profiling.do_1 "CoqSolverZE" transform_ZE_to_string f

let coqpure_to_coqinfsolver_const (c: coq_const) : coq_ZE =
match c with
(*  | CFinConst i -> ZE_Fin (explode (string_of_int i))*)
  | CFinConst i -> ZE_Fin (string_of_int i)
  | CInfConst -> ZE_Inf
  | CNegInfConst -> ZE_NegInf

let rec coqpure_to_coqinfsolver_exp (e:coq_exp) : coq_ZE coq_ZExp  =
match e with
(* | CVar v -> ZExp_Var (explode v)*)
 | CVar v -> ZExp_Var v
  | Cconst c -> ZExp_Const (coqpure_to_coqinfsolver_const c)
  | CAdd(e1, e2) -> ZExp_Add((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CSubtract(e1,e2) -> ZExp_Sub((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
(*  | CMult(i,e) -> ZExp_Mult((explode (string_of_int i)),(coqpure_to_coqinfsolver_exp e))*)
  | CMult(i,e) -> ZExp_Mult((string_of_int i),(coqpure_to_coqinfsolver_exp e))

let rec coqpure_to_coq_infsolver_bf (bf: coq_b_formula) : coq_ZE coq_ZBF =
match bf with 
  | CBConst b -> ZBF_Const b 
  | CLt(e1,e2) -> ZBF_Lt((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CLte(e1,e2) -> ZBF_Lte((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CGt(e1,e2) -> ZBF_Gt((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CGte(e1,e2) -> ZBF_Gte((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))
  | CEq(e1,e2) -> ZBF_Eq((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2)) 
  | CEqMax(e1,e2,e3) -> ZBF_Eq_Max((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2),(coqpure_to_coqinfsolver_exp e3)) 
  | CEqMin(e1,e2,e3) -> ZBF_Eq_Min((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2),(coqpure_to_coqinfsolver_exp e3)) 
  | CNeq(e1,e2) -> ZBF_Neq((coqpure_to_coqinfsolver_exp e1),(coqpure_to_coqinfsolver_exp e2))  
(*  | _ ->  failwith "coqinf.ml Max Min shoulbe all eliminated"*)

let rec coqpure_to_coq_infsolver_form (f: coq_formula) vl : coq_ZE coq_ZF = 
match f with
  | CBForm bf -> (*(match bf with
      | CEqMax(e1,e2,e3) -> 
          let ce1 = coqpure_to_coqinfsolver_exp e1 in
          let ce2 = coqpure_to_coqinfsolver_exp e2 in
          let ce3 = coqpure_to_coqinfsolver_exp e3 in
          ZF_Or(ZF_And(ZF_BF(ZBF_Gte(ce2,ce3)),ZF_BF(ZBF_Eq(ce1,ce2))),
              ZF_And(ZF_BF(ZBF_Gt(ce3,ce2)),ZF_BF(ZBF_Eq(ce1,ce3))))
      | CEqMin(e1,e2,e3) -> 
          let ce1 = coqpure_to_coqinfsolver_exp e1 in
          let ce2 = coqpure_to_coqinfsolver_exp e2 in
          let ce3 = coqpure_to_coqinfsolver_exp e3 in
          ZF_Or(ZF_And(ZF_BF(ZBF_Gte(ce2,ce3)),ZF_BF(ZBF_Eq(ce1,ce3))),
              ZF_And(ZF_BF(ZBF_Gt(ce3,ce2)),ZF_BF(ZBF_Eq(ce1,ce2))))
      | _ -> *) ZF_BF (coqpure_to_coq_infsolver_bf bf)
  | CAnd(f1,f2) -> ZF_And((coqpure_to_coq_infsolver_form f1 vl),(coqpure_to_coq_infsolver_form f2 vl))
  | COr(f1,f2) -> ZF_Or ((coqpure_to_coq_infsolver_form f1 vl),(coqpure_to_coq_infsolver_form f2 vl)) 
  | CNot f -> ZF_Not (coqpure_to_coq_infsolver_form f vl)
(*  | CForall_Fin(v,f) -> ZF_Forall_Fin((explode v),(coqpure_to_coq_infsolver_form f vl))
  | CExists_Fin(v,f) -> ZF_Exists_Fin((explode v),(coqpure_to_coq_infsolver_form f vl))*)
  | CForall_Fin(v,f) -> ZF_Forall_Fin(v,(coqpure_to_coq_infsolver_form f vl))
  | CExists_Fin(v,f) -> ZF_Exists_Fin(v,(coqpure_to_coq_infsolver_form f vl))
(* | CForall(v,f) -> if Gen.BList.mem_eq (fun s1 s2 -> (String.compare s1 s2) == 0) v vl then
      ZF_Forall((explode v),(coqpure_to_coq_infsolver_form f vl))
    else (*let () = print_endline ("Is_not_INFVar:  "^v) in*)
         ZF_Forall_Fin((explode v),(coqpure_to_coq_infsolver_form f vl))
  | CExists(v,f) -> if Gen.BList.mem_eq (fun s1 s2 -> (String.compare s1 s2) == 0) v vl then
      ZF_Exists((explode v),(coqpure_to_coq_infsolver_form f vl))
    else (*let () = print_endline ("Is_not_INFVar:  "^v) in*)
         ZF_Exists_Fin((explode v),(coqpure_to_coq_infsolver_form f vl))*)
 | CForall(v,f) -> if Gen.BList.mem_eq (fun s1 s2 -> (String.compare s1 s2) == 0) v vl then
      ZF_Forall(v,(coqpure_to_coq_infsolver_form f vl))
    else (*let () = print_endline ("Is_not_INFVar:  "^v) in*)
         ZF_Forall_Fin(v,(coqpure_to_coq_infsolver_form f vl))
  | CExists(v,f) -> if Gen.BList.mem_eq (fun s1 s2 -> (String.compare s1 s2) == 0) v vl then
      ZF_Exists(v,(coqpure_to_coq_infsolver_form f vl))
    else (*let () = print_endline ("Is_not_INFVar:  "^v) in*)
         ZF_Exists_Fin(v,(coqpure_to_coq_infsolver_form f vl))

let coqpure_to_coq_infsolver_form (f: coq_formula) vl : coq_ZE coq_ZF = 
Debug.no_2 "coqpure_to_coq_inf" string_of_coq_formula (fun c -> "") (fun c -> "") coqpure_to_coq_infsolver_form f vl

(*
let coqinfsolver_to_coqpure_const (c:coq_ZE) : coq_const =
match c with
  | ZE_Fin cl ->  CFinConst (int_of_string(implode cl))
  | ZE_Inf -> CInfConst
  | ZE_NegInf -> CNegInfConst
*)

let rec coq_infsolver_to_coqpure_exp (e: string coq_ZExp) : coq_exp = 
match e with
(*  | ZExp_Var v -> CVar (implode v)*)
  | ZExp_Var v -> CVar v
(*  | ZExp_Const c -> Cconst (CFinConst (int_of_string(implode c)))*)
  | ZExp_Const c -> Cconst (CFinConst (int_of_string c))
  | ZExp_Add(e1,e2) -> CAdd((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZExp_Sub(e1,e2) -> CSubtract((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
(*  | ZExp_Mult(i,e) -> CMult(int_of_string (implode i),(coq_infsolver_to_coqpure_exp e))*)
 | ZExp_Mult(i,e) -> CMult(int_of_string i,(coq_infsolver_to_coqpure_exp e))

let rec coq_infsolver_to_coqpure_bf (bf: string coq_ZBF) : coq_b_formula =
match bf with
  | ZBF_Const b -> CBConst b
  | ZBF_Lt(e1,e2) -> CLt((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Lte(e1,e2) -> CLte((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Gt(e1,e2) -> CGt((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Gte(e1,e2) -> CGte((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Eq(e1,e2) -> CEq((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))
  | ZBF_Eq_Max(e1,e2,e3) -> CEqMax((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2),(coq_infsolver_to_coqpure_exp e3))
  | ZBF_Eq_Min(e1,e2,e3) -> CEqMin((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2),(coq_infsolver_to_coqpure_exp e3))
  | ZBF_Neq(e1,e2) -> CNeq((coq_infsolver_to_coqpure_exp e1),(coq_infsolver_to_coqpure_exp e2))

let rec coq_infsolver_to_coqpure_form (f: string coq_ZF) : coq_formula = 
match f with
  | ZF_BF bf -> CBForm (coq_infsolver_to_coqpure_bf bf)
  | ZF_And(f1,f2) -> CAnd((coq_infsolver_to_coqpure_form f1),(coq_infsolver_to_coqpure_form f2))
  | ZF_Or(f1,f2) -> COr((coq_infsolver_to_coqpure_form f1),(coq_infsolver_to_coqpure_form f2))
  | ZF_Not g -> CNot (coq_infsolver_to_coqpure_form g)
  | ZF_Forall (s,f)  (*CForall((implode s),(coq_infsolver_to_coqpure_form f))*)
  | ZF_Exists (s,f) -> (*CExists((implode s),(coq_infsolver_to_coqpure_form f))*)
      failwith "coqinf.ml Infinity quantifiers should be all eliminated"
(*  | ZF_Forall_Fin(s,f) -> CForall_Fin((implode s),(coq_infsolver_to_coqpure_form f))
  | ZF_Exists_Fin(s,f) -> CExists_Fin((implode s),(coq_infsolver_to_coqpure_form f))*)
  | ZF_Forall_Fin(s,f) -> CForall_Fin(s,(coq_infsolver_to_coqpure_form f))
  | ZF_Exists_Fin(s,f) -> CExists_Fin(s,(coq_infsolver_to_coqpure_form f))

let coq_infsolver_to_coqpure_form (f: string coq_ZF) : coq_formula = 
Debug.no_1 "coq_inf_to_coqpure" (fun c -> "") string_of_coq_formula coq_infsolver_to_coqpure_form f 

let rec cpure_to_coqpure_exp (e: exp) : coq_exp =
match e with
  | Null _ -> CVar("null")
  | Var(sv,_) -> CVar((string_of_spec_var sv))
  | IConst(i,_) -> Cconst(CFinConst(i))
  | InfConst _ -> Cconst(CInfConst)
  | NegInfConst _ -> Cconst(CNegInfConst)
  | Add(e1,e2,_) -> CAdd((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
  | Subtract(e1,e2,_) -> CSubtract((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2))
  | Mult(e1,e2,_) -> 
      (match e1 with
        | IConst (i, _) -> CMult(i,(cpure_to_coqpure_exp e2))
        | _ -> match e2 with
            | IConst (i, _) -> CMult(i,(cpure_to_coqpure_exp e1))
            | _ -> illegal_format "[coqinf.ml] Non-linear arithmetic is not supported by Omega.")
  | _ -> illegal_format "Cannot use the expression with CoqInf Solver" 

let rec cpure_to_coqpure_vars (vl) (cbf: coq_formula) : coq_formula =
match vl with 
  | sv::vrest -> if not (is_int_var sv) 
    then let add_f = CAnd(CBForm(CNeq((CVar(string_of_spec_var sv),(Cconst(CInfConst))))),
                          CBForm(CNeq((CVar(string_of_spec_var sv),(Cconst(CNegInfConst)))))) in
         let cbf  = CAnd(add_f,cbf) in
         cpure_to_coqpure_vars vrest cbf
    else cbf
  | [] -> cbf

let cpure_to_coqpure_vars (vl) (cbf: coq_formula) : coq_formula =
Gen.Profiling.no_2 "cpure_to_coqpure_vars" cpure_to_coqpure_vars vl cbf

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
    | EqMax(e1,e2,e3, _) ->CEqMax ((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2),(cpure_to_coqpure_exp e3))
    | EqMin(e1,e2,e3, _) ->CEqMin ((cpure_to_coqpure_exp e1),(cpure_to_coqpure_exp e2),(cpure_to_coqpure_exp e3))
    | _ -> illegal_format ("Cannot use the constraint with CoqInf Solver "^(Cprinter.string_of_b_formula bf))

let rec cpure_to_coqpure (f: formula) : coq_formula =
match f with
  | BForm(bf,_) ->(*let pf,_ = bf in (match pf with 
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
                   | _ -> *)CBForm(cpure_to_coqpure_bformula bf)
  | And(f1,f2,_) -> CAnd ((cpure_to_coqpure f1),(cpure_to_coqpure f2))
  | Or(f1,f2,_,_) -> COr ((cpure_to_coqpure f1),(cpure_to_coqpure f2))
  | Not(f,_,_) -> CNot (cpure_to_coqpure f)
  | Forall(sv,f,_,_) -> 
(* type information is not reliable checking it here will lead to diff between sleek and hip output *)
      (*if is_int_var sv then*) CForall((string_of_spec_var sv),(cpure_to_coqpure f))
      (*else (*let () = print_endline ("Is_not_INFVar:  "^(Cprinter.string_of_spec_var sv)) in*)
      CForall_Fin((string_of_spec_var sv),(cpure_to_coqpure f))*)
  | Exists(sv,f,_,_) -> 
     (* if is_int_var sv then*) CExists((string_of_spec_var sv),(cpure_to_coqpure f))
     (* else CExists_Fin((string_of_spec_var sv),(cpure_to_coqpure f))*)
  | AndList _ -> illegal_format "Cannot use AndList for CoqInf Solver"

let cpure_to_coqpure (f:formula) :coq_formula = 
Debug.no_1 "cpure_to_coqpure" Cprinter.string_of_pure_formula (fun _ -> "") cpure_to_coqpure f

let string_to_spec_var str_sv = 
(* found bug with primed variables and fixed during testing *) 
  let len = (String.length str_sv) in
  if ((String.get str_sv (len-1)) == '\'') 
  then SpecVar(Int,(String.sub str_sv 0 (len-1)),Primed)
  else SpecVar(Int,str_sv,Unprimed)

let rec coqpure_to_cpure_exp (e:coq_exp) : exp =
  match e with 
    | CVar s -> if s="ZInfinity" then mkInfConst no_pos (* another bug fix with strings *)
      else if s="ZNegInfinity" then NegInfConst(zinf_str, no_pos) (* bug fixed by testing neginfconst mkNegInfConst no_pos*)
      else Var((string_to_spec_var s),no_pos)
    | Cconst c -> 
        (match c with
          | CInfConst -> mkInfConst no_pos
          | CNegInfConst -> NegInfConst(zinf_str, no_pos) (* bug fixed by testing neginfconst*)
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
      | CEqMax(e1,e2,e3) -> EqMax((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),(coqpure_to_cpure_exp e3),no_pos)
      | CEqMin(e1,e2,e3) -> EqMin((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),(coqpure_to_cpure_exp e3),no_pos)
      | CNeq(e1,e2) -> Neq((coqpure_to_cpure_exp e1),(coqpure_to_cpure_exp e2),no_pos)
  in (pf,None)

let rec coqpure_to_cpure (cf: coq_formula) : formula =
  match cf with
    | CBForm(cbf) -> BForm(coqpure_to_cpure_bformula cbf,None)
(*    | CAnd(e1,e2) -> And((coqpure_to_cpure e1),(coqpure_to_cpure e2),no_pos)
    | COr(e1,e2) -> Or((coqpure_to_cpure e1),(coqpure_to_cpure e2),None,no_pos)*)
(* *)
    | CAnd(e1,e2) -> Cpure.mkAnd (coqpure_to_cpure e1) (coqpure_to_cpure e2) no_pos
    | COr(e1,e2) -> Cpure.mkOr (coqpure_to_cpure e1) (coqpure_to_cpure e2) None no_pos
    | CNot f -> mkNot (coqpure_to_cpure f) None no_pos
    | CForall(sv,f)  (*mkForall [(string_to_spec_var sv)] (coqpure_to_cpure f) None no_pos*)
    | CExists(sv,f) ->  failwith "coqinf.ml Infinity quantifiers should be all eliminated"
(*mkExists [(string_to_spec_var sv)] (coqpure_to_cpure f) None no_pos*)
    | CForall_Fin(sv,f) -> mkForall [(string_to_spec_var sv)] (coqpure_to_cpure f) None no_pos
    | CExists_Fin(sv,f) -> mkExists [(string_to_spec_var sv)] (coqpure_to_cpure f) None no_pos

let coqpure_to_cpure (f:coq_formula) : formula = 
Debug.no_1 "coqpure_to_cpure" (fun _ -> "")  Cprinter.string_of_pure_formula coqpure_to_cpure f

let rec add_exists (f: formula) vl : formula =
match vl with
  | [] -> f
  | x::xs -> Exists(x,(add_exists f xs),None,no_pos)

let rec close_form_cpure (f: formula) : formula =
(*if List.length (fv f) > 0 
then (close_form_cpure (Exists((List.hd (fv f)),f,None,no_pos)))
else f*)
 mkExists (fv f) f None no_pos 

let rec close_form_cpure_all (f: formula) : formula =
(*if List.length (fv f) > 0 
then (close_form_cpure_all (Forall((List.hd (fv f)),f,None,no_pos)))
else f*)
mkForall (fv f) f None no_pos



let rec drop_quantifier (f:formula) vl : formula = 
match f with 
  | And(f1,f2,_) -> Cpure.mkAnd (drop_quantifier f1 vl) (drop_quantifier f2 vl) no_pos
  | Or(f1,f2,_,_) -> Cpure.mkOr (drop_quantifier f1 vl) (drop_quantifier f2 vl) None no_pos
  | Not(f,_,_) -> mkNot (drop_quantifier f vl) None no_pos
  | Forall(sv,g,_,_) -> if (Gen.BList.mem_eq eq_spec_var sv vl) 
    then (drop_quantifier g vl)
    else mkForall [sv] (drop_quantifier g vl) None no_pos
  | Exists(sv,g,_,_) ->if (Gen.BList.mem_eq eq_spec_var sv vl) 
    then (drop_quantifier g vl)
    else mkExists [sv] (drop_quantifier g vl) None no_pos
  | _ -> f

let drop_quantifier (f:formula) vl : formula =
   Gen.Profiling.no_1 "drop_quantifier" drop_quantifier f vl

let drop_quantifier (f:formula) vl :formula =
  let pr = !print_formula in 
  Debug.no_2 "drop_quant" pr (fun c -> "") pr drop_quantifier f vl 

let drop_forall (f:formula) :formula = 
  let rec helper f =
  let f_f f = 
    match f with
      | Forall(qid,qf,fl,pos) -> let fresh_fr = fresh_spec_vars [qid] in
                                 let st = List.combine [qid] fresh_fr in
                                 let rename_exist_vars  = subst st qf in
                                 Some((helper rename_exist_vars))
      | And _ | AndList _ | Or _  -> None
      | Not _ | BForm _ | Exists _ -> Some(f)
  in
  let f_bf bf = Some bf in
  let f_e e = Some e in
  map_formula f (f_f,f_bf,f_e)
  in helper f

let drop_forall (f:formula) :formula =
  let pr = !print_formula in 
  Debug.no_1 "drop_forall_inf" pr pr drop_forall f 

let close_form_cpure (f:formula) :formula =
Debug.no_1 "close_form_cpure" Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula
close_form_cpure  f

let remove_redundant_after_inf (f:formula):formula =
  let l_disj = split_disjunctions f in
  let prun_l = remove_redundant_helper l_disj [] in
  join_disjunctions prun_l

let remove_redundant_after_inf (f:formula):formula =
Gen.Profiling.no_1 "remove_redundant_after_inf" remove_redundant_after_inf f

let check_sat_inf_formula (f: formula) : formula = 
  (*let f = drop_exists f in*)
  (*let f = remove_redundant (remove_redundant_after_inf f) in*)
  let var_lst = fv f in
  (*let var_lst_not_inf = List.filter (fun c -> not(is_int_var c)) var_lst in*)
  let f = (close_form_cpure f) in
 (* let _ = print_endline("F: "^Cprinter.string_of_pure_formula f) in *)
  (*let f = drop_quantifier f var_lst_not_inf in*)
(*  let _ = print_endline("DF: "^Cprinter.string_of_pure_formula f) in *)
  let f = (cpure_to_coqpure f) in
(*  let f = cpure_to_coqpure_vars var_lst f in *)
  let vl = get_inf_vars f in
  let f = coqpure_to_cpure (coq_infsolver_to_coqpure_form (transform_ZE_to_string 
                  (coqpure_to_coq_infsolver_form f vl))) in
  let f = drop_quantifier f var_lst in
  let f = remove_redundant (remove_redundant_after_inf f) in 
  f 

let check_sat_inf_formula (f:formula) :formula =
Debug.no_1 "check_sat_coq" Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula
check_sat_inf_formula f

let check_sat_inf_formula (f:formula) :formula =
Gen.Profiling.do_1 "check_sat_coq" check_sat_inf_formula f

let check_imply_inf_formula (a: formula) (c:formula) : formula = 
  (*let a = drop_exists a in*)
  let f = Cpure.mkOr (mkNot a None no_pos) c None no_pos in
 (*let f = remove_redundant (remove_redundant_after_inf f) in*)
  let var_lst = fv f in
  (*let var_lst_not_inf = List.filter (fun c -> not(is_int_var c)) var_lst in*)
  let f = (close_form_cpure_all f) in
  (*let f = drop_quantifier f var_lst_not_inf in*)
  let f = (cpure_to_coqpure f) in
  let vl = get_inf_vars f in
  (*let f = cpure_to_coqpure_vars var_lst f in *)
(*let f = mkAnd a (mkNot_dumb c None no_pos) no_pos in*)
  let f = coqpure_to_cpure (coq_infsolver_to_coqpure_form (transform_ZE_to_string
                  (coqpure_to_coq_infsolver_form f vl))) in
  let f = drop_quantifier f var_lst in
  let f = remove_redundant (remove_redundant_after_inf f) in 
  f

let check_imply_inf_formula (a: formula) (c:formula) : formula = 
Debug.no_2 "check_imply_coq" 
Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula 
check_imply_inf_formula a c

let check_imply_inf_formula (a: formula) (c:formula) :formula =
Gen.Profiling.no_1 "check_imply_coq" check_imply_inf_formula a c

let fresh_l_name () = SpecVar(Int,fresh_old_name "l_",Unprimed)

let fresh_u_name () = SpecVar(Int,fresh_old_name "u_",Unprimed)

let rec generate_oct_inv (svl: spec_var list) : formula list =
let mk_inv_1 v = 
  let i1 = BForm(((mkLte (mkVar (fresh_l_name ()) no_pos) (mkVar v no_pos) no_pos),None),None) in
  let i2 = BForm(((mkLte (mkVar v no_pos) (mkVar (fresh_u_name ()) no_pos) no_pos),None),None) in
  Cpure.mkAnd i1 i2 no_pos 
in
let mk_inv_2_add x y = 
  let x = mkVar x no_pos in
  let y = mkVar y no_pos in
  let add_xy = mkAdd x y no_pos in
  let i1 = BForm(((mkLte (mkVar (fresh_l_name ()) no_pos) add_xy no_pos),None),None) in
  let i2 = BForm(((mkLte add_xy (mkVar (fresh_u_name ()) no_pos) no_pos),None),None) in
  (Cpure.mkAnd i1 i2 no_pos)
in
let mk_inv_2_sub x y =
  let x = mkVar x no_pos in
  let y = mkVar y no_pos in
  let sub_xy = mkSubtract x y no_pos in
  let i3 = BForm(((mkLte (mkVar (fresh_l_name ()) no_pos) sub_xy no_pos),None),None) in
  let i4 = BForm(((mkLte sub_xy (mkVar (fresh_u_name ()) no_pos) no_pos),None),None) in
  (Cpure.mkAnd i3 i4 no_pos)
in 
let mk_inv_2_min x y =
  let x = mkVar x no_pos in
  let y = mkVar y no_pos in
  let new_name = ("min"^(fresh_trailer())) in
  let nv = (mkVar (SpecVar(Int,new_name,Unprimed)) no_pos) in
  let min_xy = BForm(((mkEqMin nv x y no_pos),None),None) in
  let i3 = BForm(((mkLte (mkVar (fresh_l_name ()) no_pos) nv no_pos),None),None) in
  let i4 = BForm(((mkLte nv (mkVar (fresh_u_name ()) no_pos) no_pos),None),None) in
  mkAnd (Cpure.mkAnd i3 i4 no_pos) min_xy no_pos
in 
let mk_inv_2_max x y =
  let x = mkVar x no_pos in
  let y = mkVar y no_pos in
  let new_name = ("max"^(fresh_trailer())) in
  let nv = (mkVar (SpecVar(Int,new_name,Unprimed)) no_pos) in
  let max_xy = BForm(((mkEqMax nv x y no_pos),None),None) in
  let i1 = BForm(((mkLte (mkVar (fresh_l_name ()) no_pos) nv no_pos),None),None) in
  let i2 = BForm(((mkLte nv (mkVar (fresh_u_name ()) no_pos) no_pos),None),None) in
  mkAnd (Cpure.mkAnd i1 i2 no_pos) max_xy no_pos
in 
match svl with
  | [] -> []
  | x::xs -> let f1 = mk_inv_1 x in
             let f2 = (List.map (fun y -> mk_inv_2_add x y) xs) in
             let f3 = (List.map (fun y -> mk_inv_2_sub x y) xs) in
             let f4 = (List.map (fun y -> mk_inv_2_min x y) xs) in
             let f5 = (List.map (fun y -> mk_inv_2_max x y) xs) in
             (*let f4 = List.map (fun y -> Cpure.mkAnd f1 y no_pos) f3 in
             let f5 = List.map (fun y -> (mk_inv_1 y)) xs in
             let f6 = List.combine f5 f3 in
             let f4 = List.map (fun (x,y) -> Cpure.mkAnd y (Cpure.mkAnd f1 x no_pos) no_pos) f6 in*)
             f1::f2@f3@(generate_oct_inv xs)
             (*let f2 = join_conjunctions (List.map (fun y -> mk_inv_2 x y) xs) in
             let fx = (Cpure.mkAnd f1 f2 no_pos) in
             Cpure.mkAnd fx (generate_oct_inv xs) no_pos*)

let get_svl relf = 
match relf with
  | BForm ((RelForm (name,args,_),_),_) -> List.concat (List.map afv args)
  | _ -> []

let strongest_inv f = 
  let f_f f = None in
  let f_bf bf = let pf,l = bf in
    match pf with
    | Lte(a1,a2,p) -> Some((Eq(a1,a2,p),l))
    | _ -> Some bf in
  let f_e e = Some e
  in map_formula f (f_f,f_bf,f_e)

let qe_fixpoint rel_def = 
  let svl = get_svl (fst rel_def) in
  let rsv = name_of_rel_form (fst rel_def) in
  let octinv_lst = generate_oct_inv svl in
  (*let flist = list_of_disjs (snd rel_def) in*)
  let flist = ([(snd rel_def)]) in
  let aux f octinv = 
  let f_fa f = 
    let rec f_f f = match f with
    | BForm((RelForm(n,a,_),_),_) -> 
        if eq_spec_var rsv n                      
        then let sl = List.combine svl (List.concat (List.map afv a)) in
             (subst sl octinv)  
        else f
    | Or(f1,f2,l,p) -> (mkOr (f_f f1) (f_f f2) l p) 
    | And(f1,f2,p) ->  (mkAnd (f_f f1) (f_f f2) p)
    | Exists(sv,f,l,p) -> (Exists(sv,(f_f f),l,p))
    | Forall(sv,f,l,p) -> (Forall(sv,(f_f f),l,p))
    | Not(f,l,p) -> (Not((f_f f),l,p))
    | _ -> f
  in Some(f_f f) in
  let f_bf bf = Some bf in
  let f_e e = (Some e) in
  let orig_vl = fv f in
  let f1 = map_formula f (f_fa,f_bf,f_e) in
  let fa = Cpure.mkOr (mkNot f1 None no_pos) octinv None no_pos in
  (*let fa = Cpure.mkAnd f1 (mkNot octinv None no_pos) no_pos in*)
  (*let fa = Cpure.mkOr (mkNot octinv None no_pos) f1 None no_pos in*)
  (*let _ = print_endline ("FA: "^Cprinter.string_of_pure_formula fa ) in*)
  let var_lst = List.filter (fun v -> not(mem_svl v orig_vl)) (fv fa) in
  let f = (close_form_cpure_all fa) in
  let f = drop_quantifier f var_lst in
  (*Omega.is_valid f !Globals.imply_timeout_limit*)
  let r = (Omega.simplify f) in
  (*let r = mkNot r None no_pos in*)
  let res = 
    if (is_False r) && !allow_inf_qe_coq then 
      let f = (close_form_cpure f) in
      let f = (cpure_to_coqpure f) in
      let vl = List.map (fun sv -> string_of_spec_var sv) var_lst in
      let f = coqpure_to_cpure (coq_infsolver_to_coqpure_form (transform_ZE_to_string 
                                                                 (coqpure_to_coq_infsolver_form f vl))) in
      let f = remove_redundant (remove_redundant_after_inf f) in 
      Omega.simplify f
    else if (is_False r) && !allow_inf_qe then
      let inf_inst = Infinity.gen_instantiations var_lst [] in
      let inf_inst = inf_inst in
      let flist = List.map (fun c -> Omega.simplify (Infinity.normalize_inf_formula_sat (mkAnd f c no_pos))) inf_inst in
      (conj_of_list flist no_pos)
  (*Omega.qe f*)
  else r
  in (f1,res) in
  let fl = List.map (fun f -> (join_conjunctions (List.map (fun c ->
      let fa,fu = aux f c in
     if (is_True fu) then fu
      else 
        let vl = fv fu in
        (*let fulst = list_of_disjs fu in*)
        Omega.simplify (add_exists (mkAnd c (strongest_inv fu) no_pos) vl)) 
        (*Omega.simplify (add_exists (mkOr f1 c None no_pos) vl))*)
        octinv_lst))) flist in
       (* Omega.simplify (mkExists vl (mkOr fa (mkNot fu None no_pos) None no_pos) None no_pos))*)
  (disj_of_list fl no_pos)
 (*(join_conjunctions (List.map Omega.hull fl))*)
 (* let cnsts = (list_of_conjs (Omega.hull f)) in*)
  (*Omega.gist  (join_conjunctions (List.tl fl)) (List.hd fl)*)

let qe_fixpoint rel_def = 
  let pr0 = !print_formula in
  let pr1 = (pr_pair pr0 pr0) in
Debug.no_1 "qe_fixpoint" pr1 Cprinter.string_of_pure_formula qe_fixpoint rel_def
