Require Import Theory.
Require Import Transformation.
Require Import ZArith.
Require Import String Ascii.
Require Import Bool.
Require Import NPeano.
Require Import FunctionalExtensionality.

(* String Variable Type for Extraction  *)
Module Type STRVAR <: VARIABLE.
  Parameter var : Type. (* who konws what it is, but in reality it's OCaml string *)
  Parameter var_eq_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
  Parameter var2string : var -> string.
  Parameter string2var : string -> var.
  Axiom var2String2var : forall v, string2var(var2string v) = v.
  Axiom String2var2String : forall s, var2string(string2var s) = s.
End STRVAR.

Module InfSolverExtract (sv: STRVAR).

(* Module None_False_Bool := NoneAlwaysFalse Bool_Val. *)
(* Module IS := InfSolver sv Bool_Val None_False_Bool.   (* Two Value Logic and None is always False *) *)

(* Module Three_Val_False := NoneAlwaysFalse Three_Val. *)
(* Module IS := InfSolver sv Three_Val Three_Val_False. (* Use Three Value Logic and None is False *) *)
 
 Module IS := InfSolver sv Three_Val None3ValRel FinZero InfZeroAll. (* Use Three Value Logic, None is Unknown and Inf*0 is 0 *)

(* Extraction Algorithms *)
Open Scope Z_scope.

Definition Z_of_bool (b : bool) := if b then 1 else 0.

(* This coercion is used to make the next function shorter to write and read *)

Coercion Z_of_bool : bool >-> Z.

Definition Z_of_ascii a :=
  match a with
   Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
     b1 + 2 * (b2 + 2 * (b3 + 2 * (b4 + 2 *
      (b5 + 2 * (b6 + 2 * (b7 + 2 * b8))))))
  end.

Definition Z_of_0 := Eval compute in Z_of_ascii "0".

Definition Z_of_digit a :=
   let v := Z_of_ascii a - Z_of_0 in
   match v ?= 0 with
     Lt => None | Eq => Some v |
     Gt => match v ?= 10 with Lt => Some v | _ => None end
   end.

Fixpoint Z_of_string' (a: string) (n: Z) : option Z:=
match a with
    EmptyString => None
    | String a s' =>
          match Z_of_digit a with
          None => None
        | Some va => match Z_of_string' s' (n+1) with
                     None => Some va
                   | Some vs => Some (va * 10 ^ n + vs)
                     end
         end
end.

Definition Z_of_string (a: string) : Z := match (Z_of_string' a 0) with
| Some z => z
| None => 0
end.

Close Scope Z_scope.

Open Scope char_scope.

Definition natToDigit (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

Definition string_of_Z (n: Z) : string :=
 writeNat(Zabs_nat n).

Inductive ZExp (const_type : Type) : Type :=
  | ZExp_Var: sv.var -> ZExp const_type
  | ZExp_Const : const_type -> ZExp const_type
  | ZExp_Add : ZExp const_type -> ZExp const_type -> ZExp const_type
  | ZExp_Sub : ZExp const_type -> ZExp const_type -> ZExp const_type
  | ZExp_Mult : sv.var -> ZExp const_type -> ZExp const_type.

Inductive ZBF (const_type : Type) : Type :=
  | ZBF_Const : bool -> ZBF const_type
  | ZBF_Lt : ZExp const_type -> ZExp const_type -> ZBF const_type
  | ZBF_Lte : ZExp const_type -> ZExp const_type -> ZBF const_type
  | ZBF_Gt : ZExp const_type -> ZExp const_type -> ZBF const_type
  | ZBF_Gte : ZExp const_type -> ZExp const_type -> ZBF const_type
  | ZBF_Eq : ZExp const_type -> ZExp const_type -> ZBF const_type
  | ZBF_Eq_Max : ZExp const_type -> ZExp const_type -> ZExp const_type -> ZBF const_type
  | ZBF_Eq_Min : ZExp const_type -> ZExp const_type -> ZExp const_type -> ZBF const_type
  | ZBF_Neq : ZExp const_type -> ZExp const_type -> ZBF const_type.

Inductive ZF (const_type : Type) : Type :=
  | ZF_BF : ZBF const_type -> ZF const_type
  | ZF_And : ZF const_type -> ZF const_type -> ZF const_type
  | ZF_Or : ZF const_type -> ZF const_type -> ZF const_type
  | ZF_Not : ZF const_type -> ZF const_type
  | ZF_Forall_Fin : sv.var -> ZF const_type -> ZF const_type
  | ZF_Exists_Fin : sv.var -> ZF const_type -> ZF const_type
  | ZF_Forall : sv.var -> ZF const_type -> ZF const_type
  | ZF_Exists : sv.var -> ZF const_type -> ZF const_type.

Inductive ZE : Type :=
  | ZE_Fin : sv.var -> ZE
  | ZE_Inf : ZE
  | ZE_NegInf : ZE.

Fixpoint convert_ZF_to_IAZF_Exp (exp: ZExp ZE) : IS.IA.ZExp :=
match exp with
  | ZExp_Var v => IS.IA.ZExp_Var v
  | ZExp_Const c => match c with
                      | ZE_NegInf => IS.IA.ZExp_Const (Some(PureInfinity.N.ZE_NegInf))
                      | ZE_Inf => IS.IA.ZExp_Const (Some(PureInfinity.N.ZE_Inf))
                      | ZE_Fin v => IS.IA.ZExp_Const (Some(PureInfinity.N.ZE_Fin (Z_of_string (sv.var2string v))))
                    end
  | ZExp_Add e1 e2 => IS.IA.ZExp_Add (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2)
  | ZExp_Sub e1 e2 => IS.IA.ZExp_Sub (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2)
  | ZExp_Mult s e => IS.IA.ZExp_Mult (Z_of_string (sv.var2string s)) (convert_ZF_to_IAZF_Exp e)
end.

Fixpoint convert_ZF_to_IAZF_BF (bf: ZBF ZE) : IS.IA.ZBF :=
match bf with
  | ZBF_Const b => if b then IS.IA.ZBF_Const Three_Val.VTrue else IS.IA.ZBF_Const Three_Val.VFalse
  | ZBF_Lt e1 e2 => IS.IA.ZBF_Lt (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2)
  | ZBF_Lte e1 e2 => IS.IA.ZBF_Lte (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2)
  | ZBF_Gt e1 e2 => IS.IA.ZBF_Gt (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2)
  | ZBF_Gte e1 e2 => IS.IA.ZBF_Gte (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2)
  | ZBF_Eq e1 e2 => IS.IA.ZBF_Eq (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2)
  | ZBF_Eq_Max e1 e2 e3 => IS.IA.ZBF_Eq_Max (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2) (convert_ZF_to_IAZF_Exp e3)
  | ZBF_Eq_Min e1 e2 e3 => IS.IA.ZBF_Eq_Min (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2) (convert_ZF_to_IAZF_Exp e3)
  | ZBF_Neq e1 e2 => IS.IA.ZBF_Neq (convert_ZF_to_IAZF_Exp e1) (convert_ZF_to_IAZF_Exp e2)
end.

Fixpoint convert_ZF_to_IAZF (f: ZF ZE) : IS.IA.ZF :=
match f with
  | ZF_BF bf => IS.IA.ZF_BF (convert_ZF_to_IAZF_BF bf)
  | ZF_And f1 f2 => IS.IA.ZF_And (convert_ZF_to_IAZF f1) (convert_ZF_to_IAZF f2)
  | ZF_Or f1 f2 => IS.IA.ZF_Or (convert_ZF_to_IAZF f1) (convert_ZF_to_IAZF f2)
  | ZF_Not g => IS.IA.ZF_Not (convert_ZF_to_IAZF g)
  | ZF_Forall_Fin v g => IS.IA.ZF_Forall v PureInfinity.Q_Z (convert_ZF_to_IAZF g)
  | ZF_Exists_Fin v g => IS.IA.ZF_Exists v PureInfinity.Q_Z (convert_ZF_to_IAZF g)
  | ZF_Forall v g => IS.IA.ZF_Forall v PureInfinity.Q_ZE (convert_ZF_to_IAZF g)
  | ZF_Exists v g => IS.IA.ZF_Exists v PureInfinity.Q_ZE (convert_ZF_to_IAZF g)
end.

Fixpoint convert_FAZF_to_ZF_Exp (exp: IS.FA.ZExp) :ZExp sv.var :=
match exp with
  | IS.FA.ZExp_Var v => ZExp_Var sv.var v
  | IS.FA.ZExp_Const c => ZExp_Const sv.var (sv.string2var (string_of_Z c))
  | IS.FA.ZExp_Add e1 e2 => ZExp_Add sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2)
  | IS.FA.ZExp_Sub e1 e2 => ZExp_Sub sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2)
  | IS.FA.ZExp_Inv e => ZExp_Sub sv.var (ZExp_Const sv.var (sv.string2var (string_of_Z 0))) (convert_FAZF_to_ZF_Exp e)
  | IS.FA.ZExp_Mult c e => ZExp_Mult sv.var (sv.string2var (string_of_Z c)) (convert_FAZF_to_ZF_Exp e)
end.

Fixpoint convert_FAZF_to_ZF_BF (bf: IS.FA.ZBF) :ZBF sv.var :=
match bf with
  | IS.FA.ZBF_Const b => match b with 
                           | Three_Val.VTrue => ZBF_Const sv.var true
                           | _ => ZBF_Const sv.var false
                         end
  | IS.FA.ZBF_Lt e1 e2 => ZBF_Lt sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2)
  | IS.FA.ZBF_Lte e1 e2 => ZBF_Lte sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2)
  | IS.FA.ZBF_Gt e1 e2 => ZBF_Gt sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2)
  | IS.FA.ZBF_Gte e1 e2 => ZBF_Gte sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2)
  | IS.FA.ZBF_Eq e1 e2 => ZBF_Eq sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2)
  | IS.FA.ZBF_Eq_Max e1 e2 e3 => ZBF_Eq_Max sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2) (convert_FAZF_to_ZF_Exp e3)
  | IS.FA.ZBF_Eq_Min e1 e2 e3 => ZBF_Eq_Min sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2) (convert_FAZF_to_ZF_Exp e3)
  | IS.FA.ZBF_Neq e1 e2 => ZBF_Neq sv.var (convert_FAZF_to_ZF_Exp e1) (convert_FAZF_to_ZF_Exp e2)
end.

Fixpoint convert_FAZF_to_ZF (f: IS.FA.ZF) : ZF sv.var :=
match f with
  | IS.FA.ZF_BF bf => ZF_BF sv.var (convert_FAZF_to_ZF_BF bf)
  | IS.FA.ZF_And f1 f2 => ZF_And sv.var (convert_FAZF_to_ZF f1) (convert_FAZF_to_ZF f2)
  | IS.FA.ZF_Or f1 f2 => ZF_Or sv.var (convert_FAZF_to_ZF f1) (convert_FAZF_to_ZF f2)
  | IS.FA.ZF_Imp f1 f2 => ZF_Or sv.var (ZF_Not sv.var (convert_FAZF_to_ZF f1)) (convert_FAZF_to_ZF f2)
  | IS.FA.ZF_Not g => ZF_Not sv.var (convert_FAZF_to_ZF g)
  | IS.FA.ZF_Forall v _ g => ZF_Forall_Fin sv.var v (convert_FAZF_to_ZF g)
  | IS.FA.ZF_Exists v _ g => ZF_Exists_Fin sv.var v (convert_FAZF_to_ZF g)
end.

(* For the actual algorithm we only need string as we don't do any operation
on Z *)
Definition transform_ZE_to_string (f:ZF ZE): ZF sv.var :=
convert_FAZF_to_ZF (IS.T(convert_ZF_to_IAZF f)).
(*convert_FAZRForm_to_ZF_Z (FA.hi2zrform (T(convert_ZF_to_IAZF(f)))).*)
(*(convert_ZE_to_string (norm_F (elim_quant f)))*)

Definition transform_ZE_to_string_simplify (f:ZF ZE): ZF sv.var :=
convert_FAZF_to_ZF (IS.FA.simplifyZF(IS.T(convert_ZF_to_IAZF f))).

End InfSolverExtract.

Extraction Language Ocaml.
Set Extraction Optimize.
Set Extraction AccessOpaque.
Extract Inductive bool => bool [true false].
Extract Inductive sumbool => bool [true false].
Extract Inductive ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *) 
(fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b 
                                              then 1 lsl i 
                                              else 0 in 
                                  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *) 
(fun f c -> let n = Char.code c in 
            let h i = (n land (1 lsl i)) <> 0 in 
            f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Extract Constant zero => "'\000'".
Extract Constant one => "'\001'".
Extract Constant shift =>
 "fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".
Extract Inlined Constant ascii_dec => "(=)".
Extract Inductive string => "char list" [ "[]" "(::)" ].
(*Extract Inlined Constant string_dec => "(fun s1 s2 -> (String.compare s1 s2) = 0)".*)
(*Extract Inductive string => string ["[]" "(::)"].*)
(*Extract Constant string_dec => "is_eq".*)
Extraction "infsolver.ml" InfSolverExtract.
