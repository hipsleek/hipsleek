(*
  Created 19-Feb-2006

  core pure constraints, including arithmetic and pure pointer
*)

open Globals

(* spec var *)
type spec_var =
  | SpecVar of (typ * ident * primed)

and typ =
  | Prim of prim_type
  | OType of ident (* object type. enum type is already converted to int *)

type formula =
  | BForm of b_formula
  | And of (formula * formula * loc)
  | Or of (formula * formula * loc)
  | Not of (formula * loc)
  | Forall of (spec_var * formula * loc)
  | Exists of (spec_var * formula * loc)

(* Boolean constraints *)
and b_formula =
  | BConst of (bool * loc)
  | BVar of (spec_var * loc)
  | Lt of (exp * exp * loc)
  | Lte of (exp * exp * loc)
  | Gt of (exp * exp * loc)
  | Gte of (exp * exp * loc)
  | Eq of (exp * exp * loc) (* these two could be arithmetic or pointer *)
  | Neq of (exp * exp * loc)
  | EqMax of (exp * exp * exp * loc) (* first is max of second and third *)
  | EqMin of (exp * exp * exp * loc) (* first is min of second and third *)
	  (* bag formulas *)
  | BagIn of (spec_var * exp * loc)
  | BagNotIn of (spec_var * exp * loc)
  | BagSub of (exp * exp * loc)
  | BagMin of (spec_var * spec_var * loc)
  | BagMax of (spec_var * spec_var * loc)



(* Expression *)
and exp =
  | Null of loc
  | Var of (spec_var * loc)
  | IConst of (int * loc)
  | Add of (exp * exp * loc)
  | Subtract of (exp * exp * loc)
  | Mult of (int * exp * loc)
  | Max of (exp * exp * loc)
  | Min of (exp * exp * loc)
	  (* bag expressions *)
  | Bag of (exp list * loc)
  | BagUnion of (exp list * loc)
  | BagIntersect of (exp list * loc)
  | BagDiff of (exp * exp * loc)


and relation = (* for obtaining back results from Omega Calculator. Will see if it should be here*)
  | ConstRel of bool
  | BaseRel of (exp list * formula)
  | UnionRel of (relation * relation)

let get_exp_type (e : exp) : typ = match e with
  | Null _ -> OType ""
  | Var (SpecVar (t, _, _), _) -> t
  | IConst _ | Add _ | Subtract _ | Mult _ | Max _ | Min _  -> Prim Int
  | Bag _ | BagUnion _ | BagIntersect _ | BagDiff _ -> Prim Globals.Bag

(* free variables *)

let null_var = SpecVar (OType "", "null", Unprimed)

let rec fv (f : formula) : spec_var list =
  let tmp = fv_helper f in
  let res = remove_dups tmp in
	res

and fv_helper (f : formula) : spec_var list = match f with
  | BForm b -> bfv b
  | And (p1, p2, _) -> combine_pvars p1 p2
  | Or (p1, p2, _) -> combine_pvars p1 p2
  | Not (nf, _) -> fv_helper nf
  | Forall (qid, qf, _) -> remove_qvar qid qf
  | Exists (qid, qf, _) -> remove_qvar qid qf

and combine_pvars p1 p2 =
  let fv1 = fv_helper p1 in
  let fv2 = fv_helper p2 in
    fv1 @ fv2

and remove_qvar qid qf =
  let qfv = fv_helper qf in
    difference qfv [qid]

and bfv (bf : b_formula) = match bf with
  | BConst _ -> []
  | BVar (bv, _) -> [bv]
  | Lt (a1, a2, _) -> combine_avars a1 a2
  | Lte (a1, a2, _) -> combine_avars a1 a2
  | Gt (a1, a2, _) -> combine_avars a1 a2
  | Gte (a1, a2, _) -> combine_avars a1 a2
  | Eq (a1, a2, _) -> combine_avars a1 a2
  | Neq (a1, a2, _) -> combine_avars a1 a2
  | EqMax (a1, a2, a3, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
	  let fv3 = afv a3 in
		Util.remove_dups (fv1 @ fv2 @ fv3)
  | EqMin (a1, a2, a3, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
	  let fv3 = afv a3 in
		Util.remove_dups (fv1 @ fv2 @ fv3)
	| BagIn (v, a1, _) ->
		let fv1 = afv a1 in
		[v] @ fv1
	| BagNotIn (v, a1, _) ->
		let fv1 = afv a1 in
		[v] @ fv1
  | BagSub (a1, a2, _) -> combine_avars a1 a2
	| BagMax (v1, v2, _) ->Util.remove_dups ([v1] @ [v2])
	| BagMin (v1, v2, _) ->Util.remove_dups ([v1] @ [v2])

and combine_avars (a1 : exp) (a2 : exp) : spec_var list =
  let fv1 = afv a1 in
  let fv2 = afv a2 in
    Util.remove_dups (fv1 @ fv2)

and afv (af : exp) : spec_var list = match af with
  | Null _ -> []
  | Var (sv, _) -> [sv]
  | IConst _ -> []
  | Add (a1, a2, _) -> combine_avars a1 a2
  | Subtract (a1, a2, _) -> combine_avars a1 a2
  | Mult (c, a, _) -> afv a
  | Max (a1, a2, _) -> combine_avars a1 a2
  | Min (a1, a2, _) -> combine_avars a1 a2
  (*| BagEmpty (_) -> []*)
  | Bag (alist, _) -> let svlist = afv_bag alist in
  		Util.remove_dups svlist
  | BagUnion (alist, _) -> let svlist = afv_bag alist in
  		Util.remove_dups svlist
  | BagIntersect (alist, _) -> let svlist = afv_bag alist in
  		Util.remove_dups svlist
  | BagDiff(a1, a2, _) -> combine_avars a1 a2

and afv_bag (alist : exp list) : spec_var list = match alist with
	|[] -> []
	|a :: rest -> afv a @ afv_bag rest

and is_max_min a = match a with
  | Max _ | Min _ -> true
  | _ -> false

and isConstTrue p = match p with
  | BForm (BConst (true, pos)) -> true
  | _ -> false

and isConstFalse p = match p with
  | BForm (BConst (false, pos)) -> true
  | _ -> false

and is_null (e : exp) : bool = match e with
  | Null _ -> true
  | _ -> false

and is_zero (e : exp) : bool = match e with
  | IConst (0, _) -> true
  | _ -> false

and is_var (e : exp) : bool = match e with
  | Var _ -> true
  | _ -> false

and is_num (e : exp) : bool = match e with
  | IConst _ -> true
  | _ -> false

and is_var_num (e : exp) : bool = match e with
  | Var _ -> true
  | IConst _ -> true
  | _ -> false

and to_var (e : exp) : spec_var = match e with
  | Var (sv, _) -> sv
  | _ -> failwith ("to_var: argument is not a variable")

and can_be_aliased (e : exp) : bool = match e with
  | Var _ | Null _ -> true
	  (* null is necessary in this case: p=null & q=null.
		 If null is not considered, p=q is not inferred. *)
  | _ -> false

and get_alias (e : exp) : spec_var = match e with
  | Var (sv, _) -> sv
  | Null _ -> SpecVar (OType "", "null", Unprimed) (* it is safe to name it "null" as no other variable can be named "null" *)
  | _ -> failwith ("get_alias: argument is neither a variable nor null")

and is_object_var (sv : spec_var) = match sv with
  | SpecVar (OType _, _, _) -> true
  | _ -> false

and is_bag (e : exp) : bool = match e with
  | Bag (_, _)
  | BagUnion (_, _)
  | BagIntersect (_, _)
  | BagDiff (_, _, _) -> true
  | _ -> false

and is_arith (e : exp) : bool = match e with
  | Add _
  | Subtract _
  | Mult _
  | Min _
  | Max _ -> true
  | _ -> false

and is_bag_type (t : typ) = match t with
  | Prim Globals.Bag  -> true
  | _ -> false

and is_int_type (t : typ) = match t with
  | Prim Int -> true
  | _ -> false

and is_object_type (t : typ) = match t with
  | OType _ -> true
  | _ -> false

and should_simplify (f : formula) = match f with
  | Exists (_, Exists (_, Exists _, _), _) -> true
  | _ -> false

(* smart constructor *)

and mkRes t = SpecVar (t, res, Unprimed)

and mkAdd a1 a2 pos = Add (a1, a2, pos)

and mkSubtract a1 a2 pos = Subtract (a1, a2, pos)

and mkMult c a pos = Mult (c, a, pos)

and mkMax a1 a2 pos = Max (a1, a2, pos)

and mkMin a1 a2 pos = Min (a1, a2, pos)

and mkVar sv pos = Var (sv, pos)

and mkBVar v p pos = BVar (SpecVar (Prim Bool, v, p), pos)

and mkLt a1 a2 pos =
  if is_max_min a1 || is_max_min a2 then
	failwith ("max/min can only be used in equality")
  else
	Lt (a1, a2, pos)

and mkLte a1 a2 pos =
  if is_max_min a1 || is_max_min a2 then
	failwith ("max/min can only be used in equality")
  else
	Lte (a1, a2, pos)

and mkGt a1 a2 pos =
  if is_max_min a1 || is_max_min a2 then
	failwith ("max/min can only be used in equality")
  else
	Gt (a1, a2, pos)

and mkGte a1 a2 pos =
  if is_max_min a1 || is_max_min a2 then
	failwith ("max/min can only be used in equality")
  else
	Gte (a1, a2, pos)

and mkNull (v : spec_var) pos = mkEqExp (mkVar v pos) (Null pos) pos

and mkNeq a1 a2 pos =
  if is_max_min a1 || is_max_min a2 then
	failwith ("max/min can only be used in equality")
  else
	Neq (a1, a2, pos)

and mkEq a1 a2 pos =
  if is_max_min a1 && is_max_min a2 then
	failwith ("max/min can only appear in one side of an equation")
  else if is_max_min a1 then
	match a1 with
	  | Min (a11, a12, _) -> EqMin (a2, a11, a12, pos)
	  | Max (a11, a12, _) -> EqMax (a2, a11, a12, pos)
	  | _ -> failwith ("Presburger.mkAEq: something really bad has happened")
  else if is_max_min a2 then
	match a2 with
	  | Min (a21, a22, _) -> EqMin (a1, a21, a22, pos)
	  | Max (a21, a22, _) -> EqMax (a1, a21, a22, pos)
	  | _ -> failwith ("Presburger.mkAEq: something really bad has happened")
  else
	Eq (a1, a2, pos)

and mkAnd f1 f2 pos = match f1 with
  | BForm (BConst (false, _)) -> f1
  | BForm (BConst (true, _)) -> f2
  | _ -> match f2 with
      | BForm (BConst (false, _)) -> f2
      | BForm (BConst (true, _)) -> f1
      | _ -> And (f1, f2, pos)

and mkOr f1 f2 pos = match f1 with
  | BForm (BConst (false, _)) -> f2
  | BForm (BConst (true, _)) -> f1
  | _ -> match f2 with
      | BForm (BConst (false, _)) -> f1
      | BForm (BConst (true, _)) -> f2
      | _ -> Or (f1, f2, pos)

and mkEqExp (ae1 : exp) (ae2 : exp) pos = match (ae1, ae2) with
  | (Var v1, Var v2) ->
	  if eq_spec_var (fst v1) (fst v2) then
		mkTrue pos
	  else
		BForm (Eq (ae1, ae2, pos))
  | _ ->  BForm (Eq (ae1, ae2, pos))

and mkNeqExp (ae1 : exp) (ae2 : exp) pos = match (ae1, ae2) with
  | (Var v1, Var v2) ->
	  if eq_spec_var (fst v1) (fst v2) then
		mkFalse pos
	  else
		BForm (Neq (ae1, ae2, pos))
  | _ ->  BForm (Neq (ae1, ae2, pos))

and mkNot f pos0 = match f with
  | BForm bf -> begin
	  match bf with
		| BConst (b, pos) -> BForm (BConst ((not b), pos))
		| Lt (e1, e2, pos) -> BForm (Gte (e1, e2, pos))
		| Lte (e1, e2, pos) -> BForm (Gt (e1, e2, pos))
		| Gt (e1, e2, pos) -> BForm (Lte (e1, e2, pos))
		| Gte (e1, e2, pos) -> BForm (Lt (e1, e2, pos))
		| Eq (e1, e2, pos) -> BForm (Neq (e1, e2, pos))
		| Neq (e1, e2, pos) -> BForm (Eq (e1, e2, pos))
		| _ -> Not (f, pos0)
	end
  | _ -> Not (f, pos0)

and mkEqVar (sv1 : spec_var) (sv2 : spec_var) pos =
  if eq_spec_var sv1 sv2 then
	mkTrue pos
  else
	BForm (Eq (Var (sv1, pos), Var (sv2, pos), pos))

and mkNeqVar (sv1 : spec_var) (sv2 : spec_var) pos =
  if eq_spec_var sv1 sv2 then
	mkFalse pos
  else
	BForm (Neq (Var (sv1, pos), Var (sv2, pos), pos))

and mkEqVarInt (sv : spec_var) (i : int) pos =
  BForm (Eq (Var (sv, pos), IConst (i, pos), pos))


(*
and mkEqualAExp (ae1 : exp) (ae2 : exp) = match (ae1, ae2) with
  | (AVar (SVar sv1), AVar (SVar sv2)) ->
	  if sv1 = sv2 then
		mkTrue
	  else
		BForm (AEq (ae1, ae2))
  | _ ->  BForm (AEq (ae1, ae2))

and mkNEqualAExp (ae1 : exp) (ae2 : exp) = match (ae1, ae2) with
  | (AVar (SVar sv1), AVar (SVar sv2)) ->
	  if sv1 = sv2 then
		mkTrue
	  else
		BForm (ANeq (ae1, ae2))
  | _ ->  BForm (ANeq (ae1, ae2))

and mkNEqualVar (sv1 : spec_var) (sv2 : spec_var) =
  if sv1 = sv2 then
	mkFalse
  else
	BForm (ANeq (AVar (force_to_svar sv1), AVar (force_to_svar sv2)))

and mkNEqualVarInt (sv : spec_var) (i : int) =
  BForm (ANeq (AVar (force_to_svar sv), IConst i))
*)

and mkTrue pos = BForm (BConst (true, pos))

and mkFalse pos = BForm (BConst (false, pos))

and mkExists (vs : spec_var list) (f : formula) pos = match vs with
  | [] -> f
  | v :: rest ->
      let ef = mkExists rest f pos in
		if mem v (fv ef) then
		  Exists (v, ef, pos)
		else
		  ef

and mkForall (vs : spec_var list) (f : formula) pos = match vs with
  | [] -> f
  | v :: rest ->
      let ef = mkForall rest f pos in
		if mem v (fv ef) then
		  Forall (v, ef, pos)
		else
		  ef

(* build relation from list of expressions, for example a,b,c < d,e, f *)
and build_relation relop alist10 alist20 pos =
  let rec helper1 ae alist =
	let a = List.hd alist in
	let rest = List.tl alist in
	let tmp = BForm (relop ae a pos) in
	  if Util.empty rest then
		tmp
	  else
		let tmp1 = helper1 ae rest in
		let tmp2 = mkAnd tmp tmp1 pos in
		  tmp2 in
  let rec helper2 alist1 alist2 =
	let a = List.hd alist1 in
	let rest = List.tl alist1 in
	let tmp = helper1 a alist2 in
	  if Util.empty rest then
		tmp
	  else
		let tmp1 = helper2 rest alist2 in
		let tmp2 = mkAnd tmp tmp1 pos in
		  tmp2 in
	if List.length alist10 = 0 || List.length alist20 = 0 then
	  failwith ("build_relation: zero-length list")
	else
	  helper2 alist10 alist20

(* utility functions *)

and mem (sv : spec_var) (svs : spec_var list) : bool =
  List.exists (fun v -> eq_spec_var sv v) svs

and disjoint (svs1 : spec_var list) (svs2 : spec_var list) =
  List.for_all (fun sv -> not (mem sv svs2)) svs1

and subset (svs1 : spec_var list) (svs2 : spec_var list) =
  List.for_all (fun sv -> mem sv svs2) svs1

and difference (svs1 : spec_var list) (svs2 : spec_var list) =
  List.filter (fun sv -> not (mem sv svs2)) svs1

and intersect (svs1 : spec_var list) (svs2 : spec_var list) =
  List.filter (fun sv -> mem sv svs2) svs1

and remove_dups n = match n with
    [] -> []
  | q::qs -> if (mem q qs) then remove_dups qs else q::(remove_dups qs)

and are_same_types (t1 : typ) (t2 : typ) = match t1 with
  | Prim _ -> t1 = t2
  | OType c1 -> match t2 with
	  | Prim _ -> false
	  | OType c2 -> c1 = c2 || c1 = "" || c2 = ""

and is_otype (t : typ) : bool = match t with
  | OType _ -> true
  | Prim _ -> false

and name_of_type (t : typ) : ident = match t with
  | Prim Int -> "int"
  | Prim Bool -> "boolean"
  | Prim Void -> "void"
  | Prim Float -> "float"
  | Prim Globals.Bag -> "bag"
  | OType c -> c

and pos_of_exp (e : exp) = match e with
  | Null pos -> pos
  | Var (_, p) -> p
  | IConst (_, p) -> p
  | Add (_, _, p) -> p
  | Subtract (_, _, p) -> p
  | Mult (_, _, p) -> p
  | Max (_, _, p) -> p
  | Min (_, _, p) -> p
  (*| BagEmpty (p) -> p*)
 	| Bag (_, p) -> p
  | BagUnion (_, p) -> p
  | BagIntersect (_, p) -> p
  | BagDiff (_, _, p) -> p

and name_of_spec_var (sv : spec_var) : ident = match sv with
  | SpecVar (_, v, _) -> v

and type_of_spec_var (sv : spec_var) : typ = match sv with
  | SpecVar (t, _, _) -> t

and is_primed (sv : spec_var) : bool = match sv with
  | SpecVar (_, _, p) -> p = Primed

and is_unprimed (sv : spec_var) : bool = match sv with
  | SpecVar (_, _, p) -> p = Unprimed

and to_primed (sv : spec_var) : spec_var = match sv with
  | SpecVar (t, v, _) -> SpecVar (t, v, Primed)

and to_unprimed (sv : spec_var) : spec_var = match sv with
  | SpecVar (t, v, _) -> SpecVar (t, v, Unprimed)

and to_int_var (sv : spec_var) : spec_var = match sv with
  | SpecVar (_, v, p) -> SpecVar (Prim Int, v, p)


and fresh_old_name (s: string):string = 
	let ri = try  (String.rindex s '_') with  _ -> (String.length s) in
	let n = ((String.sub s 0 ri) ^ (fresh_trailer ())) in
	(*let _ = print_string ("init name: "^s^" new name: "^n ^"\n") in*)
	n
	

and fresh_spec_var (sv : spec_var) =
	let old_name = name_of_spec_var sv in
  let name = fresh_old_name old_name in
  (*--- 09.05.2000 *)
	(*let _ = (print_string ("\n[cpure.ml, line 521]: fresh name = " ^ name ^ "!!!!!!!!!!!\n\n")) in*)
	(*09.05.2000 ---*)
  let t = type_of_spec_var sv in
	SpecVar (t, name, Unprimed) (* fresh names are unprimed *)

and fresh_spec_vars (svs : spec_var list) = List.map fresh_spec_var svs

(******************************************************************************************************************
	22.05.2008
	Utilities for equality testing
******************************************************************************************************************)

and eq_spec_var_list (sv1 : spec_var list) (sv2 : spec_var list) =
	let rec eq_spec_var_list_helper (sv1 : spec_var list) (sv2 : spec_var list) = match sv1 with
		| [] -> true
		| h :: t -> (List.exists (fun c -> eq_spec_var h c) sv2) & (eq_spec_var_list_helper t sv2)
	in
		(eq_spec_var_list_helper sv1 sv2) & (eq_spec_var_list_helper sv2 sv1)

and eq_spec_var (sv1 : spec_var) (sv2 : spec_var) = match (sv1, sv2) with
  | (SpecVar (t1, v1, p1), SpecVar (t2, v2, p2)) ->
	  (* translation has ensured well-typedness.
		 We need only to compare names and primedness *)
	  v1 = v2 & p1 = p2

and eq_pure_formula (f1 : formula) (f2 : formula) : bool = match (f1, f2) with
	| (BForm(b1), BForm(b2)) -> (eq_b_formula b1 b2)
	| (Or(f1, f2, _), Or(f3, f4, _))
  | (And(f1, f2, _), And(f3, f4, _)) ->
  	((eq_pure_formula f1 f3) & (eq_pure_formula f2 f4)) or ((eq_pure_formula f1 f4) & (eq_pure_formula f2 f3))
  | (Not(f1, _), Not(f2, _)) -> (eq_pure_formula f1 f2)
  | (Exists(sv1, f1, _), Exists(sv2, f2, _))
  | (Forall(sv1, f1, _), Forall(sv2, f2, _)) -> (eq_spec_var sv1 sv2) & (eq_pure_formula f1 f2)
	| _ -> false

and eq_b_formula (b1 : b_formula) (b2 : b_formula) : bool = match (b1, b2) with
	| (BConst(c1, _), BConst(c2, _)) -> c1 = c2
	| (BVar(sv1, _), BVar(sv2, _)) -> (eq_spec_var sv1 sv2)
	| (Lte(e1, e2, _), Lte(e3, e4, _))
	| (Gt(e1, e2, _), Gt(e3, e4, _))
	| (Gte(e1, e2, _), Gte(e3, e4, _))
	| (Lt(e1, e2, _), Lt(e3, e4, _)) -> (eq_exp e1 e3) & (eq_exp e2 e4)
	| (Neq(e1, e2, _), Eq(e3, e4, _))
	| (Eq(e1, e2, _), Eq(e3, e4, _)) -> ((eq_exp e1 e3) & (eq_exp e2 e4)) or ((eq_exp e1 e4) & (eq_exp e2 e3))
	| (EqMax(e1, e2, e3, _), EqMax(e4, e5, e6, _))
	| (EqMin(e1, e2, e3, _), EqMin(e4, e5, e6, _))  -> (eq_exp e1 e4) & ((eq_exp e2 e5) & (eq_exp e3 e6)) or ((eq_exp e2 e6) & (eq_exp e3 e5))
	| (BagIn(sv1, e1, _), BagIn(sv2, e2, _))
	| (BagNotIn(sv1, e1, _), BagNotIn(sv2, e2, _)) -> (eq_spec_var sv1 sv2) & (eq_exp e1 e2)
	| (BagMin(sv1, sv2, _), BagMin(sv3, sv4, _))
	| (BagMax(sv1, sv2, _), BagMax(sv3, sv4, _)) -> (eq_spec_var sv1 sv3) & (eq_spec_var sv2 sv4)
	| (BagSub(e1, e2, _), BagSub(e3, e4, _)) -> (eq_exp e1 e3) & (eq_exp e2 e4)
	| _ -> false

and eq_exp_list (e1 : exp list) (e2 : exp list) : bool =
	let rec eq_exp_list_helper (e1 : exp list) (e2 : exp list) = match e1 with
		| [] -> true
		| h :: t -> (List.exists (fun c -> eq_exp h c) e2) & (eq_exp_list_helper t e2)
	in
		(eq_exp_list_helper e1 e2) & (eq_exp_list_helper e2 e1)

and eq_exp (e1 : exp) (e2 : exp) : bool = match (e1, e2) with
	| (Null(_), Null(_)) -> true
	| (Var(sv1, _), Var(sv2, _)) -> (eq_spec_var sv1 sv2)
	| (IConst(i1, _), IConst(i2, _)) -> i1 = i2
	| (Subtract(e11, e12, _), Subtract(e21, e22, _))
	| (Max(e11, e12, _), Max(e21, e22, _))
	| (Min(e11, e12, _), Min(e21, e22, _))
	| (Add(e11, e12, _), Add(e21, e22, _)) -> (eq_exp e11 e21) & (eq_exp e12 e22)
	| (Mult(i1, e11, _), Mult(i2, e21, _)) -> (i1 = i2) & (eq_exp e11 e21)
	| (Bag(e1, _), Bag(e2, _))
	| (BagUnion(e1, _), BagUnion(e2, _))
	| (BagIntersect(e1, _), BagIntersect(e2, _)) -> (eq_exp_list e1 e2)
	| (BagDiff(e1, e2, _), BagDiff(e3, e4, _)) -> (eq_exp e1 e3) & (eq_exp e2 e4)
	| _ -> false


and remove_spec_var (sv : spec_var) (vars : spec_var list) =
  List.filter (fun v -> not (eq_spec_var sv v)) vars

(* substitution *)

and subst_var_list_avoid_capture fr t svs =
  let fresh_fr = fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let svs1 = subst_var_list st1 svs in
  let svs2 = subst_var_list st2 svs1 in
	svs2

and subst_var_list sst (svs : spec_var list) = match svs with
  | sv :: rest ->
      let new_vars = subst_var_list sst rest in
      let new_sv = match List.filter (fun st -> fst st = sv) sst with
		| [(fr, t)] -> t
		| _ -> sv in
		new_sv :: new_vars
  | [] -> []

(* The intermediate fresh variables seem redundant. *)
(*and subst_avoid_capture (fr : spec_var list) (t : spec_var list) (f : formula) =
  let fresh_fr = fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst st1 f in
  let f2 = subst st2 f1 in
	f2*)

and subst_avoid_capture (fr : spec_var list) (t : spec_var list) (f : formula) =
  let st1 = List.combine fr t in
  let f2 = subst st1 f in
  f2

and subst (sst : (spec_var * spec_var) list) (f : formula) : formula = match sst with
  | s::ss -> subst ss (apply_one s f) 				(* applies one substitution at a time *)
  | [] -> f

and apply_one (fr, t) f = match f with
  | BForm bf -> BForm (b_apply_one (fr, t) bf)
  | And (p1, p2, pos) -> And (apply_one (fr, t) p1,
							  apply_one (fr, t) p2, pos)
  | Or (p1, p2, pos) -> Or (apply_one (fr, t) p1,
							apply_one (fr, t) p2, pos)
  | Not (p, pos) -> Not (apply_one (fr, t) p, pos)
  | Forall (v, qf, pos) ->
	  if eq_spec_var v fr then f
      else if eq_spec_var v t then
        let fresh_v = fresh_spec_var v in
        Forall (fresh_v, apply_one (fr, t) (apply_one (v, fresh_v) qf), pos)
	  else Forall (v, apply_one (fr, t) qf, pos)
  | Exists (v, qf, pos) ->
	  if eq_spec_var v fr then f
      else if eq_spec_var v t then
        let fresh_v = fresh_spec_var v in
        Exists (fresh_v, apply_one (fr, t) (apply_one (v, fresh_v) qf), pos)
	  else Exists (v, apply_one (fr, t) qf, pos)

and b_apply_one (fr, t) bf = match bf with
  | BConst _ -> bf
  | BVar (bv, pos) -> BVar ((if eq_spec_var bv fr then t else bv), pos)
  | Lt (a1, a2, pos) -> Lt (e_apply_one (fr, t) a1,
							e_apply_one (fr, t) a2, pos)
  | Lte (a1, a2, pos) -> Lte (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
  | Gt (a1, a2, pos) -> Gt (e_apply_one (fr, t) a1,
							e_apply_one (fr, t) a2, pos)
  | Gte (a1, a2, pos) -> Gte (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
  | Eq (a1, a2, pos) -> Eq (e_apply_one (fr, t) a1,
							e_apply_one (fr, t) a2, pos)
  | Neq (a1, a2, pos) -> Neq (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
  | EqMax (a1, a2, a3, pos) -> EqMax (e_apply_one (fr, t) a1,
									  e_apply_one (fr, t) a2,
									  e_apply_one (fr, t) a3, pos)
  | EqMin (a1, a2, a3, pos) -> EqMin (e_apply_one (fr, t) a1,
									  e_apply_one (fr, t) a2,
									  e_apply_one (fr, t) a3, pos)
	| BagIn (v, a1, pos) -> BagIn ((if eq_spec_var v fr then t else v), e_apply_one (fr, t) a1, pos)
	| BagNotIn (v, a1, pos) -> BagNotIn ((if eq_spec_var v fr then t else v), e_apply_one (fr, t) a1, pos)
	(* is it ok?... can i have a set of boolean values?... don't think so..*)
  | BagSub (a1, a2, pos) -> BagSub (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | BagMax (v1, v2, pos) -> BagMax ((if eq_spec_var v1 fr then t else v1), (if eq_spec_var v2 fr then t else v2), pos)
	| BagMin (v1, v2, pos) -> BagMin ((if eq_spec_var v1 fr then t else v1), (if eq_spec_var v2 fr then t else v2), pos)

and e_apply_one (fr, t) e = match e with
  | Null _ | IConst _ -> e
  | Var (sv, pos) -> Var ((if eq_spec_var sv fr then t else sv), pos)
  | Add (a1, a2, pos) -> Add (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
  | Subtract (a1, a2, pos) -> Subtract (e_apply_one (fr, t) a1,
										e_apply_one (fr, t) a2, pos)
  | Mult (c, a, pos) -> Mult (c, e_apply_one (fr, t) a, pos)
  | Max (a1, a2, pos) -> Max (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
  | Min (a1, a2, pos) -> Min (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
	(*| BagEmpty (pos) -> BagEmpty (pos)*)
	| Bag (alist, pos) -> Bag ((e_apply_one_bag (fr, t) alist), pos)
	| BagUnion (alist, pos) -> BagUnion ((e_apply_one_bag (fr, t) alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((e_apply_one_bag (fr, t) alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)

and e_apply_one_bag (fr, t) alist = match alist with
	|[] -> []
	|a :: rest -> (e_apply_one (fr, t) a) :: (e_apply_one_bag (fr, t) rest)

(* substituting terms for variables: can name-capturing happen?
   yes. What to do? *)

and subst_term_avoid_capture (sst : (spec_var * exp) list) (f : formula) : formula =
  let fr = List.map fst sst in
  let t = List.map snd sst in
  let fresh_fr = fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst st1 f in
  let f2 = subst_term st2 f1 in
	f2

and subst_term (sst : (spec_var * exp) list) (f : formula) : formula = match sst with
  | s :: ss -> subst_term ss (apply_one_term s f)
  | [] -> f

and apply_one_term (fr, t) f = match f with
  | BForm bf -> BForm (b_apply_one_term (fr, t) bf)
  | And (p1, p2, pos) -> And (apply_one_term (fr, t) p1, apply_one_term (fr, t) p2, pos)
  | Or (p1, p2, pos) -> Or (apply_one_term (fr, t) p1, apply_one_term (fr, t) p2, pos)
  | Not (p, pos) -> Not (apply_one_term (fr, t) p, pos)
  | Forall (v, qf, pos) -> if eq_spec_var v fr then f else Forall (v, apply_one_term (fr, t) qf, pos)
  | Exists (v, qf, pos) -> if eq_spec_var v fr then f else Exists (v, apply_one_term (fr, t) qf, pos)

and b_apply_one_term ((fr, t) : (spec_var * exp)) bf = match bf with
  | BConst _ -> bf
  | BVar (bv, pos) ->
	  if eq_spec_var bv fr then
		failwith ("Presburger.b_apply_one_term: attempting to substitute arithmetic term for boolean var")
	  else
		bf
  | Lt (a1, a2, pos) -> Lt (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Lte (a1, a2, pos) -> Lte (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Gt (a1, a2, pos) -> Gt (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Gte (a1, a2, pos) -> Gte (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Eq (a1, a2, pos) -> Eq (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Neq (a1, a2, pos) -> Neq (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | EqMax (a1, a2, a3, pos) -> EqMax (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, a_apply_one_term (fr, t) a3, pos)
  | EqMin (a1, a2, a3, pos) -> EqMin (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, a_apply_one_term (fr, t) a3, pos)
  | BagIn (v, a1, pos) -> BagIn (v, a_apply_one_term (fr, t) a1, pos)
  | BagNotIn (v, a1, pos) -> BagNotIn (v, a_apply_one_term (fr, t) a1, pos)
  | BagSub (a1, a2, pos) -> BagSub (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | BagMax (v1, v2, pos) -> BagMax (v1, v2, pos)
  | BagMin (v1, v2, pos) -> BagMin (v1, v2, pos)

and a_apply_one_term ((fr, t) : (spec_var * exp)) e = match e with
  | Null _ -> e
  | IConst _ -> e
  | Add (a1, a2, pos) -> Add (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Subtract (a1, a2, pos) -> Subtract (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Mult (c, a, pos) -> Mult (c, a_apply_one_term (fr, t) a, pos)
  | Var (sv, pos) -> if eq_spec_var sv fr then t else e
  | Max (a1, a2, pos) -> Max (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Min (a1, a2, pos) -> Min (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
	  (*| BagEmpty (pos) -> BagEmpty (pos)*)
  | Bag (alist, pos) -> Bag ((a_apply_one_term_bag (fr, t) alist), pos)
  | BagUnion (alist, pos) -> BagUnion ((a_apply_one_term_bag (fr, t) alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((a_apply_one_term_bag (fr, t) alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (a_apply_one_term (fr, t) a1,
									  a_apply_one_term (fr, t) a2, pos)

and a_apply_one_term_bag (fr, t) alist = match alist with
  |[] -> []
  |a :: rest -> (a_apply_one_term (fr, t) a) :: (a_apply_one_term_bag (fr, t) rest)

and rename_top_level_bound_vars (f : formula) = match f with
  | Or (f1, f2, pos) ->
	  let rf1 = rename_top_level_bound_vars f1 in
	  let rf2 = rename_top_level_bound_vars f2 in
	  let resform = mkOr rf1 rf2 pos in
		resform
  | And (f1, f2, pos) ->
	  let rf1 = rename_top_level_bound_vars f1 in
	  let rf2 = rename_top_level_bound_vars f2 in
	  let resform = mkAnd rf1 rf2 pos in
		resform
  | Exists (qvar, qf, pos) ->
	  let renamed_f = rename_top_level_bound_vars qf in
	  let new_qvar = fresh_spec_var qvar in
	  let rho = [(qvar, new_qvar)] in
	  let new_qf = subst rho renamed_f in
	  let res_form = Exists (new_qvar, new_qf, pos) in
		res_form
  | Forall (qvar, qf, pos) ->
	  let renamed_f = rename_top_level_bound_vars qf in
	  let new_qvar = fresh_spec_var qvar in
	  let rho = [(qvar, new_qvar)] in
	  let new_qf = subst rho renamed_f in
	  let res_form = Forall (new_qvar, new_qf, pos) in
		res_form
  | _ -> f

and split_ex_quantifiers (f0 : formula) : (spec_var list * formula) = match f0 with
  | Exists (qv, qf, pos) ->
	  let qvars, new_f = split_ex_quantifiers qf in
		(qv :: qvars, new_f)
  | _ -> ([], f0)

(* More simplifications *)

(*
   EX quantifier elimination.

   EX x . x = T & P(x) ~-> P[T], T is term
   EX x . P[x] \/ Q[x] ~-> (EX x . P[x]) \/ (EX x . Q[x])
   EX x . P & Q[x] ~-> P & Q[x], x notin FV(P)

*)

and get_subst_equation (f0 : formula) (v : spec_var) : ((spec_var * exp) list * formula) = match f0 with
  | And (f1, f2, pos) ->
	  let st1, rf1 = get_subst_equation f1 v in
		if not (Util.empty st1) then
		  (st1, mkAnd rf1 f2 pos)
		else
		  let st2, rf2 = get_subst_equation f2 v in
			(st2, mkAnd f1 rf2 pos)
  | BForm bf -> get_subst_equation_b_formula bf v
  | _ -> ([], f0)

and get_subst_equation_b_formula (f0 : b_formula) (v : spec_var) : ((spec_var * exp) list * formula) = match f0 with
  | Eq (e1, e2, pos) -> begin
	  if is_var e1 then
		let v1 = to_var e1 in
		  if eq_spec_var v1 v then ([(v, e2)], mkTrue no_pos)
		  else if is_var e2 then
			let v2 = to_var e2 in
			  if eq_spec_var v2 v then ([(v, e1)], mkTrue no_pos)
			  else ([], BForm f0)
		  else ([], BForm f0)
	  else ([], BForm f0)
	end
  | _ -> ([], BForm f0)

and list_of_conjs (f0 : formula) : formula list =
  let rec helper f conjs = match f with
	| And (f1, f2, pos) ->
		let tmp1 = helper f2 conjs in
		let tmp2 = helper f1 tmp1 in
		  tmp2
	| _ -> f :: conjs
  in
	helper f0 []

and conj_of_list (fs : formula list) pos : formula =
  let helper f1 f2 = mkAnd f1 f2 pos in
	List.fold_left helper (mkTrue pos) fs

and elim_exists (f0 : formula) : formula = match f0 with
  | Exists (qvar, qf, pos) -> begin
	  match qf with
		| Or (qf1, qf2, qpos) ->
			let new_qf1 = mkExists [qvar] qf1 qpos in
			let new_qf2 = mkExists [qvar] qf2 qpos in
			let eqf1 = elim_exists new_qf1 in
			let eqf2 = elim_exists new_qf2 in
			let res = mkOr eqf1 eqf2 pos in
			  res
		| _ ->
			let qvars0, bare_f = split_ex_quantifiers qf in
			let qvars = qvar :: qvars0 in
			let conjs = list_of_conjs bare_f in
			let no_qvars_list, with_qvars_list = List.partition
			  (fun cj -> disjoint qvars (fv cj)) conjs in
			  (* the part that does not contain the quantified var *)
			let no_qvars = conj_of_list no_qvars_list pos in
			  (* now eliminate the quantified variables from the part that contains it *)
			let with_qvars = conj_of_list with_qvars_list pos in
			  (* now eliminate the top existential variable. *)
			let st, pp1 = get_subst_equation with_qvars qvar in
			  if not (Util.empty st) then
				let new_qf = subst_term st pp1 in
				let new_qf = mkExists qvars0 new_qf pos in
				let tmp3 = elim_exists new_qf in
				let tmp4 = mkAnd no_qvars tmp3 pos in
				  tmp4
			  else (* if qvar is not equated to any variables, try the next one *)
				let tmp1 = elim_exists qf in
				let tmp2 = mkExists [qvar] tmp1 pos in
				  tmp2
	end
  | And (f1, f2, pos) -> begin
	  let ef1 = elim_exists f1 in
	  let ef2 = elim_exists f2 in
	  let res = mkAnd ef1 ef2 pos in
		res
	end
  | Or (f1, f2, pos) -> begin
	  let ef1 = elim_exists f1 in
	  let ef2 = elim_exists f2 in
	  let res = mkOr ef1 ef2 pos in
		res
	end
  | Not (f1, pos) -> begin
	  let ef1 = elim_exists f1 in
	  let res = mkNot ef1 pos in
		res
	end
  | Forall (qvar, qf, pos) -> begin
	  let eqf = elim_exists qf in
	  let res = mkForall [qvar] eqf pos in
		res
	end
  | BForm _ -> f0


(**************************************************************)
(**************************************************************)
(**************************************************************)

(*
  Assumption filtering.

  Given entailment D1 => D2, we filter out "irrelevant" assumptions as follows.
  We convert D1 to a list of conjuncts (it is safe to drop conjunts from the LHS).
  The main heuristic is to keep only conjunts that mention "relevant" variables.
  Relevant variables may be only those on the RHS, and may or may not increase
  with new variables from newly added conjunts.

  (more and more aggressive filtering)
*)

module SVar = struct
  type t = spec_var
  let compare = fun sv1 -> fun sv2 -> compare (name_of_spec_var sv1) (name_of_spec_var sv2)
end

module SVarSet = Set.Make(SVar)

let set_of_list (ids : spec_var list) : SVarSet.t =
  List.fold_left (fun s -> fun i -> SVarSet.add i s) (SVarSet.empty) ids

let print_var_set vset =
  let tmp1 = SVarSet.elements vset in
  let tmp2 = List.map name_of_spec_var tmp1 in
  let tmp3 = String.concat ", " tmp2 in
	print_string ("\nvset:\n" ^ tmp3 ^ "\n")

(*
  filter from f0 conjuncts that mention variables related to rele_vars.
*)
let rec filter_var (f0 : formula) (rele_vars0 : spec_var list) : formula =
  let is_relevant (fv, fvset) rele_var_set =
	not (SVarSet.is_empty (SVarSet.inter fvset rele_var_set)) in
  let rele_var_set = set_of_list rele_vars0 in
  let conjs = list_of_conjs f0 in
  let fv_list = List.map fv conjs in
  let fv_set = List.map set_of_list fv_list in
  let f_fv_list = List.combine conjs fv_set in
  let relevants0, unknowns0 = List.partition
	(fun f_fv -> is_relevant f_fv rele_var_set) f_fv_list in
	(* now select more "relevant" conjuncts *)
	(*
	   return value:
	   - relevants (formulas, fv_set) list
	   - unknowns
	   - updated relevant variable set
	*)
  let rele_var_set =
	let tmp1 = List.map snd relevants0 in
	let tmp2 = List.fold_left (fun s1 -> fun s2 -> SVarSet.union s1 s2) rele_var_set tmp1 in
	  tmp2
  in
	(*
	  let _ = print_var_set rele_var_set in
	  let _ = List.map
	  (fun ffv -> (print_string ("\nrelevants0: f\n" ^ (mona_of_formula (fst ffv)) ^ "\n")); print_var_set (snd ffv))
	  relevants0
	  in
	*)
	(*
	  Perform a fixpoint to select all relevant formulas.
	*)
  let rec select_relevants relevants unknowns rele_var_set =
	let reles = ref relevants in
	let unks = ref unknowns in
	let unks_tmp = ref [] in
	let rvars = ref rele_var_set in
	let cont = ref true in
	  while !cont do
		cont := false; (* assume we're done, unless the inner loop says otherwise *)
		let cont2 = ref true in
		  while !cont2 do
			match !unks with
			  | (unk :: rest) ->
				  unks := rest;
				  (*
					print_var_set !rvars;
					print_string ("\nunk:\n" ^ (mona_of_formula (fst unk)) ^ "\n");
				  *)
				  if is_relevant unk !rvars then begin
					(* add variables from unk in as relevant vars *)
					cont := true;
					rvars := SVarSet.union (snd unk) !rvars;
					reles := unk :: !reles
					(*
					  print_string ("\nadding: " ^ (mona_of_formula (fst unk)) ^ "\n")
					*)
				  end else
					unks_tmp := unk :: !unks_tmp
			  | [] ->
				  cont2 := false; (* terminate inner loop *)
				  unks := !unks_tmp;
				  unks_tmp := []
		  done
	  done;
	  begin
		let rele_conjs = List.map fst !reles in
		let filtered_f = conj_of_list rele_conjs no_pos in
		  filtered_f
	  end
  in
  let filtered_f = select_relevants relevants0 unknowns0 rele_var_set in
	filtered_f

(**************************************************************)
(**************************************************************)
(**************************************************************)

(*
  Break an entailment using the following rule:
  A -> B /\ C <=> (A -> B) /\ (A -> C)

  Return value: a list of new implications. The new antecedents
  are filtered. This works well in conjunction with existential
  quantifier elimintation and filtering.
*)

let rec break_implication (ante : formula) (conseq : formula) : ((formula * formula) list) =
  let conseqs = list_of_conjs conseq in
  let fvars = List.map fv conseqs in
  let antes = List.map (fun reles -> filter_var ante reles) fvars in
  let res = List.combine antes conseqs in
	res

(**************************************************************)
(**************************************************************)
(**************************************************************)
(*
	MOVED TO SOLVER.ML -> TO USE THE PRINTING METHODS

	We do a simplified translation towards CNF where we only take out the common
 	conjuncts from all the disjuncts:

	Ex:
 (a=1 & b=1) \/ (a=2 & b=2) - nothing common between the two disjuncts
 (a=1 & b=1 & c=3) \/ (a=2 & b=2 & c=3) ->  c=3 & ((a=1 & b=1) \/ (a=2 & b=2))

	let rec normalize_to_CNF (f : formula) pos : formula
 *)
(**************************************************************)
(**************************************************************)
(**************************************************************)

(*
  Drop bag constraint for satisfiability checking.
*)
let rec drop_bag_formula (f0 : formula) : formula = match f0 with
  | BForm bf -> BForm (drop_bag_b_formula bf)
  | And (f1, f2, pos) ->
	  let df1 = drop_bag_formula f1 in
	  let df2 = drop_bag_formula f2 in
	  let df = mkAnd df1 df2 pos in
		df
  | Or (f1, f2, pos) ->
	  let df1 = drop_bag_formula f1 in
	  let df2 = drop_bag_formula f2 in
	  let df = mkOr df1 df2 pos in
		df
  | Not (f1, pos) ->
	  let df1 = drop_bag_formula f1 in
	  let df = mkNot df1 pos in
		df
  | Forall (qvar, qf, pos) ->
	  let dqf = drop_bag_formula qf in
	  let df = mkForall [qvar] dqf pos in
		df
  | Exists (qvar, qf, pos) ->
	  let dqf = drop_bag_formula qf in
	  let df = mkExists [qvar] dqf pos in
		df
and drop_bag_b_formula (bf0 : b_formula) : b_formula = match bf0 with
  | BagIn _
  | BagNotIn _
  | BagSub _
  | BagMin _
  | BagMax _ -> BConst (true, no_pos)
  | Eq (e1, e2, pos)
  | Neq (e1, e2, pos) ->
	  if (is_bag e1) || (is_bag e2) then
		BConst (true, pos)
	  else
		bf0
  | _ -> bf0


(*************************************************************************************************************************
	05.06.2008:
	Utilities for existential quantifier elimination:
	- before we were only searching for substitutions of the form v1 = v2 and then substitute ex v1. P(v1) --> P(v2)
	- now, we want to be more aggressive and search for substitutions of the form v1 = exp2; however, we can only apply these substitutions to the pure part
	(due to the way shape predicates are recorded --> root pointer and args are suppose to be spec vars)
*************************************************************************************************************************)

and apply_one_exp ((fr, t) : spec_var * exp) f = match f with
  | BForm bf -> BForm (b_apply_one_exp (fr, t) bf)
  | And (p1, p2, pos) -> And (apply_one_exp (fr, t) p1,
							  apply_one_exp (fr, t) p2, pos)
  | Or (p1, p2, pos) -> Or (apply_one_exp (fr, t) p1,
							apply_one_exp (fr, t) p2, pos)
  | Not (p, pos) -> Not (apply_one_exp (fr, t) p, pos)
  | Forall (v, qf, pos) ->
	  if eq_spec_var v fr then f
	  else Forall (v, apply_one_exp (fr, t) qf, pos)
  | Exists (v, qf, pos) ->
	  if eq_spec_var v fr then f
	  else Exists (v, apply_one_exp (fr, t) qf, pos)

and b_apply_one_exp (fr, t) bf = match bf with
  | BConst _ -> bf
  | BVar (bv, pos) -> bf
  | Lt (a1, a2, pos) -> Lt (e_apply_one_exp (fr, t) a1,
							e_apply_one_exp (fr, t) a2, pos)
  | Lte (a1, a2, pos) -> Lte (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
  | Gt (a1, a2, pos) -> Gt (e_apply_one_exp (fr, t) a1,
							e_apply_one_exp (fr, t) a2, pos)
  | Gte (a1, a2, pos) -> Gte (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
  | Eq (a1, a2, pos) ->
  		(*
  		if (eq_b_formula bf (mkEq (mkVar fr pos) t pos)) then
  			bf
  		else*)
  		Eq (e_apply_one_exp (fr, t) a1, e_apply_one_exp (fr, t) a2, pos)
  | Neq (a1, a2, pos) -> Neq (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
  | EqMax (a1, a2, a3, pos) -> EqMax (e_apply_one_exp (fr, t) a1,
									  e_apply_one_exp (fr, t) a2,
									  e_apply_one_exp (fr, t) a3, pos)
  | EqMin (a1, a2, a3, pos) -> EqMin (e_apply_one_exp (fr, t) a1,
									  e_apply_one_exp (fr, t) a2,
									  e_apply_one_exp (fr, t) a3, pos)
	| BagIn (v, a1, pos) -> bf
	| BagNotIn (v, a1, pos) -> bf
	(* is it ok?... can i have a set of boolean values?... don't think so..*)
  | BagSub (a1, a2, pos) -> BagSub (a1, e_apply_one_exp (fr, t) a2, pos)
  | BagMax (v1, v2, pos) -> bf
	| BagMin (v1, v2, pos) -> bf

and e_apply_one_exp (fr, t) e = match e with
  | Null _ | IConst _ -> e
  | Var (sv, pos) -> if eq_spec_var sv fr then t else e
  | Add (a1, a2, pos) -> Add (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
  | Subtract (a1, a2, pos) -> Subtract (e_apply_one_exp (fr, t) a1,
										e_apply_one_exp (fr, t) a2, pos)
  | Mult (c, a, pos) -> Mult (c, e_apply_one_exp (fr, t) a, pos)
  | Max (a1, a2, pos) -> Max (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
  | Min (a1, a2, pos) -> Min (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
	(*| BagEmpty (pos) -> BagEmpty (pos)*)
	| Bag (alist, pos) -> Bag ((e_apply_one_bag_exp (fr, t) alist), pos)
	| BagUnion (alist, pos) -> BagUnion ((e_apply_one_bag_exp (fr, t) alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((e_apply_one_bag_exp (fr, t) alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)

and e_apply_one_bag_exp (fr, t) alist = match alist with
	|[] -> []
	|a :: rest -> (e_apply_one_exp (fr, t) a) :: (e_apply_one_bag_exp (fr, t) rest)

(******************************************************************************************************************
	05.06.2008
	Utilities for simplifications:
	- we do some basic simplifications: eliminating identities where the LHS = RHS
******************************************************************************************************************)
and elim_idents (f : formula) : formula = match f with
  | And (f1, f2, pos) -> mkAnd (elim_idents f1) (elim_idents f2) pos
  | Or (f1, f2, pos) -> mkOr (elim_idents f1) (elim_idents f2) pos
  | Not (f1, pos) -> mkNot (elim_idents f1) pos
  | Forall (sv, f1, pos) -> mkForall [sv] (elim_idents f1) pos
  | Exists (sv, f1, pos) -> mkExists [sv] (elim_idents f1) pos
  | BForm (f1) -> BForm(elim_idents_b_formula f1)

and elim_idents_b_formula (f : b_formula) : b_formula =  match f with
  | Lte (e1, e2, pos)
  | Gte (e1, e2, pos)
  | Eq (e1, e2, pos) ->
  	if (eq_exp e1 e2) then BConst(true, pos)
  	else f
	| Neq (e1, e2, pos)
  | Lt (e1, e2, pos)
	| Gt (e1, e2, pos) ->
		if (eq_exp e1 e2) then BConst(false, pos)
  	else f
  | _ -> f

