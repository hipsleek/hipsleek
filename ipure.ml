(*
  Created 19-Feb-2006

  Input pure constraints, including arithmetic and pure pointer
*)

open Globals

type formula = 
  | BForm of b_formula
  | And of (formula * formula * loc)
  | Or of (formula * formula * loc)
  | Not of (formula * loc)
  | Forall of ((ident * primed) * formula * loc)
  | Exists of ((ident * primed) * formula * loc)

(* Boolean constraints *)
and b_formula = 
  | BConst of (bool * loc)
  | BVar of ((ident * primed) * loc)
  | Lt of (exp * exp * loc)
  | Lte of (exp * exp * loc)
  | Gt of (exp * exp * loc)
  | Gte of (exp * exp * loc)
  | Eq of (exp * exp * loc) (* these two could be arithmetic or pointer or bags *)
  | Neq of (exp * exp * loc)
  | EqMax of (exp * exp * exp * loc) (* first is max of second and third *)
  | EqMin of (exp * exp * exp * loc) (* first is min of second and third *)
	  (* bags and bag formulae *)
  | BagIn of ((ident * primed) * exp * loc)
  | BagNotIn of ((ident * primed) * exp * loc)
  | BagSub of (exp * exp * loc)
  | BagMin of ((ident * primed) * (ident * primed) * loc)
  | BagMax of ((ident * primed) * (ident * primed) * loc)	

(* Expression *)
and exp = 
  | Null of loc
  | Var of ((ident * primed) * loc) 
	  (* variables could be of type pointer, int, sets, etc *)
  | IConst of (int * loc)
  (*| Tuple of (exp list * loc)*)
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
  |	BaseRel of (exp list * formula)
  | UnionRel of (relation * relation)

(* free variables *)

let rec fv (f : formula) : (ident * primed) list = match f with 
  | BForm b -> bfv b
  | And (p1, p2, _) -> combine_pvars p1 p2
  | Or (p1, p2, _) -> combine_pvars p1 p2
  | Not (nf, _) -> fv nf
  | Forall (qid, qf, _) -> remove_qvar qid qf
  | Exists (qid, qf, _) -> remove_qvar qid qf

and combine_pvars p1 p2 = 
  let fv1 = fv p1 in
  let fv2 = fv p2 in
    Util.remove_dups (fv1 @ fv2)

and remove_qvar qid qf =
  let qfv = fv qf in
    Util.remove_elem qid qfv

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
	| BagIn (v, a, _) -> 
		let fv = afv a in
		Util.remove_dups ([v] @ fv)
	| BagNotIn (v, a, _) -> 
		let fv = afv a in
		Util.remove_dups ([v] @ fv)	
  | BagSub (a1, a2, _) -> combine_avars a1 a2
	| BagMax (sv1, sv2, _) -> Util.remove_dups ([sv1] @ [sv2])
	| BagMin (sv1, sv2, _) -> Util.remove_dups ([sv1] @ [sv2])


and combine_avars (a1 : exp) (a2 : exp) : (ident * primed) list = 
  let fv1 = afv a1 in
  let fv2 = afv a2 in
    Util.remove_dups (fv1 @ fv2)

and afv (af : exp) : (ident * primed) list = match af with
  | Null _ -> []
  | Var (sv, _) -> [sv]
  | IConst _ -> []
  | Add (a1, a2, _) -> combine_avars a1 a2
  | Subtract (a1, a2, _) -> combine_avars a1 a2
  | Mult (c, a, _) -> afv a
  | Max (a1, a2, _) -> combine_avars a1 a2
  | Min (a1, a2, _) -> combine_avars a1 a2
  | BagDiff _|BagIntersect _|BagUnion _|Bag _ -> failwith ("afv: bag constraints are not expected")

and is_max_min a = match a with
  | Max _ | Min _ -> true
  | _ -> false

and is_null (e : exp) : bool = match e with
  | Null _ -> true
  | _ -> false

and is_var (e : exp) : bool = match e with
  | Var _ -> true
  | _ -> false

and is_bag (e : exp) : bool = match e with
  | Bag (_, _)
  | BagUnion (_, _)
  | BagIntersect (_, _)
  | BagDiff (_, _, _) -> true
  | _ -> false
  

and name_of_var (e : exp) : ident = match e with
  | Var ((v, p), pos) -> v
  | _ -> failwith ("parameter to name_of_var is not a variable")
 
and isConstTrue p = match p with
  | BForm (BConst (true, pos)) -> true
  | _ -> false

and isConstFalse p = match p with
  | BForm (BConst (false, pos)) -> true
  | _ -> false

(* smart constructor *)

and mkAdd a1 a2 pos = Add (a1, a2, pos)

and mkSubtract a1 a2 pos = Subtract (a1, a2, pos)

and mkMult c a pos = Mult (c, a, pos)

and mkMax a1 a2 pos = Max (a1, a2, pos)

and mkMin a1 a2 pos = Min (a1, a2, pos)

and mkBVar (v, p) pos = BVar ((v, p), pos)

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
	  if v1 = v2 then
		mkTrue pos
	  else
		BForm (Eq (ae1, ae2, pos))
  | _ ->  BForm (Eq (ae1, ae2, pos))

and mkNeqExp (ae1 : exp) (ae2 : exp) pos = match (ae1, ae2) with
  | (Var v1, Var v2) ->
	  if v1 = v2 then
		mkFalse pos
	  else
		BForm (Neq (ae1, ae2, pos))
  | _ ->  BForm (Neq (ae1, ae2, pos))

and mkNot f pos = Not (f, pos)

(*
and mkEqualVar (sv1 : spec_var) (sv2 : spec_var) =
  if sv1 = sv2 then
	mkTrue
  else 
	BForm (Eq (Var (force_to_svar sv1), AVar (force_to_svar sv2)))

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

and mkEqualVarInt (sv : spec_var) (i : int) =
  BForm (AEq (AVar (force_to_svar sv), IConst i))

and mkNEqualVarInt (sv : spec_var) (i : int) = 
  BForm (ANeq (AVar (force_to_svar sv), IConst i))
*)

and mkTrue pos = BForm (BConst (true, pos))

and mkFalse pos = BForm (BConst (false, pos))

and mkExists (vs : (ident * primed) list) (f : formula) pos = match vs with
  | [] -> f
  | v :: rest -> 
      let ef = mkExists rest f pos in
		if List.mem v (fv ef) then
		  Exists (v, ef, pos)
		else
		  ef

and mkForall (vs : (ident * primed) list) (f : formula) pos = match vs with
  | [] -> f
  | v :: rest -> 
      let ef = mkForall rest f pos in
		if List.mem v (fv ef) then
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
	else begin
	  helper2 alist10 alist20
	end

and pos_of_exp (e : exp) = match e with
  | Null pos -> pos
  | Var (_, p) -> p
  | IConst (_, p) -> p
  | Add (_, _, p) -> p
  | Subtract (_, _, p) -> p
  | Mult (_, _, p) -> p
  | Max (_, _, p) -> p
  | Min (_, _, p) -> p
  | Bag (_, p) -> p
  | BagUnion (_, p) -> p
  | BagIntersect (_, p) -> p
  | BagDiff (_, _, p) -> p
  
