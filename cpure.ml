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
  | BForm of (b_formula *(formula_label option)* (int option)) (* the third argument is None for non redundant formulas*)
  | And of (formula * formula * loc)
  | Or of (formula * formula * (formula_label option) * loc)
  | Not of (formula * (formula_label option)* loc)
  | Forall of (spec_var * formula * (formula_label option)*loc)
  | Exists of (spec_var * formula * (formula_label option)*loc)

(* Boolean constraints *)
and b_formula =
  | BConst of (bool * loc)
  | BVar of (spec_var * loc)
  | Lt of (exp * exp * loc)
  | Lte of (exp * exp * loc)
  | Gt of (exp * exp * loc)
  | Gte of (exp * exp * loc)
  | Eq of (exp * exp * loc) (* these two could be arithmetic or pointer or bag or list *)
  | Neq of (exp * exp * loc)
  | EqMax of (exp * exp * exp * loc) (* first is max of second and third *)
  | EqMin of (exp * exp * exp * loc) (* first is min of second and third *)
	  (* bag formulas *)
  | BagIn of (spec_var * exp * loc)
  | BagNotIn of (spec_var * exp * loc)
  | BagSub of (exp * exp * loc)
  | BagMin of (spec_var * spec_var * loc)
  | BagMax of (spec_var * spec_var * loc)
	  (* list formulas *)
  | ListIn of (exp * exp * loc)
  | ListNotIn of (exp * exp * loc)
  | ListAllN of (exp * exp * loc)
  | ListPerm of (exp * exp * loc)

(* Expression *)
and exp =
  | Null of loc
  | Var of (spec_var * loc)
  | IConst of (int * loc)
  | FConst of (float * loc)
  | Add of (exp * exp * loc)
  | Subtract of (exp * exp * loc)
  | Mult of (exp * exp * loc)
  | Div of (exp * exp * loc)
  | Max of (exp * exp * loc)
  | Min of (exp * exp * loc)
	  (* bag expressions *)
  | Bag of (exp list * loc)
  | BagUnion of (exp list * loc)
  | BagIntersect of (exp list * loc)
  | BagDiff of (exp * exp * loc)
	  (* list expressions *)
  | List of (exp list * loc)
  | ListCons of (exp * exp * loc)
  | ListHead of (exp * loc)
  | ListTail of (exp * loc)
  | ListLength of (exp * loc)
  | ListAppend of (exp list * loc)
  | ListReverse of (exp * loc)

and relation = (* for obtaining back results from Omega Calculator. Will see if it should be here *)
  | ConstRel of bool
  | BaseRel of (exp list * formula)
  | UnionRel of (relation * relation)
  
and constraint_rel = 
  | Unknown
  | Subsumed
  | Subsuming
  | Equal
  | Contradicting

and rounding_func = 
  | Ceil
  | Floor
  
(* TODO: determine correct type of an exp *)
let rec get_exp_type (e : exp) : typ = match e with
  | Null _ -> OType ""
  | Var (SpecVar (t, _, _), _) -> t
  | IConst _ -> Prim Int
  | FConst _ -> Prim Float
  | Add (e1, e2, _) | Subtract (e1, e2, _) | Mult (e1, e2, _)
  | Max (e1, e2, _) | Min (e1, e2, _) ->
      begin
        match get_exp_type e1, get_exp_type e2 with
        | Prim Int, Prim Int -> Prim Int
        | _ -> Prim Float
      end
  | Div _ -> Prim Float
  | ListHead _ | ListLength _ -> Prim Int
  | Bag _ | BagUnion _ | BagIntersect _ | BagDiff _ -> Prim Globals.Bag
  | List _ | ListCons _ | ListTail _ | ListAppend _ | ListReverse _ -> Prim Globals.List

(* type constants *)

let bool_type = Prim Bool

let int_type = Prim Int

let float_type = Prim Float

let void_type = Prim Void

(* free variables *)

let null_var = SpecVar (OType "", "null", Unprimed)

let flow_var = SpecVar ((Prim Int), flow , Unprimed)

let is_void_type t = match t with | Prim Void -> true | _ -> false


let rec fv (f : formula) : spec_var list =
  let tmp = fv_helper f in
  let res = remove_dups tmp in
	res

and fv_helper (f : formula) : spec_var list = match f with
  | BForm (b,_,_) -> bfv b
  | And (p1, p2,_) -> combine_pvars p1 p2
  | Or (p1, p2, _,_) -> combine_pvars p1 p2
  | Not (nf, _,_) -> fv_helper nf
  | Forall (qid, qf, _,_) -> remove_qvar qid qf
  | Exists (qid, qf, _,_) -> remove_qvar qid qf

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
  | ListIn (a1, a2, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		fv1 @ fv2
  | ListNotIn (a1, a2, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		fv1 @ fv2
  | ListAllN (a1, a2, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		fv1 @ fv2
  | ListPerm (a1, a2, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		fv1 @ fv2

and combine_avars (a1 : exp) (a2 : exp) : spec_var list =
  let fv1 = afv a1 in
  let fv2 = afv a2 in
    Util.remove_dups (fv1 @ fv2)

and afv (af : exp) : spec_var list = match af with
  | Null _ -> []
  | Var (sv, _) -> [sv]
  | IConst _ -> []
  | FConst _ -> []
  | Add (a1, a2, _) -> combine_avars a1 a2
  | Subtract (a1, a2, _) -> combine_avars a1 a2
  | Mult (a1, a2, _) | Div (a1, a2, _) -> combine_avars a1 a2
  | Max (a1, a2, _) -> combine_avars a1 a2
  | Min (a1, a2, _) -> combine_avars a1 a2
  (*| BagEmpty (_) -> []*)
  | Bag (alist, _) -> let svlist = afv_list alist in
  		Util.remove_dups svlist
  | BagUnion (alist, _) -> let svlist = afv_list alist in
  		Util.remove_dups svlist
  | BagIntersect (alist, _) -> let svlist = afv_list alist in
  		Util.remove_dups svlist
  | BagDiff(a1, a2, _) -> combine_avars a1 a2
  | List (alist, _) -> let svlist = afv_list alist in
  		Util.remove_dups svlist
  | ListAppend (alist, _) -> let svlist = afv_list alist in
  		Util.remove_dups svlist
  | ListCons (a1, a2, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		Util.remove_dups (fv1 @ fv2)  
  | ListHead (a, _)
  | ListTail (a, _)
  | ListLength (a, _)
  | ListReverse (a, _) -> afv a

and afv_list (alist : exp list) : spec_var list = match alist with
	|[] -> []
	|a :: rest -> afv a @ afv_list rest

and is_max_min a = match a with
  | Max _ | Min _ -> true
  | _ -> false

and isConstTrue (p:formula) = match p with
  | BForm ((BConst (true, pos)),_,_) -> true
  | _ -> false

and isConstFalse (p:formula) = match p with
  | BForm ((BConst (false, pos)),_,_) -> true
  | _ -> false

and is_null (e : exp) : bool = match e with
  | Null _ -> true
  | _ -> false

and is_zero (e : exp) : bool = match e with
  | IConst (0, _) -> true
  | FConst (0.0, _) -> true
  | _ -> false

and is_var (e : exp) : bool = match e with
  | Var _ -> true
  | _ -> false

and is_num (e : exp) : bool = match e with
  | IConst _ -> true
  | FConst _ -> true
  | _ -> false

and to_int_const e t =
  match e with
  | IConst (i, _) -> i
  | FConst (f, _) ->
      begin
        match t with
        | Ceil -> int_of_float (ceil f)
        | Floor -> int_of_float (floor f)
      end
  | _ -> 0

and is_int (e : exp) : bool = match e with
  | IConst _ -> true
  | _ -> false

and is_float (e : exp) : bool = match e with
  | FConst _ -> true
  | _ -> false
  
and get_num_int (e : exp) : int = match e with
  | IConst (b,_) -> b
  | _ -> 0

and get_num_float (e : exp) : float = match e with
  | FConst (f, _) -> f
  | _ -> 0.0

and is_var_num (e : exp) : bool = match e with
  | Var _ -> true
  | IConst _ -> true
  | FConst _ -> true
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
  
and exp_is_object_var (sv : exp) = match sv with
  | Var(SpecVar (OType _, _, _),_) -> true
  | _ -> false
  
and is_bag (e : exp) : bool = match e with
  | Bag _
  | BagUnion _
  | BagIntersect _
  | BagDiff _ -> true
  | _ -> false

and is_list (e : exp) : bool = match e with
  | List _
  | ListCons _
  | ListTail _
  | ListAppend _
  | ListReverse _ -> true
  | _ -> false

and is_arith (e : exp) : bool = match e with
  | Add _
  | Subtract _
  | Mult _
  | Div _
  | Min _
  | Max _
  | ListHead _
  | ListLength _ -> true
  | _ -> false

and is_bag_type (t : typ) = match t with
  | Prim Globals.Bag  -> true
  | _ -> false
  
and is_list_type (t : typ) = match t with
  | Prim Globals.List  -> true
  | _ -> false

and is_int_type (t : typ) = match t with
  | Prim Int -> true
  | _ -> false

and is_float_type (t : typ) = match t with
  | Prim Float -> true
  | _ -> false

and is_object_type (t : typ) = match t with
  | OType _ -> true
  | _ -> false

and should_simplify (f : formula) = match f with
  | Exists (_, Exists (_, (Exists _),_,_), _,_) -> true
  | _ -> false

(* smart constructor *)

and mkRes t = SpecVar (t, res, Unprimed)

and mkAdd a1 a2 pos = Add (a1, a2, pos)

and mkSubtract a1 a2 pos = Subtract (a1, a2, pos)

and mkIConst a pos = IConst (a, pos)

and mkFConst a pos = FConst (a, pos)

and mkMult a1 a2 pos = Mult (a1, a2, pos)

and mkDiv a1 a2 pos = Div (a1, a2, pos)

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

and mkAnd f1 f2 pos = 
	if (isConstFalse f1) then f1
	else if (isConstTrue f1) then f2
	else if (isConstFalse f2) then f2
	else if (isConstTrue f2) then f1
	else And (f1, f2, pos)

and mkOr f1 f2 lbl pos= 
	if (isConstFalse f1) then f2
	else if (isConstTrue f1) then f1
	else if (isConstFalse f2) then f1
	else if (isConstTrue f2) then f2
	else Or (f1, f2, lbl ,pos)

and mkEqExp (ae1 : exp) (ae2 : exp) pos expanded :formula = match (ae1, ae2) with
  | (Var v1, Var v2) ->
	  if eq_spec_var (fst v1) (fst v2) then
		mkTrue pos 
	  else
		BForm ((Eq (ae1, ae2, pos)),None, expanded )
  | _ ->  BForm ((Eq (ae1, ae2, pos)),None, expanded )

and mkNeqExp (ae1 : exp) (ae2 : exp) pos expanded = match (ae1, ae2) with
  | (Var v1, Var v2) ->
	  if eq_spec_var (fst v1) (fst v2) then
		mkFalse pos 
	  else
		BForm ((Neq (ae1, ae2, pos)),None, expanded )
  | _ ->  BForm ((Neq (ae1, ae2, pos)),None, expanded)

and mkNot f lbl pos0 :formula= match f with
  | BForm (bf,lbl,expanded) -> begin
	  match bf with
		| BConst (b, pos) -> BForm ((BConst ((not b), pos)),lbl,expanded)
		| Lt (e1, e2, pos) -> BForm ((Gte (e1, e2, pos)),lbl,expanded)
		| Lte (e1, e2, pos) -> BForm ((Gt (e1, e2, pos)),lbl,expanded)
		| Gt (e1, e2, pos) -> BForm ((Lte (e1, e2, pos)),lbl,expanded)
		| Gte (e1, e2, pos) -> BForm ((Lt (e1, e2, pos)),lbl,expanded)
		| Eq (e1, e2, pos) -> BForm ((Neq (e1, e2, pos)),lbl,expanded)
		| Neq (e1, e2, pos) -> BForm ((Eq (e1, e2, pos)),lbl,expanded)
		| _ -> Not (f, lbl,pos0)
	end
  | _ -> Not (f, lbl,pos0)
  
and memo_f_neg (f: b_formula): b_formula = match f with
  | Lt (e1,e2,l) -> Lte (e2,e1,l)
  | Lte (e1,e2,l) -> Lt (e2,e1,l)
  | Gt (e1,e2,l) -> Lte (e1,e2,l)
  | Gte (e1,e2,l) -> Lt (e1,e2,l)
  | Eq (e1,e2,l) -> Neq (e1,e2,l)
  | Neq (e1,e2,l) -> Eq (e1,e2,l)
  | BagIn (e1,e2,l) -> BagNotIn(e1,e2,l)
  | BagNotIn  (e1,e2,l) -> BagIn(e1,e2,l)
  | ListIn (e1,e2,l) -> ListNotIn(e1,e2,l)
  | ListNotIn (e1,e2,l) -> ListIn(e1,e2,l)
  | _ -> Error.report_error {Error.error_loc = no_pos;Error.error_text = "memoized negation: unexpected constraint type"}


and mkEqVar (sv1 : spec_var) (sv2 : spec_var) pos expanded=
  if eq_spec_var sv1 sv2 then
	mkTrue pos
  else
	BForm ((Eq (Var (sv1, pos), Var (sv2, pos), pos)),None,expanded)

and mkNeqVar (sv1 : spec_var) (sv2 : spec_var) pos expanded=
  if eq_spec_var sv1 sv2 then
	mkFalse pos
  else
	BForm ((Neq (Var (sv1, pos), Var (sv2, pos), pos)),None,expanded)

and mkEqVarInt (sv : spec_var) (i : int) pos expanded =
  BForm ((Eq (Var (sv, pos), IConst (i, pos), pos)),None,expanded)


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

(*and mkTrue pos l= BForm ((BConst (true, pos)),l)*)
and mkTrue pos =  BForm ((BConst (true, pos)),None,None)

and mkFalse pos = BForm ((BConst (false, pos)),None,None)

and mkExists (vs : spec_var list) (f : formula) lbl pos = match vs with
  | [] -> f
  | v :: rest ->
      let ef = mkExists rest f lbl pos in
		if mem v (fv ef) then
		  Exists (v, ef, lbl, pos)
		else
		  ef

and mkExistsBranches (vs : spec_var list) (f : (branch_label * formula )list) lbl pos = 
	List.map (fun (c1,c2)-> (c1,(mkExists vs c2 lbl pos))) f
	
and mkForall (vs : spec_var list) (f : formula) lbl pos = match vs with
  | [] -> f
  | v :: rest ->
      let ef = mkForall rest f lbl pos in
		if mem v (fv ef) then
		  Forall (v, ef, lbl, pos)
		else
		  ef

and split_conjunctions = function
  | And (x, y, _) -> (split_conjunctions x) @ (split_conjunctions y)
  | z -> [z]
  
and join_conjunctions f = 
	List.fold_left (fun a c-> mkAnd a c no_pos) (mkTrue no_pos) f
		  
(*take out from ante all the leafs that *)
and implied_prune_ante ante = match ante with
  | BForm (f,_,_) -> (
    match f with 
    | BConst _  | BVar _ | EqMax _ | EqMin _  | BagSub _ | BagMin _ | BagMax _  | ListAllN _ | ListPerm _ -> ante
    | ListIn _ | ListNotIn _ | BagIn _  | BagNotIn _ | Lt _ | Lte _ | Gt _ | Gte _ | Neq _ -> mkTrue no_pos
    | Eq (e1,e2,_)  -> 
      match e1 with 
        | BagUnion _ -> ante 
        | Bag _ -> ante
        | _-> match e2 with 
            | BagUnion _ -> ante 
            | Bag _ -> ante
            | _ -> mkTrue no_pos)
  | And (f1,f2,l) -> mkAnd (implied_prune_ante f1) (implied_prune_ante f2) l
  | Or _ | Not _  | Forall _  | Exists _ -> ante 

      
and is_member_pure (f:formula) (p:formula):bool = 
	let y = split_conjunctions p in
	List.exists (fun c-> equalFormula f c) y
	
and equalFormula (f1:formula)(f2:formula):bool = match (f1,f2) with
  | ((BForm (b1,_,_)),(BForm (b2,_,_))) -> equalBFormula b1 b2
  | ((Not (b1,_,_)),(Not (b2,_,_))) -> equalFormula b1 b2
  | _ -> false	


and equalBFormula (f1:b_formula)(f2:b_formula):bool = match (f1,f2) with
  | ((BVar v1),(BVar v2))-> (eq_spec_var (fst v1) (fst v2))
  | ((Lte (v1,v2,_)),(Lte (w1,w2,_)))
  | ((Lt (v1,v2,_)),(Lt (w1,w2,_)))-> (eqExp w1 v1)&&(eqExp w2 v2)
  | ((Neq (v1,v2,_)) , (Neq (w1,w2,_)))
  | ((Eq (v1,v2,_)) , (Eq (w1,w2,_))) -> ((eqExp w1 v1)&&(eqExp w2 v2))|| ((eqExp w1 v2)&&(eqExp w2 v1))
  | ((BagIn (v1,e1,_)),(BagIn (v2,e2,_)))
  | ((BagNotIn (v1,e1,_)),(BagNotIn (v2,e2,_))) -> (eq_spec_var v1 v2)&&(eqExp e1 e2)
  | ((ListIn (e1,e2,_)),(ListIn (d1,d2,_)))
  | ((ListNotIn (e1,e2,_)),(ListNotIn (d1,d2,_))) -> (eqExp e1 d1)&&(eqExp e2 d2)
  | ((ListAllN (e1,e2,_)),(ListAllN (d1,d2,_))) -> (eqExp e1 d1)&&(eqExp e2 d2)
  | ((ListPerm (e1,e2,_)),(ListPerm (d1,d2,_))) -> (eqExp e1 d1)&&(eqExp e2 d2)
  | ((BagMax (v1,v2,_)),(BagMax (w1,w2,_))) 
  | ((BagMin (v1,v2,_)),(BagMin (w1,w2,_))) -> (eq_spec_var v1 w1)&& (eq_spec_var v2 w2)
  | _ -> false
  
and eqExp (e1:exp)(e2:exp):bool = match (e1,e2) with
	| (Null _ ,Null _ ) -> true
	| (Var (v1,_), Var (v2,_)) -> (eq_spec_var v1 v2)
    | (IConst (v1,_), IConst (v2,_)) -> v1=v2
    | (FConst (v1,_), FConst (v2,_)) -> v1=v2
    | (Max (e1,e2,_),Max (d1,d2,_)) 
	| (Min (e1,e2,_),Min (d1,d2,_)) 
	| (Add (e1,e2,_),Add (d1,d2,_)) -> (((eqExp e1 d1)&&(eqExp e2 d2))||((eqExp e1 d2)&&(eqExp e2 d1)))
    | (BagDiff(e1,e2,_),BagDiff (d1,d2,_)) -> ((eqExp e1 d1)&&(eqExp e2 d2))
  (* I'm not sure about this *)
  | (Mult (e1, e2, _), Mult(d1, d2, _)) ->
      (((eqExp e1 d1)&&(eqExp e2 d2)) || ((eqExp e1 d2)&&(eqExp e2 d1)))
  | (Div _, Div _) -> false (* FIX IT *)
	| (Bag (l1,_),Bag (l2,_)) -> if (List.length l1)=(List.length l1) then List.for_all2 (fun a b-> (eqExp a b)) l1 l2 
										else false
  | (List (l1,_),List (l2,_))
  | (ListAppend (l1,_),ListAppend (l2,_))  -> if (List.length l1)=(List.length l2) then List.for_all2 (fun a b-> (eqExp a b)) l1 l2 
                    else false
  | (ListCons (e1,e2,_),ListCons (d1,d2,_)) -> (eqExp e1 d1)&&(eqExp e2 d2)
  | (ListHead (e1,_),ListHead (e2,_))
  | (ListTail (e1,_),ListTail (e2,_))
  | (ListLength (e1,_),ListLength (e2,_))
  | (ListReverse (e1,_),ListReverse (e2,_)) -> (eqExp e1 e2)
  | _ -> false
	
	
(* build relation from list of expressions, for example a,b,c < d,e, f *)
and build_relation relop alist10 alist20 lbl pos expanded=
  let rec helper1 ae alist =
	let a = List.hd alist in
	let rest = List.tl alist in
  let tt = match (relop ae a pos) with
      | Lte (e1,e2,l) 
      | Gte (e2,e1,l) -> 
          ( match e1,e2 with
            | Var (v,_), IConst(i,l) -> 
                if (i=0)&&(is_otype (type_of_spec_var v)) then Eq (e1,(Null no_pos),l) else (relop ae a pos)
            | _ -> (relop ae a pos))
      | Gt (e1,e2,l) 
      | Lt (e2,e1,l) -> 
          ( match e1,e2 with
            | Var (v,_), IConst(i,l) -> 
                if (i=0)&&(is_otype (type_of_spec_var v)) then Neq (e1,(Null no_pos),l) else (relop ae a pos)
            | _ -> (relop ae a pos))
      | _ -> (relop ae a pos) in  
	let tmp = BForm (tt,lbl,expanded) in
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
  | Prim Globals.List -> "list"
  | OType c -> c

and pos_of_exp (e : exp) = match e with
  | Null pos -> pos
  | Var (_, p) -> p
  | IConst (_, p) -> p
  | FConst (_, p) -> p
  | Add (_, _, p) -> p
  | Subtract (_, _, p) -> p
  | Mult (_, _, p) -> p
  | Div (_, _, p) -> p
  | Max (_, _, p) -> p
  | Min (_, _, p) -> p
  (*| BagEmpty (p) -> p*)
  | Bag (_, p) -> p
  | BagUnion (_, p) -> p
  | BagIntersect (_, p) -> p
  | BagDiff (_, _, p) -> p
  | List (_, p) -> p
  | ListAppend (_, p) -> p
  | ListCons (_, _, p) -> p
  | ListHead (_, p) -> p
  | ListTail (_, p) -> p
  | ListLength (_, p) -> p
  | ListReverse (_, p) -> p

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
	| (BForm(b1,_,_), BForm(b2,_,_)) -> (eq_b_formula b1 b2)
	| (Or(f1, f2, _,_), Or(f3, f4, _,_))
  | (And(f1, f2, _), And(f3, f4, _)) ->
  	((eq_pure_formula f1 f3) & (eq_pure_formula f2 f4)) or ((eq_pure_formula f1 f4) & (eq_pure_formula f2 f3))
  | (Not(f1,_, _), Not(f2,_, _)) -> (eq_pure_formula f1 f2)
  | (Exists(sv1, f1, _,_), Exists(sv2, f2, _,_))
  | (Forall(sv1, f1,_, _), Forall(sv2, f2, _,_)) -> (eq_spec_var sv1 sv2) & (eq_pure_formula f1 f2)
	| _ -> false


and eq_b_formula (b1 : b_formula) (b2 : b_formula) : bool = match (b1, b2) with
	| (BConst(c1, _), BConst(c2, _)) -> c1 = c2
	| (BVar(sv1, _), BVar(sv2, _)) -> (eq_spec_var sv1 sv2)
  | (Lte(e1, e2, _), Gt(e4, e3, _))
	| (Gt(e1, e2, _), Lte(e4, e3, _))
  | (Gte(e1, e2, _), Lt(e4, e3, _))
	| (Lt(e1, e2, _), Gte(e4, e3, _))  
	| (Lte(e1, e2, _), Lte(e3, e4, _))
	| (Gt(e1, e2, _), Gt(e3, e4, _))
	| (Gte(e1, e2, _), Gte(e3, e4, _))
	| (Lt(e1, e2, _), Lt(e3, e4, _)) -> (eq_exp e1 e3) & (eq_exp e2 e4)
	| (Neq(e1, e2, _), Neq(e3, e4, _))
	| (Eq(e1, e2, _), Eq(e3, e4, _)) -> ((eq_exp e1 e3) & (eq_exp e2 e4)) or ((eq_exp e1 e4) & (eq_exp e2 e3))
	| (EqMax(e1, e2, e3, _), EqMax(e4, e5, e6, _))
	| (EqMin(e1, e2, e3, _), EqMin(e4, e5, e6, _))  -> (eq_exp e1 e4) & ((eq_exp e2 e5) & (eq_exp e3 e6)) or ((eq_exp e2 e6) & (eq_exp e3 e5))
	| (BagIn(sv1, e1, _), BagIn(sv2, e2, _))
	| (BagNotIn(sv1, e1, _), BagNotIn(sv2, e2, _)) -> (eq_spec_var sv1 sv2) & (eq_exp e1 e2)
  | (ListIn(e1, e2, _), ListIn(d1, d2, _))
  | (ListNotIn(e1, e2, _), ListNotIn(d1, d2, _)) -> (eq_exp e1 d1) & (eq_exp e2 d2)
  | (ListAllN(e1, e2, _), ListAllN(d1, d2, _)) -> (eq_exp e1 d1) & (eq_exp e2 d2)
  | (ListPerm(e1, e2, _), ListPerm(d1, d2, _)) -> (eq_exp e1 d1) & (eq_exp e2 d2)
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
  | (FConst(f1, _), FConst(f2, _)) -> f1 = f2
	| (Subtract(e11, e12, _), Subtract(e21, e22, _))
	| (Max(e11, e12, _), Max(e21, e22, _))
	| (Min(e11, e12, _), Min(e21, e22, _))
	| (Add(e11, e12, _), Add(e21, e22, _)) -> (eq_exp e11 e21) & (eq_exp e12 e22)
  | (Mult(e11, e12, _), Mult(e21, e22, _)) -> (eq_exp e11 e21) & (eq_exp e12 e22)
  | (Div(e11, e12, _), Div(e21, e22, _)) -> (eq_exp e11 e21) & (eq_exp e12 e22)
	| (Bag(e1, _), Bag(e2, _))
	| (BagUnion(e1, _), BagUnion(e2, _))
	| (BagIntersect(e1, _), BagIntersect(e2, _)) -> (eq_exp_list e1 e2)
	| (BagDiff(e1, e2, _), BagDiff(e3, e4, _)) -> (eq_exp e1 e3) & (eq_exp e2 e4)
  | (List (l1, _), List (l2, _))
  | (ListAppend (l1, _), ListAppend (l2, _)) -> if (List.length l1) = (List.length l2) then List.for_all2 (fun a b-> (eqExp a b)) l1 l2 
          else false
  | (ListCons (e1, e2, _), ListCons (d1, d2, _)) -> (eq_exp e1 d1) && (eq_exp e2 d2)
  | (ListHead (e1, _), ListHead (e2, _))
  | (ListTail (e1, _), ListTail (e2, _))
  | (ListLength (e1, _), ListLength (e2, _))
  | (ListReverse (e1, _), ListReverse (e2, _)) -> (eq_exp e1 e2)
	| _ -> false


and remove_spec_var (sv : spec_var) (vars : spec_var list) =
  List.filter (fun v -> not (eq_spec_var sv v)) vars

(* substitution *)

and subst_var_list_avoid_capture fr t svs =
  let st1 = List.combine fr t in
  let svs1 = subst_var_list st1 svs in
	svs1

(* renaming seems redundant
and subst_var_list_avoid_capture fr t svs =
  let fresh_fr = fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let svs1 = subst_var_list st1 svs in
  let svs2 = subst_var_list st2 svs1 in
	svs2
*)

and subst_var_list sst (svs : spec_var list) = subst_var_list_par sst svs

(* filter does not support multiple occurrences of domain 
and subst_var_list sst (svs : spec_var list) = match svs with
  | sv :: rest ->
      let new_vars = subst_var_list sst rest in
      let new_sv = match List.filter (fun st -> fst st = sv) sst with
		| [(fr, t)] -> t
		| _ -> sv in
		new_sv :: new_vars
  | [] -> []
*)

and subst_var_list_par sst (svs : spec_var list) = match svs with
  | sv :: rest ->
      let new_vars = subst_var_list sst rest in
      let new_sv = subs_one sst sv in 
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
  (* let f2 = subst st1 f in *) 
  (* changing to a parallel substitution below *)
  let f2 = par_subst st1 f in 
  f2

and subst (sst : (spec_var * spec_var) list) (f : formula) : formula = match sst with
  | s::ss -> subst ss (apply_one s f) 				(* applies one substitution at a time *)
  | [] -> f

and par_subst sst f = apply_subs sst f

and apply_subs (sst : (spec_var * spec_var) list) (f : formula) : formula = match f with
  | BForm (bf,lbl,expanded) -> BForm ((b_apply_subs sst bf),lbl,expanded)
  | And (p1, p2, pos) -> And (apply_subs sst p1,
							  apply_subs sst p2, pos)
  | Or (p1, p2, lbl,pos) -> Or (apply_subs sst p1,
							apply_subs sst p2, lbl, pos)
  | Not (p, lbl, pos) -> Not (apply_subs sst p, lbl, pos)
  | Forall (v, qf,lbl, pos) ->
      let sst = diff sst v in
      if (var_in_target v sst) then
        let fresh_v = fresh_spec_var v in
           Forall (fresh_v, apply_subs sst (apply_one (v, fresh_v) qf), lbl, pos)
      else Forall (v, apply_subs sst qf, lbl, pos)
  | Exists (v, qf, lbl, pos) ->
      let sst = diff sst v in
      if (var_in_target v sst) then
        let fresh_v = fresh_spec_var v in
           Exists  (fresh_v, apply_subs sst (apply_one (v, fresh_v) qf), lbl, pos)
      else Exists  (v, apply_subs sst qf, lbl, pos)


(* cannot change to a let, why? *)
and diff (sst : (spec_var * 'b) list) (v:spec_var) : (spec_var * 'b) list
  = List.filter (fun (a,_) -> not(eq_spec_var a v)) sst

and var_in_target v sst = List.fold_left (fun curr -> fun (_,t) -> curr or (eq_spec_var t v)) false sst

and b_apply_subs sst bf = match bf with
  | BConst _ -> bf
  | BVar (bv, pos) -> BVar (subs_one sst bv, pos)
  | Lt (a1, a2, pos) -> Lt (e_apply_subs sst a1,
							e_apply_subs sst a2, pos)
  | Lte (a1, a2, pos) -> Lte (e_apply_subs sst a1,
							  e_apply_subs sst a2, pos)
  | Gt (a1, a2, pos) -> Gt (e_apply_subs sst a1,
							e_apply_subs sst a2, pos)
  | Gte (a1, a2, pos) -> Gte (e_apply_subs sst a1,
							  e_apply_subs sst a2, pos)
  | Eq (a1, a2, pos) -> Eq (e_apply_subs sst a1,
							e_apply_subs sst a2, pos)
  | Neq (a1, a2, pos) -> Neq (e_apply_subs sst a1,
							  e_apply_subs sst a2, pos)
  | EqMax (a1, a2, a3, pos) -> EqMax (e_apply_subs sst a1,
									  e_apply_subs sst a2,
									  e_apply_subs sst a3, pos)
  | EqMin (a1, a2, a3, pos) -> EqMin (e_apply_subs sst a1,
									  e_apply_subs sst a2,
									  e_apply_subs sst a3, pos)
  | BagIn (v, a1, pos) -> BagIn (subs_one sst v, e_apply_subs sst a1, pos)
  | BagNotIn (v, a1, pos) -> BagNotIn (subs_one sst v, e_apply_subs sst a1, pos)
	(* is it ok?... can i have a set of boolean values?... don't think so... *)
  | BagSub (a1, a2, pos) -> BagSub (e_apply_subs sst a1, e_apply_subs sst a2, pos)
  | BagMax (v1, v2, pos) -> BagMax (subs_one sst v1, subs_one sst v2, pos)
  | BagMin (v1, v2, pos) -> BagMin (subs_one sst v1, subs_one sst v2, pos)
  | ListIn (a1, a2, pos) -> ListIn (e_apply_subs sst a1, e_apply_subs sst a2, pos)
  | ListNotIn (a1, a2, pos) -> ListNotIn (e_apply_subs sst a1, e_apply_subs sst a2, pos)
  | ListAllN (a1, a2, pos) -> ListAllN (e_apply_subs sst a1, e_apply_subs sst a2, pos)
  | ListPerm (a1, a2, pos) -> ListPerm (e_apply_subs sst a1, e_apply_subs sst a2, pos)

and subs_one sst v = List.fold_left (fun old -> fun (fr,t) -> if (eq_spec_var fr v) then t else old) v sst 

and e_apply_subs sst e = match e with
  | Null _ | IConst _ | FConst _ -> e
  | Var (sv, pos) -> Var (subs_one sst sv, pos)
  | Add (a1, a2, pos) -> Add (e_apply_subs sst a1,
							  e_apply_subs sst a2, pos)
  | Subtract (a1, a2, pos) -> Subtract (e_apply_subs sst  a1,
										e_apply_subs sst a2, pos)
  | Mult (a1, a2, pos) -> 
      Mult (e_apply_subs sst a1, e_apply_subs sst a2, pos)
  | Div (a1, a2, pos) ->
      Div (e_apply_subs sst a1, e_apply_subs sst a2, pos)
  | Max (a1, a2, pos) -> Max (e_apply_subs sst a1,
							  e_apply_subs sst a2, pos)
  | Min (a1, a2, pos) -> Min (e_apply_subs sst a1,
							  e_apply_subs sst a2, pos)
	(*| BagEmpty (pos) -> BagEmpty (pos)*)
  | Bag (alist, pos) -> Bag ((e_apply_subs_list sst alist), pos)
  | BagUnion (alist, pos) -> BagUnion ((e_apply_subs_list sst alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((e_apply_subs_list sst alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (e_apply_subs sst a1,
							  e_apply_subs sst a2, pos)
  | List (alist, pos) -> List (e_apply_subs_list sst alist, pos)
  | ListAppend (alist, pos) -> ListAppend (e_apply_subs_list sst alist, pos)
  | ListCons (a1, a2, pos) -> ListCons (e_apply_subs sst a1, e_apply_subs sst a2, pos)
  | ListHead (a, pos) -> ListHead (e_apply_subs sst a, pos)
  | ListTail (a, pos) -> ListTail (e_apply_subs sst a, pos)
  | ListLength (a, pos) -> ListLength (e_apply_subs sst a, pos)
  | ListReverse (a, pos) -> ListReverse (e_apply_subs sst a, pos)

and e_apply_subs_list sst alist = List.map (e_apply_subs sst) alist

and apply_one (fr, t) f = match f with
  | BForm (bf,lbl,expanded) -> BForm (b_apply_one (fr, t) bf , lbl,expanded)
  | And (p1, p2, pos) -> And (apply_one (fr, t) p1,
							  apply_one (fr, t) p2, pos)
  | Or (p1, p2, lbl, pos) -> Or (apply_one (fr, t) p1,
							apply_one (fr, t) p2, lbl, pos)
  | Not (p, lbl, pos) -> Not (apply_one (fr, t) p, lbl, pos)
  | Forall (v, qf, lbl, pos) ->
	  if eq_spec_var v fr then f
      else if eq_spec_var v t then
        let fresh_v = fresh_spec_var v in
        Forall (fresh_v, apply_one (fr, t) (apply_one (v, fresh_v) qf), lbl, pos)
	  else Forall (v, apply_one (fr, t) qf, lbl, pos)
  | Exists (v, qf, lbl, pos) ->
	  if eq_spec_var v fr then f
      else if eq_spec_var v t then
        let fresh_v = fresh_spec_var v in
        Exists (fresh_v, apply_one (fr, t) (apply_one (v, fresh_v) qf), lbl, pos)
	  else Exists (v, apply_one (fr, t) qf, lbl, pos)

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
  | ListIn (a1, a2, pos) -> ListIn (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | ListNotIn (a1, a2, pos) -> ListNotIn (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | ListAllN (a1, a2, pos) -> ListAllN (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | ListPerm (a1, a2, pos) -> ListPerm (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)

and e_apply_one (fr, t) e = match e with
  | Null _ | IConst _ | FConst _ -> e
  | Var (sv, pos) -> Var ((if eq_spec_var sv fr then t else sv), pos)
  | Add (a1, a2, pos) -> Add (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
  | Subtract (a1, a2, pos) -> Subtract (e_apply_one (fr, t) a1,
										e_apply_one (fr, t) a2, pos)
  | Mult (a1, a2, pos) ->
      Mult (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | Div (a1, a2, pos) ->
      Div (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | Max (a1, a2, pos) -> Max (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
  | Min (a1, a2, pos) -> Min (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
	(*| BagEmpty (pos) -> BagEmpty (pos)*)
  | Bag (alist, pos) -> Bag (e_apply_one_list (fr, t) alist, pos)
  | BagUnion (alist, pos) -> BagUnion (e_apply_one_list (fr, t) alist, pos)
  | BagIntersect (alist, pos) -> BagIntersect (e_apply_one_list (fr, t) alist, pos)
  | BagDiff (a1, a2, pos) -> BagDiff (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
  | List (alist, pos) -> List (e_apply_one_list (fr, t) alist, pos)
  | ListAppend (alist, pos) -> ListAppend (e_apply_one_list (fr, t) alist, pos)
  | ListCons (a1, a2, pos) -> ListCons (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | ListHead (a, pos) -> ListHead (e_apply_one (fr, t) a, pos)
  | ListTail (a, pos) -> ListTail (e_apply_one (fr, t) a, pos)
  | ListLength (a, pos) -> ListLength (e_apply_one (fr, t) a, pos)
  | ListReverse (a, pos) -> ListReverse (e_apply_one (fr, t) a, pos)

and e_apply_one_list (fr, t) alist = match alist with
	|[] -> []
	|a :: rest -> (e_apply_one (fr, t) a) :: (e_apply_one_list (fr, t) rest)

(* substituting terms for variables: can name-capturing happen?
   yes. What to do? *)

(* remove redundant renaming
and subst_term_avoid_capture (sst : (spec_var * exp) list) (f : formula) : formula =
  let fr = List.map fst sst in
  let t = List.map snd sst in
  let fresh_fr = fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst st1 f in
  let f2 = subst_term st2 f1 in
	f2
*)

and subst_term_avoid_capture (sst : (spec_var * exp) list) (f : formula) : formula =
  let f2 = subst_term_par sst f in
	f2
	
and subst_term (sst : (spec_var * exp) list) (f : formula) : formula = match sst with
  | s :: ss -> subst_term ss (apply_one_term s f)
  | [] -> f

and subst_term_par (sst : (spec_var * exp) list) (f : formula) : formula = 
  apply_par_term sst f
 
(* wasn't able to make diff/diff_term polymorphic! how come? *)

and diff_term (sst : (spec_var * exp) list) (v:spec_var) : (spec_var * exp) list
 = List.filter (fun (a,_) -> not(eq_spec_var a v)) sst

and apply_par_term (sst : (spec_var * exp) list) f = match f with
  | BForm (bf,lbl,expanded) -> BForm (b_apply_par_term sst bf , lbl,expanded)
  | And (p1, p2, pos) -> And (apply_par_term sst p1, apply_par_term sst p2, pos)
  | Or (p1, p2,lbl, pos) -> Or (apply_par_term sst p1, apply_par_term sst p2, lbl, pos)
  | Not (p, lbl, pos) -> Not (apply_par_term sst p, lbl, pos)
  | Forall (v, qf, lbl, pos) ->
      let sst = diff_term sst v in
      if (var_in_target_term v sst) then
        let fresh_v = fresh_spec_var v in
           Forall (fresh_v, apply_par_term sst (apply_one (v, fresh_v) qf), lbl, pos)
      else if sst==[] then f else 
           Forall (v, apply_par_term sst qf, lbl, pos)
  | Exists (v, qf, lbl, pos) ->
      let sst = diff_term sst v in
      if (var_in_target_term v sst) then
        let fresh_v = fresh_spec_var v in
           Exists  (fresh_v, apply_par_term sst (apply_one (v, fresh_v) qf), lbl, pos)
      else if sst==[] then f else 
           Exists  (v, apply_par_term sst qf, lbl, pos)
           
and var_in_target_term v sst = List.fold_left (fun curr -> fun (_,t) -> curr or (is_member v t)) false sst

and is_member v t = let vl=afv t in List.fold_left (fun curr -> fun nv -> curr or (eq_spec_var v nv)) false vl

and b_apply_par_term (sst : (spec_var * exp) list) bf = match bf with
  | BConst _ -> bf
  | BVar (bv, pos) ->
	  if List.fold_left (fun curr -> fun (fr,_) -> curr or eq_spec_var bv fr) false sst   then
		failwith ("Presburger.b_apply_one_term: attempting to substitute arithmetic term for boolean var")
	  else
		bf
  | Lt (a1, a2, pos) -> Lt (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Lte (a1, a2, pos) -> Lte (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Gt (a1, a2, pos) -> Gt (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Gte (a1, a2, pos) -> Gte (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Eq (a1, a2, pos) -> Eq (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Neq (a1, a2, pos) -> Neq (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | EqMax (a1, a2, a3, pos) -> EqMax (a_apply_par_term sst a1, a_apply_par_term sst a2, a_apply_par_term sst a3, pos)
  | EqMin (a1, a2, a3, pos) -> EqMin (a_apply_par_term sst a1, a_apply_par_term sst a2, a_apply_par_term sst a3, pos)
  | BagIn (v, a1, pos) -> BagIn (v, a_apply_par_term sst a1, pos)
  | BagNotIn (v, a1, pos) -> BagNotIn (v, a_apply_par_term sst a1, pos)
  | BagSub (a1, a2, pos) -> BagSub (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | BagMax (v1, v2, pos) -> BagMax (v1, v2, pos)
  | BagMin (v1, v2, pos) -> BagMin (v1, v2, pos)
  | ListIn (a1, a2, pos) -> ListIn (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | ListNotIn (a1, a2, pos) -> ListNotIn (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | ListAllN (a1, a2, pos) -> ListAllN (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | ListPerm (a1, a2, pos) -> ListPerm (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)

and subs_one_term sst v orig = List.fold_left (fun old  -> fun  (fr,t) -> if (eq_spec_var fr v) then t else old) orig sst 

and a_apply_par_term (sst : (spec_var * exp) list) e = match e with
  | Null _ -> e
  | IConst _ -> e
  | FConst _ -> e
  | Add (a1, a2, pos) -> Add (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Subtract (a1, a2, pos) -> Subtract (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Mult (a1, a2, pos) ->
      Mult (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Div (a1, a2, pos) ->
      Div (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Var (sv, pos) -> subs_one_term sst sv e (* if eq_spec_var sv fr then t else e *)
  | Max (a1, a2, pos) -> Max (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | Min (a1, a2, pos) -> Min (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
	  (*| BagEmpty (pos) -> BagEmpty (pos)*)
  | Bag (alist, pos) -> Bag ((a_apply_par_term_list sst alist), pos)
  | BagUnion (alist, pos) -> BagUnion ((a_apply_par_term_list sst alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((a_apply_par_term_list sst alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (a_apply_par_term sst a1,
									  a_apply_par_term sst a2, pos)
  | List (alist, pos) -> List ((a_apply_par_term_list sst alist), pos)
  | ListAppend (alist, pos) -> ListAppend ((a_apply_par_term_list sst alist), pos)
  | ListCons (a1, a2, pos) -> ListCons (a_apply_par_term sst a1, a_apply_par_term sst a2, pos)
  | ListHead (a1, pos) -> ListHead (a_apply_par_term sst a1, pos)
  | ListTail (a1, pos) -> ListTail (a_apply_par_term sst a1, pos)
  | ListLength (a1, pos) -> ListLength (a_apply_par_term sst a1, pos)
  | ListReverse (a1, pos) -> ListReverse (a_apply_par_term sst a1, pos)

and a_apply_par_term_list sst alist = match alist with
  |[] -> []
  |a :: rest -> (a_apply_par_term sst a) :: (a_apply_par_term_list sst rest)

and apply_one_term (fr, t) f = match f with
  | BForm (bf,lbl,expanded) -> BForm (b_apply_one_term (fr, t) bf , lbl, expanded)
  | And (p1, p2, pos) -> And (apply_one_term (fr, t) p1, apply_one_term (fr, t) p2, pos)
  | Or (p1, p2, lbl, pos) -> Or (apply_one_term (fr, t) p1, apply_one_term (fr, t) p2, lbl, pos)
  | Not (p, lbl, pos) -> Not (apply_one_term (fr, t) p, lbl, pos)
  | Forall (v, qf, lbl, pos) -> if eq_spec_var v fr then f else Forall (v, apply_one_term (fr, t) qf, lbl, pos)
  | Exists (v, qf, lbl, pos) -> if eq_spec_var v fr then f else Exists (v, apply_one_term (fr, t) qf, lbl, pos)
  
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
  | ListIn (a1, a2, pos) -> ListIn (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | ListNotIn (a1, a2, pos) -> ListNotIn (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | ListAllN (a1, a2, pos) -> ListAllN (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | ListPerm (a1, a2, pos) -> ListPerm (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)

and a_apply_one_term ((fr, t) : (spec_var * exp)) e = match e with
  | Null _ -> e
  | IConst _ -> e
  | FConst _ -> e
  | Add (a1, a2, pos) -> Add (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Subtract (a1, a2, pos) -> Subtract (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Mult (a1, a2, pos) ->
      Mult (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Div (a1, a2, pos) ->
      Div (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Var (sv, pos) -> if eq_spec_var sv fr then t else e
  | Max (a1, a2, pos) -> Max (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | Min (a1, a2, pos) -> Min (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
	  (*| BagEmpty (pos) -> BagEmpty (pos)*)
  | Bag (alist, pos) -> Bag ((a_apply_one_term_list (fr, t) alist), pos)
  | BagUnion (alist, pos) -> BagUnion ((a_apply_one_term_list (fr, t) alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((a_apply_one_term_list (fr, t) alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (a_apply_one_term (fr, t) a1,
									  a_apply_one_term (fr, t) a2, pos)
  | List (alist, pos) -> List ((a_apply_one_term_list (fr, t) alist), pos)
  | ListAppend (alist, pos) -> ListAppend ((a_apply_one_term_list (fr, t) alist), pos)
  | ListCons (a1, a2, pos) -> ListCons (a_apply_one_term (fr, t) a1, a_apply_one_term (fr, t) a2, pos)
  | ListHead (a1, pos) -> ListHead (a_apply_one_term (fr, t) a1, pos)
  | ListTail (a1, pos) -> ListTail (a_apply_one_term (fr, t) a1, pos)
  | ListLength (a1, pos) -> ListLength (a_apply_one_term (fr, t) a1, pos)
  | ListReverse (a1, pos) -> ListReverse (a_apply_one_term (fr, t) a1, pos)


and a_apply_one_term_selective variance ((fr, t) : (spec_var * exp)) e : (bool*exp) = 
  let rec a_apply_one_term_list crt_var alist = match alist with
  |[] -> (false,[])
  |a :: rest -> 
    let b1,r1 = (helper crt_var a) in
    let b2,r2 = (a_apply_one_term_list crt_var rest) in
    ((b1||b2),(r1::r2))

  and helper crt_var e = match e with
  | Null _   -> (false,e)
  | IConst _ -> (false,e)
  | FConst _ -> (false,e)
  | Add (a1, a2, pos) -> 
      let b1, r1 = helper crt_var a1 in
      let b2, r2 = helper crt_var a2 in
      ((b1||b2), Add (r1, r2, pos))
  | Subtract (a1, a2, pos) -> 
    let b1 , r1 = helper crt_var a1 in
    let b2 , r2 = helper (not crt_var) a2 in
    (b1||b2, Subtract (r1 , r2 , pos))
  | Mult (a1, a2, pos) ->
      let b1 , r1 = helper crt_var a1 in
      let b2 , r2 = helper crt_var a2 in
      (b1||b2, Mult (r1 , r2 , pos))
  | Div (a1, a2, pos) ->
      let b1 , r1 = helper crt_var a1 in
      let b2 , r2 = helper (not crt_var) a2 in
      (b1||b2, Div (r1 , r2 , pos))
  | Var (sv, pos) -> if ((variance==crt_var)||(eq_spec_var sv fr)) then (true, t) else (false, e)
  | Max (a1, a2, pos) -> 
      let b1 , r1 = helper crt_var a1 in
      let b2 , r2 = helper crt_var a2 in
      (b1||b2, Max (r1 , r2 , pos))
  | Min (a1, a2, pos) -> 
      let b1 , r1 = helper (not crt_var) a1 in
      let b2 , r2 = helper (not crt_var) a2 in
      (b1||b2, Min (r1 , r2 , pos))
	  (*| BagEmpty (pos) -> BagEmpty (pos)*)
  | Bag (alist, pos) -> 
    let b1,r1 = (a_apply_one_term_list crt_var alist) in
      (b1,Bag (r1, pos))
  | BagUnion (alist, pos) -> 
    let b1,r1 = (a_apply_one_term_list crt_var alist) in
      (b1,BagUnion (r1, pos))
  | BagIntersect (alist, pos) -> 
    let b1,r1 = (a_apply_one_term_list (not crt_var) (List.tl alist)) in
    let b2,r2 = helper crt_var (List.hd alist) in
      (b1||b2 ,BagIntersect (r2::r1, pos))
  | BagDiff (a1, a2, pos) -> 
    let b1 , r1 = helper crt_var a1 in
    let b2 , r2 = helper (not crt_var) a2 in
      (b1||b2, BagDiff (r1 , r2 , pos))
  | List (alist, pos) -> 
    let b1,r1 = (a_apply_one_term_list crt_var alist) in
      (b1,List (r1, pos))
  | ListAppend (alist, pos) -> 
    let b1,r1 = (a_apply_one_term_list crt_var alist) in
      (b1,ListAppend (r1, pos))
  | ListCons (a1, a2, pos) -> 
    let b1 , r1 = helper crt_var a1 in
    let b2 , r2 = helper crt_var a2 in
      (b1||b2, ListCons (r1 , r2 , pos))
  | ListHead (a1, pos) -> 
    let b1,r1 = (helper crt_var a1) in
      (b1,ListHead (r1, pos))
  | ListTail (a1, pos) -> 
    let b1,r1 = (helper crt_var a1) in
      (b1,ListTail (r1, pos))
  | ListLength (a1, pos) -> 
    let b1,r1 = (helper crt_var a1) in
      (b1,ListLength (r1, pos))
  | ListReverse (a1, pos) -> 
    let b1,r1 = (helper crt_var a1) in
      (b1,ListReverse (r1, pos)) in
  (helper true e)

  
  
and a_apply_one_term_list (fr, t) alist = match alist with
  |[] -> []
  |a :: rest -> (a_apply_one_term (fr, t) a) :: (a_apply_one_term_list (fr, t) rest)

and rename_top_level_bound_vars (f : formula) = match f with
  | Or (f1, f2, lbl, pos) ->
	  let rf1 = rename_top_level_bound_vars f1 in
	  let rf2 = rename_top_level_bound_vars f2 in
	  let resform = mkOr rf1 rf2 lbl pos in
		resform
  | And (f1, f2, pos) ->
	  let rf1 = rename_top_level_bound_vars f1 in
	  let rf2 = rename_top_level_bound_vars f2 in
	  let resform = mkAnd rf1 rf2 pos in
		resform
  | Exists (qvar, qf, lbl, pos) ->
	  let renamed_f = rename_top_level_bound_vars qf in
	  let new_qvar = fresh_spec_var qvar in
	  let rho = [(qvar, new_qvar)] in
	  let new_qf = subst rho renamed_f in
	  let res_form = Exists (new_qvar, new_qf,lbl,  pos) in
		res_form
  | Forall (qvar, qf, lbl, pos) ->
	  let renamed_f = rename_top_level_bound_vars qf in
	  let new_qvar = fresh_spec_var qvar in
	  let rho = [(qvar, new_qvar)] in
	  let new_qf = subst rho renamed_f in
	  let res_form = Forall (new_qvar, new_qf, lbl, pos) in
		res_form
  | _ -> f

and split_ex_quantifiers (f0 : formula) : (spec_var list * formula) = match f0 with
  | Exists (qv, qf, lbl, pos) ->
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
  | BForm (bf,lbl,expanded) -> get_subst_equation_b_formula bf v lbl expanded
  | _ -> ([], f0)

and get_subst_equation_b_formula (f0 : b_formula) (v : spec_var) lbl expanded: ((spec_var * exp) list * formula) = match f0 with
  | Eq (e1, e2, pos) -> begin
	  if is_var e1 then
		let v1 = to_var e1 in
		  if eq_spec_var v1 v then ([(v, e2)], mkTrue no_pos )
		  else if is_var e2 then
			let v2 = to_var e2 in
			  if eq_spec_var v2 v then ([(v, e1)], mkTrue no_pos )
			  else ([], BForm (f0,lbl,expanded))
		  else ([], BForm (f0,lbl,expanded))
	  else if is_var e2 then
			let v2 = to_var e2 in
			  if eq_spec_var v2 v then ([(v, e1)], mkTrue no_pos )
			  else ([], BForm (f0,lbl,expanded))
		  else ([], BForm (f0,lbl,expanded))
	end
  | _ -> ([], BForm (f0,lbl,expanded))

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
(* 16.04.09 *)	
and list_of_disjs (f0 : formula) : formula list =
  let rec helper f disjs = match f with
	| Or (f1, f2,_,_) ->
		let tmp1 = helper f2 disjs in
		let tmp2 = helper f1 tmp1 in
		  tmp2
	| _ -> f :: disjs
  in
	helper f0 []

(*	
and disj_of_list (fs : formula list) pos : formula =
  let helper f1 f2 = mkOr f1 f2 pos in
	List.fold_left helper (mkTrue pos) fs
*)
	
and disj_of_list (disj_list : formula list) pos : formula = 
	match disj_list with
	| [] -> mkTrue pos
	| h :: [] -> h
	| h :: rest -> mkOr h (disj_of_list rest pos) None pos
(* 16.04.09 *)

and find_bound v f0 =
  match f0 with
  | And (f1, f2, pos) ->
      begin
      let min1, max1 = find_bound v f1 in
      let min2, max2 = find_bound v f2 in
      let min = 
        match min1, min2 with
        | None, None -> None
        | Some m1, Some m2 -> if m1 < m2 then min1 else min2 
        | Some m, None -> min1
        | None, Some m -> min2
      in
      let max =
        match max1, max2 with
        | None, None -> None
        | Some m1, Some m2 -> if m1 > m2 then max1 else max2 
        | Some m, None -> max1 
        | None, Some m -> max2
      in
      (min, max)
      end
  | BForm (bf,_,_) -> find_bound_b_formula v bf
  | _ -> None, None

  (*
and find_bound_b_formula_redlog v f0 =
  let cmd = "rlopt({" ^ (Redlog.rl_of_b_formula f0) ^ "}, " ^ (Redlog.rl_of_spec_var v) ^ ");\n" in
  let res = Redlog.send_and_receive cmd in
  print_endline res
  *)

and find_bound_b_formula v f0 =
  let val_for_max e included =
    if included then
      (* x <= e --> max(x) = floor(e) *)
      to_int_const e Floor
    else
      (* x < e --> max(x) = ceil(e) - 1 *)
      (to_int_const e Ceil) - 1
  in
  let val_for_min e included = 
    if included then
      (* x >= e --> min(x) = ceil(e) *)
      to_int_const e Ceil
    else
      (* x > e --> min(x) = floor(e) + 1 *)
      (to_int_const e Floor) + 1
  in
  let helper e1 e2 is_lt is_eq =
    if (is_var e1) && (is_num e2) then
      let v1 = to_var e1 in
      if eq_spec_var v1 v then
        if is_lt then
          let max = val_for_max e2 is_eq in
          (None, Some max)
        else
          let min = val_for_min e2 is_eq in
          (Some min, None)
      else
        (None, None)
    else if (is_var e2) && (is_num e1) then
      let v2 = to_var e2 in
      if eq_spec_var v2 v then
        if is_lt then
          let min = val_for_min e1 is_eq in
          (Some min, None)
        else
          let max = val_for_max e1 is_eq in
          (None, Some max)
      else
        (None, None)
    else
      (None, None)
  in
  match f0 with
  | Lt (e1, e2, pos) -> helper e1 e2 true false
  | Lte (e1, e2, pos) -> helper e1 e2 true true
  | Gt (e1, e2, pos) -> helper e1 e2 false false
  | Gte (e1, e2, pos) -> helper e1 e2 false true
  | _ -> (None, None)

and elim_exists_with_ineq (f0: formula): formula =
  match f0 with
  | Exists (qvar, qf,lbl, pos) ->
      begin
        match qf with
        | Or (qf1, qf2,lbl2, qpos) ->
            let new_qf1 = mkExists [qvar] qf1 lbl qpos in
            let new_qf2 = mkExists [qvar] qf2 lbl qpos in
            let eqf1 = elim_exists_with_ineq new_qf1 in
            let eqf2 = elim_exists_with_ineq new_qf2 in
            let res = mkOr eqf1 eqf2 lbl2 pos in
            res
        | _ ->
            let eqqf = elim_exists qf in
            let min, max = find_bound qvar eqqf in
            begin
              match min, max with
              | Some mi, Some ma -> 
                  let res = ref (mkFalse pos) in
                  begin
                    for i = mi to ma do
                      res := mkOr !res (apply_one_term (qvar, IConst (i, pos)) eqqf) lbl pos
                    done;
                    !res
                  end
              | _ -> f0
            end
      end
  | And (f1, f2, pos) ->
      let ef1 = elim_exists_with_ineq f1 in
      let ef2 = elim_exists_with_ineq f2 in
      mkAnd ef1 ef2 pos
  | Or (f1, f2, lbl, pos) ->
      let ef1 = elim_exists_with_ineq f1 in
      let ef2 = elim_exists_with_ineq f2 in
      mkOr ef1 ef2 lbl pos
  | Not (f1, lbl, pos) ->
      let ef1 = elim_exists_with_ineq f1 in
      mkNot ef1 lbl pos
  | Forall (qvar, qf, lbl, pos) ->
      let eqf = elim_exists_with_ineq qf in
      mkForall [qvar] eqf lbl pos
  | BForm _ -> f0

and elim_exists (f0 : formula) : formula = 
  match f0 with
  | Exists (qvar, qf, lbl, pos) -> begin
	  match qf with
		| Or (qf1, qf2, lbl2, qpos) ->
			let new_qf1 = mkExists [qvar] qf1 lbl qpos in
			let new_qf2 = mkExists [qvar] qf2 lbl qpos in
			let eqf1 = elim_exists new_qf1 in
			let eqf2 = elim_exists new_qf2 in
			let res = mkOr eqf1 eqf2 lbl2 pos in
			  res
		| _ ->
			let qf = elim_exists qf in
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
				let new_qf = mkExists qvars0 new_qf lbl pos in
				let tmp3 = elim_exists new_qf in
				let tmp4 = mkAnd no_qvars tmp3 pos in
				  tmp4
			else (* if qvar is not equated to any variables, try the next one *)
				let tmp1 = qf (*elim_exists qf*) in
				let tmp2 = mkExists [qvar] tmp1 lbl pos in
				  tmp2
	end
  | And (f1, f2, pos) -> begin
	  let ef1 = elim_exists f1 in
	  let ef2 = elim_exists f2 in
	  let res = mkAnd ef1 ef2 pos in
		res
	end
  | Or (f1, f2, lbl, pos) -> begin
	  let ef1 = elim_exists f1 in
	  let ef2 = elim_exists f2 in
	  let res = mkOr ef1 ef2 lbl pos in
		res
	end
  | Not (f1, lbl, pos) -> begin
	  let ef1 = elim_exists f1 in
	  let res = mkNot ef1 lbl pos in
		res
	end
  | Forall (qvar, qf, lbl, pos) -> begin
	  let eqf = elim_exists qf in
	  let res = mkForall [qvar] eqf lbl pos in
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
  Drop bag and list constraints for satisfiability checking.
*)
let rec drop_bag_formula (f0 : formula) : formula = match f0 with
  | BForm (bf,lbl,extended) -> BForm (drop_bag_b_formula bf, lbl,extended)
  | And (f1, f2, pos) ->
	  let df1 = drop_bag_formula f1 in
	  let df2 = drop_bag_formula f2 in
	  let df = mkAnd df1 df2 pos in
		df
  | Or (f1, f2, lbl, pos) ->
	  let df1 = drop_bag_formula f1 in
	  let df2 = drop_bag_formula f2 in
	  let df = mkOr df1 df2 lbl pos in
		df
  | Not (f1, lbl, pos) ->
	  let df1 = drop_bag_formula f1 in
	  let df = mkNot df1 lbl pos in
		df
  | Forall (qvar, qf,lbl, pos) ->
	  let dqf = drop_bag_formula qf in
	  let df = mkForall [qvar] dqf lbl pos in
		df
  | Exists (qvar, qf,lbl, pos) ->
	  let dqf = drop_bag_formula qf in
	  let df = mkExists [qvar] dqf lbl pos in
		df

and drop_bag_b_formula (bf0 : b_formula) : b_formula = match bf0 with
  | BagIn _
  | BagNotIn _
  | BagSub _
  | BagMin _
  | BagMax _
  | ListIn _
  | ListNotIn _
  | ListAllN _
  | ListPerm _ -> BConst (true, no_pos)
  | Eq (e1, e2, pos)
  | Neq (e1, e2, pos) ->
	  if (is_bag e1) || (is_bag e2) || (is_list e1) || (is_list e2) then
		BConst (true, pos)
	  else
		bf0
  | _ -> bf0


(**************************************************************)
(**************************************************************)
(**************************************************************)

(*
  List of bag variables.
*)
let rec bag_vars_formula (f0 : formula) : spec_var list = match f0 with
  | BForm (bf,lbl,_) -> (bag_vars_b_formula bf)
  | And (f1, f2, pos) -> (bag_vars_formula f1) @ (bag_vars_formula f2)
  | Or (f1, f2, lbl, pos)  -> (bag_vars_formula f1) @ (bag_vars_formula f2)
  | Not (f1, lbl, pos) -> (bag_vars_formula f1)
  | Forall (qvar, qf, lbl, pos) -> (bag_vars_formula qf)
  | Exists (qvar, qf, lbl, pos) -> (bag_vars_formula qf)
    
and bag_vars_b_formula (bf0 : b_formula) : spec_var list = match bf0 with
  | BagIn (v1,_,_)
  | BagNotIn (v1,_,_) -> [v1]
  | BagMin (v1,v2,_)
  | BagMax (v1,v2,_) -> [v1;v2]
  | _ -> []
   
(*************************************************************************************************************************
	05.06.2008:
	Utilities for existential quantifier elimination:
	- before we were only searching for substitutions of the form v1 = v2 and then substitute ex v1. P(v1) --> P(v2)
	- now, we want to be more aggressive and search for substitutions of the form v1 = exp2; however, we can only apply these substitutions to the pure part
	(due to the way shape predicates are recorded --> root pointer and args are suppose to be spec vars)
*************************************************************************************************************************)

and apply_one_exp ((fr, t) : spec_var * exp) f = match f with
  | BForm (bf, lbl,extended) -> BForm (b_apply_one_exp (fr, t) bf, lbl,extended)
  | And (p1, p2, pos) -> And (apply_one_exp (fr, t) p1,
							  apply_one_exp (fr, t) p2, pos)
  | Or (p1, p2, lbl, pos) -> Or (apply_one_exp (fr, t) p1,
							apply_one_exp (fr, t) p2,lbl, pos)
  | Not (p, lbl, pos) -> Not (apply_one_exp (fr, t) p,lbl, pos)
  | Forall (v, qf, lbl, pos) ->
	  if eq_spec_var v fr then f
	  else Forall (v, apply_one_exp (fr, t) qf,lbl, pos)
  | Exists (v, qf, lbl, pos) ->
	  if eq_spec_var v fr then f
	  else Exists (v, apply_one_exp (fr, t) qf, lbl, pos)

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
	(* is it ok?... can i have a set of boolean values?... don't think so... *)
  | BagSub (a1, a2, pos) -> BagSub (a1, e_apply_one_exp (fr, t) a2, pos)
  | BagMax (v1, v2, pos) -> bf
  | BagMin (v1, v2, pos) -> bf
  | ListIn (a1, a2, pos) -> bf
  | ListNotIn (a1, a2, pos) -> bf
  | ListAllN (a1, a2, pos) -> bf
  | ListPerm (a1, a2, pos) -> bf

and e_apply_one_exp (fr, t) e = match e with
  | Null _ | IConst _ | FConst _ -> e
  | Var (sv, pos) -> if eq_spec_var sv fr then t else e
  | Add (a1, a2, pos) -> Add (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
  | Subtract (a1, a2, pos) -> Subtract (e_apply_one_exp (fr, t) a1,
										e_apply_one_exp (fr, t) a2, pos)
  | Mult (a1, a2, pos) -> 
      Mult (e_apply_one_exp (fr, t) a1, e_apply_one_exp (fr, t) a2, pos)
  | Div (a1, a2, pos) ->
      Div (e_apply_one_exp (fr, t) a1, e_apply_one_exp (fr, t) a2, pos)
  | Max (a1, a2, pos) -> Max (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
  | Min (a1, a2, pos) -> Min (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
	(*| BagEmpty (pos) -> BagEmpty (pos)*)
  | Bag (alist, pos) -> Bag ((e_apply_one_list_exp (fr, t) alist), pos)
  | BagUnion (alist, pos) -> BagUnion ((e_apply_one_list_exp (fr, t) alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((e_apply_one_list_exp (fr, t) alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (e_apply_one_exp (fr, t) a1,
							  e_apply_one_exp (fr, t) a2, pos)
  | List (alist, pos) -> List ((e_apply_one_list_exp (fr, t) alist), pos)
  | ListAppend (alist, pos) -> ListAppend ((e_apply_one_list_exp (fr, t) alist), pos)
  | ListCons (a1, a2, pos) -> ListCons (e_apply_one_exp (fr, t) a1, e_apply_one_exp (fr, t) a2, pos)
  | ListHead (a1, pos) -> ListHead (e_apply_one_exp (fr, t) a1, pos)
  | ListTail (a1, pos) -> ListTail (e_apply_one_exp (fr, t) a1, pos)
  | ListLength (a1, pos) -> ListLength (e_apply_one_exp (fr, t) a1, pos)
  | ListReverse (a1, pos) -> ListReverse (e_apply_one_exp (fr, t) a1, pos)

and e_apply_one_list_exp (fr, t) alist = match alist with
	|[] -> []
	|a :: rest -> (e_apply_one_exp (fr, t) a) :: (e_apply_one_list_exp (fr, t) rest)

(******************************************************************************************************************
	05.06.2008
	Utilities for simplifications:
	- we do some basic simplifications: eliminating identities where the LHS = RHS
******************************************************************************************************************)
and elim_idents (f : formula) : formula = match f with
  | And (f1, f2, pos) -> mkAnd (elim_idents f1) (elim_idents f2) pos
  | Or (f1, f2, lbl, pos) -> mkOr (elim_idents f1) (elim_idents f2) lbl pos
  | Not (f1, lbl, pos) -> mkNot (elim_idents f1) lbl pos
  | Forall (sv, f1, lbl, pos) -> mkForall [sv] (elim_idents f1) lbl pos
  | Exists (sv, f1, lbl, pos) -> mkExists [sv] (elim_idents f1) lbl pos
  | BForm (f1,lbl,extended) -> BForm(elim_idents_b_formula f1, lbl,extended)

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


let combine_branch b (f, l) =
  match b with 
  | "" -> f
  | s -> try And (f, List.assoc b l, no_pos) with Not_found -> f
;;

let merge_branches l1 l2 =
  let branches = Util.remove_dups (fst (List.split l1) @ (fst (List.split l2))) in
  let map_fun branch =
    try 
      let l1 = List.assoc branch l1 in
      try
        let l2 = List.assoc branch l2 in
        (branch, mkAnd l1 l2 no_pos)
      with Not_found -> (branch, l1)
    with Not_found -> (branch, List.assoc branch l2)
  in
  List.map map_fun branches
;;

let or_branches l1 l2 =
  let branches = Util.remove_dups (fst (List.split l1) @ (fst (List.split l2))) in
  let map_fun branch =
    try 
      let l1 = List.assoc branch l1 in
      try
        let l2 = List.assoc branch l2 in
        (branch, mkOr l1 l2 None no_pos)
      with Not_found -> (branch, l1)
    with Not_found -> (branch, List.assoc branch l2)
  in
  List.map map_fun branches
;;

let add_to_branches label form branches =
  try 
    (label, (And (form, List.assoc label branches, no_pos))) :: (List.remove_assoc label branches) 
  with Not_found -> (label, form) :: branches
;;
 
let rec drop_disjunct (f:formula) : formula = 
  match f with
	  | BForm _ -> f
	  | And (f1,f2,l) -> mkAnd (drop_disjunct f1) (drop_disjunct f2) l
	  | Or (_,_,_,l) -> mkTrue l
	  | Not (f,_,_) -> f  (* Not ((drop_disjunct f),l) TODO: investigate if f is the proper return value, in conjunction with case inference*)
	  | Forall (q,f,lbl,l) -> Forall (q,(drop_disjunct f),lbl, l)
	  | Exists (q,f,lbl,l) -> Exists (q,(drop_disjunct f),lbl, l) 
  
and float_out_quantif f = match f with
		| BForm b-> (f,[],[])
		| And (b1,b2,l) -> 
			let l1,l2,l3 = float_out_quantif b1 in
			let q1,q2,q3 = float_out_quantif b2 in
			((mkAnd l1 q1 l), l2@q2, l3@q3)
		| Or (b1,b2,lbl,l) ->
			let l1,l2,l3 = float_out_quantif b1 in
			let q1,q2,q3 = float_out_quantif b2 in
			((mkOr l1 q1 lbl l), l2@q2, l3@q3)
		| Not (b,lbl,l) ->
			let l1,l2,l3 = float_out_quantif b in
			(Not (l1,lbl,l), l2,l3)
		| Forall (q,b,lbl,l)->
			let l1,l2,l3 = float_out_quantif b in
			(l1,q::l2,l3)
		| Exists (q,b,lbl,l)->
			let l1,l2,l3 = float_out_quantif b in
			(l1,l2,q::l3)
			
and check_not (f:formula):formula = 
		let rec inner (f:formula):formula*bool = match f with
			  | BForm b -> (f,false)
			  | And (b1,b2,l) -> 
					let l1,r1 = inner b1 in
					let l2,r2 = inner b2 in
					((mkAnd l1 l2 l),r1&r2)
			  | Or (b1,b2,lbl,l) -> 
					let l1,r1 = inner b1 in
					let l2,r2 = inner b2 in
					((mkOr l1 l2 lbl l),r1&r2)
			  | Not (b,lbl,l) -> begin
								match b with
								| BForm _ -> (f,false)
								| And (b1,b2,l) -> 
									let l1,_ = inner (Not (b1,lbl,l)) in
									let l2,_ = inner (Not (b2,lbl,l)) in
									((mkOr l1 l2 lbl l),true)
								| Or (b1,b2,lbl2,l) ->
									let l1,_ = inner (Not (b1,lbl,l)) in
									let l2,_ = inner (Not (b2,lbl,l)) in
									((mkAnd l1 l2 l),true)
								| Not (b,lbl,l) ->
									let l1,r1 = inner b in
									(l1,true)
								| _ -> (f,false)
							 end
			  | _ ->  (f,false) in
		let f,r = inner f in
		if r then check_not f
			else f 
	
and of_interest (e1:exp) (e2:exp) (interest_vars:spec_var list):bool = 
				let is_simple e = match e with
					  | Null _ 
					  | Var _ 
					  | IConst _ -> true
            | FConst _ -> true
					  | Add (e1,e2,_)
					  | Subtract (e1,e2,_) -> false
					  | Mult _
            | Div _
					  | Max _ 
					  | Min _
					  | Bag _
					  | BagUnion _
					  | BagIntersect _ 
					  | BagDiff _
					  | List _
					  | ListCons _
					  | ListTail _
					  | ListAppend _
					  | ListReverse _
					  | ListHead _
					  | ListLength _ -> false in
	((is_simple e1)&& match e2 with
				  | Var (v1,l)-> List.exists (fun c->eq_spec_var c v1) interest_vars
				  | _ -> false
	)||((is_simple e2)&& match e1 with
				  | Var (v1,l)-> List.exists (fun c->eq_spec_var c v1) interest_vars
				  | _ -> false) 				  
				  
and drop_null (f:formula) self neg:formula = 
	let helper(f:b_formula) neg:b_formula = match f with
	  | Eq (e1,e2,l) -> if neg then f
						else begin match (e1,e2) with
							| (Var(self,_),Null _ )
							| (Null _ ,Var(self,_))-> BConst (true,l)
							| _ -> f end
	  | Neq (e1,e2,l) -> if (not neg) then f
						 else begin match (e1,e2) with
							| (Var(self,_),Null _ )
							| (Null _ ,Var(self,_))-> BConst (true,l)
							| _ -> f end
	  | _ -> f in
	match f with
	  | BForm (b,lbl,extended)-> BForm (helper b neg , lbl, extended)
	  | And (b1,b2,l) -> And ((drop_null b1 self neg),(drop_null b2 self neg),l)
	  | Or _ -> f
	  | Not (b,lbl,l)-> Not ((drop_null b self (not neg)),lbl,l)
	  | Forall (q,f,lbl,l) -> Forall (q,(drop_null f self neg),lbl,l)
	  | Exists (q,f,lbl,l) -> Exists (q,(drop_null f self neg),lbl,l)
	  
and add_null f self extended: formula =  
	mkAnd f (BForm (mkEq (Var (self,no_pos)) (Null no_pos) no_pos , None,extended)) no_pos
	
(*to fully extend*)
(* TODO: double check this func *)

and rel_compute e1 e2:constraint_rel = match (e1,e2) with
	| Null _, Null _ -> Equal
	| Null _, Var (v1,_)  -> if (String.compare (name_of_spec_var v1)"null")=0 then Equal else Unknown
	| Null _, IConst (i,_) -> if i=0 then Equal else Contradicting
	| Var (v1,_), Null _ -> if (String.compare (name_of_spec_var v1)"null")=0 then Equal else Unknown
	| Var (v1,_), Var (v2,_) -> if (String.compare (name_of_spec_var v1)(name_of_spec_var v2))=0 then Equal else Unknown
	| Var _, IConst _ -> Unknown
	| IConst (i,_) , Null _ -> if i=0 then Equal else Contradicting
	| IConst _ ,Var _ -> Unknown
	| IConst (i1,_) ,IConst (i2,_) -> if (i1<i2) then Subsumed else if (i1=i2) then Equal else Subsuming
	| _ -> Unknown
	
	and compute_constraint_relation ((a1,a3,a4):(int* b_formula *(spec_var list)))
								((b1,b3,b4):(int* b_formula *(spec_var list)))
								:constraint_rel= match (a3,b3) with
	| ((BVar v1),(BVar v2))-> if (v1=v2) then Equal else Unknown
	| (Neq (e1,e2,_), Neq (d1,d2,_))
	| (Eq (e1,e2,_), Eq  (d1,d2,_)) -> begin match ((rel_compute e1 d1),(rel_compute e2 d2)) with
										| Equal,Equal-> Equal
										| _ -> match ((rel_compute e1 d2),(rel_compute e2 d1)) with
												| Equal,Equal-> Equal
												| _ ->  Unknown end
	| (Eq  (e1,e2,_), Neq (d1,d2,_)) 
	| (Neq (e1,e2,_), Eq  (d1,d2,_)) ->  begin 
		match ((rel_compute e1 d1),(rel_compute e2 d2)) with
										| Equal,Equal-> Contradicting
										| _ -> match ((rel_compute e1 d2),(rel_compute e2 d1)) with
												| Equal,Equal-> Contradicting
												| _ ->  Unknown end 
	| (Lt (e1,e2,_), Lt  (d1,d2,_)) 		
	| (Lt (e1,e2,_), Lte (d1,d2,_)) 
	| (Lt (e1,e2,_), Eq  (d1,d2,_)) 
	| (Lt (e1,e2,_), Neq (d1,d2,_)) 
	| (Lte (e1,e2,_), Lt  (d1,d2,_)) 
	| (Lte (e1,e2,_), Lte (d1,d2,_)) 
	| (Lte (e1,e2,_), Eq  (d1,d2,_)) 
	| (Lte (e1,e2,_), Neq (d1,d2,_)) 
	| (Eq (e1,e2,_), Lt  (d1,d2,_)) 
	| (Eq (e1,e2,_), Lte (d1,d2,_)) 
	| (Neq (e1,e2,_), Lt  (d1,d2,_)) 
	| (Neq (e1,e2,_), Lte (d1,d2,_)) -> Unknown
	| _ -> Unknown
	
and b_form_list f: b_formula list = match f with
  | BForm (b,_,_) -> [b]
  | And (b1,b2,_)-> (b_form_list b1)@(b_form_list b2)
  | Or _ -> []
  | Not _ -> []
  | Forall (_,f,_,_)
  | Exists (_,f,_,_) -> (b_form_list f)

and redundant_b_f (f:formula) :formula = match f with
  | BForm (_,p,l) -> 
      (match l with 
        | None -> f 
        | Some _ -> (mkTrue no_pos))
  | And (b1,b2,p)-> mkAnd (redundant_b_f b1) (redundant_b_f b2) p
  | Or (p1,p2,p3,p4) -> Or ((redundant_b_f p1),(redundant_b_f p2),p3,p4)
  | Not (f,fl,p) -> Not ((redundant_b_f f),fl,p)
  | Forall (q,f,fl,p) -> Forall (q,(redundant_b_f f),fl,p)
  | Exists (q,f,fl,p) -> Exists (q,(redundant_b_f f),fl,p)
  
  
and simp_mult (e : exp) :  exp =
  let rec normalize_add m lg (x: exp):  exp =
    match x with
    |  Add (e1, e2, l) ->
        let t1 = normalize_add m l e2 in normalize_add (Some t1) l e1
    | _ -> (match m with | None -> x | Some e ->  Add (e, x, lg)) in
  let rec acc_mult m e0 =
    match e0 with
    | Null _ -> e0
    | Var (v, l) ->
        (match m with 
        | None -> e0 
        | Some c ->  Mult (IConst (c, l), e0, l))
    | IConst (v, l) ->
        (match m with 
        | None -> e0 
        | Some c ->  IConst (c * v, l))
    | FConst (v, l) ->
        (match m with
        | None -> e0
        | Some c -> FConst (v *. (float_of_int c), l))
    |  Add (e1, e2, l) ->
        normalize_add None l ( Add (acc_mult m e1, acc_mult m e2, l))
    |  Subtract (e1, e2, l) ->
        normalize_add None l
          ( Add (acc_mult m e1,
             acc_mult
               (match m with | None -> Some (- 1) | Some c -> Some (- c)) e2,
             l))
    | Mult (e1, e2, l) -> Mult (acc_mult m e1, acc_mult None e2, l)
    | Div (e1, e2, l) -> Div (acc_mult m e1, acc_mult None e2, l)
    |  Max (e1, e2, l) ->
        Error.report_error
          {
            Error.error_loc = l;
            Error.error_text =
              "got Max !! (Should have already been simplified )";
          }
    |  Min (e1, e2, l) ->
        Error.report_error
          {
            Error.error_loc = l;
            Error.error_text =
              "got Min !! (Should have already been simplified )";
          }
    |  Bag (el, l) ->  Bag (List.map (acc_mult m) el, l)
    |  BagUnion (el, l) ->  BagUnion (List.map (acc_mult m) el, l)
    |  BagIntersect (el, l) -> BagIntersect (List.map (acc_mult m) el, l)
    |  BagDiff (e1, e2, l) -> BagDiff (acc_mult m e1, acc_mult m e2, l)
    |  List (_, l)
    |  ListAppend (_, l)
	|  ListCons (_, _, l)
	|  ListTail (_, l)
	|  ListReverse (_, l)
	|  ListHead (_, l)
	|  ListLength (_, l) -> 
          match m with | None -> e0 | Some c ->  Mult (IConst (c, l), e0, l)

  in acc_mult None e

and split_sums (e :  exp) : (( exp option) * ( exp option)) =
  match e with
  |  Null _ -> ((Some e), None)
  |  Var _ -> ((Some e), None)
  |  IConst (v, l) ->
      if v > 0 then 
        ((Some e), None)
      else if v < 0 then 
        (None, (Some ( IConst (- v, l))))
      else (None, None)
  | FConst (v, l) ->
      if v > 0.0 then
        ((Some e), None)
      else if v < 0.0 then
        ((None, (Some (FConst (-. v, l)))))
      else (None, None)
  |  Add (e1, e2, l) ->
      let (ts1, tm1) = split_sums e1 in
      let (ts2, tm2) = split_sums e2 in
      let tsr =
        (match (ts1, ts2) with
         | (None, None) -> None
         | (None, Some r1) -> ts2
         | (Some r1, None) -> ts1
         | (Some r1, Some r2) -> Some ( Add (r1, r2, l))) in
      let tmr =
        (match (tm1, tm2) with
         | (None, None) -> None
         | (None, Some r1) -> tm2
         | (Some r1, None) -> tm1
         | (Some r1, Some r2) -> Some ( Add (r1, r2, l)))
      in (tsr, tmr)
  |  Subtract (e1, e2, l) ->
      Error.report_error
        {
          Error.error_loc = l;
          Error.error_text =
            "got subtraction !! (Should have already been simplified )";
        }
  | Mult (e1, e2, l) ->
      let ts1, tm1 = split_sums e1 in
      let ts2, tm2 = split_sums e2 in
      let r =
        match ts1, tm1, ts2, tm2 with
        | None, None, _, _ -> None, None
        | _, _, None, None -> None, None
        | Some r1, None, Some r2, None -> Some (Mult (r1, r2, l)), None
        | Some r1, None, None, Some r2 -> None, Some (Mult (r1, r2, l))
        | None, Some r1, Some r2, None -> None, Some (Mult (r1, r2, l))
        | None, Some r1, None, Some r2 -> Some (Mult (r1, r2, l)), None
        | _ -> ((Some e), None) (* Undecidable cases *)
      in r
  | Div (e1, e2, l) ->
      (* IMHO, this implementation is useless *)
      let ts1, tm1 = split_sums e1 in
      let ts2, tm2 = split_sums e2 in
      let r =
        match ts1, tm1, ts2, tm2 with
        | None, None, _, _ -> None, None
        | _, _, None, None -> failwith "[cpure.ml] split_sums: divide by zero"
        | Some r1, None, Some r2, None -> Some (Div (r1, r2, l)), None
        | Some r1, None, None, Some r2 -> None, Some (Div (r1, r2, l))
        | None, Some r1, Some r2, None -> None, Some (Div (r1, r2, l))
        | None, Some r1, None, Some r2 -> Some (Div (r1, r2, l)), None
        | _ -> Some e, None
      in r
  |  Max (e1, e2, l) ->
      Error.report_error
        {
          Error.error_loc = l;
          Error.error_text =
            "got Max !! (Should have already been simplified )";
        }
  |  Min (e1, e2, l) ->
      Error.report_error
        {
          Error.error_loc = l;
          Error.error_text =
            "got Min !! (Should have already been simplified )";
        }
  |  Bag (e1, l) -> ((Some e), None)
  |  BagUnion (e1, l) -> ((Some e), None)
  |  BagIntersect (e1, l) -> ((Some e), None)
  |  BagDiff (e1, e2, l) -> ((Some e), None)
  |  List (el, l) -> ((Some e), None)
  |  ListAppend (el, l) -> ((Some e), None)
  |  ListCons (e1, e2, l) -> ((Some e), None)
  |  ListHead (e1, l) -> ((Some e), None)
  |  ListTail (e1, l) -> ((Some e), None)
  |  ListLength (e1, l) -> ((Some e), None)
  |  ListReverse (e1, l) -> ((Some e), None)

and move_lr (lhs :  exp option) (lsm :  exp option)
  (rhs :  exp option) (rsm :  exp option) l :
  ( exp *  exp) =
  let nl =
    match (lhs, rsm) with
    | (None, None) ->  IConst (0, l)
    | (Some e, None) -> e
    | (None, Some e) -> e
    | (Some e1, Some e2) ->  Add (e1, e2, l) in
  let nr =
    match (rhs, lsm) with
    | (None, None) ->  IConst (0, l)
    | (Some e, None) -> e
    | (None, Some e) -> e
    | (Some e1, Some e2) ->  Add (e1, e2, l)
  in (nl, nr)
	
	
and purge_mult (e :  exp):  exp = match e with
  |  Null _ -> e
  |  Var _ -> e
  |  IConst _ -> e
  | FConst _ -> e
  |  Add (e1, e2, l) ->  Add((purge_mult e1), (purge_mult e2), l)
  |  Subtract (e1, e2, l) ->  Subtract((purge_mult e1), (purge_mult e2), l)
  | Mult (e1, e2, l) ->
      let t1 = purge_mult e1 in
      let t2 = purge_mult e2 in
      begin
        match t1 with
        | IConst (v1, _) -> 
            if (v1 = 0) then t1 
            else if (v1 = 1) then t2 
            else begin 
              match t2 with
              | IConst (v2, _) -> IConst (v1 * v2, l)
              | FConst (v2, _) -> FConst ((float_of_int v1) *. v2, l)
              | _ -> Mult (t1, t2, l)
            end
        | FConst (v1, _) ->
            if (v1 = 0.0) then t1 
            else begin
              match t2 with
              | IConst (v2, _) -> FConst (v1 *. (float_of_int v2), l)
              | FConst (v2, _) -> FConst (v1 *. v2, l)
              | _ -> Mult (t1, t2, l)
            end
        | _ -> 
            begin
              match t2 with
              | IConst (v2, _) -> 
                  if (v2 = 0) then t2 
                  else if (v2 = 1) then t1 
                  else Mult (t1, t2, l)
              | FConst (v2, _) ->
                  if (v2 = 0.0) then t2 
                  else Mult (t1, t2, l)
              | _ -> Mult (t1, t2, l) 
            end
      end
  | Div (e1, e2, l) ->
      let t1 = purge_mult e1 in
      let t2 = purge_mult e2 in
      begin
        match t1 with
        | IConst (v1, _) ->
            if (v1 = 0) then FConst (0.0, l) 
            else begin
             match t2 with
              | IConst (v2, _) ->
                  if (v2 = 0) then
                    Error.report_error {
                      Error.error_loc = l;
                      Error.error_text = "divided by zero";
                    }
                  else FConst((float_of_int v1) /. (float_of_int v2), l)
              | FConst (v2, _) ->
                  if (v2 = 0.0) then
                    Error.report_error {
                      Error.error_loc = l;
                      Error.error_text = "divided by zero";
                    }
                  else FConst((float_of_int v1) /. v2, l)
              | _ -> Div (t1, t2, l) 
            end
        | FConst (v1, _) ->
            if (v1 = 0.0) then FConst (0.0, l)
            else begin
              match t2 with
              | IConst (v2, _) ->
                  if (v2 = 0) then
                    Error.report_error {
                      Error.error_loc = l;
                      Error.error_text = "divided by zero";
                    }
                  else FConst(v1 /. (float_of_int v2), l)
              | FConst (v2, _) ->
                  if (v2 = 0.0) then
                    Error.report_error {
                      Error.error_loc = l;
                      Error.error_text = "divided by zero";
                    }
                  else FConst(v1 /. v2, l)
              | _ -> Div (t1, t2, l)
            end
        | _ -> 
            begin
              match t2 with
              | IConst (v2, _) ->
                  if (v2 = 0) then
                    Error.report_error {
                      Error.error_loc = l;
                      Error.error_text = "divided by zero";
                    }
                  else Div (t1, t2, l)
              | FConst (v2, _) ->
                  if (v2 = 0.0) then
                    Error.report_error {
                      Error.error_loc = l;
                      Error.error_text = "divided by zero";
                    }
                  else Div (t1, t2, l)
              | _ -> Div (t1, t2, l)
            end
      end
  |  Max (e1, e2, l) ->  Max((purge_mult e1), (purge_mult e2), l)
  |  Min (e1, e2, l) ->  Min((purge_mult e1), (purge_mult e2), l)
  |  Bag (el, l) ->  Bag ((List.map purge_mult el), l)
  |  BagUnion (el, l) ->  BagUnion ((List.map purge_mult el), l)
  |  BagIntersect (el, l) ->  BagIntersect ((List.map purge_mult el), l)
  |  BagDiff (e1, e2, l) ->  BagDiff ((purge_mult e1), (purge_mult e2), l)
  |  List (el, l) -> List ((List.map purge_mult el), l)
  |  ListAppend (el, l) -> ListAppend ((List.map purge_mult el), l)
  |  ListCons (e1, e2, l) -> ListCons (purge_mult e1, purge_mult e2, l)
  |  ListHead (e, l) -> ListHead (purge_mult e, l)
  |  ListTail (e, l) -> ListTail (purge_mult e, l)
  |  ListLength (e, l) -> ListLength (purge_mult e, l)
  |  ListReverse (e, l) -> ListReverse (purge_mult e, l)
	
	
and b_form_simplify (b:b_formula) :b_formula = 
	let do_all e1 e2 l =
	  let t1 = simp_mult e1 in
      let t2 = simp_mult e2 in
      let (lhs, lsm) = split_sums t1 in
      let (rhs, rsm) = split_sums t2 in
      let (lh, rh) = move_lr lhs lsm rhs rsm l in
			let lh = purge_mult lh in
			let rh = purge_mult rh in
			 (lh, rh) in
  match b with
         |  BConst _ -> b
         |  BVar _ -> b
         |  Lt (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						  Lt (lh, rh, l)
         |  Lte (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
              Lte (lh, rh, l)
         |  Gt (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						  Lt (rh, lh, l)
         |  Gte (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						  Lte (rh, lh, l)
         |  Eq (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						  Eq (lh, rh, l)
         |  Neq (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						  Neq (lh, rh, l)
         |  EqMax (e1, e2, e3, l) ->
						 let ne1 = simp_mult e1 in
						 let ne2 = simp_mult e2 in
						 let ne3 = simp_mult e3 in
						 let ne1 = purge_mult ne1 in
						 let ne2 = purge_mult ne2 in
						 let ne3 = purge_mult ne3 in
						 (*if (!Tpdispatcher.tp == Tpdispatcher.Mona) then*)
							  let (s1, m1) = split_sums ne1 in
								let (s2, m2) = split_sums ne2 in
								let (s3, m3) = split_sums ne3 in
								begin
								match (s1, s2, s3, m1, m2, m3) with
									| None, None, None, None, None, None ->  BConst (true, l)
									| Some e11, Some e12, Some e13, None, None, None -> 
										let e11 = purge_mult e11 in
										let e12 = purge_mult e12 in
										let e13 = purge_mult e13 in
										 EqMax (e11, e12, e13, l)
										 
									| None, None, None, Some e11, Some e12, Some e13 -> 
										let e11 = purge_mult e11 in
										let e12 = purge_mult e12 in
										let e13 = purge_mult e13 in
										 EqMin (e11, e12, e13, l)
									| _ -> 
										  EqMax (ne1, ne2, ne3, l)
								end
							(*else 
             		 EqMax (ne1, ne2, ne3, l)*)
         |  EqMin (e1, e2, e3, l) ->
						 let ne1 = simp_mult e1 in
						 let ne2 = simp_mult e2 in
						 let ne3 = simp_mult e3 in
						 let ne1 = purge_mult ne1 in
						 let ne2 = purge_mult ne2 in
						 let ne3 = purge_mult ne3 in
						 (*if (!Tpdispatcher.tp == Tpdispatcher.Mona) then*)
							  let (s1, m1) = split_sums ne1 in
								let (s2, m2) = split_sums ne2 in
								let (s3, m3) = split_sums ne3 in
								begin
								match (s1, s2, s3, m1, m2, m3) with
									| None, None, None, None, None, None ->  BConst (true, l)
									| Some e11, Some e12, Some e13, None, None, None -> 
											let e11 = purge_mult e11 in
											let e12 = purge_mult e12 in
											let e13 = purge_mult e13 in
											 EqMin (e11, e12, e13, l)
									| None, None, None, Some e11, Some e12, Some e13 -> 
											let e11 = purge_mult e11 in
											let e12 = purge_mult e12 in
											let e13 = purge_mult e13 in
											 EqMax (e11, e12, e13, l)
									| _ ->  EqMin (ne1, ne2, ne3, l)
								end
							(*else
             		 EqMin (ne1, ne2, ne3, l)*)
         |  BagIn (v, e1, l) ->  BagIn (v, purge_mult (simp_mult e1), l)
         |  BagNotIn (v, e1, l) ->  BagNotIn (v, purge_mult (simp_mult e1), l)
         |  ListIn (e1, e2, l) -> ListIn (purge_mult (simp_mult e1), purge_mult (simp_mult e2), l)
         |  ListNotIn (e1, e2, l) -> ListNotIn (purge_mult (simp_mult e1), purge_mult (simp_mult e2), l)
         |  ListAllN (e1, e2, l) -> ListAllN (purge_mult (simp_mult e1), purge_mult (simp_mult e2), l)
         |  ListPerm (e1, e2, l) -> ListPerm (purge_mult (simp_mult e1), purge_mult (simp_mult e2), l)
         |  BagSub (e1, e2, l) ->
              BagSub (simp_mult e1, simp_mult e2, l)
         |  BagMin _ -> b
         |  BagMax _ -> b 
  
and arith_simplify (pf : formula) :  formula =   match pf with
  |  BForm (b,lbl,extended) -> BForm (b_form_simplify b,lbl,extended)
  |  And (f1, f2, loc) -> And (arith_simplify f1, arith_simplify f2, loc)
  |  Or (f1, f2, lbl, loc) -> Or (arith_simplify f1, arith_simplify f2, lbl, loc)
  |  Not (f1, lbl, loc) ->  Not (arith_simplify f1, lbl, loc)
  |  Forall (v, f1, lbl, loc) ->  Forall (v, arith_simplify f1, lbl, loc)
  |  Exists (v, f1, lbl, loc) ->  Exists (v, arith_simplify f1, lbl, loc)
	
  
let memo_norm (l:b_formula list): b_formula list = 
  let rec get_head e = match e with 
    | Null _ -> "Null"
    | Var (v,_) -> name_of_spec_var v
    | IConst (i,_)-> string_of_int i
    | FConst (f,_) -> string_of_float f
    | Add (e,_,_) | Subtract (e,_,_) | Mult (e,_,_) | Div (e,_,_)
    | Max (e,_,_) | Min (e,_,_) | BagDiff (e,_,_) | ListCons (e,_,_)| ListHead (e,_) 
    | ListTail (e,_)| ListLength (e,_) | ListReverse (e,_)  -> get_head e
    | Bag (e_l,_) | BagUnion (e_l,_) | BagIntersect (e_l,_) | List (e_l,_) | ListAppend (e_l,_)-> 
      if (List.length e_l)>0 then get_head (List.hd e_l) else "[]" in
  
  let e_cmp e1 e2 =  String.compare (get_head e1) (get_head e2) in
     
  let rec get_lists (e:exp) (disc:int): exp list * exp list = match e with
    | Add (e1,e2,l)-> 
      if (disc<>1) then ([e],[])
      else let (lp1,ln1),(lp2,ln2) = get_lists e1 disc, get_lists e2 disc in
        (lp1@lp2,ln1@ln2) 
    | Subtract (e1,e2,l)->
      if (disc<>1) then ([e],[])
      else let (lp1,ln1),(ln2,lp2) = get_lists e1 disc, get_lists e2 disc in
        (lp1@lp2,ln1@ln2) 
    | Mult (e1,e2,l)-> 
      if (disc<>(-1)) then ([e],[])
      else let (lp1,ln1),(lp2,ln2) = get_lists e1 disc, get_lists e2 disc in
        (lp1@lp2,ln1@ln2)       
    | Div (e1,e2,l)-> 
      if (disc<>(-1)) then ([e],[])
      else let (lp1,ln1),(ln2,lp2) = get_lists e1 disc, get_lists e2 disc in
        (lp1@lp2,ln1@ln2) 
    | Null _ | Var _ | IConst _ | FConst _ | Max _  | Min _ | Bag _ | BagUnion _ | BagIntersect _ 
    | BagDiff _ | List _ | ListCons _ | ListHead _ | ListTail _ | ListLength _ | ListAppend _ | ListReverse _ -> ([e],[]) in
    
  let rec norm_expr e = match e with
    | Null _ | Var _ | IConst _ | FConst _ -> e
    | Add (e1,e2,l) -> cons_lsts e 1 (fun c-> Add c) (fun d-> Subtract d) (IConst (0,l))
    | Subtract (e1,e2,l) -> cons_lsts e 1 (fun c-> Add c) (fun d-> Subtract d) (IConst (0,l))
    | Mult (e1,e2,l) -> cons_lsts e (-1) (fun c-> Mult c) (fun d-> Div d) (IConst (1,l))
    | Div (e1,e2,l) -> cons_lsts e (-1) (fun c-> Mult c) (fun d-> Div d) (IConst (1,l))
    | Max (e1,e2,l)->
      let e1,e2 = norm_expr e1, norm_expr e2 in
      if(e_cmp e1 e2)>0 then Max(e1,e2,l) else Max(e2,e1,l)
    | Min (e1,e2,l) ->
      let e1,e2 = norm_expr e1, norm_expr e2 in
      if(e_cmp e1 e2)>0 then Min(e1,e2,l) else Min(e2,e1,l)
    | Bag (e,l)-> Bag ( List.sort e_cmp (List.map norm_expr e), l)    
    | BagUnion (e,l)-> BagUnion ( List.sort e_cmp (List.map norm_expr e), l)    
    | BagIntersect (e,l)-> BagIntersect ( List.sort e_cmp (List.map norm_expr e), l)    
    | BagDiff (e1,e2,l) -> BagDiff (norm_expr e1, norm_expr e2, l)
    | List (e,l)-> List (List.sort e_cmp (List.map norm_expr e), l)    
    | ListCons (e1,e2,l)-> ListCons(norm_expr e1, norm_expr e2,l)      
    | ListHead (e,l)-> ListHead(norm_expr e, l)      
    | ListTail (e,l)-> ListTail(norm_expr e, l)      
    | ListLength (e,l)-> ListLength(norm_expr e, l)
    | ListAppend (e,l) -> ListAppend ( List.sort e_cmp (List.map norm_expr e), l)    
    | ListReverse (e,l)-> ListReverse(norm_expr e, l)  
    
  and cons_lsts (e:exp) (disc:int) cons1 cons2 (nel:exp) : exp=     
    let lp,ln = get_lists e disc in
    let lp = List.sort e_cmp (List.map norm_expr lp) in
    let ln = List.sort e_cmp (List.map norm_expr ln) in
    if (List.length lp)>0 then
      let a = List.fold_left (fun a c-> cons1(a,c,no_pos)) (List.hd lp) (List.tl lp) in
      List.fold_left(fun a c-> cons2 (a,c,no_pos)) a ln
    else List.fold_left(fun a c-> cons2 (a,c,no_pos)) nel ln in
  Util.push_time "memo_norm";
  let l = List.fold_left (fun a c-> 
    let c = b_form_simplify c in
    match c with
      | Lt  (e1,e2,l) -> Lt  (norm_expr e1,norm_expr e2,l)::a
      | Lte (e1,e2,l) -> Lte (norm_expr e1,norm_expr e2,l)::a
      | Gt  (e1,e2,l) -> Lt  (norm_expr e2,norm_expr e1,l)::a
      | Gte (e1,e2,l) -> Lte (norm_expr e2,norm_expr e1,l)::a
      | Eq  (e1,e2,l) -> 
        let e1,e2 = norm_expr e1,norm_expr e2 in
        if(eqExp e1 e2) then a else Eq(e1,e2,l)::a        
      | Neq (e1,e2,l) ->
        let e1,e2 = norm_expr e1,norm_expr e2 in
        if(eqExp e1 e2) then a else Neq(e1,e2,l)::a    
      | BagIn (v,e,l) -> BagIn (v, norm_expr e, l)::a
      | BagNotIn (v,e,l) -> BagNotIn (v, norm_expr e, l)::a
      | ListIn (e1,e2,l) -> ListIn (norm_expr e1,norm_expr e2,l)::a
      | ListNotIn (e1,e2,l) -> ListIn (norm_expr e1,norm_expr e2,l)::a    
      | BConst _ | BVar _ | EqMax _ 
      | EqMin _ |  BagSub _ | BagMin _ 
      | BagMax _ | ListAllN _ | ListPerm _ -> a) [] l in
    Util.pop_time "memo_norm";l
  
  
  
let rec get_pure_label n =  match n with
	  | And _ -> None
	  | BForm (_,l,_) 
	  | Or (_,_,l,_) 
	  | Not (_,l,_) 
	  | Forall (_,_,l,_) 
	  | Exists (_,_,l,_) -> l

let select zs n = 
	let l = List.length zs in
	(List.nth zs (n mod l))

let rec transform_exp f e  = 
	let r =  f e in 
	match r with
	| Some ne -> ne
	| None -> match e with
	  | Null _ 
	  | Var _ 
	  | IConst _
	  | FConst _ -> e
	  | Add (e1,e2,l) ->
	    let ne1 = transform_exp f e1 in
		let ne2 = transform_exp f e2 in
		Add (ne1,ne2,l)
	  | Subtract (e1,e2,l) ->
	    let ne1 = transform_exp f e1 in
		let ne2 = transform_exp f e2 in
		Subtract (ne1,ne2,l)
	  | Mult (e1,e2,l) ->
	    let ne1 = transform_exp f e1 in
		let ne2 = transform_exp f e2 in
		Mult (ne1,ne2,l)
	  | Div (e1,e2,l) ->
	    let ne1 = transform_exp f e1 in
		let ne2 = transform_exp f e2 in
		Div (ne1,ne2,l)
	  | Max (e1,e2,l) ->
	    let ne1 = transform_exp f e1 in
		let ne2 = transform_exp f e2 in
		Max (ne1,ne2,l)
	  | Min (e1,e2,l) ->
	    let ne1 = transform_exp f e1 in
		let ne2 = transform_exp f e2 in
		Min (ne1,ne2,l)
	  | Bag (le,l) -> 
		Bag (List.map (fun c-> transform_exp f c) le, l) 
	  | BagUnion (le,l) -> 
		BagUnion (List.map (fun c-> transform_exp f c) le, l)
	  | BagIntersect (le,l) -> 
		BagIntersect (List.map (fun c-> transform_exp f c) le, l)
	  | BagDiff (e1,e2,l) ->
	    let ne1 = transform_exp f e1 in
      let ne2 = transform_exp f e2 in
      BagDiff (ne1,ne2,l)
    | List (e1,l) -> List (( List.map (transform_exp f) e1), l) 
    | ListCons (e1,e2,l) -> 
    let ne1 = transform_exp f e1 in
    let ne2 = transform_exp f e2 in
    ListCons (ne1,ne2,l)
    | ListHead (e1,l) -> ListHead ((transform_exp f e1),l)
    | ListTail (e1,l) -> ListTail ((transform_exp f e1),l)
    | ListLength (e1,l) -> ListLength ((transform_exp f e1),l)
    | ListAppend (e1,l) ->  ListAppend (( List.map (transform_exp f) e1), l) 
    | ListReverse (e1,l) -> ListReverse ((transform_exp f e1),l)


	
let transform_b_formula f (e:b_formula) :b_formula = 
	let (f_b_formula, f_exp) = f in
	let r =  f_b_formula e in 
	match r with
	| Some e1 -> e1
	| None  -> match e with	  
	  | BConst _
	  | BVar _ 
	  | BagMin _ 
	  | BagMax _ -> e
	  | Lt (e1,e2,l) ->
		let ne1 = transform_exp f_exp e1 in
		let ne2 = transform_exp f_exp e2 in
		Lt (ne1,ne2,l)
	  | Lte (e1,e2,l) ->
		let ne1 = transform_exp f_exp e1 in
		let ne2 = transform_exp f_exp e2 in
		Lte (ne1,ne2,l)
	  | Gt (e1,e2,l) ->
		let ne1 = transform_exp f_exp e1 in
		let ne2 = transform_exp f_exp e2 in
		Gt (ne1,ne2,l)
	  | Gte (e1,e2,l) ->
		let ne1 = transform_exp f_exp e1 in
		let ne2 = transform_exp f_exp e2 in
		Gte (ne1,ne2,l)
	  | Eq (e1,e2,l) ->
		let ne1 = transform_exp f_exp e1 in
		let ne2 = transform_exp f_exp e2 in
		Eq (ne1,ne2,l)
	  | Neq (e1,e2,l) ->
		let ne1 = transform_exp f_exp e1 in
		let ne2 = transform_exp f_exp e2 in
		Neq (ne1,ne2,l)
	  | EqMax (e1,e2,e3,l) ->
		let ne1 = transform_exp f_exp e1 in
		let ne2 = transform_exp f_exp e2 in
		let ne3 = transform_exp f_exp e3 in
		EqMax (ne1,ne2,ne3,l)	  
	  | EqMin (e1,e2,e3,l) ->
		let ne1 = transform_exp f_exp e1 in
		let ne2 = transform_exp f_exp e2 in
		let ne3 = transform_exp f_exp e3 in
		EqMin (ne1,ne2,ne3,l)
		  (* bag formulas *)
	  | BagIn (v,e,l)->
		let ne1 = transform_exp f_exp e in
		BagIn (v,ne1,l)
	  | BagNotIn (v,e,l)->
		let ne1 = transform_exp f_exp e in
		BagNotIn (v,ne1,l)
	  | BagSub (e1,e2,l) ->
		let ne1 = transform_exp f_exp e1 in
		let ne2 = transform_exp f_exp e2 in
		BagSub (ne1,ne2,l)
    | ListIn (e1,e2,l) ->
	    let ne1 = transform_exp f_exp e1 in
      let ne2 = transform_exp f_exp e2 in
      ListIn (ne1,ne2,l)
    | ListNotIn (e1,e2,l) ->
	    let ne1 = transform_exp f_exp e1 in
      let ne2 = transform_exp f_exp e2 in
      ListNotIn (ne1,ne2,l)
    | ListAllN (e1,e2,l) ->
	    let ne1 = transform_exp f_exp e1 in
      let ne2 = transform_exp f_exp e2 in
      ListAllN (ne1,ne2,l)
    | ListPerm (e1,e2,l) ->
	    let ne1 = transform_exp f_exp e1 in
      let ne2 = transform_exp f_exp e2 in
      ListPerm (ne1,ne2,l)
	  
	  
	  
let rec transform_formula f (e:formula) :formula = 
	let (f_formula, f_b_formula, f_exp) = f in
	let r =  f_formula e in 
	match r with
	| Some e1 -> e1
	| None  -> match e with
		  | BForm (b1,b2,b3) -> 
				BForm ((transform_b_formula (f_b_formula, f_exp) b1) ,b2,b3)
		  | And (e1,e2,l) -> 
			let ne1 = transform_formula f e1 in
			let ne2 = transform_formula f e2 in
			And (ne1,ne2,l)		  
		  | Or (e1,e2,fl, l) -> 
			let ne1 = transform_formula f e1 in
			let ne2 = transform_formula f e2 in
			Or (ne1,ne2,fl,l)		  
		  | Not (e,fl,l) ->
			let ne1 = transform_formula f e in
			Not (ne1,fl,l)
		  | Forall (v,e,fl,l) ->
		    let ne = transform_formula f e in
		    Forall(v,ne,fl,l)
		  | Exists (v,e,fl,l) ->
		    let ne = transform_formula f e in
		    Exists(v,ne,fl,l)
			
			
let rename_labels  e=
	let f_b e = Some e in
	let f_e e = Some e in
	let f_f e = 
	let n_l_f n_l = match n_l with
				| None -> (fresh_branch_point_id "")
				| Some (_,s) -> (fresh_branch_point_id s) in	
		match e with
		| BForm (b,f_l,e) -> Some (BForm (b,(n_l_f f_l),e))
		| And (e1,e2,l) -> None
		| Or (e1,e2,f_l,l) -> (Some (Or (e1,e2,(n_l_f f_l),l)))
		| Not (e1,f_l, l) -> (Some (Not (e1,(n_l_f f_l),l)))
		| Forall (v,e1,f_l, l) -> (Some (Forall (v,e1,(n_l_f f_l),l)))
		| Exists (v,e1,f_l, l) -> (Some (Exists (v,e1,(n_l_f f_l),l)))in
			
	transform_formula (f_f,f_b,f_e) e
			

let types_of_vars f = 
  let var_det v = ((name_of_spec_var v),(type_of_spec_var v)) in
  let rec typ_exp e = match e with
    | Null _ 
    | IConst _
    | FConst _ -> []
    | Var (v,_) -> [(var_det v)]    
    | Add (e1,e2,_) 
    | Subtract (e1,e2,_) 
    | Mult (e1,e2,_) 
    | Div (e1,e2,_) 
    | Max (e1,e2,_) 
    | Min (e1,e2,_) 
    | BagDiff (e1,e2,_)
    | ListCons (e1,e2,_) -> (typ_exp e1)@(typ_exp e2)
    | Bag (el,l)
    | BagUnion (el,l)
    | BagIntersect (el,l)
    | List (el,l)
    | ListAppend (el,l) -> List.concat (List.map typ_exp el)  
    | ListHead (e,l)
    | ListTail (e,l)
    | ListLength (e,l)    
    | ListReverse (e,l) -> (typ_exp e) in
  let typ_b_f f = match f with
      | BConst _ -> []
      | BVar (v,_) -> [(var_det v)]
      | Lt (e1,e2,_)
      | Lte (e1,e2,_)
      | Gt (e1,e2,_)
      | Gte (e1,e2,_)
      | Eq (e1,e2,_)
      | Neq (e1,e2,_) 
      | BagSub (e1,e2,_) 
      | ListIn (e1,e2,_)
      | ListNotIn (e1,e2,_)
      | ListAllN (e1,e2,_)
      | ListPerm (e1,e2,_) -> (typ_exp e1)@(typ_exp e2)
      | EqMax (e1,e2,e3,_)
      | EqMin (e1,e2,e3,_) ->(typ_exp e1)@(typ_exp e2)@(typ_exp e3)
      | BagIn (v,e,_) 
      | BagNotIn (v,e,_) -> (var_det v)::(typ_exp e)      
      | BagMin (v1,v2,_)
      | BagMax (v1,v2,_) -> (var_det v1)::[(var_det v2)] in
  let rec helper1 f = match f with
		| BForm (b, _, _) -> typ_b_f b
		| And (e1,e2, _) 
		| Or (e1,e2, _, _) -> (helper1 e1)@(helper1 e2)
		| Not (e1, _, _ ) -> (helper1 e1)
		| Forall (v,e1, _, _) -> (var_det v)::(helper1 e1)
		| Exists (v,e1, _, _) -> (var_det v)::(helper1 e1) in
  Util.remove_dups (helper1 f)