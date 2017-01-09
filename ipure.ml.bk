(*
  Created 19-Feb-2006

  Input pure constraints, including arithmetic and pure pointer
*)

open Globals

type formula = 
  | BForm of (b_formula*(formula_label option))
  | And of (formula * formula * loc)
  | Or of (formula * formula *(formula_label option) * loc)
  | Not of (formula *(formula_label option)* loc)
  | Forall of ((ident * primed) * formula *(formula_label option)* loc)
  | Exists of ((ident * primed) * formula *(formula_label option)* loc)

(* Boolean constraints *)
and b_formula = 
  | BConst of (bool * loc)
  | BVar of ((ident * primed) * loc)
  | Lt of (exp * exp * loc)
  | Lte of (exp * exp * loc)
  | Gt of (exp * exp * loc)
  | Gte of (exp * exp * loc)
  | Eq of (exp * exp * loc) (* these two could be arithmetic or pointer or bags or lists *)
  | Neq of (exp * exp * loc)
  | EqMax of (exp * exp * exp * loc) (* first is max of second and third *)
  | EqMin of (exp * exp * exp * loc) (* first is min of second and third *)
	  (* bags and bag formulae *)
  | BagIn of ((ident * primed) * exp * loc)
  | BagNotIn of ((ident * primed) * exp * loc)
  | BagSub of (exp * exp * loc)
  | BagMin of ((ident * primed) * (ident * primed) * loc)
  | BagMax of ((ident * primed) * (ident * primed) * loc)	
	  (* lists and list formulae *)
  | ListIn of (exp * exp * loc)
  | ListNotIn of (exp * exp * loc)
  | ListAllN of (exp * exp * loc)
  | ListPerm of (exp * exp * loc)
  | RelForm of (ident * (exp list) * loc)           (* An Hoa: Relational formula to capture relations, for instance, s(a,b,c) or t(x+1,y+2,z+3), etc. *)

(* Expression *)
and exp = 
  | Null of loc
  | Var of ((ident * primed) * loc) 
	  (* variables could be of type pointer, int, bags, lists etc *)
  | IConst of (int * loc)
  | FConst of (float * loc)
  (*| Tuple of (exp list * loc)*)
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
  | ArrayAt of ((ident * primed) * exp  * loc)      (* An Hoa : array access *)


and relation = (* for obtaining back results from Omega Calculator. Will see if it should be here*)
  | ConstRel of bool
  |	BaseRel of (exp list * formula)
  | UnionRel of (relation * relation)

(* free variables *)

let rec fv (f : formula) : (ident * primed) list = match f with 
  | BForm (b,_) -> bfv b
  | And (p1, p2, _) -> combine_pvars p1 p2
  | Or (p1, p2, _,_) -> combine_pvars p1 p2
  | Not (nf, _,_) -> fv nf
  | Forall (qid, qf, _,_) -> remove_qvar qid qf
  | Exists (qid, qf, _,_) -> remove_qvar qid qf

and combine_pvars p1 p2 = 
  let fv1 = fv p1 in
  let fv2 = fv p2 in
    Gen.BList.remove_dups_eq (=) (fv1 @ fv2)
	
and remove_qvar qid qf =
  let qfv = fv qf in
    Gen.BList.remove_elem_eq (=) qid qfv

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
		Gen.BList.remove_dups_eq (=) (fv1 @ fv2 @ fv3)
  | EqMin (a1, a2, a3, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
	  let fv3 = afv a3 in
		Gen.BList.remove_dups_eq (=) (fv1 @ fv2 @ fv3)
  | BagIn (v, a, _) -> 
		let fv = afv a in
		Gen.BList.remove_dups_eq (=) ([v] @ fv)
  | BagNotIn (v, a, _) -> 
		let fv = afv a in
		Gen.BList.remove_dups_eq (=) ([v] @ fv)	
  | BagSub (a1, a2, _) -> combine_avars a1 a2
  | BagMax (sv1, sv2, _) -> Gen.BList.remove_dups_eq (=) ([sv1] @ [sv2])
  | BagMin (sv1, sv2, _) -> Gen.BList.remove_dups_eq (=) ([sv1] @ [sv2])
  | ListIn (a1, a2, _) -> 
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		Gen.BList.remove_dups_eq (=) (fv1 @ fv2)
  | ListNotIn (a1, a2, _) -> 
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		Gen.BList.remove_dups_eq (=) (fv1 @ fv2)
  | ListAllN (a1, a2, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		Gen.BList.remove_dups_eq (=) (fv1 @ fv2)
  | ListPerm (a1, a2, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		Gen.BList.remove_dups_eq (=) (fv1 @ fv2)
  | RelForm (_,args,_) -> (* An Hoa *)
		let args_fv = List.concat (List.map afv args) in
		Gen.BList.remove_dups_eq (=) args_fv
 
and combine_avars (a1 : exp) (a2 : exp) : (ident * primed) list = 
  let fv1 = afv a1 in
  let fv2 = afv a2 in
    Gen.BList.remove_dups_eq (=) (fv1 @ fv2)

and afv (af : exp) : (ident * primed) list = match af with
  | Null _ -> []
  | Var (sv, _) -> [sv]
  | IConst _ -> []
  | FConst _ -> []
  | Add (a1, a2, _) -> combine_avars a1 a2
  | Subtract (a1, a2, _) -> combine_avars a1 a2
  | Mult (a1, a2, _) | Div (a1, a2, _) -> combine_avars a1 a2
  | Max (a1, a2, _) -> combine_avars a1 a2
  | Min (a1, a2, _) -> combine_avars a1 a2
  | BagDiff (a1,a2,_) ->  combine_avars a1 a2
  | Bag(d,_)
  | BagIntersect (d,_)
  | BagUnion (d,_) ->  Gen.BList.remove_dups_eq (=) (List.fold_left (fun a c-> a@(afv c)) [] d)
  (*| BagDiff _|BagIntersect _|BagUnion _|Bag _ -> failwith ("afv: bag constraints are not expected")*)
  | List (d, _)
  | ListAppend (d, _) -> Gen.BList.remove_dups_eq (=) (List.fold_left (fun a c -> a@(afv c)) [] d)
  | ListCons (a1, a2, _) ->
	  let fv1 = afv a1 in
	  let fv2 = afv a2 in
		Gen.BList.remove_dups_eq (=) (fv1 @ fv2)  
  | ListHead (a, _)
  | ListTail (a, _)
  | ListLength (a, _)
  | ListReverse (a, _) -> afv a
  | ArrayAt (a, i, _) -> Gen.BList.remove_dups_eq (=) (a :: (afv i)) (* An Hoa *)

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
  | Bag _
  | BagUnion _
  | BagIntersect _
  | BagDiff _ -> true
  | _ -> false
  
and is_integer e =
  match e with
  | IConst _ -> true
  | Add (e1, e2, _) | Subtract (e1, e2, _) | Mult (e1, e2, _)
  | Max (e1, e2, _) | Min (e1, e2, _) ->
      is_integer e1 && is_integer e2
  | _ -> false

and is_list (e : exp) : bool = match e with
  | List _
  | ListCons _
  | ListTail _
  | ListAppend _
  | ListReverse _ -> true
  | _ -> false

and name_of_var (e : exp) : ident = match e with
  | Var ((v, p), pos) -> v
  | _ -> failwith ("parameter to name_of_var is not a variable")
 
and isConstTrue p = match p with
  | BForm (BConst (true, pos),_) -> true
  | _ -> false

and isConstFalse p = match p with
  | BForm (BConst (false, pos),_) -> true
  | _ -> false

(* smart constructor *)

and mkAdd a1 a2 pos = Add (a1, a2, pos)

and mkSubtract a1 a2 pos = Subtract (a1, a2, pos)

and mkMult a1 a2 pos = Mult (a1, a2, pos)

and mkDiv a1 a2 pos = Div (a1, a2, pos)

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
  | BForm (BConst (false, _),_) -> f1
  | BForm (BConst (true, _),_) -> f2
  | _ -> match f2 with
      | BForm (BConst (false, _),_) -> f2
      | BForm (BConst (true, _),_) -> f1
      | _ -> And (f1, f2, pos)

and mkOr f1 f2 lbl pos = match f1 with
  | BForm (BConst (false, _),_) -> f2
  | BForm (BConst (true, _),_) -> f1
  | _ -> match f2 with
      | BForm (BConst (false, _),_) -> f1
      | BForm (BConst (true, _),_) -> f2
      | _ -> Or (f1, f2, lbl, pos)

and mkEqExp (ae1 : exp) (ae2 : exp) pos = match (ae1, ae2) with
  | (Var v1, Var v2) ->
	  if v1 = v2 then
		mkTrue pos
	  else
		BForm (Eq (ae1, ae2, pos), None)
  | _ ->  BForm (Eq (ae1, ae2, pos), None)

and mkNeqExp (ae1 : exp) (ae2 : exp) pos = match (ae1, ae2) with
  | (Var v1, Var v2) ->
	  if v1 = v2 then
		mkFalse pos
	  else
		BForm (Neq (ae1, ae2, pos), None)
  | _ ->  BForm (Neq (ae1, ae2, pos), None)

and mkNot f lbl pos = Not (f, lbl, pos)

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

and mkTrue pos = BForm (BConst (true, pos), None)

and mkFalse pos = BForm (BConst (false, pos),None )

and mkExists (vs : (ident * primed) list) (f : formula) lbl pos = match vs with
  | [] -> f
  | v :: rest -> 
      let ef = mkExists rest f lbl pos in
		if List.mem v (fv ef) then
		  Exists (v, ef,lbl,  pos)
		else
		  ef

and mkForall (vs : (ident * primed) list) (f : formula) lbl pos = match vs with
  | [] -> f
  | v :: rest -> 
      let ef = mkForall rest f lbl pos in
		if List.mem v (fv ef) then
		  Forall (v, ef, lbl, pos)
		else
		  ef

(* build relation from list of expressions, for example a,b,c < d,e, f *)
and build_relation relop alist10 alist20 pos = 
  let rec helper1 ae alist = 
	let a = List.hd alist in
	let rest = List.tl alist in
	let tmp = BForm ((relop ae a pos),None) in
	  if Gen.is_empty rest then
		tmp
	  else
		let tmp1 = helper1 ae rest in
		let tmp2 = mkAnd tmp tmp1 pos in
		  tmp2 in
  let rec helper2 alist1 alist2 =
	let a = List.hd alist1 in
	let rest = List.tl alist1 in
	let tmp = helper1 a alist2 in
	  if Gen.is_empty rest then
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

 (* An Hoa *)
and pos_of_formula (f : formula) = match f with 
	| BForm (b,_) -> begin match b with
		  | BConst (_,p) | BVar (_,p)
		  | Lt (_,_,p) | Lte (_,_,p) | Gt (_,_,p) | Gte (_,_,p) | Eq (_,_,p) | Neq (_,_,p)
		  | EqMax (_,_,_,p) | EqMin (_,_,_,p) 
			| BagIn (_,_,p) | BagNotIn (_,_,p) | BagSub (_,_,p) | BagMin (_,_,p) | BagMax (_,_,p)	
		  | ListIn (_,_,p) | ListNotIn (_,_,p) | ListAllN (_,_,p) | ListPerm (_,_,p)
		  | RelForm (_,_,p) -> p
	end
  | And (_,_,p) | Or (_,_,_,p) | Not (_,_,p)
  | Forall (_,_,_,p) -> p | Exists (_,_,_,p) -> p

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
  | ArrayAt (_ ,_ , p) -> p (* An Hoa *)
  
	
	
and fresh_old_name (s: string):string = 
	let ri = try  (String.rindex s '_') with  _ -> (String.length s) in
	let n = ((String.sub s 0 ri) ^ (fresh_trailer ())) in
	n
	

and fresh_var (sv : (ident*primed)):(ident*primed) =
	let old_name = fst sv in
  let name = fresh_old_name old_name in
	(name, Unprimed) (* fresh names are unprimed *)

and fresh_vars (svs : (ident*primed) list):(ident*primed) list = List.map fresh_var svs


and eq_var (f: (ident*primed))(t:(ident*primed)):bool = ((String.compare (fst f) (fst t))==0) &&(snd f)==(snd t) 

and subst sst (f : formula) = match sst with
  | s :: rest -> subst rest (apply_one s f)
  | [] -> f 

and apply_one (fr, t) f = match f with
  | BForm (bf,lbl) -> BForm (b_apply_one (fr, t) bf, lbl)
  | And (p1, p2, pos) -> And (apply_one (fr, t) p1,
							  apply_one (fr, t) p2, pos)
  | Or (p1, p2, lbl, pos) -> Or (apply_one (fr, t) p1,
							apply_one (fr, t) p2, lbl, pos)
  | Not (p, lbl, pos) -> Not (apply_one (fr, t) p, lbl, pos)
  | Forall (v, qf, lbl, pos) ->
	  if eq_var v fr then f
      else if eq_var v t then
        let fresh_v = fresh_var v in
        Forall (fresh_v, apply_one (fr, t) (apply_one (v, fresh_v) qf), lbl, pos)
	  else Forall (v, apply_one (fr, t) qf, lbl, pos)
  | Exists (v, qf, lbl, pos) ->
	  if eq_var v fr then f
      else if eq_var v t then
        let fresh_v = fresh_var v in
        Exists (fresh_v, apply_one (fr, t) (apply_one (v, fresh_v) qf), lbl, pos)
	  else Exists (v, apply_one (fr, t) qf, lbl, pos)
  
and b_apply_one (fr, t) bf = match bf with
  | BConst _ -> bf
  | BVar (bv, pos) -> BVar ((if eq_var bv fr then t else bv), pos)
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
  | BagIn (v, a1, pos) -> BagIn ((if eq_var v fr then t else v), e_apply_one (fr, t) a1, pos)
  | BagNotIn (v, a1, pos) -> BagNotIn ((if eq_var v fr then t else v), e_apply_one (fr, t) a1, pos)
	(* is it ok?... can i have a set of boolean values?... don't think so... *)
  | BagSub (a1, a2, pos) -> BagSub (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | BagMax (v1, v2, pos) -> BagMax ((if eq_var v1 fr then t else v1), (if eq_var v2 fr then t else v2), pos)
  | BagMin (v1, v2, pos) -> BagMin ((if eq_var v1 fr then t else v1), (if eq_var v2 fr then t else v2), pos)
  | ListIn (a1, a2, pos) -> ListIn (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | ListNotIn (a1, a2, pos) -> ListNotIn (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | ListAllN (a1, a2, pos) -> ListAllN (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | ListPerm (a1, a2, pos) -> ListPerm (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | RelForm (r, args, pos) -> 
          (* An Hoa : apply to every arguments, alternatively, use e_apply_one_list *)
          RelForm (r, (List.map (fun x -> e_apply_one (fr, t) x) args), pos) 

and e_apply_one (fr, t) e = match e with
  | Null _ | IConst _ -> e
  | FConst _ -> e
  | Var (sv, pos) -> Var ((if eq_var sv fr then t else sv), pos)
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
  | Bag (alist, pos) -> Bag ((e_apply_one_list (fr, t) alist), pos)
  | BagUnion (alist, pos) -> BagUnion ((e_apply_one_list (fr, t) alist), pos)
  | BagIntersect (alist, pos) -> BagIntersect ((e_apply_one_list (fr, t) alist), pos)
  | BagDiff (a1, a2, pos) -> BagDiff (e_apply_one (fr, t) a1,
							  e_apply_one (fr, t) a2, pos)
  | List (alist, pos) -> List ((e_apply_one_list (fr, t) alist), pos)
  | ListAppend (alist, pos) -> ListAppend ((e_apply_one_list (fr, t) alist), pos)
  | ListCons (a1, a2, pos) -> ListCons (e_apply_one (fr, t) a1, e_apply_one (fr, t) a2, pos)
  | ListHead (a1, pos) -> ListHead (e_apply_one (fr, t) a1, pos)
  | ListTail (a1, pos) -> ListTail (e_apply_one (fr, t) a1, pos)
  | ListLength (a1, pos) -> ListLength (e_apply_one (fr, t) a1, pos)
  | ListReverse (a1, pos) -> ListReverse (e_apply_one (fr, t) a1, pos)
  | ArrayAt (a, ind, pos) -> ArrayAt (a, (e_apply_one (fr, t) ind), pos) (* An Hoa *)

and e_apply_one_list (fr, t) alist = match alist with
  |[] -> []
  |a :: rest -> (e_apply_one (fr, t) a) :: (e_apply_one_list (fr, t) rest)

(* apply_one function for the formula_ext_measures of ext_variance_formula *)
and e_apply_one_list_of_pair (fr, t) list_of_pair = match list_of_pair with
  | [] -> []
  | (expr, bound)::rest -> match bound with
							| None -> ((e_apply_one (fr, t) expr), None)::(e_apply_one_list_of_pair (fr, t) rest)
							| Some b_expr ->  ((e_apply_one (fr, t) expr), Some (e_apply_one (fr, t) b_expr))::(e_apply_one_list_of_pair (fr, t) rest)

and subst_list_of_pair sst ls = match sst with
  | [] -> ls
  | s::rest -> subst_list_of_pair rest (e_apply_one_list_of_pair s ls)
			 						

and look_for_anonymous_exp_list (args : exp list) :
  (ident * primed) list =
  match args with
  | h :: rest ->
      List.append (look_for_anonymous_exp h)
        (look_for_anonymous_exp_list rest)
  | _ -> []

and anon_var (id, p) = 
      if ((String.length id) > 5) &&
          ((String.compare (String.sub id 0 5) "Anon_") == 0)
      then [ (id, p) ]
      else []

and look_for_anonymous_exp (arg : exp) : (ident * primed) list = match arg with
  | Var (b1, _) -> anon_var b1
  | Add (e1, e2, _) | Subtract (e1, e2, _) | Max (e1, e2, _) |
      Min (e1, e2, _) | BagDiff (e1, e2, _) ->
      List.append (look_for_anonymous_exp e1) (look_for_anonymous_exp e2)

  | Mult (e1, e2, _) | Div (e1, e2, _) ->
      List.append (look_for_anonymous_exp e1) (look_for_anonymous_exp e2)
  | Bag (e1, _) | BagUnion (e1, _) | BagIntersect (e1, _) ->  look_for_anonymous_exp_list e1

  | ListHead (e1, _) | ListTail (e1, _) | ListLength (e1, _) | ListReverse (e1, _) -> look_for_anonymous_exp e1
  | List (e1, _) | ListAppend (e1, _) -> look_for_anonymous_exp_list e1
  | ListCons (e1, e2, _) -> (look_for_anonymous_exp e1) @ (look_for_anonymous_exp e2)
  | _ -> []

and look_for_anonymous_pure_formula (f : formula) : (ident * primed) list = match f with
  | BForm (b,_) -> look_for_anonymous_b_formula b
  | And (b1,b2,_) -> (look_for_anonymous_pure_formula b1)@ (look_for_anonymous_pure_formula b1)
  | Or  (b1,b2,_,_) -> (look_for_anonymous_pure_formula b1)@ (look_for_anonymous_pure_formula b1)
  | Not (b1,_,_) -> (look_for_anonymous_pure_formula b1)
  | Forall (_,b1,_,_)-> (look_for_anonymous_pure_formula b1)
  | Exists (_,b1,_,_)-> (look_for_anonymous_pure_formula b1)

	
and look_for_anonymous_b_formula (f : b_formula) : (ident * primed) list = match f with
  | BConst _ -> []
  | BVar (b1, _) -> anon_var b1
  | Lt (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | Lte (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | Gt (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | Gte (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | Eq (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | Neq (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | EqMax (b1, b2, b3, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2) @ (look_for_anonymous_exp b3)
  | EqMin(b1, b2, b3, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2) @ (look_for_anonymous_exp b3)
  | BagIn (b1, b2, _) -> (anon_var b1) @ (look_for_anonymous_exp b2)
  | BagNotIn (b1, b2, _) -> (anon_var b1) @ (look_for_anonymous_exp b2)
  | BagSub (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | BagMin (b1, b2, _) -> (anon_var b1) @ (anon_var b2)
  | BagMax (b1, b2, _) -> (anon_var b1) @ (anon_var b2)	
  | ListIn (b1, b2,  _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | ListNotIn (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | ListAllN (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | ListPerm (b1, b2, _) -> (look_for_anonymous_exp b1) @ (look_for_anonymous_exp b2)
  | RelForm _ -> [] (* An Hoa : TODO implement *)
  
let merge_branches l1 l2 =
  let branches = Gen.BList.remove_dups_eq (=) (fst (List.split l1) @ (fst (List.split l2))) in
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
