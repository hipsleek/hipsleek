(*
  Created 19-Feb-2006

  core pure constraints, including arithmetic and pure pointer
*)

open Globals
open Gen.Basic

module Ts = Tree_shares.Ts

(* spec var *)
type spec_var =
  | SpecVar of (typ * ident * primed)
  
type formula =
  | BForm of (b_formula *(formula_label option))
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
  | RelForm of (ident * (exp list) * loc)            (* An Hoa: Relational formula to capture relations, for instance, s(a,b,c) or t(x+1,y+2,z+3), etc. *)

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
  | ArrayAt of (spec_var * exp * loc)      (* An Hoa : array access *)

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


let rec contains_exists (f:formula) : bool =  match f with
    | BForm _ -> false
    | Or (f1,f2,_,_)  
    | And (f1,f2, _) -> (contains_exists f1) || (contains_exists f2) 
    | Not(f1,_,_)
    | Forall (_ ,f1,_,_) -> (contains_exists f1)  
    | Exists _ -> true

let eq_spec_var (sv1 : spec_var) (sv2 : spec_var) = match (sv1, sv2) with
  | (SpecVar (t1, v1, p1), SpecVar (t2, v2, p2)) ->
	    (* translation has ensured well-typedness.
		   We need only to compare names and primedness *)
	    v1 = v2 & p1 = p2

let cmp_spec_var (sv1 : spec_var) (sv2 : spec_var) = match (sv1, sv2) with
  | (SpecVar (t1, v1, p1), SpecVar (t2, v2, p2)) ->
	    let r = String.compare v1 v2 in
		if r = 0 then match p1,p2 with
		  | Unprimed, Unprimed
		  | Primed, Primed -> 0
		  | Unprimed, _ -> -1
		  | _ -> 1
		else r 
		
let remove_dups_svl vl = Gen.BList.remove_dups_eq eq_spec_var vl

     
(* TODO: determine correct type of an exp *)
let rec get_exp_type (e : exp) : typ = match e with
  | Null _ -> Named ""
  | Var (SpecVar (t, _, _), _) -> t
  | IConst _ -> Int
  | FConst _ -> Float
  | Add (e1, e2, _) | Subtract (e1, e2, _) | Mult (e1, e2, _)
  | Max (e1, e2, _) | Min (e1, e2, _) ->
      begin
        match get_exp_type e1, get_exp_type e2 with
        | Int, Int -> Int
        | _ -> Float
      end
  | Div _ -> Float
  | ListHead _ | ListLength _ -> Int
  | Bag _ | BagUnion _ | BagIntersect _ | BagDiff _ ->  ((Globals.BagT Globals.Int))  (* Globals.Bag *)
  | List _ | ListCons _ | ListTail _ | ListAppend _ | ListReverse _ -> Globals.List Globals.Int
  | ArrayAt (SpecVar (t, a, _), _, _) ->
          (* Type of a[i] is the type of the element of array a *)
          match t with
          | Array (et,_) -> et
          | _ -> let _ = failwith "Cpure.get_exp_type : " ^ a ^ " is not an array variable" in Named "" 

(* *GLOBAL_VAR* substitutions list, used by omega.ml and ocparser.mly
 * moved here from ocparser.mly *)
let omega_subst_lst = ref ([]: (string*string*typ) list)

(* type constants *)
let print_b_formula = ref (fun (c:b_formula) -> "cpure printer has not been initialized")
let print_exp = ref (fun (c:exp) -> "cpure printer has not been initialized")
let print_formula = ref (fun (c:formula) -> "cpure printer has not been initialized")
let print_svl = ref (fun (c:spec_var list) -> "cpure printer has not been initialized")

let bool_type = Bool

let int_type = Int

let float_type = Float

let void_type = Void

(* free variables *)

let null_var = SpecVar (Named "", "null", Unprimed)

let flow_var = SpecVar ((Int), flow , Unprimed)

let full_name_of_spec_var (sv : spec_var) : ident = 
  match sv with
    | SpecVar (_, v, p) -> if (p==Primed) then (v^"\'") else v

let is_void_type t = match t with | Void -> true | _ -> false

let rec fv (f : formula) : spec_var list =
  let tmp = fv_helper f in

  let res = Gen.BList.remove_dups_eq eq_spec_var tmp in
  res
and check_dups_svl ls = 
  let b=(Gen.BList.check_dups_eq eq_spec_var ls) in
  (if b then print_string ("!!!!ERROR==>duplicated vars:>>"^(!print_svl ls)^"!!")); b 
and fv_helper (f : formula) : spec_var list = match f with
  | BForm (b,_) -> bfv b
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
  Gen.BList.difference_eq eq_spec_var qfv [qid]

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
        remove_dups_svl (fv1 @ fv2 @ fv3)
  | EqMin (a1, a2, a3, _) ->
        let fv1 = afv a1 in
        let fv2 = afv a2 in
        let fv3 = afv a3 in
        remove_dups_svl (fv1 @ fv2 @ fv3)
  | BagIn (v, a1, _) ->
        let fv1 = afv a1 in
        [v] @ fv1
  | BagNotIn (v, a1, _) ->
        let fv1 = afv a1 in
        [v] @ fv1
  | BagSub (a1, a2, _) -> combine_avars a1 a2
  | BagMax (v1, v2, _) ->remove_dups_svl ([v1] @ [v2])
  | BagMin (v1, v2, _) ->remove_dups_svl ([v1] @ [v2])
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
  | RelForm (r, args, _) ->
		remove_dups_svl (List.fold_left List.append [] (List.map afv args))
		    (* An Hoa *)

and combine_avars (a1 : exp) (a2 : exp) : spec_var list =
  let fv1 = afv a1 in
  let fv2 = afv a2 in
  remove_dups_svl (fv1 @ fv2)

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
  	remove_dups_svl svlist
  | BagUnion (alist, _) -> let svlist = afv_list alist in
  	remove_dups_svl svlist
  | BagIntersect (alist, _) -> let svlist = afv_list alist in
  	remove_dups_svl svlist
  | BagDiff(a1, a2, _) -> combine_avars a1 a2
  | List (alist, _) -> let svlist = afv_list alist in
  	remove_dups_svl svlist
  | ListAppend (alist, _) -> let svlist = afv_list alist in
  	remove_dups_svl svlist
  | ListCons (a1, a2, _) ->
        let fv1 = afv a1 in
        let fv2 = afv a2 in
        remove_dups_svl (fv1 @ fv2)  
  | ListHead (a, _)
  | ListTail (a, _)
  | ListLength (a, _)
  | ListReverse (a, _) -> afv a
  | ArrayAt (a, i, _) -> remove_dups_svl (a :: afv i) (* An Hoa *)

and afv_list (alist : exp list) : spec_var list = match alist with
  |[] -> []
  |a :: rest -> afv a @ afv_list rest

and is_max_min a = match a with
  | Max _ | Min _ -> true
  | _ -> false

and string_of_relation (e:relation) : string =
  match e with
    | ConstRel b -> if b then "True" else "False"
    | BaseRel (el,f) -> pr_pair (pr_list !print_exp) !print_formula (el,f)
    | UnionRel (r1,r2) -> (string_of_relation r1)^"\n"^(string_of_relation r2)^"\n"

and isConstTrue_debug (p:formula) =
  Gen.Debug.no_1 "isConsTrue" !print_formula string_of_bool isConstTrue p


and isConstTrue (p:formula) = match p with
  | BForm ((BConst (true, pos)),_) -> true
  | _ -> false
        
and isConstBTrue (p:b_formula) = match p with
  | BConst (true, pos) -> true
  | _ -> false
        
and isConstFalse (p:formula) = match p with
  | BForm ((BConst (false, pos)),_) -> true
  | _ -> false
        
and isConstBFalse (p:b_formula) = match p with
  | BConst (false, pos) -> true
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
  | Null _ -> null_var (* it is safe to name it "null" as no other variable can be named "null" *)
  | _ -> failwith ("get_alias: argument is neither a variable nor null")

and is_object_var (sv : spec_var) = match sv with
  | SpecVar (Named _, _, _) -> true
  | _ -> false
        
and exp_is_object_var (sv : exp) = match sv with
  | Var(SpecVar (Named _, _, _),_) -> true
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

and is_bag_bform (b: b_formula) : bool = match b with
  | BagIn _ | BagNotIn _ | BagSub _ | BagMin _ | BagMax _ -> true
  | _ -> false

and is_list_bform (b: b_formula) : bool = match b with
  | ListIn _ | ListNotIn _ | ListAllN _ | ListPerm _ -> true
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
  | (Globals.BagT _) -> true
  | _ -> false
        
and is_list_type (t : typ) = match t with
  | Globals.List _  -> true
  | _ -> false

and is_int_type (t : typ) = match t with
  | Int -> true
  | _ -> false

and is_float_type (t : typ) = match t with
  | Float -> true
  | _ -> false

and is_object_type (t : typ) = match t with
  | Named _ -> true
  | _ -> false

and should_simplify (f : formula) = match f with
  | Exists _ -> true
  | _ -> false
        (* | Exists (_, Exists (_, (Exists _),_,_), _,_) -> true *)

        
and is_b_form_arith (b: b_formula) :bool = match b with
  | BConst _  | BVar _ -> true
  | Lt (e1,e2,_) | Lte (e1,e2,_)  | Gt (e1,e2,_) | Gte (e1,e2,_) | Eq (e1,e2,_) 
  | Neq (e1,e2,_) -> (is_exp_arith e1)&&(is_exp_arith e2)
  | EqMax (e1,e2,e3,_) | EqMin (e1,e2,e3,_) -> (is_exp_arith e1)&&(is_exp_arith e2) && (is_exp_arith e3)
        (* bag formulas *)
  | BagIn _ | BagNotIn _ | BagSub _ | BagMin _ | BagMax _
            (* list formulas *)
  | ListIn _ | ListNotIn _ | ListAllN _ | ListPerm _
  | RelForm _ -> false (* An Hoa *)

(* Expression *)
and is_exp_arith (e:exp) : bool= match e with
  | Null _  | Var _ | IConst _ | FConst _ -> true
  | Add (e1,e2,_)  | Subtract (e1,e2,_)  | Mult (e1,e2,_) 
  | Div (e1,e2,_)  | Max (e1,e2,_)  | Min (e1,e2,_) -> (is_exp_arith e1) && (is_exp_arith e2)
        (* bag expressions *)
  | Bag _ | BagUnion _ | BagIntersect _ | BagDiff _
            (* list expressions *)
  | List _ | ListCons _ | ListHead _ | ListTail _
  | ListLength _ | ListAppend _ | ListReverse _ -> false
  | ArrayAt _ -> true (* An Hoa : a[i] is just a value *)
        
and is_formula_arith (f:formula) :bool = match f with
  | BForm (b,_) -> is_b_form_arith b 
  | And (f1,f2,_) | Or (f1,f2,_,_)-> (is_formula_arith f1)&&(is_formula_arith f2)
  | Not (f,_,_) | Forall (_,f,_,_) | Exists (_,f,_,_)-> (is_formula_arith f)
        
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

and mkBVar v p pos = BVar (SpecVar (Bool, v, p), pos)

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

and mkEqExp (ae1 : exp) (ae2 : exp) pos :formula = match (ae1, ae2) with
  | (Var v1, Var v2) ->
        if eq_spec_var (fst v1) (fst v2) then
          mkTrue pos 
        else
          BForm ((Eq (ae1, ae2, pos)),None)
  | _ ->  BForm ((Eq (ae1, ae2, pos)),None)

and mkNeqExp (ae1 : exp) (ae2 : exp) pos = match (ae1, ae2) with
  | (Var v1, Var v2) ->
        if eq_spec_var (fst v1) (fst v2) then
          mkFalse pos 
        else
          BForm ((Neq (ae1, ae2, pos)),None)
  | _ ->  BForm ((Neq (ae1, ae2, pos)),None)

and mkNot f lbl1 pos0 :formula= match f with
  | BForm (bf,lbl) -> begin
      match bf with
        | BConst (b, pos) -> BForm ((BConst ((not b), pos)),lbl)
        | Lt (e1, e2, pos) -> BForm ((Gte (e1, e2, pos)),lbl)
        | Lte (e1, e2, pos) -> BForm ((Gt (e1, e2, pos)),lbl)
        | Gt (e1, e2, pos) -> BForm ((Lte (e1, e2, pos)),lbl)
        | Gte (e1, e2, pos) -> BForm ((Lt (e1, e2, pos)),lbl)
        | Eq (e1, e2, pos) -> BForm ((Neq (e1, e2, pos)),lbl)
        | Neq (e1, e2, pos) -> BForm ((Eq (e1, e2, pos)),lbl)
		| BagIn e -> BForm ((BagNotIn e),lbl)
		| BagNotIn e -> BForm ((BagIn e),lbl)
        | _ -> Not (f, lbl,pos0)
	end
  | _ -> Not (f, lbl1,pos0)
        
and mkEqVar (sv1 : spec_var) (sv2 : spec_var) pos=
  if eq_spec_var sv1 sv2 then
    mkTrue pos
  else
    BForm ((Eq (Var (sv1, pos), Var (sv2, pos), pos)),None)

and mkNeqVar (sv1 : spec_var) (sv2 : spec_var) pos=
  if eq_spec_var sv1 sv2 then
    mkFalse pos
  else
    BForm ((Neq (Var (sv1, pos), Var (sv2, pos), pos)),None)

and mkEqVarInt (sv : spec_var) (i : int) pos =
  BForm ((Eq (Var (sv, pos), IConst (i, pos), pos)),None)


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
and mkTrue pos =  BForm ((BConst (true, pos)),None)

and mkFalse pos = BForm ((BConst (false, pos)),None)

and mkExists_with_simpl_debug simpl (vs : spec_var list) (f : formula) lbl pos = 
  Gen.Debug.no_2 "mkExists_with_simpl" !print_svl !print_formula !print_formula 
      (fun vs f -> mkExists_with_simpl simpl vs f lbl pos) vs f

and mkExists_with_simpl simpl (vs : spec_var list) (f : formula) lbl pos = 
  let r = mkExists vs f lbl pos in
  if contains_exists r then
    simpl r
  else r

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

(* same of list_of_conjs *)
and split_conjunctions f = list_of_conjs f
  (*
    function
    | And (x, y, _) -> (split_conjunctions x) @ (split_conjunctions y)
    | z -> [z]
  *)
  
and join_conjunctions fl = conj_of_list fl no_pos

(* List.fold_left (fun a c-> mkAnd a c no_pos) (mkTrue no_pos) f *)
  
(*take out from ante all the leafs that are in the memoized lists*)
(*and implied_prune_ante ante = match ante with
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
  | Or _ | Not _  | Forall _  | Exists _ -> ante *)

  
and is_member_pure (f:formula) (p:formula):bool = 
  let y = split_conjunctions p in
  List.exists (fun c-> equalFormula f c) y
      

(*limited, should use equal_formula, equal_b_formula, eq_exp instead*)  
and equalFormula_f (eq:spec_var -> spec_var -> bool) (f1:formula)(f2:formula):bool = 
  match (f1,f2) with
    | ((BForm (b1,_)),(BForm (b2,_))) -> equalBFormula_f eq  b1 b2
    | ((Not (b1,_,_)),(Not (b2,_,_))) -> equalFormula_f eq b1 b2
    | (Or(f1, f2, _,_), Or(f3, f4, _,_))
    | (And(f1, f2, _), And(f3, f4, _)) ->  (equalFormula_f eq f1 f3) & (equalFormula_f eq f2 f4)
    | (Exists(sv1, f1, _,_), Exists(sv2, f2, _,_))
    | (Forall(sv1, f1,_, _), Forall(sv2, f2, _,_)) -> (eq sv1 sv2) & (equalFormula_f eq f1 f2)
    | _ -> false

and equalBFormula_f (eq:spec_var -> spec_var -> bool) (f1:b_formula)(f2:b_formula):bool = 
  match (f1,f2) with
    | (BConst(c1, _), BConst(c2, _)) -> c1 = c2
    | (BVar(sv1, _), BVar(sv2, _)) -> (eq sv1 sv2)
    | (Lte(e1, e2, _), Gt(e4, e3, _))
    | (Gt(e1, e2, _), Lte(e4, e3, _))
    | (Gte(e1, e2, _), Lt(e4, e3, _))
    | (Lt(e1, e2, _), Gte(e4, e3, _))  
    | (Lte(e1, e2, _), Lte(e3, e4, _))
    | (Gt(e1, e2, _), Gt(e3, e4, _))
    | (Gte(e1, e2, _), Gte(e3, e4, _))
    | (Lt(e1, e2, _), Lt(e3, e4, _)) -> (eqExp_f eq e1 e3) & (eqExp_f eq e2 e4)
    | (Neq(e1, e2, _), Neq(e3, e4, _))
    | (Eq(e1, e2, _), Eq(e3, e4, _)) -> ((eqExp_f eq e1 e3) & (eqExp_f eq e2 e4)) or ((eqExp_f eq e1 e4) & (eqExp_f eq e2 e3))
    | (EqMax(e1, e2, e3, _), EqMax(e4, e5, e6, _))
    | (EqMin(e1, e2, e3, _), EqMin(e4, e5, e6, _))  -> (eqExp_f eq e1 e4) & ((eqExp_f eq e2 e5) & (eqExp_f eq e3 e6)) or ((eqExp_f eq e2 e6) & (eqExp_f eq e3 e5))
    | (BagIn(sv1, e1, _), BagIn(sv2, e2, _))
    | (BagNotIn(sv1, e1, _), BagNotIn(sv2, e2, _)) -> (eq sv1 sv2) & (eqExp_f eq e1 e2)
    | (ListIn(e1, e2, _), ListIn(d1, d2, _))
    | (ListNotIn(e1, e2, _), ListNotIn(d1, d2, _)) -> (eqExp_f eq e1 d1) & (eqExp_f eq e2 d2)
    | (ListAllN(e1, e2, _), ListAllN(d1, d2, _)) -> (eqExp_f eq e1 d1) & (eqExp_f eq e2 d2)
    | (ListPerm(e1, e2, _), ListPerm(d1, d2, _)) -> (eqExp_f eq e1 d1) & (eqExp_f eq e2 d2)
    | (BagMin(sv1, sv2, _), BagMin(sv3, sv4, _))
    | (BagMax(sv1, sv2, _), BagMax(sv3, sv4, _)) -> (eq sv1 sv3) & (eq sv2 sv4)
    | (BagSub(e1, e2, _), BagSub(e3, e4, _)) -> (eqExp_f eq e1 e3) & (eqExp_f eq e2 e4)
    | _ -> false
          (*
            match (f1,f2) with
            | ((BVar v1),(BVar v2))-> (eq (fst v1) (fst v2))
            | ((Lte (v1,v2,_)),(Lte (w1,w2,_)))
            | ((Lt (v1,v2,_)),(Lt (w1,w2,_)))-> (eqExp_f eq w1 v1)&&(eqExp_f eq w2 v2)
            | ((Neq (v1,v2,_)) , (Neq (w1,w2,_)))
            | ((Eq (v1,v2,_)) , (Eq (w1,w2,_))) -> ((eqExp_f eq w1 v1)&&(eqExp_f eq w2 v2))|| ((eqExp_f eq w1 v2)&&(eqExp_f eq w2 v1))
            | ((BagIn (v1,e1,_)),(BagIn (v2,e2,_)))
            | ((BagNotIn (v1,e1,_)),(BagNotIn (v2,e2,_))) -> (eq v1 v2)&&(eqExp_f eq e1 e2)
            | ((ListIn (e1,e2,_)),(ListIn (d1,d2,_)))
            | ((ListNotIn (e1,e2,_)),(ListNotIn (d1,d2,_))) -> (eqExp_f eq e1 d1)&&(eqExp_f eq e2 d2)
            | ((ListAllN (e1,e2,_)),(ListAllN (d1,d2,_))) -> (eqExp_f eq e1 d1)&&(eqExp_f eq e2 d2)
            | ((ListPerm (e1,e2,_)),(ListPerm (d1,d2,_))) -> (eqExp_f eq e1 d1)&&(eqExp_f eq e2 d2)
            | ((BagMax (v1,v2,_)),(BagMax (w1,w2,_))) 
            | ((BagMin (v1,v2,_)),(BagMin (w1,w2,_))) -> (eq v1 w1)&& (eq v2 w2)
            | _ -> false
          *)
          
and eqExp_f (eq:spec_var -> spec_var -> bool) (e1:exp)(e2:exp):bool =
  match (e1, e2) with
    | (Null(_), Null(_)) -> true
    | (Var(sv1, _), Var(sv2, _)) -> (eq sv1 sv2)
    | (IConst(i1, _), IConst(i2, _)) -> i1 = i2
    | (FConst(f1, _), FConst(f2, _)) -> f1 = f2
    | (Subtract(e11, e12, _), Subtract(e21, e22, _))
    | (Max(e11, e12, _), Max(e21, e22, _))
    | (Min(e11, e12, _), Min(e21, e22, _))
    | (Add(e11, e12, _), Add(e21, e22, _)) -> (eqExp_f eq e11 e21) & (eqExp_f eq e12 e22)
    | (Mult(e11, e12, _), Mult(e21, e22, _)) -> (eqExp_f eq e11 e21) & (eqExp_f eq e12 e22)
    | (Div(e11, e12, _), Div(e21, e22, _)) -> (eqExp_f eq e11 e21) & (eqExp_f eq e12 e22)
    | (Bag(e1, _), Bag(e2, _))
    | (BagUnion(e1, _), BagUnion(e2, _))
    | (BagIntersect(e1, _), BagIntersect(e2, _)) -> (eqExp_list_f eq e1 e2)
    | (BagDiff(e1, e2, _), BagDiff(e3, e4, _)) -> (eqExp_f eq e1 e3) & (eqExp_f eq e2 e4)
    | (List (l1, _), List (l2, _))
    | (ListAppend (l1, _), ListAppend (l2, _)) -> if (List.length l1) = (List.length l2) then List.for_all2 (fun a b-> (eqExp_f eq a b)) l1 l2 
      else false
    | (ListCons (e1, e2, _), ListCons (d1, d2, _)) -> (eqExp_f eq e1 d1) && (eqExp_f eq e2 d2)
    | (ListHead (e1, _), ListHead (e2, _))
    | (ListTail (e1, _), ListTail (e2, _))
    | (ListLength (e1, _), ListLength (e2, _))
    | (ListReverse (e1, _), ListReverse (e2, _)) -> (eqExp_f eq e1 e2)
    | _ -> false


and eqExp_list_f (eq:spec_var -> spec_var -> bool) (e1 : exp list) (e2 : exp list) : bool =
  let rec eq_exp_list_helper (e1 : exp list) (e2 : exp list) = match e1 with
    | [] -> true
    | h :: t -> (List.exists (fun c -> eqExp_f eq h c) e2) & (eq_exp_list_helper t e2)
  in
  (eq_exp_list_helper e1 e2) & (eq_exp_list_helper e2 e1)
      
(*
  match (e1,e2) with
  | (Null _ ,Null _ ) -> true
  | (Var (v1,_), Var (v2,_)) -> (eq v1 v2)
  | (IConst (v1,_), IConst (v2,_)) -> v1=v2
  | (FConst (v1,_), FConst (v2,_)) -> v1=v2
  | (Div(e1, e2, _), Div(d1, d2, _)) 
  | (Subtract(e1, e2, _), Subtract(d1, d2, _)) -> (eqExp_f eq e1 d1)& (eqExp_f eq e2 d2)
  | (Max (e1,e2,_),Max (d1,d2,_)) 
  | (Min (e1,e2,_),Min (d1,d2,_)) 
  | (Mult (e1, e2, _), Mult(d1, d2, _)) ->
  | (Add (e1,e2,_),Add (d1,d2,_)) -> (eqExp_f eq e1 d1)& (eqExp_f eq e2 d2)  (*((eqExp_f eq e1 d2)&&(eqExp_f eq e2 d1))*)
  | (BagDiff(e1,e2,_),BagDiff (d1,d2,_)) -> ((eqExp_f eq e1 d1)& (eqExp_f eq e2 d2))
  | (Div _, Div _) -> false (* FIX IT *)
  | (Bag (l1,_),Bag (l2,_)) -> if (List.length l1)=(List.length l1) then List.for_all2 (fun a b-> (eqExp_f eq a b)) l1 l2 
  else false
  | (List (l1,_),List (l2,_))
  | (ListAppend (l1,_),ListAppend (l2,_))  -> if (List.length l1)=(List.length l2) then List.for_all2 (fun a b-> (eqExp_f eq a b)) l1 l2 
  else false
  | (ListCons (e1,e2,_),ListCons (d1,d2,_)) -> (eqExp_f eq e1 d1)&&(eqExp_f eq e2 d2)
  | (ListHead (e1,_),ListHead (e2,_))
  | (ListTail (e1,_),ListTail (e2,_))
  | (ListLength (e1,_),ListLength (e2,_))
  | (ListReverse (e1,_),ListReverse (e2,_)) -> (eqExp_f eq e1 e2)
  | _ -> false
*)	      

and equalFormula (f1:formula)(f2:formula):bool = equalFormula_f eq_spec_var  f1 f2

and equalBFormula (f1:b_formula)(f2:b_formula):bool = equalBFormula_f eq_spec_var  f1 f2

and eqExp (f1:exp)(f2:exp):bool = eqExp_f eq_spec_var  f1 f2

(*
(* build relation from list of expressions, for example a,b,c < d,e, f *)
  and build_relation relop alist10 alist20 lbl pos=
  let rec helper1 ae alist =
  let a = List.hd alist in
  let rest = List.tl alist in
  let check_upper r e ub pos = if ub<=1 then Eq (e,(Null no_pos),pos) else r in
  let check_lower r e lb pos = if lb>=0 then Neq (e,(Null no_pos),pos) else r in
  let rec tt relop ae a pos = 
  let r = (relop ae a pos) in
  match r with
  | Lte (e1,e2,l) 
  | Gte (e2,e1,l) -> 
  ( match e1,e2 with
  | Var (v,_), IConst(i,l) -> if (is_otype (type_of_spec_var v)) then check_upper r e1 (i+1) l else r
  | IConst(i,l), Var (v,_) -> if (is_otype (type_of_spec_var v)) then check_lower r e2 (i-1) l else r
  | _ -> r)
  | Gt (e1,e2,l) 
  | Lt (e2,e1,l) -> 
  ( match e1,e2 with
  | Var (v,_), IConst(i,l) -> if (is_otype (type_of_spec_var v)) then check_lower r e1 i l else r
  | IConst(i,l), Var (v,_) -> if (is_otype (type_of_spec_var v)) then check_upper r e2 i l else r
  | _ -> r)
  | Eq (e1,e2,l) ->
  ( match e1,e2 with
  | Var (v,_), IConst(0,l) -> if (is_otype (type_of_spec_var v)) then Eq (e1,(Null no_pos),pos) else r
  | IConst(0,l), Var (v,_) -> if (is_otype (type_of_spec_var v)) then Eq (e2,(Null no_pos),pos) else r
  | _ -> r)
  | Neq (e1,e2,l) ->
  ( match e1,e2 with
  | Var (v,_), IConst(0,l) -> if (is_otype (type_of_spec_var v)) then Neq (e1,(Null no_pos),pos) else r
  | IConst(0,l), Var (v,_) -> if (is_otype (type_of_spec_var v)) then Neq (e2,(Null no_pos),pos) else r
  | _ -> r)
  | _ -> r in 
  let tmp = BForm ((tt relop ae a pos),lbl) in
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
  else
  helper2 alist10 alist20*)
  
(* build relation from list of expressions, for example a,b,c < d,e, f *)
and build_relation relop alist10 alist20 lbl pos=
  let rec helper1 ae alist =
    let a = List.hd alist in
    let rest = List.tl alist in
    let check_upper r e ub pos = if ub>1 then r else  Eq (e,(Null no_pos),pos) in
    let check_lower r e lb pos = if lb>0 then Neq (e,(Null no_pos),pos) else r in
    let rec tt relop ae a pos = 
      let r = (relop ae a pos) in
      match r with
        | Lte (e1,e2,l) 
        | Gte (e2,e1,l) -> 
              ( match e1,e2 with
                | Var (v,_), IConst(i,l) -> if (is_otype (type_of_spec_var v)) then check_upper r e1 (i+1) l else r
                | IConst(i,l), Var (v,_) -> if (is_otype (type_of_spec_var v)) then check_lower r e2 (i-1) l else r
                | _ -> r)
        | Gt (e1,e2,l) 
        | Lt (e2,e1,l) -> 
              ( match e1,e2 with
                | Var (v,_), IConst(i,l) -> if (is_otype (type_of_spec_var v)) then check_lower r e1 i l else r
                | IConst(i,l), Var (v,_) -> if (is_otype (type_of_spec_var v)) then check_upper r e2 i l else r
                | _ -> r)
        | Eq (e1,e2,l) ->
              ( match e1,e2 with
                | Var (v,_), IConst(0,l) -> if (is_otype (type_of_spec_var v)) then Eq (e1,(Null no_pos),pos) else r
                | IConst(0,l), Var (v,_) -> if (is_otype (type_of_spec_var v)) then Eq (e2,(Null no_pos),pos) else r
                | _ -> r)
        | Neq (e1,e2,l) ->
              ( match e1,e2 with
                | Var (v,_), IConst(0,l) -> if (is_otype (type_of_spec_var v)) then Neq (e1,(Null no_pos),pos) else r
                | IConst(0,l), Var (v,_) -> if (is_otype (type_of_spec_var v)) then Neq (e2,(Null no_pos),pos) else r
                | _ -> r)
        | _ -> r in  
    let tmp = BForm ((tt relop ae a pos),lbl) in
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
  else
    helper2 alist10 alist20
        (* utility functions *)


and mem (sv : spec_var) (svs : spec_var list) : bool =
  List.exists (fun v -> eq_spec_var sv v) svs

and disjoint (svs1 : spec_var list) (svs2 : spec_var list) =
  List.for_all (fun sv -> not (mem sv svs2)) svs1

and subset (svs1 : spec_var list) (svs2 : spec_var list) =
  List.for_all (fun sv -> mem sv svs2) svs1

and intersect (svs1 : spec_var list) (svs2 : spec_var list) =
  List.filter (fun sv -> mem sv svs2) svs1

and are_same_types (t1 : typ) (t2 : typ) = match t1 with
  | Named c1 -> begin match t2 with
	    (* | _ -> false *)
      | Named c2 -> c1 = c2 || c1 = "" || c2 = ""
	  | _ -> false (* An Hoa *)
	end
  | Array (et1, _) -> begin match t2 with 
	  | Array (et2, _) -> are_same_types et1 et2
	  | _ -> false  
  end
  | _ -> t1 = t2
		
and is_otype (t : typ) : bool = match t with
  | Named _ -> true
  | _ -> false (* | _ -> false *) (* An Hoa *)

and name_of_type (t : typ) : ident = 
  string_of_typ t
(* match t with *)
(*   | Int -> "int" *)
(*   | Bool -> "boolean" *)
(*   | Void -> "void" *)
(*   | Float -> "float" *)
(*   | (TVar i) -> "TVar["^(string_of_int i)^"]" *)
(*   | (BagT t) -> "bag("^(name_of_type (t))^")" *)
(*   | Globals.List -> "list" *)
(*   | Named c -> c *)
(*   | Array (et, _) -> name_of_type et ^ "[]" (\* An Hoa *\) *)

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
  | ArrayAt (_, _, p) -> p (* An Hoa *)

and same_name_spec_var sv1 sv2 : bool = match sv1,sv2 with
  | SpecVar (_, v1, _), SpecVar (_, v2, _) -> String.compare v1 v2 = 0
  
and name_of_spec_var (sv : spec_var) : ident = match sv with
  | SpecVar (_, v, _) -> v

and full_name_of_spec_var (sv : spec_var) : ident = match sv with
  | SpecVar (_, v, p) -> if (p==Primed) then (v^"\'") else v

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
  | SpecVar (_, v, p) -> SpecVar (Int, v, p)


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

and remove_dups_spec_var_list vl = Gen.BList.remove_dups_eq eq_spec_var vl

and remove_spec_var (sv : spec_var) (vars : spec_var list) =
  List.filter (fun v -> not (eq_spec_var sv v)) vars

and is_anon_var (SpecVar (_,n,_):spec_var) : bool = ((String.length n) > 5) && ((String.compare (String.sub n 0 5) "Anon_") == 0)
  
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
        
and subst_var (fr, t) (o : spec_var) = if eq_spec_var fr o then t else o

and subst_one_var_list s l = List.map (subst_var s) l

and par_subst sst f = apply_subs sst f

and apply_subs (sst : (spec_var * spec_var) list) (f : formula) : formula = match f with
  | BForm (bf,lbl) -> BForm ((b_apply_subs sst bf),lbl)
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
  | RelForm (r, args, pos) -> RelForm (r, e_apply_subs_list sst args, pos) (* An Hoa *)
		

(* and subs_one sst v = List.fold_left (fun old -> fun (fr,t) -> if (eq_spec_var fr v) then t else old) v sst  *)

and subs_one sst v = 
  let rec helper sst v = match sst with
    | [] -> v
    | (fr,t)::sst -> if (eq_spec_var fr v) then t else (helper sst v)
  in helper sst v

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
  | ArrayAt (a, i, pos) -> ArrayAt (subs_one sst a, e_apply_subs sst i, pos) (* An Hoa : bug detected, replace a by subone sst a*)

and e_apply_subs_list sst alist = List.map (e_apply_subs sst) alist

and apply_one (fr, t) f = match f with
  | BForm (bf,lbl) -> BForm (b_apply_one (fr, t) bf , lbl)
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

and b_subst zip bf = List.fold_left (fun a c-> b_apply_one c a) bf zip
  
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
  | RelForm (r, args, pos) -> RelForm (r, e_apply_one_list (fr, t) args, pos) (* An Hoa *)

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
  | ArrayAt (a, i, pos) -> ArrayAt ((if eq_spec_var a fr then t else a), e_apply_one (fr, t) i, pos) (* An Hoa CHECK: BUG DETECTED must compare fr and a, in case we want to replace a[i] by a'[i] *)

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
  | BForm (bf,lbl) -> BForm (b_apply_par_term sst bf , lbl)
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
  | RelForm (r, args, pos) -> RelForm (r, a_apply_par_term_list sst args, pos) (* An Hoa *) 

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
  | ArrayAt (a, i, pos) -> (* An Hoa : CHECK BUG DETECTED - substitute a as well *)
		let a1 = subs_one_term sst a (Var (a,pos)) in
		(match a1 with
		  | Var (a2,_) -> ArrayAt (a2, a_apply_par_term sst i, pos) 
		  | _ -> failwith "Cannot substitute an array variable by a non variable!\n")  

and a_apply_par_term_list sst alist = match alist with
  |[] -> []
  |a :: rest -> (a_apply_par_term sst a) :: (a_apply_par_term_list sst rest)

and apply_one_term (fr, t) f = match f with
  | BForm (bf,lbl) -> BForm (b_apply_one_term (fr, t) bf , lbl)
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
  | RelForm (r, args, pos) -> RelForm (r, List.map (a_apply_one_term (fr, t)) args, pos) (* An Hoa *) 

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
  | ArrayAt (a, i, pos) -> 
		let a1 = if eq_spec_var a fr then 
		  (match t with
			| Var (a2, _) -> a2
			| _ -> failwith "Cannot apply a non-variable term to an array variable.")
		else a in
		ArrayAt (a1, a_apply_one_term (fr, t) i, pos) (* An Hoa *) 


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
          (b1,ListReverse (r1, pos))
	| ArrayAt (a, i, pos) -> (* An Hoa CHECK THIS! *)
		  let b1,i1 = (helper crt_var i) in
          (b1,ArrayAt (a, i1, pos)) in
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

and  get_subst_equation_formula_vv (f0 : formula) (v : spec_var):((spec_var * spec_var) list * formula) = 
  let r1,r2 = get_subst_equation_formula f0 v true in
  let r =List.fold_left (fun a (c1,c2)->match c2 with
    | Var (v,_)-> (c1,v)::a
    | _ -> a ) [] r1 in
  (r,r2)


and get_subst_equation_formula (f0 : formula) (v : spec_var) only_vars: ((spec_var * exp) list * formula) = match f0 with
  | And (f1, f2, pos) ->
        let st1, rf1 = get_subst_equation_formula f1 v only_vars in
        if not (Gen.is_empty st1) then
          (st1, mkAnd rf1 f2 pos)
        else
          let st2, rf2 = get_subst_equation_formula f2 v only_vars in
          (st2, mkAnd f1 rf2 pos)
  | BForm (bf,lbl) -> get_subst_equation_b_formula bf v lbl only_vars
  | _ -> ([], f0)
        
and get_subst_equation_b_formula (f : b_formula) (v : spec_var) lbl only_vars: ((spec_var * exp) list * formula) = match f with
  | Eq (e1, e2, pos) -> begin
      match e1, e2 with
        | Var (sv1, _), Var (sv2, _) -> 
              if (eq_spec_var sv1 v) && (not (eq_spec_var sv2 v)) then ([(v, e2)], mkTrue no_pos )
              else if (eq_spec_var sv2 v) && (not (eq_spec_var sv1 v))  then ([(v, e1)], mkTrue no_pos )
              else ([], BForm (f,lbl))
        | Var (sv1, _), _  ->
              if only_vars then ([], BForm (f,lbl))
              else if (eq_spec_var sv1 v) &&(not (List.exists (fun sv -> eq_spec_var sv v) (afv e2))) then ([(v, e2)], mkTrue no_pos )
              else ([], BForm (f,lbl))
        | _ , Var (sv2, _) ->
              if only_vars then ([], BForm (f,lbl))
              else if (eq_spec_var sv2 v) && (not (List.exists (fun sv -> eq_spec_var sv v) (afv e1))) then ([(v, e1)], mkTrue no_pos )
              else ([], BForm (f,lbl))
        | _ ->([], BForm (f,lbl))
    end
  | _ -> ([], BForm (f,lbl))
        
        
(* 
   Get a list of conjuncts, namely
   F1 & F2 & .. & Fn ==> [F1,F2,..,FN] 
*)
and list_of_conjs (f0 : formula) : formula list =
  let rec helper f conjs = match f with
    | And (f1, f2, pos) ->
          let tmp1 = helper f2 conjs in
          let tmp2 = helper f1 tmp1 in
          tmp2
    | _ -> f :: conjs
  in
  helper f0 []

(* 
   Make a formula from a list of conjuncts, namely
   [F1,F2,..,FN]  ==> F1 & F2 & .. & Fn 
*)
and conj_of_list (fs : formula list) pos : formula =
  match fs with
    | [] -> mkTrue pos
    | x::xs -> List.fold_left (fun a c-> mkAnd a c no_pos) x xs
          (*
            let helper f1 f2 = mkAnd f1 f2 pos in
            List.fold_left helper (mkTrue pos) fs
          *)

(* 
   Get a list of disjuncts, namely
   F1 or F2 or .. or Fn ==> [F1,F2,..,FN] 
*)
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
   deeper split of disjuncts (seems an explosion)
*)
and split_disjuncts (f0 : formula): formula list = match f0 with
  | BForm _ -> [f0]
  | And (f1,f2,_) -> 
        let l1 = split_disjuncts f1 in
        let l2 = split_disjuncts f2 in
        List.concat (List.map (fun f-> List.map (fun d-> mkAnd d f no_pos) l1) l2)
  | Or (f1,f2,_,_) -> 
        let l1 = split_disjuncts f1 in
        let l2 = split_disjuncts f2 in
        l1@l2
  | Not _ -> [f0] 
  | Forall _ -> [f0]
  | Exists (v,f,_,_) -> List.map (fun f-> mkExists [v] f None no_pos) (split_disjuncts f)
        
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
    | BForm (bf,_) -> find_bound_b_formula v bf
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

(* eliminate exists with the help of c1<=v<=c2 *)
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



(* eliminate exists with the help of v=exp *)
and elim_exists (f0 : formula) : formula = 
  let rec helper f0 =
    match f0 with
      | Exists (qvar, qf, lbl, pos) -> begin
	      match qf with
	        | Or (qf1, qf2, lbl2, qpos) ->
	              let new_qf1 = mkExists [qvar] qf1 lbl qpos in
	              let new_qf2 = mkExists [qvar] qf2 lbl qpos in
	              let eqf1 = helper new_qf1 in
	              let eqf2 = helper new_qf2 in
	              let res = mkOr eqf1 eqf2 lbl2 pos in
	              res
	        | _ ->
	              let qf = helper qf in
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
	              let st, pp1 = get_subst_equation_formula with_qvars qvar false in
	              if not (Gen.is_empty st) then
	                let new_qf = subst_term st pp1 in
	                let new_qf = mkExists qvars0 new_qf lbl pos in
	                let tmp3 = helper new_qf in
	                let tmp4 = mkAnd no_qvars tmp3 pos in
	                tmp4
	              else (* if qvar is not equated to any variables, try the next one *)
	                let tmp1 = qf (*helper qf*) in
	                let tmp2 = mkExists(*_with_simpl simpl*) [qvar] tmp1 lbl pos in
	                tmp2
        end
      | And (f1, f2, pos) -> begin
	      let ef1 = helper f1 in
	      let ef2 = helper f2 in
	      let res = mkAnd ef1 ef2 pos in
	      res
        end
      | Or (f1, f2, lbl, pos) -> begin
	      let ef1 = helper f1 in
	      let ef2 = helper f2 in
	      let res = mkOr ef1 ef2 lbl pos in
	      res
        end
      | Not (f1, lbl, pos) -> begin
	      let ef1 = helper f1 in
	      let res = mkNot ef1 lbl pos in
	      res
        end
      | Forall (qvar, qf, lbl, pos) -> begin
	      let eqf = helper qf in
	      let res = mkForall [qvar] eqf lbl pos in
	      res
        end
      | BForm _ -> f0 in
  helper f0


let string_of_spec_var (sv: spec_var) = match sv with
    | SpecVar (t, v, _) -> v ^ (if is_primed sv then "PRMD" else "")
 
let string_of_spec_var_type (sv: spec_var) = match sv with
    | SpecVar (t, v, _) -> v ^ (if is_primed sv then "PRMD" else "")^":"^(string_of_typ t)
 
 
(*module Ptr =
    functor (Elt:Gen.EQ_TYPE) ->
struct
  include Elt
  type tlist = t list
  type ef = t -> t -> bool
  module X = Gen.BListEQ(Elt)
  (*let overlap_eq eq = eq
  let intersect_eq eq (x:tlist)  (y:tlist) = Gen.BList.intersect_eq eq x y*)
  let overlap = eq
  let intersect (x:tlist)  (y:tlist) = X.intersect x y
  let star_union x y = x@y
end;;*)
 
module SV =
struct 
  type t = spec_var
  let eq = eq_spec_var
  let string_of = string_of_spec_var
end;;

module Type_prop = 
  struct
      type t=typ
      let eq t1 t2 = (t1=t2)
      let are_disj t1 t2 = match t1,t2 with
         | UNK,_
         | _,UNK -> true
         | _,_ -> 
          if t1=t2 then false
          else true
      let star_t t1 t2 = true (*decide if to keep the first arg*)
      let and_t t1 t2 = sub_type t1 t2
      let or_t t1 t2 = sub_type t2 t1 
      let string_of = string_of_typ
    end;;

module Frac_prop = 
  struct
      type t=Ts.stree
      let eq = Ts.stree_eq
      let are_disj t1 t2 = not (Ts.can_join t1 t2) 
      let star_t t1 t2 = true (*decide if to keep the first arg*)
      let and_t t1 t2 = Ts.contains t1 t2
      let or_t t1 t2 = Ts.contains t2 t1 
      let string_of = Ts.string_of_tree_share
    end;;
    
module TFProp = Gen.Mem_prop_comb (Type_prop) (Frac_prop)

module Ptr_prop =
    functor (Elt:Gen.EQ_TYPE) ->
    functor (Prop:Gen.MEM_PROP) ->
struct
  (*include Elt*)
  type t = Elt.t*Prop.t
  type tlist = t list
  type ef = t -> t -> bool
  let eq (f1,s1) (f2,s2) = Elt.eq f1 f2 (*& not (Prop.are_disj s1 s2)*)
  let overlap  = eq
  let disj x y = Prop.are_disj (snd x) (snd y)
  let strong_eq (f1,s1) (f2,s2) = Elt.eq f1 f2 & Prop.eq s1 s2
  
  let string_of (f,s) = "("^(Elt.string_of f)^" , "^(Prop.string_of s)^")"
  
  let or_t (f1,s1) (f2,s2) = Elt.eq f1 f2 & (Prop.or_t s1 s2)
  let and_t (f1,s1) (f2,s2) = Elt.eq f1 f2 & not (Prop.and_t s1 s2)
  
  let intersect = Gen.BList.intersect_rel or_t strong_eq
  let and_union x y = 
      List.filter (fun c-> List.for_all (fun d-> not (and_t d c)) y) x @ 
      List.filter (fun c-> List.for_all (fun d-> not (and_t d c)) x) y
  let star_union x y = x@y
end;;


module PtrSV = Ptr_prop(SV)(TFProp);;

module BagaSV = Gen.Baga(PtrSV);;
module EMapSV = Gen.EqMap(SV);;
module DisjSetSV = Gen.DisjSet(PtrSV);;
 
type baga_sv = BagaSV.baga

type var_aset = EMapSV.emap

let eq_spec_var_aset (aset: EMapSV.emap ) (sv1 : spec_var) (sv2 : spec_var) = match (sv1, sv2) with
  | (SpecVar (t1, v1, p1), SpecVar (t2, v2, p2)) -> EMapSV.is_equiv aset sv1 sv2 
        

let equalFormula_aset aset (f1:formula)(f2:formula):bool = equalFormula_f (eq_spec_var_aset aset)  f1 f2
  
and equalBFormula_aset aset  (f1:b_formula)(f2:b_formula) :bool = equalBFormula_f (eq_spec_var_aset aset)  f1 f2

and eqExp_aset aset  (f1:exp)(f2:exp):bool = eqExp_f (eq_spec_var_aset aset)  f1 f2


let rec eq_exp aset (e1 : exp) (e2 : exp) : bool = eqExp_aset aset e1 e2
(*
match (e1, e2) with
  | (Null(_), Null(_)) -> true
  | (Var(sv1, _), Var(sv2, _)) -> (eq_spec_var_aset aset sv1 sv2)
  | (IConst(i1, _), IConst(i2, _)) -> i1 = i2
  | (FConst(f1, _), FConst(f2, _)) -> f1 = f2
  | (Subtract(e11, e12, _), Subtract(e21, e22, _))
  | (Max(e11, e12, _), Max(e21, e22, _))
  | (Min(e11, e12, _), Min(e21, e22, _))
  | (Add(e11, e12, _), Add(e21, e22, _)) -> (eq_exp aset e11 e21) & (eq_exp aset e12 e22)
  | (Mult(e11, e12, _), Mult(e21, e22, _)) -> (eq_exp aset e11 e21) & (eq_exp aset e12 e22)
  | (Div(e11, e12, _), Div(e21, e22, _)) -> (eq_exp aset e11 e21) & (eq_exp aset e12 e22)
  | (Bag(e1, _), Bag(e2, _))
  | (BagUnion(e1, _), BagUnion(e2, _))
  | (BagIntersect(e1, _), BagIntersect(e2, _)) -> (eq_exp_list aset e1 e2)
  | (BagDiff(e1, e2, _), BagDiff(e3, e4, _)) -> (eq_exp aset e1 e3) & (eq_exp aset e2 e4)
  | (List (l1, _), List (l2, _))
  | (ListAppend (l1, _), ListAppend (l2, _)) -> if (List.length l1) = (List.length l2) then List.for_all2 (fun a b-> (eq_exp aset a b)) l1 l2 
    else false
  | (ListCons (e1, e2, _), ListCons (d1, d2, _)) -> (eq_exp aset e1 d1) && (eq_exp aset e2 d2)
  | (ListHead (e1, _), ListHead (e2, _))
  | (ListTail (e1, _), ListTail (e2, _))
  | (ListLength (e1, _), ListLength (e2, _))
  | (ListReverse (e1, _), ListReverse (e2, _)) -> (eq_exp aset e1 e2)
  | _ -> false


and eq_exp_list aset (e1 : exp list) (e2 : exp list) : bool =
  let rec eq_exp_list_helper (e1 : exp list) (e2 : exp list) = match e1 with
    | [] -> true
    | h :: t -> (List.exists (fun c -> eq_exp aset h c) e2) & (eq_exp_list_helper t e2)
  in
  (eq_exp_list_helper e1 e2) & (eq_exp_list_helper e2 e1)
*)

let eq_exp_no_aset (e1 : exp) (e2 : exp) : bool = eq_exp EMapSV.mkEmpty e1 e2        

let eq_b_formula aset (b1 : b_formula) (b2 : b_formula) : bool =  equalBFormula_aset aset b1 b2
(*
match (b1, b2) with
  | (BConst(c1, _), BConst(c2, _)) -> c1 = c2
  | (BVar(sv1, _), BVar(sv2, _)) -> (eq_spec_var_aset aset sv1 sv2)
  | (Lte(e1, e2, _), Gt(e4, e3, _))
  | (Gt(e1, e2, _), Lte(e4, e3, _))
  | (Gte(e1, e2, _), Lt(e4, e3, _))
  | (Lt(e1, e2, _), Gte(e4, e3, _))  
  | (Lte(e1, e2, _), Lte(e3, e4, _))
  | (Gt(e1, e2, _), Gt(e3, e4, _))
  | (Gte(e1, e2, _), Gte(e3, e4, _))
  | (Lt(e1, e2, _), Lt(e3, e4, _)) -> (eq_exp aset e1 e3) & (eq_exp aset e2 e4)
  | (Neq(e1, e2, _), Neq(e3, e4, _))
  | (Eq(e1, e2, _), Eq(e3, e4, _)) -> ((eq_exp aset e1 e3) & (eq_exp aset e2 e4)) or ((eq_exp aset e1 e4) & (eq_exp aset e2 e3))
  | (EqMax(e1, e2, e3, _), EqMax(e4, e5, e6, _))
  | (EqMin(e1, e2, e3, _), EqMin(e4, e5, e6, _))  -> (eq_exp aset e1 e4) & ((eq_exp aset e2 e5) & (eq_exp aset e3 e6)) or ((eq_exp aset e2 e6) & (eq_exp aset e3 e5))
  | (BagIn(sv1, e1, _), BagIn(sv2, e2, _))
  | (BagNotIn(sv1, e1, _), BagNotIn(sv2, e2, _)) -> (eq_spec_var_aset aset sv1 sv2) & (eq_exp aset e1 e2)
  | (ListIn(e1, e2, _), ListIn(d1, d2, _))
  | (ListNotIn(e1, e2, _), ListNotIn(d1, d2, _)) -> (eq_exp aset e1 d1) & (eq_exp aset e2 d2)
  | (ListAllN(e1, e2, _), ListAllN(d1, d2, _)) -> (eq_exp aset e1 d1) & (eq_exp aset e2 d2)
  | (ListPerm(e1, e2, _), ListPerm(d1, d2, _)) -> (eq_exp aset e1 d1) & (eq_exp aset e2 d2)
  | (BagMin(sv1, sv2, _), BagMin(sv3, sv4, _))
  | (BagMax(sv1, sv2, _), BagMax(sv3, sv4, _)) -> (eq_spec_var_aset aset sv1 sv3) & (eq_spec_var_aset aset sv2 sv4)
  | (BagSub(e1, e2, _), BagSub(e3, e4, _)) -> (eq_exp aset e1 e3) & (eq_exp aset e2 e4)
  | _ -> false
*)

let eq_b_formula_no_aset (b1 : b_formula) (b2 : b_formula) : bool = eq_b_formula EMapSV.mkEmpty b1 b2


let rec eq_pure_formula (f1 : formula) (f2 : formula) : bool = equalFormula f1 f2 
(*
match (f1, f2) with
  | (BForm(b1,_), BForm(b2,_)) -> (eq_b_formula [] b1 b2)
  | (Or(f1, f2, _,_), Or(f3, f4, _,_))
  | (And(f1, f2, _), And(f3, f4, _)) ->
  	    ((eq_pure_formula f1 f3) & (eq_pure_formula f2 f4)) or ((eq_pure_formula f1 f4) & (eq_pure_formula f2 f3))
  | (Not(f1,_, _), Not(f2,_, _)) -> (eq_pure_formula f1 f2)
  | (Exists(sv1, f1, _,_), Exists(sv2, f2, _,_))
  | (Forall(sv1, f1,_, _), Forall(sv2, f2, _,_)) -> (eq_spec_var sv1 sv2) & (eq_pure_formula f1 f2)
  | _ -> false
*)


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

let find_rel_constraints (f:formula) desired :formula = 
 if desired=[] then (mkTrue no_pos)
 else 
   let lf = split_conjunctions f in
   let lf_pair = List.map (fun c-> ((fv c),c)) lf in
   let var_list = fst (List.split lf_pair) in
   let rec helper (fl:spec_var list) : spec_var list = 
    let nl = List.filter (fun c-> (Gen.BList.intersect_eq (=) c fl)!=[]) var_list in
    let nl = List.concat nl in
    if (List.length fl)=(List.length nl) then fl
    else helper nl in
   let fixp = helper desired in
   let pairs = List.filter (fun (c,_) -> (List.length (Gen.BList.intersect_eq (=) c fixp))>0) lf_pair in
   join_conjunctions (snd (List.split pairs))

  
  
(*
  Drop bag and list constraints for satisfiability checking.
*)
let rec drop_bag_formula (f0 : formula) : formula = match f0 with
  | BForm (bf,lbl) -> BForm (drop_bag_b_formula bf, lbl)
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
  | BForm (bf,lbl) -> (bag_vars_b_formula bf)
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
  | BForm (bf, lbl) -> BForm (b_apply_one_exp (fr, t) bf, lbl)
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
	| RelForm (r, args, pos) -> RelForm (r, e_apply_one_list_exp (fr, t) args, pos) (* An Hoa *)

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
	| ArrayAt (a, i, pos) -> 
            let a1 = if eq_spec_var a fr then (match t with 
               | Var (s,_) -> s
               | _ -> failwith "Can only substitute array variable by array variable\n")  else a in
              ArrayAt (a1, e_apply_one_exp (fr, t) i, pos) (* An Hoa : BUG DETECTED *)

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
  | BForm (f1,lbl) -> BForm(elim_idents_b_formula f1, lbl)

and elim_idents_b_formula (f : b_formula) : b_formula =  match f with
  | Lte (e1, e2, pos)
  | Gte (e1, e2, pos)
  | Eq (e1, e2, pos) ->
  	if (eq_exp_no_aset e1 e2) then BConst(true, pos)
  	else f
  | Neq (e1, e2, pos)
  | Lt (e1, e2, pos)
  | Gt (e1, e2, pos) ->
	if (eq_exp_no_aset e1 e2) then BConst(false, pos)
  	else f
  | _ -> f


let combine_branch b (f, l) =
  match b with 
  | "" -> f
  | s -> try And (f, List.assoc b l, no_pos) with Not_found -> f
;;
(*
let merge_branches_with_common l1 l2 cf =
  let branches = Gen.BList.remove_dups_eq (=) (fst (List.split l1) @ (fst (List.split l2))) in
  let map_fun branch =
    try 
      let l1 = List.assoc branch l1 in
      try
        let l2 = List.assoc branch l2 in
        (branch, mkAnd cf (mkAnd l1 l2 no_pos) no_pos)
      with Not_found -> (branch, mkAnd cf l1 no_pos)
    with Not_found -> (branch, mkAnd cf (List.assoc branch l2) no_pos)
  in
  List.map map_fun branches
;;*)


let merge_branches_with_common l1 l2 cf evars =
  let branches = Gen.BList.remove_dups_eq (=) (fst (List.split l1) @ (fst (List.split l2))) in
  let wrap_exists (l,f) = (l, mkExists evars f None no_pos) in 
  let map_fun branch =
    try 
      let l1 = List.assoc branch l1 in
      try
        let l2 = List.assoc branch l2 in
        (branch, mkAnd cf (mkAnd l1 l2 no_pos) no_pos)
      with Not_found -> (branch, mkAnd cf l1 no_pos)
    with Not_found -> (branch, mkAnd cf (List.assoc branch l2) no_pos)
  in
  List.map (fun c->wrap_exists(map_fun c)) branches
;;


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

let or_branches_old l1 l2 =
  let branches = Gen.BList.remove_dups_eq (=) (fst (List.split l1) @ (fst (List.split l2))) in
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

let or_branches l1 l2 =
  let branches = Gen.BList.remove_dups_eq (=) (fst (List.split l1) @ (fst (List.split l2))) in
  let map_fun branch =
    try 
      let l1 = List.assoc branch l1 in
      try
        let l2 = List.assoc branch l2 in
        (branch, mkOr l1 l2 None no_pos)
      with Not_found -> (branch, mkTrue no_pos)
    with Not_found -> (branch, mkTrue no_pos )
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
	| ListLength _ 
	| ArrayAt _ -> false (* An Hoa *) in
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
	| BForm (b,lbl)-> BForm (helper b neg , lbl)
	| And (b1,b2,l) -> And ((drop_null b1 self neg),(drop_null b2 self neg),l)
	| Or _ -> f
	| Not (b,lbl,l)-> Not ((drop_null b self (not neg)),lbl,l)
	| Forall (q,f,lbl,l) -> Forall (q,(drop_null f self neg),lbl,l)
	| Exists (q,f,lbl,l) -> Exists (q,(drop_null f self neg),lbl,l)
	      
and add_null f self : formula =  
  mkAnd f (BForm (mkEq (Var (self,no_pos)) (Null no_pos) no_pos , None)) no_pos	  
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
  | BForm (b,_) -> [b]
  | And (b1,b2,_)-> (b_form_list b1)@(b_form_list b2)
  | Or _ -> []
  | Not _ -> []
  | Forall (_,f,_,_)
  | Exists (_,f,_,_) -> (b_form_list f)
        
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
	  |  ListLength (_, l) 
		|  ArrayAt (_, _, l) (* An Hoa *) -> 
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
		|  ArrayAt (a, i, l) -> ((Some e), None) (* An Hoa *)

(* 
   lhs-lsm = rhs-rsm   ==> lhs+rsm = rhs+lsm 
*)
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

(* 
   lhs-lsm = max(rhs-rsm,qhs-qsm) 
   ==> lhs+rsm+qsm = max(rhs+lsm+qsm,qhs+lsm+rsm) 
*)
and move_lr3 (lhs :  exp option) (lsm :  exp option)
      (rhs :  exp option) (rsm :  exp option) (qhs :  exp option) (qsm :  exp option) loc :
      ( exp *  exp * exp) =
  let rec add e ls = match e,ls with
    | None,[] -> IConst (0, loc)
    | Some e,[] -> e
    | None,l::ls ->  add (Some l) ls 
    | Some e,l::ls ->  add (Some (Add (e,l,loc))) ls in
  let rl,ql = match lsm with
    | None -> [],[]
    | Some e -> [e],[e] in
  let ll,ql = match rsm with
    | None -> [],ql
    | Some e -> [e],e::ql in
  let ll,rl = match qsm with
    | None -> ll,rl
    | Some e -> e::ll,e::rl in
  (add lhs ll, add rhs rl, add qhs ql)

(* TODO : must elim some multiply for MONA *)
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
                      | _ -> if (v1=2) then Add(t2,t2,l)
                        else Mult (t1, t2, l)
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
                            else if (v2 = 2) then Add(t2,t2,l)
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
	|  ArrayAt (a, i, l) -> ArrayAt (a, purge_mult i, l) (* An Hoa *)

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
  let do_all3 e1 e2 e3 l =
	let t1 = simp_mult e1 in
    let t2 = simp_mult e2 in
    let t3 = simp_mult e3 in
    let (lhs, lsm) = split_sums t1 in
    let (rhs, rsm) = split_sums t2 in
    let (qhs, qsm) = split_sums t3 in
    let ((lh,rh,qh),flag) =
      match (lhs,rhs,qhs,lsm,rsm,qsm) with
          (* -x = max(-y,-z) ==> x = min(y,z) *)
        | None,None,None,Some lh,Some rh, Some qh -> ((lh,rh,qh),false)
        | _,_,_,_,_,_ -> (move_lr3 lhs lsm rhs rsm qhs qsm l,true) in
	let lh = purge_mult lh in
	let rh = purge_mult rh in
	let qh = purge_mult qh in
	(lh, rh, qh,flag) in
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
           let lh,rh,qh,flag = do_all3 e1 e2 e3 l in
           if flag then EqMax (lh,rh,qh,l)
           else EqMin (lh,rh,qh,l)
			   (* let ne1 = simp_mult e1 in *)
			   (* let ne2 = simp_mult e2 in *)
			   (* let ne3 = simp_mult e3 in *)
			   (* let ne1 = purge_mult ne1 in *)
			   (* let ne2 = purge_mult ne2 in *)
			   (* let ne3 = purge_mult ne3 in *)
			   (* (\*if (!Tpdispatcher.tp == Tpdispatcher.Mona) then*\) *)
			   (*      let (s1, m1) = split_sums ne1 in *)
			   (*    	let (s2, m2) = split_sums ne2 in *)
			   (*    	let (s3, m3) = split_sums ne3 in *)
			   (*    	begin *)
			   (*    	match (s1, s2, s3, m1, m2, m3) with *)
			   (*    		| None, None, None, None, None, None ->  BConst (true, l) *)
			   (*    		| Some e11, Some e12, Some e13, None, None, None ->  *)
			   (*    			let e11 = purge_mult e11 in *)
			   (*    			let e12 = purge_mult e12 in *)
			   (*    			let e13 = purge_mult e13 in *)
			   (*    			 EqMax (e11, e12, e13, l) *)
			   (*    		| None, None, None, Some e11, Some e12, Some e13 ->  *)
			   (*    			let e11 = purge_mult e11 in *)
			   (*    			let e12 = purge_mult e12 in *)
			   (*    			let e13 = purge_mult e13 in *)
			   (*    			 EqMin (e11, e12, e13, l) *)
			   (*    		| _ ->  *)
			   (*    			  EqMax (ne1, ne2, ne3, l) *)
			   (*    	end *)
			   (*else 
             	 EqMax (ne1, ne2, ne3, l)*)
    |  EqMin (e1, e2, e3, l) ->
           let lh,rh,qh,flag = do_all3 e1 e2 e3 l in
           if flag then EqMin (lh,rh,qh,l)
           else EqMax (lh,rh,qh,l)
			   (* let ne1 = simp_mult e1 in *)
			   (* let ne2 = simp_mult e2 in *)
			   (* let ne3 = simp_mult e3 in *)
			   (* let ne1 = purge_mult ne1 in *)
			   (* let ne2 = purge_mult ne2 in *)
			   (* let ne3 = purge_mult ne3 in *)
			   (* (\*if (!Tpdispatcher.tp == Tpdispatcher.Mona) then*\) *)
			   (*      let (s1, m1) = split_sums ne1 in *)
			   (*    	let (s2, m2) = split_sums ne2 in *)
			   (*    	let (s3, m3) = split_sums ne3 in *)
			   (*    	begin *)
			   (*    	match (s1, s2, s3, m1, m2, m3) with *)
			   (*    		| None, None, None, None, None, None ->  BConst (true, l) *)
			   (*    		| Some e11, Some e12, Some e13, None, None, None ->  *)
			   (*    				let e11 = purge_mult e11 in *)
			   (*    				let e12 = purge_mult e12 in *)
			   (*    				let e13 = purge_mult e13 in *)
			   (*    				 EqMin (e11, e12, e13, l) *)
			   (*    		| None, None, None, Some e11, Some e12, Some e13 ->  *)
			   (*    				let e11 = purge_mult e11 in *)
			   (*    				let e12 = purge_mult e12 in *)
			   (*    				let e13 = purge_mult e13 in *)
			   (*    				 EqMax (e11, e12, e13, l) *)
			   (*    		| _ ->  EqMin (ne1, ne2, ne3, l) *)
			   (*    	end *)
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
				 |  RelForm _ -> b (* An Hoa TODO implement *) 
           
(* a+a    --> 2*a
   1+3    --> 4
   1+x>-2 --> 3+x>0
*)  

and arith_simplify (i:int) (pf : formula) :  formula =   
  Gen.Debug.no_1 ("arith_simplify LHS"^(string_of_int i)) !print_formula !print_formula 
      arith_simplify_x pf


and arith_simplify_x (pf : formula) :  formula =   
  let rec helper pf = match pf with
    |  BForm (b,lbl) -> BForm (b_form_simplify b,lbl)
    |  And (f1, f2, loc) -> And (helper f1, helper f2, loc)
    |  Or (f1, f2, lbl, loc) -> Or (helper f1, helper f2, lbl, loc)
    |  Not (f1, lbl, loc) ->  Not (helper f1, lbl, loc)
    |  Forall (v, f1, lbl, loc) ->  Forall (v, helper f1, lbl, loc)
    |  Exists (v, f1, lbl, loc) ->  Exists (v, helper f1, lbl, loc)
  in helper pf
	  
let rec get_pure_label n =  match n with
  | And _ -> None
  | BForm (_,l) 
  | Or (_,_,l,_) 
  | Not (_,l,_) 
  | Forall (_,_,l,_) 
  | Exists (_,_,l,_) -> l

let select zs n = 
  let l = List.length zs in
  (List.nth zs (n mod l))


(* decided to drop zero since same as f_comb e [] *)

let foldr_exp (e:exp) (arg:'a) (f:'a->exp->(exp * 'b) option) 
      (f_args:'a->exp->'a)(f_comb:exp -> 'b list -> 'b) 
      :(exp * 'b) =
  let rec helper (arg:'a) (e:exp) : (exp * 'b)=
    let r =  f arg e  in 
    match r with
	  | Some ne -> ne
	  | None ->  let new_arg = f_args arg e in 
        let f_comb = f_comb e in match e with
	      | Null _ 
	      | Var _ 
	      | IConst _
	      | FConst _ -> (e,f_comb [])
	      | Add (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Add (ne1,ne2,l),f_comb[r1;r2])
	      | Subtract (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Subtract (ne1,ne2,l),f_comb[r1;r2])
	      | Mult (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Mult (ne1,ne2,l),f_comb[r1;r2])
	      | Div (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Div (ne1,ne2,l),f_comb[r1;r2])
	      | Max (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Max (ne1,ne2,l),f_comb[r1;r2])
	      | Min (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Min (ne1,ne2,l),f_comb[r1;r2])
	      | Bag (le,l) -> 
                let el=List.map (fun c-> helper new_arg c) le in
                let (el,rl)=List.split el in 
		        (Bag (el, l), f_comb rl) 
	      | BagUnion (le,l) -> 
                let el=List.map (fun c-> helper new_arg c) le in
                let (el,rl)=List.split el in 
		        (BagUnion (el, l), f_comb rl) 		                
	      | BagIntersect (le,l) -> 
                let el=List.map (fun c-> helper new_arg c) le in
                let (el,rl)=List.split el in 
		        (BagIntersect (el, l), f_comb rl) 
		            (*(BagIntersect (List.map (fun c-> helper new_arg c) le, l))*)
	      | BagDiff (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
                let (ne2,r2) = helper new_arg e2 in
                (BagDiff (ne1,ne2,l),f_comb[r1;r2])
          | List (e1,l) -> (* List (( List.map (helper new_arg) e1), l)*) 
                let el=List.map (fun c-> helper new_arg c) e1 in
                let (el,rl)=List.split el in 
		        (List (el, l), f_comb rl) 
          | ListCons (e1,e2,l) -> 
                let (ne1,r1) = helper new_arg e1 in
                let (ne2,r2) = helper new_arg e2 in
                (ListCons (ne1,ne2,l),f_comb[r1;r2])
          | ListHead (e1,l) -> 
                let (ne1,r1) = helper new_arg e1 in
                (ListHead (ne1,l),f_comb [r1])
          | ListTail (e1,l) -> 
                let (ne1,r1) = helper new_arg e1 in
                (ListTail (ne1,l),f_comb [r1])
          | ListLength (e1,l) -> 
                let (ne1,r1) = helper new_arg e1 in
                (ListLength (ne1,l),f_comb [r1])
          | ListAppend (e1,l) ->  
                let el=List.map (fun c-> helper new_arg c) e1 in
                let (el,rl)=List.split el in 
		        (ListAppend (el, l), f_comb rl) 
          | ListReverse (e1,l) -> 
                let (ne1,r1) = helper new_arg e1 in
                (ListReverse (ne1,l),f_comb [r1])
				  | ArrayAt (a, i, l) -> (* An Hoa *)
	            let (ne1,r1) = helper new_arg i in
		        	(ArrayAt (a,ne1,l),f_comb [r1])
  in helper arg e

let trans_exp (e:exp) (arg:'a) (f:'a->exp->(exp * 'b) option) 
      (f_args:'a->exp->'a)(f_comb: 'b list -> 'b) 
      :(exp * 'b) =
  foldr_exp e arg f f_args (fun x l -> f_comb l) 

let fold_exp (e: exp) (f: exp -> 'b option) (f_comb: 'b list -> 'b) : 'b =
  let new_f a e = push_opt_val_rev (f e) e in
  snd (trans_exp e () new_f voidf2 f_comb)

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
				| ArrayAt (a, i, l) -> ArrayAt (a, (transform_exp f i), l) (* An Hoa *)

let foldr_b_formula (e:b_formula) (arg:'a) f f_args f_comb
      (*(f_comb:'b list -> 'b)*) :(b_formula * 'b) =
  let (f_b_formula, f_exp) = f in
  let (f_b_formula_args, f_exp_args) = f_args in
  let (f_b_formula_comb, f_exp_comb) = f_comb in
  let helper (arg:'a) (e:exp) : (exp * 'b)= foldr_exp e arg f_exp f_exp_args f_exp_comb in
  let helper2 (arg:'a) (e:b_formula) : (b_formula * 'b) =
	let r =  f_b_formula arg e in 
	match r with
	  | Some e1 -> e1
	  | None  -> let new_arg = f_b_formula_args arg e in 
        let f_comb = f_b_formula_comb e in
        match e with	  
	      | BConst _
	      | BVar _ 
	      | BagMin _ 
	      | BagMax _ -> (e,f_comb [])
	      | Lt (e1,e2,l) ->
		        let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Lt (ne1,ne2,l),f_comb[r1;r2])
	      | Lte (e1,e2,l) ->
		        let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Lte (ne1,ne2,l),f_comb[r1;r2])
	      | Gt (e1,e2,l) ->
		        let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Gt (ne1,ne2,l),f_comb[r1;r2])
	      | Gte (e1,e2,l) ->
		        let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Gte (ne1,ne2,l),f_comb[r1;r2])
	      | Eq (e1,e2,l) ->
		        let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Eq (ne1,ne2,l),f_comb[r1;r2])
	      | Neq (e1,e2,l) ->
		        let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (Neq (ne1,ne2,l),f_comb[r1;r2])
	      | EqMax (e1,e2,e3,l) ->
		        let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        let (ne3,r3) = helper new_arg e3 in
		        (EqMax (ne1,ne2,ne3,l),f_comb[r1;r2;r3])	  
	      | EqMin (e1,e2,e3,l) ->
		        let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        let (ne3,r3) = helper new_arg e3 in
		        (EqMin (ne1,ne2,ne3,l),f_comb[r1;r2;r3])
		            (* bag formulas *)
	      | BagIn (v,e,l)->
		        let (ne1,r1) = helper new_arg e in
		        (BagIn (v,ne1,l),f_comb [r1])
	      | BagNotIn (v,e,l)->
		        let (ne1,r1) = helper new_arg e in
		        (BagNotIn (v,ne1,l),f_comb [r1])
	      | BagSub (e1,e2,l) ->
		        let (ne1,r1) = helper new_arg e1 in
		        let (ne2,r2) = helper new_arg e2 in
		        (BagSub (ne1,ne2,l),f_comb[r1;r2])
          | ListIn (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
                let (ne2,r2) = helper new_arg e2 in
                (ListIn (ne1,ne2,l),f_comb[r1;r2])
          | ListNotIn (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
                let (ne2,r2) = helper new_arg e2 in
                (ListNotIn (ne1,ne2,l),f_comb[r1;r2])
          | ListAllN (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
                let (ne2,r2) = helper new_arg e2 in
                (ListAllN (ne1,ne2,l),f_comb[r1;r2])
          | ListPerm (e1,e2,l) ->
	            let (ne1,r1) = helper new_arg e1 in
                let (ne2,r2) = helper new_arg e2 in
                (ListPerm (ne1,ne2,l),f_comb[r1;r2])
					| RelForm (r, args, l) -> (* An Hoa *)
					    let tmp = List.map (helper new_arg) args in
							let nargs = List.map fst tmp in
							let rs = List.map snd tmp in
                (RelForm (r,nargs,l),f_comb rs)
  in (helper2 arg e)


let trans_b_formula (e:b_formula) (arg:'a) f 
      f_args (f_comb: 'b list -> 'b) :(b_formula * 'b) =
  foldr_b_formula e arg f f_args  ((fun x l -> f_comb l), (fun x l -> f_comb l)) 

let map_b_formula_arg (bf: b_formula) (arg: 'a) (f_bf, f_e) f_arg : b_formula =
  let trans_func f = (fun a e -> push_opt_void_pair (f a e)) in
  let new_f = trans_func f_bf, trans_func f_e in
  fst (trans_b_formula bf arg new_f f_arg voidf)
	
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
		| RelForm (r, args, l) -> (* An Hoa *)
			let nargs = List.map (transform_exp f_exp) args in
			RelForm (r,nargs,l)
	  
let foldr_formula (e: formula) (arg: 'a) f f_arg f_comb : (formula * 'b) =
    let f_formula, f_b_formula, f_exp = f in
    let f_formula_arg, f_b_formula_arg, f_exp_arg = f_arg in
    let f_formula_comb, f_b_formula_comb, f_exp_comb = f_comb in
    let foldr_b_f (arg: 'a) (e: b_formula): (b_formula * 'b) =
        foldr_b_formula e arg (f_b_formula, f_exp) (f_b_formula_arg, f_exp_arg) (f_b_formula_comb, f_exp_comb)
    in
    let rec foldr_f (arg: 'a) (e: formula): (formula * 'b) =
        let r = f_formula arg e in
        match r with
        | Some e1 -> e1
        | None ->
            let new_arg = f_formula_arg arg e in
            let f_comb = f_formula_comb e in
            match e with
            | BForm (bf, lbl) ->
                let new_bf, r1 = foldr_b_f new_arg bf in
                (BForm (new_bf, lbl), f_comb [r1])
            | And (f1, f2, l) ->
                let nf1, r1 = foldr_f new_arg f1 in
                let nf2, r2 = foldr_f new_arg f2 in
                (And (nf1, nf2, l), f_comb [r1; r2])
            | Or (f1, f2, lbl, l) ->
                let nf1, r1 = foldr_f new_arg f1 in
                let nf2, r2 = foldr_f new_arg f2 in
                (Or (nf1, nf2, lbl, l), f_comb [r1; r2])
            | Not (f1, lbl, l) ->
                let nf1, r1 = foldr_f new_arg f1 in
                (Not (nf1, lbl, l), f_comb [r1])
            | Forall (sv, f1, lbl, l) ->
                let nf1, r1 = foldr_f new_arg f1 in
                (Forall (sv, nf1, lbl, l), f_comb [r1])
            | Exists (sv, f1, lbl, l) ->
                let nf1, r1 = foldr_f new_arg f1 in
                (Exists (sv, nf1, lbl, l), f_comb [r1])
    in foldr_f arg e

(* f = (f_f, f_bf, f_e) and
 * f_f: 'a -> formula -> (formula * 'b) option
 * f_bf: 'a -> b_formula -> (b_formula * 'b) option
 * f_e: 'a -> exp -> (exp * 'b) option
 *)
let trans_formula (e: formula) (arg: 'a) f f_arg f_comb : (formula * 'b) =
    let f_comb = (fun x l -> f_comb l), 
                 (fun x l -> f_comb l),
                 (fun x l -> f_comb l)
    in
    foldr_formula e arg f f_arg f_comb

(* compute a result from formula with argument
 * f_f: 'a -> formula -> 'b option
 * f_bf: 'a -> b_formula -> 'b option
 * f_e: 'a -> exp -> 'b option
 *)
let fold_formula_arg (e: formula) (arg: 'a) (f_f, f_bf, f_e) f_arg (f_comb: 'b list -> 'b) : 'b =
    let trans_func func = (fun a e -> push_opt_val_rev (func a e) e) in
    let new_f = trans_func f_f, trans_func f_bf, trans_func f_e in
    snd (trans_formula e arg new_f f_arg f_comb)

(* compute a result from formula without passing an argument
 * f_f: formula -> 'b option
 * f_bf: b_formula -> 'b option
 * f_e: exp -> 'b option
 *)
let fold_formula (e: formula) (f_f, f_bf, f_e) (f_comb: 'b list -> 'b) : 'b =
    let trans_func func = (fun _ e -> push_opt_val_rev (func e) e) in
    let new_f = trans_func f_f, trans_func f_bf, trans_func f_e in
    let f_arg = voidf2, voidf2, voidf2 in
    snd (trans_formula e () new_f f_arg f_comb)

(* map functions to formula with argument
 * f_f: 'a -> formula -> formula option
 * f_bf: 'a -> b_formula -> b_formula option
 * f_e: 'a -> exp -> exp option
 *)
let map_formula_arg (e: formula) (arg: 'a) (f_f, f_bf, f_e) f_arg : formula =
    let trans_func f = (fun a e -> push_opt_void_pair (f a e)) in
    let new_f = trans_func f_f, trans_func f_bf, trans_func f_e in
    fst (trans_formula e arg new_f f_arg voidf)

(* map functions to formula without argument
 * f_f: formula -> formula option
 * f_bf: b_formula -> b_formula option
 * f_e: exp -> exp option
 *)
let map_formula (e: formula) (f_f, f_bf, f_e) : formula =
    let trans_func f = (fun _ e -> push_opt_void_pair (f e)) in
    let new_f = trans_func f_f, trans_func f_bf, trans_func f_e in
    let f_arg = idf2, idf2, idf2 in
    fst (trans_formula e () new_f f_arg voidf)

let rec transform_formula f (e:formula) :formula = 
	let (_ , _, f_formula, f_b_formula, f_exp) = f in
	let r =  f_formula e in 
	match r with
	| Some e1 -> e1
	| None  -> match e with
		  | BForm (b1,b2) -> 
				BForm ((transform_b_formula (f_b_formula, f_exp) b1) ,b2)
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
		| BForm (b,f_l) -> Some (BForm (b,(n_l_f f_l)))
		| And (e1,e2,l) -> None
		| Or (e1,e2,f_l,l) -> (Some (Or (e1,e2,(n_l_f f_l),l)))
		| Not (e1,f_l, l) -> (Some (Not (e1,(n_l_f f_l),l)))
		| Forall (v,e1,f_l, l) -> (Some (Forall (v,e1,(n_l_f f_l),l)))
		| Exists (v,e1,f_l, l) -> (Some (Exists (v,e1,(n_l_f f_l),l)))in			
	transform_formula ((fun _-> None),(fun _-> None), f_f,f_b,f_e) e
			
let remove_dup_constraints (f:formula):formula = 
  (*let f = elim_idents f in*)
  let l_conj = split_conjunctions f in
  let prun_l = Gen.BList.remove_dups_eq equalFormula l_conj in
  join_conjunctions prun_l

let rec get_head e = match e with 
    | Null _ -> "Null"
    | Var (v,_) -> name_of_spec_var v
    | IConst (i,_)-> string_of_int i
    | FConst (f,_) -> string_of_float f
    | Add (e,_,_) | Subtract (e,_,_) | Mult (e,_,_) | Div (e,_,_)
    | Max (e,_,_) | Min (e,_,_) | BagDiff (e,_,_) | ListCons (e,_,_)| ListHead (e,_) 
    | ListTail (e,_)| ListLength (e,_) | ListReverse (e,_)  -> get_head e
    | Bag (e_l,_) | BagUnion (e_l,_) | BagIntersect (e_l,_) | List (e_l,_) | ListAppend (e_l,_)-> 
      if (List.length e_l)>0 then get_head (List.hd e_l) else "[]"
		| ArrayAt (a, i, _) -> "" (* An Hoa *) 

let form_bform_eq (v1:spec_var) (v2:spec_var) =
   Eq(Var(v1,no_pos),Var(v2,no_pos),no_pos)

let form_formula_eq (v1:spec_var) (v2:spec_var) =
  BForm (form_bform_eq v1 v2, None)
   
let is_zero b =   match b with
    | IConst(0,_) -> true
    | _ -> false

let is_one b =   match b with
    | IConst(1,_) -> true
    | _ -> false

let simple el = List.length el <=1

let addlist_to_exp (el:exp list) : exp = 
  let el = List.sort (fun e1 e2 -> String.compare (get_head e2) (get_head e1)) el in
  match el with
    | [] -> IConst(0,no_pos)
    | e::es -> List.fold_left (fun ac e1 -> Add(e1,ac,no_pos) ) e es 

let e_cmp e1 e2 =  String.compare (get_head e1) (get_head e2) 
 
let two_args e1 e2 isOne f loc=
        if isOne e1 then e2
        else if is_one e2 then e1
        else if (e_cmp e1 e2)<0 then f(e1,e2,loc) else f(e2,e1,loc)


(* normalize add/sub expression *)
let rec simp_addsub e1 e2 loc =
  let (lhs,rhs)=norm_two_sides e1 e2 in
  match rhs with
    | IConst(0,_) -> lhs
    | _ -> Subtract(lhs,rhs,loc)

(* normalise and simplify expression *)
(* add to take a v->c eq_map *)
(* and norm_exp_aux (e:exp) = match e with  *)

and norm_exp (e:exp) = 
  let _ = print_string "\n !!!!!!!!!!!!!!!! norm exp aux \n" in
  let rec helper e = match e with
    | Var _ 
    | Null _ | IConst _ | FConst _ -> e
    | Add (e1,e2,l) -> simp_addsub e (IConst(0,no_pos)) l 
    | Subtract (e1,e2,l) -> simp_addsub e1 e2 l 
    | Mult (e1,e2,l) -> 
          let e1=helper e1 in 
          let e2=helper e2 in
          if (is_zero e1 || is_zero e2) then IConst(0,l)
          else two_args (helper e1) (helper e2) is_one (fun x -> Mult x) l
    | Div (e1,e2,l) -> if is_one e2 then e1 else Div (helper e1,helper e2,l)
    | Max (e1,e2,l)-> two_args (helper e1) (helper e2) (fun _ -> false) (fun x -> Max x) l
    | Min (e1,e2,l) -> two_args (helper e1) (helper e2) (fun _ -> false) (fun x -> Min x) l
    | Bag (e,l)-> Bag ( List.sort e_cmp (List.map helper e), l)    
    | BagUnion (e,l)-> BagUnion ( List.sort e_cmp (List.map helper e), l)    
    | BagIntersect (e,l)-> BagIntersect ( List.sort e_cmp (List.map helper e), l)    
    | BagDiff (e1,e2,l) -> BagDiff (helper e1, helper e2, l)
    | List (e,l)-> List (List.sort e_cmp (List.map helper e), l)    
    | ListCons (e1,e2,l)-> ListCons(helper e1, helper e2,l)      
    | ListHead (e,l)-> ListHead(helper e, l)      
    | ListTail (e,l)-> ListTail(helper e, l)      
    | ListLength (e,l)-> ListLength(helper e, l)
    | ListAppend (e,l) -> ListAppend ( List.sort e_cmp (List.map helper e), l)    
    | ListReverse (e,l)-> ListReverse(helper e, l) 
		| ArrayAt (a, i, l) -> ArrayAt (a, helper i, l) (* An Hoa *) in
  helper e

(* if v->c, replace v by the constant whenever encountered 
   normalise each sub-expresion only once please.
*)
(* normalise add/subtract on both lhs (e1) and rhs (e2) *)
and norm_two_sides (e1:exp) (e2:exp)   =
  let rec help_add e s pa sa c  = match e with
    | Subtract (e1,e2,l) -> help_add e1 (Add(e2,s,l)) pa sa c
    | IConst(i,_)  -> help_sub s pa sa (c+i) 
    | Add (Add(e1,e2,l1),e3,l2) -> help_add (Add(e1,Add(e2,e3,no_pos),l2)) s pa sa c
    | Add (IConst(i,l1),e,l2) -> help_add e s pa sa (c+i) 
    | Add (Subtract(e1,e2,l1),e3,l2) -> help_add (Add(e1,e3,l2)) (Add(e2,s,no_pos)) pa sa c
    | Add (e1,e2,l1) -> help_add e2 s (e1::pa) sa c (* normalise e1, is e1=c? *)
    | e1 -> help_sub s (e1::pa) sa c (* normalise e1, is e1=c? *)
  and help_sub e pa sa c  = match e with
    | IConst(i,_)  -> (pa, sa,c-i)
    | Subtract (e1,e2,l)  -> help_add e2 e1 pa sa c
    | Add (Add(e1,e2,l1),e3,l2) -> help_sub (Add(e1,Add(e2,e3,no_pos),l2)) pa sa c
    | Add (IConst(i,l1),e,l2) -> help_sub e pa sa (c-i) 
    | Add (Subtract(e1,e2,l1),e3,l2) -> help_add e2 (Add(e1,e3,l2))  pa sa c
    | Add (e1,e2,l1) -> help_sub e2 pa (e1::sa) c (* normalise e1, is e1=c? *)
    | e1 -> (pa, e1::sa, c) in (* normalise e1, is e1=c? *)
  let (lhs,rhs,i) = help_add e1 e2 [] [] 0 in
  (* let (lhs,rhs) = (List.map norm_exp lhs, List.map norm_exp rhs) in *)
  if (lhs==[]) then (IConst(i,no_pos),addlist_to_exp rhs)
  else if (rhs==[]) then  (addlist_to_exp lhs, IConst(-i,no_pos))
  else if (i==0) then (addlist_to_exp lhs, addlist_to_exp rhs)
  else if (simple rhs) then (Add(IConst(i,no_pos),addlist_to_exp lhs,no_pos),addlist_to_exp rhs)
  else (addlist_to_exp lhs, Add(IConst(-i,no_pos),addlist_to_exp rhs,no_pos))
      
let norm_bform_leq (e1:exp)  (e2:exp) loc : b_formula = 
  let (lhs,rhs) = norm_two_sides e1 e2 in
   Lte(lhs,rhs,loc)

let norm_bform_eq (e1:exp)  (e2:exp) loc : b_formula = 
  let (lhs,rhs) = norm_two_sides e1 e2 in
   Eq(lhs,rhs,loc)

let norm_bform_neq (e1:exp)  (e2:exp) loc : b_formula = 
  let (lhs,rhs) = norm_two_sides e1 e2 in
   Neq(lhs,rhs,loc)

let simp_bform simp bf =
  let f_b e = None in
  let f_e e = match e with
    | Var _ -> Some (simp e)
    | _ -> None in
  transform_b_formula (f_b,f_e) bf

(* normalise and simplify b_formula *)
let norm_bform_a (bf:b_formula) : b_formula =
  (*let bf = b_form_simplify bf in *)
  match bf with 
      | Lt  (e1,e2,l) -> norm_bform_leq (Add(e1,IConst(1,no_pos),l)) e2 l
      | Lte (e1,e2,l) -> norm_bform_leq e1 e2 l
      | Gt  (e1,e2,l) -> norm_bform_leq (Add(e2,IConst(1,no_pos),l)) e1 l
      | Gte (e1,e2,l) ->  norm_bform_leq e2 e1 l
      | Eq  (e1,e2,l) -> norm_bform_eq e1 e2 l
      | Neq (e1,e2,l) -> norm_bform_neq e1 e2 l 
      | BagIn (v,e,l) -> BagIn (v, norm_exp e, l)
      | BagNotIn (v,e,l) -> BagNotIn (v, norm_exp e, l)
      | ListIn (e1,e2,l) -> ListIn (norm_exp e1,norm_exp e2,l)
      | ListNotIn (e1,e2,l) -> ListNotIn (norm_exp e1,norm_exp e2,l)
      | BConst _ | BVar _ | EqMax _ 
      | EqMin _ |  BagSub _ | BagMin _ 
      | BagMax _ | ListAllN _ | ListPerm _ 
			| RelForm _ -> bf (* An hoa *)

let norm_bform_aux (bf:b_formula) : b_formula = norm_bform_a bf

let norm_bform_opt bf =
  match bf with
    | BConst _ | BVar _ | EqMax _ 
    | EqMin _ |  BagSub _ | BagMin _ 
    | BagMax _ | ListAllN _ | ListPerm _ -> None 
    | _ -> Some bf 

let norm_bform_option (bf:b_formula) =
  let bf=norm_bform_aux bf in
  norm_bform_opt bf


let norm_bform_option_debug (bf:b_formula) : b_formula option =
  let r = norm_bform_aux bf in
  let _ = print_string ("norm_bform inp :"^(!print_b_formula bf)^"\n") in
  let _ = print_string ("norm_bform out :"^(!print_b_formula r)^"\n") in
  norm_bform_opt r

(* name prefix for int const *)
let const_prefix = "__CONST_Int_"

let const_prefix_len = String.length(const_prefix)

(* get string name of var e *)
let string_of_var_eset e : string =
  EMapSV.string_of e


let get_sub_debug s n m =
  let _ = print_string ("get_sub inp:"^s^";"^(string_of_int n)^";"^(string_of_int m)^"\n") in
  let r = String.sub s n m in
  let _ = print_string ("get_sub out:"^r^"\n") in
  r


(* is string a int const, n is prefix length *)
let is_int_str_aux (n:int) (s:string) : bool =
  if (n<=const_prefix_len) then false
  else 
    let p = String.sub s 0 const_prefix_len in
    if (p=const_prefix) then true
    else false


(* get int value if it is an int_const *)
let get_int_const (s:string) : int option =
  let n=String.length s in
  if (is_int_str_aux n s) then
    let c = String.sub s const_prefix_len (n-const_prefix_len) in
    try Some (int_of_string c) 
    with _ -> None (* should not be possible *)
  else None

(* check if a string denotes an int_const *)
let is_int_str (s:string) : bool =
  let n=String.length s in
    is_int_str_aux n s

(* check if a string is a null const *)
let is_null_str (s:string) : bool = (s="null")


(* is string a constant?  *)
let is_const (s:spec_var) : bool = 
  let n = name_of_spec_var s in
  (is_null_str n) || (is_int_str n)

(* is string a constant?  *)
let is_null_const (s:spec_var) : bool = 
  let n = name_of_spec_var s in
  (is_null_str n) 

(* is string an int constant?  *)
let is_int_const (s:spec_var) : bool = 
  let n = name_of_spec_var s in
     (is_int_str n)

let conv_var_to_exp (v:spec_var) :exp =
  if (full_name_of_spec_var v="null") then (Null no_pos)
  else match get_int_const (name_of_spec_var v) with
    | Some i -> IConst(i,no_pos)
    | None -> Var(v,no_pos)

let conv_var_to_exp_debug (v:spec_var) :exp =
 Gen.Debug.no_1 "conv_var_to_exp" (full_name_of_spec_var) (!print_exp) conv_var_to_exp v

(* is exp a var  *)
let is_var (f:exp) = match f with
  | Var _ -> true
  | _ -> false  

(* get args from a bform formula *)
let get_bform_eq_args_aux conv (bf:b_formula) =
  match bf with
    | Eq(e1,e2,_) -> 
          let ne1=conv e1 in 
          let ne2=conv e2 in
          (match ne1,ne2 with
            | Var(v1,_),Var(v2,_) -> Some (v1,v2)
            | _, _ -> None)
    | _-> None     

(* get arguments of an eq formula *)
let get_bform_eq_args (bf:b_formula) =
  get_bform_eq_args_aux (fun x -> x) bf

let mk_sp_const (i:int) = 
          let n= const_prefix^(string_of_int i)
          in SpecVar ((Int), n , Unprimed) 

let conv_exp_to_var (e:exp) : (spec_var * loc) option = 
  match e with
    | IConst(i,loc) -> Some (mk_sp_const i,loc)
    | Null loc -> Some (null_var,loc)
    | _ -> None

(* convert exp to var representation where possible *)
let conv_exp_with_const e = match conv_exp_to_var e with
    | Some (v,loc) -> Var(v,loc)
    | _ -> e

(* get arguments of bformula and allowing constants *)
let get_bform_eq_args_with_const (bf:b_formula) =
   get_bform_eq_args_aux conv_exp_with_const bf

let get_bform_eq_args_with_const_debug (bf:b_formula) =
   Gen.Debug.no_1 " get_bform_eq_args_with_const" (!print_b_formula) (fun _ -> "?") get_bform_eq_args_with_const bf

(* form bformula assuming only vars *)
let form_bform_eq (v1:spec_var) (v2:spec_var) =
  let conv v = Var(v,no_pos) in
  if ((is_const v1) || (is_const v2)) then              
    Error.report_error  {
        Error.error_loc = no_pos;
        Error.error_text =  "form_bform_eq : adding an equality with a constant"; }
  else Eq(conv v1,conv v2,no_pos)

(* form bformula allowing constants to be converted *)
let form_bform_eq_with_const (v1:spec_var) (v2:spec_var) =
  let conv v = conv_var_to_exp v
  in Eq(conv v1,conv v2,no_pos)

(* form an equality formula assuming vars only *)
let form_formula_eq (v1:spec_var) (v2:spec_var) =
  BForm (form_bform_eq v1 v2, None)

(* form an equality formula and allowing constants *)
let form_formula_eq_with_const (v1:spec_var) (v2:spec_var) : formula =
  BForm (form_bform_eq_with_const v1 v2, None)
 
(* get args of a equality formula *)
let get_bform_eq_args_debug (bf:b_formula) : (spec_var * spec_var) option =
  let s="get_bform_eq_args " in
  let s="DEBUG "^s in
  let r=get_bform_eq_args bf in
  let _ = print_string (s^"inp:"^(!print_b_formula bf)^"\n") in
  let _ = match r with 
    | Some (v1,v2) -> let o=form_bform_eq v1 v2 in
      print_string (s^"out:"^(!print_b_formula o)^"\n") 
    | None ->  print_string (s^"out: None \n")
  in r

(* no constant must be added when adding equiv *)
let add_equiv_eq a v1 v2 = 
 if (is_const v1)||(is_const v2) then
    Error.report_error  {
        Error.error_loc = no_pos;
        Error.error_text =  "add_equiv_eq bug : adding an equality with a constant"; }
 else EMapSV.add_equiv a v1 v2

let add_equiv_eq_debug a v1 v2 = 
  let _ = print_string ("add_equiv_eq inp1 :"^(string_of_var_eset a)^"\n") in
  let _ = print_string ("add_equiv_eq inp2 :"^(full_name_of_spec_var v1)^","^(name_of_spec_var v2)^"\n") in
   let ax = add_equiv_eq a v1 v2 in
  let _ = print_string ("add_equiv_eq out :"^(string_of_var_eset ax)^"\n") in
  ax

(* constant may be added to map*)
let add_equiv_eq_with_const a v1 v2 = EMapSV.add_equiv a v1 v2

let add_equiv_eq_with_const_debug a v1 v2 = 
  let _ = print_string ("add_equiv_eq_with_const inp1 :"^(string_of_var_eset a)^"\n") in
  let _ = print_string ("add_equiv_eq_with_const inp2 :"^(full_name_of_spec_var v1)^","^(name_of_spec_var v2)^"\n") in
   let ax = add_equiv_eq_with_const a v1 v2 in
  let _ = print_string ("add_equiv_eq_with_const out :"^(string_of_var_eset ax)^"\n") in
  ax

(* get arguments of an equality formula *)
let get_formula_eq_args (f:formula) =
  match f with
    | BForm(bf,_) -> get_bform_eq_args bf
    | _ -> None

let get_formula_eq_args_debug_add bf =
  let _=print_string ("Adding") in
  get_bform_eq_args_debug bf

let get_formula_eq_args_debug_chk bf =
  let _=print_string ("Checking") in
  get_bform_eq_args_debug bf

(* get var elements from a eq-map but remove constants *)
let get_elems_eq aset =
  let vl=EMapSV.get_elems aset in
    List.filter (fun v -> not(is_const v)) vl

(* get var elements from a eq-map allowing constants *)
let get_elems_eq_with_const aset =
  let vl=EMapSV.get_elems aset in
    List.filter (fun v -> true) vl

(* let get_elems_eq_with_const_debug aset = *)
(*   Gen.Debug.no_1_list "get_elems_eq_with_const" (string_of_var_eset) (full_name_of_spec_var) get_elems_eq_with_const aset *)

(* get var elements from a eq-map allowing null *)
let get_elems_eq_with_null aset =
  let vl=EMapSV.get_elems aset in
    List.filter (fun v -> not(is_int_const v)) vl

(* below is for Andreea to implement,
   likely to require Util

*)

(* creates a false aset*)
let mkFalse_var_aset = add_equiv_eq_with_const EMapSV.mkEmpty  (mk_sp_const 0) (mk_sp_const 3)

(**)	
let get_bform_eq_vars (bf:b_formula) : (spec_var * spec_var) option =
     match bf with 
        | Eq(Var(v1,_),Var(v2,_),_) -> Some (v1,v2)
		| _ -> None

(* normalise eq_map - to implement*)
(* remove duplicate occurrences of a var in a partition, 
   check singleton & remove
   check false by presence of duplicate constants --> change to 1=0
   
   @return: var_aset - normalized eq
			 bool(1) - flag that tells if the eq has changed
			 bool(2) - flag that tells if there is a conflict in the eq
*)

let normalise_eq_aux ( aset : var_aset) : var_aset * bool * bool= 
  let plst = EMapSV.partition aset in
  let (nlst,flag) = List.fold_left 
    (fun (rl,f) l -> 
       let nl=remove_dups_svl l in
	 (nl::rl,(f||not((List.length nl)==(List.length l))))) 
    ([],false) plst in
  let (nlst2,flag2) = List.fold_left 
    (fun (rl,f) ls -> 
       if (List.length ls<=1) then (rl,true)
       else (ls::rl,f))
    ([],flag) nlst in
  let is_conflict = List.fold_left 
    (fun f ls -> 
       (f || (let cl= List.filter (fun v -> is_const v) ls in (List.length cl)>1)))
    false nlst2 
  in
    if is_conflict then (mkFalse_var_aset, true, true)
    else
      ((EMapSV.un_partition nlst2),flag2, false)


(* return the normalized eq *)
let normalise_eq (aset : var_aset) : var_aset = 
  let (r, _, _) = normalise_eq_aux aset in r

(* print if there was a change in state check - *)
let normalise_eq_debug (aset : var_aset) : EMapSV.emap =
 let ax, change, _ = normalise_eq_aux aset in
 (if change then
	let _ = print_string ("normalise_eq inp :"^(string_of_var_eset aset)^"\n") in
	print_string ("partition_eq out :"^(string_of_var_eset ax)^"\n"));
 (ax)

(* check if an eq_map has a contradiction - to implement *)
(* call normalised_eq and check if equal to 1=0 *)
(* @return: bool - flag that tells if there is a conflict in the eq 
			var_aset - normalized eq *)
let is_false_and_normalise_eq (aset : var_aset) : bool * var_aset =
	let (ax, _, conflict) = normalise_eq_aux aset in (conflict, ax) 
	
(* print if false detected - when debugging *)
let is_false_and_normalise_eq_debug (aset : var_aset) : bool * var_aset = 
  let (ax, _, conflict) = normalise_eq_aux aset in
  let _ = print_string ("normalise_eq inp :"^(string_of_var_eset aset) ^ "\n") in
  let _ = print_string ("partition_eq out :"^(string_of_var_eset ax) ^ "\n") in
  let _ = print_string ("conflict in eq: " ^ (string_of_bool conflict) ^ "\n") in
  (conflict, ax)

(* check if an eq_map has a contradiction*)
(* call normalised_eq and check if equal to 1=0 *)
let is_false_eq (aset : var_aset) : bool = 
	let (_, _, conflict) = normalise_eq_aux aset in conflict

(* check if v is a constant*)
(* return a list with all constant having the same key as v*)
let get_all_const_eq (aset : var_aset) (v : spec_var) : spec_var list =
  let nlst = EMapSV.find_equiv_all v aset in
  List.filter (is_const) nlst

(* check if v is an int constant and return its value, if so - to implement *)
(* use get_var_const *)
(* return i if i_const found *)
(* report error if wrong type found *)
let conv_var_to_exp_eq (aset : var_aset) (v:spec_var) : exp = 
  let nlst = get_all_const_eq aset v in
  match nlst with
    | [] -> Var(v,no_pos)
    | hd::_ -> conv_var_to_exp hd

(*Convert an expresion to another expresion after replacing the variables representing constants*)
let conv_exp_to_exp_eq aset e : exp =
  match e with
    | Var(v,_) -> let r = conv_var_to_exp_eq aset v in
      if not(r==e) then ((Gen.Profiling.add_to_counter "var_changed_2_const" 1); r)
      else r
    | _ -> e

(* check if v is null - to implement *)
let is_null_var_eq (aset : var_aset) (v:spec_var) : bool = 
  let nlst = get_all_const_eq aset v in
  List.exists (is_null_const) nlst


let string_of_var_list l : string =
  Gen.BList.string_of_f name_of_spec_var l

let string_of_p_var_list l : string =
  Gen.BList.string_of_f (fun (v1,v2) -> "("^(full_name_of_spec_var v1)^","^(full_name_of_spec_var v2)^")") l

(* get two lists - no_const & with_const *)
let get_equiv_eq_split aset =
  let vl=EMapSV.get_equiv aset in
    List.partition (fun (v1,v2) -> not(is_const v1) && not(is_const v2) ) vl

(* get eq pairs without const *)
let get_equiv_eq_no_const aset =
  let vl=EMapSV.get_equiv aset in
  List.filter (fun (v1,v2) -> not(is_const v1) && not(is_const v2) ) vl

(* get all eq pairs *)
let get_equiv_eq_all aset =
  let vl=EMapSV.get_equiv aset in vl

(* get eq pairs without const *)
let get_equiv_eq aset = get_equiv_eq_no_const  aset

(* get eq pairs without int const *)
let get_equiv_eq_with_null aset =
  let vl=EMapSV.get_equiv aset in
    List.filter (fun (v1,v2) -> not(is_int_const v1) && not(is_int_const v2) ) vl

(* get eq pairs without int const *)
let get_equiv_eq_with_const aset =
  let vl=EMapSV.get_equiv aset in
    List.filter (fun (v1,v2) -> true ) vl

let get_equiv_eq_with_const_debug aset =
  let ax = get_equiv_eq_with_const aset in
  let _ = print_string ("get_equiv_eq_with_const inp :"^(string_of_var_eset aset)^"\n") in
  let _ = print_string ("get_equiv_eq_with_const out :"^(string_of_p_var_list ax)^"\n") in
  ax

(*
(* return constant int for e *)
let find_int_const_eq2  (eq:'a->'a->bool) (str:'a->string) (e:'a) (s:'a e_set) : int option  =
  let r1 = find_eq2 eq s e in
  if (r1==[]) then None
  else let ls = List.filter (fun (a,k) -> k==r1 && (is_int_const (str a))  ) s in
  match ls with
    | [] -> None 
    | (x,_)::_ -> get_int_const x

*)


let is_leq eq e1 e2 =
  match e1,e2 with
    | IConst (i1,_), IConst(i2,_) -> i1<=i2
    | _,_ -> eqExp_f eq e1 e2

let is_lt eq e1 e2 =
  match e1,e2 with
    | IConst (i1,_), IConst(i2,_) -> i1<i2
    | _,_ -> false

let is_diff e1 e2 =
  match e1,e2 with
    | IConst (i1,_), IConst(i2,_) -> i1<>i2
    | _,_ -> false

(* lhs |- e1<=e2 *)
let check_imply_leq eq lhs e1 e2 =
  let rec helper l = match l with
    | [] -> -1
    | a::ls -> if helper2 a then 1 else helper ls
  and helper2 a = match a with
    | Eq(d1,d2,_) ->          
          if eqExp_f eq d1 e1 then is_leq eq d2 e2 
          else if eqExp_f eq d2 e2 then is_leq eq e1 d1 
          else helper2 (Lte(d2,d1,no_pos))
    | Lte(d1,d2,_) -> 
          if eqExp_f eq d1 e1 then is_leq eq d2 e2 
          else if eqExp_f eq d2 e2 then is_leq eq e1 d1 
          else false
    | _ -> false
  in helper lhs

(* lhs |- e1=e2 *)
let check_imply_eq eq lhs e1 e2 = 
  let rec helper l = match l with
    | [] -> -1
    | a::ls -> if helper2 a then 1 else helper ls
  and helper2 a = match a with
    | Eq(d1,d2,_) ->          
          (eqExp_f eq d1 e1 && eqExp_f eq d2 e2) ||
              (eqExp_f eq d1 e2 && eqExp_f eq d2 e1)
    | _ -> false
  in if ((eqExp_f eq) e1 e2) then 1
  else helper lhs 

(* lhs |- e1!=e2 *)
let check_imply_neq eq lhs e1 e2 = 
 let rec helper l = match l with
    | [] -> -1
    | a::ls -> if helper2 a then 1 else helper ls
  and helper2 a = match a with
    | Eq(d1,d2,_) ->          
        if eqExp_f eq d1 e1 then (is_lt eq d2 e2) || (is_lt eq e2 d2)
        else if eqExp_f eq d2 e2 then (is_lt eq e1 d1) || (is_lt eq d1 e1)
          else helper2 (Lte(d2,d1,no_pos))
     (*((eqExp_f eq d1 e1) && (is_diff d2 e2)) || ((eqExp_f eq d2 e2) && (is_diff e1 d1)) ||
     ((eqExp_f eq d2 e1) && (is_diff d1 e2)) || ((eqExp_f eq d1 e2) && (is_diff e1 d2)) ||
     (helper2 (Lte(d2,d1,no_pos)))*)
    | Lte(d1,d2,_) -> 
          if eqExp_f eq d1 e1 then is_lt eq d2 e2 
          else if eqExp_f eq d2 e2 then is_lt eq e1 d1 
          else if eqExp_f eq d1 e2 then is_lt eq d2 e1 
          else if eqExp_f eq d2 e1 then is_lt eq e2 d1 
          else 
          false
    | _ -> false
  in if ((eqExp_f eq) e1 e2) then -2
  else helper lhs 
let check_imply_neq_debug eq lhs e1 e2 = 
Gen.Debug.no_3 
    "check_imply_neq" 
    (fun c-> String.concat "&" (List.map !print_b_formula c))
    !print_exp 
    !print_exp 
    string_of_int (check_imply_neq eq ) lhs e1 e2

let check_eq_bform eq lhs rhs failval = 
  if List.exists (equalBFormula_f eq rhs) lhs then 1
  else failval

(* assume b_formula has been normalized 
     1 - true
     0 - dont know
     -1 - likely false
    -2 - definitely false
*)

let fast_imply (aset: var_aset) (lhs: b_formula list) (rhs: b_formula) : int =
  (*let _ = print_string "\n fast_imply \n" in*)
  (* let _ = Gen.Profiling.push_time "fast_imply" in *)
  (*normalize lhs and rhs*)
  let simp e = conv_exp_to_exp_eq aset e in
  let normsimp lhs rhs =
    let _ = Gen.Profiling.push_time "fi-normsimp" in
    let lhs = List.map (fun e -> norm_bform_a(simp_bform simp e)) lhs in
    let rhs = norm_bform_a( simp_bform simp rhs) in
    let _ = Gen.Profiling.pop_time "fi-normsimp" in
    (lhs,rhs) in
  let lhs,rhs = if !Globals.enable_norm_simp then normsimp lhs rhs 
  else (lhs,rhs)
  in
  let r = 
    let eq x y = EMapSV.is_equiv aset x y in
    let r1=check_eq_bform eq lhs rhs 0 in
    if (r1>0) then r1
    else 
      match rhs with
        | BConst(true,_) -> 1
        | Lte(e1,e2,_) -> check_imply_leq eq lhs e1 e2
        | Eq(e1,e2,_) -> check_imply_eq eq lhs e1 e2
        | Neq(e1,e2,_) -> check_imply_neq eq lhs e1 e2
        | EqMin _ | EqMax _ (* min/max *) -> 0
        | Lt _ | Gt _ | Gte _ -> (* RHS not normalised *) 
              let _ = print_string "warning fast_imply : not normalised"
              in 0
        | _ -> (* use just syntactic checking *) 0 in
  let _ = if r>0 then (Gen.Profiling.add_to_counter "fast_imply_success" 1) else () in
  (* let _  = Gen.Profiling.pop_time "fast_imply" in *) r

let fast_imply a l r = Gen.Profiling.do_3 "fast_imply" fast_imply a l r




let fast_imply aset (lhs:b_formula list) (rhs:b_formula) : int =
  let pr1 = !print_b_formula in
(*    let _ = print_string ("fast imply aset :"^(EMapSV.string_of aset)^"\n") in*)
  Gen.Debug.no_2 "fast_imply" (pr_list pr1) pr1 string_of_int (fun _ _ -> fast_imply aset lhs rhs) lhs rhs
  

let rec replace_pure_formula_label nl f = match f with
  | BForm (bf,_) -> BForm (bf,(nl()))
  | And (b1,b2,b3) -> And ((replace_pure_formula_label nl b1),(replace_pure_formula_label nl b2),b3)
  | Or (b1,b2,b3,b4) -> Or ((replace_pure_formula_label nl b1),(replace_pure_formula_label nl b2),(nl()),b4)
  | Not (b1,b2,b3) -> Not ((replace_pure_formula_label nl b1),(nl()),b3)
  | Forall (b1,b2,b3,b4) -> Forall (b1,(replace_pure_formula_label nl b2),(nl()),b4)
  | Exists (b1,b2,b3,b4) -> Exists (b1,(replace_pure_formula_label nl b2),(nl()),b4)

  
let rec imply_disj_orig ante_disj conseq t_imply imp_no =
  match ante_disj with
    | h :: rest -> 
	    let r1,r2,r3 = (t_imply h conseq (string_of_int !imp_no) true None) in
	    if r1 then 
	      let r1,r22,r23 = (imply_disj_orig rest conseq t_imply imp_no) in
	      (r1,r2@r22,r23)
	    else (r1,r2,r3)
    | [] -> (true,[],None)
  
let rec imply_one_conj_orig ante_disj0 ante_disj1 conseq t_imply imp_no = 
  (*let _ = print_string ("\nSplitting the antecedent for xpure0:\n") in*)
  let xp01,xp02,xp03 = imply_disj_orig ante_disj0 conseq t_imply imp_no in  
  (*let _ = print_string ("\nDone splitting the antecedent for xpure0:\n") in*)
  if (not(xp01) (*&& (ante_disj0 <> ante_disj1)*)) then
    let _ = Debug.devel_pprint ("\nSplitting the antecedent for xpure1:\n") in
    (* let _ = print_string ("\nimply_one_conj xp1 #" ^ (string_of_int !imp_no) ^ "\n") in *)
    let xp1 = imply_disj_orig ante_disj1 conseq t_imply imp_no in
    let _ = Debug.devel_pprint ("\nDone splitting the antecedent for xpure1:\n") in
	xp1
  else (xp01,xp02,xp03)	
  
let rec imply_conj_orig ante_disj0 ante_disj1 conseq_conj t_imply imp_no
   : bool * (Globals.formula_label option * Globals.formula_label option) list * Globals.formula_label option = 
  match conseq_conj with
    | h :: rest -> 
	    let (r1,r2,r3)=(imply_one_conj_orig ante_disj0 ante_disj1 h t_imply imp_no) in
	    if r1 then 
	      let r1,r22,r23 = (imply_conj_orig ante_disj0 ante_disj1 rest t_imply imp_no) in
	      (r1,r2@r22,r23)
	    else (r1,r2,r3)
    | [] -> (true,[],None)
(*###############################################################################  incremental_testing*)
(*check implication having a single formula on the lhs and a conjuction of formulas on the rhs*)
let rec imply_conj (send_ante: bool) ante conseq_conj t_imply (increm_funct :(formula) Globals.incremMethodsType option) process imp_no =
  (* let _ = print_string("\nCpure.ml: imply_conj") in *)
  match conseq_conj with
    | h :: rest ->
	      let r1,r2,r3 = (t_imply ante h (string_of_int !imp_no) true ( Some (process, send_ante))) in
          (* let _ = print_string("\nCpure.ml: h:: rest "^(string_of_bool r1)) in *)
          if r1 then
            let send_ante = if (!Globals.enable_incremental_proving) then false
            else send_ante in
	        let r1,r22,r23 = (imply_conj send_ante ante rest t_imply increm_funct process imp_no) in
	        (r1,r2@r22,r23)
	      else (r1,r2,r3)
    | [] -> (* let _ = print_string("\nCpure.ml: []")  in*) (true,[],None)

let rec imply_disj_helper ante_disj conseq_conj t_imply (increm_funct: (formula) Globals.incremMethodsType option) process imp_no
      : bool * (Globals.formula_label option * Globals.formula_label option) list * Globals.formula_label option =
  match ante_disj with
    | h :: rest ->
          (* let _ = print_string("\nCpure.ml: bef imply_conj ") in *)
	      let (r1,r2,r3) = (imply_conj true(*<-send_ante*) h conseq_conj t_imply increm_funct process imp_no) in
          (* let _ = print_string("\nCpure.ml: affer imply_conj " ^(string_of_bool r1)) in *)
	      if r1 then
	        let r1,r22,r23 = (imply_disj_helper rest conseq_conj t_imply increm_funct process imp_no) in
	        (r1,r2@r22,r23)
	      else (r1,r2,r3)
    | [] -> (true,[],None)

let imply_disj ante_disj0 ante_disj1 conseq_conj t_imply (increm_funct: (formula) Globals.incremMethodsType option) imp_no
      : bool * (Globals.formula_label option * Globals.formula_label option) list * Globals.formula_label option =
  (* let _ = print_string ("\nCpure.ml: CVC3 create process") in *)
  let start = ref false in
  let process = 
    match increm_funct with
      | Some ifun ->
            let proc0 = ifun#get_process() in 
            let proc = match proc0 with
              |Some pr -> pr
              |None -> (start :=true; ifun#start_p ()) in
            let _ = ifun#push proc in
            Some proc
      | None -> None in
  let xp01,xp02,xp03 = imply_disj_helper ante_disj0 conseq_conj t_imply increm_funct process imp_no in
  let r = if ( not(xp01) ) then begin (*xpure0 fails to prove. try xpure1*)
    let _ = Debug.devel_pprint ("\nSplitting the antecedent for xpure1:\n") in
    let r1 = imply_disj_helper ante_disj1 conseq_conj t_imply increm_funct process imp_no in
    let _ = Debug.devel_pprint ("\nDone splitting the antecedent for xpure1:\n") in
    r1
  end else (xp01, xp02, xp03) in
  let _ =
    match (increm_funct, process, !start) with
      | (Some ifun, Some proc, true) -> ifun#stop_p proc
        (* let _ = print_string("\nCpure.ml: stop process") in  *)
      | (_, _, _) -> () in
  (* let _ = print_string ("\nCpure.ml: CVC3 stop process \n\n") in *)
  r

(*###############################################################################  *)
    
(* added for better normalization *)

type exp_form = 
  | C of int 
  | V of spec_var 
  | E of exp

type add_term = (int * exp_form)  
(* e.g i*e; special case of constant i*1  3*v  4*(a*b) *)

type mult_term = (exp_form * int) 
(* e^i; special case c^1 or c^-1*)

    (* [2v,3,5v,6ab,..] *)
type add_term_list = add_term list (* default [] means 0 *)
type mult_term_list = mult_term list (* default [] means 1 *)

let mk_err s = Error.report_error
          { Error.error_loc = no_pos;
            Error.error_text = s } 

(* to be implemented : use GCD, then simplify fraction *)
let simp_frac c1 c2 = (c1,c2)

let gen_iconst (c1:int) (c2:int) : mult_term_list =
  let (d1,d2) = simp_frac c1 c2 in
  if (d1==1) then
    if (d2==1) then [] else [(C d2,-1)]
  else   
    if (d2==1) then [(C d1,1)] else [(C d1,1);(C d2,-1)]

let gen_var (v:spec_var) (c:int) : mult_term_list =
  if c==0 then [] else [(V v,c)]

let gen_exp (e:exp) (c:int) : mult_term_list =
  if c==0 then [] else [(E e,c)]

let mul_zero = [(C 0,1)]

let gen_add_exp (e:exp) (c:int) : add_term_list =
  if c==0 then [] else [(c,E e)]

let gen_add_var (e:spec_var) (c:int) : add_term_list =
  if c==0 then [] else [(c,V e)]

let gen_add_iconst (c:int) : add_term_list =
  if c==0 then [] else [(c,C 1)]

(* to be implemented *)
let eq_exp e1 e2 = false

let spec_var_cmp v1 v2 = String.compare (full_name_of_spec_var v1) (full_name_of_spec_var v2)

let cmp_term x y = match x,y with
    | C _, C _ -> 0
    | C _, _ -> -1
    | _ , C _ -> 1
    | V v1 , V v2 -> String.compare (full_name_of_spec_var v1) (full_name_of_spec_var v2)
    | V v , _ -> -1
    | _ , V v -> 1
    | E e1 , E e2 -> 0 (* to refine *)

let sort_add_term (xs:add_term_list) : add_term_list =
  let cmp (_,x) (_,y) = cmp_term x y
  in List.sort cmp xs

let cmp_mult_term (mt1: mult_term) (mt2: mult_term): int =
  let x, i1 = mt1 in
  let y, i2 = mt2 in
  let r = cmp_term x y in 
  if r == 0 then 
    compare i1 i2
  else r 

let sort_mult_term (xs:mult_term_list) : mult_term_list =
  List.sort cmp_mult_term xs

(* pre : c1!=0 *)
let rec norm_add_c (c1:int) (xs:add_term_list) : add_term_list =
  match xs with
    | [] -> gen_add_iconst c1
    | (i,C _)::xs -> norm_add_c (c1+i) xs
    | _ :: _ -> (gen_add_iconst c1)@norm_add xs

and norm_add_v c v (xs:add_term_list)  : add_term_list= 
  match xs with
    | [] -> gen_add_var v c
    | (i,V v1)::xs -> 
          if eq_spec_var v v1 then norm_add_v (i+c) v xs
          else (gen_add_var v c)@norm_add_v i v1 xs
    | _::_ -> (gen_add_var v c)@norm_add xs

and norm_add_e c e (xs:add_term_list) : add_term_list= 
  match xs with
    | [] -> gen_add_exp e c
    | (i,E e1)::xs -> 
          if eq_exp e e1 then norm_add_e (i+c) e xs
          else (gen_add_exp e c)@norm_add_e i e1  xs
    | _::_ -> (gen_add_exp e c)@norm_add xs

(* add_term_list --> add_term_list 
   2+3x+4x+4xy --> 2+7x+4xy
*)

and norm_add xs =
  match xs with 
    | [] -> []
    | (i,C _)::xs -> norm_add_c i xs
    | (i,V v)::xs -> norm_add_v i v xs
    | (i,E e)::xs -> norm_add_e i e xs

(* pre : c1!=0 *)
let rec norm_mult_c (c1:int) (c2:int) (xs:mult_term_list) : mult_term_list =
  match xs with
    | [] -> gen_iconst c1 c2
    | (C c,v)::xs -> 
          if c==0 then mul_zero else
            if v==1 then norm_mult_c (c*c1) c2 xs
            else norm_mult_c c1 (c2*c) xs
    | _ :: _ -> (gen_iconst c1 c2)@norm_mult xs
          
and norm_mult_v v c (xs:mult_term_list)  : mult_term_list= 
  match xs with
    | [] -> gen_var v c
    | (V v1,c1)::xs -> 
          if eq_spec_var v v1 then norm_mult_v v (c+c1) xs
          else (gen_var v c)@norm_mult_v v1 c1 xs
    | _::_ -> (gen_var v c)@norm_mult xs

and norm_mult_e e c (xs:mult_term_list) : mult_term_list= 
  match xs with
    | [] -> gen_exp e c
    | (E e1,c1)::xs -> 
          if eq_exp e e1 then norm_mult_e e (c+c1) xs
          else (gen_exp e c)@norm_mult_e e1 c1 xs
    | _::_ -> (gen_exp e c)@norm_mult xs

and norm_mult xs =
  match xs with 
    | [] -> []
    | (C c,b)::xs -> 
          if c==0 then mul_zero else
	        if b==1 then norm_mult_c c 1 xs
	        else norm_mult_c 1 c xs
    | (V v,p)::xs -> norm_mult_v v p xs
    | (E e,p)::xs -> norm_mult_e e p xs

(* converts add_ter -> exp *)
         
(* pre : no negative signs
   converts [add_term] -> exp *)
let add_term_to_exp (xs:add_term_list) : exp =
  let to_exp (i,e) =
    if (i<0) then mk_err "add_term has -ve sign" else
    match e with
      | C _ -> IConst(i,no_pos)
      | V v -> if (i==1) then Var(v,no_pos)
        else Mult(IConst(i,no_pos),Var(v,no_pos),no_pos)
      | E e -> if (i==1) then e
        else Mult (IConst(i,no_pos),e,no_pos) in 
  match xs with
    | [] -> IConst (0,no_pos)
    | x::xs -> List.fold_left (fun e r -> 
          let e2=to_exp r in Add (e,e2,no_pos)) (to_exp x) xs

(* pre : no negative powers
   converts [mult_term] -> exp *)
let mult_term_to_exp (xs:mult_term_list) : exp =
  let rec power e i = if i==1 then e else Mult(e,power e (i-1), no_pos) in
  let to_exp (e,i) =
    if (i<0) then mk_err "mult_term has -ve power" else
      match e with
        | C c -> IConst(c,no_pos)
        | V v -> power (Var(v,no_pos)) i
        | E e -> power e i in
  match xs with
    | [] -> IConst (1,no_pos)
    | x::xs -> List.fold_left (fun e r -> 
          let e2=to_exp r in Mult(e,e2,no_pos)) (to_exp x) xs

let split_add_term (xs:add_term_list) : (add_term_list * add_term_list) = List.partition (fun (i,_) -> i>0) xs

let split_mult_term (xs:mult_term_list) : (mult_term_list * mult_term_list)  = List.partition (fun (_,i) -> i>0) xs

let op_inv rs = List.map (fun (x,i) -> (x,-i)) rs
let op_neg rs = List.map (fun (i,x) -> (-i,x)) rs
let op_mult r1 r2 = r1@r2
let op_div r1 r2 = r1@(op_inv r2)

let op_add r1 r2 = r1@r2
let op_sub r1 r2 = op_add r1 (op_neg r2)

(* move to util.ml later *)
let assoc_op_part (split:'a -> 'a list) (comb: 'a -> ('b list) list -> 'b list)
      (base:'a->'b list) (e:'a) : 'b list =
  let rec helper e =
    match (split e) with
      | [] -> base e
      | xs -> let r = List.map (helper) xs in
        comb e r
  in helper e


(* (e1*e2)/(e3*e4) ==> [e1^1,e2^1,e3^-1,e4^-1] *)

let assoc_mult (e:exp) : mult_term_list =
  let split e = match e with
    | Mult (e1,e2,_) -> [e1;e2]
    | Div (e1,e2,_) -> [e1;e2]
    | _ -> [] in
  let comb e args = match (e,args) with
    | (Mult _,[r1;r2]) -> op_mult r1 r2
    | (Div _,[r1;r2]) -> op_div r1 r2
    | _,_ ->  mk_err "comb assoc_mult : mismatch number of arguments! " in
  let base e = match e with
    | IConst (i,_) -> [(C i,1)]
    | Var (v,_)  -> [(V v, 1)]
    | e      -> [(E e,1)]
  in assoc_op_part split comb base  e

let normalise_mult (e:exp) : exp =
  let al=assoc_mult e
  in mult_term_to_exp(norm_mult (sort_mult_term al))

(* (e1+e2)-(e3+e4) ==> [e1,e2,-e3,-e4] *)

let assoc_add (e:exp) : add_term_list =
  let  split e = match e with
    | Add (e1,e2,_) -> [e1;e2]
    | Subtract (e1,e2,_) -> [e1;e2]
    (* | Neg (e1,_) -> [e1] *)
    | _ -> [] in
  let comb e args = match e, args with
    | Add _,[r1;r2] -> op_add r1 r2
    | Subtract _,[r1;r2] -> op_sub r1 r2
    (* | Neg _,[r] -> op_neg r *)
    | _ -> mk_err "comb in assoc_add : mismatch number of arguments! " in
  let base e = match e with
    | IConst (i,_) -> [(i, C 1)]
    | Var (v,_)  -> [(1, V v)]
    | e      -> let e1=normalise_mult e in [(1, E e1)]
  in assoc_op_part split comb base  e

let normalise_add (e:exp) : exp =
  let al=assoc_add e
  in add_term_to_exp(norm_add (sort_add_term al))

let normalise_two_sides (e1:exp) (e2:exp) : (exp * exp) =
  let a1=assoc_add e1 in
  let a2=assoc_add e2 in
  let al=op_sub a1 a2 in
  let al=norm_add(sort_add_term al) in
  let (r1,r2)=List.partition (fun (i,_) -> i>=0) al in
   ((add_term_to_exp r1),(add_term_to_exp r2))

let assoc_min (e:exp) : add_term_list list =
  let  split e = match e with
    | Min (e1,e2,_) -> [e1;e2]
    | _ -> [] in
  let comb e args = match e, args with
    | Min _,[r1;r2] -> op_add r1 r2
    | _ -> mk_err "comb in assoc_min : mismatch number of arguments! " in
  let base e = [assoc_add e]
  in assoc_op_part split comb base  e

let assoc_max (e:exp) : add_term_list list =
  let  split e = match e with
    | Max (e1,e2,_) -> [e1;e2]
    | _ -> [] in
  let comb e args = match e, args with
    | Max _,[r1;r2] -> op_add r1 r2
    | _ -> mk_err "comb in assoc_max : mismatch number of arguments! " in
  let base e = [assoc_add e]
  in assoc_op_part split comb base  e

(* normalise and simplify b_formula *)
let norm_bform_b (bf:b_formula) : b_formula =
  (*let bf = b_form_simplify bf in *)
  match bf with 
    | Lt  (e1,e2,l) -> 
          let e1= (Add(e1,IConst(1,no_pos),l)) in 
          let (e1,e2) = normalise_two_sides e1 e2 in
          norm_bform_leq e1 e2 l 
    | Lte (e1,e2,l) -> 
          let (e1,e2) = normalise_two_sides e1 e2 in
          norm_bform_leq e1 e2 l 
    | Gt  (e1,e2,l) -> 
          let e1,e2= (Add(e2,IConst(1,no_pos),l),e1) in 
          let (e1,e2) = normalise_two_sides e1 e2 in
          norm_bform_leq e1 e2 l 
    | Gte (e1,e2,l) ->  
          let (e1,e2) = normalise_two_sides e2 e1 in
          norm_bform_leq e1 e2 l 
    | Eq  (e1,e2,l) -> 
          let (e1,e2) = normalise_two_sides e1 e2 in
          norm_bform_eq e1 e2 l 
    | Neq (e1,e2,l) -> 
          let (e1,e2) = normalise_two_sides e1 e2 in
          norm_bform_neq e1 e2 l  
    | BagIn (v,e,l) -> BagIn (v, norm_exp e, l)
    | BagNotIn (v,e,l) -> BagNotIn (v, norm_exp e, l)
    | ListIn (e1,e2,l) -> ListIn (norm_exp e1,norm_exp e2,l)
    | ListNotIn (e1,e2,l) -> ListNotIn (norm_exp e1,norm_exp e2,l)
    | BConst _ | BVar _ | EqMax _ 
    | EqMin _ |  BagSub _ | BagMin _ 
    | BagMax _ | ListAllN _ | ListPerm _ 
		| RelForm _ -> bf 

(***********************************
 * aggressive simplify and normalize
 * of arithmetic formulas
 **********************************)
module ArithNormalizer = struct

  (* 
   * Printing functions, mainly here for debugging purposes
   *)
  let rec string_of_exp e0 =
    let need_parentheses e = match e with
      | Add _ | Subtract _ -> true
      | _ -> false
    in let wrap e =
      if need_parentheses e then "(" ^ (string_of_exp e) ^ ")"
      else (string_of_exp e)
    in
    match e0 with
    | Null _ -> "null"
    | Var (v, _) -> string_of_spec_var v
    | IConst (i, _) -> string_of_int i
    | FConst (f, _) -> string_of_float f
    | Add (e1, e2, _) -> (string_of_exp e1) ^ " + " ^ (string_of_exp e2)
    | Subtract (e1, e2, _) -> (string_of_exp e1) ^ " - " ^ (string_of_exp e2)
    | Mult (e1, e2, _) -> (wrap e1) ^ "*" ^ (wrap e2)
    | Div (e1, e2, _) -> (wrap e1) ^ "/" ^ (wrap e2)
    | Max (e1, e2, _) -> "max(" ^ (string_of_exp e1) ^ "," ^ (string_of_exp e2) ^ ")"
    | Min (e1, e2, _) -> "min(" ^ (string_of_exp e1) ^ "," ^ (string_of_exp e2) ^ ")"
    | _ -> "???"
    
  let string_of_b_formula bf = 
    let build_exp e1 e2 op =
      (string_of_exp e1) ^ op ^ (string_of_exp e2)
    in match bf with
      | BConst (b, _) -> (string_of_bool b)
      | BVar (bv, _) -> (string_of_spec_var bv) ^ " > 0"
      | Lt (e1, e2, _) -> build_exp e1 e2 " < "
      | Lte (e1, e2, _) -> build_exp e1 e2 " <= "
      | Gt (e1, e2, _) -> build_exp e1 e2 " > "
      | Gte (e1, e2, _) -> build_exp e1 e2 " >= "
      | Eq (e1, e2, _) -> build_exp e1 e2 " = "
      | Neq (e1, e2, _) -> build_exp e1 e2 " != "
      | EqMax (e1, e2, e3, _) ->
          (string_of_exp e1) ^ " = max(" ^ (string_of_exp e2) ^ "," ^ (string_of_exp e3) ^ ")"
      | EqMin (e1, e2, e3, _) ->
          (string_of_exp e1) ^ " = min(" ^ (string_of_exp e2) ^ "," ^ (string_of_exp e3) ^ ")"
      | _ -> "???"

  let rec string_of_formula f0 = match f0 with
    | BForm (b, _) -> string_of_b_formula b
    | And (f1, f2, _) -> 
        let wrap f = match f with
          | Or _ | BForm _ -> "(" ^ (string_of_formula f) ^ ")"
          | _ -> string_of_formula f
        in
        (wrap f1) ^ " and " ^ (wrap f2)
    | Or (f1, f2, _, _) -> 
        let wrap f = match f with
          | And _ | BForm _ -> "(" ^ (string_of_formula f) ^ ")"
          | _ -> string_of_formula f
        in
        (wrap f1) ^ " or " ^ (wrap f2)
    | Not (f1, _, _) -> "not(" ^ (string_of_formula f1) ^ ")"
    | Forall (sv, f1, _, _) -> "all(" ^ (string_of_spec_var sv) ^ ", " ^ (string_of_formula f1) ^ ")"
    | Exists (sv, f1, _, _) -> "ex(" ^ (string_of_spec_var sv) ^ ", " ^ (string_of_formula f1) ^ ")"

  type add_term = int * mult_term_list

  type add_term_list = add_term list (* default [] means 0 *)

  let neg_add_term_list (terms: add_term_list) =
    List.map (fun (i, x) -> (-i, x)) terms

  let mult_2_add_terms (t1: add_term) (t2: add_term) : add_term =
    let i1, mt1 = t1 in
    let i2, mt2 = t2 in
    (i1*i2, mt1@mt2)

  (*
   * create a add_terms list from given exp
   * faltten the expression by distributing all multiplications over addition sub-exp
   * e.g.:
   *   a*(b+c) -> a*b + a*c
   *   (a+b)*(c+d) -> a*c + a*d + b*c + b*d
   *)
  let rec explode_exp (e: exp) : add_term_list = match e with
    | Add (e1, e2, _) -> (explode_exp e1) @ (explode_exp e2)
    | Subtract (e1, e2, _) -> (explode_exp e1) @ (neg_add_term_list (explode_exp e2))
    | Mult (e1, e2, _) ->
        let terms1 = explode_exp e1 in
        let terms2 = explode_exp e2 in
        List.flatten (List.map (fun t -> List.map (mult_2_add_terms t) terms2) terms1)
    | Div (e1, e2, _) -> [1, [E e, 1]] (* FIXME: to be implemented *)
    | Null _ -> []
    | Var (sv, _) -> [1, [V sv, 1]]
    | IConst (i, _) -> [1, [C i, 1]]
    | _ -> [1, [E e, 1]]

  (* convert a m_add_term to corresponding exp form 
   * also simplify the case coeff = 0 or 1 and empty mult_terms list
   *)
  let add_term_to_exp (term: add_term) : exp =
    let i, mtl = term in
    if i = 0 || mtl = [] then 
      IConst (i, no_pos)
    else if i = 1 then
      mult_term_to_exp mtl
    else
      Mult (IConst (i, no_pos), mult_term_to_exp mtl, no_pos)

  (* convert a list of add_terms back to correspondding exp form *)
  let rec add_term_list_to_exp (terms: add_term_list) : exp =
    match terms with
    | [] -> IConst (0, no_pos)
    | [term] -> add_term_to_exp term
    | head::tail -> 
        let i, mtl = head in
        if i = 0 then
          add_term_list_to_exp tail
        else
          Add (add_term_to_exp head, add_term_list_to_exp tail, no_pos)

  (* compare two lists
   * most significant item is the head of the list
   * list with smaller length will be considered less than the other
   *)
  let rec cmp_list (l1: 'a list) (l2: 'a list) (fcmp: 'a -> 'a -> int) : int =
    match l1, l2 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | h1::r1, h2::r2 ->
        let cmp_head = fcmp h1 h2 in
        if cmp_head = 0 then
          cmp_list r1 r2 fcmp
        else cmp_head

  let norm_add_term (term: add_term) : add_term =
    let i, mlist = term in
    let normalized_mult_terms = norm_mult (sort_mult_term mlist) in
    let res = match normalized_mult_terms with
      | (C c, _)::r -> (i*c, r)
      | _ -> (i, normalized_mult_terms)
    in res

  (* sort the list of add_terms after normalizing each m_add_term
   *)
  let sort_add_term_list (terms: add_term_list) : add_term_list =
    let cmp (_, x) (_, y) = cmp_list x y cmp_mult_term in
    List.sort cmp (List.map norm_add_term terms)

  let rec norm_add_term_list (terms: add_term_list) : add_term_list =
    let terms = sort_add_term_list terms in
    let rec insert (term: add_term) (termlist: add_term_list) : add_term_list = 
      let i1, mtl1 = term in
      if i1 = 0 then
        termlist
      else
        match termlist with
        | [] -> [term]
        | head::tail ->
            let i2, mtl2 = head in
            if (cmp_list mtl1 mtl2 cmp_mult_term) = 0 then
              insert (i1+i2, mtl1) tail
            else
              term::termlist
    in
    match terms with
      | [] -> []
      | head::tail -> insert head (norm_add_term_list tail)

  let norm_two_sides (e1:exp) (e2:exp) : (exp * exp) =
    let aterms1 = explode_exp e1 in
    let aterms2 = explode_exp e2 in
    let terms = norm_add_term_list (aterms1 @ (neg_add_term_list aterms2)) in
    let lhs_terms, rhs_terms = List.partition (fun (i, _) -> i >= 0) terms in
    let rhs_terms = neg_add_term_list rhs_terms in
    (add_term_list_to_exp lhs_terms), (add_term_list_to_exp rhs_terms)

  let norm_two_sides_debug e1 e2 =
    Gen.Debug.no_2 "cpure::norm_two_sides" string_of_exp string_of_exp 
    (fun (x,y) -> (string_of_exp x) ^ " | " ^ (string_of_exp y))
    norm_two_sides e1 e2

  let norm_exp (e: exp) : exp =
    let term_list = norm_add_term_list (explode_exp e) in
    add_term_list_to_exp term_list

  let norm_exp_debug e =
    Gen.Debug.no_1 "cpure::norm_exp" string_of_exp string_of_exp norm_exp e

  let norm_bform_relation rel e1 e2 l makef = match e1, e2 with
    | IConst (i1, _), IConst (i2, _) -> BConst (rel i1 i2, l)
    | _ -> makef (e1, e2, l)

  let norm_bform_leq e1 e2 l =
    norm_bform_relation (<=) e1 e2 l (fun x -> Lte x)

  let norm_bform_eq e1 e2 l = 
    norm_bform_relation (=) e1 e2 l (fun x -> Eq x)

  let norm_bform_neq e1 e2 l = 
    norm_bform_relation (<>) e1 e2 l (fun x -> Neq x)

  let norm_b_formula (bf: b_formula) : b_formula option = match bf with
    | Lt (e1, e2, l) -> 
        let e1 = Add (e1, IConst(1, no_pos), l) in 
        let lhs, rhs = norm_two_sides e1 e2 in
        Some (norm_bform_leq lhs rhs l)
    | Lte (e1, e2, l) -> 
        let lhs, rhs = norm_two_sides e1 e2 in
        Some (norm_bform_leq lhs rhs l)
    | Gt (e1, e2, l) -> 
        let e1, e2 = Add (e2, IConst(1, no_pos), l), e1 in 
        let lhs, rhs = norm_two_sides e1 e2 in
        Some (norm_bform_leq lhs rhs l)
    | Gte (e1, e2, l) ->  
        let lhs, rhs = norm_two_sides e2 e1 in
        Some (norm_bform_leq lhs rhs l)
    | Eq (e1, e2, l) ->
        let lhs, rhs = norm_two_sides e1 e2 in
        Some (norm_bform_eq lhs rhs l)
    | Neq (e1, e2, l) -> 
        let lhs, rhs = norm_two_sides e1 e2 in
        Some (norm_bform_neq lhs rhs l)
    | _ -> None

  let norm_formula_0 (f: formula) : formula =
    map_formula f (nonef, norm_b_formula, fun e -> Some (norm_exp e)) 

  let norm_formula(*_debug*) f =
    Gen.Debug.no_1 "cpure::norm_formula" string_of_formula string_of_formula
        norm_formula_0 f

end (* of ArithNormalizer module's definition *)

let has_var_exp e0 =
  let f e = match e with
    | Var _ -> Some true
    | _ -> None
  in
  fold_exp e0 f or_list 

let is_linear_formula f0 =
  let f_bf bf = 
    if is_bag_bform bf || is_list_bform bf then
      Some false
    else None
  in
  let f_e e =
    if is_bag e || is_list e then 
      Some false
    else
      match e with
      | Mult (e1, e2, _) -> 
          if has_var_exp e1 && has_var_exp e2 then
            Some false
          else None
      | Div (e1, e2, _) -> Some false
      | _ -> None
  in
  fold_formula f0 (nonef, f_bf, f_e) and_list

let is_linear_exp e0 =
  let f e =
    if is_bag e || is_list e then 
      Some false
    else
      match e with
      | Mult (e1, e2, _) -> 
          if has_var_exp e1 && has_var_exp e2 then
            Some false
          else None
      | Div (e1, e2, _) -> Some false
      | _ -> None
  in
  fold_exp e0 f and_list



let inner_simplify simpl f =
  let f_f e = match e with
    | Exists _ -> (Some (simpl e))
    | _ -> None in
  let f_bf bf = None in
  let f_e e = (Some e) in
  map_formula f (f_f, f_bf, f_e) 


let elim_exists_with_simpl simpl (f0 : formula) : formula = 
  let f = elim_exists f0 in
  inner_simplify simpl f

let elim_exists_with_simpl simpl (f0 : formula) : formula = 
  Gen.Debug.no_1 "elim_exists_with_simpl" !print_formula !print_formula 
    (fun f0 -> elim_exists_with_simpl simpl f0) f0

(* result of xpure with baga and memset/diffset *)
type xp_res_type = (BagaSV.baga * DisjSetSV.dpart * formula)

(*
(S1,D1,P1) * (S2,D2,P2)  =   (S1+S2, D1&D2,P1&P2)

(S1,D1,P1) & (S2,D2,P2)  = 
  (S1{\cap}S2, S1::D1 & S2::D2,
            (SAT(S1)&SAT(S2)) & P1&P2 )
(S1,D1,P1) \/ (S2,D2,P2) = 
  (S1{\cap}S2, SAT(S1)->S1::D1\/SAT(S2)->S1::D2, 
        SAT(S1) & P1 \/ SAT(S2) & P2)
*)

let star_xp_res ((b1,d1,p1):xp_res_type) ((b2,d2,p2):xp_res_type) =
  (BagaSV.star_baga b1 b2, DisjSetSV.star_disj_set d1 d2, mkAnd p1 p2 no_pos)

let conj_xp_res ((b1,d1,p1):xp_res_type) ((b2,d2,p2):xp_res_type) =
  let nb = BagaSV.conj_baga b1 b2 in
  let nd = DisjSetSV.conj_disj_set (b1::d1) (b2::d2) in
  let np = if (BagaSV.is_sat_baga b1) && (BagaSV.is_sat_baga b1) then  mkAnd p1 p2 no_pos  else mkFalse no_pos in
  (nb,nd,np)

let or_xp_res  ((b1,d1,p1):xp_res_type) ((b2,d2,p2):xp_res_type) =
  let nb = BagaSV.or_baga b1 b2 in
  let (np1,nd1) = if (BagaSV.is_sat_baga b1) then (p1,Some (b1::d1)) else (mkFalse no_pos,None) in
  let (np2,nd2) = if (BagaSV.is_sat_baga b2) then (p2,Some (b2::d2)) else (mkFalse no_pos,None) in
  let nd = match nd1,nd2 with
    | None,None -> []
    | None,Some nd2 -> nd2
    | Some nd1,None -> nd1
    | Some nd1,Some nd2 ->  DisjSetSV.or_disj_set (b1::d1) (b2::d2) in
    (nb,nd, mkOr np1 np2 None no_pos)

	
let rec filter_complex_inv f = match f with
  | And (f1,f2,l) -> mkAnd (filter_complex_inv f1) (filter_complex_inv f2) l
  | Or _ -> f  
  | Forall _ -> f
  | Exists _ -> f
  | Not (_,_,l) -> mkTrue l
  | BForm (b,l) -> match b with
	  | BConst _  
	  | BVar _ 
	  | BagSub _
	  | BagMin _
	  | BagMax _
	  | ListAllN _
	  | ListPerm _
	  | RelForm _ -> f
	  | _ -> mkTrue no_pos
	  
	  
	  

let mkNot_norm f lbl1 pos0 :formula= match f with
  | BForm (bf,lbl) -> begin
      let r = match bf with
        | BConst (b, pos) -> Some (BConst ((not b), pos))
        | Lt (e1, e2, pos) -> Some (Gte (e1, e2, pos))
        | Lte (e1, e2, pos) -> Some(Gt (e1, e2, pos))
        | Gt (e1, e2, pos) -> Some(Lte (e1, e2, pos))
        | Gte (e1, e2, pos) -> Some(Lt (e1, e2, pos))
        | Eq (e1, e2, pos) -> Some(Neq (e1, e2, pos))
        | Neq (e1, e2, pos) -> Some(Eq (e1, e2, pos))
		| BagIn e -> Some(BagNotIn e)
		| BagNotIn e -> Some(BagIn e)
        | _ -> None in
	match r with 
		| None -> Not (f, lbl,pos0)
		| Some bf -> BForm((norm_bform_aux bf),lbl)
	end
  | _ -> Not (f, lbl1,pos0)
