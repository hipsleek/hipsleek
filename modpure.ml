module CP = Cpure
module MP = Mcpure

module TYP =
struct
  open Globals
  type ty = CP.typ

  (* pretty printing for primitive types *)
  let string_of_prim (x:prim_type) : string = match x with
    | Bool          -> "boolean"
    | Float         -> "float"
    | Int           -> "int"
    | Void          -> "void"
    | Bag           -> "multiset"
    | List          -> "list"

  (* pretty printing for types *)
  let string_of = function 
    | CP.Prim t -> string_of_prim t 
    | CP.OType ot -> if ((String.compare ot "") == 0) then "ptr" else ot
	  
  let eq (t1:ty) (t2:ty) : bool = CP.are_same_types t1 t2

  (*Some auxiliary functions*)	

  let is_void_type (t:ty) : bool = CP.is_void_type t

  let is_bag_type (t:ty) : bool = CP.is_bag_type t

  let is_list_type (t:ty) : bool = CP.is_list_type t

  let is_int_type (t:ty) : bool = CP.is_int_type t	

  let is_float_type (t:ty) : bool = CP.is_float_type t

  let is_object_type (t:ty) : bool = CP.is_object_type t

  let mkRes (t:ty) = CP.mkRes t
	
  (* let string_of = CP.name_of_type *)
end;;

module SPEC_VAR =
struct
  open Globals
  open TYP
	  
  type v = CP.spec_var
  type t = v
 
  let string_of (sv:v) : string = CP.string_of_spec_var sv
	  
  let compare (x:v) (y:v) : comparison = 
    let v = String.compare (string_of x) (string_of y) in
    if v==0 then Equal 
    else if v>0 then Greater
    else Less

  let eq (x:v) (y:v) : bool = CP.eq_spec_var x y

  (*Some auxiliary functions*)

  let name_of (sv:v) : ident = CP.name_of_spec_var sv

  let full_name_of (sv:v) : ident = CP.full_name_of_spec_var sv
	
  let type_of (sv:v) : ty = CP.type_of_spec_var sv

  let is_unprimed (sv:v) : bool = CP.is_unprimed sv
	  
  let is_primed (sv:v) : bool  = CP.is_primed sv

  let is_object_var (sv:v) : bool = CP.is_object_var sv

  let to_primed (sv:v) : v = CP.to_primed sv

  let to_unprimed (sv:v) : v = CP.to_unprimed sv

  let mkEqVar (sv1:v) (sv2:v) pos = CP.mkEqVar sv1 sv2 pos
	
  let mkNeqVar (sv1:v) (sv2:v) pos = CP.mkNeqVar sv1 sv2 pos

  let mkEqVarInt (sv:v) (i:int) pos = CP.mkEqVarInt sv i pos

  let fresh_var (sv:v) : v = CP.fresh_spec_var sv

end;;

module SV = SPEC_VAR

module FORMULA =
struct
  open TYP
  open CP.ArithNormalizer
	
  type t = CP.formula

  let eq (f1:t) (f2:t) : bool = CP.equalFormula f1 f2 (*CP.equalFormula_f (SV.eq) f1 f2*)

  let string_of (f:t) : string = CP.ArithNormalizer.string_of_formula f

  let fv (f:t) : (SV.v list) = CP.fv f

  let normalise (f:t) : t = norm_formula f

  let foldr (e:t) arg f f_args f_comb = CP.foldr_formula e arg f f_args f_comb

  let fold (e:t) (f_f, f_bf, f_e) f_comb = CP.fold_formula (e:t) (f_f, f_bf, f_e) f_comb

  let trans (e:t) arg f f_args f_comb = CP.trans_formula e arg f f_args f_comb

  let transform f (e:t) : t = CP.transform_formula f e

  (*Some auxiliary functions*)
	
  let contains_exists (f:t) : bool = CP.contains_exists f

  let isConstTrue (f:t) : bool = CP.isConstTrue f

  let isConstFalse (f:t) : bool = CP.isConstFalse f

  let is_arith (f:t) : bool = CP.is_formula_arith f

  let mkAnd (f1:t) (f2:t) pos : t = CP.mkAnd f1 f2 pos

  let mkOr (f1:t) (f2:t) lbl pos : t = CP.mkOr f1 f2 lbl pos

  let mkNot (f:t) lbl pos : t = CP.mkNot f lbl pos

  let mkTrue pos : t = CP.mkTrue pos

  let mkFalse pos : t = CP.mkFalse pos

  let mkNull (v: SV.v) pos : t = CP.mkNull v pos

  let mkEq e1 e2 pos : t = CP.mkEqExp e1 e2 pos

  let mkNeq e1 e2 pos : t = CP.mkNeqExp e1 e2 pos	

  let mkExists (sv: SV.v list) (f:t) lbl pos = CP.mkExists sv f lbl pos
	
  let mkForall (sv: SV.v list) (f:t) lbl pos = CP.mkForall sv f lbl pos

  let should_simplify (f:t) : bool = CP.should_simplify f

end;;

module B_FORMULA =
struct
  open TYP
  open CP.ArithNormalizer
  
  type t = CP.b_formula

  let string_of (bf:t) : string = string_of_b_formula bf

  let eq (bf1:t) (bf2:t) : bool = CP.equalBFormula bf1 bf2
	  
  let fv (bf:t) : (SV.v list) = CP.bfv bf

  let normalise (bf:t) : (t option) = norm_b_formula bf

  let simplify (bf:t) : t = CP.b_form_simplify bf

  let foldr (bf:t) arg f f_args f_comb = CP.foldr_b_formula bf arg f f_args f_comb

  let trans (bf:t) arg f f_args f_comb = CP.trans_b_formula bf arg f f_args f_comb

  let transform f (bf:t) : t = CP.transform_b_formula f bf

  (*Some auxiliary functions*)	

  let isConstBTrue (bf:t) : bool = CP.isConstBTrue bf

  let isConstBFalse (bf:t) : bool = CP.isConstBFalse bf

  let is_bag (bf:t) : bool = CP.is_bag_bform bf

  let is_list (bf:t) : bool = CP.is_list_bform bf

  let is_arith (bf:t) : bool = CP.is_b_form_arith bf

  let mkNeq e1 e2 pos : t = CP.mkNeq e1 e2 pos

  let mkEq e1 e2 pos : t = CP.mkEq e1 e2 pos
	  
end;;

module EXP =
struct
  open TYP
  open CP.ArithNormalizer
	
  type t = CP.exp

  let type_of (e:t) : ty = CP.get_exp_type e

  let eq (e1:t) (e2:t) : bool = CP.eqExp e1 e2

  let string_of (e:t) : string = string_of_exp e

  let fv (e:t) : (SV.v list) = CP.afv e

  let normalise (e:t) : t = norm_exp e

  let foldr (e:t) arg f f_args f_comb = CP.foldr_exp e arg f f_args f_comb

  let fold (e:t) f f_comb zero = CP.foldr_exp e f f_comb zero

  let trans (e:t) arg f f_args f_comb = CP.trans_exp e arg f f_args f_comb

  let transform f (e:t) : t = CP.transform_exp f e

  (*Some auxiliary functions*)
	
  let is_max_min (e:t) : bool = CP.is_max_min e

  let is_null (e:t) : bool = CP.is_null e

  let is_zero (e:t) : bool = CP.is_zero e

  let is_var (e:t) : bool = CP.is_var e

  let is_num (e:t) : bool = CP.is_num e

  let is_int (e:t) : bool = CP.is_int e

  let is_float (e:t) : bool = CP.is_float e

  let is_object_var (e:t) : bool = CP.exp_is_object_var e

  let is_bag (e:t) : bool = CP.is_bag e

  let is_list (e:t) : bool = CP.is_list e

  let is_arith (e:t) : bool = CP.is_exp_arith e (*CP.is_arith e*)

  let to_int_const (e:t) rounding_func : int = CP.to_int_const e rounding_func

  let get_num_int (e:t) : int = CP.get_num_int e

  let get_num_float (e:t) : float = CP.get_num_float e

  let to_var (e:t) : SV.v = CP.to_var e

  let can_be_aliased (e:t) : bool = CP.can_be_aliased e

  let get_alias (e:t) : SV.v = CP.get_alias e

  let mkAdd (e1:t) (e2:t) pos = CP.mkAdd e1 e2 pos

  let mkSubtract (e1:t) (e2:t) pos = CP.mkSubtract e1 e2 pos

  let mkMult (e1:t) (e2:t) pos = CP.mkMult e1 e2 pos

  let mkDiv (e1:t) (e2:t) pos = CP.mkDiv e1 e2 pos

  let mkLt (e1:t) (e2:t) pos = CP.mkLt e1 e2 pos

  let mkLte (e1:t) (e2:t) pos = CP.mkLte e1 e2 pos	

  let mkGt (e1:t) (e2:t) pos = CP.mkGt e1 e2 pos

  let mkGte (e1:t) (e2:t) pos = CP.mkGte e1 e2 pos	
	
  let mkMax (e1:t) (e2:t) pos = CP.mkMax e1 e2 pos

  let mkMin (e1:t) (e2:t) pos = CP.mkMin e1 e2 pos

  let mkVar (sv:SV.v) pos = CP.mkVar sv pos

  let mkIConst (e:int) pos = CP.mkIConst e pos

  let mkFConst (e:float) pos = CP.mkFConst e pos	

end;;

module SpecVarSet = Gen.Set(SV);;

(* this is a hierachical labelling based on strings *)
(* "AB" is a subtype of "A" *) 
module StringLabel =
    struct
      open Globals
      type t=String
      let compare x y = let v = String.compare x y in
      if v==0 then Equal else if v<0 then Less else Greater
      let subtype x y = 
        let l1=String.length x in
        let l2=String.length y in
        if l2<=l1 then if y=(String.sub x 0 l2) then true
        else false
        else false
    end;;

module PureFormula =
   struct
     type t = CP.formula
     type v = CP.spec_var
     let join x y = CP.mkAnd x y Globals.no_pos
     (* let split x = match x with *)
     (*   | CP.And (f1,f2,_) -> Some(f1,f2) *)
     (*   | _ -> None *)
     let vars x = CP.fv x
     let unit = CP.mkTrue Globals.no_pos
   end;;

module MemoFormula =
   struct
     type t = MP.memoised_group
     type v = CP.spec_var
     let join x y = {
         MP.memo_group_fv =  SpecVarSet.union x.MP.memo_group_fv y.MP.memo_group_fv;
	     MP.memo_group_cons = x.MP.memo_group_cons @ y.MP.memo_group_cons;
         MP.memo_group_slice = x.MP.memo_group_slice @ y.MP.memo_group_slice;
         MP.memo_group_changed = x.MP.memo_group_changed || y.MP.memo_group_changed;
         MP.memo_group_aset = CP.EMapSV.merge_eset x.MP.memo_group_aset y.MP.memo_group_aset;
     } (* and two memoised group *)
     let vars x  = x.MP.memo_group_fv  (* free vars of memoised group *)
     let unit =  { MP.memo_group_fv = [];
	       MP.memo_group_cons = [];
			       MP.memo_group_slice = [];
			       MP.memo_group_changed = false;
			       MP.memo_group_aset = MP.empty_var_aset;}
   end;;


module Ptr =
    functor (Elt:Gen.EQ_TYPE) ->
struct
  include Elt
  type tlist = t list
  module X = Gen.BListEQ(Elt)
  let overlap = eq
  let intersect (x:tlist)  (y:tlist) = X.intersect x y
  let star_union x y = x@y
end;;

module PtrSV = Ptr(SV);;

module BagaSV = Gen.Baga(PtrSV);;
module EMapSV = Gen.EqMap(SV);;
module DisjSetSV = Gen.DisjSet(PtrSV);;
 
type baga_sv = BagaSV.baga

type var_aset = EMapSV.emap

include Globals
	
