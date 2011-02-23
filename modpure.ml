module CP = Cpure
module MP = Mcpure

module TYP =
struct
  open Globals
  type ty = CP.typ
  let eq = (=)
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
    | CP.OType ot -> if ((String.compare ot "") ==0) then "ptr" else ot
		
end;;

module SV =
struct
  open Globals
  open TYP
	  
  type v = Cpure.spec_var
  type t = v

  let is_primed = CP.is_primed

  let string_of = CP.string_of_spec_var

  let compare (x:v) (y:v) = 
    let v = String.compare (string_of x) (string_of y) in
    if v==0 then Equal 
    else if v>0 then Greater
    else Less

  let name_of = CP.name_of_spec_var

  let full_name_of  = CP.full_name_of_spec_var
	
  let type_of = CP.type_of_spec_var

  let is_unprimed = CP.is_unprimed
	
  let eq = CP.eq_spec_var

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
	
