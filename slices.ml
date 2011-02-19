type comparison = Less | Equal | Greater

module type ORDERED_TYPE =
   sig
     type t
     val compare: t -> t -> comparison (* string compare *)
   end;;

module type LABEL_TYPE =
   sig
     type t
     val compare: t -> t -> comparison (* string.compare *)
     val subtype: t -> t -> bool  (* substring test *)
   end;;

module type ASSOC_TYPE =
   (* this is to support pure formula *)
   sig
     type t
     type v
     val join: t -> t -> t  (* same as AND *)
     (* val split: t -> (t * t) option  *)(* if atomic, no splitting *)
     val vars: t->v list (* free vars of expression *)
     val unit: t (* same as true *)
   end;;

module Set =
   functor (Elt: ORDERED_TYPE) ->
     struct
       type element = Elt.t
       type set = element list
       let empty = []
       let rec add (x:element) (s:set) : set =
         match s with
           [] -> [x]
         | hd::tl ->
            match Elt.compare x hd with
              Equal   -> s         (* x is already in s *)
            | Less    -> x :: s    (* x is smaller than all elements of s *)
            | Greater -> hd :: add x tl
       let rec member (x:element) (s:set) : bool =
         match s with
           [] -> false
         | hd::tl ->
             match Elt.compare x hd with
               Equal   -> true     (* x belongs to s *)
             | Less    -> false    (* x is smaller than all elements of s *)
             | Greater -> member x tl
       let rec overlaps (x:set) (y:set) : bool =  (* checks if two sets overlap *)
         match x,y with
           | [],_ -> false
           | _,[] -> false
           | (x1::xs),(y1::ys) -> match Elt.compare x1 y1 with
               | Equal -> true
               | Less -> overlaps xs y
               | Greater -> overlaps x ys
       let rec union (x:set) (y:set) : set = (* union of two sets without duplicates *)
         match x,y with 
           | [],ys -> ys
           | xs,[] -> xs
           | (x1::xs),(y1::ys) -> match Elt.compare x1 y1 with
               | Equal -> x1::(union xs ys)
               | Less -> x1::(union xs y)
               | Greater -> y1::(union x ys)
     end;;
 

module Flexi_Partition =
    (* this supports dynamic slices *)
   functor (Elt: ORDERED_TYPE) ->
   functor (Res: ASSOC_TYPE with type v=Elt.t) ->
     struct
        module X = Set(Elt) (* with Elt.set=Res.v *)
       type vset = X.set
       type form = Res.t
       type one_p = vset * form
       type many_p = one_p list
       let rec combine (x:many_p) (vs:vset) (r:form) : one_p = (* collapse to one_p *)
         match x with
           | [] -> (vs,r)
           | (v1,r1)::xs -> combine xs (X.union v1 vs) (Res.join r1 r)
       let merge (x:many_p) (y:many_p) : many_p = (* merge two many_p into one *)
         let rec helper x y = match y with
           | [] -> x
           | (vs,r)::ys -> let (plist1,plist2) = List.partition (fun (s,_) -> X.overlaps s vs) x in
             let one_p = combine plist1 vs r in
             helper (one_p::plist2) ys
         in helper x y
       let collapse_one ((_,x):one_p) : form = x
       let collapse (x:many_p) : form = 
         let rec helper x = match x with
           | [] -> Res.unit
           | [e] -> collapse_one e
           | (_,r)::es -> Res.join r (helper es) in
         helper x
     end;;

module Fixed_Partition =
    (* this supports fixed slices *)
   functor (Elt: LABEL_TYPE) ->
   functor (Res: ASSOC_TYPE) ->
     struct
       type label = Elt.t
       type form = Res.t
       type one_p = Elt.t * Res.t
       type many_p = one_p list
       let mk_one_p (x:label) (r:form) : one_p = (x,r) 
       let merge (x:many_p) (y:many_p) : many_p = 
         let rec helper x y =
           match x,y with
             | [],_ -> y
             | _,[] -> x
             | ((l1,r1)::xs),((l2,r2)::ys) -> match Elt.compare l1 l2 with
                 | Equal -> (l1,Res.join r1 r2)::(helper xs ys)
                 | Less -> (l1,r1)::(helper xs y)
                 | Greater -> (l2,r2)::(helper x ys) 
         in helper x y
       let collapse_one ((_,x):one_p) : form = x
       let collapse (x:many_p) : form = 
         let rec helper x = match x with
           | [] -> Res.unit
           | [e] -> collapse_one e
           | (_,r)::es -> Res.join r (helper es) in
         helper x
     end;;

module CP = Cpure
module CF = Cformula
module MP = Mcpure

module SpecVar =
   struct
     type t = CP.spec_var 
     let compare x y = 
       let v=String.compare (CF.string_of_spec_var x) (CF.string_of_spec_var y) in
       if v==0 then Equal 
       else if v>0 then Greater
       else Less
   end;;
 
module SpecVarSet = Set(SpecVar);;

(* this is a hierachical labelling based on strings *)
(* "AB" is a subtype of "A" *) 
module StringLabel =
    struct
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
         MP.memo_group_aset = Util.merge_set_eq x.MP.memo_group_aset y.MP.memo_group_aset;
     } (* and two memoised group *)
     let vars x  = x.MP.memo_group_fv  (* free vars of memoised group *)
     let unit =  { MP.memo_group_fv = [];
			       MP.memo_group_cons = [];
			       MP.memo_group_slice = [];
			       MP.memo_group_changed = false;
			       MP.memo_group_aset = MP.empty_var_aset;}
   end;;
