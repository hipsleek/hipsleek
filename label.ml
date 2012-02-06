open Gen
open Globals
module CF = Cformula
module CP = Cpure

module type LABEL_TYPE =
    sig
      type t
      val unlabelled : t 
      val is_unlabelled : t -> bool (* is this unlabelled *)
      val norm : t -> t (* sort a label *)
      val is_compatible : t -> t -> bool
      val comb_identical : t -> t -> t (* combine two identical labels *)
      val comb_norm : t -> t -> t (* combine two normalised labels *)
      val string_of : t -> string
      val compare : t -> t -> int
    end;;

module Lab_List  =
struct
  type t = string list
  let unlabelled = []
  let is_unlabelled l = (l==[])
  let string_of x = pr_list pr_id x

  let rec overlap xs ys = match xs,ys with
      | [],ys -> false
      | x::xs1,[]-> false
      | x::xs1,y::ys1 ->
            let v = String.compare x y in
            if v==0 then true
            else if v<0 then overlap xs1 ys
            else overlap xs ys1

  (* assumes that xs and ys are normalized *)
  (* returns true if they overlap in some ways *)
  let is_compatible xs ys =
    if (is_unlabelled xs) || (is_unlabelled ys) then true
    else overlap xs ys

  (* assumes that xs is sorted *)
  let remove_dups xs =
    let rec helper l xs = match xs with
      | [] -> [l]
      | x::xs1 -> if l=x then helper l xs1
        else l::(helper x xs1)
    in match xs with
      | [] -> []
      | x::xs -> helper x xs

  let norm t =
    let r = List.sort (String.compare) t in
    remove_dups r

  (* assumes that xs and ys are normalized *)
  (* returns 0 if two labels are considered identical *)
  let rec compare xs ys =
    match xs,ys with
      | [],[] -> 0
      | [],y::_ -> -1
      | x::_,[] -> 1
      | x::xs1,y::ys1 -> 
            let v = String.compare x y in
            if v==0 then compare xs1 ys1
            else v

  (* assumes that xs and ys are normalized *)
  (* combine two labels that are considered identical *)
  let comb_identical xs ys = xs

  (* combine two labels that may not be identical *)
  let comb_norm xs ys = 
    let rec helper xs ys =
    match xs,ys with
      | [],ys -> ys
      | (x::xs1),[] ->  xs
      | (x::xs1),y::ys1 ->
            let v = String.compare x y in
            if v==0 then x::(helper xs1 ys1)
            else if v<0 then x::(helper xs1 ys)
            else y::(helper xs ys1)
    in helper xs ys
end;;

(* this labelling is for outermost disjuncts only *)
module Lab2_List  =
struct
  type t = (int option * string list)
      (* int replaces __i and may be used to label pre/post *)
  let unlabelled = (None, [])
  let is_unlabelled (_,l) = (l==[])
  let string_of = pr_pair (pr_opt string_of_int) (pr_list pr_id)

  let is_comp_opt lx ly = match lx,ly with
                           | Some x1,Some y1 -> x1==y1
                           | Some _, None -> true
                           | None, Some _ -> true (* not possible *)
                           | None, None -> true

  let is_compatible (lx,xs) (ly,ys) =
    if (xs==[] || ys=[]) then is_comp_opt lx ly
    else Lab_List.overlap xs ys

  let norm (opt,t) = (opt,Lab_List.norm t)

  (* assumes that xs and ys are normalized *)
  let comb_identical(opt1,xs) (opt2,ys) =
    (opt1,Lab_List.comb_identical xs ys)

  let comb_norm (opt1,xs) (opt2,ys) =
    (opt1,Lab_List.comb_norm xs ys)

  (* assumes that xs and ys are normalized *)
  let compare (opt1,xs) (opt2,ys) =
    match opt1,opt2 with
      | Some(i),Some(j) -> if i=j then 0 else if i<j then -1 else 1
      | _,_ -> Lab_List.compare xs ys
end;;

module type EXPR_TYPE =
    sig
      type e
      val comb : e -> e -> e
    end;;

module Exp_Pure =
struct 
  type e = Cpure.formula
  let comb x y = Cpure.And (x,y,no_pos)
end;;

module Exp_Heap =
struct 
  type e = CF.h_formula
  let comb x y = CF.Star 
    { CF.h_formula_star_h1 = x;
    CF.h_formula_star_h2 = y;
    CF.h_formula_star_pos = no_pos
    }
end;;

(*==============================*)
(*==== Module for Labels  ====*)
(*==============================*)
module LabelExpr = functor (Lbl :LABEL_TYPE) -> functor (Exp :EXPR_TYPE) ->
struct
  type lab_type = Lbl.t
  type exp_ty = Exp.e
  type label_list = (lab_type * exp_ty) list
  (* this assumes that list merger would not affect the order of elements *)

  (* assumes that we have identical labels *)
  let comb_node l1 l2 e1 e2 = (Lbl.comb_identical l1 l2, Exp.comb e1 e2)

  (* assumes already sorted *)
  (* nodes with identical labels are combined together *)
  (* this should not affect the order of the elements *)
  let merge (xs:label_list) (ys:label_list) : label_list =
    let rec helper xs ys =
      match xs with
        | [] -> ys
        | ((lx,x) as p1)::xs1 -> 
              begin
                match ys with
                  | [] -> xs
                  | ((ly,y) as p2)::ys1 ->
                        let v=Lbl.compare lx ly in
                        if v==0 then (comb_node lx ly x y)::(helper xs1 ys1)
                        else if v<0 then p1::(helper xs1 ys)
                        else p2::(helper xs ys1)
              end
    in helper xs ys


    

  (* nodes with identical labels are combined together *)
  let remove_dups (xs:label_list) : label_list =
    let rec helper l ex xs =
      match xs with
        | [] -> [(l,ex)]
        | (lx,x)::xs1 -> 
              if Lbl.compare l lx == 0 then helper (Lbl.comb_identical l lx) (Exp.comb ex x) xs1
              else (l,ex)::(helper lx x xs1)
    in match xs with
      | [] -> []
      | (l,x)::xs1 -> helper l x xs1

  (* sort the labelled list and comb nodes with identical labels *)
  let norm (xs:label_list) : label_list =
    let cmp (lx,_) (ly,_) = Lbl.compare lx ly in
    let rs = List.sort cmp xs in
    remove_dups rs
 
  (* check if labelled list is already normalised *)
  let is_norm (xs:label_list) : bool =
    let rec helper l xs =
      match xs with
        | [] -> true
        | (l2,_)::xs1 -> 
              if Lbl.compare l l2 < 0 then helper l2 xs1
              else false
    in match xs with
      | [] -> true
      | (l,_)::xs1 -> helper l xs1

  (* check if two label_list are compatible for zipping *)
  let rec is_zippable (xs:label_list) (ys:label_list) : bool =
    match xs,ys with
      | [], [] -> true
      | (lx,x)::xs1, (ly,y)::ys1 ->
            if Lbl.compare lx ly == 0 then (is_zippable  xs1 ys1)
            else false
      | _,_ -> false

  (* return a list of labels *)
  let get_labels (xs:label_list) : lab_type list =
    List.map fst xs

  (* return a list of formula that are compatible with label *)
  let filter_label (fid:lab_type) (xs:label_list) :  (label_list) = 
    if Lbl.is_unlabelled fid then xs
    else List.filter (fun (l,_) -> Lbl.is_compatible fid l) xs

  (* take two sorted lists of labelled expression and combine those with compatible labels *)
  let merge_compatible (xs:label_list) (ys:label_list) : label_list =
    let rec helper xs ys =
      match xs,ys with
        | [],zs 
        | zs,[] -> zs
        | ((lx,x) as p1)::xs1,((ly,y) as p2)::ys1 -> 
              begin
                let v = Lbl.compare lx ly in
                if v<0 then mc lx x xs1 ys
                else if v>0 then mc ly y ys1 xs
                else mc lx (Exp.comb x y) xs1 ys1
              end
    and mg l x ys =
      match ys with
        | [] -> (l,x)
        | (ly,y)::ys1 -> mg (Lbl.comb_norm l ly) (Exp.comb x y) ys1
    and mc l x xs ys =
      let (ys_l,ys_nl) =List.partition (fun (l2,_) -> Lbl.is_compatible l l2) ys in
      match ys_l with
        | [] -> (l,x)::(helper xs ys)
        | _ -> (mg l x ys_l)::(helper xs ys_nl) 
    in helper xs ys
end;;

module X1 = LabelExpr(Lab_List)(Exp_Pure);; 
module X2 = LabelExpr(Lab2_List)(Exp_Heap);;
