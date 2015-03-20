#include "xdebug.cppo"
open Gen
open Globals
open Label_only
open VarGen

module type EXPR_TYPE =
    sig
      type e
      val comb : e -> e -> e
      val string_of : e -> string
      val ref_string_of : (e -> string) ref
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

  let string_of = pr_list (pr_pair Lbl.string_of Exp.string_of)
  let string_of_exp = Exp.string_of
  let ref_string_of_exp = Exp.ref_string_of

  (* assumes that we have identical labels *)
  let comb_node l1 l2 e1 e2 = (l1, Exp.comb e1 e2)

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
              if Lbl.compare l lx == 0 then helper l (Exp.comb ex x) xs1
              else (l,ex)::(helper lx x xs1)
    in match xs with
      | [] -> []
      | (l,x)::xs1 -> helper l x xs1

  let sort (xs:label_list) : label_list =
    let cmp (lx,_) (ly,_) = Lbl.compare lx ly in
    List.sort cmp xs 

  (* sort the labelled list and comb nodes with identical labels *)
  let norm (xs:label_list) : label_list =
    let rs = sort xs in
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

  let get_labels (xs:label_list) : lab_type list =
    Debug.no_1 "get_labels" (fun x -> string_of_int (List.length x))
        (pr_list Lbl.string_of) get_labels xs

  let filter_aux  f (fid:lab_type) (xs:label_list) :  (label_list) = 
    let pr_len xs= string_of_int (List.length xs) in
    let rs = List.filter (fun (l,_) -> f fid l) xs in
    Debug.ninfo_zprint (lazy (("Filter Label ==> Orig:"^(pr_len xs))^(" Filtered:"^(pr_len rs)))) no_pos;
    rs

  (* return a list of formula that are compatible with label *)
  let filter_label (fid:lab_type) (xs:label_list) :  (label_list) = 
    if Lbl.is_unlabelled fid then xs
    else filter_aux Lbl.is_compatible fid xs 

  (* return a list of formula that are compatible with label *)
      (* to be used for aux calls *)
  let filter_label_rec (fid:lab_type) (xs:label_list) :  (label_list) = 
    if Lbl.is_unlabelled fid then xs
    else filter_aux Lbl.is_compatible_rec fid xs 

  let rec comb_tgt l x ys =
      match ys with
        | [] -> (l,x)
        | (ly,y)::ys1 -> comb_tgt (x_add Lbl.comb_norm 3 l ly) (Exp.comb x y) ys1

  (* ac are disjoint *)
  (* add each item from xs into ac *)
  (* returns a disjoint list *)
  let norm_aux ac xs =
    let rec helper ac xs = match xs with
      | [] -> sort ac
      | ((lx,x) as p1)::xs1 -> 
            let (ys_l,ys_nl) = List.partition (fun (l2,_) -> Lbl.is_compatible lx l2) ac in
            match ys_l with
              | [] -> helper (p1::ac) xs
              | _ -> helper ((comb_tgt lx x ys_l)::ys_nl) xs1
    in helper ac xs

  (* normalise xs so that compatible items are placed tgt *)
  (* return a disjoint list *)
  let norm_closure (xs:label_list) : label_list =
    match xs with
      | [] -> []
      | x::xs -> norm_aux [x] xs

  (* merge two disjoint lists so that the compatible items 
     are merged tgt; return a disjoint list *)
  let merge_closure (xs:label_list) (ys:label_list) : label_list =
    let tx=List.length xs in
    let ty=List.length ys in
    if tx>ty then norm_aux xs ys
    else norm_aux ys xs

end;;
