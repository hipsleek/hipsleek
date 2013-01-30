open Gen
(* open Globals *)
(* module CF = Cformula *)
(* module CP = Cpure *)

module type LABEL_TYPE =
    sig
      type a
      type t 
      val unlabelled : t 
      val is_unlabelled : t -> bool (* is this unlabelled *)
      val norm : t -> t (* sort a label *)
      val is_compatible : t -> t -> bool
      val is_compatible_rec : t -> t -> bool
      (* val comb_identical : t -> t -> t (\* combine two identical labels *\) *)
      val comb_norm : t -> t -> t (* combine two normalised labels *)
      val string_of : t -> string
      val compare : t -> t -> int
      val singleton : a -> t
    end;;

module Lab_List  =
struct
  (* type a = string *)
  type a = string
  type t = string list
  let unlabelled = []
  let is_unlabelled l = (l==[])
  let string_of x = pr_list pr_id x
  let singleton s = [s]

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

  let is_part_compatible xs ys =
    if (is_unlabelled xs) then true
    else overlap xs ys

	
  let is_compatible_rec = is_compatible

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
  let rec compare_x xs ys =
    match xs,ys with
      | [],[] -> 0
      | [],y::_ -> -1
      | x::_,[] -> 1
      | x::xs1,y::ys1 -> 
            let v = String.compare x y in
            if v==0 then compare_x xs1 ys1
            else v
  let compare xs ys = 
	let pr = pr_list pr_id  in
	Debug.no_2 "Label_compare" pr pr string_of_int compare_x xs ys 
  (* assumes that xs and ys are normalized *)
  (* combine two labels that are considered identical *)
  (* let comb_identical xs ys = xs *)

  (* combine two labels that may not be identical *)
  let comb_norm xs ys = 
    let rec helper xs ys = match xs,ys with
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
  type a = string
  type t = (int option * string list)
      (* int replaces __i and may be used to label pre/post *)
  let unlabelled = (None, [])
  let is_unlabelled (n,l) = n==None && l==[]
  let string_of = pr_pair (pr_opt string_of_int) (pr_list pr_id)
  let string_of_opt l = if is_unlabelled l then "" else pr_pair (pr_opt string_of_int) (pr_list pr_id) l
  let singleton s = (None,[s])
  let is_comp_opt lx ly = match lx,ly with
                           | Some x1,Some y1 -> x1==y1
                           | Some _, None -> true
                           | None, Some _ -> true (* not possible *)
                           | None, None -> true

  let is_compatible_rec (lx,xs) (ly,ys) =
    if (xs==[] || ys=[]) then is_comp_opt lx ly
    else Lab_List.overlap xs ys

  let is_compatible (lx,xs) (ly,ys) =
    if (xs==[] || ys=[]) then true
    else Lab_List.overlap xs ys

  let norm (opt,t) = (opt,Lab_List.norm t)

  (* assumes that xs and ys are normalized *)
  (* let comb_identical(opt1,xs) (opt2,ys) = *)
  (*   (opt1,Lab_List.comb_identical xs ys) *)

  let comb_norm (opt1,xs) (opt2,ys) =
    (opt1,Lab_List.comb_norm xs ys)

  (* assumes that xs and ys are normalized *)
  let compare (opt1,xs) (opt2,ys) =
    match opt1,opt2 with
      | Some(i),Some(j) -> if i=j then 0 else if i<j then -1 else 1
      | _,_ -> Lab_List.compare xs ys
end;;

(* module type EXPR_TYPE = *)
(*     sig *)
(*       type e *)
(*       val comb : e -> e -> e *)
(*       val string_of : e -> string *)
(*     end;; *)

type spec_label =  Lab_List.t 
let empty_spec_label = Lab_List.unlabelled

(* this spec label has default integer *)
type spec_label_def =  Lab2_List.t 
let empty_spec_label_def = Lab2_List.unlabelled
