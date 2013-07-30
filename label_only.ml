open Gen
open Globals
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
  (* let is_top_label l = List.for_all (fun c-> c="") l *)

  let is_common l = match l with
    | [] -> true
    | x::_ -> x=""

  let is_unlabelled l = is_common l

  (* let has_common l = (is_unlabelled l) or (List.exists (fun c-> c="") l) *)

  let string_of x = 
    if x=[] then "\"\""
    else pr_list_no_brk pr_string x
  let singleton s = [s]

  let get_id ls = match ls with
    | [] -> ("",[])
    | x::xs -> (x,xs)

  (* this assumes the label has been normalized *)
  let compare l1 l2 =
    let rec aux l1 l2 =
      match l1,l2 with
        | [],[] -> 0
        | [],x::_ -> -1
        | x::_,[] -> 1
        | x::l1,y::l2 -> 
              let r = String.compare x y in
              if r==0 then aux l1 l2
              else r
    in 
    let (id1,r1) = get_id l1 in
    let (id2,r2) = get_id l2 in
    let r1 = String.compare id1 id2 in
    if r1==0 then aux l1 l2
    else r1

  (* pre: label is normalized *)
  let is_equal l1 l2 =
    compare l1 l2 == 0

  let is_same_key l1 l2 =
    let (id1,r1) = get_id l1 in
    let (id2,r2) = get_id l2 in
    id1=id2

  let overlap xs ys = 
    let (id1,r1) = get_id xs in
    let (id2,r2) = get_id ys in
    (* let xs = List.sort String.compare xs in *)
    (* let ys = List.sort String.compare ys in *)
    if id1=id2 then true
    else (List.mem id1 r2) || (List.mem id2 r1)
    (* let rec aux xs ys = *)
    (*   match xs,ys with *)
    (*     | [],ys -> false *)
    (*     | x::xs1,[]-> false *)
    (*     | x::xs1,y::ys1 -> *)
    (*           let v = String.compare x y in *)
    (*           if v==0 then true *)
    (*           else if v<0 then aux xs1 ys *)
    (*           else aux xs ys1 *)
    (* in  *)
    (* aux xs ys *)

  let overlap xs ys = 
    let pr = pr_list pr_id  in
    Debug.no_2 "overlap" pr pr string_of_bool overlap xs ys 	

  (* let first_label xs = *)
  (*   fst(get_id xs) *)
(* match xs with *)
(*       | [] ->[""] *)
(*       | x::_ -> [x] *)

  (* this is for aggressive imply check *)
  let is_fully_compatible_imply ante_l conseq_l =
    let (id1,r1) = get_id ante_l in
    let (id2,r2) = get_id conseq_l in
    if id1=id2 then true
    else List.mem id1 r2

 let is_fully_compatible_imply xs ys =
    let pr = pr_list pr_id  in
    Debug.no_2 "is_fully_compatible_imply" pr pr string_of_bool is_fully_compatible_imply xs ys 	


  let is_fully_compatible_sat xs ys =
    let (id1,r1) = get_id xs in
    let (id2,r2) = get_id ys in
    if id1=id2 then true
    else (List.mem id2 r1) (* || (List.mem id2 r1) *)
    (* let x = first_label xs in *)
    (* let y = first_label ys in *)
    (* if (has_common x) && (has_common ys) || (has_common y && has_common xs)  *)
    (* then true *)
    (* else overlap x ys || overlap y xs *)
  
  let is_fully_compatible xs ys =
    (* if (has_common xs) && (has_common ys) then true *)
    (* else overlap xs ys *)
    is_fully_compatible_sat xs ys

  let is_fully_compatible xs ys =
    let pr = pr_list pr_id  in
    Debug.no_2 "is_fully_compatible_sat" pr pr string_of_bool is_fully_compatible xs ys 	

  (* assumes that xs and ys are normalized *)
  (* returns true if they overlap in some ways *)
  let is_compatible xs ys =
    let (id1,r1) = get_id xs in
    let (id2,r2) = get_id ys in
    if id1=id2 || id1="" || id2="" then true
    else (List.mem id1 r2) || (List.mem id2 r1)
    (* if (is_unlabelled xs) || (is_unlabelled ys) then true *)
    (* else overlap xs ys *)

  let is_part_compatible xs ys =
    is_compatible xs ys
    (* if (is_unlabelled xs)  then true *)
    (* else overlap xs ys *)

  let is_part_compatible xs ys = 
    let pr = pr_list pr_id  in
    Debug.no_2 "is_part_compatible" pr pr string_of_bool is_part_compatible xs ys 	
	
  let is_compatible_rec = is_compatible

  (* assumes that xs is sorted *)
  let remove_dups id r =
    let rec helper l xs = match xs with
      | [] -> [l]
      | x::xs1 -> if l=x then helper l xs1
        else l::(helper x xs1)
    in match r with
      | [] -> id::[]
      | x::xs -> id::(helper x xs)

  let norm t =
    let (id,r) = get_id t in
    let r = List.sort (String.compare) r in
    remove_dups id r

  (* assumes that xs and ys are normalized *)
  (* returns 0 if two labels are considered identical *)
  let compare xs ys =
    let (id1,r1) = get_id xs in
    let (id2,r2) = get_id ys in
    let n1=List.length r1 in
    let n2=List.length r2 in
    let sr=String.compare id1 id2 in
    let rec aux xs ys =
      match xs,ys with
        | [],[] -> 0
        | [],y::_ -> -1
        | x::_,[] -> 1
        | x::xs1,y::ys1 -> 
              let v = String.compare x y in
              if v==0 then aux xs1 ys1
              else v
    in 
    if sr==0 then
      if n1==n2 then aux r1 r2
      else 
        if n1<n2 then -1
        else 1
    else sr

  let compare xs ys = 
	let pr = pr_list pr_id  in
	Debug.no_2 "Label_compare" pr pr string_of_int compare xs ys 
  (* assumes that xs and ys are normalized *)
  (* combine two labels that are considered identical *)
  (* let comb_identical xs ys = xs *)

  (* pre : two labels must have the same id and sorted*)
  let comb_norm xs ys = 
    let rec aux xs ys = match xs,ys with
      | [],_ -> ys
      | _,[] ->  xs
      | (x::xs1),y::ys1 ->
            let v = String.compare x y in
            if v==0 then x::(aux xs1 ys1)
            else if v<0 then x::(aux xs1 ys)
            else y::(aux xs ys1) in
    let (id1,r1) = get_id xs in
    let (id2,r2) = get_id ys in
    if id1=id2 then
      id1::(aux r1 r2)
    else report_error no_pos "violate pre of Label_Only.Lab_list.comb_norm" 

  (* pre : both xs ys must be of the same id *)
  (* let merge xs ys =  *)
  (*   let rec aux xs ys = match xs,ys with *)
  (*     | [],_ -> ys *)
  (*     | _,[] ->  xs *)
  (*     | (x::xs1),y::ys1 -> *)
  (*           let v = String.compare x y in *)
  (*           if v==0 then x::(aux xs1 ys1) *)
  (*           else if v<0 then x::(aux xs1 ys) *)
  (*           else y::(aux xs ys1) *)
  (*   in match xs,ys with *)
  (*     | [],[] -> [] *)
  (*     | [],x::xs1 | x::xs1,[]  *)
  (*           -> if x="" then xs  *)
  (*             else report_error no_pos "violate pre of Label_Only.Lab_list.merge" *)
  (*     | x::xs1,y::ys1  *)
  (*           -> if x=y then x::(aux xs1 ys1) *)
  (*             else report_error no_pos "violate pre of Label_Only.Lab_list.merge" *)

end;;

(* this labelling is for outermost disjuncts only *)
module Lab2_List  =
struct
  type a = string
  type t = (int option * string list)
      (* int replaces __i and may be used to label pre/post *)
  let unlabelled = (None, [])
  let is_unlabelled (n,l) = n==None && l==[]
  let string_of = pr_pair (pr_opt string_of_int) (pr_list pr_string)
  let string_of_opt l = 
    if is_unlabelled l then "" 
    else string_of l 
      (* pr_pair (pr_opt string_of_int) (pr_list pr_id) l *)
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
