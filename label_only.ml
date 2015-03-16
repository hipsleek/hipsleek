#include "xdebug.cppo"
open VarGen
open Gen
open Globals
(* module CF = Cformula *)
(* module CP = Cpure *)

type label_ann = LA_Both | LA_Sat | LA_Imply
type lst_pair = (string * label_ann) list

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
      val comb_norm : int -> t -> t -> t (* combine two normalised labels *)
      val string_of : t -> string
      val compare : t -> t -> int
      val singleton : a -> t
      val convert : string -> lst_pair -> t
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
    else (List.mem id1 r2) (* || (List.mem id2 r1) *)
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


  let is_part_compatible_sat xs ys =
    let (id1,r1) = get_id xs in
    let (id2,r2) = get_id ys in
    if id1=id2 || id1="" || id2=""  then true
    else (List.mem id1 r2)

  let is_part_compatible_imply xs ys =
    let (id1,r1) = get_id xs in
    let (id2,r2) = get_id ys in
    if id1=id2 || id1="" then true
    else (List.mem id1 r2)


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

  let convert i lst = norm (i::List.map fst lst)

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
    let rr = aux r1 r2 in
    if id1=id2 then
      id1::rr
    else 
      let (id1,id2) = if id1="" then (id1,id2) else (id2,id1) in
      id1::(aux [id2] rr) (* to fix *)

  let comb_norm i xs ys =
    Debug.no_2_num i "comb_norm" string_of string_of string_of comb_norm xs ys 

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

module Lab_LAnn  =
struct
  (* type a = string *)
  type a = string
  type t = (string * lst_pair)
  let unlabelled = ("",[])
  (* let is_top_label l = List.for_all (fun c-> c="") l *)
  let is_common (id,ls) = (id="") 
  let is_unlabelled l = is_common l

  let string_of (id,lst) = 
    let pr = pr_list_no_brk (fun (i,l) ->
        (pr_string i)^(match l with 
          | LA_Sat -> "@S"
          | LA_Imply -> "@I"
          | LA_Both -> ""
        )) in
    (pr_string id)^(if lst==[] then "" else ","^(pr lst))

  let singleton s = (s,[])

  (* this assumes the label has been normalized *)
  let compare l1 l2 =
    let rec aux l1 l2 =
      match l1,l2 with
        | [],[] -> 0
        | [],x::_ -> -1
        | x::_,[] -> 1
        | (x,_)::l1,(y,_)::l2 -> 
              let r = String.compare x y in
              if r==0 then aux l1 l2
              else r
    in 
    let (id1,rl1) = l1 in
    let (id2,rl2) = l2 in
    let b1 = String.compare id1 id2 in
    if b1==0 then aux rl1 rl2
    else b1

  let is_equal l1 l2 =
    compare l1 l2 == 0

  let overlap xs ys = 
    let (id1,r1) = xs in
    let (id2,r2) = ys in
    let eq_id id (i,_) = i=id in
    if id1=id2 then true
    else (List.exists (eq_id id1) r2) || (List.exists (eq_id id2) r1)

  let filter_sat xs =
    List.filter (fun (_,b)->not(b==LA_Imply)) xs

  let filter_imply xs =
    List.filter (fun (_,b)->not(b==LA_Sat)) xs

  let overlap_sat x ys = 
    let ys = filter_sat ys in
    let eq_id id (i,_) = i=id in
    List.exists (eq_id x) ys

  let overlap_imply x ys = 
    let ys = filter_imply ys in
    let eq_id id (i,_) = i=id in
    List.exists (eq_id x) ys

  (* this is for aggressive imply check *)
  let is_fully_compatible_imply ante_l conseq_l =
    let (id1,r1) = ante_l in
    let (id2,r2) = conseq_l in
    if id1=id2 then true
    else overlap_imply id1 r2

 (* let is_fully_compatible_imply xs ys = *)
 (*    let pr = pr_list (pr_pair pr_id pr_none)  in *)
 (*    Debug.no_2 "is_fully_compatible_imply" pr pr string_of_bool is_fully_compatible_imply xs ys 	 *)


  (* (\* this is for aggressive imply sat *\) *)
  (* let is_fully_compatible_imply xs ys = *)
  (*   let x = first_label xs in *)
  (*   if (has_common x) && (has_common ys) then true *)
  (*   else overlap x ys *)

  (* let is_fully_compatible_imply xs ys = *)
  (*   let pr = pr_list pr_id  in *)
  (*   Debug.no_2 "is_fully_compatible_imply" pr pr string_of_bool is_fully_compatible_imply xs ys 	 *)


  let is_fully_compatible_sat xs ys =
    let (id1,r1) = xs in
    let (id2,r2) = ys in
    if id1=id2 then true
    else overlap_sat id1 r2
  
  let is_fully_compatible xs ys =
    (* if (has_common xs) && (has_common ys) then true *)
    (* else overlap xs ys *)
    is_fully_compatible_sat xs ys

  (* let is_fully_compatible xs ys = *)
  (*   let pr = pr_list pr_none  in *)
  (*   Debug.no_2 "is_fully_compatible_sat" pr pr string_of_bool is_fully_compatible xs ys 	 *)

  (* assumes that xs and ys are normalized *)
  (* returns true if they overlap in some ways *)
  let is_part_compatible_sat xs ys =
    let (id1,r1) = xs in
    let (id2,r2) = ys in
    if id1="" || id2="" || id1=id2 then true
    else overlap_sat id1 r2

  let is_part_compatible_sat xs ys =
    let pr = string_of  in
    Debug.no_2 "is_part_compatible_sat" pr pr string_of_bool is_part_compatible_sat xs ys 	


  let is_part_compatible_imply xs ys =
    let (id1,r1) = xs in
    let (id2,r2) = ys in
    if id1="" || id1=id2 then true
    else overlap_imply id1 r2

  let is_part_compatible_imply xs ys =
    let pr = string_of  in
    Debug.no_2 "is_part_compatible_imply" pr pr string_of_bool is_part_compatible_imply xs ys 	

  let is_compatible xs ys =
    is_part_compatible_sat xs ys

  (* let is_part_compatible xs ys = *)
  (*   is_compatible xs ys *)
  (*   (\* if (is_unlabelled xs)  then true *\) *)
  (*   (\* else overlap xs ys *\) *)

  (* let is_part_compatible xs ys =  *)
  (*   let pr = pr_list pr_id  in *)
  (*   Debug.no_2 "is_part_compatible" pr pr string_of_bool is_part_compatible xs ys 	 *)
	
  let is_compatible_rec = is_part_compatible_sat

  (* assumes that xs is sorted *)
  let remove_dups id r =
    let rec helper l xs = match xs with
      | [] -> [l]
      | x::xs1 -> if l=x then helper l xs1
        else l::(helper x xs1)
    in match r with
      | [] -> (id, [])
      | x::xs -> (id, (helper x xs))

  let norm t =
    let (id,r) = t in
    let r = List.sort (fun (i,_) (j,_) -> String.compare i j) r in
    remove_dups id r

  let convert i lst = norm (i,lst)

  let add_label id lst = (id,LA_Both)::lst

  (* pre : two labels must have the same id and sorted*)
  let comb_norm xs ys = 
    let rec aux xs ys = match xs,ys with
      | [],_ -> ys
      | _,[] ->  xs
      | (((x,_) as x1)::xs1),((y,_) as y1)::ys1 ->
            let v = String.compare x y in
            if v==0 then x1::(aux xs1 ys1)
            else if v<0 then x1::(aux xs1 ys)
            else y1::(aux xs ys1) in
    let (id1,r1) = xs in
    let (id2,r2) = ys in
    let rr = aux r1 r2 in
    if id1=id2 then (id1,rr)
    else 
      let (id1,id2) = if id1="" then (id1,id2) else (id2,id1) in
      (id1, aux [(id2,LA_Both)] rr) 
      (* report_error no_pos "violate pre of Label_Only.Lab_list.comb_norm"  *)

  let comb_norm i xs ys =
    Debug.no_2_num i "comb_norm" string_of string_of string_of comb_norm xs ys 

  let merge_ann ann1 ann2 =
    match ann1, ann2 with
      | LA_Both, _
      | _, LA_Both
      | LA_Sat, LA_Imply
      | LA_Imply, LA_Sat -> LA_Both
      | x,_ -> x

  let norm_ann_lst lst =
    let rec aux lst norm_lst = 
      match lst with
        |[]     -> norm_lst
        | (x,ax)::xs -> 
              let l = Gen.BList.list_find (fun (y,ay) -> if (String.compare x y == 0) then (Some (y,ay)) else None ) norm_lst in
              let norm_lst = 
              match l with
                | Some _ -> List.map (fun (y,ay) -> if (String.compare x y == 0) then  (y, merge_ann ax ay) else  (y,ay)) norm_lst
                | None -> (x,ax)::norm_lst
              in
              aux xs norm_lst
    in aux lst []

  let merge x y =
    if (is_equal x y) then
      let (x_id,x_lst) =  x in
      let (_,y_lst) =  y in
      (* let lst = x_lst@y_lst in *)
      (x_id,x_lst@y_lst)
    else
      failwith ("cannot merge labels" ^ (string_of x) ^ " and " ^ (string_of y))

  (* assumes that xs and ys are normalized *)
  (* returns 0 if two labels are considered identical *)
  (* let compare xs ys = *)
  (*   let n1=List.length xs in *)
  (*   let n2=List.length ys in *)
  (*   let rec aux xs ys = *)
  (*     match xs,ys with *)
  (*       | [],[] -> 0 *)
  (*       | [],y::_ -> -1 *)
  (*       | x::_,[] -> 1 *)
  (*       | x::xs1,y::ys1 ->  *)
  (*             let v = String.compare x y in *)
  (*             if v==0 then aux xs1 ys1 *)
  (*             else v *)
  (*   in if n1<n2 then -1 *)
  (*   else if n1>n2 then 1 *)
  (*   else aux xs ys *)

  (* let compare xs ys =  *)
  (*       let pr = pr_list pr_id  in *)
  (*       Debug.no_2 "Label_compare" pr pr string_of_int compare xs ys  *)
  (* assumes that xs and ys are normalized *)
  (* combine two labels that are considered identical *)
  (* let comb_identical xs ys = xs *)

  (* combine two labels that may not be identical *)
  (* let comb_norm xs ys =  *)
  (*   let rec helper xs ys = match xs,ys with *)
  (*     | [],ys -> ys *)
  (*     | (x::xs1),[] ->  xs *)
  (*     | (x::xs1),y::ys1 -> *)
  (*           let v = String.compare x y in *)
  (*           if v==0 then x::(helper xs1 ys1) *)
  (*           else if v<0 then x::(helper xs1 ys) *)
  (*           else y::(helper xs ys1) *)
  (*   in helper xs ys *)
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

  let convert i s = (None,Lab_List.norm (i::(List.map fst s)))

  (* assumes that xs and ys are normalized *)
  (* let comb_identical(opt1,xs) (opt2,ys) = *)
  (*   (opt1,Lab_List.comb_identical xs ys) *)

  let comb_norm (opt1,xs) (opt2,ys) =
    (opt1,Lab_List.comb_norm 4 xs ys)

  let comb_norm i xs ys =
    Debug.no_2_num i "comb_norm" string_of string_of string_of comb_norm xs ys 

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

(* type spec_label =  Lab_List.t  *)
(* let empty_spec_label = Lab_List.unlabelled *)

(* type spec_label =  Lab_LAnn.t (\* t *\) *)
(* let empty_spec_label = Lab_LAnn.unlabelled (\* unlabelled *\) *)

(* this spec label has default integer *)
type spec_label_def =  Lab2_List.t 
let empty_spec_label_def = Lab2_List.unlabelled

(* module LOne = Lab_LAnn *)
(* module LOne = Lab_List *)
module LOne = Lab_LAnn
