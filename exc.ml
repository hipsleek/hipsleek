#include "xdebug.cppo"
open VarGen
open Gen
open Globals
open VarGen

(* type constant_flow = ident (\* identifier for flows *\) *)

type nflow = (int*int)(*numeric representation of flow*)

(* type lflow = (nflow list) *)

(* type dflow = nflow * lflow (\* orig_exc, current list *\) *)


(*========================================*)
(*LDK*)
(*conversion between lflow, list and set*) 
(*lflow can be implemented as a set of element*)
(*Therefore, operations on flow can follow set theory *)
(*========================================*)
module IntSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = int
  end )

(* n1 <= n2 *)
let rec list_of_pair (n1,n2): int list = 
  if (n2<n1) then []
  else
  if (n1==n2) then 
    [n1]
  else
    (n1::(list_of_pair (n1+1,n2)))

(*convert a list of intervals into a list of integers*)
let rec list_of_list_pair ls  =
  match ls with
  | [] -> []
  | ((a,b)::xs) ->
    let tmp1 = list_of_pair (a,b) in
    let tmp2 = list_of_list_pair xs in
    tmp1@tmp2

(*get a set from a list of elements*)
let rec set_of_list ls =
  match ls with
  | [] -> IntSet.empty
  | x::xs -> 
    let s = set_of_list xs in
    IntSet.add x s

(*convert a list of pair of interval into a set of elements*)
let rec set_of_list_pair ls  =
  let ls1 = list_of_list_pair ls in
  set_of_list ls1

(*parition a sorted list into segments of consecutive numbers*)
(*for example: [1,4,5,8] -> [[1],[4,5],[8]]*)
let partition ls =
  let rec helper ls =
    match ls with
    | [] -> [[]]
    | [x] -> [[x]]
    | x::xs -> 
      let rs = helper xs in
      let tmp = List.hd rs in (*rs has at least 1 list containing a least 1 lement*)
      let y = List.hd tmp in
      if (x+1==y) then
        let new_tmp = x::tmp in
        let new_rs = new_tmp::(List.tl rs) in
        new_rs
      else
        ([x]::rs)
  in helper ls

let list_pair_of_list ls =
  let llist = partition ls in
  let rec helper ls =
    match ls with
    | [] -> []
    | [[]] -> []
    | x::xs -> (*x is a list*)
      let rs = helper xs in
      let len = List.length x in
      if (len==0) then
        rs
      else if (len==1) then
        let ele = List.hd x in
        ((ele,ele)::rs)
      else
        let first = List.hd x in
        let last = List.nth x (len-1) in
        ((first,last)::rs)
  in helper llist

let list_pair_of_set s =
  let ls = IntSet.elements s in
  list_pair_of_list ls
(*========================================*)
(*========================================*)

(*  WN/Khanh: TODO  *)
(*  (i) add notion of exact type *)
(*  (ii) add holes in nflow type *)
(*
           subtype  exact
   __Exc    12-16    16
     |
     e1     12-15    15
     |
     e2     12-14    14
   /    \
  e3    e4
  12    13

  (e1,__Exc,(12,15)),
  (e2,e1,(12,14)),
  (e4,e2,(13,13)),
  (e3,e2,(12,12)),

*)

(* Khanh : need to generalise our code to 
   use dflow instead of nflow 
   e.g in the code:
     try {
       .. throw v(of e1)
       // D & flow e1
     } catch (e2 v) {
       // D & flow norm
     }
     // D & flow e1-e2
   The flow  e1-e2 which is
   captured as 
   (e1, e1-e2)
   = ((12,15),[(12,15)-(12,14)])
   = ((12,15),[(15,15)])
*)

(* let empty_flow : nflow = (-1,0) *)

(* let is_empty_flow ((a,b):nflow) = a<0 || (a>b) *)

let is_subset_flow_ne ((s1,b1):nflow) ((s2,b2):nflow)
  = s2<=s1 && b1<=b2

(* let is_subset_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) = *)
(*       if is_empty_flow(f1) then true *)
(*       else if is_empty_flow(f2) then false *)
(*       else is_subset_flow_ne f1 f2 *)

(* is f1 an exact flow for subtype f2 *)
let is_exact_flow_ne ((s1,b1):nflow) ((s2,b2):nflow) =
  s1==s2 && b1==b2

(* let is_exact_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) = *)
(*   if is_empty_flow f1 then *)
(*     if is_empty_flow f2 then true *)
(*     else false *)
(* else is_exact_flow_ne f1 f2 *)


(* let is_exact_lflow lst mf = *)
(*   try  *)
(*     let x = last lst  *)
(*     in is_exact_flow_ne x mf *)
(*   with _ -> false *)

(* let is_exact_dflow (mf, lst) = *)
(*       is_exact_lflow lst mf *)

let is_non_overlap_flow_ne ((s1,b1):nflow) ((s2,b2):nflow) =
  b1<s2 || b2<s1

let is_overlap_flow_ne (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
  not(is_non_overlap_flow_ne f1 f2)

(* let is_overlap_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) = *)
(*       if is_empty_flow(f1) || is_empty_flow(f2) then false *)
(*       else is_overlap_flow_ne f1 f2 *)

let is_next_flow_ne ((s1,b1):nflow) ((s2,b2):nflow) =
  s2==b1+1

let is_eq_flow_ne (((s1,b1):nflow)) (((s2,b2):nflow)) =
  s1==s2 && b1==b2

(* let is_eq_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) = *)
(*       if is_empty_flow(f1) then *)
(*         if (is_empty_flow f2) then true *)
(*         else false *)
(*       else is_eq_flow_ne f1 f2 *)

let union_flow_ne ((s1,b1):nflow) ((s2,b2):nflow) =
  ((min s1 s2),(max b1 b2))

(* let union_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) = *)
(*       if (is_empty_flow f1) || (is_empty_flow f2) then empty_flow *)
(*       else union_flow_ne f1 f2 *)

let order_flow_ne (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
  if (is_subset_flow_ne f1 f2) then
    if (is_subset_flow_ne f2 f1) then 0 (*f1=f2 => 0*)
    else 1 (*if f1 is subset of f2*)
  else if (is_subset_flow_ne f2 f1) then -1 (*f2 is subset of f1*)
  else if s1<s2 then 2
  else -2


(* let order_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) = *)
(*   if (is_empty_flow f1) then  *)
(*     if (is_empty_flow f2) then 0 *)
(*     else 1 *)
(*   else if (is_empty_flow f2) then -1 *)
(*   else order_flow_ne f1 f2 *)

(* f1 - f2 *)
let subtract_flow_ne (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
  let minus (s1,b1) (s2,b2) = 
    (* fst is larger than than the second *)
    let r1 = if (s1==s2) then [] else [(s1,s2-1)] in
    let r2 = if (b1==b2) then [] else [(b2+1,b1)] in
    r1@r2 in
  if (is_subset_flow_ne f1 f2) then []
  else if is_subset_flow_ne f2 f1 then minus f1 f2
  else if not(is_overlap_flow_ne f1 f2) then [f1]
  else if s2<=b1 then [(s1,s2-1)]
  else [(s2,s1-1)]

(* let subtract_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) = *)
(*   if is_empty_flow(f1) || is_empty_flow(f2) then [] *)
(*   else subtract_flow_ne f1 f2 *)

(* let rec subtract_lflow_ne (lf:lflow) (n:nflow) : lflow = *)
(*   match lf with *)
(*     | [] -> [] *)
(*     | x::lf ->  *)
(*           let r = subtract_flow_ne x n in *)
(*           r@(subtract_lflow_ne lf n) *)

(* assumes that lf is a valid flows *)
(* let subtract_lflow (lf:lflow) (n:nflow) : lflow = *)
(*       if (is_empty_flow n) then lf *)
(*       else subtract_lflow_ne lf n *)

(* let subtract_dflow (((mf,lf):dflow) as df) (n:nflow) : dflow = *)
(*       if (is_empty_flow n) then df *)
(*       else (mf,subtract_lflow_ne lf n) *)

(* let is_empty_dflow ((mf,lf):dflow) : bool = lf==[] *)

(* let rec norm_lflow_aux ((s,b) as n) (l:lflow)  = *)
(*   match l with *)
(*     |  [] -> l *)
(*     | ((s2,b2) as n2)::xs -> *)
(*           if b+1==s2 then norm_lflow_aux (s,b2) xs *)
(*           else n::(norm_lflow_aux n2 xs) *)

(* let norm_lflow (l:lflow)  = *)
(*   match l with *)
(*     |  [] -> l *)
(*     | x::xs -> norm_lflow_aux x l *)

(* let rec is_subset_lflow (l1:lflow) (l2:lflow) = *)
(*   match l1 with *)
(*     | [] -> true *)
(*     | (s1,b1)::l1a -> *)
(*           match l2 with *)
(*             | [] -> false *)
(*             | (s2,b2)::l2a ->  *)
(*                   if s2<=s1 then *)
(*                     if b1<=b2 then is_subset_lflow l1a l2 *)
(*                     else false *)
(*                   else is_subset_lflow l1 l2a *)

(* let is_subset_dflow (((d1,l1):dflow) as f1) (((d2,l2):dflow) as f2) = *)
(*   is_subset_lflow l1 l2  *)

(* let rec is_overlap_lflow (l1:lflow) (l2:lflow) = *)
(*   match l1 with *)
(*     | [] -> false *)
(*     | ((s1,b1) as n1)::l1a -> *)
(*           match l2 with *)
(*             | [] -> false *)
(*             | ((s2,b2) as n2)::l2a -> *)
(*                   if is_overlap_flow_ne n1 n2 then true *)
(*                   else if s1<s2 then is_overlap_lflow l1a l2 *)
(*                   else is_overlap_lflow l1 l2a *)

(* let is_overlap_dflow (((d1,l1):dflow) as f1) (((d2,l2):dflow) as f2) = *)
(*   is_overlap_lflow l1 l2 *)

let sort_flow (xs:(ident * ident * nflow) list) =
  List.sort (fun (_,_,n1) (_,_,n2) -> order_flow_ne n2 n1) xs


(* global constants *)

(* (\*let any_flow = "__Any"*\) *)
(* let flow = "flow" *)
(* let top_flow = "__flow" *)
(* let n_flow = "__norm" *)
(* let cont_top = "__Cont_top" *)
(* let brk_top = "__Brk_top" *)
(* let c_flow = "__c-flow" *)
(* let raisable_class = "__Exc" *)
(* let ret_flow = "__Ret" *)
(* let spec_flow = "__Spec" *)
(* let false_flow = "__false" *)
(* let abnormal_flow = "__abnormal" *)
(* let stub_flow = "__stub" *)
(* let error_flow = "__Error" *)

(* (\* let may_error_flow_int = ref ((-2,-2):nflow) (\\*norm or error*\\) *\) *)
(* let n_flow_int = ref ((-1,-1):nflow) *)
(* let ret_flow_int = ref ((-1,-1):nflow) *)
(* let spec_flow_int = ref ((-1,-1):nflow) *)
(* let top_flow_int = ref ((-2,-2):nflow) *)
(* let exc_flow_int = ref ((-2,-2):nflow) (\*abnormal flow*\) *)
(* let error_flow_int  = ref ((-2,-2):nflow) (\*must error*\) *)
(* let false_flow_int = (0,0) *)
(* let stub_flow_int = (-3,-3) *)

(*hairy stuff for exception numbering*)
(* TODO : should be changed to use Ocaml graph *)

(* type flow_entry = string * string * nflow  *)

(* let exc_list = ref ([]:flow_entry list) *)

(* let clear_exc_list () = *)
(*   n_flow_int := (-1,-1); *)
(*   ret_flow_int := (-1,-1); *)
(*   spec_flow_int := (-1,-1); *)
(*   top_flow_int := (-2,-2); *)
(*   exc_flow_int := (-2,-2); *)
(*   exc_list := [] *)

(* let sort_exc_list () = *)
(*   let lst = !exc_list in *)
(*   exc_list := sort_flow lst *)

(* let remove_dups1 (n:flow_entry list) = Gen.BList.remove_dups_eq (fun (a,b,_) (c,d,_) -> a=c) n *)

(* let clean_duplicates ()=  *)
(*   exc_list := remove_dups1 !exc_list *)

(* let exc_cnt = new counter 0 *)

(* let reset_exc_hierarchy () = *)
(*   let () = clean_duplicates () in *)
(*   let () = exc_cnt # reset in *)
(*   let el = List.fold_left (fun acc (a,b,_) ->  *)
(*       if a="" then acc else (a,b,(0,0))::acc) [] !exc_list in *)
(*   exc_list := el *)

(* let string_of_exc_list (i:int) = *)
(*   let x = !exc_list in *)
(*   let el = pr_list (pr_triple pr_id pr_id (pr_pair string_of_int string_of_int)) (List.map (fun (a,e,p) -> (a,e,p)) x) in *)
(*   "Exception List "^(string_of_int i)^": "^(string_of_int (List.length x))^"members \n"^el *)


(* let get_hash_of_exc (f:string): nflow =  *)
(*   if ((String.compare f stub_flow)==0) then  *)
(* 	Error.report_error {Error.error_loc = no_pos; Error.error_text = ("Error found stub flow")} *)
(*   else *)
(* 	let rec get (lst:(string*string*nflow)list):nflow = match lst with *)
(* 	  | [] -> false_flow_int *)
(* 	  | (a,_,(b,c))::rst -> if (String.compare f a)==0 then (b,c) *)
(* 		else get rst in *)
(*     (get !exc_list) *)

(* (\*t1 is a subtype of t2*\) *)
(* let exc_sub_type (t1 : constant_flow) (t2 : constant_flow): bool =  *)
(*   let r11,r12 = get_hash_of_exc t1 in *)
(*   if ((r11==0) && (r12==0)) then false *)
(*   else *)
(* 	let r21,r22 = get_hash_of_exc t2 in *)
(* 	if ((r21==0) && (r22==0)) then true *)
(* 	else *)
(* 	  ((r11>=r21)&&(r12<=r22)) *)


(*let exc_int_sub_type ((t11,t12):nflow)	((t21,t22):nflow):bool = if (t11==0 && t12==0) then true else ((t11>=t21)&&(t12<=t22))*)

(* TODO : below can be improved by keeping only supertype & choosing the closest *)
(* Given (min,max) and closest found (cmin,cmax), such that cmin<=min<=max<=cmax
     (i) exact      min=max=cmax      id#
     (ii) full       min=min & max    id
     (ii) partial    otherwise        id_
*)
(* let get_closest ((min,max):nflow):(string) =  *)
(*   let rec get (lst:(string*string*nflow) list):string*nflow =  *)
(*     match lst  with *)
(* 	  | [] -> (false_flow,false_flow_int) *)
(* 	  | (a,b,(c,d)):: rest->  *)
(*             if (c==min && d==max) then (a,(c,d)) (\*a fits perfect*\) *)
(* 	        else  *)
(*               let r,(minr,maxr) = (get rest) in *)
(* 	          if (minr==c && maxr==d)||(c>min)||(d<max) then (r,(minr,maxr)) (\*the rest fits perfect or a is incompatible*\) *)
(* 	          else if (minr>min)||(maxr<max) then (a,(c,d)) (\*the rest is incompatible*\) *)
(* 	          else if ((min-minr)<=(min-c) && (maxr-max)<=(d-max)) then (r,(minr,maxr)) *)
(* 	          else (a,(c,d)) in *)
(*   let r,_ = (get !exc_list) in r *)

(* -2 : unknown; -1 - partial flow; 0 - exact type; 1 - full flow *)


(* let get_closest (((min,max):nflow) as nf):(string) =  *)
(*   let a1 = get_closest nf in *)
(*   let (a2,_) = (\* "XXX" *\) get_closest_new !exc_list nf in *)
(*   if (a1=a2) then a1 *)
(*   else  *)
(*     let pr = pr_pair string_of_int string_of_int in *)
(*     print_endline ("WN : get_closest"^(pr nf)^" new :"^a2^" old :"^a1); *)
(*     a1 *)

(* let add_edge(n1:string)(n2:string):bool = *)
(*   let () =  exc_list := !exc_list@ [(n1,n2,false_flow_int)] in *)
(*   true *)

(* let add_edge(n1:string)(n2:string):bool = *)
(*   Debug.no_2 "add_edge" pr_id pr_id string_of_bool add_edge n1 n2 *)

(*constructs the mapping between class/data def names and interval
  types*)
(* FISHY : cannot be called multiple times, lead to segmentation problem in lrr proc *)
(* why did lrr below cause segmentation problem for sleek? *)
(* let () = reset_exc_hierarchy () in *)
(* let () = print_flush "c-h 1" in *)
(* let r,_ = (lrr "" "") in *)
(* let () = print_flush "c-h 2" in *)
(* r *)

(* let update_values() = *)
(*   n_flow_int := (get_hash_of_exc n_flow); *)
(*   ret_flow_int := (get_hash_of_exc ret_flow); *)
(*   spec_flow_int := (get_hash_of_exc spec_flow); *)
(*   top_flow_int := (get_hash_of_exc top_flow); *)
(*   exc_flow_int := (get_hash_of_exc abnormal_flow); *)
(*   error_flow_int := (get_hash_of_exc error_flow) *)
(*     (\* ; Globals.sleek_mustbug_flow_int := (get_hash_of_exc Globals.sleek_mustbug_flow) *\) *)
(*     (\* ;Globals.sleek_maybug_flow_int := (get_hash_of_exc Globals.sleek_maybug_flow) *\) *)
(*     (\* ;let () = print_string ((List.fold_left (fun a (c1,c2,(c3,c4))-> a ^ " (" ^ c1 ^ " : " ^ c2 ^ "="^"["^(string_of_int c3)^","^(string_of_int c4)^"])\n") "" r)) in ()*\) *)

(* let compute_hierarchy () = *)
(*   let () = reset_exc_hierarchy () in *)
(*   exc_list := compute_hierarchy_aux exc_cnt !exc_list; *)
(*   update_values () *)


(* let compute_hierarchy i () = *)
(*   let pr () = string_of_exc_list 0 in *)
(*   Debug.no_1_num i "compute_hierarchy" pr pr (fun _ -> compute_hierarchy()) () *)


(*   (\* TODO : use a graph module here! *\) *)
(* let has_cycles ():bool = *)
(*   let rec cc (crt:string)(visited:string list):bool =  *)
(* 	let sons = List.fold_left (fun a (d1,d2,_)->if ((String.compare d2 crt)==0) then d1::a else a) [] !exc_list in *)
(* 	if (List.exists (fun c-> (List.exists (fun d->((String.compare c d)==0)) visited)) sons) then true *)
(* 	else (List.exists (fun c-> (cc c (c::visited))) sons) in	 *)
(*   (cc top_flow [top_flow]) *)

module type ETABLE =
sig
  type nflow
  (* type fe = (ident * ident * t) *)
  val flow : ident
  val top_flow : ident
  val n_flow : ident
  val cont_top : ident
  val brk_top : ident
  val c_flow : ident
  val raisable_class : ident
  val ret_flow : ident
  val loop_ret_flow : ident
  val spec_flow : ident
  val false_flow : ident
  val abnormal_flow : ident
  val stub_flow : ident
  val error_flow : ident
  val mayerror_flow : ident
  val bfail_flow : ident (*barrier failure*)
  val norm_flow_int : nflow ref
  val ret_flow_int : nflow ref
  val c_flow_int : nflow ref
  val loop_ret_flow_int : nflow ref
  val spec_flow_int : nflow ref
  val top_flow_int : nflow ref 
  val abnormal_flow_int : nflow ref
  val raisable_flow_int : nflow ref
  val error_flow_int : nflow ref
  val mayerror_flow_int : nflow ref
  val bfail_flow_int : nflow ref
  val false_flow_int : nflow
  val empty_flow : nflow 
  val is_false_flow : nflow -> bool
  val is_empty_flow : nflow -> bool
  (* is fst the exact flow of snd *)
  val is_exact_flow : nflow -> nflow -> bool
  val is_full_flow : nflow -> nflow -> bool
  val is_partial_flow : nflow -> nflow -> bool
  val is_subset_flow : nflow -> nflow -> bool
  val is_subsume_flow : nflow -> nflow -> bool
  val is_eq_flow : nflow -> nflow -> bool
  val is_overlap_flow : nflow -> nflow -> bool
  val order_flow : nflow -> nflow -> int
  val norm_flow : nflow -> nflow 
  val string_of_flow : nflow -> string
  val string_of_list_flow : nflow list -> string
  val subtract_flow : nflow -> nflow -> nflow
  val intersect_flow : nflow -> nflow -> nflow
  val union_flow : nflow -> nflow -> nflow
  val subtract_flow_l : nflow -> nflow -> nflow list
  val sub_type : typ -> typ -> bool
  class exc :
    object ('a)
      (* val mutable elist : fe list *)
      (* val mutable cnt : counter *)
      method string_of : string
      method get_hash : ident -> nflow
      method get_exc_hash : ident -> nflow option
      method add_edge : ident -> ident -> unit
      method compute_hierarchy : unit
      method get_closest : nflow -> string
      method has_cycles : bool
      (* method sort : unit *)
      method remove_dupl : unit
      method clear : unit
      method sub_type_obj : ident -> ident -> bool
      method union_flow_ne: nflow -> nflow -> nflow
      method is_norm_flow : nflow -> bool
      method is_exc_flow : nflow -> bool
      method is_top_flow : nflow -> bool
      method get_min_max : nflow -> (int*int)
      method mk_nflow_from_min_max : int -> int -> nflow
    end
  val exlist : exc
end;;

module ET_const =
struct
  let flow = "flow"
  let top_flow = "__flow"
  let n_flow = "__norm"
  let cont_top = "__Cont_top"
  let brk_top = "__Brk_top"
  let c_flow = "__cflow"
  let raisable_class = "__Exc"
  let ret_flow = "__Return"
  let loop_ret_flow = "__RET"
  let spec_flow = "__Spec"
  let false_flow = "__false"
  let abnormal_flow = "__abnormal"
  let stub_flow = "__stub" (* temp stub flow used by parser *)
  let error_flow = "__Error"
  let mayerror_flow = "__MayError"
  let bfail_flow = "__Fail"
end;;

module ETABLE_NFLOW : ETABLE =
struct
  include ET_const
  type nflow = (int*int)(*numeric representation of flow*)
  type flow_entry = (ident * ident * nflow)
  let empty_flow : nflow = (-1,0)
  let norm_flow_int = ref empty_flow
  let c_flow_int = ref empty_flow
  let ret_flow_int = ref empty_flow 
  let loop_ret_flow_int = ref empty_flow
  let spec_flow_int = ref empty_flow
  let top_flow_int = ref empty_flow 
  let abnormal_flow_int = ref empty_flow
  let raisable_flow_int = ref empty_flow
  let error_flow_int  = ref empty_flow 
  let mayerror_flow_int  = ref empty_flow 
  let bfail_flow_int  = ref empty_flow 
  let top_flow_int = ref empty_flow 
  let false_flow_int = (0,0) 
  let is_empty_flow ((a,b):nflow) = a<0 || (a>b)
  let is_false_flow (p1,p2) :bool = (p2==0)&&(p1==0) || p1>p2  
  let get_closest_new elist (((min,max):nflow) as nf):(string * int) =
    if (is_empty_flow nf) || (is_false_flow nf) then (false_flow,1)
    else
      let res = List.filter (fun (_,_,n) -> (is_subset_flow_ne nf n)) elist in
      match res with
      | [] -> ("## cannot find flow type",-2)
      | (s,_,nf2)::_ -> (s, 
                         if is_exact_flow_ne nf nf2 then 0 (* exact *)
                         else if is_eq_flow_ne nf nf2 then 1 (* full *)
                         else -1) (* partial *)
  let is_subsume_flow (n1,n2)(p1,p2) : bool =
    if (is_false_flow (p1,p2)) then true 
    else (n1<=p1)&&(p2<=n2)
  let is_subset_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    if is_empty_flow(f1) then true
    else if is_empty_flow(f2) then false
    else is_subset_flow_ne f1 f2
  let is_exact_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    if is_empty_flow f1 then
      if is_empty_flow f2 then true
      else false
    else is_exact_flow_ne f1 f2
  let is_overlap_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    if is_empty_flow(f1) || is_empty_flow(f2) then false
    else is_overlap_flow_ne f1 f2
  let is_eq_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    if is_empty_flow(f1) then
      if (is_empty_flow f2) then true
      else false
    else is_eq_flow_ne f1 f2
  let is_status_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    if is_subset_flow f1 f2 then
      if is_subset_flow f2 f1 then
        1 (* full flow *)
      else 
      if is_exact_flow f1 f2 then 0 (* exact type *)
      else -1 (* partial flow *)
    else -2 (* unknown *)
  let is_partial_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    (is_status_flow f1 f2) == -1
  let is_full_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    (is_status_flow f1 f2) == 1
  let order_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    if (is_empty_flow f1) then 
      if (is_empty_flow f2) then 0
      else 1
    else if (is_empty_flow f2) then -1
    else order_flow_ne f1 f2
  let subtract_flow_l (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    if is_empty_flow(f1) || is_empty_flow(f2) then []
    else subtract_flow_ne f1 f2
  let norm_flow (nf:nflow)  =
    if (is_empty_flow nf) then empty_flow
    else nf
  let string_of_flow = pr_pair string_of_int string_of_int
  let string_of_list_flow = pr_list string_of_flow
  let subtract_flow (((s1,b1):nflow) as f1) (((s2,b2):nflow) as f2) =
    let x = subtract_flow_l f1 f2 in
    match x with
    | [] -> empty_flow
    | [x] -> x
    | _ -> f1
  let intersect_flow (n1,n2)(p1,p2) : (int*int)= ((if (n1<p1) then p1 else n1),(if (n2<p2) then n2 else p2))
  let union_flow (n1,n2)(p1,p2) : (int*int)= ((if (n1<p1) then n1 else p1),(if (n2<p2) then p2 else n2))
  let remove_dups1 (n:flow_entry list) = Gen.BList.remove_dups_eq (fun (a,b,_) (c,d,_) -> a=c) n
  let compute_hierarchy_aux_x cnt elist =
    let rec lrr (f1:string)(f2:string):(((string*string*nflow) list)*nflow) =
      let l1 = List.find_all (fun (_,b1,_)-> ((String.compare b1 f1)==0)) elist in
      if ((List.length l1)==0) then 
        let i = cnt # inc_and_get in
        let j = cnt # inc_and_get in
        ([(f1,f2,(i,j))],(i,j))
      else 
        let ll,(mn,mx) = List.fold_left 
            (fun (t,(o_min,o_max)) (a,b,(c,d)) -> 
               let temp_l,(n_min, n_max) = (lrr a b) 
               in (temp_l@t
                  ,( (if ((o_min== -1)||(n_min<o_min)) then n_min else o_min)
                   ,(if (o_max<n_max) then n_max else o_max)))) 
            ([],(-1,-1)) 
            l1 
        in let () = cnt # inc in  (* to account for internal node *)
        ( ((f1,f2,(mn,mx+1))::ll) ,(mn,mx+1))
    in
    let r,_ = (lrr top_flow "") in
    r

  let compute_hierarchy_aux cnt elist =
    let pr = pr_list (pr_triple (fun c->c) (fun c->c) (pr_pair string_of_int string_of_int)) in
    Debug.no_1 "compute_hierarchy_aux" pr pr (fun _ -> compute_hierarchy_aux_x cnt elist) elist

  class exc =
    object (self)
      val mutable elist = ([]:flow_entry list)
      val mutable cnt = new counter 0
      method clear =
        begin
          norm_flow_int := empty_flow;
          c_flow_int := empty_flow;
          ret_flow_int := empty_flow;
          spec_flow_int := empty_flow;
          top_flow_int := empty_flow;
          abnormal_flow_int := empty_flow;
          raisable_flow_int := empty_flow;
          error_flow_int := empty_flow;
          mayerror_flow_int := empty_flow;
          bfail_flow_int := empty_flow;
          elist <- []
        end
      method private sort = 
        begin
          elist <- sort_flow elist
        end
      method remove_dupl =
        begin
          elist <- remove_dups1 elist
        end
      method string_of =
        begin
          let x = elist in
          let el = pr_list (pr_triple pr_id pr_id (pr_pair string_of_int string_of_int)) 
              (List.map (fun (a,e,p) -> (a,e,p)) x) in
          "Exception List : "^(string_of_int (List.length x))^"members \n"^el
        end
      method get_hash (f:string) : nflow =
        begin
          let foo f =
            if (f="") then  !top_flow_int
            else if ((String.compare f stub_flow)==0) then 
              Error.report_error {Error.error_loc = no_pos; Error.error_text = ("Error found stub flow")}
            else
              let rec get (lst:(string*string*nflow)list):nflow = match lst with
                | [] -> (* false_flow_int *) !top_flow_int
(* report_error no_pos ("Can not find flow of " ^ f) (\* false_flow_int *\) *)
                | (a,_,(b,c))::rst ->
                  (* let _ = print_endline a in *)
                  if (String.compare f a)==0 then (b,c)
                  else get rst in
              (* let () = y_binfo_hp (self # string_of) in *)
              (get elist)
          in
          let pr = pr_pair string_of_int string_of_int in
          (* Debug.no_1 "get_hash2" pr_id pr *) foo f
        end
      method get_exc_hash (f:string) : nflow option =
        try
          Some (self # get_hash f)
        with _ -> None
      method add_edge (n1:string)(n2:string):unit =
        begin
          (elist <- elist@ [(n1,n2,false_flow_int)])
        end
      method private reset_exc =
        begin
          let () = self # remove_dupl in
          let () = cnt # reset in
          let el = List.fold_left (fun acc (a,b,_) ->
              if a="" then acc else (a,b,(0,0))::acc) [] elist in
          elist <- el
        end
      method private update_values =
        begin
          norm_flow_int := self # get_hash n_flow;
          c_flow_int := self # get_hash c_flow;
          ret_flow_int := self # get_hash ret_flow;
          loop_ret_flow_int := self # get_hash loop_ret_flow;
          spec_flow_int := self # get_hash spec_flow;
          top_flow_int := self # get_hash top_flow;
          raisable_flow_int := self # get_hash raisable_class;
          abnormal_flow_int := self # get_hash abnormal_flow;
          bfail_flow_int := self # get_hash bfail_flow;
          error_flow_int := self # get_hash error_flow;
          mayerror_flow_int := self # get_hash mayerror_flow;
        end
      method compute_hierarchy =
        begin
          let () = self # reset_exc in
          elist <- compute_hierarchy_aux cnt elist;
          self # update_values;
          self # sort
        end
      method get_closest (((min,max):nflow) as nf):(string) =
        begin
          let (s,t)=(get_closest_new elist nf) in
          s ^ (
            if t==0 then "#E" (* exact ann *)
            else if t!=1 then "#P" (* partial ann *)
            else "") (* full *)
        end
      method has_cycles : bool =
        begin
          let rec cc (crt:string)(visited:string list):bool =
            let sons = List.fold_left (fun a (d1,d2,_)->if ((String.compare d2 crt)==0) then d1::a else a) [] elist in
            if (List.exists (fun c-> (List.exists (fun d->((String.compare c d)==0)) visited)) sons) then true
            else (List.exists (fun c-> (cc c (c::visited))) sons) in
          (cc top_flow [top_flow])
        end
      method sub_type_obj (t1 : ident) (t2 : ident): bool = 
        begin
          let n1 = self#get_hash t1 in
          let n2 = self#get_hash t2 in
          Debug.ninfo_pprint t1 no_pos;
          Debug.ninfo_pprint t2 no_pos;
          if (is_false_flow n2)
          then t1=t2
          else is_subset_flow n1 n2
        end
      method union_flow_ne ((s1,b1):nflow) ((s2,b2):nflow)=
        begin
          ((min s1 s2),(max b1 b2))
        end
      method is_norm_flow (f:nflow) =
        begin
          is_exact_flow f !norm_flow_int
        end
      method is_exc_flow (f:nflow) =
        begin
          is_subset_flow f !raisable_flow_int
        end
      method is_top_flow (f:nflow) =
        begin
          is_exact_flow f !top_flow_int
        end
      method get_min_max ((s,b):nflow) =
        begin
          (s,b)
        end
      method mk_nflow_from_min_max (s:int) (b:int) =
        begin
          (s,b)
        end
    end
  let exlist = new exc
  let rec sub_type (t1 : typ) (t2 : typ) = 
    match t1,t2 with
    | UNK, _ -> true
    | Named c1, Named c2 -> 
      if c1=c2 then true
      else if c1="" then true
      else 
        begin
          Debug.ninfo_zprint (lazy (exlist#string_of)) no_pos ;
          exlist # sub_type_obj c1 c2
        end
    | Array (et1,d1), Array (et2,d2) ->
      if (d1 = d2) then sub_type et1 et2
      else false
    | BagT et1, BagT et2 -> sub_type et1 et2
    | List et1, List et2 -> sub_type et1 et2
    | Int, NUM        -> true
    | Float, NUM        -> true
    | p1, p2 -> p1=p2
  ;;
end;;

(* Khanh : TODO : module to support dflow *)
(*most methods are implemented using set theory*)
module ETABLE_DFLOW : ETABLE  =
struct
  include ET_const
  type nf = (int*int)
  type lflow = (nf list)
  type dflow = nf * lflow
  type nflow = dflow
  (* type t = dflow *)
  (* type fe = (ident * ident * t) *)
  type flow_entry = (ident * ident * dflow)
  let empty_flow : dflow = ((-1,0),[(-1,0)])
  let norm_flow_int = ref empty_flow
  let c_flow_int = ref empty_flow
  let ret_flow_int = ref empty_flow
  let loop_ret_flow_int = ref empty_flow
  let spec_flow_int = ref empty_flow

  let top_flow_int = ref empty_flow
  let abnormal_flow_int = ref empty_flow
  let raisable_flow_int = ref empty_flow
  let error_flow_int  = ref empty_flow
  let mayerror_flow_int  = ref empty_flow
  let bfail_flow_int  = ref empty_flow
  let false_flow_int = ((0,0),[(0,0)])

  let is_empty_flow ((a,b),lst) = lst==[] || a<0 || (a>b)
  let is_false_flow ((p1,p2),lst) :bool = (p2==0)&&(p1==0) || p1>p2 
  (*n1,n2 subsume p1,p2*)
  let is_subsume_flow ((n1,n2),lst1) ((p1,p2),lst2) : bool =
    if (is_false_flow ((p1,p2),lst2)) then true
    else
      let s1 = set_of_list_pair lst1 in
      let s2 = set_of_list_pair lst2 in
      (*s2 is subset of s1*)
      if (IntSet.subset s2 s1) then
        true
      else
        false
  (*f1 is a subset of f2*) 
  (*??? biff b/w subset and subsume*)
  (*f1 is a subset of f2 => f2 subsume f1*)
  let is_subset_flow ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) =
    if is_empty_flow(f1) then true
    else if is_empty_flow(f2) then false (*?? is empty flow a subset of empty flow*)
    else
      let s1 = set_of_list_pair lst1 in
      let s2 = set_of_list_pair lst2 in
      (*s1 is subset of s2*)
      if (IntSet.subset s1 s2) then
        true
      else
        false
  let is_exact_flow ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) =
    if is_empty_flow f1 then
      if is_empty_flow f2 then true
      else false
    else is_exact_flow_ne (s1,b1) (s2,b2) (*??? not clear*)
  let is_overlap_flow ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) =
    if is_empty_flow(f1) || is_empty_flow(f2) then false
    else
      let s1 = set_of_list_pair lst1 in
      let s2 = set_of_list_pair lst2 in
      let s3 =  (IntSet.inter s2 s1) in (*set intersection*)
      if (IntSet.is_empty s3) then
        false (*no intersection*)
      else
        true
  let is_eq_flow ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) =
    if is_empty_flow(f1) then
      if (is_empty_flow f2) then true
      else false
    else 
      let s1 = set_of_list_pair lst1 in
      let s2 = set_of_list_pair lst2 in
      (IntSet.equal s1 s2)
  (*???what is it *)
  let is_status_flow ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) =
    if is_subset_flow f1 f2 then
      if is_subset_flow f2 f1 then
        1 (* full flow *)
      else
      if is_exact_flow f1 f2 then 0 (* exact type *)
      else -1 (* partial flow *)
    else -2 (* unknown *)
  let is_partial_flow ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) =
    (is_status_flow f1 f2) == -1
  let is_full_flow ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) =
    (is_status_flow f1 f2) == 1
  let order_flow ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) =
    if (is_empty_flow f1) then
      if (is_empty_flow f2) then 0
      else 1
    else if (is_empty_flow f2) then -1
    else 
    if (is_subset_flow f1 f2) then
      if (is_subset_flow f2 f1) then 0 (*f1=f2 => 0*)
      else 1 (*if f1 is subset of f2*)
    else if (is_subset_flow f2 f1) then -1 (*f2 is subset of f1*)
    else if s1<s2 then 2
    else -2
  let get_closest_new elist ((((min,max),lst):dflow) as nf):(string * int) =
    if (is_empty_flow nf) || (is_false_flow nf) then (false_flow,1)
    else
      let res = List.filter (fun (_,_,n) -> (is_subset_flow nf n)) elist in
      match res with
      | [] -> ("## cannot find flow type",-2)
      | (s,_,nf2)::_ -> (s, 
                         if is_exact_flow nf nf2 then 0 (* exact *)
                         else if is_eq_flow nf nf2 then 1 (* full *)
                         else -1) (* partial *)
  let sort_flow (xs:(ident * ident * dflow) list) =
    List.sort (fun (_,_,n1) (_,_,n2) -> order_flow n2 n1) xs
  (*f1-f2*) 
  (*??? substract_flow_f vs subtract_flow*)
  let subtract_flow_l  ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) : dflow list =
    if is_empty_flow(f1) || is_empty_flow(f2) then []
    else
      let ss1 = set_of_list_pair lst1 in
      let ss2 = set_of_list_pair lst2 in
      let ss3 = IntSet.diff ss1 ss2 in (*ss1 - ss2*)
      let rs = list_pair_of_set ss3 in
      [((s1,b1),rs)] (*a single flow*)
  (* List.map (fun (a,b) -> ((s1,b1),[(a,b)])) rs (\* different flows *\) *)
  let norm_flow (nf:dflow)  =
    if (is_empty_flow nf) then empty_flow
    else 
      let ((a,b),lst) = nf in
      let s1 = set_of_list_pair lst in (*convert list of intervals into a set*)
      let lst1 = list_pair_of_set s1 in (**)
      ((a,b),lst1)
  let string_of_flow  ((((s1,b1),lst1):dflow) as f1) = 
    let pr_pair_int = pr_pair (string_of_int) (string_of_int) in
    let pr_pair_int_list = pr_list (fun (a,b) -> pr_pair_int (a,b)) in
    pr_pair (pr_pair_int) (pr_pair_int_list) f1
  let string_of_list_flow = pr_list string_of_flow
  (*this is not used at all. only use subtract_flow_l*)
  let subtract_flow  ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) : dflow =
    let x = subtract_flow_l f1 f2 in
    match x with
    | [] -> empty_flow
    | a::_ ->  a
  (* ((s1,b1),x) (\* ??? not sure*\) *)

  let intersect_flow  ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) : dflow =
    if (is_empty_flow f1) then f1
    else if (is_empty_flow f2) then f2
    else
      let s1 = set_of_list_pair lst1 in
      let s2 = set_of_list_pair lst2 in
      let s3 = IntSet.inter s1 s2 in (*intersection*)
      let ls = IntSet.elements s3 in
      let len = List.length ls in
      if (len==0) then empty_flow
      else
        let first = List.hd ls in
        let last = List.nth ls (len-1) in
        ((first,last),(list_pair_of_set s3))
  let union_flow  ((((s1,b1),lst1):dflow) as f1) ((((s2,b2),lst2):dflow) as f2) : dflow = f2 (*for testing*)
  let remove_dups1 (n:flow_entry list) = Gen.BList.remove_dups_eq (fun (a,b,_) (c,d,_) -> a=c) n
  let compute_hierarchy_aux cnt elist =
    let rec lrr (f1:string)(f2:string):(((string*string*dflow) list)*dflow) =
      let l1 = List.find_all (fun (_,b1,_)-> ((String.compare b1 f1)==0)) elist in
      if ((List.length l1)==0) then
        let i = cnt # inc_and_get in
        let j = cnt # inc_and_get in
        (* let j = (Globals.fresh_int()) in  *)
        let dfl = ((i,j),[(i,j)])in
        ([(f1,f2,dfl)],dfl)
      else
        let init = ((-1,-1), [(-1,-1)]) in
        let ll,((mn,mx),_) = List.fold_left
            (fun (t,((o_min,o_max),_)) (a,b,((c,d),_)) ->
               let temp_l,((n_min, n_max),_) = (lrr a b) in
               let x1 = (if ((o_min== -1)||(n_min<o_min)) then n_min else o_min) in
               let x2 = (if (o_max<n_max) then n_max else o_max)
               in (temp_l@t,((x1,x2),[(x1,x2)])))
            ([],init) l1
        in
        let () = cnt # inc in  (* to account for internal node *)
        let dfl = ((mn,mx+1),[(mn,mx+1)]) in
        (((f1,f2,dfl)::ll) ,dfl)
    in
    let r,_ = (lrr top_flow "") in
    r

  class exc =
    object (self)
      val mutable elist = ([]:flow_entry list)
      val mutable cnt = new counter 0
      method clear = 
        begin
          norm_flow_int := empty_flow;
          c_flow_int := empty_flow;
          ret_flow_int := empty_flow;
          spec_flow_int := empty_flow;
          top_flow_int := empty_flow;
          abnormal_flow_int := empty_flow;
          raisable_flow_int := empty_flow;
          error_flow_int := empty_flow;
          mayerror_flow_int := empty_flow;
          bfail_flow_int := empty_flow;
          elist <- []
        end
      method private sort = 
        begin
          elist <- sort_flow elist (*?? name conflict*)
        end
      method remove_dupl =
        begin
          elist <- remove_dups1 elist
        end
      method private clean =
        begin
          elist <- remove_dups1 elist
        end
      method string_of =
        begin
          let x = elist in
          let el = pr_list (pr_triple pr_id pr_id (string_of_flow)) 
              (List.map (fun (a,e,p) -> (a,e,p)) x) in
          "Exception List : "^(string_of_int (List.length x))^"members \n"^el
        end
      method get_hash (f:string) : dflow =
        begin
          let foo f =
            if (f="") then !top_flow_int
            else if ((String.compare f stub_flow)==0) then 
              Error.report_error {Error.error_loc = no_pos; Error.error_text = ("Error found stub flow")}
            else
              let rec get (lst:(string*string*dflow)list):dflow = match lst with
                | [] -> false_flow_int
                | (a,_,fl)::rst -> if (String.compare f a)==0 then fl
                  else get rst 
              in (get elist)
          in
          (* let pr = pr_pair string_of_int string_of_int in *)
          Debug.no_1 "get_hash" pr_id (fun _ -> "?") foo f
        end
      method get_exc_hash (f:string) : dflow option =
        try
          Some (self # get_hash f)
        with _ -> None
      method add_edge (n1:string)(n2:string):unit =
        begin
          (elist <- elist@ [(n1,n2,false_flow_int)])
        end
      method private reset_exc =
        begin
          let () = self # clean in
          let () = cnt # reset in
          let el = List.fold_left (fun acc (a,b,_) -> 
              if a="" then acc else (a,b,((0,0),[(0,0)]))::acc) [] elist in
          elist <- el
        end
      method private update_values =
        begin
          norm_flow_int := self # get_hash n_flow;
          c_flow_int := self # get_hash c_flow;
          ret_flow_int := self # get_hash ret_flow;
          loop_ret_flow_int := self # get_hash loop_ret_flow;
          spec_flow_int := self # get_hash spec_flow;
          top_flow_int := self # get_hash top_flow;
          raisable_flow_int := self # get_hash raisable_class;
          abnormal_flow_int := self # get_hash abnormal_flow;
          bfail_flow_int := self # get_hash bfail_flow;
          error_flow_int := self # get_hash error_flow;
          mayerror_flow_int := self # get_hash mayerror_flow;
        end
      method compute_hierarchy =
        begin
          let () = self # reset_exc in
          elist <- compute_hierarchy_aux cnt elist;
          self # update_values;
          self # sort
        end
      method get_closest (((min,max):dflow) as nf):(string) =
        begin
          let (s,t)=(get_closest_new elist nf) in
          s ^ (
            if t==0 then "#E" (* exact ann *)
            else if t!=1 then "#P" (* partial ann *)
            else "") (* full *)
          (* fst(get_closest_new elist nf) *)
        end
      method has_cycles : bool =
        begin
          let rec cc (crt:string)(visited:string list):bool =
            let sons = List.fold_left (fun a (d1,d2,_)->if ((String.compare d2 crt)==0) then d1::a else a) [] elist in
            if (List.exists (fun c-> (List.exists (fun d->((String.compare c d)==0)) visited)) sons) then true
            else (List.exists (fun c-> (cc c (c::visited))) sons) in
          (cc top_flow [top_flow])
        end
      method sub_type_obj (t1 : ident) (t2 : ident): bool = 
        begin
          let n1 = self#get_hash t1 in
          let n2 = self#get_hash t2 in
          if (is_false_flow n2) 
          then t1=t2
          else is_subset_flow n1 n2
        end
      method union_flow_ne ((s1,b1):nflow) ((s2,b2):nflow)=
        begin
          ((min s1 s2),(max b1 b2))
        end
      method is_norm_flow (f:nflow) =
        begin
          is_exact_flow f !norm_flow_int
        end
      method is_exc_flow (f:nflow) =
        begin
          is_subset_flow f !raisable_flow_int
        end
      method is_top_flow (f:nflow) =
        begin
          is_exact_flow f !top_flow_int
        end
      method get_min_max (((s,b),_):nflow) =
        begin
          (s,b)
        end
      method mk_nflow_from_min_max (s:int) (b:int) =
        begin
          ((s,b),[(s,b)])
        end
    end
  let exlist = new exc
  let rec sub_type (t1 : typ) (t2 : typ) = 
    match t1,t2 with
    | UNK, _ -> true
    | Named c1, Named c2 ->
      let () = Debug.ninfo_hprint (add_str  "t1 " (string_of_typ)) t1 no_pos in
      let () = Debug.ninfo_hprint (add_str  "t2 " (string_of_typ)) t2 no_pos in
      if c1=c2 then true
      else if c1="" then true
      else exlist # sub_type_obj c1 c2
    | Array (et1,d1), Array (et2,d2) ->
      if (d1 = d2) then sub_type et1 et2
      else false
    | BagT et1, BagT et2 -> sub_type et1 et2
    | List et1, List et2 -> sub_type et1 et2
    | Int, NUM        -> true
    | Float, NUM        -> true
    | p1, p2 -> p1=p2
  ;;
end;;

module GTable = ETABLE_NFLOW

