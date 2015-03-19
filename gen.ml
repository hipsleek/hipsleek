#include "xdebug.cppo"
open VarGen
let silence_output = ref false
(* let no_pos =  *)
(* 	let no_pos1 = { Lexing.pos_fname = ""; *)
(* 				   Lexing.pos_lnum = 0; *)
(* 				   Lexing.pos_bol = 0;  *)
(* 				   Lexing.pos_cnum = 0 } in *)
(* 	{start_pos = no_pos1; mid_pos = no_pos1; end_pos = no_pos1;} *)

(* let is_no_pos l = (l.start_pos.Lexing.pos_cnum == 0) *)
let debug_precise_trace = ref false
let enable_counters = ref false
let profiling = ref false
let profile_threshold = 0.5

module type INC_TYPE =
sig
  type t
  val zero : t
  val inc : t -> t
end;;

module type EQ_TYPE =
sig
  type t
  val zero : t
  val is_zero : t -> bool
  val eq : t -> t -> bool
  val compare : t -> t -> int
  val string_of : t -> string
end;;

module Basic =
(* basic utilities that can be opened *)
struct

  exception Bad_string
  exception Bail

  let silenced_print f s = if !silence_output then () else f s 

  let rec restart f arg =
    try f arg with Unix.Unix_error(Unix.EINTR,_,_) -> print_string"#!Unix_error#";(restart f arg)

  let string_of_pair (p1:'a->string) (p2:'b->string) ((a,b):'a * 'b) : string = 
    "("^(p1 a)^","^(p2 b)^")"

  let rec remove_dups n = 
    match n with
        [] -> []
      | q::qs -> if (List.mem q qs) then remove_dups qs else q::(remove_dups qs)

  let pr_id x = x
  let pr_string x = "\""^x^"\""
  let opt_map f v = match v with Some a -> Some (f a) | None -> None 
  let concatMap f xs =
    let rec aux xs = match xs with
      | [] -> []
      | (x::xs) -> (f x)@(aux xs)
    in aux xs

  let print_endline_quiet s =
    let flag = !compete_mode in
    (* print_endline ("compete mode : "^(string_of_bool flag)); *)
    if flag then () 
    else print_endline s 
  let print_endline_if b s = if b then print_endline s else ()
  let print_string_if b s = if b then print_string s else ()
  let print_string_quiet s = 
    if !compete_mode then () 
    else print_string s 

  let print_web_mode s = 
    if !Globals.tnt_web_mode then print_endline s
    else print_endline_quiet s 

  let print_string_web_mode s = 
    if !Globals.tnt_web_mode then print_string s
    else print_string_quiet s 

  let pr_var_prime (id,p) = match p with
    | Primed -> id^"'"
    | Unprimed -> id

  let print_flush s = print_endline (s); flush stdout

  let pr_no x = "?"
  let pr_none x = "?"

  let pr_unit x = "()"

  let pr_option f x = match x with
    | None -> "None"
    | Some v -> "Some("^(f v)^")"

  let pr_opt = pr_option 

  let pr_opt_int = pr_option string_of_int

  let pr_pair f1 f2 (x,y) = "("^(f1 x)^","^(f2 y)^")"

  let pr_triple f1 f2 f3 (x,y,z) = "("^(f1 x)^","^(f2 y)^","^(f3 z)^")"

  let pr_quad f1 f2 f3 f4 (x,y,z,z2) = "("^(f1 x)^","^(f2 y)^","^(f3 z)^","^(f4 z2)^")"
  let pr_penta f1 f2 f3 f4 f5 (x,y,z,z2,z3) = "("^(f1 x)^",2:"^(f2 y)^",3:"^(f3 z)^",4:"^(f4 z2)^",5:"^(f5 z3)^")"
  let pr_hexa f1 f2 f3 f4 f5 f6 (x,y,z,z2,z3,z4) = "("^(f1 x)^",2:"^(f2 y)^",3:"^(f3 z)^",4:"^(f4 z2)^",5:"^(f5 z3)^",6:"^(f6 z4)^")"

  let pr_hepta f1 f2 f3 f4 f5 f6 f7 (x,y,z,z2,z3,z4,z5) = "("^(f1 x)^",2:"^(f2 y)^",3:"^(f3 z)^",4:"^(f4 z2)^",5:"^(f5 z3)^",6:"^(f6 z4)^",7:"^(f7 z5)^")"

let pr_octa f1 f2 f3 f4 f5 f6 f7 f8 (x,y,z,z2,z3,z4,z5,z6) = "("^(f1 x)^",2:"^(f2 y)^",3:"^(f3 z)^",4:"^(f4 z2)^",5:"^(f5 z3)^",6:"^(f6 z4)^",7:"^(f7 z5)^")"^",8:"^(f8 z6)^")"

  let pr_quad_ln f1 f2 f3 f4 (x,y,z,z2) = "("^(f1 x)^"\n,2:"^(f2 y)^"\n,3:"^(f3 z)^"\n,4:"^(f4 z2)^")"
  let pr_penta_ln f1 f2 f3 f4 f5 (x,y,z,z2,z3) = "("^(f1 x)^"\n,2:"^(f2 y)^"\n,3:"^(f3 z)^"\n,4:"^(f4 z2)^"\n,5:"^(f5 z3)^")"
  let pr_hexa_ln f1 f2 f3 f4 f5 f6 (x,y,z,z2,z3,z4) = "("^(f1 x)^"\n,2:"^(f2 y)^"\n,3:"^(f3 z)^"\n,4:"^(f4 z2)^"\n,5:"^(f5 z3)^"\n,6:"^(f6 z4)^")"
  let pr_hepta_ln f1 f2 f3 f4 f5 f6 f7 (x,y,z,z2,z3,z4,z5) = "("^(f1 x)^"\n,2:"^(f2 y)^"\n,3:"^(f3 z)^"\n,4:"^(f4 z2)^"\n,5:"^(f5 z3)^"\n,6:"^(f6 z4)^"\n,7:"^(f7 z5)^")"

  let pr_add_num f xs =
    let rec aux n xs = 
      match xs with
        | [] -> []
        | x::xs -> ("("^(string_of_int n)^"):"^(f x))::(aux (n+1) xs)
    in aux 1 xs
 
  let pr_lst s f xs = String.concat s (List.map f xs)
  let pr_lst_num s f xs = String.concat s (pr_add_num f xs)

 let pr_list_brk_sep open_b close_b sep f xs  = open_b ^(pr_lst sep f xs)^close_b
 let pr_list_brk open_b close_b f xs  = pr_list_brk_sep open_b close_b "," f xs
 let pr_list f xs = pr_list_brk "[" "]" f xs
 let pr_list_semi f xs = pr_list_brk_sep "[" "]" ";" f xs
 let pr_list_no_brk f xs = pr_list_brk "" "" f xs
 let pr_list_angle f xs = pr_list_brk "<" ">" f xs
 let pr_list_round f xs = pr_list_brk "(" ")" f xs
 let pr_list_round_sep sep f xs = pr_list_brk_sep "(" ")" sep f xs
 let pr_list_ln f xs = "["^(pr_lst ",\n" f xs)^"]"
 let pr_list_num f xs = "["^(pr_lst_num ",\n" f xs)^"]"
 let pr_arr_ln f arr = pr_list_ln f (Array.to_list arr)

 let pr_list_mln f xs = (pr_lst "\n--------------\n" f xs)

 let map_opt f x = match x with 
   | None -> None
   | Some v -> Some (f v)

 let map_opt_res f x = match x with 
   | None -> (None,[])
   | Some v -> let r1,r2 = f v in (Some r1,r2)
   
 let fold_opt f x = match x with 
   | None -> []
   | Some v -> (f v)
  
 let fold_pair1f f (x1,x2) = f x1, f x2
 
 let fold_pair2f f1 f2 (x1,x2) = f1 x1, f2 x2
 
 let map_opt_def def f x = match x with
	| None -> def
	| Some v -> f v

 let map_l_snd f x = List.map (fun (l,c)-> (l,f c)) x
 let map_l_fst f x = List.map (fun (l,c)-> (f l,c)) x
 let map_snd_only f x = List.map (fun (l,c)-> f c) x
 let fold_l_snd f x = List.fold_left (fun a (_,c)-> a@(f c)) []  x
 let fold_l_snd_f fj f st x = List.fold_left (fun a (_,c)-> fj a (f c)) st  x
 let map_l_snd_res f x = List.split (List.map (fun (l,c) -> let r1,r2 = f c in ((l,r1),r2)) x)
 let exists_l_snd f x = List.exists (fun (_,c)-> f c) x
 let all_l_snd f x = List.for_all (fun (_,c)-> f c) x
 
 let add_str s f xs = s^":"^(f xs)

 let opt_to_list o = match o with
   | None -> []
   | Some a -> [a]

 let opt_list_to_list o = match o with
   | None -> []
   | Some a -> a

 let fnone (c:'a):'a option = None

 let is_empty l = match l with [] -> true | _ -> false
 let is_None l = l==None

 let rec last_ne l a  = match l with
   | [] -> a
   | x::xs -> last_ne l x

 let last l = match l with
   | [] -> raise Not_found
   | x::xs -> last_ne l x

 let spacify i = 
   let s' z = List.fold_left (fun x y -> x ^ i ^ y) "" z in
   function [] -> ""
     | [x] -> x
     | x::xs -> x ^ (s' xs)

   (*
    first component of returned value contains the first i values from the list
    second component contains the rest
  *)
 let rec split_at (xs : 'a list) (i : int) : ('a list * 'a list) =
   if i = 0 then ([], xs)
   else
     let a, b = split_at (List.tl xs) (i-1) in
     ((List.hd xs) :: a, b) 

  let rec split3 (l : ('a * 'b * 'c) list) : 'a list * 'b list * 'c list = match l with
    | (h1, h2, h3) :: rest ->
	      let l1, l2, l3 = split3 rest in
		  (h1::l1, h2::l2, h3::l3)
    | [] -> ([], [], [])

  let rec combine3 a b c = match (a, b, c) with
    | (ah::arest, bh::brest, ch::crest) ->
	      let l = combine3 arest brest crest in
		  (ah, bh, ch)::l
    | ([], [], []) -> []
    | _ -> failwith ("combine3: combining lists with different lengths")

  let rec map3 (f : 'a -> 'b -> 'c -> 'd) (a0 : 'a list) (bs : 'b list) (cs : 'c list) : 'd list = 
    match (a0, bs, cs) with
	  | (a :: r1, b :: r2, c :: r3) ->
		    let r = map3 f r1 r2 r3 in
		    (f a b c) :: r
	  | [], [], [] -> []
	  | _ -> failwith ("map3: mapping lists with different lengths.")

  let rec map4 (f : 'a -> 'b -> 'c -> 'd -> 'e) (a0 : 'a list) (bs : 'b list) (cs : 'c list) (ds : 'd list) : 'e list = 
    match (a0, bs, cs, ds) with
	  | (a :: r1, b :: r2, c :: r3, d:: r4) ->
		    let r = map4 f r1 r2 r3 r4 in
		    (f a b c d) :: r
	  | [], [], [], [] -> []
	  | _ -> failwith ("map4: mapping lists with different lengths.")


  let rec repeat (v : 'a) (n : int) : 'a list =
    if n <= 0 then []
    else v :: (repeat v (n-1))

  let report_error pos msg = Error.report_error
     { Error.error_loc = pos; Error.error_text = msg}

  let report_warning pos msg = 
    if !compete_mode then ()
    else 
      Error.report_warning
     { Error.error_loc = pos; Error.error_text = msg}

end;;

module HashUti =
struct
  (* Hashtable stuff *)

  let copy_keys (keys : 'a list) (fr_tab : ('a, 'b) Hashtbl.t) (to_tab : ('a, 'b) Hashtbl.t) =
    let cp_key (k : 'a) = 
	  try
	    let v = Hashtbl.find fr_tab k in
	    Hashtbl.add to_tab k v
	  with
	    | Not_found -> () 
    in
    ignore (List.map cp_key keys)

  let list_of_hash_values (tab : ('a, 'b) Hashtbl.t) : 'b list =
    let append_val k v vl = v::vl in
    Hashtbl.fold append_val tab []

end;;


(* module type CTR_TYPE = *)
(*     sig *)
(*       type t *)
(*       val ctr : t ref *)
(*       val inc : t -> t *)
(*       val add : unit -> t (\* return latest value *\) *)
(*       val reset : unit -> unit *)
(*     end;; *)


module BList =
struct

  (* List-handling stuff *)

  let string_of_f (f:'a->string) (ls:'a list) : string =
    ("["^(String.concat "," (List.map f ls))^"]")

  (** Split the list of length k>=1 into a pair consisting of
      the list of first k-1 elements and the last element. *)
  let rec firsts_last xs = match xs with
    | [] -> failwith "Gen.first_lasts: empty list"
    | [x] -> ([],x)
    | x::xs1 ->
          let (fs,l) = firsts_last xs1 in
          (x::fs,l)

  let rec take n l  = if n<=0 then [] else
    match l with
      | h::t -> h::(take (n-1) t)
      | [] -> []

  let rec drop n l  = if n<=0 then l else
    match l with
      | h::t -> (drop (n-1) t)
      | [] -> []

  (* let remove_elem e l = List.filter (fun x -> x != e) l *)

  (* let rec remove_dups n =  *)
  (*   match n with *)
  (*       [] -> [] *)
  (*     | q::qs -> if (List.mem q qs) then remove_dups qs else q::(remove_dups qs) *)

  (* let mem f x l = List.exists (f x) l *)

  (* let rec find_dups n =  *)
  (*   match n with *)
  (*     | [] -> [] *)
  (*     | q::qs -> if (List.mem q qs) then q::(find_dups qs) else find_dups qs *)

  (* let subset l1 l2 =  *)
  (*   List.for_all (fun x -> (List.mem x l2)) l1 *)

  (* let disjoint l1 l2 =  *)
  (*   List.for_all (fun x -> not (List.mem x l2)) l1 *)

  (* let overlap eq l1 l2 =  *)
  (*   List.exists (fun x -> (List.mem x l2)) l1 *)

  (* let intersect l1 l2 = *)
  (*   List.filter (fun x -> List.mem x l2) l1 *)


  (* let difference l1 l2 = *)
  (*   List.filter (fun x -> not (List.mem x l2)) l1 *)


  (* let list_equal l1 l2 =  *)
  (*   let l = (List.length (intersect l1 l2)) in *)
  (*   ((List.length l1) =  l) && (l = (List.length l2)) *)


  let find_index (f : 'a -> bool) (xs0 : 'a list) : (int * 'a) = 
    let rec helper xs n = match xs with
	  | e :: rest -> 
		    if f e then (n, e)
		    else helper rest (n + 1)
	  | _ -> raise Not_found
    in
    helper xs0 0

  let rec list_last l = match l with
    | h::[] -> h
    | _::t -> (list_last t)
    | [] -> failwith "Gen.list_last: empty list"

  let remove_elem_eq eq e l = List.filter (fun x -> not(eq x e)) l 

  let mem_eq eq x l = List.exists (eq x) l

  let rec remove_dups_eq eq n = 
    match n with
        [] -> []
      | q::qs -> if (mem_eq eq q qs) then remove_dups_eq eq qs else q::(remove_dups_eq eq qs)

  let remove_dups_eq_stable eq n = 
    let rec aux eq n =
    match n with
        [] -> []
      | q::qs -> if (mem_eq eq q qs) then remove_dups_eq eq qs else q::(remove_dups_eq eq qs)
    in List.rev (aux eq (List.rev n))

  let rec remove_dups_eq_reserved_order eq n = 
    match n with
        [] -> []
      | q::qs -> 
          if (mem_eq eq q qs) then 
            q::(remove_dups_eq eq (List.filter (fun p -> not (eq p q)) qs))
          else q::(remove_dups_eq eq qs)

  let rec check_dups_eq eq n = 
    match n with
      | [] -> false
      | q::qs -> if (List.exists (fun c-> eq q c) qs) then true else check_dups_eq eq qs 

  let rec get_all_pairs ls = match ls with
    | [] -> []
    | c::cs -> 
          let lst = List.map (fun x -> (c,x)) cs in
          lst @ (get_all_pairs cs)

  let check_no_dups_eq eq n = not(check_dups_eq eq n)

  let subset_eq eq l1 l2 =
    List.for_all (fun x -> (mem_eq eq x l2)) l1

  let disjoint_eq eq l1 l2 =
    List.for_all (fun x -> not (mem_eq eq x l2)) l1

  let overlap_eq eq l1 l2 =
	if (l2 == []) then false
	else List.exists (fun x -> (mem_eq eq x l2)) l1

  let rec find_dups_eq eq n =
    match n with
      | [] -> []
      | q::qs -> if (List.exists (eq q) qs) then q::(find_dups_eq eq qs) else find_dups_eq eq qs

  let rec find_one_dup_eq eq (xs : 'a list) =
    match xs with
	  | [] -> []
	  | x::rest -> if List.exists (eq x) rest then [x] else find_one_dup_eq eq rest

  let mem_eq eq x ls =
    List.exists (fun e -> eq x e) ls

  let intersect_eq eq l1 l2 =
    List.filter (fun x -> List.exists (eq x) l2) l1

  let difference_eq eq l1 l2 =
    List.filter (fun x -> not (List.exists (eq x) l2)) l1

  let diff_split_eq eq l1 l2 =
    List.partition (fun x -> not (List.exists (eq x) l2)) l1

  let list_subset_eq eq l1 l2 = 
    let l = (List.length (difference_eq eq l1 l2)) in
    l==0

  (* change name to setequal *)
  let list_setequal_eq eq l1 l2 = 
    (list_subset_eq eq l1 l2) && (list_subset_eq eq l2 l1) 

  let list_equiv_eq eq l1 l2 = 
    try
      List.for_all2 eq l1 l2
    with _ -> false

  let rec list_find (f:'a -> 'b option) l = match l with 
    | [] -> None
    | x::xs -> match f x with
        | None -> list_find f xs
        | Some s -> Some s
  let add_index l =
	let rec helper id l = match l with 
		| [] -> []
		| h::t -> (id,h)::(helper (id+1) t) in
	helper 0 l
end;;

module BListEQ =
    functor (Elt : EQ_TYPE) ->
struct
  type elem = Elt.t
  type elist = elem list
  let eq = Elt.eq
  let string_of_elem = Elt.string_of
  (* let rec compare (l1:elist) (l2:elist) = *)
  (*   begin *)
  (*     match l1,l2 with *)
  (*       | [],[] -> 0 *)
  (*       | [],x::_ -> -1 *)
  (*       | x::_,[] -> 1 *)
  (*       | a::t1,b::t2 ->  *)
  (*             let c = Elt.compare a b in *)
  (*             if c==0 then *)
  (*               compare t1 t2 *)
  (*             else c *)
    (* end *)
  include BList
  let mem x l = List.exists (eq x) l
  let string_of (ls:'a list) : string 
        = string_of_f string_of_elem ls

  let rec check_dups n = 
    match n with
      | [] -> false
      | q::qs -> if (List.exists (fun c-> eq q c) qs) then true  else check_dups qs 

  let rec find_dups n = 
    match n with
      | [] -> []
      | q::qs -> if (List.exists (eq q) qs) then q::(find_dups qs) else find_dups qs

  let rec find_one_dup (xs : 'a list) =
    match xs with
	  | [] -> []
	  | x::rest -> if List.exists (eq x) rest then [x] else find_one_dup rest

  let overlap l1 l2 = 
    List.exists (fun x -> (mem x l2)) l1

  let intersect l1 l2 =
    List.filter (fun x -> List.exists (eq x) l2) l1  

  let difference l1 l2 =
    List.filter (fun x -> not (List.exists (eq x) l2)) l1

  let list_equal l1 l2 = 
    let l = (List.length (intersect l1 l2)) in
    ((List.length l1) =  l) && (l = (List.length l2))

end;;


exception Stack_Error

class ['a] mut_option =
  object (self)
     val mutable init_flag = false
     val mutable value = (None:'a option)
     method is_init  = init_flag
     method get = value
     method set (i:'a option) = 
       begin
         if init_flag then ()
         else (init_flag = true; value <- i)
       end
     method set_fn f =
       begin
         if (init_flag)  then ()
         else (init_flag = true; value <- f ())
       end
   end;;

class change_flag =
   object 
     val mutable cnt = 0
     method reset = 
       begin
         cnt <- 0
       end
     method inc = 
       begin
         cnt <- cnt+1
       end
     method exceed n = cnt>n
     method is_change = cnt>0
     method no_change = (cnt==0)
   end;;

class ['a] stack  =
  object (self)
     val mutable stk = []
     method push (i:'a) = 
       begin
         stk <- i::stk
       end
     method get_stk  = stk (* return entire content of stack *)
     method set_stk newstk  = stk <- newstk 
       (* override with a new stack *)
     method pop = match stk with 
       | [] -> print_string "ERROR : popping empty stack"; 
               raise Stack_Error
       | x::xs -> stk <- xs
     method pop_top = match stk with 
       | [] -> print_string "ERROR : popping empty stack"; 
               raise Stack_Error
       | x::xs -> stk <- xs; x
     method top : 'a = match stk with 
       | [] -> print_string "ERROR : top of empty stack"; 
               raise Stack_Error
       | x::xs -> x
     method pop_no_exc = match stk with 
       | [] -> () 
       | x::xs -> stk <- xs
     method is_empty = stk == []
     method is_avail = not(stk == [])
     method get = self # top
     (* method set x = self # push x *)
     method len = List.length stk
     method reverse = stk <- List.rev stk
     method reverse_of = List.rev stk
     method mem (i:'a) = List.mem i stk 
     method mem_eq eq (i:'a) = List.exists (fun b -> eq i b) stk 
     method find f = List.find f stk
     (* method exists (i:'a) = List.mem i stk  *)
     (* method exists_eq eq (i:'a) = List.exists (fun b -> eq i b) stk  *)
     method exists f = List.exists f stk 
     method push_list (ls:'a list) =  stk <- ls@stk
     method pop_list (ls:'a list) = 
       stk <- BList.drop (List.length ls) stk
     method pop_list_n (n: int) = 
       stk <- BList.drop n stk
     method reset = stk <- []
     method clone =
       Oo.copy self
       (* let n = new Gen.stack in *)
       (*   let lst = self # get_stk in *)
       (*   let () = n # push_list lst in *)
       (* n *)
   end;;

class ['a] stack_pr (epr:'a->string) (eq:'a->'a->bool)  =
object 
  inherit ['a] stack as super
  val elem_pr = epr 
  val elem_eq = eq 
  method string_of = Basic.pr_list_ln elem_pr stk
  method string_of_no_ln = Basic.pr_list elem_pr stk
  method string_of_no_ln_rev = 
    let s = super#reverse_of in
    Basic.pr_list elem_pr s
  method string_of_reverse = 
    let s = super#reverse_of  in
    Basic.pr_list_ln elem_pr s
  method string_of_reverse_log = 
    let s = super#reverse_of  in
    Basic.pr_list_mln elem_pr s
  method mem (i:'a) = List.exists (elem_eq i) stk
  method overlap (ls:'a list) = 
    if (ls == []) then false
    else List.exists (fun x -> List.exists (elem_eq x) ls) stk
end;;


class ['a] stack_filter (epr:'a->string) (eq:'a->'a->bool) (fil:'a->bool)  =
   object 
     inherit ['a] stack_pr epr eq as super
     val filter_fn = fil
     method filter = stk <- List.filter fil stk
     method string_of_reverse_log_filter = 
       stk <- List.filter fil stk;
       super#string_of_no_ln_rev
           (* string_of_reverse_log *)
   end;;

class ['a] stack_noexc (x_init:'a) (epr:'a->string) (eq:'a->'a->bool)  =
   object 
     inherit ['a] stack_pr epr eq
     val emp_val = x_init
     method top_no_exc : 'a = match stk with 
       | [] ->  emp_val
       | x::xs -> x
     method last : 'a = match stk with 
       | [] -> emp_val
       | _ -> List.hd (List.rev stk)
     method pop_top_no_exc = match stk with 
       | [] -> emp_val
       | x::xs -> stk <- xs; x
   end;;

(* class ['a] stack_noexc (x_init:'a) (epr:'a->string) (eq:'a->'a->bool)  = *)
(*    object  *)
(*      inherit ['a] stack *)
(*      val emp_val = x_init *)
(*      val elem_pr = epr  *)
(*      val elem_eq = eq  *)
(*      method top_no_exc : 'a = match stk with  *)
(*        | [] ->  emp_val *)
(*        | x::xs -> x *)
(*      method string_of = Basic.pr_list elem_pr stk *)
(*      method mem (i:'a) = List.exists (elem_eq i) stk *)
(*      method overlap (ls:'a list) =  *)
(* 	   if (ls == []) then false *)
(* 	   else List.exists (fun x -> List.exists (elem_eq x) ls) stk *)
(* (\* Gen.BList.overlap_eq elem_eq ls stk *\) *)
(*    end;; *)

class counter x_init =
   object 
     val mutable ctr = x_init
     method get : int = ctr
     method inc = ctr <- ctr + 1
     method inc_and_get = ctr <- ctr + 1; ctr
     method add (i:int) = ctr <- ctr + i
     method reset = ctr <- 0x0
     method string_of : string= (string_of_int ctr)
     method str_get_next : string 
     = ctr <- ctr + 1; string_of_int ctr
   end;;

(* class ['a] stack2 xinit = *)
(*    object  *)
(* 	val def = xinit *)
(* 	val mutable stk = [] *)
(* 	method push (i:'a) = stk <- i::stk *)
(* 	method pop = match stk with  *)
(*        | [] -> raise Stack_Error *)
(*        | x::xs -> stk <- xs *)
(*    method top : 'a = match stk with  *)
(*        | [] -> def *)
(*        | x::xs -> x *)
(* 	method len = List.length stk *)
(* end;; *)

(* class ['a] stack3  = *)
(*    object  *)
(* 	val mutable stk = [] *)
(* 	method push (i:'a) = stk <- i::stk *)
(* 	method pop = match stk with  *)
(*        | [] -> raise Stack_Error *)
(*        | x::xs -> stk <- xs *)
(*    method top : 'a = match stk with  *)
(*        | [] -> raise Stack_Error *)
(*        | x::xs -> x *)
(* 	method len = List.length stk *)
(* end;; *)

(* module Stack4  = *)
(*    struct  *)
(*     type a  *)
(* 	let push (i:'a) stk = i::!stk *)
(* 	let pop stk  = match stk with  *)
(*        | [] -> raise Stack_Error *)
(*        | x::xs -> xs *)
(*     let top stk  = match stk with  *)
(*        | [] -> raise Stack_Error *)
(*        | x::xs -> x *)
(*     let len stk : int = List.length stk *)
(* end;; *)

module type EQType = sig
   type a
	val eq: a -> a -> bool
	val string_of : a -> string
end;;

module EQInt : EQType = struct
   type a = int
	let eq x y = (x==y)
	let string_of x = string_of_int x
end;;

module EQList =
 functor (Elt: EQType) ->
   struct 
   type a = Elt.a list
   let rec eq x y = match x,y with
      | [],[] -> true
      | x::xs,y::ys -> (Elt.eq x y) && (eq xs ys)
      | _,_ -> false
   let string_of xs = 
     let o = List.map (Elt.string_of) xs
     in "["^(String.concat "," o)^"]"
end;;

module EQListInt : EQType = EQList(EQInt);;

module ErrorUti =
struct
  (** Error-handling functions. *)

  (* let (stkint:int stack2) = new stack2 (-1) *)

  (* let (stkint:int stack3) = new stack3  *)

  let error_list = new stack_noexc "error - stack underflow" (fun x -> x) (=)

  let warning_no  = new counter 0

  let no_errors () = (error_list#len = 0)

  let err loc msg = 
    error_list#push (loc ^ ": error: "^msg)

  let error msg = (print_string (msg ^"\n"); flush_all(); err "" msg)
  let print_errors () = 
    List.iter (function x -> print_string (x ^ "\n")) error_list#get_stk;
    print_string (string_of_int (error_list#len)^" errors.\n");
    print_string "The program is INVALID\n";
    exit 2

  let warn msg = 
    warning_no #inc;
    Basic.print_string_quiet ("*** Warning: "^ msg ^ "\n"); flush_all()

  let warn_if_none ov msg = match ov with
    | None -> warn msg
    | Some _ -> ()

  let fail s =   
    print_string (s ^ "\n"); 
    Printf.printf "There were %d warnings.\n" warning_no#get;
    flush_all();
    failwith s

end;;

let add_str s f xs = s^":"^(f xs)

type 'a keyt = int option

let key_cnt = new counter 0

let new_key () =
  let x = key_cnt # inc_and_get in
  Some x


module EqMap =
    functor (Elt : EQ_TYPE) ->
struct
  type elem = Elt.t
  type key = elem keyt
  type emap = (elem * key) list
  type epart = (elem list) list
  type elist = (elem list) 
  type epair = ((elem * elem) list) 
  open Basic

  let eq = Elt.eq 
  let string_of_elem = Elt.string_of 
  (* let string_of_emap = Basic.pr_list (fun (e,_) -> Elt.string_of e) *)
  (* let string_of_epart = Basic.pr_list (Basic.pr_list Elt.string_of) *)

  let emap_sort s = List.sort (fun (e1,_) (e2,_) -> Elt.compare e1 e2) s 

(* TODO : rec03.slk bug here *)
(* partition@53 *)
(* partition inp1 :emap[{_null,x3,y1,y2}] *)
(* [(y1,Some(22)),(_null,Some(22)),(y3,Some(23)),(y2,Some(22)),(x3,Some(22))] *)
(* partition@53 EXIT:[[_null,x3,y1,y2]] *)

  (* TODO : can we get in sorted order by elem *)
  (* let partition (s: emap) : epart = *)
  (*   let s = emap_sort s in *)
  (*   let rec insert  a k  acc =  *)
  (*     match acc with *)
  (*       | [] -> [(k,[a])] *)
  (*       | ((k2,ls) as p)::xs ->  *)
  (*             if (k=k2) then (k,a::ls)::xs *)
  (*             else p::(insert a k xs) in *)
  (*   let r = List.fold_left (fun acc (a,k) ->  insert a k acc) [] s in *)
  (*   let r = List.filter (fun (_,x) -> List.length x > 1) r in *)
  (*   (\* let r = List.rev r in *\) *)
  (*   let r = List.map ( fun (_,b) -> List.rev b) r in *)
  (*   r *)
    (* print_endline ((add_str "emap" string_of_emap) s); *)
    (* print_endline ((add_str "epart" string_of_epart) r); *)

  (* let partition (s: emap) : epart = *)
  (*   Debug.no_1 "partition" string_of_emap string_of_epart partition s *)

  let compare_key k1 k2 =
    match k1,k2 with
      | None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some n1, Some n2 -> 
            if n1=n2 then 0
            else if n1<n2 then -1 else 1
  let compare_v (e1,k1) (e2,k2) =
    let x1 =compare_key k1 k2 in
    if x1=0 then -(Elt.compare e1 e2)
    else x1

  let compare_list cmp b1 b2 =
    let rec aux b1 b2 =
    match b1,b2 with
      | [],[] -> 0
      | [],_ -> -1
      | _,[] ->1
      | (x::xs),(y::ys) ->
            let c = cmp x y in
            if c==0 then aux xs ys
            else c
    in aux b1 b2

  let partition (s: emap) : epart =
    let s = List.sort compare_v s in
    let rec aux k ls s =
      match s with
        | [] -> [ls]
        | (e2,k2)::ss -> if k==k2 then aux k (e2::ls) ss
          else ls::(aux k2 [e2] ss) in
    let ans = match s with 
      | [] -> []
      | (e,k)::ss -> aux k [e] ss in
    let ans = List.filter (fun x -> List.length x>1) ans in
    List.sort (compare_list Elt.compare) ans

    let string_of (e: emap) : string =
      let f = string_of_elem in
      let ll = partition e in 
      (* let ll = List.filter (fun v -> List.length v > 1) ll in *)

      "emap["^ (String.concat ";" (List.map (fun cl -> "{"^(String.concat ","(List.map f cl))^"}") ll))^"]"

  let key_string_of = pr_option string_of_int

  let string_of_debug (e: emap) : string =
    (* (string_of e)^"\n"^ *)
        (pr_list (pr_pair Elt.string_of key_string_of) e)

  let un_partition (ll:epart) : emap =
    let flat xs = 
      if (List.length xs>1) then 
        let newk = new_key () in
        List.map (fun x -> (x,newk)) xs 
      else [] in
    List.concat (List.map (fun x -> flat x) ll)

  let mkEmpty : emap = []

  let is_empty (m:emap) = match m with | [] -> true | _ -> false

  let find_aux (s: emap) (e:elem) (d:key) : key =
    try
      snd(List.find (fun (e1,_) -> eq e e1) s)
    with
        _ -> d

  (* find key of e in s *)
  let find (s : emap) (e:elem) : key  = find_aux s e None

  (* find key of e in s and return remainder after
     all elements equivalent to e is removed *)
  let find_remove (s : emap) (e:elem) : key * emap  = 
    let r1 = find_aux s e None in
    (r1, if r1==None then s else List.filter (fun (e2,_)-> not(eq e e2)) s)

  (* returns s |- x=y *)
  let is_equiv (s: emap)  (x:elem) (y:elem) : bool =
    if (eq x y) then true
    else
      let r1 = find s x in
      let r2 = find s y in
      (r1==r2 && not(r1==None))

  (* add x=y to e-set s and returning a new e-set with
     extra elements added *)
  let add_equiv  (s: emap) (x:elem) (y:elem) : emap = 
    if (eq x y) then s
    else
      let r1 = find s x in
      let r2 = find s y in
      begin
      match r1 with
        | None -> 
              begin
                match r2 with
                  | None ->
                        let r3 = new_key () in
                        (x,r3)::((y,r3)::s)
                  | _ -> (x,r2)::s
              end
        | _ -> 
              begin
                match r2 with
                  | None ->  (y,r1)::s
                  | _ -> 
                        begin
                          if r1==r2 then s
                          else
                            (* let r3=new_key() in *)
                            List.map (fun ((a,b) as ar) -> 
                                if (b==r1) then (a,r2) else ar) s
                        end
              end
      end

  let build_eset (xs:(elem * elem) list) :  emap =
    let pr1 = Basic.pr_pair Elt.string_of Elt.string_of in
    let p_aset = List.fold_left (fun eqs (x,y) ->
        add_equiv eqs x y
    ) mkEmpty xs in
    p_aset

  let mem x ls =
    List.exists (fun e -> eq x e) ls

  let overlap l1 l2 = 
    List.exists (fun x -> (mem x l2)) l1

  (* this method is used to merge two partitions 
     which may have different keys *)
  (* split out sub-lists in l which overlaps with x *)
  let split_partition (x:elist) (l:epart): (epart * epart) =
    List.fold_left ( fun (r1,r2) y -> if (overlap x y) then (y::r1,r2) else (r1,y::r2)) ([],[]) l

  (* merge l1 /\ l2 to [[a]] *)
  let rec merge_partition (l1:epart) (l2:epart) : epart = match l1 with
    | [] -> l2
    | x::xs ->
          let (y,ys)=split_partition x l2 in
          if y==[] then x::(merge_partition xs l2)
          else merge_partition xs ((x@(List.concat y))::ys)
            (*remove dupl of x*)

  (* return the domain of e-set *)
  let domain (s: emap) : elist = List.map fst s

  (* return list of elements in e_set *)
  let get_elems (s:emap) : elist = domain s

  (* return pairs of equivalent elements from e_set *)
  let get_equiv (s:emap) : epair = 
    let ll = partition s in
    let make_p l = match l with
      | [] -> []
      | x::xs -> List.map (fun b -> (x,b)) xs in
    List.concat (List.map make_p ll)

  let order_two (l1:'a list) (l2:'a list) : ('a list * 'a list) =
    if (List.length l1)>(List.length l2) then (l2,l1)
    else (l1,l2)

  (* merge two equivalence sets s1 /\ s2 *)
  let merge_eset (t1: emap) (t2: emap): emap =
    let r =
      let (t1,t2) = order_two t1 t2 in
      List.fold_left (fun a (p1,p2) -> add_equiv a p1 p2) t2 (get_equiv t1) in
    let pr = string_of_debug in
    (* let () = print_endline ("eset1 :"^ (pr t1)) in *)
    (* let () = print_endline ("eset2 :"^ (pr t2)) in *)
    (* let () = print_endline ("eset_out :"^ (pr r)) in *)
    r

    (* remove key e from e_set  *)
  let elim_elems_one  (s:emap) (e:elem) : emap = 
    List.filter (fun (a,k2) -> not(eq a e)) s

  let elim_elems  (s:emap) (e:elem list) : emap = 
    List.filter (fun (a,k2) -> not(mem a e)) s

  (* return all elements equivalent to e, including itself *)
  let find_equiv_all  (e:elem) (s:emap) : elist  =
    let r1 = find s e in
    if (r1==None) then []
    else List.map fst (List.filter (fun (a,k) -> k==r1) s) 
  
  (* return a distinct element equal to e *)
  let find_equiv  (e:elem) (s:emap) : elem option  =
    let ls=find_equiv_all e s in
    try 
      let p = List.find (fun x -> not(eq x e)) ls in
      Some p
    with _ -> None

  (* return an element r that is equiv to e but distinct from it, and elim e from e_set *)
  let find_equiv_elim_sure (e:elem) (s:emap) : elem option * emap  =
    let r1,s1 = find_remove s e in
    if (r1==None) then (None,s)
    else let (ls,ls2) = List.partition (fun (a,k) -> k==r1 ) s1 in
    match ls with
      | [] -> (None,s1)
      | [(x,_)] -> (Some x, ls2)
      | (x,_)::_ -> (Some x, s1)

(* return a distinct element equal to e and elim e from e_set if found *)
  let find_equiv_elim (e:elem) (s:emap) : (elem * emap) option  = 
    let (ne,ns) = find_equiv_elim_sure e s in
    match ne with
      | None -> None
      | Some x -> Some (x, ns) 

  (* make fv=tv and then eliminate fv *)
  (* fv should never be constant *)
  (* let subs_eset   ((fv,tv):elem * elem) (s:emap) : emap =  *)
  (*   if (eq fv tv) then s *)
  (*   else *)
  (*     let r1 = find s fv in *)
  (*     if (r1==None) then s *)
  (*     else  *)
  (*       let ns = add_equiv s fv tv in *)
  (*       elim_elems_one ns fv *)

  (* TODO : will below suffer name-calsh *)
  (* let subs_eset_par   (f_t_ls:(elem * elem) list) (s:emap) : emap =  *)
  (*   List.fold_left (fun e p -> subs_eset p e) s f_t_ls *)


  let subs_elem sst a =
    try 
      let (_,b) = List.find (fun (x,_) -> Elt.compare a x == 0) sst in
      b
    with _ -> a

  let subs_eset_par   (f_t_ls:(elem * elem) list) (s:emap) : emap = 
    let new_s = List.map (fun (a,k) -> (subs_elem f_t_ls a,k)) s in
    emap_sort new_s


  (* returns true if s contains no duplicates *)
  (* let check_no_dupl (s:elist) : bool = *)
  (*   let rec helper s = match s with *)
  (*     | [] -> true *)
  (*     | x::xs ->  *)
  (*           if mem x xs then false *)
  (*           else helper xs in *)
  (*   helper s *)

  let check_no_dups (s:elist) : bool = not(BList.check_dups_eq eq s)

  (* check f is 1-to-1 map assuming s contains no duplicates *)
  let is_one2one (f:elem -> elem) (s:elist) : bool =
    let l = List.map f s in
    if (check_no_dups l) then true
    else (print_string ("duplicates here :"^(BList.string_of_f string_of_elem l)^"\n") ; false) 

  (* rename the elements of e_set *)
  (* pre : f must be 1-to-1 map *)
  let rename_eset (f:elem -> elem) (s:emap) : emap = 
    let b = is_one2one f (get_elems s) in
    if b then  List.map (fun (e,k) -> (f e,k)) s
    else Error.report_error {Error.error_loc = no_pos; 
    Error.error_text = ("rename_eset : f is not 1-to-1 map")}

  let rename_eset_with_key (f:elem -> elem) (s:emap) : emap = 
    let b = is_one2one f (get_elems s) in
    if b then  List.map (fun (e,k) -> (f e, k)) s
    else Error.report_error {Error.error_loc = no_pos; 
    Error.error_text = ("rename_eset : f is not 1-to-1 map")}

  (* s - from var; t - to var *)
  let norm_subs_eq (subs:epair) : epair =
    let rec add (f,t) acc = match acc with
      | [] -> [[(f,t)]]
      | (a::acc) -> if eq (snd (List.hd a)) t then ((f,t)::a)::acc
        else a::(add (f,t) acc) in
    let rec part xs acc = match xs with
      | [] -> acc
      | (x::xs) -> part xs (add x acc) in
    let pp = part subs [] in
    let rec mkeq xs = match xs with
      | (a1,b1)::((a2,b2)::xs) -> (a1,a2)::(mkeq ((a2,b2)::xs))
      | _ -> [] in
    let eqlst = List.fold_left (fun l x -> (mkeq x) @ l) [] pp in
    eqlst

  let rename_eset_allow_clash (f:elem -> elem) (s:emap) : emap =
	let sl = get_elems s in
	let tl = List.map f sl in
	if (BList.check_no_dups_eq eq tl) then
      List.map (fun (e,k) -> (f e,k)) s
	else
	  let s1 = List.combine sl tl in
	  let e2= norm_subs_eq s1 in
	  let ns = List.fold_left (fun s (a1,a2) -> add_equiv s a1 a2) s e2 in
      List.map (fun (e,k) -> (f e,k)) ns

  (* given existential evars and an eset, return a set of substitution *)
  (* from evars to free vars, where possible *)
  (* if not possible, return subs to the first existential var found *)
  (* [v] [v=w, v=y] ---> [(v,w)] *)
  (* [v,y] [v=w, v=y] ---> [(v,w),(y,w)] *)
  (* [v,y,w] [v=w, v=y] ---> [(v,v),(w,v),(y,v)] *)
  let build_subs_4_evars evars eset =
    let rec aux ev  =
      match ev with 
        | [] -> []
        | e::evs -> 
              let eqlist = find_equiv_all e eset in
              let (bound,free) = List.partition (fun c -> BList.mem_eq eq c evars) eqlist in
              let (used,rest) = List.partition (fun c -> BList.mem_eq eq c bound) evs in
              let target = match free with 
                | [] -> e
                | h::_ -> h in
              let nsubs = List.map (fun x -> (x,target)) (e::used) in
              nsubs@(aux rest)
    in aux evars
end;;

module ID =
struct 
  type t = string
  let zero = ""
  let is_zero t = (t="")
  let eq = fun s1 s2 -> String.compare s1 s2 = 0
  let string_of = fun s -> s
  let compare = String.compare
end;;

module EMapID = EqMap(ID);;


let find_close_ids ids equivs=
  if equivs = [] then ids else
  match ids with
    | [] -> []
    | [x] -> [x]
    | sv0::rest -> let tpl0 = EMapID.mkEmpty in
      let tpl1 = List.fold_left (fun tpl sv1 -> EMapID.add_equiv tpl sv0 sv1) tpl0 rest in
      let tpl2 = List.fold_left (fun tpl (sv1,sv2) -> EMapID.add_equiv tpl sv1 sv2) tpl1 equivs in
      EMapID.find_equiv_all sv0 tpl2


module INT =
struct
  type t = int
  let zero = 0
  let inc x = 1+x
end;;

module IntCtr =
    functor (Elt : INC_TYPE) ->
struct
  type vtype = Elt.t
  type reftype = vtype ref
  let zero = Elt.zero
  let ctr = ref zero
  let reset () = ctr := zero
  let inc () : unit = 
    let v = Elt.inc (!ctr) in (ctr:=v)
end;;


type elem = int

(* class [’a] refa x_init =  *)
(*    object  *)
(*      val mutable x = (x_init : ’a) *)
(*      method get = x *)
(*      method set y = x <- y *)
(*    end;; *)


module StackTrace =
struct 
  (* keep track of calls being traced by ho_debug *)
  let ctr = new counter 0
    
  (* type stack = int list *)
  (* stack of calls being traced by ho_debug *)
  let debug_stk = new stack_noexc (-2) string_of_int (=)

  (* stack of calls with detailed tracing *)
  let dd_stk = new stack

  (* let force_dd_print () = *)
  (*   let d = dd_stk # get_stk in *)
  (*   debug_stk # overlap d *)

  let is_same_dd_get () =
    if dd_stk # is_empty then None
    else 
      let v1 = dd_stk # top in
      let v2 = debug_stk # top in
      (* let l1 = dd_stk # get_stk in *)
      (* let l2 = debug_stk # get_stk in *)
      (* let pr = Basic.pr_list string_of_int in *)
      (* let () = print_endline ("ddstk:"^(pr l1)^" hostk:"^(pr l2)) in *)
       if (v1=v2) then Some v1 else None

  let is_same_dd () =
    match (is_same_dd_get()) 
    with | None -> false
      | _ -> true

  (* pop last element from call stack of ho debug *)
  let pop_call () = 
    if is_same_dd () then dd_stk # pop;
    debug_stk # pop

  (* call f and pop its trace in call stack of ho debug *)
  let pop_aft_apply_with_exc (f:'a->'b) (e:'a) : 'b =
    let r = (try 
      (f e)
    with exc -> (pop_call(); raise exc))
    in pop_call(); r

  (* call f and pop its trace in call stack of ho debug *)
  let pop_aft_apply_with_exc_no (f:'a->'b) (e:'a) : 'b =
    try 
      let r = (f e) in
      if !debug_precise_trace then debug_stk # pop; 
      r
    with exc -> 
        begin
          if !debug_precise_trace then debug_stk # pop; 
          raise exc
        end

  (* string representation of call stack of ho_debug *)
  let string_of () : string =
    let h = debug_stk#get_stk in
    (* ("Length is:"^(string_of_int (List.length h))) *)
    String.concat "@" (List.map string_of_int (List.filter (fun n -> n>0) h) )

  let push_no_call () =
    if !debug_precise_trace then debug_stk # push (-3)
    else ()

  (* returns @n and @n1;n2;.. for a new call being debugged *)
  let push_call_gen (os:string) (flag_detail:bool) : (string * string) = 
    (* let () = print_endline ("\npush_call_gen:"^os^(string_of_bool flag_detail)) in *)
    ctr#inc;
    let v = ctr#get in
    debug_stk#push v; 
    if flag_detail then dd_stk#push v;
    let s = os^"@"^(string_of_int v) in
    let h = os^"@"^string_of() in
    s,h

  (* push call without detailed tracing *)
  let push_call (os:string) : (string * string) = 
    push_call_gen os false

  (* push call with detailed tracing *)
  let push_call_dd (os:string) : (string * string) = 
    push_call_gen os true

end;;


module type MEM_TYPE =
sig
  type t
  type ef = t -> t -> bool
  type tlist = t list
  val eq : ef
  val overlap : t -> t -> bool
  val sat : t -> bool
   val intersect : tlist -> tlist -> tlist (* /\ *)
    (* under approx or-ing *)
  val overlap_eq : ef -> t -> t -> bool
  val intersect_eq : ef -> tlist -> tlist -> tlist (* /\ *)
  val star_union : tlist -> tlist -> tlist (* @ *)
    (* combine by star, without normalization *)
  val string_of : t -> string
end;;

module type PTR_TYPE =
sig
  type t
  type ef = t -> t -> bool
  type tlist = t list
  val zero : t
  val is_zero : t -> bool
  val eq : ef
  val intersect_eq : ef -> tlist -> tlist -> tlist
  val intersect : tlist -> tlist -> tlist
  val string_of : t -> string
  val compare : t -> t -> int
end;;

module type EQ_PTR_TYPE =
    functor (Elt:EQ_TYPE) ->
    sig
      open Elt
      type a =Elt.t
      type tlist = t list
      type ef = t -> t -> bool
      val intersect : tlist -> tlist -> tlist
      val intersect_eq : ef -> tlist -> tlist -> tlist
    end;;


module Baga =
    functor (Elt : MEM_TYPE) ->
struct
  type ptr = Elt.t
  type baga = ptr list

  let mkEmpty : baga = []
  let eq = Elt.eq
  let overlap = Elt.overlap
  let intersect = Elt.intersect
  let overlap_eq = Elt.overlap_eq
  let intersect_eq = Elt.intersect_eq
  let star_union = Elt.star_union

  (* need a semantic overlap operator that takes
     aliasing into account *)

  (* a singleton bag *)
  let singleton_baga (e:ptr) : baga = [e]

  let string_of (b:baga) : string =
    Basic.pr_list (Elt.string_of) b

  let rec is_dupl_baga_eq eq (xs:baga) : bool = 
    match xs with
      | [] -> false
      | x::xs1 -> if not(Elt.sat x) then true
          else match xs1 with
          | [] -> false
          | _ -> if (List.exists (overlap_eq eq x) xs1) then true else is_dupl_baga_eq eq xs1

  let is_dupl_baga (xs:baga) : bool = is_dupl_baga_eq eq xs

  (* false result denotes contradiction *)
  let is_sat_baga_eq eq (xs:baga) : bool = 
    let r= not(is_dupl_baga_eq eq xs) in
    begin
      Basic.print_endline_quiet ("is_sat_baga_eq("^(string_of xs)^")="^(string_of_bool r));
      r
    end

  (* false result denotes contradiction *)
  let is_sat_baga (xs:baga) : bool = 
    let r = not(is_dupl_baga xs) in
    begin
      Basic.print_endline_quiet ("is_sat_baga("^(string_of xs)^")="^(string_of_bool r));
      r
    end


  (*
\    [d1,d2] & [d3,d4] = [d1,d2,d3,d4]
    [d1,d2] | [d3,d4] = [d1|d3,d1|d4,d2|d3,d2|d4]
    d1|d3 = d1 \cap d3
  *)

  (* star conjunction of two bag of addresses *)
  let star_baga (x:baga) (y:baga) : baga = star_union x y

  (* conjunction of two bag of addresses *)
  let conj_baga_eq eq (xs:baga) (ys:baga) : baga = intersect_eq eq xs ys

  (* conjunction of two bag of addresses *)
  let conj_baga (xs:baga) (ys:baga) : baga = intersect xs ys

  (* disjunction of two bag of addresses *)
  let or_baga (xs:baga) (ys:baga) : baga = intersect xs ys

  (* disjunction of two bag of addresses *)
  let or_baga_eq eq (xs:baga) (ys:baga) : baga = intersect_eq eq xs ys


end;;

module DisjSet =
    functor (Elt : PTR_TYPE) ->
struct
  type ptr = Elt.t

  (* disjointness structures*)
  type dlist = (ptr list) 
  type dpart = dlist list
      (* module BG = Baga(Elt) *)
  let eq = Elt.eq
  let intersect = Elt.intersect

  module BL_EQ = BListEQ(Elt)
  open BL_EQ

  (* let is_dupl_baga _ = true *)

  let string_of xs = Basic.pr_list (Basic.pr_list Elt.string_of) xs

  (* an empty difference set *)
  let mkEmpty : dpart = []

  (* an empty difference set *)
  let is_empty (d:dpart) : bool = (d==[])

  (* one list difference set *)
  let one_list_dset (e:dlist) : dpart = [e]

  (* a singleton difference set *)
  let singleton_dset (e:ptr) : dpart = [[e]]

  let is_dupl_dset (xs:dpart) : bool =
    List.exists (check_dups) xs

  let is_mem_dset e (el:dpart): bool =
    let ls = (List.filter (fun l -> List.exists (fun x -> eq e x) l) el) in
    ls!=[]

  (* returns a list of difference sets for element e *)
  let find_diff (eq:'a->'a->bool) (s: dpart) (e:ptr) : dpart =
    (List.filter (fun l -> List.exists (fun x -> eq e x) l) s)

  (* returns checks if l1/\l2 !=null based on physical equality *)
  let overlap_q l1 l2 = 
    List.exists (fun x -> (List.memq x l2)) l1

  (* checks s |- x!=y *)
  let is_disj (eq:'a->'a->bool) (s: dpart)  (x:ptr) (y:ptr) : bool =
    if (eq x y) then false
    else
      let l1 = find_diff eq s x in
      let l2 = find_diff eq s y in
      (overlap_q l1 l2)

  let rec remove_dups_disj_set (s: dpart): dpart =
    match s with
    | [] -> []
    | x::xs -> if (List.length x == 0) || List.exists (fun y -> (List.length x == List.length y) && List.for_all2 eq x y) xs   
      then remove_dups_disj_set xs else [x]@(remove_dups_disj_set xs)

  (* returns s1/\s2 *)
  let merge_disj_set (s1: dpart) (s2: dpart): dpart =
    s1@s2

  (*  returns d1*d2 *)
  let star_disj_set (d1: dpart) (d2: dpart): dpart = (* d1@d2 *)
    let helper d1 d2 = List.concat (List.map (fun x -> List.map (fun y -> x@y) d2 ) d1) in
    match d1,d2 with
      | [],[] -> []
      | [],d2 -> d2
      | d1,[] -> d1
      | d1,d2 -> helper d1 d2

  (* returns d1/\d2 *)
  let conj_disj_set (d1: dpart) (d2: dpart): dpart = d1@d2

  (*  returns d1\/d2 *)
  let or_disj_set (d1: dpart) (d2: dpart): dpart = 
    List.concat (List.map (fun x1 -> List.map (fun x2-> intersect x1 x2) d2) d1) 

  (* returns s1*s2 *)
  let star_disj_set (s1: dpart) (s2: dpart): dpart =
    if is_empty s1 then s2
    else if is_empty s2 then s1
    else List.concat (List.map (fun x1 -> List.map (fun x2-> x1@x2) s2) s1) 

  (* check if there was a conflict in a difference list *)
  let  is_conflict_list (l:dlist) :bool =
    let rec helper l =
      match l with
        | [] -> false
        | x::xs -> let b=List.exists (eq x) xs in
          if b then true
          else helper xs
    in helper l

  (* check if there was a conflict in a set of difference lists *)
  let is_conflict (s: dpart) : bool =
    List.exists (is_conflict_list) s

  (* false result denotes contradiction *)
  let is_sat_dset (xs:dpart) : bool =
    let r = not(is_dupl_dset xs) in
    begin
      (* print_endline ("is_sat_dset("^(string_of xs)^")="^(string_of_bool r)); *)
      r
    end

  let apply_subs subs x =
    try
      List.assoc x subs
    with _ -> x

  let mk_exist_dset (evars:ptr list) (subs: (ptr*ptr) list) (xss:dpart) : dpart = 
    let rec aux ls =
      match ls with
        | [] -> []
        | x::xs -> 
              let x = apply_subs subs x in
              if BList.mem_eq eq x evars then (aux xs)
              else x::(aux xs) 
    in
    List.map aux xss

end;;

class mult_counters =
 object (self)
  val ctrs = Hashtbl.create 10
  method get (s:string) : int = 
    try
      let r = Hashtbl.find ctrs s in r
    with
      | Not_found -> 0
  method add (s:string) (i:int) = 
    try
      let r = Hashtbl.find ctrs s in
      Hashtbl.replace ctrs  s (r+i)
    with
      | Not_found -> Hashtbl.add ctrs s i
  method inc (s:string) = self # add s 1
  method string_of : string= 
    let s = Hashtbl.fold (fun k v a-> (k,v)::a) ctrs [] in
    let s = List.sort (fun (a1,_) (a2,_)-> String.compare a1 a2) s in
    "Counters: \n"^ (String.concat "\n" (List.map (fun (k,v) -> k^" = "^(string_of_int v)) s))^"\n"
end;;

class task_table =
object 
  val tasks = Hashtbl.create 10
  method add_task_instance msg time = 	
    let m = if (time>profile_threshold) then  [time] else [] in
    try 
          (* t1 : time, cnt1: count, max1: those that exceeed threshold *)      
	  let (t1,cnt1,max1) = Hashtbl.find tasks msg in
	  Hashtbl.replace tasks msg (t1+.time,cnt1+1,m@max1)
    with Not_found -> 
	    Hashtbl.add tasks msg (time,1,m)
  method print_task_instance msg : unit = 	
    try 
 	  let (t1,cnt1,_) = Hashtbl.find tasks msg in
	  Basic.print_endline_quiet ("Time("^msg^") : "^(string_of_float t1)^" (seconds)")
    with Not_found -> 
	  Basic.print_endline_quiet ("Task "^msg^" does not exist in profiling table.")
  method print : unit = 
    let str_list = Hashtbl.fold (fun c1 (t,cnt,l) a-> (c1,t,cnt,l)::a) tasks [] in
    let str_list = List.sort (fun (c1,_,_,_)(c2,_,_,_)-> String.compare c1 c2) str_list in
    let (_,ot,_,_) = List.find (fun (c1,_,_,_)-> (String.compare c1 "Overall")=0) str_list in
    let f a = (string_of_float ((floor(100. *.a))/.100.)) in
    let fp a = (string_of_float ((floor(10000. *.a))/.100.)) in
    let (cnt,str) = List.fold_left (fun (a1,a2) (c1,t,cnt,l)  -> 
        let r = (a2^" \n("^c1^","^(f t)^","^(string_of_int cnt)^","^ (f (t/.(float_of_int cnt)))^",["^
            (if (List.length l)>0 then 
              let l = (List.sort compare l) in		
              (List.fold_left (fun a c -> a^","^(f c)) (f (List.hd l)) (List.tl l) )
            else "")^"],  "^(fp (t/.ot))^"%)") in
        ((a1+1),r) 
    ) (0,"") str_list in
    print_string ("\nProfiling Results: " ^(string_of_int cnt)^" keys."^str^"\n" ) 
end;;


module Profiling =
struct
  let counters = new mult_counters
  let tasks = new task_table
  let profiling_stack = new stack_noexc ("stack underflow",0.,false) 
    (fun (s,v,b)-> "("^s^","^(string_of_float v)^","^(string_of_bool b) ^")") (=)

  let add_to_counter (s:string) i = 
    if !enable_counters then counters#add s i
    else ()
  let inc_counter (s:string) = add_to_counter s 1

  let string_of_counters () =  counters#string_of

  let get_all_time () = 
	let r = Unix.times () in
	r.Unix.tms_utime +. r.Unix.tms_stime +. r.Unix.tms_cutime +. r.Unix.tms_cstime

  let get_main_time () = 
	let r = Unix.times () in
	r.Unix.tms_utime +. r.Unix.tms_stime (* +. r.Unix.tms_cutime +. r.Unix.tms_cstime *)

  let get_time () = get_all_time()

  let push_time_no_cnt msg = 
    if (!profiling) then
      let timer = get_time () in
	  profiling_stack # push (msg, timer,true) 
    else ()
  let push_time_always msg = 
      (* inc_counter ("cnt_"^msg); *)
      let timer = get_time () in
	  profiling_stack#push (msg, timer,true) 
	  (* profiling_stack := (msg, timer,true) :: !profiling_stack) *)

  let push_time msg = 
    if (!profiling) then
      push_time_always msg
    else ()

  let pop_time_always msg = 
    let m1,t1,_ = profiling_stack # top in
    if (String.compare m1 msg)==0 then 
      let t2 = get_time () in
      if (t2-.t1)< 0. then Error.report_error {Error.error_loc = no_pos; Error.error_text = ("negative time")}
      else
	profiling_stack # pop;
      if (List.exists (fun (c1,_,b1)-> (String.compare c1 msg)=0) profiling_stack#get_stk) then begin
	(* if (List.exists (fun (c1,_,b1)-> (String.compare c1 msg)=0&&b1) !profiling_stack) then begin *)
	(* 	profiling_stack :=List.map (fun (c1,t1,b1)->if (String.compare c1 msg)=0 then (c1,t1,false) else (c1,t1,b1)) !profiling_stack; *)
	(* 	print_string ("\n double accounting for "^msg^"\n") *)
        (* print_string ("\n skip double accounting for "^msg^"\n")  *)
	tasks # add_task_instance m1 0.
      end	
      else tasks # add_task_instance m1 (t2-.t1) 
    else
      (* let () = print_endline ("profiling_stack = " ^ profiling_stack#string_of) in *)
      Error.report_error {Error.error_loc = no_pos; Error.error_text = ("Error popping "^msg^" from the stack")}

  let pop_time msg = 
    if (!profiling) then
      pop_time_always msg
    else ()

 let print_info_task (m:string) : unit =  tasks # print_task_instance m

 let print_info () = if (!profiling) then  tasks # print else ()

 let print_counters_info () =
      if !enable_counters then
        print_string (string_of_counters ())
      else () 

  let prof_aux (s:string) (f:'a -> 'z) (e:'a) : 'z =
    try
      push_time s;
        let r=f e in
        (pop_time s; r)
    with ex -> (pop_time s; raise ex)

  let do_1 (s:string) (f:'a -> 'z) (e:'a) : 'z =
    prof_aux s f e

  let do_2 (s:string) (f:'a1 -> 'a2 -> 'z) (e1:'a1) (e2:'a2) : 'z =
    prof_aux s (f e1) e2
  (* try *)
  (*   push_time s; *)
  (*     let r=f e1 e2 in *)
  (*     (pop_time s; r) *)
  (* with ex -> (pop_time s; raise ex) *)

  let do_3 (s:string) (f:'a1 -> 'a2 -> 'a3 -> 'z) (e1:'a1) (e2:'a2) (e3:'a3) : 'z =
    prof_aux s (f e1 e2) e3


  let do_4 (s:string) (f:'a1 -> 'a2 -> 'a3 -> 'a4 -> 'z) (e1:'a1) (e2:'a2) (e3:'a3) (e4:'a4) : 'z =
    prof_aux s (f e1 e2 e3) e4

  let do_5 (s:string) (f:'a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'z) (e1:'a1) (e2:'a2) (e3:'a3) (e4:'a4)(e5:'a5) : 'z =
    prof_aux s (f e1 e2 e3 e4) e5

  let do_6 (s:string) (f:'a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'a6 -> 'z) (e1:'a1) (e2:'a2) (e3:'a3) (e4:'a4)(e5:'a5) (e6:'a6) : 'z =
    prof_aux s (f e1 e2 e3 e4 e5) e6

  let do_1_num n s =  let str=(s^"#"^n) in do_1 str
  let do_2_num n s =  let str=(s^"#"^n) in do_2 str
  let do_3_num n s =  let str=(s^"#"^n) in do_3 str
  let do_4_num n s =  let str=(s^"#"^n) in do_4 str
  let do_5_num n s =  let str=(s^"#"^n) in do_5 str
  let do_6_num n s =  let str=(s^"#"^n) in do_6 str

  let no_1 s f =  f
  let no_2 s f =  f
  let no_3 s f =  f
  let no_4 s f =  f
  let no_5 s f =  f
  let no_6 s f =  f

  let no_1_num n s f =  f
  let no_2_num n s f =  f
  let no_3_num n s f =  f
  let no_4_num n s f =  f
  let no_5_num n s f =  f
  let no_6_num n s f =  f

  let spec_counter = new counter 1

  let gen_time_msg _  = 
    spec_counter#inc;
    "time_stk_"^ (spec_counter#string_of)

  let pop_time_to_s_no_count  msg = 
	if (!profiling) then
	  let rec helper l = match l with
        | [] -> Error.report_error {Error.error_loc = no_pos; Error.error_text = ("Error special poping "^msg^"from the stack")}
        | (m1,_,_)::t ->  if not ((String.compare m1 msg)==0) then helper t			
		  else t in
      profiling_stack#set_stk (helper profiling_stack#get_stk) 
	else ()

  let add_index l = 
    let rec ff i l = match l with
	  | [] -> []
	  | a::b-> (i,a)::(ff (i+1) b) in
    (ff 0 l)


end;;

module SysUti =

struct
  open Basic
  open ErrorUti

(* Qualify helper file name *)
(* if you want to install the executable in one directory (e.g. /usr/bin),
 * but put helper files in another (/usr/share/module-language),
   here's what you need to change! *)

  let qualify_helper_fn n =
    let d =  Filename.dirname Sys.executable_name ^ "/" in
    Sys.getcwd() ^ "/" ^ d ^ n

  let lib_name n =
    try (let d = Filename.dirname Sys.executable_name ^ "/../lib/" in
	Sys.getcwd() ^ "/" ^ d ^ n)
    with Sys_error _ -> n

  let tmp_name n =
    try (let d = Filename.dirname Sys.executable_name ^ "/../tmp/" in    
	Sys.getcwd() ^ "/" ^ d ^ n)
    with Sys_error _ -> n

  (** filename handling; returns the inverse of Filename.chop_extension *)
  let extension n =
    let d = String.rindex n '.' in
    String.sub n d (String.length n - d)

  let get_path s = 
    if String.contains s '/' then
      let i = String.rindex s '/' in
      String.sub s 0 (i+1)
    else ""

  (** String-handling utility functions. *)

  let trim_quotes s = 
    let trim_last s' = if String.get s' ((String.length s')-1) = '"' then
      String.sub s' 0 ((String.length s')-1) else s' in
    if String.get s 0 = '"' then 
      (trim_last (String.sub s 1 ((String.length s) - 1)))
    else
      trim_last s

  let unescaped s =
    let n = ref 0 in
    for i = 0 to String.length s - 1 do
      n := !n +
          (match String.unsafe_get s i with
              '\\' when String.unsafe_get s (i+1) != '\\' ->
                  (match String.unsafe_get s (i+1) with
                      'n' -> 0
                    | 't' -> 0
                    | _ -> 1)
            | _ -> 1)
    done;
    if !n = String.length s then s else begin
      let s' = String.create !n in
      n := 0;
      let skip = ref 0 in
      (try (for i = 0 to String.length s - 1 do
        begin
          if (i + !skip) = String.length s then raise Bail;
          match String.unsafe_get s (i + !skip) with
            | '\\' when String.unsafe_get s (i+ !skip+1) != '\\' ->
                  (match String.unsafe_get s (i+ !skip+1) with
                      'n' -> String.unsafe_set s' !n '\n'; incr skip
                    | 'r' -> String.unsafe_set s' !n '\r'; incr skip
                    | 't' -> String.unsafe_set s' !n '\t'; incr skip
                    | '\\' -> String.unsafe_set s' !n '\\'; incr skip;
                    | _ -> raise Bad_string)
            | c -> String.unsafe_set s' !n c
        end;
          incr n
      done) with Bail -> ());
      Str.first_chars s' (String.length s - !skip)
    end

  let trim_str input =
    let start_idx = ref 0 in
    let len = String.length input in
    let () = 
	  while (!start_idx < len) && ((String.get input !start_idx) = ' ') do
	    start_idx := !start_idx + 1
	  done in
    let end_idx = ref (len - 1) in
    let () = 
	  while (!end_idx > !start_idx) && ((String.get input !end_idx) = ' ') do
	    end_idx := !end_idx - 1
	  done in
    let res = String.sub input !start_idx (!end_idx - !start_idx + 1) in
    res


  (** namespace mangling stuff *)

  let qualify_if_needed mname n =
    if String.contains n '.' then n else (mname ^ "." ^ n)

  let unqualify_getting_module s =
    if String.contains s '.' then
      let i = String.rindex s '.' in
      String.sub s 0 i
    else ""

  let unqualify s =
    if String.contains s '.' then
      let i = String.rindex s '.' in
      String.sub s (i+1) (String.length s - i - 1)
    else s

  let unprime s =
    let l = String.length s in 
    if l = 0 then s else 
      if (String.get s (l-1)) = '\'' then
        String.sub s 0 (l-1) else s

  let is_primed s =
    let l = String.length s in 
    if l = 0 then false else 
      (String.get s (l-1) = '\'')

  let replace_dot_with_uscore s =
    let dot = Str.regexp "\\." in
    let caret = Str.regexp "\\^" in
    Str.global_replace dot "" 
        (Str.global_replace caret "$" s)

  let replace_minus_with_uscore s =
    let minus = Str.regexp "-" in
    let caret = Str.regexp "\\^" in
    Str.global_replace minus "_" 
        (Str.global_replace caret "$" s)

  let replace_path_sep_with_uscore s =
    let path_sep = Str.regexp "/" in
    let caret = Str.regexp "\\^" in
    Str.global_replace path_sep "" 
        (Str.global_replace caret "$" s)

  let split_by sep s =
    let sep_regexp = Str.regexp (Str.quote sep) in
    Str.split sep_regexp s

(** Printing notifications [msg, amsg, etc] *)
let verbose = ref false

(** always print this message *)
let amsg s = print_string s; flush_all ()

(** print only if -v *)
let msg s = if !verbose then amsg s

(* get from option type, if present *)
let unsome_safe x a =
  match x with
    | Some a -> a
    | None -> a

(** removing 'option' types *)
let unsome : 'a option -> 'a = 
  function
	| Some x -> x
	| None   -> failwith "[util] tried to deoptionify None"

let is_some : 'a option -> bool =
  function
	| Some x -> true
	| None -> false


(** Read the given file into a string. *)
let string_of_file (fname : string) =
  if Sys.file_exists fname then
    let chn = open_in fname in
    let len = in_channel_length chn in
    let str = String.make len ' ' in
    let () = really_input chn str 0 len in
    (close_in chn; str)
  else
    (warn ("Could not read file " ^ fname ^ "; assuming empty content.");
    "")

let fileLine (fn:string) : string =
  begin
    let chn = open_in fn in
    let str = input_line chn in
    close_in chn;
    str
  end

(** Use timed_command utility to run an external process with a timeout. *)

let timed_command = qualify_helper_fn "timed_command"

let run_with_timeout (prog : string) (seconds : int) : int =
  (* msg ("Running with timeout: " ^ prog ^ "\n"); *)
  Sys.command (timed_command ^ Printf.sprintf " %d " seconds ^ prog)

let is_breakable c =  match c with
  | '(' | ')' | ' ' | '+' | ':'|',' -> true
  | _ -> false

let new_line_str = "\n"
(*
  if Sys.os_type = "Cygwin" then
	let t = Buffer.create 1 in
	  Buffer.add_char t (char_of_int 0x0A);
	  let tmp = Buffer.contents t in
		tmp
  else "\n"
*)

let break_lines (input : string): string =
  let buf = Buffer.create 4096 in
  let i = ref 0 in
  let cnt = ref 0 in
  let l = String.length input in
  while !i < l do
    Buffer.add_char buf input.[!i];
      cnt := !cnt + 1;
      if !cnt > 80 && (is_breakable input.[!i]) then begin
		Buffer.add_string buf new_line_str;
		cnt := 0
	  end;
      i := !i + 1
  done;
  Buffer.contents buf

let break_lines_num (input : string) num: string =
  let buf = Buffer.create 4096 in
  let i = ref 0 in
  let cnt = ref 0 in
  let l = String.length input in
  while !i < l do
    Buffer.add_char buf input.[!i];
      cnt := !cnt + 1;
      if !cnt > num && (is_breakable input.[!i]) then begin
		Buffer.add_string buf new_line_str;
		cnt := 0
	  end;
      i := !i + 1
  done;
  Buffer.contents buf

let break_lines_1024 (input : string) : string =
  (* let n= String.index input ';' in *)
  (* let s = String.sub input 0 n in *)
  (* let delta = String.length input - String.length s in *)
  (* let () = if  delta > 0  then print_endline ("XXXXXXXXXX: " ^(string_of_int delta) ) *)
  (*     else  print_endline "" in *)
  break_lines_num input (1024-32)

end;;

(* module ExcNumbering = *)
(* struct *)

(*   open Basic *)


(* end;; *)

module Stackable =
struct
  type 'a tag_elem = ('a * (int list))

  type 'a tag_list = ('a tag_elem) list

  type ('a,'b) stackable =  ('a * (('b list) list))

  type ('a,'b) list_of_stackable =  (('a,'b) stackable) list

  open Basic

  (* this imp_list is not pop-pable *)

  type 'a ilist = ('a list) ref

  let new_ilist () : 'a ilist 
        = ref []

  let add_ilist (x:'a list) (imp:'a ilist) : 'a ilist
        = imp := x@(!imp) ; imp

  let init_level ((i,stk):('a,'b) stackable) : ('a,'b) stackable
        = (i,[]::stk)

  let pushf_add_level (f:'a -> 'a * ('b list))  ((i,stk):('a,'b) stackable) : ('a,'b) stackable
        = match stk with
          | [] -> Error.report_error {Error.error_loc = no_pos; Error.error_text = ("pushf_add_level on empty stack")}
          | lvl::stk -> let (new_i,v)=f i 
            in (new_i,(v@lvl)::stk)

  let add_level (lst:'b list)  ((i,stk):('a,'b) stackable) : ('a,'b) stackable
        = match stk with
          | [] -> Error.report_error {Error.error_loc = no_pos; Error.error_text = ("pushf_add_level on empty stack")}
          | lvl::stk -> (i,(lst@lvl)::stk)

  let close_level ((i,stk):('a,'b) stackable) : ('a,'b) stackable
        = match stk with
          | lvl::(lvl2::stk) -> (i, (lvl@lvl2)::stk)
          | _ -> Error.report_error {Error.error_loc = no_pos; Error.error_text = ("close level requires at least two levels")}

  let collapsef_stack  (f:'a -> ('b list) -> 'a)  ((i,stk):('a,'b) stackable) : 'a
        = f i (List.concat stk)

  let popf_level (f:'a -> ('b list) -> ('a * ('b list))) ((i,stk):('a,'b) stackable) : ('a,'b) stackable
        = match stk with
          | lvl::stk -> let (newi,lst)=(f i lvl) in
            if (is_empty lst) then (newi, stk)
            else (add_level lst (newi,stk))
          | _ -> Error.report_error {Error.error_loc = no_pos; Error.error_text = ("popf_level on empty stack")}

  let init_level_list (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
        = List.map (init_level) xs

  let pushf_add_level_list (f:'a -> 'a * ('b list))  (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
        = List.map (pushf_add_level f) xs


  let collapsef_stack_list (f:'a ->'b list -> 'a) (xs : ('a,'b) list_of_stackable) : 'a list
        = List.map (collapsef_stack f) xs

  let close_level_list  (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
        = List.map (close_level) xs


  let popf_level_list  (f:'a -> ('b list) -> ('a * ('b list))) (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
        = List.map (popf_level f) xs

  let push_tag (xs : 'a tag_list) : ('a tag_list) =
    let rec helper xs (n:int) =
      match xs with
        | [] ->  []
        | (x,t) :: xs -> (x,(n::t))::(helper xs (n+1))
    in (helper xs 1)

  let check_sorted_tag (xs: 'a tag_list) : bool =
    let rec helper xs no =
      match xs with
        | [] -> true
        | ((x,[])::xs1) -> Error.report_error {Error.error_loc = no_pos; Error.error_text = ("tag missing during ehc_sorted_tag")}
        | ((x,n::t)::xs1) -> 
              if (n<no) then false
              else if (n==no) then helper xs1 no
              else helper xs1 n
    in helper xs 1

  (* if check_sorted_tag fail, will need to sort the tag before grouping *)
  let group_tag (xs: 'a tag_list) (acc:'a tag_list) : ('a tag_list * int) list =
    let rec helper xs acc no =
      match xs with
        | [] -> if (is_empty acc) then [] else [(List.rev acc,no)]
        | ((x,[])::xs1) -> Error.report_error {Error.error_loc = no_pos; Error.error_text = ("cannot happen!")}
        | ((x,n::t)::xs1) -> 
              if (n==no) then helper xs1 ((x,t)::acc) no
              else 
                let rs=helper xs [] (no+1) in
                if (is_empty acc) then rs
                else (List.rev acc,no)::rs
    in let r=check_sorted_tag xs in
    if r then helper xs acc 1 
    else Error.report_error {Error.error_loc = no_pos; Error.error_text = ("need to sort group_tag!")}

  let zip_tag (f: 'a -> 'b -> 'c) (xs: ('a * int) list) (ys:('b * int) list) : ('c list) =
    let rec helper xs ys =
      match xs with
        | [] -> []
        | ((x,n1)::xs1) -> 
              match ys with
                | [] -> []
                | ((y,n2)::ys1) -> 
                      if (n1==n2) then (f x y)::helper xs ys1
                      else if (n1<n2) then helper xs1 ys
                      else helper xs ys1
    in helper xs ys

end;;

include Basic
include SysUti

let try_finally e f a g =
  let flag = e () in
  try
    let r = f a in
    (g flag; r)
  with _ as e -> 
    (g flag; raise e)

let range a b =
  let rec aux a b =
    if a > b then [] else a :: aux (a+1) b  in
  (* if a > b then List.rev (aux b a) else aux a b;; *)
  if a > b then [] else aux a b;;

