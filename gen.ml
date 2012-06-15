(* *)
module type INC_TYPE =
    sig
      type t
      val zero : t
      val inc : t -> t
    end;;

module type EQ_TYPE =
    sig
      type t
      val eq : t -> t -> bool
      val string_of : t -> string
    end;;

module Basic =
(* basic utilities that can be opened *)
struct

  exception Bad_string
  exception Bail

  let rec restart f arg =
    try f arg with Unix.Unix_error(Unix.EINTR,_,_) -> print_string"#!Unix_error#";(restart f arg)

  let string_of_pair (p1:'a->string) (p2:'b->string) ((a,b):'a * 'b) : string = 
    "("^(p1 a)^","^(p2 b)^")"

  let rec remove_dups n = 
    match n with
        [] -> []
      | q::qs -> if (List.mem q qs) then remove_dups qs else q::(remove_dups qs)

  let pr_id x = x

  let print_flush s = print_string (s^"\n"); flush stdout

  let pr_no x = "?"

  let pr_unit x = "()"

  let pr_option f x = match x with
    | None -> "None"
    | Some v -> "Some("^(f v)^")"

  let pr_opt_int = pr_option string_of_int

  let pr_pair f1 f2 (x,y) = "("^(f1 x)^","^(f2 y)^")"

  let pr_triple f1 f2 f3 (x,y,z) = "("^(f1 x)^","^(f2 y)^","^(f3 z)^")"

  let pr_lst f xs = String.concat "," (List.map f xs)

 let pr_list f xs = "["^(pr_lst f xs)^"]"

  let opt_to_list o = match o with
    | None -> []
    | Some a -> [a]

  let opt_list_to_list o = match o with
    | None -> []
    | Some a -> a

  let fnone (c:'a):'a option = None

  let is_empty l = match l with [] -> true | _ -> false

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

  let rec combine4 a b c d= match (a, b, c,d) with
    | (ah::arest, bh::brest, ch::crest, dh::drest) ->
	      let l = combine4 arest brest crest drest in
		  (ah, bh, ch, dh)::l
    | ([], [], [], []) -> []
    | _ -> failwith ("combine4: combining lists with different lengths")
	
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

  let report_warning pos msg = Error.report_warning
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

  let rec check_dups_eq eq n = 
    match n with
      | [] -> false
      | q::qs -> if (List.exists (fun c-> eq q c) qs) then true  else check_dups_eq eq qs 

  let check_no_dups_eq eq n = not(check_dups_eq eq n)

  let subset_eq eq l1 l2 =
    List.for_all (fun x -> (mem_eq eq x l2)) l1

  let disjoint_eq eq l1 l2 =
    List.for_all (fun x -> not (mem_eq eq x l2)) l1

  let overlap_eq eq l1 l2 = 
    List.exists (fun x -> (mem_eq eq x l2)) l1

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

  (*intersect gen rel*)
  let intersect_rel rel eq l1 l2 = 
    remove_dups_eq eq ((List.filter (fun x-> List.exists (fun c-> rel x c) l2) l1)@(List.filter (fun x-> List.exists (rel x) l1) l2))
    
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
  
  let rec list_substs eq sst l = 
    List.map (fun v-> 
      try 
        snd (List.find (eq v) sst)
      with Not_found -> v) l 
        
end;;

module BListEQ =
    functor (Elt : EQ_TYPE) ->
struct
  type elem = Elt.t
  type elist = elem list
  let eq = Elt.eq
  let string_of_elem = Elt.string_of

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

class ['a] stack (x_init:'a) (epr:'a->string)  =
   object 
     val emp_val = x_init
     val mutable stk = []
     val elem_pr = epr 
       (* = (fun _ -> "elem printer not initialised!") *)
     method push (i:'a) = stk <- i::stk
     method get  = stk (* return entire content of stack *)
     method override newstk  = stk <- newstk 
       (* override with a new stack *)
     method pop = match stk with 
       | [] -> print_string "ERROR : popping empty stack"; 
               raise Stack_Error
       | x::xs -> stk <- xs
     method top : 'a = match stk with 
       | [] -> print_string "ERROR : top of empty stack"; 
               raise Stack_Error
       | x::xs -> x
     method pop_no_exc = match stk with 
       | [] -> () 
       | x::xs -> stk <- xs
     method top_no_exc : 'a = match stk with 
       | [] ->  emp_val
       | x::xs -> x
     method len = List.length stk
     method reverse = stk <- List.rev stk
     (* method set_pr f = elem_pr <- f *)
     method string_of = BList.string_of_f elem_pr stk
   end;;

class counter x_init =
   object 
     val mutable ctr = x_init
     method get : int = ctr
     method inc = ctr <- ctr + 1
     method add (i:int) = ctr <- ctr + i
     method reset = ctr <- 0
     method string_of : string= (string_of_int ctr)
   end;;

class ['a] stack2 xinit =
   object 
	val def = xinit
	val mutable stk = []
	method push (i:'a) = stk <- i::stk
	method pop = match stk with 
       | [] -> raise Stack_Error
       | x::xs -> stk <- xs
   method top : 'a = match stk with 
       | [] -> def
       | x::xs -> x
	method len = List.length stk
end;;

class ['a] stack3  =
   object 
	val mutable stk = []
	method push (i:'a) = stk <- i::stk
	method pop = match stk with 
       | [] -> raise Stack_Error
       | x::xs -> stk <- xs
   method top : 'a = match stk with 
       | [] -> raise Stack_Error
       | x::xs -> x
	method len = List.length stk
end;;

module Stack4  =
   struct 
    type a 
	let push (i:'a) stk = i::!stk
	let pop stk  = match stk with 
       | [] -> raise Stack_Error
       | x::xs -> xs
    let top stk  = match stk with 
       | [] -> raise Stack_Error
       | x::xs -> x
    let len stk : int = List.length stk
end;;

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

  let (stkint:int stack2) = new stack2 (-1)

 let (stkint:int stack3) = new stack3 

  let error_list = new stack "error - stack underflow" (fun x -> x)

  let warning_no  = new counter 0

  let no_errors () = (error_list#len = 0)

  let err loc msg = 
    error_list#push (loc ^ ": error: "^msg)

  let error msg = (print_string (msg ^"\n"); flush_all(); err "" msg)
  let print_errors () = 
    List.iter (function x -> print_string (x ^ "\n")) error_list#get;
    print_string (string_of_int (error_list#len)^" errors.\n");
    print_string "The program is INVALID\n";
    exit 2

  let warn msg = 
    warning_no #inc;
    print_string ("*** Warning: "^ msg ^ "\n"); flush_all()

  let warn_if_none ov msg = match ov with
    | None -> warn msg
    | Some _ -> ()

  let fail s =   
    print_string (s ^ "\n"); 
    Printf.printf "There were %d warnings.\n" warning_no#get;
    flush_all();
    failwith s

end;;

module EqMap =
    functor (Elt : EQ_TYPE) ->
struct
  type elem = Elt.t
  type key = elem list
  type emap = (elem * key) list
  type epart = (elem list) list
  type elist = (elem list) 
  type epair = ((elem * elem) list) 

  let eq = Elt.eq 
  let string_of_elem = Elt.string_of 


  let partition (s: emap) : epart =
    let rec insert (a,k) lst = match lst with
      | [] -> [(k,[a])]
      | (k2,ls)::xs -> 
            if k==k2 then (k,a::ls)::xs
            else (k2,ls)::(insert (a,k) xs) in
    let r = List.fold_left (fun lst x ->  insert x lst) [] s in
    List.map ( fun (_,b) -> b) r

  let string_of (e: emap) : string =
    let f = string_of_elem in
    let ll=partition e in 
    "[@"^ (String.concat " \n " (List.map (fun cl -> "{"^(String.concat ", "(List.map f cl))^"}") ll))^"]"

  let un_partition (ll:epart) : emap =
    let flat xs y = 
      if (List.length xs>1) then List.map (fun x -> (x,y)) xs 
      else [] in
    List.concat (List.map (fun x -> flat x x) ll)

  let mkEmpty : emap = []

  let is_empty (m:emap) = match m with | [] -> true | _ -> false

  let find_aux (s: emap) (e:elem) (d:key) : key =
    try
      snd(List.find (fun (e1,_) -> eq e e1) s)
    with
        _ -> d

  (* find key of e in s *)
  let find (s : emap) (e:elem) : key  = find_aux s e []

  (* find key of e in s and return remainder after
     all elements equivalent to e is removed *)
  let find_remove (s : emap) (e:elem) : key * emap  = 
    let r1 = find_aux s e [] in
    (r1, if r1==[] then s else List.filter (fun (e2,_)-> not(eq e e2)) s)

  (* returns s |- x=y *)
  let is_equiv (s: emap)  (x:elem) (y:elem) : bool =
    if (eq x y) then true
    else
      let r1 = find s x in
      let r2 = find s y in
      (r1==r2 && not(r1==[]))

  (* add x=y to e-set s and returning a new e-set with
     extra elements added *)
  let add_equiv  (s: emap) (x:elem) (y:elem) : emap = 
    if (eq x y) then s
    else
      let r1 = find s x in
      let r2 = find s y in
      if r1==[] then
        if r2==[] then
          let r3 = [x;y] in
          (x,r3)::((y,r3)::s)
        else (x,r2)::s
      else
        if r2==[] then (y,r1)::s
        else
          if r1==r2 then s
          else 
            let r3=r1@r2 in
            List.map (fun (a,b) -> if (b==r1 or b==r2) then (a,r3) else (a,b)) s

  let build_eset (xs:(elem * elem) list) :  emap =
    List.fold_right (fun (x,y) eqs -> add_equiv eqs x y) xs (mkEmpty)

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
  let merge_eset (s1: emap) (s2: emap): emap =
    let (t1,t2) = order_two s1 s2 in
    List.fold_left (fun a (p1,p2) -> add_equiv a p1 p2) t2 (get_equiv t1)

  (* remove key e from e_set  *)
  let elim_elems_one  (s:emap) (e:elem) : emap = 
    List.filter (fun (a,k2) -> not(eq a e)) s

  (* return all elements equivalent to e, including itself *)
  let find_equiv_all  (e:elem) (s:emap) : elist  =
    let r1 = find s e in
    if (r1==[]) then []
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
    if (r1==[]) then (None,s)
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
  let subs_eset   ((fv,tv):elem * elem) (s:emap) : emap = 
    if (eq fv tv) then s
    else
      let r1 = find s fv in
      if (r1==[]) then s
      else 
        let ns = add_equiv s fv tv in
        elim_elems_one ns fv


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
    else Error.report_error {Error.error_loc = Globals.no_pos; 
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

end;;

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
  let stk = new stack (-1) string_of_int

  (* pop last element from call stack of ho debug *)
  let pop () = stk # pop

  (* call f and pop its trace in call stack of ho debug *)
  let pop_ho (f:'a->'b) (e:'a) : 'b =
    let r = (try 
      (f e)
    with exc -> (stk#pop; raise exc))
    in stk#pop; r

  (* string representation of call stack of ho_debug *)
  let string_of () : string =
    let h = stk#get in
    String.concat "@" (List.map string_of_int h)

  (* returns @n and @n1;n2;.. for a new call being debugged *)
  let push (os:string) : (string * string) = 
    ctr#inc;
    let v = ctr#get in
    let _ = stk#push v in
    let s = os^"@"^(string_of_int v) in
    let h = os^"@"^string_of() in
    s,h
end;;

module Debug =
struct
  open StackTrace

  (* let ho_2_opt_aux (loop_d:bool) (test:'z -> bool) (s:string) (pr1:'a->string) (pr2:'b->string) (pr_o:'z->string)  (f:'a -> 'b -> 'z)  *)
  (*       (e1:'a) (e2:'b) : 'z = *)
  (*   let s,h = push s in *)
  (*   (if loop_d then print_string (h^" inp :"^(pr1 e1)^"\n")); *)
  (*   let r = try *)
  (*     pop_ho (f e1) e2  *)
  (*   with ex ->  *)
  (*       let _ = print_string (h^"\n") in *)
  (*       let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in *)
  (*       let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in *)
  (*       let _ = print_string (s^" Exception"^(Printexc.to_string ex)^"Occurred!\n") in *)
  (*       raise ex in *)
  (*   if not(test r) then r else *)
  (*     let _ = print_string (h^"\n") in *)
  (*     let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in *)
  (*     let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in *)
  (*     let _ = print_string (s^" out :"^(pr_o r)^"\n") in *)
  (*     r *)

  let ho_aux lz (loop_d:bool) (test:'z -> bool) (s:string) (args:string list) (pr_o:'z->string) (f:'a->'z) (e:'a) :'z =
    let pr_args xs =
      let rec helper (i:int) args = match args with
        | [] -> ()
        | a::args -> (print_string (s^" inp"^(string_of_int i)^" :"^a^"\n");(helper (i+1) args)) in
      helper 1 xs in
    let pr_lazy_res xs =
      let rec helper xs = match xs with
        | [] -> ()
        | (i,a)::xs -> let a1=Lazy.force a in
          if (a1=(List.nth args (i-1))) then helper xs
          else (print_string (s^" res"^(string_of_int i)^" :"^(a1)^"\n");(helper xs)) in
      helper xs in
    let s,h = push s in
    (if loop_d then print_string ("\n"^h^" ENTRY :"^(List.hd args)^"\n"));
    flush stdout;
    let r = (try
      pop_ho f e
    with ex -> 
        (let _ = print_string ("\n"^h^"\n") in
        let _ = pr_args args in
        let _ = pr_lazy_res lz in
        let _ = print_string (s^" EXIT Exception"^(Printexc.to_string ex)^"Occurred!\n") in
        flush stdout;
        raise ex)) in
    (if not(test r) then r else
      let _ = print_string ("\n"^h^"\n") in
      let _ = pr_args args in
      let _ = pr_lazy_res lz in
      let _ = print_string (s^" EXIT out :"^(pr_o r)^"\n") in
      flush stdout;
      r)

  let choose bs xs = 
    let rec hp bs xs = match bs,xs with
      |[], _ -> []
      | _, [] -> []
      | b::bs, (i,s)::xs -> if b then (i,s)::(hp bs xs) else (hp bs xs) in
    hp bs xs

  let ho_1_opt_aux (flags:bool list) (loop_d:bool) (test:'z -> bool) (s:string) (pr1:'a->string) (pr_o:'z->string)  (f:'a -> 'z) (e1:'a) : 'z =
    let a1 = pr1 e1 in
    let lz = choose flags [(1,lazy (pr1 e1))] in
    let f  = f in
    ho_aux lz loop_d test s [a1] pr_o  f e1


  let ho_2_opt_aux (flags:bool list) (loop_d:bool) (test:'z -> bool) (s:string) (pr1:'a->string) (pr2:'b->string) (pr_o:'z->string)  (f:'a -> 'b -> 'z) 
        (e1:'a) (e2:'b) : 'z =
    let a1 = pr1 e1 in
    let a2 = pr2 e2 in
    let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2))] in
    let f  = f e1 in
    ho_aux lz loop_d test s [a1;a2] pr_o f e2

  let ho_3_opt_aux  (flags:bool list) (loop_d:bool) (test:'z -> bool) (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr_o:'z->string)  (f:'a -> 'b -> 'c -> 'z) (e1:'a) (e2:'b) (e3:'c) : 'z =
    let a1 = pr1 e1 in
    let a2 = pr2 e2 in
    let a3 = pr3 e3 in
    let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2)); (3,lazy (pr3 e3))] in
    let f  = f e1 e2 in
    ho_aux lz loop_d test s [a1;a2;a3] pr_o f e3


  let ho_4_opt_aux (flags:bool list) (loop_d:bool) (test:'z->bool) (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr4:'d->string) (pr_o:'z->string) 
        (f:'a -> 'b -> 'c -> 'd-> 'z) (e1:'a) (e2:'b) (e3:'c) (e4:'d): 'z =
    let a1 = pr1 e1 in
    let a2 = pr2 e2 in
    let a3 = pr3 e3 in
    let a4 = pr4 e4 in
    let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2)); (3,lazy (pr3 e3)); (4,lazy (pr4 e4))] in
    let f  = f e1 e2 e3 in
    ho_aux lz loop_d test s [a1;a2;a3;a4] pr_o f e4


  let ho_5_opt_aux (flags:bool list) (loop_d:bool) (test:'z -> bool)  (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr4:'d->string)
        (pr5:'e->string) (pr_o:'z->string) 
        (f:'a -> 'b -> 'c -> 'd -> 'e -> 'z) (e1:'a) (e2:'b) (e3:'c) (e4:'d) (e5:'e) : 'z =
    let a1 = pr1 e1 in
    let a2 = pr2 e2 in
    let a3 = pr3 e3 in
    let a4 = pr4 e4 in
    let a5 = pr5 e5 in
    let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2)); (3,lazy (pr3 e3)); (4,lazy (pr4 e4)); (5,lazy (pr5 e5))] in
    let f  = f e1 e2 e3 e4 in
    ho_aux lz loop_d test s [a1;a2;a3;a4;a5] pr_o f e5


  let ho_6_opt_aux (flags:bool list) (loop_d:bool) (test:'z->bool) (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr4:'d->string)
        (pr5:'e->string) (pr6:'f->string) (pr_o:'z->string) 
        (f:'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'z) (e1:'a) (e2:'b) (e3:'c) (e4:'d) (e5:'e) (e6:'f): 'z =
    let a1 = pr1 e1 in
    let a2 = pr2 e2 in
    let a3 = pr3 e3 in
    let a4 = pr4 e4 in
    let a5 = pr5 e5 in
    let a6 = pr6 e6 in
    let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2)); (3,lazy (pr3 e3)); (4,lazy (pr4 e4)); (5,lazy (pr5 e5)); (6,lazy (pr6 e6))] in
    let f  = f e1 e2 e3 e4 e5 in
    ho_aux lz loop_d test s [a1;a2;a3;a4;a5;a6] pr_o f e6

  let ho_1_opt f = ho_1_opt_aux [] false f
  let ho_2_opt f = ho_2_opt_aux [] false f
  let ho_3_opt f = ho_3_opt_aux [] false f
  let ho_4_opt f = ho_4_opt_aux [] false f
  let ho_5_opt f = ho_5_opt_aux [] false f
  let ho_6_opt f = ho_6_opt_aux [] false f

  let ho_1 s = ho_1_opt_aux [] false (fun _ -> true) s
  let ho_2 s = ho_2_opt_aux [] false (fun _ -> true) s
  let ho_3 s = ho_3_opt_aux [] false (fun _ -> true) s
  let ho_4 s = ho_4_opt_aux [] false (fun _ -> true) s
  let ho_5 s = ho_5_opt_aux [] false (fun _ -> true) s
  let ho_6 s = ho_6_opt_aux [] false (fun _ -> true) s

  let ho_eff_1 s l = ho_1_opt_aux l false (fun _ -> true) s
  let ho_eff_2 s l = ho_2_opt_aux l false (fun _ -> true) s
  let ho_eff_3 s l = ho_3_opt_aux l false (fun _ -> true) s
  let ho_eff_4 s l = ho_4_opt_aux l false (fun _ -> true) s
  let ho_eff_5 s l = ho_5_opt_aux l false (fun _ -> true) s
  let ho_eff_6 s l = ho_6_opt_aux l false (fun _ -> true) s

  let loop_1 s = ho_1_opt_aux [] true (fun _ -> true) s
  let loop_2 s = ho_2_opt_aux [] true (fun _ -> true) s
  let loop_3 s = ho_3_opt_aux [] true (fun _ -> true) s
  let loop_4 s = ho_4_opt_aux [] true (fun _ -> true) s
  let loop_5 s = ho_5_opt_aux [] true (fun _ -> true) s
  let loop_6 s = ho_6_opt_aux [] true (fun _ -> true) s

  let loop_1_no _ _ _ s = s
  let loop_2_no _ _ _ _ s = s
  let loop_3_no _ _ _ _ _ s = s
  let loop_4_no _ _ _ _ _ _ s = s
  let loop_5_no _ _ _ _ _ _ _ s = s
  let loop_6_no _ _ _ _ _ _ _ _ s = s

  
  let ho_1_num (i:int) s =  let str=(s^"#"^(string_of_int i)) in ho_1 str
  let ho_2_num (i:int) s =  let str=(s^"#"^(string_of_int i)) in ho_2 str
  let ho_3_num (i:int) s =  let str=(s^"#"^(string_of_int i)) in ho_3 str
  let ho_4_num (i:int) s =  let str=(s^"#"^(string_of_int i)) in ho_4 str
  let ho_5_num (i:int) s =  let str=(s^"#"^(string_of_int i)) in ho_5 str
  let ho_6_num (i:int) s =  let str=(s^"#"^(string_of_int i)) in ho_6 str

  let no_1_num (i:int) s _ _ f  =  f
  let no_2_num (i:int) s _ _ _ f =  f
  let no_3_num (i:int) s _ _ _ _ f =  f
  let no_4_num (i:int) s _ _ _ _ _ f =  f
  let no_5_num (i:int) s _ _ _ _ _ _ f =  f
  let no_6_num (i:int) s _ _ _ _ _ _ _ f =  f

  let no_1 _ _ _ f = f
  let no_2 _ _ _ _ f = f
  let no_3 _ _ _ _ _ f = f
  let no_4 _ _ _ _ _ _ f = f
  let no_5 _ _ _ _ _ _ _ f = f
  let no_6 _ _ _ _ _ _ _ _ f = f

  let no_eff_1 _ _ _ _ f = f
  let no_eff_2 _ _ _ _ _ f = f
  let no_eff_3 _ _ _ _ _ _ f = f
  let no_eff_4 _ _ _ _ _ _ _ f = f
  let no_eff_5 _ _ _ _ _ _ _ _ f = f
  let no_eff_6 _ _ _ _ _ _ _ _ _ f = f

  let no_1_opt  _ _ _ _ f = f
  let no_2_opt  _ _ _ _ _ f = f
  let no_3_opt  _ _ _ _ _ _ f = f
  let no_4_opt  _ _ _ _ _ _ _ f = f
  let no_5_opt  _ _ _ _ _ _ _ _ f = f
  let no_6_opt  _ _ _ _ _ _ _ _ _ f = f

  let no_eff_1_opt  _ _ _ _ _ f = f
  let no_eff_2_opt  _ _ _ _ _ _ f = f
  let no_eff_3_opt  _ _ _ _ _ _ _ f = f
  let no_eff_4_opt  _ _ _ _ _ _ _ _ f = f
  let no_eff_5_opt  _ _ _ _ _ _ _ _ _ f = f
  let no_eff_6_opt  _ _ _ _ _ _ _ _ _ _ f = f
end;;

module type MEM_PROP = 
    sig
      type t
      val eq: t->t->bool
      val are_disj: t->t-> bool
      val star_t : t->t->bool (*decide if to keep the first arg*)
      val and_t : t->t->bool
      val or_t : t->t->bool
      val string_of : t -> string
    end;;

module Mem_prop_comb = 
 functor (P1:MEM_PROP) ->
 functor (P2:MEM_PROP) ->
 struct
   type t = (P1.t*P2.t)
   let eq (f1,s1) (f2,s2) = (P1.eq f1 f2)&(P2.eq s1 s2)
   let are_disj (f1,s1) (f2,s2) = 
      if P1.are_disj f1 f2 then true 
      else P2.are_disj s1 s2        
   let star_t (f1,s1) (f2,s2) = (P1.star_t f1 f2) & (P2.star_t s1 s2)
   let and_t (f1,s1) (f2,s2) = (P1.and_t f1 f2) & (P2.and_t s1 s2)
   let or_t (f1,s1) (f2,s2) = (P1.or_t f1 f2) & (P2.or_t s1 s2)
   let string_of (f,s) = "("^(P1.string_of f)^","^(P2.string_of s)^")"
  end;;

module type MEM_TYPE =
sig
  type t
  type ef = t -> t -> bool
  type tlist = t list
  val eq : ef
  val overlap : t -> t -> bool
  val intersect : tlist -> tlist -> tlist (* /\ *)
    (* under approx or-ing *)
 (* val overlap_eq : ef -> t -> t -> bool
  val intersect_eq : ef -> tlist -> tlist -> tlist (* /\ *)*)
  val star_union : tlist -> tlist -> tlist (* @ *)
  (* combine by star, without normalization *)
  val and_union : tlist -> tlist -> tlist (* @ *)    
  val string_of : t -> string
end;;

module type PTR_TYPE =
sig
  type t
  type ef = t -> t -> bool
  type tlist = t list
  val eq : ef
  val disj : ef
  (*val intersect_eq : ef -> tlist -> tlist -> tlist*)
  val intersect : tlist -> tlist -> tlist
  val string_of : t -> string
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
    functor (Elt : MEM_TYPE ) ->
struct
  type ptr = Elt.t
  type baga = ptr list

  let mkEmpty : baga = []
  let eq = Elt.eq
  let overlap = Elt.overlap
  let intersect = Elt.intersect
  (*let overlap_eq = Elt.overlap_eq
  let intersect_eq = Elt.intersect_eq*)
  let star_union = Elt.star_union
  let and_union = Elt.and_union

  (* need a semantic overlap operator that takes
     aliasing into account *)

  (* a singleton bag *)
  let singleton_baga (e:ptr) : baga = [e]

 (* let rec is_dupl_baga_eq eq (xs:baga) : bool = 
    match xs with
      | [] -> false
      | x::xs1 -> match xs1 with
          | [] -> false
          | _ -> if (List.exists (overlap_eq eq x) xs1) then true else is_dupl_baga_eq eq xs1*)

  let rec is_dupl_baga (xs:baga) : bool = 
    match xs with
      | [] -> false
      | x::xs1 -> match xs1 with
          | [] -> false
          | _ -> if (List.exists (overlap x) xs1) then true else is_dupl_baga xs1

  (* false result denotes contradiction *)
  (*let is_sat_baga_eq eq (xs:baga) : bool = not(is_dupl_baga_eq eq xs)*)

  (* false result denotes contradiction *)
  let is_sat_baga (xs:baga) : bool = not(is_dupl_baga xs)

  (*
\    [d1,d2] & [d3,d4] = [d1,d2,d3,d4]
    [d1,d2] | [d3,d4] = [d1|d3,d1|d4,d2|d3,d2|d4]
    d1|d3 = d1 \cap d3
  *)

  (* star conjunction of two bag of addresses *)
  let star_baga (x:baga) (y:baga) : baga = star_union x y

  (* conjunction of two bag of addresses *)
  (*let conj_baga_eq eq (xs:baga) (ys:baga) : baga = intersect_eq eq xs ys*)

  (* conjunction of two bag of addresses *)
  let conj_baga (xs:baga) (ys:baga) : baga = and_union xs ys

  (* disjunction of two bag of addresses *)
  let or_baga (xs:baga) (ys:baga) : baga = intersect xs ys

  (* disjunction of two bag of addresses *)
  (*let or_baga_eq eq (xs:baga) (ys:baga) : baga = intersect_eq eq xs ys*)


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
  let disj = Debug.no_2 "disjSet disj " Elt.string_of Elt.string_of string_of_bool Elt.disj

  module BL_EQ = BListEQ(Elt)
  open BL_EQ

  (* let is_dupl_baga _ = true *)

  (* an empty difference set *)
  let mkEmpty : dpart = []

  (* an empty difference set *)
  let is_empty (d:dpart) : bool = (d==[])

  (* one list difference set *)
  let one_list_dset (e:dlist) : dpart = [e]

  (* a singleton difference set *)
  let singleton_dset (e:ptr) : dpart = [[e]]

  let is_dupl_dset (xs:dpart) : bool = 
    List.exists (check_dups_eq (fun x y -> eq x y & disj x y)) xs

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
      List.exists (fun l-> 
        try
          let vx = List.find (eq x) l in
          let vy = List.find (eq y) l in
          disj vx vy
        with Not_found -> false ) s
    
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
    not(is_dupl_dset xs)

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
    "Counters: \n "^ (String.concat "\n" (List.map (fun (k,v) -> k^" = "^(string_of_int v)) s))^"\n"
end;;

class task_table =
object 
  val tasks = Hashtbl.create 10
  method add_task_instance msg time = 	
    let m = if (time>Globals.profile_threshold) then  [time] else [] in
    try 
	  let (t1,cnt1,max1) = Hashtbl.find tasks msg in
	  Hashtbl.replace tasks msg (t1+.time,cnt1+1,m@max1)
    with Not_found -> 
	    Hashtbl.add tasks msg (time,1,m)

  method print : unit = 
    let str_list = Hashtbl.fold (fun c1 (t,cnt,l) a-> (c1,t,cnt,l)::a) tasks [] in
    let str_list = List.sort (fun (c1,_,_,_)(c2,_,_,_)-> String.compare c1 c2) str_list in
    let ot = 
		try
			let (_,ot,_,_) = List.find (fun (c1,_,_,_)-> (String.compare c1 "Overall")=0) str_list in ot
		with | Not_found -> 10000000. in
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
    print_string ("\n profile results: there where " ^(string_of_int cnt)^" keys \n"^str^"\n" ) 
end;;


module Profiling =
struct
  let counters = new mult_counters
  let tasks = new task_table
  let profiling_stack = new stack ("stack underflow",0.,false) 
    (fun (s,v,b)-> "("^s^","^(string_of_float v)^","^(string_of_bool b) ^")")

  let add_to_counter (s:string) i = 
    if !Globals.enable_counters then counters#add s i
    else ()
  let inc_counter (s:string) = add_to_counter s 1

  let string_of_counters () =  counters#string_of

  let get_time () = 
	let r = Unix.times () in
	r.Unix.tms_utime +. r.Unix.tms_stime +. r.Unix.tms_cutime +. r.Unix.tms_cstime

  let push_time_no_cnt msg = 
    if (!Globals.profiling) then
      let timer = get_time () in
	  profiling_stack # push (msg, timer,true) 
    else ()

  let push_time msg = 
    if (!Globals.profiling) then
      (inc_counter ("cnt_"^msg);
      let timer = get_time () in
	  profiling_stack#push (msg, timer,true) )
	  (* profiling_stack := (msg, timer,true) :: !profiling_stack) *)
    else ()

  let pop_time msg = 
    if (!Globals.profiling) then
	  let m1,t1,_ = profiling_stack # top in
	  if (String.compare m1 msg)==0 then 
	    let t2 = get_time () in
	    if (t2-.t1)< 0. then Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("negative time")}
	    else
		  profiling_stack # pop;
	    if (List.exists (fun (c1,_,b1)-> (String.compare c1 msg)=0) profiling_stack#get) then begin
		  (* if (List.exists (fun (c1,_,b1)-> (String.compare c1 msg)=0&&b1) !profiling_stack) then begin *)
		  (* 	profiling_stack :=List.map (fun (c1,t1,b1)->if (String.compare c1 msg)=0 then (c1,t1,false) else (c1,t1,b1)) !profiling_stack; *)
		  (* 	print_string ("\n double accounting for "^msg^"\n") *)
          (* print_string ("\n skip double accounting for "^msg^"\n")  *)
	    end	
        else tasks # add_task_instance m1 (t2-.t1) 
	  else 
	    Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("Error popping "^msg^"from the stack")}
    else ()

 let print_info () = if (!Globals.profiling) then  tasks # print else ()

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
	if (!Globals.profiling) then
	  let rec helper l = match l with
        | [] -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("Error special poping "^msg^"from the stack")}
        | (m1,_,_)::t ->  if not ((String.compare m1 msg)==0) then helper t			
		  else t in
      profiling_stack#override (helper profiling_stack#get) 
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
    let _ = 
	  while (!start_idx < len) && ((String.get input !start_idx) = ' ') do
	    start_idx := !start_idx + 1
	  done in
    let end_idx = ref (len - 1) in
    let _ = 
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
    Str.global_replace dot "_" 
        (Str.global_replace caret "$" s)

  let replace_minus_with_uscore s =
    let minus = Str.regexp "-" in
    let caret = Str.regexp "\\^" in
    Str.global_replace minus "_" 
        (Str.global_replace caret "$" s)

  let replace_path_sep_with_uscore s =
    let path_sep = Str.regexp "/" in
    let caret = Str.regexp "\\^" in
    Str.global_replace path_sep "_" 
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

(** removing 'option' types *)
let unsome : 'a option -> 'a = 
  function
	| Some x -> x
	| None   -> failwith "[util] tried to deoptionify None"

let is_some : 'a option -> bool =
  function
	| Some x -> true
	| None -> false

let some2list : 'a option -> 'a list = function 
	| Some x-> [x]
	| None -> []
	 
let trans_some f (x:'a option) : 'b option= match x with
	| Some x-> Some (f x)
	| None -> None
	
	
(** Read the given file into a string. *)
let string_of_file (fname : string) =
  if Sys.file_exists fname then
    let chn = open_in fname in
    let len = in_channel_length chn in
    let str = String.make len ' ' in
    let _ = really_input chn str 0 len in
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
  | '(' | ')' | ' ' | '+' | ':' -> true
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

let break_lines (input : string) : string =
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

end;;

module ExcNumbering =
struct

  (*hairy stuff for exception numbering*)

  let exc_list = ref ([]:(string * string * Globals.nflow ) list)

  let clear_exc_list () =
    Globals.n_flow_int := (-1,-1);
    Globals.ret_flow_int := (-1,-1);
    Globals.spec_flow_int := (-1,-1);
    Globals.top_flow_int := (-2,-2);
    Globals.exc_flow_int := (-2,-2);
    exc_list := []

  let remove_dups1 n = BList.remove_dups_eq (=) n

  let get_hash_of_exc (f:string): Globals.nflow = 
    if ((String.compare f Globals.stub_flow)==0) then 
	  Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("Error found stub flow")}
    else
	  let rec get (lst:(string*string*Globals.nflow)list):Globals.nflow = match lst with
	    | [] -> Globals.false_flow_int
	    | (a,_,(b,c))::rst -> if (String.compare f a)==0 then (b,c)
		  else get rst in
      (get !exc_list)

  (*t1 is a subtype of t2*)
  let exc_sub_type (t1 : Globals.constant_flow) (t2 : Globals.constant_flow): bool = 
    let r11,r12 = get_hash_of_exc t1 in
    if ((r11==0) && (r12==0)) then false
    else
	  let r21,r22 = get_hash_of_exc t2 in
	  if ((r21==0) && (r22==0)) then true
	  else
	    ((r11>=r21)&&(r12<=r22))

  (*let exc_int_sub_type ((t11,t12):Globals.nflow)	((t21,t22):Globals.nflow):bool = if (t11==0 && t12==0) then true else ((t11>=t21)&&(t12<=t22))*)

  let get_closest ((min,max):Globals.nflow):(string) = 
    let rec get (lst:(string*string*Globals.nflow) list):string*Globals.nflow = match lst  with
	  | [] -> (Globals.false_flow,Globals.false_flow_int)
	  | (a,b,(c,d)):: rest-> if (c==min && d==max) then (a,(c,d)) (*a fits perfect*)
	    else let r,(minr,maxr) = (get rest) in
	    if (minr==c && maxr==d)||(c>min)||(d<max) then (r,(minr,maxr)) (*the rest fits perfect or a is incompatible*)
	    else if (minr>min)||(maxr<max) then (a,(c,d)) (*the rest is incompatible*)
	    else if ((min-minr)<=(min-c) && (maxr-max)<=(d-max)) then (r,(minr,maxr))
	    else (a,(c,d)) in
    let r,_ = (get !exc_list) in r

  (*constructs the mapping between class/data def names and interval types*) 
  let c_h () =
    let rec lrr (f1:string)(f2:string):(((string*string*Globals.nflow) list)*Globals.nflow) =
	  let l1 = List.find_all (fun (_,b1,_)-> ((String.compare b1 f1)==0)) !exc_list in
	  if ((List.length l1)==0) then let i = (Globals.fresh_int()) in let j = (Globals.fresh_int()) in ([(f1,f2,(i,j))],(i,j))
	  else let ll,(mn,mx) = List.fold_left (fun (t,(o_min,o_max)) (a,b,(c,d))-> let temp_l,(n_min, n_max) = (lrr a b) in 
	  (temp_l@t,((if ((o_min== -1)||(n_min<o_min)) then n_min else o_min),(if (o_max<n_max) then n_max else o_max)))			
	  ) ([],(-1,-1)) l1 in
	  ( ((f1,f2,(mn,mx))::ll) ,(mn,mx)) in
    let r,_ = (lrr Globals.top_flow "") in
    let _ = exc_list := r in
    Globals.n_flow_int := (get_hash_of_exc Globals.n_flow);
    Globals.ret_flow_int := (get_hash_of_exc Globals.ret_flow);	
    Globals.spec_flow_int := (get_hash_of_exc Globals.spec_flow);	
    Globals.top_flow_int := (get_hash_of_exc Globals.top_flow);
    Globals.exc_flow_int := (get_hash_of_exc Globals.abnormal_flow)
	    (*let _ = print_string ((List.fold_left (fun a (c1,c2,(c3,c4))-> a ^ " (" ^ c1 ^ " : " ^ c2 ^ "="^"["^(string_of_int c3)^","^(string_of_int c4)^"])\n") "" r)) in*)

  let add_edge(n1:string)(n2:string):bool =
	let _ =  exc_list := !exc_list@ [(n1,n2,Globals.false_flow_int)] in
	true

  let clean_duplicates ()= 
	exc_list := remove_dups1 !exc_list

  let has_cycles ():bool =
	let rec cc (crt:string)(visited:string list):bool = 
	  let sons = List.fold_left (fun a (d1,d2,_)->if ((String.compare d2 crt)==0) then d1::a else a) [] !exc_list in
	  if (List.exists (fun c-> (List.exists (fun d->((String.compare c d)==0)) visited)) sons) then true
	  else (List.exists (fun c-> (cc c (c::visited))) sons) in	
	(cc Globals.top_flow [Globals.top_flow])

end;;

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
          | [] -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("pushf_add_level on empty stack")}
          | lvl::stk -> let (new_i,v)=f i 
            in (new_i,(v@lvl)::stk)

  let add_level (lst:'b list)  ((i,stk):('a,'b) stackable) : ('a,'b) stackable
        = match stk with
          | [] -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("pushf_add_level on empty stack")}
          | lvl::stk -> (i,(lst@lvl)::stk)

  let close_level ((i,stk):('a,'b) stackable) : ('a,'b) stackable
        = match stk with
          | lvl::(lvl2::stk) -> (i, (lvl@lvl2)::stk)
          | _ -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("close level requires at least two levels")}

  let collapsef_stack  (f:'a -> ('b list) -> 'a)  ((i,stk):('a,'b) stackable) : 'a
        = f i (List.concat stk)

  let popf_level (f:'a -> ('b list) -> ('a * ('b list))) ((i,stk):('a,'b) stackable) : ('a,'b) stackable
        = match stk with
          | lvl::stk -> let (newi,lst)=(f i lvl) in
            if (is_empty lst) then (newi, stk)
            else (add_level lst (newi,stk))
          | _ -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("popf_level on empty stack")}

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
        | ((x,[])::xs1) -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("tag missing during ehc_sorted_tag")}
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
        | ((x,[])::xs1) -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("cannot happen!")}
        | ((x,n::t)::xs1) -> 
              if (n==no) then helper xs1 ((x,t)::acc) no
              else 
                let rs=helper xs [] (no+1) in
                if (is_empty acc) then rs
                else (List.rev acc,no)::rs
    in let r=check_sorted_tag xs in
    if r then helper xs acc 1 
    else Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("need to sort group_tag!")}

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
