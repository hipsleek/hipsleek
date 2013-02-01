(* listx.ml - lists (extended) *)

open Std


(*---- *)

let head : 'a list -> 'a = function
  | [] -> fail "Listx.head: empty list"
  | x::_ -> x

let tail : 'a list -> 'a list = function
  | [] -> fail "Listx.tail: empty list"
  | _::xs -> xs

let rec last : 'a list -> 'a = function
  | [] -> failwith "Listx.last: empty list"
  | [x] -> x
  | _::xs -> last xs

let rec get (l:'a list) (i:int) : 'a =
  if i<0 then fail "Listx.get: negative i: %d" i else
  match l with
  | [] -> fail "Listx.get: empty list for i: %d" i
  | x::_ when i=0 -> x
  | _::xs -> get xs (i-1)

let rec set (l:'a list) (i:int) (y:'a) : 'a list =
  if i<0 then fail "Listx.set: negative i: %d" i else
  match l with
  | [] -> fail "Listx.set: empty list for index: %d" i
  | x::xs when i=0 -> y :: xs
  | x::xs -> x :: (set xs (i-1) y)

let rec map_at (f:'a -> 'a) (l:'a list) (i:int) : 'a list =
  if i<0 then fail "Listx.set: negative i: %d" i else
  match l with
  | [] -> fail "Listx.set: empty list for index: %d" i
  | x::xs when i=0 -> f x :: xs
  | x::xs -> x :: (map_at f xs (i-1))

(* tail-recursive *)
let rec foldl (f:'a -> 'b -> 'a) (acc:'a) : 'b list -> 'a = function
  | [] -> acc
  | x::xs -> foldl f (f acc x) xs

(* non tail-recursive *)
let rec foldr (f:'a -> 'b -> 'b) (acc:'b) : 'a list -> 'b = function
  | [] -> acc
  | x::xs -> f x (foldr f acc xs)

let foldl1 (f:'a -> 'a -> 'a) : 'a list -> 'a = function
  | [] -> fail "Listx.foldl1: empty list for base case"
  | x::xs -> foldl f x xs

let foldr1 (f:'a -> 'a -> 'a) : 'a list -> 'b = function
  | [] -> fail "Listx.foldr1: empty list for base case"
  | x::xs -> foldr f x xs

let rec foldl2 (f:'a -> 'b -> 'c -> 'a) (acc:'a) 
    (l1:'b list) (l2:'c list) : 'a = 
  match (l1,l2) with
  | (x::xs,y::ys) -> foldl2 f (f acc x y) xs ys
  | _ -> acc

let rec foldr2 (f:'a -> 'b -> 'c -> 'c) (acc:'c) 
    (l1:'a list) (l2:'b list) : 'c = 
  match (l1,l2) with
  | (x::xs,y::ys) -> f x y (foldr2 f acc xs ys)
  | _ -> acc

let size (l:'a list) : int = foldl (fun acc _ -> 1+acc) 0 l
let cat (ls:'a list list) : 'a list = foldr (@) [] ls
let rev (l:'a list) : 'a list = foldl (fun acc x -> x::acc) [] l

let cat2 : 'a list -> 'a list -> 'a list = (@)
let cat2_rev : 'a list -> 'a list -> 'a list = List.rev_append

let rec cat_rev_with (acc:'a list) : 'a list list -> 'a list = function
  | [] -> acc
  | x::s -> cat_rev_with (cat2_rev x acc) s

let cat_rev (s:'a list list) = cat_rev_with [] s

let map_slow (f:'a -> 'b) : 'a list -> 'b list = foldr (fun x acc -> f x :: acc) []

let rec map (f:'a -> 'b) : 'a list -> 'b list = function
  | [] -> []
  | x::s -> f x :: map f s

let rec map_rev_with (acc:'b list) (f:'a -> 'b) : 'a list -> 'b list = function
  | [] -> acc
  | x::s -> map_rev_with (f x :: acc) f s

(* tail-recursive, reversed *)
let map_rev (f:'a -> 'b) (s:'a list) : 'b list = map_rev_with [] f s  

let rec iter (f:'a -> unit) : 'a list -> unit = function 
  | [] -> ()
  | a::s -> f a; iter f s

let rec iter_last (f1:'a -> unit) (f2:'a -> unit) : 'a list -> unit = function 
  | [] -> ()
  | [a] -> f2 a
  | a::s -> f1 a; iter_last f1 f2 s

let map2 (f:'a -> 'b -> 'c) : 'a list -> 'b list -> 'c list
  = foldr2 (fun x y acc -> f x y :: acc) []

let iter2 (f:'a -> 'b -> unit) : 'a list -> 'b list -> unit
  = foldr2 (fun x y acc -> f x y) ()

let rec all (f:'a -> bool) : 'a list -> bool = function
  | [] -> true
  | x::xs -> f x && all f xs

let rec some (f:'a -> bool) : 'a list -> bool = function
  | [] -> false
  | x::xs -> f x || some f xs

let rec all2 (f:'a -> 'b -> bool) (l1:'a list) (l2:'b list) : bool =
  match (l1,l2) with
  | ([],[]) -> true
  | (x::xs,y::ys) -> f x y && all2 f xs ys
  | _ -> false

let rec some2 (f:'a -> 'b -> bool) (l1:'a list) (l2:'b list) : bool = 
  match (l1,l2) with
  | (x::xs,y::ys) -> f x y || some2 f xs ys
  | _ -> false

let rec find (f:'a -> bool) : 'a list -> 'a option = function
  | [] -> None
  | x::xs -> if f x then Some x else find f xs

let mem_slow (x:'a) (l:'a list) : bool = find ((=) x) l <> None
let memq_slow (x:'a) (l:'a list) : bool = find ((==) x) l <> None

let rec mem (x:'a) : 'a list -> bool = function
  | [] -> false
  | x2::xs -> x=x2 || mem x xs

let rec memq (x:'a) : 'a list -> bool = function
  | [] -> false
  | x2::xs -> x==x2 || memq x xs

let assoc_by (f:'a -> bool) (l:('a * 'b) list) : 'b option =
  opt_map snd (find (fun (x,_) -> f x) l)

let rassoc_by (f:'b -> bool) (l:('a * 'b) list) : 'a option =
  opt_map fst (find (fun (_,y) -> f y) l)

let assoc (x:'a) : ('a * 'b) list -> 'b option = assoc_by ((=) x)
let assocq (x:'a) : ('a * 'b) list -> 'b option = assoc_by ((==) x)
let rassoc (y:'b) : ('a * 'b) list -> 'a option = rassoc_by ((=) y)
let rassocq (y:'b) : ('a * 'b) list -> 'a option = rassoc_by ((==) y)


(*---- Show and print. *)

let rec show (sep:string) (f:'a -> string) : 'a list -> string = function
  | [] -> ""
  | [x] -> f x
  | x::xs -> f x ^ sep ^ show sep f xs

let rec print (sep:string) (f:'a -> unit) : 'a list -> unit = function
  | [] -> ()
  | [x] -> f x
  | x::xs -> f x; Std.print sep; print sep f xs

let showz f s = show " " f s
let show0 f s = show "" f s
let show1 f s = show "\n" f s
let show2 f s = show "\n\n" f s

let showx sep s = show sep Std.show s
let showxz s = showx " " s
let showx0 s = showx "" s
let showx1 s = showx "\n" s
let showx2 s = showx "\n\n" s

let printz f s = print " " f s 
let print0 f s = iter f s
let print1 f s = print "\n" f s
let print2 f s  = print "\n\n" f s

let printx sep = print sep Std.printx
let printxz s = printx " " s
let printx0 s = printx "" s
let printx1 s = printx "\n" s 
let printx2 s = printx "\n\n" s


(*---- *)

let take (f:'a -> bool) (s:'a list) : 'a list =  
  rev (foldl (fun acc x -> if f x then x::acc else acc) [] s)

let drop (f:'a -> bool) : 'a list -> 'a list = take (flip f)

let split (f:'a -> bool) : 'a list -> 'a list * 'a list =
  foldl (fun (acc1,acc2) x 
    -> if f x then (x::acc1,acc2) else (acc1,x::acc2)) ([],[])

let rec taken_by (f:'a -> bool) (n:int) : 'a list -> 'a list = function
  | [] -> []
  | _ when n<1 -> []
  | x::xs -> if f x then x :: taken_by f (n-1) xs else taken_by f n xs

let rec dropn_by (f:'a -> bool) (n:int) : 'a list -> 'a list = function
  | [] -> []
  | xs when n<1 -> xs
  | x::xs -> if f x then dropn_by f (n-1) xs else x :: dropn_by f n xs

let rec taken (n:int) : 'a list -> 'a list = function
  | [] -> []
  | _ when n<1 -> []
  | x::xs -> x :: (taken (n-1) xs)

let rec dropn (n:int) : 'a list -> 'a list = function
  | [] -> []
  | xs when n<1 -> xs
  | x::xs -> dropn (n-1) xs

(* Reverse is slow... *)
let rec splitn_with (acc:'a list) (n:int) : 'a list -> 'a list * 'a list = function
  | [] -> (rev acc, [])
  | s when n<1 -> (rev acc, s)
  | x::s -> splitn_with (x :: acc) (n-1) s

let rec splitn_fast (n:int) : 'a list -> 'a list * 'a list = function
  | [] -> ([], [])
  | s when n<1 -> ([], s)
  | x::s -> let (s1,s2) = splitn_fast (n-1) s in (x::s1, s2)

(* Let's use the simplest definition for now (its speed is comparable to above). *)
let splitn (n:int) (s:'a list) : 'a list * 'a list = (taken n s, dropn n s)

let rec whilst (f:'a -> bool) : 'a list -> 'a list = function
  | [] -> []
  | x::xs -> if f x then x :: whilst f xs else []

let sum : int list -> int = foldl ( + ) 0
let prod : int list -> int = foldl ( * ) 0
let max : int list -> int = foldl Pervasives.max 0
let min : int list -> int = foldl Pervasives.min 0

let zip (l1:'a list) (l2:'b list) : ('a * 'b) list = 
  rev (foldl2 (fun acc x y -> (x,y) :: acc) [] l1 l2)

let unzip (l:('a * 'b) list) : 'a list * 'b list = 
  Std.map2 rev (foldl (fun (acc1,acc2) (x,y) -> (x::acc1, y::acc2)) ([],[]) l)

let sort_by : ('a -> 'a -> int) -> 'a list -> 'a list = List.sort
let rsort_by (f:'a -> 'a -> int) : 'a list -> 'a list = sort_by (neg2 f)
let merge_by : ('a -> 'a -> int) 
  -> 'a list -> 'a list -> 'a list = Compat.list_merge
let sort (s:'a list) : 'a list = sort_by compare s

(* interval 1 5 = [1;2;3;4;5] *)
let rec interval (i:int) (j:int) : int list =
  if i>j then [] else i :: (interval (i+1) j)

(* nonempty power set *)
let rec rpower : 'a list -> 'a list list = function
  | [] -> []
  | x::xs -> (x::xs) :: rpower xs

let power a = rev (map rev (rpower (rev a)))

(* sublist from index i (inclusive) to index j (exclusive). *)
let rec subj (l:'a list) (i:int) (j:int) : 'a list =
  if i>=j then [] else 
  match l with
  | [] -> fail "Listx.subj: empty list with i,j: %d,%d" i j
  | x::xs ->
    if i>0 then subj xs (i-1) (j-1)
    else x :: (subj xs 0 (j-1))

let subn l i n = subj l i (i+n)
let sub l i = subj l i (size l)

let lastn (l:'a list) (n:int) : 'a list = subj l (size l - n) (size l - 1)

let rec make (x:'a) (n:int) : 'a list =
  if n <= 0 then [] else x :: (make x (n-1))

let mapc (f:'a -> 'b list) (l:'a list) : 'b list = cat (map f l)

let mapc_rev (f:'a -> 'b list) (l:'a list) : 'b list = cat_rev (map_rev f l)

let map2c (f:'a -> 'b -> 'c list) (l1:'a list) (l2:'b list) : 'c list = 
  cat (map2 f l1 l2)

let rec initi (i:int) (n:int) (f:int -> 'a) : 'a list =
  if i>=n then [] else
  (f i) :: (initi (i+1) n f)

let init (n:int) (f:int -> 'a) : 'a list = initi 0 n f


(* Group adjacent and equal elements. *)
let rec group_by0 (a:'a) (s:'a list) (accum:'a list list) (f:'a -> 'a -> bool)
  : 'a list -> 'a list list = function
  | [] -> s :: accum
  | (a2::s2) when f a a2 -> group_by0 a (a::s) accum f s2
  | (a2::s2) -> group_by0 a2 [a2] (s::accum) f s2

let group_by (f:'a -> 'a -> bool) : 'a list -> 'a list list = function
  | [] -> []
  | a::s -> group_by0 a [a] [] f s

let partition_by (f:'a -> 'a -> int) (s:'a list) : 'a list list = 
  let f2 a1 a2 = (f a1 a2 = 0) in
  (group_by f2 (sort_by f s))

let rec compress : 'a option list -> 'a list = function
  | [] -> []
  | None::s -> compress s
  | Some a::s -> a :: compress s

let collect_slow (f:'a -> 'b option) (s:'a list) : 'b list =
  compress (map f s)

let rec collect (f:'a -> 'b option) : 'a list -> 'b list = function
  | [] -> []
  | a::s -> 
    (match f a with
    | None -> collect f s
    | Some b -> b :: collect f s)

let mapi (f:'a * int -> 'b) (s:'a list) : 'b list =
  map f (zip s (interval 0 ((size s) - 1)))

let iteri (f:int * 'a -> unit) (s:'a list) : unit =
  iter f (zip (interval 0 ((size s) - 1)) s)

(* Pair each element with its index. *)

let rindex (s:'a list) : ('a * int) list = zip s (interval 0 ((size s) -1))
let index (s:'a list) : (int * 'a) list = zip (interval 0 ((size s) -1)) s

let domain (s:('a * 'b) list) : 'a list = map fst s
let range (s:('a * 'b) list) : 'b list = map snd s

let rec insert (i:int) (a:'a) : 'a list -> 'a list = function
  | s when i=0 -> a :: s
  | [] -> fail "Listx.insert: list too short"
  | a2::s when i>0 -> a2 :: (insert (i-1) a s)
  | _ -> fail "Listx.insert: negative index"

let rec del (a:'a) (s:'a list) : 'a list = 
  match s with
  | [] -> []
  | a2::s2 -> if a=a2 then s2 else a2 :: del a s2

let rec del_by (f:'a -> bool) (s:'a list) : 'a list = 
  match s with
  | [] -> []
  | a::s2 -> if f a then s2 else a :: del_by f s2

(* add an new association, replacing the old one if exists *)
let assoc_add (s:('a * 'b) list) (x:'a) (y:'b) : ('a * 'b) list = 
  (x,y) :: (del_by (fun (x2,_) -> x=x2) s)

let minus (s1:'a list) (s2:'a list) : 'a list =
  foldr del s1 s2

let minus_by (f:'a -> 'a -> bool) (s1:'a list) (s2:'a list) : 'a list =
  foldr (fun a -> del_by (f a)) s1 s2

let subset (s1:'a list) (s2:'a list) : bool =
  all (fun a -> mem a s2) s1

let restrict1 (a:'a) (s:('a * 'b) list) : 'b list =
  let f (a2,b) = if a=a2 then Some b else None in
  collect f s

let restrict2 (b:'b) (s:('a * 'b) list) : 'a list =
  let f (a,b2) = if b=b2 then Some a else None in
  collect f s

let dot (a:'a) (s:'b list) : ('a * 'b) list =
  map (fun b -> (a,b)) s

let cross (s1:'a list) (s2:'b list) : ('a * 'b) list =
  mapc (fun a -> dot a s2) s1

(* separate 0 [1;2;3] = [1;0;2;0;3] *)
let rec separate (x:'a) : 'a list -> 'a list = function
  | [] -> []
  | [a] -> [a]
  | a::s -> a :: x :: (separate x s)

(* suffix 0 [1;2;3] = [1;0;2;0;3;0] *)
let rec suffix (x:'a) : 'a list -> 'a list = function
  | [] -> []
  | a::s -> a :: x :: (suffix x s)

(* unique elements (duplicates removed); stable = without changing the order *)
let rec uniq_stable : 'a list -> 'a list = function
  | [] -> []
  | a::s -> if mem a s then uniq_stable s else a :: uniq_stable s

(* unique elements (duplicates removed)
Assumption: sorted *)
let rec sorted_uniq : 'a list -> 'a list = function
  | [] -> []
  | [a] -> [a]
  | a1::(a2::_ as s) -> 
    if a1=a2 then sorted_uniq s else a1 :: sorted_uniq s

let uniq (s:'a list) : 'a list = sorted_uniq (sort s)

let rec uniq_stable_by (f:'a -> 'a -> bool) : 'a list -> 'a list = function
  | [] -> []
  | a::s -> 
    if some (f a) s then uniq_stable_by f s 
    else a :: uniq_stable_by f s

let eq (f:'a -> 'a -> bool) (s1:'a list) (s2:'a list) : bool =
  all2 f s1 s2

let is_uniq (s:'a list) : bool = (s = uniq_stable s)
let is_uniq_by (f:'a -> 'a -> bool) (s:'a list) : bool = 
  eq f s (uniq_stable_by f s)

let check_uniq (s:'a list) : unit =
  if not (is_uniq s) then 
    fail "Error: duplicates: %s" (showxz (minus s (uniq s)))

(* find one duplicate element *)
let rec dup1 : 'a list -> 'a option = function
  | [] -> None
  | x::s -> if mem x s then Some x else dup1 s

let rec dup1_by (f:'a -> 'a -> bool) : 'a list -> 'a option = function
  | [] -> None
  | x::s -> if some (f x) s then Some x else dup1_by f s

(* all duplicate elements *)
let dup (s:'a list) : 'a list = minus s (uniq s)
let dup_by (f:'a -> 'a -> bool) (s:'a list) : 'a list = 
  minus_by f s (uniq_stable_by f s)

let count (f:'a -> bool) (s:'a list) : int = size (take f s)

let fprint_sep (g:out_channel -> 'a -> unit) (sep:string) 
  (f:out_channel) (s:'a list) : unit =
  iter_last (fun a -> g f a; fprint f sep) (g f) s

let fprint (g:out_channel -> 'a -> unit) (f:out_channel) (s:'a list) : unit =
  iter (g f) s

let fcode (g:out_channel -> 'a -> unit) (f:out_channel) (s:'a list) : unit =
  Std.fprint f "["; fprint_sep g "; " f s; Std.fprint f "]"

let rec repeat (x:int) (s:'a list) : 'a list =
  if (x<=0) then [] else s @ repeat (x-1) s

let head_tail : 'a list -> 'a * 'a list = function
  | [] -> failwith "Listx.last: empty list"
  | a::s -> (a, s)

let rec map_state (f:'a -> 'b -> 'a * 'c) (a:'a) : 'b list -> 'a * 'c list = function
  | [] -> (a, [])
  | (b::s) -> 
    let (a2,c) = f a b in 
    let (a3,cs) = map_state f a2 s in
    (a2, c :: cs)

(* tail and head *)
let tail_head (s:'a list) : 'a list * 'a =
  let (h,t) = head_tail (rev s) in (rev t, h)
  
(* is s1 a prfix of s2 *)
let is_prefix (s1:'a list) (s2:'a list) : bool =
  s1 == s2 ||
  (size s1 <= size s2 && s1 = subj s2 0 (size s1))

(* skip the first n elements *)
let skip (n:int) (s:'a list) : 'a list = sub s n

let rec upto (a:'a) : 'a list -> 'a list = function
  | [] -> []
  | a2::_ when a=a2 -> []
  | a2::s -> a2 :: upto a s

let set_add (s:'a list) (a:'a) : 'a list = if mem a s then s else a :: s

let set_union (s1:'a list) (s2:'a list) = foldl set_add s1 s2

(* product [[1;2];[3];[4;5]] = [[1;3;4];[1;3;5];[2;3;4];[2;3;5]] *)
let rec product : 'a list list -> 'a list list = function
  | [] -> [[]]
  | s::ss -> 
    mapc (fun x -> map (fun s2 -> x :: s2) (product ss)) s

let add (x:'a) (s:'a list) : 'a list = x :: s

let empty : 'a list = []
let is_empty (s:'a list) : bool = s=[]
let single (x:'a) : 'a list = [x]

let if_cat (b:bool) (a:'a) (s:'a list) : 'a list = 
  if b then a :: s else s
