(* setx.ml - sets with layout equality test. *)

(* layout equality is defined by Pervasives.(=). that is, two sets are
equal if they have the same memory layout and content. using this
modules eliminates the need of passing other equality tests when using
sets or hashs. future work: type classes for ocaml. *)

(* (find-file "/usr/lib/ocaml/3.08/set.mli") *)

(* difference between setx.ml and listx.ml:

  1. ordered (for equality testing with unique representation)

  2. no duplicates

*)

open Std
module A = Arrayx
module L = Listx

type 'a t = 'a list                     (* internal representation *)
 
let rec add (a:'a) (s:'a t) : 'a t = 
  match s with
  | [] -> [a]
  | a2::s2 -> 
    let x = compare a a2 in
    if x=0 then s
    else if x=(-1) then a :: s
    else a2 :: (add a s2)

let empty = []
let is_empty (s:'a t) = (s = empty)
let is_nonempty (s:'a t) = (s <> empty)
let mem a s = L.mem a s
let foldl = L.foldl
let foldr = L.foldr
let head (s:'a t) : 'a = L.head s
let tail (s:'a t) : 'a t = L.tail s
let head_tail (s:'a t) : 'a * 'a t = (head s, tail s)

let single (a:'a) : 'a t = [a]
let minus = L.minus
let del = L.del
let some = L.some
let iter = L.iter
let iter_last = L.iter_last
let all = L.all
let last = L.last
let size (s:'a t) : int = L.size s
let subset : 'a t -> 'a t -> bool = L.subset

(* slow version *)
let rec of_list_slow : 'a list -> 'a t = function
  | [] -> empty
  | x::xs -> add x (of_list_slow xs)

(* fast version for sorted list representation *)
let of_list (s:'a list) : 'a t = L.sorted_uniq (L.sort s)

(* Assumption: unique, sorted. *)
let of_set (s:'a list) : 'a t = L.sorted_uniq (L.sort s)

let to_list : 'a t -> 'a list = identity
let to_list_list (s:'a t t) : 'a list list = Listx.map_rev to_list (to_list s)

let of_array (s:'a array) : 'a t = of_list (A.to_list s)
let to_array (s:'a t) : 'a array = A.of_list (to_list s)


(* slow version
let union (s1:'a t) (s2:'a t) : 'a t = foldr add s1 s2
*)

(* fast = merging two sorted lists (eliminating duplicates) *)
let rec union (s1:'a t) (s2:'a t) : 'a t =
  match (s1,s2) with
  | [], s -> s
  | s, [] -> s
  | (x1::s3, x2::s4) ->
    let y = compare x1 x2 in
    if y=0 then x1 :: union s3 s4       (* x1 = x2, pick x1 *)
    else if y<0 then x1 :: union s3 s2  (* x1 first *)
    else x2 :: union s1 s4              (* x2 first *)

(* integer version *)
let rec iunion (s1:int t) (s2:int t) : int t =
  match (s1,s2) with
  | [], s -> s
  | s, [] -> s
  | (x1::s3, x2::s4) ->
    if x1==x2 then x1 :: iunion s3 s4 
    else if x1<x2 then x1 :: iunion s3 s2 
    else x2 :: iunion s1 s4 


(* 2005-0330 more *)


let union_list (l:'a t list) : 'a t = Listx.foldl union empty l
let map_list (f:'a -> 'b) (s:'a t) : 'b list = Listx.map_rev f (to_list s)
let list_map (f:'a -> 'b) (s:'a list) : 'b t = of_list (Listx.map_rev f s)
let map (f:'a -> 'b) (s:'a t) : 'b t = of_list (Listx.map_rev f (to_list s))
let mapc (f:'a -> 'b t) (s:'a t) : 'b t = union_list (map f s)


(* integer version *)

let iunion_list (l:int t list) : int t = Listx.foldl iunion empty l
let imapc (f:'a -> int t) (s:'a t) : int t = iunion_list (map_list f s)


(*---- Show and Print. *)

let show (sep:string) (f:'a -> string) (s:'a t) : string = 
  Listx.show sep f (to_list s)

let print (sep:string) (f:'a -> unit) (s:'a t) : unit = 
  Listx.print sep f (to_list s)

let fprintf (g:out_channel -> 'a -> unit) (f:out_channel) (s:'a t) : unit =
  iter (fun a -> g f a) s

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


(*--- *)

let take (f:'a -> bool) (s:'a t) : 'a t = L.take f s

let induction (f1:unit -> 'b) (f2:'a -> 'a t -> 'b) (s:'a t) : 'b =
  if is_empty s then f1 () else
  let a = head s in
  let s2 = tail s in
  f2 a s2


(* worklist with a = state. *)
let rec fixpoint0 (visited:'b t) (f:'a -> 'b -> 'a * 'b t) (a:'a) (s:'b t) : 'a = 
  if is_empty s then a else
  let b = head s in
  let s2 = tail s in
  let (a2,s3) = f a b in
  let s4 = minus s3 visited in
  fixpoint0 (union visited s3) f a2 (union s2 s4)

let fixpoint f s = fixpoint0 empty f s


(* worklist with no repetition. use a better name than dfs? *)
let rec dfs0 (visited:'a t) (f:'a -> 'a t) (s:'a t) : unit = 
  if is_empty s then () else
  let a = head s in
  let s2 = tail s in
  let s3 = minus (f a) visited in
  dfs0 (union visited s3) f (union s2 s3)

(* TODO FIXME: heavily optimize this with imperative graphs. benchmark
against Fa.pt_make for making parseing automata *)
let dfs f s = dfs0 empty f s

let xx = ref 0

let rec worklist (f:'a -> 'a t) (s:'a t) : unit = 
  if is_empty s then () else
  let (a,s2) = head_tail s in
  worklist f (union s2 (f a))

let compress (s:'a option t) : 'a t = of_list (Listx.compress (to_list s))
let collect (f:'a -> 'b option) (s:'a t) : 'b t = compress (map f s)

let index (s:'a t) : (int * 'a) t = of_list (L.index (to_list s))
let rindex (s:'a t) : ('a * int) t = of_list (L.rindex (to_list s))
let interval (i:int) (j:int) : int t = of_list (L.interval i j)

(* TODO optimize *)
let count (f:'a -> bool) (s:'a t) : int = L.size (L.take f (to_list s))

let domain (s:('a * 'b) t) : 'a t = map fst s
let range (s:('a * 'b) t) : 'b t = map snd s

let rec test (s:'a t) : unit =
  match s with
  | [] -> ()
  | [a] -> ()
  | a1::a2::s2 -> assert (compare a1 a2 <= 0); test (a2::s2)

let of_list_set (s:'a t list) : 'a t = union_list (L.map_rev of_list s)

let list_mapc (f:'a -> 'b t) (s:'a list) : 'b t = of_list_set (L.map_rev f s)

let get (s:'a t) (i:int) : 'a = L.get s i

let check_subset (s1:'a t) (s2:'a t) : unit =
  if not (subset s1 s2) then fail "Error: not subset: %s" (showxz (minus s1 s2))

let check_eq (s1:'a t) (s2:'a t) : unit =
  check_subset s1 s2; check_subset s2 s1

let check_mem (a:'a) (s:'a t) : unit =
  if not (mem a s) then fail "Error: not mem: %s, %s" (Std.show a) (showxz s)

let fcode (g:out_channel -> 'a -> unit) (f:out_channel) (s:'a t) : unit =
  fprint f "Setx.of_set ["; 
  iter_last (fun a -> g f a; fprint f "; ") (g f) s; 
  fprint f "]"

let array_add (s:'a t array) (i:int) (a:'a) : unit = s.(i) <- add a s.(i)

let of_list_array (s:'a list array) : 'a t =
  of_list (L.cat_rev (A.to_list s)) 

let array_union (s:'a t array) (i:int) (x:'a t) : unit =
  s.(i) <- union s.(i) x

let array_index (s:bool array) : int t =
  let s2 = ref [] in
  for i = A.size s - 1 downto 0 do 
    if A.getx s i then s2 := i :: !s2 
  done; !s2


(*--- transitive closure *)

let dep_inverse (s:int t array) : int t array =
  let s2 = A.make (A.size s) [] in
  for i = A.size s - 1 downto 0 do
    iter (fun j -> if i<>j then s2.(j) <- i :: s2.(j)) (A.getx s i)
  done; s2

(* highly optimized. s is reflexive but dep is not. *)
let rec closure_iter (s:int t array) (dep:int t array) : int t -> unit = function
  | [] -> ()
  | i::s2 ->
    let prev = A.getx s i in
    let next = imapc (A.getx s) prev in
    if prev=next then closure_iter s dep s2
    else (A.setx s i next; closure_iter s dep (iunion s2 (A.getx dep i)))

let closure (s:int t array) : unit =
  let n = A.size s in
  for i = 0 to n-1 do array_add s i i done; (* reflexive *)
  closure_iter s (dep_inverse s) (interval 0 (n-1))


(*---- *)

let rec find (f:'a -> bool) : 'a list -> 'a option = function
  | [] -> None
  | x::xs -> if f x then Some x else find f xs

let restrict1 (a:'a) (s:('a * 'b) list) : 'b list =
  let f (a2,b) = if a=a2 then Some b else None in
  collect f s

let restrict2 (b:'b) (s:('a * 'b) list) : 'a list =
  let f (a,b2) = if b=b2 then Some a else None in
  collect f s

let intersect (s1:'a list) (s2:'a list) : 'a list =
  take (fun x -> mem x s2) s1

let disjoint (s1:'a list) (s2:'a list) : bool =
  is_empty (intersect s1 s2)
