(* hashq.ml - hash tables with quick equality *)

open Std
module A = Arrayx
module L = Listx
module X = Setx


(* The first part is copied from $OCAML/hashtbl.ml. *)

let hash = Compat.hash
let eq x y = (x = y)

(* We do dynamic hashing, and resize the table and rehash the elements
   when buckets become too long. *)

type ('a, 'b) t =
  { mutable size: int;                        (* number of elements *)
    mutable data: ('a, 'b) bucketlist array } (* the buckets *)

and ('a, 'b) bucketlist =
    Empty
  | Cons of 'a * 'b * ('a, 'b) bucketlist

let create initial_size =
  let s = min (max 1 initial_size) Compat.max_array_length in
  { size = 0; data = Array.make s Empty }

let clear h =
  for i = 0 to Array.length h.data - 1 do
    h.data.(i) <- Empty
  done;
  h.size <- 0

let copy h =
  { size = h.size;
    data = Array.copy h.data }

let length h = h.size

let resize hashfun tbl =
  let odata = tbl.data in
  let osize = Array.length odata in
  let nsize = min (2 * osize + 1) Compat.max_array_length in
  if nsize <> osize then begin
    let ndata = Array.create nsize Empty in
    let rec insert_bucket = function
        Empty -> ()
      | Cons(key, data, rest) ->
          insert_bucket rest; (* preserve original order of elements *)
          let nidx = (hashfun key) mod nsize in
          ndata.(nidx) <- Cons(key, data, ndata.(nidx)) in
    for i = 0 to osize - 1 do
      insert_bucket odata.(i)
    done;
    tbl.data <- ndata;
  end

let add h key info =
  let i = (hash key) mod (Array.length h.data) in
  let bucket = Cons(key, info, h.data.(i)) in
  h.data.(i) <- bucket;
  h.size <- succ h.size;
  if h.size > (Array.length h.data lsl 1) then resize hash h

let remove h key =
  let rec remove_bucket = function
      Empty ->
        Empty
    | Cons(k, i, next) ->
        if eq k key
        then begin h.size <- pred h.size; next end
        else Cons(k, i, remove_bucket next) in
  let i = (hash key) mod (Array.length h.data) in
  h.data.(i) <- remove_bucket h.data.(i)

let rec find_rec key = function
    Empty -> raise Not_found 
  | Cons(k, d, rest) ->
      if eq key k then d else find_rec key rest

let get h key =
  match h.data.((hash key) mod (Array.length h.data)) with
    Empty -> raise Not_found
  | Cons(k1, d1, rest1) ->
      if eq key k1 then d1 else
      match rest1 with
        Empty -> raise Not_found
      | Cons(k2, d2, rest2) ->
          if eq key k2 then d2 else
          match rest2 with
            Empty -> raise Not_found
          | Cons(k3, d3, rest3) ->
              if eq key k3 then d3 else find_rec key rest3

let find_all h key =
  let rec find_in_bucket = function
    Empty ->
      []
  | Cons(k, d, rest) ->
      if eq k key
      then d :: find_in_bucket rest
      else find_in_bucket rest in
  find_in_bucket h.data.((hash key) mod (Array.length h.data))

let replace h key info =
  let rec replace_bucket = function
      Empty ->
        raise Not_found
    | Cons(k, i, next) ->
        if eq k key
        then Cons(k, info, next)
        else Cons(k, i, replace_bucket next) in
  let i = (hash key) mod (Array.length h.data) in
  let l = h.data.(i) in
  try
    h.data.(i) <- replace_bucket l
  with Not_found ->
    h.data.(i) <- Cons(key, info, l);
    h.size <- succ h.size;
    if h.size > (Array.length h.data lsl 1) then resize hash h

let mem h key =
  let rec mem_in_bucket = function
  | Empty ->
      false
  | Cons(k, d, rest) ->
      eq k key || mem_in_bucket rest in
  mem_in_bucket h.data.((hash key) mod (Array.length h.data))

let iter f h =
  let rec do_bucket = function
      Empty ->
        ()
    | Cons(k, d, rest) ->
        f (k,d); do_bucket rest in
  let d = h.data in
  for i = 0 to Array.length d - 1 do
    do_bucket d.(i)
  done

let fold f h init =
  let rec do_bucket b accu =
    match b with
      Empty ->
        accu
    | Cons(k, d, rest) ->
        do_bucket rest (f k d accu) in
  let d = h.data in
  let accu = ref init in
  for i = 0 to Array.length d - 1 do
    accu := do_bucket d.(i) !accu
  done;
  !accu


(**** Extensions *)

(* Optimal size of table for n number of elements? *)
let make (n:int) = create (2*n + 3)

let find (s:('a,'b) t) (x:'a) : 'b option = 
  try Some (get s x) with Not_found -> None

let get_bool (s:('a,bool) t) (x:'a) : bool =
  try get s x with Not_found -> false

let get_set (s:('a,'b X.t) t) (x:'a) : 'b X.t = 
  try get s x with Not_found -> X.empty

let get_list (s:('a,'b list) t) (x:'a) : 'b list = 
  try get s x with Not_found -> []

let to_list (s:('a,'b) t) : ('a * 'b) list = fold (fun x y l -> (x,y)::l) s [] 
let to_list_set (s:('a,'b X.t) t) : ('a * 'b list) list = 
  fold (fun x y l -> (x, X.to_list y)::l) s [] 
let to_list_list (s:('a,'b list) t) : ('a * 'b) list = 
  fold (fun x ys l -> L.map (fun y -> (x,y)) ys @ l) s [] 
let to_set (s:('a,'b) t) : ('a * 'b) X.t = X.of_list (to_list s)

let of_list (s:('a * 'b) list) : ('a,'b) t = 
  let h = make (L.size s) in
  L.iter (fun (x,y) -> add h x y) s; h

let of_set (s:('a * 'b) X.t) : ('a,'b) t = 
  let h = make (X.size s) in
  X.iter (fun (x,y) -> add h x y) s; h

let map_list (f:'a * 'b -> 'c) (s:('a,'b) t) : 'c list = L.map f (to_list s)
let map_set (f:'a * 'b -> 'c) (s:('a,'b) t) : 'c X.t = X.map f (to_set s)
let mapc_list (f:'a * 'b -> 'c list) (s:('a,'b) t) : 'c list = L.mapc f (to_list s)
let mapc_set (f:'a * 'b -> 'c X.t) (s:('a,'b) t) : 'c X.t = X.mapc f (to_set s)

let mapc_rev_list (f:'a * 'b -> 'c list) (s:('a,'b) t) : 'c list = 
  L.mapc_rev f (to_list s)

let map (f:'a * 'b -> 'c * 'd) (s:('a,'b) t) : ('c,'d) t = 
  of_list (L.map f (to_list s))

let map2 (f1:'a1 -> 'a3) (f2:'a2 -> 'a4) (s:('a1,'a2) t) : ('a3,'a4) t = 
  let f (a1,a2) = (f1 a1, f2 a2) in
  of_list (L.map f (to_list s))


let preimage (s:('a,'b) t) : 'a list = fold (fun x _ l -> x::l) s []
let image (s:('a,'b) t) : 'a list = fold (fun _ y l -> y::l) s []

let rec bucket_size = function
  | Empty -> 0
  | Cons (_,_,s) -> 1 + (bucket_size s)

let rec take_bucketlist (f:'a * 'b -> bool) 
  (accum:('a,'b) bucketlist) (s:('a,'b) bucketlist) : ('a,'b) bucketlist =
  match s with
  | Empty -> accum
  | Cons (a,b,s2) when f (a,b) -> take_bucketlist f (Cons (a,b,accum)) s2
  | Cons (_,_,s2) -> take_bucketlist f accum s2

let take (f:'a * 'b -> bool) (s:('a,'b) t) : ('a,'b) t =
  { data = Arrayx.map (take_bucketlist f Empty) s.data;
    size = Arrayx.sum (Arrayx.map bucket_size s.data) }

let update (f:'a * 'b -> 'b) (h:('a,'b) t) : unit =
  let rec do_bucket = function
      Empty ->
        Empty
    | Cons(k, d, rest) ->
        Cons(k, f (k,d), do_bucket rest) in
  let d = h.data in
  for i = 0 to Array.length d - 1 do
    d.(i) <- do_bucket d.(i)
  done


let size = length
let set = replace
let del = remove

(* instead of shadowing a previous binding, add the item to the
list/set of the previous binding. *)

let add_set (s:('a,'b X.t) t) (a:'a) (b:'b) =
  replace s a (X.add b (get_set s a))

let add_list (s:('a,'b list) t) (a:'a) (b:'b) =
  replace s a (b :: get_list s a)

let union (s:('a,'b X.t) t) (a:'a) (bs:'b X.t) =
  replace s a (X.union bs (get_set s a))

(* for duplicate bindings, collect them together as a list/set instead of shadowing *)

let of_list_set (l:('a * 'b) list) : ('a,'b X.t) t = 
  let h = create (2 * (L.size l) + 1) in
  L.iter (fun (x,y) -> add_set h x y) l; h

let of_list_list (l:('a * 'b) list) : ('a,'b list) t = 
  let h = create (2 * (L.size l) + 1) in
  L.iter (fun (x,y) -> add_list h x y) l; h

let all (f:'a * 'b -> bool) (s:('a,'b) t) : bool = L.all f (to_list s)

let domain_list (s:('a,'b) t) : 'a list = L.map fst (to_list s)
let range_list (s:('a,'b) t) : 'b list = L.map snd (to_list s)
let domain (s:('a,'b) t) : 'a X.t = X.of_list (domain_list s)
let range (s:('a,'b) t) : 'b X.t = X.of_list (range_list s)

let empty () : ('a,'b) t = create 0

let inverse (s:('a,'b) t) : ('b,'a) t = 
  let f (a,b) = (b,a) in
  of_list (L.map f (to_list s))

let inverse_set (s:('a,'b X.t) t) : ('b,'a X.t) t =
  let f (a,bs) = X.map_list (fun b -> (b,a)) bs in
  of_list_set (L.mapc f (to_list s))  


let make_set (domain:'a X.t) : ('a,'b X.t) t =
  let s = make (X.size domain) in
  X.iter (fun a -> add s a X.empty) domain; s

(*------------------------------------------------------------

  Reflexive-transitive closure.

  Warshall algorithm is O(n^3). But we use worklist here.

http://www2.toki.or.id/book/AlgDesignManual/BOOK/BOOK4/NODE163.HTM

TODO: use depth-first search with caching.  

--------------------------------------------------------------*)

(* transitive closure *)
let closure_iterate (edges:('a,'a X.t) t) (inv:('a,'a X.t) t) (n:'a) =
  let ns1 = get_set edges n in
  let ns = X.mapc (get_set edges) ns1 in
  let ns2 = X.union ns1 ns in
  if ns1=ns2 then X.empty else 
  (set edges n ns2; X.del n (get_set inv n))

let closure (edges:('a,'a X.t) t) : ('a,'a X.t) t =
  let inv = inverse_set edges in
  iter (fun (a,_) -> add_set edges a a) edges; (* reflexive *)
  X.worklist (closure_iterate edges inv) (domain edges); edges


(* finit = initializer, and fdep = dependency *)
let fixpoint (az:'a X.t) (finit:('a,'b X.t) t -> unit)
  (fdep:('a,'a X.t) t -> unit) : ('a,'b X.t) t =
  let init = make (X.size az) in
  let dep = make_set az in
  let fp = make (X.size az) in
  finit init; fdep dep;
  iter (fun (a,az) -> set fp a (X.mapc (get_set init) az)) (closure dep);
  fp


(* optimize *)
let collect (f:'a * 'b -> 'c option) (s:('a,'b) t) : 'c list
  = L.collect f (to_list s)

(* optimize *)
let collect_set (f:'a * 'b -> 'c option) (s:('a,'b) t) : 'c X.t
  = X.collect f (to_set s)


(*---- Show and print. *)
 
let show (sep:string) (f1:'a1 -> string) (f2:'a2 -> string) (s:('a1,'a2) t) : string = 
  let f (a1,a2) = f1 a1 ^ " -> " ^ f2 a2 in
  L.show sep f (to_list s)

let print (sep:string) (f1:'a1 -> unit) (f2:'a2 -> unit) (s:('a1,'a2) t) : unit = 
  let f (a1,a2) = f1 a1; Std.print sep; f2 a2 in
  L.print sep f (to_list s)

let iter2 (f1:'a1 -> unit) (f2:'a2 -> unit) (s:('a1,'a2) t) : unit = 
  let f (a1,a2) = f1 a1; f2 a2 in
  iter f s

let show_set (sep:string) (f1:'a -> string) (f2:'b -> string)
  (s:('a,'b X.t) t) : string = 
  let f (a,bs) = f1 a ^ " -> {" ^ X.show ", " f2 bs ^ "}" in
  L.show sep f (to_list s)

let showz f1 f2 (s:('a1,'a2) t) = show " " f1 f2 s
let show0 f1 f2 (s:('a1,'a2) t) = show "" f1 f2 s
let show1 f1 f2 (s:('a1,'a2) t) = show "\n" f1 f2 s
let show2 f1 f2 (s:('a1,'a2) t) = show "\n\n" f1 f2 s

let showx sep (s:('a1,'a2) t) = show sep Std.show Std.show s
let showxz (s:('a1,'a2) t) = showx " " s
let showx0 (s:('a1,'a2) t) = showx "" s
let showx1 (s:('a1,'a2) t) = showx "\n" s
let showx2 (s:('a1,'a2) t) = showx "\n\n" s

let printz f1 f2 (s:('a1,'a2) t) = print " " f1 f2 s 
let print0 f1 f2 (s:('a1,'a2) t) = iter2 f1 f2 s
let print1 f1 f2 (s:('a1,'a2) t) = print "\n" f1 f2 s
let print2 f1 f2 s  = print "\n\n" f1 f2 s

let printx sep = print sep Std.printx Std.printx
let printxz (s:('a1,'a2) t) = printx " " s
let printx0 (s:('a1,'a2) t) = printx "" s
let printx1 (s:('a1,'a2) t) = printx "\n" s 
let printx2 (s:('a1,'a2) t) = printx "\n\n" s


(*---- *)

(* A indexing function: given an element of a list/set, return its integer index. *)

let index (s:'a list) : 'a -> int = 
  let s = of_list (L.rindex s) in get s

let index_set (s:'a X.t) : 'a -> int = 
  let s = of_set (X.rindex s) in get s

let index_array (s:'a array) : 'a -> int = index (A.to_list s)

let rindex_set (s:'a X.t) : int -> 'a = 
  let s2 = X.to_array s in fun i -> s2.(i)

let index2_set (s:'a X.t) : ('a -> int) * (int -> 'a) = 
  (index_set s, rindex_set s)

let restrict1 (a1:'a1) (s:('a1 * 'a2, 'b) t) : ('a2, 'b) t =
  let f ((a3,a2),b) = if a1=a3 then Some (a2,b) else None in
  of_list (L.collect f (to_list s))

let restrict2 (a2:'a2) (s:('a1 * 'a2, 'b) t) : ('a1, 'b) t =
  let f ((a1,a3),b) = if a2=a3 then Some (a1,b) else None in
  of_list (L.collect f (to_list s))

let equal (s1:('a,'b) t) (s2:('a,'b) t) : bool =
  (to_set s1) = (to_set s2)

let compose (s1:('a,'b) t) (s2:('a,'b) t) : ('a,'b) t =
  of_list (to_list s1 @ to_list s2)

let of_array (s:('a * 'b) array) : ('a,'b) t = of_list (A.to_list s)
let to_array (s:('a,'b) t) : ('a * 'b) array = A.of_list (to_list s)

let list_add (s1:('a,'b) t) (s2:('a * 'b) list) : unit = 
  L.iter (fun (a,b) -> add s1 a b) s2

let fprint (g1:out_channel -> 'a1 -> unit) (g2:out_channel -> 'a2 -> unit)
  (f:out_channel) (s:('a1,'a2) t) : unit =
  Std.fprint f "(\n"; 
  iter (fun (a1,a2) -> fprintf f "%a -> %a\n" g1 a1 g2 a2) s;
  Std.fprint f ")"

let fcode (g1:out_channel -> 'a1 -> unit) (g2:out_channel -> 'a2 -> unit)
  (f:out_channel) (s:('a1,'a2) t) : unit =
  Std.fprint f "Hashx.of_array [|\n"; 
  iter (fun (a1,a2) -> fprintf f "(%a, %a);\n" g1 a1 g2 a2) s;
  Std.fprint f "|]"

(* TODO: optimize *)
let head (s:('a,'b) t) : 'a * 'b = L.head (to_list s)

(* given a reverse integer lookup hash table ('a,int) t, return an
array with elements filled in according to the integer mapping. *)
let to_index_array (h:('a, int) t) : 'a array =
  let s = if size h = 0 then [||] else A.make (size h) (fst (head h)) in
  iter (fun (a,i) -> s.(i) <- a) h; s

let is_empty (s:('a,'b) t) : bool = size s = 0

