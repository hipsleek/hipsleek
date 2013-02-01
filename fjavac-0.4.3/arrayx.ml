(* arrayx.ml - array (extended) *)

(*
statistics: max, min, count


suffix: 

x    - unsafe bound
i    - indexed predicate
j    - indexed result
n    - counted result
2    - binary input
by   - predicated
from - offset

*)

open Std
module L = Listx

let make: int -> 'a -> 'a array = Array.make
let size : 'a array -> int = Array.length
let get : 'a array -> int -> 'a = Array.get
let set : 'a array -> int -> 'a -> unit = Array.set

(* Assumption: 0 <= offset < size a. *)
let getx : 'a array -> int -> 'a = Compat.array_unsafe_get

(* Assumption: 0 <= offset < size a. *)
let setx : 'a array -> int -> 'a -> unit = Compat.array_unsafe_set

let checkn (f:string) (a:'a array) (count:int) : unit =
  if not (count <= size a) then 
    fail "Arrayx.%s: count < size: %d" f count (size a)

let checki (f:string) (a:'a array) (offset:int) : unit =
  if not (0 <= offset && offset < size a) then 
    fail "Arrayx.%s: 0 <= offset < size: %d, %d" f offset (size a)

let check (caller:string) (a:'a array) (offset:int) (count:int) : unit =
  if not (0 <= offset && offset <= size a - count) then 
    fail "Arrayx.%s: 0 <= offset <= size - count: %d, %d, %d"
      caller offset (size a) count

(* Assumption: 0 <= offset1 < size a1 && 0 <= offset2 < size a2. *)
let copyx (a1:'a array) (offset1:int) (a2:'a array) (offset2:int) 
  (count:int) : unit =
  let f i = setx a2 (offset2+i) (getx a1 (offset1+i)) in
  if offset1 < offset2 then
    for i = count-1 downto 0 do f i done
  else
    for i = 0 to count-1 do f i done

let copy (a1:'a array) (offset1:int) (a2:'a array) (offset2:int) 
  (count:int) : unit =
  check "copy" a1 offset1 count;  
  check "copy" a2 offset2 count;
  copyx a1 offset1 a2 offset2 count

(* Assumption: 0 <= offset < size a - count *)
let fillx (a:'a array) (offset:int) (count:int) (x:'a) : unit =
  for i = offset to count-offset do setx a i x done

let fill (a:'a array) (offset:int) (count:int) (x:'a) : unit =
  check "fill" a offset count;
  fillx a offset count x

(* Assumption: 0 <= offset <= size a - count. *)
let subx (a:'a array) (offset:int) (count:int) : 'a array =
  if count = 0 then [||] else
  let a2 = make count (getx a offset) in
  copyx a offset a2 0 count; a2

let sub (a:'a array) (offset:int) (count:int) : 'a array =
  check "sub" a offset count;
  subx a offset count

let suby (a:'a array) (offset:int) (count:int) : 'a array =
  let i = cram offset 0 (size a) in
  let n = cram count 0 (size a - i) in
  subx a i n

let dup (a:'a array) : 'a array = subx a 0 (size a)

(* Assumption: size a >= 1 *)
let headx (a:'a array) : 'a = getx a 0

(* Assumption: size a >= 1 *)
let tailx (a:'a array) : 'a array = subx a 1 (size a - 1)

(* Assumption: size a >= 1 *)
let lastx (a:'a array) : 'a = getx a (size a - 1)

let head (a:'a array) : 'a = checkn "head" a 1; headx a
let tail (a:'a array) : 'a array = checkn "tail" a 1; tailx a
let last (a:'a array) : 'a = checkn "last" a 1; getx a (size a - 1)

let mapin (f:int -> 'a -> 'b) (count:int) (a:'a array) : 'b array =
  let n = size a in
  if n = 0 then [||] else
  let a2 = make n (f 0 (getx a 0)) in
  for i=1 to min count (n-1) do 
    setx a2 i (f i (getx a i))
  done; a2

let iterin (f:int -> 'a -> unit) (count:int) (a:'a array) : unit =
  let n = min count (size a) in
  for i=0 to n-1 do f i (getx a i) done

let mapn (f:'a -> 'b) (count:int) (a:'a array) : 'b array =
  mapin (lift f) count a

let itern (f:'a -> unit) (count:int) (a:'a array) : unit =
  iterin (lift f) count a

let mapi (f:int -> 'a -> 'b) (a:'a array) : 'b array = mapin f (size a) a
let iteri (f:int -> 'a -> unit) (a:'a array) : unit = iterin f (size a) a
let map (f:'a -> 'b) (a:'a array) : 'b array = mapn f (size a) a

let iter (f:'a -> unit) (a:'a array) : unit = itern f (size a)  a

let iter_last (f1:'a -> unit) (f2:'a -> unit) (a:'a array) : unit = 
  let n = size a - 1 in itern f1 n a; f2 (getx a n)

let rev (a:'a array) : 'a array =
  let a2 = dup a in
  for i=0 to size a do 
    setx a2 (size a - i - 1) (getx a i)
  done; a2

let cat_list (l:'a array list) : 'a array =
  let n = Listx.sum (Listx.map size l) in
  if n = 0 then [||] else
  let a2 = make n (headx (Listx.head l)) in
  let f i s = copyx s 0 a2 i (size s); i+size s in
  ignore (Listx.foldl f 0 l); a2

let cat2 (s1:'a array) (s2:'a array) : 'a array =
  let (n1,n2) = (size s1, size s2) in
  if n1+n2 = 0 then [||] else
  let s = make (n1+n2) (headx s1) in
  copyx s1 0 s 0 n1; copyx s2 0 s n1 n2; s

let is_prefix (s1:'a array) (a2:'a array) : bool = (s1 = (suby a2 0 (size s1)))

let rec is_subset_from (s1:'a array) (a2:'a array) (offset:int) : bool =
  size s1 <= size a2 - offset
  && (s1 = (suby a2 offset (size s1)) || is_subset_from s1 a2 (offset+1))

let is_subset (s1:'a array) (a2:'a array) : bool = is_subset_from s1 a2 0

(* Internal: 0 <= offset < size a *)
let rec set_list_from (a:'a array) (offset:int) : 'a list -> unit = function
  | [] -> ()
  | x::xs -> setx a offset x; set_list_from a (offset+1) xs

let of_list (l:'a list) : 'a array =
  let n = Listx.size l in
  if n = 0 then [||] else
  let a = make n (Listx.head l) in
  set_list_from a 0 l; a

(* Internal: 0 <= offset *)
let rec to_list_from (a:'a array) (offset:int) : 'a list =
  if offset >= size a then []
  else getx a offset :: to_list_from a (offset+1)

let to_list (a:'a array) : 'a list = to_list_from a 0

let cat (s:'a list array) : 'a array = of_list (L.cat (to_list s))

let mapic (f:int -> 'a -> 'b list) (s:'a array) : 'b array = cat (mapi f s)

let foldl (f:'a -> 'b -> 'a) (acc:'a) (a:'b array) : 'a =
  let x = ref acc in
  for i = 0 to size a - 1 do
    x := f !x (getx a i)
  done; !x

let foldr (f:'a -> 'b -> 'b) (acc:'b) (a:'a array) : 'b =
  let x = ref acc in
  for i = 0 to size a - 1 do
    x := f (getx a i) !x
  done; !x

let foldl2 (f:'a -> 'b -> 'c -> 'a) (acc:'a) 
    (a1:'b array) (a2:'c array) : 'a =
  let x = ref acc in
  let n = min (size a1 - 1) (size a2 - 1) in
  for i = 0 to n do x := f !x (getx a1 i) (getx a2 i) done; !x

let foldr2 (f:'a -> 'b -> 'c -> 'a) (acc:'c) 
    (a1:'a array) (a2:'b array) : 'a =
  let x = ref acc in
  let n = min (size a1 - 1) (size a2 - 1) in
  for i = 0 to n do x := f (getx a1 i) (getx a2 i) !x done; !x

let iter2 (f:'a -> 'b -> unit) : 'a array -> 'b array -> unit
  = foldr2 (fun x y acc -> f x y) ()

(* Assumption: 0 <= offset. *)
let rec all_fromx (f:'a -> bool) (a:'a array) (offset:int) : bool = 
  offset >= size a || (f (getx a offset) && all_fromx f a (offset+1))

(* Assumption: 0 <= offset. *)
let rec some_fromx (f:'a -> bool) (a:'a array) (offset:int) : bool = 
  offset < size a && (f (getx a offset) || some_fromx f a (offset+1))

let all (f:'a -> bool) (a:'a array) : bool = all_fromx f a 0
let some (f:'a -> bool) (a:'a array) : bool = some_fromx f a 0

(* Assumption: 0 <= offset. *)
let rec all2_fromx (f:'a -> 'b -> bool) (a1:'a array) (a2:'b array) 
  (offset1:int) (offset2:int) : bool = 
  offset1 >= size a1 || offset2 >= size a2 || 
  (f (getx a1 offset1) (getx a2 offset2)
     && all2_fromx f a1 a2 (offset1+1) (offset2+1))

(* Assumption: 0 <= offset. *)
let rec some2_fromx (f:'a -> 'b -> bool) (a1:'a array) (a2:'b array) 
  (offset1:int) (offset2:int) : bool = 
  offset1 < size a1 && offset2 < size a2 && 
  (f (getx a1 offset1) (getx a2 offset2)
     || some2_fromx f a1 a2 (offset1+1) (offset2+1))

let all2 (f:'a -> 'b -> bool) (a1:'a array) (a2:'b array) = 
  all2_fromx f a1 a2 0 0
let some2 (f:'a -> 'b -> bool) (a1:'a array) (a2:'b array) = 
  some2_fromx f a1 a2 0 0

(* Assumption: 0 <= offset. *)
let rec findij_from (f:int -> 'a -> bool) (a:'a array) (offset:int) 
  : (int * 'a) option =
  if offset >= size a then None else
  let x = getx a offset in
  if f offset x then Some (offset,x) else findij_from f a (offset+1)

let findi_from (f:int -> 'a -> bool) (a:'a array) (offset:int) : 'a option = 
  opt_map snd (findij_from f a offset)

let findj_from (f:'a -> bool) (a:'a array) (offset:int) : (int * 'a) option = 
  findij_from (lift f) a offset

let findi (f:int -> 'a -> bool) (a:'a array) : 'a option = findi_from f a 0
let findj (f:'a -> bool) (a:'a array) : (int * 'a) option = findj_from f a 0
let find (f:'a -> bool) (a:'a array) : 'a option = findi_from (lift f) a 0

let findx (f:'a -> bool) (a:'a array) : 'a = opt_get (find f a)

let mem (x:'a) (a:'a array) : bool = find ((=) x) a <> None
let memq (x:'a) (a:'a array) : bool = find ((==) x) a <> None

let assoc_by (f:'a -> bool) (a:('a * 'b) array) : 'b option =
  opt_map fst (find (fun (x,_) -> f x) a)

let rassoc_by (f:'b -> bool) (a:('a * 'b) array) : 'a option =
  opt_map fst (find (fun (_,y) -> f y) a)

let assoc x = assoc_by ((=) x)
let assocq x = assoc_by ((==) x)
let rassoc x = rassoc_by ((=) x)
let rassocq x = rassoc_by ((==) x)

(* Assumption: 0 <= offset. *)
let rec taken_fromx (f:'a -> bool) (a:'a array) (offset:int) (count:int)
  : 'a list =
  if count <= 0 || offset >= size a then [] else
  let x = getx a offset in
  let g = taken_fromx f a (offset+1) in
  if f x then x :: g (count-1) else g count

let taken f a count = taken_fromx f a 0 count
let take f a = taken f a max_int

let taken_index (f:'a -> bool) (a:'a array) : int list =
  let s = ref [] in
  for i = 0 to size a - 1 do
    if f (getx a i) then s := i :: !s
  done; !s

(* Assumption: 0 <= offset. *)
let rec dropn_fromx (f:'a -> bool) (a:'a array) (offset:int) (count:int)
  : 'a list =
  if offset >= size a then [] else
  let x = getx a offset in
  let g = dropn_fromx f a (offset+1) in
  if count>0 && f x then g (count-1) else x :: g count

let dropn f a count = dropn_fromx f a 0 count
let drop f a = dropn f a max_int

let zip (a1:'a array) (a2:'b array) : ('a * 'b) array =
  let n = min (size a1) (size a2) in
  if n = 0 then [||] else
  let a = make n (headx a1, headx a2) in
  for i = 1 to n-1 do
    setx a i (getx a1 i, getx a2 i)
  done; a
  
let unzip (a:('a * 'b) array) : 'a array * 'b array = 
  let n = size a in
  if n = 0 then ([||], [||]) else
  let (x1,x2) = headx a in
  let a1 = make n x1 in
  let a2 = make n x2 in
  for i = 1 to n-1 do
    let (x1,x2) = getx a i in
    setx a1 i x1;
    setx a2 i x2;
  done; (a1,a2)

let sum : int array -> int = foldl ( + ) 0
let prod : int array -> int = foldl ( * ) 0
let max : int array -> int = foldl Pervasives.max 0
let min : int array -> int = foldl Pervasives.min 0

let sort_by : ('a -> 'a -> int) -> 'a array -> unit = Array.sort
let sort (s:'a array) : 'a array = Array.sort Pervasives.compare s; s
let rsort (f:'a -> 'a -> int) : 'a array -> unit = sort_by (neg2 f)


(*---- Show and print. *)

let rec show_from (offset:int) (sep:string) (f:'a -> string)
  (a:'a array) : string = 
  if offset >= size a then ""
  else if offset = size a - 1 then f (getx a offset)
  else f (getx a offset) ^ sep ^ show_from (offset+1) sep f a

let rec print_from (offset:int) (sep:string) (f:'a -> unit)
  (a:'a array) : unit = 
  if offset < size a then
  if offset = size a - 1 then f (getx a offset)
  else f (getx a offset); Std.print sep; print_from (offset+1) sep f a

let show sep f a = show_from 0 sep f a
let print sep f a = print_from 0 sep f a

let showz f s = show " " f s
let show0 f s = show "" f s
let show1 f s = show "\n" f s
let show2 f s = show "\n\n" f s

let showx sep s = show sep Std.show s
let showxz s = showx " " s
let show0x s = showx "" s
let show1x s = showx "\n" s
let show2x s = showx "\n\n" s

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

let makei (n:int) (f:int -> 'a) : 'a array =
  let s = make n (f 0) in
  for i = 1 to n-1 do setx s i (f i) done; s

let rec index_i (i:int) (s:'a array) (a:'a) : int =
  if get s i = a then i else index_i (i+1) s a

let index (s:'a array) : 'a -> int = index_i 0 s

let fprint (g:out_channel -> 'a -> unit)
  (f:out_channel) (s:'a array) : unit =
  fprint f "[|\n"; 
  for i = 0 to size s - 1 do
    fprintf f "(* %02d *) %a;\n" i g (getx s i)
  done;
  fprint f "|]"

let rec interval (i:int) (j:int) : int array = of_list (L.interval i j)

 let izip (s:'a array) : (int * 'a) array = 
  let n = size s in
  if n = 0 then [||] else    
  let s2 = make n (0, getx s 0) in
  for i = 1 to size s - 1 do setx s2 i (i, getx s i) done;  s2

let bool_or (s1:bool array) (s2:bool array) : bool array =
  assert (size s1 = size s2);
  let s = dup s1 in
  for i = 0 to size s - 1 do 
    if getx s2 i then setx s i true
  done; s

let make_matrix (n:int) (m:int) (x:'a) : 'a array array =
  let s = make n [||] in
  for i = 0 to n - 1 do
    setx s i (make m x)
  done; s

let trim (m:int) (n:int) (s:'a array) : 'a array =
  Std.check (m+n <= size s) "trim too many: m+n > size: %d + %d > %d" m n (size s);
  sub s m (size s - m - n)

