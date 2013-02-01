(* mapx.ml - finite map (extended) *)

(* Just like setx.ml, this module is an extension of the map.ml in the
ocaml distribution, but restricted to datatypes whose equality is
defined with the standard comparison 'Pervasives.compare'. 

Difference with $OCAML/map.ml:

- no module strucutre
- use Pervasives.compare instead of OrderedType.compare
- parameterize the main map type 't' and the enumeration type 'enumeration' 
  with an additional type parameter 'k for key type

*)

module L = Listx
module X = Setx

let cmp x y = Pervasives.compare x y

    type ('k, 'a) t =
        Empty
      | Node of ('k,'a) t * 'k * 'a * ('k,'a) t * int

    let height = function
        Empty -> 0
      | Node(_,_,_,_,h) -> h

    let create l x d r =
      let hl = height l and hr = height r in
      Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

    let bal l x d r =
      let hl = match l with Empty -> 0 | Node(_,_,_,_,h) -> h in
      let hr = match r with Empty -> 0 | Node(_,_,_,_,h) -> h in
      if hl > hr + 2 then begin
        match l with
          Empty -> invalid_arg "Map.bal"
        | Node(ll, lv, ld, lr, _) ->
            if height ll >= height lr then
              create ll lv ld (create lr x d r)
            else begin
              match lr with
                Empty -> invalid_arg "Map.bal"
              | Node(lrl, lrv, lrd, lrr, _)->
                  create (create ll lv ld lrl) lrv lrd (create lrr x d r)
            end
      end else if hr > hl + 2 then begin
        match r with
          Empty -> invalid_arg "Map.bal"
        | Node(rl, rv, rd, rr, _) ->
            if height rr >= height rl then
              create (create l x d rl) rv rd rr
            else begin
              match rl with
                Empty -> invalid_arg "Map.bal"
              | Node(rll, rlv, rld, rlr, _) ->
                  create (create l x d rll) rlv rld (create rlr rv rd rr)
            end
      end else
        Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

    let empty = Empty

    let is_empty = function Empty -> true | _ -> false

    let rec add x data = function
        Empty ->
          Node(Empty, x, data, Empty, 1)
      | Node(l, v, d, r, h) ->
          let c = Pervasives.compare x v in
          if c = 0 then
            Node(l, x, data, r, h)
          else if c < 0 then
            bal (add x data l) v d r
          else
            bal l v d (add x data r)

    let rec get x = function
        Empty ->
          raise Not_found
      | Node(l, v, d, r, _) ->
          let c = Pervasives.compare x v in
          if c = 0 then d
          else get x (if c < 0 then l else r)

    let rec find x = function
        Empty -> None          
      | Node(l, v, d, r, _) ->
          let c = Pervasives.compare x v in
          if c = 0 then Some d
          else find x (if c < 0 then l else r)

    let rec mem x = function
        Empty ->
          false
      | Node(l, v, d, r, _) ->
          let c = Pervasives.compare x v in
          c = 0 || mem x (if c < 0 then l else r)

    let rec min_binding = function
        Empty -> raise Not_found
      | Node(Empty, x, d, r, _) -> (x, d)
      | Node(l, x, d, r, _) -> min_binding l

    let rec remove_min_binding = function
        Empty -> invalid_arg "Map.remove_min_elt"
      | Node(Empty, x, d, r, _) -> r
      | Node(l, x, d, r, _) -> bal (remove_min_binding l) x d r

    let merge t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          bal t1 x d (remove_min_binding t2)

    let rec remove x = function
        Empty ->
          Empty
      | Node(l, v, d, r, h) ->
          let c = Pervasives.compare x v in
          if c = 0 then
            merge l r
          else if c < 0 then
            bal (remove x l) v d r
          else
            bal l v d (remove x r)

    let rec iter f = function
        Empty -> ()
      | Node(l, v, d, r, _) ->
          iter f l; f v d; iter f r

    let rec map f = function
        Empty               -> Empty
      | Node(l, v, d, r, h) -> Node(map f l, v, f d, map f r, h)

    let rec mapi f = function
        Empty               -> Empty
      | Node(l, v, d, r, h) -> Node(mapi f l, v, f v d, mapi f r, h)

    let rec fold f m accu =
      match m with
        Empty -> accu
      | Node(l, v, d, r, _) ->
          fold f l (f v d (fold f r accu))

    type ('k,'a) enumeration = End | More of 'k * 'a * ('k,'a) t * ('k,'a) enumeration

    let rec cons_enum m e =
      match m with
        Empty -> e
      | Node(l, v, d, r, _) -> cons_enum l (More(v, d, r, e))

    let compare cmp m1 m2 =
      let rec compare_aux e1 e2 =
          match (e1, e2) with
          (End, End) -> 0
        | (End, _)  -> -1
        | (_, End) -> 1
        | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
            let c = Pervasives.compare v1 v2 in
            if c <> 0 then c else
            let c = cmp d1 d2 in
            if c <> 0 then c else
            compare_aux (cons_enum r1 e1) (cons_enum r2 e2)
      in compare_aux (cons_enum m1 End) (cons_enum m2 End)

    let equal cmp m1 m2 =
      let rec equal_aux e1 e2 =
          match (e1, e2) with
          (End, End) -> true
        | (End, _)  -> false
        | (_, End) -> false
        | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
            Pervasives.compare v1 v2 = 0 && cmp d1 d2 &&
            equal_aux (cons_enum r1 e1) (cons_enum r2 e2)
      in equal_aux (cons_enum m1 End) (cons_enum m2 End)


(*---- Additional functions. *)

let to_list (s:('a,'b) t) : ('a * 'b) list = 
  fold (fun a b s2 -> (a,b) :: s2) s []

let size (s:('a,'b) t) : int = Listx.size (to_list s)

let of_list (s:('a * 'b) list) : ('a,'b) t =
  Listx.foldl (fun m (a,b) -> add a b m) empty s

let get_list (s:('a,'b list) t) (x:'a) : 'b list = 
  try get x s with Not_found -> []

let get_set (s:('a,'b X.t) t) (x:'a) : 'b X.t = 
  try get x s with Not_found -> X.empty

let replace (s:('a,'b) t) (a:'a) (b:'b) =
  mapi (fun a2 b2 -> if a=a2 then b else b2) s

let add_set (s:('a,'b X.t) t) (a:'a) (b:'b) =
  replace s a (X.add b (get_set s a))

let add_list (s:('a,'b list) t) (a:'a) (b:'b) =
  replace s a (b :: get_list s a)


(* for duplicate bindings, collect them together as a list/set instead of shadowing *)

let of_list_set (s:('a * 'b) list) : ('a,'b Setx.t) t = 
  Listx.foldl (fun m (a,b) -> add_set m a b) empty s

let of_list_list (s:('a * 'b) list) : ('a,'b list) t = 
  Listx.foldl (fun m (a,b) -> add_list m a b) empty s


(*--- Show and print. *)

let show (sep:string) (f1:'a1 -> string) (f2:'a2 -> string) (s:('a1,'a2) t) : string = 
  let f (a1,a2) = f1 a1 ^ " -> " ^ f2 a2 in
  L.show sep f (to_list s)

let print (sep:string) (f1:'a1 -> unit) (f2:'a2 -> unit) (s:('a1,'a2) t) : unit = 
  let f (a1,a2) = f1 a1; Std.print sep; f2 a2 in
  L.print sep f (to_list s)

let show_set (sep:string) (f1:'a -> string) (f2:'b -> string) (s:('a,'b X.t) t) : string = 
  let f (a,bs) = f1 a ^ " -> {" ^ X.show ", " f2 bs ^ "}" in
  L.show sep f (to_list s)

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

(*--- .*)

let list_add (s1:('a,'b) t) (s2:('a * 'b) list) : ('a,'b) t =
  Listx.foldl (fun m (a,b) -> add a b m) s1 s2

let mapc_rev_list (f:'a * 'b -> 'c list) (s:('a,'b) t) : 'c list = 
  L.mapc_rev f (to_list s)

let head (s:('a,'b) t) : 'a * 'b = L.head (to_list s)

let domain_list (s:('a,'b) t) : 'a list = L.map fst (to_list s)
let range_list (s:('a,'b) t) : 'b list = L.map snd (to_list s)
let domain (s:('a,'b) t) : 'a X.t = X.of_list (domain_list s)
let range (s:('a,'b) t) : 'b X.t = X.of_list (range_list s)
