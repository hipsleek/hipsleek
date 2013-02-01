(* parse.ml - parse (input tokens to parse stacks) *)

open Std
module C = Cfg
module F = Fa
module P = Pda
module L = Listx
module M = Mapx


(* Graph structured stack 'g'. 

Tomita's GLR algorithm [p.54] does not terminate on hidden right
recursive grammar (including Java). Follow Rekers 1992 instead. The
implementation takes advantage of the assumption that there is at most
one parse tree. It uses 'merge' function to handles parse tree
ambiguity, hence avoid building and sharing parse trees.

w = graph node: state node or symbol node

g = {
  currents -- state vertices created in parsing current token i (U_i)
  actives  -- active state vertices (subset of U_i) to be processed (A)
  reduces  -- paths (w,p) to be reduced (R)
  shifts   -- vertices (w,w) to be shifted on (Q)
}
*)

type 'u w = {
  uid : int;                            (* unique id *)
  state : F.q;
  mutable ddepth : int;                 (* deterministic depth *)
  mutable succs : (int, 'u P.v ref * 'u w ref) M.t;
}  

type 'u g = {
  mutable actives : (F.q, 'u w ref) M.t;
  mutable actions : 'u w ref list;
  mutable shifts : ('u w ref * F.q) list;
}

let make_counter = ref 0

let make (q:F.q) : 'u w ref =
  incr make_counter;
  ref { uid = !make_counter; state = q; ddepth = 0; succs = M.empty }

let rec v_show : 'u P.v -> string = function
  | P.Leaf u -> show u
  | P.Node (i,_,vs)  -> showf "[%d %s]" i (L.showz vr_show vs)

and vr_show (r:'u P.v ref) : string = v_show !r

let rec w_show (w:'u w) : string =   
  showf "(%d,[%s])" w.state (M.showz int_show succ_show w.succs)

and wr_show (r:'u w ref) : string = w_show !r

and succ_show ((tr,w):('u P.v ref * 'u w ref)) : string =
  showf "(%s,%s)" (vr_show tr) (w_show !w)


(*---- Parsing. 

w1 - original node in actives
w2 - |s of w1|-away descendent of w1
w3 - node in actives with state as goto from w2
w4 - node in actives - actions
w5 - |s of w4|-away descendent of w4 through link w2-w3

*)

let report (a:'u P.a) : 'a =
  let (z,t,q) = L.head a.P.errors in
  printf "\n%s: Parse error: found '%s' but expecting\n( %s\n)\n" 
    z a.P.ts.(t) (L.show "\n  " (P.tm_show a) a.P.qs.(q));
  exit (-1)

let connect (w1:'u w ref) (r:'u P.v ref) (w2:'u w ref) : unit = 
  (!w1).ddepth <- if M.is_empty (!w1).succs then (!w2).ddepth + 1 else 0;
  (!w1).succs <- M.add (!w2).uid (r,w2) (!w1).succs 

exception Invalid                       (* invalid parse tree *)

let merge (a:'u P.a) (z:P.info) (v1:'u P.v) (v2:'u P.v) : 'u P.v =
  let tshow = opt_get a.P.show in
  let filter x = try (opt_get a.P.filter) x; true with Invalid -> false in
  let b1 = filter v1 in
  let b2 = filter v2 in
  (* FIXME: line info z is wrong: it should be the beginning of the sentence. *)
  if b1 && b2 then error "%s: Ambiguous:\n1: %s\n2: %s" z (tshow v1) (tshow v2)
  else if b1 then v1 else v2

let reduce : P.c -> int option = function
  | P.Shift _ -> None 
  | P.Reduce p -> Some p

type 'u path = 'u P.v ref list * 'u w ref (* path links and path end node 'h' *)

let rec paths (n:int) ((fs,w) as h:'u path) : 'u path list =
  if n<=0 then [h] else 
  M.mapc_rev_list (fun (_,(f0,w0)) -> paths (n-1) (f0::fs, w0)) (!w).succs

(* deterministic path *)
let rec path (n:int) ((vs,w) as h:'u path) : 'u path =
  if n<=0 then h else 
  let (_,(v,w)) = M.head (!w).succs in
  path (n-1) (v::vs, w)

let rec paths_via (n:int) (w1:'u w ref) (v:'u P.v ref) (w2:'u w ref) 
  ((vs,w):'u path) : 'u path list =
  if n<=0 then [] else 
  if w==w1 then paths (n-1) (v::vs, w2)
  else M.mapc_rev_list (fun (_,(v0,w0)) -> paths_via (n-1) w1 v w2 (v0::vs, w0)) (!w).succs

let rec reducer (a:'u P.a) (g:'u g) (z:P.info) (t:C.t) (p:int) (x:C.x) 
  ((fs,w2):'u path) : unit = 
  let q3 = P.goto a (!w2).state x in 
  let v = ref (P.Node (p, z, fs)) in
  match M.find q3 g.actives with
  | Some w3 ->
    (match M.find (!w2).uid (!w3).succs with
    | Some (r,_) -> r := merge a z !v !r
    | None ->
      connect w3 v w2;
      let f4 _ w4 =
        if not (L.memq w4 g.actions) then (
        let cs = P.actions a (!w4).state t in
        let ps = L.collect reduce cs in (* FIXME: really a set? *)
        let fp p =
          let (x,s) = a.P.ps.(p) in
          let hs = paths_via (L.size s) w3 v w2 ([],w4) in
          L.iter (reducer a g z t p x) hs in
        L.iter fp ps) in
      M.iter f4 g.actives)
  | None ->
    let w3 = make q3 in    
    connect w3 v w2;
    g.actives <- M.add q3 w3 g.actives;
    g.actions <- L.add w3 g.actions

let shifter (a:'u P.a) (g:'u g) (z:P.info) (u:'u) : unit =
  g.actives <- M.empty;
  let f (w1,q3) = 
    match M.find q3 g.actives with
    | Some w3 -> connect w3 (ref (P.Leaf u)) w1
    | None ->
      let w3 = make q3 in
      connect w3 (ref (P.Leaf u)) w1;
      g.actives <- M.add q3 w3 g.actives in
  L.iter f g.shifts

let actor (a:'u P.a) (g:'u g) (z:P.info) (t:C.t) : unit =
  let w1 = L.head g.actions in
  g.actions <- L.tail g.actions;
  let cs = P.actions a (!w1).state t in
  if cs=[] then a.P.errors <- (z, t, (!w1).state) :: a.P.errors;
  let fc = function
    | P.Shift q2 -> 
      g.shifts <- L.add (w1, q2) g.shifts
    | P.Reduce p -> 
      let (x,s) = a.P.ps.(p) in
      let hs = paths (L.size s) ([],w1) in
      L.iter (reducer a g z t p x) hs in
  L.iter fc cs

exception Nondet                        (* non-deterministic *)

(* specialization of actor, reducer, paths for |actives| = 1 *)
let rec actor1 (a:'u P.a) (g:'u g) (z:P.info) (u:'u) (t:C.t) (w1:'u w ref) : unit =
  match P.actions a (!w1).state t with
  | [P.Shift q2] ->
    let w2 = make q2 in
    connect w2 (ref (P.Leaf u)) w1;
    g.actives <- M.of_list [(q2,w2)]
  | [P.Reduce p] -> 
    let (x,s) = a.P.ps.(p) in
    if (!w1).ddepth < 10 + L.size s then raise Nondet;
    let (fs,w2) = path (L.size s) ([],w1) in
    let q3 = P.goto a (!w2).state x in
    (* FIXME: why no need to consider q3 = (!w1).state and do 'paths_via' reduce? *)
    let w3 = make q3 in
    connect w3 (ref (P.Node (p, z, fs))) w2; 
    g.actives <- M.of_list [(q3,w3)];
    g.actions <- [w3];
    actor1 a g z u t w3
  | _ -> raise Nondet

let consume (a:'u P.a) (g:'u g) (z:P.info) (u:'u) : unit =
  let t = opt_get a.P.tag u in
  g.actions <- M.range_list g.actives;
  g.shifts <- L.empty;
  (* TODO: benchmark: use non-exception style (with if-then-else) *)
  try 
    if L.size g.actions <> 1 then raise Nondet;
    actor1 a g z u t (L.head g.actions) 
  with Nondet ->
    (while not (L.is_empty g.actions) do actor a g z t done;
    shifter a g z u)

let parse (a:'u P.a) (us:(P.info * 'u) list) : 'u P.v =
  if Util.arg_bool "-time" 
  then printf_flush "Parsing %s... " (Util.info_filename (fst (L.head us)));
  Util.timers_push ();
  if debug then P.check a;  
  assert (L.size us > 0); (* always contains EOF *)
  let w = make a.P.q0 in
  (!w).ddepth <- (!w).ddepth + 1;
  let g = {
    actives = M.of_list [(a.P.q0, w)];
    actions = L.empty;
    shifts = L.empty } in
  L.iter (fun (z,u) -> consume a g z u) us;
  if M.size g.actives = 0 then report a;
  let weof = snd (snd (M.head (!(snd (M.head g.actives))).succs)) in
  if Util.arg_bool "-time" then printf_flush "%.01fs\n" (Util.timers_pop ());
  !(fst (snd (M.head (!weof).succs)))



(*
References:

Tomita style generalised parsers
http://www.cs.rhul.ac.uk/CompSci/Research/languages/publications/tomita_style_1.ps

http://www.cs.berkeley.edu/~smcpeak/elkhound/sources/elkhound/algorithm.html

www.cs.lth.se/Research/LDTA2004/d07_Johnstone.pdf
The Grammar Tool Box: a case study comparing GLR parsing algorithms

Adrian Johnstone, Elizabeth Scott, Giorgios Economopoulos: Generalised
Parsing: Some Costs. CC 2004: 89-103

Recursion Engineering for Reduction Incorporated Parsers,
Adrian Johnstone and Elizabeth Scott,

Generalised bottom up parsers with reduced stack activity,
Elizabeth Scott and Adrian Johnstone,
Computer Journal, 48, 5 565-587 (2005)

# Evaluating GLR parsing algorithms,
Adrian Johnstone, Elizabeth Scott and Giorgios Economopoulos,
Science of Computer Programming, to appear (2006)

# Right Nulled GLR parsers,
Elizabeth Scott and Adrian Johnstone,
ACM Trans. Programming Languages and Systems, to appear (2006)

Adrian Johnstone, Elizabeth Scott: Generalised Regular Parsers. CC 2003: 232-246

Pitfalls:

- Use (==) instead of (=)

- A node is _not_ unique identified by the state.

- Because of garbage collection, reference cells _cannot_ be ordered
using physical equality (=).

- paths_via instead of computing and filtering all paths

- For small associative lookup (like 'w.succs') performance is better
with binary map (logarithmic time complexity) than hash table
(constant time complexity) because of memory overhead and key
arithmetic computation.


TODO:
- check grammar for why so many nondet = 2
- bug: use McPeak's worklist for reduction

- formally prove that 'actions' and 'actives' are lists, not
sets. that is, whenever an element is added, the element is not
already in the list

FIXME: this grammar fails to parse the empty string (from optional label in Cif): 

label:
= Lset: '{' prole ++ '&' '}'
| Lpublic:
;

*)
