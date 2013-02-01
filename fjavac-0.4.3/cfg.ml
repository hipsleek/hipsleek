(* cfg.ml - context free grammar *)

open Std
module A = Arrayx
module C = Charx
module F = Fa
module H = Hashx
module L = Listx
module S = Strx
module X = Setx

(* Grammar (g): 

  g = (ts,xs,ps,x0)
  
  t  = terminals
  x  = variables
  a  = alphabets
  s  = strings

  ts = a set of terminals
  xs = a set of variables
  ps = a set of productions
  x0 = the initial variable (start symbol)

  Invariant (INV-TBOUND): 0 <= t < size ts.
  Invariant (INV-XBOUND): 0 <= x < size xs.
  Invariant (INV-START): size ps[x0] = 1.
  Invariant (INV-TOTAL): size ps = size xs.

*)

type t = int
type x = int
type ts = t X.t
type xs = x X.t
type a = T of t | X of x
type s = a list
type p = s list
type ('t,'x) g = ('t array) * ('x array) * (p array) * x 

let is_t = function T _ -> true | X _ -> false
let is_x = function T _ -> false | X _ -> true
let to_x = function T _ -> assert_false () | X x -> x


(*---- Invariant checkings (check). *)

let tcheck (ts:'t array) (t:t) : unit =
  if (t < 0 || t >= A.size ts) then 
    fail "INV-TBOUND (0 <= t < size ts): %d, %d" t (A.size ts)

let xcheck (xs:'x array) (x:x) : unit =
  if (x < 0 || x >= A.size xs) then 
    fail "INV-XBOUND (0 <= x < size xs): %d, %d" x (A.size xs)

let acheck (ts:'t array) (xs:'x array) : a -> unit = function
  | T t -> tcheck ts t
  | X x -> xcheck xs x

let scheck (ts:'t array) (xs:'x array) : s -> unit =
  L.iter (acheck ts xs)

let check ((ts,xs,ps,x0):('t,'x) g) : unit =
  xcheck xs x0;
  if (L.size ps.(x0) <> 1) then
    fail "INV-START (size ps[0] = 1): %d" (L.size ps.(x0));
  if (A.size xs <> A.size ps) then
    fail "INV-TOTAL (size xs = size ps): %d, %d" (A.size xs) (A.size ps);
  A.iter (L.iter (scheck ts xs)) ps

let rule0 (ps:p array) (x0:'x) : s =
  assert (L.size ps.(x0) = 1); (* INV-START *)
  L.head ps.(x0)


(*---- LR(0) characteristic automaton (ca).
  Ref: Hopcroft and Ullman 1979, p.250.

  Input:  CFG g = (ts,xs,ps,x0)
  Output: DFA from NFA m = (qs,az,d,q0,qf) where

  LF-items - a production with a dot (represented by an index):
  
  qs = items g
  az = union ts xs
  q0 = x0 -> . ps[x0]
  qf = { x -> s . | (x,p) <- ps, s <- p }

  items = concat [ (x,s,i) | (x,p) <- ps, s <- p, i <- 0..|s| ]

  d (x -> s1 . a s2) (Some a) = { x -> s1 a . s2 }
    where s = s1 a s2, for (x,p) <- ps, s <- p 
  d (x -> s1 . x2 s2) None = { x2 -> . s3 | s3 in ps[x2] }
    where s = s1 x2 s2, for (x,p) <- ps, s <- p

  Invariant (INV-ITEM): 0 <= i <= size s.  
*)

type tm = x * s * int                   (* LR(0) grammar item *)
type ca = (tm X.t, a) F.dfa             (* LR(0) characteristic automaton *)

(* If the next alphabet of a grammar item is a terminal, or the
grammar item is in a reduction state. *)
let tm_is_t ((x,s,i):tm) : bool = i = L.size s || is_t (L.get s i)

let tm_check (ts:'t array) (xs:'x array) ((x,s,i):tm) : unit = 
  xcheck xs x;
  scheck ts xs s;
  if (i < 0 || i > L.size s) then 
    fail "INV-ITEM (0 <= i <= size s): %d, %d" i (L.size s)  

let items ((ts,xs,ps,_):('t,'x) g) : tm array =
  let f1 x s i = (x, s, i) in
  let f2 x s = L.map (f1 x s) (L.interval 0 (L.size s)) in
  A.mapic (fun x p -> L.mapc (f2 x) p) ps

let ca_make ((ts,xs,ps,x0) as g:('t,'x) g) : ca =
  if debug then check g;
  let qs = items g in
  let qindex = H.index_array qs in
  let az1 = A.map (fun t -> T t) (A.interval 0 (A.size ts - 1)) in
  let az2 = A.map (fun x -> X x) (A.interval 0 (A.size xs - 1)) in
  let az = A.cat2 az1 az2 in
  let aindex = H.index_array az in
  let s0 = rule0 ps x0 in
  let q0 = qindex (x0, s0, 0) in
  let f1 x s = qindex (x, s, L.size s) in
  let qf = X.of_array (A.mapic (fun x p -> L.map (f1 x) p) ps) in
  let nt = H.make (A.size qs) in
  let f2 x s (i,a) =
    let q1 = qindex (x,s,i) in
    let q2 = qindex (x,s,i+1) in
    H.add nt (q1, Some (aindex a)) (X.single q2);
    match a with
    | T _ -> ()
    | X x2 ->
      let qs2 = L.map (fun s3 -> qindex (x2, s3, 0)) ps.(x2) in
      H.add nt (qindex (x,s,i), None) (X.of_list qs2) in
  A.iteri (fun x p -> L.iter (fun s -> L.iteri (f2 x s) s) p) ps;
  let m = F.nfa_to_dfa (qs, az, nt, q0, qf) in
  if debug then F.dfa_check m; m


(*---- Nullable variable sets (nu).

  Definition: the set of variables that can derive the empty
  string (nullable = { x | x derives [] }). 
*)   

type nu = xs

let nullabled (ps:p array) (dep:xs array) : unit =
  let f x s = 
    if L.all is_x s
    then X.array_union dep x (X.list_map to_x s) in
  A.iteri (fun x p -> L.iter (f x) p) ps

let nullable0 (ps:p array) (dep:xs array) 
  (nu:'x X.t) (x:'x) : 'x X.t * 'x X.t =
  let f = function T _ -> false | X x2 -> X.mem x2 nu in
  let b1 = X.mem x nu in
  let b2 = L.some (L.all f) ps.(x) in
  if b1=b2 then (nu, X.empty) 
  else (X.add x nu, dep.(x))

let nullable (ps:p array) : nu =
  let dep = A.make (A.size ps) X.empty in
  nullabled ps dep;
  X.fixpoint (nullable0 ps dep) X.empty (X.interval 0 (A.size ps - 1))


(*---- Fixpoints. *)

let fixpoint (n:int) (finit:int X.t array -> unit) (fdep:x X.t array -> unit) 
  : int X.t array =
  let init = A.make n X.empty in
  let dep = A.make n X.empty in
  finit init; fdep dep; X.closure dep;
  let s = A.make n X.empty in
  let f x xs = s.(x) <- (X.imapc (fun x2 -> init.(x2)) xs) in
  A.iteri f dep; s  


(*---- First alphabet sets (fi).

  - References: Aho-Sethi-Ullman 1988, p.189.

  - Definitions: the set of terminals that are the first of the strings
  derivable from x or s: 
   
  first x  = { t | x derives t s2 }
  sfirst s = { t | s derives t s2 }

  - Algorithms:

  sfirst0 []     = {}
  sfirst0 (t::_) = {t}
  sfirst0 (x::s) = sfirst0 s, if nullable x
  sfirst0 (x::_) = {}

  sfirstd []     = {}
  sfirstd (t::_) = {}
  sfirstd (x::s) = {x} union (sfirstd s), if nullable x
  sfirstd (x::_) = {x}
                
  first0         = { (x1,x2) | s <- ps[x1], x2 <- sfirst0 s }
  firstd         = { (x1,x2) | s <- ps[x1], x2 <- sfirstd s }

  sfirst []      = {}
  sfirst t::_    = {t}
  sfirst (x::s)  = (first x) union (sfirst s), if nullable x
  sfirst (x::_)  = (first x)

--------------------------------------------------------------*)

type fi = ts array

let rec sfirst0 (nu:nu) : s -> t list = function
  | T t::_ -> [t]
  | X x::s when X.mem x nu -> sfirst0 nu s
  | _ -> []

let rec sfirstd (nu:nu) : s -> x list = function
  | X x::s when X.mem x nu -> x :: sfirstd nu s
  | X x::_ -> [x]
  | _ -> []

and first0 (ps:p array) (nu:nu) (f0:fi) : unit =
  A.iteri (fun x p -> 
  L.iter (fun s -> X.array_union f0 x (X.of_list (sfirst0 nu s))) p) ps

and firstd (ps:p array) (nu:nu) (fd:x X.t array) : unit =
  let f x s = L.iter (fun x2 -> X.array_add fd x x2) (sfirstd nu s) in
  A.iteri (fun x p -> L.iter (f x) p) ps

let first (ps:p array) (nu:nu) : ts array =
  fixpoint (A.size ps) (first0 ps nu) (firstd ps nu)

let rec sfirst (nu:nu) (fi:fi) : s -> ts = function
  | [] -> X.empty
  | T t::_ -> X.single t
  | X x::s when X.mem x nu -> X.union fi.(x) (sfirst nu fi s)
  | X x::_ -> fi.(x)


(*------------------------------------------------------------
  Follow alphabet sets (fo). 
  Ref: Aho-Sethi-Ullman 1988, p.189.

  Definition: follow x = { t | x0 derives s1 x t s2 } (the set of
  terminals that follow the variable x in the strings derivable from
  the start symbol x0).

  sfollow0 []     = {}
  sfollow0 (t::s) = sfollow0 s
  sfollow0 (x::s) = { (x,t) | t <- sfirst s } union (sfollow0 s)

  sfollowd []     = {}
  sfollowd (t::_) = {}
  sfollowd (x::s) = {x} union (sfollowd s), if nullable x
  sfollowd (x::s) = {x}

  follow0         = union { sfollow0 s | (_,p) <- ps, s <- p }
  followd         = { (x2,x1) | (x1,p) <- ps, s <- p, x2 <- sfollowd (rev s) }
  
--------------------------------------------------------------*)

type fo = ts array

let rec sfollow0 (nu:nu) (fi:fi) (f0:fo) : s -> unit  = function
  | [] -> ()
  | (T t)::s -> sfollow0 nu fi f0 s
  | (X x)::s -> 
    X.array_union f0 x (sfirst nu fi s);
    sfollow0 nu fi f0 s

let rec sfollowd (nu:nu) : s -> x list  = function
  | (X x)::s when X.mem x nu -> x :: (sfollowd nu s)
  | (X x)::_ -> [x]
  | _ -> []

let follow0 (ps:p array) (nu:nu) (fi:fi) (f0:fo) : unit =
  A.iter (fun p -> L.iter (sfollow0 nu fi f0) p) ps

let followd (ps:p array) (nu:nu) (fd:x X.t array) : unit =
  let f x s = L.iter (fun x2 -> X.array_add fd x2 x) (sfollowd nu (L.rev s)) in
  A.iteri (fun x p -> L.iter (f x) p) ps

let follow (ps:p array) : ts array =
  let nu = nullable ps in
  let fi = first ps nu in
  fixpoint (A.size ps) (follow0 ps nu fi) (followd ps nu)



(*---- Stateful grammar (sg) and LALR(1) lookahead sets (la).

  - Reference: Bermudez-Logothetis 1989.

  - Definition: 

  1. lookahead q x s = union { t | delta* q2 s = q, (q3,t) <- follow
  (q2,x) } (the LALR(1) lookahead set in the state q for the
  production x -> s, that is, the union of the contextual follow sets
  in the state q2 for the variable x, for any state q2 such that the
  string s takes q2 to q in the LR(0) automaton of the grammar).

  2. follow (q2,x) = { t | x0 derives s1 x t s2, delta* q0 s1 = q2 } (the
  contextual follow set in the state q2 for the variable x, that is,
  the set of terminals that follow the variable x in any string s = s1
  x t s2 derivable from the start symbol x0 such that the string s1
  takes the start state q0 to q2 in the LR(0) automaton of the
  grammar).

  Invariant: delta* q0 (s1 s) = delta* (delta* q0 s1) s = delta* q2 s = q.

  Input : g  = (ts,xs,ps,x0)
          m  = (qs,az,d,q0,qf)
  Output: sg = (ts',xs',ps',x0')

  x0' = { (q0,x0) }
  ts' = { (q,t) | (q,t) <- dom d }
  xs' = union { x0 } { (q,x) | (q,x) <- dom d }
  ps' = { ((q,x), trace q s) | (q,x) <- xs', s <- ps[x] }

  trace q []   = []
  trace q a::s = (q, a) :: (trace (d q a) s)

  la q x s     = { t | q <- d* q1 s, (_,t) <- follow q1 x }
               = { t | q1 <- (inv d)* q (rev s), (_,t) <- follow q1 x }


  Note: Bermudez-Logothetis 1989 does not put x0' in xs', which is a
  mistake.

  TODO: GLR papers (Tomita 1991 and Scott McPeak 2002) suggest that
  LR(0) may have close, if not better, performance than
  LALR. Benchmark to prove or disprove this claim.

--------------------------------------------------------------*)

type sg = (F.q * t,  F.q * x) g

let to_sg (g:('t,'x) g) (m:ca) : sg =
  if debug then check g;
  let (ts,xs,ps,x0) = g in
  let (qs,az,d,q0,_) = m in
  let x0' = (q0, x0) in  
  let f1 (q,a) = match az.(a) with T t -> Some (q,t) | _ -> None in
  let f2 (q,a) = match az.(a) with X x -> Some (q,x) | _ -> None in
  let dom = H.domain d in
  let ts' = X.to_array (X.collect f1 dom) in
  let xs' = X.to_array (X.add x0' (X.collect f2 dom)) in
  let ps' = A.make (A.size xs') [] in
  let tindex = H.index_array ts' in
  let xindex = H.index_array xs' in
  let aindex = H.index_array az in
  let rec trace (q:F.q) : a list -> a list = function
    | [] -> []
    | T t::s -> 
      let q2 = F.dmove d q (aindex (T t)) in 
      T (tindex (q,t)) :: trace q2 s
    | X x::s -> 
      let q2 = F.dmove d q (aindex (X x)) in 
      X (xindex (q,x)) :: trace q2 s in
  let f q x = L.map (trace q) ps.(x) in
  A.iter (fun (q,x) -> ps'.(xindex (q,x)) <- f q x) xs';
  let g' = (ts', xs', ps', xindex x0') in
  if debug then check g'; g'

(* FIXME: shouldn't (q1,x) always be in xs? *)
let la (g:('t,'x) g) (m:ca) : F.q -> x -> s -> ts =
  if debug then (check g; F.dfa_check m);
  let (qs,az,d,_,_) = m in
  let (ts,xs,ps,_) = to_sg g m in
  let fo = follow ps in
  let invd = F.dt_inv d in
  let aindex = H.index_array az in
  let xindex = H.index_array xs in
  (fun q x s ->
    let qs1 = F.nxmove invd q (L.map aindex (L.rev s)) in
(*  todo:  assert (X.is_nonempty qs1);*)
    let f q1 = if A.mem (q1,x) xs then fo.(xindex (q1,x)) else X.empty in
    let ts2 = X.imapc f qs1 in
    X.map (fun t -> snd ts.(t)) ts2)


(*---- Misc. *)

let a_fprint (ts:string array) (xs:string array) (f:out_channel)
  : a -> unit = function
  | T t -> fprintf f "'%s'" (S.show ts.(t))
  | X x -> fprintf f "%s" xs.(x)

let s_fprint (ts:string array) (xs:string array) 
  : out_channel -> s -> unit = 
  L.fprint_sep (a_fprint ts xs) " "

let p_fprint (ts:string array) (xs:string array) 
  (f:out_channel) ((x,s):x * s) : unit =
  fprintf f "%s: %a" xs.(x) (s_fprint ts xs) s

let tm_fprint (ts:string array) (xs:string array) 
  (f:out_channel) ((x,s,i):tm) : unit =
  fprintf f "(%s,%a,%d)" xs.(x) (s_fprint ts xs) s i


let a_fcode (ts:string array) (xs:string array) (f:out_channel)
  : a -> unit = function
  | T t -> fprintf f "C.T %d" t
  | X x -> fprintf f "C.X %d" x

let s_fcode (ts:string array) (xs:string array) 
  : out_channel -> s -> unit = 
  L.fprint_sep (a_fcode ts xs) "; "

let p_fcode (ts:string array) (xs:string array) 
  (f:out_channel) ((x,s):x * s) : unit =
  fprintf f "(%d, [%a])" x (s_fcode ts xs) s

let tm_fcode (ts:string array) (xs:string array) 
  (f:out_channel) ((x,s,i):tm) : unit =
  fprintf f "(%d, [%a], %d)" x (s_fcode ts xs) s i


(*--- Conventions

g - grammar
t - grammar terminal (token)
x - grammar variable
a - grammar alphabet
s - grammar string
p - grammar production
tm - LR(0) grammar item
ca - LR(0) characteristic automaton
cq - LR(0) characteristic state
nu - nullable variable set
fi - first alphabet sets
fo - follow alphabet sets
sg - stateful grammar
st - stateful terminal
sx - stateful variable
la - LALR(1) lookahead sets

*)
