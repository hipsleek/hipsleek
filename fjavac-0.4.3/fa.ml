(* fa.ml - finite automata -*- caml -*- *)

open Std
module A = Arrayx
module H = Hashx
module L = Listx
module X = Setx


(*---- Automaton (m), or machine: 

  m  = (qs,az,dt,q0,qf)
  m  = (qs,az,nt,q0,qf)

  q  = state
  a  = alphabet
  dm = deterministic move
  nm = nondeterministic move

  qs = a set of states
  az = a set of alphabets
  dt = a deterministic transition function
  nt = a nondeterministic transition function
  q0 = the initial state
  qf = the set of final states

  Invariant (INV-QBOUND): 0 <= q < A.size qs.
  Invariant (INV-ABOUND): 0 <= a < A.size az.

  Notes on performance: States and alphabets are internally
  represented as integers for fast comparisons. Otherwise, the
  primitive functions [Pervasives.compare_val] and [String.length] are
  overly used.

  Transition functions are implemented as hashtables for
  performance. An efficient mapping of alphabets can only be
  implemented with hashtables. An efficient mapping of states can be
  implemented with arrays, but this require a small hashtable for
  alphabets at each state. Hence the mappings of alphabets and states
  are grouped together here.

----*)

type q = int
type a = int
type qs = q X.t
type dm = (q * a) * q
type nm = (q * a option) * q X.t
type dt = (q * a, q) H.t
type nt = (q * a option, q X.t) H.t
type ('q,'a) dfa = ('q array) * ('a array) * dt * q * (q X.t)
type ('q,'a) nfa = ('q array) * ('a array) * nt * q * (q X.t)


(*---- Invariant checkings (check). *)

let qcheck (qs:'q array) (q:q) : unit =
  if (q < 0 || q >= A.size qs) then 
    fail "INV-QBOUND (0 <= q < size qs): %d, %d)" q (A.size qs)

let acheck (az:'a array) (a:a) : unit =
  if (a < 0 || a >= A.size az) then 
    fail "INV-ABOUND (0 <= a < size az): %d, %d" a (A.size az)
      
let dm_check (qs:'q array) (az:'a array) (((q1,a),q2):dm) : unit =
  qcheck qs q1; acheck az a; qcheck qs q2

let dfa_check ((qs,az,d,q0,qf):('q,'a) dfa) : unit =
  H.iter (dm_check qs az) d;
  qcheck qs q0;
  X.iter (qcheck qs) qf

let nm_check (qs:'q array) (az:'a array) (((q,ao),qs2):nm) : unit =
  qcheck qs q; opt_iter (acheck az) ao; X.iter (qcheck qs) qs2

let nfa_check ((qs,az,d,q0,qf):('q,'a) nfa) : unit =
  H.iter (nm_check qs az) d;
  qcheck qs q0;
  X.iter (qcheck qs) qf


(*---- Conversions (to, of). *)

let dd_to_list (dt:dt) : (q * a * q) list =
  H.map_list (fun ((q1,a),q2) -> (q1, a, q2)) dt
  
let nd_to_list (nt:nt) : (q * a option * q list) list =
  H.map_list (fun ((q,a),qs) -> (q, a, X.to_list qs)) nt
  
let nd_of_list (nt:((q * a option) * q list) list) : nt =
  let f ((q,a),qs) = ((q, a), X.of_list qs) in
  H.of_list (L.map f nt)


(*---- Moves, extended moves, multiple moves (move, xmove, moves). *)

let dmove (dt:dt) (q:q) (a:a) : q = 
  match H.find dt (q, a) with
  | Some q2 -> q2
  | None -> fail "Invalid transition: q=%d, a=%d" q a

let dxmove (dt:dt) : q -> a list -> q = L.foldl (dmove dt)

let nmove (nt:nt) (q:q) (a:a) : qs = H.get_set nt (q, Some a)
let nmoves (nt:nt) (qs:qs) (a:a) : qs = X.imapc (fun q -> nmove nt q a) qs
let nxmoves (nt:nt) (qs:qs) (s:a list) : qs = L.foldl (nmoves nt) qs s
let nxmove (nt:nt) (q:q) : a list -> qs = nxmoves nt (X.single q)


(*---- Minimization.

  2005-1027: it seems little benefit is gained in practice: for
  'java.g' the numbers of states before and after minimizations are
  496 and 494, merely an improvement of 2 states. TODO: check if the
  algorithm is correct to see if there are actually more improvements
  possible. Good reference and reading is Gries' [2] that describes
  Hopcroft's O(n log n) algorithm.

  Input:  DFA m1 = (qs,az,dt,q0,qf)
  Output: DFA m2 = (qs',az,dt',q0',qf') where

  Assumption: each state of m1 is a set of some type 'q (the result of
  determinization) such that a state of m2 is also a set of type 'q.
 
  f = surjective function that maps a state (q) to its equivalent class (int)
  g = inverse of f that maps an equivalent class to a set of states 
  n = number of equivalent classes

  qs' = { union qs | (_,qs) <- g }
  dt' = { (f q1, a, f q2) | (q1,a,q2) <- dt }
  q0' = f q0
  qf' = { f q | q <- qf }  

  Minimization: Hopcroft and Ullman 1979, p.70.
  
  Hopcroft and Ullman. Introduction to Automata Theory, Languages, and
  Computation. Addison-Wesley, 1979.
  
  http://juggernaut.eti.pg.gda.pl/~jandac/fsm_algorithms
  n^2 minimization: http://www.mpi-sb.mpg.de/~backes\
    /uebersetzerbau.SS02/doc/closuremin.pdf
  http://www.edite-de-paris.com.fr/~fpons/Caml/Ressources/automata.html
  http://odur.let.rug.nl/~vannoord/Fsa/ prolog
  
  [1]
  J. Hopcroft, "An n log n Algorithm for Minimizing States in a Finite 
  Automaton", in: Theory of Machines and Computations, Ed. Zvi Kohavi, Azaria 
  Paz; pages 189--196, Academic Press, 1971.
  
  [2]
  D. Gries, "Describing an Algorithm by Hopcroft", in: Acta Informatica (2);
  pages 97--109, Springer, 1973
  
  [3]
  B. W. Watson, "A taxonomy of finite automata minimization algorithms"; 
  1994, http://citeseer.nj.nec.com/article/watson94taxonomy.html
  

  It should be more efficient to loop over production rules (as in the
  function 'minimize' below) than over pairs of states (than the code
  snippets below). It's also tricky to use 'continue' (as in C/Java)
  with iteration 'H.iter' to skip the rest of production rule in the
  inner loop here and continue to the next pair of states.

    for i = 0 to n-1 do
      for j = i+1 to n-1 do          (* distinct pairs (i,j) *)
        if not m.(i).(j) then           (* only non-distinguishable state *)
          H.iter (fun ((q1,a),q2) ->
            if q1=i then 
              match H.get_option dt (j,a) with
              | Some q when not m.(q).(q2) -> ()
              | _ -> (* by transition *)
                m.(i).(j) <- true; 
                m.(j).(i) <- true; 
                more := true;
                (* optimize: skip this and continue to the next pair *)
              ) dt
----*)

let minimize ((qs,az,dt,q0,qf):('q X.t,'a) dfa) =
  let n = A.size qs in
  let m = A.make_matrix n n false in    (* distinguishable *)
  let nqf = X.minus (X.interval 0 (n-1)) qf in (* non-final states *)
  X.iter (fun q1 -> X.iter (fun q2 ->   (* by finalness *)
    m.(q1).(q2) <- true; m.(q2).(q1) <- true) nqf) qf;
  let more = ref true in
  while !more do
    more := false;
    H.iter (fun ((i,a),qi) ->
      for j = 0 to n-1 do
        if not m.(i).(j) then
          match H.find dt (j,a) with
          | Some qj when not m.(qi).(qj) -> ()
          | _ -> (* by transition *)
            m.(i).(j) <- true; 
            m.(j).(i) <- true; 
            more := true;
      done
           ) dt
  done;
  let index = A.map (fun a -> fst (opt_get (A.findj (fun b -> not b) a))) m in
  printf "minimized: %d / %d\n" (A.max index) n
  
  
(*---- Epsilon transition (zt), or epsilon closure. *)

type zt = qs array

let zt_make (n:int) (nt:nt) : zt =
  let zt = A.make n X.empty in 
  let f ((q,ao),qs) =
    if is_none ao then X.iter (fun q2 -> X.array_add zt q q2) qs in
  H.iter f nt; 
  X.closure zt; zt

let zmoves (zt:zt) (qs:qs) : qs = X.imapc (fun q -> zt.(q)) qs


(*---- Valid alphabets (va). *)

type va = a X.t array

let va_make (n:int) (nt:nt) : va =  
  let va = A.make n X.empty in
  let f = function
    | ((q,None),_) -> ()
    | ((q,Some a),_) -> X.array_add va q a in
  H.iter f nt; va

let va_qs (va:va) (qs:qs) = X.imapc (fun q -> va.(q)) qs


(*---- Inverted transitions (inv). *)

let nt_inv (nt:nt) : nt =
  let f ((q1,a),qs) = X.map_list (fun q2 -> ((q2,a),q1)) qs in
  H.of_list_set (L.mapc f (H.to_list nt))

let dt_inv (dt:dt) : nt =
  let f ((q1,a),q2) = ((q2, Some a),q1) in
  H.of_list_set (L.map f (H.to_list dt))


(*---- Powerset transition (pt), or subset construction.

  pt = { (qs1,a,qs2) | q1 <- qs1, (q1,a,qs) <- nt, qs2 = union (zmoves qs)}

     = { (qs1,a,qs2) | a <- va qs1, qs2 = zmoves (moves qs a) }

  move q a   = {}  if nt (q,a) = undefined
  move q a   = nt (q,a)
  moves qs a = union { move q a | q <- qs }

  Assumption: qs1 = zmoves qs1.

----*)

type pt = (qs * a, qs) H.t

let pt_iter (nt:nt) (zt:zt) (pt:pt) (va:a X.t array) (qs1:qs) : qs X.t =
  if debug then assert (qs1 = zmoves zt qs1);  
  let f a = 
    let qs = X.imapc (fun q -> H.get_set nt (q, (Some a))) qs1 in
    let qs2 = zmoves zt qs in
    assert (X.is_nonempty qs2);         (* sanity *)
    H.set pt (qs1,a) qs2; qs2 in
  X.map f (va_qs va qs1)

(* TODO: optimize. ref: appel p.29. *)
let pt_make (n:int) (nt:nt) (zt:zt) (qs0:qs) : pt =
  let va = va_make n nt in
  let pt = H.make n in
  X.dfs (pt_iter nt zt pt va) (X.single qs0); pt


(*---- Determinization.

  Input:  NFA m1 = (qs,az,nt,q0,qf)
  Output: DFA m2 = (qs',az,dt,q0',qf') where

  dt  = powerset transition of nt
  qs' = { qs1; qs2 | (qs1,_,qs2) <- dt }
  q0' = closure q0
  qf' = { qs | qs <- qs, some q <- qf, mem q qs }

----*)

let nfa_to_dfa (((qs,az,nt,q0,qf) as m):('q,'a) nfa) : ('q X.t,'a) dfa =
  if debug then nfa_check m;
  let zt = zt_make (A.size qs) nt in
  let q0' = zt.(q0) in
  let pt = pt_make (A.size qs) nt zt q0' in
  let qs0 = X.union (X.map fst (H.domain pt)) (H.range pt) in
  let qf' = X.take (X.some (fun q -> X.mem q qf)) qs0 in
  let qindex = H.index_set qs0 in
  let qs' = A.map (X.map (fun q -> qs.(q))) (X.to_array qs0) in
  let dt = H.map (fun ((qs1,a),qs2) -> ((qindex qs1,a),qindex qs2)) pt in
  let m' = (qs', az, dt, qindex q0', X.map qindex qf') in
  if debug then dfa_check m'; m'


(*---- Conventions.

m - automata
q - states
a - alphabets
ao - optional alphabets

qs = a set of states
az = a set of alphabets
d  = a transition function (delta)
q0 = the initial state
qf = the set of final states

zt = epsilon transitions
pt = power transitions

----*)
