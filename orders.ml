#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module type VAR_TYPE =
sig
  type t
  val string_of : t -> string
  val eq : t -> t -> bool
end;; 

module type GORDERS_TYPE = 
sig
  type role
  type chan
  type suid
  
  type event
  type transmission

  val string_of_role : suid -> string
  val string_of_role : role -> string
  val string_of_chan : chan -> string
  val string_of_event : event -> string
  val string_of_transmission : transmission -> string

  type orders
  type assrt

  val string_of : assrt -> string 

  val mk_hbe : event ->  event -> assrt
  val mk_hbt : transmission -> transmission -> assrt
  val mk_cbe : event -> event -> assrt 

  val mk_and : assrt -> assrt -> assrt 
  val mk_or : assrt -> assrt -> assrt 
  val mk_order : orders -> assrt

  val mk_event : role -> suid -> chan -> event
  val mk_assrt_event : role -> suid -> chan -> assrt
  
  val mk_transmission : role -> role -> suid -> chan -> transmission
  val mk_assrt_transmission : role -> role -> suid -> chan -> assrt

  val is_assrt : assrt -> bool
  val mk_empty : unit -> assrt

  val is_cb : assrt -> bool
  val is_hb : assrt -> bool
  val get_events_unsafe : assrt -> event * event
  val get_suid : event -> suid

  val eq_role  : role  -> role  -> bool
  val eq_chan  : chan  -> chan  -> bool
  val eq_suid  : suid  -> suid  -> bool
  val eq_event : event -> event -> bool

  val contains_suid  : suid list -> suid -> bool 
  val contains_event : event list -> event -> bool 
end;;

(* generic orders, where role and chan are polymorphic *)
module GOrders
    (Var : VAR_TYPE) =
struct
  (* boundary base element *)
  type role = Var.t
  type chan = Var.t
  type suid = Var.t
                                
  type event = {
    role   : role;
    uid    : suid;
    channel: chan;
  }

  (* boundary base element *)
  and transmission = {
    sender   : role;
    receiver : role;
    uid      : suid;
    channel  : chan;
  }
  
  let string_of_role = Var.string_of
  let string_of_chan = Var.string_of
  let string_of_suid = Var.string_of
  let string_of_event e = (string_of_role e.role) ^ "^" ^(string_of_suid e.uid)
  let string_of_transmission e = (string_of_role e.sender) ^ "-" ^ (string_of_suid e.uid) ^ "->" ^ (string_of_role e.receiver)

  (* order relations - to be collected after analyzing the protocol *)
  type orders  = HBe of hbe_type
               | HBt of hbt_type
               | CBe of cbe_type
  and assrt   = Event of event
              | NEvent of event
              | Transm of transmission
              | Order of orders
              | And of and_type
              | Or of or_type
              | Impl of impl_type
              | Bot
              | NoAssrt

  and hbe_type = {
    hbe_event1 : event;
    hbe_event2 : event;
  }
  and hbt_type = {
    hbt_transmission1 : transmission;
    hbt_transmission2 : transmission;
  }
  and cbe_type = {
    cbe_event1 : event;
    cbe_event2 : event;
  }
  and and_type = {
    and_assrt1 :  assrt;
    and_assrt2 :  assrt;
  }
  and or_type = {
    or_assrt1 :  assrt;
    or_assrt2 :  assrt;
  }
  and impl_type = {
    impl_event :  event;
    impl_assrt :  assrt;
  }

  let string_of e1 =
    let rec helper e1 = 
      match e1 with
      | Event e  -> "(" ^ string_of_event e ^ ")"
      | NEvent e -> "not("^ (string_of_event e) ^ ")"
      | Transm t -> string_of_transmission t
      | Order (HBe e) -> "(" ^ (string_of_event e.hbe_event1) ^ " <_HB " ^ (string_of_event e.hbe_event2) ^ ")"
      | Order (HBt t) -> "(" ^(string_of_transmission t.hbt_transmission1) ^ " <_HB " ^ (string_of_transmission t.hbt_transmission2) ^ ")"
      | Order (CBe e) -> "(" ^ (string_of_event e.cbe_event1) ^ " <_CB " ^ (string_of_event e.cbe_event2) ^ ")"
      | And a -> (helper a.and_assrt1) ^ " & " ^ (helper a.and_assrt2)
      | Or  a -> (helper a.or_assrt1) ^ " or " ^ (helper a.or_assrt2)
      | Impl a -> (string_of_event a.impl_event) ^ "=>" ^ (helper a.impl_assrt)
      | Bot -> "Bot"
      | NoAssrt -> ""
    in helper e1

  let mk_hbe e1 e2 = Order (HBe {hbe_event1 = e1; hbe_event2 = e2})
  let mk_hbt e1 e2 = Order (HBt {hbt_transmission1 = e1; hbt_transmission2 = e2})
  let mk_cbe e1 e2 = Order (CBe {cbe_event1 = e1; cbe_event2 = e2})

  let mk_and assrt1 assrt2 = And {and_assrt1 = assrt1; and_assrt2 = assrt2}
  let mk_or assrt1 assrt2 = Or {or_assrt1 = assrt1; or_assrt2 = assrt2}
  let mk_order order = Order order
  
  let mk_event (r:role) (id:suid) (chan:chan) : event = {role = r; uid = id; channel = chan}
  let mk_assrt_event (r:role) (id:suid) (chan:chan) : assrt = Event (mk_event r id chan)

  let mk_transmission (sender:role) (receiver:role) (id:suid) (chan:chan) : transmission = {sender = sender; receiver = receiver; uid = id; channel = chan}
  let mk_assrt_transmission (sender:role) (receiver:role) (id:suid) (chan:chan) : assrt = Transm {sender = sender; receiver = receiver; uid = id; channel = chan}
  
  let is_assrt a = match a with
    | NoAssrt -> false
    | _ -> true

  let mk_empty () = NoAssrt

  let eq_role r1 r2  = Var.eq r1 r2
  let eq_chan c1 c2  = Var.eq c1 c2
  let eq_suid s1 s2  = Var.eq s1 s2
  let eq_event e1 e2 = (eq_role e1.role e2.role) && (eq_role e1.uid e2.uid)

  let contains_suid lst suid = List.exists (eq_suid suid) lst
  let contains_event lst ev  = List.exists (eq_event ev)  lst

  let is_cb assrt =
    match assrt with
    | Order (CBe _) -> true
    | _             -> false
  
  let is_hb assrt =
    match assrt with
    | Order (HBe _) -> true
    | _             -> false

  let get_events_unsafe assrt =
    match assrt with
    | Order (HBe hbe) -> hbe.hbe_event1, hbe.hbe_event2
    | Order (CBe cbe) -> cbe.cbe_event1, cbe.cbe_event2
    | _ -> failwith "Expecting a HB or CB relation"

  let get_suid ev = ev.uid
  
end ;;
  
(* ==================== KEY =========================== *)
module type DAG_KEY_TYPE =
  functor (Orders : GORDERS_TYPE) ->
sig
  type t = Orders.event

  val eq: t ->  t -> bool
  val compare: t ->  t -> int
  val string_of: t -> string
end;;

module Event  : DAG_KEY_TYPE =
  functor (Orders: GORDERS_TYPE) ->
struct
  type t = Orders.event

  let eq e1 e2      = Orders.eq_event e1 e2
  let string_of e   = Orders.string_of_event e 
  let compare e1 e2 = String.compare (string_of e1) (string_of e2)
end;;

 
(* ==================== VERTEX =========================== *)
module type VERTEX_TYPE =
  (* functor (Param : VAR_TYPE) -> *)
sig
  type t 

  val eq: t ->  t -> bool
  val compare: t ->  t -> int
  val string_of: t -> string
  val contains:  t list -> t -> bool
end;;

module EVertex  (* : VERTEX_TYPE *) =
  functor (Var : VAR_TYPE) ->
struct
  module Orders = GOrders(Var)
  type t = Orders.event

  let eq e1 e2       = Orders.eq_event e1 e2
  let string_of e    = Orders.string_of_event e
  let compare e1 e2  = String.compare (string_of e1) (string_of e2)
  let contains lst e = Orders.contains_event lst e
end;;

module VVertex  (* : VERTEX_TYPE *) =
  functor (Param : VAR_TYPE) ->
struct
  type t = Param.t

  let eq e1 e2       = Param.eq e1 e2
  let string_of e    = Param.string_of e 
  let compare e1 e2  = String.compare (string_of e1) (string_of e2)
  let contains lst e = List.exists (eq e) lst 
end;;
 
(* ====================  DAG  =========================== *)
(* module type DAG_TYPE = *)
(* sig *)
(*   type vertex  *)
(*   type arrow_kind *)
(*   type t *)

(*   val create: unit -> t *)
(* end *)

module Make_DAG0 (Vertex: VERTEX_TYPE) (* : DAG_TYPE  *)=
struct
  module Key = Vertex
  (* vertex == Key.t == Orders.event *)
  type vertex     = Vertex.t
  type key        = vertex
  type arrow_kind = HB | CB | Backward
  type elem       = {arrow: arrow_kind ; vertex: vertex}
  type elist      = elem list
  type data       = {predecessors: elist; successors: elist}
  type edge       = {tail: vertex; kind: arrow_kind; head: vertex}

  module M = Map.Make(Key)
  type t   = data M.t

  (* PRINTERS *)
  let string_of_arrow_kind arrow_kind =
    match arrow_kind with
    | HB -> "-->"
    | CB -> "->>"
    | Backward -> "<-"
  let string_of_vertex = Vertex.string_of
  let string_of_elem (e:elem): string = (string_of_arrow_kind e.arrow) ^ (string_of_vertex e.vertex)
  let string_of_elist  = pr_list string_of_elem
  let string_of_data d = pr_pair (add_str "Predecessors" string_of_elist)
      (add_str "Successors" string_of_elist) (d.predecessors,d.successors)
  let string_of tbl    = M.fold (fun key data acc ->
      (Key.string_of key) ^ ":" ^ (string_of_data data) ^ "\n" ^ acc ) tbl ""

  (* EQUALITIES *)
  let eq_arrow (a1: arrow_kind) (a2: arrow_kind) =
    match a1,a2 with
    | HB,HB | CB,CB | Backward,Backward -> true | _,_ -> false
  let eq_vertex (v1: vertex) (v2: vertex) = Key.eq v1 v2
  let eq_elem (e1:elem) (e2:elem) =
    (eq_arrow e1.arrow e2.arrow) && (eq_vertex e1.vertex e2.vertex)

    (* MAKERS *)
  let create ()        = M.empty
  let mk_empty_data () = {successors = []; predecessors = [] }
  let mk_vertex e      = e
  let mk_elem a v      = {arrow = a; vertex = v}
  let mk_edge t a h    = {tail = t; kind = a; head = h}

  
  (* QUERIES *)
  let find tbl vertex      = M.find vertex tbl
  let find_safe tbl vertex = try find tbl vertex with Not_found -> mk_empty_data ()
  let mem tbl vertex       = M.mem vertex tbl
  let elist_mem lst elem   = List.exists (eq_elem elem) lst
  let exists_elist elist elem=  elist_mem elist elem
  let exists_successor tbl key elem =
      let data = find_safe tbl key in
      elist_mem data.successors elem
  let exists_predecessor tbl key elem =
      let data = find tbl key in
      elist_mem data.predecessors elem
  let is_weak arrow   = match arrow with |CB -> true | _ -> false
  let is_strong arrow = match arrow with |HB -> true | _ -> false

  (* MISC *)
  let filter tbl (fnc: key->data->bool) = M.filter fnc tbl
  let filter_elist fnc elist = List.filter fnc elist
  let fold fnc acc tbl = M.fold fnc tbl acc
  let fold_elist fnc acc elist = List.fold_left fnc acc elist
  let map fnc tbl = M.map fnc tbl
  let map_elist fnc elist = List.map fnc elist
      
  let get_keys tbl : vertex list = List.map fst (M.bindings tbl) 
  let get_weak (elist:elist) :elist   = filter_elist (fun el -> is_weak el.arrow) elist
  let get_strong (elist:elist) :elist = filter_elist (fun el -> is_strong el.arrow) elist
  let get_successors tbl vertex   = let data = find_safe tbl vertex in data.successors
  let get_predecessors tbl vertex = let data = find_safe tbl vertex in data.predecessors
  let get_weak_successors tbl vertex   = get_weak (get_successors tbl vertex)
  let get_strong_successors tbl vertex = get_strong (get_successors tbl vertex)
  let rec get_all_successors tbl vertex =
    let successors = get_successors tbl vertex in
    List.fold_left (fun acc v -> acc@(get_all_successors tbl v.vertex)) successors successors
  let rec get_all_predecessors tbl vertex = 
    let predecessors = get_predecessors tbl vertex in
    List.fold_left (fun acc v -> acc@(get_all_predecessors tbl v.vertex)) predecessors predecessors  
  
  (* UPDATES *)
  let set_successors  succ data  = {data with successors = succ}
  let set_predecessors pred data = {data with predecessors = pred}
  let add_successors   succ data = {data with successors = succ::data.successors}
  let add_predecessors pred data = {data with predecessors = pred::data.predecessors}
 
  let add_vertex tbl key data = M.add key data tbl
  (* overwrites existing successors/predecessors *)
  let set_successors_tbl   tbl key succ =
    let data = find_safe tbl key in
    add_vertex tbl key (set_successors succ data)
  let set_predecessors_tbl tbl key pred =
    let data = find_safe tbl key in
    add_vertex tbl key (set_predecessors pred data)
  (* adds on top of the existing successors/predecessors *)
  let add_successors_tbl tbl key succ =
    let data = find_safe tbl key in
    add_vertex tbl key (add_successors succ data)
  let add_predecessors_tbl tbl key pred =
    let data = find_safe tbl key in
    add_vertex tbl key (add_predecessors pred data)

  (* Connects 2 vertices as follows:
     vertex1 : succ1, pred1  >>and<< vertex2:  succ2, pred2     ===TO===>
     vertex1 : vertex2::succ1, pred1 >>and<<  vertex2:  succ2, vertex1::pred2 ; *)
  let connect tbl arrow vertex1 vertex2 =
    let new_pred = mk_elem Backward (mk_vertex vertex1) in
    let tbl      = add_predecessors_tbl tbl vertex2 new_pred in
    let new_succ = mk_elem arrow (mk_vertex vertex2) in
    add_successors_tbl tbl vertex1 new_succ
      
  let connect_list tbl xs = 
    List.fold_left (fun tbl (kind,(e1,e2)) -> connect tbl kind e1 e2) tbl xs

  (* removes an edge from tbl, updating its head predecessors, and its tail successors *)
  let remove_edge tbl (edge:edge) =
    let head_pred = get_predecessors tbl edge.head in
    let head_pred = filter_elist (fun pred -> not (eq_elem (mk_elem Backward edge.tail) pred)) head_pred in
    let tbl = set_predecessors_tbl tbl edge.head head_pred in
    let tail_succ = get_successors tbl edge.tail in
    let tail_succ = filter_elist (fun succ -> not (eq_elem (mk_elem edge.kind edge.head) succ)) tail_succ in
    let tbl = set_successors_tbl tbl edge.tail tail_succ in
    tbl

  let remove_edge_list tbl (edges: edge list) =
    List.fold_left (fun acc_tbl edge -> remove_edge acc_tbl edge) tbl edges

  let add_edge tbl (edge:edge) = connect tbl edge.kind edge.tail edge.head

  let add_edge_list tbl (edges: edge list) =
    List.fold_left (fun acc_tbl edge -> add_edge acc_tbl edge) tbl edges

  (* remove the weak arrows, by replacing them with the stronger connection:
     ex: A <_CB B & B <_HB C ~~> A <_HB C  *)    
  let norm_weak tbl special_elem =
    (* mark for removing the weak(CB) edge with tail "key" and head in "elem"
       add all HB edges which would result from applying CB-HB once*)
    let handle_weak rem add key elem =
      if (Vertex.contains special_elem elem.vertex) then rem,add
      else
        let rem = (mk_edge key elem.arrow elem.vertex)::rem in
        let strong_successors = (get_strong_successors tbl elem.vertex) in
        let to_add = map_elist (fun el -> mk_edge key el.arrow el.vertex) strong_successors in
        let add = to_add@add in
        rem,add in
    let check_for_weak_edge rem add key elem =
      if (is_weak elem.arrow) then handle_weak rem add key elem else rem,add in
    let remove_weak_edges rem add key data =
      fold_elist (fun (rem,add) elem ->
          check_for_weak_edge rem add key elem) (rem,add) data.successors in
    let rem,add = fold (fun key data (rem,add) -> remove_weak_edges rem add key data) ([],[]) tbl in
    let tbl = remove_edge_list tbl rem in
    let tbl = add_edge_list tbl add in
    tbl
      
  (* ADVANCED QUERIES *)
    (* let has_path tbl v1 v2 = *)
    (* try *)
    (*   let rec helper key = *)
    (*     let data = find tbl key in *)
    (*     if (data_mem data (mk_elem HB v2)) then true *)
    (*     else List.exists (fun el -> helper el.vertex) data in *)
    (*   helper v1 *)
    (* with Not_found -> false *)

  
end;;
