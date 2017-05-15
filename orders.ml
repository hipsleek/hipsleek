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

  val eq_role  : role  -> role  -> bool
  val eq_chan  : chan  -> chan  -> bool
  val eq_suid  : suid  -> suid  -> bool
  val eq_event : event -> event -> bool
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
  let string_of_event e = (string_of_role e.role) ^ "," ^(string_of_suid e.uid)
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

(* ==================== ARROW =========================== *)

module type ARROW_TYPE =
sig
  type t
  type a
  type v

  val split_components: a -> t * (v * v)
  val string_of: t -> string
end;;

module Arrow (Orders: GORDERS_TYPE) =
struct
  type t = HB | CB
  type a = Orders.assrt
  type v = Orders.event
             
  let get_kind rel = if (Orders.is_cb rel)  then CB else if (Orders.is_hb rel) then HB else failwith x_tbi
  let get_events rel = Orders.get_events_unsafe rel
  let split_components rel = get_kind rel, get_events rel
  let string_of kind = match kind with
    | HB -> "-"
    | CB -> "->"
      
end;;    

(* ====================  DAG  =========================== *)
(* module type DAG = *)
(*   sig *)
(*     (\* Element type *\) *)
(*     type e *)
(*     (\* DAG inner type *\) *)
(*     type t *)
(*     type kind *)
(*     (\* Create an empty DAG *\) *)
(*     val create : unit -> t *)
(*     (\* Add a pair of < relation to DAG *\) *)
(*     val add : t -> kind -> (e * e) -> t *)
(*     (\* Add a list of pairs of < relation to DAG *\) *)
(*     (\* val add_list : t -> kind * (e * e) list -> t *\) *)
(*     (\* Check whether an element exists in the DAG *\) *)
(*     val mem : t -> e -> bool *)
(*     (\* Check whether there is a path between two nodes *\) *)
(*     val has_path : t -> e -> e -> bool *)
(*     (\* Check whether lhs < rhs *\) *)
(*     val is_lt : t -> e -> e -> bool *)
(*     (\* Check whether lhs >= rhs *\) *)
(*     val is_gte : t -> e -> e -> bool *)
(*     (\* Check whether lhs < rhs or None if not found *\) *)
(*     val is_lt_opt : t -> e -> e -> bool option *)
(*     (\* Check whether lhs >= rhs, or None if not found *\) *)
(*     val is_gte_opt : t -> e -> e -> bool option *)
(*     (\* (\\* Standard unordered fold *\\) *\) *)
(*     (\* val fold : t -> ('acc -> e -> 'acc) -> 'acc -> 'acc *\) *)
(*   end *)

(* module Make_DAG *)
(*     (Orders: GORDERS_TYPE) *)
(*     (Key   : DAG_KEY_TYPE) *)
(*     (\* (Arrow : ARROW_TYPE with type v := Key.t) *\) *)
(*   (\* : DAG with type e := Key.t *\) = *)
(* struct *)
(*     (\* Arrows *\) *)
(*     type at = HB | CB *)
(*     type aa = Orders.assrt *)
(*     type av = Orders.event *)

(*     let get_kind rel = if (Orders.is_cb rel)  then CB else if (Orders.is_hb rel) then HB else failwith x_tbi *)
(*     let get_events rel = Orders.get_events_unsafe rel *)
(*     let split_components rel = get_kind rel, get_events rel *)
(*     let string_of_arrow kind = match kind with *)
(*       | HB -> "-" *)
(*       | CB -> "->" *)
(*     (\* End - Arrows *\) *)

(*     module M   = Map.Make(Key) *)
(*     type e     = Orders.event (\* Key.t *\) *)
(*     type kind  = at (\* Arrow.t *\) *)
(*     type node  = {elem: e; successors: vertex list} *)
(*     and vertex = {kind: kind; node: node} *)
(*     type t     = node M.t *)
        
(*     let rec string_of_node  node = *)
(*       (Key.string_of node.elem) ^ ": " ^ (pr_list string_of_vertex node.successors) *)
(*     and string_of_vertex vertex = *)
(*       (string_of_arrow vertex.kind) ^ ">" ^ (string_of_node vertex.node) *)
(*     let elem_of v = (v.node).elem *)
(*     let adjacent_of v = (v.node).successors *)
(*     let mk_node e vs  = {elem = e; successors = vs} *)
(*     let mk_vertex kind node = {kind = kind; node = node} *)
(*     let add_node tbl e node = M.add e node tbl *)
(*     let add_vertex tbl e = tbl *)
(*     let mem tbl e = M.mem e tbl *)
(*     let find tbl e = M.find e tbl *)
(*     let connect tbl kind v1 v2 = tbl *)
(*     let mk_empty_successors () = [] *)
(*     let add_successor node vertex = {node with successors = vertex::node.successors} *)
(*     let add tbl kind (e1, e2) = (\* tbl *\) *)
(*       let node_e2,tbl = try (find tbl e2, tbl) with Not_found -> *)
(*         let node = mk_node e2 (mk_empty_successors ()) in *)
(*         let tbl  = add_node tbl e2 node in *)
(*         node, tbl in *)
(*       let node_e1 = try find tbl e1  with Not_found -> *)
(*         mk_node e1 (mk_empty_successors ()) in *)
(*       let vertex_e2 = mk_vertex kind node_e2 in *)
(*       let node_e1   = add_successor node_e1 vertex_e2 in *)
(*       let tbl = M.remove e1 tbl in *)
(*       let tbl = add_node tbl e1 node_e1 in *)
(*       tbl *)
(*     let add_list tbl xs = (\* failwith x_tbi *\) *)
(*       List.fold_left (fun tbl (kind,(e1,e2)) -> add tbl kind (e1,e2)) tbl xs *)
(*     let add_rels tbl xs = *)
(*       let xs = List.map (fun x -> split_components x) xs in *)
(*       add_list tbl xs *)
(*     let create () =  M.empty *)
(*     let vertex_eq v1 v2 = Key.eq (elem_of v1) (elem_of v2) *)
(*     let rec has_path_v v1 v2 = failwith x_tbi *)
(*       (\* List.fold_right (fun v acc -> (has_path_v v v2) || acc) (adjacent_of v1) *\) *)
(*       (\*                 (vertex_eq v1 v2) *\) *)
(*     let has_path_exc t e1 e2 = failwith x_tbi *)
(*       (\* has_path_v (find t e1) (find t e2) *\) *)
(*     let has_path t e1 e2 = failwith x_tbi *)
(*       (\* try has_path_v (find t e1) (find t e2) with Not_found -> false *\) *)
(*     let is_lt t e1 e2 = failwith x_tbi (\* has_path t e1 e2 *\) *)
(*     let is_gte t e1 e2 = not (is_lt t e1 e2) *)
(*     let is_lt_opt t e1 e2 =  *)
(*       try Some (has_path_exc t e1 e2) with Not_found -> None *)
(*     let is_gte_opt t e1 e2 =  *)
(*       try Some (not (has_path_exc t e1 e2)) with Not_found -> None *)
(*         (\* val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *\) *)
(*     let string_of tbl = M.fold (fun key node acc -> *)
(*         (Key.string_of key) ^ ":" ^ (string_of_node node) *)
(*         ^ "\n" ^ acc *)
(*       ) tbl ""  *)
(*   end *)

(* ====================  DAG  =========================== *)
module type DAG_TYPE =
sig
  type vertex 
  type arrow_kind
  type t

  val create: unit -> t
end

(* Orders DAG *)
module Make_DAG (Orders: GORDERS_TYPE) (Key: DAG_KEY_TYPE): DAG_TYPE =
struct
  module Key = Key(Orders)
  (* vertex == Key.t == Orders.event *)
  type vertex     = Orders.event
  type arrow_kind = HB | CB
  type elem       = {arrow: arrow_kind ; vertex: vertex}
  type data       = elem list

  module M = Map.Make(Key)
  type t   = data M.t

  (* PRINTERS *)
  let string_of_arrow_kind arrow_kind =
    match arrow_kind with
    | HB -> "-->"
    | CB -> "->>"
  let string_of_vertex = Orders.string_of_event
  let string_of_elem e = (string_of_arrow_kind e.arrow) ^ (string_of_vertex e.vertex)
  let string_of_data   = pr_list string_of_elem
  let string_of tbl    = M.fold (fun key data acc ->
      (Key.string_of key) ^ ":" ^ (string_of_data data)
      ^ "\n" ^ acc
    ) tbl ""

  (* EQUALITIES *)
  let eq_arrow (a1: arrow_kind) (a2: arrow_kind) =
    match a1,a2 with
    | HB,HB | CB,CB -> true | _,_ -> false
  let eq_vertex (v1: vertex) (v2: vertex) = Key.eq v1 v2
  let eq_elem (e1:elem) (e2:elem) =
    (eq_arrow e1.arrow e2.arrow) && (eq_vertex e1.vertex e2.vertex)
  
  (* QUERIES *)
  let find tbl vertex = M.find vertex tbl
  let mem tbl vertex  = M.mem vertex tbl
  let data_mem lst data = List.exists (eq_elem data) lst
  let exists tbl key data =
    try
      let edata = find tbl key in
      data_mem edata data
    with Not_found -> false
  
  (* MAKERS *)
  let create ()   = M.empty
  let mk_empty_data () : data = []
  let mk_vertex e = e
  let mk_elem a v = {arrow = a; vertex = v}

  (* UPDATES *)
  let add_vertex tbl key data = M.add key data tbl
  let update_data tbl key data =
    let existing_data = try (find tbl key) 
      with Not_found -> mk_empty_data () in
    add_vertex tbl key (data::existing_data)
  let connect tbl arrow vertex1 vertex2 =
    let tbl = if mem tbl vertex2 then tbl
      else add_vertex tbl vertex2 (mk_empty_data ()) in
    let new_data = mk_elem arrow (mk_vertex vertex2) in
    update_data tbl vertex1 new_data
  let connect_list tbl xs = 
      List.fold_left (fun tbl (kind,(e1,e2)) -> connect tbl kind e1 e2) tbl xs

  let has_path tbl v1 v2 =
    try
      let rec helper key =
        let data = find tbl key in
        if (data_mem data (mk_elem HB v2)) then true
        else List.exists (fun el -> helper el.vertex) data in
      helper v1
    with Not_found -> false
  
end;;
