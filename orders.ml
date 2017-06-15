#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module SC = Sesscommons

let event_rel_id: string option ref = ref None
let hb_rel_id: string option ref = ref None
let hbp_rel_id: string option ref = ref None
let cb_rel_id: string option ref = ref None

module type VAR_TYPE =
sig
  type t
  val string_of : t -> string
  val eq : t -> t -> bool
end;;

module Var (Form: SC.Message_type) =
struct
  type t = Form.var
  let string_of = Form.print_var
  let eq = Form.eq_var
end

module GOrders_Base  (Var: VAR_TYPE) =
struct
  (* type role *)
  (* type chan *)
  (* type suid *)

  type role = Var.t
  type chan = Var.t
  type suid = Var.t

  
  (* type event *)
  (* type transmission *)

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
  
end;;

module type GORDERS_TYPE =
  functor (Var: VAR_TYPE) ->
sig
  include (module type of GOrders_Base(Var))

  val string_of_suid : suid -> string
  val string_of_role : role -> string
  val string_of_chan : chan -> string
  val string_of_event : event -> string
  val string_of_transmission : transmission -> string

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

  val is_cb  : assrt -> bool
  val is_hb  : assrt -> bool
  val is_and  : assrt -> bool
  val is_or  : assrt -> bool
  val is_bot : assrt -> bool
  val get_events_unsafe : assrt -> event * event
  val get_suid : event -> suid
  val get_and_value : assrt -> assrt * assrt
  val get_or_value  : assrt -> assrt * assrt

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
  module GB = GOrders_Base(Var)
  include GB

  let string_of_role = Var.string_of
  let string_of_chan = Var.string_of
  let string_of_suid = Var.string_of
  let string_of_event e = (string_of_role e.role) ^ "^" ^(string_of_suid e.uid)
  let string_of_transmission e = (string_of_role e.sender) ^ "-" ^ (string_of_suid e.uid) ^ "->" ^ (string_of_role e.receiver)

  let string_of e1 =
    let rec helper e1 = 
      match e1 with
      | Event e  -> "(" ^ string_of_event e ^ ")"
      | NEvent e -> "not("^ (string_of_event e) ^ ")"
      | Transm t -> string_of_transmission t
      | Order (HBe e) -> "(" ^ (string_of_event e.hbe_event1) ^ " <_HBe " ^ (string_of_event e.hbe_event2) ^ ")"
      | Order (HBt t) -> "(" ^ (string_of_transmission t.hbt_transmission1) ^ " <_HBt " ^ (string_of_transmission t.hbt_transmission2) ^ ")"
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

  let is_and assrt =
    match assrt with
    | And _ -> true
    | _ -> false

  let is_or assrt =
    match assrt with
    | Or _ -> true
    | _ -> false

  let is_bot assrt =
    match assrt with
    | Bot -> true
    | _ -> false

  let get_events_unsafe assrt =
    match assrt with
    | Order (HBe hbe) -> hbe.hbe_event1, hbe.hbe_event2
    | Order (CBe cbe) -> cbe.cbe_event1, cbe.cbe_event2
    | _ -> failwith "Expecting a HB or CB relation"

  let get_suid (ev:event) = ev.uid

  let get_and_value assrt =
    match assrt with
    | And typ -> typ.and_assrt1, typ.and_assrt2 
    | _ -> failwith "Expecting an And order relation"

  let get_or_value assrt =
    match assrt with
    | Or typ -> typ.or_assrt1, typ.or_assrt2 
    | _ -> failwith "Expecting an Or order relation"

  (* (\* Transform from assrt orders -> pure formula *\) *)
  (* let rec trans_orders_to_pure_formula (orders:assrt) pos = match orders with *)
  (*   | And and_type ->  *)
  (*        let and_head = and_type.and_assrt1 in *)
  (*        let and_tail = and_type.and_assrt2 in *)
  (*        let form1 = trans_orders_to_pure_formula and_head pos in *)
  (*        let form2 = trans_orders_to_pure_formula and_tail pos in *)
  (*        let res = Form.join_conjunctions ([]@form1@form2) in *)
  (*        [res] *)
  (*    | Or or_type -> failwith "Disjunctions not allowed"  *)
  (*    | Event e -> *)
  (*        begin match !event_rel_id with  *)
  (*        | Some rel_id -> *)
  (*            let role = e.role in *)
  (*            let p_form = Form.mk_exp_rel rel_id [(role, pos)] pos in *)
  (*            [p_form] *)
  (*        | None -> [] *)
  (*        end *)
  (*    | Order order -> *)
  (*      begin *)
  (*       match order with *)
  (*       | HBe hbe ->  *)
  (*           begin match !hbp_rel_id with *)
  (*           | Some rel_id -> *)
  (*               let hbe_role1 = hbe.hbe_event1.role in *)
  (*               let hbe_role2 = hbe.hbe_event2.role in *)
  (*               let var1 = (hbe_role1, pos) in *)
  (*               let var2 = (hbe_role2, pos) in *)
  (*               let p_form = Form.mk_exp_rel rel_id [var1; var2] pos in *)
  (*               [p_form] *)
  (*           | None -> [] *)
  (*           end *)
  (*       | CBe cbe -> *)
  (*           begin match (!cb_rel_id) with *)
  (*           | Some rel_id -> *)
  (*               let cbe_role1 = cbe.cbe_event1.role in *)
  (*               let cbe_role2 = cbe.cbe_event2.role in *)
  (*               let var1 = (cbe_role1, pos) in *)
  (*               let var2 = (cbe_role2, pos) in *)
  (*               let p_form = Form.mk_exp_rel rel_id [var1; var2] pos in *)
  (*               [p_form] *)
  (*           | None ->  [] *)
  (*           end *)
  (*       | _ -> [] *)
  (*      end *)
  (*    | _ -> [] *)

end ;;

(* module type TRANS_ORDERS_TYPE = *)
(* sig *)
(*   include GORDERS_TYPE *)
(*   include SC.Message_type *)

(*   val trans_orders_to_pure_formula : assrt -> VarGen.loc -> pure_formula list *)
(* end *)

module Orders2Core (* (Orders: GORDERS_TYPE) *) (Form: SC.Message_type) =
struct
  (* module Var = Var(Form) *)
  module Ord = GOrders(Var(Form))
  (* module Ord = GOrders ( struct *)
  (*     type t = Form.var *)
  (*     let string_of = Form.print_var *)
  (*     let eq = Form.eq_var *)
  (*   end ) *)
  (* include Ord *)
  (* include Form *)
    (* Transform from assrt orders -> pure formula *)
  let rec trans_orders_to_pure_formula (orders:Ord.assrt) pos = (* failwith x_tbi *)
    match orders with
    | Ord.And and_type ->
         let and_head = and_type.Ord.and_assrt1 in
         let and_tail = and_type.Ord.and_assrt2 in
         let form1 = trans_orders_to_pure_formula and_head pos in
         let form2 = trans_orders_to_pure_formula and_tail pos in
         let res = Form.join_conjunctions ([]@form1@form2) in
         [res]
     | Ord.Or or_type -> failwith "Disjunctions not allowed"
     | Ord.Event e ->
         begin match !event_rel_id with
         | Some rel_id ->
             let role = e.role in
             let p_form = Form.mk_exp_rel rel_id [(role, pos)] pos in
             [p_form]
         | None -> []
         end
     | Ord.Order order ->
       begin
        match order with
        | Ord.HBe hbe ->
            begin match !hbp_rel_id with
            | Some rel_id ->
                let hbe_role1 = hbe.Ord.hbe_event1.role in
                let hbe_role2 = hbe.Ord.hbe_event2.role in
                let var1 = (hbe_role1, pos) in
                let var2 = (hbe_role2, pos) in
                let p_form = Form.mk_exp_rel rel_id [var1; var2] pos in
                [p_form]
            | None -> []
            end
        | Ord.CBe cbe ->
            begin match (!cb_rel_id) with
            | Some rel_id ->
                let cbe_role1 = cbe.Ord.cbe_event1.role in
                let cbe_role2 = cbe.Ord.cbe_event2.role in
                let var1 = (cbe_role1, pos) in
                let var2 = (cbe_role2, pos) in
                let p_form = Form.mk_exp_rel rel_id [var1; var2] pos in
                [p_form]
            | None ->  []
            end
        | _ -> []
       end
     | _ -> []

end
  
(* ==================== KEY =========================== *)
module type DAG_KEY_TYPE =
(* functor (Orders : GORDERS_TYPE) -> *)
  functor (Var : VAR_TYPE) ->
sig
  type t = GOrders(Var).event

  val eq: t ->  t -> bool
  val compare: t ->  t -> int
  val string_of: t -> string
end;;

module Event  : DAG_KEY_TYPE =
  functor (Var : VAR_TYPE) ->
  (* functor (Orders: GORDERS_TYPE) -> *)
struct
  (* type t = Orders.event *)
  module Orders = GOrders(Var)
  type t = Orders.event

  let eq e1 e2      = Orders.eq_event e1 e2
  let string_of e   = Orders.string_of_event e
  let compare e1 e2 = String.compare (string_of e1) (string_of e2)
end;;

 
(* ==================== VERTEX =========================== *)
module type ELEM_TYPE =
  (* functor (Param : VAR_TYPE) -> *)
sig
  type t 

  val eq: t ->  t -> bool
  val compare: t ->  t -> int
  val string_of: t -> string
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

module type LIST_TYPE =
 functor (Elem: ELEM_TYPE) ->
sig
  type t = Elem.t

  val eq: t ->  t -> bool
  val compare: t ->  t -> int
  val string_of: t -> string
  val string_of_list: t list -> string
  val contains:  t list -> t -> bool
  val unique  :  t list -> t list
  val union   :  t list -> t list -> t list
  val intersect: t list -> t list -> t list
  val is_empty : t list -> bool
  val mk_empty : unit -> t list
  val mk_singleton: t   -> t list
end;;


module DList  : LIST_TYPE =
  functor (Elem: ELEM_TYPE) ->
struct
  type t = Elem.t

  let eq = Elem.eq
  let string_of = Elem.string_of
  let string_of_list = pr_list string_of
  let compare   = Elem.compare
  let contains lst el = List.exists (eq el) lst
  let unique   lst    = List.fold_left (fun acc elem ->
      if (contains acc elem) then acc
      else elem::acc ) [] lst
  (* set union - no dupl *)
  let union l1 l2  = unique (l1@l2)
  (* set intersection - no dupl *)
  let intersect l1 l2 = unique (List.filter (contains l2) l1)
  let is_empty  (lst: t list) = List.length lst == 0
  let mk_empty (): t list = []
  let mk_singleton el = [el]
end;;

(* ====================  EDGE  =========================== *)
module Edge (Vertex: LIST_TYPE) (Elem: ELEM_TYPE) =
struct
  module Vertex = Vertex(Elem)
  type t = {tail: Vertex.t; kind: arrow_kind; head: Vertex.t}
  and arrow_kind = HB | HBP | CB | Backward

  let string_of_arrow_kind arrow_kind =
    match arrow_kind with
    | HB  -> "-->"
    | HBP -> "-->"
    | CB -> "->>"
    | Backward -> "<-"
  let string_of e =  (Vertex.string_of e.tail) ^ (string_of_arrow_kind e.kind) ^ (Vertex.string_of e.head)
  let mk_edge t a h    = {tail = t; kind = a; head = h}
  let eq_arrow (a1: arrow_kind) (a2: arrow_kind) =
    match a1,a2 with
    | HB,HB | HBP,HBP | CB,CB | Backward,Backward -> true | _,_ -> false
  let eq e1 e2 = (Vertex.eq e1.tail e2.tail) && (Vertex.eq e1.head e2.head) && (eq_arrow e1.kind e2.kind)
  let compare e1 e2 = failwith x_tbi

  let get_head edge = edge.head
  let get_tail edge = edge.tail
  let get_kind edge = edge.kind

  let is_hb arrow =  match arrow with HB | HBP -> true | _ -> false
  let is_cb arrow =  match arrow with CB -> true | _ -> false
  let is_hb_edge edge =  is_hb (get_kind edge)
  let is_cb_edge edge =  is_cb (get_kind edge)

end;;

(* ====================  DAG  =========================== *)
module Make_DAG (Elem: ELEM_TYPE) (* : DAG_TYPE  *)=
struct
  module Vertex    = DList(Elem)
  module Key       = Vertex
  module Edge      = Edge(DList)(Elem)
  module Edge_list = DList(Edge)
  (* vertex == Key.t == Orders.event *)
  type vertex     = Vertex.t
  type key        = vertex
  type arrow_kind = Edge.arrow_kind (* HB | CB | Backward *)
  type elem       = {arrow: arrow_kind ; vertex: vertex}
  type elist      = elem list
  type data       = {predecessors: elist; successors: elist}
  type edge       = Edge.t (* {tail: vertex; kind: arrow_kind; head: vertex} *)

  module M = Map.Make(Key)
  type t   = data M.t

  (* PRINTERS *)
  let string_of_arrow_kind arrow_kind = Edge.string_of_arrow_kind arrow_kind
    (* match arrow_kind with *)
    (* | HB -> "-->" *)
    (* | CB -> "->>" *)
    (* | Backward -> "<-" *)
  let string_of_elem (e:elem): string = (string_of_arrow_kind e.arrow) ^ (Vertex.string_of e.vertex)
  let string_of_elist  = pr_list string_of_elem
  let string_of_data d = pr_pair (add_str "Predecessors" string_of_elist)
      (add_str "Successors" string_of_elist) (d.predecessors,d.successors)
  (* let string_of_edge e = (Vertex.string_of e.tail) ^ (string_of_arrow_kind e.kind) ^ (Vertex.string_of e.head) *)
  (* let string_of_edge_list = pr_list string_of_edge *)
  let string_of tbl    = M.fold (fun key data acc ->
      (Key.string_of key) ^ ":" ^ (string_of_data data) ^ "\n" ^ acc ) tbl ""

  (* EQUALITIES *)
  let eq_elem (e1:elem) (e2:elem) =
    (Edge.eq_arrow e1.arrow e2.arrow) && (Vertex.eq e1.vertex e2.vertex)

    (* MAKERS *)
  let create ()        = M.empty
  let mk_empty_data () = {successors = []; predecessors = [] }
  let mk_vertex e      = e
  let mk_elem a v      = {arrow = a; vertex = v}
  (* let mk_edge t a h    = {tail = t; kind = a; head = h} *)

  
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
  let is_weak arrow   = match arrow with |Edge.CB -> true | _ -> false
  let is_strong arrow = match arrow with |Edge.HB -> true | _ -> false

  (* MISC *)
  let filter tbl (fnc: key->data->bool) = M.filter fnc tbl
  let filter_elist fnc elist = List.filter fnc elist
  let fold fnc acc tbl = M.fold fnc tbl acc
  let fold_elist fnc acc elist = List.fold_left fnc acc elist
  let map fnc tbl = M.map fnc tbl
  let map_elist fnc elist = List.map fnc elist
  let get_keys tbl : vertex list = List.map fst (M.bindings tbl)
  let get_vertex data : vertex = data.vertex


  (* EDGE OPERATIONS *)
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
  let get_all_vertex_successors tbl vertex   = List.map get_vertex (get_all_successors tbl vertex)
  let get_all_vertex_predecessors tbl vertex = List.map get_vertex (get_all_predecessors tbl vertex)
      
  (* UPDATES *)
  let set_successors  succ data  = {data with successors = succ}
  let set_predecessors pred data = {data with predecessors = pred}
  let add_successors   succ data = {data with successors = succ::data.successors}
  let add_predecessors pred data = {data with predecessors = pred::data.predecessors}
 
  let add_vertex tbl key =
    let data = find_safe tbl key in
    M.add key data tbl
  let add_vertex_list tbl (lst:vertex list) = List.fold_left (fun acc key -> add_vertex acc key ) tbl lst
  let add_key tbl key data = M.add key data tbl
  (* overwrites existing successors/predecessors *)
  let set_successors_tbl   tbl key succ =
    let data = find_safe tbl key in
    add_key tbl key (set_successors succ data)
  let set_predecessors_tbl tbl key pred =
    let data = find_safe tbl key in
    add_key tbl key (set_predecessors pred data)
  (* adds on top of the existing successors/predecessors *)
  let add_successors_tbl tbl key succ =
    let data = find_safe tbl key in
    add_key tbl key (add_successors succ data)
  let add_predecessors_tbl tbl key pred =
    let data = find_safe tbl key in
    add_key tbl key (add_predecessors pred data)

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

  let connect_edge_list tbl xs =
    let xs = List.map (fun edge -> (Edge.get_kind edge,(Edge.get_tail edge,Edge.get_head edge))) xs in
    connect_list tbl xs

  (* removes an edge from tbl, updating its head predecessors, and its tail successors *)
  let remove_edge tbl (edge:edge) =
    let head_pred = get_predecessors tbl (Edge.get_head edge) in
    let head_pred = filter_elist (fun pred -> not (eq_elem (mk_elem Edge.Backward (Edge.get_tail edge)) pred)) head_pred in
    let tbl = set_predecessors_tbl tbl (Edge.get_head edge) head_pred in
    let tail_succ = get_successors tbl (Edge.get_tail edge) in
    let tail_succ = filter_elist (fun succ -> not (eq_elem (mk_elem (Edge.get_kind edge) (Edge.get_head edge)) succ)) tail_succ in
    let tbl = set_successors_tbl tbl (Edge.get_tail edge) tail_succ in
    tbl

  let remove_edge_list tbl (edges: edge list) =
    List.fold_left (fun acc_tbl edge -> remove_edge acc_tbl edge) tbl edges

  let add_edge tbl (edge:edge) = connect tbl (Edge.get_kind edge) (Edge.get_tail edge) (Edge.get_head edge)

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
        let rem = (Edge.mk_edge key elem.arrow elem.vertex)::rem in
        let strong_successors = (get_strong_successors tbl elem.vertex) in
        let to_add = map_elist (fun el -> Edge.mk_edge key el.arrow el.vertex) strong_successors in
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

  let infer_missing_hb inf_vertexes tbl guard_hb =
    let tail = Edge.get_tail guard_hb in
    let succ = get_all_vertex_successors tbl tail in
    let succ = Vertex.union succ (Vertex.mk_singleton tail) in
    let head = Edge.get_head guard_hb in
    let pred = get_all_vertex_predecessors tbl head in
    let pred = Vertex.union pred (Vertex.mk_singleton head) in
    let intersect = Vertex.intersect succ pred in
    if not(Vertex.is_empty intersect) then []
    else
      let succ_inf = Vertex.intersect succ inf_vertexes in
      let pred_inf = Vertex.intersect pred inf_vertexes in
      (* succ_inf X pred_inf *)
      let inferred_hbs =  List.fold_left (fun acc head ->
          List.fold_left (fun acc tail -> (Edge.mk_edge tail Edge.HB head)::acc) acc succ_inf
        ) [] pred_inf in      
      inferred_hbs

  let create_dag_and_infer inf_vertexes assume guards_hb =
    (* create dag with assume *)
    let tbl = connect_edge_list (create ()) assume in
    (* add the special vertexes to the dag if not already in *)
    let tbl = add_vertex_list tbl inf_vertexes in
    let tbl = norm_weak tbl inf_vertexes in
    (* infer missing edges such that the guards hold *)
    let inf_hbs = List.fold_left (fun acc hb -> [(hb,infer_missing_hb inf_vertexes tbl hb)]@acc) [] guards_hb in
    let ()  = y_binfo_hp (add_str "DAG" string_of) tbl in
    let ()  = y_ninfo_hp (add_str "edges" Edge_list.string_of_list) assume in
    let ()  = y_binfo_hp (add_str "guards" Edge_list.string_of_list) guards_hb in
    let ()  = y_binfo_hp (add_str "inferred" (pr_list (pr_pair Edge.string_of Edge_list.string_of_list))) inf_hbs in
    inf_hbs

  let create_dag_and_infer inf_vertexes assume guards_hb =
    let pr1 = Vertex.string_of_list in
    let pr2 = Edge_list.string_of_list  in
    let pr_out = pr_lst "\n" (pr_pair Edge.string_of Edge_list.string_of_list) in
    Debug.no_3 "create_dag_and_infer" pr1 pr2 pr2 pr_out create_dag_and_infer inf_vertexes assume guards_hb

end;;
