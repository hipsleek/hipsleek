#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module F = Iformula
module P = Ipure_D
module CF = Cformula
module CP = Cpure
module MCP = Mcpure

type transmission = TSend | TReceive

let string_of_seq  = ";;"
let unk_view_id = "SESS_TEMP"

let string_of_transmission t =
  match t with
  | TSend    -> "!"
  | TReceive -> "?"

let chan_id:  string option ref = ref None
let seq_id :  string option ref = ref None 
let trans_id: string option ref = ref None
let sess_id:  string option ref = ref None
let send_id:  string option ref = ref None
let recv_id:  string option ref = ref None
let sor_id:   string option ref = ref None

let set_prim_pred_id kind id =
  match kind with
    | Transmission -> trans_id := Some id
    | Session      -> sess_id := Some id
    | Channel      -> chan_id := Some id
    | Send         -> send_id := Some id
    | Receive      -> recv_id := Some id
    | Sequence     -> seq_id := Some id
    | SOr          -> sor_id := Some id
    | Protocol     -> ()
    | Projection   -> ()

let get_prim_pred_id pred_ref =
  match !pred_ref with
    | Some str -> str
    | None ->
      let () = report_warning no_pos "Session predicate not set" in
      unk_view_id

let get_prim_pred_id_by_kind kind = match kind with
  | Transmission -> get_prim_pred_id trans_id
  | Session      -> get_prim_pred_id sess_id
  | Channel      -> get_prim_pred_id chan_id
  | Send         -> get_prim_pred_id send_id
  | Receive      -> get_prim_pred_id recv_id
  | Sequence     -> get_prim_pred_id seq_id
  | SOr          -> get_prim_pred_id sor_id
  | Protocol     -> ""
  | Projection   -> ""

let get_session_kind_of_transmission t =
  match t with
  | TSend    -> Send
  | TReceive -> Receive

let rec string_of_param_list l = match l with
  | []        -> ""
  | h::[]     -> h
  | h::t      -> h ^ ", " ^ (string_of_param_list t)

(* ======= base formula for session type ====== *)
(* ============================================ *)
module type Message_type = sig
  type formula
  type pure_formula
  type h_formula
  type h_formula_heap
  type ho_param_formula
  type struc_formula
  type node
  type param
  type arg = node * ident * (ho_param_formula list) *
             (param list) * VarGen.loc

  val is_emp : formula -> bool
  val print  : (formula -> string) ref
  val print_h_formula  : (h_formula -> string) ref
  val mk_node: ?kind:session_kind option -> arg -> h_formula
  val mk_formula_heap_only:  h_formula -> VarGen.loc -> formula
  val mk_rflow_formula:  formula -> ?kind:ho_flow_kind -> ho_param_formula
  val mk_rflow_formula_from_heap:  h_formula -> ?kind:ho_flow_kind -> VarGen.loc -> ho_param_formula
  val mk_formula: pure_formula -> arg -> formula
  val mk_struc_formula: formula -> VarGen.loc -> struc_formula
  val mk_star: h_formula -> h_formula -> VarGen.loc -> h_formula
  val mk_or: formula -> formula -> VarGen.loc -> formula
  val mk_empty: unit -> h_formula
  val mk_seq_wrapper: h_formula -> VarGen.loc -> h_formula
  val choose_ptr: ?ptr:string -> unit -> node
  val set_param:  ident ->  VarGen.loc -> param
  val get_heap_ho_args: h_formula_heap -> ho_param_formula list
  val get_heap_pos: h_formula_heap -> VarGen.loc
  val get_heap_params: h_formula_heap -> param list
  val get_heap_session_kind: h_formula_heap -> session_kind option
  val get_h_formula_heap: h_formula -> h_formula_heap
  val get_formulae_from_ho_args: ho_param_formula list -> formula list
  val struc_formula_trans_heap_node: (h_formula -> h_formula) -> struc_formula -> struc_formula
  val transform_h_formula: (h_formula -> h_formula option)-> h_formula -> h_formula
  val update_temp_heap_name: h_formula -> h_formula
  val update_formula: formula -> formula

  val is_base_formula: formula -> bool
  val get_h_formula: formula -> h_formula
  val get_h_formula_from_ho_param_formula: ho_param_formula -> h_formula
  val get_formula_from_ho_param_formula: ho_param_formula -> formula
  val is_seq_node: h_formula -> bool
  val is_or_node: h_formula -> bool
  val is_star_node: h_formula -> bool
  val is_empty_node: h_formula -> bool
  val get_node: h_formula -> arg
  val get_or_formulae: formula -> formula list
  val get_star_formulae: h_formula -> h_formula list
  val get_star_pos: h_formula -> VarGen.loc
  val get_session_kind: h_formula -> session_kind option
  val get_param_id: param -> ident
  val get_node_id: node -> ident
  val get_formula_from_struc_formula: struc_formula -> formula

end;;

module IForm = struct
  type formula = F.formula
  type pure_formula = P.formula
  type h_formula = F.h_formula
  type h_formula_heap = F.h_formula_heap
  type ho_param_formula = F.rflow_formula
  type struc_formula = F.struc_formula
  type node = Globals.ident * VarGen.primed
  type param = Ipure.exp
  type arg = node * ident * (ho_param_formula list) *
             (param list) * VarGen.loc

  let is_emp f = failwith x_tbi
  let print    = F.print_formula
  (* ptr - pointer to heap, 
     name - name of heap struct
     ho - HO param 
  *)
  let print_h_formula = F.print_h_formula
  let mk_node ?kind:(skind = None) (ptr, name, ho, params, pos)  =
    let h = (F.mkHeapNode ptr name ho 0 false (*dr*) SPLIT0
               (P.ConstAnn(Mutable)) false false false None params [] None pos) in
    F.set_session_kind_h_formula h skind
    (* h *)

  let mk_formula_heap_only h pos =
    (* let h = mk_node (ptr, name, ho, params, pos) in *)
    F.formula_of_heap_1 h pos

  let mk_rflow_formula f ?kind:(k=NEUTRAL) =
    {  F.rflow_kind = k;
       F.rflow_base = f;
       F.rflow_session_kind = None;
    }

  let mk_rflow_formula_from_heap h ?kind:(k=NEUTRAL) pos =
    let f =  mk_formula_heap_only h pos in
    {  F.rflow_kind = k;
       F.rflow_base = f;
       F.rflow_session_kind = None;
    }

  let mk_formula pure (ptr, name, ho, params, pos)  =
    let h = mk_node (ptr, name, ho, params, pos) in
    F.mkBase_wo_flow h pure [] pos

  let mk_struc_formula formula pos =
    F.mkEBase [] [] [] formula None pos

  let mk_star h1 h2 pos =
    F.mkStar h1 h2 pos

  let choose_ptr ?ptr:(str="self") () =
    (str,Unprimed)

  let mk_or f1 f2 pos =
    F.mkOr f1 f2 pos

  let mk_empty () = F.HEmp

  let mk_seq_wrapper_node hform pos =
    let ptr = choose_ptr() in
    let name = get_prim_pred_id seq_id in
    let hemp = mk_empty () in
    let args = [hform; hemp] in
    let args = List.map (fun a -> mk_rflow_formula_from_heap a pos) args in
    let params = [] in
    mk_node ~kind:(Some Sequence) (ptr, name, args, params, pos)

  (* Normalize second HO argument of Sequence such that
     it contains no base/or/*/pred unless they are
     part of a Sequence:

     self::Seq{a, c}}
      |
      |
      V
     self::Seq{a, self::Seq{c, emp}}


     self::Seq{a, c or/* b}}
      |
      |
      V
     self::Seq{a, self::Seq{c or/* b, emp}}
  *)
  let mk_seq_wrapper hform pos =
    match hform with
      | F.HeapNode node ->
        (match node.F.h_formula_heap_session_kind with
          | Some k ->
            if (k <> Sequence)
            then
              mk_seq_wrapper_node hform pos
            else
              hform
          | None -> mk_seq_wrapper_node hform pos)
      | F.Star node -> mk_seq_wrapper_node hform pos
      | _ -> hform

  let set_param id pos = Ipure_D.Var((id,Unprimed), pos) 

  let get_heap_ho_args node =
    node.F.h_formula_heap_ho_arguments

  let get_heap_pos node =
    node.F.h_formula_heap_pos

  let get_heap_params node =
    node.F.h_formula_heap_arguments

  let get_heap_session_kind node =
    node.F.h_formula_heap_session_kind

  let get_h_formula_heap h_formula =
    match h_formula with
      | F.HeapNode n -> n
      | _ -> failwith "Should be a HeapNode"

  let get_formulae_from_ho_args ho_args =
    List.map (fun a -> a.F.rflow_base) ho_args

  let struc_formula_trans_heap_node fct struc_form =
    let fct_h = (fun x -> Some (fct x)) in
    let fct = (nonef, nonef, fct_h, (somef, somef, somef, somef, somef)) in
    F.transform_struc_formula fct struc_form

  let transform_formula fct f = F.transform_formula_simp fct f

  let transform_h_formula f_h h = F.transform_h_formula f_h h

  let rec update_formula f =
    let helper f = transform_formula update_temp_heap_name f in
    let helper f =
      let pr = !print in
      Debug.no_1 "update_formula" pr pr helper f in
    helper f

  and update_temp_heap_name hform =
    let helper hform =
      let f_h hform = match hform with
        | F.HeapNode node ->
            (match node.F.h_formula_heap_session_kind with
            | None -> Some (F.HeapNode node)
            | Some k ->
                let new_name = get_prim_pred_id_by_kind k in
                Some (F.HeapNode {node with F.h_formula_heap_name = new_name}))
        | _ -> None in
      transform_h_formula f_h hform
    in
    let helper hform =
      let pr = !print_h_formula in
      Debug.no_1 "update_temp_heap_name" pr pr helper hform in
    helper hform

  let is_base_formula formula =
    match formula with
      | F.Base f -> true
      | _ -> false

  let get_h_formula formula =
    match formula with
      | F.Base f -> f.F.formula_base_heap
      | _ -> failwith "Formula Base expected."

  let get_h_formula_from_ho_param_formula rflow_formula =
    let f = rflow_formula.F.rflow_base in
    get_h_formula f

  let get_formula_from_ho_param_formula rflow_formula =
    rflow_formula.F.rflow_base

  let is_seq_node h_formula =
    match h_formula with
      | F.HeapNode node -> (match node.F.h_formula_heap_session_kind with
                             | Some Sequence -> true
                             | _ -> false)
      | _ -> false

  let is_or_node h_formula =
    match h_formula with
      | F.HeapNode node -> (match node.F.h_formula_heap_session_kind with
                             | Some SOr -> true
                             | _ -> false)
      | _ -> false

  let is_star_node h_formula =
    match h_formula with
      | F.Star node -> true
      | _ -> false

  let is_empty_node h_formula = failwith x_tbi

  let get_node h_formula = failwith x_tbi

  let get_or_formulae formula = failwith x_tbi

  let get_star_formulae formula = failwith x_tbi

  let get_star_pos h_formula = failwith x_tbi

  let get_session_kind h_formula = failwith x_tbi

  let get_param_id param = failwith x_tbi

  let get_node_id node = failwith x_tbi

  let get_formula_from_struc_formula struc_formula = failwith x_tbi

end;;

module CForm = struct
  type formula = CF.formula
  type pure_formula = CP.formula
  type h_formula = CF.h_formula
  type h_formula_heap = CF.h_formula_view
  type ho_param_formula = CF.rflow_formula
  type struc_formula = CF.struc_formula
  type node = CP.spec_var
  type param = CP.spec_var
  type arg = node * ident * (ho_param_formula list) *
             (param list) * VarGen.loc

  let is_emp f = failwith x_tbi
  let print    = CF.print_formula
  let print_h_formula = CF.print_h_formula
  let mk_node ?kind:(skind = None) (ptr, name, ho, params, pos) =
    let h = CF.mkViewNode ptr name params pos in
    match h with
      | CF.ViewNode node -> CF.ViewNode {node with h_formula_view_ho_arguments = ho;
                                                   h_formula_view_session_kind = skind}
      | _ -> failwith "Not a ViewNode."

  let mk_formula_heap_only h pos =
    CF.formula_of_heap h pos

  let mk_rflow_formula f ?kind:(k=NEUTRAL) =
    { CF.rflow_kind = k;
      CF.rflow_base = f;
    }

  let mk_rflow_formula_from_heap h ?kind:(k=NEUTRAL) pos =
    let f = mk_formula_heap_only h pos in
    { CF.rflow_kind = k;
      CF.rflow_base = f;
    }

  let mk_formula pure (ptr, name, ho, params, pos) =
    let h = mk_node (ptr, name, ho, params, pos) in
    let mix_formula = MCP.OnePF pure in
    CF.mkBase_simp h mix_formula

  let mk_struc_formula formula pos =
    CF.mkEBase formula None pos

  let mk_star h1 h2 pos =
    CF.mkStarH h1 h2 pos

  let choose_ptr ?ptr:(str="self") () =
    CP.SpecVar(UNK,str,Unprimed)

  let mk_or f1 f2 pos =
    CF.mkOr f1 f2 pos

  let mk_empty () = CF.HEmp

  let mk_seq_wrapper hform pos = hform

  let set_param id pos = CP.SpecVar(UNK,id,Unprimed)

  let get_heap_ho_args node =
    node.CF.h_formula_view_ho_arguments

  let get_heap_pos node =
    node.CF.h_formula_view_pos

  let get_heap_params node =
    node.CF.h_formula_view_arguments

  let get_heap_session_kind node = failwith x_tbi

  let get_h_formula_heap h_formula =
    match h_formula with
      | CF.ViewNode n -> n
      | _ -> failwith "CF.ViewNode expected."

  let get_formulae_from_ho_args ho_args = failwith x_tbi

  let struc_formula_trans_heap_node fct_h struc_form =
    let fct_h = (fun x -> Some (fct_h x)) in
    let fct = nonef, nonef, fct_h, (somef, somef, somef, somef, somef) in
    CF.transform_struc_formula fct struc_form

  let transform_h_formula f_h h = CF.transform_h_formula f_h h

  let update_temp_heap_name hform = hform

  let update_formula f = f

  let get_node h_formula =
    match h_formula with
      | CF.ViewNode node -> (node.CF.h_formula_view_node,
                             node.CF.h_formula_view_name,
                             node.CF.h_formula_view_ho_arguments,
                             node.CF.h_formula_view_arguments,
                             node.CF.h_formula_view_pos)
      | _ -> failwith "CF.ViewNode expected."

  let get_or_formulae formula =
    match formula with
      | CF.Or f -> [f.CF.formula_or_f1; f.CF.formula_or_f2]
      | _ -> failwith "CF.Or expected."

  let get_star_formulae h_formula =
    match h_formula with
      | CF.Star hf -> [hf.CF.h_formula_star_h1; hf.CF.h_formula_star_h2]
      | _ -> failwith "CF.Star expected."

  let get_star_pos h_formula =
    match h_formula with
      | CF.Star hf -> hf.CF.h_formula_star_pos
      | _ -> failwith "CF.Star expected."

  let get_session_kind h_formula =
    match h_formula with
      | CF.ViewNode node -> node.CF.h_formula_view_session_kind
      | _ -> failwith "CF.ViewNode expected."

  let get_param_id param =
    match param with
      | CP.SpecVar sv -> let (t, n, p) = sv in
                         n

  let get_node_id node = get_param_id node

  let get_formula_from_struc_formula struc_formula =
    match struc_formula with
      | CF.EBase base -> base.CF.formula_struc_base
      | _ -> failwith "CF.EBase expected."

  let is_base_formula formula =
    match formula with
      | CF.Base f -> true
      | _ -> false

  let get_h_formula formula =
    match formula with
      | CF.Base f -> f.CF.formula_base_heap
      | _ -> failwith "Formula Base expected."

  let get_h_formula_from_ho_param_formula rflow_formula =
    let f = rflow_formula.CF.rflow_base in
    get_h_formula f

  let get_formula_from_ho_param_formula rflow_formula =
    rflow_formula.CF.rflow_base

  let is_seq_node h_formula =
    match h_formula with
      | CF.ViewNode node -> (match node.CF.h_formula_view_session_kind with
                              | Some Sequence -> true
                              | _ -> false)
      | _ -> false

  let is_or_node h_formula =
    match h_formula with
      | CF.ViewNode node -> (match node.CF.h_formula_view_session_kind with
                              | Some SOr -> true
                              | _ -> false)
      | _ -> false

  let is_star_node h_formula =
    match h_formula with
      | CF.Star node -> true
      | _ -> false

  let is_empty_node h_formula =
    match h_formula with
      | CF.HEmp -> true
      | _ -> false

end;;

(* inst for iformula & cformula *)
module Protocol_base_formula =
  functor  (Msg: Message_type) ->
  struct
    include Msg
    type t = Msg.formula
    type a = ident * ident * VarGen.loc
    type base = {
      protocol_base_formula_sender   : ident;
      protocol_base_formula_receiver : ident;
      protocol_base_formula_message  : t;
      protocol_base_formula_pos      : VarGen.loc;
    }

    let base_type = Protocol

    let print_message f = !Msg.print f.protocol_base_formula_message

    let string_of_session_base f =
      f.protocol_base_formula_sender ^ " -> " ^ f.protocol_base_formula_receiver ^ " : " ^ (print_message f)

    let mk_base (sender, receiver, pos) formula = {
      protocol_base_formula_sender    = sender;
      protocol_base_formula_receiver  = receiver;
      protocol_base_formula_message   = formula;
      protocol_base_formula_pos       = pos;
    }

    let trans_base base =
      let ptr = Msg.choose_ptr ~ptr:session_msg_id () in
      let name = get_prim_pred_id trans_id in
      let args = [Msg.mk_rflow_formula base.protocol_base_formula_message ~kind:NEUTRAL] in
      let params = [base.protocol_base_formula_sender; base.protocol_base_formula_receiver] in
      let params = List.map (fun a -> Msg.set_param a base.protocol_base_formula_pos) params in
      Msg.mk_node (ptr, name, args, params, base.protocol_base_formula_pos)

    let get_base_pos base = base.protocol_base_formula_pos

    let is_session_base h_formula = failwith x_tbi

    let trans_h_formula_to_session_base h_formula =
      let node = Msg.get_h_formula_heap h_formula in
      let participants = List.map (fun a -> Msg.get_param_id a) (Msg.get_heap_params node) in
      let sender = List.nth participants 0 in
      let receiver = List.nth participants 1 in
      let pos = Msg.get_heap_pos node in
      let f = let form_list = Msg.get_formulae_from_ho_args (Msg.get_heap_ho_args node) in
              List.nth form_list 0 in
      mk_base (sender, receiver, pos) f

  end;;

(* inst for iformula & cformula *)
module Projection_base_formula =
  functor  (Msg: Message_type) ->
  struct
    include Msg
    type t = Msg.formula
    type a = transmission * ident * VarGen.loc
    type base = {
      projection_base_formula_op      : transmission;
      projection_base_formula_channel : ident;
      projection_base_formula_message : t;
      projection_base_formula_pos     : VarGen.loc;
    }

    let base_type = Projection

    let print_message f = !Msg.print f.projection_base_formula_message

    let string_of_session_base f =
      (f.projection_base_formula_channel) ^
      (string_of_transmission f.projection_base_formula_op) ^
      "(" ^ (print_message f) ^ ")"

    let mk_base (transmission, channel, pos) formula = {
      projection_base_formula_op      = transmission;
      projection_base_formula_channel = channel;
      projection_base_formula_message = formula;
      projection_base_formula_pos     = pos;
    }

    let trans_base base =
      let ptr = Msg.choose_ptr ~ptr:base.projection_base_formula_channel () in
      let tkind = get_session_kind_of_transmission base.projection_base_formula_op in
      let name = get_prim_pred_id_by_kind tkind in
      let args = match base.projection_base_formula_op with
        | TSend -> [Msg.mk_rflow_formula base.projection_base_formula_message ~kind:INFLOW]
        | TReceive -> [Msg.mk_rflow_formula base.projection_base_formula_message ~kind:OUTFLOW] in
      let params = [] in
      Msg.mk_node ~kind:(Some tkind) (ptr, name, args, params, base.projection_base_formula_pos)

    let get_base_pos base = base.projection_base_formula_pos

    let is_session_base h_formula =
      match Msg.get_session_kind h_formula with
        | Some Send -> true
        | Some Receive -> true
        | _ -> false

    let trans_h_formula_to_session_base h_formula =
      let () = print_endline "in session base transf" in
      let (ptr, name, args, params, pos) = Msg.get_node h_formula in
      let () = print_endline "after get_node" in
      let channel = Msg.get_node_id ptr in
      let () = print_endline "after get_node_id" in
      let f = Msg.get_formula_from_ho_param_formula (List.nth args 0) in
      let () = print_endline "after get_form" in
      let transmission = match (Msg.get_session_kind h_formula) with
        | Some Send -> TSend
        | Some Receive -> TReceive
        | _ -> failwith "Not a valid transmission type." in
      mk_base (transmission, channel, pos) f

    let trans_h_formula_to_session_seq h_formula = failwith x_tbi

  end;;

module type Session_base =
sig
  include Message_type
  type t
  type a
  type base

  val base_type : session_kind
  val string_of_session_base : base -> string
  val mk_base : a -> t -> base
  val trans_base : base -> h_formula
  val get_base_pos : base -> VarGen.loc
  val is_session_base : h_formula -> bool
  val trans_h_formula_to_session_base : h_formula -> base
end;;

(* ============== session type ================ *)
(* ============================================ *)
module Make_Session (Base: Session_base) = struct
  type t = Base.base
  
  type session =
    | SSeq  of session_seq_formula
    | SOr   of session_or_formula
    | SStar of session_star_formula
    | SBase of session_base
    | SEmp

  and session_base =
    | Base of t
    | Predicate of session_predicate

  and session_seq_formula = {
    session_seq_formula_head: session;
    session_seq_formula_tail: session;
    session_seq_formula_pos:  loc;
  }

  and session_or_formula = {
    session_seq_formula_or1: session;
    session_seq_formula_or2: session;
    session_seq_formula_pos:  loc;
  }

  and session_star_formula = {
    session_seq_formula_star1: session;
    session_seq_formula_star2: session;
    session_seq_formula_pos:  loc;
  }

  and session_predicate = {
    session_predicate_name: ident;
    session_predicate_ho_vars: (ho_flow_kind * ident * ho_split_kind) list;
    session_predicate_params: ident list;
    session_predicate_pos: loc;
  }

  let rec string_of_session s =
    (string_of_one_session s) ^ "\n"

  and string_of_one_session s = match s with
    | SSeq s  -> string_of_session_seq s
    | SOr s   -> string_of_session_or s
    | SStar s -> string_of_session_star s
    | SBase s -> string_of_session_base s
    | SEmp    -> string_of_session_emp ()

  and string_of_session_base s = match s with
    | Base b -> Base.string_of_session_base b
    | Predicate p -> string_of_session_predicate p

  and string_of_session_emp () = "emp"

  and string_of_session_seq s =
    "(" ^ string_of_one_session s.session_seq_formula_head ^ ") " ^
    string_of_seq ^
    " (" ^ string_of_one_session s.session_seq_formula_tail ^ ")"

  and string_of_session_or s =
    "(" ^ string_of_one_session s.session_seq_formula_or1 ^ ") " ^
    "or" ^
    " (" ^ string_of_one_session s.session_seq_formula_or2

  and string_of_session_star s =
    "(" ^ string_of_one_session s.session_seq_formula_star1 ^ ") " ^
    "*" ^
    " (" ^ string_of_one_session s.session_seq_formula_star2

  and string_of_session_predicate s =
    s.session_predicate_name ^ "{}" ^ "<" ^ (string_of_param_list s.session_predicate_params) ^ ">"

  let mk_base a b = Base (Base.mk_base a b)

  and mk_session_seq_formula session1 session2 loc = SSeq {
      session_seq_formula_head = session1;
      session_seq_formula_tail = session2;
      session_seq_formula_pos  = loc;
    }

  and mk_session_or_formula session1 session2 loc = SOr {
    session_seq_formula_or1 = session1;
    session_seq_formula_or2 = session2;
    session_seq_formula_pos = loc;
    }

  and mk_session_star_formula session1 session2 loc = SStar {
    session_seq_formula_star1 = session1;
    session_seq_formula_star2 = session2;
    session_seq_formula_pos   = loc;
    }

  and mk_session_predicate name ho_vars params loc = Predicate {
    session_predicate_name = name;
    session_predicate_ho_vars = ho_vars;
    session_predicate_params = params;
    session_predicate_pos = loc;
  }

  let mk_seq_node h1 h2 pos  =
    let ptr = Base.choose_ptr () in (* decide which name should be given here *)
    let name = get_prim_pred_id seq_id in
    let h2 = Base.mk_seq_wrapper h2 pos in
    let args = [h1; h2] in
    let args = List.map (fun a -> Base.mk_rflow_formula_from_heap a pos) args in
    let params = [] in
    (* let a = (sv, name, args, params, pos) in *)
    Base.mk_node ~kind:(Some Sequence) (ptr, name, args, params, pos)
    (* failwith x_tbi *)

  and mk_star_node h1 h2 pos =
    Base.mk_star h1 h2 pos

  and mk_or_node h1 h2 pos =
    let f1 = Base.mk_formula_heap_only h1 pos in
    let f2 = Base.mk_formula_heap_only h2 pos in
    let or_node = Base.mk_or f1 f2 pos in
    (* why doesn't it work without ~kind, which is optional? *)
    let rflow_form = (Base.mk_rflow_formula or_node ~kind:NEUTRAL) in
    let ptr = Base.choose_ptr () in
    let name = get_prim_pred_id sor_id in
    let args = [rflow_form] in
    let params = [] in
    Base.mk_node ~kind:(Some SOr) (ptr, name, args, params, pos)

  and mk_predicate_node p =
    let ptr = Base.choose_ptr () in
    let name = p.session_predicate_name in
    let args = [] in (* not using HO preds here *)
    let pos = p.session_predicate_pos in
    let params = p.session_predicate_params in
    let params = List.map (fun a -> Base.set_param a pos) params in
    Base.mk_node (ptr, name, args, params, pos)

  let trans_from_session s =
    let rec helper s = match s with
    | SSeq s  ->
        let arg1 = helper s.session_seq_formula_head in
        let arg2 = helper s.session_seq_formula_tail in
        mk_seq_node arg1 arg2 s.session_seq_formula_pos
      (* (\* node, view-name, ho-args, args *\) *)
      (* Base.mkFNode sv !seq_id [arg1;arg2] []
      failwith x_tbi *)
    | SOr s   ->
        let arg1 = helper s.session_seq_formula_or1 in
        let arg2 = helper s.session_seq_formula_or2 in
        mk_or_node arg1 arg2 s.session_seq_formula_pos
    | SStar s ->
        let arg1 = helper s.session_seq_formula_star1 in
        let arg2 = helper s.session_seq_formula_star2 in
        mk_star_node arg1 arg2 s.session_seq_formula_pos
    | SBase s -> (match s with
        | Base b -> Base.trans_base b
        | Predicate p -> mk_predicate_node p)
    | SEmp    -> Base.mk_empty () in
    helper s

  let trans_from_session s =
    let pr = string_of_session in
    let pr2 = !Base.print_h_formula in
    Debug.no_1 "trans_from_session" pr pr2 trans_from_session s

  let get_pos s = match s with
    | SSeq s  -> s.session_seq_formula_pos
    | SOr s   -> s.session_seq_formula_pos
    | SStar s -> s.session_seq_formula_pos
    | SBase s -> (match s with
        | Base b -> Base.get_base_pos b
        | Predicate p -> p.session_predicate_pos)
    | SEmp    -> no_pos

  let mk_formula_heap_only = Base.mk_formula_heap_only

  let mk_sess_h_formula h_form pos =
    let f = Base.mk_formula_heap_only h_form pos in
    let rflow_form = (Base.mk_rflow_formula f ~kind:NEUTRAL) in
    let ptr = Base.choose_ptr () in
    let name = get_prim_pred_id sess_id in
    let args = [rflow_form] in
    let params = [] in
    Base.mk_node  ~kind:(Some Session) (ptr, name, args, params, pos)

  let mk_struc_formula_from_session_and_formula s form_orig =
    let h_form = trans_from_session s in
    let pos = get_pos s in
    let h_form = mk_sess_h_formula h_form pos in
    let fct h = Base.mk_star h h_form pos in
    Base.struc_formula_trans_heap_node fct form_orig

  let update_formula = Base.update_formula

  (* Get clean formula, without Sess{}. *)
  let trans_h_formula_to_session h_formula =
    let rec helper h_formula =
      if (Base.is_seq_node h_formula)
      then
        let () = print_endline "detected seq" in
        let (ptr, name, args, params, pos) = Base.get_node h_formula in
        let h1 = Base.get_h_formula_from_ho_param_formula (List.nth args 0) in
        let h2 = Base.get_h_formula_from_ho_param_formula (List.nth args 1) in
        mk_session_seq_formula (helper h1) (helper h2) pos
      else
      if (Base.is_or_node h_formula)
      then
        let () = print_endline "detected or" in
        let (ptr, name, args, params, pos) = Base.get_node h_formula in
        let or_node = Base.get_formula_from_ho_param_formula (List.nth args 0) in
        let or_formulae = Base.get_or_formulae or_node in
        let h1 = Base.get_h_formula (List.nth or_formulae 0) in
        let h2 = Base.get_h_formula (List.nth or_formulae 1) in
        mk_session_or_formula (helper h1) (helper h2) pos
      else
      if (Base.is_star_node h_formula)
      then
        let () = print_endline "detected star" in
        let pos = Base.get_star_pos h_formula in
        let star_formulae = Base.get_star_formulae h_formula in
        let h1 = List.nth star_formulae 0 in
        let h2 = List.nth star_formulae 1 in
        mk_session_star_formula (helper h1) (helper h2) pos
      else
      if (Base.is_session_base h_formula)
      then
        let () = print_endline "detected base" in
        SBase (Base (Base.trans_h_formula_to_session_base h_formula))
      (* Can only be Predicate or empty heap at this point. *)
      else
      if (not (Base.is_empty_node h_formula))
      then
        let () = print_endline "detected pred" in
        let (ptr, name, args, params, pos) = Base.get_node h_formula in
        let params = List.map (fun a -> Base.get_param_id a) params in 
        SBase (mk_session_predicate name [] params pos)
      else
        let () = print_endline "detected empty?!" in
        SEmp in
    helper h_formula

  let trans_h_formula_to_session h_formula =
    let pr1 = !Base.print_h_formula in
    let pr2 = string_of_session in
    Debug.no_1 "trans_h_formula_to_session" pr1 pr2 trans_h_formula_to_session h_formula

  (* Session will look like Sess{...}. *)
  (* Strip the STAR with original formula and
   * strip Sess{} *)
  let trans_formula_to_session formula =
    if (Base.is_base_formula formula)
    then
      let h_formula = Base.get_h_formula formula in
      let (ptr, name, args, params, pos) = Base.get_node h_formula in
      (* Extract h_formula from Sess node. *)
      let h_formula = Base.get_h_formula_from_ho_param_formula (List.nth args 0) in
      (* Extract h_formula from STAR with original formula.
       * Should be second branch of star. *)
      (*let star_formulae = Base.get_star_formulae h_formula in
      let h_formula = List.nth star_formulae 1 in*)
      trans_h_formula_to_session h_formula
    else
      failwith "Formula Base expected."

  let trans_struc_formula_to_session struc_formula =
    let f = Base.get_formula_from_struc_formula struc_formula in
    trans_formula_to_session f

  let test_if_is struc_formula =
    let s = trans_struc_formula_to_session struc_formula in
    print_endline ("transformed: " ^ (string_of_session s))

end;;

(* =========== Protocol / Projection ========== *)
(* ============================================ *)

module IProtocol_base = Protocol_base_formula(IForm) ;;
module CProtocol_base = Protocol_base_formula(CForm) ;;
module IProjection_base = Projection_base_formula(IForm) ;;
module CProjection_base = Projection_base_formula(CForm) ;;

module IProtocol = Make_Session(IProtocol_base);;
module CProtocol = Make_Session(CProtocol_base);;

module IProjection = Make_Session(IProjection_base);;
module CProjection = Make_Session(CProjection_base);;

type session_type = ProtocolSession of IProtocol.session
                  | ProjectionSession of IProjection.session

let get_protocol session = 
  match session with
  | ProtocolSession s -> s
  | _ -> failwith "not a protocol formula"

let get_projection session =
  match session with
  | ProjectionSession s -> s
  | _ -> failwith "not a projection formula" 
