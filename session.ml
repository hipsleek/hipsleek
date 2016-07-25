#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module F = Iformula
module P = Ipure_D
module IP = Ipure
module CF = Cformula
module CP = Cpure
module MCP = Mcpure

type transmission = TSend | TReceive

let string_of_seq  = ";;"
let unk_view_id = "SESS_TEMP"

let session_fresh_id () = fresh_any_name session_msg_id_aux

let string_of_transmission t =
  match t with
  | TSend    -> "!"
  | TReceive -> "?"

(* prim predicates *)
let chan_id:  string option ref = ref None
let seq_id :  string option ref = ref None
let trans_id: string option ref = ref None
let sess_id:  string option ref = ref None
let send_id:  string option ref = ref None
let recv_id:  string option ref = ref None
let sor_id:   string option ref = ref None
let msg_id:   string option ref = ref None

let set_prim_pred_id kind id =
  match kind with
    | Sequence     -> seq_id := Some id
    | SOr          -> sor_id := Some id
    | Star         -> ()
    | Send         -> send_id := Some id
    | Receive      -> recv_id := Some id
    | Transmission -> trans_id := Some id
    | HVar         -> ()
    | Predicate    -> ()
    | Emp          -> ()
    | Session      -> sess_id := Some id
    | Channel      -> chan_id := Some id
    | Msg          -> msg_id := Some id

let get_prim_pred_id pred_ref =
  match !pred_ref with
    | Some str -> str
    | None ->
      let () = report_warning no_pos "Session predicate not set" in
      unk_view_id

let get_prim_pred_id_by_kind kind = match kind with
  | Sequence     -> get_prim_pred_id seq_id
  | SOr          -> get_prim_pred_id sor_id
  | Star         -> ""
  | Send         -> get_prim_pred_id send_id
  | Receive      -> get_prim_pred_id recv_id
  | Transmission -> get_prim_pred_id trans_id
  | HVar         -> ""
  | Predicate    -> ""
  | Emp          -> ""
  | Session      -> get_prim_pred_id sess_id
  | Channel      -> get_prim_pred_id chan_id
  | Msg          -> get_prim_pred_id msg_id

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
  type var
  type arg = node * ident * (ho_param_formula list) *
             (param list) * VarGen.loc

  val is_emp : formula -> bool
  val print  : (formula -> string) ref
  val print_h_formula  : (h_formula -> string) ref
  val mk_node: arg -> session_kind -> node_kind -> h_formula
  val mk_formula_heap_only:  h_formula -> VarGen.loc -> formula
  val mk_rflow_formula: ?kind:ho_flow_kind -> formula -> ho_param_formula
  val mk_rflow_formula_from_heap:  h_formula -> ?kind:ho_flow_kind -> VarGen.loc -> ho_param_formula
  val mk_formula: pure_formula -> arg -> session_kind -> node_kind -> formula
  val mk_struc_formula: formula -> VarGen.loc -> struc_formula
  val mk_star: h_formula -> h_formula -> VarGen.loc -> h_formula
  val mk_or: formula -> formula -> VarGen.loc -> formula
  val mk_empty: unit -> h_formula
  val mk_hvar: ident -> ident list -> h_formula
  val mk_seq_wrapper: h_formula -> VarGen.loc -> session_kind -> h_formula
  val choose_ptr: ?ptr:string -> unit -> node
  val set_param:  ident ->  VarGen.loc -> param

  val struc_formula_trans_heap_node: (h_formula -> h_formula) -> struc_formula -> struc_formula
  val transform_h_formula: (h_formula -> h_formula option)-> h_formula -> h_formula
  val update_temp_heap_name: h_formula -> h_formula
  val update_formula: formula -> formula
  val subst_param: (var * var) list -> param -> param
  val subst_formula: (var * var) list -> formula -> formula

  val is_base_formula: formula -> bool
  val get_h_formula: formula -> h_formula
  val get_h_formula_from_ho_param_formula: ho_param_formula -> h_formula
  val get_formula_from_ho_param_formula: ho_param_formula -> formula
  val get_node: h_formula -> arg
  val get_or_formulae: formula -> formula list
  val get_star_formulae: h_formula -> h_formula list
  val get_star_pos: h_formula -> VarGen.loc
  val get_node_kind: h_formula -> node_kind
  val get_param_id: param -> ident
  val get_node_id: node -> ident
  val get_formula_from_struc_formula: struc_formula -> formula
  val get_hvar: h_formula -> ident * ident list

end;;

module IForm = struct
  type formula = F.formula
  type pure_formula = P.formula
  type h_formula = F.h_formula
  type h_formula_heap = F.h_formula_heap
  type ho_param_formula = F.rflow_formula
  type struc_formula = F.struc_formula
  type var = Globals.ident * VarGen.primed
  type node = var
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
  let mk_node (ptr, name, ho, params, pos) sk nk =
    let h = (F.mkHeapNode ptr name ho 0 false (*dr*) SPLIT0
               (P.ConstAnn(Mutable)) false false false None params [] None pos) in
    F.set_session_kind_h_formula h sk nk

  let mk_formula_heap_only h pos =
    F.formula_of_heap_1 h pos

  let mk_rflow_formula ?kind:(k=NEUTRAL) f =
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

  let mk_formula pure (ptr, name, ho, params, pos) sk nk  =
    let h = mk_node (ptr, name, ho, params, pos) sk nk in
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

  let mk_hvar id ls = F.HVar(id, ls)

  let mk_seq_wrapper_node hform pos sk =
    let ptr = choose_ptr() in
    let name = get_prim_pred_id seq_id in
    let hemp = mk_empty () in
    let args = [hform; hemp] in
    let args = List.map (fun a -> mk_rflow_formula_from_heap a pos) args in
    let params = [] in
    mk_node (ptr, name, args, params, pos) sk Sequence

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
  let mk_seq_wrapper hform pos sk =
    match hform with
    | F.HeapNode node -> let fct si = let nk = si.node_kind in
                           (match nk with
                            | Sequence -> hform
                            | _ -> mk_seq_wrapper_node hform pos sk) in
      Gen.map_opt_def hform fct node.F.h_formula_heap_session_info
    | F.Star node -> mk_seq_wrapper_node hform pos sk
    | _ -> hform

  let set_param id pos = Ipure_D.Var((id,Unprimed), pos)

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
           let orig_node = Some (F.HeapNode node) in
                           let fct si = match si.node_kind with
                                          | Sequence | SOr | Send | Receive | Transmission
                                          | Session | Channel | Msg -> Some (F.HeapNode {node with F.h_formula_heap_name =
                                                                                         get_prim_pred_id_by_kind si.node_kind})
                                          | Star | HVar | Predicate | Emp -> orig_node in
                           Gen.map_opt_def orig_node fct node.F.h_formula_heap_session_info
        | _ -> None in
      transform_h_formula f_h hform
    in
    let helper hform =
      let pr = !print_h_formula in
      Debug.no_1 "update_temp_heap_name" pr pr helper hform in
    helper hform

  let subst_param  (sst: (var * var) list) p = IP.subst_exp sst p

  let subst_formula (sst: (var * var) list) f = F.subst_all sst f

  let is_base_formula formula =
    match formula with
      | F.Base f -> true
      | _ -> false

  let get_h_formula formula =
    match formula with
      | F.Base f -> f.F.formula_base_heap
      | F.Exists f -> f.F.formula_exists_heap
      | _ -> failwith (x_loc ^ ": Formula Base or Exists expected.")

  let get_h_formula_from_ho_param_formula rflow_formula =
    let f = rflow_formula.F.rflow_base in
    get_h_formula f

  let get_formula_from_ho_param_formula rflow_formula =
    rflow_formula.F.rflow_base

  let get_node_kind h_formula =
    match h_formula with
      | F.HeapNode node -> (match node.F.h_formula_heap_session_info with
                             | Some si -> si.node_kind
                             | None -> failwith (x_loc ^ ": Expected session information."))
      | F.Star node -> Star
      | F.HVar (sv, svl) -> HVar
      | F.HEmp -> Emp
      | _ -> failwith (x_loc ^ ": Not a valid heap formula for session.")

  let get_node h_formula =
    match h_formula with
      | F.HeapNode node -> (node.F.h_formula_heap_node,
                            node.F.h_formula_heap_name,
                            node.F.h_formula_heap_ho_arguments,
                            node.F.h_formula_heap_arguments,
                            node.F.h_formula_heap_pos)
      | _ -> failwith (x_loc ^ ": F.HeapNode expected.")

  let get_or_formulae formula =
    match formula with
      | F.Or f -> [f.F.formula_or_f1; f.F.formula_or_f2]
      | _ -> failwith (x_loc ^ ": F.Or expected.")

  let get_star_formulae h_formula =
    match h_formula with
      | F.Star hf -> [hf.F.h_formula_star_h1; hf.F.h_formula_star_h2]
      | _ -> failwith (x_loc ^ ": F.Star expected.")

  let get_star_pos h_formula =
    match h_formula with
      | F.Star hf -> hf.F.h_formula_star_pos
      | _ -> failwith (x_loc ^ ": F.Star expected.")

  let get_param_id param =
    match param with
      | P.Var v -> fst (fst v)
      | _ -> failwith (x_loc  ^ ": IPure.Var expected.")

  let get_node_id node = fst node

  let get_formula_from_struc_formula struc_formula =
    match struc_formula with
      | F.EBase base -> base.F.formula_struc_base
      | _ -> failwith (x_loc ^ ": F.EBase expected.")

  let get_hvar node =
    match node with
      | F.HVar (id, ls) -> (id, ls)
      | _ -> failwith (x_loc ^ ": F.HVar expected.")

end;;

module CForm = struct
  type formula = CF.formula
  type pure_formula = CP.formula
  type h_formula = CF.h_formula
  type h_formula_heap = CF.h_formula_view
  type ho_param_formula = CF.rflow_formula
  type struc_formula = CF.struc_formula
  type var = CP.spec_var
  type node = var
  type param = CP.spec_var
  type arg = node * ident * (ho_param_formula list) *
             (param list) * VarGen.loc

  let is_emp f = failwith x_tbi
  let print    = CF.print_formula
  let print_h_formula = CF.print_h_formula
  let mk_node (ptr, name, ho, params, pos) sk nk =
    let h = CF.mkViewNode ptr name params pos in
    match h with
      | CF.ViewNode node -> CF.ViewNode {node with CF.h_formula_view_ho_arguments = ho;
                                                   CF.h_formula_view_session_info = Some (mk_node_session_info sk nk)}
      | _ -> failwith (x_loc ^ ": CF.ViewNode expected.")

  let mk_formula_heap_only h pos =
    CF.formula_of_heap h pos

  let mk_rflow_formula ?kind:(k=NEUTRAL) f =
    { CF.rflow_kind = k;
      CF.rflow_base = f;
    }

  let mk_rflow_formula_from_heap h ?kind:(k=NEUTRAL) pos =
    let f = mk_formula_heap_only h pos in
    { CF.rflow_kind = k;
      CF.rflow_base = f;
    }

  let mk_formula pure (ptr, name, ho, params, pos) sk nk =
    let h = mk_node (ptr, name, ho, params, pos) sk nk in
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

  let mk_hvar id ls =
    let id = CP.SpecVar(UNK, id, Unprimed) in
    let ls = List.map (fun x -> CP.SpecVar(UNK, x, Unprimed)) ls in
    CF.HVar(id, ls)

  let mk_seq_wrapper hform pos sk = hform

  let set_param id pos = CP.SpecVar(UNK,id,Unprimed)

  let struc_formula_trans_heap_node fct_h struc_form =
    let fct_h = (fun x -> Some (fct_h x)) in
    let fct = nonef, nonef, fct_h, (somef, somef, somef, somef, somef) in
    CF.transform_struc_formula fct struc_form

  let transform_h_formula f_h h = CF.transform_h_formula f_h h

  let update_temp_heap_name hform = hform

  let update_formula f = f

  let subst_param  (sst: (var * var) list) p =
    try  let _,res = List.find (fun (a,_) -> CP.eq_spec_var a p) sst in res
    with Not_found -> p

  let subst_formula (sst: (var * var) list) f =
    let fromsv, tosv = List.split sst in
    CF.subst_avoid_capture fromsv tosv f

  let get_node h_formula =
    match h_formula with
      | CF.ViewNode node -> (node.CF.h_formula_view_node,
                             node.CF.h_formula_view_name,
                             node.CF.h_formula_view_ho_arguments,
                             node.CF.h_formula_view_arguments,
                             node.CF.h_formula_view_pos)
      | _ -> failwith (x_loc ^ ": CF.ViewNode expected.")

  let get_or_formulae formula =
    match formula with
      | CF.Or f -> [f.CF.formula_or_f1; f.CF.formula_or_f2]
      | _ -> failwith (x_loc ^ ": CF.Or expected.")

  let get_star_formulae h_formula =
    match h_formula with
      | CF.Star hf -> [hf.CF.h_formula_star_h1; hf.CF.h_formula_star_h2]
      | _ -> failwith (x_loc ^ ": CF.Star expected.")

  let get_star_pos h_formula =
    match h_formula with
      | CF.Star hf -> hf.CF.h_formula_star_pos
      | _ -> failwith (x_loc ^ ": CF.Star expected.")

  let get_node_kind h_formula =
    match h_formula with
      | CF.ViewNode node -> (match node.CF.h_formula_view_session_info with
                               | Some si -> si.node_kind
                               | None -> failwith (x_loc ^ ": Expected session information."))
      | CF.Star node -> Star
      | CF.HVar (sv, svl) -> HVar
      | CF.HEmp -> Emp
      | _ -> failwith (x_loc ^ ": Not a valid heap formula for session.")

  let get_param_id param =
    match param with
      | CP.SpecVar sv -> let (t, n, p) = sv in
                         n

  let get_node_id node = get_param_id node

  let get_formula_from_struc_formula struc_formula =
    match struc_formula with
      | CF.EBase base -> base.CF.formula_struc_base
      | _ -> failwith (x_loc ^ ": CF.EBase expected.")

  let is_base_formula formula =
    match formula with
      | CF.Base f -> true
      | _ -> false

  let get_h_formula formula =
    match formula with
      | CF.Base f -> f.CF.formula_base_heap
      | _ -> failwith (x_loc ^ ": Formula Base expected.")

  let get_h_formula_from_ho_param_formula rflow_formula =
    let f = rflow_formula.CF.rflow_base in
    get_h_formula f

  let get_formula_from_ho_param_formula rflow_formula =
    rflow_formula.CF.rflow_base

  let get_hvar node =
    match node with
      | CF.HVar (id, ls) -> let id = get_param_id id in
                            let ls = List.map (fun x -> get_param_id x) ls in
                            (id, ls)
      | _ -> failwith (x_loc ^ ": CF.HVar expected.")

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
      let args = [Msg.mk_rflow_formula base.protocol_base_formula_message] in
      let params = [base.protocol_base_formula_sender; base.protocol_base_formula_receiver] in
      let params = List.map (fun a -> Msg.set_param a base.protocol_base_formula_pos) params in
      Msg.mk_node (ptr, name, args, params, base.protocol_base_formula_pos) base_type Transmission

    let get_base_pos base = base.protocol_base_formula_pos

    let trans_h_formula_to_session_base h_formula = failwith x_tbi

    let subst_base (sst: (Msg.var * Msg.var) list) (msg: base): base = msg
      
  end;;

(* inst for iformula & cformula *)
module Projection_base_formula =
  functor  (Msg: Message_type) ->
  struct
    include Msg
    type t = Msg.formula
    type a = transmission * ident * param * VarGen.loc
    type base = {
      projection_base_formula_op          : transmission;
      projection_base_formula_channel     : ident;
      projection_base_formula_message     : t;
      projection_base_formula_message_var : param;
      projection_base_formula_pos         : VarGen.loc;
    }

    let base_type = Projection

    let print_message f = !Msg.print f.projection_base_formula_message

    let string_of_session_base f =
      f.projection_base_formula_channel ^
      (string_of_transmission f.projection_base_formula_op) ^
      "(" ^ (print_message f) ^ ")"

    let mk_base (transmission, channel, mv, pos) formula = {
      projection_base_formula_op          = transmission;
      projection_base_formula_channel     = channel;
      projection_base_formula_message     = formula;
      projection_base_formula_message_var = mv;
      projection_base_formula_pos         = pos;
    }

    let trans_base base =
      let ptr = Msg.choose_ptr ~ptr:base.projection_base_formula_channel () in
      let tkind = get_session_kind_of_transmission base.projection_base_formula_op in
      let name = get_prim_pred_id_by_kind tkind in
      let args = match base.projection_base_formula_op with
        | TSend -> [Msg.mk_rflow_formula ~kind:INFLOW base.projection_base_formula_message]
        | TReceive -> [Msg.mk_rflow_formula ~kind:OUTFLOW base.projection_base_formula_message] in
      let params = [base.projection_base_formula_message_var] in
      let node = Msg.mk_node (ptr, name, args, params, base.projection_base_formula_pos) base_type tkind in
      node
      (* Msg.mk_seq_wrapper node base.projection_base_formula_pos base_type *)

    let trans_base base =
      let pr1 = string_of_session_base in
      let pr2 = !Msg.print_h_formula in
      Debug.no_1 "trans_base" pr1 pr2 trans_base base

    let get_base_pos base = base.projection_base_formula_pos

    let trans_h_formula_to_session_base h_formula =
      let (ptr, name, hoargs, params, pos) = Msg.get_node h_formula in
      let channel = Msg.get_node_id ptr in
      let f = Msg.get_formula_from_ho_param_formula (List.nth hoargs 0) in
      let transmission = match (Msg.get_node_kind h_formula) with
        | Send -> TSend
        | Receive -> TReceive
        | _ -> failwith (x_loc ^ ": Not a valid transmission type.") in
      let mv = match params with
        | []    -> failwith (x_loc ^ ": empty message pointer.")
        | p::[] -> p
        | _     -> failwith (x_loc ^ ": Send/Receive nodes expect exactly one arg.")
      in
      mk_base (transmission, channel, mv, pos) f

    let trans_h_formula_to_session_base h_formula =
      let pr1 = !Msg.print_h_formula in
      let pr2 = string_of_session_base in
      Debug.no_1 "trans_h_formula_to_session_base" pr1 pr2 trans_h_formula_to_session_base h_formula

    let subst_base (sst: (Msg.var * Msg.var) list) (msg: base): base =
      { msg with
        projection_base_formula_message = subst_formula sst msg.projection_base_formula_message;
        projection_base_formula_message_var = subst_param sst msg.projection_base_formula_message_var; }

  end;;

module TPProjection_base_formula =
  functor  (Msg: Message_type) ->
  struct
    include Msg
    type t = Msg.formula
    type a = transmission * param * VarGen.loc
    type base = {
      tpprojection_base_formula_op          : transmission;
      tpprojection_base_formula_message     : t;
      tpprojection_base_formula_message_var : param;
      tpprojection_base_formula_pos         : VarGen.loc;
    }

    let base_type = TPProjection

    let print_message f = !Msg.print f.tpprojection_base_formula_message

    let string_of_session_base f =
      (string_of_transmission f.tpprojection_base_formula_op) ^
      "(" ^ (print_message f) ^ ")"

    let mk_base (transmission, mv, pos) formula = {
      tpprojection_base_formula_op          = transmission;
      tpprojection_base_formula_message     = formula;
      tpprojection_base_formula_message_var = mv;
      tpprojection_base_formula_pos         = pos;
    }

    let trans_base base =
      let ptr = Msg.choose_ptr ~ptr:session_chan_id () in
      let tkind = get_session_kind_of_transmission base.tpprojection_base_formula_op in
      let name = get_prim_pred_id_by_kind tkind in
      let args = match base.tpprojection_base_formula_op with
        | TSend -> [Msg.mk_rflow_formula ~kind:INFLOW base.tpprojection_base_formula_message]
        | TReceive -> [Msg.mk_rflow_formula ~kind:OUTFLOW base.tpprojection_base_formula_message]
      in
      let params = [base.tpprojection_base_formula_message_var] in
      let node = Msg.mk_node (ptr, name, args, params, base.tpprojection_base_formula_pos) base_type tkind in
      node
      (* Msg.mk_seq_wrapper node base.tpprojection_base_formula_pos base_type *)

    let trans_base base =
      let pr1 = string_of_session_base in
      let pr2 = !Msg.print_h_formula in
      Debug.no_1 "trans_base" pr1 pr2 trans_base base

    let get_base_pos base = base.tpprojection_base_formula_pos

    let trans_h_formula_to_session_base h_formula =
      let (ptr, name, args, params, pos) = Msg.get_node h_formula in
      let f = Msg.get_formula_from_ho_param_formula (List.nth args 0) in
      let transmission = match (Msg.get_node_kind h_formula) with
        | Send -> TSend
        | Receive -> TReceive
        | _ -> failwith (x_loc ^ ": Not a valid transmission type.") in
      let mv = match params with
        | []    -> failwith (x_loc ^ ": empty message pointer.")
        | p::[] -> p
        | _     -> failwith (x_loc ^ ": Send/Receive nodes expect exactly one arg.")
      in
      mk_base (transmission, mv, pos) f

    let subst_base (sst: (Msg.var * Msg.var) list) (msg: base): base = 
      { msg with
        tpprojection_base_formula_message = subst_formula sst msg.tpprojection_base_formula_message;
        tpprojection_base_formula_message_var = subst_param sst msg.tpprojection_base_formula_message_var; }

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
  val trans_h_formula_to_session_base : h_formula -> base
  val subst_base: ((var * var) list) -> base -> base
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
    | HVar of session_hvar

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

  and session_hvar = {
    session_hvar_id: ident;
    session_hvar_list: ident list;
    session_hvar_pos: loc;
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
    | HVar h -> string_of_session_hvar h

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

  and string_of_session_hvar s =
    "%" ^ s.session_hvar_id

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

  and mk_session_hvar id ls loc = HVar {
    session_hvar_id = id;
    session_hvar_list = ls;
    session_hvar_pos = loc;
  }

  let mk_seq_node h1 h2 pos  =
    let ptr = Base.choose_ptr () in (* decide which name should be given here *)
    let name = get_prim_pred_id seq_id in
    (*let h2 = Base.mk_seq_wrapper h2 pos Base.base_type in *)
    let args = [h1; h2] in
    let args = List.map (fun a -> Base.mk_rflow_formula_from_heap a pos) args in
    let params = [] in
    Base.mk_node (ptr, name, args, params, pos) Base.base_type Sequence

  and mk_star_node h1 h2 pos =
    Base.mk_star h1 h2 pos

  and mk_or_node h1 h2 pos =
    let f1 = Base.mk_formula_heap_only h1 pos in
    let f2 = Base.mk_formula_heap_only h2 pos in
    let or_node = Base.mk_or f1 f2 pos in
    let rflow_form = (Base.mk_rflow_formula or_node) in
    let ptr = Base.choose_ptr () in
    let name = get_prim_pred_id sor_id in
    let args = [rflow_form] in
    let params = [] in
    let node = Base.mk_node (ptr, name, args, params, pos) Base.base_type SOr in
    node
    (* Base.mk_seq_wrapper node pos Base.base_type *)

  and mk_predicate_node p =
    let ptr = Base.choose_ptr () in
    let name = p.session_predicate_name in
    let args = [] in (* not using HO preds here *)
    let pos = p.session_predicate_pos in
    let params = p.session_predicate_params in
    let params = List.map (fun a -> Base.set_param a pos) params in
    let node = Base.mk_node (ptr, name, args, params, pos) Base.base_type Predicate in
    node
    (* Base.mk_seq_wrapper node pos Base.base_type *)

  and mk_hvar_node h =
    let id = h.session_hvar_id in
    let ls = h.session_hvar_list in
    let pos = h.session_hvar_pos in
    let node = Base.mk_hvar id ls in
    node
    (* Base.mk_seq_wrapper node pos Base.base_type *)

  let trans_from_session s =
    let rec helper s = match s with
    | SSeq s  ->
        let arg1 = helper s.session_seq_formula_head in
        let arg2 = helper s.session_seq_formula_tail in
        mk_seq_node arg1 arg2 s.session_seq_formula_pos
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
        | Predicate p -> mk_predicate_node p
        | HVar h -> mk_hvar_node h)
    | SEmp    -> Base.mk_empty () in
    helper s

  let trans_from_session s =
    let pr = string_of_session in
    let pr2 = !Base.print_h_formula in
    Debug.no_1 "trans_from_session" pr pr2 trans_from_session s

  let trans_session_formula fnc s =
    let rec helper fnc s =
      let r = fnc s in
      match r with
      | Some e -> e
      | None ->
        match s with
        | SSeq s  ->
          let arg1 = helper fnc s.session_seq_formula_head in
          let arg2 = helper fnc s.session_seq_formula_tail in
          mk_session_seq_formula arg1 arg2 s.session_seq_formula_pos
        | SOr s   ->
          let arg1 = helper fnc s.session_seq_formula_or1 in
          let arg2 = helper fnc s.session_seq_formula_or2 in
          mk_session_or_formula arg1 arg2 s.session_seq_formula_pos
        | SStar s ->
          let arg1 = helper fnc s.session_seq_formula_star1 in
          let arg2 = helper fnc s.session_seq_formula_star2 in
          mk_session_star_formula arg1 arg2 s.session_seq_formula_pos
        | _ -> s
    in
    helper fnc s

  let get_pos s = match s with
    | SSeq s  -> s.session_seq_formula_pos
    | SOr s   -> s.session_seq_formula_pos
    | SStar s -> s.session_seq_formula_pos
    | SBase s -> (match s with
        | Base b -> Base.get_base_pos b
        | Predicate p -> p.session_predicate_pos
        | HVar h -> no_pos)
    | SEmp    -> no_pos

  let mk_formula_heap_only = Base.mk_formula_heap_only

  let mk_sess_h_formula h_form pos =
    let f = Base.mk_formula_heap_only h_form pos in
    let rflow_form = (Base.mk_rflow_formula f) in
    let ptr = Base.choose_ptr () in
    let name = get_prim_pred_id sess_id in
    let args = [rflow_form] in
    let params = [] in
    Base.mk_node (ptr, name, args, params, pos) Base.base_type Session

  let mk_struc_formula_from_session_and_formula s form_orig =
    let h_form = trans_from_session s in
    let pos = get_pos s in
    let h_form = mk_sess_h_formula h_form pos in
    let fct h = Base.mk_star h h_form pos in
    Base.struc_formula_trans_heap_node fct form_orig

  let update_formula = Base.update_formula

  let trans_h_formula_to_session h_formula =
    let rec helper h_formula =
      let node_kind = Base.get_node_kind h_formula in
      match node_kind with
        | Sequence ->
            let (ptr, name, args, params, pos) = Base.get_node h_formula in
            let h1 = Base.get_h_formula_from_ho_param_formula (List.nth args 0) in
            let h2 = Base.get_h_formula_from_ho_param_formula (List.nth args 1) in
            mk_session_seq_formula (helper h1) (helper h2) pos
        | SOr ->
            let (ptr, name, args, params, pos) = Base.get_node h_formula in
            let or_node = Base.get_formula_from_ho_param_formula (List.nth args 0) in
            let or_formulae = Base.get_or_formulae or_node in
            let h1 = Base.get_h_formula (List.nth or_formulae 0) in
            let h2 = Base.get_h_formula (List.nth or_formulae 1) in
            mk_session_or_formula (helper h1) (helper h2) pos
        | Star ->
            let pos = Base.get_star_pos h_formula in
            let star_formulae = Base.get_star_formulae h_formula in
            let h1 = List.nth star_formulae 0 in
            let h2 = List.nth star_formulae 1 in
            mk_session_star_formula (helper h1) (helper h2) pos
        | Send | Receive | Transmission ->
            SBase (Base (Base.trans_h_formula_to_session_base h_formula))
        | HVar ->
            let (id, ls) = Base.get_hvar h_formula in
            SBase (mk_session_hvar id ls no_pos)
        | Predicate ->
            let (ptr, name, args, params, pos) = Base.get_node h_formula in
            let params = List.map (fun a -> Base.get_param_id a) params in
            SBase (mk_session_predicate name [] params pos)
        | Emp ->
            SEmp
        | Session ->
            let (ptr, name, args, params, pos) = Base.get_node h_formula in
            let h = Base.get_h_formula_from_ho_param_formula (List.nth args 0) in
            helper h
        | Channel -> failwith (x_loc ^ ": Unexpected node kind.")
        | Msg -> failwith (x_loc ^ ": Unexpected node kind.") in
    helper h_formula

  let trans_h_formula_to_session h_formula =
    let pr1 = !Base.print_h_formula in
    let pr2 = string_of_session in
    Debug.no_1 "trans_h_formula_to_session" pr1 pr2 trans_h_formula_to_session h_formula

  (* Strip the STAR with original formula in view_decl. *)
  let get_original_h_formula h_formula =
    (* Extract h_formula from STAR with original formula.
     * If the original formula was empty, the star node
     * was not created and the session formula is preserved
     * as it was.
     * Otherwise, split STAR node and get second branch.*)
    let h_formula = match Base.get_node_kind h_formula with
                      | Star ->
                          let star_formulae = Base.get_star_formulae h_formula in
                          List.nth star_formulae 1
                      | _ -> h_formula in
    h_formula

  let get_original_h_formula h_formula =
    let pr = !Base.print_h_formula in
    Debug.no_1 "get_original_h_formula" pr pr get_original_h_formula h_formula

  let trans_formula_to_session formula =
    if (Base.is_base_formula formula)
    then
      let h_formula = Base.get_h_formula formula in
      let h_formula = get_original_h_formula h_formula in
      trans_h_formula_to_session h_formula
    else
      failwith (x_loc ^ ": Formula Base expected.")

  let trans_struc_formula_to_session struc_formula =
    let f = Base.get_formula_from_struc_formula struc_formula in
    trans_formula_to_session f

  let rec extract_bases session =
    match session with
      | SSeq s -> (extract_bases s.session_seq_formula_head) @
                  (extract_bases s.session_seq_formula_tail)
      | _  -> [session]

  (* For a single base, do we want it:
   * 1. in a Seq node with empty: Seq{base, emp}
   * or
   * 2. just the plain base, without Seq?
   * Currently doing 1.
   *)
  let rec mk_norm_session bases =
    match bases with
      | [] -> SEmp
      | [base] -> let pos = get_pos base in
                  mk_session_seq_formula base SEmp pos
      | hd :: tl -> let pos = get_pos hd in
                    mk_session_seq_formula hd (mk_norm_session tl) pos

  (* NORM3: first argument of Seq is a non-Seq node
   *
   * self::Seq{self::Seq{a.b}, self::Seq{c,d}}
   *  |
   *  |
   *  V
   * self::Seq{a, self::Seq{b, self::Seq{c,d}}}
   *
   * 1. extract all bases (non-Seq nodes) in the
   * order they appear from left to right
   * 2. remake Seq nodes with first argument a base
   *)
  let norm3_sequence session =
    let bases = extract_bases session in
    mk_norm_session bases

  let rec sor_disj_list head =
    match head with
      | SOr s -> (sor_disj_list s.session_seq_formula_or1) @
                  (sor_disj_list s.session_seq_formula_or2)
      | _ -> [head]

  let append_tail disjunct tail =
    let pos = get_pos disjunct in
    mk_session_seq_formula disjunct tail pos

  (* Split a SOr predicate into disjuncts.
   * 1. tranform head and tail into sessions
   * 2. get list of disjuncts from head
   * 3. for each disjunct, append tail
   * 4. for each disjunct, normalize
   *)
  let split_sor head tail =
    let head_session = trans_h_formula_to_session
                       (Base.get_h_formula_from_ho_param_formula head) in
    let tail_session = trans_h_formula_to_session
                       (Base.get_h_formula_from_ho_param_formula tail) in
    let disj_list = sor_disj_list head_session in
    let disj_list = List.map (fun x -> append_tail x tail_session) disj_list in
    let disj_list = List.map (fun x -> norm3_sequence x) disj_list in
    disj_list

end;;

(* =========== Protocol / Projection ========== *)
(* ============================================ *)

module IProtocol_base = Protocol_base_formula(IForm) ;;
module CProtocol_base = Protocol_base_formula(CForm) ;;
module IProjection_base = Projection_base_formula(IForm) ;;
module CProjection_base = Projection_base_formula(CForm) ;;
module ITPProjection_base = TPProjection_base_formula(IForm) ;;
module CTPProjection_base = TPProjection_base_formula(CForm) ;;

module IProtocol = Make_Session(IProtocol_base);;
module CProtocol = Make_Session(CProtocol_base);;

module IProjection = Make_Session(IProjection_base);;
module CProjection = Make_Session(CProjection_base);;

module ITPProjection = Make_Session(ITPProjection_base);;
module CTPProjection = Make_Session(CTPProjection_base);;

type session_type = ProtocolSession of IProtocol.session
                  | ProjectionSession of IProjection.session
                  | TPProjectionSession of ITPProjection.session

let get_protocol session =
  match session with
  | ProtocolSession s -> s
  | _ -> failwith "not a protocol formula"

let get_projection session =
  match session with
  | ProjectionSession s -> s
  | _ -> failwith "not a projection formula"

let get_tpprojection session =
  match session with
  | TPProjectionSession s -> s
  | _ -> failwith "not a two-party projection formula"

let is_projection si = let fct info = let sk = info.session_kind in
                       (match sk with
                         | Projection -> true 
                         | TPProjection -> true
                         | _ -> false) in
                       Gen.map_opt_def false fct si

let irename_message_pointer sf = (* sf *)
  let f_h h =
    match h with
    | F.HeapNode node ->
      let fct si =
        match si.node_kind with
        | Session ->
          begin
            let transf h = 
              match si.session_kind with
              | Projection   -> ProjectionSession (IProjection.trans_h_formula_to_session h)
              | TPProjection -> TPProjectionSession (ITPProjection.trans_h_formula_to_session h)
              | Protocol     -> ProtocolSession (IProtocol.trans_h_formula_to_session h)
            in
            let sf = transf h in
            
            Some h
          end
        | _ -> None
      in
      Gen.map_opt_def None fct node.F.h_formula_heap_session_info
    | _ -> None in
  let f = (nonef,nonef, f_h, (somef,somef,somef,somef,somef)) in
  F.transform_struc_formula f sf

let crename_message_pointer sf = sf
