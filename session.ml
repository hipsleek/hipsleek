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
  val print_struc_formula  : (struc_formula -> string) ref
  val print_h_formula  : (h_formula -> string) ref
  val print_ho_param_formula  : (ho_param_formula -> string) ref
  val mk_node: arg -> session_kind -> node_kind -> h_formula
  val mk_formula_heap_only:  h_formula -> VarGen.loc -> formula
  val mk_rflow_formula: ?sess_kind:(session_kind option) -> ?kind:ho_flow_kind -> formula -> ho_param_formula
  val mk_rflow_formula_from_heap:  h_formula -> ?sess_kind:(session_kind option) -> ?kind:ho_flow_kind -> VarGen.loc -> ho_param_formula
  val mk_formula: pure_formula -> arg -> session_kind -> node_kind -> formula
  val mk_struc_formula: formula -> VarGen.loc -> struc_formula
  val mk_star: h_formula -> h_formula -> VarGen.loc -> h_formula
  val mk_or: formula -> formula -> VarGen.loc -> formula
  val mk_empty: unit -> h_formula
  val mk_hvar: ident -> var list -> h_formula
  val mk_seq_wrapper: ?sess_kind:session_kind option -> h_formula -> VarGen.loc -> session_kind -> h_formula
  val choose_ptr: ?ptr:string -> unit -> node
  val id_to_param:  ident ->  VarGen.loc -> param
  val var_to_param: var ->  VarGen.loc -> param
  val param_to_var: param -> var

  val heap_node_transformer:  ?flow:bool -> (node_session_info -> h_formula -> h_formula option) -> h_formula -> h_formula option
  val transform_h_formula: (h_formula -> h_formula option)-> h_formula -> h_formula
  val transform_formula: (h_formula -> h_formula option)-> formula -> formula
  val transform_struc_formula:  (h_formula -> h_formula option)-> struc_formula -> struc_formula
  val map_one_rflow_formula: (formula -> formula) -> ho_param_formula -> ho_param_formula
  val update_temp_heap_name: h_formula -> h_formula option
  val subst_param:   (var * var) list -> param -> param
  val subst_var:     (var * var) list -> var -> var
  val subst_formula: (var * var) list -> formula -> formula
  val fresh_var: var -> var
  val eq_var: var -> var -> bool
  val mk_var: ident -> var

  val is_base_formula: formula -> bool
  val get_h_formula: formula -> h_formula
  val get_h_formula_safe: formula -> h_formula
  val get_h_formula_from_ho_param_formula: ho_param_formula -> h_formula
  val get_formula_from_ho_param_formula: ho_param_formula -> formula
  val get_node: h_formula -> arg
  val get_or_formulae: formula -> formula list
  val get_star_formulae: h_formula -> h_formula list
  val get_star_pos: h_formula -> VarGen.loc
  val get_node_kind: h_formula -> node_kind
  val get_session_kind: h_formula -> session_kind option
  val get_param_id: param -> ident
  val get_node_id: node -> ident
  val get_formula_from_struc_formula: struc_formula -> formula
  val get_hvar: h_formula -> ident * var list
  val get_node_session_info: h_formula -> node_session_info option

  val get_h_formula_safe: formula -> h_formula option
  val get_h_formula_from_struc_formula_safe: struc_formula -> h_formula option

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
  let print_ho_param_formula = F.print_rflow_formula
  let print_struc_formula = F.print_struc_formula
  let mk_node (ptr, name, ho, params, pos) sk nk =
    let h = (F.mkHeapNode ptr name ho 0 false (*dr*) SPLIT0
               (P.ConstAnn(Mutable)) false false false None params [] None pos) in
    F.set_session_kind_h_formula h sk nk

  let mk_formula_heap_only h pos =
    F.formula_of_heap_with_flow h F.n_flow pos

  let mk_rflow_formula ?sess_kind:(sess_kind=None) ?kind:(k=NEUTRAL) f =
    {  F.rflow_kind = k;
       F.rflow_base = f;
       F.rflow_session_kind = sess_kind;
    }

  let mk_rflow_formula_from_heap h ?sess_kind:(sess_kind=None) ?kind:(k=NEUTRAL) pos =
    let f =  mk_formula_heap_only h pos in
    {  F.rflow_kind = k;
       F.rflow_base = f;
       F.rflow_session_kind = sess_kind;
    }

  let mk_formula pure (ptr, name, ho, params, pos) sk nk  =
    let h = mk_node (ptr, name, ho, params, pos) sk nk in
    F.mkBase(* _wo_flow *) h pure IvpermUtils.empty_vperm_sets F.n_flow [] pos

  let mk_struc_formula formula pos =
    F.mkEBase [] [] [] formula None pos

  let mk_star h1 h2 pos =
    F.mkStar h1 h2 pos

  let choose_ptr ?ptr:(str=session_def_id) () =
    (str,Unprimed)

  let mk_or f1 f2 pos =
    F.mkOr f1 f2 pos

  let mk_empty () = F.HEmp

  let mk_hvar id ls = F.HVar(id, ls)

  let mk_seq_wrapper_node ?sess_kind:(sess_kind=None) hform pos sk =
    let ptr = choose_ptr() in
    let name = get_prim_pred_id seq_id in
    let hemp = mk_empty () in
    let args = [hform; hemp] in
    let args = List.map (fun a -> mk_rflow_formula_from_heap a  ~sess_kind:sess_kind pos) args in
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
  let mk_seq_wrapper ?sess_kind:(sess_kind=None) hform pos sk =
    match hform with
    | F.HeapNode node -> let fct si = let nk = si.node_kind in
                           (match nk with
                            | Sequence -> hform
                            | _ -> mk_seq_wrapper_node hform pos sk) in
      Gen.map_opt_def hform fct node.F.h_formula_heap_session_info
    | F.Star node -> mk_seq_wrapper_node hform pos sk
    | _ -> hform

  let id_to_param id pos = Ipure_D.Var((id,Unprimed), pos)

  let var_to_param sv pos = Ipure_D.Var(sv, pos)

  let param_to_var parm =
    match parm with
    | Ipure_D.Var(sv, pos) -> sv
    | _ -> failwith (x_loc ^ "param_to_var is expecting a Ipure.var exp")

  let transform_h_formula f_h h =
    F.transform_h_formula f_h h

  let transform_formula fct formula =
    let fcts = (nonef,nonef,fct,(somef,somef,somef,somef,somef)) in
    F.transform_formula fcts formula

  let transform_struc_formula fct struc_form =
    let fcts = (nonef,nonef,fct,(somef,somef,somef,somef,somef)) in
    F.transform_struc_formula fcts struc_form

  let map_one_rflow_formula fnc rflow_formula =
    F.map_one_rflow_formula fnc rflow_formula

  (* calls h_fnc on 
     (i) first session node of hform if include_flow is set 
     (ii) all nodes of hform -incl. nested HO args- otherwise 
  *)
  let heap_node_transformer ?flow:(include_flow=false) h_fnc hform =
    let loop_through_rflow helper hform =
      let f_h nh =
        match nh with
        | F.HeapNode node_new ->
          let fct = helper h_fnc in
          let trans_f = transform_formula fct in
          Some (F.map_rflow_formula_list trans_f node_new)
        | _ -> None in
      Some (transform_h_formula f_h hform) in
    let loop_through_rflow helper hform =
      let pr = !print_h_formula in
      Debug.no_1 "loop_through_rflow" pr (pr_opt pr) (fun _ -> loop_through_rflow helper hform) hform in
    let rec helper h_fnc hform = 
      match hform with
      | F.HeapNode node ->
        begin
          match node.F.h_formula_heap_session_info with
          | None    ->
            (* loop through HO param until reaching a session formula *)
            loop_through_rflow helper hform
          | Some si ->
            let new_heap = h_fnc si hform in
            if not(include_flow) then new_heap (* it's a session related node, but its transformation should stop at this level - do not attempt to transform its HO args *)
            else
              let new_heap = 
                match new_heap with
                | None   ->  hform
                | Some e ->  e in
              loop_through_rflow helper new_heap
        end
      | _ -> None
    in helper h_fnc hform

  let update_temp_heap_name hform =
    let fct si hform = match si.node_kind with
      | Sequence | SOr | Send | Receive | Transmission
      | Session | Channel | Msg ->
        let new_heap_name = get_prim_pred_id_by_kind si.node_kind in
        let updated_node  = F.set_heap_name hform new_heap_name in
        Some updated_node
      | Star | HVar | Predicate | Emp ->  None
    in heap_node_transformer fct hform

    let update_temp_heap_name hform =
      let pr = !print_h_formula in
      Debug.no_1 "update_temp_heap_name" pr (pr_opt pr) update_temp_heap_name hform 

  let subst_param  (sst: (var * var) list) p = IP.subst_exp sst p

  let subst_var    (sst: (var * var) list) p = F.subst_var_list sst p

  let subst_formula (sst: (var * var) list) f = F.subst_all sst f

  let fresh_var (v:var): var = IP.fresh_var v

  let eq_var = IP.eq_var

  let mk_var id = (id, Unprimed)

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

  let rec get_session_kind h_formula =
    match h_formula with
    | F.HeapNode node -> (match node.F.h_formula_heap_session_info with
        | Some si -> Some si.session_kind
        | None -> None)
    | F.Phase phase -> let sk1 = get_session_kind phase.F.h_formula_phase_rd in
      let sk2 = get_session_kind phase.F.h_formula_phase_rw in
      (match (sk1, sk2) with
       | (Some _, None) -> sk1
       | (None, Some _) -> sk2
       | (None, None) -> None
       | (Some _, Some _) -> sk1)
    (* TODO: Star case *)
    | _ -> None

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

  let get_node_session_info h_formula =
    match h_formula with
      | F.HeapNode hn -> hn.h_formula_heap_session_info
      | _ -> None

  let get_h_formula_safe formula =
    match formula with
      | F.Base f -> Some f.F.formula_base_heap
      | F.Exists f -> Some f.F.formula_exists_heap
      | F.Or f -> None

  let get_h_formula_from_struc_formula_safe struc_formula =
    match struc_formula with
      | F.EBase base -> get_h_formula_safe base.F.formula_struc_base
      | _ -> None

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
  let print_ho_param_formula = CF.print_rflow_formula
  let print_struc_formula = CF.print_struc_formula
  let mk_node (ptr, name, ho, params, pos) sk nk =
    let h = CF.mkViewNode ptr name params pos in
    match h with
      | CF.ViewNode node -> CF.ViewNode {node with CF.h_formula_view_ho_arguments = ho;
                                                   CF.h_formula_view_session_info = Some (mk_node_session_info sk nk)}
      | _ -> failwith (x_loc ^ ": CF.ViewNode expected.")

  let mk_formula_heap_only h pos =
    CF.formula_of_heap h pos

  let mk_rflow_formula ?sess_kind:(sess_kind=None) ?kind:(k=NEUTRAL) f =
    { CF.rflow_kind = k;
      CF.rflow_base = f;
      CF.rflow_session_kind = sess_kind;
    }

  let mk_rflow_formula_from_heap h ?sess_kind:(sess_kind=None) ?kind:(k=NEUTRAL) pos =
    let f = mk_formula_heap_only h pos in
    { CF.rflow_kind = k;
      CF.rflow_base = f;
      CF.rflow_session_kind = sess_kind;
    }

  let mk_formula pure (ptr, name, ho, params, pos) sk nk =
    let h = mk_node (ptr, name, ho, params, pos) sk nk in
    let mix_formula = MCP.OnePF pure in
    CF.mkBase_simp h mix_formula

  let mk_struc_formula formula pos =
    CF.mkEBase formula None pos

  let mk_star h1 h2 pos =
    CF.mkStarH h1 h2 pos

  let choose_ptr ?ptr:(str=session_def_id) () =
    CP.SpecVar(UNK,str,Unprimed)

  let mk_or f1 f2 pos =
    CF.mkOr f1 f2 pos

  let mk_empty () = CF.HEmp

  let mk_hvar id ls =
    let id = CP.SpecVar(UNK, id, Unprimed) in
    (* let ls = List.map (fun x -> CP.SpecVar(UNK, x, Unprimed)) ls in *)
    CF.HVar(id, ls)

  let mk_seq_wrapper ?sess_kind:(sess_kind=None) hform pos sk = hform

  let id_to_param id pos = CP.SpecVar(UNK,id,Unprimed)

  let var_to_param sv pos = sv

  let param_to_var parm = parm

  let transform_h_formula f_h h =
    CF.transform_h_formula f_h h

  let transform_formula fct f =
    let fcts = (nonef, nonef, fct, (somef, somef, somef, somef, somef)) in
    CF.transform_formula fcts f

  let transform_struc_formula fct struc_form =
    let fcts = (nonef,nonef,fct,(somef,somef,somef,somef,somef)) in
    CF.transform_struc_formula fcts struc_form

  let map_one_rflow_formula fnc rflow_formula =
    CF.map_one_rflow_formula fnc rflow_formula  
  
  let heap_node_transformer_basic ?flow:(include_flow=false) fnc hform =
    match hform with
    | CF.ViewNode node ->
      let hform_opt  =
        match node.CF.h_formula_view_session_info with
        | None    ->  None
        | Some si ->  fnc si hform
      in hform_opt
    | _ -> None

    (* calls h_fnc on 
     (i) first session node of hform if include_flow is set 
     (ii) all nodes of hform -incl. nested HO args- otherwise 
  *)
  let heap_node_transformer ?flow:(include_flow=false) h_fnc hform =
    let loop_through_rflow helper hform =
      let f_h nh =
        match nh with
        | CF.ViewNode node_new ->
          let fct = helper h_fnc in
          let trans_f = transform_formula fct in
          Some (CF.map_rflow_formula_list trans_f node_new)
        | _ -> None in
      Some (transform_h_formula f_h hform) in
    let loop_through_rflow helper hform =
      let pr = !print_h_formula in
      Debug.no_1 "loop_through_rflow" pr (pr_opt pr) (fun _ -> loop_through_rflow helper hform) hform in
    let rec helper h_fnc hform = 
      match hform with
      | CF.ViewNode node ->
        begin
          match node.CF.h_formula_view_session_info with
          | None    ->
            (* loop through HO param until reaching a session formula *)
            loop_through_rflow helper hform
          | Some si ->
            let new_heap = h_fnc si hform in
            if not(include_flow) then new_heap (* it's a session related node, but its transformation should stop at this level - do not attempt to transform its HO args *)
            else
              let new_heap = 
                match new_heap with
                | None   ->  hform
                | Some e ->  e in
              loop_through_rflow helper new_heap
        end
      | _ -> None
    in helper h_fnc hform
  
  let update_temp_heap_name hform = None

  let subst_param  (sst: (var * var) list) p =
    try  let _,res = List.find (fun (a,_) -> CP.eq_spec_var a p) sst in res
    with Not_found -> p

  let subst_var  (sst: (var * var) list) v =
    try  let _,res = List.find (fun (a,_) -> CP.eq_spec_var a v) sst in res
    with Not_found -> v

  let subst_formula (sst: (var * var) list) f =
    let fromsv, tosv = List.split sst in
    CF.subst_avoid_capture fromsv tosv f

  let fresh_var (v:var): var = CP.fresh_spec_var v

  let eq_var = CP.eq_spec_var

  let mk_var id = CP.mk_spec_var id 

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

  let rec get_session_kind h_formula = failwith x_tbi

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
      | CF.Exists f -> f.CF.formula_exists_heap
      | _ -> failwith (x_loc ^ ": Formula Base or Exists expected.")

  let get_h_formula_from_ho_param_formula rflow_formula =
    let f = rflow_formula.CF.rflow_base in
    get_h_formula f

  let get_formula_from_ho_param_formula rflow_formula =
    rflow_formula.CF.rflow_base

  let get_hvar node =
    match node with
    | CF.HVar (id, ls) -> let id = get_param_id id in
      (id, ls)
    | _ -> failwith (x_loc ^ ": CF.HVar expected.")

  let get_node_session_info h_formula =
    match h_formula with
      | CF.ViewNode vn -> vn.h_formula_view_session_info
      | _ -> None

  let get_h_formula_safe f = failwith x_tbi

  let get_h_formula_from_struc_formula_safe struc_formula = failwith x_tbi

end;;

(* inst for iformula & cformula *)
module Protocol_base_formula =
  functor  (Msg: Message_type) ->
  struct
    include Msg
    type t = Msg.formula
    type a = ident * ident * var * VarGen.loc
    type base = {
      protocol_base_formula_sender      : ident;
      protocol_base_formula_receiver    : ident;
      protocol_base_formula_message     : t;
      protocol_base_formula_message_var : var;
      protocol_base_formula_pos         : VarGen.loc;
    }

    let base_type = Protocol

    let print_message f = !Msg.print f.protocol_base_formula_message

    let string_of_session_base f =
      f.protocol_base_formula_sender ^ " -> " ^ f.protocol_base_formula_receiver ^ " : " ^ (print_message f)

    let mk_base (sender, receiver, mv, pos) formula = {
      protocol_base_formula_sender    = sender;
      protocol_base_formula_receiver  = receiver;
      protocol_base_formula_message   = formula;
      protocol_base_formula_message_var = mv;
      protocol_base_formula_pos       = pos;
    }

    let trans_base base =
      let ptr = Msg.choose_ptr ~ptr:session_msg_id () in
      let name = get_prim_pred_id trans_id in
      let args = [Msg.mk_rflow_formula ~sess_kind:(Some base_type) base.protocol_base_formula_message] in
      let params = [base.protocol_base_formula_sender; base.protocol_base_formula_receiver] in
      let params = List.map (fun a -> Msg.id_to_param a base.protocol_base_formula_pos) params in
      Msg.mk_node (ptr, name, args, params, base.protocol_base_formula_pos) base_type Transmission

    let get_base_pos base = base.protocol_base_formula_pos

    let get_message_var base = base.protocol_base_formula_message_var

    let trans_h_formula_to_session_base h_formula = failwith x_tbi

    let subst_base (sst: (Msg.var * Msg.var) list) (msg: base): base = msg

  end;;

(* inst for iformula & cformula *)
module Projection_base_formula =
  functor  (Msg: Message_type) ->
  struct
    include Msg
    type t = Msg.formula
    type a = transmission * ident * var * VarGen.loc
    type base = {
      projection_base_formula_op          : transmission;
      projection_base_formula_channel     : ident;
      projection_base_formula_message     : t;
      projection_base_formula_message_var : var;
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
        | TSend -> [Msg.mk_rflow_formula ~sess_kind:(Some base_type) ~kind:INFLOW base.projection_base_formula_message]
        | TReceive -> [Msg.mk_rflow_formula ~sess_kind:(Some base_type) ~kind:OUTFLOW base.projection_base_formula_message] in
      let pos = base.projection_base_formula_pos in
      let params = [(Msg.var_to_param base.projection_base_formula_message_var pos)] in
      let node = Msg.mk_node (ptr, name, args, params, pos) base_type tkind in
      node
      (* Msg.mk_seq_wrapper node base.projection_base_formula_pos base_type *)

    let trans_base base =
      let pr1 = string_of_session_base in
      let pr2 = !Msg.print_h_formula in
      Debug.no_1 "trans_base" pr1 pr2 trans_base base

    let get_base_pos base = base.projection_base_formula_pos

    let get_message_var base = base.projection_base_formula_message_var

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
      let mv = Msg.param_to_var mv in
      mk_base (transmission, channel, mv, pos) f

    let trans_h_formula_to_session_base h_formula =
      let pr1 = !Msg.print_h_formula in
      let pr2 = string_of_session_base in
      Debug.no_1 "trans_h_formula_to_session_base" pr1 pr2 trans_h_formula_to_session_base h_formula

    let subst_base (sst: (Msg.var * Msg.var) list) (msg: base): base =
      { msg with
        projection_base_formula_message = subst_formula sst msg.projection_base_formula_message;
        projection_base_formula_message_var = subst_var sst msg.projection_base_formula_message_var; }

  end;;

module TPProjection_base_formula =
  functor  (Msg: Message_type) ->
  struct
    include Msg
    type t = Msg.formula
    type a = transmission * var * VarGen.loc
    type base = {
      tpprojection_base_formula_op          : transmission;
      tpprojection_base_formula_message     : t;
      tpprojection_base_formula_message_var : var;
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
        | TSend -> [Msg.mk_rflow_formula ~sess_kind:(Some base_type) ~kind:INFLOW base.tpprojection_base_formula_message]
        | TReceive -> [Msg.mk_rflow_formula ~sess_kind:(Some base_type) ~kind:OUTFLOW base.tpprojection_base_formula_message]
      in
      let pos = base.tpprojection_base_formula_pos in
      let params = [(Msg.var_to_param base.tpprojection_base_formula_message_var pos)] in
      (* let param = List.map *)
      let node = Msg.mk_node (ptr, name, args, params, pos) base_type tkind in
      node
      (* Msg.mk_seq_wrapper node base.tpprojection_base_formula_pos base_type *)

    let trans_base base =
      let pr1 = string_of_session_base in
      let pr2 = !Msg.print_h_formula in
      Debug.no_1 "trans_base" pr1 pr2 trans_base base

    let get_base_pos base = base.tpprojection_base_formula_pos

    let get_message_var base = base.tpprojection_base_formula_message_var

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
      let mv = Msg.param_to_var mv in
      mk_base (transmission, mv, pos) f

    let subst_base (sst: (Msg.var * Msg.var) list) (msg: base): base = 
      { msg with
        tpprojection_base_formula_message = subst_formula sst msg.tpprojection_base_formula_message;
        tpprojection_base_formula_message_var = subst_var sst msg.tpprojection_base_formula_message_var; }

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
  val get_message_var : base -> var
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
    session_hvar_list: Base.var list;
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
    " (" ^ string_of_one_session s.session_seq_formula_or2 ^ ")"

  and string_of_session_star s =
    "(" ^ string_of_one_session s.session_seq_formula_star1 ^ ") " ^
    "*" ^
    " (" ^ string_of_one_session s.session_seq_formula_star2 ^ ")"

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
    let args = List.map (fun a -> Base.mk_rflow_formula_from_heap a ~sess_kind:(Some Base.base_type) pos) args in
    let params = [] in
    Base.mk_node (ptr, name, args, params, pos) Base.base_type Sequence

  and mk_star_node h1 h2 pos =
    Base.mk_star h1 h2 pos

  and mk_or_node h1 h2 pos =
    let f1 = Base.mk_formula_heap_only h1 pos in
    let f2 = Base.mk_formula_heap_only h2 pos in
    let or_node = Base.mk_or f1 f2 pos in
    let rflow_form = (Base.mk_rflow_formula ~sess_kind:(Some Base.base_type) or_node) in
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
    let params = List.map (fun a -> Base.id_to_param a pos) params in
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

  (* let is_session_node hform = *)
    
  
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


  (* fnc is to be used on session_base formulas
     fnc_base to be used on the Base.base formulas
  *)  
  let trans_session_base_formula
      ((fnc, fnc_base): (session_base -> session_base option) * (t -> t option))
      (sb: session_base) =
    let new_s = fnc sb in
    match new_s with
    | Some new_s -> new_s
    | None ->
      match sb with
      | Base base ->
        let new_base = fnc_base base in
        let new_base =
          match new_base with
          | Some nb -> nb
          | None    -> base
        in
        Base new_base
      | Predicate _ 
      | HVar _ -> sb

  (* fnc is to be used on the symmetric compound structs
     f_base to be used to transform base structs
  *)
  let trans_session_formula
      ((fnc, f_base): (session -> session option ) * ((session_base -> session_base option) * (t -> t option)))
      (sf:session) =
    let rec helper fnc sf =
      let r = fnc sf in
      match r with
      | Some e -> e
      | None ->
        match sf with
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
        | SBase sb -> SBase (trans_session_base_formula f_base sb)
        | SEmp -> sf
    in
    helper fnc sf

  let trans_session_formula fnc sf =
    let pr = string_of_session in
    Debug.no_1 "trans_session_formula" pr pr (trans_session_formula fnc) sf

  let get_pos s = match s with
    | SSeq s  -> s.session_seq_formula_pos
    | SOr s   -> s.session_seq_formula_pos
    | SStar s -> s.session_seq_formula_pos
    | SBase s -> (match s with
        | Base b -> Base.get_base_pos b
        | Predicate p -> p.session_predicate_pos
        | HVar h -> no_pos)
    | SEmp    -> no_pos

  let get_node_kind_opt hform =
    try Some (Base.get_node_kind hform)
    with _ -> None

  let is_node_kind hform kind =
    match (get_node_kind_opt hform) with
    | Some k -> k == kind
    | None -> false

  let is_node_kind_rflow rflow kind =
    is_node_kind rflow kind
  
  let mk_formula_heap_only = Base.mk_formula_heap_only

  let mk_sess_h_formula h_form pos =
    let f = Base.mk_formula_heap_only h_form pos in
    let rflow_form = (Base.mk_rflow_formula ~sess_kind:(Some Base.base_type) f) in
    let ptr = Base.choose_ptr () in
    let name = get_prim_pred_id sess_id in
    let args = [rflow_form] in
    let params = [] in
    Base.mk_node (ptr, name, args, params, pos) Base.base_type Session

  let mk_struc_formula_from_session_and_formula s form_orig =
    let h_form = x_add_1 trans_from_session s in
    let pos = get_pos s in
    (* let h_form = mk_sess_h_formula h_form pos in *)
    let fct h = Some (Base.mk_star h h_form pos) in
    Base.transform_struc_formula(* _trans_heap_node *) fct form_orig

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
        | Session -> failwith (x_loc ^ ": Unexpected node kind.")
            (* let (ptr, name, args, params, pos) = Base.get_node h_formula in *)
            (* let h = Base.get_h_formula_from_ho_param_formula (List.nth args 0) in *)
            (* helper h *)
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

  let get_message_var b = Base.get_message_var b

  let replace_message_var b =
    let msg_var = Base.get_message_var b in
    let new_var = Base.fresh_var msg_var in
    Base.subst_base [(msg_var,new_var)] b

  let replace_message_var b =
    let pr = Base.string_of_session_base in
    Debug.no_1 "replace_message_var" pr pr replace_message_var b
  
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

  let wrap_2ways_sess2base f_sess hform =
    let session_form = trans_h_formula_to_session hform in
    let new_session_form = f_sess session_form in
    let new_hform = x_add_1 trans_from_session new_session_form in
    new_hform

  let wrap_2ways_sess2base f_sess hform =
    let pr =  !Base.print_h_formula in
    Debug.no_1 "wrap_2ways_sess2base" pr pr (wrap_2ways_sess2base f_sess) hform

  let wrap_2ways_sess2base_opt f_sess hform =
    let session_form = trans_h_formula_to_session hform in
    let new_session_form = f_sess session_form in
    match new_session_form with
    | None -> None
    | Some new_session_form ->
      let new_hform = x_add_1 trans_from_session new_session_form in
      Some new_hform

  let wrap_2ways_sess2base_opt f_sess hform =
    let pr =  !Base.print_h_formula in
    Debug.no_1 "wrap_2ways_sess2base_opt" pr (pr_opt pr) (wrap_2ways_sess2base_opt f_sess) hform
  
  let rename_message_pointer_heap hform =
    let fnc_node sf =
      let base_f b = Some (replace_message_var b) in
      let fnc = (nonef, (nonef, base_f)) in
      let sf = trans_session_formula fnc sf in
      sf in
    wrap_2ways_sess2base fnc_node hform 
  
  let rec extract_bases session =
    match session with
      | SSeq s -> (extract_bases s.session_seq_formula_head) @
                  (extract_bases s.session_seq_formula_tail)
      | _  -> [session]

  let rec mk_norm_session bases =
    match bases with
      | [] -> SEmp
      | [base] -> base
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
  let split_sor (head: Base.ho_param_formula) (tail:Base.ho_param_formula option)
                : Base.ho_param_formula list =
    let head_session = trans_h_formula_to_session
                       (Base.get_h_formula_from_ho_param_formula head) in
    let disj_list = sor_disj_list head_session in
    let disj_list =
      let tail_session =
        match tail with
        | None      -> SEmp (* disj_list *)
        | Some tail ->
          let tail_session = trans_h_formula_to_session
              (Base.get_h_formula_from_ho_param_formula tail) in
          tail_session
      in
      let disj_list = List.map (fun x -> append_tail x tail_session) disj_list in
      disj_list in
    let disj_list = List.map (fun x -> norm3_sequence x) disj_list in
    let disj_list = List.map (fun x -> x_add_1 trans_from_session x) disj_list in
    let disj_list = List.map (fun x -> Base.mk_rflow_formula_from_heap x ~sess_kind:(Some Base.base_type) no_pos) disj_list in
    disj_list

  let split_sor (head: Base.ho_param_formula) (tail:Base.ho_param_formula option)
                : Base.ho_param_formula list =
    let pr1 = !Base.print_ho_param_formula in
    let pr2 = pr_list pr1 in
    Debug.no_2 "split_sor" pr1 (pr_opt pr1) pr2 split_sor head tail

  let split_disj (head: session) (tail: session option)
                 : session list =
    let tail = match tail with
                 | Some tail -> tail
                 | None -> SEmp in
    let disj_list = sor_disj_list head in
    let disj_list = List.map (fun x -> append_tail x tail) disj_list in
    let disj_list = List.map (fun x -> norm3_sequence x) disj_list in
    disj_list

  let split_disj (head: session) (tail: session option)
                 : session list =
    let pr1 = string_of_session in
    let pr2 = pr_list pr1 in
    Debug.no_2 "split_disj" pr1 (pr_opt pr1) pr2 split_disj head tail

  let norm_base_only_helper sf =
    match sf with
    | SBase (Base _) -> Some (mk_session_seq_formula sf SEmp (get_pos sf))
    | _        -> None
  
  let norm_base_only (base: Base.h_formula): Base.h_formula option =
    wrap_2ways_sess2base_opt norm_base_only_helper base

  let norm_base_only (base: Base.h_formula): Base.h_formula option =
    let pr = !Base.print_h_formula in
    Debug.no_1 "norm_base_only" pr (pr_opt pr) norm_base_only base

  let norm_last_seq_node (base: Base.h_formula): Base.h_formula option =
    let trans_seq_helper sf =         
      match sf with
      | SSeq seq ->
        begin
          match norm_base_only_helper seq.session_seq_formula_tail with
          | None      ->  None
          | Some tail ->  Some (SSeq {seq with session_seq_formula_tail = tail})
        end
      | _ ->  Some sf  (* if it's not seq do not norm *)
    in let fct = trans_session_formula (trans_seq_helper, (somef,somef)) in
    Some (wrap_2ways_sess2base fct base)

  let norm_last_seq_node (base: Base.h_formula): Base.h_formula option =
    let pr = !Base.print_h_formula in
    Debug.no_1 "norm_last_seq_node" pr (pr_opt pr) norm_last_seq_node base

  let update_temp_name_heap (base: Base.h_formula): Base.h_formula option =
    Base.update_temp_heap_name base

  let update_temp_name_heap (base: Base.h_formula): Base.h_formula option =
    let pr = !Base.print_h_formula in
    Debug.no_1 "update_temp_name_heap" pr (pr_opt pr) (fun _ -> update_temp_name_heap (base: Base.h_formula)) base

  let isSeqSor hform =
    let helper sf =
      match sf with
      | SSeq seq ->
        begin
          match seq.session_seq_formula_head with
          | SOr _ -> Some sf
          | _ -> None
        end
      | _ -> None
    in
    wrap_2ways_sess2base_opt helper hform
  
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

(* -------------------------------------- *)
(* rename the var which is used for describing the 
   transmitted message (the renaming taregets both the
   S/R arg(s) and their corresponding ho-arg) *)
let irename_message_pointer_heap hform =
  let fnc si hform =
    match si.session_kind with
    | Projection   -> Some (IProjection.rename_message_pointer_heap hform)
    | TPProjection -> Some (ITPProjection.rename_message_pointer_heap hform)
    | Protocol     -> Some (IProtocol.rename_message_pointer_heap hform)
  in
  IForm.heap_node_transformer ~flow:true fnc hform

let irename_message_pointer formula =
  let renamed_formula = IForm.transform_formula irename_message_pointer_heap formula in
  (* add the freshly introduced vars to the exists list *)
  let fv = F.all_fv formula in
  let all_fv = F.all_fv renamed_formula in
  let new_qvars = Gen.BList.difference_eq IP.eq_var all_fv fv in
  let renamed_formula = F.push_exists new_qvars renamed_formula in
  renamed_formula 

let irename_message_pointer formula =
  let pr = !F.print_formula in
  Debug.no_1 "irename_message_pointer" pr pr irename_message_pointer formula

let irename_message_pointer_struc formula =
  let renamed_struct = IForm.transform_struc_formula irename_message_pointer_heap formula in
  (* add the freshly introduced vars to the exists list *)
  let fv = F.struc_free_vars false formula in
  let all_fv = F.struc_free_vars false renamed_struct in
  let new_qvars = Gen.BList.difference_eq IP.eq_var all_fv fv in
  let f_f f = Some (F.push_exists new_qvars f) in
  let renamed_formula = F.transform_struc_formula (nonef,f_f,nonef,(somef,somef,somef,somef,somef)) renamed_struct in
  renamed_struct
  
let irename_message_pointer_struc formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "irename_message_pointer_struc" pr pr irename_message_pointer_struc formula

(* -------------------------------------- *)
(*** rename the first pointer of hform  ***)
let irename_session_pointer_heap ?flow:(flow=false) var hform =
  let fnc si hform =
    match hform with
    | F.HeapNode node -> Some (F.HeapNode {node with F.h_formula_heap_node = var;} )
    | _ -> None
  in
  IForm.heap_node_transformer ~flow:flow fnc hform

let irename_all_session_pointer_struc ?to_var:(var=session_self) sformula =
  let renamed_struct = IForm.transform_struc_formula (irename_session_pointer_heap ~flow:true var) sformula in
  renamed_struct

let irename_all_session_pointer_struc ?to_var:(var=session_self) formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "irename_all_session_pointer_struc" pr pr (irename_all_session_pointer_struc ~to_var:var) formula

let irename_first_session_pointer_struc ?to_var:(var=session_self) sformula =
  let renamed_struct = IForm.transform_struc_formula  (irename_session_pointer_heap var) sformula in
  renamed_struct

let irename_first_session_pointer_struc ?to_var:(var=session_self) formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "irename_first_session_pointer_struc" pr pr (irename_first_session_pointer_struc ~to_var:var) formula

(* ------------------------------------------------------- *)
(*** wrap sequence around single transmissions protocols ***)
(***    eg: x::Chan{@S !0}<> ---> x::Chan{@S !0;;emp}<>  ***)
let wrap_one_seq_heap hform =
    let fnc si hform =
    match si.session_kind with
    | Projection   -> (IProjection.norm_base_only hform)
    | TPProjection -> (ITPProjection.norm_base_only hform)
    | Protocol     -> (IProtocol.norm_base_only hform)
  in
  IForm.heap_node_transformer fnc hform

let wrap_one_seq formula = 
  let renamed_formula = IForm.transform_formula  wrap_one_seq_heap formula in
  renamed_formula

let wrap_one_seq formula =
  let pr = !F.print_formula in
  Debug.no_1 " wrap_one_seq" pr pr wrap_one_seq formula

let wrap_one_seq_struc sformula = 
  let renamed_struct = IForm.transform_struc_formula  wrap_one_seq_heap sformula in
  renamed_struct

let wrap_one_seq_struc formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "wrap_one_seq_struc" pr pr wrap_one_seq_struc formula

(* --------------------------------------------------------------- *)
(***         wrap sequence around final transmission nodes       ***)
(***    eg: x::Chan{@S !0;;!1}<> ---> x::Chan{@S !0;;!1;;emp}<>  ***)
let wrap_last_seq_node_heap hform =
  let fnc si hform =
    match si.session_kind with
    | Projection   ->  (IProjection.norm_last_seq_node hform)
    | TPProjection ->  (ITPProjection.norm_last_seq_node hform)
    | Protocol     ->  (IProtocol.norm_last_seq_node hform)
  in
  IForm.heap_node_transformer (* ~flow:true *) fnc hform

let wrap_last_seq_node formula = 
  let renamed_formula = IForm.transform_formula wrap_last_seq_node_heap formula in
  renamed_formula

let wrap_last_seq_node formula =
  let pr = !F.print_formula in
  Debug.no_1 "wrap_last_seq_node" pr pr wrap_last_seq_node formula

let wrap_last_seq_node_struc sformula = 
  let renamed_struct = IForm.transform_struc_formula wrap_last_seq_node_heap sformula in
  renamed_struct

let wrap_last_seq_node_struc formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "wrap_last_seq_node_struc" pr pr wrap_last_seq_node_struc formula


(* --------------------------------------------------------------- *)
(***               update the temporary view name                ***)
(***          eg: x::TEMP_SESS{...}<> --> x::Send{...}<>         ***)

let update_temp_name_heap hform =
  let fnc si hform =
    match si.session_kind with
    | Projection   ->  (IProjection.update_temp_name_heap hform)
    | TPProjection ->  (ITPProjection.update_temp_name_heap hform)
    | Protocol     ->  (IProtocol.update_temp_name_heap hform)
  in
  IForm.heap_node_transformer ~flow:true fnc hform

let update_temp_name form =
  IForm.transform_formula update_temp_name_heap form

let update_temp_name form =
  let pr = !F.print_formula in
  Debug.no_1 "update_temp_name" pr pr update_temp_name form

let update_temp_name_struc sform =
  IForm.transform_struc_formula update_temp_name_heap sform

let update_temp_name_struc sform =
  let pr = !F.print_struc_formula in
  Debug.no_1 "update_temp_name_struc" pr pr update_temp_name_struc sform

(* -------------------------------------- *)
let csplit_sor head tail si =
  match si.session_kind with
    | Projection   -> CProjection.split_sor head tail
    | TPProjection -> CTPProjection.split_sor head tail
    | Protocol     -> failwith (x_loc ^ ": Unexpected Protocol session.")

(* Do a split only when lhs is either a Sequence or SOr.
 * If Sequence:
 * - do the split regardless of the first parameter being a SOr
 * - preserve pointer of Sequence node in the split results
 * If SOr:
 * - do the split with an empty tail
*)
let new_lhs (lhs: CF.rflow_formula): CF.rflow_formula list =
  let lhs_hform = CForm.get_h_formula_from_ho_param_formula lhs in
  let session_info = CForm.get_node_session_info lhs_hform in
  match session_info with
  | Some si -> (match si.node_kind with
      | Sequence ->  let (ptr, name, ho_args, params, pos) = CForm.get_node lhs_hform in
        let change_ptr hform =
          (match hform with
           | CF.ViewNode vn -> Some (CF.ViewNode {vn with CF.h_formula_view_node = ptr})
           | _ -> Some hform) in
        let new_lhs = csplit_sor (List.nth ho_args 0) (Some (List.nth ho_args 1)) si in
        let new_lhs = List.map (fun x -> let f = x.CF.rflow_base in
                                 let f = CForm.transform_formula change_ptr f in
                                 CForm.mk_rflow_formula ~sess_kind:(Some si.session_kind) f) new_lhs in
        new_lhs
      | SOr -> csplit_sor lhs None si 
      | _ -> [lhs])
  | None -> [lhs]

let new_lhs (lhs: CF.rflow_formula): CF.rflow_formula list =
  let pr1 = !CF.print_rflow_formula in
  let pr2 l = List.fold_left (fun acc x -> acc ^ x) "" (List.map (fun x -> pr1 x) l) in
  Debug.no_1 "new_lhs" pr1 pr2 new_lhs lhs

(* need to check that it does not lead to unsoundness. Check that it filters out
   only those disjuncts which create unsound ctx with the new HO inst.
 *)
let check_for_ho_unsat detect_contra conseq match_ho_res =
  let fail,_,_,new_ho,es = match_ho_res in
  match fail with
  | Some _ -> true              (* return the fail ctx as it is  *)
  | None ->                     (* no fail, check if es is unsat *)
    (* Solver.solver_detect_lhs_rhs_contra *)
    let unsat_check es =
      let pr = pr_list (add_str "map" (pr_pair !CF.print_hvar !CF.print_formula)) in
      let () = y_ninfo_hp pr es.CF.es_ho_vars_map in
      (* check if there is a contra which does not involve the HO instatiations *)
      let (_,contra_init), _ = detect_contra conseq es in
      (* "contra == false" denotes contradiction found *)
      if not(contra_init) then true (*  if there is a contra which is not related to HO, return and let the rest of the system handle this contra *)
      else
        let new_conseq = CF.subst_hvar conseq es.CF.es_ho_vars_map in
        let (_,contra_final), _ = detect_contra new_conseq es in
        contra_final
    in
    (* do not check for unsat if there is no entail state set *)
    let unsat_check es = map_opt_def true unsat_check es in
    (* do not check for unsat if there is no new HO *)
    map_list_def true (fun _ -> unsat_check es) new_ho

let check_for_ho_unsat detect_contra conseq match_ho_res =
  let _,_,_,_,es = match_ho_res in
  let pr1 = pr_option !CF.print_entail_state in
  Debug.no_1 "check_for_ho_unsat" pr1 string_of_bool (fun _ -> check_for_ho_unsat detect_contra conseq match_ho_res) es

let is_node_kind hform kind = CTPProjection.is_node_kind hform kind
let is_node_kind_rflow rflow kind = CTPProjection.is_node_kind_rflow rflow kind

let rebuild_SeqSor lnode rnode largs rargs =
  let sess_kind = ref TPProjection in
  let fnc si hform =
    match si.session_kind with
    | Projection   ->  let () = sess_kind := Projection in (CProjection.isSeqSor hform)
    | TPProjection ->  (CTPProjection.isSeqSor hform)
    | Protocol     ->  let () = sess_kind := Protocol in (CProtocol.isSeqSor hform)
  in
  let left = CForm.heap_node_transformer_basic fnc lnode in
  match left with
  | Some lnode0 -> [CForm.mk_rflow_formula_from_heap lnode0 ~sess_kind:(Some !sess_kind) (CF.pos_of_h_formula lnode0)], [CForm.mk_rflow_formula_from_heap rnode ~sess_kind:(Some !sess_kind) (CF.pos_of_h_formula rnode)], "Sess"
  | None -> largs,rargs, (CF.get_node_name_x lnode)

let rebuild_SeqSor lnode rnode largs rargs =
  let pr1 = !CF.print_h_formula in
  let pr2 = pr_list (!CF.print_rflow_formula) in
  Debug.no_4 "rebuild_SeqSor" pr1 pr1 pr2 pr2 (pr_triple pr2 pr2 pr_none) rebuild_SeqSor lnode rnode largs rargs

let struc_norm sf =
  let sf = wrap_one_seq_struc sf in
  let sf = wrap_last_seq_node_struc sf in
  let sf = x_add_1 irename_message_pointer_struc sf in
  sf

let formula_norm form =
  let form = wrap_one_seq form in
  let form = wrap_last_seq_node form in
  let form = x_add_1 irename_message_pointer form in
  form

let norm_case vb =  
  let vb = struc_norm vb in
  let vb = irename_all_session_pointer_struc vb in
  vb

let norm_case vb =  
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.norm_case" pr pr norm_case vb
  
let norm_slk_struct sf =
  let sf = update_temp_name_struc sf in
  let sf = struc_norm sf in
  sf

let norm_slk_struct sf =
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.norm_slk_struct" pr pr norm_slk_struct sf


let norm_slk_formula form =
  let form = update_temp_name form in
  let form = formula_norm form in
  form

let norm_slk_formula form =
  let pr = !F.print_formula in
  Debug.no_1 "Session.norm_slk_formula" pr pr norm_slk_formula form

