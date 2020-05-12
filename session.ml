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
module Ords = Sess_orders
module SC = Sesscommons

(*
use @P to parse protocol formulae
    @S to parse two-party formulae
    @M to parse multisession formulae
 *)

type transmission = TSend | TReceive
type proj_ident = ident * ident

let string_of_seq  = ";;"
let unk_view_id = "SESS_TEMP"

let session_fresh_id () = fresh_any_name session_msg_id_aux

let string_of_transmission t =
  match t with
  | TSend    -> "!"
  | TReceive -> "?"

(* prim predicates *)
let chan_id:  string option ref = ref None
let common_id:  string option ref = ref None
let seq_id :  string option ref = ref None
let trans_id: string option ref = ref None
let sess_id:  string option ref = ref None
let send_id:  string option ref = ref None
let recv_id:  string option ref = ref None
let sor_id:   string option ref = ref None
(* let pred_id:  string option ref = ref None *)
let msg_id:   string option ref = ref None
let event_id: string option ref = ref None
let hb_id: string option ref = ref None
let cb_id: string option ref = ref None
let assume_id: string option ref = ref None
let guard_id: string option ref = ref None
let peer_id: string option ref = ref None
let fence_id: string option ref = ref None

let set_rels_id id kind =
  match kind with
  | None -> ()
  | Some kind ->
    match kind with
    | Orders Event -> SC.event_rel_id := Some id
    | Orders CB    -> SC.cb_rel_id := Some id
    | Orders HB    -> SC.hb_rel_id := Some id
    | Orders HBP    -> SC.hbp_rel_id := Some id
    | Sleek Event -> SC.sevent_rel_id := Some id
    | Sleek CB    -> SC.scb_rel_id := Some id
    | Sleek HB    -> SC.shb_rel_id := Some id
    | Sleek HBP   -> SC.shbp_rel_id := Some id
    | Fence       -> SC.fence_rel_id := Some id
    | _ -> ()

let set_prim_pred_id kind id =
  (* let () = y_ninfo "setting Sess pred id" in *)
  match kind with
    | Sequence     -> seq_id := Some id
    | SOr          -> sor_id := Some id
    | Star         -> ()
    | SExists      -> ()
    | Send         -> send_id := Some id
    | Receive      -> recv_id := Some id
    | Transmission -> trans_id := Some id
    | HVar         -> ()
    | Predicate sess_order_kind  ->
        begin
            match sess_order_kind with
            | Order Event   -> event_id := Some id
            | Order HB      -> hb_id := Some id
            | Order CB      -> cb_id := Some id
            | Assert Assume  -> assume_id := Some id
            | Assert Guard   -> guard_id := Some id
            | Assert Peer    -> peer_id := Some id
            | Assert Fence   -> fence_id := Some id
            | _ -> ()
        end
    | Emp          -> ()
    | Session      -> sess_id := Some id
    | Channel      -> chan_id := Some id
    | Common       -> common_id := Some id
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
  | SExists      -> ""
  | Send         -> get_prim_pred_id send_id
  | Receive      -> get_prim_pred_id recv_id
  | Transmission -> get_prim_pred_id trans_id
  | HVar         -> ""
  | Predicate sess_order_kind  ->
        begin
            match sess_order_kind with
            | Order Event   -> get_prim_pred_id event_id
            | Order HB      -> get_prim_pred_id hb_id
            | Order CB      -> get_prim_pred_id cb_id
            | Assert Assume  -> get_prim_pred_id assume_id
            | Assert Guard   -> get_prim_pred_id guard_id
            | Assert Peer    -> get_prim_pred_id peer_id
            | Assert Fence   -> get_prim_pred_id fence_id
            | _ -> ""
        end
  | Emp          -> ""
  | Session      -> get_prim_pred_id sess_id
  | Channel      -> get_prim_pred_id chan_id
  | Common       -> get_prim_pred_id common_id
  | Msg          -> get_prim_pred_id msg_id

let exists_pred_kind name = match name with
    | Some n -> n
    | None -> ""

let get_pred_kind name =
    if name = (exists_pred_kind !event_id)
    then
       mk_sess_order_kind Event
    else if name = (exists_pred_kind !hb_id)
    then
        mk_sess_order_kind HB
    else if name = (exists_pred_kind !cb_id)
    then
        mk_sess_order_kind CB
    else if name = (exists_pred_kind !assume_id)
    then
        mk_sess_assert_kind Assume
    else if name = (exists_pred_kind !guard_id)
    then
       mk_sess_assert_kind Guard
    else if name = (exists_pred_kind !peer_id)
    then
       mk_sess_assert_kind Peer
    else if name = (exists_pred_kind !fence_id)
    then
       mk_sess_assert_kind Fence
    else
       NO_KIND

let get_session_kind_of_transmission t =
  match t with
  | TSend    -> Send
  | TReceive -> Receive

let rec string_of_param_list l = match l with
  | []        -> ""
  | h::[]     -> h
  | h::t      -> h ^ ", " ^ (string_of_param_list t)

let is_shb_rel str = String.compare str (map_opt_def "" (fun x -> x) !SC.shb_rel_id) == 0
let is_scb_rel str = String.compare str (map_opt_def "" (fun x -> x) !SC.scb_rel_id) == 0

(* ======= base formula for session type ====== *)
(* ============================================ *)
module IForm = struct
  type formula = F.formula
  type pure_formula = P.formula
  type h_formula = F.h_formula
  type h_formula_heap = F.h_formula_heap
  type ho_param_formula = F.rflow_formula
  type struc_formula = F.struc_formula
  type var = Globals.ident * VarGen.primed
  type flow = ident
  (* type node = var *)
  type exp = Ipure.exp
  type param = exp
  type arg = var (* node *) * ident * (ho_param_formula list) *
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
  let print_var = F.string_of_spec_var
  let print_pure_formula = F.print_pure_formula
  let print_param = IP.print_exp
  let mk_node (ptr, name, ho, params, pos) sk nk =
    let h = (F.mkHeapNode ptr name ho 0 false (*dr*) SPLIT0
               (P.ConstAnn(Mutable)) false false false None params [] None pos) in
    F.set_session_kind_h_formula h sk nk

  let mk_formula_heap_only ?flow:(flow=F.n_flow) h pos =
    F.formula_of_heap_with_flow h flow pos

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

  let mk_formula_of_pure_1 pure pos =
    F.formula_of_pure_1 pure pos

  let mk_struc_formula formula pos =
    F.mkEBase [] [] [] formula None pos

  let mk_star h1 h2 pos =
    F.mkStar h1 h2 pos

  let mk_star_formula f1 f2 pos =
    F.mkStar_formula f1 f2 pos

  let mk_exists vars hform pos =
    F.mkExists vars hform (IP.mkTrue pos) IvpermUtils.empty_vperm_sets F.n_flow [] pos

  let choose_ptr ?ptr:(str=session_def_id) () =
    (str,Unprimed)

  let mk_or f1 f2 pos =
    F.mkOr f1 f2 pos

  let mk_empty () = F.HEmp

  let mk_true () = IP.mkTrue no_pos

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
                            | Some Sequence -> hform
                            | _ -> mk_seq_wrapper_node hform pos sk) in
      Gen.map_opt_def hform fct node.F.h_formula_heap_session_info
    | F.Star node -> mk_seq_wrapper_node hform pos sk
    | _ -> hform

  let mk_exp_rel id args pos =
    (* let exp_var = List.fold_left (fun acc elem -> acc@[Ipure_D.Var elem]) [] args in *)
    let exp_var = args in
    let p_form = Ipure_D.RelForm (id, exp_var, pos) in
    let b_form = (p_form, None) in
    Ipure_D.BForm (b_form, None)

  (* let mk_exp_rel id args pos =
   *   let pr1 = pr_id in
   *   let pr2 = pr_list (pr_pair print_var pr_none) in
   *   let pr_out = !print_pure_formula in
   *   Debug.no_2 "mk_exp_rel" pr1 pr2 pr_out (fun _ _ -> mk_exp_rel id args pos) id args *)

  let join_conjunctions lst = Ipure.join_conjunctions lst

  let add_pure_to_formula pure formula = F.add_pure_formula_to_formula pure formula

  let id_to_param id pos = Ipure_D.Var((id,Unprimed), pos)

  let var_to_exp id pos = Ipure_D.Var(id, pos)

  let const_to_param c pos = Ipure_D.IConst(c, pos)

  let const_to_exp c pos = Ipure_D.IConst(c, pos)

  let fconst_to_param c pos = Ipure_D.FConst(c, pos)

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

  let transform_struc_formula_formula fct struc_form =
    let fcts = (nonef,fct,somef,(somef,somef,somef,somef,somef)) in
    F.transform_struc_formula fcts struc_form

  let map_one_rflow_formula fnc rflow_formula =
    F.map_one_rflow_formula fnc rflow_formula

  let map_rflow_formula_list fnc rflow_formula_list =
    List.map (map_one_rflow_formula fnc) rflow_formula_list

  let map_rflow_formula_list_res_h trans_f node =
    F.map_rflow_formula_list trans_f node

  let get_heap_node hform =
    match hform with
    | F.HeapNode node -> Some hform
    | _ -> None

  let get_node hform =
    match hform with
    | F.HeapNode node -> node
    | _ -> failwith "Session: get_node expects a HeapNode argument"

  let update_temp_heap_name si hform =
    match si.node_kind with
    | Some nk -> begin match nk with
      | Sequence | SOr | Send | Receive | Transmission
      | Session | Channel | Common | Msg ->
        let new_heap_name = get_prim_pred_id_by_kind nk in
        let updated_node  = F.set_heap_name hform new_heap_name in
        Some updated_node
      | Star | SExists | HVar | Predicate _ | Emp ->  None
      end
    | None -> None


  let update_temp_heap_name si hform =
    let pr = !print_h_formula in
    Debug.no_1 "Session.update_temp_heap_name" pr (pr_opt pr) (update_temp_heap_name si) hform

  let set_heap_node_var var node =
    F.HeapNode {node with F.h_formula_heap_node = var;}

  let set_anns hform ann =
    F.set_sess_ann hform ann

  let get_heap_node_var node =
    node.F.h_formula_heap_node

  let subst_param  (sst: (var * var) list) p = IP.subst_exp sst p

  let subst_var    (sst: (var * var) list) p = F.subst_var_list sst p

  let subst_formula (sst: (var * var) list) f = F.subst_all sst f

  let fresh_var (v:var): var = IP.fresh_var v

  let eq_var = IP.eq_var

  let mk_var id = (id, Unprimed)

  let join_vars var1 var2 separator =
    let id1, _ = var1 in
    let id2, _ = var2 in
    (id1 ^ separator ^ id2, Unprimed)

  let divide_vars var separator = failwith x_tbi

  let is_base_formula formula =
    match formula with
      | F.Base f -> true
      | _ -> false

  let is_exists_formula formula =
    match formula with
      | F.Exists f -> true
      | _ -> false

  let get_h_formula formula =
    let h, p, vp, fl, a = F.split_components formula in
    h

  let get_pure_formula formula =
    let _, p, _, _, _ = F.split_components formula in
    p

  let get_h_formula_from_ho_param_formula rflow_formula =
    let f = rflow_formula.F.rflow_base in
    get_h_formula f

  let get_formula_from_ho_param_formula rflow_formula =
    rflow_formula.F.rflow_base

  let get_ho_param node =
    node.F.h_formula_heap_ho_arguments

  let get_node_kind h_formula =
    match h_formula with
    | F.HeapNode node -> (match node.F.h_formula_heap_session_info with
        | None -> failwith (x_loc ^ ": Expected session information.")
        | Some si -> begin
            match si.node_kind with
            | Some nk -> nk
            | None -> failwith (x_loc ^ ": Expected session information.") end )
    | F.Star node -> Star
    | F.HVar (sv, svl) -> HVar
    | F.HEmp -> Emp
    | _ -> failwith (x_loc ^ ": Not a valid heap formula for session.")

  let get_anns h_form =
    match h_form with
    | F.HeapNode node -> node.F.h_formula_heap_sess_ann
    | _ -> failwith (x_loc ^ ": F.HeapNode expected.")

  let get_exists_vars formula =
    match formula with
      | F.Exists f -> f.F.formula_exists_qvars
      | _ -> failwith (x_loc ^ ": F.Exists expected.")

  let get_formula_pos formula =
    F.pos_of_formula formula

  let rec get_session_kind h_formula =
    match h_formula with
    | F.HeapNode node -> (match node.F.h_formula_heap_session_info with
        | Some si -> si.session_kind
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

  let get_session_info h_formula =
    match h_formula with
      | F.HeapNode hn -> hn.h_formula_heap_session_info
      | _ -> None

  let get_view_session_info hnode =
    hnode.F.h_formula_heap_session_info

  let get_heap_node hform =
    match hform with
    | F.HeapNode node -> Some hform
    | _ -> None

  let get_node_only hform =
    match hform with
    | F.HeapNode node -> node
    | _ -> failwith "Session: get_node expects a HeapNode argument"

  let get_node_opt hform =
    match hform with
    | F.HeapNode node -> Some node
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

  let append_tail disjunct tail = failwith "TBI"

end;;

module CForm = struct
  type formula = CF.formula
  type pure_formula = CP.formula
  type h_formula = CF.h_formula
  type h_formula_heap = CF.h_formula_view
  type ho_param_formula = CF.rflow_formula
  type struc_formula = CF.struc_formula
  type var = CP.spec_var
  type flow = CF.flow_formula
  (* type node = var *)
  type exp = CP.exp
  type param = CP.spec_var
  type arg = var * ident * (ho_param_formula list) *
             (param list) * VarGen.loc

  let is_emp f = failwith x_tbi
  let print    = CF.print_formula
  let print_h_formula = CF.print_h_formula
  let print_ho_param_formula = CF.print_rflow_formula
  let print_struc_formula = CF.print_struc_formula
  let print_var = CF.string_of_spec_var
  let print_pure_formula = CF.print_pure_f
  let print_param = ref print_var

  let fresh_var (v:var): var = CP.fresh_spec_var v
  let eq_var = CP.eq_spec_var
  let mk_var id = CP.mk_spec_var id

  let join_vars var1 var2 separator = match var1, var2 with
    | CP.SpecVar (t1, id1, prmd), CP.SpecVar (_, id2, _) ->
        CP.SpecVar (t1, id1 ^ separator ^ id2, prmd) (* keeps the primed argument from the first var *)

  let divide_vars var separator = match var with
    | CP.SpecVar (t, id, prmd) ->
        let vars = Str.split (Str.regexp separator) id in
        match vars with
        | id1::id2::[] ->
          (CP.SpecVar (t, id1, prmd), CP.SpecVar (t, id2, prmd))
        | _ -> failwith "The var cannot be divided"

  let mk_node (ptr, name, ho, params, pos) sk nk =
    let h = CF.mkViewNode ptr name params pos in
    match h with
      | CF.ViewNode node -> CF.ViewNode {node with CF.h_formula_view_ho_arguments = ho;
                                                   CF.h_formula_view_session_info = Some (mk_view_session_info ~sk:sk ~nk:nk ())}
      | _ -> failwith (x_loc ^ ": CF.ViewNode expected.")

  let mk_formula_heap_only  ?flow:(flow=CF.mkNormalFlow ()) h pos =
    CF.formula_of_heap_fl h flow pos

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

  let mk_rflow_formula_from_heap h ?sess_kind:(sess_kind=None) ?kind:(k=NEUTRAL) pos =
    let pr1 = !print_h_formula in
    let pr2 = !print_ho_param_formula in
    Debug.no_1 "Session.mk_rflow_formula_from_heap" pr1 pr2
      (fun _ -> mk_rflow_formula_from_heap h ~sess_kind:sess_kind ~kind:k pos) h

  let mk_formula pure (ptr, name, ho, params, pos) sk nk =
    let h = mk_node (ptr, name, ho, params, pos) sk nk in
    let mix_formula = MCP.OnePF pure in
    CF.mkBase_simp h mix_formula

  let mk_formula_of_pure_1 pure pos =
    CF.formula_of_pure_formula pure pos

  let mk_struc_formula formula pos =
    CF.mkEBase formula None pos

  let mk_star h1 h2 pos =
    CF.mkStarH h1 h2 pos

  let mk_star_formula f1 f2 pos =
    CF.mkStar f1 f2 CF.Flow_combine pos

  let mk_exists vars hform pos =
    let vars = List.map (fun x -> CP.SpecVar (UNK, (fst x), (snd x))) vars in
    let mix_formula = MCP.mix_of_pure (CP.mkTrue pos) in
    CF.mkExists vars hform mix_formula CvpermUtils.empty_vperm_sets CF.TypeEmpty (CF.mkTrueFlow ()) [] pos

  let choose_ptr ?ptr:(str=session_def_id) () =
    CP.SpecVar(UNK,str,Unprimed)

  let mk_or f1 f2 pos =
    CF.mkOr f1 f2 pos

  let mk_empty () = CF.HEmp

  let mk_true () = CP.mkTrue no_pos

  let mk_hvar id ls =
    let id = CP.SpecVar(UNK, id, Unprimed) in
    (* let ls = List.map (fun x -> CP.SpecVar(UNK, x, Unprimed)) ls in *)
    CF.HVar(id, ls)

  let mk_seq_wrapper ?sess_kind:(sess_kind=None) hform pos sk = hform

  let mk_exp_rel id args pos =
    let sv = mk_var id in
    (* let exp_var = List.fold_left (fun acc elem -> acc@[CP.Var elem]) [] args in *)
    let exp_var = args in
    let p_form = CP.RelForm (sv, exp_var, pos) in
    let b_form = (p_form, None) in
    CP.BForm (b_form, None)

  (* let mk_exp_rel id args pos =
   *   let pr1 = pr_id in
   *   let pr2 = pr_list (pr_pair print_var pr_none) in
   *   let pr_out = !print_pure_formula in
   *   Debug.no_2 "mk_exp_rel" pr1 pr2 pr_out (fun _ _ -> mk_exp_rel id args pos) id args *)

  let join_conjunctions lst = CP.join_conjunctions lst

  let add_pure_to_formula pure formula = CF.add_pure_formula_to_formula pure formula

  let id_to_param id pos = CP.SpecVar(UNK,id,Unprimed)

  let var_to_exp id pos =  CP.Var (id,pos)

  let const_to_param c pos = failwith x_tbi

  let const_to_exp c pos = failwith x_tbi

  let fconst_to_param c pos = failwith x_tbi

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

  let transform_struc_formula_formula fct struc_form =
    let fcts = (nonef,fct,somef,(somef,somef,somef,somef,somef)) in
    CF.transform_struc_formula fcts struc_form

  let map_one_rflow_formula fnc rflow_formula =
    CF.map_one_rflow_formula fnc rflow_formula

  let map_rflow_formula_list fnc rflow_formula_list =
    List.map (map_one_rflow_formula fnc) rflow_formula_list

  let map_rflow_formula_list_res_h trans_f node =
    CF.map_rflow_formula_list trans_f node

  let get_heap_node hform =
    match hform with
    | CF.ViewNode node -> Some hform
    | _ -> None

  let get_node hform =
    match hform with
    | CF.ViewNode node -> node
    | _ -> failwith "Session: get_node expects a ViewNode argument"

  let update_temp_heap_name si hform = None

  let set_heap_node_var var node =
    CF.ViewNode {node with CF.h_formula_view_node = var;}

  let set_anns hform ann =
    CF.set_sess_ann hform ann

  let get_heap_node_var node = node.CF.h_formula_view_node

  let subst_param  (sst: (var * var) list) p =
    try  let _,res = List.find (fun (a,_) -> CP.eq_spec_var a p) sst in res
    with Not_found -> p

  let subst_var  (sst: (var * var) list) v =
    try  let _,res = List.find (fun (a,_) -> CP.eq_spec_var a v) sst in res
    with Not_found -> v

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
        | Some si ->
          ( match si.node_kind with
            | Some nk -> nk
            | None -> failwith (x_loc ^ ": Expected session information."))
        | None -> failwith (x_loc ^ ": Expected session information."))
    | CF.Star node -> Star
    | CF.HVar (sv, svl) -> HVar
    | CF.HEmp -> Emp
    | _ -> failwith (x_loc ^ ": Not a valid heap formula for session.")

  let get_anns h_formula =
    match h_formula with
    | CF.ViewNode node -> node.CF.h_formula_view_sess_ann
    | _ -> failwith (x_loc ^ ": CF.ViewNode expected.")

  let get_exists_vars formula =
    match formula with
      | CF.Exists f -> List.map (fun x -> match x with
                                            | CP.SpecVar sv -> let _, id, primed = sv in
                                          (id, primed))
                       f.formula_exists_qvars
      | _ -> failwith (x_loc ^ ": CF.Exists expected.")

  let get_formula_pos formula =
    CF.pos_of_formula formula

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

  let is_exists_formula formula =
    match formula with
    | CF.Exists f -> true
    | _ -> false

  let get_h_formula formula =
    let h, p, vp, fl, t, a = CF.split_components formula in
    h

  let get_h_formula formula =
    Debug.no_1 "get_h_formula" !print !print_h_formula get_h_formula formula

  let get_pure_formula formula =
    let _, p, _, _, _, _ = CF.split_components formula in
    (MCP.pure_of_mix p)

  let get_h_formula_from_ho_param_formula rflow_formula =
    let f = rflow_formula.CF.rflow_base in
    get_h_formula f

  let get_formula_from_ho_param_formula rflow_formula =
    rflow_formula.CF.rflow_base

  let get_ho_param node =
    node.CF.h_formula_view_ho_arguments

  let get_hvar node =
    match node with
    | CF.HVar (id, ls) -> let id = get_param_id id in
      (id, ls)
    | _ -> failwith (x_loc ^ ": CF.HVar expected.")

  let get_session_info h_formula =
    match h_formula with
    | CF.ViewNode vn -> vn.h_formula_view_session_info
    | _ -> None

  let get_view_session_info hnode =
    hnode.CF.h_formula_view_session_info

  let get_heap_node hform =
    match hform with
    | CF.ViewNode node -> Some hform
    | _ -> None

  let get_node_only hform =
    match hform with
    | CF.ViewNode node -> node
    | _ -> failwith "Session: get_node expects a ViewNode argument"

  let get_node_opt hform =
    match hform with
    | CF.ViewNode node -> Some node
    | _ -> None

  let get_h_formula_safe f = failwith x_tbi

  let get_h_formula_from_struc_formula_safe struc_formula = failwith x_tbi

  (* let rec extract_bases session = *)
  (*   let node_kind = get_node_kind session in  *)
  (*   match node_kind with *)
  (*   | Sequence s -> *)
  (*     let node = get_node_only session in *)
  (*     let ho_args = get_ho_param node in *)
  (*     let ho_args = List.map (fun arg -> get_h_formula_from_ho_param_formula arg) ho_args in *)
  (*     let ho_args = List.map () ho_args in *)
  (*     (extract_bases s.session_seq_formula_head) @ *)
  (*               (extract_bases s.session_seq_formula_tail) *)
  (*   | _  -> [session] *)

  (* let rec mk_norm_session bases = *)
  (*   match bases with *)
  (*   | [] -> SEmp *)
  (*   | [base] -> base *)
  (*   | hd :: tl -> let pos = get_pos hd in *)
  (*     mk_session_seq_formula hd (mk_norm_session tl) pos *)

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
  (* let norm3_sequence session = *)
  (*   let bases = extract_bases session in *)
  (*   mk_norm_session bases *)

  let sor_disj_list head =
    let node = get_node_only head in
    let ho_disj = get_ho_param node in
    let disj =
      match ho_disj with
      | [] -> failwith "a SOr node should have at least one HO"
      | h::[] -> get_formula_from_ho_param_formula h
      | _ -> failwith "a SOr node should have at least one HO"
    in let disj_lst = CF.list_of_disjs disj in
    disj_lst

  let append_tail disjunct tail =
    let pos = CF.pos_of_h_formula disjunct in
    let ptr = get_heap_node_var (get_node_only disjunct) in
    let name = get_prim_pred_id seq_id in
    (*let h2 = Base.mk_seq_wrapper h2 pos Base.base_type in *)
    let args = [disjunct; tail] in
    let args = List.map (fun a -> mk_rflow_formula_from_heap a ~sess_kind:(get_session_kind disjunct) pos) args in
    let params = [] in
    mk_node (ptr, name, args, params, pos) (get_session_kind disjunct) Sequence
  (* mk_session_seq_formula disjunct tail pos *)

  let append_tail disjunct tail =
    let pr1 = !print_h_formula in
    Debug.no_2 "Session.append_tail" pr1 pr1 pr1 append_tail disjunct tail

  (* Split a SOr predicate into disjuncts.
   * 2. get list of disjuncts from head
   * 3. for each disjunct, append tail
   * 4. for each disjunct, normalize
  *)
  let split_sor (head: ho_param_formula) (tail:ho_param_formula option)
    : ho_param_formula list =
    let head_session = get_h_formula_from_ho_param_formula head in
    let disj_list = sor_disj_list head_session in
    let disj_list =
      let tail_session =
        match tail with
        | None      -> mk_empty ()
        | Some tail -> get_h_formula_from_ho_param_formula tail
      in
      let disj_list = List.map (fun x -> append_tail (get_h_formula x) tail_session) disj_list in
      disj_list in

    (* let disj_list = List.map (fun x -> norm3_sequence x) disj_list in *)
    let disj_list = List.map (fun x -> mk_rflow_formula_from_heap x ~sess_kind:(get_session_kind head_session) no_pos) disj_list in
    disj_list
end;;

module type Msg_common_type =
  functor (Msg: SC.Message_type) ->
sig
  (* include SC.Message_type *)
  (* open Msg *)
  include (module type of Msg)
  (* include Msg *)
  val get_base_ptr: var -> h_formula_heap option -> var
  val heap_transformer: (view_session_info -> h_formula -> h_formula option) -> h_formula -> h_formula option
  val loop_through_rflow: (h_formula -> h_formula option) -> h_formula -> h_formula option
  val heap_node_transformer:  ?flow:bool -> (view_session_info -> h_formula -> h_formula option) -> h_formula -> h_formula option
  val heap_node_transformer_basic: ?flow:bool -> (view_session_info -> h_formula -> h_formula option) -> h_formula -> h_formula option
  val heap_node_transformer_gen: ?flow:bool -> ?include_msg:bool -> (Globals.view_session_info -> h_formula -> h_formula option) -> h_formula -> h_formula option
end;;

module Message_commons =
  functor  (Msg: SC.Message_type) ->
  struct
    include Msg

    let get_base_ptr def_id node =
      match node with
      | None -> def_id
      | Some node -> Msg.get_heap_node_var node

    let loop_through_rflow helper hform =
      let f_h nh =
        match get_heap_node nh with
        | None -> None
        | Some nh ->
          let node_new = get_node_only nh in
          let trans_f = transform_formula helper in
          Some (map_rflow_formula_list_res_h trans_f node_new)
      in
      Some (transform_h_formula f_h hform)

    let heap_transformer h_fnc hform =
      let rec helper h_fnc hform =
        match get_heap_node hform with
        | None -> None
        | Some hform ->
          match get_session_info hform with
          | None    ->
            (* loop through HO param until reaching a session formula *)
            loop_through_rflow (helper h_fnc) hform
          | Some si -> h_fnc si hform
      in helper h_fnc hform

    let loop_through_rflow helper hform =
      let pr = !print_h_formula in
      Debug.no_1 "Session.loop_through_rflow" pr (pr_opt pr) (fun _ -> loop_through_rflow helper hform) hform

    let heap_node_transformer_basic ?flow:(include_flow=false) fnc hform =
      match get_heap_node hform with
      | None -> None
      | Some hform ->
        let hform_opt  =
          match get_session_info hform with
          | None    ->  None
          | Some si ->  fnc si hform
        in hform_opt

    (* calls h_fnc on
       (i) first session node of hform if include_flow is set
       (ii) all nodes of hform -incl. nested HO args- otherwise
    *)
    let heap_node_transformer ?flow:(include_flow=false) h_fnc hform =
      let rec helper h_fnc hform =
        match get_heap_node hform with
        | None -> None
        | Some hform ->
          (* let node = Base.get_node_only hform in  *)
          match get_session_info hform with
          | None    ->
            (* loop through HO param until reaching a session formula *)
            loop_through_rflow (helper h_fnc) hform
          | Some si ->
            let new_heap = h_fnc si hform in
            if not(include_flow) then new_heap (* it's a session related node, but its transformation should stop at this level - do not attempt to transform its HO args *)
            else
              let new_heap =
                match new_heap with
                | None   ->  hform
                | Some e ->  e in
              loop_through_rflow (helper h_fnc) new_heap
      in helper h_fnc hform

    (* allows the transformation of nested chan specifications if include_msg is set
       eg c1::Chan{@S !v#v::Chan{@S !0}<this>}<this>
       h_fnc c1::Chan{@S !v#v::Chan{@S !0}<this>}<this>
       h_fnc v::Chan{@S !0}<this>
    *)
    let heap_node_transformer_gen ?flow:(include_flow=false) ?include_msg:(include_msg=false) h_fnc hform =
      let res = heap_node_transformer ~flow:include_flow h_fnc hform in
      if not(include_msg) then res
      else
        let updated_hform =
          match res with
          | None -> hform
          | Some hform -> hform in
        let fnc2 si hform =
          match si.node_kind with
          | Some Send | Some Receive -> loop_through_rflow (heap_node_transformer h_fnc) hform
          | _ -> None
        in
        heap_node_transformer ~flow:true fnc2 updated_hform

    let set_heap_node_var_opt var hform =
      match get_heap_node hform with
      | None -> None
      | Some hform -> Some (set_heap_node_var var (get_node_only hform))

    let set_heap_node_var_opt ?flow:(flow=false) var hform =
      let fnc si = set_heap_node_var_opt var in
      heap_node_transformer ~flow:flow fnc hform

    let set_heap_node_var_opt ?flow:(flow=false) var hform =
      let pr1 = get_node_id in
      let pr2 = !print_h_formula in
      Debug.no_2 "Session.set_heap_node_var_opt" pr1 pr2 (pr_opt pr2) (fun _ _ -> set_heap_node_var_opt ~flow:flow var hform) var hform

    (* can't really use the heap_node_transformer_gen gen here cause it needs to collect info from the last non-sess node *)
    let set_heap_node_to_chan_node hform =
      let rec helper var hform =
        match get_heap_node hform with
        | None -> None
        | Some hform ->
          let node = get_node_only hform in
          let si =  get_view_session_info node in
          match si with
          | None   ->
            let var = Some (get_heap_node_var node) in
            loop_through_rflow (helper var) hform (* call helper here to make sure we update the innermost  var ptr until hitting a session formula *)
          | Some si ->
            let var = match var with
              | None     -> (get_heap_node_var node)
              | Some var -> var (* apply transformer here *)
            in
            let loop_through_rflow_helper var_current_node var_for_loop =
              let hform =
                match x_add set_heap_node_var_opt var_current_node hform with
                | None -> hform
                | Some h -> h in
              loop_through_rflow (helper var_for_loop) hform in
            match si.node_kind with
            | Some Send | Some Receive -> loop_through_rflow_helper var None (* reset the var for send/receive messages *)
            |_ -> loop_through_rflow_helper var (Some var)
      in helper None hform

  end;;

(* inst for iformula & cformula *)
module Protocol_base_formula =
  (* functor  (Msg: Msg_common_type) -> *)
  functor  (Form: SC.Message_type) ->
struct
    module Msg = Message_commons(Form)
    include Msg
    type t = Msg.formula
    type role = Msg.var
    type chan = Msg.var
    type suid = Msg.var
    (* type var  = Msg.var *)
    type a = role * role * chan option * var * VarGen.loc * suid
    type base = {
      protocol_base_formula_sender      : role;
      protocol_base_formula_receiver    : role;
      protocol_base_formula_chan        : chan option;
      protocol_base_formula_message     : t;
      protocol_base_formula_message_var : var;
      protocol_base_formula_heap_node   : Msg.h_formula_heap option;
      protocol_base_formula_pos         : VarGen.loc;
      protocol_base_formula_uid         : suid;
    }

    let base_type = Protocol

    let print_message f = !Msg.print f.protocol_base_formula_message

    let def_suid = Msg.mk_var def_suid_name
    let eq_suid = Msg.eq_var
    let mk_suid name = Msg.mk_var name
    let mk_chan name = Msg.mk_var name
    let mk_role name = Msg.mk_var name

    let eq_role = Msg.eq_var
    let eq_chan = Msg.eq_var

    let string_of_role = Msg.print_var
    let string_of_chan = Msg.print_var
    let string_of_suid = Msg.print_var

    let string_of_session_base f =
      let pr = string_of_role in
      let suid = f.protocol_base_formula_uid in
      let suid = if eq_suid suid def_suid  then "" else "@"^ (string_of_suid suid) ^ ":"  in
      let chan =
        match f.protocol_base_formula_chan with
        | None -> ""
        | Some c -> string_of_chan c
      in
      suid ^ (pr f.protocol_base_formula_sender) ^ " -> " ^ (pr f.protocol_base_formula_receiver) ^ " : "^ chan ^ "("^ (print_message f) ^ ")"

    let mk_base (sender, receiver, chan, mv, pos, suid) ?node:(node=None) formula = {
      protocol_base_formula_sender    = sender;
      protocol_base_formula_receiver  = receiver;
      protocol_base_formula_chan      = chan;
      protocol_base_formula_message   = formula;
      protocol_base_formula_message_var = mv;
      protocol_base_formula_heap_node = node;
      protocol_base_formula_pos       = pos;
      protocol_base_formula_uid       = suid;
    }

    let get_session_heap_node s = s.protocol_base_formula_heap_node

    let trans_base base =
      let ptr = Msg.get_base_ptr (Msg.mk_var session_msg_id) base.protocol_base_formula_heap_node in
      let name = get_prim_pred_id trans_id in
      let args = [Msg.mk_rflow_formula ~sess_kind:(Some base_type) base.protocol_base_formula_message] in
      let params = [base.protocol_base_formula_sender; base.protocol_base_formula_receiver] in
      let params = List.map (fun a -> Msg.var_to_param a base.protocol_base_formula_pos) params in
      Msg.mk_node (ptr, name, args, params, base.protocol_base_formula_pos) base_type Transmission

    let get_base_pos base = base.protocol_base_formula_pos

    let get_message_var base = base.protocol_base_formula_message_var

    let get_chan base = base.protocol_base_formula_chan

    let get_message base = base.protocol_base_formula_message

    let get_sender base = base.protocol_base_formula_sender

    let get_receiver base = base.protocol_base_formula_receiver

    let get_uid base = base.protocol_base_formula_uid

    let trans_h_formula_to_session_base h_formula = failwith x_tbi

    let subst_base (sst: (Msg.var * Msg.var) list) (msg: base): base = msg

  end;;

(* inst for iformula & cformula *)
module Projection_base_formula =
  (* functor  (Msg: Msg_common_type) -> *)
  functor  (Form: SC.Message_type) ->
struct
    module Msg = Message_commons(Form)
    include Msg
    type t = Msg.formula
    type chan = Msg.var
    type a = transmission * chan * var * VarGen.loc
    type base = {
      projection_base_formula_op          : transmission;
      projection_base_formula_channel     : chan;
      projection_base_formula_message     : t;
      projection_base_formula_message_var : var;
      projection_base_formula_heap_node   : h_formula_heap option;
      projection_base_formula_pos         : VarGen.loc;
    }

    let base_type = Projection

    let eq_chan = Msg.eq_var

    let print_message f = !Msg.print f.projection_base_formula_message

    let string_of_chan = Msg.print_var

    let string_of_session_base f =
      (string_of_chan f.projection_base_formula_channel) ^
      (string_of_transmission f.projection_base_formula_op) ^
      (Msg.print_var f.projection_base_formula_message_var) ^ "#" ^
      "(" ^ (print_message f) ^ ")"

    let mk_base (transmission, channel, mv, pos) ?node:(node=None) formula = {
      projection_base_formula_op          = transmission;
      projection_base_formula_channel     = channel;
      projection_base_formula_message     = formula;
      projection_base_formula_message_var = mv;
      projection_base_formula_heap_node   = node;
      projection_base_formula_pos         = pos;
    }

    let get_session_heap_node s = s.projection_base_formula_heap_node

    let trans_base base =
      let ptr = Msg.get_base_ptr base.projection_base_formula_channel base.projection_base_formula_heap_node in
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
      Debug.no_1 "Session.trans_base" pr1 pr2 trans_base base

    let get_base_transmission base = base.projection_base_formula_op

    let get_channel base = base.projection_base_formula_channel

    let get_message base = base.projection_base_formula_message

    let get_message_var base = base.projection_base_formula_message_var

    let get_base_pos base = base.projection_base_formula_pos

    let trans_h_formula_to_session_base h_formula =
      let (ptr, name, hoargs, params, pos) = Msg.get_node h_formula in
      let channel = ptr in
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
      mk_base (transmission, channel, mv, pos) ~node:(Msg.get_node_opt h_formula) f

    let trans_h_formula_to_session_base h_formula =
      let pr1 = !Msg.print_h_formula in
      let pr2 = string_of_session_base in
      Debug.no_1 "Session.trans_h_formula_to_session_base" pr1 pr2 trans_h_formula_to_session_base h_formula

    let subst_base (sst: (Msg.var * Msg.var) list) (msg: base): base =
      { msg with
        projection_base_formula_message = subst_formula sst msg.projection_base_formula_message;
        projection_base_formula_message_var = subst_var sst msg.projection_base_formula_message_var; }

  end;;

module TPProjection_base_formula =
  (* functor  (Msg: Msg_common_type) -> *)
  functor  (Form: SC.Message_type) ->
struct
    module Msg = Message_commons(Form)
    include Msg
    type t = Msg.formula
    type a = transmission * var * VarGen.loc
    type base = {
      tpprojection_base_formula_op          : transmission;
      tpprojection_base_formula_message     : t;
      tpprojection_base_formula_message_var : var;
      tpprojection_base_formula_heap_node   : h_formula_heap option;
      tpprojection_base_formula_pos         : VarGen.loc;
    }

    let base_type = TPProjection

    let print_message f = !Msg.print f.tpprojection_base_formula_message

    let string_of_session_base f =
      (string_of_transmission f.tpprojection_base_formula_op) ^
      (Msg.print_var f.tpprojection_base_formula_message_var) ^ "#" ^
      "(" ^ (print_message f) ^ ")"

    let mk_base (transmission, mv, pos) ?node:(node=None) formula = {
      tpprojection_base_formula_op          = transmission;
      tpprojection_base_formula_message     = formula;
      tpprojection_base_formula_message_var = mv;
      tpprojection_base_formula_heap_node   = node;
      tpprojection_base_formula_pos         = pos;
    }

    let get_session_heap_node s = s.tpprojection_base_formula_heap_node

    (* TODO: include the node info *)
    let trans_base base =
      let ptr = Msg.get_base_ptr (Msg.mk_var session_chan_id) base.tpprojection_base_formula_heap_node in (* Msg.choose_ptr ~ptr:session_chan_id () in *)
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
      Debug.no_1 "Session.trans_base" pr1 pr2 trans_base base

    let get_base_pos base = base.tpprojection_base_formula_pos

    let get_message_var base = base.tpprojection_base_formula_message_var

    let get_message base = base.tpprojection_base_formula_message

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
      mk_base (transmission, mv, pos) ~node:(Msg.get_node_opt h_formula) f

    let subst_base (sst: (Msg.var * Msg.var) list) (msg: base): base =
      { msg with
        tpprojection_base_formula_message = subst_formula sst msg.tpprojection_base_formula_message;
        tpprojection_base_formula_message_var = subst_var sst msg.tpprojection_base_formula_message_var; }

  end;;

module type Session_base =
  functor (Msg: SC.Message_type) ->
sig
  (* include Msg *)
  include (module type of Message_commons(Msg))
  (* include Msg_common_type *)
  type t
  type a
  type base

  val base_type : session_kind
  val string_of_session_base : base -> string
  val mk_base : a -> ?node:h_formula_heap option -> t -> base
  val get_session_heap_node: base -> h_formula_heap option
  (* val get_base_ptr: ident -> h_formula_heap option -> var *)
  val trans_base : base -> h_formula
  val get_base_pos : base -> VarGen.loc
  val get_message_var : base -> var
  val get_message : base -> t
  val trans_h_formula_to_session_base : h_formula -> base
  val subst_base: ((var * var) list) -> base -> base
end;;

(* ============== session type ================ *)
(* ============================================ *)
module Make_Session (Base: Session_base) (Form: SC.Message_type) =
struct
  (* module Msg  = Message_commons(Form) *)
  module Base = Base(Form)
  module O2F  = Ords.Orders2Form(Form)
  module Orders = O2F.Ord
  type t = Base.base

  type session =
    | SSeq  of session_seq_formula
    | SOr   of session_or_formula
    | SStar of session_star_formula
    | SExists of session_exists_formula
    | SBase of session_base
    | SEmp

  and session_base =
    | Base of t
    | Predicate of session_predicate
    | HVar of session_hvar

  and session_seq_formula = {
    session_seq_formula_head: session;
    session_seq_formula_tail: session;
    session_seq_formula_heap_node: Base.h_formula_heap option;
    session_seq_formula_pos:  loc;
  }

  and session_or_formula = {
    session_sor_formula_or1: session;
    session_sor_formula_or2: session;
    session_sor_formula_heap_node: Base.h_formula_heap option;
    session_sor_formula_pos:  loc;
  }

  and session_star_formula = {
    session_star_formula_star1: session;
    session_star_formula_star2: session;
    session_star_formula_heap_node: Base.h_formula_heap option;
    session_star_formula_pos:  loc;
  }

  and session_exists_formula = {
    (* TODO tina: do we need a heap_node field? what is it used for? *)
    session_exists_formula_vars: (ident * primed) list;
    session_exists_formula_session: session;
    session_exists_formula_pos: loc;
  }

  (* and session_fence = { *)
  (*   session_fence_role1: ident; *)
  (*   session_fence_role2: ident; *)
  (*   session_fence_pred: session_predicate; *)
  (* } *)

  and session_predicate = {
    session_predicate_name: ident;
    session_predicate_ho_vars: (* (ho_flow_kind * ident * ho_split_kind) *) Base.ho_param_formula list;
    session_predicate_params: Base.param list;
    session_predicate_formula_heap_node: Base.h_formula_heap option;
    session_predicate_pure: Base.pure_formula;
    session_predicate_pos: loc;
    session_predicate_anns: sess_ann;
    session_predicate_orders: Orders.assrt;
    session_predicate_kind: session_predicate_kind;
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
    | SExists s -> string_of_session_exists s
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
    "(" ^ string_of_one_session s.session_sor_formula_or1 ^ ") " ^
    "or" ^
    " (" ^ string_of_one_session s.session_sor_formula_or2 ^ ")"

  and string_of_session_star s =
    "(" ^ string_of_one_session s.session_star_formula_star1 ^ ") " ^
    "*" ^
    " (" ^ string_of_one_session s.session_star_formula_star2 ^ ")"

  and string_of_session_exists s =
    "exists " ^ (pr_list (fun x -> fst x) s.session_exists_formula_vars) ^
    ": " ^ string_of_one_session s.session_exists_formula_session

  (* and string_of_session_fence f = *)
  (*       "[" ^ f.session_fence_role1 ^ ", " ^ f.session_fence_role2 ^ "]: " ^ *)
  (*   string_of_session_predicate f.session_fence_pred *)

  and string_of_session_predicate s =
    let orders = s.session_predicate_orders in
    if not (Orders.is_assrt orders) then
         s.session_predicate_name ^
         "{" ^ ((pr_list !Base.print_ho_param_formula) s.session_predicate_ho_vars) ^ "}" ^
         "<" ^ ((pr_list !Base.print_param) s.session_predicate_params) ^ ">"
    else
      s.session_predicate_name ^
      "{" ^ ( Orders.string_of orders) ^ "}"

  and string_of_session_hvar s =
    "%" ^ s.session_hvar_id

  let is_emp sess = match sess with
    | SEmp -> true
    | _    -> false

  let get_session_heap_node s =
    match s with
    | SSeq s  -> s.session_seq_formula_heap_node
    | SOr s   -> s.session_sor_formula_heap_node
    | SStar s -> s.session_star_formula_heap_node
(* TODO: review this *)
    | SExists s -> None
    | SEmp    -> None
    | SBase s -> match s with
      | Base s -> Base.get_session_heap_node s
      | Predicate s -> s.session_predicate_formula_heap_node
      | _ -> None

  let mk_base_x a b = Base (Base.mk_base a b)

  let rec mk_base a b =
    let pr =  pr_none  in
    let pr_out = string_of_session_base in
    Debug.no_1 "Session.mk_base" pr pr_out (mk_base_x a) b

  and mk_session_seq_formula session1 session2 ?node:(node=None) loc =
    let node =
      match node with
      | Some node -> Some node
      | None -> get_session_heap_node session1
        (* session1.session_seq_formula_heap_node *)
        (* Some (Base.get_node_only (mk_seq_node (Base.mk_empty ())  (Base.mk_empty ())  None loc)) *)
    in
    SSeq {
      session_seq_formula_head = session1;
      session_seq_formula_tail = session2;
      session_seq_formula_heap_node = node;
      session_seq_formula_pos  = loc;
    }

  and mk_session_or_formula session1 session2 ?node:(node=None) loc =
    let node =
      match node with
      | Some node -> Some node
      | None -> get_session_heap_node session1  in
    SOr {
      session_sor_formula_or1 = session1;
      session_sor_formula_or2 = session2;
      session_sor_formula_heap_node = node;
      session_sor_formula_pos = loc;
    }

  and mk_session_star_formula session1 session2 ?node:(node=None) loc =
    let node =
      match node with
      | Some node -> Some node
      | None -> get_session_heap_node session1  in
    SStar {
      session_star_formula_star1 = session1;
      session_star_formula_star2 = session2;
      session_star_formula_heap_node = node;
      session_star_formula_pos   = loc;
    }

  and mk_session_exists_formula vars session loc =
    SExists {
      session_exists_formula_vars = vars;
      session_exists_formula_session = session;
      session_exists_formula_pos = loc;
    }

  (* and mk_session_fence role1 role2 pred = *)
  (*   SFence { *)
  (*     session_fence_role1 = role1; *)
  (*     session_fence_role2 = role2; *)
  (*         session_fence_pred = pred; *)
  (*   } *)
  and mk_session_predicate_x name ho_vars params
    ?node:(node=None)
    ?pure:(pure=(Base.mk_true ()))
    ?sess_ann:(anns=(mk_sess_anns [AnnInactive] AnnNone))
    ?orders:(orders=Orders.mk_empty())
    ?sess_pred_kind:(sess_pred_kind=NO_KIND)
    loc =
    let sess_pred_kind = match sess_pred_kind with
        | NO_KIND -> get_pred_kind name
        | _ -> sess_pred_kind
    in
    Predicate {
      session_predicate_name = name;
      session_predicate_ho_vars = ho_vars;
      session_predicate_params = params;
      session_predicate_formula_heap_node = node;
      session_predicate_pure = pure;
      session_predicate_pos = loc;
      session_predicate_anns = anns;
      session_predicate_orders = orders;
      session_predicate_kind = sess_pred_kind;
    }

  and mk_session_predicate name ho_vars params ?node:(node=None) ?pure:(pure=(Base.mk_true ())) ?sess_ann:(anns=(mk_sess_anns [AnnInactive] AnnNone)) ?orders:(orders=Orders.mk_empty()) ?sess_pred_kind:(sess_pred_kind=NO_KIND) loc =
    Debug.no_1 "mk_session_predicate" (pr_list !Base.print_ho_param_formula) string_of_session_base (fun _ -> mk_session_predicate_x name ho_vars params ~node:node ~pure:pure ~sess_ann:anns ~orders:orders ~sess_pred_kind:sess_pred_kind loc) ho_vars

  and update_session_predicate_x ?name ?ho_vars ?params ?node
    ?pure ?sess_ann ?orders ?sess_pred_kind ?loc pred =
    let name           = match name           with | Some n -> n | None -> pred.session_predicate_name in
    let ho_vars        = match ho_vars        with | Some n -> n | None -> pred.session_predicate_ho_vars in
    let params         = match params         with | Some n -> n | None -> pred.session_predicate_params in
    let node           = match node           with | Some n -> n | None -> pred.session_predicate_formula_heap_node in
    let pure           = match pure           with | Some n -> n | None -> pred.session_predicate_pure in
    let sess_ann       = match sess_ann       with | Some n -> n | None -> pred.session_predicate_anns in
    let orders         = match orders         with | Some n -> n | None -> pred.session_predicate_orders in
    let sess_pred_kind = match sess_pred_kind with | Some n -> n | None -> pred.session_predicate_kind in
    let loc            = match loc            with | Some n -> n | None -> pred.session_predicate_pos in
    Predicate {
      session_predicate_name = name;
      session_predicate_ho_vars = ho_vars;
      session_predicate_params = params;
      session_predicate_formula_heap_node = node;
      session_predicate_pure = pure;
      session_predicate_pos = loc;
      session_predicate_anns = sess_ann;
      session_predicate_orders = orders;
      session_predicate_kind = sess_pred_kind;
    }

  and update_session_predicate ?name ?ho_vars ?params ?node
    ?pure ?sess_ann ?orders ?sess_pred_kind ?loc pred =
      let name           = match name           with | Some n -> n | None -> pred.session_predicate_name in
      let ho_vars        = match ho_vars        with | Some n -> n | None -> pred.session_predicate_ho_vars in
      let params         = match params         with | Some n -> n | None -> pred.session_predicate_params in
      let node           = match node           with | Some n -> n | None -> pred.session_predicate_formula_heap_node in
      let pure           = match pure           with | Some n -> n | None -> pred.session_predicate_pure in
      let sess_ann       = match sess_ann       with | Some n -> n | None -> pred.session_predicate_anns in
      let orders         = match orders         with | Some n -> n | None -> pred.session_predicate_orders in
      let sess_pred_kind = match sess_pred_kind with | Some n -> n | None -> pred.session_predicate_kind in
      let loc            = match loc            with | Some n -> n | None -> pred.session_predicate_pos in
      let pr_in = string_of_session_predicate in
      let pr_out = string_of_session_base in
      Debug.no_1 "update_session_predicate" pr_in pr_out (fun _ -> update_session_predicate_x ~name:name ~ho_vars:ho_vars ~params:params ~node:node
                                                      ~pure:pure ~sess_ann:sess_ann ~orders:orders ~sess_pred_kind:sess_pred_kind ~loc:loc pred) pred

  (* TODO tina: Why doesn't this use SFence constructor? *)
  (* and mk_session_fence_predicate name ho_vars params ?node:(node=None) ?pure:(pure=(Base.mk_true ())) loc = *)
  (*   { *)
  (*     session_predicate_name = name; *)
  (*     session_predicate_ho_vars = ho_vars; *)
  (*     session_predicate_params = params; *)
  (*     session_predicate_formula_heap_node = node; *)
  (*     session_predicate_pure = pure; *)
  (*     session_predicate_pos = loc; *)
  (*     (\* TODO: anns in fences? *\) *)
  (*     session_predicate_anns = []; *)
  (*   } *)

  and mk_session_hvar id ls loc = HVar {
      session_hvar_id = id;
      session_hvar_list = ls;
      session_hvar_pos = loc;
    }

  and mk_seq_node h1 h2 hnode pos  =
    (* match hnode with *)
    let ptr = Base.get_base_ptr (Base.mk_var session_seq_id) hnode in
    (* let ptr = Base.choose_ptr () in *) (* decide which name should be given here *)
    let name = get_prim_pred_id seq_id in
    (*let h2 = Base.mk_seq_wrapper h2 pos Base.base_type in *)
    let args = [h1; h2] in
    let args = List.map (fun a -> Base.mk_rflow_formula_from_heap a ~sess_kind:(Some Base.base_type) pos) args in
    let params = [] in
    Base.mk_node (ptr, name, args, params, pos) Base.base_type Sequence

  and mk_star_node h1 h2 hnode pos =
    Base.mk_star h1 h2 pos

  and mk_or_node h1 h2 hnode pos =
    let f1 = Base.mk_formula_heap_only h1 pos in
    let f2 = Base.mk_formula_heap_only h2 pos in
    let or_node = Base.mk_or f1 f2 pos in
    let rflow_form = (Base.mk_rflow_formula ~sess_kind:(Some Base.base_type) or_node) in
    (* let ptr = Base.choose_ptr () in *)
    let ptr = Base.get_base_ptr (Base.mk_var session_def_id) hnode in
    let name = get_prim_pred_id sor_id in
    let args = [rflow_form] in
    let params = [] in
    let node = Base.mk_node (ptr, name, args, params, pos) Base.base_type SOr in
    node
    (* Base.mk_seq_wrapper node pos Base.base_type *)

  and mk_exists_node vars hform pos =
    let form = Base.mk_exists vars hform pos in
    let rflow_form = Base.mk_rflow_formula ~sess_kind:(Some Base.base_type) form in
    (* ptr and name don't matter, they will be stripped off when returning the session heap formula *)
    let ptr = Base.choose_ptr () in
    let name = "exists" in
    let args = [rflow_form] in
    let params = [] in
    let node = Base.mk_node (ptr, name, args, params, pos) Base.base_type SExists in
    node

(* TODO: review this *)
  (* and mk_fence () = *)
  (*   Base.mk_empty () *)
  and mk_predicate_node_x hnode p =
    let orders = p.session_predicate_orders in
    let pos = p.session_predicate_pos in
    let args = p.session_predicate_ho_vars in
    (* transform orders to pure formula *)
    let pure_form_lst = x_add O2F.trans_orders_to_pure_formula orders pos in
    let pure_form = Base.join_conjunctions pure_form_lst in
    (* transform pure formula to ho_param_formula *)
    let ho_param_formula = Base.map_rflow_formula_list (fun elem -> Base.add_pure_to_formula pure_form elem ) args in
    (* make the actual predicate node *)
    let ptr = Base.get_base_ptr (Base.mk_var session_def_id) hnode in
    let name = p.session_predicate_name in
    let params = p.session_predicate_params in
    let anns = p.session_predicate_anns in
    let session_predicate_kind = p.session_predicate_kind in
    (* let params = (\* List.map *\) (\* (fun a -> Base.id_to_param a pos) *\) params in *)
    let node = Base.mk_node (ptr, name, ho_param_formula, params, pos) Base.base_type (mk_sess_pred_kind session_predicate_kind) in
    let node = Base.set_anns node anns in
    (* make the Predicate node *)
    node

  and mk_predicate_node hnode p =
    Debug.no_1 "mk_predicate_node" string_of_session_predicate !Base.print_h_formula (fun _ -> mk_predicate_node_x hnode p) p

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
        mk_seq_node arg1 arg2 s.session_seq_formula_heap_node s.session_seq_formula_pos
      | SOr s   ->
        let arg1 = helper s.session_sor_formula_or1 in
        let arg2 = helper s.session_sor_formula_or2 in
        mk_or_node arg1 arg2 s.session_sor_formula_heap_node s.session_sor_formula_pos
      | SStar s ->
        let arg1 = helper s.session_star_formula_star1 in
        let arg2 = helper s.session_star_formula_star2 in
        mk_star_node arg1 arg2 s.session_star_formula_heap_node s.session_star_formula_pos
      | SExists s -> let vars = s.session_exists_formula_vars in
        let hform = helper s.session_exists_formula_session in
        let pos = s.session_exists_formula_pos in
        mk_exists_node vars hform pos
      | SBase s -> (match s with
          | Base b -> Base.trans_base b
          | Predicate p -> x_add_1 mk_predicate_node p.session_predicate_formula_heap_node p
          | HVar h -> mk_hvar_node h)
      | SEmp    -> Base.mk_empty () in
    helper s

  let trans_from_session s =
    let pr = string_of_session in
    let pr2 = !Base.print_h_formula in
    Debug.no_1 "Session.trans_from_session" pr pr2 trans_from_session s


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
        (* let new_base = tra
           transform the base
 *)
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
          SSeq {s with session_seq_formula_head = helper fnc s.session_seq_formula_head;
                       session_seq_formula_tail = helper fnc s.session_seq_formula_tail; }
        | SOr s   ->
          SOr {s with session_sor_formula_or1 = helper fnc s.session_sor_formula_or1;
                      session_sor_formula_or2 = helper fnc s.session_sor_formula_or2; }
        | SStar s ->
          SStar {s with session_star_formula_star1 = helper fnc s.session_star_formula_star1;
                        session_star_formula_star2 = helper fnc s.session_star_formula_star2; }
        | SExists s ->
          SExists {s with session_exists_formula_session = helper fnc s.session_exists_formula_session;}
(* TODO: review this *)
        | SBase sb -> SBase (trans_session_base_formula f_base sb)
        | SEmp -> sf
    in
    helper fnc sf

  let trans_session_formula fnc sf =
    let pr = string_of_session in
    Debug.no_1 "Session.trans_session_formula" pr pr (trans_session_formula fnc) sf

  let get_pos s = match s with
    | SSeq s  -> s.session_seq_formula_pos
    | SOr s   -> s.session_sor_formula_pos
    | SStar s -> s.session_star_formula_pos
    | SExists s -> s.session_exists_formula_pos
(* TODO: review this *)
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

  let strip_exists_heap_node (hform: Base.h_formula) : Base.formula =
    let (ptr, name, args, params, pos) = Base.get_node hform in
    Base.get_formula_from_ho_param_formula (List.nth args 0)

  (* Given two formulae, merge their heaps and combine
   * into an Exist formula. *)
  let merge_formulae_into_exists (f1: Base.formula) (f2: Base.formula)
                                 (vars: (ident * primed) list) (pos: VarGen.loc)
                                 : Base.formula =
    let h1 = Base.get_h_formula f1 in
    let h2 = Base.get_h_formula f2 in
    let h = Base.mk_star h1 h2 pos in
    Base.mk_exists vars h pos

  let merge_formulae_into_base (f1: Base.formula) (f2: Base.formula)
                               (pos: VarGen.loc) : Base.formula =
    Base.mk_star_formula f1 f2 pos

  let merge_formulae (h1: Base.h_formula) (f2: Base.formula)
                     (pos: VarGen.loc) : Base.formula =
    let nk = Base.get_node_kind h1 in
             match nk with
               | SExists -> let f1 = strip_exists_heap_node h1 in
                            let vars = Base.get_exists_vars f1 in
                            merge_formulae_into_exists f1 f2 vars pos
               | _ -> let f1 = Base.mk_formula_heap_only h1 pos in
                            merge_formulae_into_base f1 f2 pos

  let mk_struc_formula_from_session_and_struc_formula (s: session) (sf: Base.struc_formula) =
    let pos = get_pos s in
    let h1 = x_add_1 trans_from_session s in
    (* let h_form = mk_sess_h_formula h_form pos in *)
    let f2 = Base.get_formula_from_struc_formula sf in
    let merged_form = merge_formulae h1 f2 pos in
    let fct h = Some merged_form in
    Base.transform_struc_formula_formula fct sf

  let mk_struc_formula_from_session_and_formula s sf =
    let pr1 = string_of_session in
    let pr2 = !Base.print_struc_formula in
    Debug.no_2 "Session.mk_struc_formula_from_session_and_struc_formula" pr1 pr2 pr2 mk_struc_formula_from_session_and_struc_formula s sf

  let mk_struc_formula_from_h_formula_and_formula (h1: Base.h_formula) (sf: Base.struc_formula) pos =
    let f2 = Base.get_formula_from_struc_formula sf in
    let merged_form = merge_formulae h1 f2 pos in
    let fct h = Some merged_form in
    Base.transform_struc_formula_formula fct sf

  let trans_h_formula_to_session ?pure:(pure=(Base.mk_true ())) h_formula =
    let rec helper h_formula =
      let node_kind = Base.get_node_kind h_formula in
      match node_kind with
        | Sequence ->
            let (ptr, name, args, params, pos) = Base.get_node h_formula in
            let h1 = Base.get_h_formula_from_ho_param_formula (List.nth args 0) in
            let h2 = Base.get_h_formula_from_ho_param_formula (List.nth args 1) in
            mk_session_seq_formula (helper h1) (helper h2) ~node:(Base.get_node_opt h_formula) pos
        | SOr ->
            let (ptr, name, args, params, pos) = Base.get_node h_formula in
            let or_node = Base.get_formula_from_ho_param_formula (List.nth args 0) in
            let or_formulae = Base.get_or_formulae or_node in
            let h1 = Base.get_h_formula (List.nth or_formulae 0) in
            let h2 = Base.get_h_formula (List.nth or_formulae 1) in
            mk_session_or_formula (helper h1) (helper h2) ~node:(Base.get_node_opt h_formula) pos
        | Star ->
            let pos = Base.get_star_pos h_formula in
            let star_formulae = Base.get_star_formulae h_formula in
            let h1 = List.nth star_formulae 0 in
            let h2 = List.nth star_formulae 1 in
            mk_session_star_formula (helper h1) (helper h2) pos
        | SExists ->
            let (ptr, name, args, params, pos) = Base.get_node h_formula in
            let hform = Base.get_h_formula_from_ho_param_formula (List.nth args 0) in
            let vars = Base.get_exists_vars (Base.get_formula_from_ho_param_formula (List.nth args 0)) in
            mk_session_exists_formula vars (helper hform) pos
        | Send | Receive | Transmission ->
            SBase (Base (Base.trans_h_formula_to_session_base h_formula))
        | HVar ->
            let (id, ls) = Base.get_hvar h_formula in
            SBase (mk_session_hvar id ls no_pos)
        | Predicate sess_pred_order_kind ->
            let (ptr, name, args, params, pos) = Base.get_node h_formula in
            let ann = un_option (Base.get_anns h_formula) (mk_sess_anns [AnnInactive] AnnNone) in
            (* let params = List.map (fun a -> Base.get_param_id a) params in *)
            SBase (mk_session_predicate name args params ~node:(Base.get_node_opt h_formula) ~pure:pure ~sess_ann:ann ~sess_pred_kind:sess_pred_order_kind pos)
        | Emp ->
            SEmp
        | Session -> failwith (x_loc ^ ": Unexpected node kind.")
            (* let (ptr, name, args, params, pos) = Base.get_node h_formula in *)
            (* let h = Base.get_h_formula_from_ho_param_formula (List.nth args 0) in *)
            (* helper h *)
        | Channel -> failwith (x_loc ^ ": Unexpected node kind.")
        | Common -> failwith (x_loc ^ ": Unexpected node kind.")
        | Msg -> failwith (x_loc ^ ": Unexpected node kind.")
	in
    helper h_formula

  let trans_h_formula_to_session ?pure:(pure=(Base.mk_true ())) h_formula =
    let pr1 = !Base.print_h_formula in
    let pr2 = string_of_session in
    Debug.no_1 "Session.trans_h_formula_to_session" pr1 pr2 (fun _ -> trans_h_formula_to_session ~pure:pure h_formula) h_formula

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
    Debug.no_1 "Session.get_original_h_formula" pr pr get_original_h_formula h_formula

  let get_base_pos b = Base.get_base_pos b

  let get_message_var b = Base.get_message_var b

  let get_message b = Base.get_message b

  let get_param_id param = Base.get_param_id param

  let replace_message_var b =
    let msg_var = Base.get_message_var b in
    let new_var = Base.fresh_var msg_var in
    Base.subst_base [(msg_var,new_var)] b

  let replace_message_var b =
    let pr = Base.string_of_session_base in
    Debug.no_1 "Session.replace_message_var" pr pr replace_message_var b

  let trans_formula_to_session formula =
    if (Base.is_base_formula formula or Base.is_exists_formula formula)
    then
      let h_formula = Base.get_h_formula formula in
      let pure_formula = Base.get_pure_formula formula in
      let h_formula = get_original_h_formula h_formula in
      x_add_1 (trans_h_formula_to_session ~pure:pure_formula) h_formula
    else
      failwith (x_loc ^ ": Formula Or unexpected.")

  let trans_formula_to_session formula =
    let pr1 =  !Base.print in
    let pr2 =  string_of_session in
    Debug.no_1 "trans_formula_to_session" pr1 pr2 trans_formula_to_session formula

  let trans_struc_formula_to_session struc_formula =
    let f = Base.get_formula_from_struc_formula struc_formula in
    trans_formula_to_session f

  let wrap_2ways_sess2base f_sess hform =
    let session_form = x_add_1 trans_h_formula_to_session hform in
    let new_session_form = f_sess session_form in
    let new_hform = x_add_1 trans_from_session new_session_form in
    new_hform

  let wrap_2ways_sess2base f_sess hform =
    let pr =  !Base.print_h_formula in
    Debug.no_1 "Session.wrap_2ways_sess2base" pr pr (wrap_2ways_sess2base f_sess) hform

  let wrap_2ways_sess2base_opt f_sess hform =
    let session_form = x_add_1 trans_h_formula_to_session hform in
    let new_session_form = f_sess session_form in
    match new_session_form with
    | None -> None
    | Some new_session_form ->
      let new_hform = x_add_1 trans_from_session new_session_form in
      Some new_hform

  let wrap_2ways_sess2base_opt f_sess hform =
    let pr =  !Base.print_h_formula in
    Debug.no_1 "Session.wrap_2ways_sess2base_opt" pr (pr_opt pr) (wrap_2ways_sess2base_opt f_sess) hform

  let rename_message_pointer_heap hform =
    let fnc_node sf =
      let base_f b = Some (replace_message_var b) in
      let fnc = (nonef, (nonef, base_f)) in
      let sf = trans_session_formula fnc sf in
      sf in
    x_add wrap_2ways_sess2base fnc_node hform

  let rename_message_pointer_heap hform =
    let fnc si hform = Some( rename_message_pointer_heap hform) in
    Base.heap_node_transformer_gen ~include_msg:true fnc hform

  let rename_message_pointer_heap hform =
    let pr =  !Base.print_h_formula in
    Debug.no_1 "Session.rename_message_pointer_heap" pr (pr_opt pr) rename_message_pointer_heap hform

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

  let norm_sequence hform =
    let sessf = x_add_1 trans_h_formula_to_session hform in
    let sessf = norm3_sequence sessf in
    let hform = trans_from_session sessf in
    Some hform

  let rec sor_disj_list head =
    match head with
      | SOr s -> (sor_disj_list s.session_sor_formula_or1) @
                  (sor_disj_list s.session_sor_formula_or2)
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
    let head_session = x_add_1 trans_h_formula_to_session
        (Base.get_h_formula_from_ho_param_formula head) in
    let disj_list = sor_disj_list head_session in
    let disj_list =
      let tail_session =
        match tail with
        | None      -> SEmp (* disj_list *)
        | Some tail ->
          let tail_session = x_add_1 trans_h_formula_to_session
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
    Debug.no_2 "Session.split_sor" pr1 (pr_opt pr1) pr2 split_sor head tail

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
    Debug.no_2 "Session.split_disj" pr1 (pr_opt pr1) pr2 split_disj head tail

  let norm_base_only_helper sf =
    match sf with
    | SBase (Base _) -> Some (mk_session_seq_formula sf SEmp (get_pos sf))
    | SBase (Predicate spf) ->
        begin
            match spf.session_predicate_kind with
            | Order HB
            | Order CB
            | Order Event -> None
            | _ -> Some (mk_session_seq_formula sf SEmp (get_pos sf))
        end
    | _ -> None

  let norm_base_only (base: Base.h_formula): Base.h_formula option =
    wrap_2ways_sess2base_opt norm_base_only_helper base

  let norm_base_only (base: Base.h_formula): Base.h_formula option =
    let pr = !Base.print_h_formula in
    Debug.no_1 "Session.norm_base_only" pr (pr_opt pr) norm_base_only base

  let wrap_one_seq_heap hform =
    let fnc si = x_add_1 norm_base_only in
    Base.heap_node_transformer_gen ~include_msg:true fnc hform

  let norm_last_seq_node (base: Base.h_formula): Base.h_formula option =
    let trans_seq_helper sf =
      match sf with
      | SSeq seq ->
        begin
          match (x_add_1 norm_base_only_helper seq.session_seq_formula_tail) with
          | None      ->  None
          | Some tail ->  Some (SSeq {seq with session_seq_formula_tail = tail})
        end
      | _ ->  Some sf  (* if it's not seq do not norm *)
    in let fct = trans_session_formula (trans_seq_helper, (somef,somef)) in
    Some (x_add wrap_2ways_sess2base fct base)

  let norm_last_seq_node (base: Base.h_formula): Base.h_formula option =
    let fnc si =  norm_last_seq_node in
    Base.heap_node_transformer_gen ~include_msg:true fnc base

  let norm_last_seq_node (base: Base.h_formula): Base.h_formula option =
    let pr = !Base.print_h_formula in
    Debug.no_1 "Session.norm_last_seq_node" pr (pr_opt pr) norm_last_seq_node base

  (* let update_temp_name_heap (base: Base.h_formula): Base.h_formula option = *)
  (*   Base.update_temp_heap_name base *)

  let update_temp_name_heap (base: Base.h_formula): Base.h_formula option =
    let fnc si = Base.update_temp_heap_name si in
    Base.heap_node_transformer ~flow:true fnc base

  let update_temp_name_heap (base: Base.h_formula): Base.h_formula option =
    let pr = !Base.print_h_formula in
    Debug.no_1 "Session.update_temp_name_heap" pr (pr_opt pr) (fun _ -> update_temp_name_heap (base: Base.h_formula)) base

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

  (* --------------------------------------------------------------------------------- *)
  (* replace Pred<>;;tail -----with----> unfold(Pred<>);;tail and normalize the result *)
  (* --------------------------------------------------------------------------------- *)
  let rebuild_nodes def lnode rnode l_ho_args r_ho_args si_lhs si_rhs unfold_fun is_prime_fun =
    if not (!Globals.allow_unfold) then
      let () = y_tinfo_pp "Session.rebuild_nodes: unfold is not allowed" in
      def
    else
    match si_lhs.node_kind, si_rhs.node_kind with
    | Some nk_lhs, Some nk_rhs ->
      begin
        let sess_lhs, sess_rhs = x_add_1 trans_h_formula_to_session lnode, x_add_1 trans_h_formula_to_session rnode in
        match sess_lhs,sess_rhs with
        | SSeq s_lhs, SSeq s_rhs ->
          begin
            match s_lhs.session_seq_formula_head, s_rhs.session_seq_formula_head with
            | SBase (Predicate p_lhs) as sess_lhs, SBase (Predicate p_rhs) as sess_rhs -> (* l_ho_args,r_ho_args,(CF.get_node_name_x lnode) *)
              (* let head_lhs = x_add_1 trans_from_session sess_lhs in *)
              (* let ptr = Base.get_base_ptr session_def_id p_lhs.session_predicate_formula_heap_node in *)
              (* let new_head = unfold_fun head_lhs ptr in *)
              (* let new_head = trans_formula_to_session new_head in *)
              (* let new_lseq = append_tail new_head s_lhs.session_seq_formula_tail in *)
              (* let new_lseq = norm3_sequence new_lseq in *)
              (* let new_lseq = x_add_1 trans_from_session new_lseq in *)
              (* let new_lseq_ho_arg = Base.mk_rflow_formula_from_heap new_lseq ~sess_kind:(Some Base.base_type) no_pos in *)
              def
              (* l_ho_args,r_ho_args,(CF.get_node_name_x lnode) *)
            | SBase (Predicate pl) as sess_lhs, _ -> (* l_ho_args,r_ho_args,(CF.get_node_name_x lnode) *)
              let headl = x_add_1 trans_from_session sess_lhs in
              if (is_prime_fun headl) then
	              def
              else
                let ptr = Base.get_base_ptr (Base.mk_var session_def_id) pl.session_predicate_formula_heap_node in
                let new_head = unfold_fun headl ptr in
                let pure = Base.get_pure_formula new_head in
                let new_head = trans_formula_to_session new_head in
                let new_lseq =
                  match new_head with
                  | SEmp -> s_lhs.session_seq_formula_tail
                  | _    -> append_tail new_head s_lhs.session_seq_formula_tail in
                let new_lseq = norm3_sequence new_lseq in
                let new_lseq = x_add_1 trans_from_session new_lseq in
                let new_lseq = map_opt_def new_lseq idf (norm_last_seq_node new_lseq) in
                let new_lseq = map_opt_def new_lseq idf (wrap_one_seq_heap new_lseq) in
                let new_lseq_ho_arg = Base.mk_rflow_formula_from_heap new_lseq ~sess_kind:(Some Base.base_type) no_pos in
                let new_rseq_ho_arg = Base.mk_rflow_formula_from_heap rnode ~sess_kind:(Some Base.base_type) no_pos in
                [new_lseq_ho_arg],[new_rseq_ho_arg],(get_prim_pred_id_by_kind Channel), Some pure, None
            | _, _ -> def
          end
        | SBase (Base _),  SSeq _ ->
          (* try to add the base to a seq with emp tail *)
          let new_lhs = append_tail sess_lhs SEmp in
          let new_lhs = x_add_1 trans_from_session new_lhs in
          let new_lhs_ho_arg = Base.mk_rflow_formula_from_heap new_lhs ~sess_kind:(Some Base.base_type) no_pos in
          [new_lhs_ho_arg], r_ho_args, (get_prim_pred_id_by_kind Channel),None,None
        | SSeq _, SBase (Base _) ->
          (* try to add the base to a seq with emp tail *)
          let new_rhs = append_tail sess_rhs SEmp in
          let new_rhs = x_add_1 trans_from_session new_rhs in
          let new_rhs_ho_arg = Base.mk_rflow_formula_from_heap new_rhs ~sess_kind:(Some Base.base_type) no_pos in
          l_ho_args, [new_rhs_ho_arg], (get_prim_pred_id_by_kind Channel),None,None
        | _, _ ->  def
      end
    | _, _ -> def


  let rebuild_nodes def lnode rnode l_ho_args r_ho_args si_lhs si_rhs unfold_fun is_prime_fun =
    let pr_node = !Base.print_h_formula in
    let pr_ho_args = pr_list !Base.print_ho_param_formula in
    let pr_def (a,b,c,d,e) = (pr_pair pr_ho_args pr_ho_args) (a,b) in
    Debug.no_5 "Session.rebuild_nodes_x" pr_def pr_node pr_node pr_ho_args pr_ho_args pr_def (fun _ _ _ _ _ ->
				rebuild_nodes def lnode rnode l_ho_args r_ho_args si_lhs si_rhs unfold_fun is_prime_fun) def lnode rnode l_ho_args r_ho_args

  (* --------------------------------------------------------------------------------- *)
  (* replace Pred<>;;tail -----with----> unfold(Pred<>);;tail and normalize the result *)
  (* --------------------------------------------------------------------------------- *)
  let rebuild_node def node unfold_fun is_prime_fun =
    if not (!Globals.allow_unfold) then
      let () = y_tinfo_pp "Session.rebuild_nodes: unfold is not allowed" in
      def
    else
      let sess = try Some (x_add_1 trans_h_formula_to_session node)
        with _ -> None in
      match sess with
      | Some (SSeq seq) ->
        begin
          match seq.session_seq_formula_head with
          | SBase (Predicate pl) as sess_pl ->
            let headl = x_add_1 trans_from_session sess_pl in
            if (is_prime_fun headl) then
	            def
            else
              let ptr = Base.get_base_ptr (Base.mk_var session_def_id) pl.session_predicate_formula_heap_node in
              let new_head = unfold_fun headl ptr in
              let pure = Base.get_pure_formula new_head in
              let new_head = trans_formula_to_session new_head in
              let new_lseq =
                  match new_head with
                  | SEmp -> let () = y_binfo_pp "SEMP" in seq.session_seq_formula_tail
                  | _    -> let () = y_binfo_pp "else-SEMP" in append_tail new_head seq.session_seq_formula_tail in
              (* let new_lseq = append_tail new_head seq.session_seq_formula_tail in *)
              let new_lseq = norm3_sequence new_lseq in
              let new_lseq = x_add_1 trans_from_session new_lseq in
              let new_lseq = map_opt_def new_lseq idf (norm_last_seq_node new_lseq) in
              let new_lseq = map_opt_def new_lseq idf (wrap_one_seq_heap new_lseq) in
              let new_lseq_ho_arg = Base.mk_rflow_formula_from_heap new_lseq ~sess_kind:(Some Base.base_type) no_pos in
              Some [new_lseq_ho_arg], Some pure
          | _ -> def
        end
      | _ ->  def

  let rebuild_node def node unfold_fun is_prime_fun =
    let pr_in = !Base.print_h_formula in
    let pr1 = !Base.print_ho_param_formula in
    let pr2 = !Base.print_pure_formula in
    let pr_out = pr_pair (pr_opt (pr_list pr1)) (pr_opt pr2) in
    Debug.no_1 "Session.rebuild_node_x" pr_in pr_out (fun _ -> rebuild_node def node unfold_fun is_prime_fun) node

  let remove_emps ?head:(head=true) ?tail:(tail=true) sess =
    let fixpt = ref true in
    let fnc sess =
      match sess with
      | SSeq s ->
          if head && (is_emp s.session_seq_formula_head) then
            let () = fixpt := false in
            Some s.session_seq_formula_tail
          else
            if tail && (is_emp s.session_seq_formula_tail) then
              let () = fixpt := false in
              Some s.session_seq_formula_head
            else None
      | _      -> None in
    let rec helper sess =
      let sess =  trans_session_formula (fnc, (somef,somef)) sess in
      if not (!fixpt) then let () = fixpt := true in helper sess else sess
    in helper sess

  let remove_emps_hform hform =
    let sessf = x_add_1 trans_h_formula_to_session hform in
    let sessf = remove_emps ~tail:false sessf in
    let hform = trans_from_session sessf in
    Some hform


  (* Removes Bot assrt from session predicate orders *)
  (* Examples:
    * Bot & (A,id_55) & Bot -> (A,id_55)
    * Bot & Bot & Bot & Bot -> Bot *)
  let norm_assrt prj =
    let norm prj = match prj with
    | SBase sb ->
      begin
        match sb with
        | Predicate p ->
          (* gets predicate info *)
          let orders = p.session_predicate_orders in
          let pred_kind = p.session_predicate_kind in
          (* removes Bot elem from assumptions and guards orders *)
          begin match pred_kind with
          | Assert Assume
          | Assert Guard ->
            let norm = Orders.norm_orders orders in
            (* updates the predicate with the normalized orders *)
            let pred = update_session_predicate ~orders:norm p in
            let sbase = SBase pred in
            Some sbase
          | _ -> None
          end
        | _ -> None
      end
    | _ -> None
    in
    let fnc = (norm, (nonef, nonef)) in
    let res = trans_session_formula fnc prj in
    res

  let norm_assrt prj =
    let pr = string_of_session in
    Debug.no_1 "norm_assrt" pr pr norm_assrt prj

  (* Removes assumptions and guards that have orders only with Bot *)
  (* Example: Assume{Bot} -> emp *)
  let remove_assrt_bot sess =
    let norm sess = match sess with
    | SBase sb ->
      begin match sb with
      | Predicate p ->
          let assrt = p.session_predicate_orders in
          let pred_kind = p.session_predicate_kind in
          begin match pred_kind with
          | Assert Assume
          | Assert Guard ->
              if Orders.is_bot assrt then Some SEmp
              else None
          | _ -> None
          end
      | _ -> None
      end
  | _ -> None
  in
  let fnc = (norm, (nonef, nonef)) in
  let res = trans_session_formula fnc sess in
  res

  let remove_assrt_bot prj=
    let pr = string_of_session in
    Debug.no_1 "remove_assrt_bot" pr pr remove_assrt_bot prj

  let find pred fsess =
    let rec helper sess =
      match sess with
      | SSeq s    -> helper s.session_seq_formula_head ||
                     helper s.session_seq_formula_tail
      | SOr s     -> helper s.session_sor_formula_or1  ||
                     helper s.session_sor_formula_or2
      | SStar s   -> helper s.session_star_formula_star1 ||
                     helper s.session_star_formula_star2
      | SExists s -> helper s.session_exists_formula_session
      | SBase s   -> pred s
      | SEmp      -> false
	  in
    helper fsess

end;;

(* =========== Protocol / Projection ========== *)
(* ============================================ *)

module IMessage = Message_commons(IForm);;
module CMessage = Message_commons(CForm);;

(* module IVar = *)
(* struct *)
(*   type t = IForm.var *)
(*   let string_of = IForm.print_var *)
(*   let eq = IForm.eq_var *)
(* end;; *)

(* module CVar = *)
(* struct *)
(*   type t = CForm.var *)
(*   let string_of = CForm.print_var *)
(*   let eq = CForm.eq_var *)
(* end;; *)

(* module IVar = Ords.Var(IForm) *)
(* module CVar = Ords.Var(CForm) *)
module IOrders = Ords.GOrders(Ords.Var(IForm)) ;;
module COrders = Ords.GOrders(Ords.Var(CForm)) ;;

module O2C  = Ords.Orders2Form(CForm)
module O2I  = Ords.Orders2Form(IForm)

module IProtocol_base = Protocol_base_formula(IForm) ;;
module CProtocol_base = Protocol_base_formula(CForm) ;;
module IProjection_base = Projection_base_formula(IForm) ;;
module CProjection_base = Projection_base_formula(CForm) ;;
module ITPProjection_base = TPProjection_base_formula(IForm);;
module CTPProjection_base = TPProjection_base_formula(CForm);;

module IProtocol = Make_Session(Protocol_base_formula)(IForm);;
module CProtocol = Make_Session(Protocol_base_formula)(CForm);;

(* per party  *)
module IProjection = Make_Session(Projection_base_formula)(IForm);;
module CProjection = Make_Session(Projection_base_formula)(CForm);;

(* per channel *)
module ITPProjection = Make_Session(TPProjection_base_formula)(IForm);;
module CTPProjection = Make_Session(TPProjection_base_formula)(CForm);;

type session_iformula = ProtocolSession of IProtocol.session
                  | ProjectionSession of IProjection.session
                  | TPProjectionSession of ITPProjection.session

type session_cformula = ProtocolSession of CProtocol.session
                  | ProjectionSession of CProjection.session
                  | TPProjectionSession of CTPProjection.session

(* ------ Getters for session_iformula ------ *)
let get_iprotocol (session:session_iformula) =
  match session with
  | ProtocolSession s -> s
  | _ -> failwith "not a protocol formula"

let get_iprojection (session:session_iformula) =
  match session with
  | ProjectionSession s -> s
  | _ -> failwith "not a projection formula"

let get_itpprojection (session:session_iformula) =
  match session with
  | TPProjectionSession s -> s
  | _ -> failwith "not a two-party projection formula"

(* -------------------------------------- *)
(* Protocol annotation with unique id *)
let annotate_suid (prot: IProtocol.session): IProtocol.session  =
  let fnc base =
    let suid = fresh_any_name def_suid_name in
    let suid = IProtocol_base.mk_suid suid in
    let suid = if IProtocol_base.eq_suid
        base.IProtocol_base.protocol_base_formula_uid
        IProtocol_base.def_suid then suid else  base.IProtocol_base.protocol_base_formula_uid in
    (* let () = suid := !suid + 1 in *)
    Some {base with IProtocol_base.protocol_base_formula_uid = suid} in
  let prot = IProtocol.trans_session_formula (nonef,(nonef,fnc)) prot in
  prot

let annotate_suid (prot: IProtocol.session): IProtocol.session  =
  let pr = IProtocol.string_of_session in
  Debug.no_1 "annotate_suid" pr pr annotate_suid prot

(* ====== Helpful functions used for projection ====== *)

(* Convert from session predicate IProtocol to session IProjection *)
let convert_pred_from_prot_to_proj (sess_base:IProtocol.session_base) : IProjection.session =
  match sess_base with
  | Predicate pred ->
    let name = pred.session_predicate_name in
    let ho_vars = pred.session_predicate_ho_vars in
    let params = pred.session_predicate_params in
    let node = pred.session_predicate_formula_heap_node in
    let pure = pred.session_predicate_pure in
    let pos = pred.session_predicate_pos in
    let anns = pred.session_predicate_anns in
    let orders = pred.session_predicate_orders in
    let session_predicate_kind = pred.session_predicate_kind in
    SBase (IProjection.mk_session_predicate name ho_vars params ~node:node ~pure:pure ~sess_ann:anns ~orders:orders ~sess_pred_kind:session_predicate_kind pos)
  | _ -> SEmp

let convert_pred_from_prot_to_proj (sess_base:IProtocol.session_base) : IProjection.session =
  let pr = IProtocol.string_of_session_base in
  let pr_out = IProjection.string_of_session in
  Debug.no_1 "convert_pred_from_prot_to_proj" pr pr_out convert_pred_from_prot_to_proj sess_base

(* Convert from session predicate IProjection to session ITPProjection *)
let convert_pred_from_prot_to_tproj (sess_base:IProjection.session_base) : ITPProjection.session =
  match sess_base with
  | Predicate pred ->
    let name = pred.session_predicate_name in
    let ho_vars = pred.session_predicate_ho_vars in
    let params = pred.session_predicate_params in
    let node = pred.session_predicate_formula_heap_node in
    let pure = pred.session_predicate_pure in
    let pos = pred.session_predicate_pos in
    let anns = pred.session_predicate_anns in
    let orders = pred.session_predicate_orders in
    let session_predicate_kind = pred.session_predicate_kind in
    SBase (ITPProjection.mk_session_predicate name ho_vars params ~node:node ~pure:pure ~sess_ann:anns ~orders:orders ~sess_pred_kind:session_predicate_kind pos)
  | _ -> SEmp

let is_projection si = let fct info = let sk = info.session_kind in
                         (match sk with
                          | Some Projection -> true
                          | Some TPProjection -> true
                          | _ -> false) in
  Gen.map_opt_def false fct si

let is_projection si =
  Debug.no_1 "Session.is_projection" (pr_opt string_of_view_session_info) string_of_bool is_projection si

(* -------------------------------------- *)
(* rename the var which is used for describing the
   transmitted message (the renaming taregets both the
   S/R arg(s) and their corresponding ho-arg) *)
let irename_message_pointer_heap hform =
  let fnc si hform =
    match si.session_kind with
    | Some Projection   -> (IProjection.rename_message_pointer_heap hform)
    | Some TPProjection -> (ITPProjection.rename_message_pointer_heap hform)
    | Some Protocol     -> (IProtocol.rename_message_pointer_heap hform)
    | None -> None
  in
  IMessage.heap_transformer fnc hform

let irename_message_pointer formula =
  let renamed_formula = IMessage.transform_formula irename_message_pointer_heap formula in
  (* add the freshly introduced vars to the exists list *)
  let fv = F.all_fv formula in
  let all_fv = F.all_fv renamed_formula in
  let new_qvars = Gen.BList.difference_eq IP.eq_var all_fv fv in
  let renamed_formula = F.push_exists new_qvars renamed_formula in
  renamed_formula

let irename_message_pointer formula =
  let pr = !F.print_formula in
  Debug.no_1 "Session.irename_message_pointer" pr pr irename_message_pointer formula

let irename_message_pointer_struc formula =
  let renamed_struct = IMessage.transform_struc_formula irename_message_pointer_heap formula in
  (* add the freshly introduced vars to the exists list *)
  let fv = F.struc_free_vars false formula in
  let all_fv = F.struc_free_vars false renamed_struct in
  let new_qvars = Gen.BList.difference_eq IP.eq_var all_fv fv in
  let f_f f = Some (F.push_exists new_qvars f) in
  let renamed_formula = F.transform_struc_formula (nonef,f_f,nonef,(somef,somef,somef,somef,somef)) renamed_struct in
  renamed_struct

let irename_message_pointer_struc formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.irename_message_pointer_struc" pr pr irename_message_pointer_struc formula

(* -------------------------------------- *)
(*** rename the first pointer of hform  ***)
let irename_session_pointer_heap ?flow:(flow=false) var hform =
  let fnc si = IMessage.set_heap_node_var_opt ~flow:flow var in
  IMessage.heap_transformer fnc hform

let irename_all_session_pointer_struc ?to_var:(var=session_self) sformula =
  let renamed_struct = IMessage.transform_struc_formula (irename_session_pointer_heap ~flow:true var) sformula in
  renamed_struct

let irename_all_session_pointer_struc ?to_var:(var=session_self) formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.irename_all_session_pointer_struc" pr pr (irename_all_session_pointer_struc ~to_var:var) formula

let irename_first_session_pointer_struc ?to_var:(var=session_self) sformula =
  let renamed_struct = IMessage.transform_struc_formula  (irename_session_pointer_heap var) sformula in
  renamed_struct

let irename_first_session_pointer_struc ?to_var:(var=session_self) formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.irename_first_session_pointer_struc" pr pr (irename_first_session_pointer_struc ~to_var:var) formula

(* ----------------------------------------------------------------------- *)
(*** IMessage: rename the first pointer of hform with Chan pointer where possible  ***)
let irename_sess_ptr_2_chan_ptr_heap ?flow:(flow=false) hform =
  IMessage.set_heap_node_to_chan_node hform

let irename_sess_ptr_2_chan_ptr_struc sformula =
  let renamed_struct = IMessage.transform_struc_formula (irename_sess_ptr_2_chan_ptr_heap ~flow:true) sformula in
  renamed_struct

let irename_sess_ptr_2_chan_ptr_struc formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.irename_sess_ptr_2_chan_ptr_struc" pr pr (irename_sess_ptr_2_chan_ptr_struc) formula

let irename_sess_ptr_2_chan_ptr formula =
  let renamedf = IMessage.transform_formula (irename_sess_ptr_2_chan_ptr_heap ~flow:true) formula in
  renamedf

let irename_sess_ptr_2_chan_ptr formula =
  let pr = !F.print_formula in
  Debug.no_1 "Session.irename_sess_ptr_2_chan_ptr" pr pr (irename_sess_ptr_2_chan_ptr) formula

(* ----------------------------------------------------------------------- *)
(*** CMessage: rename the first pointer of hform with Chan pointer where possible  ***)
let crename_sess_ptr_2_chan_ptr_heap ?flow:(flow=false) hform =
  CMessage.set_heap_node_to_chan_node hform

let crename_sess_ptr_2_chan_ptr_struc sformula =
  let renamed_struct = CMessage.transform_struc_formula (crename_sess_ptr_2_chan_ptr_heap ~flow:true) sformula in
  renamed_struct

let crename_sess_ptr_2_chan_ptr_struc formula =
  let pr = !CF.print_struc_formula in
  Debug.no_1 "Session.crename_sess_ptr_2_chan_ptr_struc" pr pr (crename_sess_ptr_2_chan_ptr_struc) formula

let crename_sess_ptr_2_chan_ptr formula =
  let renamedf = CMessage.transform_formula (crename_sess_ptr_2_chan_ptr_heap ~flow:true) formula in
  renamedf

let crename_sess_ptr_2_chan_ptr formula =
  let pr = !CF.print_formula in
  Debug.no_1 "Session.crename_sess_ptr_2_chan_ptr" pr pr (crename_sess_ptr_2_chan_ptr) formula

(* ------------------------------------------------------- *)
(*** wrap sequence around single transmissions protocols ***)
(***    eg: x::Chan{@S !0}<> ---> x::Chan{@S !0;;emp}<>  ***)
let wrap_one_seq_heap hform =
    let fnc si hform =
    match si.session_kind with
    | Some Projection   -> (IProjection.wrap_one_seq_heap hform)
    | Some TPProjection -> (ITPProjection.wrap_one_seq_heap hform)
    | Some Protocol     -> (IProtocol.wrap_one_seq_heap hform)
    | None -> None
  in
  IMessage.heap_transformer fnc hform

let wrap_one_seq formula =
  let renamed_formula = IMessage.transform_formula wrap_one_seq_heap formula in
  renamed_formula

let wrap_one_seq formula =
  let pr = !F.print_formula in
  Debug.no_1 "Session.wrap_one_seq" pr pr wrap_one_seq formula

let wrap_one_seq_struc sformula =
  let renamed_struct = IMessage.transform_struc_formula  wrap_one_seq_heap sformula in
  renamed_struct

let wrap_one_seq_struc formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.wrap_one_seq_struc" pr pr wrap_one_seq_struc formula

(* --------------------------------------------------------------- *)
(***         wrap sequence around final transmission nodes       ***)
(***    eg: x::Chan{@S !0;;!1}<> ---> x::Chan{@S !0;;!1;;emp}<>  ***)
let wrap_last_seq_node_heap hform =
  let fnc si hform =
    match si.session_kind with
    | Some Projection   ->  (IProjection.norm_last_seq_node hform)
    | Some TPProjection ->  (ITPProjection.norm_last_seq_node hform)
    | Some Protocol     ->  (IProtocol.norm_last_seq_node hform)
    | None -> None
  in
  IMessage.heap_transformer fnc hform

let wrap_last_seq_node formula =
  let renamed_formula = IMessage.transform_formula wrap_last_seq_node_heap formula in
  renamed_formula

let wrap_last_seq_node formula =
  let pr = !F.print_formula in
  Debug.no_1 "Session.wrap_last_seq_node" pr pr wrap_last_seq_node formula

let wrap_last_seq_node_struc sformula =
  let renamed_struct = IMessage.transform_struc_formula wrap_last_seq_node_heap sformula in
  renamed_struct

let wrap_last_seq_node_struc formula =
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.wrap_last_seq_node_struc" pr pr wrap_last_seq_node_struc formula

(* ---------------------------------------------- *)
(***                norm seq                    ***)
(***    eg: (A ;; B) ;; C  => A ;; (B ;; C)     ***)
let norm_sequence_heap hform =
    let fnc si hform =
    match si.session_kind with
    | Some Projection   -> (CProjection.norm_sequence hform)
    | Some TPProjection -> (CTPProjection.norm_sequence hform)
    | Some Protocol     -> (CProtocol.norm_sequence hform)
    | None -> None
  in
  CMessage.heap_transformer fnc hform

let norm_sequence formula =
  let updated_formula = CMessage.transform_formula norm_sequence_heap formula in
  updated_formula

let norm_sequence formula =
  let pr = !CF.print_formula in
  Debug.no_1 "Session.norm_sequence" pr pr norm_sequence formula

let norm_sequence_struc sformula =
  let norm_struct = CMessage.transform_struc_formula norm_sequence_heap sformula in
  norm_struct

let norm_sequence_struc formula =
  let pr = !CF.print_struc_formula in
  Debug.no_1 "Session.norm_sequence_struc" pr pr norm_sequence_struc formula

(* ---------------------------------------------- *)
(***                norm emp seq                ***)
(***         eg: emp ;; B ;; C  => B ;; C       ***)
let norm_emp_sequence_heap hform =
    let fnc si hform =
    match si.session_kind with
    | Some Projection   -> (CProjection.remove_emps_hform hform)
    | Some TPProjection -> (CTPProjection.remove_emps_hform hform)
    | Some Protocol     -> (CProtocol.remove_emps_hform hform)
    | None -> None
  in
  CMessage.heap_transformer fnc hform

let norm_emp_sequence formula =
  let updated_formula = CMessage.transform_formula norm_emp_sequence_heap formula in
  updated_formula

let norm_emp_sequence formula =
  let pr = !CF.print_formula in
  Debug.no_1 "Session.norm_emp_sequence" pr pr norm_emp_sequence formula

let norm_emp_sequence_struc sformula =
  let norm_struct = CMessage.transform_struc_formula norm_emp_sequence_heap sformula in
  norm_struct

let norm_emp_sequence_struc formula =
  let pr = !CF.print_struc_formula in
  Debug.no_1 "Session.norm_emp_sequence_struc" pr pr norm_emp_sequence_struc formula


(* --------------------------------------------------------------- *)
(***               update the temporary view name                ***)
(***          eg: x::TEMP_SESS{...}<> --> x::Send{...}<>         ***)
let update_temp_name_heap hform =
  let fnc si hform =
    match si.session_kind with
    | Some Projection   ->  (IProjection.update_temp_name_heap hform)
    | Some TPProjection ->  (ITPProjection.update_temp_name_heap hform)
    | Some Protocol     ->  (IProtocol.update_temp_name_heap hform)
    | None -> None
  in
  IMessage.heap_transformer fnc hform

let update_temp_name form =
  IMessage.transform_formula update_temp_name_heap form

let update_temp_name form =
  let pr = !F.print_formula in
  Debug.no_1 "Session.update_temp_name" pr pr update_temp_name form

let update_temp_name_struc sform =
  IMessage.transform_struc_formula update_temp_name_heap sform

let update_temp_name_struc sform =
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.update_temp_name_struc" pr pr update_temp_name_struc sform

(* --------------------------------------------------------------- *)
(***         replace all sorts of flows to __norm flow            ***)
let reset_flow_heap hform =
  let fnc si hform =
    (* match hform with *)
    match IMessage.get_heap_node hform with
        | None -> None
        | Some hf ->
          let node = IMessage.get_node_only hf in
          Some (IMessage.map_rflow_formula_list_res_h (F.set_flow_in_formula_override F.n_flow) node)
  in
  IMessage.heap_node_transformer_gen ~flow:true ~include_msg:true fnc hform

let reset_flow form =
  IMessage.transform_formula reset_flow_heap form

let reset_flow form =
  let pr = !F.print_formula in
  Debug.no_1 "Session.reset_flow" pr pr reset_flow form

let reset_flow_struc sform =
  IMessage.transform_struc_formula reset_flow_heap sform

let reset_flow_struc sform =
  let pr = !F.print_struc_formula in
  Debug.no_1 "Session.reset_flow_struc" pr pr reset_flow_struc sform


(* -------------------------------------- *)
let csplit_sor head tail si =
  match si.session_kind with
    | Some Projection   -> CProjection.split_sor head tail
    | Some TPProjection -> CTPProjection.split_sor head tail
    | _ -> failwith (x_loc ^ ": Unexpected Protocol session.")

(* Do a split only when lhs is either a Sequence or SOr.
 * If Sequence:
 * - do the split regardless of the first parameter being a SOr
 * - preserve pointer of Sequence node in the split results
 * If SOr:
 * - do the split with an empty tail
*)
let new_lhs (lhs: CF.rflow_formula): CF.rflow_formula list =
  let lhs_hform = CMessage.get_h_formula_from_ho_param_formula lhs in
  let session_info = CMessage.get_session_info lhs_hform in
  match session_info with
  | Some si -> (match si.node_kind with
      | Some Sequence ->  let (ptr, name, ho_args, params, pos) = CMessage.get_node lhs_hform in
        let change_ptr hform =
          (match hform with
           | CF.ViewNode vn -> Some (CF.ViewNode {vn with CF.h_formula_view_node = ptr})
           | _ -> Some hform) in
        let new_lhs = csplit_sor (List.nth ho_args 0) (Some (List.nth ho_args 1)) si in
        let new_lhs = List.map (fun x -> let f = x.CF.rflow_base in
                                 let f = CMessage.transform_formula change_ptr f in
                                 CMessage.mk_rflow_formula ~sess_kind:(si.session_kind) f) new_lhs in
        new_lhs
      | Some SOr -> csplit_sor lhs None si
      | _ -> [lhs])
  | None -> [lhs]

(* let new_lhs (lhs: CF.rflow_formula): CF.rflow_formula list = *)
(*   (* norm result *) *)
(*   let res = new_lhs lhs in   *)
(*   let res = List.map (fun x -> CMessage.map_one_rflow_formula crename_sess_ptr_2_chan_ptr x) res in *)
(*   res *)

let new_lhs (lhs: CF.rflow_formula): CF.rflow_formula list =
  let pr1 = !CF.print_rflow_formula in
  let pr2 = pr_list pr1 in
  Debug.no_1 "Session.new_lhs" pr1 pr2 new_lhs lhs

(* need to check that it does not lead to unsoundness. Check that it filters out
   only those disjuncts which create unsound ctx with the new HO inst.
 *)
let check_for_ho_unsat detect_contra conseq match_ho_res =
  let fail,_,_,new_ho,es = match_ho_res in
  (* false - consider fails are due to HO inst *)
  (* true - fails are independent of inst *)
  let treat_fail_as_false ho_lst = not ((List.length ho_lst) > 0) in
  let check_fail fail =
    (* check if fail ctx contains HO inst - if it does assume failure
       is due to HO inst and treat is as an unsat *)
    match fail with
    | CF.FailCtx (_,ctx,_) ->
      let rec helper ctx =
        match ctx with
        | CF.Ctx es -> es.CF.es_ho_vars_map
        | CF.OCtx (c1,c2) -> (helper c1)@(helper c2)
      in treat_fail_as_false  (helper ctx)
    |  _ -> treat_fail_as_false new_ho (* return the fail ctx as it is  *) in
  match fail with
  | Some (f,_) -> check_fail f
  | None ->  (* no fail, check if es is unsat *)
    (* Solver.solver_detect_lhs_rhs_contra *)
    let unsat_check es =
      let conseq = match es.CF.es_conseq_for_unsat_check with
        | None -> conseq
        | Some conseq -> conseq in
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
  (* avoid the new_heap_contra for session as it  yields
     wrong results for eg. a::node<_> & a!=null results in contra *)
  let res =
    Wrapper.wrap_one_bool Globals.new_heap_contra false
        (check_for_ho_unsat detect_contra conseq) match_ho_res in
  res

let check_for_ho_unsat detect_contra conseq match_ho_res =
  let fail,_,_,_,es = match_ho_res in
  let pr1 = pr_option !CF.print_entail_state in
  let pr2 (e,_) = (add_str "fail ctx" !CF.print_list_context) e in
  let pr3 = pr_opt  pr2 in
  Debug.no_3 "Session.check_for_ho_unsat" pr3 pr1 !CF.print_formula string_of_bool (fun _ _ _ -> check_for_ho_unsat detect_contra conseq match_ho_res) fail es conseq

(* -------------------------------------- *)

let is_node_kind hform kind = CTPProjection.is_node_kind hform kind
let is_node_kind_rflow rflow kind = CTPProjection.is_node_kind_rflow rflow kind

(* -------------------------------------- *)
(* TODO: reimplement this in a simpler manner *)
(* create a SEQ given lnode and rnode *)
let rebuild_SeqSor lnode rnode largs rargs =
  let sess_kind = ref TPProjection in
  let fnc si hform =
    match si.session_kind with
    | Some Projection   ->  let () = sess_kind := Projection in (CProjection.isSeqSor hform)
    | Some TPProjection ->  (CTPProjection.isSeqSor hform)
    | Some Protocol     ->  let () = sess_kind := Protocol in (CProtocol.isSeqSor hform)
    | None -> None
  in
  let left = CMessage.heap_node_transformer_basic fnc lnode in
  match left with
  | Some lnode0 -> [CMessage.mk_rflow_formula_from_heap lnode0 ~sess_kind:(Some !sess_kind) (CF.pos_of_h_formula lnode0)], [CMessage.mk_rflow_formula_from_heap rnode ~sess_kind:(Some !sess_kind) (CF.pos_of_h_formula rnode)], "Sess" (* this needs to be solved differently! can later lead to strange behavior *)
  | None -> largs,rargs, (CF.get_node_name_x lnode)

let rebuild_SeqSor lnode rnode largs rargs =
  let pr1 = !CF.print_h_formula in
  let pr2 = pr_list (!CF.print_rflow_formula) in
  Debug.no_4 "Session.rebuild_SeqSor" pr1 pr1 pr2 pr2 (pr_triple pr2 pr2 pr_none) rebuild_SeqSor lnode rnode largs rargs

(* add a try with block *)
(* Pred<>;;tail  ------>  unfolded Pred<>;;tail  *)
let rebuild_nodes lnode rnode l_ho_args r_ho_args unfold_fun is_prime_fun =
  let default_res = l_ho_args,r_ho_args,(CF.get_node_name_x lnode),None,None in
  let helper sil sir =
    match sil.session_kind with
    | Some Projection   -> (x_add CProjection.rebuild_nodes default_res lnode rnode l_ho_args r_ho_args sil sir unfold_fun is_prime_fun)
    | Some TPProjection -> (x_add CTPProjection.rebuild_nodes default_res lnode rnode l_ho_args r_ho_args sil sir unfold_fun is_prime_fun)
    | Some Protocol     -> (x_add CProtocol.rebuild_nodes default_res lnode rnode l_ho_args r_ho_args sil sir unfold_fun is_prime_fun)
    | None -> default_res in
  try
    match lnode, rnode with
    | CF.ViewNode nodel, CF.ViewNode noder ->

      begin
        match nodel.CF.h_formula_view_session_info, noder.CF.h_formula_view_session_info with
        | Some sil,  Some sir ->  helper sil sir
        | _,_ -> default_res
      end
    | _,_ -> default_res
  with _ ->
    report_warning no_pos "Exception while normalizing session HO args";
    default_res

let rebuild_nodes lnode rnode l_ho_args r_ho_args unfold_fun is_prime_fun =
  let pr1 = !CF.print_h_formula in
  let pr2 = pr_list !CF.print_rflow_formula in
  let pr_out (a,b,c,d,e) = (pr_pair pr2 pr2) (a,b) in
  Debug.no_2 "Session.rebuild_nodes" pr1 pr1 pr_out (fun _ _ -> rebuild_nodes lnode rnode l_ho_args r_ho_args unfold_fun is_prime_fun) lnode rnode

(* add a try with block *)
(* Pred<>;;tail  ------>  unfolded Pred<>;;tail  *)
let rebuild_node node unfold_fun is_prime_fun =
  match node with
  | CF.ViewNode vn ->
    begin
      try
        let ho_args = vn.CF.h_formula_view_ho_arguments in
        match ho_args with
        | [] -> None
        | h :: [] ->
          (* assume only one HO param (may be nested HO though) for the current node *)
          let node = CForm.get_h_formula_from_ho_param_formula h in
          let default_res = None, None in
          let ho_arg, pure = CTPProjection.rebuild_node default_res node unfold_fun is_prime_fun in
          let res =
            match ho_arg with
            | Some ho_arg ->
              let node =  CF.ViewNode {vn with CF.h_formula_view_ho_arguments = ho_arg} in
              let res = CF.formula_of_heap node vn.CF.h_formula_view_pos in
              let res = map_opt_def res (fun x -> CF.add_pure_formula_to_formula x res) pure
              in Some res
            | None -> None
          in res
        | _ -> None
      with _ -> None
    end
  | _ -> None

(* should this also be fired for orders? Its initial intent was to be fired for seq *)
let rebuild_node node unfold_fun is_prime_fun =
  let pr1 = !CF.print_h_formula in
  let pr2 = pr_list !CF.print_rflow_formula in
  let pr_out = Gen.pr_opt !CF.print_formula in
  Debug.no_1 "Session.rebuild_node" pr1 pr_out (fun _ -> rebuild_node node unfold_fun is_prime_fun) node

let struc_norm ?wrap_seq:(seq=true) sf =
  let sf = if seq then
      let sf = wrap_one_seq_struc sf in
      let sf = wrap_last_seq_node_struc sf in
      sf else sf in
  let sf = x_add_1 irename_message_pointer_struc sf in
  let sf = reset_flow_struc sf in
  let sf = irename_sess_ptr_2_chan_ptr_struc sf in
  sf

let formula_norm form =
  let form = x_add_1 wrap_one_seq form in
  let form = x_add_1 wrap_last_seq_node form in
  let form = x_add_1 irename_message_pointer form in
  let form = reset_flow form in
  let form = irename_sess_ptr_2_chan_ptr form in
  form

let formula_norm form =
  let pr = !F.print_formula in
  Debug.no_1 "Session.formula_norm" pr pr formula_norm form

let norm_case vb =
  let vb = struc_norm ~wrap_seq:false vb in
  let vb = irename_all_session_pointer_struc vb in
  let vb = irename_sess_ptr_2_chan_ptr_struc vb in
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

(*
   norm3_seq
   remove_emps
 *)
let norm_slk_cformula form =
  let form = norm_sequence form in
  let form = norm_emp_sequence form in
  form

let norm_slk_cformula form =
  let pr = !CF.print_formula in
  Debug.no_1 "Session.norm_slk_cformula" pr pr norm_slk_cformula form

let norm_slk_ctx ctx =
  let f_ctx es =
    let form  = es.CF.es_formula in
    let fnc f = Some (norm_slk_cformula f) in
    let nform = CF.transform_formula (nonef, fnc, somef, (somef, somef, somef, somef, somef)) form in
    CF.Ctx { es with CF.es_formula = nform; } in
  let nctx = CF.transform_context f_ctx ctx in
  nctx

let norm_slk_ctx ctx =
  let pr = !CF.print_context in
  Debug.no_1 "Session.norm_slk_ctx" pr pr norm_slk_ctx ctx

module EVert_elem  = Ords.EVertex(Ords.Var(IForm)) ;;
module IVert_elem  = Ords.VVertex(Ords.Var(IForm)) ;;
module CVert_elem  = Ords.VVertex(Ords.Var(CForm)) ;;

module DAG_ivar    = Ords.Make_DAG(IVert_elem) ;;
module DAG_cvar    = Ords.Make_DAG(CVert_elem) ;;
module DAG_ievent  = Ords.Make_DAG(EVert_elem) ;;

let is_rel_sleek_orders rel_sv =
  SC.is_rel_sleek_orders rel_sv

let is_rel_orders rel_sv =
  SC.is_rel_orders rel_sv
