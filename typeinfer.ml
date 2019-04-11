#include "xdebug.cppo"
open VarGen
open Globals
open Exc.GTable
open Printf
open Gen.Basic
open Gen.BList
open Perm
open Mcpure_D
open Mcpure
open Label_only

module C = Cast
module E = Env
module Err = Error
module I = Iast
module IF = Iformula
module IP = Ipure
module CF = Cformula
module CFE = Cf_ext
module CP = Cpure
module MCP = Mcpure
module H = Hashtbl
module TP = Tpdispatcher
module Chk = Checks

type spec_var_info = { mutable sv_info_kind : spec_var_kind;
                       id: int; }

and spec_var_kind = typ

type spec_var_type_list_element= (ident*spec_var_info)

and spec_var_type_list = (( ident*spec_var_info)  list)

let type_list_add v en (tlist:spec_var_type_list) =
  let  n_tl = List.remove_assoc v tlist in
  (v,en)::n_tl

let mk_spec_var_info t = { sv_info_kind =t; id = fresh_int (); }

(* finding the type of self *)
let get_type_of_self ntl =
  try
    let v = snd(List.find (fun (v,_) -> v=self) ntl) in
    v.sv_info_kind
  with _ -> UNK

(************************************************************
   Primitives handling stuff
 ************************************************************)
let string_of_tlist (tlist:spec_var_type_list) =
  let rec aux t_l = (
    match t_l with
    | [] -> ""
    | hd::tl ->
      let (ident, sv_info) = hd in
      let str_hd = "(" ^ ident ^ ":" ^ (string_of_int sv_info.id) ^ ":"^ (string_of_typ sv_info.sv_info_kind) ^ ")" in
      str_hd ^ (aux tl)
  ) in
  "["^(aux tlist)^"]"

let string_of_tlist_type (tl,t)=
  (string_of_tlist tl)^", "^(string_of_typ t)

let string_of_tlist_type_option (tl,t) =
  (string_of_tlist tl)^", "^(pr_option string_of_typ t)

let res_retrieve tlist clean_res fl =
  if clean_res then
    try
      let r = Some (snd((List.find (fun (v,en)-> v=res_name) tlist))) in
      (if (CF.subsume_flow !raisable_flow_int (exlist # get_hash fl)) then
         let n_tl = List.filter (fun (v,en)->(v<>res_name)) tlist in
         (n_tl, r)
       else (tlist, r));
    with Not_found -> (tlist, None)
  else (tlist, None)

let res_retrieve tlist clean_res fl =
  let pr = pr_id in
  (* Debug.no_eff_2 "res_retrieve" [true] *)
  (*   string_of_tlist pr pr_no *)
    (fun _ _ -> res_retrieve tlist clean_res fl) tlist fl

let res_replace tlist rl clean_res fl =
  if clean_res&&(CF.subsume_flow !raisable_flow_int (exlist # get_hash fl)) then
    let n_tl = List.filter (fun (v,en)->(v<>res_name)) tlist in
    match rl with
    | None -> n_tl
    | Some e-> (res_name, e)::n_tl
  else tlist

let res_replace tlist rl clean_res fl =
  let pr = pr_id in
  (* Debug.no_eff_2 "res_replace" [true] *)
  (*   string_of_tlist pr pr_no *)
    (fun _ _ -> res_replace tlist rl clean_res fl) tlist fl

let check_shallow_var = ref false (* true *) (*LDK: test*)

let node2_to_node_x prog (h0 : IF.h_formula_heap2) : IF.h_formula_heap =
  (* match named arguments with formal parameters to generate a list of    *)
  (* position-based arguments. If a parameter does not appear in args,     *)
  (* then it is instantiated to a fresh name.                              *)
  let rec match_args (params : ident list) args_ann :  (IP.exp * IP.ann option) list =
    match params with
    | p :: rest ->
      let tmp1 = match_args rest args_ann in
      let tmp2 = List.filter (fun a -> fst((fst a)) = p) args_ann in
      let tmp3 =
        (match tmp2 with
         | [ ((_, IP.Var ((e1, e2), e3)), ann) ] -> (IP.Var ((e1, e2), e3),ann)
         | [ ((_, IP.Null p), ann) ] -> (IP.Null p,ann)
         | [ ((_, IP.IConst (i, p)), ann) ] -> (IP.IConst (i, p), ann)
         | [ ((_, IP.FConst (i, p)), ann) ] -> (IP.FConst (i, p), ann)
         | _ ->
           let fn = ("Anon"^(fresh_trailer()))
           in
           (* let () = (print_string ("\n[astsimp.ml, line 241]: fresh *)
              (* name = " ^ fn ^ "\n")) in                               *)
           (IP.Var ((fn, Unprimed), h0.IF.h_formula_heap2_pos), None) ) in
      let tmp4 = tmp3 :: tmp1 in tmp4
    | [] -> []
  in
  try
    let vdef = I.look_up_view_def_raw x_loc prog.I.prog_view_decls h0.IF.h_formula_heap2_name in
    let args = h0.IF.h_formula_heap2_arguments in
    let hargs, hanns =
      if args==[] then ([],[]) (* don't convert if empty *)
      else
        let args_ann = List.combine  h0.IF.h_formula_heap2_arguments h0.IF.h_formula_heap2_imm_param in
        List.split (match_args vdef.I.view_vars args_ann) in
    let h = { IF.h_formula_heap_node = h0.IF.h_formula_heap2_node;
              IF.h_formula_heap_name = h0.IF.h_formula_heap2_name;
              IF.h_formula_heap_deref = h0.IF.h_formula_heap2_deref;
              IF.h_formula_heap_derv = h0.IF.h_formula_heap2_derv;
              IF.h_formula_heap_split = h0.IF.h_formula_heap2_split;
              IF.h_formula_heap_imm = h0.IF.h_formula_heap2_imm;
              IF.h_formula_heap_imm_param = hanns;
			  IF.h_formula_heap_sess_ann = None;
              IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
              IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
              IF.h_formula_heap_perm = h0.IF.h_formula_heap2_perm;
              IF.h_formula_heap_arguments = hargs;
              IF.h_formula_heap_ho_arguments = h0.IF.h_formula_heap2_ho_arguments;
              IF.h_formula_heap_poly_arguments = h0.IF.h_formula_heap2_poly_arguments;
              IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
              IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos;
              IF.h_formula_heap_session_info = None;
              IF.h_formula_heap_label = h0.IF.h_formula_heap2_label; } in
    h
  with
  | Not_found ->
    let ddef =
      I.look_up_data_def 6 h0.IF.h_formula_heap2_pos prog.I.prog_data_decls
        h0.IF.h_formula_heap2_name in
    let params = List.map I.get_field_name ddef.I.data_fields (* An Hoa : un-hard-code *) in
    let args_ann = List.combine  h0.IF.h_formula_heap2_arguments h0.IF.h_formula_heap2_imm_param in
    let hargs, hanns = List.split (match_args params args_ann) in
    let h = { IF.h_formula_heap_node = h0.IF.h_formula_heap2_node;
              IF.h_formula_heap_name = h0.IF.h_formula_heap2_name;
              IF.h_formula_heap_deref = h0.IF.h_formula_heap2_deref;
              IF.h_formula_heap_derv = h0.IF.h_formula_heap2_derv;
              IF.h_formula_heap_split = h0.IF.h_formula_heap2_split;
              IF.h_formula_heap_imm = h0.IF.h_formula_heap2_imm;
              IF.h_formula_heap_imm_param = hanns;
			  IF.h_formula_heap_sess_ann = None;
              IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
              IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
              IF.h_formula_heap_arguments = hargs;
              IF.h_formula_heap_ho_arguments = h0.IF.h_formula_heap2_ho_arguments;
              IF.h_formula_heap_poly_arguments = h0.IF.h_formula_heap2_poly_arguments;
              IF.h_formula_heap_perm = h0.IF.h_formula_heap2_perm;
              IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
              IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos;
              IF.h_formula_heap_session_info = None;
              IF.h_formula_heap_label = h0.IF.h_formula_heap2_label; } in
    h

let node2_to_node i prog (h0 : IF.h_formula_heap2) : IF.h_formula_heap =
  Debug.no_1_num i "node2_to_node"
    (fun f -> Iprinter.string_of_h_formula (IF.HeapNode2 f) )
    (fun f -> Iprinter.string_of_h_formula (IF.HeapNode f))
    (fun _ -> node2_to_node_x prog h0) h0

(********************)
(* helper functions *)
(********************)

(* should create entry in tlist *)
let rec fresh_tvar_rec tlist =
  let i = fresh_int() in
  let key = "TVar__"^(string_of_int i) in
  let t2 = TVar i in
  let en={ sv_info_kind = t2; id = i} in
  (en, (key,en)::tlist)

let fresh_tvar tlist =
  let (en, n_tlist) = fresh_tvar_rec tlist in
  (en.sv_info_kind,n_tlist)

let fresh_int_en en =
  match en with
  | TVar i -> i
  | _ -> fresh_int()

let introduce_fresh_tvar_for_each_unique_poly_aux tlist args =
  let poly_lst,n_tl = List.fold_left ( fun (acc,n_tl) ty ->
      let poly_ids = Globals.get_poly_ids ty in
      List.fold_left (fun (acc,n_tl) id ->
          if List.exists (fun (pid,_) -> id = pid) acc then acc,n_tl
          else let (fv,n_tl) = fresh_tvar n_tl in
            ( (id,fv)::acc,n_tl)
        ) (acc,n_tl) poly_ids
    ) ([], tlist) args in
  poly_lst, n_tl

let introduce_fresh_tvar_for_each_unique_poly tlist args =
  let args = List.map fst args in
  introduce_fresh_tvar_for_each_unique_poly_aux tlist args

(* 2. substitute all poly typ with their corresponding tvar (created at 1.) *)
let subst_all_poly_w_tvar_aux poly_lst args =
  let poly_from, poly_to = List.split poly_lst in
  let () = y_ninfo_hp (add_str "poly_from" (pr_list pr_id)) poly_from in
  let () = y_ninfo_hp (add_str "poly_to" (pr_list string_of_typ)) poly_to in
  let args = Globals.subs_poly_typ poly_from poly_to args in
  args

let subst_all_poly_w_tvar poly_lst args =
  let tmp_r,tmp_p = List.split args in
  let tmp_r = subst_all_poly_w_tvar_aux poly_lst tmp_r in
  let tmp_r = List.combine tmp_r tmp_p in
  let ()    = y_ninfo_hp (add_str "tmp_r" (pr_list (pr_pair string_of_typ pr_id))) tmp_r in
  tmp_r


(* should create entry in tlist *)
let rec fresh_tvar_rec tlist =
  let i = fresh_int() in
  let key = "TVar__"^(string_of_int i) in
  let t2 = TVar i in
  let en={ sv_info_kind = t2; id = i} in
  (en, (key,en)::tlist)

let fresh_tvar tlist =
  let (en, n_tlist) = fresh_tvar_rec tlist in
  (en.sv_info_kind,n_tlist)

let fresh_int_en en =
  match en with
  | TVar i -> i
  | _ -> fresh_int()

let fresh_poly_tlist tlist =
  let i              = fresh_int () in
  let fresh_poly     = poly_name i  in
  let fresh_poly_typ = Poly fresh_poly in
  let en = { sv_info_kind = fresh_poly_typ; id = i} in
  (fresh_poly_typ, (fresh_poly,en)::tlist)

(* introduces a fresh poly type for id, if id not in poly_lst *)
let update_tlist_w_fresh_poly_for_id poly_lst tlist id =
  if List.exists (fun (pid,_) -> id = pid) poly_lst then poly_lst,tlist
  else let (fv,n_tlist) = fresh_poly_tlist tlist in
    ( (id,fv)::poly_lst,n_tlist)

(* introduces a fresh poly type for each id in id_lst, if id not in poly_lst *)
let update_tlist_w_fresh_poly_for_id_list poly_lst tlist id_lst =
  List.fold_left (fun (acc,n_tl) id ->
      update_tlist_w_fresh_poly_for_id acc n_tl id
    ) (poly_lst,tlist) id_lst

(* returns the list of freshly introduced poly types and the updated tlist *)
let introduce_fresh_poly_for_each_unique_poly tlist args =
  let poly_lst,n_tl = List.fold_left ( fun (acc,n_tl) ty ->
      let poly_ids = Globals.get_poly_ids ty in
      update_tlist_w_fresh_poly_for_id_list acc n_tl poly_ids
    ) ([], tlist) args in
  poly_lst, n_tl

(* 2. substitute all poly typ with their corresponding tvar (created at 1.) *)
let subst_all_poly_w_poly poly_lst args =
  let poly_from, poly_to = List.split poly_lst in
  let () = y_ninfo_hp (add_str "poly_from" (pr_list pr_id)) poly_from in
  let () = y_ninfo_hp (add_str "poly_to" (pr_list string_of_typ)) poly_to in
  let args = Globals.subs_poly_typ poly_from poly_to args in
  args

let rec dim_unify d1 d2 = if (d1 = d2) then Some d1 else None

and must_unify (k1 : typ) (k2 : typ) tlist pos : (spec_var_type_list * typ) =
  let pr = string_of_typ in
  let pr_tl =  string_of_tlist in
  let pr_out = pr_pair pr_tl string_of_typ in
  Debug.no_3 "must_unify" pr pr pr_tl pr_out (fun _ _ _ -> must_unify_x k1 k2 tlist pos) k1 k2 tlist

and must_unify_x (k1 : typ) (k2 : typ) tlist pos : (spec_var_type_list * typ) =
  let (n_tlist,k) = x_add unify_type k1 k2 tlist in
  match k with
  | Some r -> (n_tlist,r)      (* unification succeeds -- return an option type *)
  | None -> let msg = ("UNIFICATION ERROR : at location "^(string_of_full_loc pos)
                       ^" types "^(string_of_typ (get_type_entire tlist k1))
                       ^" and "^(string_of_typ (get_type_entire tlist k2))^" are inconsistent") in
    if !Globals.enforce_type_error then report_error pos msg
    else (report_warning pos msg; (n_tlist, UNK))

and must_unify_expect (k1 : typ) (k2 : typ) tlist pos : (spec_var_type_list * typ)  =
  (* let pr = (\* string_of_typ *\) pr_none in *)
  Debug.no_3 "must_unify_expect" string_of_typ string_of_typ string_of_tlist string_of_tlist_type (fun _ _ _ -> must_unify_expect_x k1 k2 tlist pos) k1 k2 tlist

and must_unify_expect_x (k1 : typ) (k2 : typ) tlist pos : (spec_var_type_list * typ) =
  let (n_tl,k) = unify_expect k1 k2 tlist in
  match k with
  | Some r -> (n_tl,r)
  | None -> report_error pos ("TYPE ERROR 1 : Found "
                              ^(string_of_typ (get_type_entire tlist k1))
                              ^" but expecting "^(string_of_typ (get_type_entire  tlist k2)))

and unify_type (k1 : spec_var_kind) (k2 : spec_var_kind)  tlist : (spec_var_type_list * (typ option)) =
  let pr = string_of_spec_var_kind in
  let pr1 = string_of_tlist in
  let pr2 = pr_pair pr1 (pr_option pr) in
  Debug.no_3 "unify_type" pr pr pr1 pr2 unify_type_x k1 k2 tlist

and unify_type_x (k1 : spec_var_kind) (k2 : spec_var_kind) tlist : (spec_var_type_list * (typ option)) =
  x_add unify_type_modify true k1 k2 tlist

and unify_type_modify (modify_flag:bool) (k1 : spec_var_kind) (k2 : spec_var_kind) tlist : (spec_var_type_list*(typ option)) =
  let rec repl_tlist i k tl = repl_tvar_in unify modify_flag tl i k
  and unify k1 k2 tl =
    (* let () = y_binfo_hp (add_str "k111111" (string_of_typ)) k1 in *)
    (* let () = y_binfo_hp (add_str "k222222" (string_of_typ)) k2 in *)
    match k1,k2 with
    | UNK, _ -> (tl,Some k2)
    | _, UNK -> (tl,Some k1)
    | Int, NUM -> (tl,Some Int) (* HACK here : give refined type *)
    | Float, NUM -> (tl,Some Float) (* give refined type *)
    | AnnT, NUM -> (tl,Some AnnT) (* give refined type *)
    | NUM, Int -> (tl,Some Int)
    | NUM, Float -> (tl,Some Float)
    | NUM, AnnT -> (tl,Some AnnT)
    | Int, Float -> (tl,Some Float) (*LDK: support floating point*)
    | Float, Int -> (tl,Some Float) (*LDK*)
    | Tree_sh, Tree_sh -> (tl,Some Tree_sh)
    (*TODO: Need to unify the param list for polymorphic Named *)
    | Named (n1, _), Named (n2, _) when (String.compare n1 "memLoc" = 0) || n1="" ->   (* k1 is primitive memory predicate *)
      (* let () = y_binfo_pp  "memloc comparison1" in *)
      (tl, Some (mkNamedTyp n2 ))
    | Named (n1, _), Named (n2, _) when (String.compare n2 "memLoc" = 0) || n2=""  ->   (* k2 is primitive memory predicate *)
      (* let () = y_binfo_pp "unify Named typ with inttttttttttttt 11111111111" in *)
      (tl, Some (mkNamedTyp n1))
    | Named (n1, []), Int when (cmp_typ k1 role_typ) ->
      (* let () = y_binfo_pp "unify Named typ with inttttttttttttt 22222222222" in *)
      (tl, Some Int)
    | Int, Named (n2, []) when (cmp_typ k2 role_typ) -> (tl, Some Int)
    (* ************************** *)
    (* ******* temp hack ******** *)
    (* hack to make the mapping unify when part of a primitive predicate *)
    (* need to find a long term solution *)
    | _, Named (n, _) when List.mem n map_related_names -> (tl, Some k1)
    | Named (n, _), _ when List.mem n map_related_names -> (tl, Some k2)
    | Named (n1, ([] as tl1)), Named (n2, ((_::_) as tl2))
    | Named (n1, ((_::_) as tl1) ), Named (n2, ([] as tl2)) -> (tl, None)
    | Named (n1, ((t1::_) as tl1)), Named (n2, ((t2::_) as tl2)) ->
      (* unify the type parameters.
         if the unification of parameters is successful
         return (Some tk) along with the updated type list.
      *)
      let () = y_tinfo_hp (add_str "tl1111111111111" (pr_list string_of_typ)) tl1 in
      let () = y_tinfo_hp (add_str "tl2222222222222" (pr_list string_of_typ)) tl2 in
      let rec unify_param tl1 tl2 tlist tk =
        match tl1, tl2 with
        | [], []                -> (tlist, Some tk)
        | t1::_, [] | [], t1::_ -> (tlist, None)
        | t1::tl1, t2::tl2      ->
          let n_tl, res_opt = x_add unify_type t1 t2 tlist in
          match res_opt with
          | Some _ -> unify_param tl1 tl2 n_tl tk
          | None   -> (n_tl, None)
      in
      if sub_type (mkNamedTyp n1) (mkNamedTyp n2) then
        unify_param tl1 tl2 tl k1
      else if sub_type (mkNamedTyp n2) (mkNamedTyp n1) then
        unify_param tl1 tl2 tl k2
      else (tl, None)
    (* ******* end - temp hack ******** *)
    (* ******************************** *)
    (* | Int, Poly id  | Poly id, Int -> (tl,Some Int)
     * | Bool, Poly id  | Poly id, Bool -> (tl,Some Bool) *)
    | ty, Poly id  | Poly id, ty ->
      x_add unify_poly unify repl_tlist id ty tl
    | t1, t2  -> (
        let () = y_tinfo_pp  "else" in
        let () = Debug.tinfo_hprint (add_str  "t1 " (string_of_typ)) t1 no_pos in
        let () = Debug.tinfo_hprint (add_str  "t2 " (string_of_typ)) t2 no_pos in
        if is_null_type t1 then (tlist, Some k2)
        else if is_null_type t2 then (tlist, Some k1)
        else
        if sub_type t1 t2 && not(Globals.contains_poly t2) then (tlist, Some k2)  (* found t1, but expecting t2 *)
        else if sub_type t2 t1 && not(Globals.contains_poly t1) then (tlist,Some k1)
        else
          begin
            match t1,t2 with
            | TVar i1, _ -> repl_tlist i1 k2 tl
            | _, TVar i2 -> repl_tlist i2 k1 tl
            | BagT x1,BagT x2 ->
              (match (unify x1 x2 tl) with
               | (n_tl,Some t) -> (n_tl,Some (BagT t))
               | (n_tl,None) -> (n_tl,None))
            | List x1,List x2 ->
              (match (unify x1 x2 tl) with
               | (n_tl,Some t) -> (n_tl,Some (List t))
               | (n_tl,None) -> (n_tl,None))
            | Array (x1,d1),Array (x2,d2) ->
              (match (dim_unify d1 d2), (unify x1 x2 tl) with
               | Some d, (n_tl,Some t)  -> (n_tl,Some (Array (t,d)))
               | _,(n_tl,_) -> (n_tl,None))
            | Mapping (t1,t2), Mapping (t3,t4) ->
              (
                let n_tl, t5 = x_add unify_type t1 t3 tl in
                let n_tl2, t6 = x_add unify_type t2 t4 n_tl in
                match t5,t6 with
                | Some d1, Some d2 -> (n_tl2,Some (Mapping (d1,d2)))
                | _ -> (n_tl2,None))
            | Mapping (t1,t2), Array (x1,d1)
            | Array (x1,d1), Mapping (t1,t2) ->
              let n_tl, t3 = unify x1 t2 tl in
              (match t3 with
               | Some t3 -> (n_tl, Some (Mapping (t1,t2)))
               | _ -> (n_tl, None))
            | Tup2 (t1,t2),Tup2 (t3,t4) -> (
                let n_tl, t5 = unify t1 t3 tl in
                let n_tl2, t6 = unify t2 t4 n_tl in
                match t5,t6 with
                | Some d1, Some d2 -> (n_tl2,Some (Tup2 (d1,d2)))
                | _ -> (n_tl2,None))
            | _,_ -> (tl,None)
          end
      )
  in unify k1 k2 tlist

(* k2 is expected type *)
and unify_expect (k1 : spec_var_kind) (k2 : spec_var_kind) tlist : (spec_var_type_list*(typ option)) =
  unify_expect_modify true k1 k2 tlist

and must_unify_expect_test k1 k2 tlist pos =
  let (_,k) = unify_expect_modify false k1 k2 tlist  in
  match k with
  | Some r -> r
  | None -> report_error pos ("TYPE ERROR 2 : Found "
                              ^(string_of_typ (k1))
                              ^" but expecting "^(string_of_typ (k2)))

and must_unify_expect_test_2_1 k1 k2 k3 tlist pos =
  let (_, k) = unify_expect_modify false k1 k2 tlist in
  match k with
  | Some r -> r
  | None -> must_unify_expect_test k1 k3 tlist pos

and must_unify_expect_test_2 k1 k2 k3 tlist pos =
  Debug.no_2 "must_unify_expect_test_2" pr_none pr_none pr_none (fun _ _ -> must_unify_expect_test_2_1 k1 k2 k3 tlist pos) k1 k2

and subtype_expect_test _ _ = true

and unify_expect_modify (modify_flag:bool) (k1 : spec_var_kind) (k2 : spec_var_kind) tlist : (spec_var_type_list*(typ option)) =
  let pr = string_of_typ in
  Debug.no_2 "unify_expect_modify" pr (add_str "expected" pr) string_of_tlist_type_option (fun _ _ -> unify_expect_modify_x modify_flag k1 k2 tlist) k1 k2

(* unifies a poly type with any other type    *)
(* eg.   unify_poly T1 int [T1:1:TVar[1], ..] *)
(*           ==> ([T1:1:int, ..], int)        *)
and unify_poly_x unify repl id ty tlist = (* if true then tlist, Some ty else *)
  (* let helper *)
  (* if id in the list already must unify  - otherwise just add *)
  let () = y_tinfo_hp (add_str "unify_poly" (pr_pair pr_id string_of_typ)) (id,ty)  in
  (* let () = y_tinfo_hp (add_str "tlist" (string_of_tlist)) tlist  in *)
  try
    (* check if poly id is in tl already *)
    let t0 = List.assoc id tlist in
    let () = y_tinfo_hp (add_str "t0 typ" string_of_typ) t0.sv_info_kind in
    let () = y_tinfo_hp (add_str "tlist" string_of_tlist) tlist in
    (* unify the existing poly with the expected ty (eg unify TVar[1] int)*)
    let n_tl, t2 =
      (* need to recheck how to unify two poly types *)
      match ty with
      | Poly _  -> tlist, Some ty
      | TVar i1 -> begin
          match t0.sv_info_kind with
        | Poly _ -> repl i1 (Poly id) tlist  (* tlist, Some (Poly id) *)
        | _ -> repl i1 t0.sv_info_kind tlist
          end
      | Int | Bool | NUM | Float | BagT _ | List _ | Tup2 _ | Array _ | Mapping _ | Named _
        ->
        begin
          match t0.sv_info_kind with
          | Poly poly_id -> if (String.equal id poly_id) then
              (* let () = y_binfo_pp ("idddd" ^ id) in *)
              (* let () = y_binfo_pp ("poly_id" ^ poly_id) in *)
              tlist, Some ty
            else unify t0.sv_info_kind ty tlist
          | _ -> unify t0.sv_info_kind ty tlist
        end
        (* if id in associaed list corresponds to then just return updated tlist
           otherwise call unify  <<unify t0.sv_info_kind ty tlist>>
        *)
      | _       -> unify t0.sv_info_kind ty tlist in
    match t2 with
    | Some t2 ->
      (* if unification is possible update n_tl to map id to the unified type *)
      let new_tl = type_list_add id (mk_spec_var_info t2) n_tl in
      (new_tl, Some t2)
    | None -> (tlist, None)
  with Not_found ->
    let new_tl =  (id, (mk_spec_var_info (Poly id)))::tlist in
    match ty with
      | Poly _  -> new_tl, Some ty
      | TVar i1 -> repl i1 (Poly id) new_tl  (* tlist, Some (Poly id) *)
      | _       -> (new_tl, Some ty)

and unify_poly unify repl id ty tlist =
  let pr = string_of_spec_var_kind in
  let pr2 = pr_pair string_of_tlist (pr_option pr) in
  Debug.no_3 "unify_poly" pr pr string_of_tlist pr2 (fun _ _ _ -> unify_poly_x unify repl id ty tlist) (Poly id) ty tlist


(* k2 is expected type *)
and unify_expect_modify_x (modify_flag:bool) (k1 : spec_var_kind) (k2 : spec_var_kind) tlist : (spec_var_type_list*(typ option)) =
  let bal_unify k1 k2 tl= x_add unify_type_modify modify_flag k1 k2 tl in
  let repl_tlist i k tl = repl_tvar_in bal_unify modify_flag tl i k in
  let rec unify k1 k2 tl =
    match k1,k2 with
    | UNK, _ -> (tl ,Some k2)
    | _, UNK -> (tl, Some k1)
    | Poly id, ty
    | ty, Poly id -> x_add unify_poly unify repl_tlist id ty tl
    | Int, NUM   | Float, NUM -> (tl,Some k1) (* give refined type *)
    | NUM, Float | NUM,Int -> (tl,Some k2) (* give refined type *)
    | Int , Float -> (tl,Some Float) (*LDK*)
    | Float , Int -> (tl,Some Float) (*LDK*)
    | t1, t2  ->
      if sub_type t1 t2 then (tl,Some k2)  (* found t1, but expecting t2 *)
      (* else if sub_type t2 t1 then Some k1 *)
      else
        begin
          match t1,t2 with
          | TVar i1,_ -> repl_tlist i1 k2 tl
          | _,TVar i2 -> repl_tlist i2 k1 tl
          | BagT x1,BagT x2 -> (
              match (unify x1 x2 tl) with
              | (n_tl,Some t) -> (n_tl,Some (BagT t))
              | (n_tl,None) -> (n_tl,None)
            )
          | List x1,List x2 -> (
              match (unify x1 x2 tl) with
              | (n_tl,Some t) -> (n_tl,Some (List t))
              | (n_tl,None) -> (n_tl,None)
            )
          | Tup2 (t1,t2),Tup2 (t3,t4) -> (
              let n_tl, t5 = unify t1 t3 tl in
              let n_tl2, t6 = unify t2 t4 n_tl in
              match t5,t6 with
              | Some d1, Some d2 -> (n_tl2,Some (Tup2 (d1,d2)))
              | _ -> (n_tl2,None)
            )
          | Array (x1,d1),Array (x2,d2) -> (
              match (dim_unify d1 d2), (unify x1 x2 tl) with
              | Some d, (n_tl,Some t)  -> (n_tl,Some (Array (t,d)))
              | _,(n_tl,_)-> (n_tl,None)
            )
          | Mapping (t1,t2), Mapping (t3,t4) -> (
              let n_tl, t5 = unify t1 t3 tl in
              let n_tl2, t6 = unify t2 t4 n_tl in
              match t5,t6 with
              | Some d1, Some d2 -> (n_tl2,Some (Mapping (d1,d2)))
              | _ -> (n_tl2,None))
          | Mapping (t1,t2), Array (x1,d1)
          | Array (x1,d1), Mapping (t1,t2) ->
            let n_tl, t3 = unify x1 t2 tl in
            (match t3 with
             | Some t3 -> (n_tl, Some (Mapping (t1,t2)))
             | _ -> (n_tl, None))
          | _,_ -> (tlist,None)
        end
  in unify k1 k2 tlist

and repl_tvar_in unify flag tlist i k =
  Debug.no_eff_4 "repl_tvar_in" [false;false;false;true]
    string_of_bool string_of_int string_of_typ string_of_tlist string_of_tlist_type_option
    (fun _ _ _ _ -> repl_tvar_in_x unify flag tlist i k) flag i k tlist

(* TODO : should TVar j be updated to point to i *)
and repl_tvar_in_x unify flag tlist i k =
  let test x = (
    let i2 = x.id in
    match k with
    | TVar j -> i2=i || i2=j
    | _ -> i2=i
  ) in
  let new_k = (
    match k with
    | TVar _ -> UNK
    | _ -> k
  ) in
  let res_t = List.fold_right (fun (v,en) (_tl,et) ->
      match et with
      | None -> (_tl,et)
      | Some t1 ->
        if not(test en) then (_tl,et)
        else
          match en.sv_info_kind with
          | TVar _ -> (_tl,et)
          | t -> (unify t t1 _tl)
    ) tlist (tlist, Some new_k) in
  match res_t with
  | (n_tl,None) ->    (n_tl,None)
  | (n_tl,Some ut) ->
    let ut = match ut with
      | UNK -> k
      | _ -> ut in
    (* TVar i --> ut *)
    if flag then (
      let rec aux t_l = (
        match t_l with
        | [] -> []
        | (v,en)::tail ->
          if test en then
            let n_en = { sv_info_kind = ut; id = en.id} in
            let n_el = (v,n_en) in
            n_el::(aux tail)
          else
            let nt = subs_tvar_in_typ en.sv_info_kind i ut in
            let n_en = { sv_info_kind = nt; id = en.id} in
            let n_el = (v,n_en) in
            n_el::(aux tail)
      ) in
      let n_tlist = aux n_tl in
      (n_tlist,Some ut)
    ) else (n_tl,Some ut)



and get_type_entire tlist t =
  let rec helper t = match t with
    | TVar j -> get_type tlist j
    | BagT et -> BagT (helper et)
    | List et -> List (helper et)
    | Array (et,d) -> Array (helper et,d)
    | Mapping (t1,t2) -> Mapping (helper t1,helper t2)
    (* | Named tn -> Named (tn^"11111") (\* if it is a pointer with poly type field, then change the type to tn[`T], question is, how to know its field *\) *)
    | _ -> t
  in helper t

and get_type tlist i =
  let key = "TVar__"^(string_of_int i) in
  ( try
      let (v,en) = List.find (fun (var,bk) -> var=key) tlist in
      en.sv_info_kind
    with _ -> report_error no_pos ("UNEXPECTED : Type Var "^key^" cannot be found in tlist"))

and string_of_spec_var_kind (k : spec_var_kind) =
  string_of_typ k

and fresh_proc_var_kind tlist et =
  match et with
  | TVar i -> { sv_info_kind = et; id = i}
  | _ -> { sv_info_kind = et; id = fresh_int ()}


(* TODO WN : NEED to re-check this function *)
and trans_type (prog : I.prog_decl) (t : typ) (pos : loc) : typ =
  match t with
  | Named (c, tl) ->
    (try
       let todo_unk = x_add I.look_up_data_def_raw prog.I.prog_data_decls c
       in mkNamedTyp ~args:(List.map (fun t0 -> trans_type prog t0 pos) tl) c
     with
     | Not_found ->
       (try
          let todo_unk = I.look_up_view_def_raw x_loc prog.I.prog_view_decls c
          in mkNamedTyp ~args:tl c
        with
        | Not_found ->
          (try
             let todo_unk = I.look_up_enum_def_raw prog.I.prog_enum_decls c
             in Int
           with
           | Not_found -> (* An Hoa : cannot find the type, just keep the name. *)
             if CF.view_prim_lst # mem c then mkNamedTyp ~args:tl c
             else
               (* if !inter then*)
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = c ^ " is neither data, enum type, nor prim pred";
                 }
                 (*else let () = report_warning pos ("Type " ^ c ^ " is not yet defined!") in
                   let () = undef_data_types := (c, pos) :: !undef_data_types in
                   Named c (* Store this temporarily *)*)
          )))
  | Array (et, r) -> Array (trans_type prog et pos, r) (* An Hoa *)
  | Mapping (t1, t2) -> Mapping (trans_type prog t1 pos, trans_type prog t2 pos)
  | p -> p

and trans_type_back (te : typ) : typ =
  match te with
  | Named (n, tl) -> Named (n, (List.map trans_type_back tl))
  | Array (t, d) -> Array (trans_type_back t, d) (* An Hoa *)
  | Mapping (t1, t2) -> Mapping (trans_type_back t1, trans_type_back t2)
  | p -> p

and sub_type_x (t1 : typ) (t2 : typ) =
  try
    let it1 = trans_type_back t1 in
    let it2 = trans_type_back t2 in
    I.sub_type it1 it2
  with _ -> false

and sub_type (t1 : typ) (t2 : typ) =
  let pr = string_of_typ in
  Debug.no_2 "sub_type" pr pr string_of_bool sub_type_x t1 t2

and gather_type_info_var (var : ident) tlist (ex_t : typ) pos : (spec_var_type_list*typ) =
  let pr = (add_str "expected type" string_of_typ) in
  Debug.no_3 "gather_type_info_var" (* [false;true] *) (fun x -> ("ident: "^x)) string_of_tlist pr string_of_tlist_type
    (fun _ _ _ -> gather_type_info_var_x var tlist ex_t pos) var tlist ex_t

and gather_type_info_var_x (var : ident) tlist (ex_t : spec_var_kind) pos : (spec_var_type_list*spec_var_kind) =
  if (is_dont_care_var var) then
    (tlist, UNK) (* for vars such as _ and # *)
  else

    try
      let (ident, k) = List.find (fun (a,b) -> a = var) tlist in  (* higher order func, return the first ele in the tlist *)
      let (n_tlist,tmp) = x_add must_unify k.sv_info_kind ex_t tlist pos in
      let n_tlist = type_list_add ident {sv_info_kind = tmp;id=k.id} n_tlist in
      (n_tlist, tmp)
    with
    | Not_found ->
      let ex_t = get_type_entire tlist ex_t in
      let vk = fresh_proc_var_kind tlist ex_t in
      ((var,vk)::tlist, vk.sv_info_kind)
    | ex ->
      let _ = print_string_quiet (get_backtrace_quiet ()) in
      report_error pos ("gather_type_info_var : unexpected exception "^(Printexc.to_string ex))
(* raise ex *)

and gather_type_info_exp prog a0 tlist et =
  Debug.no_3 "gather_type_info_exp" (* [false;true] *)
    Iprinter.string_of_formula_exp string_of_tlist string_of_typ
    string_of_tlist_type
    (fun _ _ _ -> gather_type_info_exp_x prog a0 tlist et) a0 tlist et

(* et - expected type *)
and gather_type_info_exp_x prog a0 tlist et =
  match a0 with
  | IP.Null pos ->
    let (new_et,n_tl) = fresh_tvar tlist in
    (n_tl, new_et)
  | IP.Ann_Exp (e,t, pos) ->
    (* TODO WN : check if t<:e *)
    let () = y_tinfo_pp "inside Ann_Exp" in
    let (n_tl,n_typ) = gather_type_info_exp_x prog e tlist t in
    let () = y_tinfo_hp (add_str "Ann_Exp" (pr_pair string_of_typ string_of_typ)) (t,n_typ) in
    let (n_tl,n_typ) = x_add must_unify_expect n_typ t n_tl pos in
    (n_tl,n_typ)
  | IP.Var ((sv, sp), pos) ->
    let () = y_tinfo_pp "here1" in
    let (n_tl,n_typ) = x_add gather_type_info_var sv tlist et pos in
    let () = y_tinfo_pp "here2" in
    (n_tl,n_typ)
  | IP.Level ((sv, sp), pos) ->
    (*sv should be of lock_typ*)
    let (n_tlist,_) = x_add gather_type_info_var sv tlist lock_typ pos in
    (*level(sv) should be of type Int*)
    let (n_tlist,_)= x_add must_unify_expect Globals.level_data_typ et n_tlist pos in
    (n_tlist,Globals.level_data_typ)
  | IP.Tsconst (_,pos) ->
    let t = Tree_sh in
    let (n_tlist,_) = x_add must_unify_expect t et tlist pos in
    (n_tlist,t)
  | IP.AConst (_,pos) ->
    let t = I.ann_type in
    let (n_tlist,_) = x_add must_unify_expect t et tlist pos in
    (n_tlist,t)
  | IP.IConst (_,pos) | IP.InfConst (_,pos) | IP.NegInfConst (_,pos) ->
    let t = I.int_type in
    let (n_tl,n_typ) = x_add must_unify_expect t et tlist pos in
    (n_tl,n_typ)
  | IP.FConst (_,pos) ->
    let t = I.float_type in
    let (n_tl,n_typ) = x_add must_unify_expect t et tlist pos in
    (n_tl,n_typ)
  | IP.Tup2 ((p1,p2), pos) ->
    let (new_et, n_tl) = fresh_tvar tlist in
    let (n_tl1,t1) = x_add gather_type_info_exp prog p1 n_tl new_et in
    let (new_et2, n_tl2) = fresh_tvar n_tl1 in
    let (n_tl3,t2) = gather_type_info_exp_x prog p2 n_tl2 new_et2 in
    let (n_tl4,t) = x_add must_unify_expect et (Tup2 (t1,t2)) n_tl3 pos in
    (n_tl4,t)
  | IP.Bptriple ((pc,pt,pa), pos) ->
    let todo_unk:Globals.typ = x_add must_unify_expect_test_2 et Bptyp Tree_sh tlist pos in
    let (new_et, n_tl) = fresh_tvar tlist in
    let nt = List.find (fun (v,en) -> en.sv_info_kind = new_et) n_tl in
    let (tmp1,tmp2)=nt in
    let (n_tl1,t1) = x_add gather_type_info_exp prog pc n_tl new_et in (* Int *)
    let (n_tl2,t2) = gather_type_info_exp_x prog pt n_tl1 new_et in (* Int *)
    let (n_tl3,t3) = gather_type_info_exp_x prog pa n_tl2 new_et in (* Int *)
    let (n_tlist1,_) = x_add must_unify_expect t1 Int n_tl3 pos in
    let (n_tlist2,_) = x_add must_unify_expect t2 Int n_tlist1 pos in
    let (n_tlist3,_) = x_add must_unify_expect t3 Int n_tlist2 pos in
    let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tlist3 in
    (n_tl, Bptyp)
  | IP.Add (a1, a2, pos) ->
    let unify_ptr_arithmetic (t1,new_et) (t2,new_et2) et n_tl2 pos =
      if is_possible_node_typ t1 && !Globals.ptr_arith_flag then
        let () = y_tinfo_hp (add_str "(t1,new_et)" (pr_pair string_of_typ string_of_typ)) (t1,new_et) in
        let (n_tl2,_) = x_add must_unify_expect t1 new_et n_tl2 pos in
        let (n_tlist2,_) = x_add must_unify_expect t2 NUM n_tl2 pos in
        (n_tlist2,t1)
      else if is_possible_node_typ t2 && !Globals.ptr_arith_flag then
        let () = y_tinfo_hp (add_str "(t2,new_et2)" (pr_pair string_of_typ string_of_typ)) (t2,new_et2) in
        let (n_tl2,_) = x_add must_unify_expect t2 new_et2 n_tl2 pos in
        let (n_tlist2,_) = x_add must_unify_expect t1 NUM n_tl2 pos in
        (n_tlist2,t2)
      else
        let (n_tlist1,t1) = x_add must_unify_expect t1 et n_tl2 pos in
        let (n_tlist2,t2) = x_add must_unify_expect t2 et n_tlist1 pos in
        let (n_tlist2,t2) = x_add must_unify t1 t2 n_tlist2 pos in
        (n_tlist2,t2)
    in
    let unify_ptr_arithmetic (t1,new_et) (t2,new_et2) et n_tl2 pos =
      let pr_t = string_of_typ in
      Debug.no_4 "unify_ptr_arithmetic" pr_t pr_t pr_t string_of_tlist (pr_pair string_of_tlist string_of_typ)
        (fun _ _ _ _ -> unify_ptr_arithmetic (t1,new_et) (t2,new_et2) et n_tl2 pos) t1 t2 et n_tl2 in
    let todo_unk:Globals.typ = x_add must_unify_expect_test_2 et NUM Tree_sh tlist pos in (* UNK, Int, Float, NUm, Tvar *)
    let (new_et, n_tl) =
      if !Globals.ptr_arith_flag then (UNK,tlist)
      else fresh_tvar tlist in
    (* let (new_et2, n_tl) = fresh_tvar n_tl in           *)
    let tmp1 = try
        fst(List.find (fun (v,en) -> en.sv_info_kind = new_et) n_tl)
      with _ -> "" in
    (* let (tmp1,tmp2)=nt in            *)
    let () = x_tinfo_hp (add_str "add(et)" string_of_typ) et no_pos in
    let () = x_tinfo_hp (add_str "add(new_et)" string_of_typ) new_et no_pos in
    let (n_tl1,t1) = gather_type_info_exp prog a1 n_tl new_et in (* tvar, Int, Float *)
    let () = x_tinfo_hp (add_str "a1" !IP.print_exp) a1 no_pos in
    let () = x_tinfo_hp (add_str "t1" string_of_typ) t1 no_pos in
    let new_et2 = if is_node_typ t1 && !Globals.ptr_arith_flag
      then Int else new_et in
    let (n_tl2,t2) = gather_type_info_exp prog a2 n_tl1 new_et2 in
    let () = x_tinfo_hp (add_str "a1" !IP.print_exp) a2 no_pos in
    let () = x_tinfo_hp (add_str "t2" string_of_typ) t2 no_pos in

    let (n_tlist2,t2) = x_add unify_ptr_arithmetic (t1,new_et)
    (t2,new_et2) et n_tl2 pos in

    let n_tl = (* List.filter (fun (v,en) -> v<>tmp1) *) n_tlist2 in
    (n_tl,t2)
  | IP.Subtract (a1, a2, pos) ->
    let todo_unk:Globals.typ = x_add must_unify_expect_test et NUM tlist pos in (* UNK, Int, Float, NUm, Tvar *)
    let () = y_tinfo_pp "here in subtract" in
    let (new_et1, n_tl) = fresh_tvar tlist in
    let (new_et2, n_tl) = fresh_tvar n_tl in
    let nt = List.find (fun (v,en) -> en.sv_info_kind = new_et1) n_tl in
    let (tmp1,tmp2)=nt in
    let () = y_tinfo_hp (add_str "new_et1" string_of_typ) new_et1 in
    let (n_tl1,t1) = gather_type_info_exp_x prog a1 n_tl new_et1 in (* tvar, Int, Float *)
    let (n_tl2,t2) = gather_type_info_exp_x prog a2 n_tl1 new_et2 in (* tvar, Int, Float *)
    let () = y_tinfo_hp (add_str "(t1,t2)" (pr_pair string_of_typ string_of_typ)) (t1,t2) in
    if is_possible_node_typ t1 then (
      if is_possible_node_typ t2 then
        (* let () = y_tinfo_hp (add_str "t2" string_of_typ) t2 in *)
         let (n_tl2,_) = x_add must_unify_expect t2 new_et1 n_tl2 pos in
         let (n_tlist2,_) = x_add must_unify_expect t1 new_et2 n_tl2 pos in
         (n_tlist2,Int)
      else
        (* let () = y_tinfo_hp (add_str "t2" string_of_typ) t2 in *)
        let (n_tl2,_) = x_add must_unify_expect t1 new_et1 n_tl1 pos in
        let (n_tlist2,_) = x_add must_unify_expect t2 NUM n_tl2 pos in
        (n_tlist2,t1))
    else if is_possible_node_typ t2 then
        let (n_tl2,_) = x_add must_unify_expect t2 new_et2 n_tl2 pos in
        let (n_tlist2,_) = x_add must_unify_expect t1 NUM n_tl2 pos in
        (n_tlist2,t2)
    else
    (* if (is_possible_node_typ t1) && (is_possible_node_typ t2) then *)
    (*   let (n_tl2,_) = x_add must_unify_expect t2 new_et n_tl2 pos in *)
    (*   let (n_tlist2,_) = x_add must_unify_expect t1 new_et n_tl2 pos in *)
    (*   (n_tlist2,Int) *)
    (* else *)
      (* let (n_tlist1,t1) = x_add must_unify_expect t1 et n_tl2 pos in *)
      (* let (n_tlist2,t2) = x_add must_unify_expect t2 et n_tlist1 pos in *)
      (* let (n_tlist2,t2) = x_add must_unify t1 t2 n_tlist2 pos in *)
      (* (n_tlist2,t2) *)
      let (n_tlist1,t1) = x_add must_unify_expect t1 et n_tl2 pos in
      let (n_tlist2,t2) = x_add must_unify_expect t2 t1 n_tlist1 pos in
      let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tlist2 in
      (n_tl,t2)
  | IP.Max (a1, a2, pos) | IP.Min (a1, a2, pos)
  | IP.Mult (a1, a2, pos) | IP.Div (a1, a2, pos) ->
    let todo_unk:Globals.typ = x_add must_unify_expect_test et NUM tlist pos in (* UNK, Int, Float, NUm, Tvar *)
    let (new_et, n_tl) = fresh_tvar tlist in
    let nt = List.find (fun (v,en) -> en.sv_info_kind = new_et) n_tl in
    let (tmp1,tmp2)=nt in
    let (n_tl1,t1) = gather_type_info_exp_x prog a1 n_tl new_et in (* tvar, Int, Float *)
    let (n_tl2,t2) = gather_type_info_exp_x prog a2 n_tl1 new_et in
    let (n_tlist1,t1) = x_add must_unify_expect t1 et n_tl2 pos in
    let (n_tlist2,t2) = x_add must_unify_expect t2 t1 n_tlist1 pos in
    let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tlist2 in
    (n_tl,t2)
  | IP.TypeCast (ty, a1, pos) ->
    let todo_unk:Globals.typ = x_add must_unify_expect_test et ty tlist pos in
    let (new_et, n_tl) = fresh_tvar tlist in
    let nt = List.find (fun (v,en) -> en.sv_info_kind = new_et) n_tl in
    let (tmp1,tmp2)=nt in
    let (n_tl1,t1) = gather_type_info_exp_x prog a1 n_tl new_et in
    let (n_tlist1,t1) = x_add must_unify_expect t1 et n_tl1 pos in
    let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tl1 in
    (n_tl,t1)
  | IP.BagDiff (a1,a2,pos) ->
    let (el_t, n_tl) = fresh_tvar tlist in
    let new_et = x_add must_unify_expect_test (BagT el_t) et n_tl pos in
    let (n_tlist,t1) = gather_type_info_exp_x prog a1 tlist new_et in
    let (n_tlist,t2) = gather_type_info_exp_x prog a2 n_tlist new_et in
    let (n_tlist,n_typ) = x_add must_unify t1 t2 n_tlist pos in
    (n_tlist,n_typ)
  | IP.BagIntersect (es,pos) | IP.BagUnion (es,pos) ->
    let (el_t,n_tl) = fresh_tvar tlist in
    let new_et = x_add must_unify_expect_test (BagT el_t) et n_tl pos in
    let rec aux es_list type_list =
      match es_list with
      | []->([],type_list)
      | hd::tl ->
        let (_tlist,_typ) = gather_type_info_exp_x prog hd type_list new_et in
        let (es_type_list,new_type_list) = aux tl _tlist in
        (_typ::es_type_list, new_type_list)
    in
    let (es_type_list,new_tl) = aux es n_tl in
    List.fold_left (fun (tl,e) a -> x_add must_unify a e tl pos) (new_tl,new_et) es_type_list
  | IP.Bag (es,pos) ->
    let (el_t,n_tl) = fresh_tvar tlist in
    let (n_tlist,t) = List.fold_left (fun (type_list,et) a ->
        gather_type_info_exp_x prog a type_list et) (n_tl,el_t) es in
    (n_tlist,BagT t)
  | IP.Func (id, es, pos) ->
    let t = I.int_type in
    let (n_tlist,n_typ)= x_add must_unify_expect t et tlist pos in
    (n_tlist,n_typ)
  | IP.Template tp -> begin try
        let pos = tp.IP.templ_pos in
        let tid = tp.IP.templ_id in
        let tdef = I.look_up_templ_def_raw prog.I.prog_templ_decls tid in
        let ret_typ = tdef.I.templ_ret_typ in
        let param_types = List.map (fun (t, n) -> trans_type prog t pos) tdef.I.templ_typed_params in
        let func_typ = mkFuncT (List.map (fun (t, _) -> t) tdef.I.templ_typed_params) ret_typ in
        let (n_tl, n_typ) = x_add must_unify_expect ret_typ et tlist pos in
        let (n_tl, n_typ) = x_add gather_type_info_var tid n_tl (* ret_typ *) func_typ pos in
        let exp_et_list = List.combine tp.IP.templ_args param_types in
        let n_tlist = List.fold_left (fun tl (arg, et) ->
            fst (x_add gather_type_info_exp prog arg tl et)) n_tl exp_et_list in
        let n_tlist = match tdef.I.templ_body with
          | None -> n_tlist
          | Some b -> fst (x_add gather_type_info_exp prog b n_tlist ret_typ) in
        (n_tlist, ret_typ)
      with
      | Not_found -> failwith ("gather_type_info_exp: template " ^ tp.IP.templ_id ^ " cannot be found")
      | _ -> failwith ("type error: template " ^ tp.IP.templ_id)
    end
  | IP.ArrayAt ((a,p),idx,pos) ->
    let dim = List.length idx in
    let new_et = Array (et, dim) in
    let () = y_ninfo_hp (add_str "new_et" string_of_typ) new_et in
    let (n_tl,lt) = x_add gather_type_info_var a tlist new_et pos in
    let rec aux id_list type_list expected =
      match id_list with
      | [] -> type_list
      | hd::tl ->
        let (n_tl,n_typ) = x_add gather_type_info_exp prog hd type_list expected in (* forces the array indexes to be Int *)
        aux tl n_tl expected
    in
    (match lt with
     | Array (r,_)     ->  let n_tlist = aux idx n_tl Int in (n_tlist, r)
     | Mapping (t1,t2) ->  let tl  = aux idx tlist t1 in (tl, t2)
     | _ ->  failwith ("gather_type_info_exp: expecting type Array of dimension " ^ (string_of_int dim) ^ " but given " ^ (string_of_typ lt)))
  | IP.ListTail (a,pos)  | IP.ListReverse (a,pos) ->
    let (fv,n_tl) = fresh_tvar tlist in
    let lt = List fv in
    let (n_tl,new_et) = x_add must_unify lt et n_tl pos in
    let (n_tlist,lt) = gather_type_info_exp_x prog a n_tl new_et in
    (n_tlist,lt)
  | IP.ListAppend (es,pos) ->
    let (fv,n_tl) = fresh_tvar tlist in
    let lt = List fv in
    let (n_tl,new_et) = x_add must_unify lt et n_tl pos in
    let (n_tlist,n_type) = List.fold_left (fun (type_list,et) l ->
        gather_type_info_exp_x prog l type_list et) (n_tl,new_et) es  in
    (n_tlist,n_type)
  | IP.ListHead (a, pos) ->
    let (fv,n_tl) = fresh_tvar tlist in
    let new_et = List fv in
    let (n_tl,lt) = gather_type_info_exp_x prog a n_tl new_et in
    let (n_tlist,rs) = x_add must_unify lt (List et) n_tl pos in
    (match rs with
     | List r -> (n_tlist, r)
     | _ ->  failwith ("gather_type_info_exp: expecting List type but obtained "^(string_of_typ lt)))
  | IP.ListCons (e,es,pos) ->
    let (fv,n_tl) = fresh_tvar tlist in
    let (n_tl,e1) = gather_type_info_exp_x prog e n_tl fv in
    let lt = List e1 in
    let (n_tl,new_et) = x_add must_unify lt et n_tl pos in
    let (n_tlist,lt) = gather_type_info_exp_x prog es n_tl new_et in
    (n_tlist,lt)
  | IP.List (es,pos) ->
    let (fv,n_tl) = fresh_tvar tlist in
    let (n_tl,r) = List.fold_left (fun (type_list,et) l ->
        gather_type_info_exp_x prog l type_list et) (n_tl,fv) es  in
    let lt = List r in
    let (n_tlist,r) = x_add must_unify lt et n_tl pos in
    (n_tlist,r)
  | IP.ListLength (a, pos) ->
    let (fv,n_tl) = fresh_tvar tlist in
    let new_et = List fv in
    let (n_tl,r) = x_add must_unify Int et n_tl pos in
    let (n_tlist,_) = gather_type_info_exp_x prog a n_tl new_et in
    (n_tlist,r)
  | IP.BExpr f1 -> (x_add gather_type_info_pure prog f1 tlist, Bool)

and gather_type_info_pure_x prog (p0 : IP.formula) (tlist : spec_var_type_list) : spec_var_type_list =
  match p0 with
  | IP.BForm (b,_) -> x_add gather_type_info_b_formula prog b tlist
  | IP.And (p1, p2, pos) | IP.Or (p1, p2, _, pos) ->
    let n_tl = x_add gather_type_info_pure prog p1 tlist in
    let n_tl = x_add gather_type_info_pure prog p2 n_tl in
    n_tl
  | IP.AndList b ->
    let n_tlist = List.fold_left (fun tl (_,c) -> x_add gather_type_info_pure prog c tl) tlist b in
    n_tlist
  | IP.Not (p1, _, pos) ->
    let n_tl = gather_type_info_pure_x prog p1 tlist in
    n_tl
  | IP.Forall ((qv, qp), qf, _,pos) | IP.Exists ((qv, qp), qf, _,pos) ->
    if (List.exists (fun (v,en)-> v=qv) tlist) then
      if !check_shallow_var
      then
        Err.report_error
          {
            Err.error_loc = pos;
            Err.error_text = qv ^ " shadows outer name";
          }
      else gather_type_info_pure_x prog qf tlist
    else
      begin
        let (new_et,n_tl) = fresh_tvar tlist in
        let vk = fresh_proc_var_kind n_tl new_et in
        let n_tlist = x_add gather_type_info_pure prog qf ((qv,vk)::n_tl) in
        n_tlist
      end

and gather_type_info_pure prog (p0 : IP.formula) (tlist : spec_var_type_list) : spec_var_type_list =
  (* Debug.no_eff_2 "gather_type_info_pure" [false;true]  (Iprinter.string_of_pure_formula) string_of_tlist string_of_tlist *)
  (gather_type_info_pure_x prog) p0 tlist

and gather_type_info_p_formula prog pf tlist =  match pf with
  | IP.Frm _ -> tlist
  | IP.BConst _ -> tlist
  | IP.BVar ((bv, bp), pos) ->
    let (n_tlist,n_type) = x_add gather_type_info_var bv tlist (C.bool_type) pos in
    n_tlist
  | IP.SubAnn(a1,a2,pos) ->
    let (n_tl,n_ty) = x_add gather_type_info_exp prog a1 tlist (Cpure.ann_type) in
    let (n_tl,n_ty) = x_add gather_type_info_exp prog a2 n_tl (Cpure.ann_type) in
    n_tl
  | IP.LexVar(t_ann, ls1, ls2, pos) ->
    let n_tl = gather_type_info_term_ann prog t_ann tlist in
    let n_tl = List.fold_left (fun tl e -> fst(x_add gather_type_info_exp prog e tl (Int))) n_tl ls1 in
    let n_tl = List.fold_left (fun tl e -> fst(x_add gather_type_info_exp prog e tl (Int))) n_tl ls2 in
    n_tl
  | IP.ImmRel(r, cond, pos) ->  gather_type_info_p_formula prog r tlist
  | IP.Lt (a1, a2, pos) | IP.Lte (a1, a2, pos) | IP.Gt (a1, a2, pos) | IP.Gte (a1, a2, pos) ->
    let unify_ptr_cmp t1 t2 n_tl pos =
      if !Globals.ptr_arith_flag (* Globals.infer_const_obj # is_ana_ni *) then
        if is_node_typ t1 then
          let (n_tlist2,_) = x_add must_unify_expect t2 t1 (* Int *) n_tl pos in
          (true,n_tlist2)
        else if is_node_typ t2 then
          let (n_tlist2,_) = x_add must_unify_expect t1 t2 (* Int *) n_tl pos in
          (true,n_tlist2)
        else (false,n_tl)
      else (false,n_tl)
    in
    let (new_et1,n_tl) = fresh_tvar tlist in
    let (new_et2,n_tl) = fresh_tvar n_tl in
    let (n_tl,t1) = x_add gather_type_info_exp prog a1 n_tl new_et1 in (* tvar, Int, Float *)
    let (n_tl,t2) = x_add gather_type_info_exp prog a2 n_tl new_et2 in
    let (flag,n_tl) = unify_ptr_cmp t1 t2 n_tl pos in
    if flag then n_tl
    else
      let (n_tl,t1) = x_add must_unify_expect t1 NUM n_tl pos in
      let (n_tl,t2) = x_add must_unify_expect t2 NUM n_tl pos in
      let (n_tl,_) = x_add must_unify t1 t2 n_tl pos  in (* UNK, Int, Float, TVar *)
      n_tl
  | IP.EqMin (a1, a2, a3, pos) | IP.EqMax (a1, a2, a3, pos) ->
    let (new_et,n_tl) = fresh_tvar tlist in
    let (n_tl,t1) = x_add gather_type_info_exp prog a1 n_tl new_et in (* tvar, Int, Float *)
    let (n_tl,t2) = x_add gather_type_info_exp prog a2 n_tl new_et in
    let (n_tl,t3) = x_add gather_type_info_exp prog a3 n_tl new_et in (* tvar, Int, Float *)
    (* let (n_tl,t1) = x_add must_unify_expect t1 NUM n_tl pos in *)
    (* let (n_tl,t2) = x_add must_unify_expect t2 NUM n_tl pos in *)
    (* let (n_tl,t3) = x_add must_unify_expect t3 NUM n_tl pos in *)
    let unif_t = if (t1 == AnnT || t2 == AnnT || t3 == AnnT) then AnnT else NUM in
    let (n_tl,t1) = x_add must_unify_expect t1 unif_t n_tl pos in
    let (n_tl,t2) = x_add must_unify_expect t2 unif_t n_tl pos in
    let (n_tl,t3) = x_add must_unify_expect t3 unif_t n_tl pos in
    let (n_tl,t) = x_add must_unify t1 t2 n_tl pos  in (* UNK, Int, Float, TVar *)
    let (n_tl,t) = x_add must_unify t t3 n_tl pos  in (* UNK, Int, Float, TVar *)
    n_tl
  | IP.BagIn ((v, p), e, pos) | IP.BagNotIn ((v, p), e, pos) ->  (* v in e *)
    let (new_et,n_tl) = fresh_tvar tlist in
    let (n_tl,t1) = x_add gather_type_info_exp prog e n_tl (BagT new_et) in
    let (n_tl,t2) = x_add gather_type_info_var v n_tl new_et pos in
    let (n_tl,_)= x_add must_unify t1 (BagT t2) n_tl pos in
    n_tl
  | IP.BagSub (e1, e2, pos) ->
    let (new_et,n_tl) = fresh_tvar tlist in
    let (n_tl,t1) = x_add gather_type_info_exp prog e1 n_tl (BagT new_et) in
    let (n_tl,t2) = x_add gather_type_info_exp prog e2 n_tl (BagT new_et) in
    let (n_tl,_) = x_add must_unify t1 t2 n_tl pos in
    n_tl
  | IP.Eq (a1, a2, pos) | IP.Neq (a1, a2, pos) -> (*Need consider*) (
      (* allow comparision btw 2 pointers having different types *)
      let (new_et1,n_tl) = fresh_tvar tlist in
      let (n_tl,t1) = x_add gather_type_info_exp prog a1 n_tl new_et1 in (* tvar, Int, Float *)
      let (new_et2,n_tl) = fresh_tvar n_tl in
      let (n_tl,t2) = x_add gather_type_info_exp prog a2 n_tl new_et2 in
      let () = y_tinfo_hp (add_str "Eq:t1" string_of_typ) t1 in
      let () = y_tinfo_hp (add_str "Eq:t2" string_of_typ) t2 in
      let ntl = match t1, t2 with
        (* | Named _, Named _ -> n_tl *)
        | _ ->
          let (n_tl,_) =x_add must_unify t1 t2 n_tl pos  in (* UNK, Int, Float, TVar *)
          n_tl in
      let () = y_tinfo_hp (add_str "Eq:ntl" string_of_tlist) ntl in
      ntl
    )
  | IP.BagMax ((v1, p1), (v2, p2), pos)
  | IP.BagMin ((v1, p1), (v2, p2), pos) -> (* V1=BagMin(V2) *)
    let (et,n_tl) = fresh_tvar tlist in
    let (n_tl,t1) = x_add gather_type_info_var v1 n_tl et pos in
    let (n_tl,t) = x_add must_unify t1 NUM n_tl pos  in
    let (n_tl,_) = x_add gather_type_info_var v2 n_tl (BagT t) pos in
    n_tl
  (* | IP.VarPerm _ -> tlist (*TO CHECK: no type info*) *)
  | IP.ListIn (e1, e2, pos) | IP.ListNotIn (e1, e2, pos)  | IP.ListAllN (e1, e2, pos) ->
    let (new_et,n_tl) = fresh_tvar tlist in
    let (n_tl,t1) = x_add gather_type_info_exp prog e2 n_tl (List new_et) in
    let (n_tl,t2) = x_add gather_type_info_exp prog e1 n_tl new_et in
    let (n_tl,_) = x_add must_unify t1 (List t2) n_tl pos in
    n_tl
  | IP.ListPerm (e1, e2, pos) ->
    let (el_t,n_tl) = fresh_tvar tlist in
    let new_et = List el_t in
    let (n_tl,t1) = gather_type_info_exp_x prog e1 n_tl new_et in
    let (n_tl,t2) = gather_type_info_exp_x prog e2 n_tl new_et in
    let (n_tl,_) = x_add must_unify t1 t2 n_tl pos in
    n_tl
  | IP.TVar (var, typ, pos) ->
    let (et,n_tl) = fresh_tvar tlist in
    let (n_tl,t1) = x_add gather_type_info_exp prog var n_tl et in
    let (n_tl,t) = x_add must_unify t1 typ n_tl pos  in
    n_tl
  | IP.RelForm (r, args, pos) ->
    (
      let helper rdef =
        let args_ctypes = List.map (fun (t,n) -> trans_type prog t pos) rdef.I.rel_typed_vars in
        let args_exp_types = List.map (fun t -> (t)) args_ctypes in
        (* let () = y_binfo_hp (add_str "args_exp_types" (pr_list string_of_typ))  args_exp_types in *)
        let poly_lst, tlist = introduce_fresh_poly_for_each_unique_poly tlist args_exp_types in
        let args_exp_types = subst_all_poly_w_poly poly_lst args_exp_types in
        (* let () = y_binfo_hp (add_str "args_exp_types" (pr_list string_of_typ))  args_exp_types in
         * let () = y_binfo_hp (add_str "tlist" (string_of_tlist)) tlist in *)
        let (n_tl,n_typ) = x_add gather_type_info_var r tlist (RelT []) pos in (*Need to consider about pos*)
        let tmp_list = List.combine args args_exp_types in
        let n_tlist = List.fold_left (fun tl (arg,et) ->
            fst(x_add gather_type_info_exp prog arg tl et )) n_tl tmp_list in
        n_tlist
      in
      try
        let rdef = I.look_up_rel_def_raw prog.I.prog_rel_decls r in
        helper rdef
      with
      | Not_found ->    failwith ("gather_type_info_b_formula: relation "^r^" cannot be found")
      | Invalid_argument _ -> failwith ("number of arguments for relation " ^ r ^ " does not match")
      | e -> raise e;
        (* WN : error due to mismatched types here *)
        (* print_endline_quiet ("gather_type_info_b_formula: relation " ^ r);tlist        *)
    )
  | IP.XPure({IP.xpure_view_node = vn ;
              IP.xpure_view_name = r;
              IP.xpure_view_arguments = args;
              IP.xpure_view_pos = pos}) -> (
      try
        let hpdef = I.look_up_hp_def_raw prog.I.prog_hp_decls r in
        if (List.length args) == (List.length hpdef.I.hp_typed_inst_vars) then
          let args_ctypes = List.map (fun (t,n, i) -> trans_type prog t pos) hpdef.I.hp_typed_inst_vars in
          let args_exp_types = List.map (fun t -> (t)) args_ctypes in
          let (n_tl,_) = x_add gather_type_info_var r tlist HpT pos in (*Need to consider about pos*)
          let tmp_list = List.combine args args_exp_types in
          let n_tlist = List.fold_left (fun tl (arg,et) -> fst(x_add gather_type_info_var arg tl et pos )) n_tl tmp_list in (*Need to consider about pos*)
          n_tlist
        else
          Err.report_error{ Err.error_loc = pos; Err.error_text = ("number of arguments for heap relation "^r^" does not match"); }
      with
      | Not_found ->    failwith ("gather_type_info_b_formula: relation "^r^" cannot be found")
      | _ -> print_endline_quiet ("gather_type_info_b_formula: relation " ^ r);tlist
    )

and gather_type_info_term_ann prog tann tlist =
  match tann with
  | IP.TermU tid
  | IP.TermR tid ->
    begin
      try
        let pos = tid.IP.tu_pos in
        let sid = tid.IP.tu_sid in
        let utdef = I.look_up_ut_def_raw prog.I.prog_ut_decls sid in
        let (n_tl, n_typ) = x_add gather_type_info_var sid tlist (UtT (utdef.I.ut_is_pre)) pos in
        let param_types = List.map (fun (t, _) -> trans_type prog t pos) utdef.I.ut_typed_params in
        let exp_et_list = List.combine tid.IP.tu_args param_types in
        let n_tl = List.fold_left (fun tl (arg, et) ->
            fst (x_add gather_type_info_exp prog arg tl et)) n_tl exp_et_list in
        n_tl
      with
      | Not_found -> failwith ("gather_type_info_term_ann: " ^ tid.IP.tu_sid ^ " cannot be found")
      | Invalid_argument _ -> failwith ("number of arguments for unknown temporal " ^ tid.IP.tu_sid ^ " does not match")
      | _ -> failwith ("type error: unknown temporal " ^ tid.IP.tu_sid)
    end
  | _ -> tlist

and gather_type_info_b_formula prog b0 tlist =
  Debug.no_eff_2 "gather_type_info_b_formula" [false;true]
    Iprinter.string_of_b_formula string_of_tlist string_of_tlist
    (fun _ _ -> gather_type_info_b_formula_x prog b0 tlist) b0 tlist

(************************************************************************)
(* substitute the poly types with the actual type if it exists in tlist *)
(*    eg: [T1:1:int, TVar__2:2:`T1] ==> [T1:1:int, TVar__2:2:int]       *)
(************************************************************************)
and poly_wrapper_type_gather tlist =
  let substituted_tlist = List.map (fun (id,svi) ->
      if Globals.contains_poly svi.sv_info_kind then
        try
          let poly_typ_lst = Globals.get_poly_ids svi.sv_info_kind in
          (* associate each poly type in svi with its corresponding type from tlist *)
          (* eg: [T1:1:int, TVar__2:2:`T1] ==> [(T1,int)] *)
          let poly_typ_lst = List.map (fun a ->
              try let sv = List.assoc a tlist in Some (a,sv.sv_info_kind)
              with Not_found -> None
            ) poly_typ_lst in
          (* remove Nones *)
          let subs = List.fold_left (fun a ty -> a@(opt_to_list ty)) [] poly_typ_lst in
          let tfrom, tto = List.split subs in
          (* apply the substitution in the actual svi type *)
          let new_sv_info_kind = Globals.subs_one_poly_typ tfrom tto svi.sv_info_kind in
          (id,{svi with sv_info_kind = new_sv_info_kind;})
        with Not_found -> (id,svi)
      else (id,svi)
    ) tlist in
  substituted_tlist

and gather_type_info_b_formula_x prog b0 tlist =
  let (pf,_) = b0 in
  poly_wrapper_type_gather
    (gather_type_info_p_formula prog pf tlist)
(* match pf with *)
(*   | IP.Frm _ -> tlist *)
(* | IP.BConst _ -> tlist *)
(* | IP.BVar ((bv, bp), pos) -> *)
(*     let (n_tlist,n_type) = gather_type_info_var bv tlist (C.bool_type) pos in *)
(*     n_tlist *)
(* | IP.SubAnn(a1,a2,pos) -> *)
(*     let (n_tl,n_ty) = gather_type_info_exp a1 tlist (Cpure.ann_type) in *)
(*     let (n_tl,n_ty) = gather_type_info_exp a2 n_tl (Cpure.ann_type) in *)
(*     n_tl *)
(* | IP.LexVar(t_ann, ls1, ls2, pos) -> *)
(*     let n_tl = List.fold_left (fun tl e-> fst(gather_type_info_exp e tl (Int))) tlist ls1  in *)
(*     let n_tl = List.fold_left (fun tl e-> fst(gather_type_info_exp e tl (Int))) n_tl ls2 in *)
(*     n_tl *)
(* | IP.Lt (a1, a2, pos) | IP.Lte (a1, a2, pos) | IP.Gt (a1, a2, pos) | IP.Gte (a1, a2, pos) -> *)
(*     let (new_et,n_tl) = fresh_tvar tlist in *)
(*     let (n_tl,t1) = gather_type_info_exp a1 n_tl new_et in (\* tvar, Int, Float *\) *)
(*     let (n_tl,t2) = gather_type_info_exp a2 n_tl new_et in *)
(*     let (n_tl,t1) = x_add must_unify_expect t1 NUM n_tl pos in *)
(*     let (n_tl,t2) = x_add must_unify_expect t2 NUM n_tl pos in *)
(*     let (n_tl,_) = x_add must_unify t1 t2 n_tl pos  in (\* UNK, Int, Float, TVar *\)  *)
(*     n_tl *)
(* | IP.EqMin (a1, a2, a3, pos) | IP.EqMax (a1, a2, a3, pos) -> *)
(*     let (new_et,n_tl) = fresh_tvar tlist in *)
(*     let (n_tl,t1) = gather_type_info_exp a1 n_tl new_et in (\* tvar, Int, Float *\) *)
(*     let (n_tl,t2) = gather_type_info_exp a2 n_tl new_et in *)
(*     let (n_tl,t3) = gather_type_info_exp a3 n_tl new_et in (\* tvar, Int, Float *\) *)
(*     let (n_tl,t1) = x_add must_unify_expect t1 NUM n_tl pos in *)
(*     let (n_tl,t2) = x_add must_unify_expect t2 NUM n_tl pos in *)
(*     let (n_tl,t3) = x_add must_unify_expect t3 NUM n_tl pos in *)
(*     let (n_tl,t) = x_add must_unify t1 t2 n_tl pos  in (\* UNK, Int, Float, TVar *\)  *)
(*     let (n_tl,t) = x_add must_unify t t3 n_tl pos  in (\* UNK, Int, Float, TVar *\)  *)
(*     n_tl *)
(* | IP.BagIn ((v, p), e, pos) | IP.BagNotIn ((v, p), e, pos) ->  (\* v in e *\) *)
(*     let (new_et,n_tl) = fresh_tvar tlist in *)
(*     let (n_tl,t1) = gather_type_info_exp e n_tl (BagT new_et) in *)
(*     let (n_tl,t2) = gather_type_info_var v n_tl new_et pos in *)
(*     let (n_tl,_)= x_add must_unify t1 (BagT t2) n_tl pos in *)
(*     n_tl *)
(* | IP.BagSub (e1, e2, pos) -> *)
(*     let (new_et,n_tl) = fresh_tvar tlist in *)
(*     let (n_tl,t1) = gather_type_info_exp e1 n_tl (BagT new_et) in *)
(*     let (n_tl,t2) = gather_type_info_exp e2 n_tl (BagT new_et) in *)
(*     let (n_tl,_) = must_unify t1 t2 n_tl pos in *)
(*     n_tl *)
(* | IP.Eq (a1, a2, pos) | IP.Neq (a1, a2, pos) -> (\*Need consider*\) ( *)
(*     (\* allow comparision btw 2 pointers having different types *\) *)
(*     let (new_et1,n_tl) = fresh_tvar tlist in *)
(*     let (n_tl,t1) = gather_type_info_exp a1 n_tl new_et1 in (\* tvar, Int, Float *\) *)
(*     let (new_et2,n_tl) = fresh_tvar n_tl in *)
(*     let (n_tl,t2) = gather_type_info_exp a2 n_tl new_et2 in *)
(*     match t1, t2 with *)
(*     | Named _, Named _ -> n_tl *)
(*     | _ -> *)
(*         let (n_tl,_) = x_add must_unify t1 t2 n_tl pos  in (\* UNK, Int, Float, TVar *\) *)
(*         n_tl *)
(*   ) *)
(* | IP.BagMax ((v1, p1), (v2, p2), pos)  *)
(* | IP.BagMin ((v1, p1), (v2, p2), pos) -> (\* V1=BagMin(V2) *\) *)
(*     let (et,n_tl) = fresh_tvar tlist in *)
(*     let (n_tl,t1) = gather_type_info_var v1 n_tl et pos in *)
(*     let (n_tl,t) = x_add must_unify t1 NUM n_tl pos  in *)
(*     let (n_tl,_) = gather_type_info_var v2 n_tl (BagT t) pos in *)
(*     n_tl *)
(* | IP.VarPerm _ -> tlist (\*TO CHECK: no type info*\) *)
(* | IP.ListIn (e1, e2, pos) | IP.ListNotIn (e1, e2, pos)  | IP.ListAllN (e1, e2, pos) -> *)
(*     let (new_et,n_tl) = fresh_tvar tlist in *)
(*     let (n_tl,t1) = gather_type_info_exp e2 n_tl (List new_et) in *)
(*     let (n_tl,t2) = gather_type_info_exp e1 n_tl new_et in *)
(*     let (n_tl,_) = x_add must_unify t1 (List t2) n_tl pos in *)
(*     n_tl *)
(* | IP.ListPerm (e1, e2, pos) -> *)
(*     let (el_t,n_tl) = fresh_tvar tlist in *)
(*     let new_et = List el_t in *)
(*     let (n_tl,t1) = gather_type_info_exp_x e1 n_tl new_et in  *)
(*     let (n_tl,t2) = gather_type_info_exp_x e2 n_tl new_et in *)
(*     let (n_tl,_) = x_add must_unify t1 t2 n_tl pos in *)
(*     n_tl *)
(* | IP.RelForm (r, args, pos) ->  *)
(*     (try *)
(*       let rdef = I.look_up_rel_def_raw prog.I.prog_rel_decls r in *)
(*       let args_ctypes = List.map (fun (t,n) -> trans_type prog t pos) rdef.I.rel_typed_vars in *)
(*       let args_exp_types = List.map (fun t -> (t)) args_ctypes in *)
(*       let (n_tl,n_typ) = gather_type_info_var r tlist (RelT []) pos in (\*Need to consider about pos*\) *)
(*       let tmp_list = List.combine args args_exp_types in *)
(*       let n_tlist = List.fold_left (fun tl (arg,et) -> fst(gather_type_info_exp arg tl et )) n_tl tmp_list in *)
(*       n_tlist              *)
(*     with *)
(*       | Not_found ->    failwith ("gather_type_info_b_formula: relation "^r^" cannot be found") *)
(*       | _ -> print_endline ("gather_type_info_b_formula: relation " ^ r);tlist        *)
(*     ) *)
(* | IP.XPure({IP.xpure_view_node = vn ; *)
(*             IP.xpure_view_name = r; *)
(*             IP.xpure_view_arguments = args; *)
(*             IP.xpure_view_pos = pos}) -> ( *)
(*     try *)
(*       let hpdef = I.look_up_hp_def_raw prog.I.prog_hp_decls r in *)
(*       if (List.length args) == (List.length hpdef.I.hp_typed_inst_vars) then *)
(*         let args_ctypes = List.map (fun (t,n, i) -> trans_type prog t pos) hpdef.I.hp_typed_inst_vars in *)
(*         let args_exp_types = List.map (fun t -> (t)) args_ctypes in *)
(*         let (n_tl,_) = gather_type_info_var r tlist HpT pos in (\*Need to consider about pos*\) *)
(*         let tmp_list = List.combine args args_exp_types in *)
(*         let n_tlist = List.fold_left (fun tl (arg,et) -> fst(gather_type_info_var arg tl et pos )) n_tl tmp_list in (\*Need to consider about pos*\) *)
(*         n_tlist *)
(*       else *)
(*         Err.report_error{ Err.error_loc = pos; Err.error_text = ("number of arguments for heap relation "^r^" does not match"); } *)
(*     with *)
(*       | Not_found ->    failwith ("gather_type_info_b_formula: relation "^r^" cannot be found") *)
(*       | _ -> print_endline ("gather_type_info_b_formula: relation " ^ r);tlist *)
(*   ) *)

and guess_type_of_exp_arith a0 tlist =
  match a0 with
  | IP.Null _ ->
    let (new_et,n_tl) = fresh_tvar tlist in
    (n_tl, new_et)
  (* (tlist,UNK) *)
  | IP.Var ((sv, sp), pos) ->
    begin
      try
        let info = snd(List.find (fun (v,en) -> v=sv) tlist) in
        (tlist,info.sv_info_kind)
      with Not_found -> (tlist,UNK)
    end
  | IP.Add (e1, e2, pos) | IP.Subtract (e1, e2, pos) | IP.Mult (e1, e2, pos)
  | IP.Max (e1, e2, pos) | IP.Min (e1, e2, pos) | IP.Div (e1, e2, pos) ->
    let (n_tl,t1) = guess_type_of_exp_arith e1 tlist in
    let (n_tl,t2) = guess_type_of_exp_arith e2 n_tl in
    begin
      match t1, t2 with
      | _, UNK -> (n_tl,t1)
      | UNK, _ -> (n_tl,t2)
      | Float, Float -> (n_tl,t1)
      | Int, Int -> (n_tl,t1)
      | Int, Float | Float, Int  ->
        Err.report_error
          {
            Err.error_loc = pos;
            Err.error_text = "int<>float: type-mismatch in expression: " ^ (Iprinter.string_of_formula_exp a0);
          }
      | _ -> (n_tl,UNK)
    end
  (* | IP.Div _ -> Known (Float) *)
  | IP.IConst _ -> (tlist,Int)
  | IP.FConst _ -> (tlist,Float)
  | IP.Ann_Exp (_,t, _) -> (tlist,t)
  | _ -> (tlist,UNK)

and gather_type_info_pointer (e0 : IP.exp) (k : spec_var_kind) (tlist:spec_var_type_list) : (spec_var_type_list*typ) =
  match e0 with
  | IP.Null _ ->
    let (new_et,n_tl) = fresh_tvar tlist in
    (n_tl, new_et)
  | IP.Var ((sv, sp), pos) -> gather_type_info_var sv tlist k pos
  | _ -> Err.report_error { Err.error_loc = IP.pos_of_exp e0;
                            Err.error_text = "arithmetic is not allowed in pointer term"; }

and gather_type_info_formula prog f0 tlist filter_res:spec_var_type_list =
  Debug.no_eff_3 "gather_type_info_formula" [false;true]
    (Iprinter.string_of_formula) string_of_tlist
    string_of_bool string_of_tlist
    (fun _ _ _ -> gather_type_info_formula_x prog f0 tlist filter_res)
    f0 tlist filter_res

and gather_type_info_one_formula prog (f : IF.one_formula) tlist filter_res =
  let n_tl = (match f.IF.formula_thread with
      | None -> tlist
      | Some (v,pr) -> let (n_tl,_)= x_add gather_type_info_var v tlist thread_typ f.IF.formula_pos in n_tl
    ) in
  let n_tl = x_add gather_type_info_heap prog f.IF.formula_heap n_tl in
  let n_tl = x_add gather_type_info_pure prog f.IF.formula_pure n_tl in
  n_tl

and gather_type_info_formula_x prog f0 tlist filter_res =
  let helper pure heap tl= (
    let n_tl = x_add gather_type_info_heap prog heap tl in
    let n_tl = x_add gather_type_info_pure prog pure n_tl in
    n_tl
  ) in
  match f0 with
  | IF.Or b->
    let n_tl = gather_type_info_formula_x prog b.IF.formula_or_f1 tlist filter_res in
    let n_tl = gather_type_info_formula_x prog b.IF.formula_or_f2 n_tl filter_res in
    n_tl
  | IF.Exists b ->
    let (n_tl,rl) = res_retrieve tlist filter_res b.IF.formula_exists_flow in
    let n_tl = List.fold_left (fun tl f -> x_add gather_type_info_one_formula prog f tl filter_res) n_tl b.IF.formula_exists_and in
    let n_tl = helper b.IF.formula_exists_pure b.IF.formula_exists_heap n_tl in
    let n_tl = x_add res_replace n_tl rl filter_res b.IF.formula_exists_flow in
    n_tl
  | IF.Base b ->
    let (n_tl,rl) = res_retrieve tlist filter_res b.IF.formula_base_flow in
    let todo_unk = List.fold_left (fun tl f -> x_add gather_type_info_one_formula prog f tl filter_res) n_tl b.IF.formula_base_and in
    let n_tl = helper b.IF.formula_base_pure b.IF.formula_base_heap n_tl in
    let n_tl = x_add res_replace n_tl rl filter_res b.IF.formula_base_flow  in
    n_tl

and gather_type_info_struc_f prog (f0:IF.struc_formula) tlist =
  Debug.no_eff_2 "gather_type_info_struc_f" [false;true]
    Iprinter.string_of_struc_formula string_of_tlist string_of_tlist
  (fun _ _ -> gather_type_info_struc_f_x prog f0 tlist) f0 tlist

and gather_type_info_struc_f_x prog (f0:IF.struc_formula) tlist =
  let rec inner_collector (f0:IF.struc_formula) tl = (
    match f0 with
    | IF.EAssume b ->
      let n_tl = x_add gather_type_info_formula prog b.IF.formula_assume_simpl tl true in
      x_add gather_type_info_struc_f prog b.IF.formula_assume_struc n_tl
    | IF.ECase b ->
      List.fold_left (
        fun tl (c1,c2)->
          let n_tl = x_add gather_type_info_pure prog c1 tl in
          inner_collector c2 n_tl
      ) tl b.IF.formula_case_branches
    | IF.EBase b ->
      let n_tl  = x_add gather_type_info_formula prog b.IF.formula_struc_base tl false in
      let n_tl = (
        match b.IF.formula_struc_continuation with
        | None -> n_tl
        | Some l -> let n_tl = inner_collector l n_tl in n_tl
      ) in
      n_tl
    | IF.EInfer b -> let n_tl = inner_collector b.IF.formula_inf_continuation tl in n_tl
    | IF.EList b -> let n_tl = List.fold_left(fun tl (_,c)-> inner_collector c tl) tl b in n_tl
  ) in
  begin
    let n_tl = inner_collector f0 tlist in
    n_tl
    (* TODO WN : to remove check_shallow_var *)
    (* TODO WN : to avoid double parsing *)
    (* re-collect type info, don't check for shadowing outer var this time *)
    (* check_shallow_var := false; *)
    (* inner_collector f0; *)
    (* check_shallow_var := true *)
  end

(* |ls2| = |ls1| ==> ls1, ls2
   ls2 = ls2a::_ & |ls2a|=|ls1| -> ls1,ls2a
*)
and add_last_diff ls1 ls2 res=
  match ls1,ls2 with
  | ([], []) ->  res
  | ([], [((_,id),l,_,_)]) -> res@[(Ipure.Var ((id,Unprimed),l))]
  | (a::rest1,_::rest2) -> add_last_diff rest1 rest2 (res@[a])
  | _ -> raise (Invalid_argument "first is longer than second")

and try_unify_data_type_args prog c v deref ies tlist pos =
  let pr_tl =  string_of_tlist in
  let pr1 = add_str "name,var" (pr_pair pr_id pr_id) in
  let pr2 = add_str "args" (pr_list Iprinter.string_of_formula_exp) in
  Debug.no_3 "try_unify_data_type_args"
    pr1 pr2
    (add_str "type list" pr_tl)
    pr_tl
    (fun _ _ _ -> try_unify_data_type_args_x prog c v deref ies tlist pos) (c,v) ies tlist

and freshed_poly_typ p_typ =
  let i              = fresh_int () in
  let fresh_poly     = poly_name i  in
  let fresh_poly_typ = Poly fresh_poly in
  fresh_poly_typ

and try_unify_data_type_args_x prog c v deref ies tlist pos =
  (* An Hoa : problem detected - have to expand the inline fields as well, fix in look_up_all_fields. *)
  let pr_args = pr_list Iprinter.string_of_formula_exp in
  if (deref = 0) then (
    try (
      let ddef = x_add I.look_up_data_def_raw prog.I.prog_data_decls c in
      (* 1. let poly_types =  collect the poly types from ddef (unique types) *)
      (* let field_names = List.map I.get_field_name ddef.I.data_fields in *)
      (* let fld_typs = List.map I.get_field_typ ddef.I.data_fields in
       * let poly_typ_list = List.filter (fun t -> match t with
       *     | Poly _ -> true
       *     | _ -> false) fld_typs in *)
      (* let () = y_binfo_hp (add_str "types of fields" (pr_list string_of_typ)) poly_typ_list in *)
      (* 2. let fresh_pt   = List.map fresh poly_types  *)
      (* keep the non-poly value because we need to update the ddef which needs all the fields *)
      (* ****************** *)
      (* let () = y_binfo_hp (add_str "poly_typ_list " (pr_list string_of_typ)) poly_typ_list in
       * let fldls_w_freshed_poly_typs, tlist = introduce_fresh_poly_for_each_unique_poly tlist fld_typs in
       * let fldls_w_freshed_poly_typs_rev = List.rev fldls_w_freshed_poly_typs in
       * let ids, fresh_poly_typs  = List.split fldls_w_freshed_poly_typs_rev in *)
      let id_to_poly_typ_list = List.map (fun identity -> Poly identity) ddef.I.data_poly_para in
      let data_para_w_freshed_poly_typs, tlist = introduce_fresh_poly_for_each_unique_poly tlist id_to_poly_typ_list in
      let data_para_w_freshed_poly_typs_rev = List.rev data_para_w_freshed_poly_typs in
      let ids, fresh_poly_typs  = List.split data_para_w_freshed_poly_typs_rev in
      let () = y_tinfo_hp (add_str "fields with freshed poly types inside" (pr_list string_of_typ)) fresh_poly_typs in
      let () = y_tinfo_hp (add_str "ids " (pr_list Cprinter.string_of_ident)) ids in
      (* let fld_typs = subst_all_poly_w_poly fldls_w_freshed_poly_typs fld_typs in *)
      (* ****************** *)
      (* remove the duplicated poly types *)
      (* 3. let ddef       = [fresh_pt/poly_types] ddef -- substitute the fst ele of the field list *)
      let updated_fields = List.map (fun field ->
          let typ  = I.get_type_of_field field in
          let () = y_tinfo_hp (add_str "field typ "  string_of_typ) typ in
          (* update the type *)
          let ntyp = Globals.subs_one_poly_typ ids fresh_poly_typs typ in
          let nfield = I.set_type_of_field field ntyp in
          nfield
        ) ddef.I.data_fields in
      let ddef_tmp = { ddef with I.data_fields = updated_fields; } in
      let ddef = ddef_tmp in
      (* 4. mkNamedTyp c fresh_pt *)
      let () = y_tinfo_hp (add_str "fields with freshed poly types before mkNamedTyp" (pr_list string_of_typ)) fresh_poly_typs in
      (* This ~args should not be the fresh_poly_typs, this one should be corresponding to the poly para *)
      let (n_tl,_) = x_add gather_type_info_var v tlist ((mkNamedTyp ~args:(fresh_poly_typs) c)) pos in
      let fields = x_add_1 I.look_up_all_fields prog ddef in
      try
        (* fields may contain offset field and not-in-used *)
        let () = x_tinfo_hp (add_str "ies(1)" pr_args) ies no_pos in
        (* let ies = add_last_diff ies fields ([]) in *)
        let () = x_tinfo_hp (add_str "ies(2)" pr_args) ies no_pos in
        let f tl arg ((ty,_),_,_,_)=
          (let (n_tl,_) = x_add gather_type_info_exp prog arg tl ty in n_tl)
        in (List.fold_left2 f n_tl ies fields)
      (* normalize to replace the poly types with their instantiation *)
      with | Invalid_argument _ ->
        Err.report_error {
          Err.error_loc = pos;
          Err.error_text = "number of arguments for data " ^ c
                           ^ " does not match"^(pr_list (fun c->c)(List.map Iprinter.string_of_formula_exp ies));
        }
    )
    with Not_found -> raise Not_found
  )
  else (
    (* dereference cases *)
    try (
      let base_ddecl = (
        let dname = (
          match c with
          | "int" | "float" | "void" | "bool" -> c ^ "_star"
          | _ -> c
        ) in
        x_add I.look_up_data_def_raw prog.I.prog_data_decls dname
      ) in
      let holder_name = (
        let deref_str = ref "" in
        for i = 1 to deref do
          deref_str := !deref_str ^ "_star";
        done;
        c ^ !deref_str
      ) in
      let (n_tl,_) = x_add gather_type_info_var v tlist ((mkNamedTyp holder_name)) pos in
      let fields = x_add_1 I.look_up_all_fields prog base_ddecl in
      try
        let f tl arg ((ty,_),_,_,_)=
          (let (n_tl,_) = x_add gather_type_info_exp prog arg tl ty in n_tl)
        in (List.fold_left2 f n_tl ies fields)
      with | Invalid_argument _ ->
        Err.report_error {
          Err.error_loc = pos;
          Err.error_text = "number of arguments for data " ^ c
                           ^ " does not match"^(pr_list (fun c->c)(List.map Iprinter.string_of_formula_exp ies));
        }
    )
    with Not_found -> raise Not_found
  )

(* TODO WN : this is not doing anything *)
and fill_view_param_types (vdef : I.view_decl) =
  if (String.length vdef.I.view_data_name) = 0 then ()
  (* report_warning no_pos ("data names of " ^ vdef.I.view_name ^ " is empty") *)
  else ()

and try_unify_view_type_args prog c vdef self_ptr deref ies hoa tlist pos =
  let pr1 = add_str "is_prim_pred" string_of_bool in
  let pr2 = add_str "name,var" (pr_pair pr_id pr_id) in
  let pr3 = string_of_tlist in
  let pr4 = pr_list Iprinter.string_of_formula_exp in
  Debug.no_4 "try_unify_view_type_args" pr1 pr2 pr3 pr4 pr3
    (fun _ _ _ _ -> try_unify_view_type_args_x prog c vdef self_ptr deref ies hoa tlist pos)
    vdef.I.view_is_prim (c,self_ptr) tlist ies
      (*
        type: I.prog_decl ->
        c: view_name : Globals.ident ->
        I.view_decl ->
        v : var ptr : Globals.ident ->
        int ->
        tlist : arg list : Iprinter.P.exp list ->
        spec_var_type_list -> VarGen.loc -> spec_var_type_list
      *)
(* ident, args, table *)
and try_unify_view_type_args_x prog c vdef self_ptr deref ies hoa tlist pos =
  let id_to_poly_typ_list = (
    match vdef.I.view_poly_vars with
    | [] -> []
    | _  -> List.map (fun identity -> Poly identity) vdef.I.view_poly_vars
  ) in
  let view_pvar_w_freshed_poly_typs, tlist = introduce_fresh_poly_for_each_unique_poly tlist id_to_poly_typ_list in
  let view_pvar_w_freshed_poly_typs_rev = List.rev view_pvar_w_freshed_poly_typs in
  let ids, fresh_poly_typs  = List.split view_pvar_w_freshed_poly_typs_rev in
  let () = y_tinfo_hp (add_str "view --- fields with freshed poly types inside" (pr_list string_of_typ)) fresh_poly_typs in
  let () = y_tinfo_hp (add_str "view --- ids " (pr_list Cprinter.string_of_ident)) ids in
  let () = y_tinfo_hp (add_str "view before --- typed vars " (pr_list (pr_pair string_of_typ pr_id))) vdef.I.view_typed_vars in
  let updated_vars = (
    match (List.length fresh_poly_typs) = (List.length vdef.I.view_typed_vars) with
    | true  ->
        List.map2 (fun var freshp ->
          let ntvar = I.set_type_of_view_var var freshp in
          ntvar
        ) vdef.I.view_typed_vars fresh_poly_typs
    | false -> vdef.I.view_typed_vars
  ) in
  let () = y_tinfo_hp (add_str "view after --- typed vars " (pr_list (pr_pair string_of_typ pr_id))) updated_vars in
  (* let new_data_name = vdef.I.view_data_name ^ ((pr_list string_of_typ) fresh_poly_typs) in *)
  let vdef_tmp = { vdef with I.view_typed_vars = updated_vars; (* I.view_data_name = new_data_name *) } in
  let vdef = vdef_tmp in
  (* let get_all_poly_types vd ls =
   * let poly_types = get_all_poly_types vdef [] in
   * let poly_types_hmap = fresh_poly_tlist poly_types in *)
  (* vdef = replace_poly hmap  vdef *)
  let dname = vdef.I.view_data_name in
  let () = y_tinfo_hp (add_str "dnameeeeeeeeeee" (pr_id)) dname in
  let n_tl, self_ty = (
    match vdef.I.view_type_of_self with
    | Some (Mapping _  as ty) ->
      let () = y_tinfo_hp (add_str "tlist before" (string_of_tlist)) tlist in
      let ntlist,_ = x_add gather_type_info_var self_ptr tlist ty pos in
      let () = y_tinfo_hp (add_str "tlist after" (string_of_tlist)) ntlist in
      ntlist, ty
    | _ ->
      let () = y_tinfo_hp (add_str "self_ptr" pr_id) self_ptr in
      if (String.compare dname "" = 0) then
        let () = y_tinfo_hp (add_str "self_ptr" pr_id) self_ptr in
        tlist, UNK
      else if vdef.I.view_is_prim then
        begin
          match vdef.I.view_type_of_self with
          | None -> let () = y_ninfo_hp (add_str "self_ptr" pr_id) self_ptr in tlist, UNK
          | Some self_typ ->
            let () = y_ninfo_hp (add_str "self_ptr" pr_id) self_ptr in
            let (n_tl,_) = x_add gather_type_info_var self_ptr tlist self_typ pos in
            n_tl, UNK
        end
      else
        let expect_dname = (
          let s = ref "" in
          for i = 1 to deref do
            s := !s ^ "_star";
          done;
          dname ^ !s
        ) in
        let () = y_tinfo_hp (add_str "self_ptr" pr_id) self_ptr in
        let selftyp = get_type_of_self tlist in
        let () = y_tinfo_hp (add_str "self_ptr_typ" string_of_typ) selftyp in
        let typls =
          match selftyp with
          | Named (nam,[]) -> []
          | Named (nm, ls) ->
               let rec helper current acc comls = (
                 match current with
                 | []   -> acc
                 | h::t ->
                   let (_,ele_b) = List.find (fun (a,b) -> a = (string_of_typ h)) comls in
                   helper t (ele_b::acc) comls
               )
               in
               let new_ls = List.rev (helper ls [] view_pvar_w_freshed_poly_typs_rev) in
               new_ls
          | _ -> []
        in
        let (n_tl,_) = x_add gather_type_info_var self_ptr tlist ((mkNamedTyp ~args:typls expect_dname)) pos in
        n_tl, UNK
  ) in
  let () = if (String.length vdef.I.view_data_name) = 0  then fill_view_param_types vdef in
  (* Check type consistency for rho *)
  let ho_flow_kinds_view = List.map (fun (k, _, _) -> k) vdef.I.view_ho_vars in
  let ho_flow_kinds_args = List.map (fun ff -> ff.IF.rflow_kind) hoa in
  let rec ho_helper hov hoa =
    match hov, hoa with
    | [], [] -> ()
    | v::vr, a::ar ->
      if eq_ho_flow_kind v a then ho_helper vr ar
      else report_error pos ("Higher-order flow kinds do not match")
    | _ -> report_error pos ("Number of higher-order arguments for the view "
                             ^ c ^ " does not match")
  in
  let () = ho_helper ho_flow_kinds_view ho_flow_kinds_args in
  (**********************************)
  let vt = vdef.I.view_typed_vars in
  let rec helper exps tvars =
    match (exps, tvars) with
    | ([], []) -> []
    | (e :: rest1, t :: rest2) ->
      let tmp = helper rest1 rest2
      in
      (match e with
       | IP.Var ((v, p), pos) ->
         let ty = fst t in (ty, v) :: tmp
       | _ -> tmp)
    | _ ->
      Err.report_error
        {
          Err.error_loc = pos;
          Err.error_text =
            "number of arguments for view " ^
            (c ^ " does not match");
        } in
  let tmp_r = helper ies vt in
  (***********************************************)
  (**********replace poly vars with tvars*********)
  (***********************************************)
  (* let tmp_r =  (self_ty,self_ptr)::tmp_r in
   * let ()    = y_binfo_hp (add_str "tmp_r1 " (pr_list (pr_pair string_of_typ pr_id))) tmp_r in
   * (\* 1. for each unique poly typ introduce a fresh tvar in n_tl *\)
   * let poly_lst,n_tl = introduce_fresh_tvar_for_each_unique_poly n_tl tmp_r in
   * (\* 2. substitute all poly typ with their corresponding tvar (created at 1.) *\)
   * let tmp_r = subst_all_poly_w_tvar poly_lst tmp_r in
   * let ()    = y_binfo_hp (add_str "tmp_r2 " (pr_list (pr_pair string_of_typ pr_id))) tmp_r in *)
    (* let tmp_r = List.tl tmp_r in *)
  (***********************************************)
  (*****(end)replace poly vars with tvars*********)
  (***********************************************)
  let (vt_u,tmp_r) = List.partition (fun (ty,_) -> ty==UNK) tmp_r in
  (* WN : fixed poly type for view parameter *)
  if (Gen.is_empty vt_u || true)
  then
    let n_tl = (List.fold_left (fun tl (t, n) -> fst(x_add gather_type_info_var n tl (t) pos)) n_tl tmp_r) in
    n_tl
  else begin
    (* below seems wrong to unify against previous var names *)
    (try
       let n_tl = (List.fold_left (fun tl (t, n) -> fst(x_add gather_type_info_var n tl (t) pos))n_tl tmp_r) in
       let f tl arg lhs_v =
         (let et = get_var_kind lhs_v tl  in
          let (n_tl,new_t) = x_add gather_type_info_exp prog arg tl et in
          let (n_tl,typ) = set_var_kind lhs_v new_t n_tl in n_tl )
       in (List.fold_left2 f n_tl ies vdef.I.view_vars)
     with | Invalid_argument _ -> report_error pos ("number of arguments for view " ^ c ^ " does not match")
    )
  end

(* TODO WN : NEED to re-check this function *)
and get_var_kind (var : ident) (tlist : spec_var_type_list) =
  try
    let r = snd(List.find (fun (v,en) -> v=var) tlist) in
    r.sv_info_kind
  with Not_found -> UNK

and set_var_kind (var : ident) (k : spec_var_kind) (tlist : spec_var_type_list) =
  try
    let n_tl = (List.filter (fun (v,en)->v<>var) tlist) in
    let r = snd(List.find (fun (v,en)->v=var) tlist) in
    let n_el = (var,{id=r.id; sv_info_kind=k}) in
    (n_el::n_tl, {id=r.id; sv_info_kind=k})
  with Not_found ->
    let n_tl = (var,{ sv_info_kind = k;id = (fresh_int ()) })::tlist in
    let typ = snd(List.find (fun (v,en)->v=var) n_tl) in
    (n_tl,typ)

and get_spec_var_ident (tlist:spec_var_type_list) (var : ident) p =
  try
    let k = snd(List.find (fun (v,en)->v=var) tlist) in
    CP.SpecVar(k.sv_info_kind,var,p)
  with
  | Not_found -> CP.SpecVar(UNK,var,p)


and get_spec_var_type_list_x ?(lprime=Unprimed) (v : ident) tlist pos =
  try
    let v_info = snd(List.find (fun (tv,en) -> tv=v) tlist) in
    match v_info.sv_info_kind with
    | UNK -> Err.report_error { Err.error_loc = pos;
                                Err.error_text = v ^ " is undefined (7)"; }
    | t -> let sv = CP.SpecVar (t, v, lprime) in sv
  with
  | Not_found -> let () = x_ninfo_pp (v^" not found in tlist ") pos in
    raise Not_found
(* ;Err.report_error { Err.error_loc = pos; *)
(*                                   Err.error_text = v ^ " is undefined (8)"; } *)

and get_spec_var_type_list ?(lprime=Unprimed) (v : ident) tlist pos =
  Debug.no_1 "get_spec_var_type_list" pr_id pr_none (fun _ -> get_spec_var_type_list_x ~lprime:lprime (v : ident) tlist pos) v

(* type: ?d_tt:spec_var_type_list -> *)
(*   Globals.ident * VarGen.primed -> *)
(*   CP.spec_var list -> VarGen.loc -> Cformula.CP.spec_var *)

and get_spec_var_type_list_infer ?(d_tt = []) (v : ident * primed) fvs pos =
  let pr_sv = Cprinter.string_of_spec_var in
  let pr_v = pr_pair pr_id string_of_primed in
  Debug.no_2 "get_spec_var_type_list_infer" pr_v string_of_tlist ( pr_sv)
    (fun _ _ -> get_spec_var_type_list_infer_x d_tt v fvs pos) v  d_tt

(* type: CP.spec_var list -> Globals.ident -> Globals.typ * bool *)
and get_var_type fvs v : (typ * bool) =
  let pr_out = pr_pair string_of_typ string_of_bool in
  Debug.no_2 "get_var_type" !CP.print_svl pr_id pr_out get_var_type_x fvs v

and get_var_type_x fvs v : (typ * bool) =
  let warning_if_non_empty lst tlst =
    if lst != [] then
      let () = x_binfo_pp "WARNING : free_vars_list contains duplicates" no_pos in
      x_tinfo_hp (add_str "fvs" Cprinter.string_of_typed_spec_var_list) tlst no_pos
  in
  (* let () = x_tinfo_hp (add_str "fvs" !CP.print_svl) fvs no_pos in *)
  (* let res_list = *)
  (*   CP.remove_dups_svl (List.filter ( *)
  (*       fun c -> (v = CP.name_of_spec_var c) && (p = CP.primed_of_spec_var c) *)
  (*     ) fv_list ) in *)
  let res_list =
    (List.filter (
        fun c -> (v = CP.name_of_spec_var c) (* && (p = CP.primed_of_spec_var c) *)
      ) fvs ) in
  match res_list with
  | [] ->

    let prog = I.get_iprog () in
    begin
      try
        let rdef = I.look_up_rel_def_raw prog.I.prog_rel_decls v in
        (RelT (List.map fst rdef.I.rel_typed_vars),false)
      with _ ->
        let () = x_tinfo_pp ("Cannot find "^v^" in rel_decls, use Void type?")  no_pos in
        (Void ,false)
    end
  | sv::lst ->
    let () = warning_if_non_empty lst res_list in
    (CP.type_of_spec_var sv,true)
(* | _ -> Err.report_error { *)
(*     Err.error_loc = pos; *)
(*     Err.error_text = "could not find a coherent " ^ v ^ " type"; *)
(*   } *)

and get_spec_var_type_list_infer_x d_tt ((v, p) : ident * primed) fvs pos =
  try
    (x_add (get_spec_var_type_list ~lprime:p) v d_tt pos)
  with _ ->
    let vtyp, check = get_var_type fvs v in
    let () = x_ninfo_hp (add_str "TODO: fix quick patch to type infer" pr_id) v pos in
    (* WN TODO : this is a quick patch to type infer problem *)
    (* if check = false then *)
    (*   Err.report_error { Err.error_loc = pos; *)
    (*                      Err.error_text = v ^ " is not found in both sides"; } *)
    (* else *)
    match vtyp with
    | UNK -> Err.report_error { Err.error_loc = pos;
                                Err.error_text = v ^ " is undefined (9)"; }
    | t -> CP.SpecVar (t, v, p (* Unprimed *))

and gather_type_info_heap prog (h0 : IF.h_formula) tlist =
  Debug.no_eff_2 "gather_type_info_heap" [false;true]
    Iprinter.string_of_h_formula string_of_tlist string_of_tlist (* (fun _ -> "()") *)
    (fun _ _ -> gather_type_info_heap_x prog h0 tlist) h0 tlist

and gather_type_info_heap_x prog (h0 : IF.h_formula) tlist =
  match h0 with
  | IF.Star { IF.h_formula_star_h1 = h1;
              IF.h_formula_star_h2 = h2;
              IF.h_formula_star_pos = pos }
  | IF.StarMinus { IF.h_formula_starminus_h1 = h1;
                   IF.h_formula_starminus_h2 = h2;
                   IF.h_formula_starminus_pos = pos }
  | IF.Conj { IF.h_formula_conj_h1 = h1;
              IF.h_formula_conj_h2 = h2;
              IF.h_formula_conj_pos = pos }
  | IF.ConjStar { IF.h_formula_conjstar_h1= h1;
                  IF.h_formula_conjstar_h2= h2;
                  IF.h_formula_conjstar_pos = pos }
  | IF.ConjConj { IF.h_formula_conjconj_h1 = h1;
                  IF.h_formula_conjconj_h2 = h2;
                  IF.h_formula_conjconj_pos = pos }
  | IF.Phase { IF.h_formula_phase_rd = h1;
               IF.h_formula_phase_rw = h2;
               IF.h_formula_phase_pos = pos } ->
    let n_tl = gather_type_info_heap_x prog h1 tlist in
    let n_tl = gather_type_info_heap_x prog h2 n_tl in
    n_tl
  | IF.HSubs hf -> gather_type_info_heap_x prog hf.h_formula_subs_form tlist
  | IF.HeapNode2 h2 ->
    let h = node2_to_node 2 prog h2 in
    let fh = IF.HeapNode h in
    let n_tl = gather_type_info_heap_x prog fh tlist in
    n_tl
  | IF.HeapNode { IF.h_formula_heap_node = (v, p); (* ident, primed *)
                  IF.h_formula_heap_arguments = ies; (* arguments *)
                  IF.h_formula_heap_ho_arguments = hoa; (* rho arguments *)
                  IF.h_formula_heap_poly_arguments = poly; (* heap poly args *)
                  IF.h_formula_heap_deref = deref;
                  IF.h_formula_heap_perm = perm;
                  IF.h_formula_heap_name = v_name; (* data/pred name *)
                  IF.h_formula_heap_imm = ann; (* data/pred name *)
                  IF.h_formula_heap_imm_param = ann_param;
                  IF.h_formula_heap_pos = pos } ->
    x_tinfo_hp (add_str "view" Iprinter.string_of_h_formula) h0 no_pos;
    x_tinfo_hp (add_str "ies" (pr_list Iprinter.string_of_formula_exp)) ies no_pos;
    (* x_binfo_hp (add_str "tlist:"  (string_of_tlist)) tlist no_pos; *)
    let ft = cperm_typ () in
    let gather_type_info_ho_args hoa tlist =
      List.fold_left (fun tl a ->
          x_add gather_type_info_formula prog a.IF.rflow_base tl false) tlist hoa
    in
    let gather_type_info_ann c tlist = (
      match c with
      | IP.NoAnn -> tlist
      | IP.ConstAnn _ -> tlist
      | IP.PolyAnn ((i,_),_) -> (*ignore*)(let (n_tl,_) = (x_add gather_type_info_var i tlist AnnT pos ) in n_tl) (*remove ignore*)
    ) in
    let rec gather_type_info_param_ann lst tl = (
      match lst with
      | [] -> tl
      | (Some h)::t ->
        let n_tl = x_add gather_type_info_ann h tl in
        let n_tl = x_add gather_type_info_param_ann t n_tl in
        n_tl
      | (None)::t -> x_add gather_type_info_param_ann t tl
    ) in
    let gather_type_info_perm p tl = (
      match p with
      | None -> tl
      | Some e -> let (n_tl,_) = x_add gather_type_info_exp prog e tl ft in n_tl
    ) in
    (* open square and close square after the heap node *)
    (* the problem is how to access and infer the type of the poly data args *)
    (* except for the data type, we also need to deal with the view type *)
    (* we doesn't use the data_def. we return the data_poly_para, if Not_found -> return the number of view_poly_para *)
    let num_poly_args = List.length poly in
    x_tinfo_hp (add_str "num of poly args" (pr_list string_of_typ)) poly no_pos;
    let () = y_tinfo_hp (add_str "type tlist"  (string_of_tlist)) tlist in
    (* how to get the instances' type? if we know the instances' type, we could make a comparison between the poly paras and instances' types*)
    let flag =
      (try
         let view_d = I.look_up_view_def_raw x_loc prog.I.prog_view_decls v_name in
         (* let tmp = un_option view_d.view_type_of_self UNK in *)
         1
       with
       | Not_found ->
         0
      ) in
    let unopted_self_typ =
      (try
         let view_d = I.look_up_view_def_raw x_loc prog.I.prog_view_decls v_name in
         let tmp = un_option view_d.view_type_of_self UNK in
         let () = y_tinfo_hp (add_str "view_type_of_self000" string_of_typ) tmp in
         tmp
       with
       | Not_found -> UNK
      ) in
    let () = y_tinfo_hp (add_str "view_type_of_self567765" string_of_typ) unopted_self_typ in
    let view_or_data_poly_para =
        (try
          let data_d = I.look_up_data_def_raw prog.I.prog_data_decls v_name in
          let data_poly_para = data_d.data_poly_para in
          data_poly_para
         with
         | Not_found ->
           try
             let view_d = I.look_up_view_def_raw x_loc prog.I.prog_view_decls v_name in
             let view_poly_para = view_d.view_poly_vars in
             let unopted_self_typ = un_option view_d.view_type_of_self UNK in
             let () = y_tinfo_hp (add_str "view_type_of_self111" string_of_typ) unopted_self_typ in
             view_poly_para
           with
           | Not_found ->
               report_error pos (" cannot find the heap name in data decls or view decls! ")) in
    (* poly parameters after the data declaration *)
    let num_poly_vars = List.length view_or_data_poly_para in
    x_tinfo_hp (add_str "num of poly vars" (pr_list Cprinter.string_of_ident)) view_or_data_poly_para no_pos;
    let gather_type_info_poly vname tname lst tl = (
      match lst with
      | [] -> tl
        (* if (num_poly_args = num_poly_vars) then tl else report_error pos (" the number of this heap poly arguments is not equal to the previous data declaration poly vars! ") *)
      | _  ->    (* step1: add the pointer typ to the tlist *)
        (* how to know whether the vname, say the x, is a self typ or not? *)
        (* am I supposed to make a flag for the view -> if it is a view, then the flag is 1, else the flag is 0, which means it should be data typ *)
        let () = y_tinfo_hp (add_str "flag" string_of_int) flag in
        let tname = if flag = 1 then (string_of_typ unopted_self_typ) else tname in
        let () = y_tinfo_hp (add_str "tname" (pr_id)) tname in

        (* if it is a view, we should do the poly parameters adding corresponding to the declaration and instantiation *)
        (* e.g.*)
        (* decl:
           llp<a>[`T1,`T2] == self=null or
               self::nodep<a,r>[`T2] *  t::llp<a>[`T1,`T2].
             ==> This tells us that the self type is nodep[`T2] *) (* which is fine for now *)
        (* inst:
           x::llp<>[int, bool]
             ==> This tells us that  T1 -> int, T2 -> bool *)

        (* find the index of the elements in the list and return the value of the *)
        (* let nameMade = if flag = 1 then
         *     let combined_lt =
         *       (try
         *          let tmp = List.combine view_or_data_poly_para poly in
         *          tmp
         *        with
         *        | _ ->
         *          report_error pos ("These two lists have different lengths!"))
         *     in
         *
         * (\* [(_,_), (_,_), (_,_)] ==> [(T1,bool),(T2,int)] *\)
         * (\* if found, then replace. *\)
         *     let (nam,typList) = (
         *       match unopted_self_typ with
         *       | Named (tmpnm, [])      -> (tmpnm, [])
         *       | Named (nm, ls) -> (\* if el is in the one of the combined_lt pairs *\)
         *            let rec helper current acc comls = (
         *              match current with
         *              | []   -> acc
         *              | h::t ->
         *                let (_,ele_b) = List.find (fun (a,b) -> a = (string_of_typ h)) comls in
         *                helper t (ele_b::acc) comls
         *            )
         *            in
         *            let new_ls = List.rev (helper ls [] combined_lt) in
         *            (nm, new_ls)
         *       | _ -> (tname, [])
         *     ) in ((mkNamedTyp ~args:(typList) nam))
         *   else ((mkNamedTyp ~args:(poly) tname))
         * in *)

        (* let nameMade = if flag = 1 then
         *     let selftyp = get_type_of_self tl in
         *     let (nam,typList) = (
         *       match selftyp with
         *       | Named (tmpnm, [])    ->  (tmpnm, [])
         *       | Named (nm, ls) -> (nm, ls)
         *       | _ -> (tname, poly)
         *     ) in ((mkNamedTyp ~args:(typList) nam))
         *   else ((mkNamedTyp ~args:(poly) tname))
         * in *)

        (* let (n_tl,_) = x_add gather_type_info_var vname tl nameMade pos in *)

        (* if it is a view, we cannot directly use this 'poly' here, in this regard, we need to make a kind of mapping. ==> we should check the 'unopted_self_typ', check the elements of its list and find out that it is T2, and then replace the T2 with the bool type. In this case, we need to consider the sequence of the parameters inside the list. *)

        let n_tl = tl in
        let () = y_tinfo_hp (add_str "type n_tl"  (string_of_tlist)) n_tl in
        (* step2: check whether the number of this one is equal to the previous data declaration's. Should this be in the parser part? *)
        match (num_poly_args = num_poly_vars) with
         | true -> n_tl
         | _    -> report_error pos (" the number of this heap poly arguments is not equal to the previous data declaration poly vars! ")
    ) in
    let n_tl = x_add gather_type_info_perm perm tlist in
    let n_tl = x_add gather_type_info_ann ann n_tl in
    let n_tl = (* if (!Globals.allow_field_ann) then *) x_add gather_type_info_param_ann ann_param n_tl (* else n_tl *) in
    let n_tl = x_add gather_type_info_ho_args hoa n_tl in
    (* let (ntl1, _) = List.split n_tl in *)
    x_tinfo_hp (add_str "type list1"  (string_of_tlist)) n_tl no_pos;
    let n_tl = x_add gather_type_info_poly v v_name poly n_tl in


    (* let (ntl2, _) = List.split n_tl in *)
    x_tinfo_hp (add_str "type list2"  (string_of_tlist)) n_tl no_pos;
    (* Deal with the generic pointer! *)
    if (v_name = Parser.generic_pointer_type_name) then
      (* Assumptions:
       * (i)  ies to contain a single argument, namely the value of the pointer
       * (ii) the head of the heap node is of form "V[.TypeOfV].FieldAccess"
       *      where [.TypeOfV] is optional type of V. If it is present, it is
       *      the type of V pointer. Otherwise, we try to find this information
       *      based on its fields.
       * (iii) Temporarily assume that only one field; the case of inline fields
       *      will be dealt with later.
      *)
      (* Step 1: Extract the main variable i.e. the root of the pointer *)
      (* let () = print_endline ("[gather_type_info_heap_x] heap pointer = " ^ v) in *)
      let tokens = Str.split (Str.regexp "\\.") v in
      (* let () = print_endline ("[gather_type_info_heap_x] tokens = {" ^ (String.concat "," tokens) ^ "}") in *)
      let rootptr = List.hd tokens in
      (* Step 2: Determine the type of [rootptr] and the field by looking
       * up the current state of tlist & information supplied by the user.
      *)
      let s = List.nth tokens 1 in
      let type_found,type_rootptr = try (* looking up in the list of data types *)
          (* Good user provides type for [rootptr] ==> done! *)
          let ddef = x_add I.look_up_data_def_raw prog.I.prog_data_decls s in
          (* let () = print_endline ("[gather_type_info_heap_x] root pointer type = " ^ ddef.I.data_name) in *)
          x_tinfo_hp (add_str "type list3"  (string_of_tlist)) n_tl no_pos;
          (true, mkNamedTyp ddef.I.data_name)

        with
        | Not_found -> (false,UNK) (* Lazy user ==> perform type reasoning! *) in
      (* After this, if type_found = false then we know that
       * s is a name of field of some data type
      *)
      let type_found,type_rootptr = if type_found then (type_found,type_rootptr)
        else try (* looking up in the collected types table for [rootptr] *)
            let vi = snd(List.find (fun (v,en) -> v = rootptr) n_tl) in
            match vi.sv_info_kind with
            | UNK -> (false,UNK)
            | _ -> (true,vi.sv_info_kind) (* type of [rootptr] is known ==> done! *)
          with
          | Not_found -> (false,UNK) in
      let type_found,type_rootptr = if type_found then (type_found,type_rootptr)
        else (* inferring the type from the name of the field *)
          let dts = I.look_up_types_containing_field prog.I.prog_data_decls s in
          x_tinfo_hp (add_str "type list4"  (string_of_tlist)) n_tl no_pos;
          if (List.length dts = 1) then
            (* the field uniquely determines the data type ==> done! *)
            (* let () = print_endline ("[gather_type_info_heap_x] Only type " ^ (List.hd dts) ^ " has field " ^ s) in *)
            (true,mkNamedTyp (List.hd dts))
          else
            (false,UNK) in
      (* Step 3: Collect the remaining type information *)
      if type_found then
        (* Know the type of rootptr ==> Know the type of the field *)
        let n_tl = ([(rootptr, { sv_info_kind = type_rootptr; id = 0 })]@n_tl) in
        (* Filter out user type indication, List.tl to remove the root as well *)
        let field_access_seq = List.tl (List.filter (fun x -> I.is_not_data_type_identifier prog.I.prog_data_decls x) tokens) in
        (* Get the type of the field which is the type of the pointer *)
        let ptr_type = I.get_type_of_field_seq prog.I.prog_data_decls type_rootptr field_access_seq in
        (* let () = print_endline ("[gather_type_info_heap_x] pointer type found = " ^ (string_of_typ ptr_type)) in *)
        let (n_tl,_)= x_add gather_type_info_exp prog (List.hd ies) n_tl ptr_type in n_tl
      else n_tl
    else (* End dealing with generic ptr, continue what the original system did *)
      let n_tl =
        (try
           let vdef = I.look_up_view_def_raw x_loc prog.I.prog_view_decls v_name in
           (* let () = if vdef.I.view_is_prim then Debug.ninfo_pprint ("type_gather: prim_pred "^v_name) no_pos in *)
           (*let ss = pr_list (pr_pair string_of_typ pr_id) vdef.I.view_typed_vars in*)
           let () = if not (IF.is_param_ann_list_empty ann_param) then
               (* let () = print_string ("\n(andreeac) searching for: "^(\* c^ *\)" got: "^vdef.I.view_data_name^"-"^vdef.I.view_name^" ann_param length:"^ (string_of_int (List.length ann_param))  ^"\n") in *)
               report_error pos (" predicate parameters are not allowed to have imm annotations") in
           x_add try_unify_view_type_args prog v_name vdef v deref ies hoa n_tl pos
         with
         | Not_found ->
           (try
              let n_tl = x_add try_unify_data_type_args prog v_name v deref ies n_tl pos in
              (* collect poly types corresponding to the data poly param, and then populate the poly args list *)

              n_tl
            with
            | Not_found ->
              (*let () = print_string (Iprinter.string_of_program prog) in*)
              Err.report_error
                {
                  Err.error_loc = pos;
                  Err.error_text = x_loc ^ v_name ^ " is neither 2 a data nor view name";
                }))
      in n_tl
  | IF.ThreadNode { IF.h_formula_thread_node = (v, p); (* ident, primed *)
                    IF.h_formula_thread_perm = perm;
                    IF.h_formula_thread_name = c; (* data/pred name *)
                    IF.h_formula_thread_resource = rsr;
                    IF.h_formula_thread_delayed = dl;
                    IF.h_formula_thread_label = pi;
                    IF.h_formula_thread_pos = pos } ->
    (* Follow IF.DataNode. May need TOCHECK *)
    let dataNode = IF.mkHeapNode (v,p) c [] (* TODO:HO *) 0 false SPLIT0 (Ipure.ConstAnn(Mutable)) false false false perm [] [] pi pos in
    let n_tl = x_add gather_type_info_heap prog dataNode tlist in
    let n_tl2 = x_add gather_type_info_formula prog rsr n_tl false in
    let n_tl3 = x_add gather_type_info_pure prog dl n_tl2 in
    n_tl3
  | IF.HRel (r, args, pos) ->
    (try
       let hpdef = I.look_up_hp_def_raw prog.I.prog_hp_decls r in
       if (List.length args) == (List.length hpdef.I.hp_typed_inst_vars) then
         let args_ctypes = List.map (fun (t,n,i) -> trans_type prog t pos) hpdef.I.hp_typed_inst_vars in
         let args_exp_types = List.map (fun t -> (t)) args_ctypes in
         let (n_tl,_) = x_add gather_type_info_var r tlist HpT pos in (*Need to consider about  pos*)
         let args_expt = List.combine args args_exp_types in
         let n_tl = List.fold_left ( fun tl (arg,et) ->
             fst(gather_type_info_exp_x prog arg tl et)) n_tl args_expt in
         n_tl
       else
         Err.report_error{ Err.error_loc = pos; Err.error_text = ("number of arguments for heap relation "^r^" does not match"); }
     with
     | Not_found -> failwith ("iast.gather_type_info_heap :gather_type_info_heap: relation "^r^" cannot be found")
     | Failure s -> failwith s
     | _ -> print_endline_quiet ("gather_type_info_heap: relation " ^ r);tlist
    )
  | IF.HTrue | IF.HFalse | IF.HEmp -> tlist
  (* TODO:WN:HVar *)
  | IF.HVar (v,hvar_vs) -> (v,{sv_info_kind = FORM;id=0})::tlist

(* and trans_formula_x (prog : I.prog_decl) (quantify : bool) (fvars : ident list) sep_collect (f0 : IF.formula) tlist (clean_res:bool) : (spec_var_type_list*CF.formula) = *)

let trans_formula : (I.prog_decl -> bool -> ident list -> bool ->  Iformula.formula -> spec_var_type_list -> bool -> (spec_var_type_list * CF.formula)) ref =
  ref (fun _ _ _ _ _ _ -> failwith "TBI")

let trans_view : (I.prog_decl -> ident list -> Cast.view_decl list ->   (ident * spec_var_info) list -> I.view_decl -> Cast.view_decl) ref =
  ref (fun _ _ _ _ _ -> failwith "TBI")

(* and spec_var_type_list = (( ident*spec_var_info)  list) *)

let sv_to_typ sv = match sv with
  | CP.SpecVar(t,i,p) ->(i, mk_spec_var_info t)

let case_normalize_renamed_formula (iprog:I.prog_decl) (avail_vars:CP.spec_var list) (expl_vars:CP.spec_var list) (f:CF.formula): CF.formula =
  (* cformula --> iformula *)
  (* iformula --> normalize *)
  (* iformula --> cformula *)
  (* let all_vs = CF.fv ~vartype:Global_var.var_with_exists f in    *)
  (* let () = y_tinfo_hp (add_str "all_vs" !CP.print_svl) all_vs in *)
  let free_vs = CF.fv f in
  let () = y_tinfo_hp (add_str "free_vs" !CP.print_svl) free_vs in
  let () = y_tinfo_hp (add_str "f" !CF.print_formula) f in
  let f = !CF.rev_trans_formula f in
  let () = y_tinfo_hp (add_str "f" Iprinter.string_of_formula) f in
  let fvars = List.map CP.name_of_spec_var avail_vars in
  let tlist = List.map sv_to_typ free_vs  in
  let avail_vars = List.map CP.primed_ident_of_spec_var avail_vars in
  let expl_vars = List.map CP.primed_ident_of_spec_var expl_vars in
  (* let (f,r_avail,r_expl) = !Iast.case_normalize_formula iprog avail_vars expl_vars f in *)
  let () = y_tinfo_hp (add_str "f" Iprinter.string_of_formula) f in
  let f = !Iast.case_normalize_formula iprog avail_vars f in
  let () = y_tinfo_hp (add_str "f(norm)" Iprinter.string_of_formula) f in
  let quantify = true in
  let clean_res = false in
  let sep_collect = true in
  let (sv,f) = !trans_formula iprog quantify (fvars : ident list) sep_collect f tlist clean_res in
  f

let case_normalize_renamed_formula (iprog:I.prog_decl) (avail_vars:CP.spec_var list) (expl_vars:CP.spec_var list) (f:CF.formula): CF.formula   =
  Debug.no_2 "Norm:case_norm" !CP.print_svl !CF.print_formula !CF.print_formula (fun _ _ -> case_normalize_renamed_formula (iprog:I.prog_decl) (avail_vars:CP.spec_var list) (expl_vars:CP.spec_var list) (f:CF.formula)) avail_vars f

let create_view (iprog:I.prog_decl) (id:ident) (vs:CP.spec_var list) (f:CF.formula): Cast.view_decl =
  let f = !CF.rev_trans_formula f in
  let f = Iformula.formula_to_struc_formula f in
  let vs_ident = List.map CP.name_of_spec_var vs in
  let iview = Iast.mk_iview_decl ~v_kind:(View_NORM) id "" vs_ident f no_pos in
  let cview = !trans_view iprog [] [] [] iview in
  cview


let trans_iformula_to_cformula iprog body =
  let tlist = [] in
  let quantify = true in
  let clean_res = false in
  let sep_collect = true in
  let fvars = [] in
  let (sv,nbody) = !trans_formula iprog quantify (fvars : ident list) sep_collect body tlist clean_res in
  nbody

let update_view_new_body ?(base_flag=false) ?(iprog=None) vd view_body_lbl =
  let () = vd.C.view_un_struc_formula <- view_body_lbl in
  let iprog = match iprog with
    | Some ip -> ip
    | None ->  Iast.get_iprog () in
  let old_sf = vd.C.view_formula in
  let view_body = CF.convert_un_struc_to_formula view_body_lbl in
  let args = vd.C.view_vars in
  (* struc --> better to re-transform it *)
  let new_view_body = case_normalize_renamed_formula iprog args [] view_body in
  let view_struc = CF.formula_to_struc_formula new_view_body in
  let view_struc = CF.add_label_to_struc_formula view_struc old_sf in
  let () = C.update_view_formula (fun _ -> view_struc) vd in
  let () = if base_flag then
      begin
        let () = y_tinfo_pp "updating base case now" in
        let is_prim_v = vd.C.view_is_prim in
        let rbc = CFE.compute_raw_base_case is_prim_v view_body_lbl in
        let vbc_i = vd.C.view_baga_inv in
        let vbc_o = vd.C.view_baga_over_inv in
        let vbc_u = vd.C.view_baga_under_inv in
        (* let vbc_i = conv_baga_inv vbi_i (\* vd.I.view_baga_inv *\) in *)
        (* let vbc_o = conv_baga_inv vbi_o in *)
        (* let vbc_u = conv_baga_inv vbi_u in *)
        let new_pf = MCP.pure_of_mix vd.C.view_user_inv in
        let (vboi,vbui,user_inv,user_x_inv) = failwith x_tbi
            (* x_add CFE.compute_baga_invs vbc_i vbc_o vbc_u new_pf no_pos *) in
        let () = vd.C.view_raw_base_case <- rbc in
        let () = vd.C.view_user_inv <- user_inv in
        let () = vd.C.view_x_formula <- user_x_inv in
        (* let () = vd.C.view_baga_inv <- vbc_i in *)
        let () = vd.C.view_baga_over_inv <- vboi in
        let () = vd.C.view_baga_x_over_inv <- vboi in
        let () = vd.C.view_baga_under_inv <- vbui in
        ()
      end
  in
  (* (\* let () = C.update_view_raw_base_case (x_add CF.repl_equiv_formula find_f) v in *\) *)
  ()

let get_type_of_var ntl var_id =
  try
    let v = snd (List.find (fun (v,_) -> v = var_id) ntl) in
    v.sv_info_kind
  with _ -> UNK
;;

Tpdispatcher.sub_type := sub_type ;;
