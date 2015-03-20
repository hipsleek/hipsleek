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
  Debug.no_eff_2 "res_retrieve" [true]
                 string_of_tlist pr pr_no
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
  Debug.no_eff_2 "res_replace" [true]
                 string_of_tlist pr pr_no
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
    let vdef = I.look_up_view_def_raw 6 prog.I.prog_view_decls h0.IF.h_formula_heap2_name in
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
              IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
              IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
              IF.h_formula_heap_perm = h0.IF.h_formula_heap2_perm;
              IF.h_formula_heap_arguments = hargs;
              IF.h_formula_heap_ho_arguments = h0.IF.h_formula_heap2_ho_arguments;
              IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
              IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos;
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
                  IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
                  IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
                  IF.h_formula_heap_arguments = hargs;
                  IF.h_formula_heap_ho_arguments = h0.IF.h_formula_heap2_ho_arguments;
                  IF.h_formula_heap_perm = h0.IF.h_formula_heap2_perm;
                  IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
                  IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos;
                  IF.h_formula_heap_label = h0.IF.h_formula_heap2_label; } in
        h

let node2_to_node i prog (h0 : IF.h_formula_heap2) : IF.h_formula_heap =
  Debug.no_1_num i "node2_to_node"
      (fun f -> Iprinter.string_of_h_formula (IF.HeapNode2 f) )
      (fun f -> Iprinter.string_of_h_formula (IF.HeapNode f))
      (fun _ -> node2_to_node_x prog h0) h0

let rec dim_unify d1 d2 = if (d1 = d2) then Some d1 else None

and must_unify (k1 : typ) (k2 : typ) tlist pos : (spec_var_type_list * typ) =
  let pr = string_of_typ in
  let pr_out (_, t) = string_of_typ t in
  Debug.no_2 "must_unify" pr pr pr_out (fun _ _ -> must_unify_x k1 k2 tlist pos) k1 k2

and must_unify_x (k1 : typ) (k2 : typ) tlist pos : (spec_var_type_list * typ) =
  let (n_tlist,k) = unify_type k1 k2 tlist in
  match k with
    | Some r -> (n_tlist,r)
    | None -> report_error pos ("UNIFICATION ERROR : at location "^(string_of_full_loc pos)
      ^" types "^(string_of_typ (get_type_entire tlist k1))
      ^" and "^(string_of_typ (get_type_entire tlist k2))^" are inconsistent")

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
  let pr2 (_, t) = pr_option pr t in
  Debug.no_2 "unify_type" pr pr pr2 (fun _ _ -> unify_type_x k1 k2 tlist) k1 k2

and unify_type_x (k1 : spec_var_kind) (k2 : spec_var_kind) tlist : (spec_var_type_list * (typ option)) =
  unify_type_modify true k1 k2 tlist

and unify_type_modify (modify_flag:bool) (k1 : spec_var_kind) (k2 : spec_var_kind) tlist : (spec_var_type_list*(typ option)) =
  let rec repl_tlist i k tl = repl_tvar_in unify modify_flag tl i k 
  and unify k1 k2 tl =
    match k1,k2 with
      | UNK, _ -> (tl,Some k2)
      | _, UNK -> (tl,Some k1)
      | Int, NUM -> (tl,Some Int) (* HACK here : give refined type *)
      | Float, NUM -> (tl,Some Float) (* give refined type *)
      | NUM, Int -> (tl,Some Int)
      | NUM, Float -> (tl,Some Float)
      | Int, Float -> (tl,Some Float) (*LDK: support floating point*)
      | Float, Int -> (tl,Some Float) (*LDK*)
      | Tree_sh, Tree_sh -> (tl,Some Tree_sh)
      | Named n1, Named n2 when (String.compare n1 "memLoc" = 0) ->   (* k1 is primitive memory predicate *)
          (tl, Some (Named n2))
      | Named n1, Named n2 when (String.compare n2 "memLoc" = 0) ->   (* k2 is primitive memory predicate *)
          (tl, Some (Named n1))
      | t1, t2  -> (
          if sub_type t1 t2 then (tlist, Some k2)  (* found t1, but expecting t2 *)
          else if sub_type t2 t1 then (tlist,Some k1)
          else 
            begin
              match t1,t2 with
              | TVar i1,_ -> repl_tlist i1 k2 tl
              | _,TVar i2 -> repl_tlist i2 k1 tl
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

and must_unify_expect_test_2 k1 k2 k3 tlist pos = 
  let (_, k) = unify_expect_modify false k1 k2 tlist in
  match k with
    | Some r -> r
    | None -> must_unify_expect_test k1 k3 tlist pos 
          
and subtype_expect_test _ _ = true

and unify_expect_modify (modify_flag:bool) (k1 : spec_var_kind) (k2 : spec_var_kind) tlist : (spec_var_type_list*(typ option)) =
  let pr = string_of_typ in
  Debug.no_2 "unify_expect_modify" pr pr string_of_tlist_type_option (fun _ _ -> unify_expect_modify_x modify_flag k1 k2 tlist) k1 k2

(* k2 is expected type *)
and unify_expect_modify_x (modify_flag:bool) (k1 : spec_var_kind) (k2 : spec_var_kind) tlist : (spec_var_type_list*(typ option)) =
  let bal_unify k1 k2 tl= unify_type_modify modify_flag k1 k2 tl in
  let repl_tlist i k tl = repl_tvar_in bal_unify modify_flag tl i k in
  let rec unify k1 k2 tl =
    match k1,k2 with
    | UNK, _ -> (tl ,Some k2)
    | _, UNK -> (tl,Some k1)
    | Int, NUM -> (tl,Some Int) (* give refined type *)
    | Float, NUM -> (tl,Some Float) (* give refined type *)
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
  | (n_tl,None) -> (n_tl,None)
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

(* should create entry in tlist *)
and fresh_tvar_rec tlist = 
  let i = fresh_int() in
  let key = "TVar__"^(string_of_int i) in
  let t2 = TVar i in
  let en={ sv_info_kind = t2; id = i} in
  (en, (key,en)::tlist)

and fresh_tvar tlist = 
  let (en, n_tlist) = fresh_tvar_rec tlist in
  (en.sv_info_kind,n_tlist)

(* TODO WN : NEED to re-check this function *)
and trans_type (prog : I.prog_decl) (t : typ) (pos : loc) : typ =
  match t with
    | Named c ->
          (try
            let todo_unk = I.look_up_data_def_raw prog.I.prog_data_decls c
            in Named c
          with
            | Not_found ->
                  (try
                    let todo_unk = I.look_up_view_def_raw 6 prog.I.prog_view_decls c
                    in Named c
                  with
                    | Not_found ->
                          (try
                            let todo_unk = I.look_up_enum_def_raw prog.I.prog_enum_decls c
                            in Int
                          with
                            | Not_found -> (* An Hoa : cannot find the type, just keep the name. *)
                                  if CF.view_prim_lst # mem c then Named c
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
    | p -> p

and trans_type_back (te : typ) : typ =
  match te with 
    | Named n -> Named n 
    | Array (t, d) -> Array (trans_type_back t, d) (* An Hoa *) 
    | p -> p 

and sub_type_x (t1 : typ) (t2 : typ) =
  let it1 = trans_type_back t1 in
  let it2 = trans_type_back t2 in
  I.sub_type it1 it2

and sub_type (t1 : typ) (t2 : typ) =
  let pr = string_of_typ in
  Debug.no_2 "sub_type" pr pr string_of_bool sub_type_x t1 t2 

and gather_type_info_var (var : ident) tlist (ex_t : typ) pos : (spec_var_type_list*typ) =
  let pr = string_of_typ in
  Debug.no_eff_3 "gather_type_info_var" [false;true] (fun x -> ("ident: "^x)) string_of_tlist pr string_of_tlist_type 
                 (fun _ _ _ -> gather_type_info_var_x var tlist ex_t pos) var tlist ex_t

and gather_type_info_var_x (var : ident) tlist (ex_t : spec_var_kind) pos : (spec_var_type_list*spec_var_kind) =
  if (is_dont_care_var var) then
    (tlist, UNK) (* for vars such as _ and # *)
  else
    try
      let (ident, k) = List.find (fun (a,b) -> a = var )tlist in
      let (n_tlist,tmp) = must_unify k.sv_info_kind ex_t tlist pos in 
      let n_tlist = type_list_add ident {sv_info_kind = tmp;id=k.id} n_tlist in
      (n_tlist, tmp )
    with
      | Not_found ->
          let vk = fresh_proc_var_kind tlist ex_t in
          ((var,vk)::tlist, vk.sv_info_kind)
      | ex ->
            let _ = print_string_quiet (get_backtrace_quiet ()) in
            report_error pos ("gather_type_info_var : unexpected exception "^(Printexc.to_string ex))
            (* raise ex *)

and gather_type_info_exp prog a0 tlist et =  
  Debug.no_eff_3 "gather_type_info_exp" [false;true] 
      Iprinter.string_of_formula_exp string_of_tlist string_of_typ
     string_of_tlist_type 
    (fun _ _ _ -> gather_type_info_exp_x prog a0 tlist et) a0 tlist et

and gather_type_info_exp_x prog a0 tlist et =
  match a0 with
  | IP.Null pos -> 
      let (new_et,n_tl) = fresh_tvar tlist in
      (n_tl, new_et)
  | IP.Ann_Exp (e,t, _) -> 
      (* TODO WN : check if t<:et *)
      let (n_tl,n_typ) = gather_type_info_exp_x prog e tlist t in
      (n_tl,n_typ)
  | IP.Var ((sv, sp), pos) ->
      let (n_tl,n_typ) = gather_type_info_var sv tlist et pos in      
      (n_tl,n_typ)    
  | IP.Level ((sv, sp), pos) ->
      (*sv should be of lock_typ*)
      let (n_tlist,_) = gather_type_info_var sv tlist lock_typ pos in
      (*level(sv) should be of type Int*)
      let (n_tlist,_)= must_unify_expect Globals.level_data_typ et n_tlist pos in
      (n_tlist,Globals.level_data_typ)
  | IP.Tsconst (_,pos) ->
      let t = Tree_sh in
      let (n_tlist,_) = must_unify_expect t et tlist pos in
      (n_tlist,t)
  | IP.AConst (_,pos) -> 
      let t = I.ann_type in
      let (n_tlist,_) = must_unify_expect t et tlist pos in
      (n_tlist,t)
  | IP.IConst (_,pos) | IP.InfConst (_,pos) | IP.NegInfConst (_,pos) -> 
      let t = I.int_type in
      let (n_tl,n_typ) = must_unify_expect t et tlist pos in
      (n_tl,n_typ)      
  | IP.FConst (_,pos) -> 
      let t = I.float_type in
      let (n_tl,n_typ) = must_unify_expect t et tlist pos in
      (n_tl,n_typ)
  | IP.Tup2 ((p1,p2), pos) ->
      let (new_et, n_tl) = fresh_tvar tlist in
      let (n_tl1,t1) = gather_type_info_exp prog p1 n_tl new_et in
      let (new_et2, n_tl2) = fresh_tvar n_tl1 in
      let (n_tl3,t2) = gather_type_info_exp_x prog p2 n_tl2 new_et2 in
      let (n_tl4,t) = must_unify_expect et (Tup2 (t1,t2)) n_tl3 pos in
      (n_tl4,t)
  | IP.Bptriple ((pc,pt,pa), pos) ->
      let todo_unk:Globals.typ = must_unify_expect_test_2 et Bptyp Tree_sh tlist pos in 
      let (new_et, n_tl) = fresh_tvar tlist in
      let nt = List.find (fun (v,en) -> en.sv_info_kind = new_et) n_tl in 
      let (tmp1,tmp2)=nt in
	  let (n_tl1,t1) = gather_type_info_exp prog pc n_tl new_et in (* Int *)
	  let (n_tl2,t2) = gather_type_info_exp_x prog pt n_tl1 new_et in (* Int *)
	  let (n_tl3,t3) = gather_type_info_exp_x prog pa n_tl2 new_et in (* Int *)
      let (n_tlist1,_) = must_unify_expect t1 Int n_tl3 pos in
      let (n_tlist2,_) = must_unify_expect t2 Int n_tlist1 pos in
      let (n_tlist3,_) = must_unify_expect t3 Int n_tlist2 pos in
      let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tlist3 in
      (n_tl, Bptyp)
  | IP.Add (a1, a2, pos) -> 
      let todo_unk:Globals.typ = must_unify_expect_test_2 et NUM Tree_sh tlist pos in (* UNK, Int, Float, NUm, Tvar *)
      let (new_et, n_tl) = fresh_tvar tlist in          
      let nt = List.find (fun (v,en) -> en.sv_info_kind = new_et) n_tl in 
      let (tmp1,tmp2)=nt in           
      let (n_tl1,t1) = gather_type_info_exp_x prog a1 n_tl new_et in (* tvar, Int, Float *)
      let (n_tl2,t2) = gather_type_info_exp_x prog a2 n_tl1 new_et in
      let (n_tlist1,t1) = must_unify_expect t1 et n_tl2 pos in
      let (n_tlist2,t2) = must_unify_expect t2 t1 n_tlist1 pos in
      let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tlist2 in
      (n_tl,t2)
  | IP.Subtract (a1, a2, pos) | IP.Max (a1, a2, pos) | IP.Min (a1, a2, pos) 
  | IP.Mult (a1, a2, pos) | IP.Div (a1, a2, pos) ->
      let todo_unk:Globals.typ = must_unify_expect_test et NUM tlist pos in (* UNK, Int, Float, NUm, Tvar *)
      let (new_et, n_tl) = fresh_tvar tlist in
      let nt = List.find (fun (v,en) -> en.sv_info_kind = new_et) n_tl in 
      let (tmp1,tmp2)=nt in                   
      let (n_tl1,t1) = gather_type_info_exp_x prog a1 n_tl new_et in (* tvar, Int, Float *)
      let (n_tl2,t2) = gather_type_info_exp_x prog a2 n_tl1 new_et in
      let (n_tlist1,t1) = must_unify_expect t1 et n_tl2 pos in
      let (n_tlist2,t2) = must_unify_expect t2 t1 n_tlist1 pos in
      let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tlist2 in
      (n_tl,t2)
  | IP.TypeCast (ty, a1, pos) ->
      let todo_unk:Globals.typ = must_unify_expect_test et ty tlist pos in
      let (new_et, n_tl) = fresh_tvar tlist in
      let nt = List.find (fun (v,en) -> en.sv_info_kind = new_et) n_tl in 
      let (tmp1,tmp2)=nt in
      let (n_tl1,t1) = gather_type_info_exp_x prog a1 n_tl new_et in
      let (n_tlist1,t1) = must_unify_expect t1 et n_tl1 pos in
      let n_tl = List.filter (fun (v,en) -> v<>tmp1) n_tl1 in
      (n_tl,t1)
  | IP.BagDiff (a1,a2,pos) ->
      let (el_t, n_tl) = fresh_tvar tlist in
      let new_et = must_unify_expect_test (BagT el_t) et n_tl pos in 
      let (n_tlist,t1) = gather_type_info_exp_x prog a1 tlist new_et in 
      let (n_tlist,t2) = gather_type_info_exp_x prog a2 n_tlist new_et in
      let (n_tlist,n_typ) = must_unify t1 t2 n_tlist pos in
      (n_tlist,n_typ)
  | IP.BagIntersect (es,pos) | IP.BagUnion (es,pos) ->
      let (el_t,n_tl) = fresh_tvar tlist in
      let new_et = must_unify_expect_test (BagT el_t) et n_tl pos in 
      let rec aux es_list type_list =
        match es_list with
        | []->([],type_list)
        | hd::tl -> 
            let (_tlist,_typ) = gather_type_info_exp_x prog hd type_list new_et in
            let (es_type_list,new_type_list) = aux tl _tlist in
            (_typ::es_type_list, new_type_list) 
      in
      let (es_type_list,new_tl) = aux es n_tl in
      List.fold_left (fun (tl,e) a -> must_unify a e tl pos) (new_tl,new_et) es_type_list
  | IP.Bag (es,pos) ->
      let (el_t,n_tl) = fresh_tvar tlist in
      let (n_tlist,t) = List.fold_left (fun (type_list,et) a -> 
        gather_type_info_exp_x prog a type_list et) (n_tl,el_t) es in
      (n_tlist,BagT t)  
  | IP.Func (id, es, pos) ->
      let t = I.int_type in
      let (n_tlist,n_typ)= must_unify_expect t et tlist pos in
      (n_tlist,n_typ)
  | IP.Template tp -> begin try
      let pos = tp.IP.templ_pos in
      let tid = tp.IP.templ_id in
      let tdef = I.look_up_templ_def_raw prog.I.prog_templ_decls tid in
      let ret_typ = tdef.I.templ_ret_typ in
      let param_types = List.map (fun (t, n) -> trans_type prog t pos) tdef.I.templ_typed_params in
      let func_typ = mkFuncT (List.map (fun (t, _) -> t) tdef.I.templ_typed_params) ret_typ in 
      let (n_tl, n_typ) = must_unify_expect ret_typ et tlist pos in
      let (n_tl, n_typ) = gather_type_info_var tid n_tl (* ret_typ *) func_typ pos in
      let exp_et_list = List.combine tp.IP.templ_args param_types in
      let n_tlist = List.fold_left (fun tl (arg, et) -> 
        fst (gather_type_info_exp prog arg tl et)) n_tl exp_et_list in
      let n_tlist = match tdef.I.templ_body with
      | None -> n_tlist
      | Some b -> fst (gather_type_info_exp prog b n_tlist ret_typ) in
      (n_tlist, ret_typ)
    with
    | Not_found -> failwith ("gather_type_info_exp: template " ^ tp.IP.templ_id ^ " cannot be found")
    | _ -> failwith ("type error: template " ^ tp.IP.templ_id)
    end
  | IP.ArrayAt ((a,p),idx,pos) ->
      let dim = List.length idx in
      let new_et = Array (et, dim) in
      let (n_tl,lt) = gather_type_info_var a tlist new_et pos in
      let rec aux id_list type_list =
        match id_list with
        | [] -> type_list
        | hd::tl -> 
            let (n_tl,n_typ) = gather_type_info_exp_x prog hd type_list Int in
            aux tl n_tl
      in
      let n_tlist = aux idx n_tl in
      (match lt with
      | Array (r,_) -> (n_tlist,r)
      | _ ->  failwith ("gather_type_info_exp: expecting type Array of dimension " ^ (string_of_int dim) ^ " but given " ^ (string_of_typ lt)))           
  | IP.ListTail (a,pos)  | IP.ListReverse (a,pos) ->
      let (fv,n_tl) = fresh_tvar tlist in
      let lt = List fv in
      let (n_tl,new_et) = must_unify lt et n_tl pos in
      let (n_tlist,lt) = gather_type_info_exp_x prog a n_tl new_et in
      (n_tlist,lt)
  | IP.ListAppend (es,pos) ->
      let (fv,n_tl) = fresh_tvar tlist in
      let lt = List fv in
      let (n_tl,new_et) = must_unify lt et n_tl pos in
      let (n_tlist,n_type) = List.fold_left (fun (type_list,et) l -> 
        gather_type_info_exp_x prog l type_list et) (n_tl,new_et) es  in
      (n_tlist,n_type)
  | IP.ListHead (a, pos) ->
      let (fv,n_tl) = fresh_tvar tlist in
      let new_et = List fv in
      let (n_tl,lt) = gather_type_info_exp_x prog a n_tl new_et in
      let (n_tlist,rs) = must_unify lt (List et) n_tl pos in
      (match rs with
      | List r -> (n_tlist, r)
      | _ ->  failwith ("gather_type_info_exp: expecting List type but obtained "^(string_of_typ lt)))
  | IP.ListCons (e,es,pos) ->
      let (fv,n_tl) = fresh_tvar tlist in
      let (n_tl,e1) = gather_type_info_exp_x prog e n_tl fv in
      let lt = List e1 in
      let (n_tl,new_et) = must_unify lt et n_tl pos in
      let (n_tlist,lt) = gather_type_info_exp_x prog es n_tl new_et in
      (n_tlist,lt)
  | IP.List (es,pos) ->
      let (fv,n_tl) = fresh_tvar tlist in
      let (n_tl,r) = List.fold_left (fun (type_list,et) l -> 
        gather_type_info_exp_x prog l type_list et) (n_tl,fv) es  in
      let lt = List r in
      let (n_tlist,r) = must_unify lt et n_tl pos in
      (n_tlist,r)
  | IP.ListLength (a, pos) ->
      let (fv,n_tl) = fresh_tvar tlist in
      let new_et = List fv in
      let (n_tl,r) = must_unify Int et n_tl pos in
      let (n_tlist,_) = gather_type_info_exp_x prog a n_tl new_et in
      (n_tlist,r)
  | IP.BExpr f1 -> (gather_type_info_pure prog f1 tlist, Bool)

and gather_type_info_pure_x prog (p0 : IP.formula) (tlist : spec_var_type_list) : spec_var_type_list =
  match p0 with
  | IP.BForm (b,_) -> gather_type_info_b_formula prog b tlist
  | IP.And (p1, p2, pos) | IP.Or (p1, p2, _, pos) ->
      let n_tl = gather_type_info_pure prog p1 tlist in
      let n_tl = gather_type_info_pure prog p2 n_tl in
      n_tl
  | IP.AndList b -> 
      let n_tlist = List.fold_left (fun tl (_,c) -> gather_type_info_pure prog c tl) tlist b in 
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
          let n_tlist = gather_type_info_pure prog qf ((qv,vk)::n_tl) in
          n_tlist           
        end

and gather_type_info_pure prog (p0 : IP.formula) (tlist : spec_var_type_list) : spec_var_type_list =
  Debug.no_eff_2 "gather_type_info_pure" [false;true]  (Iprinter.string_of_pure_formula) string_of_tlist string_of_tlist
                 (gather_type_info_pure_x prog) p0 tlist

and gather_type_info_p_formula prog pf tlist =  match pf with
  | IP.Frm _ -> tlist
  | IP.BConst _ -> tlist
  | IP.BVar ((bv, bp), pos) ->
      let (n_tlist,n_type) = gather_type_info_var bv tlist (C.bool_type) pos in
      n_tlist
  | IP.SubAnn(a1,a2,pos) ->
      let (n_tl,n_ty) = gather_type_info_exp prog a1 tlist (Cpure.ann_type) in
      let (n_tl,n_ty) = gather_type_info_exp prog a2 n_tl (Cpure.ann_type) in
      n_tl
  | IP.LexVar(t_ann, ls1, ls2, pos) ->
      let n_tl = List.fold_left (fun tl e-> fst(gather_type_info_exp prog e tl (Int))) tlist ls1  in
      let n_tl = List.fold_left (fun tl e-> fst(gather_type_info_exp prog e tl (Int))) n_tl ls2 in
      let n_tl = List.fold_left (fun tl e -> fst(gather_type_info_exp prog e tl (Int))) n_tl ls2 in
      n_tl
  | IP.Lt (a1, a2, pos) | IP.Lte (a1, a2, pos) | IP.Gt (a1, a2, pos) | IP.Gte (a1, a2, pos) ->
      let (new_et,n_tl) = fresh_tvar tlist in
      let (n_tl,t1) = gather_type_info_exp prog a1 n_tl new_et in (* tvar, Int, Float *)
      let (n_tl,t2) = gather_type_info_exp prog a2 n_tl new_et in
      let (n_tl,t1) = must_unify_expect t1 NUM n_tl pos in
      let (n_tl,t2) = must_unify_expect t2 NUM n_tl pos in
      let (n_tl,_) = must_unify t1 t2 n_tl pos  in (* UNK, Int, Float, TVar *) 
      n_tl
  | IP.EqMin (a1, a2, a3, pos) | IP.EqMax (a1, a2, a3, pos) ->
      let (new_et,n_tl) = fresh_tvar tlist in
      let (n_tl,t1) = gather_type_info_exp prog a1 n_tl new_et in (* tvar, Int, Float *)
      let (n_tl,t2) = gather_type_info_exp prog a2 n_tl new_et in
      let (n_tl,t3) = gather_type_info_exp prog a3 n_tl new_et in (* tvar, Int, Float *)
      let (n_tl,t1) = must_unify_expect t1 NUM n_tl pos in
      let (n_tl,t2) = must_unify_expect t2 NUM n_tl pos in
      let (n_tl,t3) = must_unify_expect t3 NUM n_tl pos in
      let (n_tl,t) = must_unify t1 t2 n_tl pos  in (* UNK, Int, Float, TVar *) 
      let (n_tl,t) = must_unify t t3 n_tl pos  in (* UNK, Int, Float, TVar *) 
      n_tl
  | IP.BagIn ((v, p), e, pos) | IP.BagNotIn ((v, p), e, pos) ->  (* v in e *)
      let (new_et,n_tl) = fresh_tvar tlist in
      let (n_tl,t1) = gather_type_info_exp prog e n_tl (BagT new_et) in
      let (n_tl,t2) = gather_type_info_var v n_tl new_et pos in
      let (n_tl,_)= must_unify t1 (BagT t2) n_tl pos in
      n_tl
  | IP.BagSub (e1, e2, pos) ->
      let (new_et,n_tl) = fresh_tvar tlist in
      let (n_tl,t1) = gather_type_info_exp prog e1 n_tl (BagT new_et) in
      let (n_tl,t2) = gather_type_info_exp prog e2 n_tl (BagT new_et) in
      let (n_tl,_) = must_unify t1 t2 n_tl pos in
      n_tl
  | IP.Eq (a1, a2, pos) | IP.Neq (a1, a2, pos) -> (*Need consider*) (
      (* allow comparision btw 2 pointers having different types *)
      let (new_et1,n_tl) = fresh_tvar tlist in
      let (n_tl,t1) = gather_type_info_exp prog a1 n_tl new_et1 in (* tvar, Int, Float *)
      let (new_et2,n_tl) = fresh_tvar n_tl in
      let (n_tl,t2) = gather_type_info_exp prog a2 n_tl new_et2 in
      match t1, t2 with
      | Named _, Named _ -> n_tl
      | _ ->
          let (n_tl,_) = must_unify t1 t2 n_tl pos  in (* UNK, Int, Float, TVar *)
          n_tl
    )
  | IP.BagMax ((v1, p1), (v2, p2), pos) 
  | IP.BagMin ((v1, p1), (v2, p2), pos) -> (* V1=BagMin(V2) *)
      let (et,n_tl) = fresh_tvar tlist in
      let (n_tl,t1) = gather_type_info_var v1 n_tl et pos in
      let (n_tl,t) = must_unify t1 NUM n_tl pos  in
      let (n_tl,_) = gather_type_info_var v2 n_tl (BagT t) pos in
      n_tl
  (* | IP.VarPerm _ -> tlist (*TO CHECK: no type info*) *)
  | IP.ListIn (e1, e2, pos) | IP.ListNotIn (e1, e2, pos)  | IP.ListAllN (e1, e2, pos) ->
      let (new_et,n_tl) = fresh_tvar tlist in
      let (n_tl,t1) = gather_type_info_exp prog e2 n_tl (List new_et) in
      let (n_tl,t2) = gather_type_info_exp prog e1 n_tl new_et in
      let (n_tl,_) = must_unify t1 (List t2) n_tl pos in
      n_tl
  | IP.ListPerm (e1, e2, pos) ->
      let (el_t,n_tl) = fresh_tvar tlist in
      let new_et = List el_t in
      let (n_tl,t1) = gather_type_info_exp_x prog e1 n_tl new_et in 
      let (n_tl,t2) = gather_type_info_exp_x prog e2 n_tl new_et in
      let (n_tl,_) = must_unify t1 t2 n_tl pos in
      n_tl
  | IP.RelForm (r, args, pos) -> 
      (try
        let rdef = I.look_up_rel_def_raw prog.I.prog_rel_decls r in
        let args_ctypes = List.map (fun (t,n) -> trans_type prog t pos) rdef.I.rel_typed_vars in
        let args_exp_types = List.map (fun t -> (t)) args_ctypes in
        let (n_tl,n_typ) = gather_type_info_var r tlist (RelT []) pos in (*Need to consider about pos*)
        let tmp_list = List.combine args args_exp_types in
        let n_tlist = List.fold_left (fun tl (arg,et) ->
          fst(gather_type_info_exp prog arg tl et )) n_tl tmp_list in
        n_tlist             
      with
        | Not_found ->    failwith ("gather_type_info_b_formula: relation "^r^" cannot be found")
        | Invalid_argument _ -> failwith ("number of arguments for relation " ^ r ^ " does not match")
        | _ -> print_endline_quiet ("gather_type_info_b_formula: relation " ^ r);tlist       
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
          let (n_tl,_) = gather_type_info_var r tlist HpT pos in (*Need to consider about pos*)
          let tmp_list = List.combine args args_exp_types in
          let n_tlist = List.fold_left (fun tl (arg,et) -> fst(gather_type_info_var arg tl et pos )) n_tl tmp_list in (*Need to consider about pos*)
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
  | IP.TermR tid -> begin try
      let pos = tid.IP.tu_pos in
      let sid = tid.IP.tu_sid in
      let utdef = I.look_up_ut_def_raw prog.I.prog_ut_decls sid in
      let param_types = List.map (fun (t, _) -> trans_type prog t pos) utdef.I.ut_typed_params in
      let exp_et_list = List.combine tid.IP.tu_args param_types in
      let n_tlist = List.fold_left (fun tl (arg, et) -> 
        fst (gather_type_info_exp prog arg tl et)) tlist exp_et_list in
      n_tlist
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

and gather_type_info_b_formula_x prog b0 tlist =
  let (pf,_) = b0 in
  gather_type_info_p_formula prog pf tlist
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
  (*     let (n_tl,t1) = must_unify_expect t1 NUM n_tl pos in *)
  (*     let (n_tl,t2) = must_unify_expect t2 NUM n_tl pos in *)
  (*     let (n_tl,_) = must_unify t1 t2 n_tl pos  in (\* UNK, Int, Float, TVar *\)  *)
  (*     n_tl *)
  (* | IP.EqMin (a1, a2, a3, pos) | IP.EqMax (a1, a2, a3, pos) -> *)
  (*     let (new_et,n_tl) = fresh_tvar tlist in *)
  (*     let (n_tl,t1) = gather_type_info_exp a1 n_tl new_et in (\* tvar, Int, Float *\) *)
  (*     let (n_tl,t2) = gather_type_info_exp a2 n_tl new_et in *)
  (*     let (n_tl,t3) = gather_type_info_exp a3 n_tl new_et in (\* tvar, Int, Float *\) *)
  (*     let (n_tl,t1) = must_unify_expect t1 NUM n_tl pos in *)
  (*     let (n_tl,t2) = must_unify_expect t2 NUM n_tl pos in *)
  (*     let (n_tl,t3) = must_unify_expect t3 NUM n_tl pos in *)
  (*     let (n_tl,t) = must_unify t1 t2 n_tl pos  in (\* UNK, Int, Float, TVar *\)  *)
  (*     let (n_tl,t) = must_unify t t3 n_tl pos  in (\* UNK, Int, Float, TVar *\)  *)
  (*     n_tl *)
  (* | IP.BagIn ((v, p), e, pos) | IP.BagNotIn ((v, p), e, pos) ->  (\* v in e *\) *)
  (*     let (new_et,n_tl) = fresh_tvar tlist in *)
  (*     let (n_tl,t1) = gather_type_info_exp e n_tl (BagT new_et) in *)
  (*     let (n_tl,t2) = gather_type_info_var v n_tl new_et pos in *)
  (*     let (n_tl,_)= must_unify t1 (BagT t2) n_tl pos in *)
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
  (*         let (n_tl,_) = must_unify t1 t2 n_tl pos  in (\* UNK, Int, Float, TVar *\) *)
  (*         n_tl *)
  (*   ) *)
  (* | IP.BagMax ((v1, p1), (v2, p2), pos)  *)
  (* | IP.BagMin ((v1, p1), (v2, p2), pos) -> (\* V1=BagMin(V2) *\) *)
  (*     let (et,n_tl) = fresh_tvar tlist in *)
  (*     let (n_tl,t1) = gather_type_info_var v1 n_tl et pos in *)
  (*     let (n_tl,t) = must_unify t1 NUM n_tl pos  in *)
  (*     let (n_tl,_) = gather_type_info_var v2 n_tl (BagT t) pos in *)
  (*     n_tl *)
  (* | IP.VarPerm _ -> tlist (\*TO CHECK: no type info*\) *)
  (* | IP.ListIn (e1, e2, pos) | IP.ListNotIn (e1, e2, pos)  | IP.ListAllN (e1, e2, pos) -> *)
  (*     let (new_et,n_tl) = fresh_tvar tlist in *)
  (*     let (n_tl,t1) = gather_type_info_exp e2 n_tl (List new_et) in *)
  (*     let (n_tl,t2) = gather_type_info_exp e1 n_tl new_et in *)
  (*     let (n_tl,_) = must_unify t1 (List t2) n_tl pos in *)
  (*     n_tl *)
  (* | IP.ListPerm (e1, e2, pos) -> *)
  (*     let (el_t,n_tl) = fresh_tvar tlist in *)
  (*     let new_et = List el_t in *)
  (*     let (n_tl,t1) = gather_type_info_exp_x e1 n_tl new_et in  *)
  (*     let (n_tl,t2) = gather_type_info_exp_x e2 n_tl new_et in *)
  (*     let (n_tl,_) = must_unify t1 t2 n_tl pos in *)
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
    | Some (v,pr) -> let (n_tl,_)= gather_type_info_var v tlist thread_typ f.IF.formula_pos in n_tl
  ) in
  let n_tl = gather_type_info_heap prog f.IF.formula_heap n_tl in
  let n_tl = gather_type_info_pure prog f.IF.formula_pure n_tl in   
  n_tl

and gather_type_info_formula_x prog f0 tlist filter_res = 
  let helper pure heap tl= (
    let n_tl = gather_type_info_heap prog heap tl in
    let n_tl = gather_type_info_pure prog pure n_tl in
    n_tl
  ) in  
  match f0 with
  | IF.Or b->
      let n_tl = gather_type_info_formula_x prog b.IF.formula_or_f1 tlist filter_res in
      let n_tl = gather_type_info_formula_x prog b.IF.formula_or_f2 n_tl filter_res in
      n_tl
  | IF.Exists b ->
      let (n_tl,rl) = res_retrieve tlist filter_res b.IF.formula_exists_flow in
      let n_tl = List.fold_left (fun tl f -> gather_type_info_one_formula prog f tl filter_res) n_tl b.IF.formula_exists_and in
      let n_tl = helper b.IF.formula_exists_pure b.IF.formula_exists_heap n_tl in   
      let n_tl = res_replace n_tl rl filter_res b.IF.formula_exists_flow in
      n_tl 
  | IF.Base b ->
      let (n_tl,rl) = res_retrieve tlist filter_res b.IF.formula_base_flow in
      let todo_unk = List.fold_left (fun tl f -> gather_type_info_one_formula prog f tl filter_res) n_tl b.IF.formula_base_and in
      let n_tl = helper b.IF.formula_base_pure b.IF.formula_base_heap n_tl in
      let n_tl = res_replace n_tl rl filter_res b.IF.formula_base_flow  in
      n_tl

and gather_type_info_struc_f prog (f0:IF.struc_formula) tlist =
  Debug.no_eff_2 "gather_type_info_struc_f" [false;true]
                 Iprinter.string_of_struc_formula string_of_tlist string_of_tlist
                 (fun _ _ -> gather_type_info_struc_f_x prog f0 tlist) f0 tlist

and gather_type_info_struc_f_x prog (f0:IF.struc_formula) tlist = 
  let rec inner_collector (f0:IF.struc_formula) tl = (
    match f0 with
    | IF.EAssume b -> 
        let n_tl = gather_type_info_formula prog b.IF.formula_assume_simpl tl true in
        gather_type_info_struc_f prog b.IF.formula_assume_struc n_tl
    | IF.ECase b ->  
        List.fold_left (
          fun tl (c1,c2)->
            let n_tl = gather_type_info_pure prog c1 tl in
            inner_collector c2 n_tl
        ) tl b.IF.formula_case_branches
    | IF.EBase b ->  
        let n_tl  = gather_type_info_formula prog b.IF.formula_struc_base tl false in
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
  (* An Hoa : problem detected - have to expand the inline fields as well, fix in look_up_all_fields. *)
  if (deref = 0) then (
    try (
      let ddef = I.look_up_data_def_raw prog.I.prog_data_decls c in
      let (n_tl,_) = gather_type_info_var v tlist ((Named c)) pos in
      let fields = I.look_up_all_fields prog ddef in
      try
        (*fields may contain offset field and not-in-used*)
        let ies = add_last_diff ies fields ([]) in
        let f tl arg ((ty,_),_,_,_)=
          (let (n_tl,_) = gather_type_info_exp prog arg tl ty in n_tl)
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
  else (
    (* dereference cases *)
    try (
      let base_ddecl = (
        let dname = (
          match c with
          | "int" | "float" | "void" | "bool" -> c ^ "_star"
          | _ -> c
        ) in
        I.look_up_data_def_raw prog.I.prog_data_decls dname
      ) in
      let holder_name = (
        let deref_str = ref "" in
        for i = 1 to deref do
          deref_str := !deref_str ^ "_star";
        done;
        c ^ !deref_str
      ) in
      let (n_tl,_) = gather_type_info_var v tlist ((Named holder_name)) pos in
      let fields = I.look_up_all_fields prog base_ddecl in
      try 
        let f tl arg ((ty,_),_,_,_)=
          (let (n_tl,_) = gather_type_info_exp prog arg tl ty in n_tl)
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

and try_unify_view_type_args prog c vdef v deref ies hoa tlist pos =
  let pr1 = add_str "is_prim_pred" string_of_bool in
  let pr2 = add_str "name,var" (pr_pair pr_id pr_id) in
  let pr3 = string_of_tlist in
  let pr4 = pr_list Iprinter.string_of_formula_exp in
  Debug.no_4 "try_unify_view_type_args" pr1 pr2 pr3 pr4 pr3
      (fun _ _ _ _ -> try_unify_view_type_args_x prog c vdef v deref ies hoa tlist pos)
      vdef.I.view_is_prim (c,v) tlist ies
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
and try_unify_view_type_args_x prog c vdef v deref ies hoa tlist pos =
  let dname = vdef.I.view_data_name in
  let n_tl = (
    if (String.compare dname "" = 0) then tlist
    else if vdef.I.view_is_prim then
      begin
        match vdef.I.view_type_of_self with
          | None -> tlist
          | Some self_typ ->
                let (n_tl,_) = gather_type_info_var v tlist self_typ pos in
                n_tl
      end
    else 
      let expect_dname = (
          let s = ref "" in
          for i = 1 to deref do
            s := !s ^ "_star";
          done;
          dname ^ !s
      ) in
      let (n_tl,_) = gather_type_info_var v tlist ((Named expect_dname)) pos in
      n_tl
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
  let (vt_u,tmp_r) = List.partition (fun (ty,_) -> ty==UNK) tmp_r in
  if (Gen.is_empty vt_u)
  then
    let n_tl = (List.fold_left (fun tl (t, n) -> fst(gather_type_info_var n tl (t) pos)) n_tl tmp_r) in
    n_tl
  else begin
    (* below seems wrong to unify against previous var names *)
    (try 
      let n_tl = (List.fold_left (fun tl (t, n) -> fst(gather_type_info_var n tl (t) pos))n_tl tmp_r) in
      let f tl arg lhs_v = 
        (let et = get_var_kind lhs_v tl  in 
        let (n_tl,new_t) = gather_type_info_exp prog arg tl et in
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
          

and get_spec_var_type_list (v : ident) tlist pos =
  try
    let v_info = snd(List.find (fun (tv,en) -> tv=v) tlist) in
    match v_info.sv_info_kind with
    | UNK -> Err.report_error { Err.error_loc = pos;
                                Err.error_text = v ^ " is undefined"; }
    | t -> let sv = CP.SpecVar (t, v, Unprimed) in sv
  with
    | Not_found -> Err.report_error { Err.error_loc = pos;
                                      Err.error_text = v ^ " is undefined"; }

and get_spec_var_type_list_infer (v : ident * primed) fvs pos =
  (* let pr_sv = Cprinter.string_of_spec_var in *)
  Debug.no_2 "get_spec_var_type_list_infer" 
    pr_none (* (pr_list pr_sv) *) pr_none pr_none
    (fun _ _ -> get_spec_var_type_list_infer_x v fvs pos) v fvs

and get_spec_var_type_list_infer_x ((v, p) : ident * primed) fvs pos =
  let get_var_type v fv_list: (typ * bool) = 
    let res_list = 
      CP.remove_dups_svl (List.filter (
        fun c -> (v = CP.name_of_spec_var c) && (p = CP.primed_of_spec_var c)
      ) fv_list ) in
    match res_list with
    | [] -> (Void,false)
    | [sv] -> (CP.type_of_spec_var sv,true)
    | _ -> Err.report_error {
             Err.error_loc = pos;
             Err.error_text = "could not find a coherent " ^ v ^ " type";
           }
  in
  let vtyp, check = get_var_type v fvs in
 (* WN TODO : this is a quick patch to type infer problem *)
  (* if check = false then *)
  (*   Err.report_error { Err.error_loc = pos; *)
  (*                      Err.error_text = v ^ " is not found in both sides"; } *)
  (* else *)
    match vtyp with
    | UNK -> Err.report_error { Err.error_loc = pos;
                                Err.error_text = v ^ " is undefined"; }
    | t -> CP.SpecVar (t, v, Unprimed)

and gather_type_info_heap prog (h0 : IF.h_formula) tlist =
  Debug.no_eff_2 "gather_type_info_heap" [false;true]
                 Iprinter.string_of_h_formula string_of_tlist (fun _ -> "()")
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
  | IF.HeapNode2 h2 ->
      let h = node2_to_node 2 prog h2 in
      let fh = IF.HeapNode h in 
      let n_tl = gather_type_info_heap_x prog fh tlist in 
      n_tl
  | IF.HeapNode { IF.h_formula_heap_node = (v, p); (* ident, primed *)
                  IF.h_formula_heap_arguments = ies; (* arguments *)
                  IF.h_formula_heap_ho_arguments = hoa; (* rho arguments *)
                  IF.h_formula_heap_deref = deref;
                  IF.h_formula_heap_perm = perm;
                  IF.h_formula_heap_name = v_name; (* data/pred name *)
                  IF.h_formula_heap_imm = ann; (* data/pred name *)
                  IF.h_formula_heap_imm_param = ann_param;
                  IF.h_formula_heap_pos = pos } ->
      x_tinfo_hp (add_str "view" Iprinter.string_of_h_formula) h0 no_pos;
      let ft = cperm_typ () in
      let gather_type_info_ho_args hoa tlist =
        List.fold_left (fun tl a ->
          gather_type_info_formula prog a.IF.rflow_base tl false) tlist hoa
      in
      let gather_type_info_ann c tlist = (
        match c with
        | IP.ConstAnn _ -> tlist
        | IP.PolyAnn ((i,_),_) -> (*ignore*)(let (n_tl,_) = (gather_type_info_var i tlist AnnT pos ) in n_tl) (*remove ignore*)
      ) in
      let rec gather_type_info_param_ann lst tl = (
        match lst with
        | [] -> tl
        | (Some h)::t -> 
            let n_tl = gather_type_info_ann h tl in
            let n_tl = gather_type_info_param_ann t n_tl in
            n_tl
        | (None)::t -> gather_type_info_param_ann t tl 
      ) in
      let gather_type_info_perm p tl = (
        match p with
        | None -> tl
        | Some e -> let (n_tl,_) = gather_type_info_exp prog e tl ft in n_tl 
      ) in
      let n_tl = gather_type_info_perm perm tlist in
      let n_tl = gather_type_info_ann ann n_tl in
      let n_tl = (* if (!Globals.allow_field_ann) then *) gather_type_info_param_ann ann_param n_tl (* else n_tl *) in
      let n_tl = gather_type_info_ho_args hoa n_tl in
      (*Deal with the generic pointer! *)
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
          let ddef = I.look_up_data_def_raw prog.I.prog_data_decls s in 
          (* let () = print_endline ("[gather_type_info_heap_x] root pointer type = " ^ ddef.I.data_name) in *)
          (true, Named ddef.I.data_name)
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
            if (List.length dts = 1) then
              (* the field uniquely determines the data type ==> done! *)
              (* let () = print_endline ("[gather_type_info_heap_x] Only type " ^ (List.hd dts) ^ " has field " ^ s) in *)
              (true,Named (List.hd dts))
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
          let (n_tl,_)= gather_type_info_exp prog (List.hd ies) n_tl ptr_type in n_tl
        else n_tl
      else (* End dealing with generic ptr, continue what the original system did *)
        let n_tl = 
        (try
          let vdef = I.look_up_view_def_raw 10 prog.I.prog_view_decls v_name in
          (* let () = if vdef.I.view_is_prim then Debug.ninfo_pprint ("type_gather: prim_pred "^v_name) no_pos in *)
          (*let ss = pr_list (pr_pair string_of_typ pr_id) vdef.I.view_typed_vars in*)
          let () = if not (IF.is_param_ann_list_empty ann_param) then
            (* let () = print_string ("\n(andreeac) searching for: "^(\* c^ *\)" got: "^vdef.I.view_data_name^"-"^vdef.I.view_name^" ann_param length:"^ (string_of_int (List.length ann_param))  ^"\n") in *)
            report_error pos (" predicate parameters are not allowed to have imm annotations") in
          try_unify_view_type_args prog v_name vdef v deref ies hoa n_tl pos 
        with
        | Not_found ->
          (try
            let n_tl = try_unify_data_type_args prog v_name v deref ies n_tl pos in 
            n_tl
          with
          | Not_found ->
            (*let () = print_string (Iprinter.string_of_program prog) in*)
            Err.report_error
            {
              Err.error_loc = pos;
              Err.error_text = v_name ^ " is neither 2 a data nor view name";
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
      let n_tl = gather_type_info_heap prog dataNode tlist in
      let n_tl2 = gather_type_info_formula prog rsr n_tl false in
      let n_tl3 = gather_type_info_pure prog dl n_tl2 in
      n_tl3
    | IF.HRel (r, args, pos) ->
      (try
        let hpdef = I.look_up_hp_def_raw prog.I.prog_hp_decls r in
        if (List.length args) == (List.length hpdef.I.hp_typed_inst_vars) then
          let args_ctypes = List.map (fun (t,n,i) -> trans_type prog t pos) hpdef.I.hp_typed_inst_vars in
          let args_exp_types = List.map (fun t -> (t)) args_ctypes in
          let (n_tl,_) = gather_type_info_var r tlist HpT pos in (*Need to consider about  pos*)
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
