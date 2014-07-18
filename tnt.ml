open Globals

module F = Cformula
module P = Cpure
module MCP = Mcpure

type trans_TUnk = {
  trans_ctx: F.formula;
  trans_src: term_ann;
  trans_dst: term_ann; 
}
  
type pw_elem = {
  pw_ident: ident;
  pw_num: int;
  pw_args: P.spec_var list;
  pw_ctx: F.formula;
  pw_cond: P.formula;
}

type pw_trans_elem = 
  | TAnn of term_ann
  | TPwe of pw_elem

type pw_trans_typ = 
  | Ret of pw_elem 
  | Pair of (pw_trans_elem * pw_trans_elem)

type pw_trans = {
  pw_trans_ctx: F.formula;
  pw_trans_rel: pw_trans_typ;
}

let cnt_number = ref 0

let fresh_cnt () =
  cnt_number := !cnt_number + 1;
  !cnt_number
  
let reset_cnt () = cnt_number := 0
  
let diff = Gen.BList.difference_eq P.eq_spec_var

let eq_ident id1 id2 = (String.compare id1 id2) == 0  

let tu_ret_stk: pw_elem Gen.stack = new Gen.stack

let tu_call_stk: trans_TUnk Gen.stack = new Gen.stack
  
let string_of_pw_elem_wo_cond pwe = 
  "TUnk" ^ ("(" ^ pwe.pw_ident ^ "_" ^ (string_of_int pwe.pw_num) ^ ")") ^ (!P.print_svl pwe.pw_args)

let string_of_pw_elem pwe = 
  (!P.print_formula pwe.pw_cond) ^ " -> " ^ 
  (string_of_pw_elem_wo_cond pwe)
    
let string_of_trans_TUnk trans = 
  (!F.print_formula trans.trans_ctx) ^ ": " ^ 
  (string_of_term_ann trans.trans_src) ^ " -> " ^ 
  (string_of_term_ann trans.trans_dst)
  
let string_of_pw_trans_elem = function 
  | TAnn ann -> string_of_term_ann ann
  | TPwe pwe -> string_of_pw_elem_wo_cond pwe

let string_of_pw_trans_typ = function 
  | Ret pwe -> "" 
  | Pair (lhs, rhs) -> 
    (string_of_pw_trans_elem lhs) ^ " -> " ^ 
    (string_of_pw_trans_elem rhs)

let string_of_pw_trans pwt = 
  (!F.print_formula pwt.pw_trans_ctx) ^ ": " ^ 
  (string_of_pw_trans_typ pwt.pw_trans_rel)
  
let id_of_pw_elem pwe = 
  pwe.pw_ident ^ "_" ^ (string_of_int pwe.pw_num)
  
let compare_pw_elem pwe1 pwe2 =
  String.compare (id_of_pw_elem pwe1) (id_of_pw_elem pwe2)
  
let equal_pw_elem pwe1 pwe2 =
  (compare_pw_elem pwe1 pwe2) == 0
  
(* let compare_pw_trans_elem pwt1 pwt2 =                 *)
(*   match pwt1, pwt2 with                               *)
(*   | TPwe pwe1, TPwe pwe2 -> compare_pw_elem pwe1 pwe2 *)
(*   | TAnn ann1, TAnn ann2 ->                           *)

let rec get_pw_elem_context ctx = 
  match ctx with
  | F.Ctx es ->
    begin match es.F.es_var_measures with
    | None -> []
    | Some (TUnk (id, args), _, _) ->
      let args = List.map (fun (t, n, p) -> P.SpecVar (t, n, p)) args in
      let p = F.get_pure es.F.es_formula in
      let simpl_p = P.mkExists_with_simpl 
        Tpdispatcher.simplify_raw 
        (diff (P.fv p) args) 
        p None (P.pos_of_formula p) in
      [{ pw_ident = id;
         pw_num = fresh_cnt ();
         pw_args = args;
         pw_ctx = es.F.es_formula; 
         pw_cond = simpl_p; }]
    | _ -> [] end
  | F.OCtx (c1, c2) ->
    (get_pw_elem_context c1) @ (get_pw_elem_context c2)

let get_pw_elem_partial_context ctx = 
  let _, ctx_lst = ctx in
  List.concat (List.map (fun (_, c) -> get_pw_elem_context c) ctx_lst)

let get_pw_elem_list_partial_context ctx =
  reset_cnt ();
  List.concat (List.map get_pw_elem_partial_context ctx)

let rec grp_pw_elem_by_id pwt = 
  match pwt with
  | [] -> []
  | pw::pwr ->
    let id = pw.pw_ident in
    let same_grp, others = List.partition (fun pw -> 
      eq_ident id pw.pw_ident) pwr in
    (id, pw::same_grp)::(grp_pw_elem_by_id others) 
    
let build_trans_TUnk ctx src dst = 
  { trans_ctx = ctx; trans_src = src; trans_dst = dst; } 
  
let build_tu_rels_with_trans unsat pw_elem_ls trans_ls =
  let get_feasible_pwe_rhs lhs dst ctx =
    match dst with
    | TUnk (idd, to_args) ->
      let to_args = List.map (fun (t, n, p) -> P.SpecVar (t, n, p)) to_args in
      let rhs_pw_elems = List.filter (fun pwe -> eq_ident pwe.pw_ident idd) pw_elem_ls in
      List.fold_left (fun acc rhs ->
        let fr_args = rhs.pw_args in 
        let subst_cond = P.subst_avoid_capture fr_args to_args rhs.pw_cond in
        let enhanced_rhs_ctx = F.mkAnd_pure ctx (MCP.mix_of_pure subst_cond) no_pos in
        if unsat enhanced_rhs_ctx then acc
        else
          let subst_rhs = { rhs with 
            pw_args = to_args;
            pw_ctx = F.subst_avoid_capture fr_args to_args rhs.pw_ctx;
            pw_cond = subst_cond; } in 
          acc @ [Pair (lhs, TPwe subst_rhs)]) [] rhs_pw_elems
    | _ -> [Pair (lhs, TAnn dst)]
  in
  let add_ctx_to_trans_typ_list ctx =
    List.map (fun t -> { pw_trans_ctx = ctx; pw_trans_rel = t; })
  in 
  let helper trans =
    let ctx = trans.trans_ctx in
    match trans.trans_src with
    | TUnk (ids, _) ->
      let lhs_pw_elems = List.filter (fun pwe -> eq_ident pwe.pw_ident ids) pw_elem_ls in
      let feasible_pw_trans = List.fold_left (fun acc lhs ->
        let enhanced_lhs_ctx = F.mkAnd_pure ctx (MCP.mix_of_pure lhs.pw_cond) no_pos in
        if unsat enhanced_lhs_ctx then acc
        else
          let rels = get_feasible_pwe_rhs (TPwe lhs) trans.trans_dst enhanced_lhs_ctx in 
          acc @ rels) [] lhs_pw_elems in 
      add_ctx_to_trans_typ_list ctx feasible_pw_trans  
    | _ -> add_ctx_to_trans_typ_list ctx (get_feasible_pwe_rhs (TAnn trans.trans_src) trans.trans_dst ctx)
  in List.concat (List.map helper trans_ls)
  
(* TNT Graph *)
module PwElem = struct
  type t = pw_trans_elem
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end
module PG = Graph.Persistent.Digraph.Concrete(PwElem)
module PGO = Graph.Oper.P(PG)
module PGC = Graph.Components.Make(PG)
module PGP = Graph.Path.Check(PG)
module PGN = Graph.Oper.Neighbourhood(PG)
module PGT = Graph.Topological.Make(PG)
  
let process_infer unsat = 
  let pw_elem_ls = tu_ret_stk # get_stk in
  let trans_TUnk_ls = tu_call_stk # get_stk in
  let tu_rels = build_tu_rels_with_trans unsat pw_elem_ls trans_TUnk_ls in
  
  let _ = print_endline (pr_list string_of_pw_elem pw_elem_ls) in
  (* let _ = print_endline (pr_list string_of_trans_TUnk trans_TUnk_ls) in *)
  let _ = print_endline (pr_list string_of_pw_trans tu_rels) in
  ()
