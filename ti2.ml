module CP = Cpure
module CF = Cformula
module MCP = Mcpure

open Cprinter
open Globals
open Gen

(* Auxiliary methods *)
let diff = Gen.BList.difference_eq CP.eq_spec_var

let om_simplify = Omega.simplify

let eq_str s1 s2 = String.compare s1 s2 == 0

let simplify f args = 
  let bnd_vars = diff (CP.fv f) args in
  if bnd_vars == [] then f else
    CP.mkExists_with_simpl om_simplify (* Tpdispatcher.simplify_raw *)
      (diff (CP.fv f) args) f None (CP.pos_of_formula f)
  
let is_sat f = Tpdispatcher.is_sat_raw (MCP.mix_of_pure f)

let mkAnd f1 f2 = CP.mkAnd f1 f2 no_pos

let mkNot f = CP.mkNot f None no_pos

let rec partition_by_key key_of key_eq ls = 
  match ls with
  | [] -> []
  | e::es ->
    let ke = key_of e in 
    let same_es, other_es = List.partition (fun e -> key_eq ke (key_of e)) es in
    (ke, e::same_es)::(partition_by_key key_of key_eq other_es)
    
(* This method returns a unique number for (a, b) *)
(* It is used to generate num for new instantiated TermU *)    
let cantor_pair a b = (a + b) * (a + b + 1) / 2 + b

(* Element of Temporal Relation *)
type tnt_elem = CP.term_ann * CP.exp list

let compare_tnt_elem e1 e2 =
  CP.compare_term_ann (fst e1) (fst e2)
  
let eq_tnt_elem e1 e2 =
  compare_tnt_elem e1 e2 == 0
  
let print_tnt_elem = string_of_tnt_elem

let update_sol_tnt_elem s (v, l) =
  (CP.subst_sol_term_ann s v, l)

(* Temporal Relation at Return *)
type ret_trel = {
  ret_ctx: MCP.mix_formula;
  (* Collect from RHS *)
  termr_fname: ident;
  termr_params: CP.spec_var list;
  termr_lhs: tnt_elem list;
  termr_rhs: tnt_elem;
}

let print_ret_trel rel = 
  string_of_trrel_pure (rel.ret_ctx, rel.termr_lhs, rel.termr_rhs)
  
type trrel_sol = 
  | Base of CP.formula
  | Rec of CP.formula (* Recursive case *)
  | MayTerm of CP.formula (* Both base and rec cases may be reachable from this case *)
  
let print_trrel_sol s = 
  let pr = !CP.print_formula in
  match s with
  | Base c -> (pr c) ^ "@B"
  | Rec c -> (pr c) ^ "@R"
  | MayTerm c -> (pr c) ^ "@ML"

let trans_trrel_sol f = function
  | Base c -> Base (f c)
  | Rec c -> Rec (f c)
  | MayTerm c -> MayTerm (f c)

let fold_trrel_sol f = function
  | Base c -> 
    let cs = f c in
    List.map (fun c -> Base c) cs 
  | Rec c -> 
    let cs = f c in
    List.map (fun c -> Rec c) cs 
  | MayTerm c -> 
    let cs = f c in
    List.map (fun c -> MayTerm c) cs 

let simplify_trrel_sol = trans_trrel_sol om_simplify

let split_disj_trrel_sol s =
  fold_trrel_sol CP.split_disjunctions s
     
let is_base = function
  | Base _ -> true
  | _ -> false

let is_rec = function
  | Rec _ -> true
  | _ -> false

let is_mayterm = function
  | MayTerm _ -> true
  | _ -> false

let get_cond = function
  | Base c -> c
  | Rec c -> c
  | MayTerm c -> c

let get_rec_conds conds = 
  List.map get_cond (List.filter is_rec conds)  
  
(* Temporal Relation at Call *)
type call_trel = {
  call_ctx: MCP.mix_formula;
  termu_lhs: tnt_elem;
  termu_rhs: tnt_elem;
}

let print_call_trel rel = 
  string_of_turel_pure (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)
  
let update_call_trel rel ilhs irhs = 
  let _, lhs_args = rel.termu_lhs in
  let _, rhs_args = rel.termu_rhs in
  { rel with
    termu_lhs = ilhs, lhs_args;  
    termu_rhs = irhs, rhs_args; }
    
(* TNT Graph *)
module TNTElem = struct
  type t = tnt_elem
  let compare = compare_tnt_elem
  let hash = Hashtbl.hash
  let equal = eq_tnt_elem
end

module TNTEdge = struct
  type t = CP.formula
  let compare f1 f2 = if (CP.eq_pure_formula f1 f2) then 0 else 1 
  let hash = Hashtbl.hash
  let equal = CP.eq_pure_formula
  let default = CP.mkTrue no_pos
end

module TG = Graph.Persistent.Digraph.ConcreteLabeled(TNTElem)(TNTEdge)    
module TGC = Graph.Components.Make(TG)  
module TGN = Graph.Oper.Neighbourhood(TG)

let graph_of_trels trels =
  let tg = TG.empty in
  let tg = List.fold_left (fun g rel ->
    let src = rel.termu_lhs in
    let dst = rel.termu_rhs in
    let lbl = MCP.pure_of_mix rel.call_ctx in
    TG.add_edge_e g (TG.E.create src lbl dst)) tg trels
  in tg
  
let print_scc = pr_list print_tnt_elem

let print_scc_list scc_list = 
  "scc size = " ^ (string_of_int (List.length scc_list)) ^ "\n" ^ 
  (pr_list (fun scc -> (print_scc scc) ^ "\n") scc_list)

let print_scc_array scc_array =
  print_scc_list (Array.to_list scc_array)
  
let print_graph g = 
  TG.fold_edges (fun s d a -> 
    (print_tnt_elem s) ^ " -> " ^
    (print_tnt_elem d) ^ "\n" ^ a)  g ""
  
(* A scc is acyclic iff it has only one node and *)
(* this node is not a successor of itself *) 
let is_acyclic_scc g scc =
  match scc with
  | v::[] -> 
    let succ = TG.succ g v in
    not (Gen.BList.mem_eq eq_tnt_elem v succ)
  | _ -> false

(* Returns a set of successors of a scc *)  
let succ_scc g scc = 
  List.concat (List.map (TG.succ g) scc)
  
let outside_succ_scc g scc =
  let succ_scc = succ_scc g scc in
  Gen.BList.difference_eq eq_tnt_elem succ_scc scc
  
(* let no_outgoing_edge_scc g scc =                                    *)
(*   let no_outgoing_edge_node v =                                     *)
(*     let succ = TG.succ g v in                                       *)
(*     List.for_all (fun s -> Gen.BList.mem_eq eq_tnt_elem s scc) succ *)
(*   in                                                                *)
(*   List.for_all (fun v -> no_outgoing_edge_node v) scc               *)
let no_outgoing_edge_scc g scc =
  (outside_succ_scc g scc) = []   
  
let map_scc g scc f = 
  TG.map_vertex (fun v ->
    if Gen.BList.mem_eq eq_tnt_elem v scc then f v
    else v) g
  

  