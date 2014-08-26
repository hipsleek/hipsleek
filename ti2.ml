module CP = Cpure
module CF = Cformula
module MCP = Mcpure

open Cprinter
open Globals
open Gen
open Tlutils

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
let mkGt e1 e2 = CP.mkPure (CP.mkGt e1 e2 no_pos)
let mkGte e1 e2 = CP.mkPure (CP.mkGte e1 e2 no_pos)

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

let update_sol_tnt_elem s ann =
  CP.subst_sol_term_ann s ann
  
let tnt_elem_of_ann elem_list ann =
  try List.find (fun (a, _) -> CP.eq_term_ann a ann) elem_list
  with _ -> (ann, [])

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
  trel_id: int;
  termu_lhs: tnt_elem;
  termu_rhs: tnt_elem;
}

let print_call_trel rel = 
  string_of_turel_pure (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)
  
let compare_trel r1 r2 = compare r1.trel_id r2.trel_id
  
let eq_trel r1 r2 = r1.trel_id == r2.trel_id

let dummy_trel = {
  call_ctx = MCP.mix_of_pure (CP.mkTrue no_pos);
  trel_id = -1;
  termu_lhs = (MayLoop, []);
  termu_rhs = (MayLoop, []); 
}
  
let update_call_trel rel ilhs irhs = 
  let _, lhs_args = rel.termu_lhs in
  let _, rhs_args = rel.termu_rhs in
  { rel with
    termu_lhs = ilhs, lhs_args;  
    termu_rhs = irhs, rhs_args; }
    
(* TNT Graph *)
module TNTElem = struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module TNTEdge = struct
  type t = call_trel
  let compare = compare_trel
  let hash = Hashtbl.hash
  let equal = eq_trel
  let default = dummy_trel
end

module TG = Graph.Persistent.Digraph.ConcreteLabeled(TNTElem)(TNTEdge)    
module TGC = Graph.Components.Make(TG)

let graph_of_trels trels =
  let tg = TG.empty in
  let tg = List.fold_left (fun g rel ->
    let src = CP.id_of_term_ann (fst rel.termu_lhs) in
    let dst = CP.id_of_term_ann (fst rel.termu_rhs) in
    let lbl = rel in
    TG.add_edge_e g (TG.E.create src lbl dst)) tg trels
  in tg
  
let print_graph_by_num g = 
  TG.fold_edges (fun s d a -> 
    (string_of_int s) ^ " -> " ^
    (string_of_int d) ^ "\n" ^ a)  g ""
    
let print_edge e = 
  let _, rel, _ = e in
  print_call_trel rel
    
let print_graph_by_rel g = 
  TG.fold_edges (fun s d a -> 
    (print_edge (TG.find_edge g s d)) ^ "\n" ^ a)  g ""
  
let print_scc_num = pr_list string_of_int

let print_scc_list_num scc_list = 
  "scc size = " ^ (string_of_int (List.length scc_list)) ^ "\n" ^ 
  (pr_list (fun scc -> (print_scc_num scc) ^ "\n") scc_list)

let print_scc_array_num scc_array =
  print_scc_list_num (Array.to_list scc_array)  
  
(* A scc is acyclic iff it has only one node and *)
(* this node is not a successor of itself *) 
let is_acyclic_scc g scc =
  match scc with
  | v::[] -> 
    let succ = TG.succ g v in
    not (Gen.BList.mem_eq (==) v succ)
  | _ -> false

(* Returns a set of successors of a node *)
let succ_vertex g v =
  let succ = TG.succ g v in
  List.map (fun sc ->
    let _, rel, _ = TG.find_edge g v sc in
    fst rel.termu_rhs) succ 

(* Returns a set of successors of a scc *)  
let succ_scc g scc =
  List.concat (List.map (succ_vertex g) scc)

let succ_scc_num g scc =
  List.concat (List.map (TG.succ g) scc)

let outside_scc_succ_vertex g scc v =
  let succ = TG.succ g v in
  let outside_scc_succ = Gen.BList.difference_eq (==) succ scc in
  List.map (fun sc ->
    let _, rel, _ = TG.find_edge g v sc in
    fst rel.termu_rhs) outside_scc_succ
    
let outside_succ_scc g scc =
  List.concat (List.map (outside_scc_succ_vertex g scc) scc)
      
let outside_succ_scc_num g scc =
  let succ_scc_num = succ_scc_num g scc in
  Gen.BList.difference_eq (==) succ_scc_num scc
  
let no_outgoing_edge_scc g scc =
  (outside_succ_scc_num g scc) = []   

(* Methods to update rels in graph *)
let update_edge g f_rel e =
  let s, rel, d = e in
  let nrel = f_rel rel in
  TG.add_edge_e (TG.remove_edge_e g e) (s, nrel, d)
  
let update_trel f_ann rel =
  let lhs, _ = rel.termu_lhs in
  let rhs, _ = rel.termu_rhs in 
  update_call_trel rel (f_ann lhs) (f_ann rhs)
  
let map_scc g scc f_ann = 
  let f_edge g e = update_edge g (update_trel f_ann) e 
  in
  let outgoing_scc_edges =
    List.concat (List.map (fun s ->
      let succ = TG.succ g s in
      List.concat (List.map (fun d ->
        TG.find_all_edges g s d) succ)) scc)
  in
  let incoming_scc_edges = 
    List.concat (List.map (fun d ->
      let pred = TG.pred g d in
      List.fold_left (fun a s ->
        if Gen.BList.mem_eq (==) s scc (* Excluding duplicate edges *)
        then a else a @ (TG.find_all_edges g s d)
      ) [] pred) scc)
  in
  List.fold_left (fun g e -> f_edge g e) g (outgoing_scc_edges @ incoming_scc_edges)

(* This method returns all edges within a scc *)    
let find_scc_edges g scc = 
  let find_edges_vertex s =
    let succ = TG.succ g s in
    let scc_succ = Gen.BList.intersect_eq (==) succ scc in
    List.concat (List.map (fun d -> TG.find_all_edges g s d) scc_succ)
  in
  List.concat (List.map (fun v -> find_edges_vertex v) scc)

(* Ranking function synthesis *)
let rank_templ_of_tnt_elem (ann, args) =
  match ann with
  | CP.TermU uid ->
    let templ_id = uid.CP.tu_fname ^ "_r_" ^ (string_of_int uid.CP.tu_id) in 
    let templ_decl = CP.mkTemplate templ_id args no_pos in
    CP.Template templ_decl, templ_id
  | _ -> CP.mkIConst (-1) no_pos, ""

let templ_constr_of_rel rel =
  let src_rank, src_rank_id = rank_templ_of_tnt_elem rel.termu_lhs in
  let dst_rank, dst_rank_id = rank_templ_of_tnt_elem rel.termu_rhs in
  let ctx = mkAnd (MCP.pure_of_mix rel.call_ctx) (CP.cond_of_term_ann (fst rel.termu_lhs)) in
  let dec = mkGt src_rank dst_rank in
  let bnd = mkGte src_rank (CP.mkIConst 0 no_pos) in
  let es = CF.empty_es (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let _ = Template.collect_templ_assume_init es 
    (MCP.mix_of_pure ctx) dec no_pos in
  [src_rank_id; dst_rank_id]
  
let find_ranking_function_scc prog g scc =
  let scc_edges = find_scc_edges g scc in
  let _ = print_endline (pr_list print_edge scc_edges) in
  let inf_templs = List.fold_left (fun a (_, rel, _) -> 
    a @ (templ_constr_of_rel rel)) [] scc_edges in
  let _ = Template.collect_and_solve_templ_assumes_common prog inf_templs in
  
  let src_of_edges = List.map (fun (_, rel, _) -> rel.termu_lhs) scc_edges in
  fun ann ->
    [fst (rank_templ_of_tnt_elem (tnt_elem_of_ann src_of_edges ann))]
  
