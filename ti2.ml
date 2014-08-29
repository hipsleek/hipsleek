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

(* Temporal Relation at Return *)
type ret_trel = {
  ret_ctx: MCP.mix_formula;
  (* Collect from RHS *)
  termr_fname: ident;
  termr_params: CP.spec_var list;
  termr_lhs: CP.term_ann list;
  termr_rhs: CP.term_ann;
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
  termu_lhs: CP.term_ann;
  termu_rhs: CP.term_ann;
}

let print_call_trel rel = 
  string_of_turel_pure (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)
  
let compare_trel r1 r2 = compare r1.trel_id r2.trel_id
  
let eq_trel r1 r2 = r1.trel_id == r2.trel_id

let dummy_trel = {
  call_ctx = MCP.mix_of_pure (CP.mkTrue no_pos);
  trel_id = -1;
  termu_lhs = MayLoop;
  termu_rhs = MayLoop; 
}
  
let update_call_trel rel ilhs irhs = 
  { rel with
    termu_lhs = ilhs;  
    termu_rhs = irhs; }
    
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
    let src = CP.id_of_term_ann rel.termu_lhs in
    let dst = CP.id_of_term_ann rel.termu_rhs in
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
    rel.termu_rhs) succ 

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
    rel.termu_rhs) outside_scc_succ
  (* List.concat (List.map (fun sc ->                                       *)
  (*   let edges = TG.find_all_edges g v sc in                              *)
  (*   List.map (fun (_, rel, _) -> rel.termu_rhs) edges) outside_scc_succ) *)
    
let outside_succ_scc g scc =
  List.concat (List.map (outside_scc_succ_vertex g scc) scc)
      
let outside_succ_scc_num g scc =
  let succ_scc_num = succ_scc_num g scc in
  Gen.BList.difference_eq (==) succ_scc_num scc
  
let no_outgoing_edge_scc g scc =
  (outside_succ_scc_num g scc) = []   

(* Methods to update rels in graph *)
let update_trel f_ann rel =
  update_call_trel rel (f_ann rel.termu_lhs) (f_ann rel.termu_rhs)

let edges_of_scc g scc =   
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
  in (outgoing_scc_edges @ incoming_scc_edges)
  
let map_scc g scc f_edge = 
  let scc_edges = edges_of_scc g scc in
  List.fold_left (fun g e -> f_edge g e) g scc_edges

let update_edge g f_rel e =
  let s, rel, d = e in
  let nrel = f_rel rel in
  TG.add_edge_e (TG.remove_edge_e g e) (s, nrel, d)  
      
let map_ann_scc g scc f_ann = 
  let f_edge g e = update_edge g (update_trel f_ann) e in 
  map_scc g scc f_edge

(* This method returns all edges within a scc *)    
let find_scc_edges g scc = 
  let find_edges_vertex s =
    let succ = TG.succ g s in
    let scc_succ = Gen.BList.intersect_eq (==) succ scc in
    List.concat (List.map (fun d -> TG.find_all_edges g s d) scc_succ)
  in
  List.concat (List.map (fun v -> find_edges_vertex v) scc)

(* Template Utilies *)
let templ_of_term_ann ann =
  match ann with
  | CP.TermU uid ->
    let templ_id = "t_" ^ uid.CP.tu_fname ^ "_" ^ (string_of_int uid.CP.tu_id) in 
    let templ_exp = CP.mkTemplate templ_id uid.CP.tu_args no_pos in
    CP.Template templ_exp, [templ_exp.CP.templ_id], [Tlutils.templ_decl_of_templ_exp templ_exp]
  | _ -> CP.mkIConst (-1) no_pos, [], []

let add_templ_assume ctx constr inf_templs =
  let es = CF.empty_es (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let es = { es with CF.es_infer_vars_templ = inf_templs } in
  Template.collect_templ_assume_init es ctx constr no_pos

let solve_templ_assume prog templ_decls inf_templs =
  let prog = { prog with Cast.prog_templ_decls = 
    Gen.BList.remove_dups_eq Cast.eq_templ_decl 
      (prog.Cast.prog_templ_decls @ templ_decls) } in
  let res, _, _ = Template.collect_and_solve_templ_assumes_common true prog 
    (List.map CP.name_of_spec_var inf_templs) in
  res

(* Ranking function synthesis *)
let templ_rank_constr_of_rel rel =
  let src_rank, src_templ_id, src_templ_decl = templ_of_term_ann rel.termu_lhs in
  let dst_rank, dst_templ_id, dst_templ_decl = templ_of_term_ann rel.termu_rhs in
  let inf_templs = src_templ_id @ dst_templ_id in
  let ctx = mkAnd (MCP.pure_of_mix rel.call_ctx) (CP.cond_of_term_ann rel.termu_lhs) in
  let dec = mkGt src_rank dst_rank in
  let bnd = mkGte src_rank (CP.mkIConst 0 no_pos) in
  let constr = mkAnd dec bnd in
  let _ = add_templ_assume (MCP.mix_of_pure ctx) constr inf_templs in
  inf_templs, src_templ_decl @ dst_templ_decl
  
let infer_ranking_function_scc prog g scc =
  let scc_edges = find_scc_edges g scc in
  (* let _ = print_endline (pr_list print_edge scc_edges) in *)
  let inf_templs, templ_decls = List.fold_left (fun (id_a, decl_a) (_, rel, _) -> 
    let id, decl = templ_rank_constr_of_rel rel in
    (id_a @ id, decl_a @ decl)) ([], []) scc_edges in
  let inf_templs = Gen.BList.remove_dups_eq CP.eq_spec_var inf_templs in
  let res = solve_templ_assume prog templ_decls inf_templs in
  match res with
  | Sat model ->
    let sst = List.map (fun (v, i) -> (CP.SpecVar (Int, v, Unprimed), i)) model in
    let rank_of_ann = fun ann ->
      let rank_templ, _, _ = templ_of_term_ann ann in
      let rank_exp = Tlutils.subst_model_to_exp sst 
        (CP.exp_of_template_exp rank_templ) in
      [rank_exp]
    in Some rank_of_ann
  | _ -> None

(* Abductive Inference *)
let infer_abductive_icond_edge prog g e =
  let _, rel, _ = e in
  match rel.termu_lhs with
  | TermU uid ->
    let tuc = uid.CP.tu_cond in
    let eh_ctx = mkAnd (MCP.pure_of_mix rel.call_ctx) tuc in
    let abd_templ, abd_templ_id, abd_templ_decl = templ_of_term_ann rel.termu_lhs in
    let abd_cond = mkGte abd_templ (CP.mkIConst 0 no_pos) in
    let abd_ctx = mkAnd eh_ctx abd_cond in    
        
    let tuic = uid.CP.tu_icond in
    let params = List.concat (List.map CP.afv uid.CP.tu_args) in
    let args = CP.args_of_term_ann rel.termu_rhs in
    let abd_conseq = CP.subst_term_avoid_capture (List.combine params args) tuic in
    
    let _ = add_templ_assume (MCP.mix_of_pure abd_ctx) abd_conseq abd_templ_id in
    let oc = !Tlutils.oc_solver in (* Using oc to get optimal solution *)
    let _ = Tlutils.oc_solver := true in 
    let res = solve_templ_assume prog abd_templ_decl abd_templ_id in
    let _ = Tlutils.oc_solver := oc in
    
    begin match res with
    | Sat model -> 
      let sst = List.map (fun (v, i) -> (CP.SpecVar (Int, v, Unprimed), i)) model in
      let abd_exp = Tlutils.subst_model_to_exp sst (CP.exp_of_template_exp abd_templ) in
      let cond = mkGte abd_exp (CP.mkIConst 0 no_pos) in
      (* let _ = print_endline ("ABD: " ^ (!CP.print_formula cond)) in *)
      Some (uid.CP.tu_id, (params, cond))
    | _ -> None end
  | _ -> None    
      
let infer_abductive_icond_vertex prog g v = 
  let self_loop_edges = TG.find_all_edges g v v in
  let abd_conds = List.fold_left (fun a e -> a @ 
    opt_to_list (infer_abductive_icond_edge prog g e)) [] self_loop_edges in
  abd_conds
  
let infer_abductive_icond prog g scc =
  List.concat (List.map (fun v -> infer_abductive_icond_vertex prog g v) scc)
  
(* Update rels in graph with abductive conditions *)
let inst_lhs_trel_abd rel abd_conds =  
  let lhs_ann = rel.termu_lhs in
  let inst_lhs = match lhs_ann with
    | CP.TermU uid -> 
      begin try
        let tid = uid.CP.tu_id in
        let _, abd_cond = List.assoc tid abd_conds in
        let not_abd_cond = mkNot abd_cond in
        
        let tuc = uid.CP.tu_cond in
        let eh_ctx = mkAnd (MCP.pure_of_mix rel.call_ctx) tuc in
        List.concat (List.map (fun (i, c) -> 
          if (is_sat (mkAnd eh_ctx c)) then
            [ CP.TermU { uid with
                CP.tu_id = cantor_pair tid i;
                CP.tu_cond = mkAnd tuc c;
                CP.tu_icond = c; }]
          else []) [(1, abd_cond); (2, not_abd_cond)])
      with Not_found -> [lhs_ann] end
    | _ -> [lhs_ann]
  in inst_lhs
  
let inst_rhs_trel_abd inst_lhs rel abd_conds = 
  let rhs_ann = rel.termu_rhs in
  let cond_lhs = CP.cond_of_term_ann inst_lhs in
  let ctx = mkAnd (MCP.pure_of_mix rel.call_ctx) cond_lhs in
  let inst_rhs = match rhs_ann with
    | CP.TermU uid ->
      let tid = uid.CP.tu_id in
      let tuc = uid.CP.tu_cond in
      let eh_ctx = mkAnd ctx tuc in
      if not (is_sat eh_ctx) then []
      else
        begin try
          let params, abd_cond = List.assoc tid abd_conds in
          let not_abd_cond = mkNot abd_cond in
          let args = uid.CP.tu_args in
          let sst = List.combine params args in
          let abd_cond = CP.subst_term_avoid_capture sst abd_cond in
          let not_abd_cond = CP.subst_term_avoid_capture sst not_abd_cond in
          List.concat (List.map (fun (i, c) -> 
            if (is_sat (mkAnd eh_ctx c)) then
              [ CP.TermU { uid with
                CP.tu_id = cantor_pair tid i;
                CP.tu_cond = mkAnd tuc c;
                CP.tu_icond = c; }]
            else []) [(1, abd_cond); (2, not_abd_cond)])
        with Not_found -> [rhs_ann] end
    | _ -> [rhs_ann]
  in List.map (fun irhs -> update_call_trel rel inst_lhs irhs) inst_rhs
  
let inst_call_trel_abd rel abd_conds =
  let inst_lhs = inst_lhs_trel_abd rel abd_conds in
  let inst_rels = List.concat (List.map (fun ilhs -> 
    inst_rhs_trel_abd ilhs rel abd_conds) inst_lhs) in
  inst_rels

let update_graph_with_icond g scc abd_conds =
  let f_e g e =
    let _, rel, _ = e in
    let inst_rels = inst_call_trel_abd rel abd_conds in
    List.fold_left (fun g rel -> 
      let s = CP.id_of_term_ann rel.termu_lhs in
      let d = CP.id_of_term_ann rel.termu_rhs in
      TG.add_edge_e g (s, rel, d)) g inst_rels
  in  
  let scc_edges = edges_of_scc g scc in
  let g = List.fold_left (fun g v -> TG.remove_vertex g v) g scc in
  List.fold_left (fun g e -> f_e g e) g scc_edges
  
type tnt_case = CP.formula * CP.term_ann * (CP.exp list)  
  
let case_spec_of_graph g =
  let _ = print_endline (print_graph_by_rel g) in
  ()
  
    
  
