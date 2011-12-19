open Globals
open Gen
open Cprinter

module CP = Cpure
module CF = Cformula
module TP = Tpdispatcher
module PT = Prooftracer
module CPr = Cprinter

type transition = int * int

type term_reason =
  (* For MayTerm *)
  | Invalid_Measure (* The variance is not well-founded *)
  | Invalid_Transition of transition (* Transition from a lower label to a higher one *)
  | Valid_Transition of transition
  (* For Term *)
  | Valid_Measure (* The variance is well-founded *)
  | Base_Case_Entered (* Program state without loop *)
  (* For NonTerm*)
  | Infinite_Loop_Entered (* Transition to an infinite loop *)
  | Infinite_Loop

(* The termination can only be determined when 
 * a base case or an infinite loop is reached *)  
type term_status =
  | Term of term_reason
  | NonTerm of term_reason
  | MayTerm of term_reason
  | Unreachable of CF.formula list (* Original context causes unreachable *)

type term_res = transition option * term_status

type term_res_table = (loc, term_res list) Hashtbl.t

(* Printing Utilities *)
let pr_transition (trans: transition) =
  let (src, dst) = trans in
  fmt_string "Transition ";
  pr_int src; fmt_string "->"; pr_int dst

let string_of_transition (trans: transition) = 
  poly_string_of_pr pr_transition trans

let pr_term_reason = function
  | Invalid_Measure -> fmt_string "The variance is not given or The given variance is not well-founded."
  | Invalid_Transition _ -> fmt_string "The transition is not valid."
  | Valid_Transition _ -> fmt_string "The transition is valid."
  | Valid_Measure -> fmt_string "The given variance is well-founded."
  | Base_Case_Entered -> fmt_string "The base case is reached."
  | Infinite_Loop_Entered -> fmt_string "An infinite loop is entered."
  | Infinite_Loop -> fmt_string "An infinite loop."

let string_of_term_reason (reason: term_reason) =
  poly_string_of_pr pr_term_reason reason

let pr_term_status = function
  | Term reason -> fmt_string "Terminating: "; pr_term_reason reason
  | NonTerm reason -> fmt_string "Non-terminating: "; pr_term_reason reason
  | MayTerm reason -> fmt_string "May-terminating: "; pr_term_reason reason
  | Unreachable f -> fmt_string "Unreachable state with the context "; 
      pr_wrap_test "" Gen.is_empty (pr_seq "" pr_formula) f

let string_of_term_status = poly_string_of_pr pr_term_status

let pr_opt_transition = function
  | None -> fmt_string ""
  | Some trans -> pr_transition trans

let pr_term_res (trans, status) =
  (*
  fmt_open_vbox 0;
  pr_vwrap "" pr_opt_transition trans;
  pr_vwrap "" pr_term_status status
  *)
  pr_opt_transition trans; 
  fmt_string ": ";
  pr_term_status status

let string_of_term_res = poly_string_of_pr pr_term_res

let pr_term_res_tbl_ele (pos, term_res_list) = 
  (*fmt_open_vbox 0;*)
  pr_vwrap "Result of termination checking at " 
    (fun p -> fmt_string (string_of_loc p)) pos;
  pr_list_vbox_wrap "\n" pr_term_res term_res_list

let pr_term_res_tbl tbl_res = 
  Hashtbl.iter (fun pos res -> pr_term_res_tbl_ele (pos, res)) tbl_res

(* End of Printing Utilities *)

(* For automatic numbering *)
let variance_graph = ref []
let var_checked_list = ref []

let term_collect_info (es: CF.entail_state) (v: CF.ext_variance_formula) =
  variance_graph := !variance_graph @ [(es.CF.es_var_src_ctx, es.CF.es_var_dst_ctx)];
  var_checked_list := !var_checked_list @ [(es, v)]

let term_is_unreachable (es: CF.entail_state) : bool =
  CF.isAnyFalseCtx (CF.Ctx es) 

let equal_pf f1 f2 =
  let r1,_,_ = TP.imply f1 f2 "" false None in
  let r2,_,_ = TP.imply f2 f1 "" false None in
  (*let _ = begin TP.restore_suppress_imply_output_state () end in*)
  r1 & r2

let equal_pf f1 f2 = 
  let pr = CPr.string_of_pure_formula in
  Gen.Debug.no_2 "equal_pf" pr pr string_of_bool equal_pf f1 f2

let compare_pf f1 f2 =
  if (equal_pf f1 f2) then 0
  else
    let pr = CPr.string_of_pure_formula in 
    compare (pr f1) (pr f2)
	
let compare_pf f1 f2 =
  let pr = CPr.string_of_pure_formula in
  Gen.Debug.no_2 "compare_pf" pr pr string_of_int compare_pf f1 f2

module FComp = 
struct
  type t = CP.formula
  let compare = compare_pf
  let hash = Hashtbl.hash
  let equal = equal_pf
end

module IG = Graph.Persistent.Digraph.Concrete(FComp)
module IGO = Graph.Oper.P(IG)
module IGN = Graph.Oper.Neighbourhood(IG)
module IGC = Graph.Components.Make(IG)
module IGP = Graph.Path.Check(IG)

module IComp = 
struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module GS = Graph.Persistent.Digraph.Concrete(IComp)
module GSO = Graph.Oper.P(GS)
module GSN = Graph.Oper.Neighbourhood(GS)
module GSC = Graph.Components.Make(GS)
module GSP = Graph.Path.Check(GS)

(* Termination: Create state transition graph from specification *)
let build_state_trans_graph ls =
  (*print_string ("\ncall graph:\n" ^
	  (List.fold_left (fun rs (f1,f2) -> rs ^ "\n" ^ 
    (CPr.string_of_pure_formula f1) ^ " ->" ^ (CPr.string_of_pure_formula f2)) 
    "" !variance_graph) ^ "\n");*)
  let gr = IG.empty in
  let g = List.fold_left (fun g (f1,f2) ->
    let ng1 = IG.add_vertex g f1 in
	  let ng2 = IG.add_vertex ng1 f2 in
	  let ng3 = IG.add_edge ng2 f1 f2 in
	ng3) gr ls in
  g

let scc_numbering g =
  let scc_list = IGC.scc_list g in
  (*let _ = print_string (pr_list (fun l -> pr_list (CPr.string_of_pure_formula) l) scc_list) in*)
  let scc_list = snd (List.fold_left (fun (n,rs) l -> (n+1, rs @ [(n,l)])) (0,[]) scc_list) in
  let mem e ls = List.exists (fun e1 -> equal_pf e e1) ls in
  let meml ls1 ls2 = List.exists (fun e -> mem e ls2) ls1 in

  let scc_graph = GS.empty in
  let scc_graph = List.fold_left (fun sg (n,_) -> GS.add_vertex sg n) scc_graph scc_list in
  let scc_graph = List.fold_left (fun sg (n,l) ->
	  let neighbours = IGN.list_from_vertices g l in
	  List.fold_left (fun nsg (n1,l1) -> if (meml l1 neighbours) then GS.add_edge nsg n n1 else nsg) sg scc_list 
  ) scc_graph scc_list in

  let (nscc, fscc) = GSC.scc scc_graph in
  (*fun v -> List.fold_left (fun rs (n,l) -> if (mem v l) then (fscc n) else rs) 0 scc_list*)
  fun v -> 
    try
      let (n, _) = List.find (fun (_, l) -> mem v l) scc_list in
      fscc n
    with
      | Not_found -> 0

let variance_numbering ls g =
  if !Globals.term_auto_number then
    let f = scc_numbering g in
    let nf = fun v ->  
      if ((List.length (IGN.list_from_vertex g v)) = 0) then 0 else (f v) in
    let helper ele =
	    let (es,e) = ele in
      if (term_is_unreachable es) then ele
      else 
	      let nes = { es with CF.es_var_label =
		      let user_defined_var_label_lhs = es.CF.es_var_label in
		      match user_defined_var_label_lhs with
		        | None, pos -> (Some (nf es.CF.es_var_src_ctx), pos)
		        | Some i, pos -> 
              if (i = 0 || i = -1) then user_defined_var_label_lhs
			        else (Some (nf es.CF.es_var_src_ctx), pos) } 
        in
	      let ne = {e with CF.formula_var_label =
		      let user_defined_var_label_rhs = e.CF.formula_var_label in
		      match user_defined_var_label_rhs with
		        | None -> Some (nf es.CF.es_var_dst_ctx)
		        | Some i -> 
              if (i = 0 || i = -1) then user_defined_var_label_rhs
			        else Some (nf es.CF.es_var_dst_ctx)}
	      in (nes,ne)
    in List.map (fun e -> helper e) ls
  else ls
(* End of automatic numbering stuff *)

(* Termination: Add function name into names of 
 * its variables to distinguish them - 
 * For a better output 
 * Not capture bounded variables *)
let term_rename_var (pf: CP.formula) (mn: Globals.ident) : CP.formula =
  let f = CP.fv pf in
  let t = List.map (fun (CP.SpecVar (t, i, p)) -> (CP.SpecVar (t, i^"_"^mn, p))) f in
  CP.subst_avoid_capture f t pf

(* To filter the constraints of un-interested variables *)
let term_filter (pf: CP.formula) (sv: CP.spec_var list) : CP.formula =
  let cons_l = CP.list_of_conjs pf in
  let f_l = List.filter (fun f -> Gen.BList.overlap_eq CP.eq_spec_var (CP.fv f) sv) cons_l in
  CP.conj_of_list f_l (CP.pos_of_formula pf)

(* To normalize the target condition *)
(* To build correct transition graph 
 * based on specification *)
let term_normalize_target_condition (es: CF.entail_state) : CF.entail_state =
  let f = List.map (fun (v, _, _) -> v) es.CF.es_var_subst in
  let t = List.map (fun (_, v, mn) ->
    let CP.SpecVar (t, i, p) = v in
    let nid = i ^ "_" ^ mn in
    CP.to_unprimed (CP.SpecVar (t, nid, p))) es.CF.es_var_subst 
  in
  let normalized_ctx_rhs = term_filter (CP.subst_avoid_capture f t es.CF.es_var_dst_ctx) t in
  {es with CF.es_var_dst_ctx = normalized_ctx_rhs} 

(* Update context with information of termination checking *)  
let term_add_source_condition (sc: CP.formula) (mn: Globals.ident) (ctx: CF.context) pos : CF.context =  
  let n_sc = term_rename_var sc mn in
  (* Termination: Add source condition - 
   * The precondition of the initial states *)
	CF.transform_context (fun es ->
    CF.Ctx { es with CF.es_var_src_ctx = CP.mkAnd es.CF.es_var_src_ctx n_sc pos }) ctx

let term_add_target_condition (tc: CP.formula) (ctx: CF.context) pos : CF.context =  
  CF.transform_context (fun es -> 
    CF.Ctx { es with CF.es_var_dst_ctx = CP.mkAnd es.CF.es_var_dst_ctx tc pos }) ctx

let term_add_var_measure (v: CF.ext_variance_formula) (ctx: CF.context) : CF.context =
  CF.transform_context (fun es -> CF.Ctx { es with
    CF.es_var_measures = List.map (fun (e, b) -> e) v.CF.formula_var_measures;
		CF.es_var_label = (v.CF.formula_var_label, v.CF.formula_var_pos) }) ctx 

let term_add_init_ctx (ctx: CF.context) : CF.context =
  CF.transform_context (fun es -> CF.Ctx 
  {es with CF.es_var_orig_ctx = es.CF.es_formula }) ctx

let term_add_var_subst fr_vars to_vars mn sctx pos =
  let var_subst = List.map2 (fun e1 e2 -> (e1, e2, (Cast.unmingle_name mn))) to_vars fr_vars in
  let id = fun x -> x in
  let fs = fun es -> 	CF.Ctx { es with
    CF.es_var_subst = es.CF.es_var_subst @ var_subst;
		CF.es_var_loc = pos } in
  CF.transform_list_failesc_context (id, id, fs) sctx

(* To get unreachable context *)
let rec term_get_unreachable_condition (ctx: CF.list_failesc_context) : CF.formula list =
  List.concat (List.map (fun fctx -> 
    get_unreachable_condition_failesc_ctx fctx) ctx)

and get_unreachable_condition_failesc_ctx (ctx: CF.failesc_context) : CF.formula list = 
  let (_, _, bctx) = ctx in
  List.concat (List.map (fun (_, c) -> get_unreachable_condition_context c) bctx)

and get_unreachable_condition_context (ctx: CF.context) : CF.formula list =
  match ctx with
  | CF.Ctx es -> es.CF.es_var_unreachable_ctx
  | CF.OCtx (c1, c2) -> (get_unreachable_condition_context c1) @
                     (get_unreachable_condition_context c2)  

let term_add_unreachable_state (ctx: CF.list_failesc_context) pos =
  (* Termination: Add a false entail state for * 
   * unreachable recursive call if variance exists *)
	var_checked_list := !var_checked_list @ 
    [({ (CF.false_es CF.mkFalseFlow pos) with
          CF.es_var_loc = pos;
          CF.es_var_unreachable_ctx = term_get_unreachable_condition ctx; },
		  CF.empty_ext_variance_formula)]

let rec term_strip_variance ls = 
  match ls with
    | [] -> []
    | spec::rest -> match spec with
      | CF.EVariance e -> (term_strip_variance e.CF.formula_var_continuation)@(term_strip_variance rest)
      | CF.EBase b -> (CF.EBase {b with CF.formula_ext_continuation = 
          term_strip_variance b.CF.formula_ext_continuation})::(term_strip_variance rest)
      | CF.ECase c -> (CF.ECase {c with CF.formula_case_branches = 
          List.map (fun (cpf, sf) -> (cpf, term_strip_variance sf)) c.CF.formula_case_branches})::(term_strip_variance rest)
      | CF.EInfer i -> (CF.EInfer {i with CF.formula_inf_continuation =
          term_strip_variance i.CF.formula_inf_continuation})::(term_strip_variance rest)
      | _ -> spec::(term_strip_variance rest)

(* Checking the well-foundedness of the loop variance *)    
let term_check_loop_variance (src: CF.entail_state) (dst: CF.ext_variance_formula) f_imply trans pos : term_res = 
  let src_measures = src.CF.es_var_measures in
  let dst_measures = dst.CF.formula_var_measures in
  (*
  let _ = print_string ("es: " ^ (CPr.string_of_entail_state src) ^ "\n") in
  let _ = print_string ("var: " ^ (CPr.string_of_ext_formula (CF.EVariance dst)) ^ "\n") in
  let _ = print_string ("src: " ^ (pr_list CPr.string_of_formula_exp src_measures) ^ "\n") in
  let _ = print_string ("dst: " ^ (pr_list (fun (e, _) ->
    CPr.string_of_formula_exp e)dst_measures) ^ "\n") in
  *)
  (* To handle the lexicographical order *)
	let binding_measures = 
    try List.map2 (fun s d -> (s, d)) src_measures dst_measures
    with _ -> report_error pos ("Termination: Well-foundedness checking: " ^ 
                                "Variances of the state transition do not match \n")
  in

  (* To check the well-foundedness of the lexicographical order *)
  let fun_check_term lst_measures = (* [(s1,d1),(s2,d2)] -> s1=d1 & s1>=lb1 & s2>d2 & s2>=lb2 *) 
		let (_, term_formula) = List.fold_right (fun (s,d) (flag,res) ->
			let lb = match (snd d) with
			  | None -> report_error pos ("Termination: Well-foundedness checking: " ^
                                    "Lower bound is not found \n")
			  | Some exp -> exp in
			let boundedness_checking_formula = CP.BForm ((CP.mkGte s lb pos, None), None) in (* s>=lb*)
			let lexico_ranking_formula = 
			  if flag then CP.BForm ((CP.mkGt (CP.mkSubtract s (fst d) pos) (CP.mkIConst 0 pos) pos, None), None) (* s>d *)
			  else CP.BForm ((CP.mkEq s (fst d) pos, None), None) in (* s=d *)
			let f = CP.mkAnd lexico_ranking_formula boundedness_checking_formula pos in	
			(false, CP.mkAnd f res pos)) lst_measures (true, CP.mkTrue pos)
		in
		
    let (rs, _) = f_imply src term_formula pos in
      (*heap_entail_conjunct_lhs_struc prog false false (CF.Ctx src) [mkEBase term_formula loc] pos None in*)
	  let res = not (CF.isFailCtx rs) in res
	in

  (* To create input for fun_check_term from the binding measure *)
	let lexico_measures = (* [(s1,d1),(s2,d2)] -> [[(s1,d1)],[(s1,d1),(s2,d2)]] *)
		List.fold_right (fun bm res -> [bm]::(List.map (fun e -> bm::e) res)) binding_measures []	
	in

  let res = List.exists (fun lm -> fun_check_term lm) lexico_measures in
	  
  (* A valid measure can ensure the termination *)
  (* In case of an invalid measure, the result 
   * should be MayTerm *)
	if res then (trans, Term Valid_Measure) else (trans, MayTerm Invalid_Measure)

let tem_tbl_res_update (tbl_res: term_res_table ref) pos tres =
  let res = 
    try Hashtbl.find !tbl_res pos
    with _ -> []
  in 
  Hashtbl.replace !tbl_res pos (res@[tres])

let term_check_transition (es: CF.entail_state) (e: CF.ext_variance_formula)
  f_imply (tbl_res: term_res_table ref) : term_res =
  let f_pos = es.CF.es_var_loc in (* Loc of the recursive function call *)
  let v_pos = e.CF.formula_var_pos in (* Loc of the variance *)
  
  let res = 
    if (term_is_unreachable es) then (* Unreachable state *)
      (None, Unreachable es.CF.es_var_unreachable_ctx)
    else (* State transition *)
      let label_err = ("Termination: The variance label is not provided or cannot be inferred.") in
      let var_label_dst = match e.CF.formula_var_label with
	      | None -> report_error v_pos label_err 	    
        | Some i -> i
  	  in

	    let var_label_src = match es.CF.es_var_label with
        | None, pos -> report_error pos label_err
	      | Some i, _ -> i
	    in

      let trans = Some (var_label_src, var_label_dst) in

      (* Case 1: In loop - 
       * The well-foundedness of the variance need to be checked *)
      if (var_label_src = var_label_dst && var_label_dst > 0) then
        term_check_loop_variance es e f_imply trans f_pos
      (* Case 2: Base case reached *)
      else if (var_label_src > var_label_dst && var_label_dst = 0) then
        (trans, Term Base_Case_Entered)
      (* Case 3: Infinite loop is entered *)
      else if (var_label_src > var_label_dst && var_label_dst = -1) then
        (trans, NonTerm Infinite_Loop_Entered)
      (* Case 4: In an infinite loop *)
      else if (var_label_src = var_label_dst && var_label_dst = -1) then
        (trans, NonTerm Infinite_Loop)
      (* Case 5: A valid transition *)
      else if (var_label_src > var_label_dst && var_label_dst > 0) then
        (trans, MayTerm (Valid_Transition (var_label_src, var_label_dst)))
      (* Case 6: An invalid transition *)
      else if (var_label_src < var_label_dst) then
        (trans, MayTerm (Invalid_Transition (var_label_src, var_label_dst)))
      else
        (trans, NonTerm Infinite_Loop)
  in
  tem_tbl_res_update tbl_res f_pos res; res

	
let termination_check f_imply =
  let g = build_state_trans_graph !variance_graph in
	let cl = variance_numbering !var_checked_list g in
  let tbl_res = ref (Hashtbl.create 100) in
  let term_res = List.map (fun (es, e) -> term_check_transition es e f_imply tbl_res) cl in
  (*List.iter (fun r -> pr_term_res r) term_res;*)
  pr_term_res_tbl !tbl_res
