open Globals
open Cast
open Cformula
open Cprinter
open Gen

module CP = Cpure
module CF = Cformula
module TP = Tpdispatcher

let variance_graph = ref []
let var_checked_list = ref []

let update_graph vg vc = 
  variance_graph := !variance_graph @ [vg];
  var_checked_list := !var_checked_list @ [vc]

let rec equalpf_a f1 f2 =
  let _ = begin 
    TP.push_suppress_imply_output_state ();
    TP.suppress_imply_output () 
  end in
  let r1,_,_ = TP.imply f1 f2 "" false None in
  let r2,_,_ = TP.imply f2 f1 "" false None in
  let _ = begin TP.restore_suppress_imply_output_state () end in
  r1 & r2

and equalpf f1 f2 = 
  let pr = Cprinter.string_of_pure_formula in
  Gen.Debug.no_2 "equalpf" pr pr string_of_bool equalpf_a f1 f2

and comparepf_a f1 f2 =
  let _ = begin 
    TP.push_suppress_imply_output_state ();
    TP.suppress_imply_output () 
  end in
  let r1,_,_ = TP.imply f1 f2 "" false None in
  let r2,_,_ = TP.imply f2 f1 "" false None in
  let _ = begin TP.restore_suppress_imply_output_state () end in
  if (r1 & r2) then 0
  else compare (Cprinter.string_of_pure_formula f1) (Cprinter.string_of_pure_formula f2)
	
and comparepf f1 f2 =
  let pr = Cprinter.string_of_pure_formula in
  Gen.Debug.no_2 "comparepf" pr pr string_of_int comparepf_a f1 f2

module FComp = 
struct
  type t = CP.formula
  let compare = comparepf
  let hash = Hashtbl.hash
  let equal = equalpf
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

(* Termination: Create state transition graph *)
let build_state_trans_graph ls =
  (*print_string ("\ncheck_prog: call graph:\n" ^
	(List.fold_left (fun rs (f1,f2) -> rs ^ "\n" ^ (Cprinter.string_of_pure_formula f1) ^ " ->" ^ (Cprinter.string_of_pure_formula f2)) "" !Solver.variance_graph) ^ "\n");*)
  let gr = IG.empty in
  let g = List.fold_left (fun g (f1,f2) ->
    let ng1 = IG.add_vertex g f1 in
	  let ng2 = IG.add_vertex ng1 f2 in
	  let ng3 = IG.add_edge ng2 f1 f2 in
	ng3) gr ls in
  g

let scc_numbering g =
  let scc_list = IGC.scc_list g in
  let scc_list = snd (List.fold_left (fun (n,rs) l -> (n+1, rs @ [(n,l)])) (0,[]) scc_list) in
  let mem e ls = List.exists (fun e1 -> equalpf e e1) ls in
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
    let nf = fun v -> if ((List.length (IGN.list_from_vertex g v)) = 0) then 0 else (f v) in
    let helper ele =
	    let (es,e) = ele in
	    let nes = {es with CF.es_var_label =
		    let user_defined_var_label_lhs = es.CF.es_var_label in
		    match user_defined_var_label_lhs with
		      | None -> Some (nf es.CF.es_var_ctx_lhs)
		      | Some i -> 
              if (i = 0 || i = -1) then user_defined_var_label_lhs
			        else Some (nf es.CF.es_var_ctx_lhs)} in
	    let ne = {e with CF.formula_var_label =
		    let user_defined_var_label_rhs = e.CF.formula_var_label in
		    match user_defined_var_label_rhs with
		      | None -> Some (nf es.CF.es_var_ctx_rhs)
		      | Some i -> 
              if (i = 0 || i = -1) then user_defined_var_label_rhs
			        else Some (nf es.CF.es_var_ctx_rhs)}
	    in (nes,ne)
    in List.map (fun e -> helper e) ls
  else ls

let rec heap_entail_variance
	  (prog : prog_decl) 
	  (es : entail_state) 
	  (e : ext_variance_formula) =
  let pr1 = Cprinter.string_of_entail_state in
  let pr2 e = pr_list (pr_pair Cprinter.string_of_formula_exp (pr_option Cprinter.string_of_formula_exp)) e.formula_var_measures in
  Gen.Debug.no_2 "heap_entail_variance" pr1 pr2 pr_no (fun _ _ -> heap_entail_variance_x prog es e) es e

and heap_entail_variance_x
	  (prog : prog_decl) 
	  (es : entail_state) 
	  (e : ext_variance_formula) = ()
(*
  (*let loc = e.formula_var_pos in*)
  let loc = es.es_var_loc in
  let ctx = (CF.Ctx es) in

  if CF.isAnyFalseCtx ctx then (* Unreachable state *)
    let _ = Debug.print_info "Termination" "Unreachable state" loc in
    let _ = if !print_proof then 
      Prooftracer.push_term_checking loc false;
      Prooftracer.push_pop_term_unreachable_context es.CF.es_var_ctx_lhs;
      Prooftracer.pop_div () in
	  ()
  else
	let _ = if !print_proof then Prooftracer.push_term_checking loc true in
	let string_of_es_var_measure el = "[" ^ (List.fold_left (fun rs e ->
		let str = Cprinter.string_of_formula_exp e in
		if rs = "" then str else rs ^ ", " ^ str) "" el) ^ "]" in

  	let _ = Debug.print_info "Termination" 
	  ("Transition from state " ^ (Cprinter.string_of_pure_formula es.es_var_ctx_lhs) ^ 
		  " to state " ^ (Cprinter.string_of_pure_formula es.es_var_ctx_rhs)) loc in

	let var_label_rhs = match e.formula_var_label with
	  | None -> report_error no_pos ("Termination: error with auto-numbering variance label - the variance does not have a label \n")
	  | Some i -> i
  	in

	let var_label_lhs = match es.es_var_label with
	  | None -> report_error no_pos ("Termination: error with auto-numbering variance label - the variance does not have a label \n")
	  | Some i -> i
	in
	
    (*if (var_label_lhs = var_label_rhs && var_label_rhs > 0) then*) (* Case 1: In loop *)
    if (var_label_lhs = var_label_rhs) then 
	  let _ = print_string ("Termination: loop at state (" ^ (string_of_int var_label_lhs) ^ ") " ^ 
		  (Cprinter.string_of_pure_formula es.es_var_ctx_rhs)) in
	  let lhs_measures = es.es_var_measures in
	  let rhs_measures = e.formula_var_measures in
	  let rec binding lhs_m rhs_m =
		if ((List.length lhs_m) != (List.length rhs_m)) then
		  report_error no_pos ("Termination: variance checking: LHS does not match RHS \n")
		else match lhs_m with
		  | [] -> []
		  | h::t -> (h, (List.hd rhs_m))::(binding t (List.tl rhs_m)) in
	  let binding_measures = binding lhs_measures rhs_measures in
	  
	  let fun_check_term lst_measures = (* [(m1,n1),(m2,n2)] -> m1=n1 & m1>=lb1 & m2>n2 & m2>=lb2 *) 
		let (_, term_formula) = List.fold_right (fun (l,r) (flag,res) ->
			let lower_bound = match (snd r) with
			  | None -> report_error no_pos ("Termination: variance checking: error with lower bound in termination checking \n")
			  | Some exp -> exp in
			let boundedness_checking_formula = CP.BForm ((CP.mkGte l lower_bound loc, None), None) in
			let lexico_ranking_formula = 
			  if flag then CP.BForm ((CP.mkGt (CP.mkSubtract l (fst r) loc) (CP.mkIConst 0 loc) loc, None), None)
			  else CP.BForm ((CP.mkEq l (fst r) loc, None), None) in
			let f = CP.mkAnd lexico_ranking_formula boundedness_checking_formula loc in	
			(false, CP.mkAnd f res loc)) lst_measures (true, CP.mkTrue loc)
		in
		(*let _ = print_string ("\nTermination: term checking formula: "^(Cprinter.string_of_struc_formula [mkEBase (snd term_formula) loc])) in*)
        let _ = if !print_proof then Prooftracer.push_entail_variance (es.CF.es_formula, term_formula) in     
		(*let _ = begin Tpdispatcher.push_suppress_imply_output_state ();
         * Tpdispatcher.suppress_imply_output () end in*)
		let (rs, _) = (heap_entail_conjunct_lhs_struc prog false false ctx [mkEBase term_formula loc] no_pos None) in
		(*let _ = begin Tpdispatcher.restore_suppress_imply_output_state () end
         * in*)
        let _ = if !print_proof then Prooftracer.pop_div(); in 
        
	  	let res = not (CF.isFailCtx rs) in
		(*let _ = if !print_proof then Prooftracer.push_pop_entail_variance
         * (es.CF.es_formula, term_formula, res) in*)
		res
	  in

	  let lexico_measures = (* [(m1,n1),(m2,n2)] -> [[(m1,n1)],[(m1,n1),(m2,n2)]] *)
		List.fold_right (fun bm res -> [bm]::(List.map (fun e -> bm::e) res)) binding_measures []	
	  in
	  (*
		let lst_res = List.map (fun lm -> fun_check_term lm) lexico_measures in
		if (List.exists (fun (rs, prf) -> let _ = Prooftracer.log_proof prf in not (CF.isFailCtx rs)) lst_res) then
	  *)
	  let res = List.exists (fun lm -> fun_check_term lm) lexico_measures in
	  
	  let _ = if !print_proof then Prooftracer.push_pop_entail_variance_res res in
	  let _ = if !print_proof then begin Prooftracer.pop_div (); end in
	  
	  if res then
		Debug.print_info "Termination" 
			    ("Checking termination by variance " ^ (string_of_es_var_measure es.es_var_measures) ^ " : ok") loc
	  else
	    Debug.print_info "Termination" 
			    ("Checking termination by variance " ^ (string_of_es_var_measure es.es_var_measures) ^ " : failed") loc
    
    (*
	else if (var_label_lhs = var_label_rhs && var_label_rhs = 0) then (* Case 2: Base case *)
	  Debug.print_info "Termination" ("terminating state " ^ (string_of_int var_label_lhs)) loc
	else if (var_label_lhs = var_label_rhs && var_label_rhs = -1) then (* Case 3: Non-terminating cases *)
	  Debug.print_info "Termination" ("non-terminating state ") loc
	  *)
    else if (var_label_lhs > var_label_rhs) then (* Case 4: Loop transition: state transition at boundary of loop *)
	  (* Already checked UNSAT(D) at heap_entail_one_context_struc *)
      if (var_label_rhs > 0) then
	      Debug.print_info "Termination" ("Transition from variance " ^ (string_of_int var_label_lhs) ^ 
		      " to " ^ (string_of_int var_label_rhs) ^ " : safe") loc
      else if (var_label_rhs == 0) then
        Debug.print_info "Termination" ("Terminating state " ^ (string_of_int var_label_rhs)) loc
      else 
        Debug.print_info "Termination" ("Non-terminating state " ^ (string_of_int var_label_rhs)) loc

	else (* Case 5: Reverved loop transtion: might lead to non-terminating case *)
	    Debug.print_info "Termination" ("Transition from variance " ^ (string_of_int var_label_lhs) ^ 
		  " to " ^ (string_of_int var_label_rhs) ^ " : invalid") loc
*)

let termination_check prog = 
  let g = build_state_trans_graph !variance_graph in
	let cl = variance_numbering !var_checked_list g in
  if (List.length cl) != 0 then
    let _ = if !Globals.print_proof then begin Prooftracer.push_term (); end in
    let _ = List.iter (fun (es,e) -> heap_entail_variance prog es e) cl in
    if !Globals.print_proof then begin Prooftracer.pop_div (); end 
  else ()


(* Termination: Add function name into names of 
 * its variables to distinguish them - 
 * For a better output *)
let term_rename_var (f: CP.formula) (mn: Globals.ident) : CP.formula =
  let f_formula = fun f -> None in
	let f_b_formula (pf, il) = match pf with
    | CP.BVar (CP.SpecVar (t, i, p), loc) -> 
        Some ((CP.BVar ((CP.SpecVar (t, i^"_"^mn, p)), loc)), il)
    | _ -> None
	in
	let f_exp = function
    | CP.Var (CP.SpecVar (t,i,p), loc) -> 
        Some (CP.Var ((CP.SpecVar (t, i^"_"^mn, p)), loc))
    | _ -> None
	in
  CP.transform_formula (true, true, f_formula, f_b_formula, f_exp) f

let term_add_source_condition (sc: CP.formula) (mn: Globals.ident) (ctx: CF.context) pos : CF.context =  
  let n_sc = term_rename_var sc mn in
  (* Termination: Add source condition - 
   * The precondition of the initial states *)
	CF.transform_context (fun es ->
    CF.Ctx { es with CF.es_var_ctx_lhs = CP.mkAnd es.CF.es_var_ctx_lhs n_sc pos }) ctx

let term_add_measure (v: CF.ext_variance_formula) (ctx: CF.context) : CF.context =
  CF.transform_context (fun es -> CF.Ctx { es with
    CF.es_var_measures = List.map (fun (e, b) -> e) v.CF.formula_var_measures;
		CF.es_var_label = v.CF.formula_var_label }) ctx 




