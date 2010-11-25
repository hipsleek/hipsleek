(* This is a file for common utilities over Cpure *)



elim_exists (f:formula) : formula


 - with TP.simplifier

(* below from solver.ml *)

and elim_exists_pure w (f, b) lump pos =
  (elim_exists_memo_pure w f pos, List.map (fun (l, f) -> (l, elim_exists_pure_branch w f pos)) b)
      
and elim_exists_memo_pure (w : CP.spec_var list) (f0 : MCP.memo_pure) pos =
  let f_simp w f pos = Util.push_time "elim_exists";
    let f_s = elim_exists_pure_branch(*_debug*) w f pos in
    Util.pop_time "elim_exists"; f_s in
  MCP.memo_pure_push_exists_aux (f_simp,true) w f0 pos
      
and elim_exists_memo_pure_debug w f0 lump_all pos = 
  (print_string ("elim_exists_memo_pure input1: "^(Cprinter.string_of_spec_var_list w)^"\n") ;
  print_string ("elim_exists_memo_pure input2: "^(Cprinter.string_of_memo_pure_formula f0)^"\n") ;
  let r = elim_exists_memo_pure w f0 pos in  
  print_string ("elim_exists_memo_pure output: "^(Cprinter.string_of_memo_pure_formula r)^"\n") ;
  r)
      
and elim_exists_pure_branch (w : CP.spec_var list) (f0 : CP.formula) pos =
  let f = CP.mkExists w f0 None pos in
  let simplified_f = TP.simplify f in
  simplified_f

and elim_exists_pure_branch_debug w f0 = 
  let r = elim_exists_pure_branch w f0 in
  (print_string ("elim_exists_pure_branch input1: "^(Cprinter.string_of_spec_var_list w)^"\n");
  print_string ("elim_exists_pure_branch input2: "^(Cprinter.string_of_pure_formula f0)^"\n");
  r)
      
      
(* --- added 11.05.2008 *)
and entail_state_elim_exists es = 
  let f_prim = elim_exists es.es_formula in
  (* 05.06.08 *)
  (* we also try to eliminate exist vars for which a find a substitution of the form v = exp from the pure part *)
  (*let _ = print_string("[solver.ml, elim_exists_ctx]: Formula before exp exist elim: " ^ Cprinter.string_of_formula f_prim ^ "\n") in*)
  let f = elim_exists_exp f_prim in
  let qvar, base = CF.split_quantifiers f in
  let h, p, fl, b, t = CF.split_components base in
  
  let simpl_p =	
    if !Globals.simplify_pure then 
      MCP.simpl_memo_pure_formula simpl_b_formula simpl_pure_formula p TP.simplify
    else p in
  let simpl_fl = fl (*flows have nothing to simplify to*)in
  let simpl_f = CF.mkExists qvar h simpl_p t simpl_fl b no_pos in
  Ctx{es with es_formula = simpl_f}   (*assuming no change in cache formula*)
      
and elim_exists_ctx_list (ctx0 : list_context) = 
  transform_list_context (entail_state_elim_exists, (fun c-> c)) ctx0

and elim_exists_partial_ctx_list (ctx0 : list_partial_context) = 
  transform_list_partial_context (entail_state_elim_exists, (fun c-> c)) ctx0

      
and elim_exists_ctx (ctx0:context) =
  transform_context entail_state_elim_exists ctx0
      
      
and elim_ante_evars (es:entail_state) : context = 
  let f = push_exists es.es_ante_evars es.es_formula in
  let ef = elim_exists f in
  Ctx {es with es_formula = ef } (*!! maybe unsound unless new clean cache id*)

(* below from cformula *)

and split_quantifiers (f : formula) : (CP.spec_var list * formula) = match f with
  | Exists ({formula_exists_qvars = qvars; 
			 formula_exists_heap =  h; 
			 formula_exists_pure = p; 
			 formula_exists_type = t;
			 formula_exists_flow = fl;
			 formula_exists_branches = b;
			 formula_exists_pos = pos}) -> 
      (qvars, mkBase h p t fl b pos)
  | Base _ -> ([], f)
  | _ -> failwith ("split_quantifiers: invalid argument")

and add_quantifiers (qvars : CP.spec_var list) (f : formula) : formula = match f with
  | Base ({formula_base_heap = h; 
		   formula_base_pure = p; 
		   formula_base_type = t;
		   formula_base_flow = fl;
       formula_base_branches = b;
		   formula_base_pos = pos}) -> mkExists qvars h p t fl b pos
  | Exists ({formula_exists_qvars = qvs; 
			 formula_exists_heap = h; 
			 formula_exists_pure = p; 
			 formula_exists_type = t;
			 formula_exists_flow = fl;
       formula_exists_branches = b;
			 formula_exists_pos = pos}) -> 
	  let new_qvars = U.remove_dups (qvs @ qvars) in
		mkExists new_qvars h p t fl b pos
  | _ -> failwith ("add_quantifiers: invalid argument")

(* 19.05.2008 *)
and remove_quantifiers (qvars : CP.spec_var list) (f : formula) : formula = match f with
  | Base _ -> f
  | Exists ({formula_exists_qvars = qvs; 
			 formula_exists_heap = h; 
			 formula_exists_pure = p; 
			 formula_exists_type = t;
			 formula_exists_flow = fl;
       formula_exists_branches = b;
			 formula_exists_pos = pos}) -> 
	  let new_qvars = (List.filter (fun x -> not(List.exists (fun y -> CP.eq_spec_var x y) qvars)) qvs) in
	  	if (List.length new_qvars == 0) then mkBase h p t fl b pos
	  	else mkExists new_qvars h p t fl b pos
  | _ -> failwith ("add_quantifiers: invalid argument")
(* 19.05.2008 *)

and push_struc_exists (qvars : CP.spec_var list) (f : struc_formula) = 
	List.map (fun c-> match c with
	| EBase b -> EBase {b with formula_ext_exists = b.formula_ext_exists @ qvars}
	| ECase b -> ECase {b with formula_case_exists = b.formula_case_exists @ qvars}
	| EAssume (x,b,y) -> EAssume (x,(push_exists qvars b),y)) f 


and push_exists (qvars : CP.spec_var list) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
	  let new_f1 = push_exists qvars f1 in
	  let new_f2 = push_exists qvars f2 in
	  let resform = mkOr new_f1 new_f2 pos in
		resform
  | _ -> add_quantifiers qvars f

(* 19.05.2008 *)
and pop_exists (qvars : CP.spec_var list) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
	  let new_f1 = pop_exists qvars f1 in
	  let new_f2 = pop_exists qvars f2 in
	  let resform = mkOr new_f1 new_f2 pos in
		resform
  | _ -> remove_quantifiers qvars f

(* below from mc_pure.ml *)

and memo_pure_push_exists (qv:spec_var list) (c:memo_pure):memo_pure = 
  memo_pure_push_exists_aux ((fun w f p-> mkExists w f None p),false) qv c no_pos
    
(* this pushes an exist into a memo-pure;
   it is probably useful consider qv in aset for elimination.
   proc : 
   (i) find rs = overlap between qv and domain(aset)
   (ii) prepare subs: [x->o] or [x->c] or [x->x1] and 
        elim x from aset and other locations
   (ii) subtract qv-dom(subs) and add to exists
   (iii) normalise aset
*)
(* both with_const and no_const needed *)
and memo_pure_push_exists_aux  (f_simp,do_split) (qv:spec_var list) (f0:memo_pure) pos : memo_pure=
  let helper c =
    if (List.length (Util.intersect_fct eq_spec_var qv c.memo_group_fv)=0) then [c] 
    else 
      let nas, drp3 = List.partition (fun (c1,c2)->
					(List.exists (eq_spec_var c1) qv) or (List.exists (eq_spec_var c2) qv)) (get_equiv_eq_with_const c.memo_group_aset) in
      let r,drp1 = List.partition 
	(fun c-> (List.length (Util.intersect_fct eq_spec_var (bfv c.memo_formula) qv))>0) c.memo_group_cons in
      let r = List.filter (fun c-> not (c.memo_status=Implied_R)) r in
      let ns,drp2 = List.partition (fun c-> (List.length (Util.intersect_fct eq_spec_var (fv c) qv))>0) c.memo_group_slice in
      let aset = List.fold_left  ( fun a (c1,c2) -> add_equiv_eq_with_const a c1 c2) empty_var_aset drp3 in 
      let fand1 = List.fold_left (fun a c-> mkAnd a (BForm (c.memo_formula, None)) pos) (mkTrue pos) r in
      let fand2 = List.fold_left (fun a c-> mkAnd a c pos) fand1 ns in
	(* below may contain v=c *)
      let fand3 = List.fold_left (fun a (c1,c2)-> 
				    mkAnd a (BForm ((form_bform_eq_with_const c1 c2),None))  no_pos)
        fand2 nas in
      let fand4 = f_simp qv fand3 pos in
      let r = {memo_group_fv = Util.difference c.memo_group_fv qv;
	       memo_group_changed = true;
	       memo_group_cons = drp1;
	       memo_group_slice = drp2 @(split_conjunctions fand4);
	       memo_group_aset = aset;} in
	if do_split then split_mem_grp r else [r] in
    List.concat (List.map helper f0)  
 

(* below from cpure.ml *)

and elim_exists_with_ineq (f0: formula): formula =
  match f0 with
    | Exists (qvar, qf,lbl, pos) ->
          begin
            match qf with
              | Or (qf1, qf2,lbl2, qpos) ->
                    let new_qf1 = mkExists [qvar] qf1 lbl qpos in
                    let new_qf2 = mkExists [qvar] qf2 lbl qpos in
                    let eqf1 = elim_exists_with_ineq new_qf1 in
                    let eqf2 = elim_exists_with_ineq new_qf2 in
                    let res = mkOr eqf1 eqf2 lbl2 pos in
                    res
              | _ ->
                    let eqqf = elim_exists qf in
                    let min, max = find_bound qvar eqqf in
                    begin
                      match min, max with
                        | Some mi, Some ma -> 
                              let res = ref (mkFalse pos) in
                              begin
                                for i = mi to ma do
                                  res := mkOr !res (apply_one_term (qvar, IConst (i, pos)) eqqf) lbl pos
                                done;
                                !res
                              end
                        | _ -> f0
                    end
          end
    | And (f1, f2, pos) ->
          let ef1 = elim_exists_with_ineq f1 in
          let ef2 = elim_exists_with_ineq f2 in
          mkAnd ef1 ef2 pos
    | Or (f1, f2, lbl, pos) ->
          let ef1 = elim_exists_with_ineq f1 in
          let ef2 = elim_exists_with_ineq f2 in
          mkOr ef1 ef2 lbl pos
    | Not (f1, lbl, pos) ->
          let ef1 = elim_exists_with_ineq f1 in
          mkNot ef1 lbl pos
    | Forall (qvar, qf, lbl, pos) ->
          let eqf = elim_exists_with_ineq qf in
          mkForall [qvar] eqf lbl pos
    | BForm _ -> f0


and elim_exists (f0 : formula) : formula = 
  match f0 with
    | Exists (qvar, qf, lbl, pos) -> begin
	    match qf with
		  | Or (qf1, qf2, lbl2, qpos) ->
			    let new_qf1 = mkExists [qvar] qf1 lbl qpos in
			    let new_qf2 = mkExists [qvar] qf2 lbl qpos in
			    let eqf1 = elim_exists new_qf1 in
			    let eqf2 = elim_exists new_qf2 in
			    let res = mkOr eqf1 eqf2 lbl2 pos in
			    res
		  | _ ->
			    let qf = elim_exists qf in
			    let qvars0, bare_f = split_ex_quantifiers qf in
			    let qvars = qvar :: qvars0 in
			    let conjs = list_of_conjs bare_f in
			    let no_qvars_list, with_qvars_list = List.partition
			      (fun cj -> disjoint qvars (fv cj)) conjs in
			    (* the part that does not contain the quantified var *)
			    let no_qvars = conj_of_list no_qvars_list pos in
			    (* now eliminate the quantified variables from the part that contains it *)
			    let with_qvars = conj_of_list with_qvars_list pos in
			    (* now eliminate the top existential variable. *)
			    let st, pp1 = get_subst_equation_formula with_qvars qvar false in
			    if not (Util.empty st) then
				  let new_qf = subst_term st pp1 in
				  let new_qf = mkExists qvars0 new_qf lbl pos in
				  let tmp3 = elim_exists new_qf in
				  let tmp4 = mkAnd no_qvars tmp3 pos in
				  tmp4
			    else (* if qvar is not equated to any variables, try the next one *)
				  let tmp1 = qf (*elim_exists qf*) in
				  let tmp2 = mkExists [qvar] tmp1 lbl pos in
				  tmp2
	  end
    | And (f1, f2, pos) -> begin
	    let ef1 = elim_exists f1 in
	    let ef2 = elim_exists f2 in
	    let res = mkAnd ef1 ef2 pos in
		res
	  end
    | Or (f1, f2, lbl, pos) -> begin
	    let ef1 = elim_exists f1 in
	    let ef2 = elim_exists f2 in
	    let res = mkOr ef1 ef2 lbl pos in
		res
	  end
    | Not (f1, lbl, pos) -> begin
	    let ef1 = elim_exists f1 in
	    let res = mkNot ef1 lbl pos in
		res
	  end
    | Forall (qvar, qf, lbl, pos) -> begin
	    let eqf = elim_exists qf in
	    let res = mkForall [qvar] eqf lbl pos in
		res
	  end
    | BForm _ -> f0


and get_subst_equation_formula (f0 : formula) (v : spec_var) only_vars: ((spec_var * exp) list * formula) = match f0 with
  | And (f1, f2, pos) ->
	    let st1, rf1 = get_subst_equation_formula f1 v only_vars in
		if not (Util.empty st1) then
		  (st1, mkAnd rf1 f2 pos)
		else
		  let st2, rf2 = get_subst_equation_formula f2 v only_vars in
		  (st2, mkAnd f1 rf2 pos)
  | BForm (bf,lbl) -> get_subst_equation_b_formula bf v lbl only_vars
  | _ -> ([], f0)
        
and get_subst_equation_b_formula (f : b_formula) (v : spec_var) lbl only_vars: ((spec_var * exp) list * formula) = match f with
  | Eq (e1, e2, pos) -> begin
      match e1, e2 with
	    | Var (sv1, _), Var (sv2, _) -> 
              if (eq_spec_var sv1 v) && (not (eq_spec_var sv2 v)) then ([(v, e2)], mkTrue no_pos )
              else if (eq_spec_var sv2 v) && (not (eq_spec_var sv1 v))  then ([(v, e1)], mkTrue no_pos )
              else ([], BForm (f,lbl))
        | Var (sv1, _), _  ->
              if only_vars then ([], BForm (f,lbl))
              else if (eq_spec_var sv1 v) &&(not (List.exists (fun sv -> eq_spec_var sv v) (afv e2))) then ([(v, e2)], mkTrue no_pos )
              else ([], BForm (f,lbl))
        | _ , Var (sv2, _) ->
              if only_vars then ([], BForm (f,lbl))
              else if (eq_spec_var sv2 v) && (not (List.exists (fun sv -> eq_spec_var sv v) (afv e1))) then ([(v, e1)], mkTrue no_pos )
              else ([], BForm (f,lbl))
        | _ ->([], BForm (f,lbl))
    end
  | _ -> ([], BForm (f,lbl))
        
