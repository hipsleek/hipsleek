open Globals

open Cpure
(*
 -eprune = espec + ememo + eslice
 -espec enables specialization 
 -ememo will enable memoizing
 -eslice will enable slicing
*)
type var_aset = spec_var Util.eq_set 

let empty_var_aset = Util.empty_a_set_eq eq_spec_var 


(* with const for get_equiv_eq + form_formula__eq *)
(* converts an equiv set into a formula *)
let fold_aset (f:var_aset):formula = 
  List.fold_left (fun a (c1,c2)->  mkAnd (form_formula_eq_with_const c1 c2) a no_pos) 
                 (mkTrue no_pos) (get_equiv_eq_with_const f)
                 
type memo_pure = memoised_group list
 
and memoised_group = {
    memo_group_fv : spec_var list;
    memo_group_changed: bool;
    memo_group_cons : memoised_constraint list;(*used for pruning*)
    memo_group_slice: formula list; (*constraints that can not be used for pruning but belong to the current slice non-the less*)
    memo_group_aset : var_aset;
    }

and memoised_constraint = {
    (*memo_formula_mut: b_formula ref;
    memo_status_mut : prune_status ref ;*)
    memo_formula : b_formula;
    memo_status : prune_status }

and prune_status = 
  (*| Fail_prune        (*constraint that is contradicted by the current state*)*)
  | Implied_R      (*constraint that is superseeded by other constraints in the current state*)
  | Implied_P
  | Implied_N
  (*| Implied of bool*)         (*constraint that can be deducted from the current state- including predicate invariants ,
                                  the bool indicates the source true: orig 
                                                                false: invariant*)
  (*| Unknown_prune of bool*)   (*pruning constraint with unknown status, -bool indicates if it comes from an invariant*)
  
let print_mp_f = ref (fun (c:memo_pure)-> " printing not initialized")
let print_mc_f = ref (fun (c:memoised_constraint)-> "printing not initialized")
let print_sv_f = ref (fun (c:spec_var)-> "spec var printing not initialized")
let print_bf_f = ref (fun (c:b_formula)-> "b formula printing not initialized")
let print_p_f_f = ref (fun (c:formula)-> " formula printing not initialized")
let print_exp_f = ref(fun (c:exp) -> "exp_printing") 

let print_p_f_l l = String.concat "; " (List.map !print_p_f_f l)

let print_alias_set aset = Util.string_of_eq_set !print_sv_f aset
    
let rec mfv (m: memo_pure) : spec_var list = Util.remove_dups_f (List.concat (List.map (fun c-> c.memo_group_fv) m)) eq_spec_var

and pcond_fv (p:memoised_constraint) : spec_var list = bfv p.memo_formula

and isConstMConsTrue r = isConstBTrue  r.memo_formula
 (* | Fail_prune -> isConstBFalse r.memo_formula*)

  
and isConstMConsFalse r = isConstBFalse  r.memo_formula
 (* | Fail_prune -> isConstBTrue r.memo_formula*)
  
and isConstMTrue f = 
  match (List.length f) with
    | 0 -> true
    | 1 ->
        let r = List.hd f in
        (match ((List.length r.memo_group_cons),(List.length r.memo_group_slice)) with
            | 0,1 -> isConstTrue (List.hd r.memo_group_slice) && (Util.is_empty_aset_eq r.memo_group_aset)
            | 1,0 -> isConstMConsTrue (List.hd r.memo_group_cons) && (Util.is_empty_aset_eq r.memo_group_aset)
            | _ -> false)
    | _ -> false
      
and isConstGroupTrue (f:memoised_group) : bool = match f.memo_group_slice with
  | [] -> f.memo_group_cons == [] && (Util.is_empty_aset_eq f.memo_group_aset) 
  | x::[] -> f.memo_group_cons == [] && (Util.is_empty_aset_eq f.memo_group_aset) && (isConstTrue x)
  | _ -> false
  
      
and isConstMFalse f = 
  match (List.length f) with
    | 1 ->
        let r = List.hd f in
        (match ((List.length r.memo_group_cons),(List.length r.memo_group_slice)) with
            | 0,1 -> isConstFalse (List.hd r.memo_group_slice)&& (Util.is_empty_aset_eq r.memo_group_aset)
            | 1,0 -> isConstMConsFalse (List.hd r.memo_group_cons) && (Util.is_empty_aset_eq r.memo_group_aset)
            | _ -> false)
    | _ -> false
  
  
let rec filter_mem_fct fct lst =  
  let l = List.map (fun c->{c with memo_group_cons = List.filter fct c.memo_group_cons}) lst in
    List.filter (fun c-> not (isConstGroupTrue c)) l
      
and filter_mem_triv lst = 
  filter_mem_fct (fun c->match c.memo_formula with 
		    | Lte (e1,e2,l) 
		    | Gte (e1,e2,l) 
		    | Eq  (e1,e2,l) 
		    | Neq  (e1,e2,l) -> not (eqExp e1 e2)
		    | _ -> true) lst
    
and group_mem_by_fv (lst: memo_pure):memo_pure = 
  let n_l = List.fold_left (fun a d-> 
			      let n_l = List.map (fun c->((bfv c.memo_formula),[(Some c, None,None)])) d.memo_group_cons in
			      let n_l_f = List.map (fun f->((fv f),[(None, Some f, None)])) d.memo_group_slice in
			      let n_l_a = (fun f -> ((get_elems_eq f),[(None, None, Some f )])) d.memo_group_aset in
				n_l_a :: (n_l @ n_l_f @ a)) [] lst in
    
  let r = List.fold_left (fun acc (v_list, mem) -> 
			    let l_merged, l_unmerged = List.partition (fun (v_l,_)-> 
									 (List.length (Util.intersect_fct eq_spec_var v_l v_list))>0) acc in
			    let l_v,l_m = List.fold_left (fun (a1,a2)(c1,c2)-> (a1@c1,c2@a2)) (v_list,mem) l_merged in
			      ((Util.remove_dups_f l_v eq_spec_var),l_m)::l_unmerged ) [] n_l in
    
    List.map (fun (v_l,m_l)-> 
		let mc_l, f_l,a_l = List.fold_left (fun (a1,a2,a3) c -> match c with
						      | None, Some f , None -> (a1,f::a2,a3)
						      | Some f, None , None -> (f::a1,a2,a3)
						      | None, None, Some f -> (a1,a2,Util.merge_set_eq(*_debug !print_sv_f*) f a3)
						      | _ -> (a1,a2,a3)) ([],[], empty_var_aset ) m_l in      
		  { memo_group_fv = v_l; 
		    memo_group_changed = true ; 
		    memo_group_cons = mc_l;
		    memo_group_slice = f_l;
		    memo_group_aset = a_l}) r  
      
and regroup_memo_group (lst : memo_pure) : memo_pure = 
  let rec f_rec fv a = 
    let r1,r2 = List.partition (fun c-> (List.length (Util.intersect_fct eq_spec_var fv c.memo_group_fv))>0) a in
      if r1 = [] then ([],r2)
      else
	let n_fv = List.fold_left (fun ac c-> ac@c.memo_group_fv) fv r1 in
	let x1,x2 = f_rec n_fv r2 in
	  (r1@x1,x2) in
  let rec helper c = match c with
    | [] -> []
    | h::t -> 
	let h_merged,h_not_merged = f_rec h.memo_group_fv t in
	let h_m = List.fold_left (fun a c-> 
				    { memo_group_fv = a.memo_group_fv @c.memo_group_fv;
				      memo_group_slice = a.memo_group_slice @c.memo_group_slice;
				      memo_group_cons =  a.memo_group_cons  @c.memo_group_cons;
				      memo_group_changed = true;
				      memo_group_aset = Util.merge_set_eq(*_debug !print_sv_f*) a.memo_group_aset c.memo_group_aset;}) h h_merged in
	let r_h = {h_m with memo_group_fv = Util.remove_dups_f h_m.memo_group_fv eq_spec_var;} in      
	let r = helper h_not_merged in
	  r_h::r in
    helper lst
      
      

and subst_avoid_capture_memo (fr : spec_var list) (t : spec_var list) (f_l : memo_pure) : memo_pure=
  let fresh_fr = fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let helper  (s:(spec_var*spec_var) list) f  = 
    let r = Util.rename_eset_eq (subs_one s) f.memo_group_aset in
      (*let _ = print_string ("rapp1: "^(print_alias_set f.memo_group_aset)^"\n") in
	let _ = print_string ("rapp2: "^(print_alias_set r)^"\n") in*)
      {memo_group_fv = List.map (fun v-> subs_one s v) f.memo_group_fv;
       memo_group_changed = f.memo_group_changed;
       memo_group_cons = List.map (fun d->{d with memo_formula = List.fold_left (fun a c-> b_apply_one c a) d.memo_formula s;}) f.memo_group_cons;
       memo_group_slice = List.map (subst s) f.memo_group_slice; 
       memo_group_aset = r} in
  let r = List.map (helper st1) f_l in
    regroup_memo_group (List.map (helper st2) r)

and subst_avoid_capture_memo_debug1 (fr : spec_var list) (t : spec_var list) (f_l : memo_pure) : memo_pure =
  Util.ho_debug_3a_list "1 subst_avoid_capture_memo" (full_name_of_spec_var) subst_avoid_capture_memo fr t f_l

and subst_avoid_capture_memo_debug2 (fr : spec_var list) (t : spec_var list) (f_l : memo_pure) : memo_pure =
  Util.ho_debug_3a_list "2 subst_avoid_capture_memo" (full_name_of_spec_var) subst_avoid_capture_memo fr t f_l

and subst_avoid_capture_memo_debug3 (fr : spec_var list) (t : spec_var list) (f_l : memo_pure) : memo_pure =
  Util.ho_debug_3a_list "3 subst_avoid_capture_memo" (full_name_of_spec_var) subst_avoid_capture_memo fr t f_l

    
and memo_cons_subst sst (f_l : memoised_constraint list): memoised_constraint list = 
  List.map (fun c-> 
	      let nf = List.fold_left (fun a c-> b_apply_one c a) c.memo_formula sst in
		{c with memo_formula = nf }) f_l

and memo_subst (sst : (spec_var * spec_var) list) (f_l : memo_pure) = 
  let rec helper sst f_l = match sst with
    | s::ss -> helper ss (m_apply_one s f_l)
    | [] -> f_l in
    regroup_memo_group (helper sst f_l)
      
and m_apply_one (s:spec_var * spec_var) f = 
  let r1 = List.map (fun c -> 
		       let r = Util.subs_eset_eq(*_debug !print_sv_f*) s c.memo_group_aset in
			 {memo_group_fv = List.map (fun v-> subst_var s v) c.memo_group_fv;
			  memo_group_changed = c.memo_group_changed;
			  memo_group_cons = List.map (fun d->{d with memo_formula = b_apply_one s d.memo_formula;}) c.memo_group_cons;
			  memo_group_slice = List.map (apply_one s) c.memo_group_slice; 
			  memo_group_aset = r }) f in  
  let r = filter_mem_triv r1 in
    r

and h_apply_one_m_constr_lst s l = 
  List.map (fun (c,c2)-> ({c with memo_formula = b_apply_one s c.memo_formula},c2)) l

and b_f_ptr_equations f =  match f with
  | Eq (e1, e2, _) -> 
      let b = can_be_aliased e1 && can_be_aliased e2 in
        if not b then [] else [(get_alias e1, get_alias e2)]
  | _ -> [] 
      
and pure_ptr_equations (f:formula) : (spec_var * spec_var) list = 
  let rec prep_f f = match f with
    | And (f1, f2, pos) -> (prep_f f1) @ (prep_f f2)
    | BForm (bf,_) -> b_f_ptr_equations bf
    | _ -> [] in 
    prep_f f
      
(* use_with_null_const for below*)
(* assume that f is a satisfiable conjunct *)
(* returns a list of ptr eqns v1=v2 that can be found in memo_pure
   and called during matching of predicates
*)
and ptr_equations (f : memo_pure) : (spec_var * spec_var) list =  
  let helper f = 
    let r = List.fold_left (fun a c-> (a@ b_f_ptr_equations c.memo_formula)) [] f.memo_group_cons in
    let r = List.fold_left (fun a c-> a@(pure_ptr_equations c)) r f.memo_group_slice in
      r @ (get_equiv_eq_with_null f.memo_group_aset) in
    List.concat (List.map helper f)

(*and alias_of_ptr_eqs s = List.fold_left (fun a (c1,c2) -> Util.add_equiv a c1 c2) Util.empty_aset s*)
      
(*and b_formula_alias (f:b_formula):var_aset = alias_of_ptr_eqs (b_f_ptr_equations f)*)
(*and pure_alias (f:formula) : var_aset = alias_of_ptr_eqs (pure_ptr_equations f)*)
      
(*and memo_alias (m:memo_pure) : var_aset = alias_of_ptr_eqs (ptr_equations m)*)

(*and var_aset_subst_one s (l:var_aset) : var_aset = List.map (fun (a,l)-> ((subst_var s a),subst_one_var_list s l)) l *)
      
(*and var_aset_subst_list s (l:var_aset) : var_aset = List.map (fun (a,l)-> ((subs_one s a),subst_var_list s l)) l *)

(*and var_aset_subst_one_exp (v,_) (l:var_aset) : var_aset = 
  List.fold_left (fun a (c1,c2)-> if (eq_spec_var v c1) then a else (c1,(List.filter (eq_spec_var v) c2))::a ) [] l*)
      
(*  extract the equations for the variables that are to be explicitly instantiated from the residue - a Cpure.formula *)
(* get the equation for the existential variable used in the
   following variable elimination ex x. (x=y & P(x)) <=> P(y).
   The function also returns the remainder of the formula after
   the equation is extracted. It stops searching upon seeing
   Or/Exists/Forall. The equations returned are only of form
   v1 = v2 so that they can be applied to heap nodes. *)

and get_subst_equation_memo_formula_vv (f0: memo_pure) (v:spec_var) : ((spec_var * spec_var) list * memo_pure) = 
  let (r1,r2) = get_subst_equation_memo_formula f0 v true in
  let r1 = List.fold_left (fun a c-> match c with | (r,Var(v,_))-> (r,v)::a | _ -> a) [] r1 in
    (r1,r2)
      
(*it always returns either 0 or one substitutions, if more are available just picks one*)
and get_subst_equation_memo_formula (f0 : memo_pure) (v : spec_var) only_vars: ((spec_var * exp) list * memo_pure) = 
  let r = List.fold_left (fun (a1,a2) c ->
			    if not(a1=[]) then (a1,c::a2)
			    else if not(List.exists (eq_spec_var v) c.memo_group_fv) then (a1,c::a2)
			    else 
			      let acl_cons, ncl = List.fold_left (fun (a1,a2) c-> if not(a1=[]) then (a1,c::a2)
								  else 
								    let r1,r2 = get_subst_equation_b_formula c.memo_formula v None only_vars in
								      if (r1=[]) then (a1,c::a2) else (r1,a2)) ([],[]) c.memo_group_cons in
				
			      let acl_aset, nas = if not(acl_cons=[]) then (acl_cons,c.memo_group_aset)
			      else match Util.find_equiv_elim_eq v c.memo_group_aset with
                | None -> (acl_cons,c.memo_group_aset)
                | Some (s,nas) -> 
                    (*let _ = print_string ("subs_fr: "^(!print_sv_f v)^"\n") in
                      let _ = print_string ("before_el: "^(print_alias_set c.memo_group_aset)^"\n") in
                      let _ = print_string ("after_el: "^(print_alias_set nas)^"\n") in
                      let _ = print_string ("subs_to: "^(!print_sv_f s)^"\n") in*)
                    ([(v,conv_var_to_exp s)],nas) in
				
			      let acl_slice, nsl = if not (acl_aset=[]) then (acl_aset, c.memo_group_slice)
			      else List.fold_left (fun (a1,a2) c-> 
						     if not (a1=[]) then (a1,c::a2)
						     else 
						       let r1,r2 = get_subst_equation_formula c v only_vars in
							 (r1,r2::a2))([],[]) c.memo_group_slice in
			      let rg = {c with 
					  memo_group_cons=ncl; 
					  memo_group_slice=nsl; 
					  memo_group_aset = nas} in
				(acl_slice, rg::a2)) ([],[]) f0 in
    (*   let _ = print_string (" get_subst: "^(!print_mp_f f0)^"\n") in
	 let _ = print_string (" for: " ^(!print_sv_f v)^"\n") in
	 let _ = print_string (" found: "^(String.concat " "(List.map (fun (c1,c2)->
	 (!print_sv_f c1)^" -> "^(!print_exp_f c2)) (fst r)))^"\n") in*)
    r

(* below need to be with_const *)
(* this applies a substitution v->e on a list of memoised group *)
(* useful to consider two special cases is v->v2 or v->c for aset *)
and memo_apply_one_exp (s:spec_var * exp) (mem:memoised_group list) : memo_pure = 
  let fr,t = s in
  let conv eqs = match (conv_exp_to_var t) with
    | Some(vt,_) -> ([], List.fold_left 
		       (fun a2 (c1,c2) -> 
			  if (eq_spec_var c1 fr) then (add_equiv_eq_with_const a2 c2 vt)
			  else if (eq_spec_var c2 fr) then (add_equiv_eq_with_const a2 c1 vt)
			  else (add_equiv_eq_with_const a2 c1 c2)) empty_var_aset eqs)
    | None -> List.fold_left 
        (fun (a1,a2) (c1,c2) -> 
           if (eq_spec_var c1 fr) then ((BForm (Eq (conv_var_to_exp c2,t,no_pos),None))::a1,a2)
           else if (eq_spec_var c2 fr) then ((BForm (Eq (conv_var_to_exp c1,t,no_pos),None))::a1,a2)
           else (a1,add_equiv_eq_with_const a2 c1 c2)) ([],empty_var_aset) eqs in
  let r = List.map (fun c -> 
		      let eqs = get_equiv_eq_with_const c.memo_group_aset in
		      let tbm,rem = conv eqs in
			{ c with 
			    memo_group_cons = List.map (fun d->{d with memo_formula = b_apply_one_exp s d.memo_formula}) c.memo_group_cons;
			    memo_group_slice = tbm @ (List.map (apply_one_exp s) c.memo_group_slice);
			    memo_group_aset = rem}) mem in
    (*let _ = print_string ("pre got slices: "^(string_of_int (List.length r))^"\n") in*)
  let r_group = group_mem_by_fv r in
    (*let _ = print_string ("pre got slices: "^(string_of_int (List.length r_group))^"\n") in  *)
    filter_mem_triv r_group
      

and memo_f_neg (f: b_formula): b_formula = match f with
  | Lt (e1,e2,l) -> Lte (e2,e1,l)
  | Lte (e1,e2,l) -> Lt (e2,e1,l)
  | Gt (e1,e2,l) -> Lte (e1,e2,l)
  | Gte (e1,e2,l) -> Lt (e1,e2,l)
  | Eq (e1,e2,l) -> Neq (e1,e2,l)
  | Neq (e1,e2,l) -> Eq (e1,e2,l)
  | BagIn (e1,e2,l) -> BagNotIn(e1,e2,l)
  | BagNotIn  (e1,e2,l) -> BagIn(e1,e2,l)
  | ListIn (e1,e2,l) -> ListNotIn(e1,e2,l)
  | ListNotIn (e1,e2,l) -> ListIn(e1,e2,l)
  | _ -> Error.report_error {Error.error_loc = no_pos;Error.error_text = "memoized negation: unexpected constraint type"}
      
and memo_arith_simplify (f:memo_pure) : memo_pure = 
  List.map (fun c-> { c with memo_group_slice = List.map arith_simplify c.memo_group_slice}) f
    
(******************************************************************************************************************
														   Utilities for memoized formulas
******************************************************************************************************************)
    
and mkMTrue pos :memo_pure = []
and mkMFalse pos :memo_pure = 
  [{memo_group_fv=[]; 
    memo_group_changed = false; 
    memo_group_cons = [];
    memo_group_slice = [mkFalse pos];
    memo_group_aset = empty_var_aset}]
    

and memo_is_member_pure p mm = 
  List.exists (fun c-> 
		 let r = (List.exists (is_member_pure p) c.memo_group_slice)||
		   (List.exists (fun d-> 
				   (match p with | BForm (r,_)-> equalBFormula_aset c.memo_group_aset r d.memo_formula | _ -> false)) c.memo_group_cons) in
		   if r then true
		   else match p with
		     | BForm (Eq(Var(v1,_),Var(v2,_),_), _) -> Util.is_equiv_eq c.memo_group_aset v1 v2
		     | _ -> false ) mm
    
(* below with_const *)
(* this extracts a list of formula from memo_pure ;
   with_P : takes the propagated ctrs
   with_R : takes the redundant  ctrs
   with_slice : takes the non-atomic ctrs
   with_disj : takes also non-atomic  disjunctive ctrs
*)
and fold_mem_lst_to_lst_gen  (mem:memo_pure) with_R with_P with_slice with_disj: formula list=	
  let rec has_disj_f c = match c with | Or _ -> true | _ -> false  in			  
  let r = List.map (fun c-> 
		      let slice = if with_slice then 
			if with_disj then c.memo_group_slice 
			else List.filter (fun c-> not (has_disj_f c)) c.memo_group_slice
		      else [] in
		      let cons = List.filter (fun c-> match c.memo_status with 
						| Implied_R -> with_R 
						| Implied_N -> true 
						| Implied_P-> with_P) c.memo_group_cons in
		      let cons  = List.map (fun c-> (BForm(c.memo_formula, None))) cons in
		      let asetf = List.map (fun(c1,c2)-> form_formula_eq_with_const c1 c2) (get_equiv_eq_with_const c.memo_group_aset) in
			asetf @ slice@cons) mem in
  let r = List.map join_conjunctions r in
    r
      
and fold_mem_lst_to_lst mem with_dupl with_inv with_slice = fold_mem_lst_to_lst_gen mem with_dupl with_inv with_slice true
  
and fold_mem_lst_to_lst_debug mem with_dupl with_inv with_slice = 
  let r = fold_mem_lst_to_lst mem with_dupl with_inv with_slice in
    print_string ("fold_mem_lst_to_lst input: "^(!print_mp_f mem)^"\n");
    print_string ("fold_mem_lst_to_lst output: "^(print_p_f_l r)^"\n");
    r
      
      
and fold_mem_lst_gen (f_init:formula) with_dupl with_inv with_slice with_disj lst : formula = 
  let r = fold_mem_lst_to_lst_gen lst with_dupl with_inv with_slice with_disj in
    List.fold_left (fun a c-> mkAnd a c no_pos) f_init r      
      
and fold_mem_lst_no_disj (f_init:formula) with_dupl with_inv lst :formula= fold_mem_lst_gen f_init with_dupl with_inv true false lst
  
and fold_mem_lst (f_init:formula) with_dupl with_inv lst :formula= fold_mem_lst_gen f_init with_dupl with_inv true true lst
  
(*folds just the pruning constraints, ignores the memo_group_slice*) 
and fold_mem_lst_cons init_cond lst with_dupl with_inv with_slice :formula = 
  (*fold_mem_lst_to_lst lst false true false*)
  fold_mem_lst_gen (BForm (init_cond,None)) with_dupl with_inv with_slice true lst
    
and filter_useless_memo_pure (simp_fct:formula->formula) (simp_b:bool) 
    (fv:spec_var list) (c_lst:memo_pure) : memo_pure = 
  let n_c_lst = List.fold_left (fun a c-> 
				  if (isConstMFalse a) then a
				  else
				    let n_slice_lst = if c.memo_group_fv = [] then List.map simp_fct c.memo_group_slice else c.memo_group_slice in
				    let n_slice_lst = List.filter (fun c-> not (isConstTrue c)) n_slice_lst in   
				      if (List.exists isConstFalse n_slice_lst) then mkMFalse no_pos
				      else {c with memo_group_slice = n_slice_lst; memo_group_cons = c.memo_group_cons;}::a ) [] c_lst in
    List.filter (fun c-> not (isConstGroupTrue c))  n_c_lst
      
and filter_merged_cons aset l=   
  let eq = Cpure.eq_spec_var_aset aset  in
  let keep c1 c2 = match c1.memo_status ,c2.memo_status with
    | _ , Implied_R -> if (equalBFormula_f eq c1.memo_formula c2.memo_formula) then (true,false) else (true,true)
    | Implied_R , _ -> if (equalBFormula_f eq c1.memo_formula c2.memo_formula) then (false,true) else (true,true) 
    | Implied_N,Implied_N | Implied_P,Implied_P | Implied_N,Implied_P
	-> if (equalBFormula_f eq c1.memo_formula c2.memo_formula) then (false,true) else (true,true) 
    | Implied_P,Implied_N -> if (equalBFormula_f eq c1.memo_formula c2.memo_formula) then (true,false) else (true,true) in
    
  let rec remove_d n = match n with 
    | [] -> []
    | q::qs -> 
	let b,r = List.fold_left (fun (b,r) c-> 
				    let r1,r2 = keep q c in
				      (b&&r1,if r2 then c::r else r)) (true,[])qs in
	  if b then q::(remove_d r) else (remove_d r) in
    Util.push_time "filter_dupl_memo";
    let r = remove_d (List.concat l) in 
      Util.pop_time "filter_dupl_memo";
      r
	
and mkOr_mems (l1: memo_pure) (l2: memo_pure) (*with_dupl with_inv*) : memo_pure = 
  let f1 = fold_mem_lst (mkTrue no_pos) false true l1 in
  let f2 = fold_mem_lst (mkTrue no_pos) false true l2 in
    memoise_add_pure_N [] (mkOr f1 f2 None no_pos)
      
and combine_memo_branch b (f, l) =
  match b with 
    | "" -> f
    | s -> try 
	memoise_add_pure_N f (List.assoc b l) with Not_found -> f

and merge_mems (l1: memo_pure) (l2: memo_pure) slice_check_dups: memo_pure = 
  let r=  if (isConstMFalse l1)||(isConstMTrue l2) then l1
  else if (isConstMFalse l2)||(isConstMTrue l1) then l2
  else
    List.fold_left (fun a c-> 
		      let merged, un_merged = List.partition (fun d-> (List.length(Util.intersect_fct eq_spec_var d.memo_group_fv c.memo_group_fv))>0) a in
		      let n1, n2, n3, n4 = List.fold_left 
			(fun (a1,a2,a3,a4) d-> 
			   let r = (Util.merge_set_eq(*_debug !print_sv_f*) a4 d.memo_group_aset) in
			     (d.memo_group_fv@a1,
			      d.memo_group_cons::a2, 
			      d.memo_group_slice::a3, 
			      r)) 
			( c.memo_group_fv,
			  [c.memo_group_cons], 
			  [c.memo_group_slice], 
			  c.memo_group_aset)
			merged in
		      let ng = if (List.length merged)>0 then
			let n3 = List.concat n3 in
			let n_slc = if (not slice_check_dups) then n3 
			else 
			  (Util.push_time "merge_mems_r_dups";
			   let r = Util.remove_dups_f n3 eq_pure_formula in
			     Util.pop_time "merge_mems_r_dups";
			     r)in
			  {memo_group_fv = Util.remove_dups n1; 
			   memo_group_cons = filter_merged_cons n4 n2;
			   memo_group_changed = true;
			   memo_group_slice = n_slc;
			   memo_group_aset = n4;
			  }
		      else c in
			ng::un_merged) l2 l1 in
    r
      
(*add cm to l_init and depending on the fnf flag
  true: add cm and also add the negation of cm as a fail condition
  false: add only cm 
  and memoise_add_memo (l_init: memo_pure) (cm:memoised_constraint) : memo_pure =
  let fv = bfv cm.memo_formula in
  let merged,un_merged = List.partition (fun c-> (List.length (Util.intersect_fct eq_spec_var fv c.memo_group_fv))>0) l_init in
  let n_cm_lst = [cm] in
  let n1,n2,n3,n4 = List.fold_left 
  (fun (a1,a2,a3,a4) d-> 
  (d.memo_group_fv@a1,
  d.memo_group_cons::a2,
  d.memo_group_slice::a3, 
  Util.merge_set_eq(*_debug !print_sv_f*) a4 d.memo_group_aset))
  (fv,[n_cm_lst],[], empty_var_aset) merged in   
  let l = if (List.length merged)>0 then 
  let ng = {memo_group_cons =  filter_merged_cons (empty_var_aset) n2; 
  memo_group_fv = Util.remove_dups n1;
  memo_group_changed = true;
  memo_group_slice = List.concat n3;
  memo_group_aset = n4} in
  List.hd (recompute_unknowns [ng])
  else 
  {
  memo_group_cons =n_cm_lst; 
  memo_group_fv = fv; 
  memo_group_changed = true; 
  memo_group_slice = []; 
  memo_group_aset = empty_var_aset} in  
  let r = l::un_merged in
  r
  
(*and memoise_add_memo (l: memo_pure) (cm:memoised_constraint): memo_pure = memoise_add_memo_fnf l cm false*)
*)
and memoise_add_failed_memo (l:memo_pure) (p:b_formula) : memo_pure = 
  merge_mems l (create_memo_group_wrapper [p] Implied_R) false
    
and memoise_add_pure_aux (l: memo_pure) (p:formula) status : memo_pure = 
  if (isConstTrue p)||(isConstMFalse l) then l 
  else if (isConstFalse p) then mkMFalse no_pos
  else 
    (Util.push_time "add_pure";  
     let disjs, rests = List.fold_left (fun (a1,a2) c-> match c with 
					  | BForm x -> (x::a1,a2) 
					  | _ -> (a1,c::a2))  ([],[]) (list_of_conjs p) in
     let m2 = create_memo_group(*_debug*) disjs rests status in
     let r = merge_mems l m2 true in
       (*let r = List.concat (List.map split_mem_grp r) in*)
       Util.pop_time "add_pure"; r)
    
and memoise_add_pure_aux_debug l p status : memo_pure = 
  Util.ho_debug_3 "memoise_add_pure_aux " (fun _ -> "?") !print_p_f_f (fun _ -> "?") (!print_mp_f) memoise_add_pure_aux l p status

  
and memoise_add_pure_N l p = memoise_add_pure_aux(*_debug*) l p Implied_N
and memoise_add_pure_P l p = memoise_add_pure_aux(*_debug*) l p Implied_P

and create_memo_group_wrapper (l1:b_formula list) status : memo_pure = 
  let l = List.map (fun c-> (c, None)) l1 in
    create_memo_group(*_debug*) l [] status 

and anon_partition (l1:(b_formula *(formula_label option)) list) = 
  List.fold_left (fun (a1,a2) (c1,c2)-> 
		    if (List.exists is_anon_var (bfv c1)) then (a1,(BForm (c1,c2))::a2) else ((c1,c2)::a1,a2)
		 ) ([],[]) l1
    
(*add both imply and fail*)
and create_memo_group (l1:(b_formula *(formula_label option)) list) (l2:formula list) status :memo_pure = 
  let l1, to_slice2 = anon_partition l1 in
  let l1, to_slice1 = memo_norm l1 in
  let l1 = Util.remove_dups l1 in
  let l2 = to_slice1 @ to_slice2 @ l2 in
  let l2 = List.map (fun c-> (None, Some c)) l2 in
  let l1 = List.map (fun c-> (Some c,None)) l1 in  
  let ll  = List.fold_left ( fun a f->
			       let fv = match f with | None, Some c-> fv c | Some c, None -> bfv c | _-> [] in
			       let rec f_rec fv a = 
				 let r1,r2 = List.partition (fun (v,_,_)-> (List.length (Util.intersect_fct eq_spec_var fv v))>0) a in
				   if r1 = [] then ([],r2)
				   else
				     let n_fv = List.fold_left (fun ac (v,_,_)-> ac@v) fv r1 in
				     let x1,x2 = f_rec n_fv r2 in
				       (r1@x1,x2) in
			       let to_merge, no_merge = f_rec fv a in
			       let merg_fv,merg_bf, merg_f  = List.fold_left (fun (a1,a2,a3)(c1,c2,c3)-> (a1@c1,a2@c2,a3@c3)) ([],[],[]) to_merge in
			       let merg_fv = Util.remove_dups (merg_fv@fv) in
				 match f with 
				   | None, Some c -> (merg_fv,merg_bf,c::merg_f)::no_merge 
				   | Some c, None -> (merg_fv,c::merg_bf,merg_f)::no_merge 
				   | _-> no_merge) [] (l1@l2) in
  let r = List.map (fun (vars,bfs,fs)-> 
		      let nfs,aset = List.fold_left (fun (a,s) c-> 

						       match get_bform_eq_args_with_const c with 
							 | Some(v1,v2) -> (a,add_equiv_eq_with_const(*_debug*) s v1 v2)
							 | _ ->
							     let pos = {memo_formula=c;memo_status = status} in
							       ((pos::a),s)) ([],empty_var_aset) bfs in 
			{ memo_group_fv = vars;
			  memo_group_cons = filter_merged_cons aset [nfs];
			  memo_group_slice = fs;
			  memo_group_changed = true;
			  memo_group_aset = aset;}) ll in
    r
      
and create_memo_group_debug ll l2 = 
  Util.ho_debug_3 "create_memo_group " (Util.string_of_list (fun (c,_) -> !print_bf_f c)) (Util.string_of_list !print_p_f_f) (fun _ -> "?")
    (!print_mp_f) create_memo_group ll l2

    
(* with_const; use get_equiv_eq *)
(*
  This attempts to split g into multiple groups if 
  the constraints are disjoint.
*)
and split_mem_grp (g:memoised_group): memo_pure =   
  let leq_all = get_equiv_eq_with_const g.memo_group_aset in
  let leq = get_equiv_eq g.memo_group_aset in
  let l1 = List.map fv g.memo_group_slice in
  let l2 = List.map (fun c-> bfv c.memo_formula) g.memo_group_cons in
  let l3 = List.map (fun (c1,c2) -> [c1;c2]) leq in
  let needs_split = List.fold_left (fun a c-> 
				      let n_unite,unite = List.partition (fun d-> (Util.intersect_fct eq_spec_var d c)=[]) a in
					(List.fold_left (fun a c-> a@c) c unite)::n_unite ) [] (l1@l2@l3) in
    if (List.length needs_split)>1 then
      (
	Util.inc_counter "need_split";
	List.map (fun c-> {
		    memo_group_fv = c;
		    memo_group_changed = g.memo_group_changed;
		    memo_group_cons = List.filter (fun d-> not((Util.intersect c (bfv d.memo_formula))=[])) g.memo_group_cons;
		    memo_group_slice = List.filter (fun d-> not((Util.intersect c (fv d))=[])) g.memo_group_slice;
		    memo_group_aset = List.fold_left (fun a (c1,c2) -> 
							if (List.exists (eq_spec_var c1) c) or (List.exists (eq_spec_var c2) c) then add_equiv_eq_with_const a c1 c2
							else a) empty_var_aset leq_all;
		  }) needs_split
      )
    else [g]
      (*
	and_split_mem_grp_debug g =
	let r = split_mem_grp g in
	if (List.length r)>1 then *)
      
and memo_pure_push_exists (qv:spec_var list) (c:memo_pure):memo_pure = 
  if qv==[] then c
  else
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
      
and memo_norm (l:(b_formula *(formula_label option)) list): b_formula list * formula list = 
  let rec get_head e = match e with 
    | Null _ -> "Null"
    | Var (v,_) -> name_of_spec_var v
    | IConst (i,_)-> string_of_int i
    | FConst (f,_) -> string_of_float f
    | Add (e,_,_) | Subtract (e,_,_) | Mult (e,_,_) | Div (e,_,_)
    | Max (e,_,_) | Min (e,_,_) | BagDiff (e,_,_) | ListCons (e,_,_)| ListHead (e,_) 
    | ListTail (e,_)| ListLength (e,_) | ListReverse (e,_)  -> get_head e
    | Bag (e_l,_) | BagUnion (e_l,_) | BagIntersect (e_l,_) | List (e_l,_) | ListAppend (e_l,_)-> 
	if (List.length e_l)>0 then get_head (List.hd e_l) else "[]" in
    
  let e_cmp e1 e2 =  String.compare (get_head e1) (get_head e2) in
    
  let rec get_lists (e:exp) (disc:int): exp list * exp list = match e with
    | Add (e1,e2,l)-> 
	if (disc<>1) then ([e],[])
	else let (lp1,ln1),(lp2,ln2) = get_lists e1 disc, get_lists e2 disc in
	  (lp1@lp2,ln1@ln2) 
    | Subtract (e1,e2,l)->
	if (disc<>1) then ([e],[])
	else let (lp1,ln1),(ln2,lp2) = get_lists e1 disc, get_lists e2 disc in
	  (lp1@lp2,ln1@ln2) 
    | Mult (e1,e2,l)-> 
	if (disc<>(-1)) then ([e],[])
	else let (lp1,ln1),(lp2,ln2) = get_lists e1 disc, get_lists e2 disc in
	  (lp1@lp2,ln1@ln2)       
    | Div (e1,e2,l)-> 
	if (disc<>(-1)) then ([e],[])
	else let (lp1,ln1),(ln2,lp2) = get_lists e1 disc, get_lists e2 disc in
	  (lp1@lp2,ln1@ln2) 
    | Null _ | Var _ | IConst _ | FConst _ | Max _  | Min _ | Bag _ | BagUnion _ | BagIntersect _ 
    | BagDiff _ | List _ | ListCons _ | ListHead _ | ListTail _ | ListLength _ | ListAppend _ | ListReverse _ -> ([e],[]) in
    
  let rec norm_expr e = match e with
    | Null _ | Var _ | IConst _ | FConst _ -> e
    | Add (e1,e2,l) -> cons_lsts e 1 (fun c-> Add c) (fun d-> Subtract d) (IConst (0,l))
    | Subtract (e1,e2,l) -> cons_lsts e 1 (fun c-> Add c) (fun d-> Subtract d) (IConst (0,l))
    | Mult (e1,e2,l) -> cons_lsts e (-1) (fun c-> Mult c) (fun d-> (*print_string "called \n";*) Div d) (IConst (1,l))
    | Div (e1,e2,l) -> cons_lsts e (-1) (fun c-> Mult c) (fun d-> Div d) (IConst (1,l))
    | Max (e1,e2,l)->
	let e1,e2 = norm_expr e1, norm_expr e2 in
	  if(e_cmp e1 e2)>0 then Max(e1,e2,l) else Max(e2,e1,l)
    | Min (e1,e2,l) ->
	let e1,e2 = norm_expr e1, norm_expr e2 in
	  if(e_cmp e1 e2)>0 then Min(e1,e2,l) else Min(e2,e1,l)
    | Bag (e,l)-> Bag ( List.sort e_cmp (List.map norm_expr e), l)    
    | BagUnion (e,l)-> BagUnion ( List.sort e_cmp (List.map norm_expr e), l)    
    | BagIntersect (e,l)-> BagIntersect ( List.sort e_cmp (List.map norm_expr e), l)    
    | BagDiff (e1,e2,l) -> BagDiff (norm_expr e1, norm_expr e2, l)
    | List (e,l)-> List (List.sort e_cmp (List.map norm_expr e), l)    
    | ListCons (e1,e2,l)-> ListCons(norm_expr e1, norm_expr e2,l)      
    | ListHead (e,l)-> ListHead(norm_expr e, l)      
    | ListTail (e,l)-> ListTail(norm_expr e, l)      
    | ListLength (e,l)-> ListLength(norm_expr e, l)
    | ListAppend (e,l) -> ListAppend ( List.sort e_cmp (List.map norm_expr e), l)    
    | ListReverse (e,l)-> ListReverse(norm_expr e, l)  
	
  and cons_lsts (e:exp) (disc:int) cons1 cons2 (nel:exp) : exp=     
    let lp,ln = get_lists e disc in
    let lp = List.sort e_cmp (List.map norm_expr lp) in
    let ln = List.sort e_cmp (List.map norm_expr ln) in
      if (List.length lp)>0 then
	let a = List.fold_left (fun a c-> cons1(a,c,no_pos)) (List.hd lp) (List.tl lp) in
	  List.fold_left(fun a c-> cons2 (a,c,no_pos)) a ln
      else List.fold_left(fun a c-> cons2 (a,c,no_pos)) nel ln in

    (*  let norm_bf (c1:b_formula) : (b_formula option) =
	let c1 = b_form_simplify c1 in
	match c1 with
	| Lt  (e1,e2,l) -> Some (Lt  (norm_expr e1,norm_expr e2,l))
	| Lte (e1,e2,l) -> Some (Lte (norm_expr e1,norm_expr e2,l))
	| Gt  (e1,e2,l) -> Some (Lt  (norm_expr e2,norm_expr e1,l))
	| Gte (e1,e2,l) -> Some (Lte (norm_expr e2,norm_expr e1,l))
	| Eq  (e1,e2,l) -> 
	let e1,e2 = norm_expr e1,norm_expr e2 in
	if(eqExp e1 e2) then Some(BConst(true,no_pos)) else Some(Eq(e1,e2,l))
	| Neq (e1,e2,l) -> Some (Neq(norm_expr e1,norm_expr e2,l))
	| BagIn (v,e,l) -> Some (BagIn (v, norm_expr e, l))
	| BagNotIn (v,e,l) -> Some (BagNotIn (v, norm_expr e, l))
	| ListIn (e1,e2,l) -> Some (ListIn (norm_expr e1,norm_expr e2,l))
	| ListNotIn (e1,e2,l) -> Some (ListIn (norm_expr e1,norm_expr e2,l))
	| BConst _ | BVar _ | EqMax _ 
	| EqMin _ |  BagSub _ | BagMin _ 
	| BagMax _ | ListAllN _ | ListPerm _ -> None in*)
    
    Util.push_time "memo_norm";
    let l = List.fold_left (fun (a1,a2) (c1,c2)-> 
			      match norm_bform_option(*_debug*) c1 with
				| Some c1 -> (c1::a1,a2)
				| None -> (a1,(BForm(c1,c2))::a2)) ([],[]) l in
      Util.pop_time "memo_norm";l

(*
  let l = List.fold_left (fun (a1,a2) (c1,c2)-> 
    let c1 = b_form_simplify c1 in
    match c1 with
      | Lt  (e1,e2,l) -> (Lt  (norm_expr e1,norm_expr e2,l)::a1,a2)
      | Lte (e1,e2,l) -> (Lte (norm_expr e1,norm_expr e2,l)::a1,a2)
      | Gt  (e1,e2,l) -> (Lt  (norm_expr e2,norm_expr e1,l)::a1,a2)
      | Gte (e1,e2,l) -> (Lte (norm_expr e2,norm_expr e1,l)::a1,a2)
      | Eq  (e1,e2,l) -> 
        let e1,e2 = norm_expr e1,norm_expr e2 in
        if(eqExp e1 e2) then (a1,a2) else (Eq(e1,e2,l)::a1,a2)
      | Neq (e1,e2,l) -> (Neq(norm_expr e1,norm_expr e2,l)::a1,a2)
      | BagIn (v,e,l) -> (BagIn (v, norm_expr e, l)::a1,a2)
      | BagNotIn (v,e,l) -> (BagNotIn (v, norm_expr e, l)::a1,a2)
      | ListIn (e1,e2,l) -> (ListIn (norm_expr e1,norm_expr e2,l)::a1,a2)
      | ListNotIn (e1,e2,l) -> (ListIn (norm_expr e1,norm_expr e2,l)::a1,a2)
      | BConst _ | BVar _ | EqMax _ 
      | EqMin _ |  BagSub _ | BagMin _ 
      | BagMax _ | ListAllN _ | ListPerm _ -> (a1,(BForm(c1,c2))::a2)) ([],[]) l in
*)
  
let memo_norm_wrapper (l:b_formula list): b_formula list = 
 let l = List.map (fun c-> (c,None)) l in
 fst (memo_norm l)
  
(* simpl_b_f -> semantically simplifies a b_formula
   simpl_p_f -> syntactic simpl of individual small formula
   s_f -> semantic simplification of formula*)
  
let simpl_memo_pure_formula simpl_b_f simpl_p_f(f:memo_pure) s_f: memo_pure = 
  List.map (fun c-> {c with 
        memo_group_cons = List.map (fun c-> {c with memo_formula = simpl_b_f c.memo_formula}) c.memo_group_cons;
        memo_group_changed = true;
        memo_group_slice = list_of_conjs (s_f ((*simpl_p_f *)(conj_of_list c.memo_group_slice no_pos)))}) f
  
  
  
  
let memo_drop_null self l = List.map (fun c -> {c with memo_group_slice = List.map (fun c-> drop_null c self false ) c.memo_group_slice}) l
         
         
(*changes the status of the implied constraints to Implied_R in l if 
those constraints appear in the cons list of memoised constraints
this is called in order to change 
*)
let memo_change_status cons l =
  let lcns = List.map (fun cns-> (bfv cns, cns)) cons in
  List.map (fun grp-> 
    List.fold_left (fun a (vcns,cns)-> 
      if ((List.length (Util.intersect_fct eq_spec_var vcns grp.memo_group_fv))<=0) then a
      else 
        let ncns = List.map 
          (fun c-> 
            if not(eq_b_formula_no_aset c.memo_formula cns) then c
            else {c with memo_status=Implied_R}
          ) a.memo_group_cons in
        {a with memo_group_cons= ncns}
    )grp lcns
  ) l
  
let memo_find_relevant_slice fv l = List.find (fun d-> Util.subset fv d.memo_group_fv) l 

let memo_changed d = d.memo_group_changed 

(* checks wether the p_cond constraint can be syntactically dismissed (equal to a contradiction)
   if equal to an implied cond then it can be dropped as it is useless as a pruning condition
   throws an exception if p_cond is not found in corr*)    
   
let memo_f_neg_norm (p:b_formula) :b_formula = 
  match norm_bform_option (memo_f_neg p) with
    | Some s-> s
    | None -> Error.report_error 
      {Error.error_loc = no_pos; Error.error_text = "memo_f_neg_norm: the negation can not be normalized to a simple b_formula"}
   
let memo_check_syn_prun_imply (p,pn,pr_branches) crt_br corr  = 
    let f = Cpure.eq_spec_var_aset corr.memo_group_aset in
    let f_f x =  
          if equalBFormula_f f x.memo_formula p then Some []
          else if equalBFormula_f f x.memo_formula pn then Some pr_branches
          else None in
    Util.list_find f_f corr.memo_group_cons


let memo_check_syn_prun p c corr =  memo_check_syn_prun_imply p c corr
    
let memo_check_syn_prun_debug (p,pn,br) c corr = 
  let _ = print_string (" Check_syn1: "^(!print_bf_f p)^"\n") in
  let _ = print_string (" Check_syn2: "^(!print_mp_f [corr])^"\n") in
    memo_check_syn_prun_imply (p,pn,br) c corr
    
let transform_memo_formula f l : memo_pure =
  let (f_memo,f_aset, f_formula, f_b_formula, f_exp) = f in
  let r = f_memo l in 
	match r with
	| Some e1 -> e1
	| None  -> List.map (fun c-> {
      memo_group_fv = c.memo_group_fv;
      memo_group_changed = true;
      memo_group_cons = List.map (fun c-> {c with memo_formula = transform_b_formula (f_b_formula,f_exp) c.memo_formula}) c.memo_group_cons;
      memo_group_slice = List.map (transform_formula f) c.memo_group_slice;
      memo_group_aset = match (f_aset c.memo_group_aset) with | None -> c.memo_group_aset | Some s-> s;
    }) l

let process_cons_l (f:memoised_constraint list):formula list =
  let filtl = List.filter (fun c-> match c.memo_status with | Implied_R -> false |_-> true) f in
  List.map (fun c-> BForm (c.memo_formula,None)) filtl 
  (*List.fold_left (fun a c -> match c with
    | Implied_dupl -> a
    | _ -> mkAnd a c.memo_group_cons no_pos) (mkTrue no_pos) f*)

    
let process_slice impl (f:memoised_group): formula * formula = 
  let asetf = fold_aset f.memo_group_aset in
  let rec red_test impl (l_red,l_must) l = match l with
    | [] -> (l_red,l_must)
    | x::xs -> 
      let nf = join_conjunctions (xs@l_must) in
      let totalf = mkAnd nf asetf no_pos in
      if (impl totalf x) then 
        red_test impl (x::l_red,l_must) xs
       else 
        red_test impl (l_red,x::l_must) xs in
  let l1,l2 = red_test impl ([],[]) (process_cons_l f.memo_group_cons)   in
  (join_conjunctions l1, join_conjunctions l2)
  
let check_redundant impl (f:memo_pure): unit = List.iter (fun c-> 
    let red_f,n_red_f = process_slice impl c in
    print_string ("redundant: "^(!print_p_f_f red_f)^"\n nonredundant: "^(!print_p_f_f n_red_f)^"\n" ) ) f
  
let isImpl_dupl c = match c.memo_status with | Implied_R -> true | _ -> false 
let isImplT c = match c.memo_status with | Implied_N -> true | _ -> false 
let isCtrInSet aset s c =  List.exists (fun d-> eq_b_formula aset c.memo_formula d.memo_formula) s  

let cons_filter (g:memo_pure) (f:memoised_constraint->bool) : memo_pure = 
    List.map (fun c-> {c with memo_group_cons = List.filter f c.memo_group_cons}) g

let slow_imply impl nf rhs =
  let x = Util.gen_time_msg () in
  try 
    (Util.push_time x;
    Util.push_time "slow_imply");
      let r = impl nf rhs in
      (Util.pop_time "slow_imply";
      Util.pop_time_to_s_no_count x);
      r                   
  with _ -> (Util.pop_time_to_s_no_count x ;false) 

let fast_imply_debug_cmp impl aset (lhs:b_formula list) (rhs:b_formula) : int =
  let lhs_f = join_conjunctions (List.map (fun c-> (BForm (c,None))) lhs) in
  let rhs_f = BForm (rhs,None) in
  let r = fast_imply aset lhs rhs in
  let s = slow_imply impl lhs_f rhs_f in
  if s && (r<=0) then 
    let _ = print_string ("fast imply aset :"^(Util.string_of_eq_set full_name_of_spec_var aset)^"\n") in
    let _ = print_string ("fast imply inp :"^(Util.string_of_a_list !print_b_formula lhs) )in
    let _ = print_string ("fast imply inp :"^" |="^(!print_b_formula rhs)^"\n") in
    let _ = print_string ("fast imply out : ==> "^(string_of_int r)^"\n") in
    r
  else r

let elim_redundant_cons(*_slow*) impl aset asetf pn =  
  let rec helper pn s r e f = match pn with
    | [] -> (s,r,e)
    | c::cs -> 
          if (isCtrInSet aset s c) then helper cs s r (c::e) f
          else 
            let conj_cs = join_conjunctions (List.map (fun c-> (BForm (c.memo_formula,None))) cs) in
            let nf = mkAnd f conj_cs no_pos in
            let b =  Util.push_time "erc_imply";
              let r = slow_imply impl nf (BForm (c.memo_formula,None)) in
              (Util.pop_time "erc_imply"; r)   in                
            if b then
              helper cs s ({c with memo_status = Implied_R}::r) e f
            else helper cs (c::s) r e (mkAnd f (BForm (c.memo_formula,None)) no_pos) in
  helper pn [] [] [] asetf

let elim_redundant_cons_fast impl aset asetf pn =  
  let rec helper pn mc s r e f = match pn,mc with
    | [],_ -> (s,r,e)
    | (c::cs),(m::ms) -> 
      let b = 
        (Util.push_time "erc_imply";
        let r = fast_imply(*_debug_cmp impl*) aset (ms@f) m in
          (Util.pop_time "erc_imply";r>0)) in
        if b then  helper cs ms s ({c with memo_status = Implied_R}::r) e f
        else helper cs ms (c::s) r e (m::f) 
    | _ -> Error.report_error {Error.error_loc = no_pos;Error.error_text = "elim_redundant_cons_fast: unexpected pattern"} in       
  let mc=List.map (fun x -> x.memo_formula) pn in    
  helper pn  mc [] [] [] []


(* let elim_redundant_slice impl (f:memoised_group): memoised_group*memoised_group = *)

let elim_redundant_slice (impl,simpl) (f:memoised_group): memoised_group*memoised_group = 
  let asetf = fold_aset f.memo_group_aset in
  let old_r_set , np_set  = List.partition isImpl_dupl f.memo_group_cons in
  let n_set, p_set  = List.partition isImplT np_set in
  let s_set,r_set, e_set =  elim_redundant_cons impl f.memo_group_aset asetf (n_set@p_set) in
  let r2 = { (List.hd (mkMFalse no_pos)) with memo_group_cons = e_set@r_set} in
  ({f with memo_group_cons = s_set @r_set @ old_r_set;
           memo_group_slice= List.concat (List.map (fun c-> list_of_conjs (simpl c)) f.memo_group_slice)},r2)
  
let elim_redundant_aux impl (f:memo_pure): memo_pure*memo_pure = 
  let b =   !suppress_warning_msg in
  suppress_warning_msg := true;
  let r = List.map (elim_redundant_slice impl) f in
  let r = List.split r in
  suppress_warning_msg := b;
  r
  
let elim_redundant impl (f:memo_pure): memo_pure = 
  if (not !Globals.disable_elim_redundant_ctr) then 
    (Util.push_time "elim_redundant_ctr";
    let r = fst (elim_redundant_aux impl f) in
    Util.pop_time "elim_redundant_ctr";
    r)
  else f
  

let elim_redundant_debug impl (f:memo_pure) : memo_pure  = 
  let r1,r2 = elim_redundant_aux impl f in
  print_string ("eliminate_redundant input: "^(!print_mp_f f)^"\n");
  print_string ("eliminate_redundant redundant: "^(!print_mp_f r2)^"\n");
  print_string ("eliminate_redundant result: "^(!print_mp_f r1)^"\n");
  r1

(* wrapper for fast_imply*)  
let fast_memo_imply (g:memoised_group) (f:b_formula):int = 
  let cons = List.map (fun c-> c.memo_formula) g.memo_group_cons in
  fast_imply(*_debug*) g.memo_group_aset cons f


let memo_check_syn_fast (p,pn,pr_branches) crt_br corr  = 
  match (fast_memo_imply corr pn) with
    | 1 -> Some pr_branches
    | _ -> match (fast_memo_imply corr p) with
        | 1 -> Some []
        | _ -> None
 
let replace_memo_pure_label nl f = 
  List.map (fun c-> {c with memo_group_slice = List.map (replace_pure_formula_label nl) c.memo_group_slice;}) f
 
 (* imply functions *)
 
    
let mimply_process_ante with_disj ante_disj conseq str str_time t_imply imp_no =
  let fv = fv conseq in
  let n_ante = List.filter(fun c-> (List.length (Util.intersect_fct eq_spec_var fv c.memo_group_fv))>0) ante_disj in 
  let r = match with_disj with  
    | 0 -> fold_mem_lst_gen (mkTrue no_pos) false true false true n_ante
    | 1 -> fold_mem_lst_no_disj (mkTrue no_pos) false true n_ante
    | _ -> fold_mem_lst (mkTrue no_pos) false true n_ante in
  let _ = Debug.devel_pprint str no_pos in
  (Util.push_time str_time; 
  let r = t_imply r conseq ("imply_process_ante"^(string_of_int !imp_no)) false in
  Util.pop_time str_time;
  r)
 
let mimply_one_conj ante_memo0 conseq  t_imply imp_no = 
  let xp01,xp02,xp03 = mimply_process_ante 0 ante_memo0 conseq 
    ("IMP #" ^ (string_of_int !imp_no) ^ "." ^ (string_of_int 1(*!imp_subno*)) ^ " with XPure0 no complex") 
    "imply_proc_one_ncplx" t_imply imp_no in  
  if not xp01  then  
    let xp01,xp02,xp03 = mimply_process_ante 2 ante_memo0 conseq 
      ("IMP #" ^ (string_of_int !imp_no) ^ "." ^ (string_of_int 1(*!imp_subno*)) ^ " with XPure0") 
      "imply_proc_one_full" t_imply imp_no in  
    if not xp01 then (Util.inc_counter "with_disj_cnt_2_f";(xp01,xp02,xp03)	)
    else (Util.inc_counter "with_disj_cnt_2_s";(xp01,xp02,xp03)	)
  else (Util.inc_counter "with_disj_cnt_0_s";(xp01,xp02,xp03)	)

let mimply_one_conj_debug ante_memo0 conseq_conj t_imply imp_no = 
  Util.ho_debug_4 "mimply_one_conj " (!print_mp_f) (!print_p_f_f) (fun _ -> "?")
  (fun x -> string_of_int !x)
  (fun (c,_,_)-> string_of_bool c) 
  (fun (x,_,_) -> not x)
  mimply_one_conj ante_memo0 conseq_conj t_imply imp_no

  
 
let rec mimply_conj ante_memo0 conseq_conj t_imply imp_no = 
  match conseq_conj with
    | h :: rest -> 
	      let (r1,r2,r3)=(mimply_one_conj(*_debug*) ante_memo0 h t_imply imp_no) in
	      if r1 then 
	        let r1,r22,r23 = (mimply_conj ante_memo0 rest t_imply imp_no) in
	        (r1,r2@r22,r23)
	      else 
            (*let _ = print_string ("\n failed ante: "^(Cprinter.string_of_pure_formula  
              (CP.fold_mem_lst (CP.mkTrue no_pos ) false ante_memo0))^"\t |- \t"^(Cprinter.string_of_pure_formula h)^"\n") in      *)
            (r1,r2,r3)
    | [] -> (true,[],None)
   
    
let rec imply_memo ante_memo0 conseq_memo t_imply imp_no 
    :  bool * (Globals.formula_label option * Globals.formula_label option) list * Globals.formula_label option = 
  match conseq_memo with
    | h :: rest -> 
          let r = fold_mem_lst_to_lst(*_debug*) [h] false false true in
          let r = List.concat (List.map list_of_conjs r) in
	      let (r1,r2,r3)=(mimply_conj ante_memo0 r t_imply imp_no) in
	      if r1 then 
	        let r1,r22,r23 = (imply_memo ante_memo0 rest t_imply imp_no) in
	        (r1,r2@r22,r23)
	      else (r1,r2,r3)
    | [] -> (true,[],None)
          
(*let imply_memo_debug ante_memo conseq_memo t_imply =
  let (r1,r2,r3)= imply_memo ante_memo conseq_memo in  
  print_string ("imply_memo input1: "^(!print_mp_f ante_memo)^"\n");
  print_string ("imply_memo input1: "^(!print_mp_f conseq_memo)^"\n");    
  print_string ("imply_memo output: "^(string_of_bool r1)^"\n");
  (r1,r2,r3)*)

let reset_changed f = List.map (fun c-> {c with memo_group_changed = false}) f
  
let trans_memo_group (e: memoised_group) (arg: 'a) f f_arg f_comb : (memoised_group * 'b) = 
  let f_grp, f_memo_cons, f_aset, f_slice,f_fv = f in
  match f_grp arg e with 
    | Some e1-> e1
    | None -> 
      let new_arg = f_arg arg e in
      let new_cons,new_rc  = List.split ((List.map (fun c-> f_memo_cons c new_arg)) e.memo_group_cons) in
      let new_aset, new_ra = f_aset new_arg e.memo_group_aset in
      let new_slice, new_rs = List.split ((List.map (fun c-> f_slice c new_arg)) e.memo_group_slice) in
      let new_fv, new_rv =  List.split ((List.map (fun c-> f_fv c new_arg)) e.memo_group_fv) in
      ({e with
        memo_group_fv =new_fv;
        memo_group_cons = new_cons;
        memo_group_slice = new_slice;
        memo_group_aset = new_aset;}, f_comb (new_rc@new_ra@new_rs@new_rv))
  
let trans_memo_formula (e: memo_pure) (arg: 'a) f f_arg f_comb : (memo_pure * 'b) = 
  let trans_memo_gr e = trans_memo_group e arg f f_arg f_comb in
  let ne, vals = List.split (List.map trans_memo_gr e) in
  (ne, f_comb vals)
 
 
 
type mix_formula = 
  | MemoF of memo_pure
  | OnePF of formula
  
let print_mix_f  = ref (fun (c:mix_formula) -> "printing not intialized")
  
let mix_of_pure f = 
    if (!Globals.allow_pred_spec) then  MemoF (memoise_add_pure_N (mkMTrue ()) f)
    else OnePF f
    
let pure_of_mix f = match f with
  | OnePF f-> f
  | MemoF f-> fold_mem_lst (mkTrue no_pos) false true f 
  
  
let mkMTrue pos = 
    if (!Globals.allow_pred_spec) then  MemoF (mkMTrue pos)
    else OnePF (mkTrue pos)
let mkMFalse pos = 
    if (!Globals.allow_pred_spec) then MemoF (mkMFalse pos)
    else OnePF (mkFalse pos)  
  
let isConstMFalse mx = match mx with
  | MemoF mf -> isConstMFalse mf
  | OnePF f -> isConstFalse f
  
let isConstMTrue mx = match mx with
  | MemoF mf -> isConstMTrue mf
  | OnePF f -> isConstTrue f
  
let m_apply_one s qp = match qp with
  | MemoF f -> MemoF (m_apply_one s f)
  | OnePF f -> OnePF (apply_one s f)
  
let memo_apply_one_exp s qp = match qp with
  | MemoF mf -> MemoF (memo_apply_one_exp s mf)
  | OnePF f -> OnePF (apply_one_exp s f)
 
let regroup_memo_group s =  match s with
  | MemoF mf -> MemoF (regroup_memo_group mf)
  | OnePF f -> s
 
let mfv f = match f with
  | MemoF mf -> mfv mf
  | OnePF f -> fv f
 
let merge_mems_m = merge_mems
 
let merge_mems f1 f2 slice_dup = match (f1,f2) with
  | MemoF f1, MemoF f2 -> MemoF (merge_mems f1 f2 slice_dup)
  | OnePF f1, OnePF f2 -> OnePF (mkAnd f1 f2 no_pos)
  | _ -> Error.report_error {Error.error_loc = no_pos;Error.error_text = "merge mems: wrong mix of memo and pure formulas"}
  
  
let merge_mems_debug f1 f2 slice_dup = 
  Util.ho_debug_3 "merge_mems " !print_mix_f !print_mix_f (fun x -> "?")
  !print_mix_f merge_mems f1 f2 slice_dup
  
  
 let replace_mix_formula_label lb s = match s with
  | MemoF f -> MemoF (replace_memo_pure_label lb f)
  | OnePF f -> OnePF (replace_pure_formula_label lb f)
 
 let transform_mix_formula f_p_t f = match f with
  | MemoF f -> MemoF (transform_memo_formula f_p_t f)
  | OnePF f -> OnePF (transform_formula f_p_t f)
  
 let memo_pure_push_exists qv f = match f with
  | MemoF f -> MemoF (memo_pure_push_exists qv f)
  | OnePF f -> OnePF (mkExists qv f None no_pos)
 
 let ptr_equations f = match f with
  | MemoF f -> ptr_equations f
  | OnePF f -> pure_ptr_equations f
 
 
 let filter_useless_memo_pure sim_f b fv f = match f with
  | MemoF f -> MemoF (filter_useless_memo_pure sim_f b fv f)
  | OnePF _ -> f
 
let fold_mem_lst_m = fold_mem_lst
 
let fold_mem_lst init_f with_dupl with_inv f :formula= match f with
  | MemoF f -> fold_mem_lst init_f with_dupl with_inv f 
  | OnePF f -> (mkAnd init_f f no_pos)
 
 let memoise_add_pure_N (f:mix_formula) (pf:formula) = match f with
  | MemoF f -> MemoF (memoise_add_pure_N f pf)
  | OnePF f -> OnePF (mkAnd f pf no_pos)
 
let memoise_add_pure_P_m = memoise_add_pure_P
let memoise_add_pure_P (f:mix_formula) (pf:formula) = match f with
  | MemoF f -> MemoF (memoise_add_pure_P f pf)
  | OnePF f -> OnePF (mkAnd f pf no_pos)
  
  
let simpl_memo_pure_formula b_f_f p_f_f f tp_simp = match f with
  | MemoF f -> MemoF (simpl_memo_pure_formula b_f_f p_f_f f tp_simp)
  | OnePF f -> OnePF (p_f_f f)
 
let memo_arith_simplify f = match f with
  | MemoF f -> MemoF (memo_arith_simplify f)
  | OnePF f -> OnePF (arith_simplify f)
 
let memo_is_member_pure sp f = match f with
  | MemoF f -> memo_is_member_pure sp f
  | OnePF f -> is_member_pure sp f
 
let mkOr_mems (f1: mix_formula) (f2: mix_formula) : mix_formula = match f1,f2 with
  | MemoF f1, MemoF f2 -> MemoF (mkOr_mems f1 f2)
  | OnePF f1, OnePF f2 -> OnePF (mkOr f1 f2 None no_pos)
  | _ -> Error.report_error {Error.error_loc = no_pos;Error.error_text = "mkOr_mems: wrong mix of memo and pure formulas"}
  
let subst_avoid_capture_memo from t f = match f with
  | MemoF f -> MemoF (subst_avoid_capture_memo from t f)
  | OnePF f -> OnePF (subst_avoid_capture from t f)
  
let memo_subst s f = match f with
  | MemoF f -> MemoF (memo_subst s f)
  | OnePF f -> OnePF (subst s f)  
 
let elim_redundant sf f = match f with
  | MemoF f -> MemoF (elim_redundant sf f)
  | OnePF _ -> f
 
let fold_mix_lst_to_lst npf with_dupl with_inv with_slice  = match npf with
  | MemoF f -> fold_mem_lst_to_lst f with_dupl with_inv with_slice 
  | OnePF f -> [f]
  
let get_subst_equation_memo_formula_vv p qvar = match p with
  | MemoF f -> 
    let l,f = get_subst_equation_memo_formula_vv f qvar in
     (l,MemoF f)
  | OnePF f -> 
    let l,f = get_subst_equation_formula_vv f qvar in
    (l,OnePF f)

let get_subst_equation_mix_formula p qvar only_vars = match p with
  | MemoF f -> 
    let l,f = get_subst_equation_memo_formula f qvar only_vars in
     (l,MemoF f)
  | OnePF f -> 
    let l,f = get_subst_equation_formula f qvar only_vars in
    (l,OnePF f)
    
let mix_cons_filter f fct = match f with
  | MemoF f -> MemoF (cons_filter f fct)
  | OnePF _ -> f

let combine_mix_branch (s:string) (f:mix_formula * 'a) = match (fst f) with
  | MemoF mf -> MemoF (combine_memo_branch s (mf,snd f))
  | OnePF pf -> OnePF (combine_branch s (pf,snd f))
 (*
 match f with
  | MemoF f -> 
  | OnePF f -> 
 *)
let mix_drop_null self l neg = match l with
  | MemoF l -> 
    let r = List.map (fun c -> {c with memo_group_slice = List.map (fun c-> drop_null c self neg ) c.memo_group_slice}) l in
    MemoF r
  | OnePF  pf -> 
    OnePF (drop_null pf self neg)
    
let drop_triv_grps f = match f with
  | MemoF f -> MemoF (fst (List.partition (fun c-> not (isConstGroupTrue c)) f))
  | OnePF _ -> f
  
let drop_pf f = match f with
  | MemoF f -> f
  | OnePF _ -> []
    
let trans_mix_formula (e: mix_formula) (arg: 'a) f f_arg f_comb : (mix_formula * 'b) = 
  let mf,pf = f in
  let ma,pa = f_arg in
  match e with
  | MemoF e-> 
    let f,r = trans_memo_formula e arg mf ma f_comb in
    (MemoF f, r)
  | OnePF e -> 
    let f,r = trans_formula e arg pf pa f_comb in
    (OnePF f,r)
    
    
let find_rel_constraints (f:mix_formula) (v_l :spec_var list):  mix_formula = match f with
  | MemoF f -> MemoF (List.filter (fun c-> not ((Util.intersect_fct eq_spec_var c.memo_group_fv v_l )==[]))f)
  | OnePF f -> OnePF (find_rel_constraints f v_l)
