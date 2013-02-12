=============================================================================================
cast.ml:
=============================================================================================
  prog struc changes:
	mutable prog_hp_decls : hp_decl list; (*only used to compare against some expected output????*)

								
   proc struc changes:
	  mutable proc_hpdefs: Cformula.hp_rel_def list;(*set of heap predicate constraints derived from this method*)
      mutable proc_callee_hpdefs: Cformula.hp_rel_def list;
		(*set of heap predicate constraints derived from calls in this method*)
		(*due to the bottom up inference they are always just copyed from the proc_hpdefs of called methods*)
		
		
   data structure:   used in prog_hp_decls
	and hp_decl = { 
		hp_name : ident; 
		hp_vars : P.spec_var list;
		hp_formula : F.formula;}
		
=============================================================================================
cformula:
=============================================================================================
  (*intermediary structure for heap predicate inference, stores a constraint on heap predicates
    used in the context fields: es_infer_hp_rel and returned by various methods in particular
	check_specs_infer*)
and hprel= {
    hprel_kind: CP.rel_cat;
    unk_svl: CP.spec_var list;
    unk_hps:(CP.spec_var*CP.spec_var list) list;
    predef_svl: CP.spec_var list;
    hprel_lhs: formula;
    hprel_rhs: formula
}


(*seems to be finished inferred relations, used in the rel_def_stk structure*)
(*although that stack seems more internal to the inference than anything else, 
 the results are never picked from the stack, rather they are returned by the inference method*)
and hprel_def= {
    hprel_def_kind: CP.rel_cat;
    hprel_def_hrel: h_formula;
    hprel_def_body: formula option;
    hprel_def_body_lib: formula option;
}

(
(*temporal: name * hrel * definition body*)
(*actually used to store the constraints on heap predicates inference*)
(*appears in the proc fields in the cast*)
and hp_rel_def = CP.rel_cat * h_formula * formula

added the heap type:  | HRel of (CP.spec_var * (CP.exp list) * loc)





=================================================================
main sa inference:
let infer_hps_x prog proc_name (hp_constrs: CF.hprel list)
   sel_hp_rels sel_post_hps hp_rel_unkmap 
    :(CF.hprel list * CF.hp_rel_def list* (CP.spec_var*CP.exp list * CP.exp list) list) =
  analize_unk
  split_rhs
  infer_hps_fix
  generalize_hps
  generalize_pure_def_from_hpunk
  def_subst_fix
  SAU.combine_hpdefs
  generate_hp_def_from_unk_hps
  unk_hps2
  rel_helper
  SAU.transform_unk_hps_to_pure
  check_eq_hpdef
  unify_branches_hpdef
  SAU.simp_tree
  match_hps_views
  collect_sel_hp_def
  let _ = List.iter (fun hp_def -> rel_def_stk # push hp_def) sel_hp_defs in
  
