#include "xdebug.cppo"
open VarGen
open Format
open Globals 
open Exc.GTable
open Lexing 
open Cast 
open Iformula
open Cformula
open Mcpure_D
open Gen.Basic 
open Label_only

module Cprinter =
	struct
		let string_of_typed_spec_var (x: Cpure.spec_var) =
		  Format.printf "%s" (Cprinter.string_of_typed_spec_var x)
		
		let string_of_spec_var (x: Cpure.spec_var) =
		  Format.printf "%s" (Cprinter.string_of_spec_var x)
		
		let string_of_imm (imm : Cformula.ann) =
		  Format.printf "%s" (Cprinter.string_of_imm imm)
		
		let string_of_cperm (perm : Cpure.spec_var option) =
		  Format.printf "%s" (Cprinter.string_of_cperm perm)
		
		let string_of_derv dr =
		  Format.printf "%s" (Cprinter.string_of_derv dr)
		
		let string_of_ident x =
		  Format.printf "%s" (Cprinter.string_of_ident x)
		
		(* let string_of_int_label (i,s) s2 =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_int_label (i,s) s2) *)
		
		(* let string_of_int_label_opt h s2 =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_int_label_opt h s2) *)
		
		let string_of_formula_type (t:formula_type) =
		  Format.printf "%s" (Cprinter.string_of_formula_type t)
		
		(* let string_of_formula_label (i,s) s2 =                            *)
		(*   Format.printf "%s" (Cprinter.string_of_formula_label (i, s) s2) *)
		
		(* let string_of_formula_label_pr_br (i,s) s2 =                            *)
		(*   Format.printf "%s" (Cprinter.string_of_formula_label_pr_br (i, s) s2) *)
		
		(* let string_of_formula_label_opt h s2 =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_formula_label_opt h s2) *)
		
		(* let string_of_control_path_id (i,s) s2 =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_control_path_id (i,s) s2) *)
		
		(* let string_of_control_path_id_opt h s2 =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_control_path_id_opt h s2) *)
		
		let string_of_formula_label_only x =
		  Format.printf "%s" (Cprinter.string_of_formula_label_only x)
		
		let string_of_iast_label_table table =
		  Format.printf "%s" (Cprinter.string_of_iast_label_table table)
		
		let string_of_formula_label_list l =
		  Format.printf "%s" (Cprinter.string_of_formula_label_list l)
		
		let string_of_memoise_constraint c =
		  Format.printf "%s" (Cprinter.string_of_memoise_constraint c)
		
		let string_of_remaining_branches c =
		  Format.printf "%s" (Cprinter.string_of_remaining_branches c)
		
		let string_of_ms (m:(Cpure.spec_var list) list) =
		  Format.printf "%s" (Cprinter.string_of_ms m)
		
		let string_of_formula_exp (e:Cpure.exp) =
		  Format.printf "%s" (Cprinter.string_of_formula_exp e)
		
		let string_of_memoised_list l =
		  Format.printf "%s" (Cprinter.string_of_memoised_list l)
		
		let string_of_slicing_label sl =
		  Format.printf "%s" (Cprinter.string_of_slicing_label sl)
		
		let string_of_b_formula (e:Cpure.b_formula) =
		  Format.printf "%s" (Cprinter.string_of_b_formula e)
		
		let string_of_mem_formula (e:Cformula.mem_formula) =
		  Format.printf "%s" (Cprinter.string_of_mem_formula e)
		
		let string_of_pure_formula (e:Cpure.formula) =
		  Format.printf "%s" (Cprinter.string_of_pure_formula e)
		
		let string_of_pure_formula_list_noparen l = 
		  Format.printf "%s" (Cprinter.string_of_pure_formula_list_noparen l)
		
		let string_of_pure_formula_list l =
		  Format.printf "%s" (Cprinter.string_of_pure_formula_list l)
		
		let string_of_h_formula (e:h_formula) =
		  Format.printf "%s" (Cprinter.string_of_h_formula e)
		
		let string_of_formula_branches l =
		  Format.printf "%s" (Cprinter.string_of_formula_branches l)
		
		(* let string_of_flow_formula f c =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_flow_formula f c) *)
		
		let string_of_dflow n =
		  Format.printf "%s" (Cprinter.string_of_dflow n)
		
		let string_of_sharp_flow sf =
		  Format.printf "%s" (Cprinter.string_of_sharp_flow sf)
		
		let string_of_one_formula f =
		  Format.printf "%s" (Cprinter.string_of_one_formula f)
		
		let string_of_one_formula_list ls =
		  Format.printf "%s" (Cprinter.string_of_one_formula_list ls)
		
		let string_of_formula (e:formula) =
		  Format.printf "%s" (Cprinter.string_of_formula e)
		
		let string_of_formula_list_noparen l = 
		  Format.printf "%s" (Cprinter.string_of_formula_list_noparen l)
		
		let string_of_formula_list l =
		  Format.printf "%s" (Cprinter.string_of_formula_list l)
		
		let string_of_formula_base (e:formula_base) =
		  Format.printf "%s" (Cprinter.string_of_formula_base e)
		
		let string_of_list_formula (e:list_formula) =
		  Format.printf "%s" (Cprinter.string_of_list_formula e)
		
		let string_of_lhs_rhs (e) =  
		  Format.printf "%s" (Cprinter.string_of_lhs_rhs e)
		
		let string_of_only_lhs_rhs (e) =
		  Format.printf "%s" (Cprinter.string_of_only_lhs_rhs e)
		
		let string_of_numbered_list_formula (e:list_formula) =  
		  Format.printf "%s" (Cprinter.string_of_numbered_list_formula e)
		
		let string_of_numbered_list_formula_trace (e: (context * (formula*formula_trace)) list) =  
		  Format.printf "%s" (Cprinter.string_of_numbered_list_formula_trace e)
		
		let string_of_numbered_list_formula_no_trace (e: (context * (formula*formula_trace)) list) =  
		  Format.printf "%s" (Cprinter.string_of_numbered_list_formula_no_trace e)
		
		(* let string_of_list_f (f:'a->string) (e:'a list) =    *)
		(*   Format.printf "%s" (Cprinter.string_of_list_f f e) *)
		
		let string_of_pure_formula_branches (f, l) =  
		  Format.printf "%s" (Cprinter.string_of_pure_formula_branches (f, l))
		
		let string_of_memo_pure_formula_branches (f, l) =
		  Format.printf "%s" (Cprinter.string_of_memo_pure_formula_branches (f, l))
		
		let string_of_memo_pure_formula (f: memo_pure) = 
		  Format.printf "%s" (Cprinter.string_of_memo_pure_formula f)
		
		let string_of_memoised_group g =
		  Format.printf "%s" (Cprinter.string_of_memoised_group g)
		
		let string_of_mix_formula (f: Mcpure.mix_formula) = 
		  Format.printf "%s" (Cprinter.string_of_mix_formula f)
		
		let string_of_mix_formula_list_noparen l = 
		  Format.printf "%s" (Cprinter.string_of_mix_formula_list_noparen l)
		
		let string_of_mix_formula_list l =
		  Format.printf "%s" (Cprinter.string_of_mix_formula_list l)
		
		let string_of_case_guard c =
		  Format.printf "%s" (Cprinter.string_of_case_guard c)
		
		let string_of_spec_var_list_noparen l = 
		  Format.printf "%s" (Cprinter.string_of_spec_var_list_noparen l)
		
		let string_of_spec_var_list l =
		  Format.printf "%s" (Cprinter.string_of_spec_var_list l)
		
		let string_of_typed_spec_var_list l =
		  Format.printf "%s" (Cprinter.string_of_typed_spec_var_list l)
		
		let string_of_struc_formula (e:struc_formula) =
		  Format.printf "%s" (Cprinter.string_of_struc_formula e)
		
		let string_of_prior_steps pt =
		  Format.printf "%s" (Cprinter.string_of_prior_steps pt)
		
		let string_of_path_trace  (pt : path_trace) =
		  Format.printf "%s" (Cprinter.string_of_path_trace pt)
		
		let summary_list_path_trace l =
		  Format.printf "%s" (Cprinter.summary_list_path_trace l)
		
		let summary_partial_context (l1,l2) =
		  Format.printf "%s" (Cprinter.summary_partial_context (l1,l2))
		
		let string_of_pos p =
		  Format.printf "%s" (Cprinter.string_of_pos p)
		
		let string_of_estate (es : entail_state) =
		  Format.printf "%s" (Cprinter.string_of_estate es)
		
		let string_of_entail_state x =
		  Format.printf "%s" (Cprinter.string_of_entail_state x)
		
		let string_of_failure_kind e_kind =
		  Format.printf "%s" (Cprinter.string_of_failure_kind e_kind)
		
		let string_of_failure_kind_full e_kind=
		  Format.printf "%s" (Cprinter.string_of_failure_kind_full e_kind)
		
		let string_of_list_loc ls =
		  Format.printf "%s" (Cprinter.string_of_list_loc ls)
		
		let string_of_list_int ls =
		  Format.printf "%s" (Cprinter.string_of_list_int ls)
		
		(*let string_of_fail_explaining fe =                          *)
		(*  Format.printf "%s" (Cprinter.string_of_fail_explaining fe)*)
		
		let string_of_fail_estate (es:fail_context) =
		  Format.printf "%s" (Cprinter.string_of_fail_estate es)
		
		let string_of_context (ctx: context) =
		  Format.printf "%s" (Cprinter.string_of_context ctx)
		
		let string_of_context_list ctx =
		  Format.printf "%s" (Cprinter.string_of_context_list ctx)
		
		let string_of_fail_type (e:fail_type) =
		  Format.printf "%s" (Cprinter.string_of_fail_type e)
		
		let string_of_context_short (ctx:context) =
		  Format.printf "%s" (Cprinter.string_of_context_short ctx)
		
		let string_of_list_context_short (ctx:list_context) =
		  Format.printf "%s" (Cprinter.string_of_list_context_short ctx)
		
		let string_of_context_list_short (ctx:context list) =
		  Format.printf "%s" (Cprinter.string_of_context_list_short ctx)
		
		let string_of_list_context (ctx:list_context) =
		  Format.printf "%s" (Cprinter.string_of_list_context ctx)
		
		let string_of_list_context_list (ctxl:list_context list) =
		  Format.printf "%s" (Cprinter.string_of_list_context_list ctxl)
		
		let string_of_entail_state_short (e:entail_state) =
		  Format.printf "%s" (Cprinter.string_of_entail_state_short e)
		
		let string_of_esc_stack e =
		  Format.printf "%s" (Cprinter.string_of_esc_stack e)
		
		let string_of_partial_context (ctx:partial_context) =
		  Format.printf "%s" (Cprinter.string_of_partial_context ctx)
		
		let string_of_partial_context_short (ctx:partial_context) =
		  Format.printf "%s" (Cprinter.string_of_partial_context_short ctx)
		
		let string_of_failesc_context (ctx:failesc_context) =
		  Format.printf "%s" (Cprinter.string_of_failesc_context ctx)
		
		let string_of_list_partial_context (lc: list_partial_context) =
		  Format.printf "%s" (Cprinter.string_of_list_partial_context lc)
		
		let string_of_list_partial_context_short (lc: list_partial_context) =
		  Format.printf "%s" (Cprinter.string_of_list_partial_context_short lc)
		
		let string_of_list_failesc_context (lc: list_failesc_context) =
		  Format.printf "%s" (Cprinter.string_of_list_failesc_context lc)
		
		let string_of_list_failesc_context_short (lc: list_failesc_context) =
		  Format.printf "%s" (Cprinter.string_of_list_failesc_context_short lc)
		
		let string_of_list_list_partial_context (lc:list_partial_context list) =
		  Format.printf "%s" (Cprinter.string_of_list_list_partial_context lc)
		
		let string_of_mater_property p =
		  Format.printf "%s" (Cprinter.string_of_mater_property p)
		
		let string_of_mater_prop_list l =
		  Format.printf "%s" (Cprinter.string_of_mater_prop_list l)
		
		let string_of_prune_invariants p =
		  Format.printf "%s" (Cprinter.string_of_prune_invariants p)
		
		let string_of_prune_invs inv_lst =
		  Format.printf "%s" (Cprinter.string_of_prune_invs inv_lst)
		
		let string_of_view_base_case (bc:(Cpure.formula * Mcpure.mix_formula) option) =
		  Format.printf "%s" (Cprinter.string_of_view_base_case bc)
		
		let string_of_view_decl (v: Cast.view_decl) =
		  Format.printf "%s" (Cprinter.string_of_view_decl v)
		
		(* let string_of_ident_list l c =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_ident_list l c) *)
		
		let str_ident_list l =
		  Format.printf "%s" (Cprinter.str_ident_list l)
		
		let string_of_constraint_relation m =
		  Format.printf "%s" (Cprinter.string_of_constraint_relation m)
		
		let string_of_formula_exp_list l =
		  Format.printf "%s" (Cprinter.string_of_formula_exp_list l)
		
		let string_of_flow_store l =
		  Format.printf "%s" (Cprinter.string_of_flow_store l)
		
		let string_of_t_formula x =
		  Format.printf "%s" (Cprinter.string_of_t_formula x)
		
		let string_of_formulae_list l =
		  Format.printf "%s" (Cprinter.string_of_formulae_list l)
		
		let string_of_sharp st =
		  Format.printf "%s" (Cprinter.string_of_sharp st)
		
		let string_of_read_only ro =
		  Format.printf "%s" (Cprinter.string_of_read_only ro)
		
		let string_of_exp x =
		  Format.printf "%s" (Cprinter.string_of_exp x)
		
		let string_of_decl d =
		  Format.printf "%s" (Cprinter.string_of_decl d)
		
		(* let string_of_decl_list l c =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_decl_list l c) *)
		
		let string_of_data_decl d =
		  Format.printf "%s" (Cprinter.string_of_data_decl d)
		
		let string_of_coercion_type (t:Cast.coercion_type) =
		  Format.printf "%s" (Cprinter.string_of_coercion_type t)
		
		let string_of_coercion_case (t:Cast.coercion_case) =
		  Format.printf "%s" (Cprinter.string_of_coercion_case t)
		
		(* let string_of_coerc_opt op c =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_coerc_opt op c) *)
		
		let string_of_coerc_short c =
		  Format.printf "%s" (Cprinter.string_of_coerc_short c)
		
		let string_of_coerc_med c =
		  Format.printf "%s" (Cprinter.string_of_coerc_med c)
		
		let string_of_coerc_long c =
		  Format.printf "%s" (Cprinter.string_of_coerc_long c)
		
		let string_of_coercion c =
		  Format.printf "%s" (Cprinter.string_of_coercion c)
		
		let string_of_coerc c =
		  Format.printf "%s" (Cprinter.string_of_coerc c)
		
		let string_of_coerc_list l = 
		  Format.printf "%s" (Cprinter.string_of_coerc_list l)
		
		(* let string_of_proc_decl p =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_proc_decl p) *)
		
		(* let string_of_proc_decl i p =                           *)
		(*   Format.printf "%s" (Cprinter.string_of_proc_decl i p) *)
		
		let string_of_data_decl_list l =
		  Format.printf "%s" (Cprinter.string_of_data_decl_list l)
		
		let string_of_proc_decl_list l =
		  Format.printf "%s" (Cprinter.string_of_proc_decl_list l)
		
		let string_of_proc_decl_list l =
		  Format.printf "%s" (Cprinter.string_of_proc_decl_list l)
		
		let string_of_view_decl_list l =
		  Format.printf "%s" (Cprinter.string_of_view_decl_list l)
		
		let string_of_rel_decl_list rdecls = 
		  Format.printf "%s" (Cprinter.string_of_rel_decl_list rdecls)
		
		let string_of_axiom_decl_list adecls = 
		  Format.printf "%s" (Cprinter.string_of_axiom_decl_list adecls)
		
		let string_of_coerc_decl_list l =
		  Format.printf "%s" (Cprinter.string_of_coerc_decl_list l)
		
		let string_of_prog_or_branches ((prg,br):prog_or_branches) =
		  Format.printf "%s" (Cprinter.string_of_prog_or_branches (prg, br))
		
		let string_of_program p = 
		  Format.printf "%s" (Cprinter.string_of_program p)
		
		let string_of_label_partial_context x =
		  Format.printf "%s" (Cprinter.string_of_label_partial_context x)
		
		let string_of_label_list_partial_context (cl:Cformula.list_partial_context) =
		  Format.printf "%s" (Cprinter.string_of_label_list_partial_context cl)
		
		let string_of_label_failesc_context x =
		  Format.printf "%s" (Cprinter.string_of_label_failesc_context x)
		
		let string_of_label_list_failesc_context (cl:Cformula.list_failesc_context) =
		  Format.printf "%s" (Cprinter.string_of_label_list_failesc_context cl)
		
		let string_of_failure_list_failesc_context (lc: Cformula.list_failesc_context) =  
		  Format.printf "%s" (Cprinter.string_of_failure_list_failesc_context lc)
		
		let string_of_failure_list_partial_context (lc: Cformula.list_partial_context) =  
		  Format.printf "%s" (Cprinter.string_of_failure_list_partial_context lc)
	end;;

module Iprinter =
	struct
		let string_of_unary_op x =
			Format.printf "%s" (Iprinter.string_of_unary_op x)
			
		let string_of_binary_op x = 
			Format.printf "%s" (Iprinter.string_of_binary_op x)
			
		let string_of_assign_op x = 
			Format.printf "%s" (Iprinter.string_of_assign_op x )
			
		let string_of_primed x =
			Format.printf "%s" (Iprinter.string_of_primed x)
			
		let string_of_label x =
			Format.printf "%s" (Iprinter.string_of_label x)
			
		(* let string_of_formula_label x =                           *)
		(* 	Format.printf "%s" (Iprinter.string_of_formula_label x) *)
			
		let string_of_spec_label x =
			Format.printf "%s" (Iprinter.string_of_spec_label x)
			
		let string_of_spec_label_def x =
			Format.printf "%s" (Iprinter.string_of_spec_label_def x)
			
		(* let string_of_formula_label_opt h s2 =                           *)
		(* 	Format.printf "%s" (Iprinter.string_of_formula_label_opt h s2) *)
			
		(* let string_of_control_path_id (i,s) s2 =                           *)
		(* 	Format.printf "%s" (Iprinter.string_of_control_path_id (i,s) s2) *)
			
		(* let string_of_control_path_id_opt h s2 =                           *)
		(* 	Format.printf "%s" (Iprinter.string_of_control_path_id_opt h s2) *)
			
		let string_of_var (c1,c2) =
			Format.printf "%s" (Iprinter.string_of_var (c1,c2))
			
		let string_of_var_list vl =
			Format.printf "%s" (Iprinter.string_of_var_list vl)
			
		let string_of_typed_var (t,id) =
			Format.printf "%s" (Iprinter.string_of_typed_var (t,id))
			
		let string_of_typed_var_list l =
			Format.printf "%s" (Iprinter.string_of_typed_var_list l)
			
		let string_of_id (id,p) =
			Format.printf "%s" (Iprinter.string_of_id (id,p))
			
		let string_of_formula_exp x =
			Format.printf "%s" (Iprinter.string_of_formula_exp x)
			
		let string_of_formula_exp_list l = 
			Format.printf "%s" (Iprinter.string_of_formula_exp_list l)
			
		let string_of_slicing_label sl =
			Format.printf "%s" (Iprinter.string_of_slicing_label sl)
			
		let string_of_b_formula (pf,il) =
			Format.printf "%s" (Iprinter.string_of_b_formula (pf,il))
			
		let string_of_pure_formula x =
			Format.printf "%s" (Iprinter.string_of_pure_formula x)
			
		let string_of_iperm perm =
			Format.printf "%s" (Iprinter.string_of_iperm perm)
			
		let string_of_h_formula x =
			Format.printf "%s" (Iprinter.string_of_h_formula x)
			
		let string_of_imm imm =
			Format.printf "%s" (Iprinter.string_of_imm imm)
			
		let string_of_one_formula (f:Iformula.one_formula) =
			Format.printf "%s" (Iprinter.string_of_one_formula f)
			
		let string_of_one_formula_list (f:Iformula.one_formula list) =
			Format.printf "%s" (Iprinter.string_of_one_formula_list f)
			
		let string_of_formula x =
			Format.printf "%s" (Iprinter.string_of_formula x)
			
		let string_of_struc_formula c =
			Format.printf "%s" (Iprinter.string_of_struc_formula c)
			
		let string_of_form_list l =
			Format.printf "%s" (Iprinter.string_of_form_list l)
			
		let string_of_exp x =
			Format.printf "%s" (Iprinter.string_of_exp x)
			
		let string_of_decl (d, pos, il) =
			Format.printf "%s" (Iprinter.string_of_decl (d, pos, il))
			
		(* let string_of_decl_list l c =                           *)
		(* 	Format.printf "%s" (Iprinter.string_of_decl_list l c) *)
			
		let string_of_data_decl d =
			Format.printf "%s" (Iprinter.string_of_data_decl d)
			
		let string_of_global_var_decl d =
			Format.printf "%s" (Iprinter.string_of_global_var_decl d)
			
		let string_of_view_decl v = 
			Format.printf "%s" (Iprinter.string_of_view_decl v)
			
		let string_of_view_vars v_vars =
			Format.printf "%s" (Iprinter.string_of_view_vars v_vars)
			
		let string_of_coerc_decl c =
			Format.printf "%s" (Iprinter.string_of_coerc_decl c)
			
		let string_of_param par = 
			Format.printf "%s" (Iprinter.string_of_param par)
			
		let string_of_param_list l = 
			Format.printf "%s" (Iprinter.string_of_param_list l)
			
		let string_of_proc_decl p =
			Format.printf "%s" (Iprinter.string_of_proc_decl p)
			
		let string_of_rel_decl p =
			Format.printf "%s" (Iprinter.string_of_rel_decl p)
			
		let string_of_data_decl_list l =
			Format.printf "%s" (Iprinter.string_of_data_decl_list l)
			
		let string_of_proc_decl_list l =
			Format.printf "%s" (Iprinter.string_of_proc_decl_list l)
			
		let string_of_view_decl_list l =
			Format.printf "%s" (Iprinter.string_of_view_decl_list l)
			
		let string_of_coerc_decl_list l =
			Format.printf "%s" (Iprinter.string_of_coerc_decl_list l)
			
		let string_of_const_decl c =
			Format.printf "%s" (Iprinter.string_of_const_decl c)
			
		let string_of_const_decl_list l =
			Format.printf "%s" (Iprinter.string_of_const_decl_list l)
			
		let string_of_enum_decl ed =
			Format.printf "%s" (Iprinter.string_of_enum_decl ed)
			
		let string_of_enum_decl_list l =
			Format.printf "%s" (Iprinter.string_of_enum_decl_list l)
			
		let string_of_global_var_decl_list l =
			Format.printf "%s" (Iprinter.string_of_global_var_decl_list l)
			
		let string_of_rel_decl_list rdecls =
			Format.printf "%s" (Iprinter.string_of_rel_decl_list rdecls)
			
		let string_of_axiom_decl_list adecls =
			Format.printf "%s" (Iprinter.string_of_axiom_decl_list adecls)
			
		let string_of_data cdef = 
			Format.printf "%s" (Iprinter.string_of_data cdef)
			
		let string_of_program p =
			Format.printf "%s" (Iprinter.string_of_program p)
	end;;