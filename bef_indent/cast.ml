#include "xdebug.cppo"
(*
  Created 21-Feb-2006

  AST for the core language
*)

open Globals
open VarGen
open Gen.Basic
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable


module F = Cformula
(* module CF = Cformula *)
module P = Cpure
(* module CP = Cpure *)
module MP = Mcpure
module Err = Error
module LO = Label_only.LOne
module CVP = CvpermUtils

(*used in Predicate*)
let pure_hprel_map = ref ([]: (ident * ident) list)

type typed_ident = (typ * ident)

and prog_decl = {
    mutable prog_data_decls : data_decl list;
    mutable prog_logical_vars : P.spec_var list;
    mutable prog_view_decls : view_decl list;
    mutable prog_rel_decls : rel_decl list; (* An Hoa : relation definitions *)
    mutable prog_templ_decls: templ_decl list;
    mutable prog_ut_decls: ut_decl list;
    mutable prog_hp_decls : hp_decl list; (*only used to compare against some expected output????*)
    mutable prog_view_equiv : (ident * ident) list; (*inferred with --pred-en-equiv*)
    mutable prog_axiom_decls : axiom_decl list; (* An Hoa : axiom definitions *)
    (*old_proc_decls : proc_decl list;*) (* To be removed completely *)
    new_proc_decls : (ident, proc_decl) Hashtbl.t; (* Mingled name with proc_delc *)
    (*mutable prog_left_coercions : coercion_decl list;*)
    (*mutable prog_right_coercions : coercion_decl list;*)
    prog_barrier_decls : barrier_decl list
}

and prog_or_branches = (prog_decl *
    ((MP.mix_formula * (ident * (P.spec_var list))) option) )

and data_field_ann =
  | VAL
  | REC
  | F_NO_ANN

and data_decl = {
    data_name : ident;
    data_pos : loc;
    data_fields : (typed_ident * (ident list) (* data_field_ann *)) list;
    data_parent_name : ident;
    data_invs : F.formula list;
    data_methods : proc_decl list; }

and ba_prun_cond = Gen.Baga(P.PtrSV).baga * formula_label

and mater_property = {
    mater_var : P.spec_var;
    mater_full_flag : bool;
    mater_target_view : ident list; (*the view to which it materializes*)
}

and barrier_decl = {
    barrier_thc : int;
    barrier_name : ident;
    barrier_shared_vars : P.spec_var list;
    barrier_tr_list : (int*int* F.struc_formula list) list ;
    barrier_def: F.struc_formula ;
    barrier_prune_branches: formula_label list; (* all the branches of a view *)
    barrier_prune_conditions: (P.b_formula * (formula_label list)) list;
    barrier_prune_conditions_state: (int * (formula_label list)) list;
    barrier_prune_conditions_perm: (Tree_shares.Ts.t_sh* (formula_label list)) list ;
    barrier_prune_conditions_baga: ba_prun_cond list;
    barrier_prune_invariants : (formula_label list * (Gen.Baga(P.PtrSV).baga * P.b_formula list )) list ;
}

and view_kind =
  | View_PRIM
  | View_NORM
  | View_EXTN
  | View_SPEC
  | View_DERV

and view_decl = {
    view_name : ident;
    view_ho_vars : (ho_flow_kind * P.spec_var * ho_split_kind)list;
    view_vars : P.spec_var list;
    view_cont_vars : P.spec_var list;
    view_seg_opz : P.formula option; (*pred is seg + base case is emp heap*)
    view_case_vars : P.spec_var list; (* predicate parameters that are bound to guard of case, but excluding self; subset of view_vars*)
    view_uni_vars : P.spec_var list; (*predicate parameters that may become universal variables of universal lemmas*)
    view_labels : LO.t list;
    view_modes : mode list;
    view_is_prim : bool;
    view_type_of_self : typ option;
    view_is_touching : bool;
    view_is_segmented : bool;
    view_is_tail_recursive: bool;        (* true if view is tail-recursively defined *)
    view_residents: P.spec_var list;     (* list of pointers reside in the memory allocated of view *) 
    view_forward_ptrs: P.spec_var list;                          (* forward, backward properties in *)
    view_forward_fields: (data_decl * ident) list;               (* definition of the view          *) 
    view_backward_ptrs: P.spec_var list;
    view_backward_fields: (data_decl * ident) list;
    view_kind : view_kind;
    view_prop_extns:  P.spec_var list; (*for extn views*)
    view_parent_name: ident option; (*for view_spec*)
    (*a map of shape <-> pure properties*)
    (*View_EXT have been applied in this view*)
    view_domains: (ident * int * int) list;(* (view_extn_name, r_pos (0 is self) , extn_arg_pos) list;*)
    (* below to detect @L in post-condition *)
    mutable view_contains_L_ann : bool;
    view_ann_params : (P.annot_arg * int) list;
    view_params_orig: (P.view_arg * int) list;
    mutable view_partially_bound_vars : bool list;
    mutable view_materialized_vars : mater_property list; (* view vars that can point to objects *)
    view_data_name : ident;
    view_formula : F.struc_formula; (* case-structured formula *)
    mutable view_user_inv : MP.mix_formula; (* XPURE 0 -> revert to P.formula*)
    view_mem : F.mem_perm_formula option; (* Memory Region Spec *)
    view_inv_lock : F.formula option;
    mutable view_fixcalc : (MP.mix_formula) option; (*XPURE 1 -> revert to P.formula*)
    mutable view_x_formula : (MP.mix_formula); (*XPURE 1 -> revert to P.formula*)
    (* exact baga *)
    mutable view_baga_inv : Excore.ef_pure_disj option;
    (* over-approx baga *)
    mutable view_baga_over_inv : Excore.ef_pure_disj option;
    mutable view_baga_x_over_inv : Excore.ef_pure_disj option;
    (* necessary baga *)
    mutable view_baga_under_inv : Excore.ef_pure_disj option;
    mutable view_xpure_flag : bool; (* flag to indicate if XPURE0 <=> XPURE1 *)
    mutable view_baga : Gen.Baga(P.PtrSV).baga;
    mutable view_addr_vars : P.spec_var list;
    (* if view has only a single eqn, then place complex subpart into complex_inv *)
    view_complex_inv : MP.mix_formula  option; (*COMPLEX INV for --eps option*)
    view_un_struc_formula : (Cformula.formula * formula_label) list ; (*used by the unfold, pre transformed in order to avoid multiple transformations*)
    view_linear_formula : (Cformula.formula * formula_label) list ;
    view_base_case : (P.formula *MP.mix_formula) option; (* guard for base case, base case*)
    view_prune_branches: formula_label list; (* all the branches of a view *)
    view_is_rec : bool;
    view_pt_by_self : ident list;
    view_prune_conditions: (P.b_formula * (formula_label list)) list;
    view_prune_conditions_baga: ba_prun_cond list;
    view_prune_invariants : (formula_label list * (Gen.Baga(P.PtrSV).baga * P.b_formula list )) list ;
    view_pos : loc;
    view_raw_base_case: Cformula.formula option;
    view_ef_pure_disj : Excore.ef_pure_disj option
}

(* An Hoa : relation *)
and rel_decl = {
    rel_name : ident;
    rel_vars : P.spec_var list;
    rel_formula : P.formula;}

and templ_decl = {
  templ_name: ident;
  templ_ret_typ: typ;
  templ_params: P.spec_var list;
  templ_body: P.exp option;
  templ_pos: loc;
}

(* Unknown Temporal Declaration *)
and ut_decl = {
  ut_name: ident;
  ut_params: P.spec_var list;
  ut_is_pre: bool;
  ut_pos: loc;
}


and hp_decl = {
    hp_name : ident;
    mutable hp_vars_inst : (P.spec_var * Globals.hp_arg_kind) list;
    hp_part_vars: (int list) list; (*partition vars into groups e.g. pointer + pure properties*)
    mutable hp_root_pos: int;
    hp_is_pre: bool;
    hp_formula : F.formula;}

(** An Hoa : axiom *)
and axiom_decl = {
    axiom_id : int;
    axiom_hypothesis : P.formula;
    axiom_conclusion : P.formula; }

and proc_decl = {
    proc_name : ident;
    proc_args : typed_ident list;
    proc_ho_arg : typed_ident option;
    proc_args_wi: (ident*hp_arg_kind) list;
    proc_imm_args : (ident * bool) list;
    proc_source : ident; (* source file *)
    proc_return : typ;
    proc_flags : (ident*ident*(flags option)) list;
    mutable proc_important_vars : P.spec_var list; (* An Hoa : pre-computed list of important variables; namely the program parameters & logical variables in the specification that need to be retained during the process of verification i.e. such variables should not be removed when we perform simplification. Remark - all primed variables are important. *)
    (* WN : warning below is being supecedd by proc_stk_of_static_specs *)
    proc_static_specs : Cformula.struc_formula;
    (* proc_static_specs_with_pre : Cformula.struc_formula; *)
    (* this puts invariant of pre into the post-condition *)
    proc_dynamic_specs : Cformula.struc_formula;
    (*proc_dynamic_specs_with_pre : Cformula.struc_formula;*)
    (* stack of static specs inferred *)
    proc_stk_of_static_specs : Cformula.struc_formula Gen.stack;
    mutable proc_hprel_ass: (Cformula.hprel list * nflow) list;
    mutable proc_hprel_unkmap: ((P.spec_var * int list) * P.xpure_view) list;
    mutable proc_sel_hps: P.spec_var list;
    mutable proc_sel_post_hps: P.spec_var list;
    mutable proc_hpdefs: Cformula.hp_rel_def list;(*set of heap predicate constraints derived from this method*)
    mutable proc_callee_hpdefs: Cformula.hp_rel_def list;
    proc_verified_domains: infer_type list;
    (*set of heap predicate constraints derived from calls in this method*)
    (*due to the bottom up inference they are always just copyed from the proc_hpdefs of called methods*)
    proc_by_name_params : P.spec_var list;
    proc_by_copy_params: P.spec_var list;
    proc_by_value_params: P.spec_var list;
    proc_body : exp option;
    (* Termination: Set of logical variables of the proc's scc group *)
    proc_logical_vars : P.spec_var list;
    proc_call_order : int;
    proc_is_main : bool;
    proc_is_invoked : bool;
    proc_is_recursive : bool;
    proc_file : string;
    proc_loc : loc;
    (* None - not while, Some(true) : while with ret *)
    (* proc_while_with_return : bool option;  *)
    proc_test_comps :  test_comps option}

and test_comps = 
    {
        expected_ass: (ident list * ident list *(Cformula.formula * Cformula.formula) list) option;
        expected_hpdefs: (ident list * ident list *(Cformula.formula * Cformula.formula) list) option;
    }

(*TODO: should we change lemma need struc formulas?
  would this help with lemma folding later? *)

(* TODO : coercion type ->, <-, <-> just added *)
and coercion_case =
  | Simple
  | Complex
  | Ramify
  | Normalize of bool 
        (* 
           |LHS| > |RHS| --> Normalize of true --> combine
           |LHS| < |RHS| --> Normalize of false --> split
           Otherwise, simple or complex
        *)

and coercion_decl = { 
    coercion_type : coercion_type;
    coercion_exact : bool;
    coercion_name : ident;
    coercion_head : F.formula; (* used as antecedent during --elp *)
    coercion_head_norm : F.formula; (* used as consequent during --elp *)
    coercion_body : F.formula; (* used as antecedent during --elp *)
    coercion_body_norm : F.struc_formula; (* used as consequent during --elp *)
    coercion_impl_vars : P.spec_var list; (* list of implicit vars *)
    coercion_univ_vars : P.spec_var list; (* list of universally quantified variables. *)

    coercion_infer_vars :  P.spec_var list;
    (* coercion_proof : exp; *)
    (* coercion_head_exist : F.formula;   *)
 
    (* this used to build a defn for folding right lemma *)
    coercion_fold_def : view_decl Gen.mut_option;
 
    (* same as head except for annotation to self node? *)
    coercion_head_view : ident; 
    (* the name of the predicate where this coercion can be applied *)
    coercion_body_view : ident;  (* used for cycles checking *)
    coercion_mater_vars : mater_property list;
    (* coercion_simple_lhs :bool; (\* signify if LHS is simple or complex *\) *)
    coercion_case : coercion_case; (*Simple or Complex*)
    coercion_type_orig: coercion_type option; 
    coercion_kind: lemma_kind;
    coercion_origin: lemma_origin;
}

and coercion_type = Iast.coercion_type
    (* | Left *)
    (* | Equiv *)
    (* | Right *)
    

and sharp_flow = 
  | Sharp_ct of F.flow_formula
  | Sharp_id of ident

        
and sharp_val = 
  | Sharp_no_val (* captures flow without a value *)
  | Sharp_flow of ident   (* capture flow explicitly and a value*)
  | Sharp_var of typed_ident (* captures flow through a var *)

(* An Hoa : v[i] where v is an identifier and i is an expression *)
(* and exp_arrayat = { exp_arrayat_type : P.typ; (* Type of the array element *)
   exp_arrayat_array_base : ident; (* Name of the array *)
   exp_arrayat_index : exp; (* Integer valued expression for the index *)
   exp_arrayat_pos : loc; } *)

(* An Hoa : The exp_assign in core representation does not allow lhs to be another expression so array modification statement is necessary *)
(* and exp_arraymod = { exp_arraymod_lhs : exp_arrayat; (* v[i] *)
   exp_arraymod_rhs : exp;
   exp_arraymod_pos : loc } *)

and exp_assert = {
    exp_assert_asserted_formula : F.struc_formula option;
    exp_assert_assumed_formula : F.formula option;
    exp_assert_path_id : formula_label;
    exp_assert_type : assert_type;
    exp_assert_pos : loc }

and exp_assign =
    { exp_assign_lhs : ident;
    exp_assign_rhs : exp;
    exp_assign_pos : loc }

and exp_bconst = {
    exp_bconst_val : bool;
    exp_bconst_pos : loc }

and exp_bind = {
    exp_bind_type : typ; (* the type of the entire bind construct, i.e. the type of the body *)
    exp_bind_bound_var : typed_ident;
    exp_bind_fields : typed_ident list;
    exp_bind_body : exp;
    exp_bind_imm : P.ann;
    exp_bind_param_imm : P.ann list;
    exp_bind_read_only : bool; (*for frac perm, indicate whether the body will read or write to bound vars in exp_bind_fields*)
    exp_bind_path_id : control_path_id_strict;
    exp_bind_pos : loc }

and exp_block = { 
  exp_block_type : typ;
  exp_block_body : exp;
  exp_block_local_vars : typed_ident list;
  exp_block_pos : loc }

and exp_barrier = {exp_barrier_recv : typed_ident; exp_barrier_pos : loc}

and exp_cast = {
    exp_cast_target_type : typ;
    exp_cast_body : exp;
    exp_cast_pos : loc }

and exp_cond = { exp_cond_type : typ;
exp_cond_condition : ident;
exp_cond_then_arm : exp;
exp_cond_else_arm : exp;
exp_cond_path_id : control_path_id_strict;
exp_cond_pos : loc }

and exp_debug = {
    exp_debug_flag : bool;
    exp_debug_pos : loc }

and exp_fconst = {
    exp_fconst_val : float;
    exp_fconst_pos : loc }

(* instance call *)
and exp_icall = { exp_icall_type : typ;
exp_icall_receiver : ident;
exp_icall_receiver_type : typ;
exp_icall_method_name : ident;
exp_icall_arguments : ident list;
exp_icall_is_rec : bool; (* set for each mutual-recursive call *)
(*exp_icall_visible_names : P.spec_var list;*) (* list of visible names at location the call is made *)
exp_icall_path_id : control_path_id;
exp_icall_pos : loc }

and exp_iconst = {
    exp_iconst_val : int;
    exp_iconst_pos : loc }

and exp_new = {
    exp_new_class_name : ident;
    exp_new_parent_name : ident;
    exp_new_arguments : typed_ident list;
    exp_new_pos : loc }

and exp_return = { exp_return_type : typ;
exp_return_val : ident option;
exp_return_pos : loc }

(* static call *)
and exp_scall = { 
  exp_scall_type : typ;
  exp_scall_method_name : ident;
  exp_scall_lock : ident option;
  exp_scall_arguments : ident list;
  exp_scall_ho_arg : F.formula option;
  exp_scall_is_rec : bool; (* set for each mutual-recursive call *)
  (*exp_scall_visible_names : P.spec_var list;*) (* list of visible names at location the call is made *)
  exp_scall_path_id : control_path_id;
  exp_scall_pos : loc }

and exp_seq = { exp_seq_type : typ;
exp_seq_exp1 : exp;
exp_seq_exp2 : exp;
exp_seq_pos : loc }

and exp_sharp = {
    exp_sharp_type : typ;
    exp_sharp_flow_type :sharp_flow;(*the new flow*)
    exp_sharp_val :sharp_val;(*returned value*)
    exp_sharp_unpack : bool;(*true if it must get the new flow from the second element of the current flow pair*)
    exp_sharp_path_id : control_path_id;
    exp_sharp_pos : loc;
}

and exp_catch = {
    exp_catch_flow_type : nflow (* nflow *) ;
    exp_catch_flow_var : ident option;
    exp_catch_var : typed_ident option;
    exp_catch_body : exp;
    exp_catch_pos : loc }

and exp_try = { exp_try_type : typ;
exp_try_body : exp;
exp_try_path_id : control_path_id_strict;
exp_catch_clause : exp ;
exp_try_pos : loc }

and exp_this = { exp_this_type : typ;
exp_this_pos : loc }

and exp_var = { exp_var_type : typ;
exp_var_name : ident;
exp_var_pos : loc }

(* An Hoa : Empty array - only for initialization purpose *)
and exp_emparray = { exp_emparray_type : typ;
exp_emparray_dim : int;
exp_emparray_pos : loc }

and exp_var_decl = { 
  exp_var_decl_type : typ;
  exp_var_decl_name : ident;
  exp_var_decl_pos : loc }

and exp_while = { 
    exp_while_condition : ident;
    exp_while_body : exp;
    exp_while_spec : Cformula.struc_formula (*multi_spec*);
    exp_while_path_id : control_path_id;
    exp_while_pos : loc }

and exp_dprint = { 
    exp_dprint_string : ident;
    exp_dprint_visible_names : ident list;
    exp_dprint_pos : loc }

and exp_unfold = { 
    exp_unfold_var : P.spec_var;
    exp_unfold_pos : loc }

and exp_check_ref = { 
    exp_check_ref_var : ident;
    exp_check_ref_pos : loc }

and exp_java = { 
    exp_java_code : string;
    exp_java_pos : loc}
and exp_label = {
    exp_label_type : typ;
    exp_label_path_id : (control_path_id * path_label);
    exp_label_exp: exp;}
    
and exp_par = {
  exp_par_vperm: CVP.vperm_sets;
  exp_par_lend_heap: F.formula;
  exp_par_cases: exp_par_case list;
  exp_par_pos: loc;
}

and exp_par_case = {
  exp_par_case_cond: F.formula option;
  exp_par_case_vperm: CVP.vperm_sets;
  exp_par_case_body: exp;
  exp_par_case_else: bool;
  exp_par_case_pos: loc;
}
    
and exp = (* expressions keep their types *)
    (* for runtime checking *)
  | Label of exp_label
  | CheckRef of exp_check_ref
  | Java of exp_java
        (* standard expressions *)
	(* | ArrayAt of exp_arrayat (* An Hoa *) *)
	(* | ArrayMod of exp_arraymod (* An Hoa *) *)
  | Assert of exp_assert
  | Assign of exp_assign
  | BConst of exp_bconst
  | Bind of exp_bind
  | Block of exp_block
  | Barrier of exp_barrier
  | Cond of exp_cond
  | Cast of exp_cast
  | Catch of exp_catch
  | Debug of exp_debug
  | Dprint of exp_dprint
  | FConst of exp_fconst
        (*
	  | FieldRead of (P.typ * (ident * P.typ) * (ident * int) * loc) 
        (* v.f --> (type of f, v, (f, position of f in field list), pos *)
	  | FieldWrite of ((ident * P.typ) * (ident * int) * ident * loc) 
        (* field assignment is flattened to form x.f = y only *)
        *)
  | ICall of exp_icall
  | IConst of exp_iconst
	(*| ArrayAlloc of exp_aalloc *) (* An Hoa *)
  | New of exp_new
  | Null of loc
  | EmptyArray of exp_emparray (* An Hoa : add empty array as default value for array declaration *)
  | Print of (int * loc)
        (* | Return of exp_return*)
  | SCall of exp_scall
  | Seq of exp_seq
  | This of exp_this
  | Time of (bool*string*loc)
  | Var of exp_var
  | VarDecl of exp_var_decl
  | Unfold of exp_unfold
  | Unit of loc
  | While of exp_while
  | Sharp of exp_sharp
  | Try of exp_try
  | Par of exp_par

(* Stack of Template Declarations *)
let templ_decls: templ_decl Gen.stack = new Gen.stack

(* Stack of Unknown Temporal Declarations *)
let ut_decls: ut_decl Gen.stack = new Gen.stack

let get_sharp_flow sf = match sf with
  | Sharp_ct ff -> ff.F.formula_flow_interval
  | Sharp_id id -> exlist # get_hash id


let print_mix_formula = ref (fun (c:MP.mix_formula) -> "cpure printer has not been initialized")
let print_b_formula = ref (fun (c:P.b_formula) -> "cpure printer has not been initialized")
let print_h_formula = ref (fun (c:F.h_formula) -> "cpure printer has not been initialized")
let print_exp = ref (fun (c:P.exp) -> "cpure printer has not been initialized")
let print_prog_exp = ref (fun (c:exp) -> "cpure printer has not been initialized")
let print_formula = ref (fun (c:F.formula) -> "cform printer has not been initialized")
let print_dflow = ref (fun (c:Exc.GTable.nflow) -> "cpure printer has not been initialized")
let print_pure_formula = ref (fun (c:P.formula) -> "cform printer has not been initialized")
let print_spec_var_list = ref (fun (c:P.spec_var list) -> "cpure printer has not been initialized")
let print_struc_formula = ref (fun (c:F.struc_formula) -> "cpure printer has not been initialized")
let print_svl = ref (fun (c:P.spec_var list) -> "cpure printer has not been initialized")
let print_sv = ref (fun (c:P.spec_var) -> "cpure printer has not been initialized")
let print_mater_prop = ref (fun (c:mater_property) -> "cast printer has not been initialized")
let print_mater_prop_list = ref (fun (c:mater_property list) -> "cast printer has not been initialized")

(*single node -> simple (true), otherwise -> complex (false*)
(* let is_simple_formula x = true *)

let print_program = ref (fun (c:prog_decl) -> "cast printer has not been initialized")
let print_proc_decl_no_body = ref (fun (c:proc_decl) -> "cast printer has not been initialized")
let print_view_decl = ref (fun (c:view_decl) -> "cast printer has not been initialized")
let print_view_decl_short = ref (fun (c:view_decl) -> "cast printer has not been initialized")
let print_view_decl_clean = ref (fun (c:view_decl) -> "cast printer has not been initialized")
let print_hp_decl = ref (fun (c:hp_decl) -> "cast printer has not been initialized")
let print_coercion = ref (fun (c:coercion_decl) -> "cast printer has not been initialized")
let print_coerc_decl_list = ref (fun (c:coercion_decl list) -> "cast printer has not been initialized")
let print_mater_prop_list = ref (fun (c:mater_property list) -> "cast printer has not been initialized")

let slk_of_view_decl = ref (fun (c:view_decl) -> "cast printer has not been initialized")
let slk_of_data_decl = ref (fun (c:data_decl) -> "cast printer has not been initialized")

(* imply function has not been initialized yet *)
let imply_raw = ref (fun (ante: P.formula) (conseq: P.formula) -> false)


(** An Hoa [22/08/2011] Extract data field information **)

let is_primitive_proc p = (*p.proc_body==None*) not p.proc_is_main

let is_primitive_rel rel = 
  let eq_str s1 s2 = (String.compare s1 s2 == 0) in
  (eq_str rel.rel_name "dom") || (eq_str rel.rel_name "domb") 

let name_of_proc p = p.proc_name


let get_field_typ (f,_) = fst f

let get_field_name (f,_) = snd f

(** An Hoa [22/08/2011] End **)

(* transform each proc by a map function *)
(* Replaced by proc_decls_map f_p prog *)
(*
let map_proc (prog:prog_decl)
  (f_p : proc_decl -> proc_decl) : prog_decl =
  { prog with
      prog_proc_decls = List.map (f_p) prog.prog_proc_decls;
  }
*)

(* Sort a list of proc_decl by proc_call_order *)
let sort_proc_decls (pl: proc_decl list) : proc_decl list =
  List.fast_sort (fun p1 p2 -> p1.proc_call_order - p2.proc_call_order) pl

let same_call_scc p1 p2 = p1.proc_call_order == p2.proc_call_order

(* returns (procs_wo_body, proc_mutual_rec list) *)
(* The list of proc_decl must be sorted *)
let re_proc_mutual (pl : proc_decl list) : (proc_decl list * ((proc_decl list) list) ) = 
  let (pr_prim, pr_rest) = List.partition is_primitive_proc pl in
  let rec helper acc pl = match pl with
    | [] -> if acc==[] then [] else [acc]
    | x::rest -> 
          begin
            match acc with
              | [] -> helper [x] rest
              | a::_ -> if same_call_scc a x then helper (x::acc) rest
                else acc::(helper [x] rest)
          end
  in (pr_prim, helper [] pr_rest)

(* Create a hash table which contains 
 * a list of proc_decl *)
let create_proc_decls_hashtbl (cp: proc_decl list) : (ident, proc_decl) Hashtbl.t =
  let h_tbl = Hashtbl.create 20 in
  let () = List.iter (fun p -> Hashtbl.add h_tbl (p.proc_name) p) cp in
  h_tbl

let replace_proc cp new_proc =
  let id = new_proc.proc_name in
  let () = Hashtbl.replace cp.new_proc_decls id new_proc in
  cp

let proc_decls_map f decls =
  let () = Hashtbl.iter (fun i p -> 
    let np = f p in
    Hashtbl.replace decls i np   
  ) decls in
  decls

(* returns Not_found if id not in prog_decls *)
let find_proc cp id =
  Hashtbl.find cp.new_proc_decls id

(* returns None if id not in prog_decls *)
let find_proc_opt cp id =
  try 
    Some (find_proc cp id)
  with _ -> None

let list_of_procs cp =
  Hashtbl.fold (fun id pd lst -> pd::lst) cp.new_proc_decls []

let re_proc_mutual_from_prog cp : (proc_decl list * ((proc_decl list) list) ) = 
  let lst = list_of_procs cp
  in re_proc_mutual lst

let mater_prop_var a = a.mater_var 
let mater_prop_cmp_var a c = P.eq_spec_var_ident a.mater_var c.mater_var 
let mk_mater_prop v ff tv = {mater_var=v; mater_full_flag = ff; mater_target_view = tv}
let mater_prop_cmp c1 c2 = P.spec_var_cmp c1.mater_var c2.mater_var
let merge_mater_views v1 v2 = match v1,v2 with
  | [],[] -> ([],true) 
  | [],_ -> ([],false)
  | _ ,[] -> ([],false)
  | _ -> 
    if (List.length v1 == 1 && List.length v2 == 1) then
      if (String.compare (List.hd v1)(List.hd v2) == 0) then (v1,true)
      else (v1@v2,false)
    else (v1@v2,false)
  
let merge_mater_props_x x y = 
  let nl,flag = merge_mater_views x.mater_target_view y.mater_target_view in
  mk_mater_prop x.mater_var (x.mater_full_flag && y.mater_full_flag && flag)  nl

let merge_mater_props x y =
  let pr = !print_mater_prop in
  Debug.no_2 "merge_mater_props" pr pr pr merge_mater_props_x x y
  
let mater_props_to_sv_list l =  List.map (fun c-> c.mater_var) l
  
let subst_mater_list fr t l = 
  let lsv = List.combine fr t in
  (* let () = print_string "subst_mater_list: inside \n" in (\*LDK*\) *)
  List.map (fun c-> 
      {c with mater_var = P.subs_one lsv c.mater_var
              (* ; mater_var = P.subs_one lsv c.mater_var *)
      }) l

let subst_mater_list_nth i fr t l = 
  let pr_svl = !print_svl in
  Debug.no_2_num i "subst_mater_list" pr_svl pr_svl pr_no (fun _ _ -> subst_mater_list fr t l) fr t 

let subst_mater_list_nth i fr t l = 
  let pr_svl = !print_svl in
  Debug.no_3_num i "subst_mater_list" pr_svl pr_svl !print_mater_prop_list !print_mater_prop_list  subst_mater_list fr t l

let subst_coercion fr t (c:coercion_decl) = 
      {c with coercion_head = F.subst_avoid_capture fr t c.coercion_head
              ; coercion_body = F.subst_avoid_capture fr t c.coercion_body
      }
 
let subst_coercion fr t (c:coercion_decl) = 
  let pr = !print_coercion in
  Debug.no_1 "subst_coercion" pr pr (fun _ -> subst_coercion fr t c ) c

(* process each proc into some data which are then combined,
   e.g. verify each method and collect the failure points
*)
(* The following function is replace by proc_decls_fold *)
(*
let fold_proc (prog:prog_decl)
  (f_p : proc_decl -> 'b) (f_comb: 'b -> 'b -> 'b) (zero:'b) : 'b =
  List.fold_left (fun x p -> f_comb (f_p p) x) 
		zero prog.prog_proc_decls
*)

let proc_decls_fold (prog: prog_decl)
  (f_p : proc_decl -> 'b) (f_comb: 'b -> 'b -> 'b) (zero:'b) : 'b =
  Hashtbl.fold (fun id p acc -> f_comb (f_p p) acc) prog.new_proc_decls zero

(* iterate each proc to check for some property *)
(* The following function is replace by proc_decls_iter *) 
(*
let iter_proc (prog:prog_decl) (f_p : proc_decl -> unit) : unit =
  fold_proc prog (f_p) (fun _ _ -> ()) ()
*)

let proc_decls_iter (prog:prog_decl) (f_p : proc_decl -> unit) : unit =
  proc_decls_fold prog (f_p) (fun _ _ -> ()) ()

(*let arrayat_of_exp e = match e with
	| ArrayAt t -> t
	| _ -> failwith "arrayat_of_exp :: input is not case ArrayAt of exp"*)

let transform_exp (e:exp) (init_arg:'b)(f:'b->exp->(exp* 'a) option)  (f_args:'b->exp->'b)(comb_f:'a list -> 'a) (zero:'a) :(exp * 'a) =
  let rec helper (in_arg:'b) (e:exp) :(exp* 'a) =	
    match (f in_arg e) with
      | Some e1 -> e1
      | None  -> 
	        let n_arg = f_args in_arg e in
	        match e with
	          | Assert _
	          | Java _
	          | CheckRef _ 
	          | BConst _
	          | Debug _
	          | Dprint _
	          | FConst _
	          | ICall _
	          | IConst _
						(* | ArrayAlloc _ *) (* An Hoa *)
	          | New _
	          | Null _
						| EmptyArray _ (* An Hoa *)
	          | Print _
			  | Barrier _
	          | SCall _
	          | This _
	          | Time _
	          | Var _
	          | VarDecl _
	          | Unfold _
	          | Unit _
	          | Sharp _
		          -> (e, zero)
	          | Label b ->
		            let e1,r1 = helper n_arg b.exp_label_exp  in
		            (Label { b with exp_label_exp = e1;}, r1)
	          | Assign b ->
		            let e1,r1 = helper n_arg b.exp_assign_rhs in
		            (Assign { b with exp_assign_rhs = e1; }, r1)
						(* | ArrayAt b -> (* An Hoa *)
		            let e1,r1 = helper n_arg b.exp_arrayat_index in
		            (ArrayAt { b with exp_arrayat_index = e1; }, r1) *)
						(* | ArrayMod b ->
								let e1,r1 = helper n_arg (ArrayAt b.exp_arraymod_lhs) in
		            let e2,r2 = helper n_arg b.exp_arraymod_rhs in
		            (ArrayMod { b with exp_arraymod_lhs = (arrayat_of_exp e1); exp_arraymod_rhs = e2; }, comb_f [r1;r2]) *)
	          | Bind b ->
		            let e1,r1 = helper n_arg b.exp_bind_body  in
		            (Bind { b with exp_bind_body = e1; }, r1)
	          | Block b ->
		            let e1,r1 = helper n_arg b.exp_block_body in
		            (Block { b with exp_block_body = e1; }, r1)		         
	          | Cond b ->
		            let e1,r1 = helper n_arg b.exp_cond_then_arm in
		            let e2,r2 = helper n_arg b.exp_cond_else_arm in
		            let r = comb_f [r1;r2] in
		            (Cond {b with
			            exp_cond_then_arm = e1;
			            exp_cond_else_arm = e2;},r)
	          | Cast b -> 
                    let e1,r1 = helper n_arg b.exp_cast_body  in  
		            (Cast {b with exp_cast_body = e1},r1)
              | Catch b ->
                    let e1,r1 = helper n_arg b.exp_catch_body in
                    (Catch {b with exp_catch_body = e1},r1)
	          | Seq b ->
		            let e1,r1 = helper n_arg b.exp_seq_exp1 in 
		            let e2,r2 = helper n_arg b.exp_seq_exp2 in 
		            let r = comb_f [r1;r2] in
		            (Seq {b with exp_seq_exp1 = e1;exp_seq_exp2 = e2;},r)

	          | While b ->
		            let e1,r1 = helper n_arg b.exp_while_body in 
		            (While { b with exp_while_body = e1; }, r1)

	          | Try b ->
                    let e1,r1 = helper n_arg b.exp_try_body in 
                    let e2,r2 = helper n_arg b.exp_catch_clause in
		            (Try { b with exp_try_body = e1; exp_catch_clause=e2}, (comb_f [r1;r2]))
            | Par b ->
              let trans_par_case c =
                let ce, cr = helper n_arg c.exp_par_case_body in
                ({ c with exp_par_case_body = ce }, cr)
              in 
              let cl, rl = List.split (List.map trans_par_case b.exp_par_cases) in
              let r = comb_f rl in
              (Par { b with exp_par_cases = cl }, r)
  in helper init_arg e



  (*this maps an expression by passing an argument*)
let map_exp_args (e:exp) (arg:'a) (f:'a -> exp -> exp option) (f_args: 'a -> exp -> 'a) : exp =
  let f1 ac e = push_opt_void_pair (f ac e) in
  fst (transform_exp e arg f1 f_args voidf ())

  (*this maps an expression without passing an argument*)
let map_exp (e:exp) (f:exp->exp option) : exp = 
  (* fst (transform_exp e () (fun _ e -> push_opt_void_pair (f e)) idf2  voidf ()) *)
  map_exp_args e () (fun _ e -> f e) idf2 

  (*this computes a result from expression passing an argument*)
let fold_exp_args (e:exp) (init_a:'a) (f:'a -> exp-> 'b option) (f_args: 'a -> exp -> 'a) (comb_f: 'b list->'b) (zero:'b) : 'b =
  let f1 ac e = match (f ac e) with
    | Some r -> Some (e,r)
    | None ->  None in
  snd(transform_exp e init_a f1 f_args comb_f zero)
 
  (*this computes a result from expression without passing an argument*)
let fold_exp (e:exp) (f:exp-> 'b option) (comb_f: 'b list->'b) (zero:'b) : 'b =
  fold_exp_args e () (fun _ e-> f e) voidf2 comb_f zero

  (*this iterates over the expression and passing an argument*)
let iter_exp_args (e:exp) (init_arg:'a) (f:'a -> exp-> unit option) (f_args: 'a -> exp -> 'a) : unit =
  fold_exp_args  e init_arg f f_args voidf ()

  (*this iterates over the expression without passing an argument*)
let iter_exp (e:exp) (f:exp-> unit option)  : unit =  iter_exp_args e () (fun _ e-> f e) voidf2

  (*this computes a result from expression passing an argument with side-effects*)
let fold_exp_args_imp (e:exp)  (arg:'a) (imp:'c ref) (f:'a -> 'c ref -> exp-> 'b option)
  (f_args: 'a -> 'c ref -> exp -> 'a) (f_imp: 'c ref -> exp -> 'c ref) (f_comb:'b list->'b) (zero:'b) : 'b =
  let fn (arg,imp) e = match (f arg imp e) with
    | Some r -> Some (e,r)
    | None -> None in
  let fnargs (arg,imp) e = ((f_args arg imp e), (f_imp imp e)) in
  snd(transform_exp e (arg,imp) fn fnargs f_comb zero)

  (*this iterates over the expression and passing an argument*)
let iter_exp_args_imp e (arg:'a) (imp:'c ref) (f:'a -> 'c ref -> exp -> unit option)
  (f_args: 'a -> 'c ref -> exp -> 'a) (f_imp: 'c ref -> exp -> 'c ref) : unit =
  fold_exp_args_imp e arg imp f f_args f_imp voidf ()
  

let distributive_views : string list ref = ref ([])

let distributive c = List.mem c !distributive_views

let add_distributive c = distributive_views := c :: !distributive_views

let void_type = Void

let int_type = Int

let infint_type = INFInt

let float_type = Float

let bool_type = Bool

let bag_type = (BagT Int)

let list_type = List Int

let place_holder = P.SpecVar (Int, "pholder___", Unprimed)

(* smart constructors *)
(*let mkMultiSpec pos = [ SEnsure {
		sensures_base = Cformula.mkTrue pos;
		sensures_pos = pos;
	}]*)
let stub_branch_point_id s = (-1,s)
let mkEAssume pos = 
	let f = Cformula.mkTrue (Cformula.mkTrueFlow ()) pos in
	Cformula.mkEAssume [] f (Cformula.mkEBase f None no_pos) (stub_branch_point_id "") None
 
let mkEAssume_norm pos = 
	let f = Cformula.mkTrue (Cformula.mkNormalFlow ()) pos in
	(* let sf = Cformula.mkEBase f None no_pos in *)
	Cformula.mkEAssume [] f (Cformula.mkEBase f None no_pos) (stub_branch_point_id "") None
	
let mkSeq t e1 e2 pos = match e1 with
  | Unit _ -> e2
  | _ -> match e2 with
	  | Unit _ -> e1
	  | _ -> Seq ({exp_seq_type = t; exp_seq_exp1= e1; exp_seq_exp2 = e2; exp_seq_pos = pos})

(* utility functions *)

let is_var (e : exp) = match e with Var _ -> true | _ -> false

(* An Hoa : for array access a[i], the var is a *)
let get_var (e : exp) = match e with 
	| Var ({exp_var_type = _; exp_var_name = v; exp_var_pos = _}) -> v
	| _ -> failwith ("get_var: can't get identifier")

let is_block (e : exp) : bool = match e with Block _ -> true | _ -> false

let is_call (e : exp) : bool = match e with SCall _ -> true | _ -> false

let is_new (e : exp) : bool = match e with New _ -> true | _ -> false

let is_unit (e : exp) : bool = match e with Unit _ -> true | _ -> false

let is_cond (e : exp) : bool = match e with Cond _ -> true | _ -> false

let rec type_of_exp (e : exp) = match e with
  | Label b -> type_of_exp b.exp_label_exp
  | CheckRef _ -> None
  | Java _ -> None
  | Assert _ -> None
	(*| ArrayAt b -> Some b.exp_arrayat_type (* An Hoa *)*)
	(*| ArrayMod _ -> Some void_type (* An Hoa *)*)
  | Assign _ -> Some void_type
  | Barrier _ -> Some void_type
  | BConst _ -> Some bool_type
  | Bind ({exp_bind_type = t; 
		   exp_bind_bound_var = _; 
		   exp_bind_fields = _;
		   exp_bind_body = _;
		   exp_bind_pos = _}) -> Some t
  | Block ({exp_block_type = t;
			exp_block_body = _;
			exp_block_local_vars = _;
			exp_block_pos = _}) -> Some t
  | ICall ({exp_icall_type = t;
			exp_icall_receiver = _;
			exp_icall_method_name = _;
			exp_icall_arguments = _;
			exp_icall_pos = _}) -> Some t
  | Cast ({exp_cast_target_type = t}) -> Some t
  | Catch _ -> Some void_type
  | Cond ({exp_cond_type = t;
		   exp_cond_condition = _;
		   exp_cond_then_arm = _;
		   exp_cond_else_arm = _;
		   exp_cond_pos = _}) -> Some t
  | Debug _ -> None
  | Dprint _ -> None
  | FConst _ -> Some float_type
	  (*| FieldRead (t, _, _, _) -> Some t*)
	  (*| FieldWrite _ -> Some Void*)
  | IConst _ -> Some int_type
	(* An Hoa *)
	(* | ArrayAlloc ({exp_aalloc_etype = t; 
		  exp_aalloc_dimension = _; 
		  exp_aalloc_pos = _}) -> Some (P.Array t) *)
  | New ({exp_new_class_name = c; 
		  exp_new_arguments = _; 
		  exp_new_pos = _}) -> Some (Named c) (*---- ok? *)
  | Null _ -> Some (Globals.null_type (* Named "" *))
	| EmptyArray b -> Some (Array (b.exp_emparray_type, b.exp_emparray_dim)) (* An Hoa *)
  | Print _ -> None
 (* | Return ({exp_return_type = t; 
			 exp_return_val = _; 
			 exp_return_pos = _}) -> Some t*)
  | SCall ({exp_scall_type = t;
			exp_scall_method_name = _;
			exp_scall_arguments = _;
			exp_scall_pos = _}) -> Some t
  | Seq ({exp_seq_type = t; exp_seq_exp1 = _; exp_seq_exp2 = _; exp_seq_pos = _}) -> Some t
  | This ({exp_this_type = t}) -> Some t
  | Var ({exp_var_type = t; exp_var_name = _; exp_var_pos = _}) -> Some t
  | VarDecl _ -> Some void_type
  | Unit _ -> Some void_type
  | While _ -> Some void_type
  | Unfold _ -> Some void_type
  | Try _ -> Some void_type
  | Time _ -> None
  | Sharp b -> Some b.exp_sharp_type
  | Par _ -> Some void_type

and is_transparent e = match e with
  | Assert _ | Assign _ | Debug _ | Print _ -> true
  | _ -> false

(* let rec name_of_type (t : typ) = match t with *)
(*   | Prim Int -> "int" *)
(*   | Prim Bool -> "bool" *)
(*   | Prim Void -> "void" *)
(*   | Prim Float -> "float" *)
(*   | Prim (BagT t) -> "bag("^(name_of_type (Prim t))^")" *)
(*   | Prim (TVar i) -> "TVar["^(string_of_int i)^"]" *)
(*   | Prim List -> "list" *)
(*   | Named c -> c *)
(*   | Array (et, _) -> (name_of_type et) ^ "[]" (\* An hoa *\)  *)

let mingle_name (m : ident) (targs : typ list) = 
  let param_tnames = String.concat "~" (List.map string_of_typ targs) in
	m ^ "$" ^ param_tnames
  
let is_mingle_name m = String.contains m '$'

let unmingle_name (m : ident) = 
  try
	let i = String.index m '$' in
	  String.sub m 0 i
  with
	| Not_found -> m

let rec look_up_view_def_raw (defs : view_decl list) (name : ident) = match defs with
  | d :: rest -> if d.view_name = name then d else look_up_view_def_raw rest name
  | [] -> raise Not_found

let look_up_view_def_raw i (defs : view_decl list) (name : ident) = 
  let pr = fun x -> x in
  let pr_out = !print_view_decl in
  Debug.no_1_num i "look_up_view_def_raw" pr pr_out (fun _ -> look_up_view_def_raw defs name) name

let look_up_view_def_ext_size (defs : view_decl list) num_rec_br0 num_base0 =
  let ext_views = List.filter (fun v ->
      let b1 = v.view_kind=View_EXTN && List.length v.view_prop_extns = 1 in
      let num_base = match v.view_base_case with
        | None -> 0
        | Some _ -> 1
      in
      let num_rec_br = List.length v.view_un_struc_formula - num_base in
      b1 && (num_rec_br0 = num_rec_br) && (num_base0 = num_base)
  ) defs in
  ext_views


let extract_view_x_invs transed_views=
  List.fold_left (fun r vdcl ->
      if Cpure.isConstTrue (MP.pure_of_mix vdcl.view_x_formula) then
        if Cpure.isConstTrue (MP.pure_of_mix vdcl.view_user_inv) then r
        else
          r@[(vdcl.view_name,
      ((Cpure.SpecVar (Named vdcl.view_data_name, self, Unprimed))::vdcl.view_vars,
      vdcl.view_user_inv))]
      else
      r@[(vdcl.view_name,
      ((Cpure.SpecVar (Named vdcl.view_data_name, self, Unprimed))::vdcl.view_vars,
      vdcl.view_x_formula))]
  ) [] transed_views

let look_up_view_inv defs act_args name inv_compute_fnc =
  let vdcl = look_up_view_def_raw 46 defs name in
  let ss = List.combine ((P.SpecVar (Named vdcl.view_data_name, self, Unprimed))::vdcl.view_vars) act_args in
  let inv =
    let p1 = MP.pure_of_mix vdcl.view_user_inv in
    if P.isConstTrue p1 then
      (*make sure inv is not computed*)
      if !Globals.do_infer_inv then
        MP.pure_of_mix vdcl.view_x_formula
      else
        try
          (*case Globals.do_infer_inv = false*)
          let () = Globals.do_infer_inv := true in
          let new_pf = inv_compute_fnc name vdcl.view_vars vdcl.view_un_struc_formula  vdcl.view_data_name defs p1 in
          let () = Globals.do_infer_inv := false in
          new_pf
        with _ -> p1
    else p1
  in
  P.subst ss inv

(* An Hoa *)
let rec look_up_rel_def_raw (defs : rel_decl list) (name : ident) = match defs with
  | d :: rest -> if d.rel_name = name then d else look_up_rel_def_raw rest name
  | [] -> raise Not_found

let look_up_templ_def_raw (defs: templ_decl list) (name : ident) = 
  List.find (fun d -> d.templ_name = name) defs

let look_up_ut_def_raw (defs: ut_decl list) (name : ident) = 
  List.find (fun d -> d.ut_name = name) defs

let rec look_up_hp_def_raw_x (defs : hp_decl list) (name : ident) = match defs with
  | d :: rest -> if d.hp_name = name then d else look_up_hp_def_raw_x rest name
  | [] -> raise Not_found

let look_up_hp_def_raw defs name=
  let pr1 = !print_hp_decl in
  Debug.no_1 "look_up_hp_def_raw" pr_id pr1
      (fun _ -> look_up_hp_def_raw_x defs name) name

let look_up_hp_parts decls hp=
  let hp_dc = look_up_hp_def_raw decls hp in
  hp_dc.hp_part_vars

let look_up_hp_decl_data_name_x decls hp arg_pos=
  let rec look_up_data_name args n=
    match args with
      | [] -> report_error no_pos "Cast.look_up_hp_decl_data_name 1"
      | (sv,_)::rest ->( if n = arg_pos then
          match Cpure.type_of_spec_var sv with
            | Named id -> id
            | _ -> report_error no_pos "Cast.look_up_hp_decl_data_name: only pure-extend for pointer"
          else look_up_data_name rest (n+1)
        )
  in
  let hp_dcl = look_up_hp_def_raw decls hp in
  look_up_data_name hp_dcl.hp_vars_inst 0

let look_up_hp_decl_data_name decls hp arg_pos=
  Debug.no_2 "look_up_hp_decl_data_name" pr_id string_of_int pr_id
      (fun _ _ -> look_up_hp_decl_data_name_x decls hp arg_pos)
      hp arg_pos

let cmp_hp_def d1 d2 = String.compare d1.hp_name d2.hp_name = 0

let generate_pure_rel hprel=
  let n_p_hprel ={
      rel_name = default_prefix_pure_hprel ^ hprel.hp_name;
      rel_vars = List.map fst hprel.hp_vars_inst;
      rel_formula = F.get_pure hprel.hp_formula;
  }
  in
  (*add map*)
  let () = pure_hprel_map := !pure_hprel_map@[(hprel.hp_name, n_p_hprel.rel_name)] in
  let _= Smtsolver.add_relation n_p_hprel.rel_name n_p_hprel.rel_vars n_p_hprel.rel_formula in
  let _= Z3.add_relation n_p_hprel.rel_name n_p_hprel.rel_vars n_p_hprel.rel_formula in
  n_p_hprel

let add_raw_hp_rel_x prog is_pre is_unknown unknown_ptrs pos=
  if (List.length unknown_ptrs > 0) then
    let hp_decl =
      { hp_name = (if is_unknown then Globals.unkhp_default_prefix_name else
        if is_pre then Globals.hp_default_prefix_name else hppost_default_prefix_name)
        ^ (string_of_int (Globals.fresh_int()));
      hp_part_vars = [];
      hp_root_pos = 0; (*default, reset when def is inferred*)
      hp_vars_inst = unknown_ptrs;
      hp_is_pre = is_pre;
      hp_formula = F.mkBase F.HEmp (MP.mkMTrue pos) CVP.empty_vperm_sets F.TypeTrue (F.mkTrueFlow()) [] pos;}
    in
    let unk_args = (fst (List.split hp_decl.hp_vars_inst)) in
    prog.prog_hp_decls <- (hp_decl :: prog.prog_hp_decls);
    (* PURE_RELATION_OF_HEAP_PRED *)
    let p_hp_decl = generate_pure_rel hp_decl in
    let () = prog.prog_rel_decls <- (p_hp_decl::prog.prog_rel_decls) in
    let () = Smtsolver.add_hp_relation hp_decl.hp_name unk_args hp_decl.hp_formula in
    let () = Z3.add_hp_relation hp_decl.hp_name unk_args hp_decl.hp_formula in
    let hf =
      F.HRel (P.SpecVar (HpT,hp_decl.hp_name, Unprimed), 
               List.map (fun sv -> P.mkVar sv pos) unk_args,
      pos)
    in
    let () = x_tinfo_hp (add_str "define: " !print_hp_decl) hp_decl pos in
    Debug.ninfo_zprint (lazy (("       gen hp_rel: " ^ (!F.print_h_formula hf)))) pos;
    (hf, P.SpecVar (HpT,hp_decl.hp_name, Unprimed))
  else report_error pos "sau.add_raw_hp_rel: args should be not empty"

let add_raw_hp_rel prog is_pre is_unknown unknown_args pos=
  let pr1 = pr_list (pr_pair !P.print_sv print_arg_kind) in
  let pr2 = !F.print_h_formula in
  let pr4 (hf,_) = pr2 hf in
  Debug.no_1 "add_raw_hp_rel" pr1 pr4
      (fun _ -> add_raw_hp_rel_x prog is_pre is_unknown unknown_args pos) unknown_args

let set_proot_hp_def_raw r_pos defs name=
  let hpdclr = look_up_hp_def_raw defs name in
  let () = hpdclr.hp_root_pos <- r_pos in
  hpdclr

let get_proot_hp_def_raw defs name=
  let hpdclr = look_up_hp_def_raw defs name in
  hpdclr.hp_root_pos

let get_root_args_hprel hprels hp_name actual_args=
  let rec part_sv_from_pos ls n n_need rem=
    match ls with
      | [] -> report_error no_pos "sau.get_sv_from_pos"
      | sv1::rest -> if n = n_need then (sv1, rem@rest)
        else part_sv_from_pos rest (n+1) n_need (rem@[sv1])
  in
  let retrieve_root hp_name args=
    let rpos = get_proot_hp_def_raw hprels hp_name in
    let r,paras = part_sv_from_pos args 0 rpos [] in
    (r,paras)
  in
  retrieve_root hp_name actual_args

let get_root_typ_hprel hprels hp_name=
  let rec part_sv_from_pos ls n n_need rem=
    match ls with
      | [] -> report_error no_pos "sau.get_sv_from_pos"
      | sv1::rest -> if n = n_need then (sv1, rem@rest)
        else part_sv_from_pos rest (n+1) n_need (rem@[sv1])
  in
  let retrieve_root hp_name=
    let hpdclr = look_up_hp_def_raw hprels hp_name in
    let rpos = hpdclr.hp_root_pos in
    let r,_ = part_sv_from_pos (List.map fst hpdclr.hp_vars_inst) 0 rpos [] in
    match Cpure.type_of_spec_var r with
      | Named id -> id
      | _ -> ""
  in
  retrieve_root hp_name

let check_pre_post_hp defs hp_name=
  let hpdecl = look_up_hp_def_raw defs hp_name in
  hpdecl.hp_is_pre

let rec look_up_view_def (pos : loc) (defs : view_decl list) (name : ident) = match defs with
  | d :: rest -> 
	    if d.view_name = name then d 
	    else look_up_view_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
	Error.error_text = name ^ " is not a view definition"}

let look_up_view_def_num i (pos : loc) (defs : view_decl list) (name : ident) = 
  Debug.no_1_num i "look_up_view_def" pr_id pr_no 
      (fun _ -> look_up_view_def pos defs name) name

let collect_rhs_view (n:ident) (e:F.struc_formula) : (ident * ident list) =
  let f_comb = List.concat in
  let f e = match e with 
    | F.ViewNode {F.h_formula_view_name = n} -> Some [n] 
    | _ -> None in
  let f_heap e = F.fold_h_formula e f f_comb in
   (n, F.foldheap_struc_formula f_heap f_comb e)

let collect_rhs_view (n:ident) (f:F.struc_formula) : (ident * ident list) =
  let id x = x in
  let pr1 x = x in
  let pr2 = pr_pair id (pr_list id) in 
  Debug.no_1 "collect_rhs_view" pr1 pr2 (fun _ -> collect_rhs_view n f) n

let is_self_rec_rhs (lhs:ident) (rhs:F.struc_formula) : bool =
  let  (_,ns) = collect_rhs_view lhs rhs in
  List.mem lhs ns

let is_self_rec_rhs (lhs:ident) (rhs:F.struc_formula) : bool =
  Debug.no_1 "is_self_rec_rhs" (fun x -> x) (string_of_bool) (fun _ -> is_self_rec_rhs lhs rhs) lhs

(* pre: name exists as a view in prog *)
let is_rec_view_def prog (name : ident) : bool = 
   let vdef = look_up_view_def_num 2 no_pos prog.prog_view_decls name in
   (* let () = collect_rhs_view vdef in *)
   vdef.view_is_rec

(*check whether a view is a lock invariant*)
let get_lock_inv prog (name : ident) : (bool * F.formula) =
  let vdef = look_up_view_def_raw 1 prog.prog_view_decls name in
  match vdef.view_inv_lock with
    | None -> (false, (F.mkTrue (F.mkTrueFlow ()) no_pos))
    | Some f -> (true, f)

let is_lock_inv prog (name : ident) : bool =
  let vdef = look_up_view_def_raw 2 prog.prog_view_decls name in
  match vdef.view_inv_lock with
    | None -> false
    | Some f -> true

let self_param vdef = P.SpecVar (Named vdef.view_data_name, self, Unprimed) 

let look_up_view_baga prog (c : ident) (root:P.spec_var) (args : P.spec_var list) : P.spec_var list = 
  let vdef = look_up_view_def no_pos prog.prog_view_decls c in
  let ba = vdef.view_baga in
  (* let () = print_endline_quiet(" look_up_view_baga: baga= " ^ (!print_svl ba)) in *)
  let from_svs = (self_param vdef) :: vdef.view_vars in
  let to_svs = root :: args in
  P.subst_var_list_avoid_capture from_svs to_svs ba

let look_up_view_baga  prog (c : ident) (root:P.spec_var) (args : P.spec_var list) : P.spec_var list = 
      Debug.no_2 "look_up_view_baga" (fun v -> !print_svl [v]) !print_svl !print_svl 
      (fun r a ->  look_up_view_baga prog c r a) root args

let rec look_up_data_def pos (ddefs : data_decl list) (name : string) = match ddefs with
  | d :: rest -> 
	  if d.data_name = name then d 
	  else look_up_data_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = name ^ " is not a data/class declaration"}

let rec look_up_data_def_raw (ddefs : data_decl list) (name : string) =
  match ddefs with
  | d :: rest -> 
      if d.data_name = name then d 
      else look_up_data_def_raw rest name
  | [] -> raise Not_found

let look_up_extn_info_rec_field_x ddefs dname=
  let rec look_up_helper fields=
    match fields with
      | ((t,_), extns)::rest -> begin
          match t with
            | Named id1 -> if String.compare id1 dname = 0 then
                extns
              else look_up_helper rest
            | _ -> look_up_helper rest
        end
      | [] -> raise Not_found
  in
  let dd = look_up_data_def no_pos ddefs dname in
  let () = Debug.ninfo_hprint (add_str "    dd.data_fields:" (pr_list (pr_pair (pr_pair string_of_typ pr_id) (pr_list pr_id))))
      dd.data_fields no_pos in
  try
    look_up_helper dd.data_fields
  with _ ->
      let (_, extns) = List.hd dd.data_fields in
      extns

let look_up_extn_info_rec_field ddefs dname=
  Debug.no_1 "look_up_extn_info_rec_field" pr_id (pr_list pr_id)
      (fun _ -> look_up_extn_info_rec_field_x ddefs dname)
      dname

let rec look_up_parent_name pos ddefs name =
  let ddef = look_up_data_def pos ddefs name in
	ddef.data_parent_name

(*
let rec look_up_proc_def_raw (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
      if p.proc_name = name then
		p
      else
		look_up_proc_def_raw rest name
  | [] -> raise Not_found
*)

let rec look_up_proc_def_raw (procs : (ident, proc_decl) Hashtbl.t) (name : string) = 
  Hashtbl.find procs name 

(*			  
let rec look_up_proc_def pos (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
      if p.proc_name = name then
		p
      else
		look_up_proc_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = "procedure " ^ name ^ " is not found"}
*)

let rec look_up_proc_def pos (procs : (ident, proc_decl) Hashtbl.t) (name : string) = 
  try Hashtbl.find procs name 
	with Not_found -> Error.report_error {
    Error.error_loc = pos;
    Error.error_text = "look_up_proc_def: Procedure " ^ name ^ " is not found."}
    
let look_up_hpdefs_proc (procs : (ident, proc_decl) Hashtbl.t) (name : string) = 
  try
      let proc = Hashtbl.find procs name in
      proc.proc_hpdefs
  with Not_found -> Error.report_error {
      Error.error_loc = no_pos;
      Error.error_text = "look_up_hpdefs_proc: Procedure " ^ name ^ " is not found."}

let update_hpdefs_proc (procs : (ident, proc_decl) Hashtbl.t) hpdefs (name : string) = 
  try
      let proc = Hashtbl.find procs name in
      (* let new_proc = {proc with proc_hpdefs = proc.proc_hpdefs@hpdefs} in *)
      let () = proc.proc_hpdefs <- proc.proc_hpdefs@hpdefs in ()
      (* Hashtbl.replace procs name proc *)
  with Not_found -> Error.report_error {
      Error.error_loc = no_pos;
      Error.error_text = "update_hpdefs_proc: Procedure " ^ name ^ " is not found."}

let look_up_callee_hpdefs_proc (procs : (ident, proc_decl) Hashtbl.t) (name : string) = 
  try
      let proc = Hashtbl.find procs name in
      proc.proc_callee_hpdefs
  with Not_found -> []
(* Error.report_error { *)
      (* Error.error_loc = no_pos; *)
      (* Error.error_text = "Procedure " ^ name ^ " is not found."} *)

let update_callee_hpdefs_proc (procs : (ident, proc_decl) Hashtbl.t) caller_name (callee_name : string) = 
  try
      let hpdefs = look_up_hpdefs_proc procs callee_name in
      let proc = Hashtbl.find procs caller_name in
      (* let new_proc = {proc with proc_callee_hpdefs = proc.proc_callee_hpdefs@hpdefs} in *)
      let () = proc.proc_callee_hpdefs <- proc.proc_callee_hpdefs@hpdefs in ()
      (* Hashtbl.replace procs name new_proc *)
  with Not_found -> Error.report_error {
      Error.error_loc = no_pos;
      Error.error_text = "update_callee_hpdefs_proc: Procedure " ^ caller_name ^ " is not found."}

let update_sspec_proc (procs : (ident, proc_decl) Hashtbl.t) pname spec = 
  try
    let proc = Hashtbl.find procs pname in
    let new_proc = {proc with proc_static_specs = spec} in
    let () = Hashtbl.replace procs pname new_proc in
    procs
  with Not_found -> Error.report_error {
      Error.error_loc = no_pos;
      Error.error_text = "update_sspec_proc: Procedure " ^ pname ^ " is not found."}

(* Replaced by the new function with Hashtbl *)
(*
let rec look_up_proc_def_no_mingling pos (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
	  if unmingle_name p.proc_name = name then p
	  else look_up_proc_def_no_mingling pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = "procedure " ^ name ^ " is not found"}
*)
let rec look_up_proc_def_no_mingling pos (procs : (ident, proc_decl) Hashtbl.t) (name : string) = 
  let proc = Hashtbl.fold (fun i p acc -> 
    match acc with
    | None -> if unmingle_name i = name then Some p else None
    | Some _ -> acc
  ) procs None in
  match proc with
  | None -> 
    (* Error.report_error {                                                                        *)
    (*   Error.error_loc = pos;                                                                    *)
    (*   Error.error_text = "look_up_proc_def_no_mingling: Procedure " ^ name ^ " is not found." } *)
    failwith ("look_up_proc_def_no_mingling: Procedure " ^ name ^ " is not found.")
  | Some p -> p
  
(* takes a class and returns the list of all the methods from that class or from any of the parent classes *)
and look_up_all_methods (prog : prog_decl) (c : data_decl) : proc_decl list = match c.data_name with 
  | "Object" -> [] (* it does not have a superclass *)
  | _ ->  
      let cparent_decl = List.find (fun t -> (String.compare t.data_name c.data_parent_name) = 0) prog.prog_data_decls in
        c.data_methods @ (look_up_all_methods prog cparent_decl)  

(*
  coers: a list of coercion rules (proc_coercion must be true)
*)
(*
let rec look_up_distributive_def_raw coers (c : ident) : (F.formula * F.formula) list = match coers with
  | p :: rest -> begin
	  let rec find_formula coercion_list = match coercion_list with
		| (pc, (pre, post)) :: rest ->
			if pc = c then
			  Some (pre, post)
			else
			  find_formula rest
		| [] -> None 
	  in
	  let rest_coers = look_up_distributive_def_raw rest c in
		match find_formula p.proc_coercion_list with
		  | Some (pre, post) -> (pre, post) :: rest_coers
		  | None -> rest_coers
	end
  | [] -> []
*)
let lookup_view_invs rem_br v_def = 
  try 
    snd(snd (List.find (fun (c1,_)-> Gen.BList.list_setequal_eq (=) c1 rem_br) v_def.view_prune_invariants))
  with | Not_found -> []

let lookup_bar_invs_with_subs rem_br b_def zip  = 
  try 
    let v=snd(snd (List.find (fun (c1,_)-> Gen.BList.list_setequal_eq (=) c1 rem_br) b_def.barrier_prune_invariants)) in
    List.map (P.b_apply_subs zip) v
  with | Not_found -> []


let lookup_view_invs_with_subs rem_br v_def zip  = 
  try 
    let v=snd(snd (List.find (fun (c1,_)-> Gen.BList.list_setequal_eq (=) c1 rem_br) v_def.view_prune_invariants)) in
    List.map (P.b_apply_subs zip) v
  with | Not_found -> []

let lookup_view_baga_with_subs rem_br v_def from_v to_v  = 
  try 
    let v=fst(snd (List.find (fun (c1,_)-> Gen.BList.list_setequal_eq (=) c1 rem_br) v_def.view_prune_invariants)) in
    P.subst_var_list_avoid_capture from_v to_v v
  with | Not_found -> []

let look_up_coercion_def_raw coers (c : ident) : coercion_decl list = 
  List.filter (fun p ->  p.coercion_head_view = c ) coers
  
let look_up_coercion_def_raw coers (c : ident) : coercion_decl list =
  let pr1 = !print_coerc_decl_list in
	(* let pr1 l = string_of_int (List.length l) in *)
	Debug.no_2 "look_up_coercion_def_raw" pr1 (fun c-> c) (fun c-> "") look_up_coercion_def_raw coers c
  (* match coers with *)
  (* | p :: rest -> begin *)
  (*     let tmp = look_up_coercion_def_raw rest c in *)
  (*   	if p.coercion_head_view = c then p :: tmp *)
  (*   	else tmp *)
  (*   end *)
  (* | [] -> [] *)

let exist_left_lemma_w_fl coers fl=
  let is_rhs_subsume_flow_ff coer=
    F.struc_formula_is_eq_flow coer.coercion_body_norm fl.F.formula_flow_interval
  in
  (* exist a lemma i.e. rhs has fl flow *)
  List.exists is_rhs_subsume_flow_ff coers

(*
  a coercion can be simple, complex or normalizing
  Note that:
  Complex + Left == normalization
*)
(*TODO: re-implement with care*)
let case_of_coercion_x (lhs:F.formula) (rhs:F.formula) : coercion_case =
  let h,_,_,_,_,_ = F.split_components lhs in
  let hs = F.split_star_conjunctions h in
  let flag = if (List.length hs) == 1 then 
	    let sm = List.hd hs in (match sm with
	      | F.StarMinus _ -> true
	      | _ -> false)
	  else false in
  if(flag || !Globals.allow_ramify) then Ramify
  else
    let fct f = match f with
      | Cformula.Base {F.formula_base_heap=h}
      | Cformula.Exists {F.formula_exists_heap=h} ->      
          let () = x_tinfo_hp (add_str "formula_exists_heap" !print_h_formula ) h no_pos in 
          let hs = F.split_star_conjunctions h in
          let hs = List.filter (fun c -> not (c=F.HTrue || c=F.HEmp)) hs in
	      let self_n = List.for_all (fun c-> 
              let () = x_tinfo_hp (add_str "c" !print_h_formula ) c no_pos in
              let only_self = match c with
                | F.HVar _ -> false
                | F.DataNode _
                | F.ViewNode _-> (P.name_of_spec_var (F.get_node_var c)) = self 
                | F.HRel (sv,exp_lst,_) -> (
                    let () = x_tinfo_hp (add_str "sv" !print_sv ) sv no_pos in
                    match exp_lst with
                      | [sv] -> (
                          match sv with
                            | (P.Var (v,_)) -> (P.name_of_spec_var v) = self
                            | _ -> false)
                      | _ -> false
                )
                | _ -> failwith ("Only nodes, HVar, and HRel allowed after split_star_conjunctions 1") 
              in
              only_self) hs  in
          let get_name h = match h with
            | F.HVar (v,_) -> P.name_of_sv v
            | F.DataNode _
            | F.ViewNode _-> F.get_node_name 2 h
            | F.HRel (sv,exp_lst,_) -> P.name_of_spec_var sv
            | _ -> failwith ("Only nodes, HVar and HRel allowed after split_star_conjunctions 2") in
          (List.length hs),self_n, List.map get_name hs
      | _ -> 1,false,[]
    in
    (*length = #nodes, sn = is there a self node, typ= List of names of nodes*)
    let lhs_length,l_sn,lhs_typ = fct lhs in
    let rhs_length,r_sn,rhs_typ = fct rhs in
    match lhs_typ@rhs_typ with
	  | [] -> Simple
	| h::t ->
        (*
          Why using concret numbers (e.g. 1,2) here ?
          If there is a lemma that split 1 node into 3 nodes,
          it is also considered a split lemma?
        *)
        (*special case, detecting inconsistency using lemmas*)
        if rhs_length=0 then Normalize true else 
		if l_sn && r_sn && (List.for_all (fun c-> h=c) t) then
            (*all nodes having the same names*)
            (* ??? why using the node names *)
			if lhs_length=2 && rhs_length=1  then Normalize true
			else if lhs_length=1 && rhs_length=2  then Normalize false
			else if lhs_length=1 then Simple
			else Complex
		else if lhs_length=1 then Simple
			else Complex
		
let case_of_coercion lhs rhs =
	let pr1 r = match r with | Simple -> "simple" | Complex -> "complex" | Ramify -> "ramify" | Normalize b-> "normalize "^string_of_bool b in
	Debug.no_2 "case_of_coercion" !Cformula.print_formula !Cformula.print_formula pr1 case_of_coercion_x lhs rhs  

let  look_up_coercion_with_target coers (c : ident) (t : ident) : coercion_decl list = 
    List.filter (fun p ->  p.coercion_head_view = c && p.coercion_body_view = t  ) coers

let  look_up_coercion_with_target coers (c : ident) (t : ident) : coercion_decl list = 
  let pr1 = pr_list !print_coercion in
  Debug.no_3 "look_up_coercion_with_target" (fun x-> x)  (fun x-> x) pr1 pr1 
    (fun _ _ _ -> look_up_coercion_with_target coers c t) c t coers
 
let rec callees_of_proc (prog : prog_decl) (name : ident) : ident list =
  (*let pdef = look_up_proc_def_no_mingling no_pos prog.old_proc_decls name in*)
  let pdef = look_up_proc_def_no_mingling no_pos prog.new_proc_decls name in
  let callees = match pdef.proc_body with
	  | Some e -> callees_of_exp e
	  | None -> [] 
  in
	callees

and callees_of_exp (e0 : exp) : ident list = match e0 with
  | Label e -> callees_of_exp e.exp_label_exp
  | CheckRef _ -> []
  | Java _ -> []
  | Assert _ -> []
	(* AN HOA *)
	(*| ArrayAt ({exp_arrayat_type = _;
	  exp_arrayat_array_base = _;
	  exp_arrayat_index = e;
	  exp_arrayat_pos = _; }) -> callees_of_exp e*)
	(*| ArrayMod ({exp_arraymod_lhs = l;
	  exp_arraymod_rhs = r;
	  exp_arraymod_pos = _}) -> U.remove_dups (callees_of_exp (ArrayAt l) @ callees_of_exp r)*)
        (* AN HOA *)
  | Assign ({exp_assign_lhs = _;
    exp_assign_rhs = e;
    exp_assign_pos = _}) -> callees_of_exp e
  | BConst _ -> []
  | Bind ({exp_bind_type = _;
    exp_bind_bound_var = _;
    exp_bind_fields = _;
    exp_bind_body = e;
    exp_bind_pos = _}) -> callees_of_exp e
  | Block ({exp_block_type = _;
    exp_block_body = e;
    exp_block_local_vars = _;
    exp_block_pos = _}) -> callees_of_exp e
  | Barrier _ -> [] 
  | Cast ({exp_cast_body = e}) -> callees_of_exp e
  | Catch e-> callees_of_exp e.exp_catch_body
  | Cond ({exp_cond_type = _;
    exp_cond_condition = _;
    exp_cond_then_arm = e1;
    exp_cond_else_arm = e2;
    exp_cond_pos = _}) -> Gen.BList.remove_dups_eq (=) (callees_of_exp e1 @ callees_of_exp e2)
  | Debug _ -> []
  | Dprint _ -> []
  | FConst _ -> []
	(*| FieldRead _ -> []*)
	(*| FieldWrite _ -> []*)
  | ICall ({exp_icall_type = _;
    exp_icall_receiver = _;
    exp_icall_method_name = n;
    exp_icall_arguments = _;
    exp_icall_pos = _}) -> [unmingle_name n] (* to be fixed: look up n, go down recursively *)
  | IConst _ -> []
	(*| ArrayAlloc _ -> []*)
  | New _ -> []
  | Null _ -> []
  | EmptyArray _ -> [] (* An Hoa : empty array has no callee *)
  | Print _ -> []
  | Sharp b -> []
  | SCall ({exp_scall_type = _;
    exp_scall_method_name = n;
    exp_scall_arguments = _;
    exp_scall_pos = _}) -> [unmingle_name n]
  | Seq ({exp_seq_type = _;
    exp_seq_exp1 = e1;
    exp_seq_exp2 = e2;
    exp_seq_pos = _}) -> Gen.BList.remove_dups_eq (=) (callees_of_exp e1 @ callees_of_exp e2)
  | This _ -> []
  | Time _ -> []
  | Var _ -> []
  | VarDecl _ -> []
  | Unit _ -> []
  | While ({exp_while_condition = _;
    exp_while_body = e;
    exp_while_spec = _;
    exp_while_pos = _ }) -> callees_of_exp e (*-----???*)
  | Try b -> Gen.BList.remove_dups_eq (=) ((callees_of_exp b.exp_try_body)@(callees_of_exp b.exp_catch_clause))
  | Unfold _ -> []
  | Par b ->
    let callees = List.concat (List.map (fun c -> 
        callees_of_exp c.exp_par_case_body) b.exp_par_cases) in
    Gen.BList.remove_dups_eq (=) callees 

let procs_to_verify (prog : prog_decl) (names : ident list) : ident list =
  let tmp1 = List.map (callees_of_proc prog) names in
  let tmp2 = names @ (List.concat tmp1) in
  let tmp3 = Gen.BList.remove_dups_eq (=) tmp2 in
	tmp3


(*************************************************************)
(* Building the graph representing the class hierarchy       *)
(*************************************************************)

type ch_node = { ch_node_name : ident;
				 mutable ch_node_class : data_decl option;
				 mutable ch_node_coercion : proc_decl option (* coercion rule to the parent class *) }

module CD = struct
  type t = ch_node
  let compare c1 c2 = compare c1.ch_node_name c2.ch_node_name
  let hash c = Hashtbl.hash c.ch_node_name
  let equal c1 c2 = (c1.ch_node_name = c2.ch_node_name)
end

module CH = Graph.Imperative.Digraph.Concrete(CD)
module TraverseCH = Graph.Traverse.Dfs(CH)

module W = struct
  type label = CH.E.label
  type t = int
  let weight x = 1
  let zero = 0
  let add = (+)
  let compare = compare
end

module PathCH = Graph.Path.Dijkstra(CH)(W)

let class_hierarchy = CH.create ()

let build_hierarchy (prog : prog_decl) =
  (* build the class hierarchy *)
  let add_edge (cdef : data_decl) = 
	CH.add_edge class_hierarchy (CH.V.create {ch_node_name = cdef.data_name; 
											  ch_node_class = None; 
											  ch_node_coercion = None})
	  (CH.V.create {ch_node_name = cdef.data_parent_name; 
					ch_node_class = None; 
					ch_node_coercion = None}) in
  let todo_unknown = List.map add_edge prog.prog_data_decls in
	if TraverseCH.has_cycle class_hierarchy then begin
		print_string ("Class hierarchy has cycles");
		failwith ("Class hierarchy has cycles");
	  end 
	else begin
		(* now add class definitions in *)
		let update_node node = 
		  if not (node.ch_node_name = "") then
			let cdef = look_up_data_def no_pos prog.prog_data_decls node.ch_node_name in
			  node.ch_node_class <- Some cdef
		in
		  CH.iter_vertex update_node class_hierarchy
	  end

(*
  subnode: the sub class object to be converted to super class object plus
           extesions
  cdefs: list of class definition, going from super class to sub class
*)
let rec generate_extensions (subnode : F.h_formula_data) cdefs0 (pos:loc) : F.h_formula = match cdefs0 with
  | cdef1 :: _ -> begin
	  (* generate the first node *)
	  let sub_tvar = List.hd subnode.F.h_formula_data_arguments in
	  (* let sub_tvar_ann = List.hd subnode.F.h_formula_data_param_imm in *)
	  let sub_ext_var = List.hd (List.tl subnode.F.h_formula_data_arguments) in
		(* call gen_exts with sup_ext_var to link the 
		   head node with extensions *)
	  let heap_args = List.tl (List.tl subnode.F.h_formula_data_arguments) in
	  let n = List.length cdef1.data_fields in
	  let to_sup, rest_fields = Gen.split_at heap_args n in
	  let ext_name = gen_ext_name subnode.F.h_formula_data_name cdef1.data_name in
	  (*--- 09.05.2000 *)
	  let fn1 = fresh_var_name ext_name pos.start_pos.Lexing.pos_lnum in
		(*let () = (print_string ("\n[cast.ml, line 556]: fresh name = " ^ fn1 ^ "!!!!!!!!!!!\n\n")) in*)
		(*09.05.2000 ---*)
	  let sup_ext_var = P.SpecVar (Named ext_name, fn1, Unprimed) in
	  let sup_h = F.DataNode ({F.h_formula_data_node = subnode.F.h_formula_data_node;
							   F.h_formula_data_name = cdef1.data_name;
							   F.h_formula_data_derv = subnode.F.h_formula_data_derv;
							   F.h_formula_data_split = subnode.F.h_formula_data_split;
							   F.h_formula_data_imm = subnode.F.h_formula_data_imm;
                               F.h_formula_data_param_imm = subnode.F.h_formula_data_param_imm;
							   F.h_formula_data_perm = subnode.F.h_formula_data_perm; (*LDK*)
							   F.h_formula_data_origins = subnode.F.h_formula_data_origins;
							   F.h_formula_data_original = subnode.F.h_formula_data_original;
							   F.h_formula_data_arguments = sub_tvar :: sup_ext_var :: to_sup;
	                           F.h_formula_data_holes = []; (* An Hoa : Don't know what to do! *)
							   F.h_formula_data_label = subnode.F.h_formula_data_label;
                 F.h_formula_data_remaining_branches = None;
                 F.h_formula_data_pruning_conditions = [];
							   F.h_formula_data_pos = pos}) in
		(* generate extensions for the rest of the fields *)
	  let rec gen_exts top_p link_p args cdefs : F.h_formula = match cdefs with
		| cdef1 :: cdef2 :: rest -> begin
			let i = List.length cdef2.data_fields in
			let to_ext, rest_fields = Gen.split_at args i in
			let ext_name = gen_ext_name cdef1.data_name cdef2.data_name in
			  if Gen.is_empty rest then
				let ext_h = F.DataNode ({F.h_formula_data_node = top_p;
										 F.h_formula_data_name = ext_name;
										 F.h_formula_data_derv = subnode.F.h_formula_data_derv;
										 F.h_formula_data_split = subnode.F.h_formula_data_split;

										 F.h_formula_data_imm = subnode.F.h_formula_data_imm;
                                         F.h_formula_data_param_imm = subnode.F.h_formula_data_param_imm;
										 F.h_formula_data_perm = subnode.F.h_formula_data_perm; (*LDK*)
							             F.h_formula_data_origins = subnode.F.h_formula_data_origins;
							             F.h_formula_data_original = subnode.F.h_formula_data_original;
										 F.h_formula_data_arguments = link_p :: to_ext;
						F.h_formula_data_holes = []; (* An Hoa : Don't know what to do! *)
										 F.h_formula_data_label = subnode.F.h_formula_data_label;
                     F.h_formula_data_remaining_branches = None;
                     F.h_formula_data_pruning_conditions = [];
										 F.h_formula_data_pos = pos}) in
				  ext_h
			  else
				let ext_link_name = gen_ext_name cdef2.data_name ((List.hd rest).data_name) in
				(*--- 09.05.2000 *)
	  		let fn2 = fresh_var_name ext_name pos.start_pos.Lexing.pos_lnum in
				(*let () = (print_string ("\n[cast.ml, line 579]: fresh name = " ^ fn2 ^ "!!!!!!!!!!!\n\n")) in*)
				(*09.05.2000 ---*)
				let ext_link_p = P.SpecVar (Named ext_link_name, fn2, Unprimed) in
				let ext_h = F.DataNode ({F.h_formula_data_node = top_p;
										 F.h_formula_data_name = ext_name;
										 F.h_formula_data_derv = subnode.F.h_formula_data_derv;
										 F.h_formula_data_split = subnode.F.h_formula_data_split;

										 F.h_formula_data_imm = subnode.F.h_formula_data_imm;
                                         F.h_formula_data_param_imm = subnode.F.h_formula_data_param_imm;
										 F.h_formula_data_perm = subnode.F.h_formula_data_perm;
							             F.h_formula_data_origins = subnode.F.h_formula_data_origins;
							             F.h_formula_data_original = subnode.F.h_formula_data_original;
										 F.h_formula_data_arguments = ext_link_p :: to_ext;
								F.h_formula_data_holes = []; (* An Hoa : Don't know what to do! *)
										 F.h_formula_data_label = subnode.F.h_formula_data_label;
                     F.h_formula_data_remaining_branches = None;
                     F.h_formula_data_pruning_conditions = [];
										 F.h_formula_data_pos = pos}) in
				let rest_exts = gen_exts ext_link_p link_p rest_fields (cdef2 :: rest) in
				let ext = F.mkStarH ext_h rest_exts pos in
				  ext
		  end
		| _ -> F.HEmp in
	  let exts = gen_exts sup_ext_var sub_ext_var rest_fields cdefs0 in
	  let res = F.mkStarH sup_h exts pos in
		res
	end
  | _ -> F.HEmp


(*
  Checks if c1 is subtype of c2 or the other way and returns the 
  list of classes going from c1 to c2 (or c2 to c1), including c2.

  If the first component of the result is true, c1 is subtype of c2.
  If it is false, c2 is subtype of c1
*)

let find_classes (c1 : ident) (c2 : ident) : (bool * data_decl list) = 
  let v1 = CH.V.create {ch_node_name = c1; ch_node_class = None; ch_node_coercion = None} in
  let v2 = CH.V.create {ch_node_name = c2; ch_node_class = None; ch_node_coercion = None} in
	try
	  let path, _ = PathCH.shortest_path class_hierarchy v1 v2 in
		(true, List.rev (List.map (fun e -> Gen.unsome ((CH.E.dst e).ch_node_class)) path))
	with
	  | Not_found -> 
		  try
			let path, _ = PathCH.shortest_path class_hierarchy v2 v1 in
			  (false, List.rev (List.map (fun e -> Gen.unsome ((CH.E.dst e).ch_node_class)) path))
		  with
			| Not_found -> failwith ("find_classes: " ^ c1 ^ " and " ^ c2 ^ " are not related!")


(* let rec sub_type (t1 : typ) (t2 : typ) = match t1 with *)
(*   | Named c1 -> begin match t2 with *)
(* 	    | Named c2 -> begin *)
(* 		    if c1 = c2 then true *)
(* 		    else if c1 = "" then true (\* t1 is null in this case *\) *)
(* 		    else  *)
(* 			  let v1 = CH.V.create {ch_node_name = c1;  *)
(* 								    ch_node_class = None;  *)
(* 								    ch_node_coercion = None} in *)
(* 			  let v2 = CH.V.create {ch_node_name = c2;  *)
(* 								    ch_node_class = None;  *)
(* 								    ch_node_coercion = None} in *)
(* 			  try *)
(* 				  let () = PathCH.shortest_path class_hierarchy v1 v2 in *)
(* 				  true *)
(* 			  with *)
(* 				| Not_found -> false *)
(*         end *)
(*         | Array _ | _ -> false (\* An Hoa add P.Array _ *\) *)
(*   end *)
(* 	(\* An Hoa *\) *)
(*   | Array (et1, _) -> begin *)
(* 	  match t2 with *)
(* 		| Array (et2, _) -> (sub_type et1 et2) *)
(* 		| _ -> false *)
(*   end *)
(*   |  _ -> t1 = t2 *)

let sub_type (t1 : typ) (t2 : typ) = sub_type t1 t2

and exp_to_check (e:exp) :bool = match e with
  | CheckRef _
  | Debug _
  | Dprint _
  | Bind _
  | Seq _
  | Unfold _
  | Unit _
  | Print _
  | VarDecl _
  | Cast _
  | Catch _
  | Block _
  | FConst _
  | Assert _ 
  | Cond _
  | Try _ 
  | Time _ 
  | Java _ -> false
  
  | Par _
  | Barrier _ 
  | BConst _
	      (*| ArrayAt _ (* An Hoa TODO NO IDEA *)*)
	      (*| ArrayMod _ (* An Hoa TODO NO IDEA *)*)
  | Assign _
  | ICall _
  | IConst _
  | While _ 
  | This _
  | Var _
  | Null _
  | EmptyArray _ (* An Hoa : NO IDEA *)
	(*| ArrayAlloc _*) (* An Hoa : NO IDEA *)
  | New _
  | Sharp _
  | SCall _
  | Label _
      -> true
  
  
let rec pos_of_exp (e:exp) :loc = match e with
	(*| ArrayAt b -> b.exp_arrayat_pos (* An Hoa *)*)
	(*| ArrayMod b -> b.exp_arraymod_pos (* An Hoa *)*)
  | CheckRef b -> b.exp_check_ref_pos
  | BConst b -> b.exp_bconst_pos
  | Bind b -> b.exp_bind_pos
  | Cast b -> b.exp_cast_pos
  | Catch b -> b.exp_catch_pos
  | Debug b -> b.exp_debug_pos
  | Dprint b -> b.exp_dprint_pos
  | Assign b -> b.exp_assign_pos
  | FConst b -> b.exp_fconst_pos
  | ICall b -> b.exp_icall_pos
  | IConst b -> b.exp_iconst_pos
  | Print (_,b) -> b
  | Seq b -> b.exp_seq_pos
  | VarDecl b -> b.exp_var_decl_pos
  | Unfold b -> b.exp_unfold_pos
  | Unit b -> b
  | This b -> b.exp_this_pos
  | Time (_,_,p)-> p
  | Var b -> b.exp_var_pos
  | Null b -> b
	| EmptyArray b -> b.exp_emparray_pos (* An Hoa *)
  | Cond b -> b.exp_cond_pos
  | Block b -> b.exp_block_pos
  | Barrier b -> b.exp_barrier_pos
  | Java b  -> b.exp_java_pos
  | Assert b -> b.exp_assert_pos
  | New b -> b.exp_new_pos
  | Sharp b -> b.exp_sharp_pos
  | SCall b -> b.exp_scall_pos
  | While b -> b.exp_while_pos
  | Try b -> b.exp_try_pos
  | Label b -> pos_of_exp b.exp_label_exp
  | Par b -> b.exp_par_pos
	  
let get_catch_of_exp e = match e with
	| Catch e -> e
	| _  -> Error.report_error {Err.error_loc = pos_of_exp e; Err.error_text = "malformed expression, expecting catch clause"}
  
(* let get_catch_of_exp e = *)
(*   let pr = !print_prog_exp in *)
(*   Debug.no_1 "get_catch_of_exp" pr pr_no get_catch_of_exp e *)

let check_proper_return cret_type exc_list f =
  let overlap_flow_type fl res_t = match res_t with
	| Named ot -> F.overlapping fl (exlist # get_hash ot)
	| _ -> false in
  let rec check_proper_return_f f0 = match f0 with
	| F.Base b->
              let res_t,b_rez = F.get_result_type f0 in
	      let fl_int = b.F.formula_base_flow.F.formula_flow_interval in
	      if b_rez && not(F.equal_flow_interval !error_flow_int fl_int)
                && not(F.equal_flow_interval !top_flow_int fl_int) &&
                not(F.equal_flow_interval !mayerror_flow_int fl_int) then
		  if not (sub_type res_t cret_type) then
		    Err.report_error{Err.error_loc = b.F.formula_base_pos;Err.error_text ="result type does not correspond with the return type";}
		  else ()
	      else 
                let () = x_tinfo_hp (add_str "fl_int" !print_dflow) fl_int no_pos in
                let () = x_tinfo_hp (add_str "norm_flow_int" !print_dflow) !norm_flow_int no_pos in
                let exc_list = !norm_flow_int::exc_list in
                let  _ = x_tinfo_hp (add_str "exc_list" (pr_list !print_dflow)) exc_list no_pos in
                if not (List.exists (fun c->
                  (* let _ =print_endline_quiet"XX" in *) F.subsume_flow c fl_int) exc_list) then
                let () = Debug.ninfo_pprint "Here:" no_pos in
                let () = Debug.ninfo_hprint (!print_dflow) fl_int no_pos in
                let () = Debug.ninfo_hprint (add_str "length(exc_list)" (fun l -> string_of_int (List.length l))) exc_list no_pos in
                if exc_list!= [] then
		Err.report_warning{Err.error_loc = b.F.formula_base_pos;Err.error_text ="the result type "^(!print_dflow fl_int)^" is not covered by the throw list"^(pr_list !print_dflow exc_list);}
	      (* WN: exception and result type do not match ..
              else if not(overlap_flow_type fl_int res_t) then
		Err.report_error{Err.error_loc = b.F.formula_base_pos;Err.error_text ="result type "^(!print_dflow res_t)^" does not correspond (overlap) with the flow type"^(!print_dflow fl_int);}
              *)
	      else
(* else *)
		(*let _ =print_string ("\n ("^(string_of_int (fst fl_int))^" "^(string_of_int (snd fl_int))^"="^(Exc.get_closest fl_int)^
		  (string_of_bool (Cpure.is_void_type res_t))^"\n") in*)
		if not(((F.equal_flow_interval !norm_flow_int fl_int)&&(Cpure.is_void_type res_t))|| (not (F.equal_flow_interval !norm_flow_int fl_int))) then
		  Error.report_error {Err.error_loc = b.F.formula_base_pos; Err.error_text ="no return in a non void function or for a non normaesl flow"}
		else ()
	| F.Exists b->
		  let res_t,b_rez = F.get_result_type f0 in
		  let fl_int = b.F.formula_exists_flow.F.formula_flow_interval in
		  if b_rez then
			if (F.equal_flow_interval !norm_flow_int fl_int) then
			  if not (sub_type res_t cret_type) then
				Err.report_error{Err.error_loc = b.F.formula_exists_pos;Err.error_text ="result type does not correspond with the return type";}
			  else ()
			else
			  if not (List.exists (fun c-> F.subsume_flow c fl_int) exc_list) then
				Err.report_error{Err.error_loc = b.F.formula_exists_pos;Err.error_text ="not all specified flow types are covered by the throw list";}
			  else if not(overlap_flow_type fl_int res_t) then
				Err.report_error{Err.error_loc = b.F.formula_exists_pos;Err.error_text ="result type does not correspond with the flow type";}
			  else ()
		  else
			(* let _ =print_string ("\n ("^(string_of_int (fst fl_int))^" "^(string_of_int (snd fl_int))^"="^(Exc.get_closest fl_int)^
			   (string_of_bool (Cpure.is_void_type res_t))^"\n") in*)
			if not(((F.equal_flow_interval !norm_flow_int fl_int)&&(Cpure.is_void_type res_t))|| (not (F.equal_flow_interval !norm_flow_int fl_int))) then
			  Error.report_error {Err.error_loc = b.F.formula_exists_pos;Err.error_text ="no return in a non void function or for a non normal flow"}
			else ()
	| F.Or b-> check_proper_return_f b.F.formula_or_f1 ; check_proper_return_f b.F.formula_or_f2 in
  let rec helper f0 = match f0 with
	| F.EBase b   -> (match b.F.formula_struc_continuation with | None -> () | Some l -> helper l)
	| F.ECase b   -> List.iter (fun (_,c)-> helper c) b.F.formula_case_branches
	| F.EAssume b ->
			if (F.isAnyConstFalse b.F.formula_assume_simpl)||(F.isAnyConstTrue b.F.formula_assume_simpl) then ()
			else check_proper_return_f b.F.formula_assume_simpl
	| F.EInfer b  -> ()(*check_proper_return cret_type exc_list b.formula_inf_continuation*)
	| F.EList b   -> List.iter (fun c-> helper(snd c)) b 
	in
    helper f

 
(* type: Globals.typ -> Globals.nflow list -> F.struc_formula -> unit *)
let check_proper_return cret_type exc_list f = 
  let pr1 = pr_list pr_no in
  let pr2 = !print_struc_formula in
  Debug.no_2 "check_proper_return" pr1 pr2 pr_no (fun _ _ -> check_proper_return cret_type exc_list f) exc_list f
(* TODO : res must be consistent with flow outcome *)

let formula_of_unstruc_view_f vd = F.formula_of_disjuncts (fst (List.split vd.view_un_struc_formula))


let vdef_fold_use_bc prog ln2  = match ln2 with
  | F.ViewNode vn -> 
    (try 
      let vd = look_up_view_def_raw 3 prog.prog_view_decls vn.F.h_formula_view_name in
      match vd.view_raw_base_case with
        | None -> None
        | Some f-> Some {vd with view_formula = F.formula_to_struc_formula f}
    with  
    | Not_found -> report_error no_pos ("fold: view def not found:"^vn.F.h_formula_view_name^"\n"))
  | _ -> None

let vdef_fold_use_bc prog ln2  = 
  let pr1 x = "?" in
  let pr2 x = match x with
    | None -> "None"
    | Some f -> !print_struc_formula f.view_formula in
  Debug.no_1 "vdef_fold_use_bc" pr1 pr2 (fun _ -> vdef_fold_use_bc prog ln2) ln2

(* WN : this helps build a vdef to perform right lemma folding *)
(* This will make sure that the variables in coer
coincide with the variables in the corresponding
view definition
   In the present of permissions, this may not hold
   as the LHS of a view definition does not have permissions
   while the LHS of a coer does.
*)

let vdef_lemma_fold prog coer  = 
  let cfd = coer.coercion_fold_def in
  let lhs = coer.coercion_head in
  (* body contains orig=false but not body_norm*)
  (* let rhs = F.formula_to_struc_formula coer.coercion_body in *)
  let rhs = (* F.formula_to_struc_formula *) coer.coercion_body_norm in
  (* let () = Debug.info_hprint (add_str "head" Cprinter.string_of_formula) lhs no_pos in *)
  if cfd # is_init then                 (* how do we use cfd? why do we need it? *)
    cfd # get
  else
    let vd2 = match lhs with
      | F.Base bf ->
            begin
              match bf.F.formula_base_heap with
                | F.ViewNode vn -> 
                      (try 
                        let vd = look_up_view_def_raw 13 prog.prog_view_decls vn.F.h_formula_view_name in
                        let to_vars = vd.view_vars in
                        let from_vars = vn.F.h_formula_view_arguments in
                        let subs = List.combine from_vars to_vars in
                        (* let pr = Cprinter.string_of_spec_var_list in *)
                        (* let () = x_tinfo_hp (add_str "from_vars" pr)  from_vars no_pos in *)
                        (* let () = x_tinfo_hp (add_str "to_vars" pr) to_vars no_pos in *)
                        let rhs = F.subst_struc subs rhs in
                        (* let un_struc =  F.struc_to_view_un_s (F.label_view rhs) in *)
                        let un_struc =  F.get_view_branches (F.label_view rhs) in
                        Some {vd with view_formula = rhs; view_un_struc_formula = un_struc}
                      with  
                        | Not_found -> None
                      )
                | _ -> None 
            end
      | _ -> None in
    (* let () = Debug.info_hprint (add_str "vd2" (pr_option Cprinter.string_of_view_decl_short)) vd2 no_pos in *)
    let () = cfd # set vd2 in
    vd2

(* let vdef_lemma_fold prog coer  =  *)
(*   let cfd = coer.coercion_fold_def in *)
(*   let lhs = coer.coercion_head in *)
(*   let rhs = coer.coercion_body_norm in *)
(*   let () = Debug.info_hprint (add_str "head" !print_formula) lhs no_pos in *)
(*   let () = Debug.info_hprint (add_str "body" !print_struc_formula) rhs no_pos in *)
(*   if cfd # is_init then cfd # get *)
(*   else *)
(*     let vd2 = match lhs with *)
(*       | F.Base bf -> *)
(*             begin *)
(*               match bf.F.formula_base_heap with *)
(*                 | F.ViewNode vn ->  *)
(*                       (try  *)
(*                         let vd = look_up_view_def_raw 13 prog.prog_view_decls vn.F.h_formula_view_name in *)
(*                         Some {vd with view_formula = rhs} *)
(*                       with   *)
(*                         | Not_found -> None *)
(*                       ) *)
(*                 | _ -> None  *)
(*             end *)
(*       | _ -> None in *)
(*     let () = cfd # set vd2 in *)
(*     vd2 *)

let vdef_lemma_fold prog coer =
  let op = coer.coercion_fold_def in
  let pr _ = pr_option !print_view_decl_short (op # get) in
   Debug.no_1 "vdef_lemma_fold" pr pr (fun _ -> vdef_lemma_fold prog coer) ()

let get_xpure_one vdef rm_br  =
  match rm_br with
    | Some l -> let n=(List.length l) in
      if n<(List.length vdef.view_prune_branches) then
        (* if !force_verbose_xpure then Some vdef.view_x_formula  else *) None
      else (match vdef.view_complex_inv with
        | None -> None
        | Some f -> Some f)  (* unspecialised with a complex_inv *)
    | None -> Some vdef.view_x_formula

let get_xpure_one vdef rm_br  =
  let pr mf = !print_mix_formula mf in
  Debug.no_1 "get_xpure_one" pr_no (pr_option pr) (fun _ -> get_xpure_one vdef rm_br) rm_br

let any_xpure_1 prog (f:F.h_formula) : bool =
  let ff e = match e with
	| F.ViewNode ({ F.h_formula_view_node = p;
	  F.h_formula_view_name = c;
	  F.h_formula_view_remaining_branches = rm_br;
	  F.h_formula_view_pos = pos}) ->
          let vdef = look_up_view_def_num 1 pos prog.prog_view_decls c in
          (match get_xpure_one vdef rm_br with
            | None -> Some false
            | Some r -> Some true (* check against vdef for complex_inv *)
          ) 
    | _ -> None
  in
  let comb_f = List.exists (fun x-> x) in
  F.fold_h_formula f ff comb_f

let any_xpure_1 prog (f:F.h_formula) : bool =
  let pr = !print_h_formula in
  Debug.no_1 "any_xpure_1" pr string_of_bool (fun _ -> any_xpure_1 prog f) f 

(*find and add uni_vars to view*)
(*if the view is recursive, only consider its view_vars
otherwise, go into its heap node and 
find all possible uni_vars*)
let rec add_uni_vars_to_view_x cprog (l2r_coers:coercion_decl list) (view:view_decl) : view_decl =
  let view_vars = view.view_vars in
  let look_up_one_x (coer:coercion_decl) (view:view_decl): P.spec_var list =
    let coer_uni_vars = coer.coercion_univ_vars in
    if (coer_uni_vars=[]) then []
    else
      let rec process_h_formula (h_f:F.h_formula):P.spec_var list = 
        match h_f with
          | F.ViewNode vn ->
              (* let () = print_string "\n process_h_formula: F.ViewNode \n" in *)
              (* let () = print_string ("\n process_h_formula:" *)
              (*                       ^"\n ### vn = " ^ (Cprinter.string_of_ident vn.F.h_formula_view_name) *)
              (*                       ^"\n ### view.view_name = " ^ (Cprinter.string_of_ident view.view_name) *)
              (*                       ^ "\n\n") in *)
              if ((String.compare vn.F.h_formula_view_name view.view_name)!=0) then []
              else
                let args = vn.F.h_formula_view_arguments in
                (* let () = print_string ("\n process_h_formula:" *)
                (*                       ^"\n ### coer_uni_vars = " ^ (Cprinter.string_of_spec_var_list coer_uni_vars) *)
                (*                       ^"\n ### args = " ^ (Cprinter.string_of_spec_var_list args) *)
                (*                       ^"\n ### view_vars = " ^ (Cprinter.string_of_spec_var_list view_vars) *)
                (* ^ "\n\n") in *)
            (*at this point |view_vars| = |args|*)
                let rec helper args view_vars =
                  match args, view_vars with
                    | arg::argvs, var::vars ->
                        let res = helper argvs vars in
                        if (List.mem arg coer_uni_vars) then var::res
                        else res
                    | _ -> []
                in
                helper args view_vars
          | F.Star {  F.h_formula_star_h1 = h1;
                       F.h_formula_star_h2 = h2}
              -> 
              (* let () = print_string "\n process_h_formula: F.Star \n" in *)
              let vars1 =  process_h_formula h1 in
              let vars2 =  process_h_formula h2 in
              P.remove_dups_svl vars1@vars2
              
          | _ -> 
              (* let () = print_string "\n process_h_formula: [] \n" in *)
              []
      in
      let body = coer.coercion_body in
      match body with
        | F.Base {F.formula_base_heap = h}
        | F.Exists {F.formula_exists_heap = h} ->
            (* let () = print_string "\n process_h_formula: F.Exists \n" in *)
            process_h_formula h
        | _ -> []
  in 
  let look_up_one (coer:coercion_decl) (view:view_decl): P.spec_var list =
    Debug.no_2 "look_up_one"
        !print_coercion
        !print_view_decl
        !print_svl
        look_up_one_x coer view
  in
  let res = List.map (fun coer -> look_up_one coer view) l2r_coers in
  let res1 = List.flatten res in
  (* let () = print_string ("\n add_uni_vars_to_view:" *)
  (*                       ^"\n ### res1 = " ^ (Cprinter.string_of_spec_var_list res1) *)
  (*                       ^ "\n\n") in *)
  let uni_vars = P.remove_dups_svl res1 in
  if (view.view_is_rec) then {view with view_uni_vars = uni_vars}
  else
	let rec process_h_formula (h_f:F.h_formula):P.spec_var list = match h_f with
		| F.ViewNode vn ->
            if ((String.compare vn.F.h_formula_view_name view.view_name)=0) then []
			else
				let vdef = look_up_view_def_raw 4 cprog.prog_view_decls vn.F.h_formula_view_name in
				let vdef = add_uni_vars_to_view_x cprog l2r_coers vdef in
				let vdef_uni_vars = vdef.view_uni_vars in
				let fr = vdef.view_vars in
				let t = vn.F.h_formula_view_arguments in
				let vdef_uni_vars = P.subst_var_list_avoid_capture fr t vdef_uni_vars in
				vdef_uni_vars
        | F.Star {  F.h_formula_star_h1 = h1;
					F.h_formula_star_h2 = h2} -> 
				let vars1 =  process_h_formula h1 in
                let vars2 =  process_h_formula h2 in
                P.remove_dups_svl vars1@vars2
        | _ -> [] in
    let rec process_struc_formula (f:F.struc_formula):P.spec_var list = match f with
          | F.EBase e ->
            (*find all possible universal vars from a h_formula*)
              let vars1 = match e.F.formula_struc_base with
                  | F.Base {F.formula_base_heap = h;F.formula_base_pure = p}
                  | F.Exists {F.formula_exists_heap = h;F.formula_exists_pure = p} ->
                      let vars = process_h_formula h in
                      (match vars with
                        | [] -> []
                        | v::vs -> 
                            let xs = MP.find_closure_mix_formula v p in
                            let xs = Gen.BList.intersect_eq P.eq_spec_var xs view_vars in xs)
                (*vars is the set of all possible uni_vars in all nodes*)
                  | _ -> []
              in
              let vars2 = match e.F.formula_struc_continuation with | None -> [] | Some l -> process_struc_formula l in
              P.remove_dups_svl (vars1@vars2)
		  | F.EList b -> P.remove_dups_svl (List.flatten (List.map (fun c-> process_struc_formula (snd c)) b))
          | _ ->
              let () = print_string "[add_uni_vars_to_view] Warning: only handle EBase \n" in
              []
      in
    let vars = process_struc_formula view.view_formula in
    let vars = vars@uni_vars in
    let vars = P.remove_dups_svl vars in
    {view with view_uni_vars = vars}

(*find and add uni_vars to view*)
let add_uni_vars_to_view cprog (l2r_coers:coercion_decl list) (view:view_decl) : view_decl =
  Debug.no_2 "add_uni_vars_to_view"
      !print_coerc_decl_list
      !print_view_decl
      !print_view_decl
      (fun _ _ -> add_uni_vars_to_view_x cprog l2r_coers view) l2r_coers view

(************************************************************
Building the call graph for procedure hierarchy based on Cast
*************************************************************)
module IdentComp = struct
  type t = ident
  let compare = compare
  let hash = Hashtbl.hash
  let equal = ( = )
end
module IG = Graph.Persistent.Digraph.Concrete(IdentComp)
module IGO = Graph.Oper.P(IG)
module IGC = Graph.Components.Make(IG)
module IGP = Graph.Path.Check(IG)
module IGN = Graph.Oper.Neighbourhood(IG)
module IGT = Graph.Topological.Make(IG)

let ex_args f a b = f b a

let ngs_union gs = 
  List.fold_left IGO.union IG.empty gs 

let addin_callgraph_of_exp (cg:IG.t) exp mnv : IG.t = 
  let f e = 
    match e with
    | ICall e ->
      (* let () = print_endline_quiet(mnv ^ " -> " ^ e.exp_icall_method_name) in *)
      Some (IG.add_edge cg mnv e.exp_icall_method_name)
    | SCall e ->
      (* let () = print_endline_quiet(mnv ^ " -> " ^ e.exp_scall_method_name) in *)
      Some (IG.add_edge cg mnv e.exp_scall_method_name)
    | _ -> None
  in
  fold_exp exp f ngs_union cg
	
let addin_callgraph_of_proc cg proc : IG.t = 
  match proc.proc_body with
  | None -> cg
  | Some e -> addin_callgraph_of_exp cg e proc.proc_name

let callgraph_of_prog prog : IG.t = 
  let cg = IG.empty in
  let pn pc = pc.proc_name in
  (*let mns = List.map pn prog.old_proc_decls in*)
  let mns = List.map pn (list_of_procs prog) in 
  let cg = List.fold_right (ex_args IG.add_vertex) mns cg in
  (*List.fold_right (ex_args addin_callgraph_of_proc) prog.old_proc_decls cg*)
  Hashtbl.fold (fun i pd acc -> ex_args addin_callgraph_of_proc pd acc) prog.new_proc_decls cg

let count_term_scc (procs: proc_decl list) : int =
  List.fold_left (fun acc p -> 
    acc + (F.count_term_struc p.proc_static_specs)) 0 procs

(* Mutual groups with logical phase variables added *)
(* those with logical variables explicitly added will
   not have a re-numbering done *)
let stk_scc_with_phases = new Gen.stack 

(* Termination: Add the call numbers and the implicit phase 
 * variables to specifications if the option 
 * --dis-call-num and --dis-phase-num are not enabled (default) *)
let rec add_term_nums_prog (cp: prog_decl) : prog_decl =
  if !Globals.dis_call_num && !Globals.dis_phase_num then cp 
  else 
    let (prim_grp, mutual_grps) = re_proc_mutual (sort_proc_decls (list_of_procs cp)) in
    let log_vars = cp.prog_logical_vars in
    (* Only add the phase variables into scc group with >1 Term *)
    let mutual_grps = List.map (fun scc -> (count_term_scc scc, scc)) mutual_grps in
    let mutual_grps = List.filter (fun (c,_) -> c>0) mutual_grps in
    if mutual_grps!=[] then 
      begin
        let pr p = p.proc_name in
        x_dinfo_zp (lazy (">>>>>> [term.ml][Adding Call Number and Phase Logical Vars] <<<<<<")) no_pos;
        x_dinfo_hp (add_str ("Mutual Groups") (pr_list (pr_pair string_of_int (pr_list pr)))) mutual_grps no_pos;
        x_dinfo_pp "\n" no_pos

      end;
    let pvs = List.map (fun (n, procs) ->
        let mn = List.hd procs in
        (* TNT Inference: Enable call_num but Disable phase_num *)
        let inf_tnt = (Globals.infer_const_obj # is_term) || (List.exists (fun proc -> 
          F.is_inf_tnt_struc_formula proc.proc_static_specs) procs) in 
        let pv = add_term_nums_proc_scc procs cp.new_proc_decls log_vars
          ((not !dis_call_num) || inf_tnt) ((not !dis_phase_num) && (not inf_tnt) && n>1 && mn.proc_is_recursive) 
        in (match pv with 
          | [] -> ()
          | x::_ -> stk_scc_with_phases # push mn.proc_call_order); pv
    ) mutual_grps
    in
    let () = x_dinfo_hp (add_str "Mutual Grps with Phases" 
        (pr_list (string_of_int))) (stk_scc_with_phases # get_stk) no_pos in
    let () = x_dinfo_hp (add_str "Mutual Grps" (pr_list (pr_pair string_of_int (pr_list (fun p -> p.proc_name))))) mutual_grps no_pos in
    let () = x_dinfo_hp (add_str "Phase Vars Added" (pr_list (pr_list !P.print_sv))) pvs no_pos in
    let pvl = Gen.BList.remove_dups_eq P.eq_spec_var 
      ((List.concat pvs) @ log_vars) in
    { cp with prog_logical_vars = pvl } 

(* Do not add call numbers and phase variables 
 * into the specification of a primitive call. 
 * The return value contains a list of new 
 * added spec_var *)   
and add_term_nums_proc_scc_x (procs: proc_decl list) tbl log_vars (add_call: bool) (add_phase: bool) =
  let n_procs, pvs = List.split (List.map (fun proc -> 
    add_term_nums_proc proc log_vars add_call add_phase
  ) procs) in 
  let pvs = List.concat pvs in
  let n_procs = List.map (fun proc -> { proc with
    (* Option 1: Add logical variables of scc group into specifications for inference *)
    (* Option 2: Store the set of logical variables into proc_logical_vars 
     * It will be added into the initial context in check_proc *)
       proc_logical_vars = pvs;
  }) n_procs in
  let () = List.iter (fun proc ->
    Hashtbl.replace tbl proc.proc_name proc 
  ) n_procs in 
  pvs

and add_term_nums_proc_scc (procs: proc_decl list) tbl log_vars (add_call: bool) (add_phase: bool) =
  let pr ps = pr_list (fun p -> p.proc_name) ps in
  Debug.no_1 "add_term_nums_proc_scc" pr !P.print_svl
      (fun _ -> add_term_nums_proc_scc_x (procs: proc_decl list) tbl log_vars (add_call: bool) (add_phase: bool)) procs

(* adding call number and phase variables into spec *)
and add_term_nums_proc (proc: proc_decl) log_vars add_call add_phase = 
  if not (proc.proc_is_main) then (proc, [])
  else if (not add_call) && (not add_phase) then (proc, [])
  else 
    let call_num = 
      if add_call then Some proc.proc_call_order
      else None
    in
    let n_ss, pvl1 = F.add_term_nums_struc proc.proc_static_specs log_vars call_num add_phase in
    let n_ds, pvl2 = F.add_term_nums_struc proc.proc_dynamic_specs log_vars call_num add_phase in
    ({ proc with
      proc_static_specs = n_ss; 
      proc_dynamic_specs = n_ds; 
    }, pvl1 @ pvl2)


let collect_hp_rels prog= Hashtbl.fold (fun i p acc-> 
	let name = unmingle_name p.proc_name in
	(List.map (fun c-> name,c) p.proc_hpdefs)@acc) prog.new_proc_decls []

let look_up_cont_args_x a_args vname cviews=
  let vdef = look_up_view_def_raw 5 cviews vname in
  let pr_args = List.combine vdef.view_vars a_args in
  List.fold_left (fun ls cont_sv -> ls@[List.assoc cont_sv pr_args]) [] vdef.view_cont_vars

let look_up_cont_args a_args vname cviews=
  let pr1 = !Cpure.print_svl in
  Debug.no_2 "look_up_cont_args" pr1 pr_id pr1
      (fun _ _ -> look_up_cont_args_x a_args vname cviews) a_args vname

let exp_fv (e:exp) =
  let comb_f = List.concat in
  let f (ac:ident list) e : ident list option= match e with
    | Assert b ->
	  let l = (Gen.fold_opt F.struc_fv b.exp_assert_asserted_formula)@ (Gen.fold_opt F.fv b.exp_assert_assumed_formula)in
	  Some (ac@ List.map P.name_of_spec_var l)
    | Java _ -> Some ac
    | CheckRef b-> Some (b.exp_check_ref_var::ac)
    | BConst _ -> Some ac
    | Debug _ -> Some ac
    | Dprint b -> Some (b.exp_dprint_visible_names@ac)
    | FConst _ -> Some ac
    | ICall b -> Some (b.exp_icall_receiver::b.exp_icall_arguments@ac)
    | IConst _ -> Some ac
    | New b -> Some ((List.map snd b.exp_new_arguments)@ac)
    | Null _ -> Some ac
    | EmptyArray _ -> Some ac
    | Print _ -> Some ac
    | Barrier b-> Some ((snd b.exp_barrier_recv)::ac)
    | SCall b -> Some (ac@b.exp_scall_arguments)
    | This _ -> Some ac
    | Time _ -> Some ac
    | Var b -> Some (b.exp_var_name::ac)
    | VarDecl b -> Some (b.exp_var_decl_name::ac)
    | Unfold b -> Some ((P.name_of_spec_var b.exp_unfold_var)::ac)
    | Unit _ -> Some ac
    | Sharp _ -> Some ac
    |  _ -> None
  in
  let f_args (ac:ident list) e : ident list= match e with
    | Label b -> ac
    | Assign b -> b.exp_assign_lhs::ac
    | Bind b ->ac@ ((snd b.exp_bind_bound_var)::(List.map snd b.exp_bind_fields))
    | Block b -> ac@(List.map snd b.exp_block_local_vars)
    | Cond b ->b.exp_cond_condition::ac
    | Cast b -> ac
    | Catch b -> (Gen.fold_opt (fun (_,c)-> [c]) b.exp_catch_var)@ac
    | Seq b -> ac
    | While b -> ac@[b.exp_while_condition]@(List.map P.name_of_spec_var (F.struc_fv b.exp_while_spec))
    | Try b -> ac
    | _ -> ac in
  fold_exp_args e [] f f_args comb_f []


let get_mut_vars_bu_x cprocs (e0 : exp): (ident list * ident list) =
   let f e=
    match e with
      | Var { exp_var_name = id} -> Some [id]
      | _ -> None
  in
  let get_vars e= fold_exp e f (List.concat) [] in
  let rec collect_lhs_ass_vars e=
    match e with
      | Assign {exp_assign_lhs = id;
        exp_assign_rhs = rhs;} -> begin
           match rhs with
             | Var {exp_var_name = rid} ->
                   Some [(id, [(id,rid)])]
             | _ -> Some [(id,[])]
        end
      | _ -> None
  in
  let look_up_inst_args_x proc act_args=
    let pr_args_wi = List.combine proc.proc_args_wi act_args in
    List.fold_left (fun r ((_,ni_info), act_arg) -> if ni_info = I then r@[act_arg] else r) [] pr_args_wi
  in
  let look_up_inst_args proc act_args=
    let pr1 p = p.proc_name in
    let pr2 = pr_list pr_id in
    Debug.no_2 "look_up_inst_args" pr1 pr2 pr2
        (fun _ _ -> look_up_inst_args_x proc act_args)
        proc act_args
  in
  let rec collect_bind_vars e=
    match e with
      | Bind {exp_bind_bound_var = (_,id);
        exp_bind_body = b;
        } -> begin let b_opt = collect_bind_vars b in
        match b_opt with
          | None -> Some [id]
          | Some ids -> Some (id::ids)
        end
      | Unfold u -> Some [(P.name_of_spec_var u.exp_unfold_var)]
      | SCall sc -> begin if sc.exp_scall_is_rec then None else
          let pn = sc.exp_scall_method_name in
          let act_args = sc.exp_scall_arguments in
          try
            let proc = List.find (fun p -> String.compare pn p.proc_name=0) cprocs in
            Some (look_up_inst_args proc act_args)
          with _ -> None
        end
      | _ -> None
  in
  let lhs_eq_vars = fold_exp e0 collect_lhs_ass_vars (List.concat) [] in
  let lhs_vars, eqs = List.fold_left (fun (r1,r2) (id, ls) -> (r1@[id], r2@ls)) ([],[]) lhs_eq_vars in
  let bind_vars = fold_exp e0 collect_bind_vars(List.concat) [] in
  (*todo*)
  let mut_unaccess_vars = (* Gen.find_close_ids *) (lhs_vars@bind_vars)  in
  let mut_unaccess_vars1 = Gen.BList.remove_dups_eq (fun s1 s2 -> String.compare s1 s2 = 0) mut_unaccess_vars in
  (mut_unaccess_vars1, Gen.BList.difference_eq (fun s1 s2 -> String.compare s1 s2 = 0) mut_unaccess_vars1 lhs_vars)


let get_mut_vars_bu cprocs (e0 : exp) =
  let pr1 = !print_prog_exp in
  let pr2 = pr_list pr_id in
  Debug.no_1 "get_mut_vars_bu" pr1 (pr_pair pr2 pr2)
      (fun _ -> get_mut_vars_bu_x cprocs e0) e0

let update_mut_vars_bu iprog cprog scc_procs =
  let string_cmp=(fun s1 s2 -> String.compare s1 s2 = 0) in
  let update_mut_vars_proc cprocs proc=
    match proc.proc_body with
      | Some p ->
            let mut_unchange_vars, mut_vars = get_mut_vars_bu cprocs p in
            let new_args_wi,diff_args_i = List.fold_left (fun (r1,r2) (arg, ni_info) ->
                if ni_info = I then (r1@[(arg, ni_info)],r2) else
                  if Gen.BList.mem_eq string_cmp arg mut_vars then
                    (r1@[(arg, I)],r2@[arg])
                  else (r1@[(arg, ni_info)],r2)
            ) ([],[]) proc.proc_args_wi in
            (*update hp_decl of precondition*)
            let () = if diff_args_i = [] then () else
              let () = x_tinfo_hp (add_str "\n update ni:" pr_id) (proc.proc_name ^ ": " ^ (String.concat "," diff_args_i)) no_pos in
              let hpargs = Cformula.get_hp_rel_pre_struc_formula proc.proc_static_specs in
              let todo_unk = List.map (fun (hp,args) ->
                  let s_args = List.map P.name_of_spec_var args in
                  let inter = Gen.BList.intersect_eq string_cmp s_args diff_args_i in
                  if inter = [] then () else
                    let hp_decl = look_up_hp_def_raw cprog.prog_hp_decls (P.name_of_spec_var hp) in
                    let pr = List.combine hp_decl.hp_vars_inst s_args in
                    let n_vars_inst = List.map (fun ((form_sv, info), act_sv) ->
                        if Gen.BList.mem_eq string_cmp act_sv inter then (form_sv, I) else (form_sv, info)
                    ) pr in
                    let () = hp_decl.hp_vars_inst <- n_vars_inst in
                    ()
              ) hpargs in
              ()
            in
            {proc with proc_args_wi = new_args_wi}
      | None -> proc
  in
  let new_scc_procs, _ = List.fold_left (fun (r1,done_procs) scc ->
      let new_scc = match scc with
        | [proc] -> let n_proc = update_mut_vars_proc done_procs proc in
          [n_proc]
        | _ -> (*todo: compute fixpoint for mutrec*)
              List.map (update_mut_vars_proc done_procs) scc
      in
      (r1@[new_scc], done_procs@(List.filter (fun p -> p.proc_is_main) new_scc))
  ) ([],[]) scc_procs
  in
  new_scc_procs

let eq_templ_decl t1 t2 = String.compare t1.templ_name t2.templ_name == 0
let get_emp_map_x cprog=
  let helper vdef=
    let o_base = if !Globals.norm_cont_analysis then
      let () = Debug.ninfo_hprint (add_str "vdef.view_seg_opz" (pr_opt !Cpure.print_formula)) vdef.view_seg_opz no_pos in
      vdef.view_seg_opz
    else
      match vdef.view_base_case with
        | None -> None
        | Some (p,_) -> begin
            let neq_null_svl = Cpure.get_neq_null_svl p in
            if neq_null_svl != [] then None else
              Some p
          end
    in
    (vdef.view_name, P.SpecVar (Named vdef.view_data_name, self, Unprimed)::vdef.view_vars, o_base)
  in
  List.map helper cprog.prog_view_decls

let get_emp_map cprog=
  let pr1 = fun _ -> "cprog" in
  let pr3 = fun p -> match p with
    | None -> "None"
    | Some f -> !Cpure.print_formula f
  in
  let pr2 = pr_list (pr_triple pr_id !Cpure.print_svl pr3) in
  Debug.no_1 "get_emp_map" pr1 pr2
      (fun _ -> get_emp_map_x cprog) cprog

(*
  is complex: both lhs and rhs <=4 pred instance for segmentation optimization
*)
let is_complex_entailment_4graph_x prog ante conseq=
  (* let () = Debug.info_hprint (add_str "is_complex_entailment_4graph" pr_id) "start" no_pos in *)
  let is_null_node (Cpure.SpecVar (_,id,_)) = String.compare id null_name = 0
  in
   let seg_opz_views = List.fold_left (fun r vdecl ->
       match vdecl.view_seg_opz with
         | Some _ -> r@[vdecl.view_name]
         | None -> r
   ) [] prog.prog_view_decls in
   let () = Debug.ninfo_hprint (add_str "seg_opz_views" (pr_list pr_id)) seg_opz_views no_pos in
   if List.length seg_opz_views  > 1 then false else
   let ldnodes, lvnodes,_ = (Cformula.get_hp_rel_formula ante) in
   let rvnodes = (Cformula.get_views_struc conseq) in
   let rdnodes = Cformula.get_datas_struc conseq in
   let lvleng =  List.length lvnodes in
   let rvleng =  List.length rvnodes in
   if (rvleng = 1 && rdnodes = [] &&  lvleng = 0) ||
     (lvleng < graph_norm_instance_threshold && rvleng < graph_norm_instance_threshold)
     || List.exists (fun vn -> is_null_node vn.Cformula.h_formula_view_node) (rvnodes@lvnodes)
   then
     false else
     begin try
       (*explicit quantifiers in rhs*)
       let is_rhs_ex_quans = match conseq with
         | F.EBase eb ->
           let quans,bare = F.split_quantifiers eb.F.formula_struc_base in
           let () = Debug.ninfo_hprint (add_str "quans" !Cpure.print_svl) quans no_pos in
           if quans = [] then false else
             let _, mf, _, _, _, _ = F.split_components bare in
             let eqnull_svl =  Mcpure.get_null_ptrs mf in
             let eqs = (Mcpure.ptr_equations_without_null mf) in
             let svl_eqs = List.fold_left (fun r (sv1,sv2) -> r@[sv1;sv2]) [] eqs in
             (*temporal dis null*)
             if (eqnull_svl != []) then
               if not (rdnodes = [] (* && ldnodes = [] *)) then true else
                 Cpure.diff_svl quans (svl_eqs@eqnull_svl) != []
             else
               Cpure.diff_svl quans (svl_eqs) != []
         | _ -> true
       in
       let () = Debug.ninfo_hprint (add_str "is_rhs_ex_quans" string_of_bool) is_rhs_ex_quans no_pos in
       if is_rhs_ex_quans then false else
         let vnodes = lvnodes@rvnodes in
         let n_seg_vnodes = List.fold_left (fun count vn ->
             if Gen.BList.mem_eq (fun s1 s2 -> String.compare s1 s2 = 0) vn.Cformula.h_formula_view_name seg_opz_views then count+1 else count
         ) 0 vnodes in
         n_seg_vnodes >=  ((* graph_norm_instance_threshold + *) graph_norm_instance_threshold)
     with _ -> false
     end

let is_complex_entailment_4graph prog ante conseq=
  let pr1 = !Cformula.print_formula in
  let pr2 = !Cformula.print_struc_formula in
  Debug.no_2 "is_complex_entailment_4graph" pr1 pr2 string_of_bool
      (fun _ _ -> is_complex_entailment_4graph_x prog ante conseq) ante conseq

(* 
 * + Return:
 *     - true if vdecl is a touching predicate,
 *     - otherwise return false 
 * + Note: 
 *    - check only inductive cases (contain heap nodes)
 *    - generated disequality constrains between forward_poiters and self
 *    - if all the constrains are implied by the pure part of view's definietion,
 *      then the view is nontouching
 *)
let is_touching_view_x (vdecl: view_decl) : bool =
  (* requires: view_decl must be preprocessed to fill the view_cont_vars field *)
  let vname = vdecl.view_name in
  let pos = vdecl.view_pos in
  let forward_ptrs = vdecl.view_forward_ptrs in
  let is_touching_branch branch = (
    let (_,mf,_,_,_,_) = F.split_components branch in
    let self_sv = P.SpecVar (Named vdecl.view_data_name, self, Unprimed) in
    let nontouching_cond = (
      let conds = List.map (fun y -> P.mkNeqVar self_sv y pos) forward_ptrs in
      List.fold_left (fun x1 x2 -> P.mkAnd x1 x2 pos ) (P.mkTrue pos) conds
    ) in
    let pf = MP.pure_of_mix mf in
    (* to ensure nontouching property, the pure part of a branch must *)
    (* imply the nontouching condition                                *)
    not (!imply_raw pf nontouching_cond)
  ) in
  let branches, _ = List.split vdecl.view_un_struc_formula in
  List.for_all is_touching_branch branches

let is_touching_view (vdecl: view_decl) : bool =
  let pr = !print_view_decl in
  let pr_out = string_of_bool in
  Debug.no_1 "is_touching_view" pr pr_out is_touching_view_x vdecl

(* 
 * + Return:
 *     - true if vdecl is a segmented predicate,
 *     - otherwise return false 
 * + Note: 
 *    - check only inductive cases (contain heap nodes)
 *    - generated equality constrains between forward_pointers and null
 *    - if all the constrains is implied by the pure part of view's definietion,
 *      then the view is nonsegmented
 *)
(* TRUNG TODO: check segmented condition *)
let is_segmented_view_x (vdecl: view_decl) : bool =
  (* requires: view_decl must be preprocessed to fill the view_cont_vars field *)
  let pos = vdecl.view_pos in
  let forward_ptrs = vdecl.view_forward_ptrs in
  let is_segmented_branch branch = (
    let (_,mf,_,_,_,_) = F.split_components branch in
    let pf = MP.pure_of_mix mf in
    List.exists (fun sv ->
      let null_cond = P.mkNull sv pos in
      not (!imply_raw pf null_cond)
    ) forward_ptrs
  ) in
  let branches, _ = List.split vdecl.view_un_struc_formula in
  let segmented = (List.for_all is_segmented_branch branches) in
  segmented

let is_segmented_view (vdecl: view_decl) : bool =
  let pr = !print_view_decl in
  let pr_out = string_of_bool in
  Debug.no_1 "is_segmented_view" pr pr_out is_segmented_view_x vdecl

module ViewGraph = struct
  module Vertex = struct
    type t = ident
    let compare = String.compare
    let hash = Hashtbl.hash
    let equal v1 v2 = (String.compare v1 v2 == 0)
  end

  type vertex_env = (string * string) list (* list of vertex name & its typename *)

  module Label = struct
    type t = | DataField of (ident * ident)   (* data name + field name *)
             | ViewField of (ident * ident)   (* view name + field name *)
             | Equality

    let compare e1 e2 = match e1, e2 with
      | DataField (d1,f1), DataField (d2,f2) ->
          let compare_host = (String.compare d1 d2) in
          if (compare_host != 0) then compare_host
          else String.compare f1 f2
      | DataField _, _ -> -1
      | ViewField _, DataField _ -> 1
      | ViewField (v1,f1), ViewField (v2,f2) -> 
          let compare_host = (String.compare v1 v2) in
          if (compare_host != 0) then compare_host
          else String.compare f1 f2
      | ViewField _, Equality -> -1
      | Equality, Equality -> 0
      | Equality, _ -> 1

    let default = Equality
  end
  
  module Weight = struct
    type label = Label.t
    type t = int
    let weight lbl = match lbl with
      | Label.Equality -> 0       (* to make sure the shortest always choose *)
      | Label.DataField _ -> 1    (* equality, then data field, then view field *)
      | Label.ViewField _ -> 100
    let zero = 0
    let add =  (+)
    let compare = compare
  end
  
  include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vertex) (Label)

  let update_vertex_env env vname vtype =
    if (List.exists (fun (v,t) ->
      (String.compare v vname == 0) && (String.compare t vtype == 0)
    ) env) then env
    else env @ [(vname, vtype)]

  let get_type_of_vertex env vname =
    List.fold_left (fun types (v,t) ->
      if (String.compare v vname == 0) then types @ [t]
      else types
    ) [] env

  let get_vertex_of_type env typ =
    List.fold_left (fun vertices (v,t) ->
      if (String.compare t typ == 0) then vertices @ [v]
      else vertices
    ) [] env

  let make_edge lbl v1 v2 = (v1, lbl, v2)
  
  let get_label e =
    let (_, lbl, _) = e in
    lbl

  let is_field_label lbl =
    match lbl with
    | Label.DataField _ -> true
    | Label.ViewField _ -> true
    | _ -> false

  let is_equality_label lbl =
    match lbl with
    | Label.Equality -> true
    | _ -> false
  
  let is_data_field_label lbl =
    match lbl with
    | Label.DataField _ -> true
    | _ -> false

  let is_view_field_label lbl =
    match lbl with
    | Label.ViewField _ -> true
    | _ -> false

  let equal_label lbl1 lbl2 =
    match lbl1, lbl2 with
    | Label.Equality, Label.Equality -> true
    | Label.Equality, _ -> false
    | Label.DataField (x1, x2), Label.DataField (y1, y2) ->
        (String.compare x1 y1 = 0) && (String.compare x2 y2 = 0) 
    | Label.DataField _, _ -> false
    | Label.ViewField (x1, x2), Label.ViewField (y1, y2) ->
        (String.compare x1 y1 = 0) && (String.compare x2 y2 = 0) 
    | Label.ViewField _, _ -> false

  let string_of_label e =  match e with
    | Label.Equality -> "equality"
    | Label.DataField (h,f) -> "data:" ^ h^"."^f
    | Label.ViewField (h,f) -> "view:" ^ h^"."^f

  let string_of_graph g =
    let str = ref "view_graph:\n" in
    str := !str ^ "    vertices: ";
    let () = iter_vertex (fun v -> str := !str ^ v ^ ", ") g in
    str := !str ^ "\n    edges: ";
    let () = iter_edges_e (fun e ->
      let (s,l,d)  = e in 
      str := !str ^ "<" ^ (string_of_label l) ^ "> : "
             ^ s ^ " --> " ^ d ^ ";;   ";
    ) g in
    str := !str ^ "\n";
    !str
end

(*
 * a view is tail recursively defined if there is a case
 * that self points to the view itself
 *)
let is_tail_recursive_view_x (vd: view_decl) : bool =
  let vname = vd.view_name in
  let collect_view_pointed_by_self f = (
    let views = ref [] in
    let (hf,_,_,_,_,_) = F.split_components f in
    let f_hf hf = (match hf with
      | F.ViewNode vn ->
          let nname = P.name_of_spec_var vn.F.h_formula_view_node in
          let () = (
            if (String.compare nname self = 0) then
              views := vn.F.h_formula_view_name :: !views
            else ()
          ) in
          Some hf
      | _ -> None
    ) in
    let todo_unk = F.transform_h_formula f_hf hf in
    !views
  ) in
  let is_tail_recursive_branch (f: F.formula) = (
    let views = collect_view_pointed_by_self f in
    List.exists (fun vn -> String.compare vn vname = 0) views
  ) in
  let branches, _ = List.split vd.view_un_struc_formula in
  let tail_recursive = (List.exists is_tail_recursive_branch branches) in
  tail_recursive

let is_tail_recursive_view (vd: view_decl) : bool =
  let pr_view = !print_view_decl in
  let pr_out = string_of_bool in
  Debug.no_1 "is_tail_recursive_view" pr_view pr_out
      (fun _ -> is_tail_recursive_view_x vd) vd


let collect_subs_from_view_node_x (vn: F.h_formula_view) (vd: view_decl)
    : (P.spec_var * P.spec_var) list =
  let view_type = Named vd.view_data_name in
  let self_var = P.SpecVar (view_type, self, Unprimed) in
  let subs = [(self_var, vn.F.h_formula_view_node)] in
  let subs = List.fold_left2 (fun subs sv1 sv2 ->
    subs @ [(sv1, sv2)]
  ) subs vd.view_vars vn.F.h_formula_view_arguments in
  subs

let collect_subs_from_view_node (vn: F.h_formula_view) (vd: view_decl)
    : (P.spec_var * P.spec_var) list =
  let pr_subs = pr_list (fun (x,y) -> 
    "(" ^ (P.name_of_spec_var x) ^ "," ^ (P.name_of_spec_var y) ^ ")"
  ) in
  let pr_vn vn = !print_h_formula (F.ViewNode vn) in
  Debug.no_1 "collect_subs_from_view_node" pr_vn pr_subs
    (fun _ -> collect_subs_from_view_node_x vn vd) vn

let collect_subs_from_view_formula_x (f: F.formula) (vd: view_decl)
    : (P.spec_var * P.spec_var) list =
  let is_view_var v = (
    List.exists (fun sv -> P.eq_spec_var v sv) vd.view_vars
  ) in
  let is_self v = String.compare (P.name_of_spec_var v) self = 0 in
  let subs_list = ref [] in
  let f_e_f _ = None in
  let f_f _ = None in
  let f_h_f _ = None in
  let f_m mp = Some mp in
  let f_a _ = None in
  let f_pf pf = None in
  let f_b bf= (
    let pf, a = bf in
    match pf with
    | P.Eq (P.Var (sv1, _), P.Var(sv2, _), _) ->
        let new_subs = (
          (* in tail-recursive predicates, self must be substituted *)
          if (is_self sv1) then (
            if (vd.view_is_tail_recursive) then [(sv1,sv2)]
            else [(sv2,sv1)]
          )
          else if (is_self sv2) then (
            if (vd.view_is_tail_recursive) then [(sv2,sv1)]
            else [(sv1,sv2)]
          )
          (* otherwise only subs a view var by a non-view var *)
          else if (is_view_var sv1) && (not (is_view_var sv2)) then
            [(sv1,sv2)]
          else if (is_view_var sv2) && (not (is_view_var sv1)) then
            [(sv2,sv1)]
          (* othersise do randomly *)
          else [(sv1, sv2)]
        ) in
        let () = subs_list := !subs_list @ new_subs in
        (Some (pf,a))
    | _ -> None
  ) in
  let f_e _ = None in
  let todo_unk = F.transform_formula (f_e_f, f_f, f_h_f, (f_m, f_a, f_pf, f_b, f_e)) f in
  !subs_list

let collect_subs_from_view_formula (f: F.formula) (vd: view_decl)
    : (P.spec_var * P.spec_var) list =
  let pr_f = !print_formula in
  let pr_out = pr_list (fun (x,y) -> 
    "(" ^ (P.name_of_spec_var x) ^ "," ^ (P.name_of_spec_var y) ^ ")"
  ) in
  Debug.no_1 "collect_subs_from_view_formula" pr_f pr_out
      (fun _ -> collect_subs_from_view_formula_x f vd) f

(* split view formula to base cases and inductive cases *) 
let split_view_branches (vd: view_decl) : (F.formula list * F.formula list) =
  let vname = vd.view_name in
  let branches,_ = List.split vd.view_un_struc_formula in
  let base_fs, induct_fs = List.partition (fun f ->
    let views = F.get_views f in
    let induct_views = List.filter (fun vd ->
      eq_str vd.F.h_formula_view_name vname
    ) views in
    (List.length induct_views = 0)
  ) branches in
  (base_fs, induct_fs)

(* unfold the occurences of a view in a formula by its base case *)
let unfold_base_case_formula (f: F.formula) (vd: view_decl) (base_f: F.formula) =
  let vname = vd.view_name in
  let extra_pure = ref [] in
  let replace_hf hf = (match hf with
    | F.ViewNode vn ->
        if (String.compare vn.F.h_formula_view_name vname = 0) then
          let subs = collect_subs_from_view_node vn vd in
          let () = Debug.ninfo_hprint (add_str "base_f" !F.print_formula) base_f no_pos in
          let new_subs = match base_f with
            | F.Exists fe ->
                  let qvars = fe.F.formula_exists_qvars in
                  let vl = List.map (fun (_,sv) -> sv) subs in
                  let qvars = List.filter (fun sv -> not(List.mem sv vl)) qvars in
                  List.map (fun sv -> match sv with
                    | P.SpecVar (t,n,p) -> (P.SpecVar (t,fresh_any_name n,p),sv)) qvars
            | _ -> []
          in
          let subs = subs@new_subs in
          let () = Debug.ninfo_hprint (add_str "subs" (pr_list (pr_pair !P.print_sv !P.print_sv))) subs no_pos in
          let replacing_f = F.subst_one_by_one subs base_f in
          let () = Debug.ninfo_hprint (add_str "replacing_f" !F.print_formula) replacing_f no_pos in
          let (replacing_hf,extra_pf,_,_,_,_) = F.split_components replacing_f in
          let extra_qvars = F.get_exists replacing_f in
          let () = Debug.ninfo_hprint (add_str "extra_qvars" (pr_list !P.print_sv)) extra_qvars no_pos in
          extra_pure := !extra_pure @ [(extra_pf, extra_qvars)];
          Some replacing_hf                  (* replace the heap part *)
        else (Some hf)
    | _ -> None) in
  let f_ef _ = None in
  let f_f _ = None in
  let f_m mp = Some mp in
  let f_a a = Some a in
  let f_pf pf = Some pf in
  let f_b bf= Some bf in
  let f_e e = Some e in
  let () = Debug.ninfo_hprint (add_str "f" !F.print_formula) f no_pos in
  let new_f = F.transform_formula (f_ef, f_f, replace_hf, (f_m, f_a, f_pf, f_b, f_e)) f in
  let () = Debug.ninfo_hprint (add_str "new_f" !F.print_formula) new_f no_pos in
  let pos = F.pos_of_formula new_f in
  let new_f = List.fold_left (fun f (mf,qv) ->
    let nf = F.mkAnd_pure f mf pos in       (* add the pure part back *)
    F.push_exists qv nf
  ) new_f !extra_pure in
  let () = Debug.ninfo_hprint (add_str "new_f_final" !F.print_formula) new_f no_pos in
  new_f

let unfold_base_case_formula (f: F.formula) (vd: view_decl) (base_f: F.formula) =
  let pr = !F.print_formula in
  Debug.no_2 "unfold_base_case_formula" pr pr pr
      (fun _ _ -> unfold_base_case_formula f vd base_f) f base_f

(*
 * compute the possible pointers that reside in the memory allocated of view
 * they are the pointer from self to the last nodes in predicates
 *)
let compute_view_residents_x (vd: view_decl) : P.spec_var list =
  let vname = vd.view_name in
  let dname = vd.view_data_name in
  let self_var = P.SpecVar (Named dname, self, Unprimed) in
  let branches, _ = List.split vd.view_un_struc_formula in
  let base_fs, induct_fs = split_view_branches vd in
  if (List.length base_fs != 1) then []
  (* consider only the predicates have 1 base case*)
  else (
    let base_f = List.hd base_fs in
    (* collect residents which are obvious nodes *)
    let residents = ref [] in
    let collect_node hf = (match hf with
      | F.ViewNode {F.h_formula_view_node = sv; F.h_formula_view_imm = imm}
      | F.DataNode {F.h_formula_data_node = sv; F.h_formula_data_imm = imm} ->
          let () = if not (P.isLend imm) then residents := !residents @ [sv] in
          Some hf
      | _ -> None
    ) in
    let () = List.iter (fun f->
      let (hf,pf,_,_,_,_) = F.split_components f in
      let todo_unk = F.transform_h_formula collect_node hf in
      let eqs = MP.ptr_equations_without_null pf in
      residents := F.find_close !residents eqs;
    ) branches in
    residents := P.intersect_svl !residents (vd.view_cont_vars @ [self_var]);
    let () = List.iter (fun f ->
      (* unfold the inductive formulathen collect residents *)
      let new_f = unfold_base_case_formula f vd base_f in
      let (hf,pf,_,_,_,_) = F.split_components new_f in
      let todo_unk = F.transform_h_formula collect_node hf in
      let eqs = MP.ptr_equations_without_null pf in
      residents := F.find_close !residents eqs;
    ) induct_fs in
    residents := P.intersect_svl !residents (vd.view_cont_vars @ [self_var]);
    residents := P.remove_dups_svl !residents;
    !residents;
  )

let compute_view_residents (vd: view_decl) : P.spec_var list =
  let pr_vd = !print_view_decl in
  let pr_out = pr_list !P.print_sv in
  Debug.no_1 "compute_view_residents" pr_vd pr_out
      (fun _ -> compute_view_residents_x vd) vd

let collect_forward_backward_from_formula (f: F.formula) vdecl ddecl fwp fwf bwp bwf =
  let (hf,pf,_,_,_,_) = F.split_components f in
  let eqs = MP.ptr_equations_without_null pf in
  let dname = ddecl.data_name in
  let vname = vdecl.view_name in
  let self_var = P.SpecVar (Named dname, self, Unprimed) in
  let self_closure = F.find_close [self_var] eqs in
  let is_core_dnode node = eq_str (F.get_node_name 3 node) dname in
  let is_core_vnode node = eq_str (F.get_node_name 4 node) vname in
  let core_dnodes = List.filter is_core_dnode (F.get_dnodes f) in
  let core_vnodes = List.filter is_core_vnode (F.get_vnodes f) in
  let core_nodes = core_dnodes @ core_vnodes in
  let core_ptrs = List.map F.get_node_var core_nodes in
  let is_first_node node = P.mem_svl (F.get_node_var node) self_closure in
  let first_node = List.hd (List.filter is_first_node core_nodes) in 
  let last_nodes = (
    let remove_dups_hfl hfl = (
      let eq_hf hf1 hf2 = (
        let sv1 = F.get_node_var hf1 in
        let sv2 = F.get_node_var hf2 in
        P.eq_spec_var sv1 sv2
      ) in
      Gen.BList.remove_dups_eq eq_hf hfl 
    ) in
    let get_dnode_field_value dnode field ddecl = (
      List.hd (List.concat (List.map2 (fun ((_,fld),_) arg ->
        if (eq_str fld field) then [arg] else []
      ) ddecl.data_fields dnode.F.h_formula_data_arguments))
    ) in
    let get_vnode_ptr_value vnode ptr vdecl = (
      List.hd (List.concat (List.map2 (fun sv arg ->
        if (P.eq_spec_var sv ptr) then [arg] else []
      ) vdecl.view_vars vnode.F.h_formula_view_arguments))
    ) in
    (* propagate forward pointers, fields to find last node *)
    let rec propagate_forward (fw_ptrs: P.spec_var list) (fw_fields: ident list) (nodes: F.h_formula list) = (
      if (fw_fields = []) then []
      else match nodes with
        | [] -> []
        | ((F.ViewNode vnode) as node)::rest when (is_core_vnode node) ->
            let fw_ptrs = List.map (fun ptr ->
              get_vnode_ptr_value vnode ptr vdecl
            ) fw_ptrs in
            let fw_ptrs = F.find_close fw_ptrs eqs in
            let fw_ptrs = P.intersect_svl fw_ptrs core_ptrs in
            (* if it points to outsides, then it's last node *)
            if (fw_ptrs = []) then [node]
            else
              let is_fw_node n = P.mem_svl (F.get_node_var n) fw_ptrs in
              let fw_nodes = List.filter is_fw_node core_nodes in
              propagate_forward fw_ptrs fw_fields (remove_dups_hfl (rest@fw_nodes))
        | ((F.DataNode dnode) as node)::rest when (is_core_dnode node) ->
            let fw_ptrs = List.map (fun fld ->
              get_dnode_field_value dnode fld ddecl
            )fw_fields in
            let fw_ptrs = F.find_close fw_ptrs eqs in
            let fw_ptrs = P.intersect_svl fw_ptrs core_ptrs in
            (* if it points to outsides, then it's last node *)
            if (fw_ptrs = []) then [node]
            else
              let is_fw_node n = P.mem_svl (F.get_node_var n) fw_ptrs in
              let fw_nodes = List.filter is_fw_node core_nodes in
              propagate_forward fw_ptrs fw_fields ( remove_dups_hfl (rest@fw_nodes))
        | _ -> []
    ) in
    (* propagate backward pointers, fields to find last node *)
    let rec propagate_backward (bw_ptrs: P.spec_var list) (bw_fields: ident list) (nodes: F.h_formula list) = (
      match nodes with
      | [] -> []
      | ((F.ViewNode vnode) as node)::rest when (is_core_vnode node) ->
          let node_closure = F.find_close [(F.get_node_var node)] eqs in
          let bw_nodes = List.concat (List.map (fun ptr ->
            List.concat (List.map (fun n -> match n with
              | F.ViewNode vn ->
                  let ptr = get_vnode_ptr_value vn ptr vdecl in
                  if (P.mem_svl ptr node_closure) then [n]
                  else []
              | _ -> []
            ) core_dnodes)
          ) bw_ptrs) in
          if (bw_nodes = []) then [node]
          else propagate_backward bw_ptrs bw_fields (remove_dups_hfl (bw_nodes@rest))
      | ((F.DataNode dnode) as node)::rest when (is_core_dnode node) ->
          let node_closure = F.find_close [(F.get_node_var node)] eqs in
          let bw_nodes = List.concat (List.map (fun fld ->
            List.concat (List.map (fun n -> match n with
              | F.DataNode dn ->
                  let ptr = get_dnode_field_value dn fld ddecl in
                  if (P.mem_svl ptr node_closure) then [n]
                  else []
              | _ -> []
            ) core_dnodes)
          ) bw_fields) in
          if (bw_nodes = []) then [node]
          else propagate_backward bw_ptrs bw_fields (remove_dups_hfl (bw_nodes@rest))
      | _ -> []
    ) in
    let nodes1 = (propagate_forward fwp fwf [first_node]) in
    let nodes2 = (propagate_backward bwp bwf [first_node]) in
    let eq_node node1 node2 = P.eq_spec_var (F.get_node_var node1) (F.get_node_var node2) in
    Gen.BList.remove_dups_eq eq_node (nodes1 @ nodes2)
  ) in
  Debug.ninfo_hprint (add_str "first node" !print_h_formula) first_node no_pos;
  Debug.ninfo_hprint (add_str "last nodes" (pr_list !print_h_formula )) last_nodes no_pos;
  (* find forward, backward field using first and last nodes *)
  let collect_field node ptrs = (match node with
    | F.DataNode dn -> 
        let ptrs_closure = F.find_close ptrs eqs in
        List.concat (List.map2 (fun arg ((_,fld),_) ->
          if (P.mem_svl arg ptrs_closure) then [fld] else []
        ) dn.F.h_formula_data_arguments ddecl.data_fields)
    | _ -> []
  ) in
  let new_bwf = Gen.BList.remove_dups_eq eq_str (collect_field first_node bwp) in
  let new_fwf = List.concat (List.map (fun node -> collect_field node fwp) last_nodes) in
  let new_fwf = Gen.BList.remove_dups_eq eq_str new_fwf in
  (* find forward, backward pointer using first and last nodes *)
  let collect_pointer node fields = (match node with
    | F.DataNode dn ->
        List.concat (List.map2 (fun arg ((_,fld),_) ->
          if (List.exists (fun s -> eq_str s fld) fields) then (
            let closure = F.find_close [arg] eqs in
            Cpure.intersect_svl closure vdecl.view_cont_vars
          ) else []
        ) dn.F.h_formula_data_arguments ddecl.data_fields)
    | _ -> []
  ) in
  let new_bwp = P.remove_dups_svl (collect_pointer first_node bwf) in
  let new_fwp = List.concat (List.map (fun node -> collect_pointer node fwf) last_nodes) in
  let new_fwp = P.remove_dups_svl new_fwp in
  (new_fwp, new_fwf, new_bwp, new_bwf)
  (* Debug.ninfo_hprint (add_str "forward, backward 2 " (fun (x,y,z,t) ->  *)
  (*       "fwp: " ^ (pr_list !P.print_sv x) ^ "; "                       *)
  (*     ^ "fwf: " ^ (pr_list idf y) ^ "; "                                *)
  (*     ^ "bwp: " ^ (pr_list !P.print_sv z) ^ "; "                       *)
  (*     ^ "bwf: " ^ (pr_list idf t)                                       *)
  (*   ) ) (!fwp,!fwf,!bwp,!bwf) no_pos;                                   *)



let compute_view_forward_backward_info_x (vdecl: view_decl) (prog: prog_decl)
    : (  P.spec_var list * (data_decl * ident) list
       * P.spec_var list * (data_decl * ident) list ) =
  let pos = vdecl.view_pos in
  let vname = vdecl.view_name in
  let dname = vdecl.view_data_name in
  let self_sv = P.SpecVar (Named dname, self, Unprimed) in
  let () = if (eq_str dname "") then (
    report_warning pos "compute_view_fw_bw: data name in view is empty";
  ) in
  let ddecl = (
    try look_up_data_def_raw prog.prog_data_decls dname 
    with _ ->
        if !compete_mode then raise Not_found else
          report_error pos ("compute_view_fw_bw: data not found: " ^ dname)
  ) in
  let base_fs, induct_fs = split_view_branches vdecl in
  if (List.length base_fs != 1) then ([],[],[],[])
  (* consider only the predicates have 1 base case*)
  else (
    (* extract inductive information, nodes from head and tail part of formula *)
    let extract_head_body_node f = (
      let views = F.get_views f in
      let induct_views = List.filter (fun vd ->
        eq_str vd.F.h_formula_view_name vname
      ) views in
      if (List.length induct_views != 1) then None
      (* consider only view has 1 inductive view in its formula definition *)
      else (
        let head_node = (
          let is_self_node hf = (match hf with
            | F.DataNode dn when (eq_str (P.name_of_sv dn.F.h_formula_data_node) self) -> [hf]
            | F.ViewNode vn when (eq_str (P.name_of_sv vn.F.h_formula_view_node) self) -> [hf]
            | _ -> []
          ) in
          let self_nodes = F.get_one_kind_heap is_self_node f in
          if (self_nodes = []) then
            let () = report_warning pos "compute_fw_bw: self points to nowhere" in F.HEmp
          else (List.hd self_nodes)
        ) in
        let body_nodes = (
          let is_body_node hf = (match hf with
            | F.DataNode {F.h_formula_data_name = dn; F.h_formula_data_node = sv} ->
                if (eq_str dn dname) && not (eq_str (P.name_of_sv sv) self) then [hf]
                else []
            | F.ViewNode {F.h_formula_view_name = vn; F.h_formula_view_node = sv} ->
                if (eq_str vn vname) && not (eq_str (P.name_of_sv sv) self) then [hf]
                else []
            | _ -> []
          ) in
          F.get_one_kind_heap is_body_node f
        ) in
        Some (head_node, body_nodes)
      )
    ) in
    let get_residents hf vd = (match hf with
      | F.DataNode dn -> [dn.F.h_formula_data_node]
      | F.ViewNode vn -> (* prerequisite: view_decl of vn must be vd *)
          let residents = List.concat (List.map2 (fun v1 v2 ->
            if (List.exists (fun v -> P.eq_spec_var v2 v) vd.view_residents) then [v1]
            else []
          ) vn.F.h_formula_view_arguments vd.view_vars) in
          residents @ [vn.F.h_formula_view_node]
      | _ -> [] 
    ) in
    let head_body_info = List.map extract_head_body_node induct_fs in
    (* do fix point iteration to find forward, backward info *)
    let fwp, fwf, bwp, bwf = ref [], ref [], ref [], ref [] in
    let fwp_m, fwf_m, bwp_m, bwf_m = ref true, ref true, ref true, ref true in
    while (!fwp_m || !fwf_m || !bwp_m || !bwf_m) do
      fwp_m := false; fwf_m := false; bwp_m := false; bwf_m := false;
      List.iter2 (fun f head_body ->
        match head_body with
        | None -> ()
        | Some (head_node, body_nodes) -> (
            (* find forward, backward info from head and body node *)
            let head_ptrs = get_residents head_node vdecl in
            let body_ptrs = List.concat (List.map (fun n -> get_residents n vdecl) body_nodes) in
            Debug.ninfo_hprint (add_str "head_node" !F.print_h_formula) head_node no_pos;
            Debug.ninfo_hprint (add_str "body_nodes" (pr_list !F.print_h_formula)) body_nodes no_pos;
            Debug.ninfo_hprint (add_str "head_ptrs" (pr_list !P.print_sv)) head_ptrs no_pos;
            Debug.ninfo_hprint (add_str "body_ptrs" (pr_list !P.print_sv)) body_ptrs no_pos;
            let (hf,pf,_,_,_,_) = F.split_components f in
            let eqs = MP.ptr_equations_without_null pf in
            let () = match head_node with
              | F.ViewNode vn -> 
                  List.iter2 (fun sv1 sv2 ->
                    let sv1_closure = F.find_close [sv1] eqs in
                    let rch_ptrs = P.intersect_svl sv1_closure body_ptrs in
                    Debug.ninfo_hprint (add_str "fwp - sv1" !print_sv) sv1 no_pos;
                    Debug.ninfo_hprint (add_str "fwp - sv2" !print_sv) sv2 no_pos;
                    Debug.ninfo_hprint (add_str "fwp - rch_ptrs" (pr_list !print_sv)) rch_ptrs no_pos;
                    if (List.length rch_ptrs > 0) && (not (P.mem_svl sv2 !fwp)) then (
                      fwp := sv2::!fwp; fwp_m := true;
                    )
                  ) vn.F.h_formula_view_arguments vdecl.view_vars;
              | F.DataNode dn ->
                  List.iter2 (fun sv1 ((_,fld),_) ->
                    let sv1_closure = F.find_close [sv1] eqs in
                    let rch_ptrs = P.intersect_svl sv1_closure body_ptrs in
                    let rch_ptrs = P.intersect_svl rch_ptrs body_ptrs in
                    Debug.ninfo_hprint (add_str "fwf - sv1" (!print_sv)) sv1 no_pos;
                    Debug.ninfo_hprint (add_str "fwf - fld" idf) fld no_pos;
                    Debug.ninfo_hprint (add_str "fwf - rch_ptrs" (pr_list !print_sv)) rch_ptrs no_pos;
                    if (List.length rch_ptrs > 0) && (not (List.exists (fun s -> eq_str s fld) !fwf)) then (
                      fwf := fld::!fwf; fwf_m := true;
                    )
                  ) dn.F.h_formula_data_arguments ddecl.data_fields;
              | _ -> ()
            in
            let new_bwps, new_bwfs = ref [], ref [] in 
            let () = List.iter (fun body_node ->
              match body_node with
              | F.ViewNode vn ->
                  let p_bwps = List.concat (List.map2 (fun sv1 sv2 ->
                    let sv1_closure = F.find_close [sv1] eqs in
                    let rch_ptrs = P.intersect_svl sv1_closure head_ptrs in
                    if (List.length rch_ptrs > 0) then [sv2] else []
                  ) vn.F.h_formula_view_arguments vdecl.view_vars) in
                  Debug.ninfo_hprint (add_str "p_bwps" (pr_list !P.print_sv)) p_bwps no_pos;
                  if (!new_bwps = []) then new_bwps := p_bwps
                  else if (p_bwps != []) then
                    new_bwps := Cpure.intersect_svl !new_bwps p_bwps;
                  Debug.ninfo_hprint (add_str "new_bwps" (pr_list !P.print_sv)) !new_bwps no_pos;
              | F.DataNode dn ->
                  let p_bwfs = List.concat (List.map2 (fun sv1 ((_,fld),_) ->
                    let sv1_closure = F.find_close [sv1] eqs in
                    let rch_ptrs = P.intersect_svl sv1_closure head_ptrs in
                    Debug.ninfo_hprint (add_str "bwf - sv1" (!print_sv)) sv1 no_pos;
                    Debug.ninfo_hprint (add_str "bwf - fld" idf) fld no_pos;
                    Debug.ninfo_hprint (add_str "bwf - rch_ptrs" (pr_list !print_sv)) rch_ptrs no_pos;
                    if (List.length rch_ptrs > 0) then [fld] else []
                  ) dn.F.h_formula_data_arguments ddecl.data_fields) in
                  Debug.ninfo_hprint (add_str "p_bwfs" (pr_list idf)) p_bwfs no_pos;
                  if (!new_bwfs = []) then new_bwfs := p_bwfs
                  else if (p_bwfs != []) then
                    new_bwfs := Gen.BList.intersect_eq eq_str !new_bwfs p_bwfs;
                  Debug.ninfo_hprint (add_str "new_bwfs" (pr_list idf)) !new_bwfs no_pos;
              | _ -> ()
            ) body_nodes in
            let new_bwps = P.remove_dups_svl (!new_bwps @ !bwp) in
            if (List.length new_bwps != List.length !bwp) then (
              bwp := new_bwps; bwp_m := true;
            );
            let new_bwfs = Gen.BList.remove_dups_eq eq_str (!new_bwfs @ !bwf) in
            if (List.length new_bwfs != List.length !bwf) then (
              bwf := new_bwfs; bwf_m := true;
            );

            Debug.ninfo_hprint (add_str "forward, backward 1 " (fun (x,y,z,t) -> 
                  "fwp: " ^ (pr_list !P.print_sv x) ^ "; "
                ^ "fwf: " ^ (pr_list idf y) ^ "; " 
                ^ "bwp: " ^ (pr_list !P.print_sv z) ^ "; "
                ^ "bwf: " ^ (pr_list idf t)
              ) ) (!fwp,!fwf,!bwp,!bwf) no_pos;
            (* unfold the inductive formulathen collect residents *)
            let base_f = List.hd base_fs in
            Debug.ninfo_hprint (add_str "f" (!F.print_formula)) f no_pos;
            let f = unfold_base_case_formula f vdecl base_f in
            Debug.ninfo_hprint (add_str "unfold_f" (!F.print_formula)) f no_pos;
            let new_fwp, new_fwf, new_bwp, new_bwf = 
              collect_forward_backward_from_formula f vdecl ddecl !fwp !fwf !bwp !bwf in
            if (List.length new_fwp > List.length !fwp) then (fwp := new_fwp; fwp_m := true);
            if (List.length new_fwf > List.length !fwf) then (fwf := new_fwf; fwf_m := true);
            if (List.length new_bwp > List.length !bwp) then (bwp := new_bwp; bwp_m := true);
            if (List.length new_bwf > List.length !bwf) then (bwf := new_bwf; bwf_m := true);

            Debug.ninfo_hprint (add_str "forward, backward 2 " (fun (x,y,z,t) -> 
                  "fwp: " ^ (pr_list !P.print_sv x) ^ "; "
                ^ "fwf: " ^ (pr_list idf y) ^ "; " 
                ^ "bwp: " ^ (pr_list !P.print_sv z) ^ "; "
                ^ "bwf: " ^ (pr_list idf t)
              ) ) (!fwp,!fwf,!bwp,!bwf) no_pos;
          )
      ) induct_fs head_body_info;
      Debug.ninfo_hprint (add_str "loop flag: " (fun (x,y,z,t) ->
            "fwp_m: " ^ (string_of_bool x) ^ "; "
          ^ "fwf_m: " ^ (string_of_bool y) ^ "; " 
          ^ "bwp_m: " ^ (string_of_bool z) ^ "; "
          ^ "bwf_m: " ^ (string_of_bool t)
        )) (!fwp_m,!fwf_m,!bwp_m,!bwf_m) no_pos;
    done;
    let fwf = List.map (fun fld -> (ddecl,fld)) !fwf in
    let bwf = List.map (fun fld -> (ddecl,fld)) !bwf in
    (!fwp, fwf, !bwp, bwf)
  )

let compute_view_forward_backward_info (vdecl: view_decl) (prog: prog_decl)
    : (  P.spec_var list * (data_decl * ident) list
       * P.spec_var list * (data_decl * ident) list ) =
  let pr_vd = !print_view_decl in
  let pr_svl = pr_list !P.print_sv in
  let pr_idl = pr_list idf in
  let pr_out (fwp,fwf,bwp,bwf) = (
    let fwp_s = pr_svl fwp in
    let fwf_s = pr_list (fun(d,f) -> d.data_name^"."^f) fwf in
    let bwp_s = pr_svl bwp in
    let bwf_s = pr_list (fun(d,f) -> d.data_name^"."^f) bwf in
    ("(fwp = " ^ fwp_s ^ "  ;; fwf = " ^ fwf_s 
     ^ "  ;; bwp = " ^ bwp_s ^ "  ;; bwf = " ^ bwf_s ^ ")") 
  ) in
  Debug.no_1 "compute_view_forward_backward_info" pr_vd pr_out
       (fun _ -> compute_view_forward_backward_info_x vdecl prog) vdecl

let categorize_view (prog: prog_decl) : prog_decl =
  (* requires: view_decl must be preprocessed to fill the view_cont_vars field *)
  let vdecls = prog.prog_view_decls in
  let new_vdecls = List.map (fun vd ->
    (* view residents *)
    let residents = compute_view_residents vd in
    let vd = { vd with view_residents = residents } in
    (* forward & backward pointers, fields *)
    let (fwp, fwf, bwp, bwf) = compute_view_forward_backward_info vd prog in
    let vd = {vd with view_forward_ptrs = fwp;
                      view_backward_ptrs = bwp;
                      view_forward_fields = fwf;
                      view_backward_fields = bwf;} in
    (* touching & segmented is computed only when the forward and backward pointers is available *)
    let touching = is_touching_view vd in
    let segmented = is_segmented_view vd in
    let vd = { vd with view_is_touching = touching;
                       view_is_segmented = segmented; } in
    (* is tail-recursively defined view? *)
    let tail_recursive = is_tail_recursive_view vd in
    let vd = { vd with view_is_tail_recursive = tail_recursive } in
    vd
  ) vdecls in
  { prog with prog_view_decls = new_vdecls }
 

(*
   A h_formula is resourceless if
   - prim_pred
   - ho_args = [] 
*)
let is_resourceless_h_formula_x prog (h: F.h_formula) =
  let rec helper h =
    match h with
      | F.HEmp -> true
      | F.HFalse -> true
      | F.ViewNode v ->
            let vdef = look_up_view_def v.h_formula_view_pos prog.prog_view_decls v.h_formula_view_name in
            (vdef.view_is_prim && v.h_formula_view_ho_arguments=[])
      | F.DataNode _
      | F.ThreadNode _ -> false
      | F.Star ({h_formula_star_h1 = h1;
          h_formula_star_h2 = h2;})
      | F.StarMinus ({ h_formula_starminus_h1 = h1;
          h_formula_starminus_h2 = h2;})
      | F.Conj ({ h_formula_conj_h1 = h1;
          h_formula_conj_h2 = h2;})
      | F.ConjStar ({h_formula_conjstar_h1 = h1;
          h_formula_conjstar_h2 = h2;} )
      | F.ConjConj ({h_formula_conjconj_h1 = h1;
          h_formula_conjconj_h2 = h2;} )
      | F.Phase ({ h_formula_phase_rd = h1;
          h_formula_phase_rw = h2;}) ->
            ((helper h1) && (helper h2))
      | _ -> false
  in helper h

let is_resourceless_h_formula prog (h: F.h_formula) =
  Debug.no_1 "is_resourceless_h_formula"
      !print_h_formula string_of_bool
      (fun _ -> is_resourceless_h_formula_x prog h) h

(*************************************************)      
(* Construct a data dependency graph from an exp *)
(*************************************************)
let is_prim_proc prog id = 
  try
    let proc = Hashtbl.find prog.new_proc_decls id in
    not proc.proc_is_main
  with _ -> false
  
let print_data_dependency_graph ddg = 
  IG.fold_edges (fun s d a -> "\n" ^ s ^ " -> " ^ d ^ a)  ddg ""

let eq_str s1 s2 = String.compare s1 s2 == 0
      
let remove_dups_id = Gen.BList.remove_dups_eq eq_str

(* src depends on exp *)
let data_dependency_graph_of_exp prog src exp =
  let rec helper ddg src exp = 
    match exp with
    | Label e -> helper ddg src e.exp_label_exp
    | Assign e ->
      (* let ddg = IG.add_edge ddg src e.exp_assign_lhs in *)
      helper ddg e.exp_assign_lhs e.exp_assign_rhs
    | Bind e ->
      let bvar = snd e.exp_bind_bound_var in
      let ddg = IG.add_edge ddg src bvar in
      let ddg = List.fold_left (fun g (_, i) ->
        IG.add_edge g bvar i) ddg e.exp_bind_fields in
      helper ddg bvar e.exp_bind_body
    | Block e -> helper ddg src e.exp_block_body
    | Cond e ->
      let ddg = IG.add_edge ddg src e.exp_cond_condition in
      let ddg = helper ddg src e.exp_cond_then_arm in
      helper ddg src e.exp_cond_else_arm
    | Cast e -> helper ddg src e.exp_cast_body 
    | Catch e -> helper ddg src e.exp_catch_body 
    | ICall e -> 
      let ddg, dst =
        let mn = e.exp_icall_method_name in
        if is_prim_proc prog mn then ddg, src
        else
          let ddg = IG.add_edge ddg src mn in  
          ddg, mn
      in
      List.fold_left (fun g i -> 
        IG.add_edge g dst i) ddg e.exp_icall_arguments
    | SCall e -> 
      let ddg, dst =
        let mn = e.exp_scall_method_name in
        if is_prim_proc prog mn then ddg, src
        else
          let ddg = IG.add_edge ddg src mn in  
          ddg, mn
      in
      List.fold_left (fun g i -> 
        IG.add_edge g dst i) ddg e.exp_scall_arguments
    | Seq e ->
      let ddg = helper ddg src e.exp_seq_exp1 in
      helper ddg src e.exp_seq_exp2
    | Var e -> IG.add_edge ddg src e.exp_var_name
    | While e -> 
      let ddg = IG.add_edge ddg src e.exp_while_condition in
      helper ddg src e.exp_while_body
    | Try e ->
      let ddg = helper ddg src e.exp_try_body in
      helper ddg src e.exp_catch_clause
    | _ -> ddg
  in
  let ddg = IG.empty in
  helper ddg src exp
  
let data_dependency_graph_of_exp prog src exp =
  Debug.no_1 "data_dependency_graph_of_exp" idf print_data_dependency_graph
    (fun _ -> data_dependency_graph_of_exp prog src exp) src
    
let rec_calls_of_exp exp = 
  let f exp = 
    match exp with
    | ICall e -> if e.exp_icall_is_rec then Some ([e.exp_icall_method_name]) else None
    | SCall e -> if e.exp_scall_is_rec then Some ([e.exp_scall_method_name]) else None
    | _ -> None
  in fold_exp exp f List.concat []
  
let has_ref_params prog mn =
  try
    let proc = find_proc prog mn in
    proc.proc_by_name_params != []
  with _ -> false
  
let has_named_params prog mn =
  try
    let proc = find_proc prog mn in
    List.exists (fun (t, _) -> is_node_typ t) proc.proc_args
  with _ -> false
  
let is_rec_proc prog mn = 
  try
    let proc = find_proc prog mn in
    proc.proc_is_recursive
  with _ -> false

let data_dependency_graph_of_proc prog proc = 
  match proc.proc_body with
  | None -> None
  | Some e -> Some (data_dependency_graph_of_exp prog proc.proc_name e)
  
let rec collect_dependence_procs_aux prog init ws ddg src =
  try
    let succ = IG.succ ddg src in
    match succ with
    | [] -> [], ws
    | _ -> 
      let depend_mns = List.filter is_mingle_name succ in
      let depend_mns = 
        if init then 
          if not (is_rec_proc prog src) then []
          else List.filter (fun mn -> 
            not (eq_str mn src) && 
            ((has_ref_params prog mn) || (has_named_params prog mn))) depend_mns  
        else depend_mns
      in
      let working_succ = Gen.BList.difference_eq eq_str succ ws in 
      List.fold_left (fun (acc, ws) d ->
        let dd, ws = collect_dependence_procs_aux prog false (ws @ [d]) ddg d in
        (acc @ dd), ws) (depend_mns, ws) working_succ
  with _ -> [], ws
  
let collect_dependence_procs prog g pn = 
  fst (collect_dependence_procs_aux prog true [pn] g pn)

let dependence_procs_of_proc prog proc =
  match proc.proc_body with
  | None -> []
  | Some e ->
    let pn = proc.proc_name in
    let ddg = data_dependency_graph_of_exp prog pn e in
    let rec_pns = rec_calls_of_exp e in
    let pns = remove_dups_id (pn::rec_pns) in
    let r = List.fold_left (fun acc pn -> 
      acc @ (collect_dependence_procs prog ddg pn)) [] pns in
    remove_dups_id r
    
let add_inf_post_proc proc = 
  { proc with 
      proc_static_specs = Cformula.add_inf_post_struc proc.proc_static_specs; 
      proc_dynamic_specs = Cformula.add_inf_post_struc proc.proc_dynamic_specs; }
      
let add_post_for_tnt_prog prog =
  let inf_term_procs = Hashtbl.fold (fun _ proc acc ->
    let spec = proc.proc_static_specs in
    if not (Cformula.is_inf_term_only_struc spec) then acc
    else acc @ [proc]) prog.new_proc_decls [] in (* @term only, no @term_wo_post *)
  let inf_post_procs = List.fold_left (fun acc proc ->
    let dprocs = dependence_procs_of_proc prog proc in
    let () = 
      if is_empty dprocs then ()
      else print_endline_quiet ("\n !!! @post is added into " ^ 
        (pr_list idf dprocs) ^ " for " ^ proc.proc_name) 
    in
    acc @ dprocs) [] inf_term_procs in
  let inf_post_procs = Gen.BList.remove_dups_eq
    (fun s1 s2 -> String.compare s1 s2 == 0) inf_post_procs in
  { prog with
      new_proc_decls = proc_decls_map (fun proc ->
        if List.mem proc.proc_name inf_post_procs then
          add_inf_post_proc proc
        else proc) prog.new_proc_decls; }
  
