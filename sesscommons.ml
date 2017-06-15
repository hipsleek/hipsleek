#include "xdebug.cppo"
open VarGen
open Globals

(* ======= base formula for session type ====== *)
(* ============================================ *)
module type Message_type = sig
  type formula
  type pure_formula
  type h_formula
  type h_formula_heap
  type ho_param_formula
  type struc_formula
  (* type node *)
  type param
  type var
  type flow
  type arg = var (* node *) * ident * (ho_param_formula list) *
             (param list) * VarGen.loc

  val is_emp : formula -> bool
  val print  : (formula -> string) ref
  val print_struc_formula  : (struc_formula -> string) ref
  val print_h_formula  : (h_formula -> string) ref
  val print_ho_param_formula  : (ho_param_formula -> string) ref
  val print_var  : (var -> string)
  val print_param: (param -> string) ref
  val print_pure_formula: (pure_formula -> string) ref
      
  val mk_node: arg -> session_kind -> node_kind -> h_formula
  val mk_formula_heap_only: ?flow:flow -> h_formula -> VarGen.loc -> formula
  val mk_rflow_formula: ?sess_kind:(session_kind option) -> ?kind:ho_flow_kind -> formula -> ho_param_formula
  val mk_rflow_formula_from_heap:  h_formula -> ?sess_kind:(session_kind option) -> ?kind:ho_flow_kind -> VarGen.loc -> ho_param_formula
  val mk_formula: pure_formula -> arg -> session_kind -> node_kind -> formula
  val mk_struc_formula: formula -> VarGen.loc -> struc_formula
  val mk_star: h_formula -> h_formula -> VarGen.loc -> h_formula
  val mk_star_formula: formula -> formula -> VarGen.loc -> formula
  val mk_exists: (ident * primed) list -> h_formula -> VarGen.loc -> formula
  val mk_or: formula -> formula -> VarGen.loc -> formula
  val mk_empty: unit -> h_formula
  val mk_true: unit -> pure_formula
  val mk_hvar: ident -> var list -> h_formula
  val mk_seq_wrapper: ?sess_kind:session_kind option -> h_formula -> VarGen.loc -> session_kind -> h_formula
  val mk_exp_rel: ident -> (var * VarGen.loc) list -> VarGen.loc -> pure_formula 

  val choose_ptr: ?ptr:string -> unit -> var (* node *)
  val id_to_param:  ident ->  VarGen.loc -> param
  val const_to_param:  int ->  VarGen.loc -> param
  val fconst_to_param:  float ->  VarGen.loc -> param
  val var_to_param: var ->  VarGen.loc -> param
  val param_to_var: param -> var

  val transform_h_formula: (h_formula -> h_formula option)-> h_formula -> h_formula
  val transform_formula: (h_formula -> h_formula option)-> formula -> formula
  val transform_struc_formula:  (h_formula -> h_formula option)-> struc_formula -> struc_formula
  val transform_struc_formula_formula:  (formula -> formula option)-> struc_formula -> struc_formula
  val map_one_rflow_formula: (formula -> formula) -> ho_param_formula -> ho_param_formula
  val map_rflow_formula_list: (formula -> formula) -> ho_param_formula list -> ho_param_formula list
  val map_rflow_formula_list_res_h: (formula -> formula) -> h_formula_heap -> h_formula
  val update_temp_heap_name: view_session_info -> h_formula -> h_formula option
  val set_heap_node_var: var -> h_formula_heap -> h_formula
  val set_ann_list: h_formula -> sess_ann list -> h_formula
  val subst_param:   (var * var) list -> param -> param
  val subst_var:     (var * var) list -> var -> var
  val subst_formula: (var * var) list -> formula -> formula
  val fresh_var: var -> var
  val eq_var: var -> var -> bool
  val mk_var: ident -> var
  val append_tail: h_formula -> h_formula -> h_formula
  val join_conjunctions: pure_formula list -> pure_formula

  val is_base_formula: formula -> bool
  val is_exists_formula: formula -> bool
  val get_h_formula: formula -> h_formula
  val get_pure_formula: formula -> pure_formula
  val get_h_formula_safe: formula -> h_formula
  val get_h_formula_from_ho_param_formula: ho_param_formula -> h_formula
  val get_formula_from_ho_param_formula: ho_param_formula -> formula
  val get_ho_param: h_formula_heap -> ho_param_formula list
  val get_node: h_formula -> arg
  val get_or_formulae: formula -> formula list
  val get_star_formulae: h_formula -> h_formula list
  val get_star_pos: h_formula -> VarGen.loc
  val get_param_id: param -> ident
  val get_node_id: var(* node *) -> ident
  val get_formula_from_struc_formula: struc_formula -> formula
  val get_hvar: h_formula -> ident * var list
  val get_session_info: h_formula -> view_session_info option
  val get_view_session_info:  h_formula_heap -> view_session_info option
  val get_node_kind: h_formula -> node_kind
  val get_session_kind: h_formula -> session_kind option
  val get_heap_node: h_formula -> h_formula option
  val get_node_only: h_formula -> h_formula_heap
  val get_node_opt:  h_formula -> h_formula_heap option
  val get_heap_node_var: h_formula_heap -> var
  val get_ann_list: h_formula -> sess_ann list option
  val get_exists_vars: formula -> (ident * primed) list
  val get_formula_pos: formula -> VarGen.loc
      
  val get_h_formula_safe: formula -> h_formula option
  val get_h_formula_from_struc_formula_safe: struc_formula -> h_formula option

end;;


