#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure

module CF = Cformula
module CP = Cpure

(*********************************************************************
 * Data structures
 *********************************************************************)

(* goal *)
type goal = {
  gl_prog : Cast.prog_decl;
  gl_pre_cond : CF.formula;
  gl_post_cond : CF.formula;
  gl_framed_heaps : CF.h_formula list;
  gl_vars: CP.spec_var list;
}

(* Synthesis rules
 * TODO: add more synthesis rules here *)
type rule =
  | RlFuncCall of rule_func_call
  | RlAssign of rule_assign
  | RlBindWrite of rule_bind
  (* | RlBindRead *)

and rule_func_call = {
  rfc_func_name : string;
  rfc_params : CP.exp list;
}

(* TODO: should we rename variables?? *)
and rule_bind = {
  rb_var: CP.spec_var;
  rb_field: typed_ident;
  rb_rhs: CP.spec_var;
}

and rule_assign = {
  ra_lhs : CP.spec_var;
  ra_rhs : CP.spec_var;
}

(* AssignPure *)
(* {x = a} {x = b} --> {x = b} if b \in varSet*)

(* AssignPureSymb *)
(* {x = a & b = t} {x = b} --> x = t when varSet = {x, t} *)

(* Atomic derivation *)
type derivation = {
  drv_kind : derivation_kind;
  drv_rule : rule;
  drv_goal : goal;
}

and derivation_kind =
  | DrvStatus of bool
  | DrvSubgoals of goal list

(* Synthesis tree *)
type synthesis_tree =
  | StSearch of synthesis_tree_search
  | StDerive of synthesis_tree_derive

and synthesis_tree_search = {
  sts_goal : goal;
  sts_sub_trees : synthesis_tree list;
  sts_status : synthesis_tree_status;
}

and synthesis_tree_derive = {
  std_goal : goal;
  std_rule : rule;
  std_sub_trees : synthesis_tree list;
  std_status : synthesis_tree_status;
}

and synthesis_tree_core = {
  stc_goal : goal;
  stc_rule : rule;
  stc_sub_trees : synthesis_tree_core list;
}

and synthesis_tree_status =
  | StValid of synthesis_tree_core
  | StUnkn of string


(*********************************************************************
 * Constructors
 *********************************************************************)

let mk_goal cprog pre post vars =
  { gl_prog = cprog;
    gl_pre_cond = pre;
    gl_post_cond = post;
    gl_framed_heaps = [];
    gl_vars = vars;  }

let mk_derivation_sub_goals goal rule subgoals =
  { drv_kind = DrvSubgoals subgoals;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_success goal rule =
  { drv_kind = DrvStatus true;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_fail goal rule =
  { drv_kind = DrvStatus false;
    drv_rule = rule;
    drv_goal = goal; }

let mk_synthesis_tree_search goal sub_trees status : synthesis_tree =
  StSearch {
    sts_goal = goal;
    sts_sub_trees = sub_trees;
    sts_status = status; }

let mk_synthesis_tree_derive goal rule sub_trees status : synthesis_tree =
  StDerive {
    std_goal = goal;
    std_rule = rule;
    std_sub_trees = sub_trees;
    std_status = status; }

let mk_synthesis_tree_core goal rule sub_trees : synthesis_tree_core =
  { stc_goal = goal;
    stc_rule = rule;
    stc_sub_trees = sub_trees; }

let mk_synthesis_tree_success goal rule : synthesis_tree =
  let stcore = mk_synthesis_tree_core goal rule [] in
  StDerive {
    std_goal = goal;
    std_rule = rule;
    std_sub_trees = [];
    std_status = StValid stcore; }

let mk_synthesis_tree_fail goal sub_trees msg : synthesis_tree =
  StSearch {
    sts_goal = goal;
    sts_sub_trees = sub_trees;
    sts_status = StUnkn msg; }

(*********************************************************************
 * Queries
 *********************************************************************)

let get_synthesis_tree_status stree : synthesis_tree_status =
  match stree with
  | StDerive std -> std.std_status
  | StSearch sts -> sts.sts_status

let is_synthesis_tree_success stree : bool =
  let status = get_synthesis_tree_status stree in
  match status with
  | StValid _ -> true
  | StUnkn _ -> false


(*********************************************************************
 * Printing
 *********************************************************************)

let pr_exp_opt exp = match exp with
  | None -> "None"
  | Some e -> Cprinter.string_of_exp e

let pr_goal goal =
  let pr_formula = Cprinter.string_of_formula in
  let vars = goal.gl_vars in
  let pr_svs = Cprinter.string_of_spec_var_list in
  "goal (" ^ "vars:" ^ (pr_svs vars) ^ "\n" ^
  "pre: " ^ (pr_formula goal.gl_pre_cond) ^ "\n" ^
  "post: " ^ (pr_formula goal.gl_post_cond) ^ ")"

let pr_rule_assign rule =
  let lhs = rule.ra_lhs in
  let rhs = rule.ra_rhs in
  (Cprinter.string_of_spec_var lhs) ^ " = " ^ (Cprinter.string_of_spec_var rhs)

let pr_rule_bind rule =
  let exp = rule.rb_var in
  (Cprinter.string_of_spec_var exp) ^ ", " ^ (snd rule.rb_field) ^ ", "
  ^ (Cprinter.string_of_spec_var rule.rb_rhs)

let pr_rule rule = match rule with
  | RlFuncCall fc -> "RlFuncCal"
  | RlAssign rule -> "RlAssign " ^ "(" ^ (pr_rule_assign rule) ^ ")"
  | RlBindWrite rule -> "RlBindWrite " ^ "(" ^ (pr_rule_bind rule) ^ ")"

let rec pr_st st = match st with
  | StSearch st_search -> "StSearch [" ^ (pr_st_search st_search) ^ "]"
  | StDerive st_derive -> "StDerive [" ^ (pr_st_derive st_derive) ^ "]"

and pr_st_search st =
  let goal = st.sts_goal in
  let sub_trees = st.sts_sub_trees in
  let st_str = (pr_list pr_st) sub_trees in
  (pr_goal goal) ^ st_str

and pr_st_derive st =
  (pr_goal st.std_goal) ^ "\n" ^
  (pr_rule st.std_rule) ^ "\n" ^
  ((pr_list pr_st) st.std_sub_trees)
  (* ^ "\n" ^  (pr_st_status st.std_status) *)

and pr_st_status st_status = match st_status with
  | StUnkn str -> "StUnkn " ^ str
  | StValid st_core -> pr_st_core st_core

and pr_st_core st =
  let goal = st.stc_goal in
  let sub_trees = st.stc_sub_trees in
  (pr_goal goal) ^ "=n" ^
  (pr_rule st.stc_rule) ^
  ((pr_list pr_st_core) sub_trees)

(*****************************************************
  * Atomic functions
********************************************************)

(* Get the value of a field *)
let get_field var access_field data_decls =
  let name = var.CF.h_formula_data_name in
  try
    let data = List.find (fun x -> String.compare x.Cast.data_name name == 0) data_decls in
    let fields = var.CF.h_formula_data_arguments in
    let data_fields = List.map fst data.Cast.data_fields in
    let pairs = List.combine data_fields fields in
    let result = List.filter (fun (x,y) -> x = access_field) pairs in
    if result = [] then None
    else Some (snd (List.hd result))
  with Not_found -> None

(* Update a data node with a new value to the field *)
let set_field var access_field (new_val:CP.spec_var) data_decls =
  let name = var.CF.h_formula_data_name in
  try
    let data = List.find (fun x -> String.compare x.Cast.data_name name == 0) data_decls in
    let fields = var.CF.h_formula_data_arguments in
    let data_fields = List.map fst data.Cast.data_fields in
    let pairs = List.combine data_fields fields in
    let update_field (field, old_val) =
      if field = access_field then new_val
      else old_val in
    let new_fields = List.map update_field pairs in
    {var with CF.h_formula_data_arguments = new_fields}
  with Not_found -> report_error no_pos "Synthesis.ml could not find the data decls"
