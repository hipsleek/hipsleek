(*
  Created 21-Feb-2006

  AST for the core language
*)

open Globals
open Gen.Basic

module F = Cformula
module P = Cpure
module MP = Mcpure
module Err = Error

type typed_ident = (typ * ident)



and prog_decl = { 
    mutable prog_data_decls : data_decl list;
	mutable prog_view_decls : view_decl list;
	mutable prog_rel_decls : rel_decl list; (* An Hoa : relation definitions *)
	prog_proc_decls : proc_decl list;
	mutable prog_left_coercions : coercion_decl list;
	mutable prog_right_coercions : coercion_decl list;
    prog_barrier_decls : barrier_decl list}
	
and prog_or_branches = (prog_decl * (MP.mix_formula * ((string*P.formula)list)*(P.spec_var list)) option )
	
and data_decl = { 
    data_name : ident;
    data_fields : typed_ident list;
    data_parent_name : ident;
    data_invs : F.formula list;
    data_methods : proc_decl list; }

and barrier_decl = {
	barrier_thc : int;
	barrier_name : ident;
	barrier_shared_vars : P.spec_var list;
	barrier_tr_list : (int*int* F.struc_formula list) list ;
	barrier_def: F.struc_formula ;
	}
	
and ba_prun_cond = Gen.Baga(P.PtrSV).baga * formula_label
    
and mater_property = {
  mater_var : P.spec_var;
  mater_full_flag : bool;
  mater_target_view : ident list; (*the view to which it materializes*)
  }
  
    
and view_decl = { 
    view_name : ident; 
    view_vars : P.spec_var list;
    view_case_vars : P.spec_var list; (* predicate parameters that are bound to guard of case, but excluding self; subset of view_vars*)
    view_labels : branch_label list;
    view_modes : mode list;
    mutable view_partially_bound_vars : bool list;
    mutable view_materialized_vars : mater_property list; (* view vars that can point to objects *)
    view_data_name : ident;
    view_formula : F.struc_formula;
    view_user_inv : (MP.mix_formula * (branch_label * P.formula) list); (* XPURE 0 -> revert to P.formula*)
    mutable view_x_formula : (MP.mix_formula * (branch_label * P.formula) list); (*XPURE 1 -> revert to P.formula*)
    mutable view_baga : Gen.Baga(P.PtrSV).baga;
    mutable view_addr_vars : P.spec_var list;
    (* if view has only a single eqn, then place complex subpart into complex_inv *)  
    view_complex_inv : (MP.mix_formula * (branch_label * P.formula) list) option; (*COMPLEX INV for --eps option*)
    view_un_struc_formula : (Cformula.formula * formula_label) list ; (*used by the unfold, pre transformed in order to avoid multiple transformations*)
    view_base_case : (P.formula *(MP.mix_formula*((branch_label*P.formula)list))) option; (* guard for base case, base case (common pure, pure branches)*)
    view_prune_branches: formula_label list; (* all the branches of a view *)
    view_is_rec : bool;
    view_prune_conditions: (P.b_formula * (formula_label list)) list;
    view_prune_conditions_baga: ba_prun_cond list;
    view_prune_invariants : (formula_label list * (Gen.Baga(P.PtrSV).baga * P.b_formula list )) list ;
    view_raw_base_case: Cformula.formula option;}

(* An Hoa : relation *)					
and rel_decl = { 
    rel_name : ident; 
    rel_vars : P.spec_var list;
    rel_formula : P.formula;
    (* rel_case_vars : P.spec_var list; (* predicate parameters that are bound to guard of case, but excluding self; subset of rel_vars*)
       rel_labels : branch_label list;
       rel_modes : mode list;
       mutable rel_partially_bound_vars : bool list;
       mutable rel_materialized_vars : P.spec_var list; (* rel vars that can point to objects *)
       rel_formula : F.struc_formula;
       rel_user_inv : (MP.mix_formula * (branch_label * P.formula) list); (* XPURE 0 -> revert to P.formula*)
       mutable rel_x_formula : (MP.mix_formula * (branch_label * P.formula) list); (*XPURE 1 -> revert to P.formula*)
       mutable rel_addr_vars : P.spec_var list;
       rel_un_struc_formula : (Cformula.formula * formula_label) list ; (*used by the unfold, pre transformed in order to avoid multiple transformations*)
       rel_base_case : (P.formula *(MP.mix_formula*((branch_label*P.formula)list))) option; (* guard for base case, base case (common pure, pure branches)*)
       rel_prune_branches: formula_label list;
       rel_prune_conditions: (P.b_formula * (formula_label list)) list;
       rel_prune_invariants : (formula_label list * P.b_formula list) list ;
       rel_raw_base_case: Cformula.formula option; *)}
    
and proc_decl = { 
    proc_name : ident;
    proc_args : typed_ident list;
				  proc_return : typ;
    proc_static_specs : Cformula.struc_formula;
    proc_static_specs_with_pre : Cformula.struc_formula;
    proc_dynamic_specs : Cformula.struc_formula;
    (*proc_dynamic_specs_with_pre : Cformula.struc_formula;*)
    proc_by_name_params : P.spec_var list;
    proc_body : exp option;
    proc_file : string;
    proc_loc : loc; }

(*TODO: should we change lemma need struc formulas?
  would this help with lemma folding later? *)

(* TODO : coercion type ->, <-, <-> just added *)
and coercion_decl = { 
    coercion_type : coercion_type;
    coercion_name : ident;
    coercion_head : F.formula;
    coercion_body : F.formula;
    coercion_univ_vars : P.spec_var list; (* list of universally quantified variables. *)
    (* coercion_proof : exp; *)
    (* coercion_head_exist : F.formula;   *)
    (* same as head except for annotation to self node? *)
    coercion_head_view : ident; 
    (* the name of the predicate where this coercion can be applied *)
    coercion_body_view : ident;  (* used for cycles checking *)
    coercion_mater_vars : mater_property list;
    coercion_simple_lhs :bool; (* signify if LHS is simple or complex *)
}

and coercion_type = Iast.coercion_type
    (* | Left *)
    (* | Equiv *)
    (* | Right *)
    
and sharp_flow = 
  | Sharp_ct of F.flow_formula
  | Sharp_v of ident
        
and sharp_val = 
  | Sharp_no_val 
  | Sharp_finally of ident
  | Sharp_prog_var of typed_ident

(* An Hoa : v[i] where v is an identifier and i is an expression *)
(* and exp_arrayat = { exp_arrayat_type : P.typ; (* Type of the array element *)
   exp_arrayat_array_name : ident; (* Name of the array *)
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
    exp_bind_imm : bool;
	exp_bind_perm : ident option;
    exp_bind_path_id : control_path_id;
    exp_bind_pos : loc }

and exp_block = { exp_block_type : typ;
    exp_block_body : exp;
    exp_block_local_vars : typed_ident list;
    exp_block_pos : loc }

and exp_cast = { 
    exp_cast_target_type : typ;
    exp_cast_body : exp;
    exp_cast_pos : loc }

and exp_cond = { exp_cond_type : typ;
    exp_cond_condition : ident;
    exp_cond_then_arm : exp;
    exp_cond_else_arm : exp;
    exp_cond_path_id : control_path_id;
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
and exp_scall = { exp_scall_type : typ;
   exp_scall_method_name : ident;
    exp_scall_arguments : ident list;
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
    exp_catch_flow_type : nflow ;
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
    exp_emparray_pos : loc }

and exp_var_decl = { exp_var_decl_type : typ;
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
  | Barrier_cmd of exp_var
  | BConst of exp_bconst
  | Bind of exp_bind
  | Block of exp_block
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

let print_mix_formula = ref (fun (c:MP.mix_formula) -> "cpure printer has not been initialized")
let print_b_formula = ref (fun (c:P.b_formula) -> "cpure printer has not been initialized")
let print_h_formula = ref (fun (c:F.h_formula) -> "cpure printer has not been initialized")
let print_exp = ref (fun (c:P.exp) -> "cpure printer has not been initialized")
let print_formula = ref (fun (c:P.formula) -> "cpure printer has not been initialized")
let print_struc_formula = ref (fun (c:F.struc_formula) -> "cpure printer has not been initialized")
let print_svl = ref (fun (c:P.spec_var list) -> "cpure printer has not been initialized")
let print_sv = ref (fun (c:P.spec_var) -> "cpure printer has not been initialized")
let print_mater_prop = ref (fun (c:mater_property) -> "cast printer has not been initialized")

let is_simple_formula x = true
(* transform each proc by a map function *)
let map_proc (prog:prog_decl)
  (f_p : proc_decl -> proc_decl) : prog_decl =
  { prog with
      prog_proc_decls = List.map (f_p) prog.prog_proc_decls;
  }

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
  Gen.Debug.no_2 "merge_mater_props" pr pr pr merge_mater_props_x x y
  
let mater_props_to_sv_list l =  List.map (fun c-> c.mater_var) l
  
let subst_mater_list fr t l = 
  let lsv = List.combine fr t in
  List.map (fun c-> 
      {c with mater_var = P.subs_one lsv c.mater_var
              (* ; mater_var = P.subs_one lsv c.mater_var *)
      }) l

let subst_mater_list_nth i fr t l = 
  let pr_svl = !print_svl in
  Gen.Debug.no_2_num i "subst_mater_list" pr_svl pr_svl pr_no (fun _ _ -> subst_mater_list fr t l) fr t 

let subst_coercion fr t (c:coercion_decl) = 
      {c with coercion_head = F.subst_avoid_capture fr t c.coercion_head
              ; coercion_body = F.subst_avoid_capture fr t c.coercion_body
      }
 
(* process each proc into some data which are then combined,
   e.g. verify each method and collect the failure points
*)
let fold_proc (prog:prog_decl)
  (f_p : proc_decl -> 'b) (f_comb: 'b -> 'b -> 'b) (zero:'b) : 'b =
  List.fold_left (fun x p -> f_comb (f_p p) x) 
		zero prog.prog_proc_decls

(* iterate each proc to check for some property *)
let iter_proc (prog:prog_decl) (f_p : proc_decl -> unit) : unit =
  fold_proc prog (f_p) (fun _ _ -> ()) ()

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
	          | New _
	          | Null _
						| EmptyArray _ (* An Hoa *)
	          | Print _
	          | SCall _
	          | This _
	          | Time _
            | Barrier_cmd _
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
let mkEAssume pos = [Cformula.EAssume  ([],(Cformula.mkTrue (Cformula.mkTrueFlow ()) pos),(stub_branch_point_id ""))]
	
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
  | Barrier_cmd _ -> None
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
  | New ({exp_new_class_name = c; 
		  exp_new_arguments = _; 
		  exp_new_pos = _}) -> Some (Named c) (*---- ok? *)
  | Null _ -> Some (Named "")
	| EmptyArray b -> Some (Array (b.exp_emparray_type, None)) (* An Hoa *)
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

let unmingle_name (m : ident) = 
  try
	let i = String.index m '$' in
	  String.sub m 0 i
  with
	| Not_found -> m

let rec look_up_view_def_raw (defs : view_decl list) (name : ident) = match defs with
  | d :: rest -> if d.view_name = name then d else look_up_view_def_raw rest name
  | [] -> raise Not_found

(* An Hoa *)
let rec look_up_rel_def_raw (defs : rel_decl list) (name : ident) = match defs with
  | d :: rest -> if d.rel_name = name then d else look_up_rel_def_raw rest name
  | [] -> raise Not_found

let rec look_up_view_def (pos : loc) (defs : view_decl list) (name : ident) = match defs with
  | d :: rest -> 
	    if d.view_name = name then d 
	    else look_up_view_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
	Error.error_text = name ^ " is not a view definition"}

let look_up_view_def_num i (pos : loc) (defs : view_decl list) (name : ident) = 
  Gen.Debug.no_1_num i "look_up_view_def" pr_id pr_no 
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
  Gen.Debug.no_1 "collect_rhs_view" pr1 pr2 (fun _ -> collect_rhs_view n f) n

let is_self_rec_rhs (lhs:ident) (rhs:F.struc_formula) : bool =
  let  (_,ns) = collect_rhs_view lhs rhs in
  List.mem lhs ns

let is_self_rec_rhs (lhs:ident) (rhs:F.struc_formula) : bool =
  Gen.Debug.no_1 "is_self_rec_rhs" (fun x -> x) (string_of_bool) (fun _ -> is_self_rec_rhs lhs rhs) lhs

(* pre: name exists as a view in prog *)
let is_rec_view_def prog (name : ident) : bool = 
   let vdef = look_up_view_def_num 2 no_pos prog.prog_view_decls name in
   (* let _ = collect_rhs_view vdef in *)
   vdef.view_is_rec

let look_up_view_baga prog (c : ident) (root:P.PtrSV.t) (args:P.BagaSV.baga) : P.BagaSV.baga = 
  let vdef = look_up_view_def no_pos prog.prog_view_decls c in
  let ba = vdef.view_baga in
  (*let _ = print_endline (" look_up_view_baga: baga= " ^ (!print_svl ba)) in*)
  let from_svs = P.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
  let to_svs = root :: args in
  Gen.BList.list_substs (fun b a-> P.eq_spec_var (fst a) (fst b)) (List.combine from_svs to_svs) ba
  (*P.subst_var_list_avoid_capture from_svs to_svs ba*)

let look_up_view_baga  prog (c : ident) (root:P.PtrSV.t) (args:P.BagaSV.baga) : P.BagaSV.baga = 
    let pr_ptrSV = pr_pair !print_sv (fun (_,c)-> Tree_shares.Ts.string_of_tree_share c) in
      let print_r = Gen.pr_list pr_ptrSV in
      Gen.Debug.no_2 "look_up_view_baga" pr_ptrSV print_r print_r
      (fun r a ->  look_up_view_baga prog c r a) root args

let rec look_up_data_def pos (ddefs : data_decl list) (name : string) = match ddefs with
  | d :: rest -> 
	  if d.data_name = name then d 
	  else look_up_data_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = name ^ " is not a data/class declaration"}

let rec look_up_parent_name pos ddefs name =
  let ddef = look_up_data_def pos ddefs name in
	ddef.data_parent_name

let rec look_up_proc_def_raw (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
      if p.proc_name = name then
		p
      else
		look_up_proc_def_raw rest name
  | [] -> raise Not_found
	  
let rec look_up_proc_def pos (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
      if p.proc_name = name then
		p
      else
		look_up_proc_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = "procedure " ^ name ^ " is not found"}

let rec look_up_bar_def pos (bars : barrier_decl list) (name : string) = match bars with
  | p :: rest ->
      if p.barrier_name = name then
		p
      else
		look_up_bar_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = "barrier " ^ name ^ " is not found"}
							  
let rec look_up_proc_def_no_mingling pos (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
	  if unmingle_name p.proc_name = name then p
	  else look_up_proc_def_no_mingling pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = "procedure " ^ name ^ " is not found"}

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


let lookup_view_invs_with_subs rem_br v_def zip  = 
  try 
    let v=snd(snd (List.find (fun (c1,_)-> Gen.BList.list_setequal_eq (=) c1 rem_br) v_def.view_prune_invariants)) in
    List.map (P.b_apply_subs zip) v
  with | Not_found -> []

let lookup_view_baga_with_subs rem_br v_def from_v to_v = 
  try 
    let v=fst(snd (List.find (fun (c1,_)-> Gen.BList.list_setequal_eq (=) c1 rem_br) v_def.view_prune_invariants)) in
    Gen.BList.list_substs (fun b a-> P.eq_spec_var (fst a) (fst b)) (List.combine from_v to_v) v
    (*P.subst_var_list_avoid_capture from_v to_v v*)
  with | Not_found -> []

let look_up_coercion_def_raw coers (c : ident) : coercion_decl list = 
  List.filter (fun p ->  p.coercion_head_view = c ) coers
  (* match coers with *)
  (* | p :: rest -> begin *)
  (*     let tmp = look_up_coercion_def_raw rest c in *)
  (*   	if p.coercion_head_view = c then p :: tmp *)
  (*   	else tmp *)
  (*   end *)
  (* | [] -> [] *)


let  look_up_coercion_with_target coers (c : ident) (t : ident) : coercion_decl list = 
  List.filter (fun p ->  p.coercion_head_view = c && p.coercion_body_view = t  ) coers


let rec callees_of_proc (prog : prog_decl) (name : ident) : ident list =
  let pdef = look_up_proc_def_no_mingling no_pos prog.prog_proc_decls name in
  let callees = 
	match pdef.proc_body with
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
			 exp_arrayat_array_name = _;
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
  | Barrier_cmd _ -> []
  | VarDecl _ -> []
  | Unit _ -> []
  | While ({exp_while_condition = _;
			exp_while_body = e;
			exp_while_spec = _;
			exp_while_pos = _ }) -> callees_of_exp e (*-----???*)
  | Try b -> Gen.BList.remove_dups_eq (=) ((callees_of_exp b.exp_try_body)@(callees_of_exp b.exp_catch_clause))
  | Unfold _ -> []

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
  let _ = List.map add_edge prog.prog_data_decls in
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
	  let sub_ext_var = List.hd (List.tl subnode.F.h_formula_data_arguments) in
		(* call gen_exts with sup_ext_var to link the 
		   head node with extensions *)
	  let heap_args = List.tl (List.tl subnode.F.h_formula_data_arguments) in
	  let n = List.length cdef1.data_fields in
	  let to_sup, rest_fields = Gen.split_at heap_args n in
	  let ext_name = gen_ext_name subnode.F.h_formula_data_name cdef1.data_name in
	  (*--- 09.05.2000 *)
	  let fn1 = fresh_var_name ext_name pos.start_pos.Lexing.pos_lnum in
		(*let _ = (print_string ("\n[cast.ml, line 556]: fresh name = " ^ fn1 ^ "!!!!!!!!!!!\n\n")) in*)
		(*09.05.2000 ---*)
	  let sup_ext_var = P.SpecVar (Named ext_name, fn1, Unprimed) in
	  let sup_h = F.DataNode ({F.h_formula_data_node = subnode.F.h_formula_data_node;
							   F.h_formula_data_name = cdef1.data_name;
							   F.h_formula_data_perm = subnode.F.h_formula_data_perm;
							   F.h_formula_data_imm = subnode.F.h_formula_data_imm;
							   F.h_formula_data_arguments = sub_tvar :: sup_ext_var :: to_sup;
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
										  F.h_formula_data_perm = subnode.F.h_formula_data_perm;
										 F.h_formula_data_imm = subnode.F.h_formula_data_imm;
										 F.h_formula_data_arguments = link_p :: to_ext;
										 F.h_formula_data_label = subnode.F.h_formula_data_label;
                     F.h_formula_data_remaining_branches = None;
                     F.h_formula_data_pruning_conditions = [];
										 F.h_formula_data_pos = pos}) in
				  ext_h
			  else
				let ext_link_name = gen_ext_name cdef2.data_name ((List.hd rest).data_name) in
				(*--- 09.05.2000 *)
	  		let fn2 = fresh_var_name ext_name pos.start_pos.Lexing.pos_lnum in
				(*let _ = (print_string ("\n[cast.ml, line 579]: fresh name = " ^ fn2 ^ "!!!!!!!!!!!\n\n")) in*)
				(*09.05.2000 ---*)
				let ext_link_p = P.SpecVar (Named ext_link_name, fn2, Unprimed) in
				let ext_h = F.DataNode ({F.h_formula_data_node = top_p;
										 F.h_formula_data_name = ext_name;
										 F.h_formula_data_perm = subnode.F.h_formula_data_perm;
										 F.h_formula_data_imm = subnode.F.h_formula_data_imm;
										 F.h_formula_data_arguments = ext_link_p :: to_ext;
										 F.h_formula_data_label = subnode.F.h_formula_data_label;
                     F.h_formula_data_remaining_branches = None;
                     F.h_formula_data_pruning_conditions = [];
										 F.h_formula_data_pos = pos}) in
				let rest_exts = gen_exts ext_link_p link_p rest_fields (cdef2 :: rest) in
				let ext = F.mkStarH_nn ext_h rest_exts pos in
				  ext
		  end
		| _ -> F.HTrue in
	  let exts = gen_exts sup_ext_var sub_ext_var rest_fields cdefs0 in
	  let res = F.mkStarH_nn sup_h exts pos in
		res
	end
  | _ -> F.HTrue


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
(* 				  let _ = PathCH.shortest_path class_hierarchy v1 v2 in *)
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

let sub_type (t1 : typ) (t2 : typ) = 
  Globals.sub_type t1 t2

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
        
  | BConst _
	      (*| ArrayAt _ (* An Hoa TODO NO IDEA *)*)
	      (*| ArrayMod _ (* An Hoa TODO NO IDEA *)*)
  | Assign _
  | ICall _
  | IConst _
  | While _ 
  | This _
  | Var _
  | Barrier_cmd _
  | Null _
  | EmptyArray _ (* An Hoa : NO IDEA *)
  | New _
  | Sharp _
  | SCall _
  | Label _
      -> true
  
  
let rec pos_of_exp (e:exp) :loc = match e with
	(*| ArrayAt b -> b.exp_arrayat_pos (* An Hoa *)*)
	(*| ArrayMod b -> b.exp_arraymod_pos (* An Hoa *)*)
  | CheckRef b -> b.exp_check_ref_pos
  | Barrier_cmd b -> b.exp_var_pos
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
  | Java b  -> b.exp_java_pos
  | Assert b -> b.exp_assert_pos
  | New b -> b.exp_new_pos
  | Sharp b -> b.exp_sharp_pos
  | SCall b -> b.exp_scall_pos
  | While b -> b.exp_while_pos
  | Try b -> b.exp_try_pos
  | Label b -> pos_of_exp b.exp_label_exp
	  
let get_catch_of_exp e = match e with
	| Catch e -> e
	| _  -> Error.report_error {Err.error_loc = pos_of_exp e; Err.error_text = "malformed expression, expecting catch clause"}
  
  
let rec check_proper_return cret_type exc_list f = 
	let overlap_flow_type fl res_t = match res_t with 
		| Named ot -> F.overlapping fl (Gen.ExcNumbering.get_hash_of_exc ot)
		| _ -> false in
	let rec check_proper_return_f f0 = match f0 with
	| F.Base b->
		let res_t,b_rez = F.get_result_type f0 in
		let fl_int = b.F.formula_base_flow.F.formula_flow_interval in
		if b_rez then
			if (F.equal_flow_interval !n_flow_int fl_int) then 
				if not (sub_type res_t cret_type) then 					
					Err.report_error{Err.error_loc = b.F.formula_base_pos;Err.error_text ="result type does not correspond with the return type";}
				else ()
			else 
				if not (List.exists (fun c-> F.subsume_flow c fl_int) exc_list) then
				Err.report_error{Err.error_loc = b.F.formula_base_pos;Err.error_text ="not all specified flow types are covered by the throw list";}
				else if not(overlap_flow_type fl_int res_t) then
				Err.report_error{Err.error_loc = b.F.formula_base_pos;Err.error_text ="result type does not correspond (overlap) with the flow type";}
				else ()			
		else 
			(*let _ =print_string ("\n ("^(string_of_int (fst fl_int))^" "^(string_of_int (snd fl_int))^"="^(Gen.ExcNumbering.get_closest fl_int)^
									(string_of_bool (Cpure.is_void_type res_t))^"\n") in*)
			if not(((F.equal_flow_interval !n_flow_int fl_int)&&(Cpure.is_void_type res_t))|| (not (F.equal_flow_interval !n_flow_int fl_int))) then 
				Error.report_error {Err.error_loc = b.F.formula_base_pos; Err.error_text ="no return in a non void function or for a non normal flow"}
			else ()
	| F.Exists b->
		let res_t,b_rez = F.get_result_type f0 in
		let fl_int = b.F.formula_exists_flow.F.formula_flow_interval in
		if b_rez then
			if (F.equal_flow_interval !n_flow_int fl_int) then 
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
			(* let _ =print_string ("\n ("^(string_of_int (fst fl_int))^" "^(string_of_int (snd fl_int))^"="^(Gen.ExcNumbering.get_closest fl_int)^
									(string_of_bool (Cpure.is_void_type res_t))^"\n") in*)
			 if not(((F.equal_flow_interval !n_flow_int fl_int)&&(Cpure.is_void_type res_t))|| (not (F.equal_flow_interval !n_flow_int fl_int))) then 
				Error.report_error {Err.error_loc = b.F.formula_exists_pos;Err.error_text ="no return in a non void function or for a non normal flow"}
			else ()			
	| F.Or b-> check_proper_return_f b.F.formula_or_f1 ; check_proper_return_f b.F.formula_or_f2 in
	let helper f0 = match f0 with 
		| F.EBase b-> check_proper_return cret_type exc_list  b.F.formula_ext_continuation
		| F.ECase b-> List.iter (fun (_,c)-> check_proper_return cret_type exc_list c) b.F.formula_case_branches
		| F.EAssume (_,b,_)-> if (F.isAnyConstFalse b)||(F.isAnyConstTrue b) then () else check_proper_return_f b
		| F.EVariance b -> ()
		in
	List.iter helper f

  
let formula_of_unstruc_view_f vd = F.formula_of_disjuncts (fst (List.split vd.view_un_struc_formula))


let vdef_fold_use_bc prog ln2  = match ln2 with
  | F.ViewNode vn -> 
    (try 
      let vd = look_up_view_def_raw prog.prog_view_decls vn.F.h_formula_view_name in
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
  Gen.Debug.no_1 "vdef_fold_use_bc" pr1 pr2 (fun _ -> vdef_fold_use_bc prog ln2) ln2


let get_xpure_one vdef rm_br  =
  match rm_br with
    | Some l -> let n=(List.length l) in  
      if n<(List.length vdef.view_prune_branches) then None
      else (match vdef.view_complex_inv with 
        | None -> None 
        | Some f -> Some f)  (* unspecialised with a complex_inv *)
    | None -> Some vdef.view_x_formula 

let get_xpure_one vdef rm_br  =
  let pr (mf,_) = !print_mix_formula mf in
  Gen.Debug.no_1 "get_xpure_one" pr_no (pr_option pr) (fun _ -> get_xpure_one vdef rm_br) rm_br

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
  Gen.Debug.no_1 "any_xpure_1" pr string_of_bool (fun _ -> any_xpure_1 prog f) f 

  
  
let mkFull_bind_exp e = 
  let rec ft _ e = match e with
   | Bind b-> 
		let bb = transform_exp b.exp_bind_body 0 ft (fun _ _ -> 0) (fun _ -> 0) 0 in
	  Some (Bind{b with exp_bind_perm=None; exp_bind_body= fst bb},0)
   | _ -> None in
  fst (transform_exp e 0 ft (fun _ _-> 0) (fun _ -> 0) 0)  