#include "xdebug.cppo"
module CP = Cpure

let pr_sv = CP.string_of_spec_var
let pr_svl = CP.string_of_spec_var_list
let pr_pair_id = fun (x,y) -> x ^ "-->" ^  y
let eq_pair_id = fun (x1,y1) (x2,y2) -> (x1=x2) && (y1=y2)

let stk_vars = new Gen.stack_pr "stk-vars" (pr_sv) CP.eq_spec_var_nop

let set_stk_vars vs = 
  let () = stk_vars # reset in
  stk_vars # push_list vs

let stk_renamed_vars = new Gen.stack_pr "stk-renamed-vars" pr_pair_id eq_pair_id

let stk_evars = new Gen.stack_pr "stk-evars" (pr_sv) CP.eq_spec_var_nop

let stk_var_ident = new Gen.stack_pr "stk-var-ident" (Gen.pr_id) (=)

let in_vars = new VarGen.store [] pr_svl

class var_types =
  object
    val mutable vars_implicit = false
    val mutable vars_explicit = false
    val mutable vars_exists = false
    val mutable vars_heap_only = false
    val mutable vars_heap_ptr_only = false
    val mutable vars_view_only = false
    method is_implicit : bool = vars_implicit
    method is_explicit : bool = vars_explicit
    method is_exists : bool = vars_exists
    method is_heap_only : bool = vars_heap_only 
    method is_heap_ptr_only : bool = vars_heap_ptr_only 
    method is_view_only : bool = vars_view_only
    method set_implicit : unit = vars_implicit <- true
    method set_explicit : unit = vars_explicit <- true
    method set_exists : unit = vars_exists <- true
    method set_heap_only : unit = vars_heap_only <- true
    method set_heap_ptr_only : unit = vars_heap_ptr_only <- true
    method set_view_only : unit = (vars_heap_only <- true; vars_view_only <- true)
  end;;

let var_with_implicit =
  let v = new var_types in
  let () = v # set_implicit in
  v

(* excludes HRel and HVar arguments *)
let var_with_heap_only =
  let v = new var_types in
  let () = v # set_heap_only in
  v

let var_with_heap_ptr_only =
  let v = new var_types in
  let () = v # set_heap_ptr_only in
  v

let var_with_view_only =
  let v = new var_types in
  let () = v # set_view_only in
  v

let var_with_implicit_explicit =
  let v = new var_types in
  let () = v # set_implicit in
  let () = v # set_explicit in
  v

let var_with_exists = 
  let v = new var_types in
  let () = v # set_exists in
  v

let var_with_none =
  let v = new var_types in
  v

let sleek_cnt_timeout_limit = new Gen.counter 5
