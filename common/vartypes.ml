class var_types =
  object
    val mutable vars_implicit = false
    val mutable vars_explicit = false
    val mutable vars_exists = false
    val mutable vars_heap_only = false
    val mutable vars_heap_ptr_only = false
    val mutable vars_view_only = false
    val mutable vars_with_rel = false
    method is_implicit : bool = vars_implicit
    method is_explicit : bool = vars_explicit
    method is_exists : bool = vars_exists
    method is_heap_only : bool = vars_heap_only
    method is_heap_ptr_only : bool = vars_heap_ptr_only
    method is_view_only : bool = vars_view_only
    method with_rel = vars_with_rel
    method set_implicit : unit = vars_implicit <- true
    method set_explicit : unit = vars_explicit <- true
    method set_exists : unit = vars_exists <- true
    method set_heap_only : unit = vars_heap_only <- true
    method set_heap_ptr_only : unit = vars_heap_ptr_only <- true
    method set_view_only : unit = (vars_heap_only <- true; vars_view_only <- true)
    method set_with_rel = vars_with_rel <- true
  end

let var_with_implicit =
  let v = new var_types in
  let () = v # set_implicit in
  v

(* excludes HRel arguments *)
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

let var_with_rel =
  let v = new var_types in
  let () = v # set_with_rel in
  v
