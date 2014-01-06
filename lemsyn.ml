open Globals
open Wrapper
open Gen
open Others
open Label_only

module I  = Iast
module C  = Cast
module IF = Iformula
module IP = Ipure
module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module H  = Hashtbl

let gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc lhs_node lhsb rhs_node rhsb =
  let lview,rview = match lhs_node,lhs_node with
    | CF.ViewNode vl, CF.ViewNode vr -> vl,vr
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  try
    (*left*)
    let lr = lview.CF.h_formula_view_node in
    let lselfr = CP.SpecVar (CP.type_of_spec_var lr, self, CP.primed_of_spec_var lr) in
    let lss = [(lr, lselfr)] in
    (*right*)
    let rr = rview.CF.h_formula_view_node in
    let rselfr = CP.SpecVar (CP.type_of_spec_var rr, self, CP.primed_of_spec_var rr) in
    let rss = [(rr, rselfr)] in
    (*LHS: find reachable heap + pure*)
    (*RHS: find reachable heap + pure*)
    (*TEMP*)
    let lf1 = CF.subst lss (CF.formula_of_heap lhs_node no_pos) in
    let rf1 = CF.subst rss (CF.formula_of_heap rhs_node no_pos) in
    let lf2 = formula_rev_fnc lf1 in
    let rf2 = formula_rev_fnc rf1 in
    (*gen lemma*)
    let lemma_name = "cyc" in
    let l_coer = I.mk_lemma (fresh_any_name lemma_name) I.Left [] lf2 rf2 in
    (*add lemma*)
    let iprog = I.get_iprog () in
    let res = manage_unsafe_lemmas_fnc [l_coer] iprog prog in
    ()
  with _ -> ()
