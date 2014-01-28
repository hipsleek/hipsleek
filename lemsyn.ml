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
module CFU = Cfutil
module CP = Cpure
module MCP = Mcpure
module H  = Hashtbl


let gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc es lhs_node lhs_b0 rhs_node rhs_b0 =
  let get_eqset puref =
    let (subs,_) = CP.get_all_vv_eqs puref in
    let eqset = CP.EMapSV.build_eset subs in
    eqset
  in
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
    (*TEMP*)
    (* let lf1 = CF.subst lss (CF.formula_of_heap lhs_node no_pos) in *)
    (* let rf1 = CF.subst rss (CF.formula_of_heap rhs_node no_pos) in *)
    (*NORM lhs-rhs*)
    let ( _,mix_lf,_,_,_) = CF.split_components (CF.Base lhs_b0) in
    let l_emap0 = get_eqset (MCP.pure_of_mix mix_lf) in
    let (_,mix_rf0,_,_,_) = CF.split_components (CF.Base rhs_b0) in
    let r_emap0 = get_eqset (MCP.pure_of_mix mix_rf0) in
    let r_eqsetmap0 = CP.EMapSV.build_eset es.CF.es_rhs_eqset in
    let lhs_b1, rhs_b1, _ = CFU.smart_subst_new lhs_b0 rhs_b0 []
           l_emap0 r_emap0 r_eqsetmap0 [] ([lr;rr])
    in
    (*LHS: find reachable heap + pure*)
    let lf1a = CF.subst_b lss lhs_b1 in
    let rf1a = CF.subst_b lss rhs_b1 in
    let lf1 = CFU.obtain_reachable_formula prog (CF.Base lf1a) [lselfr] in
    let rf1 = CFU.obtain_reachable_formula prog (CF.Base rf1a) [rselfr] in
    (* let lf1 = CF.subst lss  *)
    (*RHS: find reachable heap + pure*)
    let lf2 = formula_rev_fnc lf1 in
    let rf2 = formula_rev_fnc rf1 in
    (*gen lemma*)
    let lemma_name = "cyc" in
    let l_coer = I.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE I.Left [] lf2 rf2 in
    (*add lemma*)
    let iprog = I.get_iprog () in
    let res = manage_unsafe_lemmas_fnc [l_coer] iprog prog in
    let _ = print_endline (" gen lemma:" ^ (Cprinter.string_of_formula lf1) ^ " -> "
    ^ (Cprinter.string_of_formula rf1)) in
    ()
  with _ -> ()

let gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc es lhs_node lhsb rhs_node rhsb =
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 = Cprinter.string_of_h_formula in
  Debug.no_4 "LEMSYN.gen_lemma" pr2 pr1 pr2 pr1 pr_none
      (fun _ _ _ _ -> gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc es lhs_node lhsb rhs_node rhsb)
      lhs_node lhsb rhs_node rhsb
