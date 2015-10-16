#include "xdebug.cppo"

open Globals
open VarGen
open Gen.Basic
open Wrapper
open Others
open Exc.GTable
open Printf
open Gen.Basic
open Gen.BList
open Mcpure_D
open Mcpure
open Label_only
open Typeinfer

module CA = Cast
module CF = Cformula
module CP = Cpure

let dump_self () =
  let id = (fresh_trailer()) in
  CP.SpecVar (null_type, "Anon_"^id, Unprimed)

let func_call_no = ref (0: int)

let subst_view_by_hole holes0 f0=
  (* let rec look_up_hole holes vn= *)
  (*   match holes with *)
  (*     | [] -> raise Not_found *)
  (*     | (hvf,hole_id)::rest -> begin *)
  (*           match hvf with *)
  (*             | CF.ViewNode vn1 -> *)
  (*                   if CP.eq_spec_var vn.CF.h_formula_view_node vn1.CF.h_formula_view_node then (CF.Hole hole_id) *)
  (*                   else look_up_hole rest vn *)
  (*             | _ -> look_up_hole rest vn *)
  (*       end *)
  (* in *)
  let rec subst_hf hf= match hf with
    | CF.Star f ->
          let nhf1,holes1 = subst_hf f.CF.h_formula_star_h1 in
          let nhf2,holes2 = subst_hf f.CF.h_formula_star_h2 in
          CF.Star {f with CF.h_formula_star_h1 = nhf1;
              CF.h_formula_star_h2 = nhf2;},holes1@holes2
    | CF.StarMinus f ->
          let nhf1,holes1 = subst_hf f.CF.h_formula_starminus_h1 in
          let nhf2,holes2 = subst_hf f.CF.h_formula_starminus_h2 in
          CF.StarMinus {f with CF.h_formula_starminus_h1 = nhf1;
              CF.h_formula_starminus_h2 = nhf2;},holes1@holes2
    | CF.Conj f->
          let nhf1,holes1 = subst_hf f.CF.h_formula_conj_h1 in
          let nhf2,holes2 = subst_hf f.CF.h_formula_conj_h2 in
          CF.Conj {f with CF.h_formula_conj_h1 = nhf1;
              CF.h_formula_conj_h2 = nhf2;},holes1@holes2
    | CF.ConjStar f->
          let nhf1,holes1 = subst_hf f.CF.h_formula_conjstar_h1 in
          let nhf2,holes2 = subst_hf f.CF.h_formula_conjstar_h2 in
          CF.ConjStar {f with CF.h_formula_conjstar_h1 = nhf1;
              CF.h_formula_conjstar_h2 = nhf2;},holes1@holes2
    | CF.ConjConj f ->
          let nhf1,holes1 = subst_hf f.CF.h_formula_conjconj_h1 in
          let nhf2,holes2 = subst_hf f.CF.h_formula_conjconj_h2 in
          CF.ConjConj {f with CF.h_formula_conjconj_h1 = nhf1;
              CF.h_formula_conjconj_h2 = nhf2;},holes1@holes2
    | CF.Phase f ->
          let nhf1,holes1 = subst_hf f.CF.h_formula_phase_rd in
          let nhf2,holes2 = subst_hf f.CF.h_formula_phase_rw in
          CF.Phase {f with CF.h_formula_phase_rd = nhf1;
              CF.h_formula_phase_rw = nhf2;},holes1@holes2
    | CF.ViewNode vn ->
          let hole_id = fresh_int () in
          (CF.Hole hole_id, [(hf, hole_id)])
    | _ -> hf, []
  in
  let rec helper f=
   match f with
  | CF.Base fb ->
        let n_hf,n_crt_holes = subst_hf fb.CF.formula_base_heap in
        CF.Base {fb with CF.formula_base_heap = n_hf;}, n_crt_holes
  | CF.Exists _ -> let quans, base1 = CF.split_quantifiers f in
    let nf, n_crt_holes = helper f in
    (CF.add_quantifiers quans nf), n_crt_holes
  | CF.Or orf -> let f1, holes1 = helper orf.CF.formula_or_f1 in
    let f2, holes2 = helper orf.CF.formula_or_f2 in
    CF.Or {orf with CF.formula_or_f1 = f1;
        CF.formula_or_f2 = f2}, holes1@holes2
  in
  helper f0

let symex_td_method_call prog proc ctx ecall=
  let move_br2err (fbrs, es, brs)=
    let err_brs = List.map (fun (pt,c, oft) -> (pt, CF.transform_context (fun es -> CF.Ctx {es with CF.es_formula = CF.substitute_flow_in_f !error_flow_int !norm_flow_int es.CF.es_formula;}) c, oft)) brs in
    (fbrs, es@[((-1,"-1"), err_brs)], [])
  in
  let clone_br2err is_clone_err safe_fl err_fl (fbrs, es, brs)=
    let safe_brs = List.map (fun (pt,c, oft) -> (pt, CF.transform_context (fun es -> CF.Ctx {es with CF.es_formula = CF.mkAnd_pure es.CF.es_formula safe_fl no_pos;}) c, oft)) brs in
    let es_errs = if is_clone_err then
      let err_brs = List.map (fun (pt,c, oft) -> (pt, CF.transform_context (fun es ->
        let cmb_f = CF.mkAnd_pure es.CF.es_formula err_fl no_pos in
        CF.Ctx {es with CF.es_formula = CF.substitute_flow_in_f !error_flow_int !norm_flow_int cmb_f;}
      ) c, oft)) brs in
      [((-1,"-1"), err_brs)]
    else [] in
    (fbrs, es@es_errs, safe_brs)
  in
  (****************************************)
  (****************************************)
  (* ecall = assert_error *)
  let mn = CA.unmingle_name ecall.CA.exp_scall_method_name in
  if String.compare mn assert_err_fn = 0 then
    List.map move_br2err ctx
  else
    (*otherwise*)
    (* generate a pred wrt. method call *)
    let mdecl = CA.look_up_proc_def_raw prog.Cast.new_proc_decls ecall.CA.exp_scall_method_name in
    let view_args =
      let sst= List.combine ecall.exp_scall_arguments mdecl.CA.proc_args in
      List.map (fun (act, (t, form)) -> CP.SpecVar (t, act, Primed)) sst
    in
    let res = if mdecl.CA.proc_return = Void then
      CP.SpecVar (mdecl.CA.proc_return,  res_name ^(fresh_trailer()) , Unprimed)
    else
      let tmp_no = if !func_call_no= 0 then "" else
        "___" ^ (string_of_int !func_call_no)
      in
      CP.SpecVar (mdecl.CA.proc_return,  ("tmp" ^ tmp_no), Primed) in
    let e = CP.SpecVar (Int, err_var^(fresh_trailer()), Unprimed) in
    let view_args_extra = view_args@[res; e] in
    let hv = CF.mkViewNode (dump_self ()) (method2pred mn) view_args_extra ecall.CA.exp_scall_pos in
    let hole_id = fresh_int () in
    let hole = CF.Hole hole_id in
    (* let hv_f = CF.formula_of_heap hv ecall.CA.exp_scall_pos in *)
    (* let hv_f = CF.formula_of_heap hole ecall.CA.exp_scall_pos in *)
    let hv_f = CF.formula_of_heap hv ecall.CA.exp_scall_pos in
    let ctx1 = CF.transform_list_failesc_context 
    (idf,idf,(fun es ->
        (* let es_f, new_crt_holes = subst_view_by_hole  es.CF.es_crt_holes es.es_formula in *)
        Ctx{es with es_formula =
                CF.mkStar (* es_f *) es.es_formula hv_f CF.Flow_combine ecall.CA.exp_scall_pos;
        CF.es_crt_holes = es.CF.es_crt_holes(* @new_crt_holes@[(hv, hole_id)] *)
    })) ctx in
    (* ecall contain assert_error *)
    let is_clone = mdecl.CA.proc_has_assert_err in
    let e_exp = CP.Var (e, no_pos) in
    let safe_fl = MCP.mix_of_pure (CP.mkEqExp e_exp (CP.IConst (0, no_pos)) no_pos) in
    let err_fl = (CP.mkEqExp e_exp (CP.IConst (1, no_pos)) no_pos) in
    let err_fl = MCP.mix_of_pure (err_fl) in
    let res = List.map (clone_br2err is_clone safe_fl err_fl) ctx1 in
    let () = func_call_no := !func_call_no + 1 in
    res

let symex_td_method_call prog proc ctx ecall=
  let pr1 = Cprinter.string_of_list_failesc_context_short in
  let pr2 ecall = !CA.print_prog_exp (C.SCall ecall) in
  Debug.no_2 "symex_td_method_call" pr1 pr2 pr1
      (fun _ _ -> symex_td_method_call prog proc ctx ecall)
      ctx ecall
