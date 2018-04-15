#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module S = Session 
module CP = Cpure
module CF = Cformula
module SC = Sesscommons

(* Transforms Order relations to Sleek relations
 * Example: ocb(A,id_1,B,id_2) -> cb(A__id_1,B__id_2) *)
let trans_ord2sleek_rels (p_formula:CP.p_formula) =
  match p_formula with
  | CP.RelForm (spec_var, vars, loc) ->
      begin match spec_var with
      | CP.SpecVar (typ, id, prmd) ->
          let ev_rel_id = un_option !SC.event_rel_id "" in
          let hbp_rel_id = un_option !SC.hbp_rel_id "" in
          let hb_rel_id = un_option !SC.hb_rel_id "" in
          let cb_rel_id = un_option !SC.cb_rel_id "" in
          (* obtains sleek relation id *)
          let sid = 
            if id = ev_rel_id then un_option !SC.sevent_rel_id ""
            else if id = hbp_rel_id then un_option !SC.shbp_rel_id ""
            else if id = hb_rel_id then un_option !SC.shb_rel_id ""
            else if id = cb_rel_id then un_option !SC.scb_rel_id ""
            else ""
          in
          if not(String.compare sid "" == 0) then (* check for order relation *)
            let rec get_vars vars = begin match vars with
              | role::suid::t -> begin match role, suid with
                | CP.Var (role, pos), CP.Var (suid, _) ->
                    let joined_vars = S.CForm.join_vars role suid orders_vars_separator in
                    (CP.Var (joined_vars, pos))::(get_vars t)
                | _ -> []
                end
              | [] -> []
              | _::[] -> failwith "Expecting a list of vars with even number of elements"
            end in
            let res = get_vars vars in
            let new_spec_var = CP.SpecVar (typ, sid, prmd) in
            Some (CP.RelForm (new_spec_var, res, loc))
          else None
      end
  | _ -> None

let trans_ord2sleek_rels (p_formula:CP.p_formula) =
  let pr = !CP.print_p_formula in
  let pr_out = pr_opt !CP.print_p_formula in
  Debug.no_1 "trans_ord2sleek_rels" pr pr_out trans_ord2sleek_rels p_formula

let trans_pure_fct fct =
  let trans_b_form bform =
    let p_form, ant = bform in
    let p_form = x_add_1 fct p_form in
    match p_form with
    | Some p -> Some (p, ant)
    | None -> None
  in
  (nonef,nonef,nonef,trans_b_form,somef)

let trans_rels_in_formula (fct: CP.p_formula -> CP.p_formula option) (formula: CP.formula) =
  if not(!ord2sleek) then formula
  else  CP.transform_formula (trans_pure_fct fct) formula

(* Transforms Sleek relations to Order relations
 * Example: cb(A__id_1,B__id_2) -> ocb(A,id_1,B,id_2) *)
let trans_sleek2ord_rels (p_formula:CP.p_formula) =
  match p_formula with
  | CP.RelForm (spec_var, vars, loc) ->
      begin match spec_var with
      | CP.SpecVar (typ, id, prmd) ->
          let ev_rel_id = un_option !SC.sevent_rel_id "" in
          let hbp_rel_id = un_option !SC.shbp_rel_id "" in
          let cb_rel_id = un_option !SC.scb_rel_id "" in
          (* obtains order relation id *)
          let oid = 
            if id = ev_rel_id then un_option !SC.event_rel_id ""
            else if id = hbp_rel_id then un_option !SC.hbp_rel_id ""
            else if id = cb_rel_id then un_option !SC.cb_rel_id ""
            else ""
          in
          if not(String.compare oid "" = 0) then (* check for sleek relation *)
            let res = List.fold_left (fun acc var -> match var with
              | CP.Var  (var, pos) ->
                let (role, id) = S.CForm.divide_vars var orders_vars_separator in
                acc@[CP.Var (role, pos); CP.Var (id, pos)]
              | _ -> acc
            ) [] vars in
            let new_spec_var = CP.SpecVar (typ, oid, prmd) in
            Some (CP.RelForm (new_spec_var, res, loc))
          else None
      end
  | _ -> None

let trans_sleek2ord_rels (p_formula:CP.p_formula) =
  let pr = !CP.print_p_formula in
  let pr_out = pr_opt !CP.print_p_formula in
  Debug.no_1 "trans_sleek2ord_rels" pr pr_out trans_sleek2ord_rels p_formula

let trans_ord2sleek_rels_in_pure_formula (formula: CP.formula) =
  trans_rels_in_formula trans_ord2sleek_rels formula

let trans_sleek2ord_rels_in_pure_formula (formula:CP.formula) =
  trans_rels_in_formula trans_sleek2ord_rels


let trans_h_formula_fct fct  =
  let f_p_t = trans_pure_fct fct in
  let rec f_h hform =  match hform with
    | CF.ViewNode vn ->
      (* transform HO args *)
      Some (CF.ViewNode {vn with  CF.h_formula_view_ho_arguments =
                                    List.map
                                      (fun rf ->
                                         {rf with CF.rflow_base = CF.transform_formula (nonef,nonef,f_h, f_p_t) rf.CF.rflow_base }
                                      ) vn.CF.h_formula_view_ho_arguments })
    | _ -> None
  in
  f_h
    
let trans_formula_fct fct  =
  let f_p_t = trans_pure_fct fct in
  let f_h   = trans_h_formula_fct fct in
  (nonef,nonef,f_h,f_p_t)

let trans_ord2sleek_rels_in_formula (formula:CF.formula) =
  CF.transform_formula (trans_formula_fct trans_ord2sleek_rels) formula 

let trans_sleek2ord_rels_in_formula (formula:CF.formula) =
  CF.transform_formula (trans_formula_fct trans_sleek2ord_rels) formula 

let trans_ord2sleek_rels_in_struc_formula struc =
  CF.transform_struc_formula (trans_formula_fct trans_ord2sleek_rels) struc

let trans_sleek2ord_rels_in_struc_formula struc =
  CF.transform_struc_formula (trans_formula_fct trans_sleek2ord_rels) struc

let trans_ord2sleek_rels_in_es es =
  {es with CF.es_formula = trans_ord2sleek_rels_in_formula es.CF.es_formula }

let trans_sleek2ord_rels_in_es es =
  {es with CF.es_formula = trans_sleek2ord_rels_in_formula es.CF.es_formula }

let trans_ord2sleek_rels_in_context ctx =
  CF.transform_context (fun es ->
      CF.Ctx (trans_ord2sleek_rels_in_es es)
    ) ctx


let trans_ord2sleek_rels_in_list_context lc =
  CF.transform_list_context ((fun es ->
      CF.Ctx (trans_ord2sleek_rels_in_es es)
    ), (fun c->c)) lc

let trans_sleek2ord_rels_in_list_context lc =
  CF.transform_list_context ((fun es ->
      CF.Ctx (trans_sleek2ord_rels_in_es es)
    ), (fun c->c)) lc
