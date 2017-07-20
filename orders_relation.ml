#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module S = Session 
module CP = Cpure
module SC = Sesscommons

let vars_separator = "__"

(* Transforms Order relations to Sleek relations *)
let trans_ord_rels_to_sleek_rels (p_formula:CP.p_formula) =
  match p_formula with
  | CP.RelForm (spec_var, vars, loc) ->
      begin match spec_var with
      | CP.SpecVar (typ, id, prmd) ->
          let ev_rel_id = un_option !SC.event_rel_id "" in
          let hbp_rel_id = un_option !SC.hbp_rel_id "" in
          let cb_rel_id = un_option !SC.cb_rel_id "" in
          (* obtains sleek relation id *)
          let sid = 
            if id = ev_rel_id then un_option !SC.sevent_rel_id ""
            else if id = hbp_rel_id then un_option !SC.shbp_rel_id ""
            else if id = cb_rel_id then un_option !SC.scb_rel_id ""
            else ""
          in
          if sid != "" then (* check for order relation *)
            let rec get_vars vars = begin match vars with
              | role::suid::t -> begin match role, suid with
                | CP.Var (role, pos), CP.Var (suid, _) ->
                    let joined_vars = S.CForm.join_vars role suid vars_separator in
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

let trans_ord_rels_to_sleek_rels (p_formula:CP.p_formula) =
  let pr = !CP.print_p_formula in
  let pr_out = pr_opt !CP.print_p_formula in
  Debug.no_1 "trans_ord_rels_to_sleek_rels" pr pr_out trans_ord_rels_to_sleek_rels p_formula

