#include "xdebug.cppo"

open VarGen
open Globals
open Gen.Basic

module CP = Cpure
module TL = Tlutils

(* e.g. given x', x=x'+a'-b'+1 return x+a'-b'+1 *)
let extract_ind_exp sv form : CP.exp =
  (* norm should be a sum of terms *)
  let () = x_binfo_hp (add_str "specvar: " CP.string_of_spec_var) sv no_pos in

  (* term will be of form coe*sv^1  *)
  let is_term_for_sv (term : TL.term) : bool =
    match term.TL.term_var with
    | [(v,1)] -> CP.eq_spec_var sv v
    | _ -> false in

  let negate_term t =
    let neg = match t.TL.term_coe with
      | CP.IConst (i, pos) ->
        CP.mkIConst (-1 * i) pos
      | coe ->
        let pos = CP.pos_of_exp coe in
        CP.mkMult (CP.mkIConst (-1) pos) coe pos in
    { t with TL.term_coe = neg } in

  match form with
  | CP.BForm ((CP.Eq (lhs, rhs, _), _), _) ->
    let lhs_tl = TL.term_list_of_exp (CP.afv lhs) lhs in
    let () = x_binfo_hp (add_str "lhs terms: " TL.print_term_list) lhs_tl no_pos in
    let rhs_tl = TL.term_list_of_exp (CP.afv rhs) rhs in
    let () = x_binfo_hp (add_str "rhs terms: " TL.print_term_list) rhs_tl no_pos in
    (* move lhs terms to rhs *)
    let tl = rhs_tl @ (List.map negate_term lhs_tl) in
    (* move the *sv* given to the 'lhs',
     * assume that the form contains the specvar *)
    let (s,rest) = List.partition is_term_for_sv tl in
    let s = List.map negate_term s in
    let new_form = CP.BForm ((CP.mkEq (TL.exp_of_term_list s no_pos) (TL.exp_of_term_list rest no_pos) no_pos, None), None) in
    let () = x_binfo_hp (add_str "rearranged: " !CP.print_formula) new_form no_pos in
    (match s with
     | [] -> failwith "extract_ind_exp: expected formula to contain given spec_var"
     | [s] ->
       (* since form is equivalent to x'=f(x,...),
        * sv_coe is going to be -1 or 1. *)
       (match s.TL.term_coe with
        | CP.IConst (i, pos) ->
          let res_tl = if i > 0
            then rest
            else (List.map negate_term rest) in
          TL.exp_of_term_list res_tl no_pos
        | _ -> failwith "extract_ind_exp: expected coe of spec_var to be -1 or 1")
     | _ -> failwith "extract_ind_exp: expected only one specvar term")
  | _ -> failwith "extract_ind_exp: expected Eq lhs=rhs formula"

let extract_ind_exp sv form : CP.exp =
  let pr1 = Cprinter.string_of_spec_var in
  let pr2 = !CP.print_formula in
  let pr_out = Cprinter.string_of_formula_exp in
  Debug.no_2 "simplify_ind_form" pr1 pr2 pr_out extract_ind_exp sv form

let analyse_param (lst_assume : CP.infer_rel_type list) (args : Cast.typed_ident list) : CP.param_flow list list =
  (* group together which have relations  *)
  let primed_args = List.map (fun (t,i) -> CP.sp_add_prime (CP.mk_typed_spec_var t i) Primed) args in

  (* let flow_of_arg (idx, arg) = *)

  let frm_assumes = List.map (fun (cat,lhs,rhs) ->
    (* find the flow; i.e. maybe a transition from one index to another in
     * pre/post Rltn
     * all recursive procs have a relation on LHS.
     * (all non-recursive don't have any list_assume). *)
    let lhs_formulae = CP.split_conjunctions lhs in
    (* assumes that at least one RelForm in the list of formulae,
     * assumes it is *the* relation we're looking for. *)
    match (List.filter CP.is_RelForm lhs_formulae) with
       | [] -> []
       | pre_r::_ ->
          let pre_r_args = CP.get_rel_args pre_r in
          let post_r = rhs in
          let post_r_args = CP.get_rel_args post_r in
          (* you should have used the vars themselves, rather than idx. *)
          let post_with_index = List.mapi (fun i x -> (i,x)) post_r_args in
          let args_with_index = List.mapi (fun i x -> (i,x)) primed_args in
          (* build (flow, constraints) for each arg *)
          let flow_of_arg (idx, arg) = (* : ((int * int) option * CP.formula list) *)
            let flow_to_idx = List.filter (fun (i,x) ->
              CP.eq_spec_var_unp arg x) post_with_index in
            let flow = match flow_to_idx with
              | (i,_)::_ -> Some (idx,i)
              | [] -> None in
            (* all the (in)equalities are on the LHS, the entailed relation on RHS *)
            (* need to get all the 'constraints' on `arg`. *)
            let has_arg form =
              let spec_vars = CP.fv form in
              CP.is_eq_exp form &&
              CP.EMapSV.mem arg spec_vars &&
              CP.EMapSV.mem (CP.sp_rm_prime arg) spec_vars in
            let constraints = List.filter has_arg lhs_formulae in
            let () = x_binfo_hp (add_str ("constraints of " ^ (Cprinter.string_of_spec_var arg)) (pr_list !CP.print_formula)) constraints no_pos in
            (arg,flow,constraints) in
          let res = List.map flow_of_arg args_with_index in
          (* TODO: analyse res into CP.param_flow list *)
          List.map (fun (arg,flow,constr) ->
            match flow with
            (* if None, may be constant, or alias, or something else. *)
            | None -> CP.UNKNOWN arg
            | Some (fr_a,to_a) ->
              let from_arg = List.nth primed_args fr_a in
              (match constr with
               | [] -> CP.FLOW from_arg
               | [form] ->
                 (* am assuming there is only one x'=f(x) form per infer_rel_ass *)
                 let simpl = extract_ind_exp from_arg form in
                 CP.IND (CP.afv simpl, simpl)
               | _ -> failwith "more constraints than assumed")
          ) res
    ) lst_assume in

  (* TODO: combine various param-flow lists, reduce duplication. *)
  frm_assumes

let analyse_param (lst_assume : CP.infer_rel_type list) (args : Cast.typed_ident list) : (CP.param_flow list list) =
  let pr = Cprinter.string_of_pure_formula in
  let pr_def = pr_list (pr_pair pr pr) in
  let pr_oblg = pr_list (fun (_,a,b) -> pr_pair pr pr (a,b)) in
  let pr1 = pr_oblg in
  let pr2 = pr_list (pr_pair string_of_typ pr_id) in
  let pr_out = pr_list (pr_list Cprinter.string_of_param_flow) in
  Debug.no_2 "analyse_param" pr1 pr2 pr_out analyse_param lst_assume args
