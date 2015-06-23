#include "xdebug.cppo"

open VarGen
open Globals
open Gen.Basic

module CP = Cpure

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
            (flow, constraints) in
          let res = List.map flow_of_arg args_with_index in
          (* TODO: analyse res into CP.param_flow list *)
          List.map (fun a -> CP.UNKNOWN a) primed_args
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
