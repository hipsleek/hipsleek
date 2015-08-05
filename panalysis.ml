#include "xdebug.cppo"

open VarGen
open Globals
open Gen.Basic

module CP = Cpure
module TL = Tlutils

(* e.g. given x', x=x'+a'-b'+1 return x+a'-b'+1 *)
let extract_ind_exp sv form : CP.param_flow =
  (* norm should be a sum of terms *)
  let () = x_tinfo_hp (add_str "specvar: " CP.string_of_spec_var) sv no_pos in

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
  | CP.BForm ((CP.Lt (lhs, rhs, _) as pf, _), _)
  | CP.BForm ((CP.Lte (lhs, rhs, _) as pf, _), _)
  | CP.BForm ((CP.Gt (lhs, rhs, _) as pf, _), _)
  | CP.BForm ((CP.Gte (lhs, rhs, _) as pf, _), _)
  | CP.BForm ((CP.Eq (lhs, rhs, _) as pf, _), _) ->
    let lhs_tl = TL.term_list_of_exp (CP.afv lhs) lhs in
    let () = x_tinfo_hp (add_str "lhs terms: " TL.print_term_list) lhs_tl no_pos in
    let rhs_tl = TL.term_list_of_exp (CP.afv rhs) rhs in
    let () = x_tinfo_hp (add_str "rhs terms: " TL.print_term_list) rhs_tl no_pos in
    (* move lhs terms to rhs *)
    let tl = rhs_tl @ (List.map negate_term lhs_tl) in
    (* move the *sv* given to the 'lhs',
     * assume that the form contains the specvar *)
    let (s,rest) = List.partition is_term_for_sv tl in
    let s = List.map negate_term s in
    let new_form = CP.BForm ((CP.mkEq (TL.exp_of_term_list s no_pos) (TL.exp_of_term_list rest no_pos) no_pos, None), None) in
    let () = x_tinfo_hp (add_str "rearranged: " !CP.print_formula) new_form no_pos in
    (match s with
     | [] -> failwith "extract_ind_exp: expected formula to contain given spec_var"
     | [s] ->
       (* since form is equivalent to x'=f(x,...),
        * sv_coe is going to be -1 or 1. *)
       (match s.TL.term_coe with
        | CP.IConst (i, pos) ->
          (* This affects the result we end up with *)
          (* If I could think of a way to write this without
           * so much repetition, I would. *)
          if i > 0 then
            let simpl = TL.exp_of_term_list rest no_pos in
            (match pf with
             | CP.Lt (_,_,_) -> CP.DEC (CP.afv simpl,simpl)
             | CP.Lte (_,_,_) -> CP.DECEQ (CP.afv simpl,simpl)
             | CP.Eq (_,_,_) -> CP.IND (CP.afv simpl,simpl)
             | CP.Gt (_,_,_) -> CP.INC (CP.afv simpl,simpl)
             | CP.Gte (_,_,_) -> CP.INCEQ (CP.afv simpl,simpl)
             | _ -> failwith "pf must be one of lt/lte/eq/gt/gte")
          else
            (* needs to invert the _flow_, also. *)
            let rest = (List.map negate_term rest) in
            let simpl = TL.exp_of_term_list rest no_pos in
            (match pf with
             | CP.Lt (_,_,_) -> CP.INC (CP.afv simpl,simpl)
             | CP.Lte (_,_,_) -> CP.INCEQ (CP.afv simpl,simpl)
             | CP.Eq (_,_,_) -> CP.IND (CP.afv simpl,simpl)
             | CP.Gt (_,_,_) -> CP.DEC (CP.afv simpl,simpl)
             | CP.Gte (_,_,_) -> CP.DECEQ (CP.afv simpl,simpl)
             | _ -> failwith "pf must be one of lt/lte/eq/gt/gte")
          (* let simpl = TL.exp_of_term_list res_tl no_pos in *)
          (* CP.IND (CP.afv simpl,simpl) *)
        | _ -> failwith "extract_ind_exp: expected coe of spec_var to be -1 or 1")
     | _ -> failwith "extract_ind_exp: expected only one specvar term")
  | _ -> failwith "extract_ind_exp: expected Eq/Lt/Gt lhs=rhs formula"

let extract_ind_exp sv form : CP.param_flow =
  let pr1 = Cprinter.string_of_spec_var in
  let pr2 = !CP.print_formula in
  let pr_out = Cprinter.string_of_param_flow in
  Debug.no_2 "extract_ind_exp" pr1 pr2 pr_out extract_ind_exp sv form

let analyse_param (lst_assume : CP.infer_rel_type list) (args : Cast.typed_ident list) : (CP.formula * CP.param_flow list) list =
  (* group together which have relations  *)
  let primed_args = List.map (fun (t,i) -> CP.sp_add_prime (CP.mk_typed_spec_var t i) Primed) args in
  let unprimed_args = List.map (fun (t,i) -> CP.sp_rm_prime (CP.mk_typed_spec_var t i)) args in

  (* Given e.g. (R(x'), R(x')), normalise to (x'=x & R(x), R(x'))
   * so that analysis of params can be done more consistently. *)
  let normalise_infer_rel (ir : CP.infer_rel_type) : CP.infer_rel_type =
    let helper (f : CP.formula) =
      match f with
      | CP.BForm ((CP.RelForm (r,rel_arg_exps,pos),_),_) ->
        (* assumes this RelForm is a relation for the proc we analyse *)
        (* build v'=v for when the rel_args don't correspond to
         * the unprimed_args. *)
        let rel_args = CP.get_rel_args f in
        let zip = List.combine rel_args unprimed_args in
        let diff = List.filter (fun (r,arg) -> not (CP.eq_spec_var r arg)) zip in
        let eq = List.map (fun (r,arg) -> CP.mkEqVar r arg pos) diff in
        eq@[CP.mkRel r (List.map (fun sv -> CP.mkVar sv pos) unprimed_args) pos]
      | _ -> [f] in
    let (a,lhs,rhs) = ir in
    let lhs_fs = CP.split_conjunctions lhs in
    let norm_fs = List.flatten (List.map helper lhs_fs) in
    let new_lhs = CP.join_conjunctions norm_fs in
    (a,new_lhs,rhs) in

  let is_same_set_of_svs svs1 svs2 =
    List.for_all (fun u -> List.exists (fun v -> CP.eq_spec_var_unp u v) svs1) svs2 &&
    List.for_all (fun u -> List.exists (fun v -> CP.eq_spec_var_unp u v) svs2) svs1 in

  let lst_assume = List.map normalise_infer_rel lst_assume in

  let zipped_frm_assumes = List.map (fun (cat,lhs,rhs) ->
    (* find the flow; i.e. maybe a transition from one index to another in
     * pre/post Rltn
     * all recursive procs have a relation on LHS.
     * (all non-recursive don't have any list_assume). *)
    let lhs_formulae = CP.split_conjunctions lhs in

    (* may have formulae like a'=a or b'=a,
     * may be necessary to make use of this formulae *)
    let emap = List.fold_left (fun emap f -> 
      match f with
      | CP.BForm((pf,_),_) ->
        (match pf with
         | CP.Eq (CP.Var (sv1,_),CP.Var(sv2,_),_) ->
           CP.EMapSV.add_equiv emap sv1 sv2
         | _ -> emap)
      | _ -> emap) CP.EMapSV.mkEmpty lhs_formulae in
    let () = Debug.tinfo_hprint (add_str "EMap" CP.EMapSV.string_of) emap no_pos in

    (* assumes that at least one RelForm in the list of formulae, *)
    let post_r = match CP.get_RelForm rhs with
                 (* assumes it is *the* relation we're looking for. *)
                 | r::_ -> r
                 | _ -> failwith "Assumes RHS contains a RelForm" in
    let post_r_args = CP.get_rel_args post_r in
    let constraits_of_arg arg =
      (* all the (in)equalities are on the LHS, the entailed relation on RHS *)
      (* need to get all the 'constraints' on `arg`. *)
      let has_arg form =
        let spec_vars = CP.fv form in
        CP.is_eq_exp form &&
        CP.EMapSV.mem arg spec_vars &&
        CP.EMapSV.mem (CP.sp_rm_prime arg) spec_vars in
      (* let constraints = List.filter has_arg lhs_formulae in *)
      let constraints =
        (match (List.filter (fun f ->
                               let spec_vars = CP.fv f in
                               CP.EMapSV.mem arg spec_vars)
                            lhs_formulae) with
           (* I don't see why there'd be no formulae involving arg *)
         | [] -> []
           (* assuming that if there's only one formula involving arg,
            * it must be a defining formula for that arg. *)
         | [f] -> [f]
         | fs ->
           (* assuming that either arg has an alias e.g. b'=a,
            * or there's a formula w/ unprimed e.g. x=x'+1 *)
           let sv = (match CP.EMapSV.find_equiv arg emap with
                     | Some sv -> sv (* some formula arg=sv *)
                     | None -> (CP.sp_rm_prime arg)) in
           List.filter (fun f ->
                          let spec_vars = CP.fv f in
                          CP.EMapSV.mem sv spec_vars)
                       fs) in
      let () = x_tinfo_hp (add_str ("constraints of " ^ (Cprinter.string_of_spec_var arg)) (pr_list !CP.print_formula)) constraints no_pos in
      (arg,constraints) in
    let res = List.map constraits_of_arg post_r_args in
    let analysis = List.map (fun (arg,constr) ->
      (match constr with
         (* since we normalise the input, we shouldn't see empty here. *)
       | [] -> CP.UNKNOWN arg
       | [form] ->
         (* am assuming there is only one x'=f(x) form per infer_rel_ass *)
         extract_ind_exp arg form
       | _ -> failwith "more constraints than assumed")) res in
    (post_r,analysis)) lst_assume in

  (* Print summary of results
   * (for convenience, so -dre analyse isn't needed). *)
  let pr = Cprinter.string_of_pure_formula in
  let pr_def = pr_list (pr_pair pr pr) in
  let pr1 = pr_list (fun (_,a,b) -> pr_pair pr pr (a,b)) in
  let pr2 = pr_list (pr_pair string_of_typ pr_id) in
  let pr_out_item = pr_pair Cprinter.string_of_pure_formula (pr_list Cprinter.string_of_param_flow) in
  let pr_out = pr_list pr_out_item in

  (* debug output initial results (before removing primes) *)
  let () = Debug.tinfo_hprint (add_str "initial result" pr_out) zipped_frm_assumes no_pos in

  (* eliminate the primed specvars from the expressions
   * of the param flows. *)
  (* svs,flows need to be the same length *)
  let simplify (svs,flows : CP.spec_var list * CP.param_flow list) : CP.param_flow list =
    (* helper functions *)
    let primed_vars_of_flow flow =
      match CP.exp_of_param_flow flow with
      | Some e ->
        List.filter CP.is_primed (CP.afv e)
      | None -> [] in
    (* replace occurrences of sv with sub in exp *)
    let subst_primed_var exp sv sub =
      let subst = CP.transform_exp (fun e ->
        match e with
        | CP.Var(v,_) when CP.eq_spec_var sv v ->
          Some sub
        | _ -> None) exp in
      Tlutils.normalize_exp subst in

    let zipped = List.combine svs flows in
    (* get rid of primed spec_vars in the expressions, *)
    (* assumes the sv/flows are formed nicely,
     * so that this can terminate. *)
    let rec helper (res:(CP.spec_var * CP.param_flow) list) (zipped:(CP.spec_var * CP.param_flow) list) =
      match zipped with
      | [] -> res
      | (sv,flow)::rest ->
        (match primed_vars_of_flow flow with
         | [] ->
           (* no more primed in flow,
            * so, carry on to the next one. *)
           helper (res@[(sv,flow)]) rest
         | primed ->
           let flow_subst flow pv =
             (* assumes all the primed vars in the exp of a param_flow
              * occur as arguments to the function. i.e. in res@rest *)
             let replacement = List.assoc pv (res@rest) in
             (match (flow,replacement) with
              | (CP.UNKNOWN _,_) -> flow
              | (_,CP.UNKNOWN _) -> CP.UNKNOWN sv

              | (CP.IND(svs,e1),CP.INC(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.INC(CP.afv e,e)
              | (CP.IND(svs,e1),CP.INCEQ(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.INCEQ(CP.afv e,e)
              | (CP.IND(svs,e1),CP.IND(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.IND(CP.afv e,e)
              | (CP.IND(svs,e1),CP.DEC(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.DEC(CP.afv e,e)
              | (CP.IND(svs,e1),CP.DECEQ(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.DECEQ(CP.afv e,e)

              | (CP.INC(svs,e1),CP.INC(nsvs,e2))
              | (CP.INC(svs,e1),CP.INCEQ(nsvs,e2))
              | (CP.INC(svs,e1),CP.IND(nsvs,e2)) -> (* INC *)
                let e = subst_primed_var e1 pv e2 in
                CP.INC(CP.afv e,e)
              | (CP.INC(svs,e1),CP.DEC(nsvs,e2)) -> CP.UNKNOWN sv
              | (CP.INC(svs,e1),CP.DECEQ(nsvs,e2)) -> CP.UNKNOWN sv

              | (CP.INCEQ(svs,e1),CP.INCEQ(nsvs,e2))
              | (CP.INCEQ(svs,e1),CP.IND(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.INCEQ(CP.afv e,e)
              | (CP.INCEQ(svs,e1),CP.INC(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.INC(CP.afv e,e)
              | (CP.INCEQ(svs,e1),CP.DEC(nsvs,e2)) -> CP.UNKNOWN sv
              | (CP.INCEQ(svs,e1),CP.DECEQ(nsvs,e2)) -> CP.UNKNOWN sv

              | (CP.DEC(svs,e1),CP.INC(nsvs,e2)) -> CP.UNKNOWN sv
              | (CP.DEC(svs,e1),CP.INCEQ(nsvs,e2)) -> CP.UNKNOWN sv
              | (CP.DEC(svs,e1),CP.IND(nsvs,e2))
              | (CP.DEC(svs,e1),CP.DEC(nsvs,e2))
              | (CP.DEC(svs,e1),CP.DECEQ(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.DEC(CP.afv e,e)

              | (CP.DECEQ(svs,e1),CP.INC(nsvs,e2)) -> CP.UNKNOWN sv
              | (CP.DECEQ(svs,e1),CP.INCEQ(nsvs,e2)) -> CP.UNKNOWN sv
              | (CP.DECEQ(svs,e1),CP.IND(nsvs,e2))
              | (CP.DECEQ(svs,e1),CP.DECEQ(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.DECEQ(CP.afv e,e)
              | (CP.DECEQ(svs,e1),CP.DEC(nsvs,e2)) ->
                let e = subst_primed_var e1 pv e2 in
                CP.DEC(CP.afv e,e)

              (* TODO: Need to take care of cases where (one of)
               * the flows is CONST or FLOW.
               * Alternatively, these are 'special' cases of the
               * other flows, so it could be IND(x) rather than FLO(x)
               * at this stage. *)

              | (_,_) -> CP.UNKNOWN sv) in
           (* fold over / substitute for each of the primed vars in the flow. *)
           let flow = List.fold_left flow_subst flow primed in
           helper res ((sv,flow)::rest))
      in
    let res = helper [] zipped in
    let (_,simpl_flows) = List.split res in
    simpl_flows in

  let frm_assumes = List.map (fun (rel,pa) ->
    let args = CP.get_rel_args rel in
    let simpl = simplify (args,pa) in
    (rel,simpl)) zipped_frm_assumes in

  let () = Debug.tinfo_hprint (add_str "interim result" pr_out) frm_assumes no_pos in

  (* combine various param-flow lists, reduce duplication. *)
  let is_param_flows_same (r1,pf1) (r2,pf2) : bool =
    (* if two pflows are the same, each exp will have same TL *)
    let is_pflow_same p q =
      let e1 = CP.exp_of_param_flow p in
      let e2 = CP.exp_of_param_flow q in
      match (e1,e2) with
      | (Some e1,Some e2) ->
        CP.eqExp (CP.mkIConst 0 no_pos)
                 (Tlutils.normalize_exp (CP.mkSubtract e1 e2 no_pos))
      | _ -> false in
    List.for_all2 is_pflow_same pf1 pf2 in

  let frm_assumes = List.fold_left (fun uniq pflows ->
      if List.exists (is_param_flows_same pflows) uniq
      then uniq
      else pflows::uniq) [] frm_assumes in

  (* param_flow will only be of form like IND at this point, 
   * not FLOW,CONST. Convert if applicable. *)
  let specialise_flow f =
    match f with
    | CP.IND([],exp) ->
      CP.CONST exp
      (* because of manipulation by normalisation to termlist exp,
       * sv will have explicit coeff of 1. *)
    | CP.IND(svs,CP.Mult(CP.IConst(1,_),CP.Var(sv,_),_)) ->
      CP.FLOW sv
    | _ -> f in

  let frm_assumes = List.map (fun (rel,flows) ->
    (rel,List.map specialise_flow flows)) frm_assumes in

  let () = Debug.binfo_pprint "ANALYSE PARAMETERS RESULT" no_pos in
  let () = Debug.binfo_pprint "=========================" no_pos in
  let () = Debug.binfo_hprint (add_str "relations (normalised)" pr1) lst_assume no_pos in
  let () = Debug.binfo_hprint (add_str "args" pr2) args no_pos in
  let () = Debug.binfo_hprint (add_str "result" pr_out) frm_assumes no_pos in
  let () = Debug.binfo_pprint "" no_pos in (* pr_list does't end in newline. *)

  frm_assumes

let analyse_param (lst_assume : CP.infer_rel_type list) (args : Cast.typed_ident list) : (CP.formula * CP.param_flow list) list =
  let pr = Cprinter.string_of_pure_formula in
  let pr_def = pr_list (pr_pair pr pr) in
  let pr_oblg = pr_list (fun (_,a,b) -> pr_pair pr pr (a,b)) in
  let pr1 = pr_oblg in
  let pr2 = pr_list (pr_pair string_of_typ pr_id) in
  let pr_out_item = pr_pair Cprinter.string_of_pure_formula (pr_list Cprinter.string_of_param_flow) in
  let pr_out = pr_list pr_out_item in
  Debug.no_2 "analyse_param" pr1 pr2 pr_out analyse_param lst_assume args
