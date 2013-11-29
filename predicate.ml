open Globals
open Gen

module DD = Debug
module Err = Error
module CA = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq
module TP = Tpdispatcher


let default_prefix_pure_hprel = "_pure_of_"

let pure_hprel_map = ref ([]: (ident * ident) list)

let generate_pure_rel hprel=
  let n_p_hprel ={
      CA.rel_name = default_prefix_pure_hprel ^ hprel.CA.hp_name;
      CA.rel_vars = List.map fst hprel.CA.hp_vars_inst;
      CA.rel_formula = CF.get_pure hprel.CA.hp_formula;
  }
  in
  (*add map*)
  let _ = pure_hprel_map := !pure_hprel_map@[(hprel.CA.hp_name, n_p_hprel.CA.rel_name)] in
  let _= Smtsolver.add_relation n_p_hprel.CA.rel_name n_p_hprel.CA.rel_vars n_p_hprel.CA.rel_formula in
  n_p_hprel

let pure_relation_name_of_heap_pred (CP.SpecVar (_, hp, p))=
  let rec look_up map=
    match map with
      | [] -> report_error no_pos "predicate.pure_relation_name_of_heap_pred"
      | (id1,id2)::rest -> if String.compare id1 hp = 0 then (CP.SpecVar (RelT [], id2, p)) else
          look_up rest
  in
  look_up !pure_hprel_map


let heap_pred_name_of_pure_relation (CP.SpecVar (_, pure_hp, p))=
  let rec look_up map=
    match map with
      | [] -> None
      | (id1,id2)::rest -> if String.compare id2 pure_hp = 0 then Some (CP.SpecVar(HpT, id1, p)) else
          look_up rest
  in
  look_up !pure_hprel_map


let pure_of_heap_pred_gen_h hf0=
  let rec helper hf=
    match hf with
      | CF.Star { CF.h_formula_star_h1 = hf1;
        CF.h_formula_star_h2 = hf2;
        CF.h_formula_star_pos = pos} ->
            let nh1,ps1 = helper hf1 in
            let nh2, ps2 = helper hf2 in
            let nh = match nh1,nh2 with
              | (CF.HEmp,CF.HEmp) -> CF.HEmp
              | (CF.HEmp,_) -> nh2
              | (_, CF.HEmp) -> nh1
              | _ -> CF.Star {CF.h_formula_star_h1 = nh1;
                CF.h_formula_star_h2 = nh2;
                CF.h_formula_star_pos = pos}
            in (nh, ps1@ps2)
      | CF.StarMinus { CF.h_formula_starminus_h1 = hf1;
        CF.h_formula_starminus_h2 = hf2;
CF.h_formula_starminus_aliasing = al;
        CF.h_formula_starminus_pos = pos} ->
            let nh1,ps1 = helper hf1 in
            let nh2, ps2 = helper hf2 in
            let nh = match nh1, nh2 with
              | (CF.HEmp,CF.HEmp) -> CF.HEmp
              | (CF.HEmp,_) -> nh2
              | (_, CF.HEmp) -> nh1
              | _ -> CF.StarMinus { CF.h_formula_starminus_h1 = nh1;
                CF.h_formula_starminus_h2 = nh2;
                CF.h_formula_starminus_aliasing = al;
                CF.h_formula_starminus_pos = pos}
            in (nh, ps1@ps2)
      | CF.ConjStar { CF.h_formula_conjstar_h1 = hf1;
        CF.h_formula_conjstar_h2 = hf2;
        CF.h_formula_conjstar_pos = pos} ->
             let nh1,ps1 = helper hf1 in
             let nh2, ps2 = helper hf2 in
             let nh = match nh1, nh2 with
               | (CF.HEmp,CF.HEmp) -> CF.HEmp
               | (CF.HEmp,_) -> nh2
               | (_, CF.HEmp) -> nh1
               | _ ->  CF.ConjStar { CF.h_formula_conjstar_h1 = nh1;
                 CF.h_formula_conjstar_h2 = nh2;
                 CF.h_formula_conjstar_pos = pos}
             in (nh, ps1@ps2)
      | CF.ConjConj { CF.h_formula_conjconj_h1 = hf1;
        CF.h_formula_conjconj_h2 = hf2;
        CF.h_formula_conjconj_pos = pos} ->
            let nh1,ps1 = helper hf1 in
            let nh2, ps2 = helper hf2 in
            let nh = match nh1, nh2 with
              | (CF.HEmp,CF.HEmp) -> CF.HEmp
              | (CF.HEmp,_) -> nh2
              | (_, CF.HEmp) -> nh1
              | _ -> CF.ConjConj { CF.h_formula_conjconj_h1 = nh1;
                CF.h_formula_conjconj_h2 = nh2;
                CF.h_formula_conjconj_pos = pos}
            in (nh, ps1@ps2)
      | CF.Phase { CF.h_formula_phase_rd = hf1;
        CF.h_formula_phase_rw = hf2;
        CF.h_formula_phase_pos = pos} ->
            let nh1,ps1 = helper hf1 in
            let nh2, ps2 = helper hf2 in
            let nh = match nh1, nh2 with
              | (CF.HEmp,CF.HEmp) -> CF.HEmp
              | (CF.HEmp,_) -> nh2
              | (_, CF.HEmp) -> nh1
              | _ -> CF.Phase { CF.h_formula_phase_rd = nh1;
                CF.h_formula_phase_rw = nh2;
                CF.h_formula_phase_pos = pos}
            in (nh, ps1@ps2)
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
        CF.h_formula_conj_h2 = hf2;
        CF.h_formula_conj_pos = pos} ->
            let nh1,ps1 = helper hf1 in
            let nh2, ps2 = helper hf2 in
            let nh = match nh1, nh2 with
              | (CF.HEmp,CF.HEmp) -> CF.HEmp
              | (CF.HEmp,_) -> nh2
              | (_, CF.HEmp) -> nh1
              | _ -> CF.Conj { CF.h_formula_conj_h1 = nh1;
                CF.h_formula_conj_h2 = nh2;
                CF.h_formula_conj_pos = pos}
            in (nh, ps1@ps2)
      | CF.HRel (hp, eargs, p) ->
            let prel = pure_relation_name_of_heap_pred hp in
            let p= CP.mkRel prel eargs p in
            (CF.HEmp, [(p,hp)])
      | _ -> (hf,[])
  in
  helper hf0

let pure_of_heap_pred_x pos hfs=
  let ps, p_hps = List.fold_left ( fun (ls,ls2) hf ->
      let _, pr_ps =  pure_of_heap_pred_gen_h hf in
      let ps,hprels = List.split pr_ps in
      (ls@ps, ls2@hprels)
  ) ([],[]) hfs
  in
  let p = CP.conj_of_list ps pos in
  p,p_hps

let pure_of_heap_pred pos hfs=
  let pr1 = !CP.print_formula in
  let pr2 = pr_list_ln Cprinter.prtt_string_of_h_formula in
  (* let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in *)
  Debug.no_1 "pure_of_heap_pred" pr2 (pr_pair pr1 !CP.print_svl)
      (fun _ -> pure_of_heap_pred_x pos hfs) hfs

(* let pure_of_heap_pred_x f0= *)
(*   let rec helper f= *)
(*     match f with *)
(*       | CF.Base fb -> *)
(*             let nh, ps = pure_of_heap_pred_h fb.CF.formula_base_heap in *)
(*             let new_p = CP.conj_of_list ps fb.CF.formula_base_pos in *)
(*             CF.Base { fb with CF.formula_base_pure = MCP.merge_mems fb.CF.formula_base_pure (MCP.mix_of_pure new_p) true; *)
(*                 CF.formula_base_heap = nh; *)
(*             } *)
(*       | CF.Exists _ -> *)
(*             let qvars, base1 = CF.split_quantifiers f in *)
(*             let nf = helper base1 in *)
(*             CF.add_quantifiers qvars nf *)
(*       | CF.Or orf -> *)
(*             let nf1 = helper orf.CF.formula_or_f1 in *)
(*             let nf2 = helper orf.CF.formula_or_f2 in *)
(*             ( CF.Or {orf with CF.formula_or_f1 = nf1; *)
(*                 CF.formula_or_f2 = nf2;}) *)
(*   in *)
(*   helper f0 *)


let trans_rels_gen pf0 =
  let rec helper pf=
    match pf with
      | CP.BForm (bf,a) -> begin
          match bf with
            | (CP.RelForm (r, eargs, p),x) ->
                  let ohp = heap_pred_name_of_pure_relation r in
                  (
                      match ohp with 
                        | None -> (pf,[])
                        | Some hp -> (CP.BForm (((CP.BConst (true, p)), x) ,a),  [(CF.HRel (hp, eargs, p))])
                  )
            | _ -> (pf, [])
        end
      | CP.And (f1,f2,p) -> let nf1, hf1 = helper f1 in
        let nf2, hf2= helper f2 in
        let np = match (CP.isConstTrue nf1), (CP.isConstTrue nf2) with
          | true,true -> nf1
          | true,_ -> nf2
          | _, true -> nf1
          | _ -> CP.And (nf1,nf2,p)
        in (np, hf1@hf2)
  | CP.AndList lp-> let r,hfs = List.fold_left (fun (ps, hfs) (l, p) ->
        let np, n_hfs = helper p in
        if CP.isConstTrue np then
          (ps, hfs@n_hfs)
        else (ps@[(l,np)], hfs@n_hfs)
    ) ([],[]) lp in
    if r = [] then (CP.mkTrue no_pos, hfs) else (CP.AndList r,hfs)
  | CP.Or (f1,f2,c,p) -> let nf1, hf1 = helper f1 in
    let nf2, hf2= helper f2 in
    let np = match (CP.isConstTrue nf1), (CP.isConstTrue nf2) with
      | true,true -> nf1
      | true,_ -> nf2
      | _, true -> nf1
      | _ -> CP.Or (nf1,nf2, c,p)
    in (np, hf1@hf2)
  | CP.Not (f,b,p) -> let np,hfs = helper f in
    if CP.isConstTrue np then
      (CP.mkTrue p, hfs)
    else (CP.Not (np, b, p), hfs)
  | CP.Forall (a,f,c,p) -> let np,hfs = helper f in
    if CP.isConstTrue np then
      (CP.mkTrue p, hfs)
    else
      (CP.Forall (a,np,c,p), hfs)
  | CP.Exists (a,f,b,p) -> let np,hfs = helper f in
    if CP.isConstTrue np then
      (CP.mkTrue p, hfs)
    else
      (CP.Exists (a,np,b,p), hfs)
  in
  helper pf0

let trans_rels_x pf0 =
  let rec helper pf=
    match pf with
      | CP.BForm (bf,a) -> begin
          match bf with
            | (CP.RelForm (r, eargs, p),x) ->
                  let ohp = heap_pred_name_of_pure_relation r in
                  (
                      match ohp with 
                        | None -> None
                        | Some hp -> Some (hp, CF.HRel (hp, eargs, p))
                  )
            | _ -> None
        end
      | _ -> None
  in
  let ps = CP.list_of_conjs pf0 in
  let pr_hp_rhs = List.map helper ps in
  List.fold_left (fun r (r_opt) -> match r_opt with
    | None -> r
    | Some a -> r@[a]
  ) [] pr_hp_rhs

let trans_rels pf0 =
  let pr1 = !CP.print_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv Cprinter.prtt_string_of_h_formula) in
  Debug.no_1 "trans_rels" pr1 ( pr2)
      (fun _ -> trans_rels_x pf0) pf0

let heap_pred_of_pure_x p0=
  let _,hfs = trans_rels_gen p0 in
  match hfs with
    | [] -> false, CF.HEmp
    | _ -> let hf = CF.join_star_conjunctions hfs in
      true,hf
      (* let pos = CP.pos_of_formula p0 in *)
      (* let f0 = CF.formula_of_heap hf pos in *)
      (* CF.mkAnd_pure f0 (MCP.mix_of_pure np) pos *)

let heap_pred_of_pure p0=
  let pr1 = !CP.print_formula in
  let pr2 = Cprinter.prtt_string_of_h_formula in
  Debug.no_1 "heap_pred_of_pure" pr1 (pr_pair string_of_bool pr2)
      (fun _ -> heap_pred_of_pure_x p0) p0
