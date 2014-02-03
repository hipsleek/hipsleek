open Globals

module CF = Cformula

let subst_formula formula hprel_def =
  match formula with
    | CF.Base b -> (
          match b.CF.formula_base_heap with
            | CF.HRel _ -> (
                  if (CF.get_node_name b.CF.formula_base_heap == CF.get_node_name hprel_def.CF.hprel_def_hrel)
                  then (
                      let first_formula = match (List.hd hprel_def.CF.hprel_def_body) with
                        | (_, None) -> formula
                        | (_, Some f) -> f
                      in
                      List.fold_left (fun all_formula (_, formula) ->
                          match formula with
                            | None -> all_formula
                            | Some f -> CF.mkOr all_formula f no_pos)
                          first_formula (List.tl hprel_def.CF.hprel_def_body) )
                  else formula )
            | _ -> formula )
    | _ -> raise (Failure "fail formula")

let rec subst_struc struc_formula hprel_def =
  match struc_formula with
    | CF.EBase eb -> CF.EBase { eb with
          CF.formula_struc_base = subst_formula eb.CF.formula_struc_base hprel_def;
          CF.formula_struc_continuation = match eb.CF.formula_struc_continuation with
            | None -> None
            | Some sf -> Some (subst_struc sf hprel_def) }
    | CF.EAssume ea -> CF.EAssume { ea with
          CF.formula_assume_simpl = subst_formula ea.CF.formula_assume_simpl hprel_def }
    | CF.EList el -> CF.EList (List.map (fun (label, sf) -> (label, subst_struc sf hprel_def)) el)
    | CF.EInfer ei -> subst_struc ei.CF.formula_inf_continuation hprel_def
    | CF.ECase ec -> struc_formula

let get_case struc_formula prog args =
  let rec helper struc_formula prog =
    match struc_formula with
      | CF.EBase eb ->
            let pre_cond = eb.CF.formula_struc_base in
            let (mix_formula, _, _) = Solver.xpure prog pre_cond in
            Mcpure.pure_of_mix mix_formula
      | CF.EList el -> let (_, sf) = List.hd el in helper sf prog
      | CF.ECase _ | CF.EInfer _ | CF.EAssume _ -> raise (Failure "fail get_case")
  in
  let rec split_case case =
    match case with
      | Cpure.And(f1, f2, _) -> (Cpure.break_formula1 f1) :: (split_case f2)
      | Cpure.Or(f1, f2, _, pos) -> [Cpure.break_formula1 case]
      | Cpure.BForm _ -> [[case]]
      | _ -> raise (Failure "fail split_case")
  in
  let filter_case case_list_list args =
    let rec helper case_list args =
      match case_list with
        | [] -> []
        | hd::tl -> (List.filter (fun f ->
              match f with
                | Cpure.BForm(bf, label) ->
                      let vars = Cpure.fv f in
                      let is_contains = List.fold_left (fun res arg -> res or (Cpure.mem_svl1 arg vars)) false args in
                      is_contains
                | _ -> false
          ) hd)::(helper tl args)
       in
    let case_list_list1 = helper case_list_list args in
    List.filter (fun fl ->
        match fl with
          | [] -> false
          | _ -> true
    ) case_list_list1
  in
  (* let rec filter case args = *)
  (*   match case with *)
  (*     | Cpure.And(f1, f2, pos) -> Cpure.mkAnd (filter f1 args) (filter f2 args) pos *)
  (*     | Cpure.Or(f1, f2, label, pos) -> Cpure.mkOr (filter f1 args) (filter f2 args) label pos *)
  (*     | Cpure.BForm(bf, label) -> ( *)
  (*           let vars = Cpure.fv case in *)
  (*           let is_contains = List.fold_left (fun res arg -> res or (Cpure.mem_svl1 arg vars)) false args in *)
  (*           if is_contains then case else Cpure.mkPure (Cpure.mkEq (Cpure.mkIConst 0 no_pos) (Cpure.mkIConst 0 no_pos) no_pos) *)
  (*       ) *)
  (*     | _ -> raise (Failure "fail filter") *)
  (* in *)
  let case0 = helper struc_formula prog in
  let case1 = Solver.normalize_to_CNF case0 no_pos in
  let case_list_list = split_case case1 in
  let filtered_case_list_list = filter_case case_list_list args in
  let case2 = match filtered_case_list_list with
    | [] -> Cpure.mkTrue no_pos
    | hd::tl -> (
          let first_or = List.fold_left (fun f1 f2 -> Cpure.mkOr f1 f2 None no_pos) (List.hd hd) (List.tl hd) in
          List.fold_left (fun f1 fl ->
              let f2 = List.fold_left (fun f11 f12 -> Cpure.mkOr f11 f12 None no_pos) (List.hd fl) (List.tl fl) in
              Cpure.mkAnd f1 f2 no_pos) first_or tl
      )
  in
  (* let case10 = filter case1 args in *)
  case2

let group_paths1 grouped_hprel_defs =
  let _ = print_endline "group_paths1" in grouped_hprel_defs

let group_paths hprel_defs =
  let rec group grouped_hprel_defs hprel_defs hprel_def =
    match hprel_defs with
      | [] -> [grouped_hprel_defs]
      | hd::tl -> (
            let (cond_path1, _) = List.hd hd.CF.hprel_def_body in
            let (cond_path2, _) = List.hd hprel_def.CF.hprel_def_body in
            if (cond_path1 == cond_path2) then group (grouped_hprel_defs@[hd]) tl hprel_def else group grouped_hprel_defs tl hprel_def
        )
  in
  let rec remove old_hprel_defs hprel_def =
    match old_hprel_defs with
      | [] -> []
      | hd::tl -> (
            let (cond_path1, _) = List.hd hd.CF.hprel_def_body in
            let (cond_path2, _) = List.hd hprel_def.CF.hprel_def_body in
            if (cond_path1 == cond_path2) then remove tl hprel_def else hd::(remove tl hprel_def)
        )
  in
  let rec helper hprel_defs new_hprel_defs =
    match hprel_defs with
      | [] -> new_hprel_defs
      | hd::tl -> (
            let grouped_hprel_defs = group [] hprel_defs (List.hd hprel_defs) in
            let removed_hprel_defs = remove hprel_defs (List.hd hprel_defs) in
            helper removed_hprel_defs new_hprel_defs@grouped_hprel_defs
        )
  in
  helper hprel_defs []

let partition_paths hprel_defs prog =
  List.fold_left (fun all_hprel_defs hprel_def ->
      let new_hprel_defs = List.map (fun hprel_def_body ->
          CF.mk_hprel_def hprel_def.CF.hprel_def_kind hprel_def.CF.hprel_def_hrel hprel_def.CF.hprel_def_guard [hprel_def_body] None) hprel_def.CF.hprel_def_body in
      new_hprel_defs@all_hprel_defs)
      [] hprel_defs

let rec group_cases pf_sf_l =
  let is_eq pf1 pf2 =
    let not_pf1 = Cpure.mkNot pf1 None no_pos in
    let not_pf2 = Cpure.mkNot pf2 None no_pos in
    let formula = Cpure.mkAnd (Cpure.mkOr not_pf1 pf2 None no_pos) (Cpure.mkOr not_pf2 pf1 None no_pos) no_pos in
    not (Tpdispatcher.is_sat 100 (Cpure.mkNot formula None no_pos) "check eq" "")
  in
  let rec helper pf1 tl1 =
    match tl1 with
      | [] -> []
      | (pf,sf)::tl -> if (is_eq pf pf1) then (helper pf1 tl) else (pf,sf)::(helper pf1 tl)
  in
  match pf_sf_l with
    | [] -> []
    | (pf1,sf1)::tl -> (
          let sfl = List.fold_left (fun sfs (pf, sf) -> if (is_eq pf pf1) then sf::sfs else sfs) [sf1] tl in
          (pf1, CF.mkEList_flatten sfl)::(group_cases (helper pf1 tl))
      )

let check_cases cases =
  let uni_case = List.fold_left (fun uc c -> Cpure.mkOr uc c None no_pos) (List.hd cases) (List.tl cases) in
  not (Tpdispatcher.is_sat 100 (Cpure.mkNot uni_case None no_pos) "check universe" "")

let create_specs hprel_defs prog proc_name =
  let _ = print_endline "\n*************************************" in
  let _ = print_endline "**************case specs*************" in
  let _ = print_endline "*************************************" in
  let rec helper proc_list = match proc_list with
    | [] -> ()
    | hd::tl -> (
        if (proc_name == hd.Cast.proc_name) then
          let grouped_hprel_defs =
            if (hd.Cast.proc_is_recursive)
            then
              [hprel_defs]
            else
              let partition_hprel_defs = partition_paths hprel_defs prog in
              group_paths partition_hprel_defs
          in
          let proc_static_specs = hd.Cast.proc_static_specs in
          let specs = List.map (fun hprel_defs -> List.fold_left (fun new_spec hprel_def -> subst_struc new_spec hprel_def) proc_static_specs hprel_defs) grouped_hprel_defs in
          let args = CF.h_fv (List.hd (List.hd grouped_hprel_defs)).CF.hprel_def_hrel in
          let cases = List.map (fun struc_formula -> get_case struc_formula prog args) specs in
          let final_spec =
          if (check_cases cases)
          then CF.ECase {
              CF.formula_case_branches = group_cases (List.combine cases specs);
              CF.formula_case_pos = no_pos
          }
          else
          CF.mkEList_flatten specs
          in
          let _ = print_endline (Cprinter.string_of_struc_formula_for_spec1 final_spec) in
          let _ = print_endline "*************************************" in
          ()
        else
          helper tl
      )
  in
  helper (Cast.list_of_procs prog)
