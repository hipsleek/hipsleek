let partition_constrs_4_paths link_hpargs_w_path constrs0 prog proc_name =
  let rec init body stmt cpl binding = match stmt with
    | Cast.Label lab -> (* let _ = print_endline "label" in *) init body lab.Cast.exp_label_exp cpl binding
    (* | Cast.CheckRef _ -> let _ = print_endline "check ref" in cpl *)
    (* | Cast.Java _ -> let _ = print_endline "java" in cpl *)
    (* | Cast.Assert _ -> let _ = print_endline "assert" in cpl *)
    | Cast.Assign assi -> (* let _ = print_endline "assign" in *) init body assi.Cast.exp_assign_rhs cpl binding
    (* | Cast.BConst _ -> let _ = print_endline "bconst" in cpl *)
    (* | Cast.Bind _ -> let _ = print_endline "bind" in cpl *)
    | Cast.Block bl -> (* let _ = print_endline "block" in *) init body bl.Cast.exp_block_body cpl binding
    (* | Cast.Barrier _ -> let _ = print_endline "barrier" in cpl *)
    | Cast.Cond co -> (* let _ = print_endline "cond" in *)
      let (cpl1, binding1) = init body co.Cast.exp_cond_then_arm (List.map (fun (cp, cl) -> (1::cp, cl)) cpl) binding in
      let (cpl2, binding2) = init body co.Cast.exp_cond_else_arm (List.map (fun (cp, cl) -> (2::cp, cl)) cpl) binding in
      (cpl1@cpl2, binding1@binding2)
    (* | Cast.Cast _ -> let _ = print_endline "cast" in cpl *)
    (* | Cast.Catch _ -> let _ = print_endline "catch" in cpl *)
    (* | Cast.Debug _ -> let _ = print_endline "debug" in cpl *)
    (* | Cast.Dprint _ -> let _ = print_endline "dprint" in cpl *)
    (* | Cast.FConst _ -> let _ = print_endline "fconst" in cpl *)
    (* | Cast.ICall _ -> let _ = print_endline "icall" in cpl *)
    (* | Cast.IConst _ -> let _ = print_endline "iconst" in cpl *)
    (* | Cast.New _ -> let _ = print_endline "new" in cpl *)
    (* | Cast.Null _ -> let _ = print_endline "null" in cpl *)
    (* | Cast.EmptyArray _ -> let _ = print_endline "empty array" in cpl *)
    (* | Cast.Print _ -> let _ = print_endline "print" in cpl *)
    | Cast.SCall sc -> (* let _ = print_endline "scall" in *)
      (* let cl1 = if ((String.compare sc.Cast.exp_scall_method_name "is_null___$node") = 0 or *)
      (*         (String.compare sc.Cast.exp_scall_method_name "is_not_null___$node") = 0) then *)
      (*   sc::cl else cl in *)
      (* if sc.Cast.exp_scall_is_rec then (cp, cl1) else (cp, cl1) *)
      (List.map (fun (cp, cl) -> (cp, sc::cl)) cpl, binding)
    | Cast.Seq seq -> (* let _ = print_endline "seq" in *)
      let (cpl1, binding1) = init body seq.Cast.exp_seq_exp1 cpl binding in
      init body seq.Cast.exp_seq_exp2 cpl1 binding1
    (* | Cast.This _ -> let _ = print_endline "this" in cpl *)
    (* | Cast.Time _ -> let _ = print_endline "time" in cpl *)
    (* | Cast.Var _ -> let _ = print_endline "var" in cpl *)
    (* | Cast.VarDecl _ -> let _ = print_endline "var decl" in cpl *)
    (* | Cast.Unfold _ -> let _ = print_endline "unfold" in cpl *)
    (* | Cast.Unit _ -> let _ = print_endline "unit" in cpl *)
    (* | Cast.While _ -> let _ = print_endline "while" in cpl *)
    (* | Cast.Sharp _ -> let _ = print_endline "sharp" in cpl *)
    (* | Cast.Try _ -> let _ = print_endline "try" in cpl *)
    | _ -> (cpl, binding)
  in
  (* let rec loop cpl args = *)
    (* let _ = List.map (fun (cp, cl) ->  *)
    (*     let _ = List.map (fun c -> *)
    (*         if c.Cast.exp_scall_is_rec *)
    (*         then *)
    (*           let values = ["not_null"] *)
    (*           let _ = List.map (fun c -> *)
    (*               let name = c.Cast.exp_scall_method_name in *)
    (*               let paras = c.Cast.exp_scall_arguments in *)
    (*               if ((String.compare name "is_null___$node") = 0 and () *)
    (*           ) *)
    (*           print_endline "rec" *)
    (*         else ()) cl in *)
    (*     (cp, cl)) cpl in *)
   (*  cpl *)
  (* in *)
  (* let rec stop body cpl0 cpl1 args = *)
  (*   if ((List.length cpl0) == (List.length cpl1)) then cpl0 *)
  (*   else stop body cpl1 (loop cpl1 args) args  *)
  (* in *)
  let check_node name =
    ((String.compare name "is_null___$node") = 0) or ((String.compare name "is_not_null___$node") = 0)
  in
  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false
  in
  let rec part stmt cpl args = match stmt with
    | Cast.Label lab -> part lab.Cast.exp_label_exp cpl args
    | Cast.Assign assi -> part assi.Cast.exp_assign_rhs cpl args
    | Cast.Block bl -> part bl.Cast.exp_block_body cpl args
    | Cast.Cond co ->
          let (_, cl) = List.hd cpl in
          let sc = List.hd cl in
          if (List.mem "x" sc.Cast.exp_scall_arguments) then
            let cpl1 = part co.Cast.exp_cond_then_arm (List.map (fun (cps, cl) -> (List.map (fun cp -> (1::cp)) cps, cl)) cpl) args in
            let cpl2 = part co.Cast.exp_cond_else_arm (List.map (fun (cps, cl) -> (List.map (fun cp -> (2::cp)) cps, cl)) cpl) args in
            cpl1@cpl2
          else
            List.map (fun (cps, cl) ->
                let cps1 = List.map (fun cp -> (1::cp)) cps in
                let cps2 = List.map (fun cp -> (2::cp)) cps in
                let cps = cps1@cps2 in
                (cps, cl)) cpl
    | Cast.SCall sc ->
          if (check_node sc.Cast.exp_scall_method_name) then
            List.map (fun (cp, cl) -> (cp, sc::cl)) cpl
          else cpl
    | Cast.Seq seq ->
          let cpl1 = part seq.Cast.exp_seq_exp1 cpl args in
          part seq.Cast.exp_seq_exp2 cpl1 args
    | _ -> cpl
  in
  let string_of_cond_path cp = List.fold_left (fun s i -> s ^ string_of_int(i) ^ ";") "" cp in
  let _ = print_endline proc_name in
  let proc = Cast.find_proc prog proc_name in
  let _ = print_endline (Cprinter.string_of_proc_decl 100 proc) in
  let cpl = match proc.Cast.proc_body with
    | None -> [([], [])]
    | Some body -> part body [([[0]], [])] proc.Cast.proc_args
  in
  (* let cpl = match proc.Cast.proc_body with *)
  (*   | None -> [([], [])] *)
  (*   | Some body -> *)
  (*         let cpl0 = [([0], [])] in *)
  (*         let (cpl1, binding) = init body body [([0], [])] [] in *)
  (*         let cpl2 = stop body cpl0 cpl1 proc.Cast.proc_args in *)
  (*         cpl1 *)
  (* in *)
  (* let _ = List.map (fun hprel -> print_endline ("hprel: " ^ (Cprinter.string_of_hprel_short hprel))) constrs0 in *)
  (* let _ = List.map (fun (cps, _) -> let _ = print_endline "cond path: " in List.map (fun cp -> print_endline (string_of_cond_path cp)) cps) cpl in *)
  (* let _ = List.map (fun (_, cl) -> let _ = print_endline "call list: " in List.map (fun cl -> print_endline (Cprinter.string_of_exp (Cast.SCall cl))) cl) cpl in *)
  (* let _ = List.map (fun (il, _) -> let _ = print_endline "il: " in List.map (fun i -> print_string (string_of_int i)) il) link_hpargs_w_path in *)
  let a = List.map (fun (cps, _) -> let filted_hprel = 
    List.filter (fun hprel -> 
        let cp_hprel = string_of_cond_path hprel.Cformula.hprel_path in
        List.fold_left (fun b hprel1 -> b or (contains (string_of_cond_path hprel1) cp_hprel)) false cps
    ) constrs0 in
  (List.hd cps, [], filted_hprel)) cpl in
  let _ = List.map (fun (_, _, hprel_list) -> let _ = print_endline "hprel group:" in List.map (fun hprel -> print_endline (Cprinter.string_of_hprel_short hprel)) hprel_list) a in
  a
  (* let a = Sacore.partition_constrs_4_paths link_hpargs_w_path constrs0 in *)
  (* a *)

 let subst_formula formula hprel_def =
  let helper formula h_formula hprel_def =
    if (Cformula.get_node_name h_formula == Cformula.get_node_name hprel_def.Cformula.hprel_def_hrel)
    then (
        let first_formula = match (List.hd hprel_def.Cformula.hprel_def_body) with
          | (_, None) -> formula
          | (_, Some f) -> f
        in
        List.fold_left (fun all_formula (_, formula) ->
            match formula with
              | None -> all_formula
              | Some f -> Cformula.mkOr all_formula f Globals.no_pos)
            first_formula (List.tl hprel_def.Cformula.hprel_def_body)
    )
    else formula
  in
  match formula with
    | Cformula.Base b -> (
          match b.Cformula.formula_base_heap with
            | Cformula.HRel _ as h_formula -> helper formula h_formula hprel_def
            | _ -> formula
      )
    | Cformula.Exists e -> (
          match e.Cformula.formula_exists_heap with
            | Cformula.HRel _ as h_formula -> helper formula h_formula hprel_def
            | _ -> formula
      )
    | _ -> formula (* raise (Failure "fail formula") *)

let rec subst_struc struc_formula hprel_def =
  match struc_formula with
    | Cformula.EBase eb -> Cformula.EBase { eb with
          Cformula.formula_struc_base = subst_formula eb.Cformula.formula_struc_base hprel_def;
          Cformula.formula_struc_continuation = match eb.Cformula.formula_struc_continuation with
            | None -> None
            | Some sf -> Some (subst_struc sf hprel_def) }
    | Cformula.EAssume ea -> Cformula.EAssume { ea with
          Cformula.formula_assume_simpl = subst_formula ea.Cformula.formula_assume_simpl hprel_def }
    | Cformula.EList el -> Cformula.EList (List.map (fun (label, sf) -> (label, subst_struc sf hprel_def)) el)
    | Cformula.EInfer ei -> subst_struc ei.Cformula.formula_inf_continuation hprel_def
    | Cformula.ECase ec -> struc_formula

let get_case struc_formula prog args hprel_defs =
  let rec helper struc_formula prog =
    match struc_formula with
      | Cformula.EBase eb ->
            let formula = eb.Cformula.formula_struc_base in
            let pre_cond = ( match formula with
              | Cformula.Base b -> (
                    match b.Cformula.formula_base_heap with
                      | Cformula.HRel _ as h_formula -> 
                            let hprel_def = List.find (fun hp -> (String.compare (Cprinter.string_of_h_formula hp.Cformula.hprel_def_hrel) (Cprinter.string_of_h_formula h_formula) == 0)) hprel_defs in
                            let formula = ( match (List.hd hprel_def.Cformula.hprel_def_body) with
                              | (_, None) -> raise (Failure "fail get_case")
                              | (_, Some f) -> f
                            ) in formula
                      | _ -> formula
                )
              | _ -> formula
            ) in
            let (mix_formula, _, _) = Cvutil.xpure prog pre_cond in
            Mcpure.pure_of_mix mix_formula
      | Cformula.EList el -> let (_, sf) = List.hd el in helper sf prog
      | Cformula.ECase _ | Cformula.EInfer _ | Cformula.EAssume _ -> raise (Failure "fail get_case")
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
  (*           if is_contains then case else Cpure.mkPure (Cpure.mkEq (Cpure.mkIConst 0 Globals.no_pos) (Cpure.mkIConst 0 Globals.no_pos) Globals.no_pos) *)
  (*       ) *)
  (*     | _ -> raise (Failure "fail filter") *)
  (* in *)
  let case0 = helper struc_formula prog in
  let case1 = Solver.normalize_to_CNF case0 Globals.no_pos in
  Cpure.remove_dup_constraints case1
  (* let _ = print_endline (Cprinter.string_of_pure_formula case1) in *)
  (* let case_list_list = split_case case1 in *)
  (* let filtered_case_list_list = filter_case case_list_list args in *)
  (* let case2 = match filtered_case_list_list with *)
  (*   | [] -> Cpure.mkTrue Globals.no_pos *)
  (*   | hd::tl -> ( *)
  (*         let first_or = List.fold_left (fun f1 f2 -> Cpure.mkOr f1 f2 None Globals.no_pos) (List.hd hd) (List.tl hd) in *)
  (*         List.fold_left (fun f1 fl -> *)
  (*             let f2 = List.fold_left (fun f11 f12 -> Cpure.mkOr f11 f12 None Globals.no_pos) (List.hd fl) (List.tl fl) in *)
  (*             Cpure.mkAnd f1 f2 Globals.no_pos) first_or tl *)
  (*     ) *)
  (* in *)
  (* (\* let case10 = filter case1 args in *\) *)
  (* case2 *)

(* let group_paths1 grouped_hprel_defs = *)
(*   let _ = print_endline "group_paths1" in grouped_hprel_defs *)

let group_paths hprel_defs =
  let rec helper hprel_defs new_hprel_defs =
    match hprel_defs with
      | [] -> new_hprel_defs
      | hd::tl -> (
            let (cond_path1, _) = List.hd hd.Cformula.hprel_def_body in
            let grouped_hprel_defs = List.fold_left (fun grouped_hprel_defs hprel_def ->
                let (cond_path2, _) = List.hd hprel_def.Cformula.hprel_def_body in
                if (cond_path1 == cond_path2) then (grouped_hprel_defs@[hprel_def]) else grouped_hprel_defs
            ) [] hprel_defs in
            let removed_hprel_defs = List.filter (fun hprel_def ->
                let (cond_path2, _) = List.hd hprel_def.Cformula.hprel_def_body in
                not (cond_path1 == cond_path2)
            ) hprel_defs in
            helper removed_hprel_defs new_hprel_defs@[grouped_hprel_defs]
        )
  in
  helper hprel_defs []

let partition_paths hprel_defs prog =
  List.fold_left (fun all_hprel_defs hprel_def ->
      let new_hprel_defs = List.map (fun hprel_def_body ->
          Cformula.mk_hprel_def hprel_def.Cformula.hprel_def_kind hprel_def.Cformula.hprel_def_hrel hprel_def.Cformula.hprel_def_guard [hprel_def_body] None) hprel_def.Cformula.hprel_def_body in
      new_hprel_defs@all_hprel_defs)
      [] hprel_defs

let rec group_cases pf_sf_l =
  let is_eq pf1 pf2 =
    let not_pf1 = Cpure.mkNot pf1 None Globals.no_pos in
    let not_pf2 = Cpure.mkNot pf2 None Globals.no_pos in
    let formula = Cpure.mkAnd (Cpure.mkOr not_pf1 pf2 None Globals.no_pos) (Cpure.mkOr not_pf2 pf1 None Globals.no_pos) Globals.no_pos in
    not (Tpdispatcher.is_sat 100 (Cpure.mkNot formula None Globals.no_pos) "check eq" "")
  in
  match pf_sf_l with
    | [] -> []
    | (pf1,sf1)::tl -> (
          let sfl = List.fold_left (fun sfs (pf, sf) -> if (is_eq pf pf1) then sf::sfs else sfs) [sf1] tl in
          (pf1, Cformula.mkEList_flatten sfl)::(group_cases (List.filter (fun (pf, sf) -> not (is_eq pf pf1)) tl))
      )

let check_cases cases specs = (* true *)
  (* if ((List.length cases) == 1)  *)
  (* then false *)
  (* else ( *)
  (*     let _ = print_endline "abc" in *)
  (*     let uni_case = List.fold_left (fun uc c -> Cpure.mkOr uc c None Globals.no_pos) (List.hd cases) (List.tl cases) in *)
  (*     not (Tpdispatcher.is_sat 100 (Cpure.mkNot uni_case None Globals.no_pos) "check universe" "") *)
  (* ) *)
  let rec helper pure_formula =
    let list_conjs = Cpure.split_conjunctions pure_formula in
    let filtered_list_conjs = List.filter (fun pf -> Tpdispatcher.is_sat 100 (Cpure.mkNot pf None Globals.no_pos) "check true conjs" "") list_conjs in
    List.fold_left (fun pfs pf -> Cpure.mkAnd pfs pf Globals.no_pos) (List.hd filtered_list_conjs) (List.tl filtered_list_conjs)
  in
  let uni_case = List.fold_left (fun uc c -> Cpure.mkOr uc c None Globals.no_pos) (List.hd cases) (List.tl cases) in
  if not (Tpdispatcher.is_sat 100 (Cpure.mkNot uni_case None Globals.no_pos) "check universe" "")
  then (cases, specs)
  else (
      let new_cases = cases@[Cpure.mkNot (helper (Solver.normalize_to_CNF uni_case Globals.no_pos)) None Globals.no_pos] in
      let new_specs = specs@[Cformula.mkEFalse Cformula.mkFalseFlow Globals.no_pos] in
      (new_cases, new_specs)
  )

(* let subst_hprel_defs hprel_defs = *)
(*   let (main, opt) = List.fold_left (fun (main, opt) hprel_def -> *)
(*       let name = Cformula.get_node_name hprel_def.Cformula.hprel_def_hrel in *)
(*       let reg = Str.regexp "_.*" in *)
(*       let pos = try Str.search_forward reg name 0 with *)
(*         | Not_found -> -1 *)
(*       in *)
(*       if (pos == -1) *)
(*       then (hprel_def::main, opt) *)
(*       else (main, hprel_def::opt) *)
(*   ) ([], []) hprel_defs in *)
(*   List.map (fun hprel_def -> *)
(*       let new_body = List.map (fun (cp, fo) -> *)
(*           match fo with *)
(*             | None -> (cp, fo) *)
(*             | Some f -> ( *)
(*                   match f with *)
(*                     | Cformula.Base fb -> ( *)
(*                           match fb.Cformula.formula_base_heap with *)
(*                             | Cformula.HRel hr as hf -> ( *)
(*                                   let name = Cformula.get_node_name hf in *)
(*                                   let subst_formula = List.find (fun formula -> name == Cformula.get_node_name formula.Cformula.hprel_def_hrel) opt in *)
(*                                   match List.hd subst_formula.Cformula.hprel_def_body with *)
(*                                     | (_, Some f) -> (cp, Some f) *)
(*                                     | (_, None) -> raise (Failure "subst hprel") *)
(*                               ) *)
(*                             | _ -> (cp,fo) *)
(*                       ) *)
(*                     | _ -> (cp,fo) *)
(*               ) *)
(*       ) hprel_def.Cformula.hprel_def_body in *)
(*       { hprel_def with *)
(*           Cformula.hprel_def_body = new_body }) main *)

let create_specs hprel_defs prog proc_name =
  let _ = print_endline "\n*************************************" in
  let _ = print_endline "**************case specs*************" in
  let _ = print_endline "*************************************" in
  let proc = try List.find (fun proc -> proc.Cast.proc_name = proc_name) (Cast.list_of_procs prog) with
    | Not_found -> raise (Failure "fail proc name")
  in
  let partition_hprel_defs = partition_paths hprel_defs prog in
  let grouped_hprel_defs = group_paths partition_hprel_defs in
  (* let _ = List.map (fun hprel_defs -> List.map (fun hprel_def -> print_endline (Cprinter.string_of_hprel_def_short hprel_def)) hprel_defs) grouped_hprel_defs in *)
  (* let grouped_hprel_defs = *)
  (*   if (hd.Cast.proc_is_recursive) *)
  (*   then *)
  (*     [hprel_defs] *)
  (*   else *)
  (*     let partition_hprel_defs = partition_paths hprel_defs prog in *)
  (*     group_paths partition_hprel_defs *)
  (* in *)
  (* let substed_grouped_hprel_defs = List.map (fun hprel_defs -> subst_hprel_defs hprel_defs) grouped_hprel_defs in *)
  (* let _ = List.map (fun hprel_defs -> List.map (fun hprel_def -> print_endline (Cprinter.string_of_hprel_def_short hprel_def)) hprel_defs) substed_grouped_hprel_defs in *)
  let proc_static_specs = proc.Cast.proc_static_specs in
  let specs = List.map (fun hprel_defs -> List.fold_left (fun new_spec hprel_def -> subst_struc new_spec hprel_def) proc_static_specs hprel_defs) grouped_hprel_defs (* substed_grouped_hprel_defs *) in
  let args = Cformula.h_fv (List.hd (List.hd grouped_hprel_defs (* substed_grouped_hprel_defs *))).Cformula.hprel_def_hrel in
  let cases = List.map (fun struc_formula -> get_case struc_formula prog args hprel_defs) specs in
  (* let final_spec = *)
  (* if (check_cases cases specs) *)
  (* then Cformula.ECase { *)
  (*     Cformula.formula_case_branches = group_cases (List.combine cases specs); *)
  (*     Cformula.formula_case_pos = Globals.no_pos *)
  (* } *)
  (* else *)
  (* Cformula.mkEList_flatten specs *)
  let (new_cases, new_specs) = check_cases cases specs in
  let final_spec = Cformula.ECase {
      Cformula.formula_case_branches = group_cases (List.combine new_cases new_specs);
      Cformula.formula_case_pos = Globals.no_pos
  }
  in
  let sfv = Cformula.struc_fv final_spec in
  let sfv_short = Cformula.shorten_svl sfv in
  let short_final_spec = Cformula.subst_struc_avoid_capture sfv sfv_short final_spec in
  let _ = print_endline (Cprinter.string_of_struc_formula_for_spec1 short_final_spec) in
  let _ = print_endline "*************************************" in
  ()
