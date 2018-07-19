#include "xdebug.cppo"
open VarGen
open Gen.Basic
open Globals

module I = Iast
module C = Cast
module CP = Cpure

let repair_prog_with_templ_main iprog cprog =
  let (lhs, rhs) = !Typechecker.lhs_rhs_to_repair in
  let lhs_pf = List.hd lhs in
  let rhs_pf = List.hd rhs in
  let () = x_binfo_pp "marking \n" no_pos in
  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false
  in
  (* let cprog, _ = Astsimp.trans_prog iprog in *)
  let (repaired_lhs, _, nprog) =
    Songbirdfront.get_repair_candidate cprog lhs_pf rhs_pf in
  let n_iprog = Typechecker.update_iprog_exp_defns iprog nprog.Cast.prog_exp_decls in
  (* let () = x_dinfo_hp (add_str "fun_defns: " Cprinter.string_of_exp_decl_list)
   *     nprog.prog_exp_decls no_pos in
   * let () = x_binfo_hp (add_str "new iprog exp_decls: " Iprinter.string_of_exp_decl_list)
   *     n_iprog.prog_exp_decls no_pos in *)
  match !Typechecker.proc_to_repair with
  | None -> (false, iprog)
  | Some proc_name_to_repair ->
    (* let () = x_binfo_pp proc_name_to_repair no_pos in *)
    let proc_to_repair = List.find (fun x ->
        let params = x.Iast.proc_args in
        let typs = List.map (fun x -> x.Iast.param_type) params in
        let mingled_name = Cast.mingle_name x.Iast.proc_name typs in
        contains proc_name_to_repair mingled_name)
        iprog.Iast.prog_proc_decls in
    let n_iproc = Iast.repair_proc proc_to_repair
        n_iprog.Iast.prog_exp_decls in
    let () = x_binfo_hp (add_str "new proc: "
                           (Iprinter.string_of_proc_decl))
        n_iproc no_pos in
    let n_proc_decls =
      List.map (fun x -> if (x.Iast.proc_name = n_iproc.proc_name)
                 then n_iproc else x) iprog.prog_proc_decls in
    let n_prog = {iprog with prog_proc_decls = n_proc_decls} in
    (true, n_prog)

let repair_prog_with_templ iprog =
  let () = x_binfo_pp "marking \n" no_pos in
  let () = Typechecker.lhs_rhs_to_repair := ([], []) in
  let () = Typechecker.proc_to_repair := None in
  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false
  in
  let cprog, _ = Astsimp.trans_prog iprog in
  try
    let () = Typechecker.check_prog_wrapper iprog cprog in
    None
  with _ as e ->
      let (lhs, rhs) = !Typechecker.lhs_rhs_to_repair in
      let lhs_pf = List.hd lhs in
      let rhs_pf = List.hd rhs in
      let (repaired_lhs, _, nprog) =
        Songbirdfront.get_repair_candidate cprog lhs_pf rhs_pf in
      let n_iprog = Typechecker.update_iprog_exp_defns iprog nprog.Cast.prog_exp_decls in
      match !Typechecker.proc_to_repair with
      | None -> Some (false, iprog)
      | Some proc_name_to_repair ->
        (* let () = x_binfo_pp proc_name_to_repair no_pos in *)
        let proc_to_repair = List.find (fun x ->
            let params = x.Iast.proc_args in
            let typs = List.map (fun x -> x.Iast.param_type) params in
            let mingled_name = Cast.mingle_name x.Iast.proc_name typs in
            contains proc_name_to_repair mingled_name)
            iprog.Iast.prog_proc_decls in
        let n_iproc = Iast.repair_proc proc_to_repair
            n_iprog.Iast.prog_exp_decls in
        let () = x_binfo_hp (add_str "new proc: "
                               (Iprinter.string_of_proc_decl))
            n_iproc no_pos in
        let n_proc_decls =
          List.map (fun x -> if (x.Iast.proc_name = n_iproc.proc_name)
                     then n_iproc else x) iprog.prog_proc_decls in
        let n_prog = {iprog with prog_proc_decls = n_proc_decls} in
        Some (true, n_prog)

let create_templ_proc proc replaced_exp loc vars =
  let var_names = List.map CP.name_of_sv vars in
  (* let var_typs = List.map CP.typ_of_sv vars in *)
  let () = x_binfo_hp (add_str "replaced_exp: " (Iprinter.string_of_exp))
      (I.Assign replaced_exp) no_pos in
  let (n_exp, replaced_vars) = I.replace_assign_exp replaced_exp var_names in
  let () = x_binfo_hp (add_str "replaced_vars: " (pr_list pr_id))
      replaced_vars no_pos in
  let () = x_binfo_hp (add_str "n_exp: " (Iprinter.string_of_exp)) n_exp no_pos in
  if n_exp = (I.Assign replaced_exp) then None
  else
    let unk_vars = List.filter (fun x -> List.mem (CP.name_of_sv x) replaced_vars) vars in
    let unk_var_names = List.map CP.name_of_sv unk_vars in
    let unk_var_typs = List.map CP.typ_of_sv unk_vars in

    let unk_exp = I.mk_exp_decl (List.combine unk_var_typs unk_var_names) in
    let n_proc_body = Some (I.replace_exp_with_loc (Gen.unsome proc.I.proc_body)
                              n_exp loc) in
    let n_proc = {proc with proc_body = n_proc_body} in
    Some (n_proc, unk_exp)

let repair_one_statement iprog proc statement statement_pos vars lhs_pf rhs_pf =
  let var_names = List.map CP.name_of_sv vars in
  let var_typs = List.map CP.typ_of_sv vars in
  let n_proc_exp = create_templ_proc proc statement statement_pos vars in
  (* let () = x_binfo_pp "marking \n" no_pos in *)
  match n_proc_exp with
  | None -> None
  | Some (templ_proc, unk_exp) ->
    let () = x_binfo_hp (add_str "new proc: " (Iprinter.string_of_proc_decl))
        templ_proc no_pos in
    let n_proc_decls =
      List.map (fun x -> if (x.I.proc_name = templ_proc.proc_name)
                 then templ_proc else x) iprog.I.prog_proc_decls in
    let n_iprog = {iprog with I.prog_proc_decls = n_proc_decls} in
    let () = x_binfo_hp (add_str "exp_decl: " (Iprinter.string_of_exp_decl))
        unk_exp no_pos in
    let input_repair_proc = {n_iprog with I.prog_exp_decls = [unk_exp]} in
    let repair_res = repair_prog_with_templ input_repair_proc in
    match repair_res with
    | None -> None
    | Some (res, res_iprog) ->
      let repaired_proc = List.find (fun x -> x.I.proc_name = proc.proc_name)
        res_iprog.Iast.prog_proc_decls in
      let () = x_binfo_hp (add_str "repaired proc" (Iprinter.string_of_proc_decl
                                                   )) repaired_proc no_pos in
      let score = if res then
        100
      else 0
      in Some (score, n_iprog)

let start_repair iprog cprog =
  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false
  in
  match !Typechecker.proc_to_repair with
  | None -> (false, None)
  | Some proc_name_to_repair ->
    (* let () = x_binfo_pp "marking \n" no_pos in *)
    let proc_to_repair = List.find (fun x ->
        let params = x.Iast.proc_args in
        let typs = List.map (fun x -> x.Iast.param_type) params in
        let mingled_name = Cast.mingle_name x.Iast.proc_name typs in
        contains proc_name_to_repair mingled_name)
        iprog.Iast.prog_proc_decls in
    let assign_exp_list =
      I.list_of_assign_exp (Gen.unsome proc_to_repair.proc_body) in
    let (lhs, rhs) = !Typechecker.lhs_rhs_to_repair in
    let pure_lhs = List.hd lhs in
    let pure_rhs = List.hd rhs in
    let vars = CP.fv pure_lhs in
    let vars = List.filter (fun x -> String.compare (CP.name_of_sv x)
                               Globals.res_name != 0) vars in
    let (fst_exp, fst_loc) = List.hd assign_exp_list in
    let _ = repair_one_statement iprog proc_to_repair fst_exp fst_loc vars
        pure_lhs pure_rhs in
    (* let _ = create_templ_proc fst_exp var_names proc_to_repair fst_loc in *)
    (false, None)
