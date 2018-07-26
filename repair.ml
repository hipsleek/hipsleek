#include "xdebug.cppo"
open VarGen
open Printf
open Gen.Basic
open Globals

module I = Iast
module C = Cast
module CP = Cpure

let output_repaired_iprog src pos repaired_exp =
  let file_name = Filename.basename src in
  let r_file = "repaired_" ^ file_name in
  let dir = Filename.dirname src in
  let to_saved_file = dir ^ Filename.dir_sep ^ r_file in
  let () = x_tinfo_pp dir no_pos in
  let read_file filename =
    let lines = ref [] in
    let chan = open_in filename in
    try
      while true; do
        lines := input_line chan :: !lines
      done; []
    with End_of_file ->
      close_in chan;
      List.rev !lines
  in
  let lines = read_file src in
  let count = ref 0 in
  let lines_with_lnums = List.map (fun x ->
      let () = count := 1 + !count in
      (x, !count)) lines in
  let (start_lnum, start_cnum) = (pos.VarGen.start_pos.Lexing.pos_lnum,
                                  pos.VarGen.start_pos.Lexing.pos_cnum
                                  - pos.VarGen.start_pos.Lexing.pos_bol) in
  let (end_lnum, end_cnum) = (pos.VarGen.end_pos.Lexing.pos_lnum,
                              pos.VarGen.end_pos.Lexing.pos_cnum
                              - pos.VarGen.end_pos.Lexing.pos_bol) in
  if (start_lnum != end_lnum) then
    report_error no_pos "repaired expression has to be in one line"
  else
    let exp_str = repaired_exp |> (Cprinter.poly_string_of_pr
                                     Cprinter.pr_formula_exp) in
    let () = x_tinfo_hp (add_str "pos" VarGen.string_of_loc) pos no_pos in
    let output_lines = List.map (fun (x,y) ->
        if (y != start_lnum) then x
        else
          let () = x_tinfo_hp (add_str "x" pr_id) x no_pos in
          let () = x_tinfo_hp (add_str "start" string_of_int) (start_cnum -1) no_pos in
          let () = x_tinfo_hp (add_str "end" string_of_int)
              (end_cnum - start_cnum + 1) no_pos in
          let to_be_replaced = String.sub x (start_cnum - 1) (end_cnum - start_cnum + 1) in
          Str.replace_first (Str.regexp_string to_be_replaced) exp_str x
      ) lines_with_lnums in
    let output = String.concat "\n" output_lines in
    let () = x_tinfo_hp (add_str "output_prog:" pr_id) output no_pos in
    let oc = open_out to_saved_file in
    fprintf oc "%s\n" output;
    close_out oc;
    let () = x_binfo_pp "\n\n \n" no_pos in
    ()

let repair_prog_with_templ_main iprog cprog =
  let (lhs, rhs) = !Typechecker.lhs_rhs_to_repair in
  let lhs_pf = List.hd lhs in
  let rhs_pf = List.hd rhs in
  let () = x_tinfo_pp "marking \n" no_pos in
  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false
  in
  let sb_res = Songbirdfront.get_repair_candidate cprog lhs_pf rhs_pf in
  match sb_res with
  | None -> None
  | Some (nprog, _) ->
    let n_iprog = Typechecker.update_iprog_exp_defns iprog nprog.Cast.prog_exp_decls in
    match !Typechecker.proc_to_repair with
    | None -> None
    | Some proc_name_to_repair ->
      let () = x_tinfo_pp proc_name_to_repair no_pos in
      let proc_to_repair = List.find (fun x ->
          let params = x.Iast.proc_args in
          let typs = List.map (fun x -> x.Iast.param_type) params in
          let mingled_name = Cast.mingle_name x.Iast.proc_name typs in
          contains proc_name_to_repair mingled_name)
          iprog.I.prog_proc_decls in
      let () = x_tinfo_hp (add_str "old proc: " (Iprinter.string_of_proc_decl))
          proc_to_repair no_pos in
      let n_iproc = I.repair_proc proc_to_repair n_iprog.I.prog_exp_decls false in

      let () = x_tinfo_hp (add_str "exp_decls: " (Iprinter.string_of_exp_decl_list))
      n_iprog.I.prog_exp_decls no_pos in
      let () = x_binfo_hp (add_str "new proc: " (Iprinter.string_of_proc_decl))
          n_iproc no_pos in
      let n_proc_decls =
        List.map (fun x -> if (x.Iast.proc_name = n_iproc.proc_name)
                   then n_iproc else x) iprog.prog_proc_decls in
      let n_prog = {iprog with prog_proc_decls = n_proc_decls} in
      let n_cprog, _ = Astsimp.trans_prog n_prog in
      try
        let () = Typechecker.check_prog_wrapper n_iprog n_cprog in
        Some n_prog
      with _ ->
        begin
          let n_iproc = I.repair_proc proc_to_repair n_iprog.I.prog_exp_decls true in
          let n_proc_decls =
            List.map (fun x -> if (x.Iast.proc_name = n_iproc.proc_name)
                       then n_iproc else x) iprog.prog_proc_decls in
          let () = x_binfo_hp (add_str "new proc: " (Iprinter.string_of_proc_decl))
          n_iproc no_pos in
          let n_prog = {iprog with prog_proc_decls = n_proc_decls} in
          let n_cprog, _ = Astsimp.trans_prog n_prog in
          try
            let () = Typechecker.check_prog_wrapper n_iprog n_cprog in
            Some n_prog
          with _ -> None
        end


let repair_prog_with_templ iprog is_cond =
  let () = x_tinfo_pp "marking \n" no_pos in
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
      try
        begin
          let sb_res = Songbirdfront.get_repair_candidate cprog lhs_pf rhs_pf in
          match sb_res with
          | None -> None
          | Some (nprog, repaired_exp) ->
            let n_iprog = Typechecker.update_iprog_exp_defns iprog nprog.Cast.prog_exp_decls in
            match !Typechecker.proc_to_repair with
            | None -> None
            | Some proc_name_to_repair ->
              let () = x_dinfo_pp proc_name_to_repair no_pos in
              let proc_to_repair = List.find (fun x ->
                  let params = x.Iast.proc_args in
                  let typs = List.map (fun x -> x.Iast.param_type) params in
                  let mingled_name = Cast.mingle_name x.Iast.proc_name typs in
                  contains proc_name_to_repair mingled_name)
                  iprog.Iast.prog_proc_decls in
              let n_iproc = Iast.repair_proc proc_to_repair
                  n_iprog.Iast.prog_exp_decls false in
              let () = x_binfo_hp (add_str "new proc:" (Iprinter.string_of_proc_decl))
                  n_iproc no_pos in
              let n_proc_decls =
                List.map (fun x -> if (x.Iast.proc_name = n_iproc.proc_name)
                           then n_iproc else x) iprog.prog_proc_decls in
              let nn_iprog = {iprog with prog_proc_decls = n_proc_decls} in
              let nn_cprog, _ = Astsimp.trans_prog nn_iprog in
              try
                let () = Typechecker.check_prog_wrapper nn_iprog nn_cprog in
                Some (nn_iprog, repaired_exp)
              with _ ->
                if is_cond then
                  begin
                    let snd_iproc = Iast.repair_proc proc_to_repair
                        n_iprog.Iast.prog_exp_decls true in
                    let () = x_binfo_hp (add_str "new proc:" (Iprinter.string_of_proc_decl))
                        snd_iproc no_pos in
                    let snd_proc_decls =
                      List.map (fun x -> if (x.Iast.proc_name = n_iproc.proc_name)
                                 then snd_iproc else x) iprog.prog_proc_decls in
                    let snd_iprog = {iprog with prog_proc_decls = snd_proc_decls} in
                    let snd_cprog, _ = Astsimp.trans_prog snd_iprog in
                    try
                      let () = Typechecker.check_prog_wrapper snd_iprog snd_cprog in
                      Some (snd_iprog, repaired_exp)
                    with _ -> None
                  end
                else None
        end
      with _ -> None

let create_templ_proc proc replaced_exp vars heuristic =
  let var_names = List.map (fun x -> x.I.param_name) vars in
  let () = x_tinfo_hp (add_str "replaced_exp: " (Iprinter.string_of_exp))
      (replaced_exp) no_pos in
  let (n_exp, replaced_vars, replaced_pos_list) =
    I.replace_assign_exp replaced_exp var_names heuristic in
  let () = x_tinfo_hp (add_str "replaced_vars: " (pr_list pr_id))
      replaced_vars no_pos in
  let () = x_tinfo_hp (add_str "n_exp: " (Iprinter.string_of_exp)) n_exp no_pos
  in
  if n_exp = replaced_exp then None
  else if (List.length replaced_pos_list > 1) then None
  else
    let exp_loc = List.hd replaced_pos_list in
    let unk_vars = List.filter (fun x -> List.mem (x.I.param_name) replaced_vars) vars in
    let unk_var_names = List.map (fun x -> x.I.param_name) unk_vars in
    let unk_var_typs = List.map (fun x -> x.I.param_type) unk_vars in
    let unk_exp = I.mk_exp_decl (List.combine unk_var_typs unk_var_names) in
    let n_proc_body = Some (I.replace_exp_with_loc (Gen.unsome proc.I.proc_body)
                              n_exp exp_loc) in
    let n_proc = {proc with proc_body = n_proc_body} in
    let replaced_pos = List.hd replaced_pos_list in
    Some (n_proc, unk_exp, replaced_pos)

let repair_one_statement iprog proc exp is_cond vars heuristic =
  let n_proc_exp = create_templ_proc proc exp vars heuristic
  in
  (* None *)
  let () = x_tinfo_pp "marking \n" no_pos in
  match n_proc_exp with
  | None -> None
  | Some (templ_proc, unk_exp, replaced_pos) ->
    let () = x_tinfo_hp (add_str "new proc: " (Iprinter.string_of_proc_decl))
        templ_proc no_pos in

    let var_names = List.map (fun x -> x.I.param_name) vars in
    let var_typs = List.map (fun x -> x.I.param_type) vars in
    let n_proc_decls =
      List.map (fun x -> if (x.I.proc_name = templ_proc.proc_name)
                 then templ_proc else x) iprog.I.prog_proc_decls in
    let n_iprog = {iprog with I.prog_proc_decls = n_proc_decls} in
    let () = x_dinfo_hp (add_str "exp_decl: " (Iprinter.string_of_exp_decl))
        unk_exp no_pos in
    let input_repair_proc = {n_iprog with I.prog_exp_decls = [unk_exp]} in
    let repair_res = repair_prog_with_templ input_repair_proc is_cond in
    match repair_res with
    | None -> None
    | Some (res_iprog, repaired_exp) ->
      let repaired_proc = List.find (fun x -> x.I.proc_name = proc.proc_name)
        res_iprog.Iast.prog_proc_decls in
      let () = x_binfo_hp (add_str "repaired proc" (Iprinter.string_of_proc_decl
                                                   )) repaired_proc no_pos in
      let exp_pos = I.get_exp_pos exp in
      let score = 100 * (10 - (List.length vars))
                  + exp_pos.VarGen.start_pos.Lexing.pos_lnum in
      let () = x_dinfo_hp (add_str "score:" (string_of_int)) score no_pos in
      Some (score, res_iprog, replaced_pos, repaired_exp)

let get_best_repair repair_list =
  try
    let max_candidate = List.hd repair_list in
    let res = List.fold_left (fun x y ->
        let (a1, b1, c1, d3) = x in
        let (a2, b2, c2, d2) = y in
        if a1 > a2 then x else y
      ) max_candidate (List.tl repair_list) in
    Some res
  with Failure _ -> None

let start_repair iprog cprog =
  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false
  in
  match !Typechecker.proc_to_repair with
  | None -> None
  | Some proc_name_to_repair ->
    let () = x_tinfo_pp "marking \n" no_pos in
    let proc_to_repair = List.find (fun x ->
        let params = x.Iast.proc_args in
        let typs = List.map (fun x -> x.Iast.param_type) params in
        let mingled_name = Cast.mingle_name x.Iast.proc_name typs in
        contains proc_name_to_repair mingled_name)
        iprog.Iast.prog_proc_decls in
    let candidate_exp_list =
      I.list_of_candidate_exp (Gen.unsome proc_to_repair.proc_body) in
    let () = x_tinfo_hp (add_str "replaced_exp: " (pr_list Iprinter.string_of_exp))
        (candidate_exp_list |> List.map fst) no_pos in
    let vars = proc_to_repair.I.proc_args in
    let repair_res_list =
      List.map (fun stmt -> repair_one_statement iprog proc_to_repair (fst stmt)
                   (snd stmt) vars false) candidate_exp_list in
    None
    (* let repair_res_list = List.filter(fun x -> x != None) repair_res_list in
     * let h_repair_res_list = if (repair_res_list == []) then
     *     List.map (fun stmt -> repair_one_statement iprog proc_to_repair
     *                  (fst stmt) (snd stmt) vars true) candidate_exp_list
     *   else repair_res_list
     * in
     * let h_repair_res_list = List.filter(fun x -> x != None) h_repair_res_list in
     * let h_repair_res_list = List.map Gen.unsome h_repair_res_list in
     * let best_res = get_best_repair h_repair_res_list in
     * match best_res with
     * | None -> None
     * | Some (_, best_r_prog, pos, repaired_exp) ->
     *   let repaired_proc = List.find (fun x -> x.I.proc_name = proc_to_repair.proc_name)
     *       best_r_prog.Iast.prog_proc_decls in
     *   let () = x_binfo_hp (add_str "best repaired proc" (Iprinter.string_of_proc_decl
     *                                                     )) repaired_proc no_pos
     *   in
     *   let () = x_tinfo_hp (add_str "templ: " (Cprinter.poly_string_of_pr
     *                                             Cprinter.pr_formula_exp))
     *       repaired_exp no_pos in
     *   Some (best_r_prog, pos, repaired_exp) *)
