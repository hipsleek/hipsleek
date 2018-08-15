#include "xdebug.cppo"
open VarGen
open Printf
open Gen.Basic
open Globals

module I = Iast
module C = Cast
module CP = Cpure

let stop = ref false
let next_proc = ref false

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
  let ents = !Typechecker.repairing_ents in
  let () = x_tinfo_pp "marking \n" no_pos in
  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false
  in
  let sb_res = Songbirdfront.get_repair_candidate cprog ents None in
  match sb_res with
  | None -> None
  | Some (_, _, None, _) -> None
  | Some (nprog, _, Some neg_prog, _) ->
    match !Typechecker.proc_to_repair with
    | None -> None
    | Some proc_name_to_repair ->
      let n_iprog = Typechecker.update_iprog_exp_defns iprog nprog.Cast.prog_exp_decls in
      let () = x_tinfo_pp proc_name_to_repair no_pos in
      let proc_to_repair = List.find (fun x ->
          let params = x.I.proc_args in
          let typs = List.map (fun x -> x.I.param_type) params in
          let mingled_name = Cast.mingle_name x.I.proc_name typs in
          contains proc_name_to_repair mingled_name)
          iprog.I.prog_proc_decls in
      let () = x_tinfo_hp (add_str "old proc: " (Iprinter.string_of_proc_decl))
          proc_to_repair no_pos in
      let n_iproc = I.repair_proc proc_to_repair n_iprog.I.prog_exp_decls in

      let () = x_tinfo_hp (add_str "exp_decls: " (Iprinter.string_of_exp_decl_list))
      n_iprog.I.prog_exp_decls no_pos in
      let () = x_binfo_hp (add_str "new proc: " (Iprinter.string_of_proc_decl))
          n_iproc no_pos in
      let n_proc_decls =
        List.map (fun x -> if (x.I.proc_name = n_iproc.proc_name)
                   then n_iproc else x) iprog.prog_proc_decls in
      let n_prog = {iprog with prog_proc_decls = n_proc_decls} in
      let n_cprog, _ = Astsimp.trans_prog n_prog in
      try
        let () = Typechecker.check_prog_wrapper n_iprog n_cprog in
        Some n_prog
      with _ ->
        begin
          let n_iprog = Typechecker.update_iprog_exp_defns iprog
              neg_prog.Cast.prog_exp_decls in
          let n_iproc = I.repair_proc proc_to_repair n_iprog.I.prog_exp_decls in
          let n_proc_decls =
            List.map (fun x -> if (x.I.proc_name = n_iproc.proc_name)
                       then n_iproc else x) n_iprog.prog_proc_decls in
          let () = x_tinfo_hp (add_str "new proc: " (Iprinter.string_of_proc_decl))
          n_iproc no_pos in
          let n_prog = {n_iprog with prog_proc_decls = n_proc_decls} in
          let n_cprog, _ = Astsimp.trans_prog n_prog in
          try
            let () = Typechecker.check_prog_wrapper n_iprog n_cprog in
            Some n_prog
          with _ -> None
        end


let repair_prog_with_templ iprog cond_op =
  let () = Typechecker.repairing_ents := [] in
  let () = Typechecker.proc_to_repair := None in
  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false
  in
  let () = x_tinfo_pp "marking \n" no_pos in
  let cprog, _ = Astsimp.trans_prog iprog in
  try
    let () = Typechecker.check_prog_wrapper iprog cprog in
    let () = next_proc := false in
    None
  with _ as e ->
      let ents = !Typechecker.repairing_ents in
      try
        begin
          let sb_res = Songbirdfront.get_repair_candidate cprog ents cond_op in
          match sb_res with
          | None -> let () = next_proc := false in
            None
          | Some (nprog, repaired_exp, _, _) ->
            match !Typechecker.proc_to_repair with
            | None -> let () = next_proc := false in
              None
            | Some proc_name_to_repair ->
              let exp_decls = nprog.Cast.prog_exp_decls in
              let n_iprog = Typechecker.update_iprog_exp_defns iprog exp_decls in
              let proc_to_repair = List.find (fun x ->
                  let params = x.I.proc_args in
                  let typs = List.map (fun x -> x.I.param_type) params in
                  let mingled_name = Cast.mingle_name x.I.proc_name typs in
                  contains proc_name_to_repair mingled_name)
                  n_iprog.I.prog_proc_decls in
              let n_iproc = I.repair_proc proc_to_repair
                  n_iprog.I.prog_exp_decls in
              let () = x_binfo_hp (add_str "new proc_body:" (Iprinter.string_of_exp))
                  (Gen.unsome n_iproc.I.proc_body) no_pos in
              let n_proc_decls =
                List.map (fun x -> if (x.I.proc_name = n_iproc.proc_name)
                           then n_iproc else x) iprog.prog_proc_decls in
              let nn_iprog = {iprog with prog_proc_decls = n_proc_decls} in
              let nn_cprog, _ = Astsimp.trans_prog nn_iprog in
              let current_proc = !Typechecker.proc_to_repair in
              try
                let () = Typechecker.check_prog_wrapper nn_iprog nn_cprog
                in
                let () = next_proc := false in
                Some (nn_iprog, repaired_exp)
              with _ ->
                let () = x_tinfo_pp "marking \n" no_pos in
                let next_proc_name = !Typechecker.proc_to_repair in
                if (String.compare (Gen.unsome current_proc)
                      (Gen.unsome next_proc_name) != 0) then
                  let () = next_proc := true in
                  Some (nn_iprog, repaired_exp)
                else
                  let () = next_proc := false in
                  None
                (* if cond_op == None then None
                 * else
                 *   begin
                 *     let n_iprog = Typechecker.update_iprog_exp_defns iprog
                 *         neg_prog.Cast.prog_exp_decls in
                 *     let proc_to_repair = List.find (fun x ->
                 *         let params = x.I.proc_args in
                 *         let typs = List.map (fun x -> x.I.param_type) params in
                 *         let mingled_name = Cast.mingle_name x.I.proc_name typs in
                 *         contains proc_name_to_repair mingled_name)
                 *         n_iprog.I.prog_proc_decls in
                 *     let n_iproc = I.repair_proc proc_to_repair
                 *         n_iprog.I.prog_exp_decls in
                 *     let () = x_binfo_hp (add_str "new proc:" (Iprinter.string_of_proc_decl))
                 *         n_iproc no_pos in
                 *     let n_proc_decls =
                 *       List.map (fun x -> if (x.I.proc_name = n_iproc.proc_name)
                 *                  then n_iproc else x) iprog.prog_proc_decls in
                 *     let nn_iprog = {iprog with prog_proc_decls = n_proc_decls} in
                 *     let nn_cprog, _ = Astsimp.trans_prog nn_iprog in
                 *     try
                 *       let () = Typechecker.check_prog_wrapper nn_iprog nn_cprog in
                 *       Some (nn_iprog, repaired_exp)
                 *     with _ -> None
                 *   end *)
        end
      with _ ->
        let () = next_proc := false in
        None

let create_templ_proc proc replaced_exp vars heuristic =
  let var_names = List.map fst vars in
  let () = x_tinfo_hp (add_str "exp input: " (Iprinter.string_of_exp))
      (replaced_exp) no_pos in
  let () = x_tinfo_hp (add_str "exp_vars input: " (pr_list pr_id)) var_names no_pos in
  let (n_exp, replaced_vars, _) =
    I.replace_assign_exp replaced_exp var_names heuristic in
  let () = x_tinfo_hp (add_str "replaced_vars: " (pr_list pr_id))
      replaced_vars no_pos in
  let () = x_tinfo_hp (add_str "n_exp: " (Iprinter.string_of_exp)) n_exp no_pos
  in
  (* None *)
  if n_exp = replaced_exp then
    let () = next_proc := false in
    None
  (* else if (List.length replaced_pos_list > 1) then None *)
  else
    let exp_loc = I.get_exp_pos replaced_exp in
    (* let unk_vars = List.filter (fun (x,y) -> List.mem x replaced_vars) vars in *)
    (* let unk_vars = List.map (fun (x,y) -> (y,x)) unk_vars in *)

    let unk_vars = List.map (fun x -> (Globals.Int, x)) replaced_vars in
    (* let is_user_defined_type unk_vars =
     *   List.exists (fun (x, y) -> match x with
     *       | Int -> false
     *       | _ -> true) unk_vars
     * in
     * if is_user_defined_type unk_vars then None
     * else *)
    let unk_exp = I.mk_exp_decl unk_vars in
    let n_proc_body = Some (I.replace_exp_with_loc (Gen.unsome proc.I.proc_body)
                              n_exp exp_loc) in
    let n_proc = {proc with proc_body = n_proc_body} in
    (* let replaced_pos = List.hd replaced_pos_list in *)
    Some (n_proc, unk_exp, exp_loc)

let repair_one_statement iprog proc exp is_cond vars heuristic =
  let () = x_tinfo_hp (add_str "exp candidate: " (Iprinter.string_of_exp))
      exp no_pos in
  if !stop then
    let () = next_proc := false in
    None
  else
    let n_proc_exp = create_templ_proc proc exp vars heuristic
    in
    (* None *)
    let () = x_dinfo_pp "marking \n" no_pos in
    match n_proc_exp with
    | None -> let () = next_proc := false in
      None
    | Some (templ_proc, unk_exp, replaced_pos) ->
      let () = x_tinfo_hp (add_str "new proc: " (Iprinter.string_of_exp))
          (Gen.unsome templ_proc.I.proc_body) no_pos in
      (* None *)

      let var_names = List.map fst vars in
      let var_typs = List.map snd vars in
      let n_proc_decls =
        List.map (fun x -> if (x.I.proc_name = templ_proc.I.proc_name)
                   then templ_proc else x) iprog.I.prog_proc_decls in
      let n_iprog = {iprog with I.prog_proc_decls = n_proc_decls} in
      let () = x_tinfo_hp (add_str "exp_decl: " (Iprinter.string_of_exp_decl))
          unk_exp no_pos in
      let input_repair_proc = {n_iprog with I.prog_exp_decls = [unk_exp]} in
      (* None *)
      try
        let _ = Astsimp.trans_prog input_repair_proc in
        let repair_res = repair_prog_with_templ input_repair_proc is_cond in
        match repair_res with
        | None -> None
        | Some (res_iprog, repaired_exp) ->
          let repaired_proc = List.find (fun x -> x.I.proc_name = proc.I.proc_name)
              res_iprog.I.prog_proc_decls in
          let () = x_tinfo_hp
              (add_str "best repaired proc" (Iprinter.string_of_exp))
              (Gen.unsome repaired_proc.I.proc_body) no_pos in
          let exp_pos = I.get_exp_pos exp in
          let score = 100 * (10 - (List.length vars))
                      + exp_pos.VarGen.start_pos.Lexing.pos_lnum in
          let () = x_dinfo_hp (add_str "score:" (string_of_int)) score no_pos in
          let () = stop := true in
          Some (score, res_iprog, replaced_pos, repaired_exp)
      with _ ->
        let () = next_proc := false in
        None

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

let repair_by_mutation iprog repairing_proc =
  let () = x_tinfo_pp "marking \n" no_pos in
  let proc_body = Gen.unsome repairing_proc.I.proc_body in
  let logical_locs = I.collect_logical_locs proc_body in
  let candidate_procs = List.map (fun x -> I.mutate_prog x repairing_proc)
      logical_locs in
  let check_candidate iprog mutated_proc =
    let () = x_tinfo_hp
        (add_str "candidate proc" (Iprinter.string_of_exp))
        (Gen.unsome mutated_proc.I.proc_body) no_pos in
    if (!stop) then None
    else
      let n_proc_decls =
        List.map (fun x -> if (x.I.proc_name = mutated_proc.I.proc_name)
                   then mutated_proc else x) iprog.I.prog_proc_decls in
      let n_iprog = {iprog with I.prog_proc_decls = n_proc_decls} in
      let n_cprog, _ = Astsimp.trans_prog n_iprog in
      try
        let () = Typechecker.check_prog_wrapper n_iprog n_cprog in
        let () = stop := true in
        let () = x_binfo_hp
            (add_str "best repaired proc" (Iprinter.string_of_exp))
            (Gen.unsome mutated_proc.I.proc_body) no_pos in
        Some n_iprog
      with _ -> None
  in
  List.map (fun x -> check_candidate iprog x) candidate_procs

let start_repair iprog =
  (* let iprog = I.normalize_prog iprog in
   * let () = x_tinfo_hp (add_str "normalized procs: " (pr_list Iprinter.string_of_proc_decl))
   *         iprog.I.prog_proc_decls no_pos in *)
  let cprog, _ = Astsimp.trans_prog iprog in

  match !Typechecker.proc_to_repair with
  | None ->
    let () = next_proc := false in
    None
  | Some proc_name_to_repair ->
    let () = x_tinfo_pp "marking \n" no_pos in
    let proc_name_to_repair = Cast.unmingle_name proc_name_to_repair in
    let () = x_tinfo_hp (add_str "proc_name: " pr_id) (proc_name_to_repair)
        no_pos in
    let proc_to_repair = List.find (fun x -> String.compare (x.I.proc_name)
                                       proc_name_to_repair == 0)
        iprog.I.prog_proc_decls in
    let () = x_tinfo_hp (add_str "proc: " (Iprinter.string_of_proc_decl))
          proc_to_repair no_pos in
    let candidate_exp_list =
      I.list_of_candidate_exp (Gen.unsome proc_to_repair.proc_body) in
    let var_decls = I.list_vars (Gen.unsome proc_to_repair.proc_body) iprog in
    let () = x_tinfo_hp (add_str "var decls: " (pr_list (pr_pair pr_id Globals.string_of_typ)))
        var_decls no_pos in
    let filter_candidate (x, y) =
      match x with
      | I.Var var ->
        begin
          try
            let (v, typ) = List.find (fun (x, _) ->
                ExtLib.String.exists var.I.exp_var_name x) var_decls in
            if typ == Globals.Int then true
            else false
          with _ -> true
        end
      | _ -> true
    in
    (* let candidate_exp_list = List.filter filter_candidate candidate_exp_list in *)
    let () = x_tinfo_hp (add_str "candidate exps: " (pr_list Iprinter.string_of_exp))
        (candidate_exp_list |> List.map fst) no_pos in
    (* None *)

    let vars = proc_to_repair.I.proc_args in
    let vars = List.map (fun x -> (x.I.param_name, x.I.param_type)) vars in
    let vars = vars @ var_decls in
    let vars = List.filter (fun (x, y) -> match y with
        | Int -> true
        | _ -> false) vars in
    let repair_res_list =
      List.map (fun stmt -> repair_one_statement iprog proc_to_repair (fst stmt)
                   (snd stmt) vars false) candidate_exp_list in
    let h_repair_res_list = List.filter(fun x -> x != None) repair_res_list in
    let h_repair_res_list = List.map Gen.unsome h_repair_res_list in
    let best_res = get_best_repair h_repair_res_list in
    match best_res with
    | None ->
      let mutated_res = repair_by_mutation iprog proc_to_repair in
      let mutated_res = List.filter(fun x -> x != None) mutated_res in
      let mutated_res = List.map Gen.unsome mutated_res in
      if mutated_res = [] then
        let () = next_proc := false in
        None
      else Some (List.hd mutated_res)
    | Some (_, best_r_prog, pos, repaired_exp) ->
      let repaired_proc = List.find (fun x -> x.I.proc_name = proc_to_repair.proc_name)
          best_r_prog.I.prog_proc_decls in
      let () = x_binfo_hp
          (add_str "best repaired proc" (Iprinter.string_of_exp))
          (Gen.unsome repaired_proc.I.proc_body) no_pos in
      let () =
        x_tinfo_hp (add_str "templ: "
                      (Cprinter.poly_string_of_pr Cprinter.pr_formula_exp))
          repaired_exp no_pos in
      Some best_r_prog
      (* Some (best_r_prog, pos, repaired_exp) *)

let rec start_repair_wrapper iprog =
  let tmp = start_repair iprog in
  let () = x_tinfo_hp (add_str "next_proc: " string_of_bool) (!next_proc) no_pos in
  if (!next_proc) then
    let () = stop := false in
    start_repair_wrapper iprog
  else tmp
