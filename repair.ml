#include "xdebug.cppo"
open VarGen
open Printf
open Gen.Basic
open Globals
open Iast

module C = Cast
module CP = Cpure
module CF = Cformula

let stop = ref false
let next_proc = ref false
let pr_proc = Iprinter.string_of_proc_decl

let rec replace_exp_with_loc exp n_exp loc =
  match exp with
  | Assign e ->
    if (e.exp_assign_pos = loc) then n_exp else
      let r_exp1 = replace_exp_with_loc e.exp_assign_lhs n_exp loc in
      let r_exp2 = replace_exp_with_loc e.exp_assign_rhs n_exp loc in
      Assign {e with exp_assign_lhs = r_exp1;
                     exp_assign_rhs = r_exp2}
  | Binary e ->
    begin
      match e.exp_binary_op with
      | OpEq
      | OpNeq
      | OpLt
      | OpLte
      | OpGt
      | OpGte ->
        let r_exp1 = replace_exp_with_loc e.exp_binary_oper1 n_exp loc in
        Binary {e with exp_binary_oper1 = r_exp1}
      | _ ->
        if e.exp_binary_pos = loc then n_exp else
          let r_exp1 = replace_exp_with_loc e.exp_binary_oper1 n_exp loc in
          let r_exp2 = replace_exp_with_loc e.exp_binary_oper2 n_exp loc in
          Binary {e with exp_binary_oper1 = r_exp1;
                         exp_binary_oper2 = r_exp2}
            end
  | Bind e ->
    if e.exp_bind_pos = loc then n_exp else
      let r_exp = replace_exp_with_loc e.exp_bind_body n_exp loc in
      Bind {e with exp_bind_body = r_exp}
  | Block e ->
    if e.exp_block_pos = loc then n_exp
    else
      let r_exp = replace_exp_with_loc e.exp_block_body n_exp loc in
      Block {e with exp_block_body = r_exp}
  | Cast e -> Cast {e with
                    exp_cast_body = replace_exp_with_loc e.exp_cast_body n_exp loc}
  | Cond e ->
    let r_cond = replace_exp_with_loc e.exp_cond_condition n_exp loc in
    let r_then_branch = replace_exp_with_loc e.exp_cond_then_arm n_exp loc in
    let r_else_branch = replace_exp_with_loc e.exp_cond_else_arm n_exp loc in
    Cond {e with exp_cond_condition = r_cond;
                 exp_cond_then_arm = r_then_branch;
                 exp_cond_else_arm = r_else_branch}
  | Catch e ->
    Catch {
      e with exp_catch_body = replace_exp_with_loc e.exp_catch_body n_exp loc }
  | IntLit e -> if (e.exp_int_lit_pos = loc) then n_exp else exp
  | Label (a, body) -> Label (a, replace_exp_with_loc body n_exp loc)
  | Member e ->
    Member {e with exp_member_base = replace_exp_with_loc e.exp_member_base n_exp loc}
  | New e ->
    exp
  | Return e ->
    (* exp *)
    let r_val = match e.exp_return_val with
      | None -> None
      | Some e -> Some (replace_exp_with_loc e n_exp loc)
    in Return {e with exp_return_val = r_val}
  | Seq e ->
    let r_e1 = replace_exp_with_loc e.exp_seq_exp1 n_exp loc in
    let r_e2 = replace_exp_with_loc e.exp_seq_exp2 n_exp loc in
    Seq {e with exp_seq_exp1 = r_e1;
                exp_seq_exp2 = r_e2}
  | Unary e ->
    let n_e = replace_exp_with_loc e.exp_unary_exp n_exp loc in
    Unary {e with exp_unary_exp = n_e}
  | Var v -> if (v.exp_var_pos = loc) then n_exp else exp
  | _ -> exp

let replace_assign_exp exp vars heuristic =
  let rec prelist a b = match a, b with
    | [], _ -> true
    | _, [] -> false
    | h::t, h'::t' -> h = h' && prelist t t'
  in
  let rec sublist a b = match a, b with
    | [], _ -> true
    | _, [] -> false
    | h::_, h'::t' -> (h = h' && prelist a b) || sublist a t'
  in
  let is_cond exp = match exp with
    | Binary e ->
      begin
        match e.exp_binary_op with
        | OpEq
        | OpNeq
        | OpLt
        | OpLte
        | OpGte
        | OpGt ->
          true
        | _ -> false
      end
    | _ -> false
  in
  let is_unk_exp exp = match exp with
    | UnkExp _ -> true
    | _ -> false
  in
  let rec replace exp vars =
    let exp_vars = collect_vars_exp exp in
    let () = x_tinfo_hp (add_str "exp_vars: " (pr_list pr_id)) exp_vars no_pos
    in
    if (sublist exp_vars vars & not (is_cond exp)) then
      (mk_unk_exp exp_vars (get_exp_pos exp), exp_vars, [get_exp_pos exp])
    else
      match exp with
      | Binary b ->
        if is_cond exp then
          let (a1, b1, c1) = replace b.exp_binary_oper1 vars in
          (Binary { b with exp_binary_oper1 = a1}, b1, c1)
        else
          let (a1, b1, c1) = replace b.exp_binary_oper1 vars in
          let (a2, b2, c2) = replace b.exp_binary_oper2 vars in
          if (is_unk_exp a1 && is_unk_exp a2) then
            (combine_unk_exp a1 a2 b.exp_binary_pos, b1@b2, c1@c2)
          else
            (Binary {
                b with exp_binary_oper1 = a1;
                       exp_binary_oper2 = a2;
              }, b1 @ b2, c1@c2)
      | _ -> (exp, [], [])

  in
  let () = x_tinfo_hp (add_str "vars: " (pr_list pr_id)) vars no_pos in
  let exp_vars = collect_vars_exp exp in
  if (exp_vars == []) then
    (mk_unk_exp [] (get_exp_pos exp), [], [get_exp_pos exp])
  else replace exp vars

(* Normalize arithmetic expression *)
let normalize_arith_exp exp =
  let rec is_compose_exp exp = match exp with
    | Binary e -> true
    | Unary e -> is_compose_exp e.exp_unary_exp
    | Block e -> is_compose_exp e.exp_block_body
    | _ -> false
  in
  let rec aux exp = match exp with
    | Binary e ->
      begin
        match e.exp_binary_op with
        | OpLogicalAnd
        | OpLogicalOr ->
          let (e1, list1) =
            if (is_compose_exp e.exp_binary_oper1) then
              aux e.exp_binary_oper1
            else (e.exp_binary_oper1, []) in
          let (e2, list2) =
            if (is_compose_exp e.exp_binary_oper2) then
              aux e.exp_binary_oper2
            else (e.exp_binary_oper2, []) in
          let n_exp = Binary {e with exp_binary_oper1 = e1;
                                     exp_binary_oper2 = e2}
          in (n_exp, list1@list2)
        | OpEq
        | OpNeq
        | OpLt
        | OpLte
        | OpGt
        | OpGte -> if (is_compose_exp e.exp_binary_oper1) then
            let loc = get_exp_pos e.exp_binary_oper1 in
            let n_name = "exp_" ^ (VarGen.string_of_loc_repair loc) in
            let var = Var {
                exp_var_name = n_name;
                exp_var_pos = loc;
              } in
            let n_exp = Binary {e with exp_binary_oper1 = var} in
            (n_exp, [(n_name, e.exp_binary_oper1)])
          else (exp, [])
        | _ -> (exp, [])
    end
    | Assign e ->
      let (e1, list1) = aux e.exp_assign_rhs in
      (Assign {e with exp_assign_rhs = e1}, list1)
    | Block b ->
      let (e1, l1) = aux b.exp_block_body in
      (Block {b with exp_block_body = e1}, l1)
    | Cond e ->
      let (e1, l1) = aux e.exp_cond_condition in
      let (e2, l2) = aux e.exp_cond_then_arm in
      let (e3, l3) = aux e.exp_cond_else_arm in
      (Cond {e with exp_cond_condition = e1;
                    exp_cond_then_arm = e2;
                    exp_cond_else_arm = e3}, l1@l2@l3)
    | Label (a, e) ->
      let (e1, l1) = aux e in
      (Label (a, e1), l1)
    | Seq e ->
      let (e1, l1) = aux e.exp_seq_exp1 in
      let (e2, l2) = aux e.exp_seq_exp2 in
      (Seq {e with exp_seq_exp1 = e1; exp_seq_exp2 = e2}, l1@l2)
    | Unary e ->
      let (e1, l1) = aux e.exp_unary_exp in
      (Unary {e with exp_unary_exp = e1}, l1)
    | _ -> (exp, [])
  in
  let (n_exp, assign_list) = aux exp in

  let collect_local_var_decls exp =
    let rec aux exp list = match exp with
      | Block e -> aux e.exp_block_body list
      | Seq e ->
        let list1 = aux e.exp_seq_exp1 list in
        aux e.exp_seq_exp2 list1
      | VarDecl _ -> [exp] @ list
      | Label (_, e) -> aux e list
      | _ -> list
    in List.rev (aux exp [])
  in
  let collect_main exp =
    let rec aux exp list = match exp with
      | Block e -> aux e.exp_block_body list
      | Seq e ->
        let list1 = aux e.exp_seq_exp1 list in
        aux e.exp_seq_exp2 list1
      | VarDecl _ -> list
      | Label (_, e) -> aux e list
      | _ -> [exp] @ list
    in List.rev (aux exp [])
  in
  let var_decls = collect_local_var_decls n_exp in
  let pr_exps = pr_list Iprinter.string_of_exp in
  let pr_exp = Iprinter.string_of_exp in

  let () = x_tinfo_hp (add_str "n_exp: " pr_exp) n_exp no_pos in
  let () = x_tinfo_hp (add_str "var decls: " pr_exps) var_decls no_pos in

  let rec find_main exp vars = match exp with
    | Block e -> find_main e.exp_block_body vars
    | Label (_, el) -> find_main el vars
    | Seq e ->
      if (List.mem e.exp_seq_exp1 vars) then e.exp_seq_exp2
      else if (List.mem e.exp_seq_exp2 vars) then e.exp_seq_exp1
      else
        let e1 = find_main e.exp_seq_exp1 vars in
        let e2 = find_main e.exp_seq_exp2 vars in
        Seq {e with exp_seq_exp1 = e1;
                    exp_seq_exp2 = e2}
    | _ -> exp
  in
  (* let main_exp = find_main n_exp var_decls in *)
  let rec sequencing_exp exp_list = match exp_list with
    | [] -> report_error no_pos "cannot sequencing empty list"
    | [x] -> x
    | h::t -> mkSeq h (sequencing_exp t) no_pos
  in
  let main_exp = sequencing_exp (collect_main n_exp) in
  let () = x_tinfo_hp (add_str "main: " pr_exp) main_exp no_pos in
  let assign_list = Gen.BList.remove_dups_eq (fun a b ->
      String.compare (fst a) (fst b) == 0) assign_list in
  let attached_exp = List.fold_left(fun a (b, c) ->
      let var_decl = VarDecl {
          exp_var_decl_type = int_type;
          exp_var_decl_decls = [(b, None, no_pos)];
          exp_var_decl_pos = no_pos
        }
      in
      let assign = Assign {
          exp_assign_op = OpAssign;
          exp_assign_lhs = Var {
              exp_var_name = b;
              exp_var_pos = no_pos;
            };
          exp_assign_rhs = c;
          exp_assign_path_id = None;
          exp_assign_pos = no_pos
        } in
      let seq = Seq {
          exp_seq_exp1 = var_decl;
          exp_seq_exp2 = assign;
          exp_seq_pos = no_pos
        }
      in
      Seq {
        exp_seq_exp1 = seq;
        exp_seq_exp2 = a;
        exp_seq_pos = no_pos
      }
    ) main_exp assign_list in
  let attached_exp = if (var_decls = []) then attached_exp
    else
      let var_decls = sequencing_exp var_decls in
      mkSeq var_decls attached_exp no_pos
  in
  attached_exp

(* Normalize logical exp *)
(* e.g x < y <-> x - y < 0 *)
let rec normalize_logical_exp exp = match exp with
  | Binary e ->
    begin
      match e.exp_binary_op with
      | OpLt
      | OpLte
      | OpGt
      | OpGte ->
        if not(is_zero_exp e.exp_binary_oper2) then
          let e_oper1 = e.exp_binary_oper1 in
          let e_oper2 = e.exp_binary_oper2 in
          let e_pos = e.exp_binary_pos in
          let e1 = mkBinary OpMinus e_oper1 e_oper2 None e_pos in
          Binary { e with exp_binary_oper1 = e1;
                          exp_binary_oper2 = mkIntLit 0 no_pos;
                          exp_binary_pos = no_pos }
        else exp
      | OpLogicalAnd
      | OpLogicalOr ->
        let e_1 = normalize_logical_exp e.exp_binary_oper1 in
        let e_2 = normalize_logical_exp e.exp_binary_oper2 in
        Binary { e with exp_binary_oper1 = e_1;
                        exp_binary_oper2 = e_2 }
      | _ -> exp
    end
  | Assign e ->
    let rhs_e = normalize_logical_exp e.exp_assign_rhs in
    let pr_exp = Iprinter.string_of_exp in
    let () = x_tinfo_hp (add_str "rhs: " pr_exp) e.exp_assign_rhs no_pos in
    Assign {e with exp_assign_rhs = rhs_e}
  | Block b -> Block {b with exp_block_body = normalize_logical_exp b.exp_block_body}
  | Cond e ->
    let e_cond = normalize_logical_exp e.exp_cond_condition in
    let e_then = normalize_logical_exp e.exp_cond_then_arm in
    let e_else = normalize_logical_exp e.exp_cond_else_arm in
    Cond {e with exp_cond_condition = e_cond;
                 exp_cond_then_arm = e_then;
                 exp_cond_else_arm = e_else}
  | Label (a, e) -> Label (a, normalize_logical_exp e)
  | Seq e ->
    let e_1 = normalize_logical_exp e.exp_seq_exp1 in
    let e_2 = normalize_logical_exp e.exp_seq_exp2 in
    Seq {e with exp_seq_exp1 = e_1;
                exp_seq_exp2 = e_2}
  | Unary e ->
    let e1 = normalize_logical_exp e.exp_unary_exp in
    Unary {e with exp_unary_exp = e1}
  | CallNRecv e ->
    let args = e.exp_call_nrecv_arguments in
    let n_args = List.map normalize_logical_exp args in
    CallNRecv {e with exp_call_nrecv_arguments = n_args}
  | CallRecv e ->
    let args = e.exp_call_recv_arguments in
    let n_args = List.map normalize_logical_exp args in
    CallRecv {e with exp_call_recv_arguments = n_args}
  | _ -> exp

(* normalize iast procedures *)
let normalize_proc iprog proc_decl =
  let n_proc_body = match proc_decl.proc_body with
    | None -> None
    | Some body_exp ->
      let n_exp = body_exp in
      let n_exp = normalize_logical_exp body_exp in
      (* let n_exp = normalize_arith_exp n_exp in *)
      Some n_exp
  in
  let nprog = {proc_decl with proc_body = n_proc_body} in
  nprog

(* normalize iast program input for repair*)
let normalize_prog iprog =
  {iprog with prog_proc_decls = List.map (fun x -> normalize_proc iprog x) iprog.prog_proc_decls}

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
  let () = x_binfo_pp "marking \n" no_pos in
  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false
  in
  let sb_res = Songbird.get_repair_candidate cprog ents None in
  match sb_res with
  | None -> None
  | Some (nprog, _, _, _) ->
    match !Typechecker.proc_to_repair with
    | None -> None
    | Some proc_name_to_repair ->
      let n_iprog = Typechecker.update_iprog_exp_defns iprog nprog.Cast.prog_exp_decls in
      let () = x_binfo_pp "marking \n" no_pos in
      let () = x_binfo_pp proc_name_to_repair no_pos in
      let proc_to_repair = List.find (fun x ->
          let params = x.proc_args in
          let typs = List.map (fun x -> x.param_type) params in
          let mingled_name = Cast.mingle_name x.proc_name typs in
          contains proc_name_to_repair mingled_name)
          iprog.prog_proc_decls in
      let () = x_binfo_hp (add_str "old proc: " (Iprinter.string_of_proc_decl))
          proc_to_repair no_pos in
      let n_iproc = repair_proc proc_to_repair n_iprog.prog_exp_decls in

      let () = x_binfo_hp (add_str "exp_decls: " (Iprinter.string_of_exp_decl_list))
      n_iprog.prog_exp_decls no_pos in
      let () = x_binfo_hp (add_str "new proc: " (Iprinter.string_of_proc_decl))
          n_iproc no_pos in
      let n_proc_decls =
        List.map (fun x -> if (x.proc_name = n_iproc.proc_name)
                   then n_iproc else x) iprog.prog_proc_decls in
      let n_prog = {iprog with prog_proc_decls = n_proc_decls} in
      let n_cprog, _ = Astsimp.trans_prog n_prog in
      try
        let () = Typechecker.check_prog_wrapper n_iprog n_cprog in
        Some n_prog
      with _ -> None
        (* begin
         *   let n_iprog = Typechecker.update_iprog_exp_defns iprog
         *       neg_prog.Cast.prog_exp_decls in
         *   let n_iproc = repair_proc proc_to_repair n_iprog.prog_exp_decls in
         *   let n_proc_decls =
         *     List.map (fun x -> if (x.proc_name = n_iproc.proc_name)
         *                then n_iproc else x) n_iprog.prog_proc_decls in
         *   let () = x_tinfo_hp (add_str "new proc: " (Iprinter.string_of_proc_decl))
         *   n_iproc no_pos in
         *   let n_prog = {n_iprog with prog_proc_decls = n_proc_decls} in
         *   let n_cprog, _ = Astsimp.trans_prog n_prog in
         *   try
         *     let () = Typechecker.check_prog_wrapper n_iprog n_cprog in
         *     Some n_prog
         *   with _ -> None
         * end *)


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
          let sb_res = Songbird.get_repair_candidate cprog ents cond_op in
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
                  let params = x.proc_args in
                  let typs = List.map (fun x -> x.param_type) params in
                  let mingled_name = Cast.mingle_name x.proc_name typs in
                  contains proc_name_to_repair mingled_name)
                  n_iprog.prog_proc_decls in
              let n_iproc = repair_proc proc_to_repair
                  n_iprog.prog_exp_decls in
              let () = x_tinfo_hp (add_str "new proc_body:" (Iprinter.string_of_exp))
                  (Gen.unsome n_iproc.proc_body) no_pos in
              let n_proc_decls =
                List.map (fun x -> if (x.proc_name = n_iproc.proc_name)
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

let create_tmpl_proc proc replaced_exp vars heuristic =
  let var_names = List.map fst vars in
  let pr_exp = Iprinter.string_of_exp_repair in
  let () = x_tinfo_hp (add_str "exp input: " pr_exp) (replaced_exp) no_pos in
  let () = x_tinfo_hp (add_str "exp_vars input: " (pr_list pr_id)) var_names no_pos in
  let (n_exp, replaced_vars, _) =
    replace_assign_exp replaced_exp var_names heuristic in
  let () = x_tinfo_hp (add_str "replaced_vars: " (pr_list pr_id))
      replaced_vars no_pos in
  let () = x_tinfo_hp (add_str "n_exp: " (Iprinter.string_of_exp)) n_exp no_pos
  in
  (* None *)
  if n_exp = replaced_exp then
    let () = next_proc := false in
    None
  else
    let exp_loc = get_exp_pos replaced_exp in
    let unk_vars = List.map (fun x -> (Globals.Int, x)) replaced_vars in
    let unk_exp = mk_exp_decl unk_vars in
    let n_proc_body = Some (replace_exp_with_loc (Gen.unsome proc.proc_body)
                              n_exp exp_loc) in
    let n_proc = {proc with proc_body = n_proc_body} in
    Some (n_proc, unk_exp, exp_loc)

let repair_one_statement iprog proc exp is_cond vars heuristic =
  let pr_exp = Iprinter.string_of_exp_repair in
  let () = x_tinfo_hp (add_str "exp candidate: " pr_exp)
      exp no_pos in
  if !stop then
    let () = next_proc := false in
    None
  else
    let n_proc_exp = create_tmpl_proc proc exp vars heuristic
    in
    let () = x_dinfo_pp "marking \n" no_pos in
    match n_proc_exp with
    | None -> let () = next_proc := false in
      None
    | Some (templ_proc, unk_exp, replaced_pos) ->
      let () = x_tinfo_hp (add_str "new proc: " pr_exp)
          (Gen.unsome templ_proc.proc_body) no_pos in
      let var_names = List.map fst vars in
      let var_typs = List.map snd vars in
      let n_proc_decls =
        List.map (fun x -> if (x.proc_name = templ_proc.proc_name)
                   then templ_proc else x) iprog.prog_proc_decls in
      let n_iprog = {iprog with prog_proc_decls = n_proc_decls} in
      let () = x_tinfo_hp (add_str "exp_decl: " (Iprinter.string_of_exp_decl))
          unk_exp no_pos in
      let input_repair_proc = {n_iprog with prog_exp_decls = [unk_exp]} in
      try
        let _ = Astsimp.trans_prog input_repair_proc in
        let repair_res = repair_prog_with_templ input_repair_proc is_cond in
        match repair_res with
        | None -> None
        | Some (res_iprog, repaired_exp) ->
          let repaired_proc = List.find (fun x -> x.proc_name = proc.proc_name)
              res_iprog.prog_proc_decls in
          let () = x_tinfo_hp
              (add_str "best repaired proc" (Iprinter.string_of_exp_repair))
              (Gen.unsome repaired_proc.proc_body) no_pos in
          let exp_pos = get_exp_pos exp in
          let score = 100 * (10 - (List.length vars))
                      + exp_pos.VarGen.start_pos.Lexing.pos_lnum in
          let () = x_dinfo_hp (add_str "score:" (string_of_int)) score no_pos in
          let () = stop := true in
          Some (score, res_iprog, replaced_pos, repaired_exp)
      with _ ->
        let () = next_proc := false in
        None

let repair_one_heap_stmt iprog proc stmt =
  let n_proc = create_tmpl_hproc proc stmt in
  let pr_exp = Iprinter.string_of_exp_repair in
  let () = x_binfo_hp (add_str "n_proc" pr_exp) (Gen.unsome n_proc.proc_body) no_pos in
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
  let proc_body = Gen.unsome repairing_proc.proc_body in
  let logical_locs = collect_logical_locs proc_body in
  let candidate_procs = List.map (fun x -> mutate_prog x repairing_proc)
      logical_locs in
  let constant_candidates =
    List.map (fun x -> mk_constant x repairing_proc) logical_locs in
  let candidates = candidate_procs @ constant_candidates in
  let check_candidate iprog mutated_proc =
    let () = x_tinfo_hp
        (add_str "candidate proc" (Iprinter.string_of_exp))
        (Gen.unsome mutated_proc.proc_body) no_pos in
    if (!stop) then None
    else
      let n_proc_decls =
        List.map (fun x -> if (x.proc_name = mutated_proc.proc_name)
                   then mutated_proc else x) iprog.prog_proc_decls in
      let n_iprog = {iprog with prog_proc_decls = n_proc_decls} in
      let n_cprog, _ = Astsimp.trans_prog n_iprog in
      try
        let () = Typechecker.check_prog_wrapper n_iprog n_cprog in
        let () = stop := true in
        let () = x_tinfo_hp
            (add_str "best repaired proc" (Iprinter.string_of_exp_repair))
            (Gen.unsome mutated_proc.proc_body) no_pos in
        Some n_iprog
      with _ -> None
  in
  List.map (fun x -> check_candidate iprog x) candidates

let synthesize (pre:CF.formula) (post:CF.formula) (vars:CP.spec_var list) =
  let pr_formula = Cprinter.string_of_formula in
  let () = x_binfo_hp (add_str "pre: " pr_formula) pre no_pos in
  let () = x_binfo_hp (add_str "post: " pr_formula) post no_pos in
  let goal = Synthesis.mk_goal pre post vars in
  let _ = Synthesizer.synthesize_one_goal goal in
  None

let start_repair iprog =
  let cprog, _ = Astsimp.trans_prog iprog in
  let pr_exps = pr_list Iprinter.string_of_exp in

  match (!Typechecker.proc_to_repair) with
  | (Some proc_name_to_repair) ->
    let proc_name_to_repair = Cast.unmingle_name proc_name_to_repair in
    let () = x_binfo_hp (add_str "proc_name: " pr_id) (proc_name_to_repair)
        no_pos in
    let () = Globals.start_repair := true in
    let proc_to_repair = List.find (fun x -> String.compare (x.proc_name)
                                       proc_name_to_repair == 0)
        iprog.prog_proc_decls in
    let () = x_tinfo_hp (add_str "proc: " pr_proc) proc_to_repair no_pos in
    let cands = get_stmt_candidates (Gen.unsome proc_to_repair.proc_body) in
    let () = x_binfo_hp (add_str "candidates: " pr_exps) cands no_pos in
    let var_x = CP.SpecVar (Named "node", "x", VarGen.Unprimed) in
    let var_y = CP.SpecVar (Named "node", "y", VarGen.Unprimed) in
    let var_q = CP.SpecVar (Named "node", "q", VarGen.Unprimed) in
    let var_n1 = CP.SpecVar (Int, "n1", VarGen.Unprimed) in
    let var_n2 = CP.SpecVar (Int, "n2", VarGen.Unprimed) in
    let one = CP.mkIConst 1 no_pos in
    (* let pre =
     *   let node_x = CF.mkDataNode var_x "node" [var_q] no_pos in
     *   let pure_eq1 = CP.mkNull var_q no_pos in
     *   let pure_eq2 = CP.mkEqExp (CP.mkVar var_n1 no_pos) one no_pos in
     *   (\* let node_y = CF.mkDataNode var_y "node" [var_b] no_pos in *\)
     *   let node_y = CF.mkViewNode var_y "ll" [var_n2] no_pos in
     *   let pure = CP.mkAnd pure_eq1 pure_eq2 no_pos in
     *   let ante_h = CF.mkStarH node_x node_y no_pos in
     *   CF.mkBase_simp ante_h (Mcpure.mix_of_pure pure)
     * in
     * let post =
     *   let var_n = CP.SpecVar (Int, "n", VarGen.Unprimed) in
     *   let n1_plus_n2 = CP.mkAdd (CP.mkVar var_n1 no_pos) (CP.mkVar var_n2 no_pos) no_pos in
     *   let pure = CP.mkEqExp (CP.mkVar var_n no_pos) n1_plus_n2 no_pos in
     *   let node_x = CF.mkViewNode var_x "ll" [var_n] no_pos in
     *   CF.mkBase_simp node_x (Mcpure.mix_of_pure pure)
     * in *)
    (* pre: : x::node<q>@M * y::ll<n2>@M&q=null & n1=1 *)
    (* post: : x::ll<n>@M&n=n1+n2&{FLOW,(4,5)=__norm#E}[] *)

    let var_a = CP.SpecVar (Named "node", "a", VarGen.Unprimed) in
    let var_b = CP.SpecVar (Named "node", "b", VarGen.Unprimed) in
    let pre =
      let node_x = CF.mkDataNode var_x "node" [var_a] no_pos in
      let node_y = CF.mkDataNode var_y "node" [var_b] no_pos in
      let hf = CF.mkStarH node_x node_y no_pos in
      CF.mkBase_simp hf (Mcpure.mix_of_pure (CP.mkTrue no_pos)) in
    let post =
      let node_x = CF.mkDataNode var_x "node" [var_y] no_pos in
      let node_y = CF.mkDataNode var_y "node" [var_b] no_pos in
      let hf = CF.mkStarH node_x node_y no_pos in
      CF.mkBase_simp hf (Mcpure.mix_of_pure (CP.mkTrue no_pos)) in

    let _ = synthesize pre post [var_x; var_y] in
    (* let ante = CF.mkBase_simp node_a (Mcpure.mix_of_pure pure_eq) in *)

    (* let repair_res_list =
     *   List.map (fun stmt -> repair_one_heap_stmt iprog proc_to_repair stmt) cands in *)
    (* pre = x::node<a> *)
    (* post = x::node<b> *)
      (* | SpecVar of (typ * ident * primed) *)


    (* let h_repair_res_list = List.filter(fun x -> x != None) repair_res_list in
     * let h_repair_res_list = List.map Gen.unsome h_repair_res_list in
     * let best_res = get_best_repair h_repair_res_list in *)
    None
    (* begin
     *   match best_res with
     *   | None ->
     *     (* None *)
     *     let mutated_res = repair_by_mutation iprog proc_to_repair in
     *     let mutated_res = List.filter(fun x -> x != None) mutated_res in
     *     let mutated_res = List.map Gen.unsome mutated_res in
     *     if mutated_res = [] then
     *       let repair_res_list =
     *         List.map (fun stmt -> repair_one_statement iprog proc_to_repair (fst stmt)
     *                      (snd stmt) vars false) filtered in
     *       let h_repair_res_list = List.filter(fun x -> x != None) repair_res_list in
     *       let h_repair_res_list = List.map Gen.unsome h_repair_res_list in
     *       let best_res = get_best_repair h_repair_res_list in
     *       begin
     *         match best_res with
     *         | None ->
     *           let () = next_proc := false in
     *           None
     *         | Some (_, best_r_prog, pos, repaired_exp) ->
     *           let repaired_proc = List.find (fun x -> x.proc_name = proc_to_repair.proc_name)
     *               best_r_prog.prog_proc_decls in
     *           Some best_r_prog
     *       end
     *     else Some (List.hd mutated_res)
     *   | Some (_, best_r_prog, pos, repaired_exp) ->
     *     let repaired_proc = List.find (fun x -> x.proc_name = proc_to_repair.proc_name)
     *         best_r_prog.prog_proc_decls in
     *     let () = x_tinfo_hp
     *         (add_str "best repaired proc" (Iprinter.string_of_exp))
     *         (Gen.unsome repaired_proc.proc_body) no_pos in
     *     let () =
     *       x_tinfo_hp (add_str "templ: "
     *                     (Cprinter.poly_string_of_pr Cprinter.pr_formula_exp))
     *         repaired_exp no_pos in
     *     Some best_r_prog
     *     (* Some (best_r_prog, pos, repaired_exp) *)
     * end *)
  | _ ->
    let () = next_proc := false in
    None

let rec start_repair_wrapper iprog =
  let tmp = start_repair iprog in
  let () = x_tinfo_hp (add_str "next_proc: " string_of_bool) (!next_proc) no_pos in
  if (!next_proc) then
    let () = stop := false in
    let () = Globals.start_repair := false in
    start_repair_wrapper iprog
  else tmp
