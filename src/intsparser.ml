#include "xdebug.cppo"
open VarGen
open Globals
open Gen.Basic
open Iexp

module I = Iast
module IF = Iformula
module IP = Ipure

let empty_prog : I.prog_decl =
  { prog_include_decls = [];
    prog_data_decls = [];
    prog_global_var_decls = [];
    prog_logical_var_decls = [];
    prog_enum_decls = [];
    prog_view_decls = [];
    prog_func_decls = [];
    prog_rel_decls = [];
    prog_rel_ids = [];
    prog_templ_decls = [];
    prog_ut_decls = [];
    prog_ui_decls = [];
    prog_hp_decls = [];
    prog_hp_ids = [];
    prog_axiom_decls = [];
    prog_proc_decls = [];
    prog_coercion_decls = [];
    prog_hopred_decls = [];
    prog_barrier_decls = [];
    prog_test_comps = []; }

let init_conditions_of_block (b : ints_block) : ints_exp_assume list =
  let vars_of_exp e =
    let f e =
      match e with
      | I.Var { I.exp_var_name = id } -> Some [id]
      | _ -> None in
    I.fold_exp e f (List.concat) [] in
  let vars_of_asg asg =
    let lhs = asg.ints_exp_assign_lhs in
    vars_of_exp lhs in
  let vars_of_assume asm =
    vars_of_exp asm.ints_exp_assume_formula in
  let rec helper blk_cmds assigned =
    match blk_cmds with
    | [] -> []
    | (Assume asm)::cmds ->
      (* assumption is "inital" if all of the variables in its formula
       * aren't used by any asg's lhs so far in the block. *)
      if (List.exists
           (fun i -> List.mem i assigned)
           (vars_of_assume asm))
      then helper cmds assigned
      else asm::(helper cmds assigned)
    | (Assign asg)::cmds ->
      helper cmds ((vars_of_asg asg)@assigned)
  in
  helper b.ints_block_commands []

let trans_pure_formula (ass : ints_exp_assume) : IP.formula =
  let rec helper exp =
    match exp with
    | I.Binary op ->
      let pos = op.I.exp_binary_pos in
      let e1 = op.I.exp_binary_oper1 in
      let e2 = op.I.exp_binary_oper2 in
      (match op.I.exp_binary_op with
       | I.OpEq ->
         let pe1 = I.trans_to_exp_form e1 in
         let pe2 = I.trans_to_exp_form e2 in
         IP.BForm (((IP.Eq (pe1, pe2, pos)), None), None)
       | I.OpNeq ->
         let pe1 = I.trans_to_exp_form e1 in
         let pe2 = I.trans_to_exp_form e2 in
         IP.BForm (((IP.Neq (pe1, pe2, pos)), None), None)
       | I.OpLt ->
         let pe1 = I.trans_to_exp_form e1 in
         let pe2 = I.trans_to_exp_form e2 in
         IP.BForm (((IP.Lt (pe1, pe2, pos)), None), None)
       | I.OpLte ->
         let pe1 = I.trans_to_exp_form e1 in
         let pe2 = I.trans_to_exp_form e2 in
         IP.BForm (((IP.Lte (pe1, pe2, pos)), None), None)
       | I.OpGt ->
         let pe1 = I.trans_to_exp_form e1 in
         let pe2 = I.trans_to_exp_form e2 in
         IP.BForm (((IP.Gt (pe1, pe2, pos)), None), None)
       | I.OpGte ->
         let pe1 = I.trans_to_exp_form e1 in
         let pe2 = I.trans_to_exp_form e2 in
         IP.BForm (((IP.Gte (pe1, pe2, pos)), None), None)
       | I.OpLogicalAnd ->
         let pf1 = helper e1 in
         let pf2 = helper e2 in
         IP.And (pf1, pf2, pos)
       | I.OpLogicalOr ->
         let pf1 = helper e1 in
         let pf2 = helper e2 in
         IP.Or (pf1, pf2, None, pos)
       | _ -> report_error no_pos "intsparser.trans_pure_formula: unexpected bin_op"
      )
    | _ -> report_error no_pos "intsparser.trans_pure_formula: unexpected exp"
  in
  helper ass.ints_exp_assume_formula

let pure_formula_of_condition (cond : ints_exp_assume list) : IP.formula =
  let true_formula = IP.BForm ((IP.BConst (true, no_pos), None), None) in
  List.fold_right (fun a pf2 ->
    let pos = a.ints_exp_assume_pos in
    let pf1 = trans_pure_formula a in
    IP.And (pf1, pf2, pos)) cond true_formula

let is_equivalent_condition c1 c2 =
  let pf1 = pure_formula_of_condition c1 in
  let pf2 = pure_formula_of_condition c2 in
  let cf1 = Astsimp.trans_pure_formula pf1 [] empty_prog in
  let cf2 = Astsimp.trans_pure_formula pf2 [] empty_prog in
  Tpdispatcher.simpl_imply_raw cf1 cf2 &&
  Tpdispatcher.simpl_imply_raw cf2 cf1

let rec partition_by_key key_of key_eq ls =
  match ls with
  | [] -> []
  | e::es ->
    let ke = key_of e in
    let same_es, other_es = List.partition (fun e -> key_eq ke (key_of e)) es in
    (ke, e::same_es)::(partition_by_key key_of key_eq other_es)

let ints_loc_prefix = "ints_method_"

let name_of_ints_loc lbl =
  match lbl with
  | NumLoc (i, _) -> ints_loc_prefix ^ (string_of_int i)
  | NameLoc (s, _) -> s

let pos_of_ints_loc lbl =
  match lbl with
  | NumLoc (_, p)
  | NameLoc (_, p) -> p

let eq_ints_loc lbl1 lbl2 =
  (String.compare (name_of_ints_loc lbl1) (name_of_ints_loc lbl2)) == 0

let rec trans_ints_exp_lst (exps: ints_exp list) (last_exp: I.exp): I.exp =
  match exps with
  | [] -> last_exp
  | e::es ->
    let cont_exp = trans_ints_exp_lst es last_exp in
    match e with
    | Assign asg ->
      let asg_pos = asg.ints_exp_assign_pos in
      let asg_exp = I.mkAssign I.OpAssign asg.ints_exp_assign_lhs asg.ints_exp_assign_rhs
                      (fresh_branch_point_id "") asg_pos in
      I.mkSeq asg_exp cont_exp asg_pos
    | Assume asm ->
      let asm_pos = asm.ints_exp_assume_pos in
      I.mkCond asm.ints_exp_assume_formula cont_exp (I.Empty asm_pos) None asm_pos

let trans_ints_block (blk: ints_block): I.exp =
  let exps = blk.ints_block_commands in
  let fr = blk.ints_block_from in
  let t = blk.ints_block_to in
  let pos = blk.ints_block_pos in
  (* Translate to_label to a method call *)
  let to_exp = I.mkCallNRecv (name_of_ints_loc t) None [] None (fresh_branch_point_id "") (pos_of_ints_loc t) in
  (* Translate ints_exp list *)
  trans_ints_exp_lst exps to_exp

let trans_ints_block_lst fn (fr_lbl: ints_loc) (blks: ints_block list): I.proc_decl =
  let pos = pos_of_ints_loc fr_lbl in
  let proc_name = name_of_ints_loc fr_lbl in
  let blks = partition_by_key init_conditions_of_block is_equivalent_condition blks in
  (* Take blocks with equivalent starting conditions
   * and form into sequence of if/else with nondet() condition. *)
  let nondet_seq_for_blocks cond blks =
    let rec nondet_chain_for blks =
      match blks with
      | [] -> (I.Empty no_pos)
      | blk::blks ->
        let nondet_call = I.mkCallNRecv Globals.nondet_int_proc_name None [] None None no_pos in
        let nondet_cond = I.mkBinary I.OpGt nondet_call (I.mkIntLit 0 no_pos) None no_pos in
        I.mkCond nondet_cond (trans_ints_block blk) (nondet_chain_for blks) None blk.ints_block_pos in
    let nondet_chain = nondet_chain_for blks in
    let cond_exps = List.map (fun asm -> Assume asm) cond in
    trans_ints_exp_lst cond_exps nondet_chain
  in
  let proc_body = List.fold_left (fun acc (cond, blks) ->
      let blks_exp = match blks with
        | [blk] ->
          let () = x_binfo_pp "tmp: GAH! WHY???" no_pos in
          trans_ints_block blk
        | blks ->
          (* Multiple blocks with the same condition; introduce nondet. *)
          let () = x_binfo_pp "tmp: I SHOULD BE HAPPY IF I CAN SEE THIS." no_pos in
          nondet_seq_for_blocks cond blks in
      I.mkSeq acc blks_exp (I.get_exp_pos acc)
    ) (I.Empty pos) blks in
  I.mkProc fn proc_name [] "" None false [] [] I.void_type None (IF.EList []) (IF.mkEFalseF ()) pos (Some proc_body)

let trans_ints_prog fn (iprog: ints_prog): I.prog_decl =
  let main_proc =
    let start_lbl = iprog.ints_prog_start in
    let pos = pos_of_ints_loc start_lbl in
    let start_exp = I.mkCallNRecv (name_of_ints_loc start_lbl) None [] None (fresh_branch_point_id "") pos in
    I.mkProc fn "main" [] "" None false [] [] I.void_type None (IF.EList []) (IF.mkEFalseF ()) pos (Some start_exp)
  in
  let from_lbls = List.map (fun blk -> blk.ints_block_from) iprog.ints_prog_blocks in
  let to_lbls = List.map (fun blk -> blk.ints_block_to) iprog.ints_prog_blocks in
  let abandoned_to_lbls = Gen.BList.remove_dups_eq eq_ints_loc (Gen.BList.difference_eq eq_ints_loc to_lbls from_lbls) in
  let abandoned_procs = List.map (fun lbl ->
      let pos = pos_of_ints_loc lbl in
      let ret_exp = I.mkReturn None None pos in
      I.mkProc fn (name_of_ints_loc lbl) [] "" None false [] [] I.void_type None (IF.EList []) (IF.mkEFalseF ()) pos (Some ret_exp)
    ) abandoned_to_lbls in

  let proc_blks = partition_by_key (fun blk -> blk.ints_block_from) eq_ints_loc iprog.ints_prog_blocks in
  let proc_decls =
    [main_proc] @
    (List.map (fun (fr, blks) -> trans_ints_block_lst fn fr blks) proc_blks) @
    abandoned_procs @
    (* ensure `nondet()` proc is in program *)
    match (Parser.create_tnt_prim_proc Globals.nondet_int_proc_name) with
    | None -> [] | Some pd -> [pd]
  in
  let global_vars =
    let f e =
      match e with
      | I.Var v -> Some [(v.I.exp_var_name, v.I.exp_var_pos)]
      | _ -> None
    in
    let all_vars = List.concat (List.map (fun pd ->
        match pd.I.proc_body with
        | None -> []
        | Some b -> I.fold_exp b f (List.concat) [])
      proc_decls) in
    Gen.BList.remove_dups_eq (fun (s1, _) (s2, _) -> String.compare s1 s2 == 0) all_vars
  in
  let () = x_binfo_hp (add_str "global_vars" (pr_list fst)) global_vars no_pos in
  let global_var_decls = List.map (fun (d, p) -> I.mkGlobalVarDecl Int [(d, None, p)] p) global_vars in
  (* Inline Iast procedure if body is only a call to another procedure *)
  let proc_decls =
      let rec inline_body pd proc_names =
        (match pd.I.proc_body with
        | Some (CallNRecv { exp_call_nrecv_method = cnr_method }) ->
                let called_proc = (List.find
                  (fun pd -> cnr_method = pd.I.proc_name)
                  proc_decls) in
                (* If we're not trying to inline it, then recurse (+ this name) *)
                if not (List.mem called_proc.I.proc_name proc_names) then
                  let called_proc = inline_body called_proc (pd.I.proc_name::proc_names) in
                  { pd with I.proc_body = called_proc.I.proc_body }
                else
                  pd
        | _ -> pd) in
      (List.map (fun pd -> inline_body pd []) proc_decls) in
  let called_proc_names =
    let f caller_name e =
      match e with
      (* Don't consider calls where the proc name is the caller name. *)
      | I.CallNRecv { exp_call_nrecv_method = cnr_method } when cnr_method <> caller_name ->
        Some [cnr_method]
      | _ -> None
    in
    let all_calls = "main" :: List.concat (List.map (fun pd ->
        match pd.I.proc_body with
        | None -> []
        | Some b -> I.fold_exp b (f pd.I.proc_name) (List.concat) [])
    proc_decls) in
    Gen.BList.remove_dups_eq (fun s1 s2 -> String.compare s1 s2 == 0) all_calls
  in
  let () = x_binfo_hp (add_str "called_proc_names" (pr_list (fun x->x))) called_proc_names no_pos in
  (* remove procedures which aren't called *)
  let proc_decls =
    List.filter (fun pd -> List.mem pd.I.proc_name called_proc_names) proc_decls
  in
  { prog_include_decls = [];
    prog_data_decls = [];
    prog_global_var_decls = global_var_decls;
    prog_logical_var_decls = [];
    prog_enum_decls = [];
    prog_view_decls = [];
    prog_func_decls = [];
    prog_rel_decls = [];
    prog_rel_ids = [];
    prog_templ_decls = [];
    prog_ut_decls = [];
    prog_ui_decls = [];
    prog_hp_decls = [];
    prog_hp_ids = [];
    prog_axiom_decls = [];
    prog_proc_decls = proc_decls;
    prog_coercion_decls = [];
    prog_hopred_decls = [];
    prog_barrier_decls = [];
    prog_test_comps = []; }

let parse_ints (file_name: string): I.prog_decl =
  let in_chnl = open_in file_name in
  let lexbuf = Lexing.from_channel in_chnl in
  let iprog =
    try
      let p = Iparser.program Ilexer.tokenizer lexbuf in
      let () = close_in in_chnl in
      p
    with e ->
      let () = close_in in_chnl in
      match e with
      | Parsing.Parse_error ->
        let curr = lexbuf.Lexing.lex_curr_p in
        let err_pos = { start_pos = curr; mid_pos = curr; end_pos = curr; } in
        (* let line = curr.Lexing.pos_lnum in                       *)
        (* let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in *)
        let token = Lexing.lexeme lexbuf in
        Gen.report_error err_pos ("Intsparser: Unexpected token " ^ token)
      | _ -> raise e
  in
  trans_ints_prog file_name iprog
