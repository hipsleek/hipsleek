#include "xdebug.cppo"
open VarGen
open Printf
open Gen.Basic
open Globals
open Exc.GTable

module C = Cast
module CP = Cpure
module CF = Cformula
module Syn = Synthesis
module I = Iast
module MCP = Mcpure
module Err = Error

let pr_proc = Iprinter.string_of_proc_decl_repair
let pr_cproc = Cprinter.string_of_proc_decl 1
let pr_iprog = Iprinter.string_of_program_repair
let pr_cprog = Cprinter.string_of_program
let pr_ctx = Cprinter.string_of_list_failesc_context
let pr_formula = Cprinter.string_of_formula
let pr_struc_f = Cprinter.string_of_struc_formula
let pr_hps = pr_list Iprinter.string_of_hp_decl
let pr_exp = Iprinter.string_of_exp_repair
let pr_exps = pr_list Iprinter.string_of_exp
let pr_c_exps = pr_list Cprinter.string_of_exp
let pr_c_exp =  Cprinter.string_of_exp
let pr_int = string_of_int
let pr_bool = string_of_bool
let pr_vars = Cprinter.string_of_typed_spec_var_list
let pr_pos = string_of_loc

let next_proc = ref false
let stop = ref false
let infestor_num = ref 0

type block_tree = {
  bt_statements: C.exp list;
  bt_block_left : block_tree_node;
  bt_block_right: block_tree_node;
}

and block_tree_node =
  | BtEmp
  | BtNode of block_tree

let rec pr_bt (bt: block_tree) =
  let stmts = bt.bt_statements in
  let str_stmts = stmts |> pr_list Cprinter.string_of_exp in
  let l_tree = bt.bt_block_left |> pr_btn in
  let r_tree = bt.bt_block_right |> pr_btn in
  str_stmts ^ "\n" ^
  l_tree ^ "\n" ^
  r_tree

and pr_btn (btn: block_tree_node) = match btn with
  | BtEmp -> "BtEmp"
  | BtNode bt -> "BtNode (" ^ (pr_bt bt) ^ ")"

let get_statement_traces (bt:block_tree) =
  let rec aux (bt:block_tree) =
    match bt.bt_block_left, bt.bt_block_right with
    | BtEmp, BtEmp -> [[bt.bt_statements]]
    | BtEmp, BtNode right ->
      let r_traces = aux right in
      List.map (fun x -> bt.bt_statements::x) r_traces
    | BtNode left, BtEmp ->
      let l_trace = aux left in
      List.map (fun x -> bt.bt_statements::x) l_trace
    | BtNode left, BtNode right ->
      let stmts = bt.bt_statements in
      let left = aux left in
      let right = aux right in
      let l_traces = List.map (fun x -> stmts::x) left in
      let r_traces = List.map (fun x -> stmts::x) right in
      l_traces @ r_traces in
  aux bt

let is_return_exp (exp:I.exp) =
  match exp with
  | I.Return _ -> true
  | _ -> false

let is_return_block (blocks : C.exp list) =
  let aux (exp: C.exp) = match exp with
    | C.Sharp _ -> true
    | _ -> false in
  List.exists aux blocks

let read_file filename =
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; []
  with End_of_file -> close_in chan;
    List.rev !lines

let get_block_traces (proc : C.proc_decl) =
  let input_tree = {
      bt_statements = [];
      bt_block_left = BtEmp;
      bt_block_right = BtEmp;
    } in
  let rec aux (exp: C.exp) block_tree = match exp with
    | C.Label exp -> aux exp.C.exp_label_exp block_tree
    | C.Block exp -> aux exp.C.exp_block_body block_tree
    | C.Seq s_exp ->
      let block_tree = aux s_exp.C.exp_seq_exp1 block_tree in
      aux s_exp.C.exp_seq_exp2 block_tree
    | C.Bind _ | C.Sharp _ | SCall _
    | C.VarDecl _ ->
      let stmts = (block_tree.bt_statements) @ [exp] in
      {block_tree with bt_statements = stmts}
    | C.Assign a_exp ->
      (* if is_seq_exp a_exp.C.exp_assign_rhs then
       *   let r_tree = aux a_exp.C.exp_assign_rhs input_tree in
       *   {block_tree with bt_block_right = BtNode r_tree}
       * else *)
      let stmts = (block_tree.bt_statements) @ [exp] in
      {block_tree with bt_statements = stmts}
    | C.Cond exp ->
      let l_tree = aux exp.C.exp_cond_then_arm input_tree in
      let r_tree = aux exp.C.exp_cond_else_arm input_tree in
      {block_tree with bt_block_left = BtNode l_tree;
                       bt_block_right = BtNode r_tree}
    | _ -> block_tree in
  match proc.C.proc_body with
  | None -> input_tree
  | Some c_exp -> aux c_exp input_tree

let get_stmt_candidates (exp: I.exp) =
  let rec aux (exp:I.exp) list =
    match exp with
    | I.CallRecv _ | I.CallNRecv _ | I.Assign _ | I.Binary _ -> [exp]@list
    | I.Block block -> aux block.exp_block_body list
    | I.Cond exp_cond -> let exp2_list = aux exp_cond.exp_cond_then_arm list in
      aux exp_cond.exp_cond_else_arm exp2_list
    | I.Label (a, lexp) -> aux lexp list
    | I.Seq exp_seq -> let exp1_list = aux exp_seq.exp_seq_exp1 list in
      aux exp_seq.exp_seq_exp2 exp1_list
    | I.Var _ | I.VarDecl _ -> list
    | I.Unary e -> aux e.exp_unary_exp list
    | _ -> [exp] @ list in
  List.rev(aux exp [])

let rec get_var_decls pos (exp: C.exp) = match exp with
  | C.VarDecl var ->
    let v_pos = var.C.exp_var_decl_pos in
    if get_start_lnum v_pos < get_start_lnum pos then
      let v_name = var.C.exp_var_decl_name in
      let v_typ = var.C.exp_var_decl_type in
      [(v_typ, v_name)]
    else []
  | C.Seq seq -> (get_var_decls pos seq.C.exp_seq_exp1) @
                 (get_var_decls pos seq.C.exp_seq_exp2)
  | C.Cond cond -> (get_var_decls pos cond.C.exp_cond_then_arm) @
                   (get_var_decls pos cond.C.exp_cond_else_arm)
  | C.Block b -> get_var_decls pos b.C.exp_block_body
  | C.Label e -> get_var_decls pos e.C.exp_label_exp
  | _ -> []

let rec get_block_var_decls pos (exp: C.exp) = match exp with
  | C.VarDecl var ->
    let v_pos = var.C.exp_var_decl_pos in
    if get_start_lnum v_pos < get_start_lnum pos then
      let v_name = var.C.exp_var_decl_name in
      let v_typ = var.C.exp_var_decl_type in
      [(v_typ, v_name)]
    else []
  | C.Seq seq -> (get_block_var_decls pos seq.C.exp_seq_exp1) @
                 (get_block_var_decls pos seq.C.exp_seq_exp2)
  | C.Cond cond -> (get_block_var_decls pos cond.C.exp_cond_then_arm) @
                   (get_block_var_decls pos cond.C.exp_cond_else_arm)
  | C.Block b -> get_block_var_decls pos b.C.exp_block_body
  | C.Label e -> get_block_var_decls pos e.C.exp_label_exp
  | _ -> []

let get_trace_var_decls pos trace =
  let aux (e : C.exp) = match e with
    | C.VarDecl var ->
      let v_pos = var.C.exp_var_decl_pos in
      if get_start_lnum v_pos < get_start_lnum pos then
        let v_name = var.C.exp_var_decl_name in
        let v_typ = var.C.exp_var_decl_type in
        [(v_typ, v_name)]
      else []
    | _ -> [] in
  let aux_block block =
    block |> List.map aux |> List.concat in
  trace |> List.map aux_block |> List.concat

let type_of_exp (exp:I.exp) : typ = match exp with
  | IntLit _ -> Int
  | Binary bexp ->
    begin
      match bexp.I.exp_binary_op with
      | OpPlus | OpMinus | OpMult | OpDiv | OpMod | OpEq | OpNeq | OpLt
      | OpLte | OpGt | OpGte -> Int
      | _ -> Bool
    end
  | _ -> Void

let create_fcode_exp (vars: typed_ident list) : I.exp =
  let args = vars |> List.map snd
             |> List.map (fun x -> I.Var { exp_var_name = x;
                                           exp_var_pos = no_pos}) in
  I.CallNRecv { exp_call_nrecv_method = fcode_str;
                exp_call_nrecv_lock = None;
                exp_call_nrecv_ho_arg = None;
                exp_call_nrecv_arguments = args;
                exp_call_nrecv_path_id = None;
                exp_call_nrecv_pos = no_pos}

let create_fcode_proc (args : typed_ident list) typ =
  let rec helper args = match args with
    | [] -> ""
    | [(typ, name)] -> (string_of_typ typ) ^ " " ^ name
    | h::t ->
      let tail = helper t in
      let head = string_of_typ (fst h) ^ " " ^ (snd h) in
      head ^ "," ^ tail in
  let names = args |> List.map snd in
  let arg_str = helper args in
  let arg_names = pr_idents_wo_brackets names "," in
  let fcode = hp_str ^ " P(" ^ arg_str ^ ").\n" ^
              hp_str ^ " Q(" ^ arg_str ^ ").\n" ^
              (string_of_typ typ) ^  " " ^ fcode_str ^ "(" ^ arg_str ^ ")\n" ^
              "requires P(" ^ arg_names ^ ")\n" ^
              "ensures Q(" ^ arg_names ^ ");" in
  let lines = read_file "prelude.ss" in
  let line = String.concat "\n" lines in
  let fcode = line ^ "\n" ^ fcode in
  let n_prog = Parser.parse_hip_string "fcode" fcode in
  n_prog

let create_cast_fcode (vars: typed_ident list) pos =
  let args = vars |> List.map snd in
  let types = vars |> List.map fst in
  let name = C.mingle_name fcode_str types in
  C.SCall {
    exp_scall_type = Int;
    exp_scall_method_name = name;
    exp_scall_lock = None;
    exp_scall_arguments = args;
    exp_scall_ho_arg = None;
    exp_scall_is_rec = false;
    exp_scall_path_id = None;
    exp_scall_pos = pos;
  }

let eq_exp e1 e2 = let loc1 = I.get_exp_pos e1 in
  let loc2 = I.get_exp_pos e2 in
  loc1 = loc2

let rec replace_exp exp n_exp old_exp : I.exp =
  match (exp: I.exp) with
  | Assign e -> if eq_exp exp old_exp then n_exp else
      let r1 = replace_exp e.exp_assign_lhs n_exp old_exp in
      let r2 = replace_exp e.exp_assign_rhs n_exp old_exp in
      Assign {e with exp_assign_lhs = r1;
                     exp_assign_rhs = r2}
  | Binary e -> if eq_exp exp old_exp then n_exp else
      let r1 = replace_exp e.exp_binary_oper1 n_exp old_exp in
      let r2 = replace_exp e.exp_binary_oper2 n_exp old_exp in
      Binary {e with exp_binary_oper1 = r1;
                     exp_binary_oper2 = r2}
  | Bind e -> if eq_exp exp old_exp then n_exp else
      let r_exp = replace_exp e.exp_bind_body n_exp n_exp in
      Bind {e with exp_bind_body = r_exp}
  | Block e -> let r_exp = replace_exp e.exp_block_body n_exp old_exp in
      Block {e with exp_block_body = r_exp}
  | Cast e ->
    Cast {e with exp_cast_body = replace_exp e.exp_cast_body n_exp old_exp}
  | Cond e -> let r1 = replace_exp e.exp_cond_condition n_exp old_exp in
    let r2 = replace_exp e.exp_cond_then_arm n_exp old_exp in
    let r3 = replace_exp e.exp_cond_else_arm n_exp old_exp in
    Cond {e with exp_cond_condition = r1;
                 exp_cond_then_arm = r2;
                 exp_cond_else_arm = r3}
  | Catch e -> Catch {
      e with exp_catch_body = replace_exp e.exp_catch_body n_exp old_exp }
  | IntLit e -> if eq_exp exp old_exp then n_exp else exp
  | Label (a, body) -> Label (a, replace_exp body n_exp old_exp)
  | Member e ->
    Member {e with exp_member_base = replace_exp e.exp_member_base n_exp old_exp}
  | Return e -> if eq_exp exp old_exp then n_exp else exp
  | Seq e -> let r_e1 = replace_exp e.exp_seq_exp1 n_exp old_exp in
    let r_e2 = replace_exp e.exp_seq_exp2 n_exp old_exp in
    Seq {e with exp_seq_exp1 = r_e1; exp_seq_exp2 = r_e2}
  | Unary e -> let n_e = replace_exp e.exp_unary_exp n_exp old_exp in
    Unary {e with exp_unary_exp = n_e}
  | CallRecv _
  | CallNRecv _ -> if eq_exp exp old_exp then n_exp else exp
  | _ -> exp

let rec replace_exp_with_loc exp n_exp loc : I.exp =
  match (exp:I.exp) with
  | Assign e -> if (e.exp_assign_pos = loc) then n_exp else
      let r_exp1 = replace_exp_with_loc e.exp_assign_lhs n_exp loc in
      let r_exp2 = replace_exp_with_loc e.exp_assign_rhs n_exp loc in
      Assign {e with exp_assign_lhs = r_exp1;
                     exp_assign_rhs = r_exp2}
  | Binary e ->
    begin
      match e.exp_binary_op with
      | OpEq | OpNeq | OpLt | OpLte | OpGt | OpGte ->
        let r_exp1 = replace_exp_with_loc e.exp_binary_oper1 n_exp loc in
        Binary {e with exp_binary_oper1 = r_exp1}
      | _ -> if e.exp_binary_pos = loc then n_exp else
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
    else let r_exp = replace_exp_with_loc e.exp_block_body n_exp loc in
      Block {e with exp_block_body = r_exp}
  | Cast e ->
    Cast {e with exp_cast_body = replace_exp_with_loc e.exp_cast_body n_exp loc}
  | Cond e -> let r_cond = replace_exp_with_loc e.exp_cond_condition n_exp loc in
    let r_then_branch = replace_exp_with_loc e.exp_cond_then_arm n_exp loc in
    let r_else_branch = replace_exp_with_loc e.exp_cond_else_arm n_exp loc in
    Cond {e with exp_cond_condition = r_cond;
                 exp_cond_then_arm = r_then_branch;
                 exp_cond_else_arm = r_else_branch}
  | Catch e -> Catch {
      e with exp_catch_body = replace_exp_with_loc e.exp_catch_body n_exp loc }
  | IntLit e -> if (e.exp_int_lit_pos = loc) then n_exp else exp
  | Label (a, body) -> Label (a, replace_exp_with_loc body n_exp loc)
  | Member e ->
    Member {e with exp_member_base = replace_exp_with_loc e.exp_member_base n_exp loc}
  | New e -> exp
  | Return e -> let r_val = match e.exp_return_val with
      | None -> None
      | Some e -> Some (replace_exp_with_loc e n_exp loc) in
    Return {e with exp_return_val = r_val}
  | Seq e -> let r_e1 = replace_exp_with_loc e.exp_seq_exp1 n_exp loc in
    let r_e2 = replace_exp_with_loc e.exp_seq_exp2 n_exp loc in
    Seq {e with exp_seq_exp1 = r_e1;
                exp_seq_exp2 = r_e2}
  | Unary e -> let n_e = replace_exp_with_loc e.exp_unary_exp n_exp loc in
    Unary {e with exp_unary_exp = n_e}
  | Var v -> if (v.exp_var_pos = loc) then n_exp else exp
  | _ -> exp

let replace_assign_exp exp vars heuristic =
  let rec prelist a b = match a, b with
    | [], _ -> true      | _, [] -> false
    | h::t, h'::t' -> h = h' && prelist t t' in
  let rec sublist a b = match a, b with
    | [], _ -> true      | _, [] -> false
    | h::_, h'::t' -> (h = h' && prelist a b) || sublist a t' in
  let is_cond exp = match (exp:I.exp) with
    | Binary e ->
      begin
        match e.exp_binary_op with
        | OpEq | OpNeq | OpLt | OpLte | OpGte | OpGt -> true
        | _ -> false
      end
    | _ -> false in
  let is_unk_exp exp = match (exp:I.exp) with
    | UnkExp _ -> true      | _ -> false in
  let rec replace exp vars =
    let exp_vars = I.collect_vars_exp exp in
    let () = x_tinfo_hp (add_str "exp_vars: " (pr_list pr_id)) exp_vars no_pos in
    if (sublist exp_vars vars & not (is_cond exp)) then
      (I.mk_unk_exp exp_vars (I.get_exp_pos exp), exp_vars, [I.get_exp_pos exp])
    else match exp with
      | Binary b ->
        if is_cond exp then
          let (a1, b1, c1) = replace b.exp_binary_oper1 vars in
          (Binary { b with exp_binary_oper1 = a1}, b1, c1)
        else let (a1, b1, c1) = replace b.exp_binary_oper1 vars in
          let (a2, b2, c2) = replace b.exp_binary_oper2 vars in
          if (is_unk_exp a1 && is_unk_exp a2) then
            (I.combine_unk_exp a1 a2 b.exp_binary_pos, b1@b2, c1@c2)
          else (Binary { b with exp_binary_oper1 = a1;
                                exp_binary_oper2 = a2}, b1 @ b2, c1@c2)
      | _ -> (exp, [], []) in
  let () = x_tinfo_hp (add_str "vars: " (pr_list pr_id)) vars no_pos in
  let exp_vars = I.collect_vars_exp exp in
  if (exp_vars == []) then
    (I.mk_unk_exp [] (I.get_exp_pos exp), [], [I.get_exp_pos exp])
  else replace exp vars

(* Normalize arithmetic expression *)
let normalize_arith_exp exp =
  let rec is_compose_exp (exp:I.exp) = match exp with
    | Binary e -> true
    | Unary e -> is_compose_exp e.exp_unary_exp
    | Block e -> is_compose_exp e.exp_block_body
    | _ -> false
  in
  let rec aux (exp:I.exp) = match exp with
    | Binary e ->
      begin
        match e.exp_binary_op with
        | OpLogicalAnd      | OpLogicalOr ->
          let (e1, list1) =
            if (is_compose_exp e.exp_binary_oper1) then
              aux e.exp_binary_oper1
            else (e.exp_binary_oper1, []) in
          let (e2, list2) =
            if (is_compose_exp e.exp_binary_oper2) then
              aux e.exp_binary_oper2
            else (e.exp_binary_oper2, []) in
          let n_exp = I.Binary {e with exp_binary_oper1 = e1;
                                     exp_binary_oper2 = e2} in
          (n_exp, list1@list2)
        | OpEq | OpNeq | OpLt | OpLte | OpGt | OpGte ->
          if (is_compose_exp e.exp_binary_oper1) then
            let loc = I.get_exp_pos e.exp_binary_oper1 in
            let n_name = "exp_" ^ (VarGen.string_of_loc_repair loc) in
            let var = I.Var { exp_var_name = n_name;
                            exp_var_pos = loc} in
            let n_exp = I.Binary {e with exp_binary_oper1 = var} in
            (n_exp, [(n_name, e.exp_binary_oper1)])
          else (exp, [])
        | _ -> (exp, [])
    end
    | Assign e -> let (e1, list1) = aux e.exp_assign_rhs in
      (I.Assign {e with exp_assign_rhs = e1}, list1)
    | Block b -> let (e1, l1) = aux b.exp_block_body in
      (I.Block {b with exp_block_body = e1}, l1)
    | Cond e -> let (e1, l1) = aux e.exp_cond_condition in
      let (e2, l2) = aux e.exp_cond_then_arm in
      let (e3, l3) = aux e.exp_cond_else_arm in
      (I.Cond {e with exp_cond_condition = e1;
                    exp_cond_then_arm = e2;
                    exp_cond_else_arm = e3}, l1@l2@l3)
    | Label (a, e) -> let (e1, l1) = aux e in (I.Label (a, e1), l1)
    | Seq e -> let (e1, l1) = aux e.exp_seq_exp1 in
      let (e2, l2) = aux e.exp_seq_exp2 in
      (I.Seq {e with exp_seq_exp1 = e1; exp_seq_exp2 = e2}, l1@l2)
    | Unary e -> let (e1, l1) = aux e.exp_unary_exp in
      (I.Unary {e with exp_unary_exp = e1}, l1)
    | _ -> (exp, []) in
  let (n_exp, assign_list) = aux exp in
  let collect_local_var_decls exp =
    let rec aux exp list = match (exp:I.exp) with
      | Block e -> aux e.exp_block_body list
      | Seq e ->
        let list1 = aux e.exp_seq_exp1 list in
        aux e.exp_seq_exp2 list1
      | VarDecl _ -> [exp] @ list
      | Label (_, e) -> aux e list
      | _ -> list in
    List.rev (aux exp []) in
  let collect_main exp =
    let rec aux exp list = match (exp:I.exp) with
      | Block e -> aux e.exp_block_body list
      | Seq e -> let list1 = aux e.exp_seq_exp1 list in
        aux e.exp_seq_exp2 list1
      | VarDecl _ -> list
      | Label (_, e) -> aux e list
      | _ -> [exp] @ list in
    List.rev (aux exp []) in
  let var_decls = collect_local_var_decls n_exp in
  let pr_exps = pr_list Iprinter.string_of_exp in
  let pr_exp = Iprinter.string_of_exp in
  let () = x_tinfo_hp (add_str "n_exp: " pr_exp) n_exp no_pos in
  let () = x_tinfo_hp (add_str "var decls: " pr_exps) var_decls no_pos in
  let rec find_main exp vars = match (exp:I.exp) with
    | Block e -> find_main e.exp_block_body vars
    | Label (_, el) -> find_main el vars
    | Seq e -> if (List.mem e.exp_seq_exp1 vars) then e.exp_seq_exp2
      else if (List.mem e.exp_seq_exp2 vars) then e.exp_seq_exp1
      else let e1 = find_main e.exp_seq_exp1 vars in
        let e2 = find_main e.exp_seq_exp2 vars in
        Seq {e with exp_seq_exp1 = e1;
                    exp_seq_exp2 = e2}
    | _ -> exp in
  let rec sequencing_exp exp_list = match exp_list with
    | [] -> report_error no_pos "cannot sequencing empty list"
    | [x] -> x
    | h::t -> I.mkSeq h (sequencing_exp t) no_pos in
  let main_exp = sequencing_exp (collect_main n_exp) in
  let () = x_tinfo_hp (add_str "main: " pr_exp) main_exp no_pos in
  let assign_list = Gen.BList.remove_dups_eq (fun a b ->
      String.compare (fst a) (fst b) == 0) assign_list in
  let attached_exp = List.fold_left(fun a (b, c) ->
      let var_decl = I.VarDecl { exp_var_decl_type = I.int_type;
                               exp_var_decl_decls = [(b, None, no_pos)];
                                 exp_var_decl_pos = no_pos} in
      let assign = I.Assign { exp_assign_op = OpAssign;
                              exp_assign_lhs = Var {
                                  exp_var_name = b;
                                  exp_var_pos = no_pos;
                                };
                              exp_assign_rhs = c;
                              exp_assign_path_id = None;
                            exp_assign_pos = no_pos
                          } in
      let seq = I.Seq { exp_seq_exp1 = var_decl;
                      exp_seq_exp2 = assign;
                      exp_seq_pos = no_pos} in
      I.Seq { exp_seq_exp1 = seq;
            exp_seq_exp2 = a;
            exp_seq_pos = no_pos
          }
    ) main_exp assign_list in
  let attached_exp = if (var_decls = []) then attached_exp
    else let var_decls = sequencing_exp var_decls in
      I.mkSeq var_decls attached_exp no_pos in
  attached_exp

(* Normalize logical exp *)
(* e.g x < y <-> x - y < 0 *)
let rec normalize_logical_exp exp : I.exp = match (exp:I.exp) with
  | Binary e ->
    begin
      match e.exp_binary_op with
      | OpLt | OpLte | OpGt | OpGte ->
        if not(I.is_zero_exp e.exp_binary_oper2) then
          let e_oper1 = e.exp_binary_oper1 in
          let e_oper2 = e.exp_binary_oper2 in
          let e_pos = e.exp_binary_pos in
          let e1 = I.mkBinary OpMinus e_oper1 e_oper2 None e_pos in
          Binary { e with exp_binary_oper1 = e1;
                          exp_binary_oper2 = I.mkIntLit 0 no_pos;
                          exp_binary_pos = no_pos }
        else exp
      | OpLogicalAnd | OpLogicalOr ->
        let e_1 = normalize_logical_exp e.exp_binary_oper1 in
        let e_2 = normalize_logical_exp e.exp_binary_oper2 in
        Binary { e with exp_binary_oper1 = e_1;
                        exp_binary_oper2 = e_2 }
      | _ -> exp
    end
  | Assign e -> let rhs_e = normalize_logical_exp e.exp_assign_rhs in
    let pr_exp = Iprinter.string_of_exp in
    let () = x_tinfo_hp (add_str "rhs: " pr_exp) e.exp_assign_rhs no_pos in
    Assign {e with exp_assign_rhs = rhs_e}
  | Block b ->
    Block {b with exp_block_body = normalize_logical_exp b.exp_block_body}
  | Cond e -> let e_cond = normalize_logical_exp e.exp_cond_condition in
    let e_then = normalize_logical_exp e.exp_cond_then_arm in
    let e_else = normalize_logical_exp e.exp_cond_else_arm in
    Cond {e with exp_cond_condition = e_cond;
                 exp_cond_then_arm = e_then;
                 exp_cond_else_arm = e_else}
  | Label (a, e) -> Label (a, normalize_logical_exp e)
  | Seq e -> let e_1 = normalize_logical_exp e.exp_seq_exp1 in
    let e_2 = normalize_logical_exp e.exp_seq_exp2 in
    Seq {e with exp_seq_exp1 = e_1;
                exp_seq_exp2 = e_2}
  | Unary e -> let e1 = normalize_logical_exp e.exp_unary_exp in
    Unary {e with exp_unary_exp = e1}
  | CallNRecv e -> let args = e.exp_call_nrecv_arguments in
    let n_args = List.map normalize_logical_exp args in
    CallNRecv {e with exp_call_nrecv_arguments = n_args}
  | CallRecv e -> let args = e.exp_call_recv_arguments in
    let n_args = List.map normalize_logical_exp args in
    CallRecv {e with exp_call_recv_arguments = n_args}
  | _ -> exp

(* normalize iast procedures *)
let normalize_proc iprog proc_decl =
  let n_proc_body = match proc_decl.I.proc_body with
    | None -> None
    | Some body_exp -> let n_exp = body_exp in
      let n_exp = normalize_logical_exp body_exp in
      Some n_exp in
  let nprog = {proc_decl with proc_body = n_proc_body} in
  nprog

(* normalize iast program input for repair*)
let normalize_prog iprog =
  {iprog with I.prog_proc_decls = List.map (fun x -> normalize_proc iprog x) iprog.I.prog_proc_decls}

let output_repaired_iprog src pos repaired_exp =
  let file_name, dir = Filename.basename src, Filename.dirname src in
  let r_file = "repaired_" ^ file_name in
  let to_saved_file = dir ^ Filename.dir_sep ^ r_file in
  let lines, count = read_file src, ref 0 in
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
  else let exp_str = repaired_exp |> (Cprinter.poly_string_of_pr
                                     Cprinter.pr_formula_exp) in
    let () = x_tinfo_hp (add_str "pos" VarGen.string_of_loc) pos no_pos in
    let output_lines = List.map (fun (x,y) ->
        if (y != start_lnum) then x
        else let () = x_tinfo_hp (add_str "x" pr_id) x no_pos in
          let () = x_tinfo_hp (add_str "start" string_of_int) (start_cnum -1) no_pos in
          let () = x_tinfo_hp (add_str "end" string_of_int)
              (end_cnum - start_cnum + 1) no_pos in
          let to_be_replaced = String.sub x (start_cnum - 1) (end_cnum - start_cnum + 1) in
          Str.replace_first (Str.regexp_string to_be_replaced) exp_str x
      ) lines_with_lnums in
    let output = String.concat "\n" output_lines in
    let () = x_tinfo_hp (add_str "output_prog:" pr_id) output no_pos in
    let oc = open_out to_saved_file in
    fprintf oc "%s\n" output; close_out oc;
    let () = x_binfo_pp "\n\n \n" no_pos in
    ()

let repair_prog_with_templ iprog cond_op =
  let () = Typechecker.repair_proc := None in
  let contains s1 s2 = let re = Str.regexp_string s2 in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false in
  let () = x_tinfo_pp "marking \n" no_pos in
  let cprog, _ = Astsimp.trans_prog iprog in
  try
    let () = Typechecker.check_prog_wrapper iprog cprog in
    let () = next_proc := false in
    None
  with _ as e -> None

let create_block_exp (block: C.exp list) =
  match block with
  | [] -> failwith "blocks cannot be empty"
  | [head] -> head
  | head :: tail ->
    List.fold_left Syn.mkCSeq head tail

let create_tmpl_proc_pure proc replaced_exp vars heuristic =
  let var_names = List.map fst vars in
  let pr_exp = Iprinter.string_of_exp_repair in
  let () = x_tinfo_hp (add_str "exp input: " pr_exp) (replaced_exp) no_pos in
  let () = x_tinfo_hp (add_str "exp_vars input: " (pr_list pr_id)) var_names no_pos in
  let (n_exp, replaced_vars, _) =
    replace_assign_exp replaced_exp var_names heuristic in
  let () = x_tinfo_hp (add_str "replaced_vars: " (pr_list pr_id))
      replaced_vars no_pos in
  let () = x_tinfo_hp (add_str "n_exp: " (Iprinter.string_of_exp)) n_exp no_pos in
  if n_exp = replaced_exp then
    let () = next_proc := false in None
  else let exp_loc = I.get_exp_pos replaced_exp in
    let unk_vars = List.map (fun x -> (Globals.Int, x)) replaced_vars in
    let unk_exp = I.mk_exp_decl unk_vars in
    let n_proc_body = Some (replace_exp_with_loc (Gen.unsome proc.I.proc_body)
                              n_exp exp_loc) in
    let n_proc = {proc with proc_body = n_proc_body} in
    Some (n_proc, unk_exp, exp_loc)

let repair_one_statement (iprog:I.prog_decl) proc exp is_cond vars heuristic =
  let pr_exp = Iprinter.string_of_exp_repair in
  let () = x_tinfo_hp (add_str "exp candidate: " pr_exp) exp no_pos in
  if !stop then let () = next_proc := false in None
  else let n_proc_exp = create_tmpl_proc_pure proc exp vars heuristic in
    let () = x_dinfo_pp "marking \n" no_pos in
    match n_proc_exp with
    | None -> let () = next_proc := false in None
    | Some (templ_proc, unk_exp, replaced_pos) ->
      let () = x_tinfo_hp (add_str "new proc: " pr_exp)
          (Gen.unsome templ_proc.proc_body) no_pos in
      let var_names = List.map fst vars in
      let var_typs = List.map snd vars in
      let n_proc_decls =
        List.map (fun x -> if (x.I.proc_name = templ_proc.proc_name)
                   then templ_proc else x) iprog.I.prog_proc_decls in
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
          let repaired_proc = List.find (fun x -> x.I.proc_name = proc.proc_name)
              res_iprog.I.prog_proc_decls in
          let () = x_tinfo_hp
              (add_str "best repaired proc" (Iprinter.string_of_exp_repair))
              (Gen.unsome repaired_proc.proc_body) no_pos in
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
  try let max_candidate = List.hd repair_list in
    let res = List.fold_left (fun x y ->
        let (a1, b1, c1, d3) = x in
        let (a2, b2, c2, d2) = y in
        if a1 > a2 then x else y
      ) max_candidate (List.tl repair_list) in
    Some res
  with Failure _ -> None

let repair_by_mutation (iprog:I.prog_decl) (repairing_proc:I.proc_decl) =
  let () = x_tinfo_pp "marking \n" no_pos in
  let proc_body = Gen.unsome repairing_proc.I.proc_body in
  let logical_locs = I.collect_logical_locs proc_body in
  let candidate_procs = List.map (fun x -> I.mutate_prog x repairing_proc)
      logical_locs in
  let constant_candidates =
    List.map (fun x -> I.mk_constant x repairing_proc) logical_locs in
  let candidates = candidate_procs @ constant_candidates in
  let check_candidate iprog mutated_proc =
    let () = x_tinfo_hp (add_str "candidate proc" (Iprinter.string_of_exp))
        (Gen.unsome mutated_proc.I.proc_body) no_pos in
    if (!stop) then None
    else let n_proc_decls =
        List.map (fun x -> if (x.I.proc_name = mutated_proc.proc_name)
                   then mutated_proc else x) iprog.I.prog_proc_decls in
      let n_iprog = {iprog with I.prog_proc_decls = n_proc_decls} in
      let n_cprog, _ = Astsimp.trans_prog n_iprog in
      try
        let () = Typechecker.check_prog_wrapper n_iprog n_cprog in
        let () = stop := true in
        let () = x_tinfo_hp (add_str "best repaired proc" (Iprinter.string_of_exp_repair))
            (Gen.unsome mutated_proc.proc_body) no_pos in
        Some n_iprog
      with _ -> None in
  List.map (fun x -> check_candidate iprog x) candidates

let mk_specs (pre_cond, post_cond) =
  let assume_f = CF.mkEBase post_cond None no_pos in
  let post = CF.mkEAssume_simp [] post_cond assume_f (-1, "post") in
  let base = CF.mkEBase_with_cont (CP.mkTrue no_pos) (Some post) no_pos in
  let specs = CF.mkEBase pre_cond (Some base) no_pos in
  specs

let mk_block_proc (proc: C.proc_decl) block_exp specs =
  let args = proc.C.proc_args in
  let pf = MCP.mix_of_pure (CP.mkFalse no_pos) in
  let dynamic_f = CF.mkBase_simp CF.HFalse pf in
  let dynamic_specs = CF.mkEBase dynamic_f None no_pos in
  let proc = {
    C.proc_name = "block_fragment";
    C.proc_source = proc.C.proc_source;
    C.proc_flags = proc.C.proc_flags;
    C.proc_args = [];
    C.proc_ho_arg = None;
    C.proc_args_wi = [];
    C.proc_imm_args = [];
    C.proc_return = Void;
    C.proc_important_vars =  [];
    C.proc_dynamic_specs = dynamic_specs;
    C.proc_stk_of_static_specs = new Gen.stack_pr "static-specs"
      Cprinter.string_of_struc_formula (==);
    C.proc_hprel_ass = [];
    C.proc_hprel_unkmap = [];
    C.proc_sel_hps = [];
    C.proc_sel_post_hps = [];
    C.proc_hpdefs = [];
    C.proc_callee_hpdefs = [];
    C.proc_by_name_params = [];
    C.proc_by_copy_params = [];
    C.proc_by_value_params = [];
    C.proc_body = Some block_exp;
    C.proc_logical_vars = [];
    C.proc_call_order = 0;
    C.proc_is_main = false;
    C.proc_is_invoked = false;
    C.proc_verified_domains = [];
    C.proc_is_recursive = false;
    C.proc_file = proc.C.proc_file;
    C.proc_loc = proc.C.proc_loc;
    C.proc_test_comps = None;
  } in
  let () = proc.C.proc_stk_of_static_specs # push_pr
             (x_loc ^ "init of proc_stk_of_static_specs") specs in
  proc

let mk_fcode_cprocs iprog var_decls =
  let fcode_prog = create_fcode_proc var_decls Void in
  let fcode_prog = {iprog with
                    I.prog_hp_decls = fcode_prog.I.prog_hp_decls;
                    I.prog_proc_decls = fcode_prog.I.prog_proc_decls} in
  let fcode_cprog,_ = Astsimp.trans_prog fcode_prog in
  let fcode_cprocs =
    C.list_of_procs fcode_cprog
    |> List.filter (fun x -> is_substr fcode_str x.C.proc_name) in
  fcode_cprocs


let create_tmpl_body_block_x (body : C.exp) (block : C.exp list) var_decls =
  let replace_pos = block |> List.map C.pos_of_exp |> List.rev |> List.hd in
  let replace_exp = block |> List.rev |> List.hd in
  let removed_exps = block |> List.rev |> List.tl in
  let fcode = create_cast_fcode var_decls replace_pos in
  let rec helper exp = match exp with
    | C.Block e ->
      helper e.C.exp_block_body
    | C.Seq e ->
      (helper e.C.exp_seq_exp1) @ (helper e.C.exp_seq_exp2)
    | C.Label e -> helper e.C.exp_label_exp
    | _ -> [exp] in
  let rec aux exp = match exp with
    | C.Block e ->
      let n_e = aux e.C.exp_block_body in
      C.Block {e with exp_block_body = n_e}
    | C.Seq e ->
      let e1 = e.C.exp_seq_exp1 in
      let e1_list = helper e1 in
      let subset l1 l2 = List.for_all (fun e -> List.mem e l2) l1 in
      if subset e1_list removed_exps
      then aux e.C.exp_seq_exp2
      else
        let e2 = e.C.exp_seq_exp2 in
        C.Seq {e with exp_seq_exp1 = aux e1;
                           exp_seq_exp2 = aux e2}
    | C.Label e ->
      let n_e = aux e.C.exp_label_exp in
      Label {e with exp_label_exp = n_e}
    | C.Cond e ->
      let e1 = aux e.C.exp_cond_then_arm in
      let e2 = aux e.C.exp_cond_else_arm in
      C.Cond {e with exp_cond_then_arm = e1;
                     exp_cond_else_arm = e2}
    | _ ->
      if exp = replace_exp then fcode
      else exp in
  aux body

let create_tmpl_body_block (body: C.exp) block var_decls =
  Debug.no_2 "create_tmpl_body_block" pr_c_exp pr_c_exps pr_c_exp
    (fun _ _ -> create_tmpl_body_block_x body block var_decls) body block

let reset_repair_straight_line var_decls replace_pos =
  let () = Syn.is_return_cand := false in
  let () = Syn.block_var_decls := var_decls in
  let () = Synthesis.entailments := [] in
  let () = Syn.repair_pos := Some replace_pos in
  let () = verified_procs := [] in
  ()

let reset_repair_block () =
  let () = Synthesis.entailments := [] in
  ()

let create_tmpl_body_stmt (block: C.exp list) var_decls sub_block =
  let replace_pos = sub_block |> List.map C.pos_of_exp |> List.hd in
  let fcode = create_cast_fcode var_decls replace_pos in
  let statement = sub_block |> List.rev |> List.hd in
  let to_delete = sub_block |> List.rev |> List.tl in
  let filter x = not(List.mem x to_delete) in
  let block = List.filter filter block in
  let helper stmt =
    if stmt = statement then fcode
    else stmt in
  let block = List.map helper block in
  create_block_exp block

  (* let rec aux (exp:C.exp) = match exp with
   *   | C.Seq e ->
   *     let n_e1 = aux e.C.exp_seq_exp1 in
   *     let n_e2 = aux e.C.exp_seq_exp2 in
   *     C.Seq {e with exp_seq_exp1 = n_e1;
   *                   exp_seq_exp2 = n_e2;}
   *   | C.VarDecl _ -> exp
   *   | C.Sharp _ -> exp
   *   | _ -> let pos = C.pos_of_exp exp in
   *     if eq_loc pos replace_pos then fcode
   *     else exp in
   * aux body *)

let is_var_decl (exp: C.exp) = match exp with
  | C.VarDecl _ -> true
  | _ -> false

let is_suspect_exp (exp: C.exp) = match exp with
  | C.Assign _ | C.Bind _ -> true
  | _ -> false

let create_sub_blocks (block : C.exp list) =
  let get_ln x =
    let pos = x |> C.pos_of_exp in
    pos.start_pos.Lexing.pos_lnum in
  let pos_list = block |> List.map get_ln in
  let pos_list = pos_list |> Gen.BList.remove_dups_eq (=) in
  let sub_blocks = pos_list |> List.map
                     (fun x -> List.filter (fun y -> (get_ln y) = x) block) in
  sub_blocks

let create_tmpl_proc (iprog: I.prog_decl) (prog : C.prog_decl) (proc : C.proc_decl)
    (block: C.exp list) =
  let pos_list = block |> List.map C.pos_of_exp
               |> Gen.BList.remove_dups_eq eq_loc |> List.rev in
  let replace_pos = List.hd pos_list in
  let proc_args = proc.C.proc_args in
  let body = proc.C.proc_body |> Gen.unsome in
  let helper t = match t with
    | Named _ | Int -> true
    | _ -> false in
  let var_decls = get_var_decls replace_pos body
                |> List.filter (fun (x, _) -> helper x) in
  let var_decls = proc_args @ var_decls in
  let fcode_prog = create_fcode_proc var_decls Void in
  let n_proc_decls = iprog.I.prog_proc_decls @ fcode_prog.I.prog_proc_decls in
  let n_hp_decls = iprog.I.prog_hp_decls @ fcode_prog.I.prog_hp_decls in
  let eq_data_decl x y = eq_str x.I.data_name y.I.data_name in
  let n_data_decls = iprog.I.prog_data_decls
                     @ fcode_prog.I.prog_data_decls
                     |> Gen.BList.remove_dups_eq eq_data_decl in
  let eq_proc x y = eq_str x.I.proc_name y.I.proc_name in
  let procs = iprog.I.prog_proc_decls @ fcode_prog.I.prog_proc_decls
              |> Gen.BList.remove_dups_eq eq_proc in
  let fcode_prog = {iprog with
                    I.prog_hp_decls = fcode_prog.I.prog_hp_decls;
                    I.prog_proc_decls = fcode_prog.I.prog_proc_decls} in
  let () = x_tinfo_hp (add_str "fcode" pr_iprog) fcode_prog no_pos in
  let fcode_cprog,_ = Astsimp.trans_prog fcode_prog in
  let n_body = create_tmpl_body_block body block var_decls in
  let () = x_tinfo_hp (add_str "n_body" pr_c_exp) n_body no_pos in
  let n_proc = {proc with C.proc_body = Some n_body} in
  (* report_error no_pos "to debug template proc" *)
  let fcode_cprocs = C.list_of_procs fcode_cprog in
  let n_prog = C.replace_proc prog n_proc in
  let all_procs = C.list_of_procs n_prog in
  let all_procs = all_procs @ fcode_cprocs in
  let n_hashtbl = C.create_proc_decls_hashtbl all_procs in
  let c_hp_decls = prog.C.prog_hp_decls @ fcode_cprog.C.prog_hp_decls in
  let n_prog = {prog with new_proc_decls = n_hashtbl;
                          C.prog_hp_decls = c_hp_decls} in
  let n_iprog = {iprog with I.prog_proc_decls = n_proc_decls;
                            I.prog_hp_decls = n_hp_decls} in
  let () = x_tinfo_hp (add_str "n_prog" pr_cprog) n_prog no_pos in
  let () = if is_return_block block then
      Syn.is_return_cand := true
    else Syn.is_return_cand := false in
  let specs = (n_proc.Cast.proc_stk_of_static_specs # top) in
  let post_proc = specs |> Syn.get_post_cond |> Syn.rm_emp_formula in
  let res_vars = CF.fv post_proc |> List.filter CP.is_res_sv
                 |> CP.remove_dups_svl in
  let () = Syn.syn_res_vars := res_vars in
  (n_iprog, n_prog, n_proc)


let buggy_num_strategy body =
  let rec aux exp changed =
    if changed then exp, true
    else
      match exp with
      | I.Block block ->
        let n_block, res = aux block.I.exp_block_body changed in
        (I.Block {block with exp_block_body = n_block}, res)
      | I.Label (a, l) ->
        let n_l, res = aux l changed in
        (I.Label (a, n_l), res)
      | I.Seq seq ->
        let (n_e1, r1) = aux seq.I.exp_seq_exp1 changed in
        let (n_e2, r2) = aux seq.I.exp_seq_exp2 r1 in
        (I.Seq {seq with exp_seq_exp1 = n_e1;
                         exp_seq_exp2 = n_e2}, r2)
      | I.Cond cond ->
        let (n_e1, r1) = aux cond.I.exp_cond_condition changed in
        let (n_e2, r2) = aux cond.I.exp_cond_then_arm r1 in
        let (n_e3, r3) = aux cond.I.exp_cond_else_arm r2 in
        let n_e = I.Cond {cond with exp_cond_condition = n_e1;
                                    exp_cond_then_arm = n_e2;
                                    exp_cond_else_arm = n_e3} in
        (n_e, r3)
      | I.Assign e ->
        let n_e1, r1 = aux e.I.exp_assign_lhs changed in
        let n_e2, r2 = aux e.I.exp_assign_rhs r1 in
        (I.Assign {e with exp_assign_lhs = n_e1;
                          exp_assign_rhs = n_e2}, r2)
      | I.IntLit num ->
        let n_num = num.I.exp_int_lit_val + 3 in
        (I.IntLit {num with exp_int_lit_val = n_num}, true)
      | I.Return e ->
        let n_e, res = match e.I.exp_return_val with
          | None -> None, false
          | Some r_e ->
            let n_r, res = aux r_e changed in
            (Some n_r, res) in
        (I.Return {e with exp_return_val = n_e}, res)
      | I.Binary bin ->
        let n_e1, r1 = aux bin.I.exp_binary_oper1 changed in
        let n_e2, r2 = aux bin.I.exp_binary_oper2 r1 in
        (I.Binary {bin with exp_binary_oper1 = n_e1;
                            exp_binary_oper2 = n_e2}, r2)
      | _ -> (exp, false) in
  aux body false

(* different numeric constraint: n -> n + 3 *)
let buggy_num_dif_pos body dif_num =
  let rec aux exp changed =
    if changed = 0 then exp, 0
    else
      match exp with
      | I.Block block ->
        let n_block, res = aux block.I.exp_block_body changed in
        (I.Block {block with exp_block_body = n_block}, res)
      | I.Label (a, l) ->
        let n_l, res = aux l changed in
        (I.Label (a, n_l), res)
      | I.Seq seq ->
        let (n_e1, r1) = aux seq.I.exp_seq_exp1 changed in
        let (n_e2, r2) = aux seq.I.exp_seq_exp2 r1 in
        (I.Seq {seq with exp_seq_exp1 = n_e1;
                         exp_seq_exp2 = n_e2}, r2)
      | I.Cond cond ->
        let (n_e1, r1) = aux cond.I.exp_cond_condition changed in
        let (n_e2, r2) = aux cond.I.exp_cond_then_arm r1 in
        let (n_e3, r3) = aux cond.I.exp_cond_else_arm r2 in
        let n_e = I.Cond {cond with exp_cond_condition = n_e1;
                                    exp_cond_then_arm = n_e2;
                                    exp_cond_else_arm = n_e3} in
        (n_e, r3)
      | I.Assign e ->
        let n_e1, r1 = aux e.I.exp_assign_lhs changed in
        let n_e2, r2 = aux e.I.exp_assign_rhs r1 in
        (I.Assign {e with exp_assign_lhs = n_e1;
                          exp_assign_rhs = n_e2}, r2)
      | I.IntLit num ->
        if changed = 1 then
          let n_num = num.I.exp_int_lit_val + 3 in
          (I.IntLit {num with exp_int_lit_val = n_num}, changed - 1)
        else (exp, changed - 1)
      | I.Return e ->
        let n_e, res = match e.I.exp_return_val with
          | None -> None, changed
          | Some r_e ->
            let n_r, res = aux r_e changed in
            (Some n_r, res) in
        (I.Return {e with exp_return_val = n_e}, res)
      | I.Binary bin ->
        let n_e1, r1 = aux bin.I.exp_binary_oper1 changed in
        let n_e2, r2 = aux bin.I.exp_binary_oper2 r1 in
        (I.Binary {bin with exp_binary_oper1 = n_e1;
                            exp_binary_oper2 = n_e2}, r2)
      | _ -> (exp, changed) in
  aux body dif_num

(* to delete one branch *)
let delete_one_branch body dif_num =
  let rec aux exp changed =
    if changed = 0 then exp, 0
    else
      match exp with
      | I.Block block ->
        let n_block, res = aux block.I.exp_block_body changed in
        (I.Block {block with exp_block_body = n_block}, res)
      | I.Label (a, l) ->
        let n_l, res = aux l changed in
        (I.Label (a, n_l), res)
      | I.Seq seq ->
        let (n_e1, r1) = aux seq.I.exp_seq_exp1 changed in
        let (n_e2, r2) = aux seq.I.exp_seq_exp2 r1 in
        (I.Seq {seq with exp_seq_exp1 = n_e1;
                         exp_seq_exp2 = n_e2}, r2)
      | I.Cond cond ->
        if changed = 1 then
          let n_e = I.Empty (I.get_exp_pos cond.I.exp_cond_then_arm) in
          let n_cond = I.Cond {cond with exp_cond_then_arm = n_e} in
          (n_cond, 0)
        else
          let (n_e1, r1) = aux cond.I.exp_cond_condition changed in
          let (n_e2, r2) = aux cond.I.exp_cond_then_arm r1 in
          let (n_e3, r3) = aux cond.I.exp_cond_else_arm r2 in
          let n_e = I.Cond {cond with exp_cond_condition = n_e1;
                                      exp_cond_then_arm = n_e2;
                                      exp_cond_else_arm = n_e3} in
          (n_e, r3)
      | I.Assign e ->
        let n_e1, r1 = aux e.I.exp_assign_lhs changed in
        let n_e2, r2 = aux e.I.exp_assign_rhs r1 in
        (I.Assign {e with exp_assign_lhs = n_e1;
                          exp_assign_rhs = n_e2}, r2)
      | I.Return e ->
        let n_e, res = match e.I.exp_return_val with
          | None -> None, changed
          | Some r_e ->
            let n_r, res = aux r_e changed in
            (Some n_r, res) in
        (I.Return {e with exp_return_val = n_e}, res)
      | _ -> (exp, changed) in
  aux body dif_num

(* x = y -> x != y *)
let buggy_boolean_exp body dif_num =
  let rec aux exp changed =
    if changed = 0 then exp, 0
    else
      match exp with
      | I.Block block ->
        let n_block, res = aux block.I.exp_block_body changed in
        (I.Block {block with exp_block_body = n_block}, res)
      | I.Label (a, l) ->
        let n_l, res = aux l changed in
        (I.Label (a, n_l), res)
      | I.Seq seq ->
        let (n_e1, r1) = aux seq.I.exp_seq_exp1 changed in
        let (n_e2, r2) = aux seq.I.exp_seq_exp2 r1 in
        (I.Seq {seq with exp_seq_exp1 = n_e1;
                         exp_seq_exp2 = n_e2}, r2)
      | I.Cond cond ->
        let (n_e1, r1) = aux cond.I.exp_cond_condition changed in
        let (n_e2, r2) = aux cond.I.exp_cond_then_arm r1 in
        let (n_e3, r3) = aux cond.I.exp_cond_else_arm r2 in
        let n_e = I.Cond {cond with exp_cond_condition = n_e1;
                                    exp_cond_then_arm = n_e2;
                                    exp_cond_else_arm = n_e3} in
        (n_e, r3)
      | I.Assign e ->
        let n_e1, r1 = aux e.I.exp_assign_lhs changed in
        let n_e2, r2 = aux e.I.exp_assign_rhs r1 in
        (I.Assign {e with exp_assign_lhs = n_e1;
                          exp_assign_rhs = n_e2}, r2)
      | I.Return e ->
        let n_e, res = match e.I.exp_return_val with
          | None -> None, changed
          | Some r_e ->
            let n_r, res = aux r_e changed in
            (Some n_r, res) in
        (I.Return {e with exp_return_val = n_e}, res)
      | I.Binary bin ->
        let changed, n_op = match bin.I.exp_binary_op with
          | I.OpEq -> (changed - 1, I.OpNeq)
          | _ -> (changed, bin.I.exp_binary_op) in
        let n_e1, r1 = aux bin.I.exp_binary_oper1 changed in
        let n_e2, r2 = aux bin.I.exp_binary_oper2 r1 in
        (I.Binary {bin with exp_binary_oper1 = n_e1;
                            exp_binary_op = n_op;
                            exp_binary_oper2 = n_e2}, r2)
      | _ -> (exp, changed) in
  aux body dif_num

(* x->next : x *)
let buggy_mem_dif_pos body dif_num =
  let rec aux exp changed =
    let rec helper args changed = match args with
      | [] -> [], changed
      | head::tail ->
        let n_h, n_changed = aux head changed in
        let n_tail, n_changed = helper tail n_changed in
        (n_h::n_tail, n_changed) in
    if changed = 0 then exp, 0
    else
      match exp with
      | I.Block block ->
        let n_block, res = aux block.I.exp_block_body changed in
        (I.Block {block with exp_block_body = n_block}, res)
      | I.Label (a, l) ->
        let n_l, res = aux l changed in
        (I.Label (a, n_l), res)
      | I.Seq seq ->
        let (n_e1, r1) = aux seq.I.exp_seq_exp1 changed in
        let (n_e2, r2) = aux seq.I.exp_seq_exp2 r1 in
        (I.Seq {seq with exp_seq_exp1 = n_e1;
                         exp_seq_exp2 = n_e2}, r2)
      | I.Cond cond ->
        let (n_e1, r1) = aux cond.I.exp_cond_condition changed in
        let (n_e2, r2) = aux cond.I.exp_cond_then_arm r1 in
        let (n_e3, r3) = aux cond.I.exp_cond_else_arm r2 in
        let n_e = I.Cond {cond with exp_cond_condition = n_e1;
                                    exp_cond_then_arm = n_e2;
                                    exp_cond_else_arm = n_e3} in
        (n_e, r3)
      | I.Assign e ->
        let n_e1, r1 = aux e.I.exp_assign_lhs changed in
        let n_e2, r2 = aux e.I.exp_assign_rhs r1 in
        (I.Assign {e with exp_assign_lhs = n_e1;
                          exp_assign_rhs = n_e2}, r2)
      | I.CallRecv e ->
        let args = e.I.exp_call_recv_arguments in
        let n_args, n_changed = helper args changed in
        let n_exp = I.CallRecv {e with exp_call_recv_arguments = n_args;} in
        (n_exp, n_changed)
      | I.CallNRecv e ->
        let args = e.I.exp_call_nrecv_arguments in
        let n_args, n_changed = helper args changed in
        let n_exp = I.CallNRecv {e with exp_call_nrecv_arguments = n_args;} in
        (n_exp, n_changed)
      | I.Member e ->
        if changed = 1 then (e.I.exp_member_base, 0)
        else (exp, changed - 1)
      | I.Return e ->
        let n_e, res = match e.I.exp_return_val with
          | None -> None, changed
          | Some r_e ->
            let n_r, res = aux r_e changed in
            (Some n_r, res) in
        (I.Return {e with exp_return_val = n_e}, res)
      | I.Binary bin ->
        let n_e1, r1 = aux bin.I.exp_binary_oper1 changed in
        let n_e2, r2 = aux bin.I.exp_binary_oper2 r1 in
        (I.Binary {bin with exp_binary_oper1 = n_e1;
                            exp_binary_oper2 = n_e2}, r2)
      | _ -> (exp, changed) in
  aux body dif_num
