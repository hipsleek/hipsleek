#include "xdebug.cppo"
open VarGen
open Printf
open Gen.Basic
open Globals

module I = Iast
(* Generate repair candidates *)
(* mutation strategy *)

let pr_exp = Iprinter.string_of_exp_repair
let pr_bool = string_of_bool

let equal_to_not_equal eq_exp =
  let to_neq_ref = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Binary b_exp ->
      let n_bin_op =
        match b_exp.I.exp_binary_op with
        | I.OpEq ->
          let () = to_neq_ref := true in
          I.OpNeq
        | _ -> b_exp.I.exp_binary_op in
      I.Binary {b_exp with I.exp_binary_op = n_bin_op}
    | I.Seq seq ->
      let n_exp1 = aux_exp seq.I.exp_seq_exp1 in
      let n_exp2 = if !to_neq_ref then seq.I.exp_seq_exp2
        else aux_exp seq.I.exp_seq_exp2 in
      I.Seq {seq with I.exp_seq_exp1 = n_exp1;
                      I.exp_seq_exp2 = n_exp2;}
    | I.Cond cond_exp ->
      let n_condition = aux_exp cond_exp.I.exp_cond_condition in
      I.Cond {cond_exp with I.exp_cond_condition = n_condition}
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | _ -> i_exp in
  let not_eq_exp = aux_exp eq_exp in
  (not_eq_exp, !to_neq_ref)

let eq_to_neq_two_left eq_exp =
  let to_neq_ref = ref false in
  let activated = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Binary b_exp ->
      let n_bin_op =
        match b_exp.I.exp_binary_op with
        | I.OpEq ->
          let () = to_neq_ref := true in
          I.OpNeq
        | _ -> b_exp.I.exp_binary_op in
      I.Binary {b_exp with I.exp_binary_op = n_bin_op}
    | I.Seq seq ->
      let n_exp1 = aux_exp seq.I.exp_seq_exp1 in
      let n_exp2 = if !to_neq_ref then seq.I.exp_seq_exp2
        else aux_exp seq.I.exp_seq_exp2 in
      I.Seq {seq with I.exp_seq_exp1 = n_exp1;
                      I.exp_seq_exp2 = n_exp2;}
    | I.Cond cond_exp ->
      if !activated then
        let n_cond = aux_exp cond_exp.I.exp_cond_condition in
        I.Cond {cond_exp with I.exp_cond_condition = n_cond}
      else
        let () = activated := true in
        let n_left = aux_exp cond_exp.I.exp_cond_then_arm in
        I.Cond {cond_exp with I.exp_cond_then_arm = n_left}
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | _ -> i_exp in
  let not_eq_exp = aux_exp eq_exp in
  (not_eq_exp, !to_neq_ref)

let eq_to_neq_two_left i_exp =
  Debug.no_1 "eq_to_neq_two_left" pr_exp (pr_pair pr_exp pr_bool)
    (fun _ -> eq_to_neq_two_left i_exp) i_exp

let equal_to_neq_two_right eq_exp =
  let to_neq_ref = ref false in
  let activated = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Binary b_exp ->
      let n_bin_op =
        match b_exp.I.exp_binary_op with
        | I.OpEq ->
          let () = to_neq_ref := true in
          I.OpNeq
        | _ -> b_exp.I.exp_binary_op in
      I.Binary {b_exp with I.exp_binary_op = n_bin_op}
    | I.Seq seq ->
      let n_exp1 = aux_exp seq.I.exp_seq_exp1 in
      let n_exp2 = if !to_neq_ref then seq.I.exp_seq_exp2
        else aux_exp seq.I.exp_seq_exp2 in
      I.Seq {seq with I.exp_seq_exp1 = n_exp1;
                      I.exp_seq_exp2 = n_exp2;}
    | I.Cond cond_exp ->
      if !activated then
        let n_cond = aux_exp cond_exp.I.exp_cond_condition in
        I.Cond {cond_exp with I.exp_cond_condition = n_cond}
      else
        let () = activated := true in
        let n_right = aux_exp cond_exp.I.exp_cond_else_arm in
        I.Cond {cond_exp with I.exp_cond_else_arm = n_right}
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | _ -> i_exp in
  let not_eq_exp = aux_exp eq_exp in
  (not_eq_exp, !to_neq_ref)

let not_equal_to_equal n_equal_exp =
  let to_eq_ref = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Binary b_exp ->
      let n_bin_op =
        match b_exp.I.exp_binary_op with
        | I.OpNeq ->
          let () = to_eq_ref := true in
          I.OpEq
        | _ -> b_exp.I.exp_binary_op in
      I.Binary {b_exp with I.exp_binary_op = n_bin_op}
    | I.Seq seq ->
      let n_exp1 = aux_exp seq.I.exp_seq_exp1 in
      let n_exp2 = if !to_eq_ref then seq.I.exp_seq_exp2
        else aux_exp seq.I.exp_seq_exp2 in
      I.Seq {seq with I.exp_seq_exp1 = n_exp1;
                      I.exp_seq_exp2 = n_exp2;}
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | I.Cond cond_exp ->
      let n_condition = aux_exp cond_exp.I.exp_cond_condition in
      I.Cond {cond_exp with I.exp_cond_condition = n_condition}
    | _ -> i_exp in
  let eq_exp = aux_exp n_equal_exp in
  (eq_exp, !to_eq_ref)

let neq_to_eq_two_left n_equal_exp =
  let to_eq_ref = ref false in
  let activated = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Binary b_exp ->
      let n_bin_op =
        match b_exp.I.exp_binary_op with
        | I.OpNeq ->
          let () = to_eq_ref := true in
          I.OpEq
        | _ -> b_exp.I.exp_binary_op in
      I.Binary {b_exp with I.exp_binary_op = n_bin_op}
    | I.Seq seq ->
      let n_exp1 = aux_exp seq.I.exp_seq_exp1 in
      let n_exp2 = if !to_eq_ref then seq.I.exp_seq_exp2
        else aux_exp seq.I.exp_seq_exp2 in
      I.Seq {seq with I.exp_seq_exp1 = n_exp1;
                      I.exp_seq_exp2 = n_exp2;}
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | I.Cond cond_exp ->
      if !activated then
        let n_condition = aux_exp cond_exp.I.exp_cond_condition in
        I.Cond {cond_exp with I.exp_cond_condition = n_condition}
      else
        let () = activated := true in
        let n_left = aux_exp cond_exp.I.exp_cond_then_arm in
        I.Cond {cond_exp with I.exp_cond_then_arm = n_left}
    | _ -> i_exp in
  let eq_exp = aux_exp n_equal_exp in
  (eq_exp, !to_eq_ref)

let neq_to_eq_two_right n_equal_exp =
  let to_eq_ref = ref false in
  let activated = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Binary b_exp ->
      let n_bin_op =
        match b_exp.I.exp_binary_op with
        | I.OpNeq ->
          let () = to_eq_ref := true in
          I.OpEq
        | _ -> b_exp.I.exp_binary_op in
      I.Binary {b_exp with I.exp_binary_op = n_bin_op}
    | I.Seq seq ->
      let n_exp1 = aux_exp seq.I.exp_seq_exp1 in
      let n_exp2 = if !to_eq_ref then seq.I.exp_seq_exp2
        else aux_exp seq.I.exp_seq_exp2 in
      I.Seq {seq with I.exp_seq_exp1 = n_exp1;
                      I.exp_seq_exp2 = n_exp2;}
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | I.Cond cond_exp ->
      if !activated then
        let n_condition = aux_exp cond_exp.I.exp_cond_condition in
        I.Cond {cond_exp with I.exp_cond_condition = n_condition}
      else
        let () = activated := true in
        let n_left = aux_exp cond_exp.I.exp_cond_else_arm in
        I.Cond {cond_exp with I.exp_cond_else_arm = n_left}
    | _ -> i_exp in
  let eq_exp = aux_exp n_equal_exp in
  (eq_exp, !to_eq_ref)

let remove_field_in_condition n_equal_exp var_decls data_decls =
  let rm_field_strategy = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | I.Seq seq ->
      let n_exp1 = aux_exp seq.I.exp_seq_exp1 in
      let n_exp2 = if !rm_field_strategy then seq.I.exp_seq_exp2
        else aux_exp seq.I.exp_seq_exp2 in
      I.Seq {seq with I.exp_seq_exp1 = n_exp1;
                      I.exp_seq_exp2 = n_exp2;}
    | I.Binary b_exp ->
      let n_lhs = aux_exp b_exp.I.exp_binary_oper1 in
      let n_rhs = if !rm_field_strategy then b_exp.I.exp_binary_oper2
        else aux_exp b_exp.I.exp_binary_oper2 in
      I.Binary {b_exp with I.exp_binary_oper1 = n_lhs;
                           I.exp_binary_oper2 = n_rhs}
    | I.Cast cast_exp ->
      let n_exp = aux_exp cast_exp.I.exp_cast_body in
      I.Cast {cast_exp with I.exp_cast_body = n_exp}
    | I.Cond cond_exp ->
      let (removed_field_exp, is_changed, _) =
        Repairpure.remove_field_infestor cond_exp.I.exp_cond_condition 1
          var_decls data_decls in
      if is_changed = 0 then
        let () = rm_field_strategy := true in
        I.Cond {cond_exp with I.exp_cond_condition = removed_field_exp}
      else i_exp
    | _ -> i_exp in
  let rm_field_exp = aux_exp n_equal_exp in
  (rm_field_exp, !rm_field_strategy)

let remove_field_in_cond_two_left n_equal_exp var_decls data_decls =
  let rm_field_strategy = ref false in
  let activated = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | I.Seq seq ->
      let n_exp1 = aux_exp seq.I.exp_seq_exp1 in
      let n_exp2 = if !rm_field_strategy then seq.I.exp_seq_exp2
        else aux_exp seq.I.exp_seq_exp2 in
      I.Seq {seq with I.exp_seq_exp1 = n_exp1;
                      I.exp_seq_exp2 = n_exp2;}
    | I.Binary b_exp ->
      let n_lhs = aux_exp b_exp.I.exp_binary_oper1 in
      let n_rhs = if !rm_field_strategy then b_exp.I.exp_binary_oper2
        else aux_exp b_exp.I.exp_binary_oper2 in
      I.Binary {b_exp with I.exp_binary_oper1 = n_lhs;
                           I.exp_binary_oper2 = n_rhs}
    | I.Cast cast_exp ->
      let n_exp = aux_exp cast_exp.I.exp_cast_body in
      I.Cast {cast_exp with I.exp_cast_body = n_exp}
    | I.Cond cond_exp ->
      if !activated then
        let (removed_field_exp, is_changed, _) =
          Repairpure.remove_field_infestor cond_exp.I.exp_cond_condition 1
            var_decls data_decls in
        if is_changed = 0 then
          let () = rm_field_strategy := true in
          I.Cond {cond_exp with I.exp_cond_condition = removed_field_exp}
        else i_exp
      else
        let () = activated := true in
        let n_left = aux_exp cond_exp.I.exp_cond_then_arm in
        I.Cond {cond_exp with I.exp_cond_then_arm = n_left}
    | _ -> i_exp in
  let rm_field_exp = aux_exp n_equal_exp in
  (rm_field_exp, !rm_field_strategy)

let remove_field_in_cond_two_left i_exp var_decls data_decls =
  Debug.no_1 "rm_field_two_left" pr_exp (pr_pair pr_exp pr_bool)
    (fun _ -> remove_field_in_cond_two_left i_exp var_decls data_decls) i_exp

let remove_field_in_cond_two_right n_equal_exp var_decls data_decls =
  let rm_field_strategy = ref false in
  let activated = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | I.Seq seq ->
      let n_exp1 = aux_exp seq.I.exp_seq_exp1 in
      let n_exp2 = if !rm_field_strategy then seq.I.exp_seq_exp2
        else aux_exp seq.I.exp_seq_exp2 in
      I.Seq {seq with I.exp_seq_exp1 = n_exp1;
                      I.exp_seq_exp2 = n_exp2;}
    | I.Binary b_exp ->
      let n_lhs = aux_exp b_exp.I.exp_binary_oper1 in
      let n_rhs = if !rm_field_strategy then b_exp.I.exp_binary_oper2
        else aux_exp b_exp.I.exp_binary_oper2 in
      I.Binary {b_exp with I.exp_binary_oper1 = n_lhs;
                           I.exp_binary_oper2 = n_rhs}
    | I.Cast cast_exp ->
      let n_exp = aux_exp cast_exp.I.exp_cast_body in
      I.Cast {cast_exp with I.exp_cast_body = n_exp}
    | I.Cond cond_exp ->
      if !activated then
        let (removed_field_exp, is_changed, _) =
          Repairpure.remove_field_infestor cond_exp.I.exp_cond_condition 1
            var_decls data_decls in
        if is_changed = 0 then
          let () = rm_field_strategy := true in
          I.Cond {cond_exp with I.exp_cond_condition = removed_field_exp}
        else i_exp
      else
        let () = activated := true in
        let n_left = aux_exp cond_exp.I.exp_cond_else_arm in
        I.Cond {cond_exp with I.exp_cond_else_arm = n_left}
    | _ -> i_exp in
  let rm_field_exp = aux_exp n_equal_exp in
  (rm_field_exp, !rm_field_strategy)

let add_field_in_condition n_equal_exp var_decls data_decls num =
  let add_field_strategy = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Unary u_exp ->
      let n_exp = aux_exp u_exp.I.exp_unary_exp in
      I.Unary {u_exp with I.exp_unary_exp = n_exp}
    | I.Cast cast_exp ->
      let n_exp = aux_exp cast_exp.I.exp_cast_body in
      I.Cast {cast_exp with I.exp_cast_body = n_exp}
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | I.Cond cond_exp ->
      let (add_field_exp, is_changed, _) =
        Repairpure.add_field_infestor cond_exp.I.exp_cond_condition num
          var_decls data_decls in
      if is_changed = 0 then
        let () = add_field_strategy := true in
        I.Cond {cond_exp with I.exp_cond_condition = add_field_exp}
      else i_exp
    | _ -> i_exp in
  let add_field_exp = aux_exp n_equal_exp in
  (add_field_exp, !add_field_strategy)

let add_field_in_cond_two_left n_equal_exp var_decls data_decls num =
  let add_field_strategy = ref false in
  let activated = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Unary u_exp ->
      let n_exp = aux_exp u_exp.I.exp_unary_exp in
      I.Unary {u_exp with I.exp_unary_exp = n_exp}
    | I.Cast cast_exp ->
      let n_exp = aux_exp cast_exp.I.exp_cast_body in
      I.Cast {cast_exp with I.exp_cast_body = n_exp}
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | I.Cond cond_exp ->
      if !activated then
        let (removed_field_exp, is_changed, _) =
          Repairpure.add_field_infestor cond_exp.I.exp_cond_condition num
            var_decls data_decls in
        if is_changed = 0 then
          let () = add_field_strategy := true in
          I.Cond {cond_exp with I.exp_cond_condition = removed_field_exp}
        else i_exp
      else
        let () = activated := true in
      let n_left = aux_exp cond_exp.I.exp_cond_then_arm in
        I.Cond {cond_exp with I.exp_cond_then_arm = n_left}
    | _ -> i_exp in
  let add_field_exp = aux_exp n_equal_exp in
  (add_field_exp, !add_field_strategy)

let add_field_in_cond_two_right n_equal_exp var_decls data_decls num =
  let add_field_strategy = ref false in
  let activated = ref false in
  let rec aux_exp i_exp = match i_exp with
    | I.Unary u_exp ->
      let n_exp = aux_exp u_exp.I.exp_unary_exp in
      I.Unary {u_exp with I.exp_unary_exp = n_exp}
    | I.Cast cast_exp ->
      let n_exp = aux_exp cast_exp.I.exp_cast_body in
      I.Cast {cast_exp with I.exp_cast_body = n_exp}
    | I.Block block ->
      I.Block {block with I.exp_block_body = aux_exp block.I.exp_block_body}
    | I.Label (a, l_exp) -> I.Label (a, aux_exp l_exp)
    | I.Cond cond_exp ->
      if !activated then
        let (removed_field_exp, is_changed, _) =
          Repairpure.add_field_infestor cond_exp.I.exp_cond_condition num
            var_decls data_decls in
        if is_changed = 0 then
          let () = add_field_strategy := true in
          I.Cond {cond_exp with I.exp_cond_condition = removed_field_exp}
        else i_exp
      else
        let () = activated := true in
      let n_left = aux_exp cond_exp.I.exp_cond_else_arm in
        I.Cond {cond_exp with I.exp_cond_else_arm = n_left}
    | _ -> i_exp in
  let add_field_exp = aux_exp n_equal_exp in
  (add_field_exp, !add_field_strategy)

let mutate_iast_exp iprog iproc (input_exp: I.exp) : I.exp list =
  let list = [] in
  let list = (equal_to_not_equal input_exp)::list in
  let list = (eq_to_neq_two_left input_exp)::list in
  let list = (equal_to_neq_two_right input_exp)::list in

  let list = (not_equal_to_equal input_exp)::list in
  let list = (neq_to_eq_two_left input_exp)::list in
  let list = (neq_to_eq_two_right input_exp)::list in
  let var_decls = iproc.I.proc_args |> List.map
                    (fun x -> (x.I.param_type, x.I.param_name)) in
  let data_decls = iprog.I.prog_data_decls in
  let rec aux_mutate1 body num list =
    let n_exp, is_changed = add_field_in_condition body var_decls
        data_decls num in
    if is_changed then
      let n_list = (n_exp, true)::list in
      aux_mutate1 body (num+1) n_list
    else list in
  let rec aux_mutate2 body num list =
    let n_exp, is_changed = add_field_in_cond_two_left body var_decls
        data_decls num in
    if is_changed then
      let n_list = (n_exp, true)::list in
      aux_mutate2 body (num+1) n_list
    else list in
  let rec aux_mutate3 body num list =
    let n_exp, is_changed = add_field_in_cond_two_right body var_decls
        data_decls num in
    if is_changed then
      let n_list = (n_exp, true)::list in
      aux_mutate3 body (num+1) n_list
    else list in

  let list = (aux_mutate1 input_exp 1 [])@list in
  let list = (aux_mutate2 input_exp 1 [])@list in
  let list = (aux_mutate3 input_exp 1 [])@list in
  (* let list = (add_field_in_cond_two_left input_exp var_decls data_decls)::list in
   * let list = (add_field_in_cond_two_right input_exp var_decls data_decls)::list in *)

  let list = (remove_field_in_condition input_exp var_decls data_decls)::list in
  let list = (remove_field_in_cond_two_left input_exp var_decls data_decls)::list in
  let list = (remove_field_in_cond_two_right input_exp var_decls data_decls)::list in
  list |> List.filter (fun (_,y) -> y) |> List.map fst

