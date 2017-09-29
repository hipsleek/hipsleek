#include "xdebug.cppo"
open Array_formula
open Array_biabduction_pre_condition
open Array_biabduction



let array_biabduction_partial_order_pair_content =
  let mkFreshContent () =
    let fresh_u_1 = global_get_new_var () in
    let fresh_u_2 = global_get_new_var () in
    ([fresh_u_1; fresh_u_2], (fresh_u_1, fresh_u_2))
  in
  let mkContentEq (v11, v12) (v21, v22) =
    mkAnd (mkEqSv v11 v21) (mkEqSv v12 v22)
  in
  array_biabduction_partial_order_generic mkContentEq mkFreshContent
;;
  

let trans_array_entailment_pair_content lhs rhs =
  let trans_array_entailment_generic mkTransformer mkContentEq lhs rhs =
    let match_common (lhs_h, rhs_h) var_info =
      let () = print_endline ("match_common " ^ (!str_pformula var_info)) in
      let is_eq v1 v2 =
        isValid (mkImply var_info (mkEqSv v1 v2))
      in
      let is_content_eq v1 v2 =
        isValid (mkImply var_info (mkContentEq v1 v2))
      in
      let helper h1 h2 =
        match h1, h2 with
        | AsegNE_p (a1, b1), AsegNE_p (a2, b2)
          | AsegNE_p (a1, b1), Aseg_p (a2, b2)
          | Aseg_p (a1, b1), AsegNE_p (a2, b2) ->
           is_eq a1 a2 && is_eq b1  b2
        | Pointsto_p (i1, v1), Pointsto_p (i2, v2) ->
           is_eq i1 i2 && is_content_eq v1 v2
        | _, _ -> false
      in

      let rec helper_entry lhead lhs_h rhead rhs_h =
        match lhs_h with
        | lh :: ltail ->
           begin match rhs_h with
           | rh :: rtail ->
              if helper lh rh
              then helper_entry lhead ltail [] (rhead @ rtail)
              else helper_entry lhead lhs_h (rh :: rhead) rtail
           | [] ->
              helper_entry (lh :: lhead) ltail [] (rhead @ rhs_h) end
        | [] ->
           (lhead, rhead @ rhs_h)
      in

      helper_entry [] lhs_h [] rhs_h
    in
    let get_hlst_var_lst hlst =
      let helper = function
        | AsegNE_p (a, b)
          | Aseg_p (a, b)
          | Gap_p (a, b)
          -> [a; b]
        | Pointsto_p (p, _) ->
           [p]
      in
      List.concat (List.map helper hlst)
    in
    
    
    let () = print_endline ("lhs: " ^ (!str_cformula lhs)) in
    let () = print_endline ("rhs: " ^ (!str_cformula rhs)) in
    let transLHS = mkTransformer lhs in
    let (l_elst, l_plst, l_hlst) = transLHS#formula_to_general_formula in
    let transRHS = mkTransformer rhs in
    let (r_elst, r_plst, r_hlst) = transRHS#formula_to_general_formula in
    let lhs_hlst_var_lst = get_hlst_var_lst l_hlst in
    let rhs_hlst_var_lst = get_hlst_var_lst r_hlst in
    let hlst_var_lst = lhs_hlst_var_lst @ rhs_hlst_var_lst in
    

    let is_heap_vars sv = List.exists (fun nsv -> is_same_sv nsv sv) hlst_var_lst in
    let not_heap_vars = List.filter (fun sv -> not (is_heap_vars sv)) ((get_fv_pure (mkAndlst l_plst)) @ (get_fv_pure (mkAndlst r_plst))) in
    
    let var_info = simplify (mkExists not_heap_vars (mkAndlst (l_plst @ r_plst))) in
    let (new_l_hlst, new_r_hlst) = match_common (l_hlst, r_hlst) var_info in

    let lhs_ptr_positive = mkAndlst (List.map mkPositive lhs_hlst_var_lst) in
    let rhs_ptr_positive = mkAndlst (List.map mkPositive rhs_hlst_var_lst) in
        
    ((transLHS#get_root, l_elst, (get_segment_pure l_hlst) @ [lhs_ptr_positive; get_disjoint_pure l_hlst] @ l_plst, new_l_hlst),
     (transRHS#get_root, r_elst, (get_segment_pure r_hlst) @ [rhs_ptr_positive; get_disjoint_pure r_hlst] @ r_plst, new_r_hlst),
     var_info)
  in
  trans_array_entailment_generic (fun f -> new arrPredTransformer_orig_pair_content f) (fun (v11, v12) (v21, v22) -> mkAnd (mkEqSv v11 v21) (mkEqSv v21 v22)) lhs rhs
;;
  



let array_entailment_classical_entailment_interface_pair_content lhs rhs =
  let ((lhs_root, lhs_e, lhs_p, lhs_h), (rhs_root, rhs_e, rhs_p, rhs_h), var_info) =
     trans_array_entailment_pair_content lhs rhs
  in
  let (f, norm) = array_biabduction_partial_order_pair_content (lhs_e, ([], lhs_p), mkStarForm lhs_h) (rhs_e, ([], rhs_p), mkStarForm rhs_h) var_info in
  if check_norm_validity norm (mkAndlst lhs_p) (mkAndlst rhs_p)
  then
    mkEmptySuccCtx ()
  else
    mkEmptyFailCtx ()
;;
