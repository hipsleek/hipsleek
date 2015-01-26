open Globals
open Cformula
open Cpure
open Mcpure

module CP = Cpure
module MCP = Mcpure

type vperm_res = 
  | Fail of list_context
  | Succ of entail_state

let vperm_entail_rhs estate lhs_p rhs_p pos = 
  let old_lhs_zero_vars = estate.es_var_zero_perm in
  let rhs_vperms, _ = MCP.filter_varperm_mix_formula rhs_p in
  (*find a closure of exist vars*)
  let func v = 
    if (List.mem v estate.es_evars) then find_closure_mix_formula v lhs_p
    else [v]
  in
  (* let lhs_zero_vars = List.concat (List.map (fun v -> find_closure_mix_formula v lhs_p) old_lhs_zero_vars) in *)
  let lhs_zero_vars = List.concat (List.map func old_lhs_zero_vars) in
  (* let _ = print_endline ("zero_vars = " ^ (Cprinter.string_of_spec_var_list lhs_zero_vars)) in *)
  let _ = if (!Globals.ann_vp) && (lhs_zero_vars!=[] || rhs_vperms!=[]) then
    Debug.devel_pprint ("heap_entail_empty_rhs_heap: checking " ^(string_of_vp_ann VP_Zero)^ (Cprinter.string_of_spec_var_list lhs_zero_vars) ^ " |- "  ^ (pr_list Cprinter.string_of_pure_formula rhs_vperms)^"\n") pos
  in
  let rhs_val, rhs_vrest = List.partition (fun f -> CP.is_varperm_of_typ f VP_Value) rhs_vperms in
  (* let rhs_ref, rhs_vrest2 = List.partition (fun f -> CP.is_varperm_of_typ f VP_Ref) rhs_vrest in *)
  let rhs_full, rhs_vrest3 = List.partition (fun f -> CP.is_varperm_of_typ f VP_Full) rhs_vrest in
  (* let _ = print_endline ("\n LDK: " ^ (pr_list Cprinter.string_of_pure_formula rhs_vrest3)) in *)
  let _ = if (rhs_vrest3!=[]) then
    print_endline ("[Warning] heap_entail_empty_rhs_heap: the conseq should not include variable permissions other than " ^ (string_of_vp_ann VP_Value) ^ " and " ^ (string_of_vp_ann VP_Full))
        (*ignore those var perms in rhs_vrest3*)
  in
  let rhs_val_vars = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Value)) rhs_val) in
  (* let rhs_ref_vars = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Ref)) rhs_ref) in *)
  let rhs_full_vars = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Full)) rhs_full) in
  (* v@zero  |- v@value --> fail *)
  (* v@zero  |- v@full --> fail *)
  let tmp1 = Gen.BList.intersect_eq CP.eq_spec_var_ident lhs_zero_vars (rhs_val_vars) in
  let tmp3 = Gen.BList.intersect_eq CP.eq_spec_var_ident lhs_zero_vars (rhs_full_vars) in
  let dup_vars = Gen.BList.find_dups_eq CP.eq_spec_var_ident rhs_full_vars in
  if (!Globals.ann_vp) && (tmp1!=[] (* || tmp2!=[ ]*) || tmp3!=[] || dup_vars !=[]) then
    begin
      (*FAIL*)
        let msg1 = 
          if (dup_vars !=[]) then 
            let msg = (": full permission var " ^ (Cprinter.string_of_spec_var_list (dup_vars))^ " cannot be duplicated" ^ "\n") in
            let _ = Debug.devel_pprint ("heap_entail_empty_rhs_heap" ^ msg) pos in
            msg
          else ""
        in
        let msg2 = if tmp1!=[] then
              let msg = (": pass-by-val var " ^ (Cprinter.string_of_spec_var_list (tmp1))^ " cannot have possibly zero permission" ^ "\n") in
              let _ = Debug.devel_pprint ("heap_entail_empty_rhs_heap" ^ msg) pos in
              msg
            else ""
        in
        let msg3 = if tmp3!=[] then 
              let msg = (": full permission var " ^ (Cprinter.string_of_spec_var_list (tmp3))^ " cannot have possibly zero permission" ^ "\n") in
              let _ = Debug.devel_pprint ("heap_entail_empty_rhs_heap" ^ msg) pos in
              msg
            else ""
        in
      Debug.devel_pprint ("heap_entail_empty_rhs_heap: failed in entailing variable permissions in conseq\n") pos;
      Debug.devel_pprint ("heap_entail_empty_rhs_heap: formula is not valid\n") pos;
      let rhs_p = List.fold_left (fun mix_f vperm -> memoise_add_pure_N mix_f vperm) rhs_p rhs_vperms in
      (* picking original conseq since not found here *)
      let conseq = (formula_of_mix_formula rhs_p pos) in
      let rhs_b = extr_rhs_b conseq in
      let err_o = mkFailCtx_vperm (msg1 ^ "\n" ^ msg2 ^ "\n" ^ msg3) rhs_b estate conseq (mk_cex true) pos in
      Fail err_o
    end
  else
    (* not(v \in S) *)
    (* -------------------- *)
    (* S@zero |- v@value  --> S@Z *)


    (*        not(v \in S) *)
    (* ----------------------- *)
    (* S@zero |- v@full  --> S+{v}@Z *)
    (*note: use the old_lhs_zero_vars, not use its closure*)
    let estate = if not (!Globals.ann_vp) then estate else
      let new_lhs_zero_vars = (old_lhs_zero_vars@rhs_full_vars) in (*TO CHECK*)
      {estate with es_var_zero_perm=new_lhs_zero_vars}
    in Succ estate