open Globals
open Cast
open Cformula
open Prooftracer
open Gen.Basic

module CP = Cpure
module PR = Cprinter
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher


(* ============================================== *)
(* cformula *)
(* ============================================== *)


(* ============================================== *)
(* Solver *)
(* ============================================== *)


(*pickup a node named "name" from a list of nodes*)
let pick_up_node_x (ls:CF.h_formula list) (name:ident):(CF.h_formula * CF.h_formula list) =
  let rec helper ls =
  match ls with
    | [] -> CF.HTrue,[]
    | x::xs ->
        match x with
          | ViewNode ({h_formula_view_node = c})
          | DataNode ({h_formula_data_node = c}) ->

              let c_str = (CP.name_of_spec_var c) in
              let ri = try  (String.rindex c_str '_') with  _ -> (String.length c_str) in
              let c_name = (String.sub c_str 0 ri)  in
              (* let _ = print_string ("pick_up_node:" ^ c_name ^ " &&"  ^ name ^ "\n\n " ) in *)
              if ((String.compare c_name name) ==0)
              then
                (x,xs)
              else
                let res1,res2 = helper xs in
                (res1,x::res2)
          | _ ->
              let res1,res2 = helper xs in
                (res1,x::res2)
  in helper ls



(*pickup a node named "name" from a list of nodes*)
let pick_up_node (ls:CF.h_formula list) (name:ident):(CF.h_formula * CF.h_formula list) =
  let rec pr xs = 
    match xs with
      | [] -> ""
      | x::xs1 -> (!print_h_formula x) ^ "|*|" ^ pr xs1
  in
  let pr2 (a,b) =
    (Cprinter.string_of_h_formula a) ^ "|&&&|"  ^ (pr b)
  in
  Gen.Debug.no_2 "pick_up_node"
      pr (fun id -> id) pr2
      pick_up_node_x ls name


let normalize_w_coers prog (estate:CF.entail_state) (coers:coercion_decl list) (h:h_formula) (p:MCP.mix_formula) : (h_formula * MCP.mix_formula) =
  let rec helper (estate:CF.entail_state) (h:h_formula) (p:MCP.mix_formula) : (h_formula*MCP.mix_formula) =
    (*try to check whether the current estate with h=anode*rest and pure=p 
      can entail the lhs of an coercion*)
    let process_one_x estate anode rest coer h p =
      let f = mkBase rest p CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in
      let coer_lhs = coer.coercion_head in
      let coer_rhs = coer.coercion_body in

      (*compute free vars in extra heap and guard*)
      let compute_extra_vars () =
        let lhs_heap, lhs_guard, _, _, _ = split_components coer_lhs in
        let lhs_hs = CF.split_star_conjunctions lhs_heap in (*|lhs_hs|>1*)
        let head_node, rest = pick_up_node lhs_hs Globals.self in
        (* let head_node = List.hd lhs_hs in *)
        (* let extra_opt = join_star_conjunctions_opt (List.tl lhs_hs) in *)
        let extra_opt = join_star_conjunctions_opt rest in
        let extra_heap =
          (match (extra_opt) with
            | None ->
                let _ = print_string "[normalize_frac] Warning: List of conjunctions can not be empty \n" in
                CF.HTrue
            | Some res_f -> res_f)
        in
        let h_vars = CF.h_fv head_node in
        let e_vars = CF.h_fv extra_heap in
        let p_vars = MCP.mfv lhs_guard in
        let vars = Gen.BList.difference_eq CP.eq_spec_var (e_vars@p_vars) h_vars in
        Gen.BList.remove_dups_eq CP.eq_spec_var vars
      in
      (* rename the bound vars *)
      let extra_vars = compute_extra_vars () in
      let extra_vars_new =  CP.fresh_spec_vars extra_vars in
      let tmp_rho = List.combine extra_vars extra_vars_new in
      let coer_lhs = CF.subst tmp_rho coer_lhs in
      let coer_rhs = CF.subst tmp_rho coer_rhs in
      (************************************************************************)
      (* also rename the free vars from the rhs that do not appear in the lhs *)
      let lhs_fv = (Solver.fv_rhs coer_lhs coer_rhs) in
      let fresh_lhs_fv = CP.fresh_spec_vars lhs_fv in
      let tmp_rho = List.combine lhs_fv fresh_lhs_fv in
      let coer_lhs = CF.subst tmp_rho coer_lhs in
      let coer_rhs = CF.subst tmp_rho coer_rhs in
      (************************************************************************)
      (* (\************************************************************************\) *)
      (* (\* rename the free vars in the lhs and rhs to avoid name collision *\) *)
      (* (\* between lemmas and entailment formulas*\) *)
      (* (\* let lhs_fv = (fv_rhs coer_lhs coer_rhs) in *\) *)
      (* let lhs_fv = (CF.fv coer_lhs) in *)
      (* let fresh_lhs_fv = CP.fresh_spec_vars lhs_fv in *)
      (* let tmp_rho = List.combine lhs_fv fresh_lhs_fv in *)
      (* let coer_lhs = CF.subst tmp_rho coer_lhs in *)
      (* let coer_rhs = CF.subst tmp_rho coer_rhs in *)
      (* (\************************************************************************\) *)
      (* let _ = print_string ("normalize_w_coers: before and after renamed" *)
      (*                       ^ "\n ### coer.coercion_head = " ^ (Cprinter.string_of_formula coer.coercion_head) *)
      (*                       ^ "\n ### coer.coercion_body = " ^ (Cprinter.string_of_formula coer.coercion_body) *)
      (*                       ^ "\n ### coer_lhs = " ^ (Cprinter.string_of_formula coer_lhs) *)
      (*                       ^ "\n ### coer_rhs = " ^ (Cprinter.string_of_formula coer_rhs) *)
      (*                       ^ "\n") in *)

      let lhs_heap, lhs_guard, lhs_flow, lhs_branches, _ = split_components coer_lhs in
      let lhs_guard = MCP.fold_mem_lst (CP.mkTrue no_pos) false false (* true true *) lhs_guard in  (* TODO : check with_dupl, with_inv *)
      let lhs_hs = CF.split_star_conjunctions lhs_heap in (*|lhs_hs|>1*)
      (* let lhs_hs = List.rev lhs_hs in *)
      let head_node, rest = pick_up_node lhs_hs Globals.self in
      (* let head_node = List.hd lhs_hs in *)
      (* let extra_opt = join_star_conjunctions_opt (List.tl lhs_hs) in *)
      let extra_opt = join_star_conjunctions_opt rest in
      let extra_heap =
        (match (extra_opt) with
          | None ->
              let _ = print_string "[normalize_frac] Warning: List of conjunctions can not be empty \n" in
              CF.HTrue
          | Some res_f -> res_f)
      in
      (* let _ = print_string ("normalize_w_coers: before and after renamed" *)
      (*                       ^ "\n ### lhs_heap = " ^ (Cprinter.string_of_h_formula lhs_heap) *)
      (*                       ^ "\n ### head_node = " ^ (Cprinter.string_of_h_formula head_node) *)
      (*                       ^ "\n ### anode = " ^ (Cprinter.string_of_h_formula anode) *)

      (*                       ^ "\n") in *)

      match anode, head_node with (*node -> current heap node | lhs_heap -> head of the coercion*)
        | ViewNode ({ h_formula_view_node = p1;
                      h_formula_view_name = c1;
                      h_formula_view_origins = origs;
                      (* h_formula_view_original = original; (*LDK: unused*) *)
                      h_formula_view_remaining_branches = br1;
                      h_formula_view_frac_perm = frac1; (*LDK*)
                      h_formula_view_arguments = ps1} (* as h1 *)),
      ViewNode ({ h_formula_view_node = p2;
                  h_formula_view_name = c2;
                  h_formula_view_remaining_branches = br2;
                  h_formula_view_frac_perm = frac2; (*LDK*)
                  h_formula_view_arguments = ps2} (* as h2 *))
	    | DataNode ({ h_formula_data_node = p1;
	                  h_formula_data_name = c1;
	                  h_formula_data_origins = origs;
	                  h_formula_data_remaining_branches = br1;
	                  h_formula_data_frac_perm = frac1; (*LDK*)
	                  h_formula_data_arguments = ps1} (* as h1 *)),
      DataNode ({ h_formula_data_node = p2;
	              h_formula_data_name = c2;
	              h_formula_data_remaining_branches = br2;
	              h_formula_data_frac_perm = frac2; (*LDK*)
	              h_formula_data_arguments = ps2} (* as h2 *)) when CF.is_eq_node_name(*is_eq_view_spec*) c1 c2 (*c1=c2 && (br_match br1 br2) *) ->

            let lhs_guard_new,coer_rhs_new1,extra_heap_new = match frac1,frac2 with
              | Some f1, Some f2 ->
                  let guard = CP.subst_avoid_capture (p2 :: (f2 :: ps2)) (p1 :: (f1 :: ps1)) lhs_guard in
                  let rhs = subst_avoid_capture (p2 :: (f2 :: ps2)) (p1 :: (f1 :: ps1)) coer_rhs in
                  let extra = CF.subst_avoid_capture_h (p2 :: (f2 :: ps2)) (p1 :: (f1 :: ps1)) extra_heap in
                  (guard,rhs,extra)
              | Some f1, None ->
                  let guard = CP.subst_avoid_capture (p2 :: (full_perm_var::ps2)) (p1 :: (f1::ps1)) lhs_guard in
                  (*We propagate fractional permission from view node to lemma node*)
                  let rhs = subst_avoid_capture (p2 :: (full_perm_var::ps2)) (p1 :: (f1::ps1)) coer_rhs in
                  let extra = CF.subst_avoid_capture_h (p2 :: (full_perm_var::ps2)) (p1 :: (f1::ps1)) extra_heap in
                  let extra, svl =  propagate_frac_h_formula extra f1 in
                  let rhs = propagate_frac_formula rhs f1 in
                  (guard,rhs,extra)
              | None, Some f2 ->
                  let guard = CP.subst_avoid_capture (p2 :: (f2::ps2)) (p1 :: (full_perm_var::ps1)) lhs_guard in
                  let rhs = subst_avoid_capture (p2 :: (f2::ps2)) (p1 :: (full_perm_var::ps1)) coer_rhs in
                  let extra = CF.subst_avoid_capture_h (p2 :: (f2::ps2)) (p1 :: (full_perm_var::ps1)) extra_heap in
                  (guard,rhs,extra)
              | None, None ->
                  let guard = CP.subst_avoid_capture (p2 :: ps2) (p1 :: ps1) lhs_guard in
                  let rhs = subst_avoid_capture (p2 :: ps2) (p1 :: ps1) coer_rhs in
                  let extra =  CF.subst_avoid_capture_h (p2 :: ps2) (p1 :: ps1) extra_heap in
                  (guard,rhs,extra)
            in



            (* let lhs_guard_new = match frac1,frac2 with *)
            (*   | Some f1, Some f2 -> *)
            (*       CP.subst_avoid_capture (p2 :: (f2 :: ps2)) (p1 :: (f1 :: ps1)) lhs_guard *)
            (*   | Some f1, None -> *)
            (*       CP.subst_avoid_capture (p2 :: (full_perm_var::ps2)) (p1 :: (f1::ps1)) lhs_guard *)
            (*   | None, Some f2 -> *)
            (*       CP.subst_avoid_capture (p2 :: (f2::ps2)) (p1 :: (full_perm_var::ps1)) lhs_guard *)
            (*   | None, None -> *)
            (*       CP.subst_avoid_capture (p2 :: ps2) (p1 :: ps1) lhs_guard *)
            (* in *)
		    (* let coer_rhs_new1 = match frac1,frac2 with *)
            (*   | Some f1, Some f2 -> *)
            (*       subst_avoid_capture (p2 :: (f2 :: ps2)) (p1 :: (f1 :: ps1)) coer_rhs *)
            (*   | Some f1, None -> *)
            (*       subst_avoid_capture (p2 :: (full_perm_var::ps2)) (p1 :: (f1::ps1)) coer_rhs *)
            (*   | None, Some f2 -> *)
            (*       subst_avoid_capture (p2 :: (f2::ps2)) (p1 :: (full_perm_var::ps1)) coer_rhs *)
            (*   | None, None -> *)
            (*       subst_avoid_capture (p2 :: ps2) (p1 :: ps1) coer_rhs *)

            (* in *)
		    let coer_rhs_new = add_origins coer_rhs_new1 ((* coer.coercion_name :: *)origs) in
            (* let extra_heap_new = match frac1,frac2 with *)
            (*   | Some f1, Some f2 -> *)
            (*       CF.subst_avoid_capture_h (p2 :: (f2 :: ps2)) (p1 :: (f1 :: ps1)) extra_heap *)
            (*   | Some f1, None -> *)
            (*       CF.subst_avoid_capture_h (p2 :: (full_perm_var::ps2)) (p1 :: (f1::ps1)) extra_heap *)
            (*   | None, Some f2 -> *)
            (*       CF.subst_avoid_capture_h (p2 :: (f2::ps2)) (p1 :: (full_perm_var::ps1)) extra_heap *)
            (*   | None, None -> *)
            (*       CF.subst_avoid_capture_h (p2 :: ps2) (p1 :: ps1) extra_heap *)
            (* in *)
            let new_es_heap = anode in (*consumed*)
            let old_trace = estate.es_trace in
            let new_estate = {estate with es_heap = new_es_heap; es_formula = f;es_trace=("(normalizing)"::old_trace); es_is_normalizing = true} in
            let new_ctx1 = Ctx new_estate in
            let new_ctx = SuccCtx[((* set_context_must_match *) new_ctx1)] in
            (*prove extra heap + guard*)
            let conseq_extra = mkBase extra_heap_new (MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) lhs_guard_new) CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in 
            (* let conseq_extra = mkBase extra_heap_new (MCP.OnePF (CP.mkTrue no_pos)) CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in  *)

	        Debug.devel_pprint ("normalize_w_coers:process_one: check extra heap") no_pos;
	        Debug.devel_pprint ("normalize_w_coers:process_one: new_ctx: "
		                        ^ (Cprinter.string_of_spec_var p2) ^ "\n"
		                        ^ (Cprinter.string_of_context new_ctx1)) no_pos;
	        Debug.devel_pprint ("normalize_w_coers:process_one: conseq_extra:\n"
		                        ^ (Cprinter.string_of_formula conseq_extra)) no_pos;

            let check_res, check_prf = Solver.heap_entail prog false new_ctx conseq_extra no_pos in

	        Debug.devel_pprint ("normalize_w_coers:process_one: after check extra heap: "
		                        ^ (Cprinter.string_of_spec_var p2) ^ "\n"
		                        ^ (Cprinter.string_of_list_context check_res)) no_pos;

          (*PROCCESS RESULT*)
            match check_res with 
              | FailCtx _ -> 
                (*false, return dummy h and p*)
                  (false, estate, h,p)
              | SuccCtx res -> 
                (*we expect only one result*)
                  let ctx = List.hd res in
                  match ctx with
                    | OCtx (c1, c2) ->
                        let _ = print_string ("[solver.ml] Warning: normalize_w_coers:process_one: expect only one context \n") in
                        (false,estate,h,p)
                    | Ctx es ->
                        let new_ante1 = normalize_combine coer_rhs_new es.es_formula no_pos in
                        let new_ante = add_mix_formula_to_formula p new_ante1 in
                        let new_ante = CF.remove_dupl_conj_eq_formula new_ante in
                        let h1,p1,_,_,_ = split_components new_ante in
                        let new_es = {new_estate with es_formula=new_ante; es_trace=old_trace} in
                        (true,new_es,h1,p1)
    in
    let process_one estate anode rest coer h p =
      let pr (c1,c2,c3,c4) = string_of_bool c1 ^ "||" ^ Cprinter.string_of_entail_state c2 in 
      Gen.Debug.no_5 "process_one" Cprinter.string_of_entail_state Cprinter.string_of_h_formula Cprinter.string_of_h_formula Cprinter.string_of_h_formula  Cprinter.string_of_mix_formula pr  
          (fun _ _ _ _ _ -> process_one_x estate anode rest coer h p) estate anode rest  h p 
    in
    (*process a list of pairs (anode * rest) *)
    let rec process_one_h h_lst =
      match h_lst with
        | [] -> 
            (*so far, could not find any entailment -> can not normalize*)
            h,p
        | (anode,rest)::xs ->
            (*for each pair (anode,rest), find a list of coercions*)
            let name = match anode with
              | ViewNode vn -> vn.h_formula_view_name
              | DataNode dn -> dn.h_formula_data_name
              | _ -> 
              let _ = print_string("[solver.ml] Warning: normalize_w_coers expecting DataNode or ViewNode \n") in
              ""
            in
            let c_lst = look_up_coercion_def_raw coers name in (*list of coercions*)
            let lst = List.map (fun c -> (c,anode,rest)) c_lst in
            (*process a triple (coer,anode,res)*)
            let rec process_one_coerc lst =
              match lst with
                | [] -> 
                    (*so far, there is no entailment -> process the rest of pairs of (anode,rest)*)
                    process_one_h xs 
                | ((coer,anode,res)::xs1) ->
                    (*for each triple, try to find a posible entailment*)
                    let res,res_es,res_h,res_p = process_one estate anode rest coer h p in
                    if (res) (*we could find a result*)
                    then
                      (*restart and normalize the new estate*)
                      helper res_es res_h res_p
                    else
                      (*otherwise, try the rest*)
                      process_one_coerc xs1
            in
            process_one_coerc lst
    in
    (*split into pairs of (single node * the rest)  *)
    let h_lst = Solver.split_linear_node_guided [] h in
    process_one_h h_lst
  in
  helper estate h p (*start*)

(*   let rec helper (estate:CF.entail_state) (h:h_formula) (p:MCP.mix_formula) : (h_formula*MCP.mix_formula) = *)
(*     let hs = CF.split_star_conjunctions h in *)
(*     let process_one anode coer h p = *)
(*       let coer_lhs = coer.coercion_head in *)
(*       let coer_rhs = coer.coercion_body in *)
(*       (\************************************************************************\) *)
(*       (\* rename the free vars in the lhs and rhs to avoid name collision *\) *)
(*       (\* between lemmas and entailment formulas*\) *)
(*       (\* let lhs_fv = (fv_rhs coer_lhs coer_rhs) in *\) *)
(*       let lhs_fv = (CF.fv coer_lhs) in *)

(*       let fresh_lhs_fv = CP.fresh_spec_vars lhs_fv in *)
(*       let tmp_rho = List.combine lhs_fv fresh_lhs_fv in *)
(*       let coer_lhs = CF.subst tmp_rho coer_lhs in *)
(*       let coer_rhs = CF.subst tmp_rho coer_rhs in *)
(*       (\************************************************************************\) *)
(*       let lhs_heap, lhs_guard, lhs_flow, lhs_branches, _ = split_components coer_lhs in *)
(*       let lhs_hs = CF.split_star_conjunctions lhs_heap in (\*|lhs_hs|>1*\) *)
(*       let head_node = List.hd lhs_hs in *)
(*       let extra_opt = join_star_conjunctions_opt (List.tl lhs_hs) in *)
(*       let extra_heap = *)
(*         (match (extra_opt) with *)
(*           | None -> *)
(*               let _ = print_string "[normalize_frac] Warning: List of conjunctions can not be empty \n" in *)
(*               CF.HTrue *)
(*           | Some res_f -> res_f) *)
(*       in *)
(*       match anode, head_node with (\*node -> current heap node | lhs_heap -> head of the coercion*\) *)
(*         | ViewNode ({ h_formula_view_node = p1; *)
(*                       h_formula_view_name = c1; *)
(*                       h_formula_view_origins = origs; *)
(*                   (\* h_formula_view_original = original; (\*LDK: unused*\) *\) *)
(*                       h_formula_view_remaining_branches = br1; *)
(*                       h_formula_view_frac_perm = frac1; (\*LDK*\) *)
(*                       h_formula_view_arguments = ps1} (\* as h1 *\)), *)
(*       ViewNode ({ h_formula_view_node = p2; *)
(*                   h_formula_view_name = c2; *)
(*                   h_formula_view_remaining_branches = br2; *)
(*                   h_formula_view_frac_perm = frac2; (\*LDK*\) *)
(*                   h_formula_view_arguments = ps2} (\* as h2 *\)) *)
(* 	    | DataNode ({ h_formula_data_node = p1; *)
(* 	                  h_formula_data_name = c1; *)
(* 	                  h_formula_data_origins = origs; *)
(* 	                  h_formula_data_remaining_branches = br1; *)
(* 	                  h_formula_data_frac_perm = frac1; (\*LDK*\) *)
(* 	                  h_formula_data_arguments = ps1} (\* as h1 *\)), *)
(*       DataNode ({ h_formula_data_node = p2; *)
(* 	              h_formula_data_name = c2; *)
(* 	              h_formula_data_remaining_branches = br2; *)
(* 	              h_formula_data_frac_perm = frac2; (\*LDK*\) *)
(* 	              h_formula_data_arguments = ps2} (\* as h2 *\)) when CF.is_eq_node_name(\*is_eq_view_spec*\) c1 c2 (\*c1=c2 && (br_match br1 br2) *\) -> *)
(*             let lhs_guard_new = match frac1,frac2 with *)
(*               | Some f1, Some f2 -> *)
(*                   CP.subst_avoid_capture (p2 :: (f2 :: ps2)) (p1 :: (f1 :: ps1)) lhs_guard *)
(*               | Some f1, None -> *)
(*                   CP.subst_avoid_capture (p2 :: (full_perm_var::ps2)) (p1 :: (f1::ps1)) lhs_guard *)
(*               | None, Some f2 -> *)
(*                   CP.subst_avoid_capture (p2 :: (f2::ps2)) (p1 :: (full_perm_var::ps1)) lhs_guard *)
(*               | None, None -> *)
(*                   CP.subst_avoid_capture (p2 :: ps2) (p1 :: ps1) lhs_guard *)
(*             in *)
(* 		    let coer_rhs_new1 = match frac1,frac2 with *)
(*               | Some f1, Some f2 -> *)
(*                   subst_avoid_capture (p2 :: (f2 :: ps2)) (p1 :: (f1 :: ps1)) coer_rhs *)
(*               | Some f1, None -> *)
(*                   subst_avoid_capture (p2 :: (full_perm_var::ps2)) (p1 :: (f1::ps1)) coer_rhs *)
(*               | None, Some f2 -> *)
(*                   subst_avoid_capture (p2 :: (f2::ps2)) (p1 :: (full_perm_var::ps1)) coer_rhs *)
(*               | None, None -> *)
(*                   subst_avoid_capture (p2 :: ps2) (p1 :: ps1) coer_rhs *)

(*             in *)
(* 		    let coer_rhs_new = add_origins coer_rhs_new1 ((\* coer.coercion_name :: *\)origs) in *)
(*             let extra_heap_new = match frac1,frac2 with *)
(*               | Some f1, Some f2 -> *)
(*                   CF.subst_avoid_capture_h (p2 :: (f2 :: ps2)) (p1 :: (f1 :: ps1)) extra_heap *)
(*               | Some f1, None -> *)
(*                   CF.subst_avoid_capture_h (p2 :: (full_perm_var::ps2)) (p1 :: (f1::ps1)) extra_heap *)
(*               | None, Some f2 -> *)
(*                   CF.subst_avoid_capture_h (p2 :: (f2::ps2)) (p1 :: (full_perm_var::ps1)) extra_heap *)
(*               | None, None -> *)
(*                   CF.subst_avoid_capture_h (p2 :: ps2) (p1 :: ps1) extra_heap *)
(*             in *)
(*             let new_es_heap = anode in (\*consumed*\) *)
(*             let new_estate = {estate with es_heap = new_es_heap; es_formula = f;es_trace=("(Complex)"::old_trace)} in *)


(*     in *)
(*     let rec process (hs:h_formula list) = *)
(*       match hs with *)
(*         | [] -> (h,p) *)
(*         | x::xs -> *)
(*             (\* let c = look_up_coercion_def_raw coers *\) *)
(*             let name = match x with *)
(*               | ViewNode vn -> vn.h_formula_view_name *)
(*               | DataNode dn -> dn.h_formula_data_name *)
(*               | _ = *)
(*               let _ = print_string("[solver.ml] Warning: normalize_w_coers expecting DataNode or ViewNode ") in *)
(*               "" *)
(*             in *)
(*             let c = look_up_coercion_def_raw coers name in *)

(*     in process hs *)
(* (\* *)
(* process_one x *)
(* if succeed -> helper *)
(* else *)
(* process xs *)
(* *\) *)
(*   in *)
(*   helper estate h p *)

let normalize_formula_w_coers_x prog estate (f:formula) (coers:coercion_decl list): formula =
  if (isAnyConstFalse f) then f
  else
    let coers = List.filter (fun c -> 
        match c.coercion_case with
          | Cast.Simple -> false
          | Cast.Complex -> false
          | Cast.Normalize -> true) coers
    in
    (* let _ = print_string ("normalize_formula_w_coers: "  *)
    (*                       ^ " ### coers = " ^ (Cprinter.string_of_coerc_list coers) *)
    (*                       ^ "\n\n") *)
    (* in *)
    let rec helper f =
      match f with
        | Base b ->
            let h = b.formula_base_heap in
            let p = b.formula_base_pure in
            (* let t = b.formula_base_type in *)
            (* let fl = b.formula_base_flow in *)
            (* let br = b.formula_base_branches in *)
            let h,p = normalize_w_coers prog estate coers h p (* t fl br *) in
            Base {b with formula_base_heap=h;formula_base_pure=p}
        | Exists e ->
            let h = e.formula_exists_heap in
            let p = e.formula_exists_pure in
            (* let t = e.formula_exists_type in *)
            (* let fl = e.formula_exists_flow in *)
            (* let br = e.formula_exists_branches in *)
            let h,p = normalize_w_coers prog estate coers h p (* t fl br *) in
            Exists {e with formula_exists_heap=h; formula_exists_pure=p }
        | Or o ->
	        let f1 = helper o.formula_or_f1 in
	        let f2 = helper o.formula_or_f2 in
            Or {o with formula_or_f1 = f1; formula_or_f2 = f2}
    in helper f

let normalize_formula_w_coers prog estate (f:formula) (coers:coercion_decl list): formula =
  Gen.Debug.no_1 "normalize_formula_w_coers" Cprinter.string_of_formula Cprinter.string_of_formula
      (fun _ -> normalize_formula_w_coers_x  prog estate f coers) f


