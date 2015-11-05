#include "xdebug.cppo"
open VarGen
open Template
open Cpure
open Globals
open Gen
open Tlutils

module TP = Tpdispatcher

(***************************)
(* LEXICOGRAPHIC INFERENCE *)
(***************************)
exception Lex_Infer_Failure of string 

(* e1 > e2 --> e1 >= 0 *)
let trans_dec_to_bnd_constr (f: formula) =
  let f_b b = 
    let (p, _) = b in match p with
    | Gt (e1, e2, pos) -> Some (Gte (e1, mkIConst 0 (pos_of_exp e2), pos), None)
    | _ -> Some (mkTrue_b (pos_of_b_formula b)) 
  in transform_formula (nonef, nonef, nonef, f_b, nonef) f

(* e1 > e2 --> e1 >= e2 *)
let trans_dec_to_unaff_constr (f: formula) =
  let f_b b = 
    let (p, _) = b in match p with
    | Gt (e1, e2, pos) -> Some (Gte (e1, e2, pos), None)
    | _ -> Some (mkTrue_b (pos_of_b_formula b)) 
  in transform_formula (nonef, nonef, nonef, f_b, nonef) f

let rec powerset l =
  match l with 
  | [] -> [[]]
  | x::xs ->
    let powerset_xs = powerset xs in
    powerset_xs @ (List.map (fun e -> x::e) powerset_xs) 

let powerset l = 
  List.stable_sort (fun l1 l2 -> 
      (List.length l2) - (List.length l1)) (powerset l)

let find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs unaff_constrs =
  let unaff_il, unaff_ctrs = List.split unaff_constrs in

  let constrs = List.fold_left (fun ac ta ->
      let cl = gen_templ_constr ta in ac @ cl) [] (rank_constrs @ unaff_ctrs) in
  if constrs = [] then None
  else
    let unks = Gen.BList.remove_dups_eq eq_spec_var 
        (List.concat (List.map fv constrs)) in
    let res = get_model (List.for_all is_linear_formula constrs) templ_unks unks constrs in
    match res with
    | Sat model -> 
      let res_templ_decls = subst_model_to_templ_decls inf_templs templ_unks prog.C.prog_templ_decls model in
      Some (List.concat (List.map (fun tdef -> 
          fold_opt (fun e -> [e]) tdef.C.templ_body) res_templ_decls), 
            (i, unaff_il))
    | _ -> None

let find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs unaff_constrs =
  let pr_ctr = fun ta -> pr_pair string_of_loc (pr_pair !print_formula !print_formula)
      (ta.ass_pos, (ta.ass_ante, ta.ass_cons_no_templ)) in
  let pr1 = pr_list pr_ctr in
  let pr2 = pr_list (fun (i, ta) -> (string_of_int i) ^ "@" ^ (string_of_loc ta.ass_pos)) in
  let pr3 = pr_pair string_of_int (pr_list string_of_int) in
  let pr4 = pr_opt (pr_pair (pr_list !print_exp) pr3) in
  Debug.no_2 "find_potential_lex_single_rank" pr1 pr2 pr4
    (fun _ _ -> find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs unaff_constrs)
    rank_constrs unaff_constrs

let find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs unaff_constrs =
  let rec search_rank ls = 
    match ls with
    | [] -> None
    | u::us ->
      let r = find_potential_lex_single_rank prog inf_templs templ_unks i rank_constrs u in 
      match r with
      | Some _ -> r
      | None -> search_rank us
  in search_rank (powerset unaff_constrs) 

(* [1; 2; 3] --> [[1; 2; 3]; [2; 3; 1]; [3; 1; 2]] *)
let rec rotate_head_list ls =
  match ls with
  | [] -> []
  | x::xs -> ls::(List.map (fun xs -> xs @ [x]) (rotate_head_list xs))

let find_lex_rank prog inf_templs templ_unks dec_assumes =
  match dec_assumes with
  | [] 
  | _::[] -> raise (Lex_Infer_Failure 
                      "Nothing to do with Lexicographic Inference (less than 2 call contexts).")
  | c::cs -> 
    let i, c_templ_assume = c in
    let bnd = trans_dec_to_bnd_constr c_templ_assume.ass_cons_no_templ in
    let rank = find_potential_lex_single_rank prog inf_templs templ_unks i 
        [c_templ_assume; { c_templ_assume with ass_cons_no_templ = bnd; }]
        (List.map (fun (i, cs_templ_assume) -> 
             (i, { cs_templ_assume with 
                   ass_cons_no_templ = trans_dec_to_unaff_constr cs_templ_assume.ass_cons_no_templ; }
             )) cs)
    in match rank with
    | None -> raise (Lex_Infer_Failure "Cannot find a potential ranking function")
    | Some r -> r

let rec sort_rank_list num rank_l =
  if num < 0 then []
  else
    let hd, tl = List.partition (fun (r, (_, unaff_l)) -> 
        (List.length unaff_l) == num) rank_l in
    match hd with
    | [] -> raise (Lex_Infer_Failure 
                     "Cannot find suitable lexicographic ranking function")
    | (r, (i, _))::xs -> (* TODO: Backtracking here *) 
      let r_tl = List.map (fun (r, (j, unaff_l)) -> (r, (j, List.filter (fun k -> k != i) unaff_l))) (xs @ tl) in
      r::(sort_rank_list (num-1) r_tl)

(*************************************)
(* CONDITIONAL TERMINATION INFERENCE *)
(*************************************)
type reach_status = 
  | Reach_Term
  | Reach_Loop
  | Reach_Both

type rec_trans = {
  trans_ctx: formula;
  trans_src_id: spec_var;
  trans_src_fv: spec_var list;
  trans_dst_id: spec_var;
  trans_dst_args: exp list;
  trans_rec_cond: formula; (* Simplification of trans_ctx *)
}

exception Cond_Infer_Failure of string 

let print_reach_status = function
  | Reach_Term -> "Term"
  | Reach_Loop -> "Rec"
  | Reach_Both -> "Both"

let print_rec_trans t = 
  let pr1 = !print_formula in
  let pr2 = !print_sv in
  let pr3 = !print_svl in
  let pr4 = pr_list !print_exp in
  (pr1 t.trans_ctx) ^ ": " ^ 
  (pr2 t.trans_src_id) ^ (pr3 t.trans_src_fv) ^ 
  " -> " ^ (pr2 t.trans_dst_id) ^ (pr4 t.trans_dst_args) 

let print_rec_cond (id, (svl, cond)) =
  let pr1 = !print_sv in
  let pr2 = !print_svl in
  let pr3 = !print_formula in
  (pr1 id) ^ (pr2 svl) ^ "(" ^ (pr3 cond) ^ ")"

let get_loop_trans_templ (f: formula) =
  let f_b b = 
    let (p, _) = b in match p with
    | Gt (Template t1, Template t2, _) -> Some [(t1, t2)]
    | _ -> Some []
  in fold_formula f (nonef, f_b, nonef) List.concat

let get_loop_trans_templ_assume (ta: templ_assume) =
  let dec_cons = ta.ass_cons in
  let src_templ, dst_templ = match (get_loop_trans_templ dec_cons) with
    | (s, d)::[] -> (s, d)
    | _ -> raise (Cond_Infer_Failure "There are more than one decreasing constraints") 
  in
  let fv_call_ctx = List.concat (List.map afv src_templ.templ_args) in 
  let call_ctx = ta.ass_ante in
  let rec_cond = mkExists_with_simpl idf (* TP.simplify *) 
      (Gen.BList.difference_eq eq_spec_var (fv call_ctx) fv_call_ctx) 
      call_ctx None (pos_of_formula call_ctx) in
  { trans_ctx = call_ctx;
    trans_src_id = src_templ.templ_id;
    trans_src_fv = fv_call_ctx;
    trans_dst_id = dst_templ.templ_id;
    trans_dst_args = dst_templ.templ_args;
    trans_rec_cond = rec_cond; }

let merge_loop_cond loop_cond_list = 
  match loop_cond_list with
  | [] -> None
  | (id, (sv, rc))::xs ->
    let pos = pos_of_formula rc in
    let rc_xs = List.map (fun (id, (svx, rcx)) -> 
        subst_avoid_capture svx sv rcx) xs in
    Some (id, (sv, TP.hull (List.fold_left (fun a c -> mkOr a c None pos) rc rc_xs)))

let infer_loop_status ctx loop_cond = 
  let imply ante cons = 
    let (r, _, _) = x_add TP.imply_one 0 ante cons "0" true None in r 
  in
  let r1 = imply ctx loop_cond in
  if r1 then Reach_Loop
  else 
    let r2 = imply ctx (mkNot loop_cond None (pos_of_formula loop_cond)) in
    if r2 then Reach_Term else Reach_Both

let infer_loop_status ctx loop_cond =
  let pr = !print_formula in
  Debug.no_2 "infer_loop_status" pr pr print_reach_status
    infer_loop_status ctx loop_cond

let infer_loop_trans_status loop_cond_list trans =
  let ctx = trans.trans_ctx in
  let dst_id = trans.trans_dst_id in
  let dst_args = trans.trans_dst_args in
  let dst_sv, dst_loop_cond = List.assoc dst_id loop_cond_list in
  let subst_loop_cond = apply_par_term (List.combine dst_sv dst_args) dst_loop_cond in 
  let status = infer_loop_status ctx subst_loop_cond in
  status

let strengthen_trans_with_templ trans loop_cond_list =
  let src_id = trans.trans_src_id in
  let src_fv = trans.trans_src_fv in
  let ctx = trans.trans_ctx in
  let (cond_fv, cond_f) = List.assoc src_id loop_cond_list in
  let pos = pos_of_formula ctx in

  let templ_id = fresh_spec_var src_id in
  let templ_decl = mkTemplate (name_of_spec_var templ_id)
      (List.map (fun sv -> mkVar sv pos) src_fv) pos in
  let templ_exp = Template templ_decl in
  let templ_constr = mkPure (mkLte templ_exp (mkIConst 0 pos) pos) in
  let s_ctx = mkAnd ctx templ_constr pos in
  let s_cond_f = mkAnd cond_f 
      (subst_avoid_capture src_fv cond_fv templ_constr) (pos_of_formula cond_f) in
  { trans with trans_ctx = s_ctx; }, 
  (src_id, (cond_fv, s_cond_f))::(List.remove_assoc src_id loop_cond_list),
  templ_id

(* (1) Partition loop_trans_list into Reach_Loop, Reach_Term and Reach_Both 
 * (2) Infer loop condition LC from Reach_Both group 
 *     (2a) Success -> add LC to Reach_Loop and !LC to Reach_Both 
 *     (2b) Failed -> add LC and !LC to Reach_Both
 * (3) Do ranking function synthesis on Reach_Both, return to (2) *)

let rec infer_pre_cond_iter loop_trans_list loop_cond_list =
  (* (1) Partition loop_trans_list into Reach_Loop, Reach_Term and Reach_Both *)
  let reach_status_trans = List.map (fun t -> 
      infer_loop_trans_status loop_cond_list t, t) loop_trans_list in
  let reach_both_trans, reach_other_trans = List.partition (fun (st, _) -> 
      match st with Reach_Both -> true | _ -> false) reach_status_trans in

  let () = 
    x_tinfo_pp ">>>>>>> infer_pre_cond_iter <<<<<<<" no_pos;
    List.iter (fun (r, t) -> x_tinfo_hp (add_str "loop trans: "
                                           (fun (r, t) -> (print_rec_trans t) ^ "(" ^ (print_reach_status r) ^ ")")) (r, t) no_pos)
      reach_status_trans;
    List.iter (fun c -> x_tinfo_hp (add_str "loop cond: " 
                                      (fun c -> print_rec_cond c)) c no_pos) loop_cond_list
  in

  (* (2) Infer loop condition from Reach_Both group 
   * by strengthening the context of loop transitions 
   * and loop conditions with unknown templates *)
  if reach_both_trans = [] then
    List.iter (fun c -> x_tinfo_hp (add_str "Non-Termination Condition: " 
                                      (fun c -> print_rec_cond c)) c no_pos) loop_cond_list
  else
    let templ_reach_both_trans, templ_loop_cond, templ_id_list = List.fold_left (
        fun (trans_list, loop_cond_list, templ_id_list) (_, trans) -> 
          let templ_trans, n_loop_cond_list, templ_id = strengthen_trans_with_templ trans loop_cond_list in
          trans_list @ [templ_trans], n_loop_cond_list, templ_id_list @ [templ_id]) 
        ([], loop_cond_list, []) reach_both_trans in

    let () = 
      List.iter (fun t -> x_tinfo_hp (add_str "templ loop trans: " 
                                        print_rec_trans) t no_pos) templ_reach_both_trans;
      List.iter (fun c -> x_tinfo_hp (add_str "templ loop cond: " 
                                        (fun c -> print_rec_cond c)) c no_pos) templ_loop_cond
    in

    let reach_both_src_ids = List.map (fun t -> t.trans_src_id) templ_reach_both_trans in
    (* Search for related transitions of the strengthened dst loop conds *)
    let rel_trans = List.filter (fun t -> mem t.trans_dst_id reach_both_src_ids) 
        (List.map snd reach_other_trans) in

    let es = CF.empty_es (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
    let es = { es with CF.es_infer_vars_templ = templ_id_list; } in 
    let es = List.fold_left (fun es trans ->
        let rec_cond_fv, rec_cond = List.assoc trans.trans_dst_id templ_loop_cond in
        let rec_cond = apply_par_term (List.combine rec_cond_fv trans.trans_dst_args) rec_cond in

        let () = 
          x_tinfo_hp (add_str "templ entail: " (fun (ctx, rc) -> 
              (!print_formula ctx) ^ " --> " ^ (!print_formula rc))) 
            (trans.trans_ctx, rec_cond) no_pos
        in

        let es = collect_templ_assume_conj_rhs es trans.trans_ctx rec_cond no_pos in
        es) es (templ_reach_both_trans @ rel_trans)
    in

    (* Solve the template constraints *)
    let _, templ_unks, res = solve_templ_assume () in
    let () = 
      x_tinfo_hp (add_str "templ res: " print_solver_res) res no_pos
    in

    match res with
    | Sat m ->
      let model = List.map (fun v -> 
          let vi = List.assoc (name_of_spec_var v) m in
          (v, vi)) templ_unks in
      let sst_loop_cond = List.map (fun (id, (sv, c)) ->
          (id, (sv, subst_model_to_formula model c))) templ_loop_cond in
      let sst_loop_trans = (List.map snd reach_other_trans) @
                           (List.map (fun t -> 
                                { t with trans_ctx = subst_model_to_formula model t.trans_ctx}) 
                               templ_reach_both_trans) in 
      let _ =
        List.iter (fun t -> x_tinfo_hp (add_str "sst loop trans: " 
                                          print_rec_trans) t no_pos) sst_loop_trans;
        List.iter (fun c -> x_tinfo_hp (add_str "sst loop cond: " 
                                          (fun c -> print_rec_cond c)) c no_pos) sst_loop_cond
      in infer_pre_cond_iter sst_loop_trans sst_loop_cond
    | _ -> ()

let infer_pre_cond_iter loop_trans_list loop_cond_list =
  let pr1 = pr_list print_rec_trans in
  let pr2 = pr_list print_rec_cond in
  let pr3 _ = "" in
  Debug.no_2 "infer_pre_cond_iter" pr1 pr2 pr3
    infer_pre_cond_iter loop_trans_list loop_cond_list

(* This method is invoked when the ranking function synthesis fails *)
let infer_loop_template_init prog (templ_assumes: templ_assume list) = 
  let loop_trans_list = List.map get_loop_trans_templ_assume templ_assumes in
  let loop_cond_list = List.map (fun t -> 
      (t.trans_src_id, (t.trans_src_fv, t.trans_rec_cond))) loop_trans_list in  
  let grouped_loop_cond = partition_by_assoc eq_spec_var loop_cond_list in
  (* merged_loop_cond = disj of loop_cond_list *)
  let merged_loop_cond = List.concat (List.map (fun lc -> fold_opt (fun rc -> [rc]) 
                                                   (merge_loop_cond lc)) grouped_loop_cond) in
  infer_pre_cond_iter loop_trans_list merged_loop_cond

(******************)
(* MAIN FUNCTIONS *)
(******************)  

(* We reuse the term-form of the antecedents 
 * from prior normal termination inference *)
let infer_lex_template_init prog (inf_templs: ident list) 
    templ_unks (templ_assumes: templ_assume list) =
  let dec_templ_assumes = List.filter (fun ta -> is_Gt_formula ta.ass_cons) templ_assumes in
  let num_call_ctx = List.length dec_templ_assumes in
  let () = print_endline_quiet "**** LEXICOGRAPHIC RANK INFERENCE RESULT ****" in

  if num_call_ctx == 1 then begin
    print_endline_quiet ("Nothing to do with Lexicographic Inference (only one call context).");
    print_endline_quiet ("Trying to infer conditional termination and/or non-termination ...");
    infer_loop_template_init prog dec_templ_assumes
  end
  else try
      let num_dec_templ_assumes, _ = List.fold_left (fun (a, i) dta -> 
          a @ [(i, dta)], i+1) ([], 1) dec_templ_assumes in
      let dec_templ_assumes_l = rotate_head_list num_dec_templ_assumes in
      let rank_l = List.map (find_lex_rank prog inf_templs templ_unks) dec_templ_assumes_l in
      let res = sort_rank_list (num_call_ctx-1) rank_l in
      print_endline_quiet (pr_list (pr_list !print_exp) res)
    with Lex_Infer_Failure reason -> 
      print_endline_quiet reason; ()
(* print_endline ("Trying to infer conditional termination and/or non-termination ..."); *)
(* infer_loop_template_init prog dec_templ_assumes *)

let infer_lex_template_res prog (inf_templs: ident list) 
    templ_unks (templ_assumes: templ_assume list) =
  let dec_templ_assumes = List.filter (fun ta -> is_Gt_formula ta.ass_cons) templ_assumes in
  let num_call_ctx = List.length dec_templ_assumes in
  let () = x_binfo_pp ("#ctx of infer-lex: " ^ (string_of_int num_call_ctx)) no_pos in
  if num_call_ctx <= 1 || num_call_ctx > 10 then []
  else
    try
      let num_dec_templ_assumes, _ = List.fold_left (fun (a, i) dta -> 
          a @ [(i, dta)], i+1) ([], 1) dec_templ_assumes in
      let dec_templ_assumes_l = rotate_head_list num_dec_templ_assumes in
      let rank_l = List.map (find_lex_rank prog inf_templs templ_unks) dec_templ_assumes_l in
      let res = sort_rank_list (num_call_ctx-1) rank_l in
      List.concat res
    with Lex_Infer_Failure _ -> []

let infer_lex_template_res prog (inf_templs: ident list) 
    templ_unks (templ_assumes: templ_assume list) =
  let pr1 = string_of_bool in
  let pr2 = pr_list pr_templ_assume in
  let pr3 = pr_list !print_exp in
  Debug.no_2 "infer_lex_template_res" pr1 pr2 pr3 
    (fun _ _ -> infer_lex_template_res prog inf_templs templ_unks templ_assumes)
    (!Tlutils.oc_solver) templ_assumes

let infer_rank_template_init prog (inf_templs: ident list) =
  let res, templ_assumes, templ_unks = collect_and_solve_templ_assumes_common false prog inf_templs in
  match res with
  | Unsat -> 
    if !Globals.templ_piecewise then
      let () = print_endline_quiet ("Continue with piecewise function inference ...") in
      let ptempl_assumes, inf_ptempls, ptempl_defs = 
        Piecewise.infer_piecewise_main prog templ_assumes in
      let estate = CF.empty_es (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
      let estate = { estate with CF.es_infer_vars_templ = inf_ptempls; } in
      let es = List.fold_left (fun es (ante, cons) -> 
          let nes = collect_templ_assume_init es (MCP.mix_of_pure ante) cons no_pos in
          match nes with | Some es -> es | None -> es) estate ptempl_assumes in
      (* let prog = { prog with C.prog_templ_decls = prog.C.prog_templ_decls @ ptempl_defs } in *)
      let () = prog.C.prog_templ_decls <- prog.C.prog_templ_decls @ ptempl_defs in
      let todo_unk = collect_and_solve_templ_assumes_common false prog (List.map name_of_spec_var inf_ptempls) in ()
    else 
      let () = print_endline_quiet ("Trying to infer lexicographic termination arguments ...") in
      infer_lex_template_init prog inf_templs templ_unks templ_assumes
  | _ -> ()


