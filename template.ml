#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Cpure
open Tlutils

module MCP = Mcpure
module CF = Cformula
module C = Cast
(* module TU = Tlutils *)
(* module DD = Debug *)

(********************************)
(* COLLECT TEMPLATE ASSUMPTIONS *)
(********************************)
let collect_templ_assume_rhs (es: CF.entail_state) (ante: formula) (cons: formula) pos = 
  let cons_fv = fv cons in
  let ante = find_rel_constraints ante cons_fv in
  
  let es = { es with CF.es_infer_templ_assume = 
    es.CF.es_infer_templ_assume @ [(ante, cons)]; } in

  let inf_templs = es.CF.es_infer_vars_templ in
  let ante_no_templ, ante_unks = trans_formula_templ inf_templs ante in
  let cons_no_templ, cons_unks = trans_formula_templ inf_templs cons in
  let vars = diff ((fv ante) @ (fv cons)) (ante_unks @ cons_unks) in

  let ante_no_templ, subst = find_eq_subst_formula vars ante_no_templ in
  let cons_no_templ = apply_par_term subst cons_no_templ in
  
  let true_f = mkPure (mkLte (mkIConst (-1) pos) (mkIConst 0 pos) pos) in
  let ante_fl = true_f::(split_conjunctions ante_no_templ) in
  let ante_tl = List.map (term_list_of_formula vars) ante_fl in
  
  (* let () = print_endline ("collect_templ_assume_rhs: ante: " ^ (!print_formula ante)) in                *)
  (* let () = print_endline ("collect_templ_assume_rhs: ante_tl: " ^ (pr_list print_term_list ante_tl)) in *)

  let () = templ_assume_scc_stk # push 
    { ass_vars = vars;
      ass_unks = ante_unks @ cons_unks;
      ass_ante = ante;
      ass_cons = cons;
      ass_ante_tl = ante_tl;
      ass_cons_no_templ = cons_no_templ;
      ass_pos = pos; } in
  es

let collect_templ_assume_rhs (es: CF.entail_state) (ante: formula) (cons: formula) pos = 
  let pr1 = !CF.print_entail_state in
  let pr2 = !print_formula in
  Debug.no_3 "collect_templ_assume_rhs" pr1 pr2 pr2 pr1
    (fun _ _ _ -> collect_templ_assume_rhs es ante cons pos) es ante cons

let exp_of_templ_decl (tdef: C.templ_decl): exp =
  let pos = tdef.C.templ_pos in
  let func_typ = List.fold_right (fun v r_typ -> FuncT (type_of_spec_var v, r_typ))
    tdef.C.templ_params tdef.C.templ_ret_typ in 
  let tid = SpecVar (func_typ, tdef.C.templ_name, Unprimed) in
  let targs = List.map (fun v -> mkVar v pos) tdef.C.templ_params in
  Template {
    templ_id = tid; templ_args = targs; templ_unks = []; 
    templ_body = tdef.C.templ_body; templ_pos = pos; }

let replace_eq_conseq (cons: formula): formula =
  let f_f f = match f with
    | BForm (bf, lbl) -> (match bf with
      | Eq (e1, e2, pos), il -> 
        let f1 = BForm ((Gte (e1, e2, pos), il), lbl) in
        let f2 = BForm ((Lte (e1, e2, pos), il), lbl) in
        Some (mkAnd f1 f2 pos)
      | _ -> Some f)
    | _ -> None 
  in transform_formula (nonef, nonef, f_f, nonef, nonef) cons

let replace_eq_conseq (cons: formula): formula =
  let pr = !print_formula in
  Debug.no_1 "replace_eq_conseq" pr pr replace_eq_conseq cons

let simplify_templ_conseq (should_simpl_no_templ: bool) (cons: formula) =
  let cons = replace_eq_conseq cons in
  let cons_l = split_conjunctions cons in
  let cons_l =
    (* If there is no unknowns template in the LHS *)
    (* then we can remove non-template formulas in *)
    (* RHS as they have been already proved        *)
    if (should_simpl_no_templ) then List.filter has_template_formula cons_l 
    else cons_l
  in cons_l

let collect_templ_assume_conj_rhs (es: CF.entail_state) (ante: formula) (cons: formula) pos =
  let cons_l = simplify_templ_conseq (not (has_template_formula ante)) cons in
  let es = List.fold_left (fun es cons ->
    let es = collect_templ_assume_rhs es ante cons pos in
    es) es cons_l in
  es

let collect_templ_assume_conj_rhs (es: CF.entail_state) (ante: formula) (cons: formula) pos =  
  let pr1 = !CF.print_entail_state in
  let pr2 = !print_formula in
  Debug.no_3 "collect_templ_assume_conj_rhs" pr1 pr2 pr2 pr1
    (fun _ _ _ -> collect_templ_assume_conj_rhs es ante cons pos) es ante cons

let simplify_templ_ante (ante: formula) =
  let ante_l = split_disjunctions_deep ante in
  List.map (fun f -> snd (elim_exists_with_fresh_vars f)) ante_l

let simplify_templ_ante (ante: formula) =
  let pr = !print_formula in
  Debug.no_1 "simplify_templ_ante" pr (pr_list pr)
  simplify_templ_ante ante
  
let collect_templ_assume_disj_lhs (es: CF.entail_state) (ante: formula) (cons: formula) pos = 
  let ante_l = simplify_templ_ante ante in
  let es = List.fold_left (fun es ante ->
    let es = collect_templ_assume_conj_rhs es ante cons pos in
    es) es ante_l in
  es

let collect_templ_assume_disj_lhs (es: CF.entail_state) (ante: formula) (cons: formula) pos =  
  let pr1 = !CF.print_entail_state in
  let pr2 = !print_formula in
  Debug.no_3 "collect_templ_assume_disj_lhs" pr1 pr2 pr2 pr1
    (fun _ _ _ -> collect_templ_assume_disj_lhs es ante cons pos) es ante cons

let collect_templ_assume_init (es: CF.entail_state) (ante: formula) (cons: formula) pos =
  let inf_templs = es.CF.es_infer_vars_templ in
  let _ =
    (* To generate sleek file of original template inference *)
    if !gen_templ_slk then 
      templ_sleek_scc_stk # push (inf_templs, ante, cons)
    else () 
  in
  let es = collect_templ_assume_disj_lhs es ante cons pos in
  Some es

let collect_templ_assume_init (es: CF.entail_state) (ante: MCP.mix_formula) (cons: formula) pos =
  let pr1 = !MCP.print_mix_formula in
  let pr2 = !print_formula in
  let pr3 = string_of_loc in
  Debug.no_3 "collect_templ_assume_init" pr1 pr2 pr3 (pr_opt !CF.print_entail_state) 
    (fun _ _ _ -> collect_templ_assume_init es (MCP.pure_of_mix ante) cons pos) ante cons pos 
    
 (*********************************************)
(* GENERATE CONSTRAINTS OF TEMPLATE UNKNOWNS *)
(*********************************************)
let unk_lambda_sv num =
  let name = List.fold_left (fun a i -> a ^ "_" ^ (string_of_int i)) "lambda" num in
  SpecVar (Int, name, Unprimed)

let collect_unk_constrs (ante: term list) (cons: term list) pos: formula list =
  let rem_cons, constrs = List.fold_left (fun (cons, fl) at -> 
    let cons_same_deg, cons_notsame_deg = 
      List.partition (fun t -> is_same_degree t at) cons in
    let a_exp = at.term_coe in
    let c_exp = match cons_same_deg with
    | [] -> mkIConst 0 pos
    | c::cs -> List.fold_left (fun a ct -> mkAdd a ct.term_coe pos) c.term_coe cs
    in
    (* Because of the addition constraint -1 <= 0
     * we do not need Gte for the base coefficient *)
    let constr = mkPure (mkEq a_exp c_exp pos) in 
    (cons_notsame_deg, fl @ [constr])) (cons, []) ante in
  let rem_constrs = List.map (fun ct -> 
    mkPure (mkEq (mkIConst 0 pos) ct.term_coe pos)) rem_cons in
  constrs @ rem_constrs

let gen_templ_constr_farkas (ante_tl: term list list) (cons_t: term list) pos: formula list =
  let constrs = 
    let ante_w_unks, unks, _ = List.fold_left (fun (a, unks, i) tl ->
      let unk_lambda = mkVar (unk_lambda_sv [fresh_int (); i]) pos in
      let tl = List.map (fun t -> { t with term_coe = mkMult t.term_coe unk_lambda pos; }) tl in
      (a @ [tl], unks @ [unk_lambda], i+1)) ([], [], 0) ante_tl in
    let ante_sum_t = partition_term_list (List.concat ante_w_unks) pos in
    (List.map (fun unk -> mkPure (mkGte unk (mkIConst 0 pos) pos)) unks) @
    (collect_unk_constrs ante_sum_t cons_t pos) in
  constrs

let gen_templ_constr_farkas (ante_tl: term list list) (cons_t: term list) pos: formula list =
  let pr1 = print_term_list in
  let pr2 = pr_list pr1 in
  let pr3 = pr_list !print_formula in
  Debug.no_2 "gen_templ_constr_farkas" pr2 pr1 pr3 
  (fun _ _ -> gen_templ_constr_farkas ante_tl cons_t pos)
  ante_tl cons_t

let gen_templ_constr (ta: templ_assume) =
  let ante_tl = ta.ass_ante_tl in
  let cons_t = term_list_of_formula ta.ass_vars 
    (normalize_formula ta.ass_cons_no_templ) in
  let pos = ta.ass_pos in
  gen_templ_constr_farkas ante_tl cons_t pos

(******************************)
(* SOLVE TEMPLATE ASSUMPTIONS *)
(******************************)
let gen_slk_infer_templ_scc () =
  let inp = List.rev (templ_sleek_scc_stk # get_stk) in
  let () = templ_sleek_stk # reset in

  let out = List.map (fun (templ_vars, ante, cons) ->
    "infer " ^ (!print_svl templ_vars) ^ " " ^ 
    (!print_formula ante) ^ " |- " ^ (!print_formula cons) ^ ".") inp in
  let str = (String.concat "\n\n" out) ^ "\n\ntemplate_solve.\n" in
  templ_sleek_stk # push str

let gen_slk_file prog =
  let file_name_ss = List.hd !Globals.source_files in
  let out_chn =
    let reg = Str.regexp ".ss" in
    let file_name_slk = "logs/templ_" ^ (Str.global_replace reg ".slk" file_name_ss) in
    let () = print_endline_quiet ("\n Generating sleek file: " ^ file_name_slk) in
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    open_out (file_name_slk)
  in

  let templ_decl_str = (String.concat ".\n" 
    (List.map Cprinter.string_of_templ_decl prog.C.prog_templ_decls)) ^ ".\n"
  in

  let templ_infer_str = String.concat "\n\n" (List.rev (templ_sleek_stk # get_stk)) in
  
  let slk_output = templ_decl_str ^ "\n\n" ^ templ_infer_str in
  let () = output_string out_chn slk_output in
  let () = close_out out_chn in
  ()

let solve_templ_assume _ =
  let templ_assumes = List.rev (templ_assume_scc_stk # get_stk) in
  let () = templ_assume_scc_stk # reset in
  if templ_assumes = [] then [], [], Unknown
  else
    let constrs, templ_unks = List.fold_left (fun (ac, au) ta ->
      let constr = gen_templ_constr ta in
      (ac @ constr), (au @ ta.ass_unks)) ([], []) templ_assumes in
    let templ_unks = Gen.BList.remove_dups_eq eq_spec_var templ_unks in
  
    let () = 
      if !gen_templ_slk then gen_slk_infer_templ_scc ()
      else ()
    in
      
    (* Printing template assumptions *)
    let () = 
      if !print_relassume then
        if templ_assumes = [] then ()
        else begin
          (print_endline_quiet "**** TEMPLATE ASSUMPTION(S) ****";
          print_endline_quiet (pr_list (fun ta -> 
            (Cprinter.string_of_templ_assume (ta.ass_ante, ta.ass_cons)) ^ "\n") 
          templ_assumes))
        end
      else ()
    in
  
    let unks = remove_dups (List.concat (List.map fv constrs)) in
    let res = get_model (List.for_all is_linear_formula constrs) templ_unks unks constrs in
    templ_assumes, templ_unks, res

let silent_pr silent str =
  if silent then ()
  else print_endline_quiet str  
      
let collect_and_solve_templ_assumes_common silent prog (inf_templs: ident list) =
  let templ_assumes, templ_unks, res = solve_templ_assume () in
  match res with
  | Unsat -> 
    let () = silent_pr silent ("TEMPLATE INFERENCE: Unsat.") in 
    res, templ_assumes, templ_unks
  | Sat model ->
    let () = 
      if not silent then
        (* let () = print_endline ("MODEL: " ^ (pr_list (pr_pair pr_id string_of_int) model)) in *)
        (* let () = print_endline ("TEMPL UNKS: " ^ (pr_list pr_spec_var templ_unks)) in         *)
        let templ_decls = prog.C.prog_templ_decls in
        let res_templ_decls = subst_model_to_templ_decls inf_templs templ_unks templ_decls model in
        silent_pr silent "**** TEMPLATE INFERENCE RESULT ****";
        silent_pr silent (pr_list (fun tdef -> 
          (Cprinter.string_of_templ_decl tdef) ^ "\n") res_templ_decls)
      else () 
    in res, templ_assumes, templ_unks
  | _ -> 
    (* print_endline ("TEMPLATE INFERENCE: No result.") *) 
    res, templ_assumes, templ_unks

let collect_and_solve_templ_assumes prog (inf_templs: ident list) =
  let res, templ_assumes, _ = collect_and_solve_templ_assumes_common false prog inf_templs in
  match res with
  | Unsat -> 
    if !Globals.templ_piecewise then
      let () = print_endline_quiet ("\nContinue with piecewise function inference ...") in
      let ptempl_assumes, inf_ptempls, ptempl_defs = 
        Piecewise.infer_piecewise_main prog templ_assumes in
      let estate = CF.empty_es (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
      let estate = { estate with CF.es_infer_vars_templ = inf_ptempls; } in
      let es = List.fold_left (fun es (ante, cons) -> 
        let nes = collect_templ_assume_init es (MCP.mix_of_pure ante) cons no_pos in
        match nes with | Some es -> es | None -> es) estate ptempl_assumes in
      let prog = { prog with C.prog_templ_decls = prog.C.prog_templ_decls @ ptempl_defs } in
      let todo_unk = collect_and_solve_templ_assumes_common false prog (List.map name_of_spec_var inf_ptempls) in ()
    else ()
  | _ -> ()



