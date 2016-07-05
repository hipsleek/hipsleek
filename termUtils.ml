#include "xdebug.cppo"
open VarGen
module MCP = Mcpure

open Gen.Basic
open Globals
open Others
open Cprinter
open Cpure
open Cformula

(* To find a LexVar formula *)
exception LexVar_Not_found;;
exception Invalid_Phase_Num;;

let find_lexvar_b_formula (bf: b_formula): lex_info =
  let (pf, _) = bf in
  match pf with
  | LexVar t_info -> t_info
  | _ -> raise LexVar_Not_found

let rec find_lexvar_formula (f: CP.formula): lex_info =
  match f with
  | BForm (bf, _) -> find_lexvar_b_formula bf
  | And (f1, f2, _) ->
    (try find_lexvar_formula f1
     with _ -> find_lexvar_formula f2)
  | AndList l -> 
    let rec hlp l = match l with
      | [] -> raise LexVar_Not_found
      | (_,h)::t -> (try find_lexvar_formula h
                     with _ -> hlp t) in
    hlp l
  | _ -> raise LexVar_Not_found

(* Strip LexVar from formula *)
let strip_lexvar_pure_only f =
  let mf_ls = split_conjunctions f in
  let (lexvar, other_p) = List.partition (is_lexvar) mf_ls in
  (lexvar, join_conjunctions other_p)

let def_lbl l =
  LO.is_common l
(*     if l==[] then true *)
(* else List.exists (fun s -> s="") l *)

let def_lbl l =
  Debug.no_1 "def_lbl" (LO.string_of) string_of_bool def_lbl l

let strip_lexvar_list ls =
  let rec aux xs =
    match xs with
    | [] -> ([],[])
    | ((l,f) as ff) ::xs ->
      let (l0,r0) = aux xs in
      let (l2,r2) = 
        if def_lbl l then
          let (l3,f3) = strip_lexvar_pure_only f in
          (l3,(l,f3))
        else ([],ff)
      in
      (l2@l0,r2::r0)
  in aux ls

let strip_lexvar_from_andlist ls =
  List.fold_left (fun (l,cj) f ->
      match f with
      | AndList ls -> 
        let (l0,nls) = strip_lexvar_list ls in
        (l0@l,(AndList nls)::cj)
      | _ -> if is_lexvar f then (f::l,cj)
        else (l,f::cj)
    ) ([],[]) ls

let strip_lexvar_from_pure f =
  let mf_ls = split_conjunctions f in
  let (lexvar,fs) = strip_lexvar_from_andlist mf_ls in
  (* let (lexvar, other_p) = List.partition (is_lexvar) mf_ls in *)
  (lexvar, join_conjunctions fs)

let strip_lexvar_memo_grp mg =
  let b_lexvar, memo_grp_cons = List.partition (fun mc -> 
      is_lexvar_b_formula mc.Mcpure_D.memo_formula) mg.Mcpure_D.memo_group_cons in
  let lexvar, memo_grp_slice = List.split (List.map 
                                             (fun f -> strip_lexvar_from_pure f) mg.Mcpure_D.memo_group_slice) in
  let lexvar = 
    (List.map (fun mc -> BForm (mc.Mcpure_D.memo_formula, None)) b_lexvar) @ 
    (List.concat lexvar) in 
  (lexvar, { mg with
             Mcpure_D.memo_group_cons = memo_grp_cons;
             Mcpure_D.memo_group_slice = memo_grp_slice; })

let strip_lexvar_mix_formula (mf: MCP.mix_formula) =
  match mf with
  | MCP.OnePF f ->
    let lexvar, f = strip_lexvar_from_pure f in
    (lexvar, MCP.OnePF f)
  | MCP.MemoF mp -> 
    let lexvar, mp = List.split (List.map strip_lexvar_memo_grp mp) in
    (List.concat lexvar, MCP.MemoF mp)

let strip_lexvar_mix_formula mf =
  let pr0 = !CP.print_formula in
  let pr = !MCP.print_mix_formula in
  Debug.no_1 "strip_lexvar_mix_formula" pr (pr_pair (pr_list pr0) pr) strip_lexvar_mix_formula mf

let strip_lexvar_formula_for_termAssume (f: formula) =
  let _, fp, _, _, _, _ = split_components f in
  let (lexvar, other_p) = strip_lexvar_mix_formula fp in
  let termr, lexvar = List.partition is_TermR_formula lexvar in
  let termr_lex = List.map (fun f ->
      let tinfo = find_lexvar_formula f in tinfo.lex_ann) termr in
  match lexvar with
  | [] -> other_p, None, termr_lex
  | lv::[] ->
    let tinfo = find_lexvar_formula lv in
    let t_ann, ml, il = tinfo.lex_ann, tinfo.lex_exp, tinfo.lex_tmp in 
    let ml = tinfo.lex_exp in
    let il = tinfo.lex_tmp in 
    other_p, Some (t_ann, ml, il), termr_lex
  | _ -> report_error no_pos "[term.ml][strip_lexvar_formula]: More than one LexVar to be stripped." 

let strip_lexvar_formula (f: formula) =
  let _, pure_f, _, _, _, _ = split_components f in
  let (lexvar, other_p) = strip_lexvar_mix_formula pure_f in
  (* Using transform_formula to update the pure part of f *)
  let f_e_f _ = None in
  let f_f _ = None in
  let f_h_f e = Some e in
  let f_m mp = Some (MCP.memo_of_mix other_p) in
  let f_a _ = None in
  let f_p_f pf = Some (MCP.pure_of_mix other_p) in
  let f_b _ = None in
  let f_e _ = None in
  (lexvar, transform_formula (f_e_f, f_f, f_h_f, (f_m, f_a, f_p_f, f_b, f_e)) f) 

let strip_lexvar_es_lhs (es: entail_state) : context =
  if (es.es_var_measures = None) || (has_lexvar_formula es.es_formula) 
  (* This is to ensure we strip Lexvar only once or when necessary *)
  then
    let lexvar, es_f = strip_lexvar_formula es.es_formula in
    let termr, lexvar = List.partition is_TermR_formula lexvar in
    let termr_lex = List.map (fun f ->
        let tinfo = find_lexvar_formula f in tinfo.lex_ann) termr in
    let err_msg = 
      ("[term.ml][strip_lexvar_lhs]: More than one LexVar to be stripped." ^ 
       (!print_entail_state es))
    in
    match lexvar with
    | [] ->
      if termr_lex = [] then Ctx es
      else Ctx { es with
                 es_formula = es_f; 
                 es_term_res_lhs = es.es_term_res_lhs @ termr_lex; }
    | lv::[] ->
      if (es.es_var_measures = None) then
        let tinfo = find_lexvar_formula lv in
        let t_ann, ml, il = tinfo.lex_ann, tinfo.lex_exp, tinfo.lex_tmp in 
        let ml = tinfo.lex_exp in
        let il = tinfo.lex_tmp in 
        Ctx { es with
              es_formula = es_f;
              es_var_measures = Some (t_ann, ml, il);
              es_term_res_lhs = es.es_term_res_lhs @ termr_lex; }
      else report_error no_pos err_msg 
    | _ -> report_error no_pos err_msg 
  else Ctx es

let strip_lexvar_lhs (ctx: context) : context =
  transform_context strip_lexvar_es_lhs ctx

let strip_lexvar_lhs (ctx: context) : context =
  let pr = Cprinter.string_of_context in
  Debug.no_1 "strip_lexvar_lhs" pr pr strip_lexvar_lhs ctx

let strip_lexvar_list_failesc_ctx ctx = 
  transform_list_failesc_context (idf, idf, strip_lexvar_es_lhs) ctx

let rec strip_lexvar_post for_loop sf =
  let rec_f = strip_lexvar_post for_loop in
  match sf with
  | ECase ec -> ECase { ec with formula_case_branches = map_l_snd rec_f ec.formula_case_branches }
  | EBase eb -> EBase { eb with formula_struc_continuation = map_opt rec_f eb.formula_struc_continuation }
  | EAssume af ->
    if for_loop then
      let f_post = mkBase_simp HEmp (MCP.mkMFalse no_pos) in
      EAssume { af with
        formula_assume_simpl = f_post;
        formula_assume_struc = mkEBase f_post None no_pos; }
    else
      EAssume { af with
        formula_assume_simpl = snd (strip_lexvar_formula af.formula_assume_simpl);
        formula_assume_struc = strip_lexvar_assume_struc af.formula_assume_struc }
  | EInfer ei -> EInfer { ei with formula_inf_continuation = rec_f ei.formula_inf_continuation }
  | EList el -> mkEList_no_flatten (map_l_snd rec_f el)

and strip_lexvar_assume_struc sf = 
  let rec_f = strip_lexvar_assume_struc in
  match sf with 
  | ECase ec -> ECase { ec with formula_case_branches = map_l_snd rec_f ec.formula_case_branches }
  | EBase eb ->
    let base = eb.formula_struc_base in
    let term_ann_base = collect_term_ann base in
    let n_base = 
      if List.exists CP.is_TermR term_ann_base (* has_unknown_post_lexvar *)
      then snd (strip_lexvar_formula base) else base
    in 
    EBase { eb with
      formula_struc_base = n_base;
      formula_struc_continuation = map_opt rec_f eb.formula_struc_continuation }
  | EAssume _ -> sf
  | EInfer ei -> EInfer { ei with formula_inf_continuation = rec_f ei.formula_inf_continuation }
  | EList el -> mkEList_no_flatten (map_l_snd rec_f el)

(* let rec strip_lexvar_post sf =                                                               *)
(*   match sf with                                                                              *)
(*   | ECase ec -> ECase { ec with                                                              *)
(*       formula_case_branches = map_l_snd strip_lexvar_post ec.formula_case_branches }         *)
(*   | EBase eb -> EBase { eb with                                                              *)
(*       formula_struc_continuation = map_opt strip_lexvar_post eb.formula_struc_continuation } *)
(*   | EAssume af -> EAssume { af with                                                          *)
(*       formula_assume_simpl = snd (strip_lexvar_formula af.formula_assume_simpl);             *)
(*       formula_assume_struc = strip_lexvar_post af.formula_assume_struc }                     *)
(*   | EInfer ei -> EInfer { ei with                                                            *)
(*       formula_inf_continuation = strip_lexvar_post ei.formula_inf_continuation }             *)
(*   | EList el -> mkEList_no_flatten (map_l_snd strip_lexvar_post el)                          *)

(* End of LexVar handling *) 