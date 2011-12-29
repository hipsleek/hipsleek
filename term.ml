module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module DD = Debug
open Gen.Basic
open Globals

(* To handle LexVar formula *)
let trans_lexvar_rhs estate lhs_p rhs_p pos =
  try
    let ante = MCP.pure_of_mix lhs_p in
    let conseq = MCP.pure_of_mix rhs_p in
    let dst_lv = CP.find_lexvar_formula conseq in (* [d1,d2] *)
    (*let src_lv = CP.find_lexvar_formula ante in (* [s1,s2] *)*)
    let src_lv = CP.find_lexvar_formula (estate.CF.es_var_measures) in
    (* Filter LexVar in RHS *)
    let rhs_ls = CP.split_conjunctions conseq in
    let (_, other_rhs) = List.partition (CP.is_lexvar) rhs_ls in
    let conseq = CP.join_conjunctions other_rhs in
    (* [s1,s2] |- [d1,d2] -> [(s1,d1), (s2,d2)] *)
    let bnd_measures = List.map2 (fun s d -> (s, d)) src_lv dst_lv in
    (* [(0,0), (s2,d2)] -> [(s2,d2)] *)
    let bnd_measures = CP.syn_simplify_lexvar bnd_measures in
    if bnd_measures = [] then (estate, lhs_p, MCP.mix_of_pure conseq)
    else
      (* [(s1,d1), (s2,d2)] -> [[(s1,d1)], [(s1,d1),(s2,d2)]]*)
      let lst_measures = List.fold_right (fun bm res ->
        [bm]::(List.map (fun e -> bm::e) res)) bnd_measures [] in
      (* [(s1,d1),(s2,d2)] -> s1=d1 & s2>d2 *)
      let lex_formula measure = snd (List.fold_right (fun (s,d) (flag,res) ->
        let f = 
			    if flag then CP.BForm ((CP.mkGt s d pos, None), None) (* s>d *)
			    else CP.BForm ((CP.mkEq s d pos, None), None) in (* s=d *)
        (false, CP.mkAnd f res pos)) measure (true, CP.mkTrue pos)) in
      let rank_formula = List.fold_left (fun acc m ->
        CP.mkOr acc (lex_formula m) None pos) (CP.mkFalse pos) lst_measures in
      let n_conseq = CP.mkAnd conseq (CP.simplify_disj rank_formula) pos in
      let n_rhs_p = MCP.mix_of_pure n_conseq in
      begin
        (* print_endline ">>>>>> trans_lexvar_rhs <<<<<<" ; *)
        (* print_endline ("Transformed RHS: " ^ (Cprinter.string_of_mix_formula n_rhs_p)) ; *)
        DD.devel_pprint ">>>>>> trans_lexvar_rhs <<<<<<" pos;
        DD.devel_pprint ("Transformed RHS: " ^ (Cprinter.string_of_mix_formula n_rhs_p)) pos;
      end;
      (estate, lhs_p, n_rhs_p)
  with _ -> (estate, lhs_p, rhs_p)

(*
type: 'a ->
  MCP.mix_formula ->
  MCP.mix_formula -> Globals.loc -> 'a * MCP.mix_formula * MCP.mix_formula
*)

let trans_lexvar_rhs estate lhs_p rhs_p pos =
  let pr = !CF.print_mix_formula in
  let pr2 = !CF.print_entail_state_short in
   Gen.Debug.no_2 "trans_lexvar_rhs" pr pr (pr_triple pr2 pr pr)  
      (fun _ _ -> trans_lexvar_rhs estate lhs_p rhs_p pos) lhs_p rhs_p

let strip_lexvar_mix_formula (mf: MCP.mix_formula) =
  let mf_p = MCP.pure_of_mix mf in
  let mf_ls = CP.split_conjunctions mf_p in
  let (lexvar, other_p) = List.partition (CP.is_lexvar) mf_ls in
  (lexvar, CP.join_conjunctions other_p)

let strip_lexvar_lhs (ctx: CF.context) : CF.context =
  let es_strip_lexvar_lhs (es: CF.entail_state) : CF.context =
    let _, pure_f, _, _, _ = CF.split_components es.CF.es_formula in
    let (lexvar, other_p) = strip_lexvar_mix_formula pure_f in
    (* Using transform_formula to update the pure part of es_f *)
    let f_e_f _ = None in
    let f_f _ = None in
    let f_h_f e = Some e in
    let f_m mp = Some (MCP.memoise_add_pure_N_m (MCP.mkMTrue_no_mix no_pos) other_p) in
    let f_a _ = None in
    let f_p_f pf = Some other_p in
    let f_b _ = None in
    let f_e _ = None in
    match lexvar with
    | [] -> CF.Ctx es
    | lv::[] -> CF.Ctx { es with 
      CF.es_formula = CF.transform_formula (f_e_f, f_f, f_h_f, (f_m, f_a, f_p_f, f_b, f_e)) es.CF.es_formula;
      CF.es_var_measures = lv; 
    }
    | _ -> report_error no_pos "[term.ml][strip_lexvar_lhs]: More than one LexVar to be stripped." 
  in CF.transform_context es_strip_lexvar_lhs ctx

