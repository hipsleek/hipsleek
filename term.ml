module CP = Cpure
module MCP = Mcpure
module DD = Debug

(* To handle LexVar formula *)
let trans_lexvar_rhs estate lhs_p rhs_p pos =
  try
    let ante = MCP.pure_of_mix lhs_p in
    let conseq = MCP.pure_of_mix rhs_p in
    let src_lv = CP.find_lexvar_formula ante in (* [s1,s2] *)
    let dst_lv = CP.find_lexvar_formula conseq in (* [d1,d2] *)
    (* [s1,s2] |- [d1,d2] -> [(s1,d1), (s2,d2)] *)
    let bnd_measures = List.map2 (fun s d -> (s, d)) src_lv dst_lv in
    if bnd_measures = [] then (estate, lhs_p, rhs_p)
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
        DD.devel_pprint ">>>>>> trans_lexvar_rhs <<<<<<" pos;
        DD.devel_pprint ("Transformed RHS: " ^ (Cprinter.string_of_mix_formula n_rhs_p)) pos;
      end;
      (estate, lhs_p, n_rhs_p)
  with _ -> (estate, lhs_p, rhs_p)

