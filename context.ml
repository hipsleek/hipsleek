open Globals
open Cformula
open Cast
open Cprinter
open Gen.Basic


type match_res = {
    match_res_lhs_node : h_formula; (* node from the extracted formula *)                                                                                        
    match_res_lhs_rest : h_formula; (* lhs formula - contains holes in place of matched immutable nodes/views *)
    match_res_holes : (h_formula * int) list; (* imm node/view that have been replaced in lhs together with their corresponding hole id *)
    match_res_type : match_type; (* indicator of what type of matching *)
    match_res_rhs_node : h_formula;
    match_res_rhs_rest : h_formula;}
    

(*
type context = (h_formula (* frame with a hole *)
		* h_formula (* formula from the hole *)
		* int (* hole identifier*)
		* h_formula (* node from the extracted formula *)                                                                                          
		* match_type (* indicator of what type of macthing *)
		* h_formula (* context - reading phase prior to hole *)
		* (int * h_formula) list (* multiple holes with immutable terms extracted *)
	       )
*)

(*
and phase_type = 
  | Spatial  
  | Classic
*)

and mater_source = 
  | View_mater
  | Coerc_mater of  coercion_decl (* (Iast.coercion_type * Globals.ident) *)

and match_type =
  | Root
  | MaterializedArg of (mater_property*mater_source) 
  | WArg
  
and action = 
  | M_match of match_res
  | M_fold of match_res
  | M_unfold  of (match_res * int) (* zero denotes no counting *)
  | M_base_case_unfold of match_res
  | M_base_case_fold of match_res
  | M_rd_lemma of match_res
  | M_lemma  of (match_res * (coercion_decl option))
  | Undefined_action of match_res
  | M_Nothing_to_do of string
  | M_unmatched_rhs_data_node of h_formula
  | Seq_action of action_wt list
  | Search_action of action_wt list (*the match_res indicates if pushing holes for each action is required or it will be done once, at the end*)
  
  (* | Un *)
  (* | M *)
  (* | Opt int *)

and action_wt = (int * action)  (* -1 : unknown, 0 : mandatory; >0 : optional (lower value has higher priority) *) 

let is_complex_action a = match a with
  | Search_action _ 
  | Seq_action _ -> true
  | _ -> false
  
(* let is_search_action_wt (_,a) = is_complex_action a *)

let pr_mater_source ms = match ms with
  | View_mater -> fmt_string "view_defn_mater"
  | Coerc_mater c -> fmt_string ("coerc_defn_mater: "^(string_of_coercion_type c.coercion_type)^" "^c.coercion_name)
  
let pr_match_type (e:match_type):unit =
  match e with
    | Root -> fmt_string "Root"
    | MaterializedArg (mv,ms) -> 
      fmt_string "MaterializedArg "; pr_mater_prop mv;fmt_string " " ;pr_mater_source ms    
    | WArg -> fmt_string "WArg"

let pr_match_res (c:match_res):unit =
  fmt_string "{ match_res_lhs_node "; pr_h_formula c.match_res_lhs_node;
  fmt_string "\n match_res_lhs_rest "; pr_h_formula c.match_res_lhs_rest;
  fmt_string "\n match_res_holes "; pr_seq "" (Cprinter.pr_pair  pr_h_formula pr_int) c.match_res_holes;  
  fmt_string "\n match_res_type "; pr_match_type c.match_res_type;
  fmt_string "\n match_res_rhs_node "; pr_h_formula c.match_res_rhs_node;
  fmt_string "\n match_res_rhs_rest "; pr_h_formula c.match_res_rhs_rest;
  fmt_string "}"
  
let pr_simpl_match_res (c:match_res):unit = 
fmt_string "(";
  fmt_string "\n match_res_lhs_node "; pr_h_formula c.match_res_lhs_node;
  fmt_string "\n match_res_rhs_node "; pr_h_formula c.match_res_rhs_node;
  fmt_string ")"

let rec pr_action_res pr_mr a = match a with
  | Undefined_action e -> pr_mr e; fmt_string "==> Undefined_action"
  | M_match e -> pr_mr e; fmt_string "==> Match"
  | M_fold e -> pr_mr e; fmt_string "==> Fold"
  | M_unfold (e,i) -> pr_mr e; fmt_string ("==> Unfold "^(string_of_int i))
  | M_base_case_unfold e -> pr_mr e; fmt_string "==> Base case unfold"
  | M_base_case_fold e -> pr_mr e; fmt_string "==> Base case fold"
  | M_rd_lemma e -> pr_mr e; fmt_string "==> Right distributive lemma"
  | M_lemma (e,s) -> pr_mr e; fmt_string ("==> "^(match s with | None -> "any lemma" | Some c-> "lemma "
        ^(string_of_coercion_type c.coercion_type)^" "^c.coercion_name))
  | M_Nothing_to_do s -> fmt_string ("Nothing can be done: "^s)
  | M_unmatched_rhs_data_node h -> fmt_string ("Unmatched RHS data note: "^(string_of_h_formula h))
  | Seq_action l -> fmt_string "seq:"; pr_seq "" (pr_action_wt_res pr_mr) l
  | Search_action l -> fmt_string "search:"; pr_seq "" (pr_action_wt_res pr_mr) l

and pr_action_wt_res pr_mr (w,a) = (pr_action_res pr_mr a);
  fmt_string ("(Weigh:"^(string_of_int w)^")")

let string_of_action_res_simpl (e:action) = poly_string_of_pr (pr_action_res pr_simpl_match_res) e

let string_of_action_wt_res_simpl (e:action_wt) = poly_string_of_pr (pr_action_wt_res pr_simpl_match_res) e

let string_of_action_res e = poly_string_of_pr (pr_action_res pr_match_res) e

let string_of_action_wt_res e = poly_string_of_pr (pr_action_wt_res pr_match_res) e


let string_of_match_res e = poly_string_of_pr pr_match_res e  
   
let action_get_holes a = match a with
  | Undefined_action e
  | M_match e
  | M_fold e
  | M_unfold (e,_)
  | M_rd_lemma e
  | M_lemma (e,_)
  | M_base_case_unfold e
  | M_base_case_fold e -> Some e.match_res_holes
  | Seq_action _
  | M_Nothing_to_do _  
  | M_unmatched_rhs_data_node _
  | Search_action _ ->None

 
let action_get_holes (a:action):(h_formula*int) list option = 
  let pr1 = string_of_action_res in
  let pr2 = pr_option pr_no in
  Gen.Debug.no_1 "action_get_holes" pr1 pr2 action_get_holes a

let action_wt_get_holes (_,a) = action_get_holes a
   
(*
and ctx_type = 
  | SpatialImm
  | SpatialMutable
  | ConjImm
  | ConjMutable
*)
(* 
   returns a list of tuples: (rest, matching node, flag, phase, ctx)
   The flag associated with each node lets us know if the match is at the root pointer, materialized arg, arg.
*)

(* computes must-alias sets from equalities, maintains the invariant *)
(* that these sets form a partition. *)
let rec alias_x (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list = 
  match ptr_eqs with
  | (v1, v2) :: rest -> begin
	  let rest_sets = alias_x rest in
	  let search (v : CP.spec_var) (asets : CP.spec_var list list) = List.partition (fun aset -> CP.mem v aset) asets in
	  let av1, rest1 = search v1 rest_sets in
	  let av2, rest2 = search v2 rest1 in
	  let v1v2_set = CP.remove_dups_svl (List.concat ([v1; v2] :: (av1 @ av2))) in
	  v1v2_set :: rest2
	end
  | [] -> []


(* let alias_x (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list =  *)
(*   let aset = alias_x ptr_eqs in *)
(* List.filter (fun l -> List.length l > 1) aset *)

let alias_nth i (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list = 
  let psv = Cprinter.string_of_spec_var in
  let pr1 l = pr_list (pr_pair psv psv) l in
  let pr2 l = pr_list (pr_list psv) l in
  Gen.Debug.no_1_num i "alias" pr1 pr2 alias_x ptr_eqs

let get_aset (aset : CP.spec_var list list) (v : CP.spec_var) : CP.spec_var list =
  let tmp = List.filter (fun a -> CP.mem v a) aset in
  match tmp with
	| [] -> []
	| [s] -> s
	| _ -> failwith ((string_of_spec_var v) ^ " appears in more than one alias sets")

let get_aset (aset : CP.spec_var list list) (v : CP.spec_var) : CP.spec_var list =
let psv = Cprinter.string_of_spec_var in
 let pr1 = (pr_list psv) in
 let pr2 = pr_list pr1 in
 Gen.Debug.no_2 "get_aset" pr2  psv pr1 get_aset aset v

let comp_aliases_x (rhs_p:MCP.mix_formula) : (CP.spec_var) list list =
    let eqns = MCP.ptr_equations_without_null rhs_p in
    alias_nth 1 eqns 

let comp_aliases (rhs_p:MCP.mix_formula) : (CP.spec_var) list list =
 let psv = Cprinter.string_of_spec_var in
 let pr2 = (pr_list (pr_list psv)) in
 let pr1 = Cprinter.string_of_mix_formula in
 Gen.Debug.no_1 "comp_aliase" pr1 pr2 comp_aliases_x rhs_p

let comp_alias_part r_asets a_vars = 
    (* let a_vars = lhs_fv @ posib_r_aliases in *)
    let fltr = List.map (fun c-> Gen.BList.intersect_eq (CP.eq_spec_var) c a_vars) r_asets in
    let colaps l = List.fold_left (fun a c -> match a with 
      | [] -> [(c,c)]
      | h::_-> (c,(fst h))::a) [] l in
    List.concat (List.map colaps fltr) 

(*  (resth1, anode, r_flag, phase, ctx) *)   
let rec choose_context_x prog rhs_es lhs_h lhs_p rhs_p posib_r_aliases rhs_node rhs_rest pos :  match_res list =
  (* let _ = print_string("choose ctx: lhs_h = " ^ (string_of_h_formula lhs_h) ^ "\n") in *)
  let imm,p = match rhs_node with
    | DataNode{h_formula_data_node=p;h_formula_data_imm=imm} |ViewNode{h_formula_view_node=p;h_formula_view_imm=imm}-> (imm,p)
    | _ -> report_error no_pos "choose_context unexpected rhs formula\n" in
  let lhs_fv = (h_fv lhs_h) @ (MCP.mfv lhs_p) in
  let eqns' = MCP.ptr_equations_without_null lhs_p in
  let r_eqns =
    let eqns = (MCP.ptr_equations_without_null rhs_p)@rhs_es in
    let r_asets = alias_nth 2 eqns in
    let a_vars = lhs_fv @ posib_r_aliases in
    let fltr = List.map (fun c-> Gen.BList.intersect_eq (CP.eq_spec_var) c a_vars) r_asets in
    let colaps l = List.fold_left (fun a c -> match a with 
      | [] -> [(c,c)]
      | h::_-> (c,(fst h))::a) [] l in
    List.concat (List.map colaps fltr) in
  let eqns = (p, p) :: eqns' in
  let asets = alias_nth 3 (eqns@r_eqns) in
  let paset = get_aset asets p in (* find the alias set containing p *)
  if Gen.is_empty paset then  failwith ("choose_context: Error in getting aliases for " ^ (string_of_spec_var p))
  else if (* not(CP.mem p lhs_fv) ||  *)(!Globals.enable_syn_base_case && (CP.mem CP.null_var paset))	then 
	(Debug.devel_pprint ("choose_context: " ^ (string_of_spec_var p) ^ " is not mentioned in lhs\n\n") pos; [] )
  else (spatial_ctx_extract prog lhs_h paset imm rhs_node rhs_rest) 

and choose_context prog es lhs_h lhs_p rhs_p posib_r_aliases rhs_node rhs_rest pos :  match_res list =
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 l = pr_list string_of_match_res l in
  let pr3 = Cprinter.string_of_mix_formula in
  (*let pr2 (m,svl,_) = (Cprinter.string_of_spec_var_list svl) ^ ";"^ (Cprinter.string_of_mix_formula m) in*)
  Gen.Debug.loop_4_no "choose_context" pr1 pr1 pr3 pr3 pr2 
      (fun _ _ _ _ -> choose_context_x prog es lhs_h lhs_p rhs_p posib_r_aliases rhs_node rhs_rest pos) lhs_h rhs_node lhs_p rhs_p



and view_mater_match prog c vs1 aset imm f =
  let vdef = look_up_view_def_raw prog.prog_view_decls c in
  let mvs = subst_mater_list_nth 1 vdef.view_vars vs1 vdef.view_materialized_vars in
  try
    let mv = List.find (fun v -> List.exists (CP.eq_spec_var v.mater_var) aset) mvs in
    if imm then
      let hole_no = Globals.fresh_int() in
      [(Hole hole_no, f, [(f, hole_no)], MaterializedArg (mv,View_mater))]
    else [(HTrue, f, [], MaterializedArg (mv,View_mater))]
  with 
      _ ->  
          if List.exists (fun v -> CP.mem v aset) vs1 then
            if imm then
              let hole_no = Globals.fresh_int() in 
              [(Hole hole_no, f, [(f, hole_no)], WArg)]
            else [(HTrue, f, [], WArg)]
          else []

and choose_full_mater_coercion_x l_vname l_vargs r_aset (c:coercion_decl) =
  if not(c.coercion_simple_lhs && c.coercion_head_view = l_vname) then None
  else 
    let args = List.tl (fv_simple_formula c.coercion_head) in (* dropping the self parameter *)
    let lmv = subst_mater_list_nth 2 args l_vargs c.coercion_mater_vars in
    try
      let mv = List.find (fun v -> List.exists (CP.eq_spec_var v.mater_var) r_aset) lmv in
      Some (c,mv)
    with  _ ->  None

and choose_full_mater_coercion l_vname l_vargs r_aset (c:coercion_decl) =
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr (c,_) = string_of_coercion c in
  Gen.Debug.no_1 "choose_full_mater_coercion" pr_svl (pr_option pr) (fun _ -> choose_full_mater_coercion_x l_vname l_vargs r_aset c) r_aset

and coerc_mater_match_x prog l_vname (l_vargs:P.spec_var list) r_aset imm (lhs_f:Cformula.h_formula) =
  (* TODO : how about right coercion, Cristina? *)
  let coercs = prog.prog_left_coercions in
  let pos_coercs = List.fold_right (fun c a -> match (choose_full_mater_coercion l_vname l_vargs r_aset c) with 
    | None ->  a 
    | Some t -> t::a) coercs [] in
  let res = List.map (fun (c,mv) -> (HTrue, lhs_f, [], MaterializedArg (mv,Coerc_mater c))) pos_coercs in
  (* let pos_coercs = List.fold_left  *)
  (*   (fun a c->  *)
  (*       let args = List.tl (fv_simple_formula c.coercion_head) in  *)
  (*       let lmv = subst_mater_list_nth 3 args l_vargs c.coercion_mater_vars in *)
  (*       try *)
  (*         let mv = List.find (fun v -> List.exists (CP.eq_spec_var v.mater_var) r_aset) lmv in *)
  (*         (HTrue, lhs_f, [], MaterializedArg (mv,Coerc_mater c.coercion_name))::a *)
  (*       with  _ ->  a) [] pos_coercs in *)
  if imm then [] else res

and coerc_mater_match prog l_vname (l_vargs:P.spec_var list) r_aset imm (lhs_f:Cformula.h_formula) =
  let pr = Cprinter.string_of_h_formula in
  let pr4 (h1,h2,l,mt) = pr_pair pr pr (h1,h2) in
  let pr2 ls = pr_list pr4 ls in
  let pr_svl = Cprinter.string_of_spec_var_list in
  Gen.Debug.no_3 "coerc_mater_match" pr_id pr_svl pr_svl pr2
      (fun _ _ _ -> coerc_mater_match_x prog l_vname (l_vargs:P.spec_var list) r_aset imm (lhs_f:Cformula.h_formula)) l_vname l_vargs r_aset
      
(*
  spatial context
*)
      
and spatial_ctx_extract p f a i rn rr = 
  let pr = pr_list string_of_match_res in
  let pr_svl = Cprinter.string_of_spec_var_list in
  (* let pr = pr_no in *)
  Gen.Debug.no_4 "spatial_context_extract " string_of_h_formula string_of_bool pr_svl string_of_h_formula pr 
      (fun _ _ _ _ -> spatial_ctx_extract_x p f a i rn rr) f i a rn

and spatial_ctx_extract_x prog (f0 : h_formula) (aset : CP.spec_var list) (imm : bool) rhs_node rhs_rest : match_res list  =
  (* let _ = print_string("spatial_ctx_extract with f0 = " ^ (string_of_h_formula f0) ^ "\n") in  *)
  let rec helper f = match f with
    | HTrue 
    | HFalse -> []
    | Hole _ -> []
    | DataNode ({h_formula_data_node = p1; 
	  h_formula_data_imm = imm1}) ->
          if ((CP.mem p1 aset) && (subtype imm imm1)) then 
            if imm then
              let hole_no = Globals.fresh_int() in 
              [((Hole hole_no), f, [(f, hole_no)], Root)]
            else
              [(HTrue, f, [], Root)]
          else 
            []
    | ViewNode ({h_formula_view_node = p1;
	  h_formula_view_imm = imm1;
	  h_formula_view_arguments = vs1;
	  h_formula_view_name = c}) ->
          if (subtype imm imm1) then
            (if (CP.mem p1 aset)  then
              if imm then
                let hole_no = Globals.fresh_int() in
                (*[(Hole hole_no, matched_node, hole_no, f, Root, HTrue, [])]*)
                [(Hole hole_no, f, [(f, hole_no)], Root)]
              else
                [(HTrue, f, [], Root)]
            else
              let vmm = view_mater_match prog c vs1 aset imm f in
              let cmm = coerc_mater_match prog c vs1 aset imm f in
              vmm@cmm
            )
          else []
    | Star ({h_formula_star_h1 = f1;
	  h_formula_star_h2 = f2;
	  h_formula_star_pos = pos}) ->
          let l1 = helper f1 in
          let res1 = List.map (fun (lhs1, node1, hole1, match1) -> (mkStarH lhs1 f2 pos, node1, hole1, match1)) l1 in  

          let l2 = helper f2 in
          let res2 = List.map (fun (lhs2, node2, hole2, match2) -> (mkStarH f1 lhs2 pos, node2, hole2, match2)) l2 in
          res1 @ res2
    | _ -> 
          let _ = print_string("[context.ml]: There should be no conj/phase in the lhs at this level; lhs = " ^ (string_of_h_formula f) ^ "\n") in
          failwith("[context.ml]: There should be no conj/phase in the lhs at this level\n")

  (*| Conj ({h_formula_conj_h1 = f1;
    h_formula_conj_h2 = f2;
    h_formula_conj_pos = pos}) -> (* [] *)
    let l1 = helper f1 in
    let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (mkConjH ctx1 f2 pos, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in  

    let l2 = helper f2 in
    let res2 = List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (mkConjH f1 ctx2 pos, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2 in
    res1 @ res2

    | Phase ({h_formula_phase_rd = f1;
    h_formula_phase_rw = f2;
    h_formula_phase_pos = pos}) ->
  (* let _ = print_string("in phase with f1 = " ^ (string_of_h_formula f1) ^ "\n") in *)
  (* let _ = print_string("and f2 = " ^ (string_of_h_formula f2) ^ "\n") in *)
    let l1 = helper f1 in		
    let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (mkPhaseH ctx1 f2 pos, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in  

    let l2 = helper f2 in
    let res2 = 
    if not(imm) && (List.length l2) > 0 then
  (* drop read phase *)
    List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2
    else
    List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (mkPhaseH f1 ctx2 pos, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2
    in
    res1 @ res2
  (*	  
    let l2 = helper f2 in
  (*List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> ((*mkPhaseH f1 ctx2 pos*)ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2*)
    List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (mkPhaseH f1 ctx2 pos, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2  
  *)
  *)
  in
  let l = helper f0 in
  List.map (fun (lhs_rest,lhs_node,holes,mt) ->
      { match_res_lhs_node = lhs_node;
      match_res_lhs_rest = lhs_rest;
      match_res_holes = holes;
      match_res_type = mt;
      match_res_rhs_node = rhs_node;
      match_res_rhs_rest = rhs_rest;}) l
      
and process_one_match prog (c:match_res) :action_wt =
  let pr1 = string_of_match_res in
  let pr2 = string_of_action_wt_res  in
  Gen.Debug.no_1 "process_one_match" pr1 pr2 (process_one_match_x prog) c 

(*
(* return a list of nodes from heap f that appears in *)
(* alias set aset. The flag associated with each node *)
(* lets us know if the match is at the root pointer,  *)
(* or at materialized args,...                        *)
*)
and process_one_match_x prog (c:match_res) :action_wt =
  let rhs_node = c.match_res_rhs_node in
  let lhs_node = c.match_res_lhs_node in
  let r = match c.match_res_type with 
    | Root ->
          (match lhs_node,rhs_node with
            | DataNode dl, DataNode dr -> 
                  if (String.compare dl.h_formula_data_name dr.h_formula_data_name)==0 then (0,M_match c)
                  else (0,M_Nothing_to_do ("no proper match (type error) found for: "^(string_of_match_res c)))
            | ViewNode vl, ViewNode vr -> 
                  let l1 = [(1,M_base_case_unfold c)] in
                  let l2 = 
                    if (String.compare vl.h_formula_view_name vr.h_formula_view_name)==0 then [(1,M_match c)] 
                    else if not(is_rec_view_def prog vl.h_formula_view_name) then [(2,M_unfold (c,0))] 
                    else if not(is_rec_view_def prog vr.h_formula_view_name) then [(2,M_fold c)] 
                    else [(1,M_Nothing_to_do ("mis-matched LHS:"^(vl.h_formula_view_name)^" and RHS: "^(vr.h_formula_view_name)))]
                  in
                  let l3 = if (vl.h_formula_view_original || vr.h_formula_view_original)
                  then begin
                    let left_ls = look_up_coercion_with_target prog.prog_left_coercions vl.h_formula_view_name vr.h_formula_view_name in
                    let right_ls = look_up_coercion_with_target prog.prog_right_coercions vr.h_formula_view_name vl.h_formula_view_name in
                    let left_act = List.map (fun l -> (1,M_lemma (c,Some l))) left_ls in
                    let right_act = List.map (fun l -> (1,M_lemma (c,Some l))) right_ls in
                    if (left_act==[] && right_act==[]) then [] (* [(1,M_lemma (c,None))] *) (* only targetted lemma *)
                    else left_act@right_act
                  end
                  else [] in
                  let l4 = []
                    (*if get_view_original rhs_node then 
                      [M_base_case_fold c] 
                      else [] *)in
                  let src = (-1,Search_action (l1@l2@l3@l4)) in
                  src (*Seq_action [l1;src]*)
            | DataNode dl, ViewNode vr -> (0,M_fold c)  (* (-1,Search_action [(1,M_fold c);(1,M_rd_lemma c)]) *)
            | ViewNode vl, DataNode dr -> (0,M_unfold (c,0))
            | _ -> report_error no_pos "process_one_match unexpected formulas\n"	
          )
    | MaterializedArg (mv,ms) ->
          (match lhs_node,rhs_node with
            | DataNode dl, _ -> (1,M_Nothing_to_do ("matching lhs: "^(string_of_h_formula lhs_node)^" with rhs: "^(string_of_h_formula rhs_node)))
            | ViewNode vl, ViewNode vr -> 
                  let a1 = (match ms with
                    | View_mater -> M_unfold (c,0)
                    | Coerc_mater s -> M_lemma (c,Some s)) in
                  (match mv.mater_full_flag with
                    | true -> (0,a1)
                    | false -> (1,a1)
                          (*let a2 = in
                            Search_action (a1::a2)*))
            | ViewNode vl, DataNode dr -> 
                  let i = if mv.mater_full_flag then 0 else 1 in 
                  let a1 = (match ms with
                    | View_mater -> (i,M_unfold (c,i)) 
                    | Coerc_mater s -> (i,M_lemma (c,Some s))) in
                  a1
                      (* (match mv.mater_full_flag with *)
                      (*   | true -> (0,a1) *)
                      (*   | false -> (1,M_unfold (c,1)))  *)
                      (* to prevent infinite unfolding *)
                      (* M_Nothing_to_do "no unfold for partial materialize as loop otherwise") *)
                      (* unfold to some depth *)
                      (* M_Nothing_to_do (string_of_match_res c) *)
            | _ -> report_error no_pos "process_one_match unexpected formulas\n"	 
          )
    | WArg -> (1,M_Nothing_to_do (string_of_match_res c)) in
  r

and process_matches prog lhs_h ((l:match_res list),(rhs_node,rhs_rest)) =
  let pr = Cprinter.string_of_h_formula   in
  let pr1 = pr_list string_of_match_res in
  let pr2 x = (fun (l1, (c1,c2)) -> "(" ^ (pr1 l1) ^ ",(" ^ (pr c1) ^ "," ^ (pr c2) ^ "))" ) x in
  let pr3 = string_of_action_wt_res in
  Gen.Debug.no_2 "process_matches" pr pr2 pr3 (fun _ _-> process_matches_x prog lhs_h (l, (rhs_node,rhs_rest))) lhs_h (l, (rhs_node,rhs_rest))

and process_matches_x prog lhs_h ((l:match_res list),(rhs_node,rhs_rest)) = match l with
  | [] -> let r0 = (1,M_unmatched_rhs_data_node rhs_node) in
          if (is_view rhs_node) && (get_view_original rhs_node) then
            let r = (1,M_base_case_fold { 
            match_res_lhs_node = HTrue; 
            match_res_lhs_rest = lhs_h; 
            match_res_holes = [];
            match_res_type = Root;
            match_res_rhs_node = rhs_node;
            match_res_rhs_rest = rhs_rest;}) in
        (-1, (Search_action [r]))
      else r0
(* M_Nothing_to_do ("no match found for: "^(string_of_h_formula rhs_node)) *)
  | x::[] -> process_one_match prog x 
  | _ -> (-1,Search_action (List.map (process_one_match prog) l))

and sort_wt (ys: action_wt list) : action list =
  let rec recalibrate_wt (w,a) = match a with
    | Search_action l ->
          let l = List.map recalibrate_wt l in
          let sl = List.sort (fun (w1,_) (w2,_) -> if w1<w2 then -1 else if w1>w2 then 1 else 0 ) l in
          let h = (List.hd sl) in
          let rw = (fst h) in
          if (rw==0) then h
          else (rw,Search_action sl)
    | Seq_action l ->
          let l = List.map recalibrate_wt l in
          let rw = List.fold_left (fun a (w,_)-> if (a<=w) then w else a) (fst (List.hd l)) (List.tl l) in
          (rw,Seq_action l)
    | _ -> if (w == -1) then (0,a) else (w,a) in
  let ls = List.map recalibrate_wt ys in
  let sl = List.sort (fun (w1,_) (w2,_) -> if w1<w2 then -1 else if w1>w2 then 1 else 0 ) ls in
  (snd (List.split sl)) 

and pick_unfold_only ((w,a):action_wt) : action_wt list =
  match a with
    | M_unfold _ -> [(w,a)]
    | Seq_action l -> 
          if l==[] then [] 
          else pick_unfold_only (List.hd l)
    | Search_action l -> List.concat (List.map pick_unfold_only l)
    | _ -> []


(* and heap_entail_non_empty_rhs_heap_x prog is_folding  ctx0 estate ante conseq lhs_b rhs_b pos : (list_context * proof) = *)

and compute_actions_x prog es lhs_h lhs_p rhs_p posib_r_alias rhs_lst pos :action = 
  let r = List.map (fun (c1,c2)-> (choose_context prog es lhs_h lhs_p rhs_p posib_r_alias c1 c2 pos,(c1,c2))) rhs_lst in
  (* match r with  *)
  (*   | [] -> M_Nothing_to_do "no nodes to match" *)
  (*   | x::[]-> process_matches lhs_h x *)
  (*   | _ ->  List.hd r (\*Search_action (None,r)*\) *)
  let r = List.map (process_matches prog lhs_h) r in
  match r with
    | [] -> M_Nothing_to_do "no nodes on RHS"
    | xs -> let ys = sort_wt r in List.hd (ys)

and compute_actions prog es lhs_h lhs_p rhs_p posib_r_alias rhs_lst pos =
  let psv = Cprinter.string_of_spec_var in
  let pr0 = pr_list (pr_pair psv psv) in
  let pr = Cprinter.string_of_h_formula   in
  (* let pr1 x = String.concat ";\n" (List.map (fun (c1,c2)-> "("^(Cprinter.string_of_h_formula c1)^" *** "^(Cprinter.string_of_h_formula c2)^")") x) in *)
  let pr3 = Cprinter.string_of_mix_formula in
  let pr1 x = pr_list (fun (c1,c2)-> "("^(Cprinter.string_of_h_formula c1)^", "^(Cprinter.string_of_h_formula c2)^")") x in
  let pr2 = string_of_action_res_simpl in
  Gen.Debug.no_5 "compute_actions" pr0 pr pr1 pr3 pr3 pr2 (fun _ _ _ _ _-> compute_actions_x prog es lhs_h lhs_p rhs_p posib_r_alias rhs_lst pos) es lhs_h rhs_lst lhs_p rhs_p

and input_formula_in2_frame (frame, id_hole) (to_input : formula) : formula =
  match to_input with
    | Base (fb) ->
	      Base{fb with formula_base_heap = input_h_formula_in2_frame (frame, id_hole) fb.formula_base_heap;}
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) -> 
	      Or({formula_or_f1 = (input_formula_in2_frame (frame, id_hole) f1);
	      formula_or_f2 = (input_formula_in2_frame (frame, id_hole) f2);
	      formula_or_pos = pos})
    | Exists(fe) ->
	      Exists{fe with formula_exists_heap = input_h_formula_in2_frame (frame, id_hole) fe.formula_exists_heap;}


and input_h_formula_in2_frame (frame, id_hole) (to_input : h_formula) : h_formula = 
  match frame with
    | Hole id ->
	      if id = id_hole then to_input
	      else frame
    | Star ({h_formula_star_h1 = f1;
	  h_formula_star_h2 = f2;
	  h_formula_star_pos = pos}) -> 
	      let new_f1 = input_h_formula_in2_frame (f1, id_hole) to_input in 
	      let new_f2 = input_h_formula_in2_frame (f2, id_hole) to_input in
	      Star ({h_formula_star_h1 = new_f1;
		  h_formula_star_h2 = new_f2;
		  h_formula_star_pos = pos})  
    | Conj ({h_formula_conj_h1 = f1;
	  h_formula_conj_h2 = f2;
	  h_formula_conj_pos = pos}) -> 
	      let new_f1 = input_h_formula_in2_frame (f1, id_hole) to_input in 
	      let new_f2 = input_h_formula_in2_frame (f2, id_hole) to_input in
	      Conj ({h_formula_conj_h1 = new_f1;
		  h_formula_conj_h2 = new_f2;
		  h_formula_conj_pos = pos})  
    | Phase ({h_formula_phase_rd = f1;
	  h_formula_phase_rw = f2;
	  h_formula_phase_pos = pos}) -> 
	      let new_f1 = input_h_formula_in2_frame (f1, id_hole) to_input in 
	      let new_f2 = input_h_formula_in2_frame (f2, id_hole) to_input in
	      Phase ({h_formula_phase_rd = new_f1;
		  h_formula_phase_rw = new_f2;
		  h_formula_phase_pos = pos})  
    | DataNode _ 
    | ViewNode _
    | HTrue | HFalse -> frame
          

(* 
   and input_ctx_frame (ctx : Cformula.context) : Cformula.context =
   match ctx with
   | Ctx(es) ->
   Ctx {es with es_formula = input_formula_in2_frame es.es_frame es.es_formula; es_frame = [];}
   | OCtx(c1, c2) -> OCtx((input_ctx_frame c1), (input_ctx_frame c2))

   and input_list_ctx_frame (ctx : Cformula.list_context) : Cformula.list_context =
   match ctx with
   | FailCtx _ -> ctx
   | SuccCtx (cl) -> SuccCtx(List.map input_ctx_frame cl)
*)
(* create an empty context *)
(*and mk_empty_frame (id_hole : int) : h_formula = Hole(id_hole)*)
(*
  and mk_empty_frame (): (h_formula * int) = 
  let hole_id = Globals.fresh_int () in
  (Hole(hole_id), hole_id)

(* check whether a context is empty *)
  and is_empty_frame (frame : formula) : bool = match frame with 
  | Base ({formula_base_heap = fb_h;}) -> is_hole_heap_frame fb_h
  | _  -> failwith "context.ml, is_empty_ctx: check this\n" (* todo: check this *)

  and is_hole_heap_frame (frame_h : h_formula) : bool = match frame_h with
  | Hole _ -> true
  | _ -> false

*)
(*------	
  and update_ctx_frame ctx0 (frame, hole_id) = 
  match ctx0 with
  | Ctx(es) -> Ctx{es with es_frame = (frame, hole_id)}
  | OCtx(c1, c2) -> 
  let update_c1 = update_ctx_frame c1 (frame, hole_id) in
  let update_c2 = update_ctx_frame c2 (frame, hole_id) in
  OCtx(update_c1, update_c2)

  and update_list_ctx_frame ctx0 (frame, hole_id) = 
  match ctx0 with
  | FailCtx _ -> let _ = print_string("fail with frame " ^ (string_of_h_formula frame) ^ "\n") in ctx0
  | SuccCtx (cl) -> SuccCtx(List.map (fun x -> update_ctx_frame x (frame, hole_id))cl) 
  -----*)
and update_ctx_es_formula ctx0 f = 
  match ctx0 with
    | Ctx(es) -> Ctx{es with es_formula = f}
    | OCtx(c1, c2) -> 
	      let update_c1 = update_ctx_es_formula c1 f in
	      let update_c2 = update_ctx_es_formula c2 f in
	      OCtx(update_c1, update_c2)

and update_ctx_es_orig_conseq ctx new_conseq = 
  match ctx with
    | Ctx(es) -> Ctx{es with es_orig_conseq = new_conseq}
    | OCtx(c1, c2) -> 
	      let update_c1 = update_ctx_es_orig_conseq c1 new_conseq in
	      let update_c2 = update_ctx_es_orig_conseq c2 new_conseq in
	      OCtx(update_c1, update_c2)

(* computes must-alias sets from equalities, maintains the invariant *)
(* that these sets form a partition. *)
(* and alias (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list = match ptr_eqs with *)
(*   | (v1, v2) :: rest -> begin *)
(* 	  let rest_sets = alias rest in *)
(* 	  let search (v : CP.spec_var) (asets : CP.spec_var list list) = List.partition (fun aset -> CP.mem v aset) asets in *)
(* 	  let av1, rest1 = search v1 rest_sets in *)
(* 	  let av2, rest2 = search v2 rest1 in *)
(* 	  let v1v2_set = CP.remove_dups_svl (List.concat ([v1; v2] :: (av1 @ av2))) in *)
(* 	  v1v2_set :: rest2 *)
(* 	end *)
(*   | [] -> [] *)


(* I <: M *)
(* return true if imm1 <: imm2 *)	
and subtype (imm1 : bool) (imm2 : bool) : bool = not(imm2) or imm1

  
(* utilities for handling lhs heap state continuation *)
and push_cont_ctx (cont : h_formula) (ctx : Cformula.context) : Cformula.context =
  match ctx with
    | Ctx(es) -> Ctx(push_cont_es cont es)
    | OCtx(c1, c2) ->
	      OCtx(push_cont_ctx cont c1, push_cont_ctx cont c2)

and push_cont_es (cont : h_formula) (es : entail_state) : entail_state =  
  {  es with
      es_cont = cont::es.es_cont;
  }

and pop_cont_es (es : entail_state) : (h_formula * entail_state) =  
  let cont = es.es_cont in
  let crt_cont, cont =
    match cont with
      | h::r -> (h, r)
      | [] -> (HTrue, [])
  in
  (crt_cont, 
  {  es with
      es_cont = cont;
  })

(* utilities for handling lhs holes *)
(* push *)
and push_crt_holes_list_ctx (ctx : list_context) (holes : (h_formula * int) list) : list_context = 
  let pr1 = Cprinter.string_of_list_context in
  let pr2 = pr_no (* pr_list (pr_pair string_of_h_formula string_of_int ) *) in
  Gen.Debug.no_2 "push_crt_holes_list_ctx" pr1 pr2 pr1 (fun _ _-> push_crt_holes_list_ctx_x ctx holes) ctx holes
      
and push_crt_holes_list_ctx_x (ctx : list_context) (holes : (h_formula * int) list) : list_context = 
  match ctx with
    | FailCtx _ -> ctx
    | SuccCtx(cl) ->
	      SuccCtx(List.map (fun x -> push_crt_holes_ctx x holes) cl)

and push_crt_holes_ctx (ctx : context) (holes : (h_formula * int) list) : context = 
  match ctx with
    | Ctx(es) -> Ctx(push_crt_holes_es es holes)
    | OCtx(c1, c2) ->
	      let nc1 = push_crt_holes_ctx c1 holes in
	      let nc2 = push_crt_holes_ctx c2 holes in
	      OCtx(nc1, nc2)

and push_crt_holes_es (es : Cformula.entail_state) (holes : (h_formula * int) list) : Cformula.entail_state =
  {
      es with
          es_crt_holes = holes @ es.es_crt_holes; 
  }
      
and push_holes (es : Cformula.entail_state) : Cformula.entail_state = 
  {  es with
      es_hole_stk   = es.es_crt_holes::es.es_hole_stk;
      es_crt_holes = [];
  }

(* pop *)

and pop_holes_es (es : Cformula.entail_state) : Cformula.entail_state = 
  match es.es_hole_stk with
    | [] -> es
    | c2::stk -> {  es with
		  es_hole_stk = stk;
	      es_crt_holes = es.es_crt_holes @ c2;
	  }

(* substitute *)
and subs_crt_holes_list_ctx (ctx : list_context) : list_context = 
  match ctx with
    | FailCtx _ -> ctx
    | SuccCtx(cl) ->
	      SuccCtx(List.map subs_crt_holes_ctx cl)

and subs_crt_holes_ctx (ctx : context) : context = 
  match ctx with
    | Ctx(es) -> Ctx(subs_holes_es es)
    | OCtx(c1, c2) ->
	      let nc1 = subs_crt_holes_ctx c1 in
	      let nc2 = subs_crt_holes_ctx c2 in
	      OCtx(nc1, nc2)

and subs_holes_es (es : Cformula.entail_state) : Cformula.entail_state = 
  (* subs away current hole list *)
  {  es with
	  es_crt_holes   = [];
      es_formula = apply_subs es.es_crt_holes es.es_formula;
  }

and apply_subs (crt_holes : (h_formula * int) list) (f : formula) : formula =
  match f with
    | Base(bf) ->
	      Base{bf with formula_base_heap = apply_subs_h_formula crt_holes bf.formula_base_heap;}
    | Exists(ef) ->
	      Exists{ef with formula_exists_heap = apply_subs_h_formula crt_holes ef.formula_exists_heap;}
    | Or({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) ->
	      let sf1 = apply_subs crt_holes f1 in
	      let sf2 = apply_subs crt_holes f2 in
	      mkOr sf1  sf2 pos

and apply_subs_h_formula crt_holes (h : h_formula) : h_formula = 
  let rec helper (i : int) crt_holes : h_formula = 
    (match crt_holes with
	  | (h1, i1) :: rest -> 
	        if i==i1 then h1
	        else helper i rest
	  | [] -> Hole(i))
  in
  match h with
    | Hole(i) -> helper i crt_holes
    | Star({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
	      let nh1 = apply_subs_h_formula crt_holes h1 in
	      let nh2 = apply_subs_h_formula crt_holes h2 in
	      Star({h_formula_star_h1 = nh1;
	      h_formula_star_h2 = nh2;
	      h_formula_star_pos = pos})
    | Conj({h_formula_conj_h1 = h1;
	  h_formula_conj_h2 = h2;
	  h_formula_conj_pos = pos}) ->
	      let nh1 = apply_subs_h_formula crt_holes h1 in
	      let nh2 = apply_subs_h_formula crt_holes h2 in
	      Conj({h_formula_conj_h1 = nh1;
	      h_formula_conj_h2 = nh2;
	      h_formula_conj_pos = pos})
    | Phase({h_formula_phase_rd = h1;
	  h_formula_phase_rw = h2;
	  h_formula_phase_pos = pos}) ->
	      let nh1 = apply_subs_h_formula crt_holes h1 in
	      let nh2 = apply_subs_h_formula crt_holes h2 in
	      Phase({h_formula_phase_rd = nh1;
	      h_formula_phase_rw = nh2;
	      h_formula_phase_pos = pos})
    | _ -> h

  (*if Gen.is_empty matches then NoMatch	(* can't find an aliased node, but p is mentioned in LHS *)
  else Match (matches)*)

type deprecated_find_node_result =
  | Deprecated_Failed (* p2 (of p2::c2<V2> coming from the RHS) is not in FV(LHS) *)
  | Deprecated_NoMatch (* p2 \in FV(LHS), but no aliased node is found *)
  | Deprecated_Match of match_res list (* found p1::c1<V1> such that p1=p2 *)
  
let rec pr_node_res (e:deprecated_find_node_result) =
  match e with
    | Deprecated_Failed -> fmt_string "Failed"
    | Deprecated_NoMatch -> fmt_string "NoMatch"
    | Deprecated_Match l -> pr_seq "Match" pr_match_res l
let string_of_node_res e = poly_string_of_pr pr_node_res e
  
let deprecated_find_node_one prog node lhs_h lhs_p rhs_v pos : deprecated_find_node_result =
  let node = match node with | ViewNode v -> ViewNode{v with h_formula_view_node = rhs_v} | _ -> report_error pos "deprecated_find_node_one error" in
  let matches = choose_context prog [] lhs_h lhs_p (MCP.mkMTrue no_pos) [] node HTrue pos in 
  if Gen.is_empty matches then Deprecated_NoMatch	(* can't find an aliased node, but p is mentioned in LHS *)
  else Deprecated_Match matches

      (* find a node from the left hand side *)
let deprecated_find_node prog node lhs_h (lhs_p : MCP.mix_formula) (ps : CP.spec_var list) pos : deprecated_find_node_result =
  let rec merge_results rs1 rs2 = match rs1 with
    | Deprecated_Failed -> rs2
    | Deprecated_NoMatch -> begin
        match rs2 with
	      | Deprecated_Failed -> rs1
	      | _ -> rs2
      end
    | Deprecated_Match l1 -> begin
        match rs2 with
	      | Deprecated_Failed -> rs1
	      | Deprecated_NoMatch -> rs1
	      | Deprecated_Match  l2 -> rs1 (*TODO: fix it Match (l1 @ l2) *)
      end in
  let tmp1 = List.map (fun p -> deprecated_find_node_one prog node lhs_h lhs_p p pos) ps in
  let tmp2 = List.fold_left merge_results Deprecated_Failed tmp1 in
  tmp2
