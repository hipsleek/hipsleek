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
  | Cond_action of action_wt list
  | Seq_action of action_wt list
  | Search_action of action_wt list (*the match_res indicates if pushing holes for each action is required or it will be done once, at the end*)
  | M_lhs_case of match_res
  (* | Un *)
  (* | M *)
  (* | Opt int *)

and action_wt = (int * action)  (* -1 : unknown, 0 : mandatory; >0 : optional (lower value has higher priority) *) 

let norm_search_action ls = match ls with
  | [] -> M_Nothing_to_do ("search action is empty")
  | [(_,a)] -> a
  | lst -> Search_action lst

let is_complex_action a = match a with
  | Search_action _ 
  | Cond_action _ 
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
  fmt_string "\n match_res_holes "; pr_seq "" (Cprinter.pr_pair_aux  pr_h_formula pr_int) c.match_res_holes;  
  fmt_string "\n match_res_type "; pr_match_type c.match_res_type;
  fmt_string "\n match_res_rhs_node "; pr_h_formula c.match_res_rhs_node;
  fmt_string "\n match_res_rhs_rest "; pr_h_formula c.match_res_rhs_rest;
  fmt_string "}"
  
let pr_simpl_match_res (c:match_res):unit = 
fmt_string "(";
  fmt_string "\n LHS "; pr_h_formula c.match_res_lhs_node;
  fmt_string "\n RHS "; pr_h_formula c.match_res_rhs_node;
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
  | Cond_action l -> fmt_string "COND:"; pr_seq "" (pr_action_wt_res pr_mr) l
  | Seq_action l -> fmt_string "SEQ:"; pr_seq "" (pr_action_wt_res pr_mr) l
  | Search_action l -> fmt_string "SEARCH:"; pr_seq "" (pr_action_wt_res pr_mr) l
  | M_lhs_case e -> pr_mr e; fmt_string "==> LSH case analysis"

and pr_action_wt_res pr_mr (w,a) = (pr_action_res pr_mr a);fmt_string ("(Weigh:"^(string_of_int w)^")")
let string_of_action_res_simpl (e:action) = poly_string_of_pr (pr_action_res pr_simpl_match_res) e
let string_of_action_res_simpl_0 (e:action) = poly_string_of_pr (pr_action_res (fun _ -> fmt_string " ")) e
let string_of_action_wt_res_simpl (e:action_wt) = poly_string_of_pr (pr_action_wt_res pr_simpl_match_res) e
let string_of_action_res e = poly_string_of_pr (pr_action_res pr_match_res) e
let string_of_action_wt_res e = poly_string_of_pr (pr_action_wt_res pr_match_res) e
let string_of_match_res e = poly_string_of_pr pr_match_res e  


type strat_constr =     
      {
       name : string;
       no_match : prog_decl -> h_formula -> h_formula-> h_formula -> action_wt;
       root_d_d : prog_decl -> match_res ->  h_formula_data ->  h_formula_data -> action_wt;
       root_d_v : prog_decl -> match_res ->  h_formula_data ->  h_formula_view -> action_wt;
       root_v_d : prog_decl -> match_res ->  h_formula_view ->  h_formula_data -> action_wt;
       root_v_v : prog_decl -> match_res ->  h_formula_view ->  h_formula_view -> action_wt;
       mater_d_d : prog_decl -> match_res -> mater_property -> mater_source ->  h_formula_data ->  h_formula_data -> action_wt;
       mater_d_v : prog_decl -> match_res -> mater_property -> mater_source ->  h_formula_data ->  h_formula_view -> action_wt;
       mater_v_d : prog_decl -> match_res -> mater_property -> mater_source ->  h_formula_view ->  h_formula_data -> action_wt;
       mater_v_v : prog_decl -> match_res -> mater_property -> mater_source ->  h_formula_view ->  h_formula_view -> action_wt;
     }
;;

module type STRATEG = sig val sc : strat_constr  end;;

module Default_strategy : STRATEG = 
   struct
    let sc = 
     {
         name = "default";
         root_d_d = (fun prog m dl dr ->
           if (String.compare dl.h_formula_data_name dr.h_formula_data_name)==0 then (0,M_match m)
                  else (0,M_Nothing_to_do ("no proper match (type error) found for: "^(string_of_match_res m))));

         root_v_v = (fun prog m vl vr ->
                  (* let l1 = [(1,M_base_case_unfold c)] in *)
                  let view_decls = prog.prog_view_decls in
                  let vl_name = vl.h_formula_view_name in
                  let vr_name = vr.h_formula_view_name in
                  let vl_vdef = look_up_view_def_raw view_decls vl_name in
                  let vr_vdef = look_up_view_def_raw view_decls vr_name in
                  let vl_is_rec = vl_vdef.view_is_rec in
                  let vr_is_rec = vr_vdef.view_is_rec in
                  let vl_self_pts = vl_vdef.view_pt_by_self in
                  let vr_self_pts = vr_vdef.view_pt_by_self in
                  let vl_view_orig = vl.h_formula_view_original in
                  let vr_view_orig = vr.h_formula_view_original in
                  let vl_view_derv =  vl.h_formula_view_derv in
                  let vr_view_derv = vr.h_formula_view_derv in
                  (* let vl_fold_num = vl_vdef.view_orig_fold_num in *)
                  (* let vr_fold_num = vr_vdef.view_orig_fold_num in *)
                  (*let en_num = !num_self_fold_search in*)
                  let en_self_fold = !self_fold_search_flag in
                  let l2 = 
                    let a1 = (1,M_base_case_unfold m) in
                    let a2 = (1,M_match m) in
                    let a3 = 
                      if (String.compare vl_name vr_name)==0 then Some (1,Cond_action [a1;a2])
                      else None in
                    let a4 = 
                      if not(vl_is_rec) then Some (2,M_unfold (m,0))
                      else if not(vr_is_rec) then Some (2,M_fold m) 
                      else None in
                    let a5 = 
                      if a4==None then
                        begin
                          let l1 =
                            if (vl_view_orig && vr_view_orig && en_self_fold && Gen.BList.mem_eq (=) vl_name vr_self_pts) 
                            then  [(2,M_fold m)] 
                            else [] in
                          let l2 =
                            if (vl_view_orig && vr_view_orig && en_self_fold && Gen.BList.mem_eq (=) vr_name vl_self_pts) 
                            then [(2,M_unfold (m,0))]
                            else [] in
                          let l = l1@l2 in
                          if l=[] then None
                          else Some (2,Cond_action l) 
                        end
                      else a4 in
                    let a6 = 
                      match a3 with 
                        | None -> a5
                        | Some a1 -> 
                              if not(a4==None) then a3
                              else 
                                match a5 with
                                  | None -> a3
                                  | Some a2 -> Some (1,Cond_action [a2; a1]) in
                    match a6 with
                      | Some a -> [a]
                      | None -> 
                            let lst=[(1,M_base_case_unfold m);(1,M_Nothing_to_do ("mis-matched LHS:"^(vl_name)^" and RHS: "^(vr_name)))] in
                            [(1,Cond_action lst)]
                  in
                  (* using || results in some repeated answers but still terminates *)
                  let flag = 
                    if !ann_derv 
                    then (not(vl_view_derv) && not(vr_view_derv)) 
                    else (vl_view_orig || vr_view_orig)
                  in
                  let l3 = if flag
                  then begin
                    let left_ls = look_up_coercion_with_target prog.prog_left_coercions vl_name vr_name in
                    let right_ls = look_up_coercion_with_target prog.prog_right_coercions vr_name vl_name in
                    let left_act = List.map (fun l -> (1,M_lemma (m,Some l))) left_ls in
                    let right_act = List.map (fun l -> (1,M_lemma (m,Some l))) right_ls in
                    if (left_act==[] && right_act==[]) then [] (* [(1,M_lemma (c,None))] *) (* only targetted lemma *)
                    else left_act@right_act
                  end
                  else  [] in
                  let l4 = 
                    (* TODO WN : what is original?? *)
                    if get_view_original m.match_res_rhs_node then 
                      [(2,M_base_case_fold m)] 
                    else [] in
                  let src = (-1,norm_search_action (l2@l3@l4)) in
                  src (*Seq_action [l1;src]*));
         root_d_v = (fun prog m dl vr ->
                  let vr_name = vr.h_formula_view_name in
                  let view_decls = prog.prog_view_decls in
                  let vr_vdef = look_up_view_def_raw view_decls vr_name in
                  let vr_self_pts = vr_vdef.view_pt_by_self in
                  let vr_view_orig = vr.h_formula_view_original in
                  if (vr_view_orig || vr_self_pts==[]) then (1,M_fold m)(*(-1,Search_action [(1,M_fold c);(1,M_rd_lemma c)]) *)
                  else (1,M_Nothing_to_do (" matched data with derived self-rec RHS node "^(string_of_match_res m))));
        root_v_d = (fun prog m vl dr ->
                  let vl_name = vl.h_formula_view_name in
                  let view_decls = prog.prog_view_decls in
                  let vl_vdef = look_up_view_def_raw view_decls vl_name in
                  let vl_self_pts = vl_vdef.view_pt_by_self in
                  let vl_view_orig = vl.h_formula_view_original in
                  let uf_i = if vl_view_orig then 0 else 1 in
                  let ua = (1, M_unfold (m,uf_i)) in
                  let left_ls = look_up_coercion_with_target prog.prog_left_coercions vl.h_formula_view_name dr.h_formula_data_name in
                  (* if (left_ls == [] && (vl_view_orig ) then ua *)
                  (* else (1,M_lemma (c,Some (List.hd left_ls))) *)
                  if (vl_view_orig || vl_self_pts==[]) then ua
                  else if (left_ls != []) then (1,M_lemma (m,Some (List.hd left_ls)))
                  else (1,M_Nothing_to_do ("matching data with deriv self-rec LHS node "^(string_of_match_res m))));
         mater_d_d = (fun prog m mv ms dl dr ->
             (1,M_Nothing_to_do ("matching lhs: "^(string_of_h_formula m.match_res_lhs_node)^" with rhs: "^(string_of_h_formula m.match_res_rhs_node))));
         mater_d_v = (fun prog m mv ms dl dr ->
             (1,M_Nothing_to_do ("matching lhs: "^(string_of_h_formula m.match_res_lhs_node)^" with rhs: "^(string_of_h_formula m.match_res_rhs_node))));
         mater_v_v = (fun prog m mv ms vl vr ->
                  let a1 = (match ms with
                    | View_mater -> 
                          let uf_i = if mv.mater_full_flag then 0 else 1 in
                          M_unfold (m,uf_i) (* uf_i to prevent infinite unfolding *)
                    | Coerc_mater s -> 
                          (* let _ = print_string "\n selected lemma XX" in *)
                          M_lemma (m,Some s)) in
                  let l1 = [(1,M_base_case_unfold m)] in
                  (-1, (Search_action ((1,a1)::l1))));
         mater_v_d = (fun prog m mv ms vl vr ->
                  let lhs_case_flag = vl.h_formula_view_lhs_case in
                  let a2 = 
                    (match ms with
                      | View_mater -> 
                          let uf_i = if mv.mater_full_flag then 0 else 1 in
                          (1,M_unfold (m,uf_i))
                      | Coerc_mater s -> (1,M_lemma (m,Some s))) in
                  let a1 = 
                    if (lhs_case_flag=true) then
                      let l1 = [(1,M_lhs_case m)] in
                      (-1, (Search_action (a2::l1)))
                    else
                      let l1 = [(1,M_base_case_unfold m)] in
                      (-1, (Search_action (a2::l1)))
                  in a1);
        no_match = (fun prog lhs_h rhs_node rhs_rest -> 
                  let r0 = (2,M_unmatched_rhs_data_node rhs_node) in
                  if (is_view rhs_node) && (get_view_original rhs_node) then
                    let r = (2, M_base_case_fold { 
                        match_res_lhs_node = HTrue; 
                        match_res_lhs_rest = lhs_h; 
                        match_res_holes = [];
                        match_res_type = Root;
                        match_res_rhs_node = rhs_node;
                        match_res_rhs_rest = rhs_rest;}) in (*(-1, Search_action [r])*)
                    let r1 = (2, M_fold {
                        match_res_lhs_node = HTrue; 
                        match_res_lhs_rest = lhs_h; 
                        match_res_holes = [];
                        match_res_type = Root;
                        match_res_rhs_node = rhs_node;
                        match_res_rhs_rest = rhs_rest;
                    }) in
                    (-1, (Cond_action [r;r1]))
                  else r0);
     }
end ;;


let c_strat = ref Default_strategy.sc ;;
let strateg_repo = ref (Hashtbl.create 10);;
Hashtbl.add !strateg_repo Default_strategy.sc.name Default_strategy.sc;;
let set_strateg s = 
  try
      c_strat := Hashtbl.find !strateg_repo s 
  with
    | Not_found -> failwith ("invalid strategy: "^s)
