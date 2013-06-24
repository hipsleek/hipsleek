open Globals
open Cformula
open Cast
open Cprinter
open Gen.Basic
open Immutable

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
  | M_split_match of match_res
  | M_fold of match_res
  | M_unfold  of (match_res * int) (* zero denotes no counting *)
  | M_base_case_unfold of match_res
  | M_base_case_fold of match_res
  | M_rd_lemma of match_res
  | M_lemma  of (match_res * (coercion_decl option))
  | Undefined_action of match_res
  | M_Nothing_to_do of string
  | M_infer_heap of (h_formula * h_formula) (* rhs * rhs_rest *)
  | M_unmatched_rhs_data_node of (h_formula * h_formula)
  (* perform a list of actions until there is one succeed*)
  | Cond_action of action_wt list
  (*not handle yet*) 
  | Seq_action of action_wt list 
  | Search_action of action_wt list (*the match_res indicates if pushing holes for each action is required or it will be done once, at the end*)
  | M_lhs_case of match_res
  (* | Un *)
  (* | M *)
  (* | Opt int *)

and action_wt = (int * action)  (* -1 : unknown, 0 : mandatory; >0 : optional (lower value has higher priority) *) 


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
    | Root -> 
          fmt_open_hbox (); 
          fmt_string "Root";
          fmt_close_box();
    | MaterializedArg (mv,ms) -> 
          fmt_open_hbox ();
          fmt_string "MaterializedArg "; 
          pr_mater_prop mv;
          fmt_space () ;
          pr_mater_source ms;
          fmt_close_box();
    | WArg -> fmt_string "WArg"


let pr_match_res (c:match_res):unit =
  fmt_open_vbox 1;
  pr_vwrap "Type: " pr_match_type c.match_res_type;
  pr_vwrap "LHS: " pr_h_formula c.match_res_lhs_node;
  pr_vwrap "RHS: " pr_h_formula c.match_res_rhs_node;
  fmt_string "\n lhs_rest: "; pr_h_formula c.match_res_lhs_rest;
  fmt_string "\n rhs_rest: "; pr_h_formula c.match_res_rhs_rest;
  (* fmt_string "\n res_holes: "; pr_seq "" (Cprinter.pr_pair_aux  pr_h_formula pr_int) c.match_res_holes;   *)
  (* fmt_string "}" *)
  fmt_close ()
  
let pr_simpl_match_res (c:match_res):unit = 
  fmt_open_vbox 1;
  pr_vwrap "LHS: " pr_h_formula c.match_res_lhs_node;
  pr_vwrap "RHS: " pr_h_formula c.match_res_rhs_node;
  fmt_close ()
(* fmt_string "("; *)
(*   fmt_string "\n LHS "; pr_h_formula c.match_res_lhs_node; *)
(*   fmt_string "\n RHS "; pr_h_formula c.match_res_rhs_node; *)
(*   fmt_string ")" *)

let rec pr_action_name a = match a with
  | Undefined_action e -> fmt_string "Undefined_action"
  | M_match e -> fmt_string "Match"
  | M_split_match e -> fmt_string "Split&Match "
  | M_fold e -> fmt_string "Fold"
  | M_unfold (e,i) -> fmt_string ("Unfold "^(string_of_int i))
  | M_base_case_unfold e -> fmt_string "BaseCaseUnfold"
  | M_base_case_fold e -> fmt_string "BaseCaseFold"
  | M_rd_lemma e -> fmt_string "RD_Lemma"
  | M_lemma (e,s) -> fmt_string (""^(match s with | None -> "AnyLemma" | Some c-> "Lemma "
        ^(string_of_coercion_type c.coercion_type)^" "^c.coercion_name))
  | M_Nothing_to_do s -> fmt_string ("NothingToDo"^s)
  | M_infer_heap p -> fmt_string ("InferHeap")
  | M_unmatched_rhs_data_node (h,_) -> fmt_string ("UnmatchedRHSData")
  | Cond_action l -> fmt_string "COND"
  | Seq_action l -> fmt_string "SEQ"
  | Search_action l -> fmt_string "SEARCH"
  | M_lhs_case e -> fmt_string "LHSCaseAnalysis"

let rec pr_action_res pr_mr a = match a with
  | Undefined_action e -> fmt_string "Undefined_action =>"; pr_mr e
  | M_match e -> fmt_string "Match =>"; pr_mr e
  | M_split_match e -> fmt_string "SplitMatch =>"; pr_mr e
  | M_fold e -> fmt_string "Fold =>"; pr_mr e
  | M_unfold (e,i) -> fmt_string ("Unfold "^(string_of_int i)^" =>"); pr_mr e
  | M_base_case_unfold e -> fmt_string "BaseCaseUnfold =>"; pr_mr e
  | M_base_case_fold e -> fmt_string "BaseCaseFold =>"; pr_mr e
  | M_rd_lemma e -> fmt_string "RD_Lemma =>"; pr_mr e
  | M_lemma (e,s) -> fmt_string ((match s with | None -> "AnyLemma" | Some c-> "Lemma "
        ^(string_of_coercion_type c.coercion_type)^" "^c.coercion_name)^" =>"); pr_mr e
  | M_Nothing_to_do s -> fmt_string ("NothingToDo => "^s)
  | M_infer_heap p -> let pr = string_of_h_formula in
    fmt_string ("InferHeap => "^(pr_pair pr pr p))
  | M_unmatched_rhs_data_node (h,_) -> fmt_string ("UnmatchedRHSData => "^(string_of_h_formula h))
  | Cond_action l -> pr_seq_nocut "COND =>" (pr_action_wt_res pr_mr) l
  | Seq_action l -> pr_seq_vbox "SEQ =>" (pr_action_wt_res pr_mr) l
  | Search_action l -> 
        fmt_open_vbox 1;
        pr_seq_vbox "SEARCH =>" (pr_action_wt_res pr_mr) l;
        fmt_close();
  | M_lhs_case e -> fmt_string "LHSCaseAnalysis =>"; pr_mr e

and pr_action_wt_res pr_mr (w,a) = 
  fmt_string ("Prio:"^(string_of_int w)); (pr_action_res pr_mr a)

let string_of_action_name (e:action) = poly_string_of_pr pr_action_name e

let string_of_action_res_simpl (e:action) = poly_string_of_pr (pr_action_res pr_simpl_match_res) e

let string_of_action_res_simpl_0 (e:action) = poly_string_of_pr (pr_action_res (fun _ -> fmt_string " ")) e

let string_of_action_wt_res_simpl (e:action_wt) = poly_string_of_pr (pr_action_wt_res pr_simpl_match_res) e

let string_of_action_res e = poly_string_of_pr (pr_action_res pr_match_res) e

let string_of_action_wt_res e = poly_string_of_pr (pr_action_wt_res pr_match_res) e

let string_of_action_wt_res0 e = poly_string_of_pr (pr_action_wt_res (fun _ -> fmt_string "")) e

let string_of_match_res e = poly_string_of_pr pr_match_res e  

let must_action_stk = new Gen.stack(* _noexc (M_Nothing_to_do "empty must_action_stk") string_of_action_res_simpl (=) *)
   
let action_get_holes a = match a with
  | Undefined_action e
  | M_match e
  | M_split_match e
  | M_lhs_case e
  | M_fold e
  | M_unfold (e,_)
  | M_rd_lemma e
  | M_lemma (e,_)
  | M_base_case_unfold e
  | M_base_case_fold e -> Some e.match_res_holes
  | Seq_action _
  | Cond_action _
  | M_Nothing_to_do _  
  | M_unmatched_rhs_data_node _
  | M_infer_heap _
  | Search_action _ ->None

 
let action_get_holes (a:action):(h_formula*int) list option = 
  let pr1 = string_of_action_res in
  let pr2 = pr_option (pr_list (pr_pair Cprinter.string_of_h_formula string_of_int)) in
  Debug.no_1 "action_get_holes" pr1 pr2 action_get_holes a

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
  Debug.no_1_num i "alias" pr1 pr2 alias_x ptr_eqs

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
 Debug.no_2 "get_aset" pr2  psv pr1 get_aset aset v

let comp_aliases_x (rhs_p:MCP.mix_formula) : (CP.spec_var) list list =
    let eqns = MCP.ptr_equations_without_null rhs_p in
    alias_nth 1 eqns 

let comp_aliases (rhs_p:MCP.mix_formula) : (CP.spec_var) list list =
 let psv = Cprinter.string_of_spec_var in
 let pr2 = (pr_list (pr_list psv)) in
 let pr1 = Cprinter.string_of_mix_formula in
 Debug.no_1 "comp_aliase" pr1 pr2 comp_aliases_x rhs_p

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
  match rhs_node with
    | DataNode _ 
    | ViewNode _ ->
          let imm,pimm,p= match rhs_node with
            | DataNode{h_formula_data_node=p;h_formula_data_imm=imm; h_formula_data_param_imm = pimm;} -> ( imm, pimm, p)
            | ViewNode{h_formula_view_node=p;h_formula_view_imm=imm} -> (imm, [], p)
            | _ -> report_error no_pos "choose_context unexpected rhs formula\n"
          in
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
          if Gen.is_empty paset then
            failwith ("choose_context: Error in getting aliases for " ^ (string_of_spec_var p))
          else if (* not(CP.mem p lhs_fv) ||  *)(!Globals.enable_syn_base_case && (CP.mem CP.null_var paset)) then
            (Debug.devel_zprint (lazy ("choose_context: " ^ (string_of_spec_var p) ^ " is not mentioned in lhs\n\n")) pos; [] )
          else (spatial_ctx_extract prog lhs_h paset imm pimm rhs_node rhs_rest) 
    | HTrue -> (
          if (rhs_rest = HEmp) then (
              (* if entire RHS is HTrue then it matches with the entire LHS*)
              let mres = { match_res_lhs_node = lhs_h;
              match_res_lhs_rest = HEmp;
              match_res_holes = [];
              match_res_type = Root;
              match_res_rhs_node = HTrue;
              match_res_rhs_rest = HEmp; } in
              [mres]
          )
          else []
      )
    | HRel _ -> []
    | _ -> report_error no_pos "choose_context unexpected rhs formula\n"

and choose_context prog es lhs_h lhs_p rhs_p posib_r_aliases rhs_node rhs_rest pos :  match_res list =
  let psv =  Cprinter.string_of_spec_var in
  let pr0 = pr_list (pr_pair psv psv) in
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 l = pr_list string_of_match_res l in
  let pr3 = Cprinter.string_of_mix_formula in
  (*let pr4 = pr_list Cprinter.string_of_spec_var in*)
  (*let pr2 (m,svl,_) = (Cprinter.string_of_spec_var_list svl) ^ ";"^ (Cprinter.string_of_mix_formula m) in*)
  Debug.no_5 "choose_context" 
      (add_str "LHS node" pr1) 
      (add_str "RHS node" pr1) 
      (add_str "LHS pure" pr3) 
      (add_str "RHS pure" pr3)
      (add_str "right aliase" pr0)
      pr2 
      (fun _ _ _ _ _ -> choose_context_x prog es lhs_h lhs_p rhs_p posib_r_aliases rhs_node rhs_rest pos) lhs_h rhs_node lhs_p rhs_p es

(* type: Cast.prog_decl ->
   Globals.ident ->
   Cast.P.spec_var list ->
   Cformula.CP.spec_var list ->
   bool ->
   Cformula.h_formula *)

and view_mater_match prog c vs1 aset imm f =
  let pr1 = (fun x -> x) in
  let pr2 = !print_svl in
  Debug.no_3 "view_mater_match" pr1 pr2 pr2 pr_no (fun _ _ _ -> view_mater_match_x prog c vs1 aset imm f) c vs1 aset

and view_mater_match_x prog c vs1 aset imm f =
  let vdef = look_up_view_def_raw prog.prog_view_decls c in
  let vdef_param = (self_param vdef)::(vdef.view_vars) in
  let mvs = subst_mater_list_nth 1 vdef_param vs1 vdef.view_materialized_vars in
  (* let vars =  vdef.view_vars in *)
  (* let _ = print_string ("\n\nview_mater_match: vars = " ^ (Cprinter.string_of_spec_var_list vars)^ " \n\n") in  *)
  try
    let mv = List.find (fun v -> List.exists (CP.eq_spec_var v.mater_var) aset) mvs in
    if  (produces_hole imm) && not(!Globals.allow_field_ann) then
      let hole_no = Globals.fresh_int() in
      [(Hole hole_no, f, [(f, hole_no)], MaterializedArg (mv,View_mater))]
    else [(HTrue, f, [], MaterializedArg (mv,View_mater))]
  with 
      _ ->  
          if List.exists (CP.eq_spec_var CP.null_var) aset then [] 
          else
            if List.exists (fun v -> CP.mem v aset) vs1 then
              if (produces_hole imm) && not(!Globals.allow_field_ann) then
                let hole_no = Globals.fresh_int() in 
                [(Hole hole_no, f, [(f, hole_no)], WArg)]
              else [(HEmp, f, [], WArg)]
            else []

(* and view_mater_match prog c vs1 aset imm f = *)
(*   let pr = fun v-> string_of_int (List.length v) in *)
(*   let psv = Cprinter.string_of_spec_var in *)
(*   let pr1 = pr_list psv in *)
(*   let pr2 = pr_list  psv in   *)
(*   Debug.no_2 "view_mater_match" pr1 pr2 pr (fun _ _ -> view_mater_match_x prog c vs1 aset imm f) vs1 aset *)
              
and choose_full_mater_coercion_x l_vname l_vargs r_aset (c:coercion_decl) =
  (* if not(c.coercion_simple_lhs && c.coercion_head_view = l_vname) then None *)
  if not((c.coercion_case=Cast.Simple || c.coercion_case= (Normalize false)) && c.coercion_head_view = l_vname) then None
  else 
    let args = List.tl (fv_simple_formula_coerc c.coercion_head) in (* dropping the self parameter and fracvar *)
    (* let args = List.tl (fv_simple_formula c.coercion_head) in (\* dropping the self parameter *\) *)
    (* let _ = print_string ( "choose_full_mater_coercion_x:" *)
    (*                        ^"\n ###args = " ^ (Cprinter.string_of_spec_var_list args) *)
    (*                        ^"\n ###l_vargs = " ^ (Cprinter.string_of_spec_var_list l_vargs) *)
    (*                        ^"\n ###c.coercion_mater_vars = " ^ (Cprinter.string_of_mater_prop_list c.coercion_mater_vars) *)
    (*                       ^ "\n") in *)
    let lmv = subst_mater_list_nth 2 args l_vargs c.coercion_mater_vars in
    try
      let mv = List.find (fun v -> List.exists (CP.eq_spec_var v.mater_var) r_aset) lmv in
      Some (c,mv)
    with  _ ->  None

and choose_full_mater_coercion l_vname l_vargs r_aset (c:coercion_decl) =
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr (c,_) = string_of_coercion c in
  Debug.no_1 "choose_full_mater_coercion" pr_svl (pr_option pr) (fun _ -> choose_full_mater_coercion_x l_vname l_vargs r_aset c) r_aset

and coerc_mater_match_x prog l_vname (l_vargs:P.spec_var list) r_aset (imm : ann) (lhs_f:Cformula.h_formula) =
  (* TODO : how about right coercion, Cristina? *)
  let coercs = prog.prog_left_coercions in
  (* let _ = print_string ("coerc_mater_match_x:" *)
  (*                       ^"\n l_vname = " ^ (Cprinter.string_of_ident l_vname) *)
  (*                       ^"\n  l_vargs = " ^ (Cprinter.string_of_spec_var_list l_vargs) *)
  (*                       ^"\n  r_aset = " ^ (Cprinter.string_of_spec_var_list r_aset) *)
  (*                       ^ "\n coercs = " ^ (if (coercs!=[]) then Cprinter.string_of_coercion (List.hd coercs) else "") *)
  (*                       ^ "\n") in *)
  let pos_coercs = List.fold_right (fun c a -> match (choose_full_mater_coercion l_vname l_vargs r_aset c) with 
    | None ->  a 
    | Some t -> t::a) coercs [] in
  let res = List.map (fun (c,mv) -> (HEmp, lhs_f, [], MaterializedArg (mv,Coerc_mater c))) pos_coercs in
  (* let pos_coercs = List.fold_left  *)
  (*   (fun a c->  *)
  (*       let args = List.tl (fv_simple_formula c.coercion_head) in  *)
  (*       let lmv = subst_mater_list_nth 3 args l_vargs c.coercion_mater_vars in *)
  (*       try *)
  (*         let mv = List.find (fun v -> List.exists (CP.eq_spec_var v.mater_var) r_aset) lmv in *)
  (*         (HTrue, lhs_f, [], MaterializedArg (mv,Coerc_mater c.coercion_name))::a *)
  (*       with  _ ->  a) [] pos_coercs in *)
  if produces_hole imm then [] else res

and coerc_mater_match prog l_vname (l_vargs:P.spec_var list) r_aset imm (lhs_f:Cformula.h_formula) =
  let pr = Cprinter.string_of_h_formula in
  let pr4 (h1,h2,l,mt) = pr_pair pr pr (h1,h2) in
  let pr2 ls = pr_list pr4 ls in
  let pr_svl = Cprinter.string_of_spec_var_list in
  Debug.no_3 "coerc_mater_match" pr_id pr_svl pr_svl pr2
      (fun _ _ _ -> coerc_mater_match_x prog l_vname (l_vargs:P.spec_var list) r_aset imm (lhs_f:Cformula.h_formula)) l_vname l_vargs r_aset
      
(*
  spatial context
  type: Cast.prog_decl ->
  Cformula.h_formula ->
  Cformula.CP.spec_var list ->
  bool -> Cformula.h_formula -> Cformula.h_formula -> match_res list
  f - left heap/node
  a - alias of right node
  rn - right node
  rr - right rest
*)
and spatial_ctx_extract p f a i pi rn rr = 
  let pr = pr_list string_of_match_res in
  let pr_svl = Cprinter.string_of_spec_var_list in
  (*let pr_aset = pr_list (pr_list Cprinter.string_of_spec_var) in*)
  (* let pr = pr_no in *)
  Debug.no_4 "spatial_context_extract " string_of_h_formula Cprinter.string_of_imm pr_svl string_of_h_formula pr 
      (fun _ _ _ _-> spatial_ctx_extract_x p f a i pi rn rr ) f i a rn 

and update_ann (f : h_formula) (pimm1 : ann list) (pimm : ann list) : h_formula = 
  let pr lst = "[" ^ (List.fold_left (fun y x-> (Cprinter.string_of_imm x) ^ ", " ^ y) "" lst) ^ "]; " in
  Debug.no_3 "update_ann" (Cprinter.string_of_h_formula) pr pr  (Cprinter.string_of_h_formula) (fun _ _ _-> update_ann_x f pimm1 pimm) f pimm1 pimm

and update_ann_x (f : h_formula) (pimm1 : ann list) (pimm : ann list) : h_formula = 
  let new_field_ann_lnode = Immutable.replace_list_ann pimm1 pimm in
  (* asankhs: If node has all field annotations as @A make it HEmp *)
  if (isAccsList new_field_ann_lnode) then HEmp else
    let updated_f = match f with 
      | DataNode d -> DataNode ( {d with h_formula_data_param_imm = new_field_ann_lnode} )
      | _          -> report_error no_pos ("[context.ml] : only data node should allow field annotations \n")
    in
    updated_f


and imm_split_lhs_node estate l_node r_node =
  {estate with es_formula = imm_f_split_lhs_node estate.es_formula l_node r_node}

and imm_f_split_lhs_node f l_node r_node = match l_node, r_node with
  | DataNode dl, DataNode dr ->
	if (!Globals.allow_field_ann) then 
	  let n_f = update_ann l_node dl.h_formula_data_param_imm dr.h_formula_data_param_imm in
	  mkStar (formula_of_heap n_f no_pos) f Flow_combine no_pos
        else f
  | _ -> f 
        
and spatial_ctx_extract_x prog (f0 : h_formula) (aset : CP.spec_var list) (imm : ann) (pimm : ann list) rhs_node rhs_rest : match_res list  =
  let rec helper f = match f with
    | HTrue -> []
    | HFalse -> []
    | HEmp -> []
    | HRel _ -> []
    | Hole _ -> []
    | DataNode ({h_formula_data_node = p1; 
      h_formula_data_imm = imm1;
      h_formula_data_param_imm = pimm1}) ->
	  (* imm1 = imm annotation on the LHS
	     imm = imm annotation on the RHS *) 
	  (* let subtyp = subtype_ann imm1 imm in *)
          if ((CP.mem p1 aset) (* && (subtyp) *)) then 
	    (* let field_ann = false in *)
	    
            if ( (not !Globals.allow_field_ann) && produces_hole imm) then (* not consuming the node *)
	      let hole_no = Globals.fresh_int() in 
	      [((Hole hole_no), f, [(f, hole_no)], Root)]
            else
              (*if (!Globals.allow_field_ann) then
                let new_f = update_ann f pimm1 pimm in
              (* let _ = print_string ("\n(andreeac) spatial_ctx_extarct helper initial f: " ^ (Cprinter.string_of_h_formula f)) in *)
              (* let _ = print_string ("\n(andreeac) spatial_ctx_extarct helper new f: " ^ (Cprinter.string_of_h_formula new_f)) in *)
	        [(new_f,f,[],Root)]
	        else*)
              [(HEmp, f, [], Root)]
          else []
    | ViewNode ({h_formula_view_node = p1;
      h_formula_view_imm = imm1;
      h_formula_view_perm = perm1;
      h_formula_view_arguments = vs1;
      h_formula_view_name = c}) ->
          (* if (subtype_ann imm1 imm) then *)
          (if (CP.mem p1 aset) then
            (* let _ = print_string("found match for LHS = " ^ (Cprinter.string_of_h_formula f) ^ "\n") in *)
            if produces_hole imm (*&& not(!Globals.allow_field_ann)*) then
	      (* let _ = print_string("imm = Lend " ^ "\n") in *)
              let hole_no = Globals.fresh_int() in
              (*[(Hole hole_no, matched_node, hole_no, f, Root, HTrue, [])]*)
              [(Hole hole_no, f, [(f, hole_no)], Root)]
            else
              [(HEmp, f, [], Root)]
          else
            let vmm = view_mater_match prog c (p1::vs1) aset imm f in
            let cmm = coerc_mater_match prog c vs1 aset imm f in 
            (*LDK: currently, assume that frac perm does not effect 
              the choice of lemmas (coercions)*)
            vmm@cmm
          )
              (* else [] *)
    | Star ({h_formula_star_h1 = f1;
      h_formula_star_h2 = f2;
      h_formula_star_pos = pos}) ->
          let l1 = helper f1 in
          let res1 = List.map (fun (lhs1, node1, hole1, match1) -> (mkStarH lhs1 f2 pos, node1, hole1, match1)) l1 in  
          let l2 = helper f2 in
          let res2 = List.map (fun (lhs2, node2, hole2, match2) -> (mkStarH f1 lhs2 pos, node2, hole2, match2)) l2 in
	  (* let _ = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x f:"  ^ (Cprinter.string_of_h_formula f)) in *)
	  (* let helper0 lst = List.fold_left (fun res (a,_,_,_) -> res ^ (Cprinter.string_of_h_formula a) ) "" lst in *)
	  (* let _ = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x res1:"  ^ helper0 res1) in *)
	  (* let _ = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x res2:"  ^ helper0 res2) in  *)
          res1 @ res2
    | StarMinus ({h_formula_starminus_h1 = f1;
      h_formula_starminus_h2 = f2;
      h_formula_starminus_pos = pos}) ->
          let l1 = helper f1 in
          let res1 = List.map (fun (lhs1, node1, hole1, match1) -> (mkStarMinusH lhs1 f2 pos 12 , node1, hole1, match1)) l1 in  
          let l2 = helper f2 in
          let res2 = List.map (fun (lhs2, node2, hole2, match2) -> (mkStarMinusH f1 lhs2 pos 13, node2, hole2, match2)) l2 in
	  (* let _ = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x f:"  ^ (Cprinter.string_of_h_formula f)) in *)
	  (* let helper0 lst = List.fold_left (fun res (a,_,_,_) -> res ^ (Cprinter.string_of_h_formula a) ) "" lst in *)
	  (* let _ = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x res1:"  ^ helper0 res1) in *)
	  (* let _ = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x res2:"  ^ helper0 res2) in  *)
          res1 @ res2          
    | Conj({h_formula_conj_h1 = f1;
      h_formula_conj_h2 = f2;
      h_formula_conj_pos = pos}) ->  if (!Globals.allow_mem) then 
        let l1 = helper f1 in
        let res1 = List.map (fun (lhs1, node1, hole1, match1) -> 
            if not (is_empty_heap node1) && (is_empty_heap rhs_rest) then 
              let ramify_f2 = mkStarMinusH f2 node1 pos 37 in
              (mkConjH lhs1 ramify_f2 pos , node1, hole1, match1)
            else (mkConjH lhs1 f2 pos , node1, hole1, match1)) l1 in  
        let l2 = helper f2 in
        let res2 = List.map (fun (lhs2, node2, hole2, match2) -> 
            if not (is_empty_heap node2) && (is_empty_heap rhs_rest) then 
              let ramify_f1 = mkStarMinusH f1 node2 pos 38 in
              (mkConjH ramify_f1 lhs2 pos , node2, hole2, match2)
            else
              (mkConjH f1 lhs2 pos , node2, hole2, match2)) l2 in
        (*let helper0 lst = List.fold_left (fun res (a,_,_,_) -> res ^ (Cprinter.string_of_h_formula a) ) "" lst in 
      	  let _ = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x res1:"  ^ helper0 res1) in
	  let _ = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x res2:"  ^ helper0 res2) in *)
        res1 @ res2
      else 
	let _ = print_string("[context.ml]: Conjunction in lhs, use mem specifications. lhs = " ^ (string_of_h_formula f) ^ "\n") in
        failwith("[context.ml]: There should be no conj/phase in the lhs at this level\n")
            
    | ConjStar({h_formula_conjstar_h1 = f1;
      h_formula_conjstar_h2 = f2;
      h_formula_conjstar_pos = pos}) ->  if (!Globals.allow_mem) then 
        let l1 = helper f1 in
        let res1 = List.map (fun (lhs1, node1, hole1, match1) -> (mkConjStarH lhs1 f2 pos , node1, hole1, match1)) l1 in  
        let l2 = helper f2 in
        let res2 = List.map (fun (lhs2, node2, hole2, match2) -> (mkConjStarH f1 lhs2 pos , node2, hole2, match2)) l2 in
        res1 @ res2
      else 
	let _ = print_string("[context.ml]: Conjunction in lhs, use mem specifications. lhs = " ^ (string_of_h_formula f) ^ "\n") in
        failwith("[context.ml]: There should be no conj/phase in the lhs at this level\n")
            
    | ConjConj({h_formula_conjconj_h1 = f1;
      h_formula_conjconj_h2 = f2;
      h_formula_conjconj_pos = pos}) ->  if (!Globals.allow_mem) then 
        let l1 = helper f1 in
        let res1 = List.map (fun (lhs1, node1, hole1, match1) -> (mkConjConjH lhs1 f2 pos , node1, hole1, match1)) l1 in  
        let l2 = helper f2 in
        let res2 = List.map (fun (lhs2, node2, hole2, match2) -> (mkConjConjH f1 lhs2 pos , node2, hole2, match2)) l2 in
        res1 @ res2
      else 
	let _ = print_string("[context.ml]: Conjunction in lhs, use mem specifications. lhs = " ^ (string_of_h_formula f) ^ "\n") in
        failwith("[context.ml]: There should be no conj/phase in the lhs at this level\n")          	          					
    | _ -> 
          let _ = print_string("[context.ml]: There should be no conj/phase in the lhs at this level; lhs = " ^ (string_of_h_formula f) ^ "\n") in
          failwith("[context.ml]: There should be no conj/phase in the lhs at this level\n")
  in
  let l = helper f0 in
  List.map (fun (lhs_rest,lhs_node,holes,mt) ->
      (* let _ = print_string ("\n(andreeac) lhs_rest spatial_ctx_extract " ^ (Cprinter.string_of_h_formula lhs_rest) ^ "\n(andreeac) f0: " ^ (Cprinter.string_of_h_formula f0)) in *)
      { match_res_lhs_node = lhs_node;
      match_res_lhs_rest = lhs_rest;
      match_res_holes = holes;
      match_res_type = mt;
      match_res_rhs_node = rhs_node;
      match_res_rhs_rest = rhs_rest;}) l

(*
  In the presence of permissions,
  LOOKING for actions on SPLIT/COMBINE lemmas to apply 
  because exact MATCH may fail*)
and lookup_lemma_action prog (c:match_res) :action =
  Debug.no_1 "lookup_lemma_action"
      string_of_match_res string_of_action_res
      (lookup_lemma_action_x prog) c

and lookup_lemma_action_x prog (c:match_res) :action =
  let rhs_node = c.match_res_rhs_node in
  let lhs_node = c.match_res_lhs_node in
  let view_decls = prog.prog_view_decls in
  let i,act = match c.match_res_type with 
      (*no need to prioritize => discount i, only return act*)
    | Root ->
          (match lhs_node,rhs_node with
            | DataNode dl, DataNode dr ->
                  (*              let dl_data_orig = dl.h_formula_data_original in
                                  let dr_data_orig = dr.h_formula_data_original in
                                  let dl_data_derv = dl.h_formula_data_derv in
                                  let dr_data_derv = dr.h_formula_data_derv in
                                  let flag = 
                                  if !ann_derv 
                                  then (not(dl_data_derv) && not(dr_data_derv)) 
                                  else (dl_data_orig || dr_data_orig)
                                  in*)
                  (*expecting ((String.compare dl.h_formula_data_name dr.h_formula_data_name)==0) == true*)
                  let l = 
                    let left_ls = look_up_coercion_with_target (List.filter (fun c -> c.coercion_case = (Cast.Normalize false)) prog.prog_left_coercions) dl.h_formula_data_name dr.h_formula_data_name in
                    let right_ls = look_up_coercion_with_target (List.filter (fun c -> c.coercion_case = (Cast.Normalize true)) prog.prog_right_coercions) dr.h_formula_data_name dl.h_formula_data_name in
                    let left_act = List.map (fun l -> (1,M_lemma (c,Some l))) left_ls in
                    let right_act = List.map (fun l -> (1,M_lemma (c,Some l))) right_ls in
                    left_act@right_act
                  in
                  if l=[] then (1,M_Nothing_to_do (string_of_match_res c))
                  else (-1,Search_action l)
            | ViewNode vl, ViewNode vr ->
                  let vl_name = vl.h_formula_view_name in
                  let vr_name = vr.h_formula_view_name in
                  let vl_vdef = look_up_view_def_raw view_decls vl_name in
                  let vr_vdef = look_up_view_def_raw view_decls vr_name in
                  let vl_view_orig = vl.h_formula_view_original in
                  let vr_view_orig = vr.h_formula_view_original in
                  let vl_view_derv =  vl.h_formula_view_derv in
                  let vr_view_derv = vr.h_formula_view_derv in
                  (*Are they in LOCKED state*)
                  let is_l_lock = match vl_vdef.view_inv_lock with
                    | Some _ -> true
                    | None -> false
                  in
                  let is_r_lock = match vr_vdef.view_inv_lock with
                    | Some _ -> true
                    | None -> false
                  in
                  let flag = 
                    if !ann_derv 
                    then (not(vl_view_derv) && not(vr_view_derv)) 
                      (* else (vl_view_orig || vr_view_orig) *)
                    else
                      (*only apply a SPLIT lemma to a lock
                        if both sides are original*)
                      (* if (is_l_lock) then *)
                      (*   (vl_view_orig && vr_view_orig) *)
                      (*if RHS is original --> SPLIT*)
                      if (is_l_lock && is_r_lock && vr_view_orig) then
                        true
                      else if (is_l_lock && is_r_lock && not vr_view_orig) then
                        false
                      else
                        (vl_view_orig || vr_view_orig)
                  in
                  let vl_new_orig = if !ann_derv then not(vl_view_derv) else vl_view_orig in
                  let vr_new_orig = if !ann_derv then not(vr_view_derv) else vr_view_orig in
                  let l = if flag
                  then begin
                    (*expecting ((String.compare vl.h_formula_view_name vr.h_formula_view_name)==0)*)
                    let left_ls = look_up_coercion_with_target (List.filter (fun c -> c.coercion_case = (Cast.Normalize false)) prog.prog_left_coercions) vl_name vr_name in
                    let right_ls = look_up_coercion_with_target (List.filter (fun c -> c.coercion_case = (Cast.Normalize true)) prog.prog_right_coercions) vr_name vl_name in
                    let left_act = if (not(!ann_derv) || vl_new_orig) then List.map (fun l -> (1,M_lemma (c,Some l))) left_ls else [] in
                    let right_act = if (not(!ann_derv) || vr_new_orig) then List.map (fun l -> (1,M_lemma (c,Some l))) right_ls else [] in
                    left_act@right_act
                  end
                  else  [] in
                  if l=[] then (1,M_Nothing_to_do (string_of_match_res c))
                  else (-1,Search_action l)
            | DataNode dl, ViewNode vr -> (1,M_Nothing_to_do (string_of_match_res c))
            | ViewNode vl, DataNode dr -> (1,M_Nothing_to_do (string_of_match_res c))
            | _ -> report_error no_pos "process_one_match unexpected formulas\n"	              )
    | MaterializedArg (mv,ms) -> 
          (*unexpected*)
          (1,M_Nothing_to_do (string_of_match_res c))
    | WArg -> (1,M_Nothing_to_do (string_of_match_res c))
  in
  act

and process_one_match prog is_normalizing (c:match_res) :action_wt =
  let pr1 = string_of_match_res in
  let pr2 = string_of_action_wt_res0  in
  Debug.no_1 "process_one_match" pr1 pr2 (process_one_match_x prog is_normalizing) c 

(*
(* return a list of nodes from heap f that appears in *)
(* alias set aset. The flag associated with each node *)
(* lets us know if the match is at the root pointer,  *)
(* or at materialized args,...                        *)
*)
and norm_search_action ls = match ls with
  | [] -> M_Nothing_to_do ("search action is empty")
  | [(_,a)] -> a
  | lst -> Search_action lst

and process_one_match_x prog is_normalizing (c:match_res) :action_wt =
  let rhs_node = c.match_res_rhs_node in
  let lhs_node = c.match_res_lhs_node in
  let filter_norm_lemmas l = 
    List.filter (fun c-> match c.coercion_case with 
      | Normalize b-> if b || !use_split_match then false else true 
      | _ -> true) l in
  let r = match c.match_res_type with 
    | Root ->
          let view_decls = prog.prog_view_decls in
          (match lhs_node,rhs_node with
            | DataNode dl, DataNode dr -> 
		  (**TO CHECK: follow view nodes *)
                  let dl_data_orig = dl.h_formula_data_original in
                  let dr_data_orig = dr.h_formula_data_original in
                  let dl_data_derv = dl.h_formula_data_derv in
                  let dr_data_derv = dr.h_formula_data_derv in
                  let dl_flag, dr_flag = 
                    if !ann_derv then
                      (not(dl_data_derv)),(not(dr_data_derv))
                    else
                      dl_data_orig,dr_data_orig
                  in
                  let l2 =
                    if ((String.compare dl.h_formula_data_name dr.h_formula_data_name)==0 && 
                        ((dl_flag==false && (dl.h_formula_data_origins!=[])) 
                        || ((dr_flag==false && dr.h_formula_data_origins!=[])))) then [(0,M_match c)] (*force a MATCH after each lemma*)
                    else 
                      if (String.compare dl.h_formula_data_name dr.h_formula_data_name)==0 then [(1,M_match c)]
                      else [(1,M_Nothing_to_do ("no proper match (type error) found for: "^(string_of_match_res c)))]
                  in
		  let l2 = if !perm=Dperm && !use_split_match && not !consume_all then (1,M_split_match c)::l2 else l2 in
                  (*apply lemmas on data nodes*)
                  (* using || results in some repeated answers but still terminates *)
                  (*let dl_new_orig = if !ann_derv then not(dl_data_derv) else dl_data_orig in*)
                  let flag = 
                    if !ann_derv 
                    then (not(dl_data_derv) && not(dr_data_derv)) 
                    else (dl_data_orig || dr_data_orig)
                  in
                  let l3 = if flag
                  then 
                    begin
                      let left_ls = filter_norm_lemmas(look_up_coercion_with_target prog.prog_left_coercions dl.h_formula_data_name dr.h_formula_data_name) in
                      let right_ls = filter_norm_lemmas(look_up_coercion_with_target prog.prog_right_coercions dr.h_formula_data_name dl.h_formula_data_name) in
                      let left_act = List.map (fun l -> (1,M_lemma (c,Some l))) left_ls in
                      let right_act = List.map (fun l -> (1,M_lemma (c,Some l))) right_ls in
                      if (left_act==[] && right_act==[]) then [] (* [(1,M_lemma (c,None))] *) (* only targetted lemma *)
                      else left_act@right_act
                    end
                  else [] in
                  let src = (-1,Search_action (l2@l3)) in
                  src
            | ViewNode vl, ViewNode vr -> 
                  (* let l1 = [(1,M_base_case_unfold c)] in *)
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
                  let vl_view_origs = vl.h_formula_view_origins in
                  let vr_view_origs = vr.h_formula_view_origins in
                  let vl_view_derv =  vl.h_formula_view_derv in
                  let vr_view_derv = vr.h_formula_view_derv in
                  (*Are they in LOCKED state*)
                  let is_l_lock = match vl_vdef.view_inv_lock with
                    | Some _ -> true
                    | None -> false
                  in
                  let is_r_lock = match vr_vdef.view_inv_lock with
                    | Some _ -> true
                    | None -> false
                  in
                  (* let vl_fold_num = vl_vdef.view_orig_fold_num in *)
                  (* let vr_fold_num = vr_vdef.view_orig_fold_num in *)
                  (*let en_num = !num_self_fold_search in*)
                  let en_self_fold = !self_fold_search_flag in
                  let l2 = 
                    if ((String.compare vl_name vr_name)==0 && 
                        ((vl_view_orig==false && (vl_view_origs!=[])) 
                        || ((vr_view_orig==false && vr_view_origs!=[])))) then 
                      [(0,M_match c)] (*force a MATCH after each lemma*)
                    else
                      let a1 = (1,M_base_case_unfold c) in
		      let a2 = (1,M_match c) in
                      let a2 = if !perm=Dperm && !use_split_match && not !consume_all then (1,Search_action [a2;(1,M_split_match c)]) else a2 in
                      let a3 =
                        (*Do not fold/unfold LOCKs, only match*)
                        if (is_l_lock || is_r_lock) then Some a2 else 
                          if (String.compare vl_name vr_name)==0 then Some (1,Cond_action [a1;a2])
                          else None in
                      let a4 = 
                        (*Do not fold/unfold LOCKs*)
                        if (is_l_lock || is_r_lock) then None else 
                          if not(vl_is_rec) then Some (2,M_unfold (c,0))
                          else if not(vr_is_rec) then Some (2,M_fold c) 
                          else None in
                      let a5 = 
                        if a4==None then
                          begin
                            let l1 =
                              (*Do not fold/unfold LOCKs*)
                              if (is_l_lock) then [] else 
                                if (vl_view_orig && vr_view_orig && en_self_fold && Gen.BList.mem_eq (=) vl_name vr_self_pts) 
                                then  [(2,M_fold c)] 
                                else [] in
                            let l2 =
                              (*Do not fold/unfold LOCKs*)
                              if (is_r_lock) then [] else
                                if (vl_view_orig && vr_view_orig && en_self_fold && Gen.BList.mem_eq (=) vr_name vl_self_pts) 
                                then [(2,M_unfold (c,0))]
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
                              (* TO CHECK : MUST ensure not fold/unfold LOCKs*)
                              let lst=[(1,M_base_case_unfold c);(1,M_Nothing_to_do ("mis-matched LHS:"^(vl_name)^" and RHS: "^(vr_name)))] in
                              (*let lst = [(1,M_base_case_unfold c);(1,M_unmatched_rhs_data_node (rhs_node,c.match_res_rhs_rest))] in*)
                              [(1,Cond_action lst)]
                  in
                  (* using || results in some repeated answers but still terminates *)
                  let vl_new_orig = if !ann_derv then not(vl_view_derv) else vl_view_orig in
                  let vr_new_orig = if !ann_derv then not(vr_view_derv) else vr_view_orig in
                  let flag = 
                    if !ann_derv 
                    then (not(vl_view_derv) && not(vr_view_derv)) 
                      (* else (vl_view_orig || vr_view_orig) *)
                    else
                      (*only apply a SPLIT lemma to a lock
                        if both sides are original*)
                      (* if (is_l_lock) then *)
                      (*   (vl_view_orig && vr_view_orig) *)
                      (*if RHS is original --> SPLIT*)
                      if (is_l_lock && is_r_lock && vr_view_orig) then
                        true
                      else if (is_l_lock && is_r_lock && not vr_view_orig) then
                        false
                      else
                        (vl_view_orig || vr_view_orig)
                  in
                  let l3 = if flag
                  then begin
                    let left_ls = filter_norm_lemmas(look_up_coercion_with_target prog.prog_left_coercions vl_name vr_name) in
                    let right_ls = filter_norm_lemmas(look_up_coercion_with_target prog.prog_right_coercions vr_name vl_name) in
                    let left_act = if (not(!ann_derv) || vl_new_orig) then List.map (fun l -> (1,M_lemma (c,Some l))) left_ls else [] in
                    let right_act = if (not(!ann_derv) || vr_new_orig) then List.map (fun l -> (1,M_lemma (c,Some l))) right_ls else [] in
                    (* let left_act = List.map (fun l -> (1,M_lemma (c,Some l))) left_ls in *)
                    (* let right_act = List.map (fun l -> (1,M_lemma (c,Some l))) right_ls in *)
                    (* if (left_act==[] && right_act==[]) then [] (\* [(1,M_lemma (c,None))] *\) (\* only targetted lemma *\) *)
                    (* else *)
                    left_act@right_act
                  end
                  else  [] in
                  (*let l4 = 
                  (* TODO WN : what is original?? *)
                  (* Without it, run-fast-test of big imm runs faster while
                    * still accurate. However, it fails with
                    * imm/imm1.slk imm/imm3.slk *)
                    if get_view_original rhs_node then 
                    [(2,M_base_case_fold c)] 
                    else [] in*)
                  (* [] in *)
                  let src = (-1,norm_search_action (l2@l3  (* @l4 *) )) in
                  src (*Seq_action [l1;src]*)
            | DataNode dl, ViewNode vr -> 
                  let vr_name = vr.h_formula_view_name in
                  let vr_vdef = look_up_view_def_raw view_decls vr_name in
                  let vr_self_pts = vr_vdef.view_pt_by_self in
                  let vr_view_orig = vr.h_formula_view_original in
                  let vr_view_derv = vr.h_formula_view_derv in
                  (*Is it LOCKED state*)
                  let is_r_lock = match vr_vdef.view_inv_lock with
                    | Some _ -> true
                    | None -> false
                  in
                  let new_orig = if !ann_derv then not(vr_view_derv) else vr_view_orig in
                  (* let right_ls = look_up_coercion_with_target prog.prog_right_coercions vr_name dl.h_formula_data_name in *)
                  (* let a1 = if (new_orig || vr_self_pts==[]) then [(1,M_fold c)] else [] in *)
                  let a1 = 
                    if is_r_lock then [] else
                      if (new_orig || vr_self_pts==[]) then [(1,M_fold c)] else [] in
                  let a2 = if (new_orig) then [(1,M_rd_lemma c)] else [] in
                  let a = a1@a2 in
                  if a!=[] then (-1,Search_action a)
                  else (1,M_Nothing_to_do (" matched data with derived self-rec RHS node "^(string_of_match_res c)))
            | ViewNode vl, DataNode dr -> 
                  let vl_name = vl.h_formula_view_name in
                  let vl_vdef = look_up_view_def_raw view_decls vl_name in
                  let vl_self_pts = vl_vdef.view_pt_by_self in
                  let vl_view_orig = vl.h_formula_view_original in
                  let vl_view_derv = vl.h_formula_view_derv in
                  (*Is it LOCKED state*)
                  let is_l_lock = match vl_vdef.view_inv_lock with
                    | Some _ -> true
                    | None -> false
                  in
                  let new_orig = if !ann_derv then not(vl_view_derv) else vl_view_orig in
                  let uf_i = if new_orig then 0 else 1 in
                  let left_ls = filter_norm_lemmas(look_up_coercion_with_target prog.prog_left_coercions vl_name dr.h_formula_data_name) in
                  (* let a1 = if (new_orig || vl_self_pts==[]) then [(1,M_unfold (c,uf_i))] else [] in *)
                  let a1 = 
                    if is_l_lock then [] else
                      if (new_orig || vl_self_pts==[]) then [(1,M_unfold (c,uf_i))] else [] in
                  let a2 = if (new_orig & left_ls!=[]) then [(1,M_lemma (c,Some (List.hd left_ls)))] else [] in
                  (* if (left_ls == [] && (vl_view_orig ) then ua *)
                  (* else (1,M_lemma (c,Some (List.hd left_ls))) *)
                  let a = a1@a2 in
                  if a!=[] then (-1,Search_action a)
                    (* if (vl_view_orig || vl_self_pts==[]) then ua *)
                    (* else if (left_ls != []) then (1,M_lemma (c,Some (List.hd left_ls))) *)
                  else (1,M_Nothing_to_do ("matching data with deriv self-rec LHS node "^(string_of_match_res c)))
            | _ -> report_error no_pos "process_one_match unexpected formulas 1\n"	
          )
    | MaterializedArg (mv,ms) ->
          (* let _ = print_string "\n materialized args  analysis here!\n" in  *)  
          let uf_i = if mv.mater_full_flag then 0 else 1 in 
          (match lhs_node,rhs_node with
            | DataNode dl, _ -> (1,M_Nothing_to_do ("matching lhs: "^(string_of_h_formula lhs_node)^" with rhs: "^(string_of_h_formula rhs_node)))
            | ViewNode vl, ViewNode vr -> 
                  let a1 = (match ms with
                    | View_mater -> 
                          (* print_string "\n WN : unfold for meteralised!"; *)
                          M_unfold (c,uf_i) (* uf_i to prevent infinite unfolding *)
                    | Coerc_mater s -> 
                          (* let _ = print_string "\n selected lemma XX" in *)
                          M_lemma (c,Some s)) in
                  let l1 = [(1,M_base_case_unfold c)] in
                  (-1, (Search_action ((1,a1)::l1)))
            | ViewNode vl, DataNode dr ->
                  (* let _ = print_string "\n try LHS case analysis here!\n" in *)


                  (* let i = if mv.mater_full_flag then 0 else 1 in  *)
                  (* let a1 = (match ms with *)
                  (*   | View_mater -> (1,M_unfold (c,uf_i))  *)
                  (*   | Coerc_mater s -> (1,M_lemma (c,Some s))) in *)
                  
                  let lhs_case_flag = vl.h_formula_view_lhs_case in


                  (* let _ = print_string ("process_one_match_x:"  *)
                  (*                       ^ "### lhs_case_flag = " ^ (string_of_bool lhs_case_flag) *)
                  (*                       ^ "\n\n" )in *)
                  let a2 = 
                    (match ms with
                      | View_mater -> (1,M_unfold (c,uf_i))
                      | Coerc_mater s -> (1,M_lemma (c,Some s))) in
                  (* WHY do we need LHS_CASE_ANALYSIS? *)
                  let a1 = 
                    if (lhs_case_flag=true) then
                      let l1 = [(1,M_lhs_case c)] 
                      in
                      (* (-1, (Search_action (a2::l1))) *)
                      (-1, (Cond_action (a2::l1)))
                    else
                      let l1 = [(1,M_base_case_unfold c)] in
                      (* (-1, (Search_action (a2::l1))) *)
                      (-1, (Cond_action (a2::l1)))
                  in a1
            | _ -> report_error no_pos "process_one_match unexpected formulas 2\n"	
          )
    | WArg -> (1,M_Nothing_to_do (string_of_match_res c)) in

  let r1 = match c.match_res_type with 
      (*Used when normalizing. MATCH only*)
    | Root ->
          (match lhs_node,rhs_node with
            | DataNode dl, DataNode dr -> 
                  if ((String.compare dl.h_formula_data_name dr.h_formula_data_name)==0) 
                  then (0,M_match c)
                  else  (1,M_Nothing_to_do (string_of_match_res c))
            | ViewNode vl, ViewNode vr -> 
                  if ((String.compare vl.h_formula_view_name vr.h_formula_view_name)==0) 
                  then (0,M_match c)
                  else  (1,M_Nothing_to_do (string_of_match_res c))
            | DataNode dl, ViewNode vr -> (1,M_Nothing_to_do (string_of_match_res c))
            | ViewNode vl, DataNode dr -> (1,M_Nothing_to_do (string_of_match_res c))
            | _ -> report_error no_pos "process_one_match unexpected formulas 3\n"	              )
    | MaterializedArg (mv,ms) -> 
          (*??? expect MATCHING only when normalizing => this situation does not need to be handled*)
          (* let _ = print_string ("\n [context.ml] Warning: process_one_match not support Materialized Arg when normalizing\n") in *)
          (1,M_Nothing_to_do (string_of_match_res c))
    | WArg -> (1,M_Nothing_to_do (string_of_match_res c)) in
  (*if in normalizing process => choose r1, otherwise, r*)
  if (is_normalizing) then r1
  else r


and process_matches prog estate lhs_h is_normalizing ((l:match_res list),(rhs_node,rhs_rest)) =
  let pr = Cprinter.string_of_h_formula   in
  let pr1 = pr_list string_of_match_res in
  let pr2 x = (fun (l1, (c1,c2)) -> "(" ^ (pr1 l1) ^ ",(" ^ (pr c1) ^ "," ^ (pr c2) ^ "))" ) x in
  let pr3 = string_of_action_wt_res0 in
  Debug.no_2 "process_matches" pr pr2 pr3 (fun _ _-> process_matches_x prog estate lhs_h is_normalizing (l, (rhs_node,rhs_rest))) lhs_h (l, (rhs_node,rhs_rest))

and process_matches_x prog estate lhs_h is_normalizing ((l:match_res list),(rhs_node,rhs_rest)) = 
    let _ = Debug.tinfo_pprint "**** sel_hp_rel **********************" no_pos in
    let _ = Debug.tinfo_hprint (add_str "hp_rel" Cprinter.string_of_spec_var_list) estate.es_infer_vars_hp_rel no_pos in
    let _ = Debug.tinfo_hprint (add_str "sel_hp_rel" Cprinter.string_of_spec_var_list) estate.es_infer_vars_sel_hp_rel no_pos in
    let _ = Debug.tinfo_hprint (add_str "sel_post_hp_rel" Cprinter.string_of_spec_var_list) estate.es_infer_vars_sel_post_hp_rel no_pos in
    match l with
      | [] -> 
            let r0 = (2,M_unmatched_rhs_data_node (rhs_node,rhs_rest)) in
            let rs = 
              if estate.es_infer_vars_hp_rel==[] then []
              else [(2,M_infer_heap (rhs_node,rhs_rest))] in
            if (is_view rhs_node) && (get_view_original rhs_node) then
              let r = (2, M_base_case_fold { match_res_lhs_node = HEmp;
              match_res_lhs_rest = lhs_h;
              match_res_holes = [];
              match_res_type = Root;
              match_res_rhs_node = rhs_node;
              match_res_rhs_rest = rhs_rest; }) in 
              (* WN : why do we need to have a fold following a base-case fold?*)
              (* changing to no_match found *)
              (*(-1, Search_action [r])*)
              (* let r1 = (2, M_fold { *)
              (*     match_res_lhs_node = HTrue;  *)
              (*     match_res_lhs_rest = lhs_h;  *)
              (*     match_res_holes = []; *)
              (*     match_res_type = Root; *)
              (*     match_res_rhs_node = rhs_node; *)
              (*     match_res_rhs_rest = rhs_rest; *)
              (* }) in *)
              (* temp removal of infer-heap and base-case fold *)
              (-1, (Cond_action (rs@[r;r0])))
            else (-1, Cond_action (rs@[r0]))
              (* M_Nothing_to_do ("no match found for: "^(string_of_h_formula rhs_node)) *)
      | x::[] -> process_one_match prog is_normalizing x 
      | _ -> (-1,Search_action (List.map (process_one_match prog is_normalizing) l))

and choose_closest a ys =
  let similar m o =
    (m.match_res_lhs_node == o.match_res_lhs_node)
    && (m.match_res_rhs_node == o.match_res_rhs_node) in
  let rec find m ys = 
    match ys with
      | [] -> None
      | (_,x)::xs ->
            begin
              let r =(find_a m x) in
              match r with
                | None -> find m xs
                | Some a -> r
            end 
  and find_a m x = 
    match x with
      | M_match o ->
            if similar m o then Some x
            else None
      | Cond_action awl 
      | Seq_action awl
      | Search_action awl
          -> (find m awl)
      | _ -> None in
  match a with
    | M_match m -> find m ys
    | _ -> None
          
and choose_match f ys =
  match f with
    | None -> None
    | Some a -> choose_closest a ys


and sort_wt (ys: action_wt list) : action list =
  let pr = pr_list string_of_action_wt_res_simpl in
  let pr2 = pr_list string_of_action_res in
  Debug.no_1 "sort_wt" pr pr2 sort_wt_x ys

and sort_wt_x (ys: action_wt list) : action list =
  let rec recalibrate_wt (w,a) = match a with
    | Search_action l ->
          let l = List.map recalibrate_wt l in
          let sl = List.sort (fun (w1,_) (w2,_) -> if w1<w2 then -1 else if w1>w2 then 1 else 0 ) l in
          let h = (List.hd sl) in
          let rw = (fst h) in
          (* WHY did we pick only ONE when rw==0?*)
          (*Since -1 : unknown, 0 : mandatory; >0 : optional (lower value has higher priority) *)
          if (rw==0) then h 
          else (rw,Search_action sl)
    | Cond_action l (* TOCHECK : is recalibrate correct? *)
        ->
          (*drop ummatched actions if possible*)
          (* let l = drop_unmatched_action l in *)
          let l = List.map recalibrate_wt l in
          let rw = List.fold_left (fun a (w,_)-> if (a<=w) then w else a) (fst (List.hd l)) (List.tl l) in
          (rw,Cond_action l)
    | Seq_action l ->
          let l = List.map recalibrate_wt l in
          let rw = List.fold_left (fun a (w,_)-> if (a<=w) then w else a) (fst (List.hd l)) (List.tl l) in
          (rw,Seq_action l)
    | _ -> if (w == -1) then (0,a) else (w,a) in
  let ls = List.map recalibrate_wt ys in
  let sl = List.sort (fun (w1,_) (w2,_) -> if w1<w2 then -1 else if w1>w2 then 1 else 0 ) ls in
  (snd (List.split sl))

and drop_unmatched_action l=
  let rec helper acs rs=
    match acs with
      | [] -> rs
      | ac::ss ->
            ( match ac with
              | (_, M_unmatched_rhs_data_node _) -> helper ss rs
              | _ -> helper ss (ac::rs)
            )
  in
  (match l with
    | [] -> []
    | [a] -> [a]
    | _ -> helper l []
  )

and sort_wt_match opt (ys: action_wt list) : action list =
  match (choose_match opt ys) with
    | None -> sort_wt ys
    | Some a -> 
          (* let _ = print_endline "WN : Found a must_action_stk match" in  *)
          [a]

and sort_wt_new (ys: action_wt list) : action_wt list =
  let pr = pr_list string_of_action_wt_res_simpl in
  Debug.no_1 "sort_wt_new" pr pr sort_wt_new_x ys

and group_equal_actions (ys: action_wt list) (running:action_wt list) (running_w: int) (rs: action_wt list):
      (action_wt list)=
  let pr = pr_list string_of_action_wt_res_simpl in
  Debug.no_4 "group_equal_actions" pr pr string_of_int pr pr group_equal_actions_x ys running running_w rs

and group_equal_actions_x (ys: action_wt list) (running:action_wt list) (running_w: int) (rs: action_wt list):
      (action_wt list)=
  match ys with
    | [] -> let new_rs =
        match running with
          | [] -> rs
          | [a] -> rs @ [a]
          | _ -> rs @ [(running_w, Cond_action running)]
      in new_rs
    | (w, act)::ss ->
          if (w > running_w) then
            begin
              let new_rs =
                match running with
                  | [] -> rs
                  | [a] -> rs @ [a]
                  | _ -> rs @ [(running_w, Cond_action running)]
              in
              group_equal_actions ss [(w, act)] w new_rs
            end
          else if (w = running_w) then
            group_equal_actions ss (running @ [(w, act)]) running_w rs
          else
            (*something is wrong here*)
            report_error no_pos "context: sort_wt_new: w should be >= current weight"


(*sorted and group euqal actions into a cond_action*)
and sort_wt_new_x (ys: action_wt list) : action_wt list =
  (* ys is a soted ation list
     running: current equal action group. init = []
     running_w: current wwight. inti = -1
     rs: return list, init = []
  *)
  
  let rec recalibrate_wt (w,a) = match a with
    | Search_action l ->
          let l = List.map recalibrate_wt l in
          let sl = List.sort (fun (w1,_) (w2,_) -> if w1<w2 then -1 else if w1>w2 then 1 else 0 ) l in
          let h = (List.hd sl) in
          let rw = (fst h) in
          (* WHY did we pick only ONE when rw==0?*)
          (*Since -1 : unknown, 0 : mandatory; >0 : optional (lower value has higher priority) *)
          if (rw==0) then h 
          else
            let rs = group_equal_actions sl [] (-1) [] in
            let rs1 =
              (
                  match rs with
                    | [] -> (rw, a)
                    | [act] -> act
                    | ls -> (rw,Cond_action ls)
              )
            in rs1
    | Cond_action l (* TOCHECK : is recalibrate correct? *) ->
          let l = List.map recalibrate_wt l in
          (  match l with
            | [] -> (w,a)
            | [act] -> act
            | l->
                  let rw = List.fold_left (fun a (w,_)-> if (a<=w) then a else w) (fst (List.hd l)) (List.tl l) in
                  (rw,Cond_action l)
          )
    | Seq_action l ->
          let l = List.map recalibrate_wt l in
          let rw = List.fold_left (fun a (w,_)-> if (a<=w) then a else w) (fst (List.hd l)) (List.tl l) in
          (rw,Seq_action l)
    | _ -> if (w == -1) then (0,a) else (w,a) in
  let ls = List.map recalibrate_wt ys in
  let sl = List.sort (fun (w1,_) (w2,_) -> if w1<w2 then -1 else if w1>w2 then 1 else 0 ) ls in
  (group_equal_actions sl [] (-1) [])

and pick_unfold_only ((w,a):action_wt) : action_wt list =
  match a with
    | M_unfold _ -> [(w,a)]
    | Seq_action l  | Cond_action l -> 
          if l==[] then [] 
          else pick_unfold_only (List.hd l)
    | Search_action l -> List.concat (List.map pick_unfold_only l)
    | _ -> []


(* and heap_entail_non_empty_rhs_heap_x prog is_folding  ctx0 estate ante conseq lhs_b rhs_b pos : (list_context * proof) = *)

and compute_actions_x prog estate es lhs_h lhs_p rhs_p posib_r_alias rhs_lst is_normalizing pos :action =
  let opt = 
    if not(must_action_stk # is_empty) then
      let a = must_action_stk # top in
      (must_action_stk # pop; Some a)
    else None
  in
  (* let _ = print_string ("\n(andreeac) context.ml l_h:"  ^ (Cprinter.string_of_h_formula lhs_h)) in *)
  let r = List.map (fun (c1,c2)-> (choose_context prog es lhs_h lhs_p rhs_p posib_r_alias c1 c2 pos,(c1,c2))) rhs_lst in
  (* match r with  *)
  (*   | [] -> M_Nothing_to_do "no nodes to match" *)
  (*   | x::[]-> process_matches lhs_h x *)
  (*   | _ ->  List.hd r (\*Search_action (None,r)*\) *)
  (* let _ = print_string (" compute_actions: before process_matches") in *)
  let r = List.map (process_matches prog estate lhs_h is_normalizing) r in
  match r with
    | [] -> M_Nothing_to_do "no nodes on RHS"
    | xs -> 
          (*  imm/imm1.slk imm/imm3.slk fails if sort_wt not done *)
          let ys = sort_wt_match opt r in 
          List.hd (ys)
              (*  match ys with
                  | [(_, act)] -> act
                  | ys -> (Cond_action ys) *)
              (* (List.hd (ys)) *)
              (* time for runfast hip --eps --imm - 42s *)
              (* Cond_action (r) *)
              (* time for runfast hip --eps --imm - 43s *)

and compute_actions prog estate es (* list of right aliases *)
      lhs_h (*lhs heap *) 
      lhs_p (*lhs pure*) 
      rhs_p (*rhs pure*)
      posib_r_alias (*possible rhs variables*)
      rhs_lst is_normalizing 
      pos =
  let psv = Cprinter.string_of_spec_var in
  let pr0 = pr_list (pr_pair psv psv) in
  (* let pr_rhs_lst = pr_list (pr_pair Cprinter.string_of_h_formula Cprinter.string_of_h_formula) in *)
  let pr = Cprinter.string_of_h_formula   in
  (* let pr1 x = String.concat ";\n" (List.map (fun (c1,c2)-> "("^(Cprinter.string_of_h_formula c1)^" *** "^(Cprinter.string_of_h_formula c2)^")") x) in *)
  (* let pr3 = Cprinter.string_of_mix_formula in *)
  let pr1 x = pr_list (fun (c1,_)-> Cprinter.string_of_h_formula c1) x in
  (* let pr4 = pr_list Cprinter.string_of_spec_var in *)
  let pr2 = string_of_action_res_simpl in
  Debug.no_3 "compute_actions" 
      (add_str "EQ ptr" pr0) 
      (add_str "LHS heap" pr) 
      (* (add_str "LHS pure" pr3)  *)
      (add_str "RHS cand" pr1)
      (* (add_str "right alias" pr4) *)
      pr2
      (fun _ _ _-> compute_actions_x prog estate es lhs_h lhs_p rhs_p posib_r_alias rhs_lst is_normalizing pos) es lhs_h (* lhs_p *) rhs_lst  (* posib_r_alias *)

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
    | ConjStar ({h_formula_conjstar_h1 = f1;
      h_formula_conjstar_h2 = f2;
      h_formula_conjstar_pos = pos}) -> 
	  let new_f1 = input_h_formula_in2_frame (f1, id_hole) to_input in 
	  let new_f2 = input_h_formula_in2_frame (f2, id_hole) to_input in
	  ConjStar ({h_formula_conjstar_h1 = new_f1;
	  h_formula_conjstar_h2 = new_f2;
	  h_formula_conjstar_pos = pos}) 
    | ConjConj ({h_formula_conjconj_h1 = f1;
      h_formula_conjconj_h2 = f2;
      h_formula_conjconj_pos = pos}) -> 
	  let new_f1 = input_h_formula_in2_frame (f1, id_hole) to_input in 
	  let new_f2 = input_h_formula_in2_frame (f2, id_hole) to_input in
	  ConjConj ({h_formula_conjconj_h1 = new_f1;
	  h_formula_conjconj_h2 = new_f2;
	  h_formula_conjconj_pos = pos}) 		  		  
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
    | HEmp
    | HRel _
    | HTrue | HFalse | StarMinus _ -> frame
          
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
  let matches = choose_context prog [] lhs_h lhs_p (MCP.mkMTrue no_pos) [] node HEmp pos in
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
