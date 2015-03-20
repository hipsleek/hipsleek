#include "xdebug.cppo"
open VarGen

open Globals
open Cformula
open Cast
open Cprinter
open Gen.Basic
open Immutable

module CF = Cformula
module CFU = Cfutil

type match_res = {
    match_res_lhs_node : h_formula; (* node from the extracted formula *)
    match_res_lhs_rest : h_formula; (* lhs formula - contains holes in place of matched immutable nodes/views *)
    match_res_holes : (h_formula * int) list; (* imm node/view that have been replaced in lhs together with their corresponding hole id *)
    match_res_type : match_type; (* indicator of what type of matching *)
    match_res_rhs_node : h_formula;
    match_res_rhs_rest : h_formula;
}

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
        (* materialized match which can reveal some nodes when defn unfolded *)
  | WArg (* indirect matching with other parameter *)
  | Wand
  
and action = 
  | M_match of match_res
  | M_split_match of match_res
  | M_fold of match_res
  | M_acc_fold of (match_res * (Acc_fold.fold_type list))
  | M_unfold  of (match_res * int) (* zero denotes no counting *)
  | M_base_case_unfold of match_res
  | M_base_case_fold of match_res
  | M_seg_fold of (match_res * int)
  | M_rd_lemma of match_res
  | M_lemma  of (match_res * (coercion_decl option))
  | Undefined_action of match_res
  | M_Nothing_to_do of string
  | M_infer_heap of (h_formula * h_formula) (* rhs * rhs_rest *)
  | M_unmatched_rhs_data_node of (h_formula * h_formula * CVP.vperm_sets)
  (* perform a list of actions until there is one succeed*)
  | Cond_action of action_wt list
  (*not handle yet*) 
  | Seq_action of action_wt list 
  | Search_action of action_wt list (*the match_res indicates if pushing holes for each action is required or it will be done once, at the end*)
  | M_lhs_case of match_res
        (*match * number_of_unfold * unfold_or_fold * type_lemma_syn*)
        (* lem_type = 0: LEFT *)
  | M_ramify_lemma of match_res
        (* lem_type = 1 :RIGHT *)
        (* lem_type = 2: INFER *)
  | M_cyclic of (match_res* int * int * int * h_formula option)
  (* | Un *)
  (* | M *)
  (* | Opt int *)

and action_wt = (int * action)  (* -1 : unknown, 0 : mandatory; >0 : optional (lower value has higher priority) *) 

let get_rhs_rest_emp_flag act old_is_rhs_emp =
  match act with
    | M_match m
    | M_split_match m
    | M_fold m
    | M_unfold  (m,_)
    | M_base_case_unfold m
    | M_base_case_fold m
    | M_seg_fold (m,_)
    | M_acc_fold (m,_)
    | M_rd_lemma m
    | M_lemma  (m, _)
    | M_ramify_lemma m
    | Undefined_action m
    | M_lhs_case m
    | M_cyclic (m,_,_,_,_) ->
          if m.match_res_rhs_rest = HEmp then true else false
    | M_Nothing_to_do _ -> old_is_rhs_emp
    | M_infer_heap _ -> old_is_rhs_emp
    | M_unmatched_rhs_data_node _ -> false
          (* perform a list of actions until there is one succeed*)
    | Cond_action _ -> old_is_rhs_emp
          (*not handle yet*)
    | Seq_action _ -> old_is_rhs_emp
    | Search_action _ -> old_is_rhs_emp

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
    | Wand -> fmt_string "Wand"


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

let string_of_match_res_pair (c:match_res) : string =
  (try 
    let lhs_n = CF.get_node_var c.match_res_lhs_node in
    let rhs_n = CF.get_node_var c.match_res_rhs_node in
    pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var (lhs_n,rhs_n)
  with _ -> "(UNK)")

let rec pr_action_name a = match a with
  | Undefined_action e -> fmt_string "Undefined_action"
  | M_match e ->
        let str = string_of_match_res_pair e in
        fmt_string ("Match" ^ str)
  | M_split_match e -> fmt_string "Split&Match "
  | M_fold e -> fmt_string "Fold"
  | M_unfold (e,i) -> fmt_string ("Unfold "^(string_of_int i))
  | M_base_case_unfold e -> fmt_string "BaseCaseUnfold"
  | M_base_case_fold e -> fmt_string "BaseCaseFold"
  | M_seg_fold e -> fmt_string "SegFold"
  | M_acc_fold _ -> fmt_string "AccFold"
  | M_rd_lemma e -> fmt_string "RD_Lemma"
  | M_ramify_lemma e -> fmt_string "Ramify Lemma"
  | M_lemma (e,s) ->
        let str = string_of_match_res_pair e in
        fmt_string (""^(match s with | None -> "AnyLemma" | Some c-> "(Lemma "
        ^(string_of_coercion_type c.coercion_type)^" "^c.coercion_name ^ str ^ ")"))
  | M_Nothing_to_do s -> fmt_string ("NothingToDo"^s)
  | M_infer_heap p -> fmt_string ("InferHeap")
  | M_unmatched_rhs_data_node (h,_,_) -> fmt_string ("UnmatchedRHSData")
  | Cond_action l -> fmt_string "COND"
  | Seq_action l -> fmt_string "SEQ"
  | Search_action l -> fmt_string "SEARCH"
  | M_lhs_case e -> fmt_string "LHSCaseAnalysis"
  | M_cyclic _ -> fmt_string "Match cyclic"

let rec pr_action_res pr_mr a = match a with
  | Undefined_action e -> fmt_string "Undefined_action =>"; pr_mr e
  | M_match e -> fmt_string "Match =>"; pr_mr e
  | M_split_match e -> fmt_string "SplitMatch =>"; pr_mr e
  | M_fold e -> fmt_string "Fold =>"; pr_mr e
  | M_unfold (e,i) -> fmt_string ("Unfold "^(string_of_int i)^" =>"); pr_mr e
  | M_base_case_unfold e -> fmt_string "BaseCaseUnfold =>"; pr_mr e
  | M_base_case_fold e -> fmt_string "BaseCaseFold =>"; pr_mr e
  | M_seg_fold (e,_) -> fmt_string "SegFold =>"; pr_mr e
  | M_acc_fold (e,steps) ->
      let pr_steps s = fmt_string ("\n fold steps:" ^ (pr_list Acc_fold.print_fold_type s)) in
      fmt_string "AccFold =>"; pr_mr e; pr_steps steps
  | M_rd_lemma e -> fmt_string "RD_Lemma =>"; pr_mr e
  | M_ramify_lemma e -> fmt_string "Ramify_Lemma =>"; pr_mr e
  | M_lemma (e,s) -> fmt_string ((match s with | None -> "AnyLemma" | Some c-> "(Lemma "
        ^(string_of_coercion_type c.coercion_type)^" "^c.coercion_name)^") =>"); pr_mr e
  | M_Nothing_to_do s -> fmt_string ("NothingToDo => "^s)
  | M_infer_heap p ->
      let pr = string_of_h_formula in
      fmt_string ("InferHeap => "^(pr_pair pr pr p))
  | M_unmatched_rhs_data_node (h,_,_) -> fmt_string ("UnmatchedRHSData => "^(string_of_h_formula h))
  | Cond_action l -> pr_seq_nocut "COND =>" (pr_action_wt_res pr_mr) l
  | Seq_action l -> pr_seq_vbox "SEQ =>" (pr_action_wt_res pr_mr) l
  | Search_action l -> 
        fmt_open_vbox 1;
        pr_seq_vbox "SEARCH =>" (pr_action_wt_res pr_mr) l;
        fmt_close();
  | M_lhs_case e -> fmt_string "LHSCaseAnalysis =>"; pr_mr e
  | M_cyclic (e,_,_,_,_) -> fmt_string "Match cyclic =>"; pr_mr e

and pr_action_wt_res pr_mr (w,a) = 
  fmt_string ("Prio:"^(string_of_int w)^" "); (pr_action_res pr_mr a)

let string_of_action_name (e:action) = poly_string_of_pr pr_action_name e

let string_of_action_res_simpl (e:action) = poly_string_of_pr (pr_action_res pr_simpl_match_res) e

let string_of_action_res_simpl_0 (e:action) = poly_string_of_pr (pr_action_res (fun _ -> fmt_string " ")) e

let string_of_action_wt_res_simpl (e:action_wt) = poly_string_of_pr (pr_action_wt_res pr_simpl_match_res) e

let string_of_action_res e = poly_string_of_pr (pr_action_res pr_match_res) e

let string_of_action_wt_res e = poly_string_of_pr (pr_action_wt_res pr_match_res) e

let string_of_action_wt_res0 e = poly_string_of_pr (pr_action_wt_res (fun _ -> fmt_string "")) e

let string_of_match_type e = poly_string_of_pr pr_match_type e  

let string_of_match_res e = poly_string_of_pr pr_match_res e  

let must_action_stk = new Gen.stack(* _noexc (M_Nothing_to_do "empty must_action_stk") string_of_action_res_simpl (=) *)
   
let action_get_holes a = match a with
  | Undefined_action e
  | M_match e
  | M_split_match e
  | M_lhs_case e
  | M_fold e
  | M_unfold (e,_)
  | M_seg_fold (e,_)
  | M_acc_fold (e,_)
  | M_rd_lemma e
  | M_ramify_lemma e
  | M_lemma (e,_)
  | M_base_case_unfold e
  | M_cyclic (e,_,_,_,_)
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
(* let rec alias_x (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list =  *)
(*   match ptr_eqs with *)
(*   | (v1, v2) :: rest -> begin *)
(* 	  let rest_sets = alias_x rest in *)
(* 	  let search (v : CP.spec_var) (asets : CP.spec_var list list) = List.partition (fun aset -> CP.mem v aset) asets in *)
(* 	  let av1, rest1 = search v1 rest_sets in *)
(* 	  let av2, rest2 = search v2 rest1 in *)
(* 	  let v1v2_set = CP.remove_dups_svl (List.concat ([v1; v2] :: (av1 @ av2))) in *)
(* 	  v1v2_set :: rest2 *)
(* 	end *)
(*   | [] -> [] *)


(* let alias_x (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list =  *)
(*   let aset = alias_x ptr_eqs in *)
(* List.filter (fun l -> List.length l > 1) aset *)

(* let alias_nth i (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list =  *)
(*   let psv = Cprinter.string_of_spec_var in *)
(*   let pr1 l = pr_list (pr_pair psv psv) l in *)
(*   let pr2 l = pr_list (pr_list psv) l in *)
(*   Debug.no_1_num i "alias" pr1 pr2 alias_x ptr_eqs *)

(* let get_aset (aset : CP.spec_var list list) (v : CP.spec_var) : CP.spec_var list = *)
(*   let tmp = List.filter (fun a -> CP.mem v a) aset in *)
(*   match tmp with *)
(* 	| [] -> [] *)
(* 	| [s] -> s *)
(* 	| _ -> failwith ((string_of_spec_var v) ^ " appears in more than one alias sets") *)

(* let get_aset (aset : CP.spec_var list list) (v : CP.spec_var) : CP.spec_var list = *)
(* let psv = Cprinter.string_of_spec_var in *)
(*  let pr1 = (pr_list psv) in *)
(*  let pr2 = pr_list pr1 in *)
(*  Debug.no_2 "get_aset" pr2  psv pr1 get_aset aset v *)

(* let comp_aliases_x (rhs_p:MCP.mix_formula) : (CP.spec_var) list list = *)
(*     let eqns = MCP.ptr_equations_without_null rhs_p in *)
(*     alias_nth 1 eqns  *)

(* let comp_aliases (rhs_p:MCP.mix_formula) : (CP.spec_var) list list = *)
(*  let psv = Cprinter.string_of_spec_var in *)
(*  let pr2 = (pr_list (pr_list psv)) in *)
(*  let pr1 = Cprinter.string_of_mix_formula in *)
(*  Debug.no_1 "comp_aliase" pr1 pr2 comp_aliases_x rhs_p *)

(* let comp_alias_part r_asets a_vars =  *)
(*     (\* let a_vars = lhs_fv @ posib_r_aliases in *\) *)
(*     let fltr = List.map (fun c-> Gen.BList.intersect_eq (CP.eq_spec_var) c a_vars) r_asets in *)
(*     let colaps l = List.fold_left (fun a c -> match a with  *)
(*       | [] -> [(c,c)] *)
(*       | h::_-> (c,(fst h))::a) [] l in *)
(*     List.concat (List.map colaps fltr)  *)

let is_match_res_from_coerc_or_root m =
  match m.match_res_type with
    (* | Root  *)
    | MaterializedArg (_, Coerc_mater _) -> true
    (* | MaterializedArg (_, Weak_coerc_mater _) -> true *)
    |_ -> false

let get_hp_match_res lst =
  List.filter (fun m -> is_match_res_from_coerc_or_root m) lst

let filter_match_res_list lst rhs_node = 
  match rhs_node with
    | HRel _ ->    List.filter (fun m -> is_match_res_from_coerc_or_root m) lst
    | _      ->  lst

let convert_starminus ls = 
        List.map (fun m ->
          let lhs_rest = m.match_res_lhs_rest in
          let () = print_string ("lhs_res:"^(Cprinter.string_of_h_formula lhs_rest)^"\n") in
          let rec helper  hrest  = 
          (match hrest with
            | StarMinus ({h_formula_starminus_h1 = h1;
                          h_formula_starminus_h2 = h2;
                          h_formula_starminus_aliasing = al;
                          h_formula_starminus_pos = pos}) ->
                (let h1 =  match al with
                  | Not_Aliased -> mkStarH h2 h1 pos 
                  | May_Aliased -> mkConjH h2 h1 pos
                  | Must_Aliased -> mkConjConjH h2 h1 pos
                  | Partial_Aliased -> mkConjStarH h2 h1 pos in 
                (mkStarMinusH h1 h2 al pos 111))
            | Star({h_formula_star_h1 = h1;
                    h_formula_star_h2 = h2;
                    h_formula_star_pos = pos}) ->
                mkStarH (helper h1) (helper h2) no_pos 
            | _ -> hrest)
          in 
          let h = helper lhs_rest in
          let () = print_string ("new_lhs_res:"^(Cprinter.string_of_h_formula h)^"\n") 
          in { match_res_lhs_node = m.match_res_lhs_node;
               match_res_lhs_rest = h;
               match_res_holes = m.match_res_holes;
               match_res_type = m.match_res_type;
               match_res_rhs_node = m.match_res_rhs_node;
               match_res_rhs_rest = m.match_res_rhs_rest}
        ) ls

(*  (resth1, anode, r_flag, phase, ctx) *)

(* 
 * Trung, delete later: 
 *   - Choose context, requires rhs_node is either a HRel or a Node (Data, View, Thread)
 *   - In acc-fold: choose_context must allow rhs_node is a general heap formula
 *     (or a chain of heap nodes and views )
 *)
let rec choose_context_x prog rhs_es lhs_h lhs_p rhs_p posib_r_aliases rhs_node rhs_rest pos : match_res list =
  (* let () = print_string("choose ctx: lhs_h = " ^ (string_of_h_formula lhs_h) ^ "\n") in *)
  match rhs_node with
    | HRel _  
    | ThreadNode _ 
    | DataNode _ 
    | HVar _
    | ViewNode _ ->
      let imm, pimm, p = match rhs_node with
        | DataNode { h_formula_data_node=p; h_formula_data_imm=imm; h_formula_data_param_imm=pimm; } -> (imm, pimm, p)
        | ViewNode { h_formula_view_node=p; h_formula_view_imm=imm } -> (imm, [], p)
        (* TODO:WN:HVar *)
        | HVar (v,_) -> (CP.ConstAnn(Mutable), [], v)
        | ThreadNode { h_formula_thread_node=p; } -> (CP.ConstAnn(Mutable), [], p)
        | HRel (hp, e, _) ->
          let args = CP.diff_svl (get_all_sv rhs_node) [hp] in
          let root, _ = Sautil.find_root prog [hp] args [] in
          let () = x_tinfo_hp (add_str "root" Cprinter.string_of_spec_var) root pos in
          (CP.ConstAnn(Mutable), [], root)
        | _ -> report_error no_pos "choose_context unexpected rhs formula\n"
      in
      let lhs_fv = (h_fv lhs_h) @ (MCP.mfv lhs_p) in
      let eqns' = MCP.ptr_equations_without_null lhs_p in
      (* let emap = CP.EMapSV.build_eset eqns' in *)
      let r_eqns =
        let eqns = (MCP.ptr_equations_without_null rhs_p) @ rhs_es in
        let r_asets = Csvutil.alias_nth 2 eqns in
        let a_vars = lhs_fv @ posib_r_aliases in
        let fltr = List.map (fun c-> Gen.BList.intersect_eq (CP.eq_spec_var) c a_vars) r_asets in
        let colaps l = List.fold_left (fun a c -> match a with
          | [] -> [(c,c)]
          | h::_-> (c,(fst h))::a) [] l 
        in
        List.concat (List.map colaps fltr) 
      in
      let eqns = (p, p) :: eqns' in
      let emap = CP.EMapSV.build_eset eqns' in
      (* let emap = CP.EMapSV.build_eset eqns in *)
      (* let paset = CP.EMapSV.find_equiv_all p emap in *)
      (* let paset = p::paset in *)
      let asets = Csvutil.alias_nth 3 (eqns@r_eqns) in
      let paset = Csvutil.get_aset asets p in (* find the alias set containing p *)
      if Gen.is_empty paset then
        failwith ("choose_context: Error in getting aliases for " ^ (string_of_spec_var p))
      else if (* not(CP.mem p lhs_fv) ||  *)(!Globals.enable_syn_base_case && (CP.mem CP.null_var paset)) then
        (x_dinfo_zp (lazy ("choose_context: " ^ (string_of_spec_var p) ^ " is not mentioned in lhs\n\n")) pos; [] )
      else 
        (* (* TRUNG TODO: to insert acc_fold context here *)                  *)
        (* let accfold_res = (                                                *)
        (*   if !Globals.acc_fold then                                        *)
        (*     spatial_ctx_accfold_extract prog lhs_h lhs_p rhs_node rhs_rest *)
        (*   else []                                                          *)
        (* ) in                                                               *)
        let mt_res = spatial_ctx_extract prog lhs_h paset imm pimm rhs_node rhs_rest emap in
        let mt_res = filter_match_res_list mt_res rhs_node in
        (* (accfold_res @ mt_res) *)
        mt_res
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
    (* | HRel _ -> [] *) (* spatial_ctx_extract prog lhs_h paset CF.ConstAnn(Mutable) [] rhs_node rhs_rest *)
    | _ -> report_error no_pos "choose_context unexpected rhs formula\n"

and choose_context prog es lhs_h lhs_p rhs_p posib_r_aliases rhs_node rhs_rest pos
    :  match_res list =
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
      (fun _ _ _ _ _ -> choose_context_x prog es lhs_h lhs_p rhs_p posib_r_aliases rhs_node rhs_rest pos) 
      lhs_h rhs_node lhs_p rhs_p es

(* type: Cast.prog_decl ->
   Globals.ident ->
  Immutable.CP.spec_var list ->
  Immutable.CP.spec_var list ->
  Immutable.CP.ann ->
  Cformula.h_formula ->
  Cformula.CP.annot_arg list ->
  (Cformula.h_formula * Cformula.h_formula *
   (Cformula.h_formula * int) list * match_type)
  list
*)
and view_mater_match prog c vs1 aset imm f anns =
  let pr1 = (fun x -> x) in
  let pr2 = !print_svl in
  let pro1 = (add_str "lhs_rest" Cprinter.string_of_h_formula) in
  let pro2 = (add_str "lhs_node" Cprinter.string_of_h_formula) in
  let pro3 = (add_str "holes" (pr_list (pr_pair Cprinter.string_of_h_formula string_of_int))) in
  let pro4 = (add_str "match_type" string_of_match_type) in
  let pr = pr_list (pr_quad pro1 pro2 pro3 pro4) in
  Debug.no_4 "view_mater_match" (add_str "heap_f" Cprinter.string_of_h_formula)
      (add_str "c" pr1) (add_str "vs1" pr2) 
      (add_str "aset" pr2) pr (fun _ _ _ _ -> view_mater_match_x prog c vs1 aset imm f anns) f c vs1 aset

and view_mater_match_x prog c vs1 aset imm f anns =
  let vdef = look_up_view_def_raw 11 prog.prog_view_decls c in
  let vdef_param = (self_param vdef)::(vdef.view_vars) in
  let mvs = subst_mater_list_nth 1 vdef_param vs1 vdef.view_materialized_vars in
  let vars =  vdef.view_vars in
  let () = x_tinfo_hp  (add_str "vars" Cprinter.string_of_spec_var_list ) vars no_pos in
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
    let () = DD.ninfo_hprint (add_str "args" (pr_list Cprinter.string_of_spec_var)) args no_pos in
    match l_vargs with
      | [] -> None
      | _  -> 
            let lmv = subst_mater_list_nth 2 args l_vargs c.coercion_mater_vars in
            let () = Debug.ninfo_hprint (add_str "lmv" Cprinter.string_of_mater_prop_list) lmv no_pos in
            try
              let mv = List.find (fun v -> List.exists (CP.eq_spec_var v.mater_var) r_aset) lmv in 
              (* above goes awry when we're using self var in the entailment! andreea *)
              let () = Debug.ninfo_hprint (add_str "mv" Cprinter.string_of_mater_prop_list) [mv] no_pos in
              Some (Coerc_mater c,mv)
            with  _ ->  (* andreeac below test is inefficient. to be replaced *)
                if(( List.length (Cformula.get_HRels_f c.coercion_body)) > 0) then
                  match lmv with
                    | [] -> None
                    | _  -> Some (Coerc_mater c, List.hd lmv) 
                else None

and choose_full_mater_coercion l_vname l_vargs r_aset (c:coercion_decl) =
  let pr_svl = Cprinter.string_of_spec_var_list in
  (* let pr (c,_) = string_of_coercion c in *)
  Debug.no_1 "choose_full_mater_coercion" pr_svl (* (pr_option pr) *) pr_none (fun _ -> choose_full_mater_coercion_x l_vname l_vargs r_aset c) r_aset

and coerc_mater_match_x coercs vname (vargs:P.spec_var list) r_aset (lhs_f:Cformula.h_formula) =
  (* TODO : how about right coercion, Cristina? *)
  (* WN_all_lemma - is this overriding of lemmas? *)
  (* let coercs = (Lem_store.all_lemma # get_left_coercion)(\*prog.prog_left_coercions*\) in *)
  (* let () = x_tinfo_hp (add_str "coercs" (pr_list Cprinter.string_of_coercion)) coercs no_pos in *)
  let pos_coercs = List.fold_right (fun c a ->
      match (choose_full_mater_coercion vname vargs r_aset c) with 
        | None ->  a 
        | Some t -> t::a
  ) coercs [] in
  let res = List.map (fun (c,mv) -> (HEmp, lhs_f, [], MaterializedArg (mv,c))) pos_coercs in
  (* let pos_coercs = List.fold_left  *)
  (*   (fun a c->  *)
  (*       let args = List.tl (fv_simple_formula c.coercion_head) in  *)
  (*       let lmv = subst_mater_list_nth 3 args l_vargs c.coercion_mater_vars in *)
  (*       try *)
  (*         let mv = List.find (fun v -> List.exists (CP.eq_spec_var v.mater_var) r_aset) lmv in *)
  (*         (HTrue, lhs_f, [], MaterializedArg (mv,Coerc_mater c.coercion_name))::a *)
  (*       with  _ ->  a) [] pos_coercs in *)
  (* if produces_hole imm then [] else *) res

and coerc_mater_match coercs l_vname (l_vargs:P.spec_var list) r_aset (lhs_f:Cformula.h_formula) =
  let pr = Cprinter.string_of_h_formula in
  let pr4 (h1,h2,l,mt) = pr_pair pr pr (h1,h2) in
  let pr2 ls = pr_list pr4 ls in
  let pr_svl = Cprinter.string_of_spec_var_list in
  Debug.no_3 "coerc_mater_match" pr_id pr_svl pr_svl pr2
      (fun _ _ _ -> coerc_mater_match_x coercs l_vname (l_vargs:P.spec_var list) r_aset (lhs_f:Cformula.h_formula)) l_vname l_vargs r_aset

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
(* Trung, delete later: extract node in LHS (f) to match with node in RHS *)
and spatial_ctx_extract p f a i pi rn rr emap = 
  let pr = pr_list string_of_match_res in
  let pr_svl = Cprinter.string_of_spec_var_list in
  (*let pr_aset = pr_list (pr_list Cprinter.string_of_spec_var) in*)
  (* let pr = pr_no in *)
  Debug.no_4 "spatial_ctx_extract" string_of_h_formula Cprinter.string_of_imm pr_svl string_of_h_formula pr 
      (fun _ _ _ _-> spatial_ctx_extract_x p f a i pi rn rr emap) f i a rn 

and update_field_imm (f : h_formula) (pimm1 : CP.ann list) (consumed_ann: CP.ann list) (residue: bool): h_formula = 
  let pr lst = "[" ^ (List.fold_left (fun y x-> (Cprinter.string_of_imm x) ^ ", " ^ y) "" lst) ^ "]; " in
  let pr_out = Cprinter.string_of_h_formula in
  Debug.no_2 "update_field_ann" (Cprinter.string_of_h_formula) pr  pr_out (fun _ _-> update_field_imm_x f pimm1 consumed_ann residue) f pimm1

and update_field_imm_x (f : h_formula) (new_fann: CP.ann list) (consumed_ann: CP.ann list) (residue: bool): h_formula  = 
  (* let (res_ann, cons_ann), niv, constr = Immutable.replace_list_ann pimm1 pimm impl_vars evars in *)
  (* asankhs: If node has all field annotations as @A make it HEmp *)
  if (isAccsList new_fann) && (!Globals.remove_abs) then HEmp else
    let updated_f = match f with 
      | DataNode d -> 
            let lst = List.combine new_fann consumed_ann in
            let lst = List.combine d.h_formula_data_arguments lst in
            let new_args = List.map (fun (arg, (new_ann, cons_ann)) -> 
                if (residue && isAccs new_ann && not(isAccs cons_ann)) then  CP.fresh_spec_var arg
                else arg ) lst in
            DataNode ( {d with h_formula_data_param_imm = new_fann; 
                h_formula_data_arguments = new_args;
            } )
      | ViewNode v -> ViewNode ( {v with h_formula_view_annot_arg =  CP.update_positions_for_imm_view_params  new_fann v.h_formula_view_annot_arg} )
      | _          -> report_error no_pos ("[context.ml] : only data node should allow field annotations \n")
    in
    updated_f

and update_imm (f : h_formula) (imm1 : CP.ann) (imm2 : CP.ann) es(* : h_formula *) = 
  let pr = Cprinter.string_of_imm in
  let pr_out = pr_triple (Cprinter.string_of_h_formula) pr_none pr_none in
    Debug.no_3 "update_ann" (Cprinter.string_of_h_formula) pr pr  pr_out  (fun _ _ _-> update_imm_x f imm1 imm2  es) f imm1 imm2

and update_imm_x (f : h_formula) (imm1 : CP.ann) (imm2 : CP.ann)  es = 
  (* let new_imm_lnode, niv, constr = Immutable.remaining_ann imm1 imm2 impl_vars evars in *)
  let (res_ann, cons_ann), niv, constr = Immutable.replace_list_ann 1 [imm1] [imm2]  es in
  (* asankhs: If node has all field annotations as @A make it HEmp *)
  if (isAccsList res_ann) && (!Globals.remove_abs) then (HEmp, [], (([],[],[]),[]) )else
    let updated_f = match f with 
      | DataNode d -> DataNode ( {d with h_formula_data_imm = List.hd res_ann} )
      | _          -> report_error no_pos ("[context.ml] : only data node should allow field annotations \n")
    in
    (updated_f,niv, constr)

and imm_split_lhs_node_x estate l_node r_node = match l_node, r_node with
  | DataNode dl, DataNode dr ->
	if (!Globals.allow_field_ann) then 
          let (res_ann, cons_ann), niv, constr = Immutable.replace_list_ann 2 (dl.h_formula_data_param_imm) (dr.h_formula_data_param_imm) estate in
          let n_f = update_field_imm l_node res_ann cons_ann true in
          let n_ch = update_field_imm l_node cons_ann cons_ann false in
	  (* let n_f, niv, constr = update_field_imm l_node dl.h_formula_data_param_imm dr.h_formula_data_param_imm estate.es_gen_impl_vars  estate.es_evars in *)
	  let n_es = {estate with es_formula = mkStar (formula_of_heap n_f no_pos) estate.es_formula Flow_combine no_pos;
              es_heap = mkStarH  n_ch  estate.es_heap no_pos;
              (* es_gen_impl_vars =estate.es_gen_impl_vars@niv *) } in
          (n_es, constr)
        else (* if(!Globals.allow_imm) then *)
          if not(produces_hole  dr.h_formula_data_imm) then
            let n_f, niv, constr = update_imm l_node dl.h_formula_data_imm dr.h_formula_data_imm estate in
            let n_es = {estate with es_formula = mkStar (formula_of_heap n_f no_pos) estate.es_formula Flow_combine no_pos;
                (* es_gen_impl_vars = estate.es_gen_impl_vars@niv  *)} in
            (n_es, constr)
          else
            (estate,(([],[],[]),[]))
        (* else *)
        (*   (estate,(([],[],[]),[])) *)
  | (ViewNode vl), ViewNode vr ->
        if (!Globals.allow_field_ann) then
          let l_ann = CP.annot_arg_to_imm_ann_list (get_node_annot_args l_node) in
          let r_ann = CP.annot_arg_to_imm_ann_list (get_node_annot_args r_node) in
          (* let () = Debug.ninfo_hprint (add_str "l_node" (Cprinter.string_of_h_formula)) l_node no_pos in *)
          (* let () = Debug.ninfo_hprint (add_str "r_node" (Cprinter.string_of_h_formula)) r_node no_pos in *)
          let (res_ann, cons_ann), niv, constr = Immutable.replace_list_ann 3 l_ann r_ann estate in
          let n_f = update_field_imm l_node res_ann cons_ann true in
          let n_ch = update_field_imm l_node cons_ann cons_ann false in
          let n_es = {estate with es_formula = mkStar (formula_of_heap n_f no_pos) estate.es_formula Flow_combine no_pos;
              es_heap = mkStarH  n_ch  estate.es_heap no_pos;
              (* es_gen_impl_vars =estate.es_gen_impl_vars@niv *) } in
          (n_es, constr)
        else
          (estate,(([],[],[]),[]))
  | _ -> (estate,(([],[],[]),[]))

and imm_split_lhs_node estate l_node r_node =
  let pr_node = Cprinter.string_of_h_formula in
  let pr_es = Cprinter.string_of_entail_state in
  let pr_lst str =  add_str str Cprinter.string_of_pure_formula_list in
  let pr_second = (pr_pair (pr_triple (pr_lst "to_lhs") (pr_lst "to_rhs") (pr_lst "to_rhs_ex")) (add_str "subst" string_of_subst)) in
  let pr_out = pr_pair pr_es pr_second in
  Debug.no_3 "imm_split_lhs_node" pr_es pr_node pr_node pr_out imm_split_lhs_node_x estate l_node r_node

(*  *)
and get_data_nodes_ptrs_to_view prog hd_nodes hv_nodes view_sv =
  let unlinked_nodes = ref ([]: CP.spec_var list) in
  List.filter (fun node ->
      if Gen.BList.mem_eq CP.eq_spec_var (node.h_formula_data_node) !unlinked_nodes then false
      else
        let ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes [node.h_formula_data_node] in
        if (empty_inters view_sv ptrs) then begin
          unlinked_nodes := !unlinked_nodes @ ptrs;
          false
        end
        else true
  ) hd_nodes

and get_view_nodes_ptrs_to_view prog hd_nodes hv_nodes view_sv =
  let unlinked_nodes = ref ([]: CP.spec_var list) in
  List.filter (fun node ->
      if Gen.BList.mem_eq CP.eq_spec_var (node.h_formula_view_node) !unlinked_nodes then false
      else
        let ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes [node.h_formula_view_node] in
        if (empty_inters view_sv ptrs)then begin
          unlinked_nodes := !unlinked_nodes @ ptrs;
          false
        end
        else true
  ) hv_nodes

and get_hrels_ptrs_to_view prog hd_nodes hv_nodes hrels view_sv =
  (List.filter (fun (hp0, e0,_) ->  
      let args0 = CP.diff_svl (get_all_sv (HRel(hp0, e0,no_pos))) [hp0] in
      let root0, _  = Sautil.find_root prog [hp0] args0  [] in
      let ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes [root0] in
      (* replace root with aset *)
      not(empty_inters view_sv ptrs)
  ) hrels)

and empty_inters lst1 lst2 = 
  match Gen.BList.intersect_eq (CP.eq_spec_var) lst1 lst2 with
      | [] -> true
      | _  -> false

and exists_candidate_lemma_x coercs vname = 
  let valid_cand c = if ((c.coercion_case=Cast.Simple || c.coercion_case= (Normalize false)) && c.coercion_head_view = vname) then true else false in
  List.exists valid_cand coercs  

and exists_candidate_lemma coercs vname = 
  Debug.no_1 "exists_candidate_lemma" pr_id string_of_bool (fun _ -> exists_candidate_lemma_x coercs vname) vname

(* try to find a lemma to be applied only if the view on the lhs is reachable from a node matching
the node on the rhs *)
and check_pred_reachability prog (must_contain: P.spec_var list) (target_f: Cformula.h_formula) target_aset =
  let hd_nodes, hv_nodes, hrels = get_hp_rel_h_formula target_f in
  let ptrs0 = (List.map (fun v -> v.h_formula_data_node) (get_data_nodes_ptrs_to_view prog hd_nodes hv_nodes target_aset) ) in
  if (empty_inters ptrs0 must_contain) then
    let ptrs0 = (List.map (fun v -> v.h_formula_view_node) (get_view_nodes_ptrs_to_view prog hd_nodes hv_nodes target_aset) ) in
    if (empty_inters ptrs0 must_contain) then
      let ptrs0 = (List.map (fun (hp0,e0,_) -> 
          let args0 = CP.diff_svl (get_all_sv (HRel(hp0, e0,no_pos))) [hp0] in
          let root0, _  = Sautil.find_root prog [hp0] args0  [] in
          root0) (get_hrels_ptrs_to_view prog hd_nodes hv_nodes hrels target_aset)) in
      if (empty_inters ptrs0 must_contain) then false
      else true
    else true
  else true

and coerc_mater_match_with_unk_hp_left prog (l_vname: ident) (r_vname: ident) (l_vargs: P.spec_var list) (r_vargs: P.spec_var list) (r_aset: P.spec_var list) (lhs_node: Cformula.h_formula) (l_f: Cformula.h_formula) view_sv =
  let coerc_left = Lem_store.all_lemma # get_left_coercion in
  let exists_left = exists_candidate_lemma coerc_left l_vname in
  let cmm = if exists_left then 
    let reachable_pred = check_pred_reachability prog r_aset l_f view_sv in 
    if (reachable_pred) then 
      coerc_mater_match coerc_left l_vname l_vargs r_aset lhs_node
    else []
  else [] in
  cmm

and coerc_mater_match_with_unk_hp_right prog (l_vname: ident) (r_vname: ident) (l_vargs: P.spec_var list) (r_vargs: P.spec_var list) (r_aset: P.spec_var list) (lhs_node: Cformula.h_formula) (l_f: Cformula.h_formula) view_sv =
  let coerc_right = Lem_store.all_lemma # get_right_coercion in
  let exists_right = exists_candidate_lemma coerc_right r_vname in
  let cmm = if exists_right then 
    let reachable_pred = check_pred_reachability prog r_aset l_f view_sv in 
    if (reachable_pred) then 
      coerc_mater_match coerc_right r_vname r_vargs view_sv lhs_node
    else [] 
  else [] in
  cmm

and coerc_mater_match_with_unk_hp_x prog (l_vname: ident) (r_vname: ident) (l_vargs: P.spec_var list) (r_vargs: P.spec_var list) (r_aset: P.spec_var list) (lhs_node: Cformula.h_formula) (l_f: Cformula.h_formula) view_sv =
  let cmml = coerc_mater_match_with_unk_hp_left prog l_vname r_vname l_vargs r_vargs r_aset lhs_node l_f view_sv in
  let cmmr = coerc_mater_match_with_unk_hp_right prog l_vname r_vname l_vargs r_vargs r_aset lhs_node l_f view_sv in 
  cmml@cmmr

and coerc_mater_match_with_unk_hp prog (l_vname: ident) (r_vname: ident) (l_vargs: P.spec_var list) (r_vargs: P.spec_var list)  (r_aset: P.spec_var list) (lhs_node: Cformula.h_formula) (l_f: Cformula.h_formula) view_sv =
  let pr_svl = Cprinter.string_of_spec_var_list in
  Debug.no_4 "coerc_mater_match_with_unk_hp" pr_id pr_svl pr_svl pr_svl pr_none (fun _ _ _ _-> coerc_mater_match_with_unk_hp_x prog (l_vname: ident) r_vname (l_vargs: P.spec_var list) r_vargs (r_aset: P.spec_var list) (lhs_node: Cformula.h_formula) (l_f: Cformula.h_formula) view_sv) l_vname l_vargs r_aset view_sv

and spatial_ctx_extract_hrel_on_lhs prog hp e rhs_node aset (lhs_node: Cformula.h_formula) (l_f: Cformula.h_formula) emap =
  match rhs_node with
    | ViewNode ({h_formula_view_node = p1;
      h_formula_view_imm = imm1;
      h_formula_view_perm = perm1;
      h_formula_view_arguments = vs1;
      h_formula_view_name = c}) -> 
          let args = CP.diff_svl (get_all_sv lhs_node) [hp] in
           (* let () = DD.info_zprint (lazy (("  args: " ^ (!CP.print_svl args)))) no_pos in *)
          if args = [] then [] else
            let root, _  = Sautil.find_root prog [hp] args  [] in
            let root_aset = CP.EMapSV.find_equiv_all root emap in
            let root_aset = root::root_aset in
            (* let e = List.fold_left (fun a v-> CP.is_var v then  a@[CP.exp_to_spec_var v] else a) []  e in *)
            let cmm = coerc_mater_match_with_unk_hp prog (CP.name_of_spec_var hp) c args vs1 aset lhs_node l_f root_aset in 
            cmm
    | _ -> []

and coerc_mater_match_gen_x l_vname (l_vargs:P.spec_var list) (* r_vname (r_vargs:P.spec_var list)  l_asset*) r_aset (lhs_f:Cformula.h_formula) =
  let coerc_left = Lem_store.all_lemma # get_left_coercion in
  let cmml = coerc_mater_match coerc_left l_vname (l_vargs:P.spec_var list) r_aset (lhs_f:Cformula.h_formula) in
  let coerc_right = Lem_store.all_lemma # get_right_coercion in
  (* let cmmr = coerc_mater_match coerc_right l_vname (l_vargs:P.spec_var list) r_aset (lhs_f:Cformula.h_formula) in *)
  let cmmr = coerc_mater_match coerc_right l_vname (l_vargs:P.spec_var list) r_aset (lhs_f:Cformula.h_formula) in
  cmml(* @cmmr *)

and coerc_mater_match_gen l_vname (l_vargs:P.spec_var list) r_aset (lhs_f:Cformula.h_formula) =
  let pr = Cprinter.string_of_h_formula in
  let pr4 (h1,h2,l,mt) = pr_pair pr pr (h1,h2) in
  let pr2 ls = pr_list pr4 ls in
  let pr_svl = Cprinter.string_of_spec_var_list in
  Debug.no_3 "coerc_mater_match_gen" pr_id pr_svl pr_svl pr2
      (fun _ _ _ -> coerc_mater_match_gen_x l_vname (l_vargs:P.spec_var list) r_aset (lhs_f:Cformula.h_formula)) l_vname l_vargs r_aset

and spatial_ctx_extract_x prog (f0 : h_formula)
    (aset : CP.spec_var list) (imm : CP.ann) (pimm : CP.ann list)
    rhs_node rhs_rest emap
    : match_res list  =
  let rec helper f = match f with    (* f is formula in LHS *)
    | HTrue -> []
    | HFalse -> []
    | HEmp -> []
    | Hole _ -> []
    | HVar (v,_) -> 
      (match rhs_node with
        (* URGENT:TODO:WN:HVar *)
        | HVar (vr,_) -> if CP.eq_spec_var v vr then [(HEmp, f, [], Root)] else []
        | _ -> [])
    | ThreadNode ({h_formula_thread_node = p1;}) -> (
        match rhs_node with
        | HRel _ -> []
        | ThreadNode _ -> (*TOCHECK*)
            [(HEmp, f, [], Root)]
        | _      ->
            if ((CP.mem p1 aset) (* && (subtyp) *)) then 
              if (not !Globals.allow_field_ann) then
                (* not consuming the node *)
                let hole_no = Globals.fresh_int() in 
                [((Hole hole_no), f, [(f, hole_no)], Root)]
              else
                [(HEmp, f, [], Root)]
            else []
      )
    | DataNode ({h_formula_data_node = p1; 
                 h_formula_data_imm = imm1;
                 h_formula_data_param_imm = pimm1}) -> (
        match rhs_node with
        | HRel _ -> []
        | _      ->
            if ((CP.mem p1 aset) (* && (subtyp) *)) then 
              if ( (not !Globals.allow_field_ann) && produces_hole imm) then
                (* not consuming the node *)
                let hole_no = Globals.fresh_int() in 
                [((Hole hole_no), f, [(f, hole_no)], Root)]
              else
                (*if (!Globals.allow_field_ann) then
                  let new_f = update_ann f pimm1 pimm in
                  [(new_f,f,[],Root)]
                  else*)
                [(HEmp, f, [], Root)]
            else []
      )
    | ViewNode ({h_formula_view_node = p1;
                 h_formula_view_imm = imm1;
                 h_formula_view_perm = perm1;
                 h_formula_view_arguments = vs1;
                 h_formula_view_name = c}) as v -> (
        let anns = get_node_annot_args f in
        match rhs_node with
        | HRel (hp,_,_) ->
            let p1_eq = CP.EMapSV.find_equiv_all p1 emap in
            let p1_eq = p1::p1_eq in
            let cmm = coerc_mater_match_with_unk_hp prog c
                (CP.name_of_spec_var hp) vs1 [] aset f f0 p1_eq in
            cmm
        | _ -> 
            (* if (subtype_ann imm1 imm) then *)
            if (CP.mem p1 aset) then
              (* let () = print_string("found match for LHS = " ^ (Cprinter.string_of_h_formula f) ^ "\n") in *)
              if produces_hole imm && not(!Globals.allow_field_ann) then
              (* let () = print_string("imm = Lend " ^ "\n") in *)
                let hole_no = Globals.fresh_int() in
                (*[(Hole hole_no, matched_node, hole_no, f, Root, HTrue, [])]*)
                [(Hole hole_no, f, [(f, hole_no)], Root)]
              else
                [(HEmp, f, [], Root)]
                    (********** Loc: TODO multiple matching, the former is empty*********)
                (* begin *)
                (*   match rhs_node with *)
                (*     | ViewNode {h_formula_view_name = r_vn} -> *)
                (*           let () = DD.ninfo_hprint (add_str " l_view_name" pr_id) c no_pos in *)
                (*           let () = DD.ninfo_hprint (add_str " r_vn" pr_id) r_vn no_pos in *)
                (*           if String.compare r_vn c = 0 then [(HEmp, f, [], Root)] else [] *)
                (*     | _ ->  [(HEmp, f, [], Root)] *)
                (* end *)
                    (*********************** END LOC TOD**********************)
            else
              let vmm = view_mater_match prog c (p1::vs1) aset imm f anns in
              let cmm = coerc_mater_match_gen c vs1 aset f in
              (*LDK: currently, assume that frac perm does not effect
                the choice of lemmas (coercions)*)
              vmm@cmm
      )
    | HRel (hp,e,_) ->
        spatial_ctx_extract_hrel_on_lhs prog hp e rhs_node aset f f0 emap
    | Star ({h_formula_star_h1 = f1;
             h_formula_star_h2 = f2;
             h_formula_star_pos = pos}) ->
        let l1 = helper f1 in
        let res1 = List.map (fun (lhs1, node1, hole1, match1) ->
          (mkStarH lhs1 f2 pos, node1, hole1, match1)
        ) l1 in
        let l2 = helper f2 in
        let res2 = List.map (fun (lhs2, node2, hole2, match2) ->
          (mkStarH f1 lhs2 pos, node2, hole2, match2)
        ) l2 in
        res1 @ res2
    | StarMinus ({h_formula_starminus_h1 = f1;
                  h_formula_starminus_h2 = f2;
                  h_formula_starminus_aliasing = al;
                  h_formula_starminus_pos = pos}) ->
      let f = (let f1 =  match al with
                  | Not_Aliased -> mkStarH f2 f1 pos 
                  | May_Aliased -> mkConjH f2 f1 pos
                  | Must_Aliased -> mkConjConjH f2 f1 pos
                  | Partial_Aliased -> mkConjStarH f2 f1 pos in 
                (mkStarMinusH f1 f2 al pos 111)) in
      [f,rhs_node,[],Wand]
      (*
	    let _ = print_string("[context.ml]:Use ramification lemma, lhs = " ^ (string_of_h_formula f) ^ "\n") in
        failwith("[context.ml]: There should be no wand in the lhs at this level\n")*)
          (*let l1 = helper f1 in
          let res1 = List.map (fun (lhs1, node1, hole1, match1) -> (mkStarMinusH lhs1 f2 al pos 12 , node1, hole1, match1)) l1 in  
          let l2 = helper f2 in
          let res2 = List.map (fun (lhs2, node2, hole2, match2) -> (mkStarMinusH f1 lhs2 al pos 13, node2, hole2, match2)) l2 in
          res1 @ res2*)
    
    | Conj({h_formula_conj_h1 = f1;
            h_formula_conj_h2 = f2;
      h_formula_conj_pos = pos}) ->  if (!Globals.allow_mem || !Globals.allow_ramify) then 
        if CF.contains_starminus f1 || CF.contains_starminus f2 then
          let () = print_string("[context.ml]:Use ramification lemmas lhs = " ^ (string_of_h_formula f) ^ "\n") in
          failwith("[context.ml]: There should be no wand in the lhs at this level\n")
        else 
          let l1 = helper f1 in
          let res1 = List.map (fun (lhs1, node1, hole1, match1) -> 
          let nl,nn,nh,nm = 
            if not (is_empty_heap node1) && (is_empty_heap rhs_rest) then 
              let ramify_f2 = mkStarMinusH f2 node1 May_Aliased pos 37 in
             (* if CF.contains_starminus lhs1 then (lhs1, node1, hole1, match1)
              else*) (mkStarH lhs1 ramify_f2 pos , node1, hole1, match1)
            else (mkStarH lhs1 f2 pos , node1, hole1, match1) in
          (*let () = print_endline("F : "^Cprinter.string_of_h_formula nl) in*) nl,nn,nh,nm) l1 in 
          let l2 = helper f2 in
          let res2 = List.map (fun (lhs2, node2, hole2, match2) -> 
          let nl,nn,nh,nm = 
            if not (is_empty_heap node2) && (is_empty_heap rhs_rest) then 
              let ramify_f1 = mkStarMinusH f1 node2 May_Aliased pos 38 in
              if CF.contains_starminus lhs2 then 
                match lhs2 with
                  | StarMinus ({h_formula_starminus_h1 = lhs2_f1;
                                h_formula_starminus_h2 = lhs2_f2;
                                h_formula_starminus_aliasing = lhs2_al;
                                h_formula_starminus_pos = lhs2_pos}) -> (mkStarMinusH (mkConjH f1 lhs2_f1 lhs2_pos) node2 lhs2_al pos 39, node2, hole2, match2)
                  | _ -> (mkStarH ramify_f1 lhs2 pos, node2, hole2, match2)
              else (mkStarH ramify_f1 lhs2 pos, node2, hole2, match2)
            else
              (mkStarH f1 lhs2 pos , node2, hole2, match2) in
          (*let () = print_endline("G : "^Cprinter.string_of_h_formula nl) in*) nl,nn,nh,nm) l2 in
          (*let helper0 lst = List.fold_left (fun res (a,_,_,_) -> res ^ (Cprinter.string_of_h_formula a) ) "" lst in 
            let () = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x res1:"  ^ helper0 res1) in
            let () = print_string ("\n(andreeac) context.ml spatial_ctx_extract_x res2:"  ^ helper0 res2) in *)
          res1 @ res2
      (*[(mkStarMinusH f rhs_node Not_Aliased pos 37,rhs_node,[],Root)]*)
        else 
          let () = print_string("[context.ml]: Conjunction in lhs, use mem specifications. lhs = "
              ^ (string_of_h_formula f) ^ "\n") in
          failwith("[context.ml]: There should be no conj/phase in the lhs at this level 1\n")
    | ConjStar({h_formula_conjstar_h1 = f1;
                h_formula_conjstar_h2 = f2;
                h_formula_conjstar_pos = pos}) ->
        if (!Globals.allow_mem) then 
          let l1 = helper f1 in
          let res1 = List.map (fun (lhs1, node1, hole1, match1) ->
            (mkConjStarH lhs1 f2 pos , node1, hole1, match1)
          ) l1 in
          let l2 = helper f2 in
          let res2 = List.map (fun (lhs2, node2, hole2, match2) ->
            (mkConjStarH f1 lhs2 pos , node2, hole2, match2)
          ) l2 in
          res1 @ res2
        else
          let () = print_string("[context.ml]: Conjunction in lhs, use mem specifications. lhs = "
              ^ (string_of_h_formula f) ^ "\n") in
          failwith("[context.ml]: There should be no conj/phase in the lhs at this level 2\n")
    | ConjConj({h_formula_conjconj_h1 = f1;
                h_formula_conjconj_h2 = f2;
                h_formula_conjconj_pos = pos}) ->
        if (!Globals.allow_mem) then
          let l1 = helper f1 in
          let res1 = List.map (fun (lhs1, node1, hole1, match1) ->
            (mkConjConjH lhs1 f2 pos , node1, hole1, match1)
          ) l1 in
          let l2 = helper f2 in
          let res2 = List.map (fun (lhs2, node2, hole2, match2) ->
            (mkConjConjH f1 lhs2 pos , node2, hole2, match2)
          ) l2 in
          res1 @ res2
        else
          let () = print_string("[context.ml]: Conjunction in lhs, use mem specifications. lhs = "
              ^ (string_of_h_formula f) ^ "\n") in
          failwith("[context.ml]: There should be no conj/phase in the lhs at this level 3\n")
    | _ ->
          let () = print_string("[context.ml]: There should be no conj/phase in the lhs at this level; lhs = "
              ^ (string_of_h_formula f) ^ "\n") in
          failwith("[context.ml]: There should be no conj/phase in the lhs at this level\n")
  in
  (* todo:Long *)
  (* why is l empty? *)
  let l = helper f0 in
  let pr1 = (add_str "lhs_rest" Cprinter.string_of_h_formula) in
  let pr2 = (add_str "lhs_node" Cprinter.string_of_h_formula) in
  let pr3 = (add_str "holes" (pr_list (pr_pair Cprinter.string_of_h_formula string_of_int))) in
  let pr4 = (add_str "match_type" string_of_match_type) in
  let pr = pr_quad pr1 pr2 pr3 pr4 in
  let () = DD.ninfo_hprint (add_str "l_xxx" (pr_list pr)) l no_pos in
  List.map (fun (lhs_rest,lhs_node,holes,mt) ->
      (* let () = print_string ("\n(andreeac) lhs_rest spatial_ctx_extract " ^ (Cprinter.string_of_h_formula lhs_rest) ^ "\n(andreeac) f0: " ^ (Cprinter.string_of_h_formula f0)) in *)
      { match_res_lhs_node = lhs_node;
        match_res_lhs_rest = lhs_rest;
        match_res_holes = holes;
        match_res_type = mt;
        match_res_rhs_node = rhs_node;
        match_res_rhs_rest = rhs_rest; }
  ) l


(* spatial_ctx_extract prog lhs_h paset imm pimm rhs_node rhs_rest emap in *)

(* and spatial_ctx_accfold_extract_x prog lhs_h lhs_p rhs_node rhs_rest rhs_p : match_res list = *)
(*   match rhs_node with                                                                         *)
(*   | ViewNode vn -> (                                                                          *)
(*       (* only do accfold when rhs_node is a view *)                                           *)
(*       try                                                                                     *)
(*         let vnode = vn.CF.h_formula_view_node in                                              *)
(*         let vname = vn.CF.h_formula_view_name in                                              *)
(*         let vdecl = look_up_view_def_raw 0 prog.prog_view_decls vname in                      *)
(*         let heap_chains = Acc_fold.collect_heap_chains lhs_h lhs_p vnode vdecl prog in        *)
(*         (* remove the last chain which has only 1 atomic hformula                             *)
(*            which is already extracted in normal spatial_ctx_extract *)                        *)
(*         let heap_chains = List.filter (fun ((hf,_,_),hf_rest) ->                              *)
(*           let coded_hf = Acc_fold.encode_h_formula hf in                                      *)
(*           (List.length coded_hf > 1)                                                          *)
(*         ) heap_chains in                                                                      *)
(*         List.map (fun ((hf_chain,_,_),hf_rest) ->                                             *)
(*           { match_res_lhs_node = hf_chain;                                                    *)
(*             match_res_lhs_rest = hf_rest;                                                     *)
(*             match_res_lhs_p = lhs_p;                                                          *)
(*             match_res_holes = [];                                                             *)
(*             match_res_type = Root;                                                            *)
(*             match_res_rhs_node = rhs_node;                                                    *)
(*             match_res_rhs_rest = rhs_rest;                                                    *)
(*             match_res_rhs_p = rhs_p; }                                                        *)
(*         ) heap_chains                                                                         *)
(*       with _ -> []                                                                            *)
(*     )                                                                                         *)
(*   | _ -> []                                                                                   *)

(* and spatial_ctx_accfold_extract prog lhs_h lhs_p rhs_node rhs_rest =                          *)
(*   let pr_hf = !CF.print_h_formula in                                                          *)
(*   let pr_out = pr_list string_of_match_res in                                                 *)
(*   Debug.no_2 "spatial_ctx_accfold_extract" pr_hf pr_hf pr_out                                 *)
(*       (fun _ _ -> spatial_ctx_accfold_extract_x prog lhs_h lhs_p rhs_node rhs_rest)           *)
(*       lhs_h rhs_node                                                                          *)

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
            | ThreadNode {CF.h_formula_thread_name = dl_name},
              ThreadNode {CF.h_formula_thread_name = dr_name;CF.h_formula_thread_split = dr_split}
            | DataNode {CF.h_formula_data_name = dl_name},
              DataNode {CF.h_formula_data_name = dr_name;CF.h_formula_data_split = dr_split} ->
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
                    (* WN_all_lemma - is this overriding of lemmas? *)
                    let left_lemmas = (List.filter (fun c -> c.coercion_case = (Cast.Normalize false)) (*prog.prog_left_coercions*) (Lem_store.all_lemma # get_left_coercion)) in
                    let right_lemmas = (List.filter (fun c -> c.coercion_case = (Cast.Normalize true)) (*prog.prog_right_coercions*) (Lem_store.all_lemma # get_right_coercion)) in
                    let left_lemmas =
                      if (dr_split = SPLIT0) then
                        (*do not split --> not apply lemma_split *)
                        List.filter (fun c -> c.coercion_kind != LEM_SPLIT) left_lemmas
                      else left_lemmas
                    in
                    let left_ls = look_up_coercion_with_target left_lemmas dl_name dr_name in
                    let right_ls = look_up_coercion_with_target right_lemmas dr_name dl_name in
                    let simple_ls = look_up_coercion_with_target (List.filter (fun c -> c.coercion_case = Cast.Simple) (*prog.prog_right_coercions*) ((Lem_store.all_lemma # get_left_coercion) @ (Lem_store.all_lemma # get_right_coercion))) dr_name dl_name in
                    let left_act = List.map (fun l -> (1,M_lemma (c,Some l))) left_ls in
                    let right_act = List.map (fun l -> (1,M_lemma (c,Some l))) right_ls in
                    let simple_act = List.map (fun l -> (1,M_lemma (c,Some l))) simple_ls in
                    left_act@right_act@simple_act
                  in
                  if l=[] then (1,M_Nothing_to_do (string_of_match_res c))
                  else (-1,Search_action l)
            | ViewNode vl, ViewNode vr ->
                  let vl_name = vl.h_formula_view_name in
                  let vr_name = vr.h_formula_view_name in
                  let vl_vdef = look_up_view_def_raw 12 view_decls vl_name in
                  let vr_vdef = look_up_view_def_raw 13 view_decls vr_name in
                  let vl_view_orig = vl.h_formula_view_original in
                  let vr_view_orig = vr.h_formula_view_original in
                  let vl_view_derv =  vl.h_formula_view_derv in
                  let vr_view_derv = vr.h_formula_view_derv in
                  let vr_view_split = vr.h_formula_view_split in
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
                    let left_lemmas = (List.filter (fun c -> c.coercion_case = (Cast.Normalize false)) (Lem_store.all_lemma # get_left_coercion)) in
                    let left_lemmas =
                      if (vr_view_split = SPLIT0) then
                        (*do not split --> not apply lemma_split *)
                        List.filter (fun c -> c.coercion_kind != LEM_SPLIT) left_lemmas
                      else left_lemmas
                    in
                    let right_lemmas = (List.filter (fun c -> c.coercion_case = (Cast.Normalize true)) (Lem_store.all_lemma # get_right_coercion) (*prog.prog_right_coercions*)) in
                    let left_ls = look_up_coercion_with_target left_lemmas vl_name vr_name in
                    let right_ls = look_up_coercion_with_target right_lemmas vr_name vl_name in
                    let left_act = if (not(!ann_derv) || vl_new_orig) then List.map (fun l -> (1,M_lemma (c,Some l))) left_ls else [] in
                    let right_act = if (not(!ann_derv) || vr_new_orig) then List.map (fun l -> (1,M_lemma (c,Some l))) right_ls else [] in
                    left_act@right_act
                  end
                  else  [] in
                  (* let () = Debug.info_hprint (add_str "xxxx" pr_id) "1"  no_pos in *)
                  if l=[] then
                    (* if not (!Globals.cyc_proof_syn) then *) (1,M_Nothing_to_do (string_of_match_res c))
                    (* else (1, M_cyclic (c, -1,-1,-1,None)) *)
                  else (-1,Search_action l)
            | DataNode dl, ViewNode vr -> (1,M_Nothing_to_do (string_of_match_res c))
            | ViewNode vl, DataNode dr -> (1,M_Nothing_to_do (string_of_match_res c))
            | _ -> report_error no_pos "process_one_match unexpected formulas\n"	              )
    | MaterializedArg (mv,ms) ->
          (*unexpected*)
          (1,M_Nothing_to_do (string_of_match_res c))
    | WArg ->
          (1,M_Nothing_to_do (string_of_match_res c))
    | Wand ->  (1,M_Nothing_to_do (string_of_match_res c))
  in
  act

and filter_norm_lemmas l = 
  List.filter (fun c-> match c.coercion_case with 
    | Normalize b -> if b || !use_split_match then false else true 
    | _ -> true) l 

and filter_lemmas_by_kind l k = 
  List.filter (fun c-> if c.coercion_case == k then true else false) l 


and search_lemma_candidates prog flag_lem ann_derv vr_view_split (vl_view_origs,vr_view_origs)
      (vl_new_orig,vr_new_orig) (vl_name,vr_name) m_res lhs rhs remap=
  let extract_node_info hnode=
    match hnode with
      | ViewNode vn -> (vn.h_formula_view_node, vn.h_formula_view_arguments)
      | DataNode dn -> (dn.h_formula_data_node, dn.h_formula_data_arguments)
      | _ -> raise Not_found
  in
  if flag_lem then
    let left_ls = filter_norm_lemmas (look_up_coercion_with_target (Lem_store.all_lemma # get_left_coercion) vl_name vr_name) in
    let left_ls =
      if (vr_view_split = SPLIT0) && (not !Globals.ho_always_split) then
        (* do not split --> not apply lemma_split *)
        List.filter (fun c -> c.coercion_kind != LEM_SPLIT) left_ls
      else left_ls
    in
    let right_ls = filter_norm_lemmas(look_up_coercion_with_target (Lem_store.all_lemma # get_right_coercion) vr_name vl_name) in
    let left_act = if (not(!ann_derv) || vl_new_orig) then List.map (fun l -> 
        if (Immutable.is_lend l.Cast.coercion_body) then (1,M_lemma (m_res,Some l))
        else (1,M_lemma (m_res,Some l))) left_ls else [] in
    let non_loop_candidate l = not (Gen.BList.mem_eq (fun s1 s2 -> (String.compare s1 s2 = 0)) l.Cast.coercion_name vr_view_origs)in
    let right_act =
      List.fold_left (fun acc l ->
          if  (vr_new_orig || (non_loop_candidate l)) then
            let prio = (* if ((Immutable.is_lend l.Cast.coercion_body) && vr_view_orig ) then 1 else*) 1 in
            acc@[(prio,M_lemma (m_res,Some l))]
          else acc) [] right_ls
    in
    left_act@right_act
  else  []

and process_one_match_mater_unk_w_view lhs_name rhs_name c ms f = 
  let right_ls = filter_norm_lemmas(look_up_coercion_with_target (Lem_store.all_lemma # get_right_coercion) rhs_name lhs_name) in
  let left_ls = filter_norm_lemmas(look_up_coercion_with_target (Lem_store.all_lemma # get_left_coercion) lhs_name rhs_name) in
  let coerc_lst = left_ls@right_ls in
  let prio, coerc = match ms with
    | Coerc_mater s -> (1,s)
    | _ -> failwith("[context.ml]: only lemma cand be fired at this point for UNK pred on lhs\n")
  in
  if List.exists (fun coerc0 -> coerc0.coercion_name = coerc.coercion_name) coerc_lst then  
    (prio, M_lemma (c,Some coerc))
  else
    f 

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

and norm_cond_action ls = match ls with
  | [] -> M_Nothing_to_do ("cond action is empty")
  | [(_,a)] -> a
  | lst -> Cond_action lst

and check_lemma_not_exist vl vr=
  if not !Globals.lemma_syn then false else
    let vl_name = vl.h_formula_view_name in
    let vr_name = vr.h_formula_view_name in

    (* let new_orig = if !ann_derv then not(vl.h_formula_view_derv) else vl.h_formula_view_original in *)
    let left_ls = look_up_coercion_with_target (List.filter (fun c -> c.coercion_case = Simple || c.coercion_case = Complex ) (Lem_store.all_lemma # get_left_coercion)) vl_name vr_name in
    let right_ls = look_up_coercion_with_target (List.filter (fun c -> c.coercion_case = Simple || c.coercion_case = Complex) (Lem_store.all_lemma # get_right_coercion) ) vr_name vl_name in
    let vl_new_orig = if !ann_derv then not(vl.h_formula_view_derv) else vl.h_formula_view_original in
    let vr_new_orig = if !ann_derv then not(vr.h_formula_view_derv) else vr.h_formula_view_original in
    let b_left = if (not(!ann_derv) || vl_new_orig) then true
    else false in
    let b_right = if (not(!ann_derv) || vr_new_orig) then true
    else false in
    b_left && b_right &&(left_ls@right_ls)=[]

and process_one_match_accfold_x (prog: C.prog_decl) (mt_res: match_res)
    (lhs_h: CF.h_formula) (lhs_p: MCP.mix_formula) (rhs_p: MCP.mix_formula)
    : action_wt list =
  if !Globals.acc_fold then (
    let lhs_node = mt_res.match_res_lhs_node in
    let rhs_node = mt_res.match_res_rhs_node in
    match lhs_node, rhs_node with
    | DataNode {h_formula_data_node = lv}, ViewNode vr
    | ViewNode {h_formula_view_node = lv}, ViewNode vr -> (
        let rv = vr.h_formula_view_node in
        let vr_name = vr.h_formula_view_name in
        let try_accfold = (
          if (CP.eq_spec_var lv rv) then true
          else 
            let pf = CP.mkAnd (MCP.pure_of_mix lhs_p) (MCP.pure_of_mix rhs_p) no_pos in
            let emap = CP.EMapSV.build_eset (CP.pure_ptr_equations pf) in
            let aliases = CP.EMapSV.find_equiv_all lv emap in
            if (CP.EMapSV.mem rv aliases) then true
            else false
        ) in
        if (try_accfold) then (
          let vdecl = look_up_view_def_raw 1 prog.prog_view_decls vr_name in
          let heap_chains = Acc_fold.collect_heap_chains lhs_h lhs_p lv vdecl prog in
          let fold_seqs = List.map (fun ((hf,_,_,_),hf_rest) ->
            let fold_steps = Acc_fold.detect_fold_sequence hf lv vdecl prog in
            (hf,hf_rest,fold_steps)
          ) heap_chains in
          let fold_seqs = List.filter (fun (_,_,fold_steps) ->
            (* do acc-fold only there is more than 1 fold steps *)
            List.length fold_steps > 1
          ) fold_seqs in
          let actions = List.map (fun (hf,hf_rest,fold_steps) ->
            let mt_res = {mt_res with match_res_lhs_node = hf;
                                      match_res_lhs_rest = hf_rest;} in
            (1, M_acc_fold (mt_res, fold_steps))
          ) fold_seqs in
          actions
        )
        else []
      )
    | _ -> [] 
  )
  else []

and process_one_match_accfold (prog: C.prog_decl) (mt_res: match_res)
    (lhs_h: CF.h_formula) (lhs_p: MCP.mix_formula) (rhs_p: MCP.mix_formula)
    : action_wt list =
  let pr_mr = string_of_match_res in
  let pr_h = !CF.print_h_formula in
  let pr_p = !MCP.print_mix_formula in
  let pr_out = pr_list string_of_action_wt_res in
  Debug.no_4 "process_one_match_accfold" 
      (add_str "match_res" pr_mr) (add_str "lhs_h" pr_h) 
      (add_str "lhs_p" pr_p) (add_str "rhs_p" pr_p) pr_out
      (fun _ _ _ _ -> process_one_match_accfold_x prog mt_res lhs_h lhs_p rhs_p)
      mt_res lhs_h lhs_p rhs_p


and process_one_match prog estate lhs_h lhs_p conseq is_normalizing
    (mt_res:match_res) (rhs_node,rhs_rest,rhs_p) reqset
    :action_wt =
  let pr_mr = string_of_match_res in
  let pr_h = !CF.print_h_formula in
  let pr_p = !MCP.print_mix_formula in
  let pr_out = string_of_action_wt_res0 in
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 es = (pr_option Cprinter.string_of_mix_formula) es.es_folding_conseq_pure in
  Debug.no_7 "process_one_match" 
      (add_str "match_res" pr_mr) (add_str "lhs_h" pr_h) (add_str "lhs_p" pr_p)
      (add_str "rhs_node" pr_h) (add_str "rhs_rest" pr_h) (add_str "rhs_p" pr_p)
      (pr_pair pr1 pr2) pr_out
      (fun _ _ _ _ _ _ _ -> process_one_match_x prog estate lhs_h lhs_p conseq is_normalizing
                          mt_res (rhs_node,rhs_rest,rhs_p) reqset)
      mt_res lhs_h lhs_p rhs_node rhs_rest rhs_p (reqset, estate)

and process_one_match_x prog estate lhs_h lhs_p rhs is_normalizing (m_res:match_res) (rhs_node,rhs_rest,rhs_p) reqset
    : action_wt =
  let pr_debug s = x_tinfo_pp s no_pos in
  let pr_hdebug h a = x_tinfo_hp h a no_pos in
  let rhs_node = m_res.match_res_rhs_node in
  let lhs_node = m_res.match_res_lhs_node in
  let rhs_vperm_set = CF.get_vperm_set rhs in

  (*Normalize false --> split
    Normalize true --> combine/normalize
  *)
  let filter_norm_lemmas l = List.filter (fun c -> 
      match c.coercion_case with 
        | Normalize b -> 
            (* For fractional permission (e.g. in ParaHIP),              *)
            (* also filter out SPLIT formula.                            *)
            (* Current heuristic is to decide SPLIT or MATCH when MATCH. *)
            (* VPerm: Always apply lemma_split when ann_vp *)
            if !Globals.ho_always_split && not b then true
            else
              let b = 
                if (!Globals.perm = Frac) || (!Globals.perm = Bperm)
                then not b else b 
              in
              if b || !use_split_match then false else true 
        | _ -> true) l
  in
  let r = match m_res.match_res_type with 
    | Root ->
          let view_decls = prog.prog_view_decls in
          (match lhs_node, rhs_node with
            | ThreadNode ({CF.h_formula_thread_original = dl_orig;
                         CF.h_formula_thread_origins = dl_origins;
                         CF.h_formula_thread_derv = dl_derv;
                         CF.h_formula_thread_name = dl_name;
                        }),
              ThreadNode ({CF.h_formula_thread_original = dr_orig;
                         CF.h_formula_thread_origins = dr_origins;
                         CF.h_formula_thread_derv = dr_derv;
                         CF.h_formula_thread_split = dr_split;
                         CF.h_formula_thread_name = dr_name;
                        })
	        (** ThreadNode is treated in a similar way to DataNode *)
            | DataNode ({CF.h_formula_data_original = dl_orig;
                         CF.h_formula_data_origins = dl_origins;
                         CF.h_formula_data_derv = dl_derv;
                         CF.h_formula_data_name = dl_name;
                        }),
              DataNode ({CF.h_formula_data_original = dr_orig;
                         CF.h_formula_data_origins = dr_origins;
                         CF.h_formula_data_derv = dr_derv;
                         CF.h_formula_data_split = dr_split;
                         CF.h_formula_data_name = dr_name;
                        }) -> 
		  (**TO CHECK: follow view nodes *)
                  pr_debug "DATA vs DATA\n";
                  let dl_flag, dr_flag = 
                    if !ann_derv then
                      (not(dl_derv)),(not(dr_derv))
                    else
                      dl_orig,dr_orig
                  in
                  let l2 =
                    if ((String.compare dl_name dr_name)==0 && 
                        ((dl_flag==false && (dl_origins!=[])) 
                        || ((dr_flag==false && dr_origins!=[])))) then [(0,M_match m_res)] (*force a MATCH after each lemma*)
                    else 
                      if (String.compare dl_name dr_name)==0 
                      then 
                        (* temp change to 0 to give fold higher priority *)
                        [(1,M_match m_res)]
                      else [(1,M_Nothing_to_do ("no proper match (type error) found for: "^(string_of_match_res m_res)))]
                  in
		  let l2 = if !perm=Dperm && !use_split_match && not !consume_all then (1,M_split_match m_res)::l2 else l2 in
                  (*apply lemmas on data nodes*)
                  (* using || results in some repeated answers but still terminates *)
                  (*let dl_new_orig = if !ann_derv then not(dl_derv) else dl_orig in*)
                  let flag = 
                    if !ann_derv 
                    then (not(dl_derv) && not(dr_derv)) 
                    else (dl_orig || dr_orig)
                  in
                  let l3 = if flag
                  then 
                    begin
                      (* WN_all_lemma - is this overriding of lemmas? *)
                      let left_ls = filter_norm_lemmas(look_up_coercion_with_target (Lem_store.all_lemma # get_left_coercion) (*prog.prog_left_coercions*) dl_name dr_name) in
                      let left_ls =
                        if (dr_split = SPLIT0) then
                        (*do not split --> not apply lemma_split *)
                          List.filter (fun c -> c.coercion_kind != LEM_SPLIT) left_ls
                        else left_ls
                      in
                      let right_ls = filter_norm_lemmas(look_up_coercion_with_target (Lem_store.all_lemma # get_right_coercion) (*prog.prog_right_coercions*) dr_name dl_name) in
                      let left_act = List.map (fun l -> (1,M_lemma (m_res,Some l))) left_ls in
                      let right_act = List.map (fun l -> (1,M_lemma (m_res,Some l))) right_ls in
                      if (left_act==[] && right_act==[]) then [] (* [(1,M_lemma (c,None))] *) (* only targetted lemma *)
                      else left_act@right_act
                    end
                  else [] in
                  let src = (-1,Search_action (l2@l3)) in
                  src
            | HVar _, HVar _ -> (1, M_match m_res)
            | ViewNode vl, ViewNode vr -> 
                pr_debug "VIEW vs VIEW\n";
                (* let l1 = [(1,M_base_case_unfold m_res)] in *)
                let vl_name = vl.h_formula_view_name in
                let vr_name = vr.h_formula_view_name in
                let vl_vdef = look_up_view_def_raw 14 view_decls vl_name in
                let vr_vdef = look_up_view_def_raw 14 view_decls vr_name in
                let vl_is_rec = vl_vdef.view_is_rec in
                let vl_is_prim = vl_vdef.view_is_prim in
                let vr_is_rec = vr_vdef.view_is_rec in
                let vl_self_pts = vl_vdef.view_pt_by_self in
                let vr_self_pts = vr_vdef.view_pt_by_self in
                let vl_view_orig = vl.h_formula_view_original in
                let vr_view_orig = vr.h_formula_view_original in
                let vl_view_origs = vl.h_formula_view_origins in
                let vr_view_origs = vr.h_formula_view_origins in
                let vl_view_derv =  vl.h_formula_view_derv in
                let vr_view_derv = vr.h_formula_view_derv in
                let vr_view_split = vr.h_formula_view_split in
                let () = Debug.ninfo_hprint (add_str "cyclic " pr_id) " 1" no_pos in
                let () = Debug.ninfo_hprint (add_str "vl_name: " pr_id) vl_name no_pos in
                let () = Debug.ninfo_hprint (add_str "vr_name: " pr_id) vr_name no_pos in
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
                let s_eq = (String.compare vl_name vr_name)==0 in
                let vl_b = vl_view_origs!=[] in
                let vr_b = vr_view_origs!=[] in
                let flag = (s_eq && 
                      ((vl_view_orig==false && vl_b) 
                      || ((vr_view_orig==false && vr_b)))) in
                let () = Debug.ninfo_hprint (add_str "force_match" string_of_bool) flag no_pos in
                let () = Debug.ninfo_hprint (add_str "s_eq" string_of_bool) s_eq no_pos in
                let () = Debug.ninfo_hprint (add_str "vl_b" string_of_bool) vl_b no_pos in
                let () = Debug.ninfo_hprint (add_str "vr_b" string_of_bool) vr_b no_pos in
                let () = Debug.ninfo_hprint (add_str "vl_view_orig" string_of_bool) vl_view_orig no_pos in
                let () = Debug.ninfo_hprint (add_str "vr_view_orig" string_of_bool) vr_view_orig no_pos in
                let () = Debug.ninfo_hprint (add_str "vr_view_derv" string_of_bool) vr_view_derv no_pos in
                let flag_lem = (
                  if !ann_derv then (not(vl_view_derv) && not(vr_view_derv)) 
                    (* else (vl_view_orig || vr_view_orig) *)
                  else
                    (*only apply a SPLIT lemma to a lock
                      if both sides are original*)
                    (* if (is_l_lock) then *)
                    (*   (vl_view_orig && vr_view_orig) *)
                    (*if RHS is original --> SPLIT*)
                    if (is_l_lock && is_r_lock && vr_view_orig) then true
                    else if (is_l_lock && is_r_lock && not vr_view_orig) then false
                    else (vl_view_orig || vr_view_orig)
                ) in
                let vl_new_orig = if !ann_derv then not(vl_view_derv) else vl_view_orig in
                let vr_new_orig = if !ann_derv then not(vr_view_derv) else vr_view_orig in
                let () = Debug.ninfo_hprint (add_str "vl_new_orig" string_of_bool) vl_new_orig no_pos in
                let () = Debug.ninfo_hprint (add_str "vr_new_orig" string_of_bool) vr_new_orig no_pos in
                let seg_fold_type = 
                  if !Globals.seg_fold then 
                    (Cfutil.is_seg_view2_fold_form prog vl estate.CF.es_formula vr rhs reqset estate.es_folding_conseq_pure) 
                  else -1
                in
                let l2, syn_lem_typ = (
                     let new_orig = if !ann_derv then not(vl.h_formula_view_derv) else vl.h_formula_view_original in
                     let uf_i = if new_orig then 0 else 1 in
                     let syn_lem_typ = if seg_fold_type>=0 then -1 else CFU.need_cycle_checkpoint prog vl estate.CF.es_formula vr rhs reqset in
                     if flag then
                       [(0,M_match m_res)],-1 (*force a MATCH after each lemma*)
                     else
                       let a1 = (2,M_base_case_unfold m_res) in
                       (*gen tail-rec <-> non_tail_rec: but only ONE lemma_tail_rec_count *)
                       (* todo: check exist tail-rec <-> non_tail_rec ?? instead of lemma_tail_rec_count *)
                       let a2 = (
                           if (syn_lem_typ = 3 && !Globals.lemma_tail_rec_count = 0) ||
                             (check_lemma_not_exist vl vr && (syn_lem_typ != -1)) then
                               let a21 = (1,M_match m_res) in
                               let () = Globals.lemma_tail_rec_count := !Globals.lemma_tail_rec_count + 1 in
                               let a22 = (1,M_cyclic (m_res,uf_i, 0, syn_lem_typ, None)) in
                               (* (1,Cond_action [a21;a22]) *) a22
                           else
                            let split_act = 
                              if (vr_view_split=SPLIT1) || !Globals.ho_always_split then
                                (* SPLIT only, no match *)
                                let lem_split = search_lemma_candidates prog flag_lem ann_derv vr_view_split
                                  (vl_view_origs,vr_view_origs) (vl_new_orig,vr_new_orig) (vl_name,vr_name) 
                                  m_res estate.CF.es_formula rhs reqset 
                                in
                                if lem_split = [] then None
                                else Some (1, M_Nothing_to_do ("to lemma_split: LHS:"^(vl_name)^" and RHS: "^(vr_name)))
                              else None
                            in
                            match split_act with
                            | Some a -> a
                            | None ->
                               (*allow matching*)
                               let m_act = (1,M_match m_res) in
                             (* (1,Search_action [m_act; (1, M_Nothing_to_do ("to fold: LHS:"^(vl_name)^" and RHS: "^(vr_name)))]) *)
                             if !Globals.seg_fold then (
                                  let seg_acts = if seg_fold_type>= 0 then
                                    [(1, M_seg_fold (m_res, seg_fold_type))]
                                  else
                                    (* [(1, M_Nothing_to_do ("to fold: LHS:"^(vl_name)^" and RHS: "^(vr_name)))] *)
                                    []
                                  in
                                  (1,Cond_action ([m_act]@seg_acts))
                             )
                             else
                               m_act
                       ) in
                       let a2 = if !perm=Dperm && !use_split_match && not !consume_all then (1,Search_action [a2;(1,M_split_match m_res)]) else a2 in
                    let a3 = (
                      (*Do not fold/unfold LOCKs, only match*)
                      if (is_l_lock || is_r_lock) then Some a2 else 
                        if (String.compare vl_name vr_name)==0 then Some (if !dis_base_case_unfold then a2 else (1, Cond_action [a1;a2]))
                        else None
                    ) in
                    let a4 = (
                      (*Do not fold/unfold LOCKs*)
                      if (is_l_lock || is_r_lock) then None else 
                        if not(vl_is_rec) && not(vl_is_prim) then Some (2,M_unfold (m_res,0))
                        else if not(vr_is_rec) && not(vl_is_prim) then Some (2,M_fold m_res) 
                        else None
                    ) in
                    let a5 = (
                      if a4==None then
                        begin
                          let l1 =
                            (*Do not fold/unfold LOCKs*)
                            if (is_l_lock) then [] else 
                              if (vl_view_orig && vr_view_orig && en_self_fold && Gen.BList.mem_eq (=) vl_name vr_self_pts) 
                              then  [(2,M_fold m_res)] 
                              else [] in
                          let l2 =
                            (*Do not fold/unfold LOCKs*)
                            if (is_r_lock) then [] else
                              if (vl_view_orig && vr_view_orig && en_self_fold && Gen.BList.mem_eq (=) vr_name vl_self_pts) 
                              then [(2,M_unfold (m_res,0))]
                              else [] in
                          let l = l1@l2 in
                          if l=[] then None
                          else Some (2,Cond_action l) 
                        end
                      else a4 
                    ) in
                    let a6 = (
                      match a3 with 
                        | None -> a5
                        | Some a1 -> 
                              if not(a4==None) then a3
                              else 
                                match a5 with
                                  | None -> a3
                                  | Some a2 -> Some (1,Cond_action [a2; a1]) 
                    ) in
                    let a7 =
                        if (!Globals.smart_lem_search ) then
                          let lem_act = search_lemma_candidates prog flag_lem ann_derv vr_view_split 
                            (vl_view_origs,vr_view_origs) (vl_new_orig,vr_new_orig) (vl_name,vr_name) m_res estate.CF.es_formula rhs reqset in
                          if lem_act = [] then a6 else
                            match a6 with
                              | Some a ->  Some (1, Cond_action ([a]@lem_act))
                              | None   -> if List.length lem_act > 0 then Some (1, Cond_action (lem_act)) else None
                        else a6
                    in
                    match a6 with
                      | Some a -> [a],syn_lem_typ
                      | None -> let () = Debug.ninfo_hprint (add_str "cyclic " pr_id) " 2" no_pos in
                        (* TO m_resHECK : MUST ensure not fold/unfold LOCKs*)
                        (* let () = Debug.ninfo_hprint (add_str "xxxx" pr_id) "4"  no_pos in *)
                        (* let lst=[(1,M_base_case_unfold m_res);(1,M_Nothing_to_do ("mis-matched LHS:"^(vl_name)^" and RHS: "^(vr_name)))] in *)
                        (*cyclic: add lemma_unsafe then unfold lhs*)
                        (*L2: change here for cyclic*)
                        let lst=
                              let syn_lem_typ = if seg_fold_type>=0 then -1 else CFU.need_cycle_checkpoint prog vl estate.CF.es_formula vr rhs reqset in
                              if check_lemma_not_exist vl vr && (syn_lem_typ != -1) then
                                let new_orig = if !ann_derv then not(vl.h_formula_view_derv) else vl.h_formula_view_original in
                                let uf_i = if new_orig then 0 else 1 in
                                [(1,M_cyclic (m_res,uf_i,0, syn_lem_typ, None))(* ;(1,M_unfold (m_res, uf_i)) *)]
                              else
                                let acts = [(3,M_base_case_unfold m_res) (* ;(1,M_cyclic m_res) *)] in
                                (* let acts1= *)
                                (*   if !do_classic_frame_rule && (Cfutil.is_fold_form  prog vl estate.CF.es_formula vr rhs reqset) then *)
                                (*     acts@[(1, M_Nothing_to_do ("to fold: LHS:"^(vl_name)^" and RHS: "^(vr_name)))] *)
                                (*   else *)
                                (*     acts *)
                                (* in *)
                                acts
                        in
                            (*let lst = [(1,M_base_case_unfold m_res);(1,M_unmatched_rhs_data_node (rhs_node,m_res.match_res_rhs_rest))] in*)
                            (*L2: change here for cyclic*)
                            [(1,Cond_action lst)],syn_lem_typ
                ) in
                (* using || results in some repeated answers but still terminates *)
                (* let l3 = ( *)
                (*   if flag then  *)
                (*     let left_ls = filter_norm_lemmas(look_up_coercion_with_target (Lem_store.all_lemma # get_left_coercion) (\*prog.prog_left_coercions*\) vl_name vr_name) in *)
                (*     let right_ls = filter_norm_lemmas(look_up_coercion_with_target (Lem_store.all_lemma # get_right_coercion) (\*prog.prog_right_coercions*\) vr_name vl_name) in *)
                (*     let left_act = if (not(!ann_derv) || vl_new_orig) then List.map (fun l ->  *)
                (*         if (Immutable.is_lend l.Cast.coercion_body) then (1,M_lemma (m_res,Some l)) *)
                (*         else (1,M_lemma (m_res,Some l))) left_ls else [] in *)
                (*     let non_loop_candidate l = not (Gen.BList.mem_eq (fun s1 s2 -> (String.compare s1 s2 = 0)) l.Cast.coercion_name vr_view_origs)in *)
                (*     let right_act =   *)
                (*       List.fold_left (fun acc l ->  *)
                (*           if  (vr_new_orig || (non_loop_candidate l)) then *)
                (*             let prio = (\* if ((Immutable.is_lend l.Cast.coercion_body) && vr_view_orig ) then 1 else*\) 1 in  *)
                (*             acc@[(prio,M_lemma (m_res,Some l))] *)
                (*           else acc) [] right_ls *)
                (*     in *)
                (*     left_act@right_act *)
                (*   else  [] *)
                (* ) in *)
                let l3 = if seg_fold_type<0 then(* if not (!Globals.smart_lem_search) then  *)
                  search_lemma_candidates prog flag_lem ann_derv vr_view_split 
                    (vl_view_origs,vr_view_origs) (vl_new_orig,vr_new_orig) (vl_name,vr_name) m_res estate.CF.es_formula rhs reqset else [] in
                (*let l4 = 
                (* TODO WN : what is original?? *)
                (* Without it, run-fast-test of big imm runs faster while
                  * still accurate. However, it fails with
                  * imm/imm1.slk imm/imm3.slk *)
                  if get_view_original rhs_node then 
                  [(2,M_base_case_fold m_res)] 
                  else [] in*)
                (* [] in *)
                (* try accelerated folding *)
                let a = l2@l3 in
                (* let a_fold, a_rest = List.partition (fun (_,act) -> *)
                (*   match act with                                    *)
                (*   | M_fold _ -> true                                *)
                (*   | _ -> false                                      *)
                (* ) a in                                              *)
                (* try accelerated folding *)
                let a_accfold = process_one_match_accfold prog m_res lhs_h lhs_p rhs_p in
                Debug.ninfo_hprint (add_str "a_accfold length" (fun x -> string_of_int (List.length x))) a_accfold no_pos;
                Debug.ninfo_hprint (add_str "a normal length" (fun x -> string_of_int (List.length x))) a no_pos;
                (* return *)
                (* (1, norm_search_action (a_accfold@a_fold@a_rest)) *)
                (1, norm_cond_action (a_accfold@ [(1,norm_search_action a)]))
            | DataNode dl, ViewNode vr -> 
                pr_debug "DATA vs VIEW\n";
                let vr_name = vr.h_formula_view_name in
                let vr_vdef = look_up_view_def_raw 15 view_decls vr_name in
                let vr_self_pts = vr_vdef.view_pt_by_self in
                let vr_view_orig = vr.h_formula_view_original in
                let vr_view_derv = vr.h_formula_view_derv in
                let dl_orig = dl.h_formula_data_original in
                let dl_derv = dl.h_formula_data_derv in
                       (* CF.h_formula_data_origins = dr_origins; *)
                (*Is it LOCKED state*)
                let is_r_lock = match vr_vdef.view_inv_lock with
                  | Some _ -> true
                  | None -> false
                in
                let new_orig_r = if !ann_derv then not(vr_view_derv) else vr_view_orig in
                let new_orig_l = if !ann_derv then not(dl_derv) else dl_orig in
                let sub_ann  = if (!Globals.allow_field_ann) then 
                  let r,_,_,_ = Immutable.subtype_ann_list [] [] dl.h_formula_data_param_imm (CP.annot_arg_to_imm_ann_list (get_node_annot_args rhs_node)) in
                  let isAccs  = Immutable.isAccsList dl.h_formula_data_param_imm in
                  r && not(isAccs)
                else true in
                (* let right_ls = look_up_coercion_with_target prog.prog_right_coercions vr_name dl.h_formula_data_name in *)
                (* let a1 = if (new_orig || vr_self_pts==[]) then [(1,M_fold m_res)] else [] in *)
                let () = Debug.ninfo_hprint (add_str "new_orig_r" string_of_bool) new_orig_r no_pos in
                let () = Debug.ninfo_hprint (add_str "vr_view_derv" string_of_bool) vr_view_derv no_pos in
                let () = Debug.ninfo_hprint (add_str "vr_view_orig" string_of_bool) vr_view_orig no_pos in
                let () = Debug.ninfo_hprint (add_str "!ann_derv" string_of_bool) !ann_derv no_pos in
                let seg_fold_type = if !Globals.seg_fold then
                  (Cfutil.is_seg_view_br_fold_form prog dl estate.CF.es_formula vr rhs reqset estate.CF.es_folding_conseq_pure)
                else gen_lemma_action_invalid
                in
                let a1 = (
                  if is_r_lock then [] else
                    if ((new_orig_r || vr_self_pts==[]) && sub_ann) then
                      let () = Debug.ninfo_hprint (add_str "cyclic " pr_id) " 3" no_pos in
                      let () = x_tinfo_hp (add_str "cyclic:add_checkpoint" pr_id) "fold" no_pos in
                      let syn_lem_typ = if seg_fold_type >= 0 then gen_lemma_action_invalid else
                        CFU.need_cycle_checkpoint_fold prog dl estate.CF.es_formula vr rhs reqset in
                       if (syn_lem_typ != gen_lemma_action_invalid) then
                         let acts =
                           if (CFU.get_shortest_length_base (List.map fst vr_vdef.view_un_struc_formula)
                               vr_name) >0 then
                             (*find the first viewnode readable from left datanode*)
                             let lvs = CF.look_up_reachable_first_reachable_view prog
                               (CF.formula_of_heap lhs_h no_pos) [dl.CF.h_formula_data_node] in
                             let uf_i = if new_orig_r then 0 else 1 in
                             if lvs = [] then
                               [(1,M_fold m_res)]
                             else
                               let vl = List.hd lvs in
                               if syn_lem_typ=3 || (syn_lem_typ=1 && check_lemma_not_exist vl vr) then
                                 let new_orig_r = if !ann_derv then not(vl.h_formula_view_derv) else vl.h_formula_view_original in
                                 (* let new_c = {c with match_res_lhs_node = CF.ViewNode vl} in *)
                                 let unfold_view_opt = if syn_lem_typ = 3 then
                                   None
                                 else Some (CF.ViewNode vl)
                                 in
                                 [(1,M_cyclic( m_res, uf_i, 0, syn_lem_typ, unfold_view_opt))]
                               else [(1,M_fold m_res)]
                           else
                              let () = Debug.ninfo_hprint (add_str "cyclic:add_checkpoint" pr_id) "fold 3" no_pos in
                             let cyc_tail_rec_lemmas=
                               if syn_lem_typ=3 then
                                 let uf_i = if new_orig_r then 0 else 1 in
                                 [(1,M_cyclic( m_res, uf_i, 0, syn_lem_typ, None))]
                               else []
                             in
                             cyc_tail_rec_lemmas@[(1,M_fold m_res)]
                         in
                         acts
                       else
                         (* fold to activate/change  *)
                         [(1,M_fold m_res)]
                    else []
                ) in
                (* WN : what is M_rd_lemma for?? *)
                (* WN : why do we apply lemma blindly here!! *)
                (* leads to unsoundness of sh-rev3a.slk *)
                (* ==========andreea: a naive fix for left compelx lemma -- to be refined ========== *)
                let a3 = (
                  let right_ls = filter_norm_lemmas (look_up_coercion_with_target (Lem_store.all_lemma # get_right_coercion)
                      vr_name dl.h_formula_data_name) in
                  let left_ls = filter_norm_lemmas (look_up_coercion_with_target (Lem_store.all_lemma # get_left_coercion)
                      dl.h_formula_data_name vr_name) in
                  (* for left lemmas, only a complex one might trigger a match data --> view *)
                  let left_ls = filter_lemmas_by_kind left_ls Complex in 
                  (* let right_act = if (not(!ann_derv) || dl.h_formula_data_original) then  *)
                  let left_act  = if (not(!ann_derv) || new_orig_l) then List.map (fun l -> (1,M_lemma (m_res,Some l))) left_ls else [] in
                  let right_act = if (not(!ann_derv) || new_orig_r) then List.map (fun l -> (1,M_lemma (m_res,Some l))) right_ls else [] in
                  left_act@right_act 
                ) in
                (* ==================== *)
                let r_lem =
                  if (Lem_store.all_lemma # any_coercion
                  && !Globals.allow_rd_lemma)
                  then
                    [
                        (1,M_rd_lemma m_res)
                    ]
                  else [] in
                let a2 = if (new_orig_r) then r_lem else [] in
                (* let a2 = if (new_orig) then [(1,M_rd_lemma m_res)] else [] in *)
                let seg_acts = 
                   if !Globals.seg_fold then
                     if seg_fold_type>= 0 then
                       [(1, M_seg_fold (m_res, seg_fold_type))]
                     else []
                   else []
                in
                let a = a1@seg_acts@a2@a3 in
                (* let a_fold, a_rest = List.partition (fun (_,act) -> *)
                (*   match act with                                    *)
                (*   | M_fold _ -> true                                *)
                (*   | _ -> false                                      *)
                (* ) a in                                              *)
                (* try accelerated folding *)
                let a_accfold = process_one_match_accfold prog m_res lhs_h lhs_p rhs_p in
                Debug.ninfo_hprint (add_str "a_accfold length" (fun x -> string_of_int (List.length x))) a_accfold no_pos;
                Debug.ninfo_hprint (add_str "a normal length" (fun x -> string_of_int (List.length x))) a no_pos;
                (* return *)
                (* (1, norm_search_action (a_accfold@a_fold@a_rest)) *)
                (1, norm_cond_action (a_accfold@ [(1,norm_search_action a)]))
            | ViewNode vl, DataNode dr -> 
                  pr_debug "VIEW vs DATA\n";
                  let vl_name = vl.h_formula_view_name in
                  let vl_vdef = look_up_view_def_raw 16 view_decls vl_name in
                  let vl_self_pts = vl_vdef.view_pt_by_self in
                  let vl_view_orig = vl.h_formula_view_original in
                  let vl_view_derv = vl.h_formula_view_derv in
                  let dr_orig = dr.h_formula_data_original in
                  let dr_derv = dr.h_formula_data_derv in
                  let () = pr_debug "pred<..> |- node<..>" in
                  (*Is it LOCKED state*)
                  let is_l_lock = match vl_vdef.view_inv_lock with
                    | Some _ -> true
                    | None -> false
                  in
                  let () = Debug.ninfo_hprint (add_str "cyclic " pr_id) " 4" no_pos in
                  let new_orig_l = if !ann_derv then not(vl_view_derv) else vl_view_orig in
                  let new_orig_r = if !ann_derv then not(dr_derv) else dr_orig in
                  let uf_i = if new_orig_l then 0 else 1 in
                  (* WN_all_lemma - is this overriding of lemmas? *)
                  (* let left_ls = filter_norm_lemmas (look_up_coercion_with_target (Lem_store.all_lemma # get_left_coercion)(\*prog.prog_left_coercions*\) vl_name dr.h_formula_data_name) in *)
                  (* let a1 = if (new_orig || vl_self_pts==[]) then [(1,M_unfold (m_res,uf_i))] else [] in *)
                  (* let () = pr_hdebug (add_str "left_ls" (pr_list pr_none)) left_ls in *)
                  let sub_ann  = if (!Globals.allow_field_ann) then 
                    let r,_,_,_ = Immutable.subtype_ann_list [] []  (CP.annot_arg_to_imm_ann_list (get_node_annot_args lhs_node)) dr.h_formula_data_param_imm in
                    r
                  else true in
                  let a1 = 
                    if is_l_lock then [] else
                      if ((new_orig_l || vl_self_pts==[]) && sub_ann) then 
                      (*then [(1,M_unfold (m_res,uf_i))] else [] in*)
                        if vl_vdef.view_is_prim then []
                        else
                          (*cyclic checkpoint here*)
                          let syn_lem_typ = CFU.need_cycle_checkpoint_unfold prog vl estate.CF.es_formula dr rhs reqset in
                          if syn_lem_typ =3 || (syn_lem_typ != -1 && not (Cfutil.poss_prune_pred prog vl estate.CF.es_formula)) then
                            (*find the first viewnode readable from right datanode*)
                               let lvs = CF.look_up_reachable_first_reachable_view prog
                                 rhs [dr.CF.h_formula_data_node] in
                               if lvs = [] then [(1,M_unfold (m_res,uf_i))] else
                                 [(1,M_cyclic( m_res, uf_i, 0, syn_lem_typ, None))]
                          else
                          [(1,M_unfold (m_res,uf_i))] 
                      else [] in
                  (* let a2_syn = if (new_orig_l & left_ls!=[]) then [(1,M_lemma (m_res,Some (List.hd left_ls)))] else [] in *)

                  let a2 =
                    let left_ls = filter_norm_lemmas (look_up_coercion_with_target (Lem_store.all_lemma # get_left_coercion)
                        vl_name dr.h_formula_data_name) in
                    let left_act  = if (not(!ann_derv) || new_orig_l) then List.map (fun l -> (1,M_lemma (m_res,Some l))) left_ls else [] in
                    left_act in
                    (* ==================== *)
                  (* if (left_ls == [] && (vl_view_orig ) then ua *)
                  (* else (1,M_lemma (m_res,Some (List.hd left_ls))) *)
                  let a = a1@a2 in
                  if a!=[] then (-1,Search_action a)
                    (* if (vl_view_orig || vl_self_pts==[]) then ua *)
                    (* else if (left_ls != []) then (1,M_lemma (m_res,Some (List.hd left_ls))) *)
                  else (1,M_Nothing_to_do ("matching data with deriv self-rec LHS node "^(string_of_match_res m_res)))
            | ViewNode vl, HRel (h_name, args, _) -> (* cant it reach this branch? *)
                  pr_debug "VIEW vs HREL\n";
                  let h_name = Cpure.name_of_spec_var h_name in
                  let vl_name = vl.h_formula_view_name in

                  let left_ls = filter_norm_lemmas(look_up_coercion_with_target (Lem_store.all_lemma # get_left_coercion) vl_name h_name) in
                  let right_ls = filter_norm_lemmas(look_up_coercion_with_target (Lem_store.all_lemma # get_right_coercion) h_name vl_name) in
                  let left_act = List.map (fun l -> (1,M_lemma (m_res,Some l))) left_ls in
                  let right_act = List.map (fun l -> (1,M_lemma (m_res,Some l))) right_ls in
                  let l = left_act@right_act in
                  let res = 
                    match l with
                      | []     -> (1, M_Nothing_to_do (string_of_match_res m_res)) (* nothing to do or infer? *)
                      | l1::[] -> l1
                      | _      -> (-1, norm_search_action l)
                  in res
            | DataNode _,  HRel _
            | HRel _, _            -> (1,M_Nothing_to_do (string_of_match_res m_res))
            | _ -> report_error no_pos "process_one_match unexpected formulas 1\n"	
          )
    | MaterializedArg (mv,ms) ->
          let () = pr_debug "materialized args  analysis here!" in  
          let uf_i = 
            if mv.mater_full_flag 
            then (pr_debug "FULL" ;0) 
            else (pr_debug "PARTIAL";1) 
          in 
          (* let uf_i = 1 in *)
          (match lhs_node,rhs_node with
            | DataNode dl, _ -> (1,M_Nothing_to_do ("matching lhs: "^(string_of_h_formula lhs_node)^" with rhs: "^(string_of_h_formula rhs_node)))
            | ThreadNode dt, _ -> (1,M_Nothing_to_do ("matching lhs: "^(string_of_h_formula lhs_node)^" with rhs: "^(string_of_h_formula rhs_node)))
            | ViewNode vl, ViewNode vr ->
                  let vl_name = vl.h_formula_view_name in
                  let vr_name = vr.h_formula_view_name in
                  let vl_view_orig = vl.h_formula_view_original in
                  let vr_view_orig = vr.h_formula_view_original in
                  let vl_view_origs = vl.h_formula_view_origins in
                  let vr_view_origs = vr.h_formula_view_origins in
                  let s_eq = (String.compare vl_name vr_name)==0 in
                  let vl_b = vl_view_origs!=[] in
                  let vr_b = vr_view_origs!=[] in
                  let flag = (s_eq && 
                      ((vl_view_orig==false && vl_b) 
                      || ((vr_view_orig==false && vr_b)))) in
                  if flag then
                    (0,M_match m_res) (*force a MATCH after each lemma*)
                  else
                  let a1 = (match ms with
                    | View_mater -> 
                          let () = pr_debug "unfold for meterialised!\n" in  
                          M_unfold (m_res,uf_i) (* uf_i to prevent infinite unfolding *)
                    | Coerc_mater s -> 
                          let () = pr_debug "selected lemma XX\n" in  
                          M_lemma (m_res,Some s)) in
                  let l1 = if !dis_base_case_unfold then  [] else [(4,M_base_case_unfold m_res)] in
                  (-1, (Search_action ((1,a1)::l1)))
            | HRel (h_name, _, _), ViewNode vl ->
                  let h_name = Cpure.name_of_spec_var h_name in
                  let vl_name = vl.h_formula_view_name in
                  let alternative = process_infer_heap_match ~vperm_set:rhs_vperm_set prog estate lhs_h lhs_p is_normalizing rhs reqset (rhs_node,rhs_rest) in
                  process_one_match_mater_unk_w_view h_name vl_name m_res ms alternative 
            | ViewNode vl, HRel (h_name, _, _) ->
                  let h_name = Cpure.name_of_spec_var h_name in
                  let vl_name = vl.h_formula_view_name in
                  let alternative = process_infer_heap_match ~vperm_set:rhs_vperm_set prog estate lhs_h lhs_p is_normalizing rhs reqset (rhs_node,rhs_rest) in
                  process_one_match_mater_unk_w_view vl_name h_name m_res ms alternative 
            | ViewNode vl, DataNode dr ->
                  let () = pr_hdebug (add_str "cyclic " pr_id) " 5" in
                  let () = pr_debug "try LHS case analysis here!\n" in
                  (* let i = if mv.mater_full_flag then 0 else 1 in  *)
                  (* let a1 = (match ms with *)
                  (*   | View_mater -> (1,M_unfold (m_res,uf_i))  *)
                  (*   | Coerc_mater s -> (1,M_lemma (m_res,Some s))) in *)
                  let lhs_case_flag = vl.h_formula_view_lhs_case in
                  (* let () = print_string ("process_one_match_x:"  *)
                  (*                       ^ "### lhs_case_flag = " ^ (string_of_bool lhs_case_flag) *)
                  (*                       ^ "\n\n" )in *)
                  let a2 = 
                    (match ms with
                      | View_mater -> (uf_i,M_unfold (m_res,uf_i))
                      | Coerc_mater s -> (* (uf_i,M_lemma (m_res,Some s))) in *)
                            (1,M_lemma (m_res,Some s))) in
                  (* WHY do we need LHS_CASE_ANALYSIS? *)
                  let vdef = x_add C.look_up_view_def_raw 43 prog.C.prog_view_decls vl.CF.h_formula_view_name in
                  let lem_infer_opt = CFU.check_seg_split_pred prog estate.CF.es_formula vdef vl dr in
                  let a1 = if !Globals.lemma_syn && lem_infer_opt !=None then
                    let () = DD.ninfo_hprint (add_str "infer lemma" pr_id) "1" no_pos in
                    (1,M_cyclic (m_res,uf_i, 0, 2, None))
                  else
                    if (lhs_case_flag=true && !Globals.lhs_case_flag) then
                      let l1 = [(1,M_lhs_case m_res)] 
                      in
                      if !Globals.lhs_case_search_flag 
                      then 
                        let () = pr_debug "Sel (search) 1" in
                        (-1, (Search_action (a2::l1)))
                      else 
                        let () = pr_debug "Sel (cond) 2" in
                        (-1, (Cond_action (a2::l1)))
                    else
                      let () = pr_debug ("Sel (cond) 3:"^(string_of_int uf_i)) in
                      let l1 = if !dis_base_case_unfold then [] else [(5,M_base_case_unfold m_res)] in
                      (* (-1, (Search_action (a2::l1))) *)
                      (5, (Cond_action (a2::l1)))
                  in a1
            | HRel _, _ -> (1,M_Nothing_to_do ("matching lhs: "^(string_of_h_formula lhs_node)^" with rhs: "^(string_of_h_formula rhs_node)))
            | _ -> report_error no_pos "process_one_match unexpected formulas 2\n"	
          )
    | WArg -> begin
        (***************************************************)
        let () = pr_debug "WArg  analysis here!\n" in
        let () = Debug.ninfo_hprint (add_str "xxx" pr_id) "WArg  analysis here" no_pos in
        (* let view_decls = prog.prog_view_decls in *)
        (* match lhs_node,rhs_node with *)
        (*   | ViewNode vl, DataNode dr -> *)
        (* (1,M_Nothing_to_do (string_of_match_res m_res)) *)
        (*   | _ -> (1,M_Nothing_to_do (string_of_match_res m_res)) *)
                (***************************************************)
                (***************************************************)
                (1,M_Nothing_to_do (string_of_match_res m_res))
    end
    | Wand -> (*let _ = (print_endline"eliminate wand") in *)
               if (Lem_store.all_lemma # any_coercion) then (1,M_ramify_lemma m_res)
               else (1,M_Nothing_to_do (string_of_match_res m_res))
  in

  let r1 = match m_res.match_res_type with 
      (*Used when normalizing. MATCH only*)
    | Root ->
          (match lhs_node,rhs_node with
            | DataNode dl, DataNode dr -> 
                  if ((String.compare dl.h_formula_data_name dr.h_formula_data_name)==0) 
                  then (0,M_match m_res)
                  else  (1,M_Nothing_to_do (string_of_match_res m_res))
            | ThreadNode dl, ThreadNode dr -> 
                  if ((String.compare dl.h_formula_thread_name dr.h_formula_thread_name)==0) 
                  then (0,M_match m_res)
                  else  (1,M_Nothing_to_do (string_of_match_res m_res))
            | ViewNode vl, ViewNode vr -> 
                  if ((String.compare vl.h_formula_view_name vr.h_formula_view_name)==0) 
                  then (0,M_match m_res)
                  else  (1,M_Nothing_to_do (string_of_match_res m_res))
            | HVar _, HVar _ -> (0, M_match m_res)
            | DataNode dl, ViewNode vr -> (1,M_Nothing_to_do (string_of_match_res m_res))
            | ViewNode vl, DataNode dr -> (1,M_Nothing_to_do (string_of_match_res m_res))
            | _, ViewNode vr -> (1,M_Nothing_to_do (string_of_match_res m_res))
            | ViewNode _, HRel _ 
            | DataNode _, HRel _ 
            | HRel _, _            ->(1,M_Nothing_to_do (string_of_match_res m_res))
            | _ -> report_error no_pos "process_one_match unexpected formulas 3\n"	              )
    | MaterializedArg (mv,ms) -> 
          (*??? expect MATCHING only when normalizing => this situation does not need to be handled*)
          (* let () = print_string ("\n [context.ml] Warning: process_one_match not support Materialized Arg when normalizing\n") in *)
          (1,M_Nothing_to_do (string_of_match_res m_res))
    | WArg -> (1,M_Nothing_to_do (string_of_match_res m_res)) 
    | Wand -> (1,M_Nothing_to_do (string_of_match_res m_res)) in
  (*if in normalizing process => choose r1, otherwise, r*)
  if (is_normalizing) then r1
  else r


and process_infer_heap_match ?(vperm_set=CVP.empty_vperm_sets) prog estate lhs_h lhs_p is_normalizing rhs reqset (rhs_node,rhs_rest) =
  let r0 = (2,M_unmatched_rhs_data_node (rhs_node,rhs_rest,vperm_set)) in
  let ptr_vs = estate.es_infer_vars in
  let ptr_vs = List.filter (fun v -> CP.is_otype(CP.type_of_spec_var v)) ptr_vs in
  (* let () = DD.info_zprint  (lazy  ("  estate.es_infer_vars_hp_rel: " ^ (!CP.print_svl estate.es_infer_vars_hp_rel))) no_pos in *)
  let rs = 
    if estate.es_infer_vars_hp_rel==[] && ptr_vs==[] then
      (*to support lemma with unknown preds*)
      []
    else [(2,M_infer_heap (rhs_node,rhs_rest))]
  in
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
    let cyc_acts = 
      try
        let vl, vr,lhs_rest = Cfutil.find_view_match lhs_h rhs_node in
        let syn_lem_typ = CFU.need_cycle_checkpoint prog vl estate.CF.es_formula vr rhs reqset in
        let vl_name = vl.h_formula_view_name in
        let vr_name = vr.h_formula_view_name in
        let vl_vdef = look_up_view_def_raw 24 prog.Cast.prog_view_decls vl_name in
        let vr_vdef = look_up_view_def_raw 24 prog.Cast.prog_view_decls vr_name in
        let vl_is_rec = vl_vdef.view_is_rec in
        let vl_is_prim = vl_vdef.view_is_prim in
        let vr_is_rec = vr_vdef.view_is_rec in
        let vl_self_pts = vl_vdef.view_pt_by_self in
        let vr_self_pts = vr_vdef.view_pt_by_self in
        let vl_view_orig = vl.h_formula_view_original in
        let vr_view_orig = vr.h_formula_view_original in
        let vl_view_origs = vl.h_formula_view_origins in
        let vr_view_origs = vr.h_formula_view_origins in
        let vl_view_derv =  vl.h_formula_view_derv in
        let vr_view_derv = vr.h_formula_view_derv in
        let vr_view_split = vr.h_formula_view_split in
        let m_res = { match_res_lhs_node = ViewNode vl;
        match_res_lhs_rest = lhs_rest;
        match_res_holes = [];
        match_res_type = Root;
        match_res_rhs_node = rhs_node;
        match_res_rhs_rest = rhs_rest; } in
        if check_lemma_not_exist vl vr && (syn_lem_typ != -1) then
          let new_orig = if !ann_derv then not(vl.h_formula_view_derv) else vl.h_formula_view_original in
          let uf_i = if new_orig then 0 else 1 in
          [(1,M_cyclic (m_res,uf_i, 0, syn_lem_typ, None))]
        else
          let flag_lem = (
              if !ann_derv then (not(vl_view_derv) && not(vr_view_derv)) 
              else
                (*only apply a SPLIT lemma to a lock
                  if both sides are original*)
                (* if (is_l_lock) then *)
                (*   (vl_view_orig && vr_view_orig) *)
                (*if RHS is original --> SPLIT*)
                let is_l_lock = match vl_vdef.view_inv_lock with
                  | Some _ -> true
                  | None -> false
                in
                let is_r_lock = match vr_vdef.view_inv_lock with
                  | Some _ -> true
                  | None -> false
                in
                if (is_l_lock && is_r_lock && vr_view_orig) then true
                else if (is_l_lock && is_r_lock && not vr_view_orig) then false
                else (vl_view_orig || vr_view_orig)
          ) in
          let vl_new_orig = if !ann_derv then not(vl_view_derv) else vl_view_orig in
          let vr_new_orig = if !ann_derv then not(vr_view_derv) else vr_view_orig in
          let lem_act = search_lemma_candidates prog flag_lem ann_derv vr_view_split 
            (vl_view_origs,vr_view_origs) (vl_new_orig,vr_new_orig) (vl_name,vr_name) m_res estate.CF.es_formula rhs reqset in
          if lem_act = [] then [] else
            [(1,norm_search_action lem_act)]
      with _ -> []
    in
    (* temp removal of infer-heap and base-case fold *)
    (-1, (Cond_action (rs@cyc_acts@[r;r0])))
  else (-1, Cond_action (rs@[r0]))
    (* M_Nothing_to_do ("no match found for: "^(string_of_h_formula rhs_node)) *)

and process_matches prog estate lhs_h lhs_p conseq is_normalizing reqset (((l:match_res list),(rhs_node,rhs_rest,rhs_p)) as ks) =
  let pr = Cprinter.string_of_h_formula   in
  let pr1 = pr_list string_of_match_res in
  let pr2 x = (fun (l1, (c1,c2)) -> "(" ^ (pr1 l1) ^ ",(" ^ (pr c1) ^ "," ^ (pr c2) ^ "))" ) x in
  let pr3 = string_of_action_wt_res0 in
  Debug.no_4 "process_matches" (add_str "lhs_h" pr)
      (add_str "matches" pr1)
      (add_str "rhs_node" pr) 
      (add_str "rhs_rest" pr) pr3 
      (fun _ _ _ _ -> process_matches_x prog estate lhs_h lhs_p conseq is_normalizing reqset ks) 
      lhs_h l rhs_node rhs_rest

and process_matches_x prog estate lhs_h lhs_p conseq is_normalizing reqset ((l:match_res list),(rhs_node,rhs_rest,rhs_p))= 
  let rhs_vperm_set = CF.get_vperm_set conseq in
  let () = x_tinfo_pp "**** sel_hp_rel **********************" no_pos in
  let () = x_tinfo_hp (add_str "hp_rel" Cprinter.string_of_spec_var_list) estate.es_infer_vars_hp_rel no_pos in
  let () = x_tinfo_hp (add_str "sel_hp_rel" Cprinter.string_of_spec_var_list) estate.es_infer_vars_sel_hp_rel no_pos in
  let () = x_tinfo_hp (add_str "sel_post_hp_rel" Cprinter.string_of_spec_var_list) estate.es_infer_vars_sel_post_hp_rel no_pos in
  match l with
    | [] ->  process_infer_heap_match ~vperm_set:rhs_vperm_set prog estate lhs_h lhs_p is_normalizing conseq reqset (rhs_node,rhs_rest)
          (* let r0 = (2,M_unmatched_rhs_data_node (rhs_node,rhs_rest)) in *)
          (* let ptr_vs = estate.es_infer_vars in *)
          (* let ptr_vs = List.filter (fun v -> CP.is_otype(CP.type_of_spec_var v)) ptr_vs in *)
          (* let rs =  *)
          (*   if estate.es_infer_vars_hp_rel==[] && ptr_vs==[] then [] *)
          (*   else [(2,M_infer_heap (rhs_node,rhs_rest))] in *)
          (* if (is_view rhs_node) && (get_view_original rhs_node) then *)
          (*   let r = (2, M_base_case_fold { match_res_lhs_node = HEmp; *)
          (*   match_res_lhs_rest = lhs_h; *)
          (*   match_res_holes = []; *)
          (*   match_res_type = Root; *)
          (*   match_res_rhs_node = rhs_node; *)
          (*   match_res_rhs_rest = rhs_rest; }) in  *)
          (*   (\* WN : why do we need to have a fold following a base-case fold?*\) *)
          (*   (\* changing to no_match found *\) *)
          (*   (\*(-1, Search_action [r])*\) *)
          (*   (\* let r1 = (2, M_fold { *\) *)
          (*   (\*     match_res_lhs_node = HTrue;  *\) *)
          (*   (\*     match_res_lhs_rest = lhs_h;  *\) *)
          (*   (\*     match_res_holes = []; *\) *)
          (*   (\*     match_res_type = Root; *\) *)
          (*   (\*     match_res_rhs_node = rhs_node; *\) *)
          (*   (\*     match_res_rhs_rest = rhs_rest; *\) *)
          (*   (\* }) in *\) *)
          (*   (\* temp removal of infer-heap and base-case fold *\) *)
          (*   (-1, (Cond_action (rs@[r;r0]))) *)
          (* else (-1, Cond_action (rs@[r0])) *)
            (* M_Nothing_to_do ("no match found for: "^(string_of_h_formula rhs_node)) *)
    | x::[] -> process_one_match prog estate lhs_h lhs_p conseq is_normalizing x (rhs_node,rhs_rest,rhs_p) reqset
    | _ ->  
          let rs = List.map (fun l -> process_one_match prog estate lhs_h lhs_p conseq is_normalizing l (rhs_node,rhs_rest,rhs_p) reqset) l in
          let () = x_tinfo_pp "process many matches" no_pos in
          (* WN : TODO use cond_action if of different priorities *)
          let rs = sort_wt rs in
          let () = x_tinfo_hp (pr_list string_of_action_wt_res_simpl) rs no_pos in
          (-1, Search_action rs)

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
          
and choose_match_x f ys =
  match f with
    | None -> None
    | Some a -> choose_closest a ys

and choose_match f ys = 
  let pr = pr_list_num string_of_action_wt_res in
  let pr2 = pr_option string_of_action_res in
  Debug.no_1 "choose_match" pr pr2 (choose_match_x f) ys

and sort_wt (ys: action_wt list) : action_wt list =
  let pr = pr_list string_of_action_wt_res_simpl in
  (* let pr2 = pr_list string_of_action_res in *)
  Debug.no_1 "sort_wt" pr pr sort_wt_x ys

and sort_wt_x (ys: action_wt list) : action_wt list =
  let rec uncertain (_,a) = match a with 
    | M_infer_heap _
    | M_base_case_fold _
    | M_rd_lemma _
    | M_lemma  _
    | M_ramify_lemma _
    | M_base_case_unfold _ 
    | M_unfold _
    | M_fold _
    | M_seg_fold _
    | M_acc_fold _
    | M_split_match _ 
    | M_match _ 
    | M_cyclic _
    | M_lhs_case _ -> false
    | M_Nothing_to_do _ 
    | Undefined_action _ 
    | M_unmatched_rhs_data_node _ -> true
    | Search_action l
    | Seq_action l
    | Cond_action l ->
        List.exists uncertain l  in	
  
  let rec recalibrate_wt (w,a) = 
    let pick a b = if a<b then a else b in
    match a with
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
          let rw = List.fold_left (fun a (w,_)-> pick a w) (fst (List.hd l)) (List.tl l) in
          (rw,Cond_action l)
    | Seq_action l ->
          let l = List.map recalibrate_wt l in
          let rw = List.fold_left (fun a (w,_)-> pick a w) (fst (List.hd l)) (List.tl l) in
          (rw,Seq_action l)
    | _ -> if (w == -1) then (0,a) else (w,a) in
  let ls = List.map recalibrate_wt ys in
  let sl = List.sort (fun (w1,_) (w2,_) -> if w1<w2 then -1 else if w1>w2 then 1 else 0 ) ls in
  (* WN : is below critical? why do we need them? *)
  (* let ucert, cert = List.partition uncertain sl in (\*delay uncertain*\) *)
  (* let sl = cert@ucert in *)
  (* what if after sorted, there are elements with the same priority ??? *)
  (* LDK: temporarily combine them into a Cond_action to ensure that
     the head of the list has unique weight *)
  let head_w,head_a = List.hd sl in
  let eq_ls, neq_ls = List.partition (fun (w,_) -> w==head_w) (List.tl sl) in
  let res =
    if (eq_ls == []) then
      sl
    else
      (*Use Cond_action to avoid explosion*)
      let new_head = (head_w,Cond_action ((head_w,head_a)::eq_ls)) in
      (new_head::neq_ls)
  in
  res
  (* (snd (List.split res)) *)

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

and sort_wt_match opt (ys: action_wt list) : action_wt list =
  match (choose_match opt ys) with
    | None -> sort_wt ys
    | Some a -> 
          (* let () = print_endline "WN : Found a must_action_stk match" in  *)
          [(0,a)]

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

and compute_actions_x prog estate es lhs_h lhs_p rhs_p posib_r_alias
    (rhs_lst : (CF.h_formula * CF.h_formula * MCP.mix_formula) list)
    is_normalizing conseq pos
    : action =
  let opt = 
    if not(must_action_stk # is_empty) then
      let a = must_action_stk # top in
      (must_action_stk # pop; Some a)
    else None
  in
  (* let () = print_string ("\n(andreeac) context.ml l_h:"  ^ (Cprinter.string_of_h_formula lhs_h)) in *)
  let r = List.map (fun (c1,c2,c3)->
    (choose_context prog es lhs_h lhs_p rhs_p posib_r_alias c1 c2 pos , (c1,c2,c3))
  ) rhs_lst in
  (* match r with  *)
  (*   | [] -> M_Nothing_to_do "no nodes to match" *)
  (*   | x::[]-> process_matches lhs_h x *)
  (*   | _ ->  List.hd r (\*Search_action (None,r)*\) *)
  (* let () = print_string (" compute_actions: before process_matches") in *)
  (* type: (match_res list * (Cformula.h_formula * Cformula.h_formula)) list *)
  (* Todo:Long *)
  let () = x_tinfo_hp (add_str "r_xxx" (pr_list (pr_pair (pr_list string_of_match_res) pr_none))) r no_pos in 
  let r = List.map (process_matches prog estate lhs_h lhs_p conseq is_normalizing es) r in
  match r with
    | [] -> M_Nothing_to_do "no nodes on RHS"
    | xs -> 
          (*  imm/imm1.slk imm/imm3.slk fails if sort_wt not done *)
          let () = x_tinfo_hp (add_str "weighted action" (pr_list_num 
              (string_of_action_wt_res_simpl))) r no_pos in
          let ys = sort_wt_match opt r in
          let () = x_tinfo_hp (add_str "sorted action" (pr_list_num string_of_action_wt_res_simpl)) ys no_pos in
          let ys2 = drop_low ys in
          (* let ys2 = snd (List.split ys) in *)
 	  (*Cond_action  ys *)
	  (*above would be required for entailments in which an available match has no solution unless another one is performed first*)
	  (*it could be expensive and trip the inference therefore a current solution delays matches with miss-match and unmatched actions*)
          (*
            LDK: why only List.hd ???
            This makes compute_actions nondeterministic if we have
            different orderings of heap nodes in the entailments.
            What if ys=[-1,Search1) ; (-1,Search2)]
          *)
	  List.hd (ys2)
              (*  match ys with
                  | [(_, act)] -> act
                  | ys -> (Cond_action ys) *)
              (* (List.hd (ys)) *)
              (* time for runfast hip --eps --imm - 42s *)
              (* Cond_action (r) *)
              (* time for runfast hip --eps --imm - 43s *)

and drop_low ys =
  let rec aux a ys = 
    match ys with
      | [] -> []
      | (b,x)::ys -> 
            if a==b then x::(aux a ys)
            else [] 
  in
  match ys with
    | [] -> []
    | ((a,w) (* as y *))::_ -> aux a ys 


and compute_actions prog estate es (* list of right aliases *)
    lhs_h (*lhs heap *) 
    lhs_p (*lhs pure*) 
    rhs_p (*rhs pure*)
    posib_r_alias (*possible rhs variables*)
    (rhs_lst : (CF.h_formula * CF.h_formula * MCP.mix_formula) list)
    is_normalizing (conseq:CF.formula) pos
    : action =
  let psv = Cprinter.string_of_spec_var in
  let pr0 = pr_list (pr_pair psv psv) in
  (* let pr_rhs_lst = pr_list (pr_pair Cprinter.string_of_h_formula Cprinter.string_of_h_formula) in *)
  let pr = Cprinter.string_of_h_formula   in
  (* let pr1 x = String.concat ";\n" (List.map (fun (c1,c2)-> "("^(Cprinter.string_of_h_formula c1)^" *** "^(Cprinter.string_of_h_formula c2)^")") x) in *)
  let pr3 = Cprinter.string_of_mix_formula in
  let pr1 x = pr_list (fun (c1,_,_)-> Cprinter.string_of_h_formula c1) x in
  let pr4 = pr_list Cprinter.string_of_spec_var in
  let pr2 = string_of_action_res_simpl in
  Debug.no_6 "compute_actions"
      (add_str "EQ ptr" pr0) 
      (add_str "LHS heap" pr) 
      (add_str "LHS pure" pr3)
      (add_str "RHS cand" pr1)
      (add_str "RHS pure" pr3)
      (add_str "right alias" pr4)
      pr2
      (fun _ _ _ _ _ _ -> compute_actions_x prog estate es lhs_h lhs_p rhs_p posib_r_alias rhs_lst is_normalizing conseq pos)
      es lhs_h lhs_p rhs_lst rhs_p posib_r_alias 

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
    | ThreadNode _
    | HEmp | HVar _
    | HRel _ | FrmHole _
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
  let node = match node with 
  | ViewNode v -> ViewNode{v with h_formula_view_node = rhs_v}
  | _ -> report_error pos "deprecated_find_node_one error" in
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

(*only check cyclic for fold-unfold*)
let need_check_cyclic_x act0=
  let rec helper act=
    match act with
      | M_fold _ | M_unfold _ -> true
      | Search_action ls | Seq_action ls | Cond_action ls ->
            List.exists (fun (_,a) -> helper a) ls
      | _ -> false
  in
  helper act0

let need_check_cyclic act0=
  let pr1 = string_of_action_res_simpl in
  Debug.no_1 "need_check_cyclic" pr1 string_of_bool
      (fun _ -> need_check_cyclic_x act0) act0
