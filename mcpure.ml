#include "xdebug.cppo"
open Globals
open Gen.Basic
open VarGen

open Cpure
open Mcpure_D
open Slicing

module AutoS = MCP_Util (Syn_Label_AuS)
module AnnoS = MCP_Util (Syn_Label_AnS)

(*
 eprune = espec + ememo + eslice
 -espec enables specialization
 -ememo will enable memoizing
 -eslice will enable slicing
*)

let print_mp_f = ref (fun (c: memo_pure) -> "printing not initialized")
let print_mp_full = ref (fun (c:memo_pure)-> " printing not initialized")
let print_mg_f = ref (fun (c: memoised_group) -> "printing not initialized")
let print_mc_f = ref (fun (c: memoised_constraint) -> "printing not initialized")
let print_sv_f = ref (fun (c: spec_var) -> "spec_var printing not initialized")
let print_sv_l_f = ref (fun (c: spec_var list) -> "spec_var list printing not initialized")
let print_sv = print_sv_f
let print_svl = print_svl
let print_bf_f = ref (fun (c: b_formula) -> "b_formula printing not initialized")
let print_p_f_f = ref (fun (c: formula) -> "formula printing not initialized")
let print_pure_f = print_p_f_f
let print_exp_f = ref(fun (c: exp) -> "exp printing not initialized")
(* let print_mix_f = ref (fun (c:mix_formula)-> " printing not initialized") *)

let print_p_f_l l = String.concat "; " (List.map !print_p_f_f l)

let print_alias_set aset = EMapSV.string_of aset

(* with const for get_equiv_eq + form_formula_eq *)
(* converts an equiv set into a formula *)
let fold_aset (f: var_aset) : formula =
  List.fold_left (fun a (c1, c2)->  mkAnd (form_formula_eq_with_const c1 c2) a no_pos)
    (mkTrue no_pos) (get_equiv_eq_with_const f)

let fold_aset (f: var_aset) : formula =
  Debug.no_1 "fold_aset" print_alias_set !print_p_f_f fold_aset f

let fv_memoised_constraint ({ memo_formula = bf }: memoised_constraint) : spec_var list
  = bfv bf

let fv_memoised_group (m: memoised_group) : spec_var list =
  match m with
  { memo_group_cons = mc_ls;
    memo_group_slice = f_ls;
    memo_group_aset = eq_set }  ->
    let v1 = List.concat (List.map fv_memoised_constraint mc_ls) in
    let v2 = List.concat (List.map fv f_ls) in
    let v3 = List.filter (fun x -> not (is_const x)) (fv_var_aset eq_set) in
    v1@v2@v3

let repatch_memoised_group (m: memoised_group) : memoised_group =
  let new_vars = fv_memoised_group m in
  { m with memo_group_fv = new_vars }

let repatch_memo_pure (ms: memo_pure) : memo_pure =
  List.map repatch_memoised_group ms

(* v2 must be a subset of v1 *)
let consistent_memoised_group (m: memoised_group) : bool =
  let v1 = m.memo_group_fv in
  let v2 = fv_memoised_group m in
  let r = Gen.BList.difference_eq eq_spec_var v2 v1 in
  let r2 = Gen.BList.difference_eq eq_spec_var v1 v2 in
  if r==[] then 
    if r2==[] then true
    else
     (* let s = ("WARNING: FreeVars unused :"^(!print_svl r2)) in
      let () = report_warning no_pos s in*)
      true
  else
    let s = ("ERROR: FreeVars not captured: " ^ (!print_svl r)) in
    let () = report_warning no_pos s in
    false

let consistent_memo_pure (m:memo_pure) : bool =
  List.for_all consistent_memoised_group m 

let check_repatch_memo_pure l s =
  if consistent_memo_pure l then l
  else 
    let () = report_warning no_pos ("repatching memo_pure"^s) in
    repatch_memo_pure l
(*

type: Mcpure_D.memoised_group ->
  'a ->
  ('a -> Mcpure_D.memoised_group -> (Mcpure_D.memoised_group * 'b) option) *
  (Mcpure_D.memoised_constraint -> 'a -> Mcpure_D.memoised_constraint * 'c) *
  ('a -> Mcpure_D.var_aset -> Mcpure_D.var_aset * 'c list) *
  (Cpure.formula -> 'a -> Cpure.formula * 'c) *
  (Cpure.spec_var -> 'a -> Cpure.spec_var * 'c) ->
  ('a -> Mcpure_D.memoised_group -> 'a) ->
  ('c list -> 'b) -> Mcpure_D.memoised_group * 'b

Expecting
=========

type: memo_pure ->
  'a ->
  ('a -> memo_pure -> (memo * 'a) option) 
  ('a -> memo_pure -> 'a) ->
  ('a list -> 'a) -> memo_pure * 'b

*)

let trans_memo_pure (e: memo_pure) (arg: 'a) f f_arg (comb:'b list->'b) : (memo_pure * 'b) =
  match f arg e with
    | Some (r,other) -> (r,other)
    | None -> (e,comb [])

let trans_memo_group (e: memoised_group) (arg: 'a) f (f_arg:'a->memoised_group->'a) f_comb : (memoised_group * 'b) =
  let f_grp, f_memo_cons, f_aset, f_slice, f_fv = f in
  match f_grp arg e with 
    | Some e1 -> e1
    | None -> 
      let new_arg = f_arg arg e in
      let new_cons, new_rc  = List.split ((List.map (fun c -> f_memo_cons c new_arg)) e.memo_group_cons) in
      let new_aset, new_ra = f_aset new_arg e.memo_group_aset  in
      let new_slice, new_rs = List.split ((List.map (fun c -> f_slice c new_arg)) e.memo_group_slice) in
      let new_fv, new_rv =  List.split ((List.map (fun c -> f_fv c new_arg)) e.memo_group_fv) in
      let new_lv, new_rl = List.split ((List.map (fun c -> f_fv c new_arg)) e.memo_group_linking_vars) in
      ({e with
        memo_group_fv = new_fv;
        memo_group_linking_vars = new_lv;
        memo_group_cons = new_cons;
        memo_group_slice = new_slice;
        memo_group_aset = new_aset;}, f_comb (new_rc@new_ra@new_rs@new_rv@new_rl))  

let trans_memo_formula (e: memo_pure) (arg: 'a) f f_arg f_comb : (memo_pure * 'b) = 
  let trans_memo_gr e = trans_memo_group e arg f f_arg f_comb in
  let ne, vals = List.split (List.map trans_memo_gr e) in
  (ne, f_comb vals)
  
let rec mfv (m: memo_pure) : spec_var list = Gen.BList.remove_dups_eq eq_spec_var (List.concat (List.map (fun c -> c.memo_group_fv) m))


and pcond_fv (p:memoised_constraint) : spec_var list = bfv p.memo_formula

and isConstMConsTrue r = isConstBTrue r.memo_formula
 (* | Fail_prune -> isConstBFalse r.memo_formula*)
  
and isConstMConsFalse r = isConstBFalse  r.memo_formula
 (* | Fail_prune -> isConstBTrue r.memo_formula*)
  
and isConstMTrue f = 
  match (List.length f) with
    | 0 -> true
    | 1 ->
        let r = List.hd f in
        (match ((List.length r.memo_group_cons),(List.length r.memo_group_slice)) with
            | 0,1 -> isConstTrue (List.hd r.memo_group_slice) && (EMapSV.is_empty r.memo_group_aset)
            | 1,0 -> isConstMConsTrue (List.hd r.memo_group_cons) && (EMapSV.is_empty r.memo_group_aset)
            | _ -> false)
    | _ -> false
      
and isTrivMTerm f = match f with
  | h::[]-> h.memo_group_fv==[] &&  h.memo_group_linking_vars==[] && h.memo_group_cons==[] && h.memo_group_aset==[] &&
		(match h.memo_group_slice with
			| h::[] -> isTrivTerm h
			| _ -> false)
  | _ -> false 
    
and isConstGroupTrue (f:memoised_group) : bool = match f.memo_group_slice with
  | [] -> f.memo_group_cons == [] && (EMapSV.is_empty f.memo_group_aset) 
  | x::[] -> f.memo_group_cons == [] && (EMapSV.is_empty f.memo_group_aset) && (isConstTrue x)
  | _ -> false
      
and isConstMFalse f = 
  match (List.length f) with
    | 1 ->
        let r = List.hd f in
        (match ((List.length r.memo_group_cons),(List.length r.memo_group_slice)) with
            | 0,1 -> isConstFalse (List.hd r.memo_group_slice)&& (EMapSV.is_empty r.memo_group_aset)
            | 1,0 -> isConstMConsFalse (List.hd r.memo_group_cons) && (EMapSV.is_empty r.memo_group_aset)
            | _ -> false)
    | _ -> false
  
let rec filter_mem_fct fct lst =  
  let l = List.map (fun c->{c with memo_group_cons = List.filter fct c.memo_group_cons}) lst in
  List.filter (fun c-> not (isConstGroupTrue c)) l

and filter_mem_triv lst = 
  filter_mem_fct (fun c ->
      let (pf,_) = c.memo_formula in
      match pf with 
	| Lte (e1,e2,l) 
	| Gte (e1,e2,l) 
	| Eq  (e1,e2,l) 
	| Neq  (e1,e2,l) -> not (eqExp e1 e2)
	| _ -> true) lst

and group_mem_by_fv (lst: memo_pure):memo_pure =
  Debug.no_1 "group_mem_by_fv" !print_mp_f !print_mp_f group_mem_by_fv_x lst
      
and group_mem_by_fv_x (lst: memo_pure):memo_pure =
  (* if !do_slicing then AnnoS.group_mem_by_fv lst *)
  if not !dis_slc_ann then AnnoS.group_mem_by_fv lst
  else AutoS.group_mem_by_fv lst

and regroup_memo_group (lst: memo_pure) : memo_pure =
  Debug.no_1 "regroup_memo_group" !print_mp_f !print_mp_f regroup_memo_group_x lst

and regroup_memo_group_x (lst: memo_pure) : memo_pure =
  (* if !do_slicing then AnnoS.regroup_memo_group lst *)
  if not !dis_slc_ann then AnnoS.regroup_memo_group lst
  else AutoS.regroup_memo_group lst

and subst_avoid_capture_memo (fr : spec_var list) (t : spec_var list) (f_l : memo_pure) : memo_pure =
  Debug.no_3 "subst_avoid_capture_memo" !print_svl !print_svl !print_mp_f !print_mp_f
      subst_avoid_capture_memo_x fr t f_l
      
and subst_avoid_capture_memo_x (fr : spec_var list) (t : spec_var list) (f_l : memo_pure) : memo_pure =
  let st1 = List.combine fr t in
  (* let st2 = List.combine fresh_fr t in *)
  let helper (s:(spec_var*spec_var) list) f  = 
    let r = EMapSV.rename_eset_allow_clash (subs_one s) f.memo_group_aset in
    (*let () = print_string ("rapp1: "^(print_alias_set f.memo_group_aset)^"\n") in
      let () = print_string ("rapp2: "^(print_alias_set r)^"\n") in*)
    {memo_group_fv = List.map (fun v-> subs_one s v) f.memo_group_fv;
    memo_group_linking_vars = List.map (fun v-> subs_one s v) f.memo_group_linking_vars; 
    memo_group_changed = f.memo_group_changed;
    memo_group_unsat = f.memo_group_unsat; (* TODO: Slicing UNSAT *)
    memo_group_cons = List.map (fun d->{d with memo_formula = b_apply_subs s d.memo_formula;}) f.memo_group_cons;
    memo_group_slice = List.map (par_subst s) f.memo_group_slice; 
    memo_group_aset = r} in
  let r = List.map (helper st1) f_l in
  regroup_memo_group r

(* and subst_avoid_capture_memo_debug (fr : spec_var list) (t : spec_var list) (f_l : memo_pure) : memo_pure = *)
(*   Debug.no_3a_list "subst_avoid_capture_memo" (full_name_of_spec_var) subst_avoid_capture_memo fr t f_l *)

and memo_cons_subst sst (f_l : memoised_constraint list): memoised_constraint list = 
  List.map (fun c -> 
      (* let nf = List.fold_left (fun a c-> b_apply_one c a) c.memo_formula sst in *)
      let nf = b_apply_subs sst c.memo_formula in
      { c with memo_formula = nf }) f_l

and memo_subst (sst : (spec_var * spec_var) list) (f_l : memo_pure) = 
  let rec helper sst f_l = match sst with
    | s::ss -> helper ss (m_apply_one s f_l)
    | [] -> f_l in
  regroup_memo_group (helper sst f_l)

and m_apply_one (s: spec_var * spec_var) f = m_apply_par [s] f


and m_apply_par_x (sst:(spec_var * spec_var) list) f = 
  let r1 = List.map (fun c -> 
      let r = EMapSV.subs_eset_par sst c.memo_group_aset in
      (* Slicing: Linking Variables Inference        *)
      (* We might have some new linking variables    *)
      (* that need to add to memo_group_linking_vars *)
      let subs_cons, lv = List.split (List.map (fun d ->
          let subs_memo = b_apply_subs sst d.memo_formula in
          let lv = match snd subs_memo with
            | None -> []
            | Some (_, _, le) -> List.concat (List.map (fun e -> CP.afv e) le) 
          in { d with memo_formula = subs_memo; }, lv) c.memo_group_cons) in
      { memo_group_fv = Gen.BList.remove_dups_eq eq_spec_var (List.map (fun v -> subst_var_par sst v) c.memo_group_fv);
      memo_group_linking_vars = 
              Gen.BList.remove_dups_eq eq_spec_var
                  ((List.map (fun v1 -> 
                      let v2 = subst_var_par sst v1 in
                      (* print_endline ("\nADD LV: " ^ (!print_sv v2)); *)
                      (* Hashtbl.add !linking_var_tbl (name_of_spec_var v2); *)
                      linking_var_tbl := (name_of_spec_var v2)::!linking_var_tbl;
                      v2) c.memo_group_linking_vars) @
                      (List.concat lv));
      memo_group_changed = c.memo_group_changed;
      (* Slicing: A substituted slice keeps its unsat flag *)
      (* if it is not merged to other slices               *)
      (* TODO: Slicing UNSAT: x>3 & y<=3 --> x>3 & x<=3 *)
      memo_group_unsat = c.memo_group_unsat; 
      memo_group_cons = subs_cons;
      memo_group_slice = List.map (apply_subs sst) c.memo_group_slice; 
      memo_group_aset = r }) f in  
  let r = filter_mem_triv r1 in
  r

and m_apply_par (sst:(spec_var * spec_var) list) f = 
  let pr1 = pr_list (pr_pair !print_sv_f !print_sv_f ) in
  let pr2 = !print_mp_f in
  Debug.no_2 "m_apply_par" pr1 pr2 pr2 m_apply_par_x sst f

(*MOVE to cpure.ml*)
(* and b_f_ptr_equations_aux with_null f = *)
(*   let (pf, _) = f in *)
(*   match pf with *)
(*   | Eq (e1, e2, _) -> *)
(*       let b = can_be_aliased_aux with_null e1 && can_be_aliased_aux with_null e2 in *)
(*       if not b then [] else [(get_alias e1, get_alias e2)] *)
(*   | _ -> []  *)

(*MOVE to cpure.ml*)
(* and b_f_ptr_equations f = b_f_ptr_equations_aux true f *)

(*MOVE to cpure.ml*)
(* and is_bf_ptr_equations bf = *)
(*   let (pf,_) = bf in *)
(*   match pf with *)
(*   | Eq (e1, e2, _) -> can_be_aliased_aux true e1 && can_be_aliased_aux true e2 *)
(*   | _ -> false *)

and b_f_bag_equations_aux with_emp f =
  let (pf,_) = f in
  match pf with
    | Eq (e1, e2, _) ->
          let b = can_be_aliased_aux_bag with_emp e1 && can_be_aliased_aux_bag with_emp e2 in
          if not b then [] else [(get_alias_bag e1, get_alias_bag e2)]
    | _ -> [] 

and b_f_bag_equations f = b_f_bag_equations_aux true f

and is_bf_ptr_equations bf =
  let (pf,_) = bf in
  match pf with
    | Eq (e1, e2, _) -> can_be_aliased_aux true e1 && can_be_aliased_aux true e2
    | _ -> false

(*MOVE to cpure.ml*)
(* and is_pure_ptr_equations f = match f with *)
(*   | BForm (bf,_) -> is_bf_ptr_equations bf *)
(*   | _ -> false *)

(*MOVE to cpure.ml*)
(* and remove_ptr_equations f is_or = match f with *)
(*   | BForm (bf,_) ->  *)
(*     if is_bf_ptr_equations bf then  *)
(*       if is_or then mkFalse no_pos *)
(*       else mkTrue no_pos  *)
(*     else f *)
(*   | And (f1,f2,p) -> mkAnd (remove_ptr_equations f1 false) (remove_ptr_equations f2 false) p *)
(*   | AndList b -> mkAndList (map_l_snd (fun c-> remove_ptr_equations c false) b) *)
(*   | Or (f1,f2,o,p) -> mkOr (remove_ptr_equations f1 true) (remove_ptr_equations f2 true) o p *)
(*   | Not (f,o,p) -> Not (remove_ptr_equations f false,o,p) *)
(*   | Forall (v,f,o,p) -> Forall (v,remove_ptr_equations f false,o,p) *)
(*   | Exists (v,f,o,p) -> Exists (v,remove_ptr_equations f false,o,p) *)

(*MOVE to cpure.ml*)
(* and pure_ptr_equations (f:formula) : (spec_var * spec_var) list =  *)
(*   pure_ptr_equations_aux true f *)

(*MOVE to cpure.ml*)
(* and pure_ptr_equations_aux_x with_null (f:formula) : (spec_var * spec_var) list =  *)
(*   let rec prep_f f = match f with *)
(*     | And (f1, f2, pos) -> (prep_f f1) @ (prep_f f2) *)
(* 	| AndList b -> fold_l_snd prep_f b *)
(*     | BForm (bf,_) -> b_f_ptr_equations_aux with_null bf *)
(*     | _ -> [] in  *)
(*   prep_f f *)

(*MOVE to cpure.ml*)
(* and pure_ptr_equations_aux with_null (f:formula) : (spec_var * spec_var) list =  *)
(*   let pr1 = string_of_bool in *)
(*   let pr2 = !print_pure_f in *)
(*   let pr3 = pr_list (pr_pair !print_sv !print_sv) in *)
(*   Debug.no_2 "pure_ptr_equations_aux" pr1 pr2 pr3 pure_ptr_equations_aux_x with_null f  *)

and pure_bag_equations_aux_x with_emp (f:formula) : (spec_var * spec_var) list = 
  let rec prep_f f = match f with
    | And (f1, f2, pos) -> (prep_f f1) @ (prep_f f2)
    | BForm (bf,_) -> b_f_bag_equations_aux with_emp bf
    | _ -> [] 
  in prep_f f

and pure_bag_equations_aux with_emp (f:formula) : (spec_var * spec_var) list = 
  let pr1 = string_of_bool in
  let pr2 = !print_pure_f in
  let pr3 = pr_list (pr_pair !print_sv !print_sv) in
  Debug.no_2 "pure_bag_equations_aux" pr1 pr2 pr3 pure_bag_equations_aux_x with_emp f 

(* use_with_null_const for below *)
(* assume that f is a satisfiable conjunct *) 
(* returns a list of ptr eqns v1=v2 that can be found in memo_pure *)
(* and called during matching of predicates *)
and ptr_equations_aux_mp_x with_null (f : memo_pure) : (spec_var * spec_var) list =  
  let helper f = 
    let r = List.fold_left (fun a c -> (a @ b_f_ptr_equations c.memo_formula)) [] f.memo_group_cons in
    let r = List.fold_left (fun a c -> a @ (pure_ptr_equations_aux with_null c)) r f.memo_group_slice in
    let eqs = (if !enulalias(*with_null*) then get_equiv_eq_with_null else get_equiv_eq) f.memo_group_aset in
    r @ eqs in
  List.concat (List.map helper f)

and ptr_equations_aux_mp with_null (f : memo_pure) : (spec_var * spec_var) list =
  let pr_out = pr_list (pr_pair !print_sv !print_sv) in
  Debug.no_2 "ptr_equations_aux_mp"
      string_of_bool !print_mp_f pr_out
      ptr_equations_aux_mp_x with_null f

and bag_equations_aux_mp with_emp (f : memo_pure) : (spec_var * spec_var) list =  
  let helper f = 
    let r = List.fold_left (fun a c -> (a @ b_f_bag_equations c.memo_formula)) [] f.memo_group_cons in
    let r = List.fold_left (fun a c -> a @ (pure_bag_equations_aux with_emp c)) r f.memo_group_slice in
    let eqs = get_equiv_eq f.memo_group_aset in
    r @ eqs in
  List.concat (List.map helper f)

(*and alias_of_ptr_eqs s = List.fold_left (fun a (c1,c2) -> EMapSV.add_equiv a c1 c2) Gen.is_empty_aset s*)
      
(*and b_formula_alias (f:b_formula):var_aset = alias_of_ptr_eqs (b_f_ptr_equations f)*)
(*and pure_alias (f:formula) : var_aset = alias_of_ptr_eqs (pure_ptr_equations f)*)
      
(*and memo_alias (m:memo_pure) : var_aset = alias_of_ptr_eqs (ptr_equations m)*)

(*and var_aset_subst_one s (l:var_aset) : var_aset = List.map (fun (a,l)-> ((subst_var s a),subst_one_var_list s l)) l *)
      
(*and var_aset_subst_list s (l:var_aset) : var_aset = List.map (fun (a,l)-> ((subs_one s a),subst_var_list s l)) l *)

(*and var_aset_subst_one_exp (v,_) (l:var_aset) : var_aset = 
  List.fold_left (fun a (c1,c2)-> if (eq_spec_var v c1) then a else (c1,(List.filter (eq_spec_var v) c2))::a ) [] l*)
      
(* extract the equations for the variables that are to be explicitly instantiated from the residue - a Cpure.formula *)
(* get the equation for the existential variable used in the
   following variable elimination ex x. (x=y & P(x)) <=> P(y).
   The function also returns the remainder of the formula after
   the equation is extracted. It stops searching upon seeing
   Or/Exists/Forall. The equations returned are only of form
   v1 = v2 so that they can be applied to heap nodes. *)

and pure_of_memo_pure f =  fold_mem_lst (mkTrue no_pos) false true f

and bag_vars_memo_pure (mp : memo_pure) : spec_var list =
  let pf = pure_of_memo_pure mp in
  bag_vars_formula pf

and get_subst_equation_memo_formula_vv (f0: memo_pure) (v:spec_var) : ((spec_var * spec_var) list * memo_pure) = 
  let (r1,r2) = get_subst_equation_memo_formula f0 v true in
  let r1 = List.fold_left (fun a c-> match c with | (r,Var(v,_))-> (r,v)::a | _ -> a) [] r1 in
  (r1,r2)
      
(* It always returns either 0 or one substitutions, *)
(* if more are available just picks one *)
and get_subst_equation_memo_formula_x (f0 : memo_pure) (v : spec_var) only_vars: ((spec_var * exp) list * memo_pure) =
  let bag_vars = bag_vars_memo_pure f0 in
  (*OVERIDDING the input for soundness*)
  (*If there are bag constraints -> only find equations of variables
    such as x=v & x in BAG, but not x=v+1 & x in BAG*)
  let only_vars = if (Gen.BList.mem_eq eq_spec_var v bag_vars) then true else only_vars in
  let r = List.fold_left (fun (a1,a2) c ->
      if not(a1=[]) then (a1,c::a2)
      else if not(List.exists (eq_spec_var v) c.memo_group_fv) then (a1,c::a2)
      else 
	let acl_cons, ncl = List.fold_left (fun (a1,a2) c -> 
            if not(a1=[]) then (a1,c::a2)
	    else 
	      let r1,r2 = get_subst_equation_b_formula c.memo_formula v None only_vars in
	      if (r1=[]) then (a1,c::a2) else (r1,a2)) ([],[]) c.memo_group_cons 
        in
	
	let acl_aset, nas = if not(acl_cons=[]) then (acl_cons,c.memo_group_aset)
	else match EMapSV.find_equiv_elim v c.memo_group_aset with
          | None -> (acl_cons,c.memo_group_aset)
          | Some (s,nas) -> ([(v,conv_var_to_exp s)],nas) 
        in
	
	let acl_slice, nsl = if not (acl_aset=[]) then (acl_aset, c.memo_group_slice)
	else List.fold_left (fun (a1,a2) c -> 
	    if not (a1=[]) then (a1,c::a2)
	    else 
	      let r1,r2 = get_subst_equation_formula c v only_vars in
	      (r1,r2::a2))([],[]) c.memo_group_slice 
        in
	let rg = { c with 
	    memo_group_cons=ncl; 
	    memo_group_slice=nsl; 
	    memo_group_aset = nas } in
	(acl_slice, rg::a2)) ([],[]) f0 
  in
  r

and get_subst_equation_memo_formula (f0 : memo_pure) (v : spec_var) only_vars: ((spec_var * exp) list * memo_pure) =
  let pr_out = pr_pair (pr_list (pr_pair !print_sv !print_exp)) !print_mp_f in
  Debug.no_3 "get_subst_equation_memo_formula"
      !print_mp_f !print_sv string_of_bool pr_out
      get_subst_equation_memo_formula_x f0 v only_vars


and get_all_vv_eqs_memo f = List.fold_left (fun (a1,a2) c ->
	let v1, ncl = List.fold_left (fun (a1,a2) c -> 
	      match get_all_vv_eqs_bform c.memo_formula with
		  | [] -> a1,c::a2
		  | h::_ -> h::a1,a2) ([],[]) c.memo_group_cons in
	let v2 = EMapSV.get_equiv c.memo_group_aset in
	let v3, nsl =  List.fold_left (fun (a1,a2) c -> 
	      let r1,r2 = get_all_vv_eqs c in
	      (r1,r2::a2))([],[]) c.memo_group_slice in
	let rg = { c with 
	    memo_group_cons=ncl; 
	    memo_group_slice=nsl; 
	    memo_group_aset = EMapSV.mkEmpty } in
	(v1@v2@v3, rg::a2)) ([],[]) f
	  
	  
(* below need to be with_const *)
(* this applies a substitution v->e on a list of memoised group *)
(* useful to consider two special cases is v->v2 or v->c for aset *)
and memo_apply_one_exp (s:spec_var * exp) (mem:memoised_group list) : memo_pure =
  let pr = pr_pair !print_sv !print_exp_f in
  Debug.no_2  "memo_apply_one_exp" pr !print_mp_f !print_mp_f
      memo_apply_one_exp_x s mem

and memo_apply_one_exp_x (s:spec_var * exp) (mem:memoised_group list) : memo_pure = 
  let fr, t = s in
  let conv eqs = match (conv_exp_to_var t) with
    | Some (vt, _) -> ([], List.fold_left (fun a2 (c1, c2) ->
          if (eq_spec_var c1 fr) then (add_equiv_eq_with_const a2 c2 vt)
          else if (eq_spec_var c2 fr) then (add_equiv_eq_with_const a2 c1 vt)
          else (add_equiv_eq_with_const a2 c1 c2)) empty_var_aset eqs)
    | None -> List.fold_left (fun (a1, a2) (c1, c2) -> 
          if (eq_spec_var c1 fr) then ((BForm ((Eq (conv_var_to_exp c2,t,no_pos), None),None))::a1,a2)
          else if (eq_spec_var c2 fr) then ((BForm ((Eq (conv_var_to_exp c1,t,no_pos), None),None))::a1,a2)
          else (a1,add_equiv_eq_with_const a2 c1 c2)) ([],empty_var_aset) eqs 
  in
  let r = List.map (fun c -> 
      let eqs = get_equiv_eq_with_const c.memo_group_aset in
      let tbm, rem = conv eqs in
      let r = { c with
          memo_group_cons = List.map (fun d->{d with memo_formula = b_apply_one_exp s d.memo_formula}) c.memo_group_cons;
          memo_group_slice = tbm @ (List.map (apply_one_exp s) c.memo_group_slice);
          memo_group_aset = rem } in
      let r_fv = remove_dups_svl ((get_elems_eq r.memo_group_aset) @ 
          (List.concat (List.map (fun c -> bfv c.memo_formula) r.memo_group_cons)) @
          (List.concat (List.map fv r.memo_group_slice))) in
      let diff x y = Gen.BList.difference_eq eq_spec_var x y in
      let r_lfv = diff r.memo_group_linking_vars (diff r.memo_group_fv r_fv) in
      { r with memo_group_fv = r_fv; memo_group_linking_vars = r_lfv; }) mem in
  let r_group = group_mem_by_fv r in
  filter_mem_triv r_group
      
and memo_f_neg (f: b_formula): b_formula =
  let (pf,il) = f in
  let npf = match pf with
    | Lt (e1,e2,l) -> Gte (e2,e1,l)
    | Lte (e1,e2,l) -> Gt (e2,e1,l)
    | Gt (e1,e2,l) -> Lte (e1,e2,l)
    | Gte (e1,e2,l) -> Lt (e1,e2,l)
    | Eq (e1,e2,l) -> Neq (e1,e2,l)
    | Neq (e1,e2,l) -> Eq (e1,e2,l)
    | BagIn (e1,e2,l) -> BagNotIn(e1,e2,l)
    | BagNotIn  (e1,e2,l) -> BagIn(e1,e2,l)
    | ListIn (e1,e2,l) -> ListNotIn(e1,e2,l)
    | ListNotIn (e1,e2,l) -> ListIn(e1,e2,l)
    | _ -> Error.report_error {Error.error_loc = no_pos; Error.error_text = "memoized negation: unexpected constraint type"}
  in (npf,il)
         
and memo_arith_simplify (f : memo_pure) : memo_pure = 
  List.map (fun c -> { c with memo_group_slice = List.map (arith_simplify 5) c.memo_group_slice }) f
      
(******************************************************************************************************************
                                                                                                                   Utilities for memoized formulas
******************************************************************************************************************)
      
and mkMTrue pos : memo_pure = []

and mkMFalse pos : memo_pure = 
  [{memo_group_fv = [];
  memo_group_linking_vars = [];
  memo_group_changed = false; 
  memo_group_unsat = false; (* Slicing: Do not need to check UNSAT with False slice *)
  memo_group_cons = [];
  memo_group_slice = [mkFalse pos];
  memo_group_aset = empty_var_aset}]

and memo_is_member_pure p mm = 
  List.exists (fun c-> 
      let r = (List.exists (is_member_pure p) c.memo_group_slice)||
	(List.exists (fun d-> 
	    (match p with | BForm (r,_)-> equalBFormula_aset c.memo_group_aset r d.memo_formula | _ -> false)) c.memo_group_cons) in
      if r then true
      else match p with
	| BForm ((Eq(Var(v1,_),Var(v2,_),_),_), _) -> EMapSV.is_equiv c.memo_group_aset v1 v2
	| _ -> false ) mm


and fold_mem_lst_to_lst_gen  (mem:memo_pure) with_R with_P with_slice with_disj: formula list =	
  let prb = string_of_bool in
  Debug.no_5 "fold_mem_lst_to_lst_gen" 
      !print_mp_f 
      (add_str "with redundant" prb)
      (add_str "with propagated/inv" prb)
      (add_str "with slice" prb)
      (add_str "with disj" prb)
      (pr_list !print_p_f_f)
      (fun _ _ _ _ _ -> fold_mem_lst_to_lst_gen_x (mem:memo_pure) with_R with_P with_slice with_disj) mem  with_R with_P with_slice with_disj
      
(* below with_const *)
(* this extracts a list of formula from memo_pure ;
   with_P : takes the propagated ctrs
   with_R : takes the redundant ctrs
   with_slice : takes the non-atomic ctrs
   with_disj : takes also non-atomic disjunctive ctrs
*)
      
(* returns list of AND formulas, each slice will be a formula *)
and fold_mem_lst_to_lst_gen_x (mem:memo_pure) with_R with_P with_slice with_disj : formula list =
  fold_mem_lst_to_lst_gen_orig mem with_R with_P with_slice with_disj
      (* if !do_slicing && !multi_provers then                                    *)
      (*   fold_mem_lst_to_lst_gen_slicing mem with_R with_P with_slice with_disj *)
      (* else                                                                     *)
      (*   fold_mem_lst_to_lst_gen_orig mem with_R with_P with_slice with_disj    *)

and fold_slice_gen (mg : memoised_group) with_R with_P with_slice with_disj : formula =
  let rec has_disj_f c = match c with | Or _ -> true | _ -> false in
  let slice =
    if with_slice then 
      if with_disj then mg.memo_group_slice 
      else List.filter (fun c -> not (has_disj_f c)) mg.memo_group_slice
    else [] in
  let cons = List.filter (fun c -> match c.memo_status with 
    | Implied_R -> with_R 
    | Implied_N -> true 
    | Implied_P-> with_P) mg.memo_group_cons in
  let cons  = List.map (fun c -> (BForm (c.memo_formula, None))) cons in
  let asetf = List.map (fun (c1,c2) -> form_formula_eq_with_const c1 c2) (get_equiv_eq_with_const mg.memo_group_aset) in
  join_conjunctions (asetf @ slice @ cons)
      
and fold_mem_lst_to_lst_gen_orig (mem:memo_pure) with_R with_P with_slice with_disj : formula list =				  
  List.map (fun mg -> fold_slice_gen mg with_R with_P with_slice with_disj) mem
      
(*
  and fold_mem_lst_to_lst_gen_slicing (mem:memo_pure) with_R with_P with_slice with_disj : formula list =
  Debug.no_1 "fold_mem_lst_to_lst_gen_slicing"
  !print_mp_f
  (pr_list !print_p_f_f)
  (fun mem -> fold_mem_lst_to_lst_gen_slicing_x mem with_R with_P with_slice with_disj) mem
*)	
(* find relevant slices to fold them to a formula *)
(* [A, B, C] -> [A /\ C, B /\ C, C] *)
and fold_mem_lst_to_lst_gen_slicing (mem:memo_pure) with_R with_P with_slice with_disj : formula list =
  (*let () = print_string ("\nfold_mem_lst_to_lst_gen_slicing: mem:\n" ^ (!print_mp_f mem) ^ "\n") in*)
  
  let rec has_disj_f c = match c with | Or _ -> true | _ -> false in

  let is_related mg1 mg2 =
    let (nlv1, lv1) =
      (Gen.BList.difference_eq eq_spec_var mg1.memo_group_fv mg1.memo_group_linking_vars,
      mg1.memo_group_linking_vars) in
    let fv2 = mg2.memo_group_fv in
    if (nlv1 == []) then 
      Gen.BList.overlap_eq eq_spec_var lv1 fv2 (* mg1 is a linking constraint and it contains knowledge about variables of mg2 *)
    else
      Gen.BList.overlap_eq eq_spec_var nlv1 fv2 (* mg1 is a general knowledge about variables of mg2 *)
  in

  let pick_rel_constraints mg mp =
    List.find_all (fun mgs -> mgs != mg && is_related mgs mg) mp
  in

  let filter_list_mg l_mg =
    List.map (fun mg ->
	let slice =
	  if with_slice then 
	    if with_disj then mg.memo_group_slice 
	    else List.filter (fun c -> not (has_disj_f c)) mg.memo_group_slice
	  else [] in
	let cons = List.filter (fun c -> match c.memo_status with 
	  | Implied_R -> with_R 
	  | Implied_N -> true 
	  | Implied_P-> with_P) mg.memo_group_cons in
	let cons  = List.map (fun c -> (BForm (c.memo_formula, None))) cons in
	let asetf = List.map (fun (c1,c2) -> form_formula_eq_with_const c1 c2) (get_equiv_eq_with_const mg.memo_group_aset) in
	join_conjunctions (asetf @ slice @ cons)  
    ) l_mg
  in

  let r = List.map (fun mg ->
      let rel_mgs = mg::(pick_rel_constraints mg mem) in
      filter_list_mg rel_mgs
  ) mem in
  let res = List.map join_conjunctions r in
  (*let () = print_string ("\nfold_mem_lst_to_lst_gen_slicing: res:\n" ^ (pr_list !print_p_f_f res) ^ "\n") in*)
  res

(* Find relevant slices to fold them to a formula for SAT checking                                     *)
(* SAT(A /\ B) = SAT(A) /\ SAT(B) if fv(A) intersect fv(B) = Empty or linking vars of A and B          *)
(* For AVL example with size, height, sum and bag properties,                                          *)
(*   A contains size (n) and height (h) with linking constraint n>=h                                   *)
(*   B constains sum with linking variable v                                                           *)
(*   C constains bag with linking variable v                                                           *)
      
(* If C is a linking constraint of A and B: [A, B, C] -> [A /\ B /\ C]                                 *)
(* [n1<0, n2>0, $ n1>n2] -> [n1<0 & n2>0 & n1>n2]                                                      *)	

(* If C is a linking var/expr of A and B: [A, B, C] -> [A /\ C, B /\ C]                                *)
(* [s=s1+($ v) & s>0 & s1>0, B=B1U{($ v)}, v>0] -> [s=s1+($ v) & s>0 & s1>0 & v>0, B=B1U{($ v)} & v>0] *)	
and fold_mem_lst_to_lst_gen_for_sat_slicing (mem:memo_pure) with_R with_P with_slice with_disj : formula list =
  (*let () = print_string ("\nfold_mem_lst_to_lst_gen_slicing: mem:\n" ^ (!print_mp_f mem) ^ "\n") in*)
  
  let has_disj_f c = match c with | Or _ -> true | _ -> false in

  let memo_group_linking_vars_exps (mg : memoised_group) =
    let cons_lv = List.fold_left (fun acc mc -> acc @ (b_formula_linking_vars_exps mc.memo_formula)) [] mg.memo_group_cons in
    let slice_lv = List.fold_left (fun acc f -> acc @ (formula_linking_vars_exps f)) [] mg.memo_group_slice in
    Gen.BList.remove_dups_eq eq_spec_var (cons_lv @ slice_lv)
  in

  let fv_without_linking_vars_exps mg =
    let fv_no_lv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv (memo_group_linking_vars_exps mg) in
    (* If all fv are linking vars then mg should be a linking constraint *)
    if (fv_no_lv = []) then mg.memo_group_fv else fv_no_lv
  in 

  (*
    let is_related mg1 mg2 = (* if true, mg1 and mg2 should be merged into one slice for SAT checking *)
    let mg1_fv_no_lv = fv_without_linking_vars_exps mg1 in
    let mg2_fv_no_lv = fv_without_linking_vars_exps mg2 in
    Gen.BList.overlap_eq eq_spec_var mg1_fv_no_lv mg2_fv_no_lv
    in
  *)

  let slice_memo_pure (mp : memo_pure) : (spec_var list * spec_var list * memoised_group list) list =
    (* OUT: list of (list of fv, list of fv without linking vars, list of memo_group) *)
    let repart acc mg = 
      let mg_fv_no_lv = fv_without_linking_vars_exps mg in
      let (ol, nl) = List.partition (* overlap_list, non_overlap_list with mg *)
	(fun (_, vl, mgl) -> (Gen.BList.overlap_eq eq_spec_var vl mg_fv_no_lv)
	) acc
      in
      let n_fvl = List.fold_left (fun a (fvl, _, _) -> a@fvl) mg.memo_group_fv ol in
      let n_vl = List.fold_left (fun a (_, vl, _) -> a@vl) mg_fv_no_lv ol in
      let n_mgl = List.fold_left (fun a (_, _, mgl) -> a@mgl) [mg] ol  in
      (Gen.BList.remove_dups_eq eq_spec_var n_fvl,
      Gen.BList.remove_dups_eq eq_spec_var n_vl,
      n_mgl)::nl
    in List.fold_left repart [] mp
  in

  let slice_linking_vars_constraints mgl =
    (* Separate the above list of memo_group list into two parts: *)
    (* - Need to check SAT *)
    (* - Unneed to check SAT (constraints of linking vars) *)
    let rec repart (unchk_l, n_l, un_l) =
      match unchk_l with
	| [] -> (unchk_l, n_l, un_l)
	| (fvl, vl, mgl)::unchk_rest ->
	      let mgl_lv = Gen.BList.difference_eq eq_spec_var fvl vl in
	      if (mgl_lv = []) then
		repart (unchk_rest, (fvl, vl, mgl)::n_l, un_l)
	      else
		let is_related vl1 vl2 = Gen.BList.overlap_eq eq_spec_var vl1 vl2 in
		(* Search relevant constraints in list of unchecked constraints *)
		(* Move merged constraints into list of unneeded to check SAT constraints *)
		let (merged_mgl1, unmerged_mgl1) = List.partition
		  (fun (_, vl1, _) -> is_related vl1 mgl_lv) unchk_rest
		in

		(* Search relevant constraints in list of needed to check SAT constraints *)
		(* Move merged constraints into list of unneeded to check SAT constraints *)
		let (merged_mgl2, unmerged_mgl2) = List.partition
		  (fun (_, vl2, _) -> is_related vl2 mgl_lv) n_l
		in
		
		(* Search relevant constraints in list of unneeded to check SAT constraints *)
		let merged_mgl3 = List.find_all
		  (fun (_, vl3, _) -> is_related vl3 mgl_lv) un_l
		in

		let n_mgl =
		  mgl @
		      (List.fold_left (fun acc (_, _, mgl1) -> acc@mgl1) [] merged_mgl1) @
		      (List.fold_left (fun acc (_, _, mgl2) -> acc@mgl2) [] merged_mgl2) @
		      (List.fold_left (fun acc (_, _, mgl3) -> acc@mgl3) [] merged_mgl3)
		in
		
		let n_unchk_l = unmerged_mgl1 in
		let n_n_l = (fvl, vl, n_mgl)::unmerged_mgl2 in
		let n_un_l = merged_mgl1 @ merged_mgl2 @ un_l in
		repart (n_unchk_l, n_n_l, n_un_l)
    in

    let (_, n_l, _) = repart (mgl, [], []) in
    n_l
  in 
  
  let filter_list_mg l_mg =
    List.map (fun mg ->
	let slice =
	  if with_slice then 
	    if with_disj then mg.memo_group_slice 
	    else List.filter (fun c -> not (has_disj_f c)) mg.memo_group_slice
	  else [] in
	let cons = List.filter (fun c -> match c.memo_status with 
	  | Implied_R -> with_R 
	  | Implied_N -> true 
	  | Implied_P-> with_P) mg.memo_group_cons in
	let cons  = List.map (fun c -> (BForm (c.memo_formula, None))) cons in
	let asetf = List.map (fun (c1,c2) -> form_formula_eq_with_const c1 c2) (get_equiv_eq_with_const mg.memo_group_aset) in
	join_conjunctions (asetf @ slice @ cons)  
    ) l_mg
  in

  let n_l = slice_linking_vars_constraints (slice_memo_pure mem) in

  let res = List.map (
      fun (_, _, mgl) -> join_conjunctions (filter_list_mg mgl)
  ) n_l in
  (*let () = print_string ("\nfold_mem_lst_to_lst_gen_slicing: res:\n" ^ (pr_list !print_p_f_f res) ^ "\n") in*)
  res
      
and fold_mem_lst_to_lst_x mem with_dupl with_inv with_slice = fold_mem_lst_to_lst_gen mem with_dupl with_inv with_slice true

and fold_mem_lst_to_lst mem with_dupl with_inv with_slice =
  Debug.no_1 "fold_mem_lst_to_lst" !print_mp_f print_p_f_l
      (fun _ -> fold_mem_lst_to_lst_x mem with_dupl with_inv with_slice) mem
      
and fold_mem_lst_gen (f_init:formula) with_dupl with_inv with_slice with_disj lst : formula = 
  let r = fold_mem_lst_to_lst_gen lst with_dupl with_inv with_slice with_disj in
  List.fold_left (fun a c -> mkAnd a c no_pos) f_init r      
      
and fold_mem_lst_no_complex (*no disj*) (f_init:formula) with_dupl with_inv lst : formula =
  fold_mem_lst_gen f_init with_dupl with_inv true false lst

and fold_mem_lst_with_complex (f_init:formula) with_dupl with_inv (lst:memo_pure) : formula =
  fold_mem_lst_gen f_init with_dupl with_inv true true lst

(*
  and fold_mem_lst (f_init:formula) with_dupl with_inv (lst:memo_pure) : formula =
  Debug.no_2 "fold_mem_lst_m"
  !print_p_f_f !print_mp_f !print_p_f_f
  (fun _ _ -> fold_mem_lst_x f_init with_dupl with_inv lst) f_init lst
*)
	
and fold_mem_lst (f_init:formula) with_dupl with_inv (lst:memo_pure) : formula =
  fold_mem_lst_gen f_init with_dupl with_inv true true lst
  
(* folds just the pruning constraints, ignores the memo_group_slice *) 
and fold_mem_lst_cons init_cond lst with_dupl with_inv with_slice : formula = 
  (*fold_mem_lst_to_lst lst false true false*)
  fold_mem_lst_gen (BForm (init_cond,None)) with_dupl with_inv with_slice true lst
      
and filter_useless_memo_pure (simp_fct:formula->formula) (simp_b:bool) 
      (fv:spec_var list) (c_lst:memo_pure) : memo_pure = 
  let n_c_lst = List.fold_left (fun a c-> 
      if (isConstMFalse a) then a
      else
	let n_slice_lst = if c.memo_group_fv = [] then List.map simp_fct c.memo_group_slice else c.memo_group_slice in
	let n_slice_lst = List.filter (fun c-> not (isConstTrue c)) n_slice_lst in   
	if (List.exists isConstFalse n_slice_lst) then mkMFalse no_pos
	else {c with memo_group_slice = n_slice_lst; memo_group_cons = c.memo_group_cons;}::a ) [] c_lst in
  List.filter (fun c-> not (isConstGroupTrue c))  n_c_lst
      
and filter_merged_cons_x aset l =   
  let eq = Cpure.eq_spec_var_aset aset  in
  let keep c1 c2 = match c1.memo_status, c2.memo_status with
    | _, Implied_R -> if (equalBFormula_f eq c1.memo_formula c2.memo_formula) then (true,false) else (true,true)
    | Implied_R, _ -> if (equalBFormula_f eq c1.memo_formula c2.memo_formula) then (false,true) else (true,true) 
    | Implied_N, Implied_N | Implied_P, Implied_P | Implied_N, Implied_P
	  -> if (equalBFormula_f eq c1.memo_formula c2.memo_formula) then (false,true) else (true,true) 
    | Implied_P, Implied_N -> if (equalBFormula_f eq c1.memo_formula c2.memo_formula) then (true,false) else (true,true) in
  let rec remove_d n = match n with 
    | [] -> []
    | q::qs -> 
	  let b,r = List.fold_left (fun (b,r) c-> 
	      let r1,r2 = keep q c in
	      (b&&r1,if r2 then c::r else r)) (true,[])qs in
	  if b then q::(remove_d r) else (remove_d r) in
  Gen.Profiling.push_time "filter_dupl_memo";
  let r = remove_d (List.concat l) in 
  Gen.Profiling.pop_time "filter_dupl_memo";
  r

and filter_merged_cons aset l =
  let pr1  = pr_list (pr_list !print_mc_f) in
  let pr_out = (pr_list !print_mc_f) in
  Debug.no_2 "filter_merged_cons" print_alias_set pr1 pr_out
  filter_merged_cons_x aset l

and mkOr_mems (l1: memo_pure) (l2: memo_pure) (*with_dupl with_inv*) : memo_pure = 
  let f1 = fold_mem_lst_with_complex (mkTrue no_pos) false true l1 in
  let f2 = fold_mem_lst_with_complex (mkTrue no_pos) false true l2 in
  memoise_add_pure_N [] (mkOr f1 f2 None no_pos)

and combine_memo_branch b (f, l) =
  match b with 
    | "" -> f
    | s -> try memoise_add_pure_N f (List.assoc b l) with Not_found -> f

(*ambiguous name. another method with the same name is declared more down*)
and merge_mems (l1: memo_pure) (l2: memo_pure) slice_check_dups : memo_pure =
  Debug.no_3 "merge_mems_m" !print_mp_f !print_mp_f (fun b -> string_of_bool b)
      !print_mp_f merge_mems_x l1 l2 slice_check_dups
      
and merge_mems_x (l1: memo_pure) (l2: memo_pure) slice_check_dups : memo_pure =
  merge_mems_check l1 l2 slice_check_dups

and merge_mems_check (l1: memo_pure) (l2: memo_pure) slice_check_dups : memo_pure =
  let r = merge_mems_nx l1 l2 slice_check_dups in
  if (consistent_memo_pure r) then r
  else report_error no_pos "merge_mems : inconsistent memo_pure here"

and merge_mems_full_check (l1: memo_pure) (l2: memo_pure) slice_check_dups: memo_pure =
  let b1 = consistent_memo_pure l1 in
  let b2 = consistent_memo_pure l2 in
  let f l = "" in
  (* "FREEVARS: "^(!print_svl (mfv l))^"\n" in  *)
  let s1 = if b1 then "" else (f l1)^(!print_mp_f l1) in
  let s2 = if b2 then "" else (f l2)^(!print_mp_f l2) in
  if b1 && b2 then
    let r = merge_mems_nx l1 l2 slice_check_dups in
    if (consistent_memo_pure r) then r
    else report_error no_pos "merge_mems : inconsistent memo_pure after merging"
  else
    let () = print_endline_quiet s1 in
    let () = print_endline_quiet s2 in
    report_error no_pos ("merge_mems : inconsistent memo_pure before merging")

and merge_mems_repatch (l1: memo_pure) (l2: memo_pure) slice_check_dups: memo_pure =
  let r = merge_mems_nx l1 l2 slice_check_dups in
  if (consistent_memo_pure r) then r
  else check_repatch_memo_pure r "@ merge_mems"

and merge_mems_nx (l1: memo_pure) (l2: memo_pure) slice_check_dups: memo_pure = 
  let r = 
    if (isConstMFalse l1) || (isConstMTrue l2) then l1
    else if (isConstMFalse l2) || (isConstMTrue l1) then l2
      (* else if !do_slicing then AnnoS.merge_mems_nx l1 l2 slice_check_dups filter_merged_cons *)
    else if not !dis_slc_ann then AnnoS.merge_mems_nx l1 l2 slice_check_dups filter_merged_cons
    else AutoS.merge_mems_nx l1 l2 slice_check_dups filter_merged_cons
  in r

(*add cm to l_init and depending on the fnf flag
  true: add cm and also add the negation of cm as a fail condition
  false: add only cm 
  and memoise_add_memo (l_init: memo_pure) (cm:memoised_constraint) : memo_pure =
  let fv = bfv cm.memo_formula in
  let merged,un_merged = List.partition (fun c-> (List.length (Gen.BList.intersect_eq eq_spec_var fv c.memo_group_fv))>0) l_init in
  let n_cm_lst = [cm] in
  let n1,n2,n3,n4 = List.fold_left 
  (fun (a1,a2,a3,a4) d-> 
  (d.memo_group_fv@a1,
  d.memo_group_cons::a2,
  d.memo_group_slice::a3, 
  EMapSV.merge_eset(*_debug !print_sv_f*) a4 d.memo_group_aset))
  (fv,[n_cm_lst],[], empty_var_aset) merged in   
  let l = if (List.length merged)>0 then 
  let ng = {memo_group_cons =  filter_merged_cons (empty_var_aset) n2; 
  memo_group_fv = remove_dups_svl n1;
  memo_group_changed = true;
  memo_group_slice = List.concat n3;
  memo_group_aset = n4} in
  List.hd (recompute_unknowns [ng])
  else 
  {
  memo_group_cons =n_cm_lst; 
  memo_group_fv = fv; 
  memo_group_changed = true; 
  memo_group_slice = []; 
  memo_group_aset = empty_var_aset} in  
  let r = l::un_merged in
  r
  
(*and memoise_add_memo (l: memo_pure) (cm:memoised_constraint): memo_pure = memoise_add_memo_fnf l cm false*)
*)
and memoise_add_failed_memo (l:memo_pure) (p:b_formula) : memo_pure = 
  merge_mems l (create_memo_group_wrapper [p] Implied_R) false
      
and memoise_add_pure_aux_x (l: memo_pure) (p:formula) status : memo_pure = 
  if (isConstTrue p)||(isConstMFalse l) then l 
  else if (isConstFalse p) then mkMFalse no_pos
  else 
    (Gen.Profiling.push_time "add_pure";
    let disjs, rests = List.fold_left (fun (a1,a2) c -> match c with 
      | BForm x -> (x::a1,a2) 
      | _ -> (a1,c::a2))  ([],[]) (list_of_conjs p) in
    let m2 = create_memo_group(*_debug*) disjs rests status in
    let r = merge_mems l m2 true in
    (*let r = List.concat (List.map split_mem_grp r) in*)
    Gen.Profiling.pop_time "add_pure"; r)

and memoise_add_pure_aux l p status : memo_pure = 
  let pr1 = !print_mp_f in
  let pr2 = !print_p_f_f in
  Debug.no_2 "memoise_add_pure_aux " pr1 pr2 pr1 (fun _ _ ->  memoise_add_pure_aux_x l p status) l p

and memoise_add_pure_N l p =
  let pr1 = !print_mp_f in
  let pr2 = !print_p_f_f in
  Debug.no_2 "memoise_add_pure_N_m" pr1 pr2 pr1 (fun _ _ -> memoise_add_pure_N_x l p) l p

and memoise_add_pure_P l p =
  let pr1 = !print_mp_f in
  let pr2 = !print_p_f_f in
  Debug.no_2 "memoise_add_pure_P_m" pr1 pr2 pr1 (fun _ _ -> memoise_add_pure_P_x l p) l p
      
and memoise_add_pure_N_x l p = memoise_add_pure_aux l p Implied_N
and memoise_add_pure_P_x l p = memoise_add_pure_aux l p Implied_P

and create_memo_group_wrapper (l1:b_formula list) status : memo_pure =
  Debug.no_2 "create_memo_group_wrapper"
      (fun bl -> List.fold_left (fun r b -> r ^ (!print_bf_f b)) "" bl)
      (fun s -> "") !print_mp_f create_memo_group_wrapper_a l1 status 
      
and create_memo_group_wrapper_a (l1:b_formula list) status : memo_pure = 
  let l = List.map (fun c -> (c, None)) l1 in
  create_memo_group l [] status 

and anon_partition_x (l1:(b_formula *(formula_label option)) list) = 
  List.fold_left (fun (a1,a2) (c1,c2)-> 
      if (List.exists is_anon_var (bfv c1)) then (a1,(BForm (c1,c2))::a2) else ((c1,c2)::a1,a2)
  ) ([],[]) l1

and anon_partition (l1:(b_formula *(formula_label option)) list) =
  let pr1 = fun bl -> "[" ^ (List.fold_left (fun res (b,_) -> res ^ (!print_bf_f b)) "" bl) ^ "]" in
  let pr_out = pr_pair (pr_list (pr_pair !CP.print_b_formula pr_none)) (pr_list !CP.print_formula) in
  Debug.no_1 "anon_partition" pr1 pr_out anon_partition_x l1


and create_memo_group (l1:(b_formula * (formula_label option)) list) 
    (l2:formula list) (status:prune_status)
    : memo_pure =
  let pr1 = fun bl -> "[" ^ (List.fold_left (fun res (b,_) -> res ^ (!print_bf_f b)) "" bl) ^ "]" in
  let pr2 = fun fl -> "[" ^ (List.fold_left (fun res f -> res ^ (!print_p_f_f f)) "" fl) ^ "]" in
  Debug.no_3 "[mcpure.ml] create_memo_group" pr1 pr2 (fun s -> "") !print_mp_f create_memo_group_x l1 l2 status

and create_memo_group_x 
      (l1: (b_formula * (formula_label option)) list) 
      (l2: formula list) (status: prune_status) : memo_pure =	 
  let l1, to_slice2 = anon_partition l1 in
  let l1, to_slice1 = memo_norm l1 in
  let l2 = to_slice1 @ to_slice2 @ l2 in
  (* if !do_slicing then *)
  if not !dis_slc_ann then
    AnnoS.create_memo_group l1 l2 status filter_merged_cons
  else 
    AutoS.create_memo_group l1 l2 status filter_merged_cons

(* with_const; use get_equiv_eq *)
(*
  This attempts to split g into multiple groups if 
  the constraints are disjoint.
*)
and split_mem_grp (g:memoised_group): memo_pure =
  Debug.no_1 "split_mem_grp" !print_mg_f !print_mp_f split_mem_grp_x g

and split_mem_grp_x (g:memoised_group): memo_pure =
  (* if !do_slicing then AnnoS.split_mem_grp g *)
  if not !dis_slc_ann then AnnoS.split_mem_grp g
  else AutoS.split_mem_grp g

(* this pushes an exist into a memo-pure;
   it is probably useful consider qv in aset for elimination.
   proc : 
   (i) find rs = overlap between qv and domain(aset)
   (ii) prepare subs: [x->o] or [x->c] or [x->x1] and 
   elim x from aset and other locations
   (iii) subtract qv-dom(subs) and add to exists
   (iv) normalise aset
*)
(* both with_const and no_const needed *)
(* finds eq overlap with qv and substitutes the equalities into grp, 
 * returns the qv vars that have not been substituted and the 
 * memo_pure with the substitution performed *)

and memo_pure_push_exists_eq (qv:spec_var list) (f0:memo_pure) pos : (memo_pure * spec_var list) = 
  Debug.no_2 "memo_pure_push_exists_eq" !print_sv_l_f !print_mp_f
      (fun (c, vl)-> !print_mp_f c ^"\n to be q vars: "^(!print_sv_l_f vl)) (fun qv f0 -> memo_pure_push_exists_eq_x qv f0 pos) qv f0	  
      
and memo_pure_push_exists_eq_x (qv: spec_var list) (f0: memo_pure) pos : (memo_pure * spec_var list) =
  let split_eqs eq_list qv  = 
    let aliases  = List.map (fun c -> (c, EMapSV.find_equiv_all c eq_list)) qv in
    let rec find_subst r l = match l with
      | [] -> r
      | (c1, [])::t -> find_subst r t
      | (c1, c2)::t -> 
            try
              let s = List.find (fun c -> not(Gen.BList.mem_eq eq_spec_var c qv)) c2 in
              find_subst ((c1,s)::r) t
            with _ -> 
                try
                  let nc2 = List.find (fun c -> not (eq_spec_var c1 c)) c2 in
		  let nc2 = try snd (List.find (fun (c,_)-> eq_spec_var c nc2) r) with _ -> nc2 in
		  let r = List.map (fun (d1,d2)-> if eq_spec_var d2 c1 then (d1,nc2) else (d1,d2)) r in
                  let new_t  = List.map (fun (q1, q2) -> (q1,List.filter (fun c -> not (eq_spec_var c1 c)) q2)) t in
                  find_subst ((c1,nc2)::r) new_t
                with _ -> find_subst r t
    in
    find_subst [] aliases 
  in
  let split_eqs eq_list qv = Debug.no_2 "MCP.split_eqs " EMapSV.string_of !print_svl (pr_list (pr_pair !print_sv !print_sv)) split_eqs eq_list qv in
  let all_aliases = List.fold_left (fun acc grp -> acc @ grp.memo_group_aset) [] f0 in
  let to_subst = split_eqs all_aliases qv in
  let subst_vars = fst (List.split to_subst) in
  let r_v = Gen.BList.difference_eq eq_spec_var qv subst_vars in
  let r = List.fold_left (fun acc (c1, c2) ->
      let l = conv_var_to_exp c2 in
      match l with
	| Null _
	| IConst _ -> memo_apply_one_exp (c1, l) acc
	| Var (v, _) -> m_apply_one (c1, v) acc
	| _ -> acc) f0 to_subst in
  (r, r_v)
      
and memo_pure_push_exists_slice (f_simp,do_split) (qv:spec_var list) (f0:memo_pure) pos : memo_pure =
  Debug.no_2 "memo_pure_push_exists_slice" !print_sv_l_f !print_mp_f !print_mp_f
      (fun qv f0 -> memo_pure_push_exists_slice_x (f_simp,do_split) qv f0 pos) qv f0
      
(* pushes the exists into the individual groups, 
 * picks the simple and complex constraints related to qv, 
 * combines them into a formula *)
and memo_pure_push_exists_slice_x (f_simp, do_split) (qv: spec_var list) (f0: memo_pure) pos : memo_pure =  
  (* Builds a formula to be simplified with the constraints related to qv *)
  (* Ex x, y. A(x) /\ B(y) <-> Ex x. A(x) /\ Ex y. B(y) iff x notin FV(B) /\ y notin FV(A) *)
  
  (* Get relevant constraints with respect to qv *)  
  let pick_rel_constraints slice cons aset =
    let equiv_lst = get_equiv_eq_with_const aset in
    let nas, drp3 = List.partition (fun (c1, c2) -> (List.exists (eq_spec_var c1) qv) || (List.exists (eq_spec_var c2) qv)) equiv_lst in
    let r, drp1 = List.partition (fun c -> (Gen.BList.overlap_eq eq_spec_var (bfv c.memo_formula) qv)) cons in
    let r = List.filter (fun c -> not (c.memo_status = Implied_R)) r in
    let ns, drp2 = List.partition (fun c -> (Gen.BList.overlap_eq eq_spec_var (fv c) qv)) slice in 
    let aset = List.fold_left (fun a (c1, c2) -> add_equiv_eq_with_const a c1 c2) empty_var_aset drp3 in 
    let fand1 = List.fold_left (fun a c -> mkAnd a (BForm (c.memo_formula, None)) pos) (mkTrue pos) r in
    let fand2 = List.fold_left (fun a c -> mkAnd a c pos) fand1 ns in
    let fand3 = List.fold_left (fun a (c1, c2) -> mkAnd a (BForm (((form_bform_eq_with_const c1 c2), None), None)) pos) fand2 nas in
    (fand3, drp1, drp2, aset)
  in
  
  (* Simplify relevant constraints and form new memo groups *)
  let helper mg =
    let (to_simpl, rem_cons, rem_slice, rem_aset) = pick_rel_constraints mg.memo_group_slice mg.memo_group_cons mg.memo_group_aset in
    let after_simpl = f_simp qv to_simpl pos in
    let after_elim_trues = List.filter (fun c -> not (isConstTrue c)) (split_conjunctions after_simpl) in
    let n_memo_group_fv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv qv in
    let n_memo_group_lv = 
      (* if !do_slicing then *)
      if not !dis_slc_ann then
        Gen.BList.difference_eq eq_spec_var
            (Gen.BList.remove_dups_eq eq_spec_var mg.memo_group_linking_vars) qv
      else []
    in
    let r = {
        memo_group_fv = n_memo_group_fv;
        memo_group_linking_vars = n_memo_group_lv;
        memo_group_changed = true;
	      (* TODO: Slicing UNSAT *)
	      memo_group_unsat = true; 
        memo_group_cons = rem_cons;
        memo_group_slice = rem_slice @ after_elim_trues;
        memo_group_aset = rem_aset;
    } in
    if do_split then split_mem_grp r else [r] 
  in

  let helper mg = 
    Debug.no_1 "memo_pure_push_exists_slice@heper" !print_mg_f !print_mp_f
    helper mg
  in 
  
  let () = Gen.Profiling.push_time "push_exists_slicing" in
  (* Consider only constraints which are relevant to qv *)
  let rel_mg, non_rel_mg = List.partition (fun mg -> Gen.BList.overlap_eq eq_spec_var qv mg.memo_group_fv) f0 in
  let rel_mg = 
    (* if !do_slicing then *)
    if not !dis_slc_ann then
      (* Merge relevant constraints together - For soundness *)
      let l = MG_Constr_AnS.constr_of_atom_list rel_mg in
      let sl = MG_AnS.split_by_fv qv l in
      MF_AnS.memo_pure_of_mg_slice sl None
    else rel_mg
  in
  let res = (List.concat (List.map helper rel_mg)) @ non_rel_mg in
  let () = Gen.Profiling.pop_time "push_exists_slicing" in res
                                                              
(* Pushes exists qv over f0. It takes two steps:
   First: searches for substitutions in the eq set,
   this avoids some simplify calls.
   Second: pushes the rest of the qv vars through
   memo_pure_push_exists_slice which picks relevant constraints
   ands them and sends them to simplify
*)
and memo_pure_push_exists_all fs qv f0 pos =
  Debug.no_3 "memo_pure_push_exists_all" !print_sv_l_f !print_mp_f (fun _ -> "")
      !print_mp_f (memo_pure_push_exists_all_x fs) qv f0 pos
      
and memo_pure_push_exists_all_x (f_simp,do_split) (qv:spec_var list) (f0:memo_pure) pos : memo_pure=
  if qv==[] then f0
  else
    let (f0,nqv) = memo_pure_push_exists_eq qv f0 pos in
    memo_pure_push_exists_slice (f_simp,do_split) nqv f0 pos

and memo_pure_push_exists (qv:spec_var list) (c:memo_pure) =
  Debug.no_2 "memo_pure_push_exists_m"
      !print_svl !print_mp_f !print_mp_f
      memo_pure_push_exists_x qv c

and memo_pure_push_exists_x (qv:spec_var list) (c:memo_pure):memo_pure = 
  if qv==[] then c
  else
    memo_pure_push_exists_all ((fun w f p-> mkExists w f None p),false) qv c no_pos

and rename_vars_memo_pure (mp : memo_pure) arg =
  let replace x arg = (* Replace x by its assoc in arg *)
    try List.assoc x arg
    with | Not_found -> x in
  (* Do not rename a bound variable *)
  let f_arg_f arg x =
    match x with
      | Forall (sv, _, _, _) -> List.remove_assoc sv arg
      | Exists (sv, _, _, _) -> List.remove_assoc sv arg
      | _ -> arg
  in
  let f_arg_orig arg x = arg in
  
  let f_formula arg x = None in

  (* Process in exp first *)
  (* spec_var in BagIn, BagNotIn, BVar, BagMin, BagMax of b_formula *)
  (* will be renamed later by f_b_formula_2 *)
  let f_b_formula_1 arg x = None in
  let f_b_formula_2 arg x = 
    let (pf, anno) = x in 
    match pf with
      | BVar (sv, l) -> Some ((BVar (replace sv arg, l), anno), None)
      | BagMin (sv1, sv2, l) -> Some ((BagMin (replace sv1 arg, replace sv2 arg, l), anno), None)
      | BagMax (sv1, sv2, l) -> Some ((BagMax (replace sv1 arg, replace sv2 arg, l), anno), None)
      | BagIn (sv, e, l) -> Some ((BagIn (replace sv arg, e, l), anno), None)
      | BagNotIn (sv, e, l) -> Some ((BagNotIn (replace sv arg, e, l), anno), None)
      | _ -> None
  in

  (* spec_var in ArrayAt will be renamed later by f_exp_2 *)
  let f_exp_1 arg x =
    match x with
      | Var (sv, l) -> Some (Var (replace sv arg, l), None)
      | _ -> None
  in
  let f_exp_2 arg x =
    match x with
      | ArrayAt (sv, e, l) -> Some (ArrayAt(replace sv arg, e, l), None)
      | _ -> Some (x, None)
  in
  (* Do not change anything *)
  let f_exp_3 arg x = Some (x, None) in

  let f_comb _ = None in 
  
  let f_grp arg x = None in
  let f_cons x arg =
    let n_memo_formula, _ = trans_b_formula x.memo_formula arg (f_b_formula_1, f_exp_1) (f_arg_orig, f_arg_orig) f_comb in
    let n_memo_formula, _ = trans_b_formula n_memo_formula arg (f_b_formula_1, f_exp_2) (f_arg_orig, f_arg_orig) f_comb in
    let n_memo_formula, _ = trans_b_formula n_memo_formula arg (f_b_formula_2, f_exp_3) (f_arg_orig, f_arg_orig) f_comb in
    ({x with memo_formula = n_memo_formula}, None)
  in
  
  let f_aset arg x = (EMapSV.rename_eset_with_key (fun e -> replace e arg) x, []) in

  let f_slice x arg =
    let n_x, _ = trans_formula x arg (f_formula, f_b_formula_1, f_exp_1) (f_arg_f, f_arg_orig, f_arg_orig) f_comb in
    let n_x, _ = trans_formula n_x arg (f_formula, f_b_formula_1, f_exp_2) (f_arg_f, f_arg_orig, f_arg_orig) f_comb in
    let n_x, _ = trans_formula n_x arg (f_formula, f_b_formula_2, f_exp_3) (f_arg_f, f_arg_orig, f_arg_orig) f_comb in
    (n_x, None)
  in
  
  let f_fv x arg = (replace x arg, None) in

  let n_mp, _ = trans_memo_formula mp arg (f_grp, f_cons, f_aset, f_slice, f_fv) f_arg_orig f_comb in
  n_mp
      
(* Do not push Exists on the linking vars if the formula is in LHS *)
(* Rename those linking vars by fresh names -> instantiation *)
and memo_pure_push_exists_lhs (qv:spec_var list) (c:memo_pure) : memo_pure =
  let lv = List.fold_left (fun acc mg -> acc @ mg.memo_group_linking_vars) [] c in

  (* Rename linking vars which need to push Exists *)
  let nlv_ex = Gen.BList.difference_eq eq_spec_var qv lv in
  let lv_ex = Gen.BList.difference_eq eq_spec_var qv nlv_ex in
  let n_lv_ex = List.map (fun sv -> (sv, match sv with | SpecVar (t, i, p) -> SpecVar (t, fresh_any_name i, p))) lv_ex in

  let n_c = rename_vars_memo_pure c n_lv_ex in

  (*let () = print_string ("memo_pure_push_exists_lhs: n_c: " ^ (!print_mp_f n_c) ^ "\n") in*)
  
  memo_pure_push_exists nlv_ex n_c
      
and memo_norm (l:(b_formula * (formula_label option)) list): b_formula list * formula list =
  Debug.no_1 "memo_norm" (fun l -> List.fold_left (fun a (bf,_) -> a ^ (!print_bf_f bf)) "" l)
      (fun (bfl, fl) ->
	  "[" ^ (List.fold_left (fun a bf -> a ^ "," ^ (!print_bf_f bf)) "" bfl) ^ "]" ^
	      "[" ^ (List.fold_left (fun a f -> a ^ (!print_p_f_f f)) "" fl) ^ "]")
      memo_norm_x l
      
and memo_norm_x (l:(b_formula *(formula_label option)) list): b_formula list * formula list = 
 (* let rec get_head e = match e with 
    | Null _ -> "Null"
    | Var (v,_) -> name_of_spec_var v
    | Level (v,_) -> name_of_spec_var v
    | IConst (i,_)-> string_of_int i
    | FConst (f,_) -> string_of_float f
    | AConst (f,_) -> string_of_heap_ann f
    | InfConst(i,_) -> i
    | Tsconst (f,_) -> Tree_shares.Ts.string_of f
    | Add (e,_,_) | Subtract (e,_,_) | Mult (e,_,_) | Div (e,_,_)
    | Max (e,_,_) | Min (e,_,_) | BagDiff (e,_,_) | ListCons (e,_,_)| ListHead (e,_) 
    | ListTail (e,_)| ListLength (e,_) | ListReverse (e,_)  -> get_head e
    | Bag (e_l,_) | BagUnion (e_l,_) | BagIntersect (e_l,_) | List (e_l,_) | ListAppend (e_l,_)-> 
	  if (List.length e_l)>0 then get_head (List.hd e_l) else "[]"
    | Func (a,i,_) -> (name_of_spec_var a) ^ "(" ^ (String.concat "," (List.map get_head i)) ^ ")"
    | ArrayAt (a,i,_) -> (name_of_spec_var a) ^ "[" ^ (String.concat "," (List.map get_head i)) ^ "]" (* An Hoa *)    
  in*)
  
  (*let e_cmp e1 e2 =  String.compare (get_head e1) (get_head e2) in
  
  let rec get_lists (e:exp) (disc:int): exp list * exp list = match e with
    | Add (e1,e2,l)-> 
	  if (disc<>1) then ([e],[])
	  else let (lp1,ln1),(lp2,ln2) = get_lists e1 disc, get_lists e2 disc in
	  (lp1@lp2,ln1@ln2) 
    | Subtract (e1,e2,l)->
	  if (disc<>1) then ([e],[])
	  else let (lp1,ln1),(ln2,lp2) = get_lists e1 disc, get_lists e2 disc in
	  (lp1@lp2,ln1@ln2) 
    | Mult (e1,e2,l)-> 
	  if (disc<>(-1)) then ([e],[])
	  else let (lp1,ln1),(lp2,ln2) = get_lists e1 disc, get_lists e2 disc in
	  (lp1@lp2,ln1@ln2)       
    | Div (e1,e2,l)-> 
	  if (disc<>(-1)) then ([e],[])
	  else let (lp1,ln1),(ln2,lp2) = get_lists e1 disc, get_lists e2 disc in
	  (lp1@lp2,ln1@ln2) 
    | Null _ | Var _ | IConst _ | AConst _ | InfConst _ | Tsconst _ | FConst _ | Max _  | Min _ | Bag _ | BagUnion _ | BagIntersect _ 
    | Level _
    | BagDiff _ | List _ | ListCons _ | ListHead _ | ListTail _ | ListLength _ | ListAppend _ | ListReverse _ 
    | ArrayAt _ | Func _ -> ([e],[]) (* An Hoa *) in*)
  
  (*let rec norm_expr e = match e with
    | Null _ | Var _ | IConst _ | FConst _ | AConst _ | Tsconst _ | InfConst _ 
    | Level _ -> e
    | Add (e1,e2,l) -> cons_lsts e 1 (fun c-> Add c) (fun d-> Subtract d) (IConst (0,l))
    | Subtract (e1,e2,l) -> cons_lsts e 1 (fun c-> Add c) (fun d-> Subtract d) (IConst (0,l))
    | Mult (e1,e2,l) -> cons_lsts e (-1) (fun c-> Mult c) (fun d-> (*print_string "called \n";*) Div d) (IConst (1,l))
    | Div (e1,e2,l) -> cons_lsts e (-1) (fun c-> Mult c) (fun d-> Div d) (IConst (1,l))
    | Max (e1,e2,l)->
	  let e1,e2 = norm_expr e1, norm_expr e2 in
	  if(e_cmp e1 e2)>0 then Max(e1,e2,l) else Max(e2,e1,l)
    | Min (e1,e2,l) ->
	  let e1,e2 = norm_expr e1, norm_expr e2 in
	  if(e_cmp e1 e2)>0 then Min(e1,e2,l) else Min(e2,e1,l)
    | Bag (e,l)-> Bag ( List.sort e_cmp (List.map norm_expr e), l)    
    | BagUnion (e,l)-> BagUnion ( List.sort e_cmp (List.map norm_expr e), l)    
    | BagIntersect (e,l)-> BagIntersect ( List.sort e_cmp (List.map norm_expr e), l)    
    | BagDiff (e1,e2,l) -> BagDiff (norm_expr e1, norm_expr e2, l)
    | List (e,l)-> List (List.sort e_cmp (List.map norm_expr e), l)    
    | ListCons (e1,e2,l)-> ListCons(norm_expr e1, norm_expr e2,l)      
    | ListHead (e,l)-> ListHead(norm_expr e, l)      
    | ListTail (e,l)-> ListTail(norm_expr e, l)      
    | ListLength (e,l)-> ListLength(norm_expr e, l)
    | ListAppend (e,l) -> ListAppend ( List.sort e_cmp (List.map norm_expr e), l)    
    | ListReverse (e,l)-> ListReverse(norm_expr e, l)
    | Func (a,i,l) -> Func (a, List.map norm_expr i, l)
    | ArrayAt (a,i,l) -> ArrayAt (a, List.map norm_expr i, l) (* An Hoa *)
	  
  and cons_lsts (e:exp) (disc:int) cons1 cons2 (nel:exp) : exp=     
    let lp,ln = get_lists e disc in
    let lp = List.sort e_cmp (List.map norm_expr lp) in
    let ln = List.sort e_cmp (List.map norm_expr ln) in
    if (List.length lp)>0 then
      let a = List.fold_left (fun a c-> cons1(a,c,no_pos)) (List.hd lp) (List.tl lp) in
      List.fold_left(fun a c-> cons2 (a,c,no_pos)) a ln
    else List.fold_left(fun a c-> cons2 (a,c,no_pos)) nel ln in*)

  (*  let norm_bf (c1:b_formula) : (b_formula option) =
      let c1 = b_form_simplify c1 in
      match c1 with
      | Lt  (e1,e2,l) -> Some (Lt  (norm_expr e1,norm_expr e2,l))
      | Lte (e1,e2,l) -> Some (Lte (norm_expr e1,norm_expr e2,l))
      | Gt  (e1,e2,l) -> Some (Lt  (norm_expr e2,norm_expr e1,l))
      | Gte (e1,e2,l) -> Some (Lte (norm_expr e2,norm_expr e1,l))
      | Eq  (e1,e2,l) -> 
      let e1,e2 = norm_expr e1,norm_expr e2 in
      if(eqExp e1 e2) then Some(BConst(true,no_pos)) else Some(Eq(e1,e2,l))
      | Neq (e1,e2,l) -> Some (Neq(norm_expr e1,norm_expr e2,l))
      | BagIn (v,e,l) -> Some (BagIn (v, norm_expr e, l))
      | BagNotIn (v,e,l) -> Some (BagNotIn (v, norm_expr e, l))
      | ListIn (e1,e2,l) -> Some (ListIn (norm_expr e1,norm_expr e2,l))
      | ListNotIn (e1,e2,l) -> Some (ListIn (norm_expr e1,norm_expr e2,l))
      | BConst _ | BVar _ | EqMax _ 
      | EqMin _ |  BagSub _ | BagMin _ 
      | BagMax _ | ListAllN _ | ListPerm _ -> None in*)
  
  Gen.Profiling.push_time "memo_norm";
  let l = List.fold_left (fun (a1,a2) (c1,c2)-> 
      match norm_bform_option(*_debug*) c1 with
	| Some c1 -> (c1::a1,a2)
	| None -> (a1,(BForm(c1,c2))::a2)) ([],[]) l in
  Gen.Profiling.pop_time "memo_norm";l

(*
  let l = List.fold_left (fun (a1,a2) (c1,c2)-> 
    let c1 = b_form_simplify c1 in
    match c1 with
      | Lt  (e1,e2,l) -> (Lt  (norm_expr e1,norm_expr e2,l)::a1,a2)
      | Lte (e1,e2,l) -> (Lte (norm_expr e1,norm_expr e2,l)::a1,a2)
      | Gt  (e1,e2,l) -> (Lt  (norm_expr e2,norm_expr e1,l)::a1,a2)
      | Gte (e1,e2,l) -> (Lte (norm_expr e2,norm_expr e1,l)::a1,a2)
      | Eq  (e1,e2,l) -> 
        let e1,e2 = norm_expr e1,norm_expr e2 in
        if(eqExp e1 e2) then (a1,a2) else (Eq(e1,e2,l)::a1,a2)
      | Neq (e1,e2,l) -> (Neq(norm_expr e1,norm_expr e2,l)::a1,a2)
      | BagIn (v,e,l) -> (BagIn (v, norm_expr e, l)::a1,a2)
      | BagNotIn (v,e,l) -> (BagNotIn (v, norm_expr e, l)::a1,a2)
      | ListIn (e1,e2,l) -> (ListIn (norm_expr e1,norm_expr e2,l)::a1,a2)
      | ListNotIn (e1,e2,l) -> (ListIn (norm_expr e1,norm_expr e2,l)::a1,a2)
      | BConst _ | BVar _ | EqMax _ 
      | EqMin _ |  BagSub _ | BagMin _ 
      | BagMax _ | ListAllN _ | ListPerm _ -> (a1,(BForm(c1,c2))::a2)) ([],[]) l in
*)
  
let memo_norm_wrapper (l:b_formula list): b_formula list = 
 let l = List.map (fun c-> (c,None)) l in
 fst (memo_norm l)
  
(* simpl_b_f -> semantically simplifies a b_formula
   simpl_p_f -> syntactic simpl of individual small formula
   s_f -> semantic simplification of formula*)
  
let simpl_memo_pure_formula_x simpl_b_f simpl_p_f(f:memo_pure) s_f: memo_pure = 
  List.map (fun c-> {c with 
    memo_group_cons = List.map (fun c-> {c with memo_formula = simpl_b_f c.memo_formula}) c.memo_group_cons;
    memo_group_changed = true;
    memo_group_slice = list_of_conjs (s_f ((*simpl_p_f *)(conj_of_list c.memo_group_slice no_pos)))}) f  

let simpl_memo_pure_formula simpl_b_f simpl_p_f (f:memo_pure) s_f: memo_pure =
  Debug.no_1 "simpl_memo_pure_formula"
      !print_mp_f !print_mp_f
      (fun _ -> simpl_memo_pure_formula_x simpl_b_f simpl_p_f f s_f) f
  
let memo_drop_null self l = List.map (fun c -> {c with memo_group_slice = List.map (fun c-> drop_null c self false ) c.memo_group_slice}) l       
         
(*changes the status of the implied constraints to Implied_R in l if 
those constraints appear in the cons list of memoised constraints
this is called in order to change 
*)
let memo_change_status cons l =
  let lcns = List.map (fun cns-> (bfv cns, cns)) cons in
  List.map (fun grp-> 
    List.fold_left (fun a (vcns,cns)-> 
      if ((List.length (Gen.BList.intersect_eq eq_spec_var vcns grp.memo_group_fv))<=0) then a
      else 
        let ncns = List.map 
          (fun c-> 
            if not(eq_b_formula_no_aset c.memo_formula cns) then c
            else {c with memo_status=Implied_R}
          ) a.memo_group_cons in
        {a with memo_group_cons= ncns}
    ) grp lcns
  ) l
  
let memo_find_relevant_slice_orig fv l = List.find (fun d -> Gen.BList.subset_eq eq_spec_var fv d.memo_group_fv) l

let memo_find_relevant_slice_slicing fv l =
  let rs = List.find (fun d -> Gen.BList.subset_eq eq_spec_var fv d.memo_group_fv) l in
  List.fold_left (fun acc s ->
      { memo_group_fv = acc.memo_group_fv @ s.memo_group_fv;
      memo_group_linking_vars = [];
      memo_group_cons = acc.memo_group_cons @ s.memo_group_cons;
      memo_group_slice = acc.memo_group_slice @ s.memo_group_slice;
      memo_group_changed = acc.memo_group_changed || s.memo_group_changed;
      memo_group_unsat = true; (* TODO: Slicing UNSAT *)
      memo_group_aset = EMapSV.merge_eset acc.memo_group_aset s.memo_group_aset;
      }
  ) rs l

let memo_find_relevant_slice fv l =
  memo_find_relevant_slice_orig fv l
  (*
  if !do_slicing then
	memo_find_relevant_slice_slicing fv l
  else
	memo_find_relevant_slice_orig fv l
  *)
  
let memo_find_relevant_slices fv l = List.filter (fun d ->  Gen.BList.overlap_eq eq_spec_var fv d.memo_group_fv) l

let memo_get_asets fv l = 
  let r = memo_find_relevant_slices fv l in
  match r with
    | [] -> empty_var_aset
    | h::t -> List.fold_left (fun a c-> EMapSV.merge_eset a c.memo_group_aset) h.memo_group_aset t 
    
let memo_changed d = d.memo_group_changed

let memo_changed d = 
  Debug.no_1 "memo_changed" pr_none string_of_bool memo_changed d


(* checks wether the p_cond constraint can be syntactically dismissed (equal to a contradiction)
   if equal to an implied cond then it can be dropped as it is useless as a pruning condition
   throws an exception if p_cond is not found in corr*)    
   
let memo_f_neg_norm (p:b_formula) : b_formula = 
  match norm_bform_option (memo_f_neg p) with
    | Some s-> s
    | None -> Error.report_error 
      {Error.error_loc = no_pos; Error.error_text = "memo_f_neg_norm: the negation can not be normalized to a simple b_formula"}
   
let memo_check_syn_prun_imply (p,pn,pr_branches) crt_br corr  = 
  let f = Cpure.eq_spec_var_aset corr.memo_group_aset in
  let f_f x =  
    if equalBFormula_f f x.memo_formula p then Some []
    else if equalBFormula_f f x.memo_formula pn then Some pr_branches
    else None in
  Gen.BList.list_find f_f corr.memo_group_cons

let memo_check_syn_prun p c corr =  memo_check_syn_prun_imply p c corr
    
let memo_check_syn_prun_debug (p,pn,br) c corr = 
  let () = print_string (" Check_syn1: "^(!print_bf_f p)^"\n") in
  let () = print_string (" Check_syn2: "^(!print_mp_f [corr])^"\n") in
    memo_check_syn_prun_imply (p,pn,br) c corr
    
let transform_memo_formula f l : memo_pure =
  let (f_memo, f_aset, f_formula, f_b_formula, f_exp) = f in
  let r = f_memo l in 
	match r with
	| Some e1 -> e1
	| None  -> List.map (fun c -> {
      memo_group_fv = c.memo_group_fv;
	  	memo_group_linking_vars = c.memo_group_linking_vars;
      memo_group_changed = true;
			(* TODO: Slicing UNSAT: The transformed formula seems not be changed *)
			memo_group_unsat = c.memo_group_unsat; 
      memo_group_cons = List.map (fun c -> {c with memo_formula = transform_b_formula (f_b_formula, f_exp) c.memo_formula}) c.memo_group_cons;
      memo_group_slice = List.map (transform_formula f) c.memo_group_slice;
      memo_group_aset = match (f_aset c.memo_group_aset) with | None -> c.memo_group_aset | Some s -> s;
    }) l
		
let transform_memo_formula f l =
	let pr = !print_mp_f in
	Debug.no_1 "transform_memo_formula" pr pr
	(fun _ -> transform_memo_formula f l) l

let process_cons_l (f:memoised_constraint list):formula list =
  let filtl = List.filter (fun c-> match c.memo_status with | Implied_R -> false |_-> true) f in
  List.map (fun c-> BForm (c.memo_formula,None)) filtl 
  (*List.fold_left (fun a c -> match c with
    | Implied_dupl -> a
    | _ -> mkAnd a c.memo_group_cons no_pos) (mkTrue no_pos) f*)
    
let process_slice impl (f:memoised_group): formula * formula = 
  let asetf = fold_aset f.memo_group_aset in
  let rec red_test impl (l_red,l_must) l = match l with
    | [] -> (l_red,l_must)
    | x::xs -> 
      let nf = join_conjunctions (xs@l_must) in
      let totalf = mkAnd nf asetf no_pos in
      if (impl totalf x) then 
        red_test impl (x::l_red,l_must) xs
      else 
        red_test impl (l_red,x::l_must) xs in
  let l1,l2 = red_test impl ([],[]) (process_cons_l f.memo_group_cons)   in
  (join_conjunctions l1, join_conjunctions l2)
	
let check_redundant impl (f:memo_pure): unit = List.iter (fun c-> 
  let red_f,n_red_f = process_slice impl c in
  print_string ("redundant: "^(!print_p_f_f red_f)^"\n nonredundant: "^(!print_p_f_f n_red_f)^"\n" ) ) f
  
let isImpl_dupl c = match c.memo_status with | Implied_R -> true | _ -> false 
let isImplT c = match c.memo_status with | Implied_N -> true | _ -> false 
let isCtrInSet aset s c =  List.exists (fun d-> eq_b_formula aset c.memo_formula d.memo_formula) s  

(* WN : what does this cons_filter do? *)
let cons_filter (g:memo_pure) (f:memoised_constraint->bool) : memo_pure = 
    List.map (fun c-> {c with memo_group_cons = List.filter f c.memo_group_cons}) g

let slow_imply_x impl nf rhs =
  let x = Gen.Profiling.gen_time_msg () in
  try 
    (Gen.Profiling.push_time_no_cnt x;
    Gen.Profiling.push_time "slow_imply");
      let r = impl nf rhs in
      (Gen.Profiling.pop_time "slow_imply";
      Gen.Profiling.pop_time_to_s_no_count x);
      r
  with _ -> (Gen.Profiling.pop_time_to_s_no_count x ;false) 

let slow_imply impl nf rhs =
  Debug.no_2 "slow_imply"
      !print_formula !print_formula string_of_bool
      (fun _ _ -> slow_imply_x impl nf rhs) nf rhs
(*
let fast_imply_debug_cmp impl aset (lhs:b_formula list) (rhs:b_formula) : int =
  let lhs_f = join_conjunctions (List.map (fun c-> (BForm (c,None))) lhs) in
  let rhs_f = BForm (rhs,None) in
  let r = fast_imply aset lhs rhs in
  let s = slow_imply impl lhs_f rhs_f in
  if s && (r<=0) then 
    let () = print_string ("fast imply aset :"^(EMapSV.string_of full_name_of_spec_var aset)^"\n") in
    let () = print_string ("fast imply inp :"^(Gen.BList.string_of_f !print_b_formula lhs) )in
    let () = print_string ("fast imply inp :"^" |="^(!print_b_formula rhs)^"\n") in
    let () = print_string ("fast imply out : ==> "^(string_of_int r)^"\n") in
    r
  else r
*)

let elim_redundant_cons_x impl (aset) (asetf:formula) (pn:memoised_constraint list) =  
  let rec helper pn s r e f = match pn with
    | [] -> (s,r,e)
    | c::cs -> 
      if (isCtrInSet aset s c) then helper cs s r (c::e) f
      else
        (*Assume c is not duplicated inside cs. Otherwise, trivially consider redundant
        For example: given c ^ c ^ b, c^b always implies c. Therefore, c is considered
        redundant and removed*)
        let conj_cs = join_conjunctions (List.map (fun c-> (BForm (c.memo_formula,None))) cs) in
        let nf = mkAnd f conj_cs no_pos in
        let b =  Gen.Profiling.push_time "erc_imply";
          let r = slow_imply impl nf (BForm (c.memo_formula,None)) in
          (Gen.Profiling.pop_time "erc_imply"; r)   in                
        if b then
          helper cs s ({c with memo_status = Implied_R}::r) e f
        else helper cs (c::s) r e (mkAnd f (BForm (c.memo_formula,None)) no_pos) in
  helper pn [] [] [] asetf

let elim_redundant_cons(*_slow*) impl (aset) (asetf:formula) (pn:memoised_constraint list) =
  let pr_out (o1,o2,o3)= "(1) " ^ (pr_list !print_mc_f o1) ^ "(2) " ^(pr_list !print_mc_f o2) ^ "(3) " ^ (pr_list !print_mc_f o3) in
  Debug.no_3 "elim_redundant_cons"
      print_alias_set !print_formula (pr_list !print_mc_f) pr_out
      (fun _ _ _ -> elim_redundant_cons_x impl aset asetf pn) aset asetf pn
(*
let elim_redundant_cons_fast_x impl aset asetf pn =  
  let rec helper pn mc s r e f = match pn,mc with
    | [],_ -> (s,r,e)
    | (c::cs),(m::ms) -> 
      let b = 
        (Gen.Profiling.push_time "erc_imply";
        let r = fast_imply(*_debug_cmp impl*) aset (ms@f) m in
          (Gen.Profiling.pop_time "erc_imply";r>0)) in
        if b then  helper cs ms s ({c with memo_status = Implied_R}::r) e f
        else helper cs ms (c::s) r e (m::f) 
    | _ -> Error.report_error {Error.error_loc = no_pos;Error.error_text = "elim_redundant_cons_fast: unexpected pattern"} in       
  let mc=List.map (fun x -> x.memo_formula) pn in    
  helper pn  mc [] [] [] []
*)

(* let elim_redundant_slice impl (f:memoised_group): memoised_group*memoised_group = *)

let elim_redundant_slice_x (impl, simpl) (f:memoised_group): memoised_group * memoised_group = 
  let asetf = fold_aset f.memo_group_aset in
  (*do not elim VarPerm formula*)
  (* let vperm_set, rest = List.partition (fun m_constr -> is_varperm_b m_constr.memo_formula) f.memo_group_cons in *)
  let old_r_set , np_set  = List.partition isImpl_dupl f.memo_group_cons in
  let n_set, p_set  = List.partition isImplT np_set in
  let s_set,r_set, e_set =  elim_redundant_cons impl f.memo_group_aset asetf (n_set@p_set) in
  let r2 = { (List.hd (mkMFalse no_pos)) with memo_group_cons = e_set@r_set (* @vperm_set *) } in (*TO CHECK: should vperm_set in r2 ??? *)
  ({f with memo_group_cons = s_set @ r_set @ old_r_set (* @vperm_set *);
           memo_group_slice = List.concat (List.map (fun c -> list_of_conjs (simpl c)) f.memo_group_slice)},r2)

let elim_redundant_slice (impl, simpl) (f:memoised_group): memoised_group * memoised_group =
  let pr_out = pr_pair !print_mg_f !print_mg_f in
  Debug.no_1 "elim_redundant_slice" !print_mg_f pr_out
      (fun _ -> elim_redundant_slice_x (impl, simpl) f) f

let elim_redundant_aux impl (f:memo_pure): memo_pure*memo_pure = 
  let b =   !suppress_warning_msg in
  suppress_warning_msg := true;
  let r = List.map (elim_redundant_slice impl) f in
  let r = List.split r in
  suppress_warning_msg := b;
  r
  
let elim_redundant impl (f:memo_pure): memo_pure = 
  if (not !Globals.disable_elim_redundant_ctr) then 
    (Gen.Profiling.push_time "elim_redundant_ctr";
    let r = fst (elim_redundant_aux impl f) in
    Gen.Profiling.pop_time "elim_redundant_ctr";
    r)
  else f

let elim_redundant impl (f:memo_pure) : memo_pure  =
  let pr = !print_mp_f in
  Debug.no_1 "elim_redundant" pr pr (fun _ -> elim_redundant impl f) f
  (* let r1,r2 = elim_redundant_aux impl f in *)
  (* print_string ("eliminate_redundant input: "^(!print_mp_f f)^"\n"); *)
  (* print_string ("eliminate_redundant redundant: "^(!print_mp_f r2)^"\n"); *)
  (* print_string ("eliminate_redundant result: "^(!print_mp_f r1)^"\n"); *)
  (* r1 *)

(* wrapper for fast_imply*)
let rec fast_memo_imply (g:memoised_group) (f:b_formula):int =
  Debug.no_2 "fast_memo_imply" !print_mg_f !print_bf_f string_of_int fast_memo_imply_x g f
	
and fast_memo_imply_x (g:memoised_group) (f:b_formula):int = 
  let cons = List.map (fun c-> c.memo_formula) g.memo_group_cons in
  fast_imply g.memo_group_aset cons f

let memo_check_syn_fast (p,pn,pr_branches) crt_br corr  = 
  match (fast_memo_imply corr pn) with
    | 1 -> Some pr_branches
    | _ -> match (fast_memo_imply corr p) with
        | 1 -> Some []
        | _ -> None
 
let replace_memo_pure_label nl f = 
  List.map (fun c-> {c with memo_group_slice = List.map (replace_pure_formula_label nl) c.memo_group_slice;}) f
  
let is_linking_constraint m =
  Gen.BList.subset_eq eq_spec_var m.memo_group_fv m.memo_group_linking_vars 
  
(* SAT functions *)
let is_sat_memo_sub_no_complete f with_dupl with_inv t_is_sat =
  (* let perf = List.filter (fun c -> c.memo_group_unsat) f in *)
  let is_sat m = 
    if is_linking_constraint m then true
    else
      let rel_m = AnnoS.get_rel_mem !Globals.slicing_rel_level m f in
      let merged_m = fold_mem_lst_gen (mkTrue no_pos) with_dupl with_inv true true rel_m in
      t_is_sat merged_m
  in 
  if (isConstMFalse f) then false
  else (not (List.exists (fun m -> not (is_sat m)) f))
(* Ineq utils *)
let is_ineq_linking_memo_group (mg : memoised_group) : bool =
  List.exists (fun mc -> is_ineq_linking_bform mc.memo_formula) mg.memo_group_cons

let is_ineq_linking_memo_group (mg : memoised_group) : bool =
  let pr = !print_mg_f in
  Debug.no_1 "is_ineq_linking_memo_group" pr string_of_bool
      is_ineq_linking_memo_group mg


let exists_contradiction_eq (mem : memo_pure) (ls : spec_var list) : bool =
  (*List.exists (fun mg -> (is_ineq_linking_memo_group mg) && (Gen.BList.subset_eq eq_spec_var mg.memo_group_fv ls)) mem*)
  List.exists (fun mg ->
    (is_ineq_linking_memo_group mg) &&
    (List.exists (fun mc ->
      let bf = mc.memo_formula in
      (* let fv = match (get_bform_neq_args_with_const bf) with *)
        (* | Some (v1, v2) -> [v1; v2]                            *)
        (* | None -> []                                           *)
      (* in Gen.BList.subset_eq eq_spec_var fv ls               *)
      match (get_bform_neq_args_with_const bf) with
        | Some (v1, v2) -> Gen.BList.subset_eq eq_spec_var [v1; v2] ls 
        | None -> false
    ) mg.memo_group_cons)) mem

(* WN : this procedure avoided some SAT calls from
is_sat_memo_sub_no_ineq_slicing_complete inp1 : (([x!=y][x=y & 4<=x]))
is_sat_memo_sub_no_ineq_slicing_complete@4 EXIT out :false
 Can we allow SAT calls to be invoked here,
 as we like to make prover calls explicit.
 *)
         
let is_sat_memo_sub_no_ineq_slicing_complete (mem : memo_pure) with_dupl with_inv t_is_sat : bool =
  if (isConstMFalse mem) then false
  else
    (* create a single eset for memo pure *)
    let m_aset = List.fold_left (fun a mg -> EMapSV.merge_eset a mg.memo_group_aset) [] mem in
    (* parition the eset *)
    let m_apart = EMapSV.partition m_aset in
    let is_sat_one_slice mg =
      if (is_ineq_linking_memo_group mg)
      (* mg is a linking inequality *)
      then not (List.exists (fun mc ->
        let bf = mc.memo_formula in
        match (get_bform_neq_args_with_const bf) with
        | Some (v1, v2) -> List.exists (fun ls -> 
            Gen.BList.subset_eq eq_spec_var [v1; v2] ls) m_apart  
        | None -> false) mg.memo_group_cons) 
      else
        t_is_sat (fold_slice_gen mg with_dupl with_inv true true)
    in
    (* List.fold_left (fun acc mg -> if not acc then acc else is_sat_one_slice mg) true mem *)
    not (List.exists (fun mg -> not (is_sat_one_slice mg)) mem)

let is_sat_memo_sub_no_ineq_slicing_complete (mem : memo_pure) with_dupl with_inv t_is_sat : bool =
  let pr = !print_mp_f in
  Debug.no_1 "is_sat_memo_sub_no_ineq_slicing_complete"
      pr string_of_bool
      (fun _ -> is_sat_memo_sub_no_ineq_slicing_complete mem with_dupl with_inv t_is_sat) mem 

(* IMPLY functions *)
let memo_impl_fail_vars = ref [] 
 
let rec mimply_process_ante with_disj ante_disj conseq str str_time t_imply imp_no =
 Debug.no_3 "mimply_process_ante" (fun x -> string_of_int x) (!print_mp_f) (!print_p_f_f)  
  (fun (c,_,_)-> string_of_bool c) 
  (fun with_disj ante_disj conseq -> mimply_process_ante_x with_disj ante_disj conseq str str_time t_imply imp_no) 
    with_disj ante_disj conseq

and mimply_process_ante_x with_disj ante_disj conseq str str_time t_imply imp_no =
  let n_ante = 
    (* if !do_slicing then  *)
		if not !dis_slc_ann then
      AnnoS.get_rel_ctr !slicing_rel_level conseq ante_disj
    else
      AutoS.get_rel_ctr 1 conseq ante_disj
  in
  (* Assumption: ante_disj is SAT *)
  (* let n_ante = if n_ante == [] then ante_disj else n_ante in *)
  let r = match with_disj with  
    | 0 -> fold_mem_lst_gen (mkTrue no_pos) !no_LHS_prop_drop true false true n_ante
    | 1 -> fold_mem_lst_no_complex (mkTrue no_pos) !no_LHS_prop_drop true n_ante
    | _ -> fold_mem_lst_with_complex (mkTrue no_pos) !no_LHS_prop_drop true n_ante in
  let () = x_dinfo_pp str no_pos in
  let () = x_tinfo_hp (add_str "ante" !Cpure.print_formula) r no_pos in
  let () = x_tinfo_hp (add_str "conseq" !Cpure.print_formula) conseq no_pos in  
  (* print_endline ("ANTE: " ^ (!Cpure.print_formula r)); *)
  (Gen.Profiling.push_time str_time;
  let (rb,_,_) as r = t_imply r conseq ("imply_process_ante:"^(string_of_int !imp_no)) false None in
  Gen.Profiling.pop_time str_time;
  memo_impl_fail_vars:= (if rb then [] else  List.concat (List.map (fun c-> c.memo_group_fv) n_ante));
  r)

and pick_relevant_lhs_constraints choose_algo (nlv, lv) ante_disj =
  Debug.no_3 "pick_relevant_lhs_constraints"
	string_of_int
	(fun (nlv, lv) -> (!print_sv_l_f nlv) ^ (!print_sv_l_f lv))
	!print_mp_f	!print_mp_f
	pick_relevant_lhs_constraints_x choose_algo (nlv, lv) ante_disj
	
and pick_relevant_lhs_constraints_x choose_algo (nlv, lv) ante_disj =
  (*let choose_algo = !opt_imply in*)
  if choose_algo = 0 then
	pick_relevant_lhs_constraints_simpl (nlv@lv) ante_disj
  else if choose_algo = 1 then
	pick_relevant_lhs_constraints_opt_1 (nlv@lv) ante_disj
  else if choose_algo = 2 then
	pick_relevant_lhs_constraints_opt_2 (nlv@lv) ante_disj
  else if choose_algo = 3 then
	pick_relevant_lhs_constraints_opt_3 (nlv@lv) ante_disj
  else
	ante_disj
  
and pick_relevant_lhs_constraints_simpl fv ante_disj =
  List.filter (fun c -> (Gen.BList.overlap_eq eq_spec_var fv c.memo_group_fv)) ante_disj

and pick_relevant_lhs_constraints_opt_1_1 (nlv, lv) ante_disj =
  (*
  let (c_nlv, c_lv) = fv_with_slicing_label conseq in
  
  let ((a_lv1, ante1), rest_ante1) = List.fold_left
	(fun ((lv, ante), r_ante) mg ->
	  let mg_nlv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv mg.memo_group_linking_vars in
	  let cond = Gen.BList.overlap_eq eq_spec_var c_nlv mg_nlv in
	  if cond then ((lv@mg.memo_group_linking_vars, ante@[mg]), r_ante)
	  else ((lv, ante), r_ante@[mg])
	)
	(([],[]), []) ante_disj in

		let n_lv = a_lv1@c_lv in
		let ante2 = List.filter
		(fun mg ->
		let mg_nlv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv mg.memo_group_linking_vars in
		Gen.BList.overlap_eq eq_spec_var n_lv mg_nlv
		) rest_ante1 in

  ante1 @ ante2 (* Algo 1 *)
  *)

  if (lv = []) then
	List.filter (fun c -> (Gen.BList.overlap_eq eq_spec_var nlv c.memo_group_fv)) ante_disj
  else
	let fv = nlv@lv in
	let ((direct_fv, direct_lv, direct_ante), residue_ante) = List.fold_left
	  (fun ((fvd, dlv, atd), r) mg ->
		let mg_ulv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv mg.memo_group_linking_vars in
		let cond1 = (mg_ulv != []) && (Gen.BList.overlap_eq eq_spec_var fv mg_ulv) in
		let cond2 = Gen.BList.list_setequal_eq eq_spec_var mg.memo_group_linking_vars fv in
			(*let _ =
			  if (not cond2) then
			  print_string ("mimply_process_ante_slicing: false\n" ^ (!print_sv_l_f mg.memo_group_linking_vars) ^ (!print_sv_l_f fv))
			  else () in*)
		if (cond1 || cond2) then ((fvd@mg.memo_group_fv, dlv@mg.memo_group_linking_vars, atd@[mg]), r)
		else ((fvd, dlv, atd), r@[(mg_ulv, mg)])
	  )
	  (([], [], []), []) ante_disj in

	let res_lv = Gen.BList.difference_eq eq_spec_var direct_lv fv in
	let res_ulv = Gen.BList.difference_eq eq_spec_var (Gen.BList.difference_eq eq_spec_var direct_fv direct_lv) fv in

	let (_, indirect_ante) = List.split (
	  List.filter
		(
		  fun (mg_ulv, mg) ->
			  (* Version 1 *)
			  (*let mg_ulv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv mg.memo_group_linking_vars in*)
			  (*if mg.memo_group_linking_vars = [] then
				Gen.BList.overlap_eq eq_spec_var mg.memo_group_fv (res_lv@res_ulv)
				else
				Gen.BList.overlap_eq eq_spec_var mg.memo_group_linking_vars res_ulv*)

			  (* Version 2 *)
			  (*Gen.BList.overlap_eq eq_spec_var mg.memo_group_fv res_fv*)

			  (* Version 3 *)
			(Gen.BList.overlap_eq eq_spec_var mg.memo_group_fv res_ulv) || (Gen.BList.overlap_eq eq_spec_var mg_ulv res_lv)
		) residue_ante) in
	direct_ante@indirect_ante

and pick_relevant_lhs_constraints_opt_1 fv ante_disj =
  let () = Gen.Profiling.push_time "--opt-imply 1" in
  let ((direct_fv, direct_lv, direct_ante), residue_ante) = List.fold_left
	  (fun ((fvd, dlv, atd), r) mg ->
		let mg_ulv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv mg.memo_group_linking_vars in
		let cond = Gen.BList.overlap_eq eq_spec_var fv mg_ulv in
		if cond then ((fvd@mg.memo_group_fv, dlv@mg.memo_group_linking_vars, atd@[mg]), r)
		else ((fvd, dlv, atd), r@[mg])
	  )
	  (([], [], []), []) ante_disj in

  let direct_ulv = Gen.BList.difference_eq eq_spec_var direct_fv direct_lv in
  let need_to_find_links = direct_ulv @ fv in

  let linking_ante = List.filter
	(fun mg -> (not (mg.memo_group_linking_vars == [])) && Gen.BList.subset_eq eq_spec_var mg.memo_group_linking_vars need_to_find_links
	) residue_ante in
  let () = Gen.Profiling.pop_time "--opt-imply 1" in
  direct_ante @ linking_ante

and pick_relevant_lhs_constraints_opt_2_1 fv ante_disj = (* exhausted search - TODO: Slicing: fix bugs *)
  let repart acc mg =
	let (ol, nl) = List.partition
	  (fun (vl, mgl) -> Gen.BList.overlap_eq eq_spec_var vl mg.memo_group_fv) acc in
	let n_vl = List.fold_left (fun a (vl, _) -> a@vl) mg.memo_group_fv ol in
	let n_mgl = List.fold_left (fun a (_, mgl) -> a@mgl) [mg] ol in
	(n_vl, n_mgl)::nl
  in
  let n_partitions = List.fold_left repart [] ante_disj in
  List.fold_left
	(fun acc (vl, mgl) ->
	  if Gen.BList.overlap_eq eq_spec_var vl fv then acc@mgl
	  else acc
	)
	[] n_partitions

and pick_relevant_lhs_constraints_opt_2 fv ante_disj = (* exhausted search *)
  let rec exhaustive_collect fv ante =
	let (n_fv, n_ante1, r_ante) = List.fold_left
	  (fun (afv, amc, rmc) mg ->
		if Gen.BList.overlap_eq eq_spec_var afv mg.memo_group_fv then
		  (afv@mg.memo_group_fv, amc@[mg], rmc)
		else (afv, amc, rmc@[mg])
	  ) (fv, [], []) ante in
	if n_fv = fv then n_ante1
	else
	  let n_ante2 = exhaustive_collect n_fv r_ante in
	  n_ante1 @ n_ante2
  in
  
  let () = Gen.Profiling.push_time "--opt-imply 2" in
  let r = exhaustive_collect fv ante_disj in
  let () = Gen.Profiling.pop_time "--opt-imply 2" in r

and pick_relevant_lhs_constraints_opt_3 fv ante_disj = (* exhausted search *)
  let rec exhaustive_collect_with_selection fv ante =
	  let (n_fv, n_ante1, r_ante) = List.fold_left (fun (afv, amc, rmc) (mg_ulv, mg) ->
		  let cond_direct = Gen.BList.overlap_eq eq_spec_var afv mg_ulv in
		  (*let cond_link = ((List.length mg.memo_group_linking_vars) > 1) && (Gen.BList.subset_eq eq_spec_var mg.memo_group_linking_vars afv) in*)
		  let cond_link = (mg_ulv = []) && (Gen.BList.subset_eq eq_spec_var mg.memo_group_linking_vars afv) in
		  if (cond_direct || cond_link) then
		    (afv@mg.memo_group_fv, amc@[mg], rmc)
		  else (afv, amc, rmc@[(mg_ulv, mg)])
	    ) (fv, [], []) ante in
	  if n_fv = fv then n_ante1
	  else
	    let n_ante2 = exhaustive_collect_with_selection n_fv r_ante in
	    n_ante1 @ n_ante2
    in

    let ante_with_ulv = List.map
	  (fun mg ->
	    let mg_ulv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv mg.memo_group_linking_vars in
	    (mg_ulv, mg)
	  ) ante_disj in

  let () = Gen.Profiling.push_time "--opt-imply 3" in
  let r = exhaustive_collect_with_selection fv ante_with_ulv in
  let () = Gen.Profiling.pop_time "--opt-imply 3" in r
	
let mimply_one_conj ante_memo0 conseq t_imply imp_no =
  (* TODO CG : if no complex at all just try one of them *)
  let no_complex = false in
  if not(!Globals.smart_memo) || no_complex
  then mimply_process_ante 2 ante_memo0 conseq
    (* ("IMP #" ^ (string_of_int !imp_no) ^ (*"." ^ (string_of_int 1(*!imp_subno*)) ^ *)" with XPure0")*) ""
    "imply_proc_one_full" t_imply imp_no 
  else
    let xp01,xp02,xp03 = mimply_process_ante 0 ante_memo0 conseq 
      (*("IMP #" ^ (string_of_int !imp_no) ^ (*"." ^ (string_of_int 1(*!imp_subno*)) ^*) " with XPure0 no complex")*) "" 
      "imply_proc_one_ncplx" t_imply imp_no in  
    if not xp01  then  
      let xp01,xp02,xp03 = mimply_process_ante 2 ante_memo0 conseq 
        (* ("IMP #" ^ (string_of_int !imp_no) ^ (*"." ^ (string_of_int 1(*!imp_subno*)) ^ *)" with XPure0")*) ""
        "imply_proc_one_full" t_imply imp_no in  
      if not xp01 then (Gen.Profiling.inc_counter "with_disj_cnt_2_f";(xp01,xp02,xp03)	)
      else (Gen.Profiling.inc_counter "with_disj_cnt_2_s";(xp01,xp02,xp03)	)
    else (Gen.Profiling.inc_counter "with_disj_cnt_0_s";(xp01,xp02,xp03)	)

let mimply_one_conj ante_memo0 conseq_conj t_imply imp_no = 
  Debug.no_4_opt (fun (x,_,_) -> not x) "mimply_one_conj " (!print_mp_f) (!print_p_f_f) (fun _ -> "?")
  (fun x -> string_of_int !x)
  (fun (c,_,_)-> string_of_bool c) 
  mimply_one_conj ante_memo0 conseq_conj t_imply imp_no
 
let rec mimply_conj ante_memo0 conseq_conj t_imply imp_no = 
  (*let () = print_string ("\nMcpure.ml: mimply_conj " ^ (string_of_int !imp_no)) in*)
  match conseq_conj with
    | h :: rest -> 
	      let (r1,r2,r3) = (mimply_one_conj ante_memo0 h t_imply imp_no) in
	      if r1 then 
	        let r1,r22,r23 = (mimply_conj ante_memo0 rest t_imply imp_no) in
	        (r1,r2@r22,r23)
	      else
          (*let () = print_string ("\n failed ante: "^(Cprinter.string_of_pure_formula  
            (fold_mem_lst (mkTrue no_pos ) false ante_memo0))^"\t |- \t"^(Cprinter.string_of_pure_formula h)^"\n") in      *)
          (r1,r2,r3)
    | [] -> (true, [], None)

let mimply_conj ante_memo0 conseq_conj t_imply imp_no = 
  Debug.no_2 "mimply_conj"
      (!print_mp_f) (pr_list !print_p_f_f) (fun (x,_,_) -> string_of_bool x)
      (fun _ _ -> mimply_conj ante_memo0 conseq_conj t_imply imp_no) ante_memo0 conseq_conj

let rec imply_memo ante_memo0 conseq_memo t_imply imp_no =
 Debug.no_2 "imply_memo(inner)" (!print_mp_f)
      (!print_mp_f)
      (fun (r,_,_) -> string_of_bool r)
      (fun ante_memo0 conseq_memo -> imply_memo_x ante_memo0 conseq_memo t_imply imp_no) ante_memo0 conseq_memo

and imply_memo_x ante_memo0 conseq_memo t_imply imp_no (* A -> B & C *) 
    :  bool * (Globals.formula_label option * Globals.formula_label option) list * Globals.formula_label option = 
  match conseq_memo with
    | h :: rest -> 
        let r = fold_mem_lst_to_lst [h] false !no_RHS_prop_drop true in
        let r = List.concat (List.map list_of_conjs r) in
	      let (r1,r2,r3)=(mimply_conj ante_memo0 r t_imply imp_no) in (* A -> B *)
	      if r1 then 
	        let r1,r22,r23 = (imply_memo_x ante_memo0 rest t_imply imp_no) in (* A -> C *)
	        (r1,r2@r22,r23)
	      else (r1,r2,r3)
    | [] -> (true, [], None)

(*and opt_imply_memo_group_slicing ante_mc conseq_mg t_imply imp_no =
  let c_lv = conseq_mg.memo_group_linking_vars in
  let c_nlv = Gen.BList.difference_eq eq_spec_var conseq_mg.memo_group_fv c_lv in
  (true, [], None)
*)
        
let imply_memo ante_memo0 conseq_memo t_imply imp_no =
  if (isConstMFalse ante_memo0) then (true,[],None) (* Slicing: TODO: if a FALSE is found in the ante then return true *)
  else
  let ante_memo0 = 
    if !f_2_slice  || !dis_slicing (* Use one slice for proving (sat, imply) *)
	  then
	  match ante_memo0 with
       | [] -> []
       | [h] -> [h]
       | h::t -> [List.fold_left (fun a c ->
          let na = EMapSV.merge_eset a.memo_group_aset c.memo_group_aset in
            {memo_group_fv = remove_dups_svl (a.memo_group_fv @ c.memo_group_fv);
             memo_group_linking_vars = [];
             memo_group_cons = filter_merged_cons na [a.memo_group_cons; c.memo_group_cons];
             memo_group_changed = true;
						 memo_group_unsat = false; (* Slicing UNSAT: The UNSAT check has already done *)
             memo_group_slice = a.memo_group_slice @ c.memo_group_slice;
             memo_group_aset = na;}) h t]
    else ante_memo0 in
  imply_memo ante_memo0 conseq_memo t_imply imp_no

let imply_memo i ante_memo0 conseq_memo t_imply imp_no=
 Debug.no_2_num i "imply_memo 2" (!print_mp_f)
      (!print_mp_f)
      (fun (r,_,_) -> string_of_bool r)
      (fun ante_memo0 conseq_memo -> imply_memo ante_memo0 conseq_memo t_imply imp_no) ante_memo0 conseq_memo

	
(*let imply_memo_debug ante_memo conseq_memo t_imply =
  let (r1,r2,r3)= imply_memo ante_memo conseq_memo in  
  print_string ("imply_memo input1: "^(!print_mp_f ante_memo)^"\n");
  print_string ("imply_memo input1: "^(!print_mp_f conseq_memo)^"\n");    
  print_string ("imply_memo output: "^(string_of_bool r1)^"\n");
  (r1,r2,r3)*)

let reset_changed f = List.map (fun c-> {c with memo_group_changed = false}) f

let reset_unsat_flag_mem mp = 
	List.map (fun m -> { m with memo_group_unsat = false }) mp

(*
let trans_memo_group (e: memoised_group) (arg: 'a) f f_arg f_comb : (memoised_group * 'b) = 
  let f_grp, f_memo_cons, f_aset, f_slice,f_fv = f in
  match f_grp arg e with 
    | Some e1-> e1
    | None -> 
      let new_arg = f_arg arg e in
      let new_cons,new_rc  = List.split ((List.map (fun c-> f_memo_cons c new_arg)) e.memo_group_cons) in
      let new_aset, new_ra = f_aset new_arg e.memo_group_aset in
      let new_slice, new_rs = List.split ((List.map (fun c-> f_slice c new_arg)) e.memo_group_slice) in
      let new_fv, new_rv =  List.split ((List.map (fun c-> f_fv c new_arg)) e.memo_group_fv) in
      ({e with
        memo_group_fv =new_fv;
        memo_group_cons = new_cons;
        memo_group_slice = new_slice;
        memo_group_aset = new_aset;}, f_comb (new_rc@new_ra@new_rs@new_rv))
  

(*
type: Mcpure_D.memo_pure ->
  'a ->
  ('a -> Mcpure_D.memoised_group -> (Mcpure_D.memoised_group * 'b) option) *
  (Mcpure_D.memoised_constraint -> 'c -> Mcpure_D.memoised_constraint * 'b) *
  ('c -> Mcpure_D.var_aset -> Mcpure_D.var_aset * 'b list) *
  (Cpure.formula -> 'c -> Cpure.formula * 'b) *
  (Cpure.spec_var -> 'c -> Cpure.spec_var * 'b) ->
  ('a -> Mcpure_D.memoised_group -> 'c) ->
  ('b list -> 'b) -> Mcpure_D.memo_pure * 'b
*)

let trans_memo_formula (e: memo_pure) (arg: 'a) f f_arg f_comb : (memo_pure * 'b) = 
  let trans_memo_gr e = trans_memo_group e arg f f_arg f_comb in
  let ne, vals = List.split (List.map trans_memo_gr e) in
  (ne, f_comb vals)*)

	
type mix_formula = 
  | MemoF of Mcpure_D.memo_pure
  | OnePF of Cpure.formula 
  
let print_mix_f  = ref (fun (c:mix_formula) -> "printing not intialized")
let print_mix_formula  = print_mix_f

let consistent_mix_formula (m:mix_formula) : bool =
  match m with
    | MemoF mp -> consistent_memo_pure mp
    | OnePF _ -> true
  
let mix_of_pure f =
	(* if (!Globals.allow_pred_spec or !Globals.do_slicing) *)
  if !Globals.en_slc_ps
	then MemoF (memoise_add_pure_N (mkMTrue ()) f)
  else OnePF f

let mix_of_pure f =
  Debug.no_1 "mix_of_pure"
	!print_p_f_f !print_mix_f
	mix_of_pure f
	  
let pure_of_mix f = match f with
  | OnePF f -> f
  | MemoF f -> fold_mem_lst_with_complex (mkTrue no_pos) false true f 

let memo_of_mix f = match f with
  | OnePF pf -> memoise_add_pure_N (mkMTrue no_pos) pf
  | MemoF mf -> mf

let mix_of_memo f = 
  if !Globals.en_slc_ps then MemoF f
  else OnePF (fold_mem_lst_with_complex (mkTrue no_pos) false true f)
  
let mkMFalse_no_mix = mkMFalse

let mkMTrue_no_mix = mkMTrue
  
let mkMTrue pos = 
	(* if (!Globals.allow_pred_spec or !Globals.do_slicing) *)
	if !Globals.en_slc_ps
	then  MemoF (mkMTrue pos)
	else OnePF (mkTrue pos)
	  
let mkMFalse pos = 
	(* if (!Globals.allow_pred_spec or !Globals.do_slicing) *)
	if !Globals.en_slc_ps
	then MemoF (mkMFalse pos)
	else OnePF (mkFalse pos)  
  
let isConstMFalse mx = match mx with
  | MemoF mf -> isConstMFalse mf
  | OnePF f -> isConstFalse f
  
let isConstMTrue mx = match mx with
  | MemoF mf -> isConstMTrue mf
  | OnePF f -> isConstTrue f

let isTrivMTerm mx = match mx with
  | MemoF mf -> isTrivMTerm mf
  | OnePF f -> isTrivTerm f
   
let m_apply_one s qp = match qp with
  | MemoF f -> MemoF (m_apply_one s f)
  | OnePF f -> OnePF (apply_subs [s] f)

let m_apply_par sst qp = match qp with
  | MemoF f -> MemoF (m_apply_par sst f)
  | OnePF f -> OnePF (apply_subs sst f)

let memo_apply_one_exp s qp = match qp with
  | MemoF mf -> MemoF (memo_apply_one_exp s mf)
  | OnePF f -> OnePF (apply_one_exp s f)
 
let regroup_memo_group s =  match s with
  | MemoF mf -> MemoF (regroup_memo_group mf)
  | OnePF f -> s

let regroup_memo_group s =
  Debug.no_1 "regroup_memo_group"
	!print_mix_f !print_mix_f regroup_memo_group s
	
let mfv f = match f with
  | MemoF mf -> mfv mf
  | OnePF f -> fv f
 
let merge_mems_m = merge_mems
 
let merge_mems f1 f2 slice_dup = match (f1,f2) with
  | MemoF f1, MemoF f2 -> MemoF (merge_mems f1 f2 slice_dup)
  | OnePF f1, OnePF f2 -> OnePF (mkAnd f1 f2 no_pos)
  | OnePF f1_f, MemoF f2_m -> 
      MemoF (memoise_add_pure_N f2_m f1_f)
  | MemoF f1_m, OnePF f2_f ->
      MemoF (memoise_add_pure_N f1_m f2_f)

(* let merge_mems f1 f2 slice_dup = match (f1,f2) with *)
(*   | MemoF f1, MemoF f2 -> MemoF (merge_mems f1 f2 slice_dup) *)
(*   | OnePF f1, OnePF f2 -> OnePF (mkAnd f1 f2 no_pos) *)
(*   | OnePF f1, MemoF f2 -> *)
(*       let () = print_string "[mcpure.ml]Warning: merge mems: mix of memo and pure formulas 1 \n" in MemoF f2 *)
(*   | MemoF f1, OnePF f2 -> *)
(*       let () = print_string "[mcpure.ml]Warning: merge mems: mix of memo and pure formulas 2 \n" in MemoF f1 *)
  (* | _ -> Error.report_error {Error.error_loc = no_pos;Error.error_text = "merge mems: wrong mix of memo and pure formulas"} *)
  
  
let merge_mems f1 f2 slice_dup = 
  Debug.no_3 "merge_mems " !print_mix_f !print_mix_f (string_of_bool)
  !print_mix_f merge_mems f1 f2 slice_dup

let reset_unsat_flag_mix m = 
	match m with
	| MemoF mf -> MemoF (reset_unsat_flag_mem mf)
	| _ -> m  
  
let replace_mix_formula_label lb s = match s with
  | MemoF f -> MemoF (replace_memo_pure_label lb f)
  | OnePF f -> OnePF (replace_pure_formula_label lb f)
	
let transform_mix_formula f_p_t f = 
  match f with
    | MemoF f -> MemoF (transform_memo_formula f_p_t f)
    | OnePF f -> OnePF (transform_formula f_p_t f)
	
let memo_pure_push_exists qv f = match f with
  | MemoF f -> MemoF (memo_pure_push_exists qv f)
  | OnePF f -> OnePF (mkExists qv f None no_pos)

let memo_pure_push_exists qv f =
  Debug.no_2 "memo_pure_push_exists"
	!print_svl !print_mix_f !print_mix_f
	memo_pure_push_exists qv f

let memo_pure_push_exists_lhs qv f = match f with
  | MemoF f -> MemoF (memo_pure_push_exists_lhs qv f)
  | OnePF f -> OnePF (mkExists qv f None no_pos)
	
let ptr_equations_aux with_null f = match f with
  | MemoF f -> ptr_equations_aux_mp with_null f
  | OnePF f -> pure_ptr_equations_aux with_null f

let bag_equations_aux with_emp f = match f with
  | MemoF f -> bag_equations_aux_mp with_emp f
  | OnePF f -> pure_bag_equations_aux with_emp f

(* type: mix_formula -> (Cpure.EMapSV.elem * Cpure.EMapSV.elem) list *)
 let ptr_equations_with_null f = ptr_equations_aux true f
 
 let ptr_equations_with_null f = 
   let pr1 = !print_mix_f in
   let pr_elem = Cpure.SV.string_of in
   let pr2 = pr_list (pr_pair pr_elem pr_elem) in
   Debug.no_1 "ptr_equations_with_null" pr1 pr2 ptr_equations_with_null f

let ptr_equations_without_null f = ptr_equations_aux false f

let ptr_equations_without_null f = 
   let pr1 = !print_mix_f in
   let pr_elem = Cpure.SV.string_of in
   let pr2 = pr_list (pr_pair pr_elem pr_elem) in
   Debug.no_1 "ptr_equations_without_null" pr1 pr2 ptr_equations_without_null f

let ptr_bag_equations_without_null f = (ptr_equations_aux true f) @ (bag_equations_aux true f)

let filter_useless_memo_pure sim_f b fv f = match f with
  | MemoF f -> MemoF (filter_useless_memo_pure sim_f b fv f)
  | OnePF _ -> f

let filter_useless_memo_pure sim_f b fv f = 
  Debug.no_1 "filter_useless_memo_pure"
    !print_mix_f !print_mix_f
    (fun _ -> filter_useless_memo_pure sim_f b fv f) f
 
let fold_mem_lst_m = fold_mem_lst_with_complex
 
let fold_mem_lst init_f with_dupl with_inv f : formula= match f with
  | MemoF f -> fold_mem_lst_with_complex init_f with_dupl with_inv f 
  | OnePF f -> (mkAnd init_f f no_pos)

(*
let fold_mem_lst init_f with_dupl with_inv f =
  Debug.no_2 "fold_mem_lst"
	!print_p_f_f !print_mix_f !print_p_f_f
	(fun _ _ -> fold_mem_lst init_f with_dupl with_inv f) init_f f
*)
let memoise_add_pure_N_m = memoise_add_pure_N

let memoise_add_pure_N (f:mix_formula) (pf:formula) = match f with
  | MemoF f -> MemoF (memoise_add_pure_N f pf)
  | OnePF f -> OnePF (mkAnd f pf no_pos)

let memoise_add_pure_N (f:mix_formula) (pf:formula) =
  Debug.no_2 "memoise_add_pure_N"
	!print_mix_f !print_p_f_f !print_mix_f
	memoise_add_pure_N f pf

let memoise_add_pure (f:mix_formula) (pf:formula) = memoise_add_pure_N f pf
 
let memoise_add_pure_P_m = memoise_add_pure_P

let memoise_add_pure_P (f:mix_formula) (pf:formula) = match f with
  | MemoF f -> MemoF (memoise_add_pure_P f pf)
  | OnePF f -> OnePF (mkAnd f pf no_pos)

let memoise_add_pure_P (f:mix_formula) (pf:formula) =
  Debug.no_2 "memoise_add_pure_P"
	!print_mix_f !print_p_f_f !print_mix_f
	memoise_add_pure_P f pf
		
let simpl_memo_pure_formula b_f_f p_f_f f tp_simp = match f with
  | MemoF f -> MemoF (simpl_memo_pure_formula b_f_f p_f_f f tp_simp)
  | OnePF f -> OnePF ((*p_f_f*) tp_simp f)

let simpl_memo_pure_formula b_f_f p_f_f f tp_simp =
  Debug.no_1 "simpl_memo_pure_formula"
    !print_mix_f !print_mix_f
    (fun _ -> simpl_memo_pure_formula b_f_f p_f_f f tp_simp) f

let memo_arith_simplify f = match f with
  | MemoF f -> MemoF (memo_arith_simplify f)
  | OnePF f -> OnePF (arith_simplify 6 f)
 
let memo_arith_simplify f = 
  Debug.no_1 "memo_arith_simplify" (!print_mix_f) (!print_mix_f) memo_arith_simplify f 

let memo_is_member_pure sp f = match f with
  | MemoF f -> memo_is_member_pure sp f
  | OnePF f -> is_member_pure sp f
 
let mkOr_mems (f1: mix_formula) (f2: mix_formula) : mix_formula = match f1,f2 with
  | MemoF f1, MemoF f2 -> MemoF (mkOr_mems f1 f2)
  | OnePF f1, OnePF f2 -> OnePF (mkOr f1 f2 None no_pos)
  | _ -> Error.report_error {Error.error_loc = no_pos;Error.error_text = "mkOr_mems: wrong mix of memo and pure formulas"}
  (* | OnePF pf, MemoF mf -> *)
  (*     memoise_add_pure_N f2 pf *)
  (* | MemoF mf, OnePF pf -> *)
  (*     memoise_add_pure_N f1 pf *)

let subst_avoid_capture_memo from t f = match f with
  | MemoF f -> MemoF (subst_avoid_capture_memo(*_debug*) from t f)
  | OnePF f -> OnePF (subst_avoid_capture from t f)
  
let memo_subst s f = match f with
  | MemoF f -> MemoF (memo_subst s f)
  | OnePF f -> OnePF (subst s f)  

let list_pos_of_mix_formula mf=
  match mf with
  | MemoF f -> []
  | OnePF f -> (Cpure.list_pos_of_formula f [])

let subst_pos_mix_formula p mf=
 match mf with
  | MemoF f -> mf
  | OnePF f -> OnePF (Cpure.subst_pos_formula p f)

let elim_redundant sf f = match f with
  | MemoF f -> MemoF (elim_redundant sf f)
  | OnePF _ -> f
 
let fold_mix_lst_to_lst npf with_dupl with_inv with_slice  = match npf with
  | MemoF f -> fold_mem_lst_to_lst f with_dupl with_inv with_slice 
  | OnePF f -> [f]

let get_null_ptrs mf=
  let eq_null_filter (v1,v2)=
    let b1 =  (CP.is_null_const v1) in
    let b2 = (CP.is_null_const v2) in
    match b1,b2 with
      | true,true -> []
      | true,false -> [v2]
      | false,true -> [v1]
      | false,false -> []
  in
  let eqNulls = ptr_equations_with_null mf in
  List.concat (List.map eq_null_filter eqNulls)

let get_subst_equation_memo_formula_vv p qvar = match p with
  | MemoF f -> 
    let l,f = get_subst_equation_memo_formula_vv f qvar in
     (l,MemoF f)
  | OnePF f -> 
    let l,f = get_subst_equation_formula_vv f qvar in
    (l,OnePF f)

let get_subst_equation_mix_formula p qvar only_vars = match p with
  | MemoF f -> 
    let l,f = get_subst_equation_memo_formula f qvar only_vars in
     (l,MemoF f)
  | OnePF f -> 
    let l,f = get_subst_equation_formula f qvar only_vars in
    (l,OnePF f)

let get_all_vv_eqs_mix f = match f with 
	| MemoF f -> 
		let l,f = get_all_vv_eqs_memo f in
		l, MemoF f
	| OnePF f -> 
		let l,f = get_all_vv_eqs f in
		l, OnePF f

let get_all_vv_eqs_mix f = 
  let pr1 = !print_mix_f in
  let pr = pr_list (pr_pair !print_sv_f !print_sv_f) in
  let pr2 = pr_pair pr !print_mix_f in
  Debug.no_1 "get_all_vv_eqs_mix" pr1 pr2 get_all_vv_eqs_mix f 

let mix_cons_filter f fct = match f with
  | MemoF f -> MemoF (cons_filter f fct)
  | OnePF _ -> f

let mix_cons_filter f fct = 
  let pr = !print_mix_f in
  Debug.no_1 "mix_cons_filter" pr pr 
      (fun _ -> mix_cons_filter f fct) f
(*
let combine_mix_branch (s:string) (f:mix_formula * 'a) = match (fst f) with
  | MemoF mf -> MemoF (combine_memo_branch s (mf,snd f))
  | OnePF pf -> OnePF (combine_branch s (pf,snd f))*)
 (*
 match f with
  | MemoF f -> 
  | OnePF f -> 
 *)
let mix_drop_null self l neg = match l with
  | MemoF l -> 
    let r = List.map (fun c -> {c with memo_group_slice = List.map (fun c-> drop_null c self neg ) c.memo_group_slice}) l in
    MemoF r
  | OnePF  pf -> 
    OnePF (drop_null pf self neg)
    
let drop_triv_grps f = match f with
  | MemoF f -> MemoF (fst (List.partition (fun c-> not (isConstGroupTrue c)) f))
  | OnePF _ -> f
  
let drop_pf f = match f with
  | MemoF f -> f
  | OnePF _ -> []

let memo_group_drop_rel f =
  let mc = f.memo_group_cons in
  let ms = f.memo_group_slice in
  let mc = List.filter (fun bf -> match bf.memo_formula with (RelForm _,_) -> false | _ -> true) mc in
  let ms = List.map (Cpure.drop_rel_formula) ms in
  { f with memo_group_cons = mc; memo_group_slice = ms}

(* drop unknown rel constraint from f *)
let memo_drop_rel f = List.map (memo_group_drop_rel) f

let memo_drop_rel f =
  let pr = !print_mp_f in
  Debug.no_1 "memo_drop_rel" pr pr memo_drop_rel f

let mix_drop_rel f = match f with
  | MemoF f -> MemoF (memo_drop_rel f)
  | OnePF f -> OnePF (drop_rel_formula f)

  
let trans_mix_formula (e: mix_formula) (arg: 'a) f f_arg f_comb : (mix_formula * 'b) = 
  let mf,pf = f in
  let ma,pa = f_arg in
  match e with
  | MemoF e-> 
    let f,r = trans_memo_formula e arg mf ma f_comb in
    (MemoF f, r)
  | OnePF e -> 
    let f,r = trans_formula e arg pf pa f_comb in
    (OnePF f,r)
    
let trans_n_mix_formula (e: mix_formula) (arg: 'a) f f_arg f_comb : (mix_formula * 'b) = 
  let mf,pf = f in
  let ma,pa = f_arg in
  match e with
  | MemoF e-> 
    let f,r = trans_memo_pure e arg mf ma f_comb in
    (MemoF f, r)
  | OnePF e -> 
    let f,r = trans_formula e arg pf pa f_comb in
    (OnePF f,r)

(*find constraints in f that related to specvar in v_l*)    
let find_rel_constraints (f:mix_formula) (v_l :spec_var list):  mix_formula = match f with
  | MemoF f -> 
MemoF (List.filter (fun c-> not ((Gen.BList.intersect_eq eq_spec_var c.memo_group_fv v_l )==[]))f)
  | OnePF f -> OnePF (Cpure.find_rel_constraints f v_l)
  
let memo_filter_complex_inv f = List.map (fun c-> {c with memo_group_cons = []; memo_group_aset=[]}) f
	
  
let filter_complex_inv f = match f with
  | MemoF f -> MemoF (memo_filter_complex_inv f)
  | OnePF f -> OnePF (filter_complex_inv f)
	
	
let isConstTrueBranch (p,bl) = (isConstMTrue p)&& (List.for_all (fun (_,b)-> isConstTrue b) bl)


(*Moved to cpure.ml*)
(* let find_closure (v:spec_var) (vv:(spec_var * spec_var) list) : spec_var list =  *)
(*   let rec helper (vs: spec_var list) (vv:(spec_var * spec_var) list) = *)
(*     match vv with *)
(*       | (v1,v2)::xs ->  *)
(*           let v3 = if (List.exists (fun v -> eq_spec_var v v1) vs) then Some v2 *)
(*               else if (List.exists (fun v -> eq_spec_var v v2) vs) then Some v1 *)
(*               else  *)
(*                 None  *)
(*           in *)
(*           (match v3 with *)
(*             | None -> helper vs xs *)
(*             | Some x -> helper (x::vs) xs) *)
(*       | [] -> vs *)
(*   in *)
(*   helper [v] vv *)

let find_closure_mix_formula_x (v:spec_var) (f:mix_formula) : spec_var list = find_closure v (ptr_equations_with_null f)

let find_closure_mix_formula (v:spec_var) (f:mix_formula) : spec_var list = 
  Debug.no_2 "find_closure_mix_formula" 
      !print_sv_f
      !print_mix_f
      !print_sv_l_f
      find_closure_mix_formula_x v f

(*let trans_memo_group (e: memoised_group) (arg: 'a) f f_arg f_comb : (memoised_group * 'b) = *)
(*  let f_grp, f_memo_cons, f_aset, f_slice,f_fv = f in*)
(*  match f_grp arg e with *)
(*    | Some e1-> e1*)
(*    | None -> *)
(*      let new_arg = f_arg arg e in*)
(*      let new_cons,new_rc  = List.split ((List.map (fun c-> f_memo_cons c new_arg)) e.memo_group_cons) in*)
(*      let new_aset, new_ra = f_aset new_arg e.memo_group_aset in*)
(*      let new_slice, new_rs = List.split ((List.map (fun c-> f_slice c new_arg)) e.memo_group_slice) in*)
(*      let new_fv, new_rv =  List.split ((List.map (fun c-> f_fv c new_arg)) e.memo_group_fv) in*)
(*      ({e with*)
(*        memo_group_fv =new_fv;*)
(*        memo_group_cons = new_cons;*)
(*        memo_group_slice = new_slice;*)
(*        memo_group_aset = new_aset;}, f_comb (new_rc@new_ra@new_rs@new_rv))*)
  
    
  
let constraint_collector p_sel f : (mix_formula * (b_formula * spec_var) list)=
   let f_comb f = List.concat f in
   let pf_f _ f= match f with
    | Or _ -> Some (f,[])
    | _ -> None    in
   let pf_b _ b = match p_sel b with
      | (false,l) -> Some ((BConst (true,no_pos),None),l)
      | (true,l) -> Some (b,l) in
   let pf_e _ e = Some (e,[]) in
   let pf_all = (pf_f,pf_b,pf_e) in
   let p_arg = (fun _ _ ->0),(fun _ _ ->0),(fun _ _ ->0) in
   
   let mf_fv v _ = (v, []) in
   let mf_slice f _ = (f,[]) in
   let mf_aset _ f =(f,[]) in
   let mf_memo_cons f _ = (f,[]) in
   let mf_grp _ x = 
         let slice,l_slice =List.split 
            (List.map (fun f-> trans_formula f 0 pf_all p_arg f_comb) x.memo_group_slice) in
         let l_slice = List.concat l_slice in
         let cons,l_cons = List.fold_left (fun (a1,a2) c-> match c.memo_status with
                          | Implied_N ->  (match (p_sel c.memo_formula) with
                                                | (true,l) -> (c::a1,l@a2)
                                                | (false,l)-> (a1,l@a2))
                          | _ -> (c::a1,a2)) ([],[]) x.memo_group_cons in
         let aset, l_aset =
            let vl = EMapSV.get_equiv x.memo_group_aset in
            List.fold_left (fun (a1,a2) (v1,v2)->
                match p_sel ((Eq (Var (v1,no_pos), Var (v2,no_pos),no_pos)),None) with
                  | (true,l) -> ((v1,v2)::a1, l@a2)
                  | (false,l) -> (a1, l@a2)) ([],[]) vl in
         let aset = List.fold_left (fun a (x,y) -> EMapSV.add_equiv a x y) []  aset in
         let x = {x with
            memo_group_fv = [];
            memo_group_slice = slice;
            memo_group_cons = cons;
            memo_group_aset = aset; } in
         Some ({x with memo_group_fv = fv_memoised_group x} ,
        l_slice@ l_cons@ l_aset) in
   let mf_all = (mf_grp, mf_memo_cons, mf_aset, mf_slice, mf_fv) in
   trans_mix_formula f 0 (mf_all, pf_all) 
    ((fun _ _ ->0) , p_arg) f_comb
   
(** An Hoa : Simplify the mix formula by removing duplicates and redundant constraints. **)
let simplify_mix_formula mf =
	match mf with 		
		| MemoF _ -> mf
		| OnePF f -> 
			let nf = remove_dup_constraints f in
			let nf = remove_redundant_constraints nf in
				OnePF nf

(* (*NOTE: do not reuse the returned mix_f when --eps*)                                  *)
(* let normalize_varperm_mix_formula_x (mix_f:mix_formula) : mix_formula =               *)
(*   match mix_f with                                                                    *)
(*     | OnePF f -> OnePF (normalize_varperm f)                                          *)
(*     | MemoF mp ->                                                                     *)
(*         let f = pure_of_mix mix_f in                                                  *)
(*         (* let f = fold_mem_lst (mkTrue no_pos) false true mix_f in *)                *)
(*         let new_f = normalize_varperm f in                                            *)
(*         (mix_of_pure new_f)                                                           *)

(* (* combine VarPerm formulas into 4 types*)                                            *)
(* (*NOTE: do not reuse the returned mix_f when --eps*)                                  *)
(* let normalize_varperm_mix_formula (mix_f:mix_formula) : mix_formula =                 *)
(*   Debug.no_1 "normalize_varperm_mix_formula"                                          *)
(*       !print_mix_f !print_mix_f                                                       *)
(*       normalize_varperm_mix_formula_x mix_f                                           *)

(* (*NOTE: do not reuse the returned mix_f when --eps*)                                  *)
(* let filter_varperm_mix_formula_x (mix_f:mix_formula) : (formula list * mix_formula) = *)
(*   match mix_f with                                                                    *)
(*     | OnePF f ->                                                                      *)
(*         let ls,f1 = filter_varperm f in                                               *)
(*         (ls,OnePF f1)                                                                 *)
(*     | MemoF mp ->                                                                     *)
(*         let f = fold_mem_lst (mkTrue no_pos) false true mix_f in                      *)
(*         let ls,new_f = filter_varperm f in                                            *)
(*         (ls, (mix_of_pure new_f))                                                     *)

(* (*NOTE: do not reuse the returned mix_f when --eps*)                                  *)
(* (* pure_of_mix may discard some info when --eps *)                                    *)
(* let filter_varperm_mix_formula (mix_f:mix_formula) : (formula list * mix_formula) =   *)
(*   let pr_out (ls,f) =                                                                 *)
(*     "\n ### ls = " ^ (pr_list !print_formula ls)                                      *)
(*     ^ "\n ### f = " ^ (!print_mix_f f)                                                *)
(*   in                                                                                  *)
(*   Debug.no_1 "filter_varperm_mix_formula"                                             *)
(*       !print_mix_f pr_out                                                             *)
(*       filter_varperm_mix_formula_x mix_f                                              *)

(* let get_varperm_mix_formula_x (mix_f:mix_formula) typ : spec_var list =               *)
(*   match mix_f with                                                                    *)
(*     | OnePF f ->                                                                      *)
(*         let res = Cpure.get_varperm_pure f typ in                                     *)
(*         res                                                                           *)
(*     | MemoF mp ->                                                                     *)
(*         let f = pure_of_mix mix_f in                                                  *)
(*         let res = Cpure.get_varperm_pure f typ in                                     *)
(*         res                                                                           *)

(* let get_varperm_mix_formula (mix_f:mix_formula) typ : spec_var list =                 *)
(*   Debug.no_2 "get_varperm_mix_formula"                                                *)
(*       !print_mix_f string_of_vp_ann !print_svl                                        *)
(*       get_varperm_mix_formula_x mix_f typ                                             *)

(* (*Note: use this method with care.                                                    *)
(* The conversion between pure_of_mix and mix_of_pure                                    *)
(* may affect --eps*)                                                                    *)
(* let drop_varperm_mix_formula (mix_f:mix_formula) : mix_formula =                      *)
(*   match mix_f with                                                                    *)
(*     | OnePF f ->                                                                      *)
(*         let f1 = Cpure.drop_varperm_formula f in                                      *)
(*         (OnePF f1)                                                                    *)
(*     | MemoF mp ->                                                                     *)
(*         let f = pure_of_mix mix_f in                                                  *)
(*         let f1 = Cpure.drop_varperm_formula f in                                      *)
(*         let f2 = mix_of_pure f1 in                                                    *)
(*         f2                                                                            *)

(*Eq, Lt, Lte, Gt, Gte*)
let remove_dupl_conj_mix_formula_x (f:mix_formula):mix_formula =
  (match f with
    | MemoF _ -> 
        (*Todo: implement this*)
        (* let () = print_string ("[cformula.ml][remove_dupl_conj_eq_mix_formula] Warning: not yet support MemoF \n") in *)
        f
    | OnePF p_f -> (OnePF (remove_dupl_conj_pure p_f))
  )

(*Eq, Lt, Lte, Gt, Gte*)
let remove_dupl_conj_mix_formula (f:mix_formula):mix_formula = 
  Debug.no_1 "remove_dupl_conj_mix_formula" !print_mix_formula !print_mix_formula 
      remove_dupl_conj_mix_formula_x f

let drop_float_formula_mix_formula (mf : mix_formula) : mix_formula =
  match mf with
    | OnePF f -> 
        let nf = Cpure.drop_float_formula f in
        (OnePF nf)
    | MemoF mp ->
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let nf = Cpure.drop_float_formula f in
        (mix_of_pure nf)

(*extract lockset constraints from a formula*)
let extractLS_mix_formula_x (mf : mix_formula) : mix_formula =
  match mf with
    | OnePF f -> 
        let mf_delayed = Cpure.extractLS_pure f in
        (OnePF mf_delayed)
    | MemoF mp ->
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let delayed = Cpure.extractLS_pure f in
        (mix_of_pure delayed)

(*extract lockset constraints from a formula*)
let extractLS_mix_formula (mf : mix_formula) : mix_formula =
  Debug.no_1 "extractLS_mix_formula" !print_mix_formula !print_mix_formula
      extractLS_mix_formula_x mf

(*remove lockset constraints from a formula*)
let removeLS_mix_formula_x (mf : mix_formula) : mix_formula =
  match mf with
    | OnePF f -> 
        let mf_delayed = Cpure.removeLS_pure f in
        (OnePF mf_delayed)
    | MemoF mp ->
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let delayed = Cpure.removeLS_pure f in
        (mix_of_pure delayed)

(*remove lockset constraints from a formula*)
let removeLS_mix_formula (mf : mix_formula) : mix_formula =
  Debug.no_1 "removeLS_mix_formula" !print_mix_formula !print_mix_formula
      removeLS_mix_formula_x mf

(*remove level constraints from a formula*)
let remove_level_mix_formula_x (mf : mix_formula) : mix_formula =
  let f_m mp = None in
  let f_a _ = None in
  let f_p_f pf = None in
  let f_b b =
	let (pf,il) = b in
	let npf = match pf with
          | Frm _
	  | BConst _
	  | XPure _ 
	  | BVar _ 
	  | BagMin _ 
          | SubAnn _
          (* | VarPerm _ *)
	  | BagMax _ -> pf
	  | Lt (e1,e2,l)
	  | Lte (e1,e2,l)
	  | Gt (e1,e2,l)
	  | Gte (e1,e2,l)
	  | Eq (e1,e2,l)
	  | Neq (e1,e2,l)
	  | BagSub (e1,e2,l)
	  | ListIn (e1,e2,l)
	  | ListNotIn (e1,e2,l)
	  | ListAllN (e1,e2,l)
	  | ListPerm (e1,e2,l) ->
          if ( has_level_constraint_exp e1 || has_level_constraint_exp e2) then
            mkTrue_p no_pos
          else pf
	  | EqMax (e1,e2,e3,l)
	  | EqMin (e1,e2,e3,l) ->
          if ( has_level_constraint_exp e1 || has_level_constraint_exp e2 || has_level_constraint_exp e3) then
            mkTrue_p no_pos
          else pf
	    (* bag formulas *)
	  | BagIn (v,e,l)
	  | BagNotIn (v,e,l)->
          if ( has_level_constraint_exp e) then
            mkTrue_p no_pos
          else pf
	  | RelForm (r, args, l) -> pf (*TOCHECK*)
	  | LexVar t_info -> pf (*TOCHECK*)
	in Some (npf,il)
  in
  let f_e e = None in
  let trans = (f_m, f_a, f_p_f, f_b, f_e) in
  match mf with
    | OnePF f -> 
        let nmf = Cpure.transform_formula trans f in
        (OnePF nmf)
    | MemoF mp ->
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let nmf = Cpure.transform_formula trans f in
        (mix_of_pure nmf)

(*remove level constraints from a formula*)
let remove_level_mix_formula (mf : mix_formula) : mix_formula =
  Debug.no_1 "remove_level_mix_formula" !print_mix_formula !print_mix_formula
      remove_level_mix_formula_x mf

(*remove constraints related to a list of spec vars*)
let drop_svl_mix_formula (mf : mix_formula)  (svl:spec_var list) : mix_formula =
  match mf with
    | OnePF f -> 
        let nf = drop_svl_pure f svl in
        (OnePF nf)
    | MemoF mp ->
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let nf = drop_svl_pure f svl in
        (mix_of_pure nf)

let has_level_constraint_mix_formula (mf : mix_formula) : bool =
  match mf with
    | OnePF f -> 
        let b = has_level_constraint f in
        b
    | MemoF mp ->
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let b = has_level_constraint f  in
        b

let translate_level_mix_formula_x (mf : mix_formula)  : mix_formula =
  if not (has_level_constraint_mix_formula mf) then mf else
  match mf with
    | OnePF f -> 
        let nf = translate_level_pure f in
        (OnePF nf)
    | MemoF mp ->
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let nf = translate_level_pure f  in
        (mix_of_pure nf)

let translate_level_mix_formula (mf : mix_formula) : mix_formula =
  Debug.no_1 "translate_level_mix_formula" !print_mix_formula !print_mix_formula 
      translate_level_mix_formula_x mf

(* translate l1=l2 into l1=l2 & level(l1)=level(l2) *)
let translate_level_eqn_mix_formula_x (mf : mix_formula)  : mix_formula =
  match mf with
    | OnePF f -> 
        let nf = translate_level_eqn_pure f in
        (OnePF nf)
    | MemoF mp ->
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let nf = translate_level_eqn_pure f  in
        (mix_of_pure nf)

(* translate l1=l2 into l1=l2 & level(l1)=level(l2) *)
let translate_level_eqn_mix_formula (mf : mix_formula) : mix_formula =
  Debug.no_1 "translate_level_eqn_mix_formula" !print_mix_formula !print_mix_formula 
      translate_level_eqn_mix_formula_x mf

let infer_lsmu_mix_formula_x (mf : mix_formula)  : mix_formula * (CP.spec_var list) =
  match mf with
    | OnePF f -> 
        let nf,evars = infer_lsmu_pure f in
        (OnePF nf),evars
    | MemoF mp -> 
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let nf,evars = infer_lsmu_pure f  in
        (mix_of_pure nf),evars

let infer_lsmu_mix_formula (mf : mix_formula)  : mix_formula * (CP.spec_var list) =
  let pr_out = pr_pair !print_mix_formula !print_svl in
  Debug.no_1 "infer_lsmu_mix_formula" !print_mix_formula pr_out
      infer_lsmu_mix_formula_x mf

let translate_waitlevel_mix_formula_x (mf : mix_formula)  : mix_formula =
  let fvars = mfv mf in
  let b = List.exists (fun v -> (name_of_spec_var v = Globals.waitlevel_name)) fvars in
  if not b then mf else
  match mf with
    | OnePF f -> 
        let nf = translate_waitlevel_pure f in
        (OnePF nf)
    | MemoF mp ->
        (*TO CHECK: This may break --eps*)
        let f = fold_mem_lst (mkTrue no_pos) false true mf in
        let nf = translate_waitlevel_pure f  in
        (mix_of_pure nf)

let translate_waitlevel_mix_formula (mf : mix_formula) : mix_formula =
  Debug.no_1 "translate_waitlevel_mix_formula" !print_mix_formula !print_mix_formula 
      translate_waitlevel_mix_formula_x mf

let remove_disj_clauses (mf: mix_formula): mix_formula = 
  let pf = pure_of_mix mf in
  let rm_disj f = 
    let mf_conjs = split_conjunctions f in
    let (disj,mf_conjs) = List.partition is_disjunct mf_conjs in
      mf_conjs 
  in
  let mf_conjs = rm_disj pf in
  let mf_conjs = List.map (fun x -> match x with 
    | AndList xs -> 
          let ys = List.map (fun (l,a) -> (l,join_conjunctions (rm_disj a))) xs in
          AndList ys
    | y -> y) mf_conjs in
  let mf = join_conjunctions (mf_conjs) in
  mix_of_pure mf

let remove_disj_clauses (mf: mix_formula): mix_formula = 
  let pr = !print_mix_formula in
  Debug.no_1 "remove_disj_clauses" pr pr remove_disj_clauses mf

  
let drop_triv_eq (mf: mix_formula): mix_formula = match mf with
	| MemoF _ -> mf
	| OnePF f -> OnePF (drop_triv_eq f)

	
let check_pointer_dis_sat mf = match mf with
	| MemoF _ -> true, mf
	| OnePF f -> 
		let r,b = check_pointer_dis_sat f in
		b, OnePF r

let get_rel_ctr (mf: mix_formula) (vl: spec_var list) : mix_formula =
  match mf with
  | MemoF f -> 
      MemoF (List.filter (fun m -> 
        Gen.BList.overlap_eq eq_spec_var m.memo_group_fv vl) f)
  | OnePF f -> 
      let mf = memoise_add_pure_N_m (mkMTrue_no_mix ()) f in
      let simp_mf = List.filter (fun m -> 
        Gen.BList.overlap_eq eq_spec_var m.memo_group_fv vl) mf in
      OnePF (pure_of_mix (MemoF simp_mf))

let partition_mix_formula (mf: mix_formula) ff : mix_formula * mix_formula =
  match mf with
  | MemoF f -> 
    let fm, om = List.partition (fun m -> ff m) f in
    MemoF fm, MemoF om
  | OnePF f -> 
    let mf = memoise_add_pure_N_m (mkMTrue_no_mix ()) f in
    let fmf, omf = List.partition (fun m -> ff m) mf in
    OnePF (pure_of_mix (MemoF fmf)), OnePF (pure_of_mix (MemoF omf))
