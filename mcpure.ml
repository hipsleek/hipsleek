open Globals

open Cpure

(*
 -eprune = espec + ememo + eslice
 -espec enables specialization 
 -ememo will enable memoizing
 -eslice will enable slicing
*)

type memo_pure = memoised_group list
  
and memoised_group = {
    memo_group_fv : spec_var list;
    memo_group_changed: bool;
    memo_group_cons : memoised_constraint list;(*used for pruning*)
    memo_group_slice: formula list; (*constraints that can not be used for pruning but belong to the current slice non-the less*)}

and memoised_constraint = {
    (*memo_formula_mut: b_formula ref;
    memo_status_mut : prune_status ref ;*)
    memo_formula : b_formula;
    memo_status : prune_status }

and prune_status = 
  | Fail_prune        (*constraint that is contradicted by the current state*)
  | Implied_dupl      (*constraint that is superseeded by other constraints in the current state*)
  | Implied of bool         (*constraint that can be deducted from the current state- including predicate invariants ,the bool indicates the source true: orig false: invariant*)
  | Unknown_prune of bool   (*pruning constraint with unknown status, -bool indicates if it comes from an invariant
                          true -> if proven becomes Implied, false becomes Implied_dupl*)
  
    
    
let rec mfv (m: memo_pure) : spec_var list = Util.remove_dups_f (List.concat (List.map (fun c-> c.memo_group_fv) m)) eq_spec_var


and isConstMConsTrue r = match r.memo_status with
  | Implied _ | Implied_dupl -> isConstBTrue  r.memo_formula
  | Fail_prune -> isConstBFalse r.memo_formula
  | _ -> false
  
and isConstMConsFalse r = match r.memo_status with
  | Implied _ | Implied_dupl -> isConstBFalse  r.memo_formula
  | Fail_prune -> isConstBTrue r.memo_formula
  | _ -> false  
  
and isConstMTrue f = 
  match (List.length f) with
    | 0 -> true
    | 1 ->
        let r = List.hd f in
        (match ((List.length r.memo_group_cons),(List.length r.memo_group_slice)) with
            | 0,1 -> isConstTrue (List.hd r.memo_group_slice)
            | 1,0 -> isConstMConsTrue (List.hd r.memo_group_cons) 
            | _ -> false)
    | _ -> false
      
and isConstMFalse f = 
  match (List.length f) with
    | 1 ->
        let r = List.hd f in
        (match ((List.length r.memo_group_cons),(List.length r.memo_group_slice)) with
            | 0,1 -> isConstFalse (List.hd r.memo_group_slice)
            | 1,0 -> isConstMConsFalse (List.hd r.memo_group_cons)
            | _ -> false)
    | _ -> false
  
  
let rec filter_mem_fct fct lst =  
   let l = List.map (fun c->{c with memo_group_cons = List.filter fct c.memo_group_cons}) lst in
  List.filter (fun c-> (List.length c.memo_group_cons)+(List.length c.memo_group_slice)>0) l
    
and filter_mem_triv lst = 
  filter_mem_fct (fun c->match c.memo_formula with 
    | Lte (e1,e2,l) 
    | Gte (e1,e2,l) 
    | Eq  (e1,e2,l) 
    | Neq  (e1,e2,l) -> not (eqExp e1 e2)
    | _ -> true) lst
  
and group_mem_by_fv (lst: memo_pure):memo_pure = 
    let n_l = List.fold_left (fun a d-> 
      let n_l = List.map (fun c->((bfv c.memo_formula),[(Some c, None)])) d.memo_group_cons in
      let n_l_f = List.map (fun f->((fv f),[(None, Some f)])) d.memo_group_slice in
      n_l @ n_l_f @ a) [] lst in
      
    let r = List.fold_left (fun acc (v_list, mem) -> 
        let l_merged, l_unmerged = List.partition (fun (v_l,_)-> 
          (List.length (Util.intersect_fct eq_spec_var v_l v_list))>0) acc in
        let l_v,l_m = List.fold_left (fun (a1,a2)(c1,c2)-> (a1@c1,c2@a2)) (v_list,mem) l_merged in
        ((Util.remove_dups_f l_v eq_spec_var),l_m)::l_unmerged ) [] n_l in
        
    List.map (fun (v_l,m_l)-> 
      let mc_l, f_l = List.fold_left (fun (a1,a2) c -> match c with
        | None, Some f -> (a1,f::a2)
        | Some f, None -> (f::a1,a2)
        | _ -> (a1,a2)) ([],[]) m_l in      
      { memo_group_fv = v_l; 
        memo_group_changed = true ; 
        memo_group_cons = mc_l;
        memo_group_slice = f_l;}) r  
  
and regroup_memo_group (lst : memo_pure) : memo_pure = 
   let rec f_rec fv a = 
     let r1,r2 = List.partition (fun c-> (List.length (Util.intersect_fct eq_spec_var fv c.memo_group_fv))>0) a in
     if r1 = [] then ([],r2)
     else
      let n_fv = List.fold_left (fun ac c-> ac@c.memo_group_fv) fv r1 in
      let x1,x2 = f_rec n_fv r2 in
      (r1@x1,x2) in
   let rec helper c = match c with
    | [] -> []
    | h::t -> 
      let h_merged,h_not_merged = f_rec h.memo_group_fv t in
      let h_m = List.fold_left (fun a c-> 
        { memo_group_fv = a.memo_group_fv @c.memo_group_fv;
          memo_group_slice = a.memo_group_slice @c.memo_group_slice;
          memo_group_cons =  a.memo_group_cons  @c.memo_group_cons;
          memo_group_changed = true;}) h h_merged in
      let r_h = {h_m with memo_group_fv = Util.remove_dups_f h_m.memo_group_fv eq_spec_var;} in      
      let r = helper h_not_merged in
      r_h::r in
  helper lst
  
  

and subst_avoid_capture_memo (fr : spec_var list) (t : spec_var list) (f_l : memo_pure) =
  let fresh_fr = fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let helper  (s:(spec_var*spec_var) list) f  = 
   {memo_group_fv = List.map (fun v-> subs_one s v) f.memo_group_fv;
    memo_group_changed = f.memo_group_changed;
    memo_group_cons = List.map (fun d->{d with memo_formula = List.fold_left (fun a c-> b_apply_one c a) d.memo_formula s;}) f.memo_group_cons;
    memo_group_slice = List.map (subst s) f.memo_group_slice; } in
  let r = List.map (helper st1) f_l in
  regroup_memo_group (List.map (helper st2) r)

  

and subst_memo (sst : (spec_var * spec_var) list) (f_l : memo_pure) = 
  let rec helper sst f_l = match sst with
  | s::ss -> helper ss (m_apply_one s f_l)
  | [] -> f_l in
  regroup_memo_group (helper sst f_l)
  

and m_apply_one s f = 
  let r = List.map (fun c -> 
    {memo_group_fv = List.map (fun v-> subst_var s v) c.memo_group_fv;
    memo_group_changed = c.memo_group_changed;
    memo_group_cons = List.map (fun d->{d with memo_formula = b_apply_one s d.memo_formula;}) c.memo_group_cons;
    memo_group_slice = List.map (apply_one s) c.memo_group_slice; }) f in  
  filter_mem_triv r

and h_apply_one_m_constr_lst s l = 
  List.map (fun (c,c2)-> ({c with memo_formula = b_apply_one s c.memo_formula},c2)) l

(* assume that f is a satisfiable conjunct *)
and ptr_equations (f : memo_pure) : (spec_var * spec_var) list = 
  let prep_b_f bf =  match bf with
	  | Eq (e1, e2, _) -> 
      let b = can_be_aliased e1 && can_be_aliased e2 in
        if not b then [] else [(get_alias e1, get_alias e2)]
    | _ -> [] in  
  let rec prep_f f = match f with
    | And (f1, f2, pos) -> (prep_f f1) @ (prep_f f2)
    | BForm (bf,_,_) -> prep_b_f bf
    | _ -> [] in  
  let helper f = 
    let r = List.fold_left (fun a c-> match c.memo_status with
        | Implied _
        | Implied_dupl -> (a@ prep_b_f c.memo_formula)
        | _ -> a) [] f.memo_group_cons in
    List.fold_left (fun a c-> a@(prep_f c)) r f.memo_group_slice in
 List.concat (List.map helper f)

(*  extract the equations for the variables that are to be explicitly instantiated from the residue - a Cpure.formula *)
(* get the equation for the existential variable used in the
   following variable elimination ex x. (x=y & P(x)) <=> P(y).
   The function also returns the remainder of the formula after
   the equation is extracted. It stops searching upon seeing
   Or/Exists/Forall. The equations returned are only of form
   v1 = v2 so that they can be applied to heap nodes. *)

and get_subst_equation_memo_formula_vv (f0: memo_pure) (v:spec_var) : ((spec_var * spec_var) list * memo_pure) = 
  let (r1,r2) = get_subst_equation_memo_formula f0 v true in
  let r1 = List.fold_left (fun a c-> match c with | (r,Var(v,_))-> (r,v)::a | _ -> a) [] r1 in
  (r1,r2)
   
and get_subst_equation_memo_formula (f0 : memo_pure) (v : spec_var) only_vars: ((spec_var * exp) list * memo_pure) = 
  List.fold_left (fun (a1,a2) c->
    if not(a1=[]) then (a1,c::a2)
    else if not(List.exists (eq_spec_var v) c.memo_group_fv) then (a1,c::a2)
    else 
      let acl, ncl = List.fold_left (fun (a1,a2) c-> if not(a1=[]) then (a1,c::a2)
        else match c.memo_status with
        | Implied _ | Implied_dupl -> 
          let r1,r2 = get_subst_equation_b_formula c.memo_formula v None None only_vars in
          if (r1=[]) then (a1,c::a2) else (r1,a2)
        | _ -> (a1,c::a2)) ([],[]) c.memo_group_cons in
      let acl, nsl = if not (acl=[]) then (acl, c.memo_group_slice)
        else List.fold_left (fun (a1,a2) c-> 
          if not (a1=[]) then (a1,c::a2)
          else 
            let r1,r2 = get_subst_equation_formula c v only_vars in
            (r1,r2::a2))([],[]) c.memo_group_slice in
      (acl, {c with memo_group_cons=ncl; memo_group_slice=nsl}::a2)) ([],[]) f0


and memo_pure_elim_exists (f0: memo_pure):memo_pure = 
  List.map (fun c-> 
    {c with memo_group_slice = List.fold_left (fun a c->
      let r = elim_exists c in
      if (isConstTrue r) then a else (list_of_conjs r)@a) [] c.memo_group_slice}) f0 
      
and mapply_one_exp s mem = 
  let r = List.map (fun c -> 
      { c with 
        memo_group_cons = List.map (fun d->{d with memo_formula = b_apply_one_exp s d.memo_formula}) c.memo_group_cons;
        memo_group_slice = List.map (apply_one_exp s) c.memo_group_slice}) mem in
  (*let _ = print_string ("pre got slices: "^(string_of_int (List.length r))^"\n") in*)
  let r_group = group_mem_by_fv r in
  (*let _ = print_string ("pre got slices: "^(string_of_int (List.length r_group))^"\n") in  *)
  filter_mem_triv r_group
  

and memo_f_neg (f: b_formula): b_formula = match f with
  | Lt (e1,e2,l) -> Lte (e2,e1,l)
  | Lte (e1,e2,l) -> Lt (e2,e1,l)
  | Gt (e1,e2,l) -> Lte (e1,e2,l)
  | Gte (e1,e2,l) -> Lt (e1,e2,l)
  | Eq (e1,e2,l) -> Neq (e1,e2,l)
  | Neq (e1,e2,l) -> Eq (e1,e2,l)
  | BagIn (e1,e2,l) -> BagNotIn(e1,e2,l)
  | BagNotIn  (e1,e2,l) -> BagIn(e1,e2,l)
  | ListIn (e1,e2,l) -> ListNotIn(e1,e2,l)
  | ListNotIn (e1,e2,l) -> ListIn(e1,e2,l)
  | _ -> Error.report_error {Error.error_loc = no_pos;Error.error_text = "memoized negation: unexpected constraint type"}
  
  
and memo_arith_simplify (f:memo_pure) : memo_pure = 
   List.map (fun c-> { c with memo_group_slice = List.map arith_simplify c.memo_group_slice}) f
  
(******************************************************************************************************************
	Utilities for memoized formulas
******************************************************************************************************************)
   
and mkMTrue pos :memo_pure = []
and mkMFalse pos :memo_pure = 
  [{memo_group_fv=[]; 
    memo_group_changed = false; 
    memo_group_cons = [];
    memo_group_slice = [mkFalse pos]}]
        

and memo_is_member_pure p mm = 
  List.exists (fun c-> 
    (List.exists (is_member_pure p) c.memo_group_slice)||
    (List.exists (fun c-> match c.memo_status with
      | Implied _ | Implied_dupl-> (match p with | BForm (r,_,_)-> equalBFormula r c.memo_formula | _ -> false) 
      | _-> false ) c.memo_group_cons)) mm
          
and fold_mem_lst_to_lst mem with_dupl with_inv : formula list=
    List.map (fun c-> 
      List.fold_left (fun a c-> match c.memo_status with 
        | Implied_dupl -> if with_dupl then mkAnd a (BForm (c.memo_formula,None,None)) no_pos  else a
        | Implied b -> 
            if with_inv then mkAnd a (BForm (c.memo_formula,None,None)) no_pos 
            else if b then            
              mkAnd a (BForm (c.memo_formula,None,None)) no_pos 
            else mkTrue no_pos              
        | _ -> a)(conj_of_list c.memo_group_slice no_pos) c.memo_group_cons) mem
          
and fold_mem_lst (f_init:formula) with_dupl with_inv lst :formula= 
  let r = fold_mem_lst_to_lst lst with_dupl with_inv in
  List.fold_left (fun a c-> mkAnd a c no_pos) f_init r

and filter_useless_mem fv c = 
    match (List.length c.memo_group_slice) with
      | 0 -> ((List.length c.memo_group_cons)>0)(*((List.length (Util.intersect_fct eq_spec_var fv c.memo_group_fv))>0)*)
      | 1 -> (((List.length c.memo_group_cons)=0)&&(not (isConstTrue (List.hd c.memo_group_slice))))|| ((List.length c.memo_group_cons)>0)
      | _ -> true 
 
and filter_mem fvs lst  = 
  filter_mem_fct (fun c->List.length(Util.intersect_fct eq_spec_var fvs (bfv c.memo_formula))>0) lst
 
and recompute_unknowns (p:memo_pure): memo_pure= p
    
and filter_merged_cons l =   
  let keep c1 c2 = match c1.memo_status ,c2.memo_status with
    | Implied _ , Implied _ 
    | Implied_dupl, Implied_dupl 
    | Unknown_prune _, Unknown_prune _ 
    | Fail_prune,Fail_prune -> if (equalBFormula c1.memo_formula c2.memo_formula) then (true,false) else (true,true)
    | Implied _ , Implied_dupl -> if (equalBFormula c1.memo_formula c2.memo_formula) then (false,true) else (true,true)
    | Implied_dupl , Implied _ -> if (equalBFormula c1.memo_formula c2.memo_formula) then (true,false) else (true,true)
    | _ -> (true, true) in
    
  let rec remove_d n = match n with 
    | [] -> []
    | q::qs -> 
      let b,r = List.fold_left (fun (b,r) c-> 
        let r1,r2 = keep q c in
        (b&&r1,if r2 then c::r else r)) (true,[])qs in
      if b then q::(remove_d r) else (remove_d r) in
  (*
  let rec remove_d n =  match n with | [] -> []
  | q::qs -> 
    let nqs = List.filter (fun c-> not (mem_eq_st c q)) qs in
    q::(remove_d nqs)in   *)
  Util.push_time "filter_dupl_memo";let r = remove_d (List.concat l) in Util.pop_time "filter_dupl_memo"; r
  
and mkOr_mems (l1: memo_pure) (l2: memo_pure) (*with_dupl with_inv*) : memo_pure = 
  let f1 = fold_mem_lst (mkTrue no_pos) false true l1 in
  let f2 = fold_mem_lst (mkTrue no_pos) false true l2 in
   memoise_add_pure [] (mkOr f1 f2 None no_pos)
   
and combine_memo_branch b (f, l) =
  match b with 
  | "" -> f
  | s -> try 
    memoise_add_pure f (List.assoc b l) with Not_found -> f

and merge_mems (l1: memo_pure) (l2: memo_pure) slice_check_dups: memo_pure = 
  if (isConstMFalse l1)||(isConstMTrue l2) then l1
  else if (isConstMFalse l2)||(isConstMTrue l1) then l2
  else
    let n_l = List.fold_left (fun a c-> 
      let merged, un_merged = List.partition (fun d-> (List.length(Util.intersect_fct eq_spec_var d.memo_group_fv c.memo_group_fv))>0) a in
      let n1,n2,n3 = List.fold_left 
          (fun (a1,a2,a3) d-> (d.memo_group_fv@a1,d.memo_group_cons::a2, d.memo_group_slice::a3)) 
          (c.memo_group_fv,[c.memo_group_cons], [c.memo_group_slice]) 
          merged in
      let ng = if (List.length merged)>0 then
        let n3 = List.concat n3 in
        let n_slc = if (not slice_check_dups) then n3 
        else 
          (Util.push_time "merge_mems_r_dups";
          let r = Util.remove_dups_f n3 eq_pure_formula in
          Util.pop_time "merge_mems_r_dups";
          r)in
          {memo_group_fv = Util.remove_dups n1; 
           memo_group_cons = filter_merged_cons n2;
           memo_group_changed = true;
           memo_group_slice = n_slc;}
        else c in
      ng::un_merged) l2 l1 in
    recompute_unknowns n_l

and memoise_add_memo (l: memo_pure) (cm:memoised_constraint): memo_pure =
  let fv = bfv cm.memo_formula in
  let merged,un_merged = List.partition (fun c-> (List.length (Util.intersect_fct eq_spec_var fv c.memo_group_fv))>0) l in
  let n1,n2,n3 = List.fold_left (fun (a1,a2,a3) d-> (d.memo_group_fv@a1,d.memo_group_cons::a2,d.memo_group_slice::a3))(fv,[[cm]],[]) merged in   
  let l = if (List.length merged)>0 then 
    let ng = {memo_group_cons =  filter_merged_cons n2; 
              memo_group_fv = Util.remove_dups n1;
              memo_group_changed = true;
              memo_group_slice = List.concat n3;} in
    List.hd (recompute_unknowns [ng])
    else {memo_group_cons =[cm]; memo_group_fv = fv; memo_group_changed = true; memo_group_slice = []} in  
  l::un_merged   
  
and memoise_add_pure (l: memo_pure) (p:formula) : memo_pure = 
  if (isConstTrue p)||(isConstMFalse l) then l 
  else if (isConstFalse p) then mkMFalse no_pos
  else 
    (Util.push_time "add_pure";  
    let disjs, rests = List.fold_left (fun (a1,a2) c-> match c with | BForm x -> (x::a1,a2) | _ -> (a1,c::a2))([],[]) (list_of_conjs p) in
    let m2 = create_memo_group disjs rests false in
    let r = merge_mems l m2 true in
    Util.pop_time "add_pure"; r)
   
(*add both imply and fail*)

and create_memo_group_wrapper (l1:b_formula list) inv_cons : memo_pure = 
  let l = List.map (fun c-> (c, None, None)) l1 in
  create_memo_group l [] inv_cons 

and create_memo_group (l1:(b_formula *(formula_label option)* (int option)) list) (l2:formula list) inv_cons:memo_pure = 
  let l1,l_to_slice = memo_norm l1 in
  let l1 = Util.remove_dups l1 in
  let l2 = (List.map (fun c-> BForm c) l_to_slice)@l2 in
  let l2 = List.map (fun c-> (None, Some c)) l2 in
  let l1 = List.map (fun c-> (Some c,None)) l1 in  
  let ll  = List.fold_left ( fun a f->
    let fv = match f with | None, Some c-> fv c | Some c, None -> bfv c | _-> [] in
    let rec f_rec fv a = 
        let r1,r2 = List.partition (fun (v,_,_)-> (List.length (Util.intersect_fct eq_spec_var fv v))>0) a in
        if r1 = [] then ([],r2)
        else
          let n_fv = List.fold_left (fun ac (v,_,_)-> ac@v) fv r1 in
          let x1,x2 = f_rec n_fv r2 in
          (r1@x1,x2) in
    let to_merge, no_merge = f_rec fv a in
    let merg_fv,merg_bf, merg_f  = List.fold_left (fun (a1,a2,a3)(c1,c2,c3)-> (a1@c1,a2@c2,a3@c3)) ([],[],[]) to_merge in
    let merg_fv = Util.remove_dups (merg_fv@fv) in
    match f with 
      | None, Some c -> (merg_fv,merg_bf,c::merg_f)::no_merge 
      | Some c, None -> (merg_fv,c::merg_bf,merg_f)::no_merge 
      | _-> no_merge) [] (l1@l2) in
  List.map (fun (vars,bfs,fs)-> 
    let nfs = List.fold_left (fun a c-> 
      let pos = {memo_formula=c;memo_status = Implied (not inv_cons)} in
      let neg = {memo_formula=memo_f_neg c;memo_status = Fail_prune} in
    (pos::(neg::a))) [] bfs in 
    { memo_group_fv=vars;
      memo_group_cons=filter_merged_cons [nfs];
      memo_group_slice = fs;
      memo_group_changed = true}) ll
  
and memo_pure_push_exists qv c = List.map (memo_group_push_exists qv) c
  
and memo_group_push_exists qv c =
  if (List.length (Util.intersect_fct eq_spec_var qv c.memo_group_fv)=0) then c 
  else 
    let r,drp1 = List.partition (fun c-> (List.length (Util.intersect_fct eq_spec_var (bfv c.memo_formula) qv))>0) c.memo_group_cons in
    let ns,drp2 = List.partition (fun c-> (List.length (Util.intersect_fct eq_spec_var (fv c) qv))>0) c.memo_group_slice in
    let fand = List.fold_left (fun a c-> match c.memo_status with
      | Implied _
      | Implied_dupl -> mkAnd a (BForm (c.memo_formula, None, None)) no_pos
      | _ -> a) (mkTrue no_pos) r in
    let fand = List.fold_left (fun a c-> mkAnd a c no_pos) fand ns in
    let fand = mkExists qv fand None no_pos in
     {memo_group_fv = Util.difference c.memo_group_fv qv;
      memo_group_changed = true;
      memo_group_cons = drp1;
      memo_group_slice = fand::drp2;}
   

and memo_norm (l:(b_formula *(formula_label option)* (int option)) list): b_formula list * (b_formula *(formula_label option)* (int option)) list = 
  let rec get_head e = match e with 
    | Null _ -> "Null"
    | Var (v,_) -> name_of_spec_var v
    | IConst (i,_)-> string_of_int i
    | FConst (f,_) -> string_of_float f
    | Add (e,_,_) | Subtract (e,_,_) | Mult (e,_,_) | Div (e,_,_)
    | Max (e,_,_) | Min (e,_,_) | BagDiff (e,_,_) | ListCons (e,_,_)| ListHead (e,_) 
    | ListTail (e,_)| ListLength (e,_) | ListReverse (e,_)  -> get_head e
    | Bag (e_l,_) | BagUnion (e_l,_) | BagIntersect (e_l,_) | List (e_l,_) | ListAppend (e_l,_)-> 
      if (List.length e_l)>0 then get_head (List.hd e_l) else "[]" in
  
  let e_cmp e1 e2 =  String.compare (get_head e1) (get_head e2) in
     
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
    | Null _ | Var _ | IConst _ | FConst _ | Max _  | Min _ | Bag _ | BagUnion _ | BagIntersect _ 
    | BagDiff _ | List _ | ListCons _ | ListHead _ | ListTail _ | ListLength _ | ListAppend _ | ListReverse _ -> ([e],[]) in
    
  let rec norm_expr e = match e with
    | Null _ | Var _ | IConst _ | FConst _ -> e
    | Add (e1,e2,l) -> cons_lsts e 1 (fun c-> Add c) (fun d-> Subtract d) (IConst (0,l))
    | Subtract (e1,e2,l) -> cons_lsts e 1 (fun c-> Add c) (fun d-> Subtract d) (IConst (0,l))
    | Mult (e1,e2,l) -> cons_lsts e (-1) (fun c-> Mult c) (fun d-> Div d) (IConst (1,l))
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
    
  and cons_lsts (e:exp) (disc:int) cons1 cons2 (nel:exp) : exp=     
    let lp,ln = get_lists e disc in
    let lp = List.sort e_cmp (List.map norm_expr lp) in
    let ln = List.sort e_cmp (List.map norm_expr ln) in
    if (List.length lp)>0 then
      let a = List.fold_left (fun a c-> cons1(a,c,no_pos)) (List.hd lp) (List.tl lp) in
      List.fold_left(fun a c-> cons2 (a,c,no_pos)) a ln
    else List.fold_left(fun a c-> cons2 (a,c,no_pos)) nel ln in
  Util.push_time "memo_norm";
  let l = List.fold_left (fun (a1,a2) (c1,c2,c3)-> 
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
      | BagMax _ | ListAllN _ | ListPerm _ -> (a1,(c1,c2,c3)::a2)) ([],[]) l in
    Util.pop_time "memo_norm";l
  
let memo_norm_wrapper (l:b_formula list): b_formula list = 
 let l = List.map (fun c-> (c,None,None)) l in
 fst (memo_norm l)
  
  
(******************************************************************************************************************
	End utilities for memoized formulas
******************************************************************************************************************)


let transform_memo_formula f l : memo_pure =
  let (f_memo, f_formula, f_b_formula, f_exp) = f in
  let r = f_memo l in 
	match r with
	| Some e1 -> e1
	| None  -> List.map (fun c-> {
      memo_group_fv = c.memo_group_fv;
      memo_group_changed = true;
      memo_group_cons = List.map (fun c-> {c with memo_formula = transform_b_formula (f_b_formula,f_exp) c.memo_formula}) c.memo_group_cons;
      memo_group_slice = List.map (transform_formula f) c.memo_group_slice;
    }) l
