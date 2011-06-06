open Globals
module P = Cpure
module Ts = Tree_shares

type share = Ts.stree

type frac_perm = 
	| PConst of share
	| PVar of P.spec_var

(*perm_modifier*)

type perm_formula = 
  | And of (perm_formula * perm_formula * loc)
  | Or  of (perm_formula * perm_formula * loc)
  | Join of (frac_perm*frac_perm*frac_perm * loc) (*v1+v2 = v3*)
  | Eq of (frac_perm*frac_perm *loc)
  | Exists of (P.spec_var  list * perm_formula *loc)
  | PTrue of loc
  | PFalse of loc

let print_perm_f = ref (fun (c:perm_formula)-> " printing not initialized")
let print_frac_f = ref (fun (b:bool) (c:frac_perm)-> "printing not initialized")
  
let fresh_perm_var () = P.SpecVar (Named perm,fresh_name(),Unprimed)

let top_share = Ts.top

let mkCPerm s : frac_perm = PConst s
let mkVPerm v :frac_perm = PVar v
  
let mkPFull () :frac_perm = mkCPerm top_share

let mkTrue pos = PTrue pos
let mkFalse pos = PFalse pos

let mkOr f1 f2 pos = match f1 with
  | PTrue _ -> f1
  | PFalse _ -> f2
  | _ -> match f2 with
        | PTrue _ -> f2
        | PFalse _ -> f1 
        | _ -> Or (f1,f2,pos)

let mkAnd f1 f2 pos = match f1 with
  | PTrue _ -> f2
  | PFalse _ -> f1
  | _ -> match f2 with
        | PTrue _ -> f1
        | PFalse _ -> f2 
        | _ -> And (f1,f2,pos)
        
let mkEq f1 f2 pos = Eq (f1,f2,pos)

let is_full_frac t = Ts.stree_eq t Ts.top 

let mkFullVar () : (P.spec_var * perm_formula) = 
  let nv = fresh_perm_var() in
  (nv,mkEq (mkVPerm nv) (mkPFull ()) no_pos)

let mkJoin v1 v2 v3 pos = Join (v1,v2,v3,pos)

let isConstFalse f = match f with PFalse _ -> true | _ -> false
let isConstTrue  f = match f with PTrue _ -> true | _ -> false

let frac_fv f= match f with | PVar v -> [v] | PConst _ -> []

let rec fv f = match f with
  | And (f1,f2,_) -> Gen.BList.remove_dups_eq P.eq_spec_var ((fv f1)@(fv f2))
  | Or (f1,f2,_) -> Gen.BList.remove_dups_eq P.eq_spec_var ((fv f1)@(fv f2))
  | Join (f1,f2,f3,_) -> Gen.BList.remove_dups_eq P.eq_spec_var ((frac_fv f1)@(frac_fv f2)@(frac_fv f3))
  | Eq (f1,f2,_) -> Gen.BList.remove_dups_eq P.eq_spec_var ((frac_fv f1)@(frac_fv f2))
  | Exists (l1,f1,_) -> Gen.BList.difference_eq P.eq_spec_var (fv f1) l1
  | PTrue _ | PFalse _ -> [] 
    
(*
let to_cnf f = 
 let rec merge_f l g1 g2 = match g1 with
    | Or (f1,f2,l)-> mkOr (merge_f l f1 g2) (merge_f l f2 g2) l
    | _ -> match g2 with
      | Or (f1,f2,l) -> mkOr (merge_f l g1 f1) (merge_f l g1 f2) l
      | _ -> mkAnd g1 g2 l in
  let rec cnf_c f = match f with
    | PTrue _ | PFalse _ | Join _  | Eq _ | Exists _ -> f 
    | And (f1,f2,l) -> 
       let f1 = cnf_d f1 in
       let f2 = cnf_d f2 in
       (merge_f l f1 f2) in
  let rec cnf_d f = match f with
    | Or (f1,f2,l) -> mkOr (cnf_d f1, cnf_d f2, l)
    | _ -> cnf_c f in
 cnf_d f
 *)
 
let mkExists vl f pos =  match f with
  | PFalse _
  | PTrue _ -> f
  | _ ->
    let nl = Gen.BList.intersect_eq P.eq_spec_var vl (fv f) in
    if nl==[] then f else Exists (nl,f,pos)
    
and subst_perm (fr, t) o = match o with
  | PVar s -> PVar (P.subst_var (fr,t) s)
  | PConst _  -> o
  
and subst_perm_expr (fr, t) o = match o with
  | PVar s -> if (P.eq_spec_var s fr) then t else o
  | PConst _ -> o
  
let rec apply_one_gen (fr,t) f f_s= match f with
  | And (f1,f2,p) -> mkAnd (apply_one_gen (fr,t) f1 f_s) (apply_one_gen (fr,t) f2 f_s ) p
  | Or (f1,f2,p) -> Or (apply_one_gen (fr,t) f1 f_s ,apply_one_gen (fr,t) f2 f_s , p)
  | Join (f1,f2,f3,p) -> Join (f_s (fr,t) f1, f_s (fr,t) f2, f_s (fr,t) f3, p)
  | Eq (f1,f2,p) -> Eq (f_s (fr,t) f1, f_s (fr,t) f2, p)
  | Exists (qsv,f1,p) ->  
      if Gen.BList.mem_eq P.eq_spec_var fr qsv then f 
      else Exists (qsv, apply_one_gen (fr,t) f1 f_s , p)
  | _ -> f

let apply_one s f = apply_one_gen s f subst_perm
let apply_one_exp s f = apply_one_gen s f subst_perm_expr
  
let rec subst (sst : (P.spec_var * P.spec_var) list) (f : perm_formula) : perm_formula = match sst with
  | s::ss -> subst ss (apply_one s f) 				(* applies one substitution at a time *)
  | [] -> f

and subst_avoid_capture (fr : P.spec_var list) (t : P.spec_var list) (f : perm_formula) =
  let st1 = List.combine fr t in
  let f2 = apply_subs st1 f in 
  f2
  
and apply_subs_frac sst f = match f with
  | PVar v -> PVar (P.subs_one sst v)
  | PConst _ -> f
  
and apply_subs (sst : (P.spec_var * 'b) list) (f : perm_formula) : perm_formula = match f with
  | And (f1,f2,p) -> And (apply_subs sst f1,apply_subs sst f2, p)
  | Or (f1,f2,p) -> Or (apply_subs sst f1,apply_subs sst f2, p)
  | Join (f1,f2,f3,p) -> Join (apply_subs_frac sst f1, apply_subs_frac sst f2, apply_subs_frac sst f3, p)
  | Eq (f1,f2,p) -> Eq (apply_subs_frac sst f1, apply_subs_frac sst f2, p)
  | Exists (qsv,f1,p) -> 
      let nv,nf = List.fold_left (fun (av,af) v->
        let sst = P.diff sst v in
        if (P.var_in_target v sst) then
          let fresh_v = P.fresh_spec_var v in
          (fresh_v::av, apply_subs sst (apply_one (v, fresh_v) af))
        else (v::av, apply_subs sst af) ) ([],f1) qsv in
      Exists (nv,nf,p)
  | _ -> f 
  
let eq_fperm v1 v2  = match v1,v2 with
  | PVar v1,PVar v2 -> P.eq_spec_var v1 v2 
  | PConst c1,PConst c2 -> Ts.stree_eq c1 c2
  | _ -> false
  
let rec eq_perm_formula (f1 : perm_formula) (f2 : perm_formula) : bool = match (f1,f2) with
  | And (f11,f12,_), And (f21,f22,_)
  | Or  (f11,f12,_), Or (f21,f22,_) -> 
      ((eq_perm_formula f11 f21) && (eq_perm_formula f12 f22))||((eq_perm_formula f11 f22) && (eq_perm_formula f12 f21))
  | Join (f11,f12,f13,_), Join (f21,f22,f23,_) -> 
      ((eq_fperm f11 f21)&&(eq_fperm f12 f22)&&(eq_fperm f13 f23)) || ((eq_fperm f11 f22)&&(eq_fperm f12 f21)&&(eq_fperm f13 f23))
  | Eq (f11,f12,_) , Eq(f21,f22,_) -> ((eq_fperm f11 f21)&&(eq_fperm f12 f22)) || ((eq_fperm f11 f22)&&(eq_fperm f12 f21))
  | Exists (l1,f1,_), Exists (l2,f2,_) -> (List.length l1 = List.length l2 ) && (List.for_all2 P.eq_spec_var l1 l2) && (eq_perm_formula f1 f2)
  | PTrue _, PTrue _
  | PFalse _, PFalse _ -> true
  | _ -> false
 

let rec list_of_conjs (f:perm_formula): perm_formula list = match f with
  | And (f1,f2,_) -> (list_of_conjs f1) @ (list_of_conjs f2)
  | _ -> [f]
  
let conj_of_list l = List.fold_left (fun a c-> mkAnd a c no_pos) (mkTrue no_pos) l

let rec factor_comm f = match f with
  | Or (f1,f2,p)->  
    let f1 = factor_comm f1 in
    let f2 = factor_comm f2 in
    let l1 = list_of_conjs f1 in
    let l2 = list_of_conjs f2 in
    let com,ncom1,ncom2 = List.fold_left (fun (comm,ncomm,l2) c -> 
      let l1,l2 = List.partition (fun c1-> eq_perm_formula c1 c) l2 in
      match l1 with
        | [] -> (comm,c::ncomm,l2)
        | _ -> (c::comm,ncomm,l2)) ([],[],l2) l1 in
    conj_of_list ((mkOr (conj_of_list ncom1) (conj_of_list ncom2) p)::com)
  | And (f1,f2,p)-> mkAnd (factor_comm f1) (factor_comm f2) p 
  | Join _ -> f
  | Eq _ -> f
  | Exists (v,f,p)-> mkExists v (factor_comm f) p
  | _ -> f
  
let var_get_subst f1 f2 v pos = match f1,f2 with 
  | PVar v1 , PVar v2 -> 
	  if P.eq_spec_var v1 v2 then ([],mkTrue pos)
      else if P.eq_spec_var v v1 then ([(v,f2)],mkTrue pos)
      else if P.eq_spec_var v v2 then ([(v,f1)],mkTrue pos)
      else ([],mkEq f1 f2 pos)
  | PVar v1, _ -> if P.eq_spec_var v v1 then ([(v,f2)],mkTrue pos) else ([],mkEq f1 f2 pos)
  | _ ,PVar v2 -> if P.eq_spec_var v v2 then ([(v,f1)],mkTrue pos) else ([],mkEq f1 f2 pos)
  | PConst _ ,PConst _ -> ([],mkEq f1 f2 pos)
  
let rec get_subst_eq_f f v = match f with
  | And (f1,f2,p) -> 
    let st1, rf1 = get_subst_eq_f f1 v in
		if (List.length st1)>0 then  (st1, mkAnd rf1 f2 p)
		else
		  let st2, rf2 = get_subst_eq_f f2 v in
		  (st2, mkAnd rf1 rf2 p)
  | Eq(f1,f2,p)-> var_get_subst f1 f2 v p
  | _ -> [],f
  
(*elim exists*)(*TODO*) 
(*try and eliminate vars from w, what can not be done return*)
let elim_exists_perm w f1 = (w,f1)
(*try and eliminate vars from w, what can not be done, push as existentials-eliminate them*)
let elim_exists w f1 = f1 (*loop*)


  (*let f = factor_comm f1 in
  List.fold_left (fun (a1,a2) c->
    let s,nf = get_subst_eq_f a2 c in
    if (Util.empty s) then (w::a1,a2)
    else (a1,apply_subs s nf)) ([],f) w *)
    
(*TODO*)
let elim_exists_exp_perm f = f
(*TODO*)
let simpl_perm_formula f = f

(*imply*)(*TODO*)
let imply f1 f2 = true
(*TODO*)
let match_imply l_v r_v l_f r_f l_node e_vars :(bool * P.spec_var * P.spec_var * 'a * 'b * 'c) option = 
    Some (false,l_v, r_v, l_f, r_f, l_node)

(*sat*)(*TODO*)

let is_sat f = true
  
    
let does_match p = match p with
  | Some _ -> true
  | None -> false
  
let needs_split p = match p with
  | Some (true,_,_,_,_,_)-> true
  | _ -> false

let heap_partial_imply l_h l_pr perm_imply mkStarH h_apply_one pos = match perm_imply with
  | Some (b,l_v,r_v,l_f,r_f,l_node)->
    if b then 
      let s1 = fresh_perm_var () in
      let s2 = fresh_perm_var () in
      let l_node' = h_apply_one (l_v,s1) l_node in
      let l_h' = mkStarH l_node' l_h pos in
      let pr_eq = mkJoin (mkVPerm l_v) (mkVPerm s1) (mkVPerm s2) pos in
      let l_pr'= mkAnd l_pr pr_eq pos in
      (l_h',l_pr',[s1;s2],(r_v,s2))
    else (l_h,l_pr,[],(r_v,l_v))
  | None -> 
    let f = fresh_perm_var () in
    let t = fresh_perm_var () in
    (l_h,l_pr,[],(f,t))

and get_eqns_free ((fr,t) : P.spec_var * P.spec_var) (evars : P.spec_var list) (expl_inst : P.spec_var list) 
      (struc_expl_inst : P.spec_var list) pos : perm_formula*perm_formula * (P.spec_var * P.spec_var) list = 
	if (P.mem fr evars) || (P.mem fr expl_inst) then (mkTrue pos, mkTrue pos,[(fr, t)])
  else if (P.mem fr struc_expl_inst) then (mkTrue pos, mkEq (mkVPerm fr) (mkVPerm t) pos,[])
  else (mkEq (mkVPerm fr) (mkVPerm t) pos, mkTrue pos, [])


(*transformers*)

let get_subst_equation_perm_formula f qvars = ([],f)


let transform_frac f (e:frac_perm) : frac_perm = match f e with
    | Some e -> e
    | None -> e

let rec transform_perm (f:(perm_formula->perm_formula option)* (frac_perm -> frac_perm option)) (e:perm_formula) :perm_formula = 
	let (f_perm_f, f_frac) = f in
	let r =  f_perm_f e in 
	match r with
	| Some e1 -> e1
	| None  -> match e with	  
    | PTrue _ -> e
    | PFalse _ -> e
    | Or (f1,f2,p) ->
      let nf1 = transform_perm f f1 in
      let nf2 = transform_perm f f2 in
      mkOr nf1 nf2 p
    | And (f1,f2,p) ->
      let nf1 = transform_perm f f1 in
      let nf2 = transform_perm f f2 in
      mkAnd nf1 nf2 p
    | Join (fr1,fr2,fr3,p) ->
      let nfr1 = transform_frac f_frac fr1 in
      let nfr2 = transform_frac f_frac fr2 in
      let nfr3 = transform_frac f_frac fr3 in
      mkJoin nfr1 nfr2 nfr3 p 
    | Eq (fr1,fr2,p) ->
      let nfr1 = transform_frac f_frac fr1 in
      let nfr2 = transform_frac f_frac fr2 in
      mkEq nfr1 nfr2 p
    | Exists (qv,fr,p) ->
      let nfr = transform_perm f fr in
      mkExists qv nfr p 
      
let fold_frac_perm (e:frac_perm) (arg: 'a) f f_arg (f_comb: (*frac_perm ->*) 'b list -> 'b) :(frac_perm * 'b) =
  let r = f arg e in
  match r with
  | Some s -> s
  | None -> (e, f_comb  [])
      
let trans_perm (e:perm_formula) (arg: 'a) f f_arg f_comb_a : (perm_formula * 'b) =
 let f_perm, f_frac = f in
 let f_perm_arg, f_frac_arg = f_arg in
 (*let f_perm_comb, f_frac_comb = f_comb_a in*)
 let foldr_frac (arg: 'a) (e: frac_perm): (frac_perm * 'b) = fold_frac_perm e arg f_frac f_frac_arg f_comb_a in   
    
 let rec foldr_f (arg: 'a) (e:perm_formula) :(perm_formula * 'b) = 
   let r = f_perm arg e in
   match r with
   | Some e -> e
   | None ->
      let new_arg = f_perm_arg arg e in
      let f_comb = f_comb_a  in
      match e with
      | Or (f1,f2,p) ->
        let nf1, r1 = foldr_f new_arg f1 in
        let nf2, r2 = foldr_f new_arg f2 in
        (mkOr nf1 nf2 p, f_comb [r1;r2])
      | And (f1,f2,p) ->
        let nf1, r1 = foldr_f new_arg f1 in
        let nf2, r2 = foldr_f new_arg f2 in
        (mkAnd nf1 nf2 p, f_comb [r1;r2])
      | Join (f1,f2,f3,p) ->
        let nf1,r1 = foldr_frac new_arg f1 in
        let nf2,r2 = foldr_frac new_arg f2 in
        let nf3,r3 = foldr_frac new_arg f3 in
        (mkJoin nf1 nf2 nf3 p, f_comb [r1;r2;r3])
      | Eq (f1,f2,p) ->
        let nf1,r1 = foldr_frac new_arg f1 in
        let nf2,r2 = foldr_frac new_arg f2 in
        (mkEq nf1 nf2 p, f_comb [r1;r2])
      | Exists (qv,f,p) ->
         let nf,r = foldr_f new_arg f in
         (mkExists qv nf p, f_comb [r]) 
      | PTrue _ -> (e,f_comb [])
      | PFalse _ -> (e, f_comb []) in
 foldr_f arg e

let rec normalize_to_CNF (f : perm_formula) pos : perm_formula = match f with
  | Or (f1, f2, p) ->
        let conj, disj1, disj2 = (find_common_conjs f1 f2 p) in
	     (mkAnd conj (mkOr disj1 disj2 p) p)
  | And (f1, f2, p) -> mkAnd (normalize_to_CNF f1 p) (normalize_to_CNF f2 p) p
  | Exists (sp, f1, p) -> mkExists sp (normalize_to_CNF f1 p) p
  | _ -> f
(* take two formulas f1 and f2 and returns:
   - the formula containing the commom conjuncts
   - the formula representing what's left of f1
   - the formula representing what's left of f2
*)
  
 and find_common_conjs (f1 : perm_formula) (f2 : perm_formula) pos : (perm_formula * perm_formula * perm_formula) = match f1 with
  | Eq _ 
  | Join _ ->
        if (List.exists (fun c -> (eq_perm_formula c f1)) (list_of_conjs f2)) then (f1, (mkTrue pos), (remove_conj f2 f1 pos))
        else ((mkTrue pos), f1, f2)
  | And(f11, f12, p) ->
        let outer_conj, new_f1, new_f2 = (find_common_conjs f11 f2 p) in
        let outer_conj_prim, new_f1_prim, new_f2_prim  = (find_common_conjs f12 new_f2 p) in
	    ((mkAnd outer_conj outer_conj_prim p), (mkAnd new_f1 new_f1_prim p), new_f2_prim)
  | Or(f11, f12, p) ->
        let new_f11 = (normalize_to_CNF f11 p) in
        let new_f12 = (normalize_to_CNF f12 p) in
	    (mkTrue pos),(mkOr new_f11 new_f12 p),f2
  | _ -> ((mkTrue pos), f1, f2)

and remove_conj (f : perm_formula) (conj : perm_formula) pos : perm_formula = match f with
  | Eq _
  | Join _ -> if eq_perm_formula f conj then mkTrue pos else f
  | And(f1, f2, p) ->
        (mkAnd (remove_conj f1 conj p) (remove_conj f2 conj p) p)
  | _ -> f

  

let find_rel_constraints (f:perm_formula) desired :perm_formula = 
 if desired=[] then (mkTrue no_pos)
 else 
   let lf = list_of_conjs f in
   let lf_pair = List.map (fun c-> ((fv c),c)) lf in
   let var_list = fst (List.split lf_pair) in
   let rec helper (fl:P.spec_var list) : P.spec_var list = 
    let nl = List.filter (fun c-> (Gen.BList.intersect_eq P.eq_spec_var c fl)!=[]) var_list in
    let nl = List.concat nl in
    if (List.length fl)=(List.length nl) then fl
    else helper nl in
   let fixp = helper desired in
   let pairs = List.filter (fun (c,_) -> (List.length (Gen.BList.intersect_eq P.eq_spec_var c fixp))>0) lf_pair in
   conj_of_list (snd (List.split pairs))