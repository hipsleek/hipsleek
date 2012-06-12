open Globals

module P = Cpure
module Ts = Tree_shares.Ts

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
  | Exists1 of (P.spec_var  list * perm_formula *loc)
  | Dom of (P.spec_var * share * share)
  | PTrue of loc
  | PFalse of loc

let print_counter = ref 0
let perm_log_name = "perm.log.tex" 
let perm_log_file = ref (stdout)
let print_perm_f = ref (fun (c:perm_formula)-> " printing not initialized")
let print_frac_f = ref (fun (c:frac_perm)-> "printing not initialized")
let print_sv = ref (fun (s:P.spec_var)-> "printing not initialized")
let print_share = ref (fun (s:share)-> "printing not initialized")
let latex_of_formula = ref (fun (f:perm_formula) -> "latexing not initialized ")
let latex_print_sv v = 
  let s = !print_sv v in
  let rec helper i = 
    if (i>=0) then 
      let c = String.get s i in 
     (helper (i-1))^ (if c=='_' then "\\_" else if c=='\'' then "'" else if c=='\\' then "\\" else Char.escaped c)
    else "" in
  " \\ensuremath{ \\mathsf{"^(helper ((String.length s)-1))^"} } "


let fresh_perm_var () = P.SpecVar (Named perm,fresh_name(),Unprimed)

let mk_perm_var (a,b) = P.SpecVar (Named perm, a,b)

let top_share = Ts.top
let bot_share = Ts.bot

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
        
let eq_fperm v1 v2  = match v1,v2 with
  | PVar v1,PVar v2 -> P.eq_spec_var v1 v2 
  | PConst c1,PConst c2 -> Ts.stree_eq c1 c2
  | _ -> false
        
let mkEq f1 f2 pos = if (eq_fperm f1 f2)  then PTrue pos else Eq (f1,f2,pos)

let mkEq_vars f1 f2 pos = if (P.eq_spec_var f1 f2) then mkTrue pos else  Eq (PVar f1,PVar f2,pos)

let is_full_frac t = Ts.stree_eq t Ts.top 

let isConstFperm f = match f with
  | PConst _ -> true 
  | _ -> false

let isConstXFperm x f = match f with
  | PConst s  -> Ts.stree_eq s x
  | _ -> false
(*let mkFullVar () : (P.spec_var * perm_formula) = 
  let nv = fresh_perm_var() in
  (nv,mkEq (mkVPerm nv) (mkPFull ()) no_pos)*)

let mkJoin v1 v2 v3 pos = Join (v1,v2,v3,pos)

let mkDom v d1 d2 = if (Ts.contains d2 d1)&&(not (Ts.empty d2)) then Dom (v,d1,d2) else PFalse no_pos

let isConstFalse f = match f with PFalse _ -> true | _ -> false
let isConstTrue  f = match f with PTrue _ -> true | _ -> false

let frac_fv f= match f with | PVar v -> [v] | PConst _ -> []

let rec fv f = match f with
  | And (f1,f2,_) -> Gen.BList.remove_dups_eq P.eq_spec_var ((fv f1)@(fv f2))
  | Or (f1,f2,_) -> Gen.BList.remove_dups_eq P.eq_spec_var ((fv f1)@(fv f2))
  | Join (f1,f2,f3,_) -> Gen.BList.remove_dups_eq P.eq_spec_var ((frac_fv f1)@(frac_fv f2)@(frac_fv f3))
  | Eq (f1,f2,_) -> Gen.BList.remove_dups_eq P.eq_spec_var ((frac_fv f1)@(frac_fv f2))
  | Exists1 (l1,f1,_) -> Gen.BList.difference_eq P.eq_spec_var (fv f1) l1
  | Dom (v,_,_) -> [v]
  | PTrue _ | PFalse _ -> [] 
  
let mkExists1 vl f pos =  match f with
  | PFalse _
  | PTrue _ -> f
  | _ ->
    let nl = Gen.BList.intersect_eq P.eq_spec_var vl (fv f) in
    if nl=[] then f else Exists1 (nl,f,pos) 
    
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
  | Eq (f1,f2,p) -> mkEq (f_s (fr,t) f1) (f_s (fr,t) f2)  p
  | Dom (v,d1,d2) -> (match f_s (fr,t) (PVar v) with
	 | PVar v-> Dom (v,d1,d2)
	 | PConst v-> if Ts.contains d2 v && Ts.contains v d1 then PTrue no_pos else PFalse no_pos)
  | Exists1 (qsv,f1,p) ->  
      if Gen.BList.mem_eq P.eq_spec_var fr qsv then f 
      else Exists1 (qsv, apply_one_gen (fr,t) f1 f_s , p)
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
  | Dom (v,d1,d2) -> Dom (P.subs_one sst v, d1,d2)
  | Exists1 (qsv,f1,p) -> 
      let nv,nf = List.fold_left (fun (av,af) v->
        let sst = P.diff sst v in
        if (P.var_in_target v sst) then
          let fresh_v = P.fresh_spec_var v in
          (fresh_v::av, apply_subs sst (apply_one (v, fresh_v) af))
        else (v::av, apply_subs sst af) ) ([],f1) qsv in
      Exists1 (nv,nf,p)
  | _ -> f 
    
let cmp_fperm v1 v2 = match v1,v2 with
  | PVar v1,PVar v2 -> P.cmp_spec_var v1 v2 
  | PConst c1,PConst c2 -> Ts.stree_cmp c1 c2
  | PVar _, PConst _ -> -1
  | PConst _, PVar _ ->  1
  
let rec eq_perm_formula (f1 : perm_formula) (f2 : perm_formula) : bool = match (f1,f2) with
  | And (f11,f12,_), And (f21,f22,_)
  | Or  (f11,f12,_), Or (f21,f22,_) -> 
      ((eq_perm_formula f11 f21) && (eq_perm_formula f12 f22))||((eq_perm_formula f11 f22) && (eq_perm_formula f12 f21))
  | Join (f11,f12,f13,_), Join (f21,f22,f23,_) -> 
      ((eq_fperm f11 f21)&&(eq_fperm f12 f22)&&(eq_fperm f13 f23)) || ((eq_fperm f11 f22)&&(eq_fperm f12 f21)&&(eq_fperm f13 f23))
  | Eq (f11,f12,_) , Eq(f21,f22,_) -> ((eq_fperm f11 f21)&&(eq_fperm f12 f22)) || ((eq_fperm f11 f22)&&(eq_fperm f12 f21))
  | Exists1 (l1,f1,_), Exists1 (l2,f2,_) -> (List.length l1 = List.length l2 ) && (List.for_all2 P.eq_spec_var l1 l2) && (eq_perm_formula f1 f2)
  | Dom (v1,d11,d12), Dom (v2,d21,d22) -> P.eq_spec_var v1 v2 && Ts.stree_eq d11 d21 && Ts.stree_eq d12 d22
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
  | Dom _ -> f
  | Eq _ -> f
  | Exists1 (v,f,p)-> mkExists1 v (factor_comm f) p
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
 
and get_eqns_free_a ((r_node_pr,l_node_pr) : P.spec_var option * P.spec_var option) (evars : P.spec_var list) (expl_inst : P.spec_var list) 
      (struc_expl_inst : P.spec_var list) pos : perm_formula*perm_formula * (P.spec_var * P.spec_var option) list = 
	let tr = mkTrue pos in
	match l_node_pr, r_node_pr with
		| None, None -> (tr, tr, [])
		| Some v, None -> (tr, mkEq (mkVPerm v) (mkPFull ()) pos,[])
		| _ , Some v -> 
			let dst = match l_node_pr with | None -> mkPFull () | Some v-> mkVPerm v in
			let r = mkEq (mkVPerm v) dst pos in
			if (P.mem v evars) || (P.mem v expl_inst) then (tr,tr,[(v, l_node_pr)])
			else if (P.mem v struc_expl_inst) then (tr, r,[])  
			else (r ,tr,[]) 

and get_eqns_free (l_node_pr,r_node_pr) evars expl_inst struc_expl_inst pos = 
	let pr (a,b,_)= "to left: "^(!print_perm_f a)^"\n to right: "^(!print_perm_f b)^"\n" in
	Gen.Debug.no_1 "get_eqns_free" (fun c-> "?") pr (fun _ -> get_eqns_free_a (r_node_pr,l_node_pr) evars expl_inst struc_expl_inst pos) r_node_pr
			
(*transformers  *)

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
	| Dom (v,d1,d2) -> e
    | Exists1 (qv,fr,p) ->
      let nfr = transform_perm f fr in
      mkExists1 qv nfr p 
      
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
      | Exists1 (qv,f,p) ->
         let nf,r = foldr_f new_arg f in
         (mkExists1 qv nf p, f_comb [r]) 
	  | Dom (v,d1,d2) -> (e, f_comb [])
      | PTrue _ -> (e,f_comb [])
      | PFalse _ -> (e, f_comb []) in
 foldr_f arg e

let find_rel_constraints (f:perm_formula) desired :perm_formula =  (*TODO -> check this*)
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
   

  
let rec list_of_a_f b f : ((P.spec_var list * ( frac_perm*frac_perm)list * (frac_perm*frac_perm*frac_perm) list* 'b) list option)= match f with
	| And (f1,f2,_) -> 
		(match (list_of_a_f b f1),(list_of_a_f b f2) with
		  | None,_ 
		  | _,None -> None
		  | Some r1, Some r2 ->     
        let ll = List.map (fun (v1,s1,f1,d1) -> List.map (fun (v2,s2,f2,d2) -> (v1@v2,s1@s2, f1@f2, d1@d2)) r1 ) r2 in
        Some (List.concat ll))
	| Or  (f1,f2,_) ->
    if b then failwith ("cperm list_of_a_f will not allow existentials over disjunctions")
    else
		(match (list_of_a_f b f1),(list_of_a_f b f2) with
		  | None, x 
		  | x, None -> x
		  | Some l1, Some l2 -> Some (l1@l2))
	| Join (f1,f2,f3,_) -> Some [([],[],[(f1,f2,f3)],[])]
	| Eq  (f1,f2,_) -> (match f1,f2 with | PConst c1, PConst c2 -> if Ts.eq c1 c2 then Some [([],[],[],[])] else None | _-> Some [([],[(f1,f2)],[],[])])
	| Dom (v,d1,d2) -> Some [([],[],[],[(v,d1,d2)])]
    | Exists1 (vl,f,_) ->
		(match list_of_a_f true f with 
		 | None -> None
		 | Some l -> Some (List.map (fun (c1,c2,c3,c4)-> (vl@c1,c2,c3,c4)) l))
	| PTrue _ -> Some [([],[],[],[])]
	| PFalse _ -> None

exception Unsat_exception
      
let is_sat_p_t (evs,lp,lt,ld) = 
  let tree_unsat lj =  
    (*dont : expand constants anything else is free*)
    let resteq1,lj = List.fold_left (fun (ar,al) (c1,c2,c3)-> 
        let r2,r3 = match c1,c2 with
           | PConst c, PVar v 
           | PVar v,PConst c -> [v],c
           | PVar v1,PVar v2 -> [v1;v2],bot_share 
           | _ -> raise Unsat_exception in
        match c3 with
           | PConst _ -> ((c3,r2,r3)::ar,al) 
           | PVar v-> (ar,(v,r2,r3)::al)) ([],[]) lj in
    let resteq2,lj = List.partition (fun (c,_,_)-> List.exists (fun (_,l,_)-> List.exists (P.eq_spec_var c) l) lj) lj in
    let resteq = resteq1@(List.map (fun (v,c1,c2)-> (PVar v, c1, c2))resteq2) in
    let groups = List.fold_left (fun a (c1,c2,c3)-> 
       let rec hlp r = match r with 
         | [] -> [[(c1,c2,c3)]] 
         | h::t-> (match h with 
                    | [] -> raise Unsat_exception 
                    | (v,_,_)::_-> if (P.eq_spec_var v c1) then ((c1,c2,c3)::h)::t else h::(hlp t))in
       hlp a) [] lj in  
    let groups = List.sort (fun l1 l2-> compare (List.length l1) (List.length l2)) groups in
    
    let subst2 grp (vl,c) :(P.spec_var list * Ts.stree) list= List.map (fun (c1,c2,c3) -> 
      let f c1 c2 = if Ts.can_join c1 c2 then Ts.join c1 c2 else raise Unsat_exception in 
      let rl,rc = List.fold_left (fun (rl,rc) v-> if P.eq_spec_var v c1 then (c2@rl,f rc c3) else (v::rl,rc))([],c) vl in
      if Gen.BList.check_dups_eq P.eq_spec_var rl then raise Unsat_exception else (rl,rc)) grp in
        
    let subst3 grp (c1,vl,c) = List.map (fun (c2,c3)-> 
        if List.exists (P.eq_spec_var c1) c2 then raise Unsat_exception else (c1,c2,c3)) (subst2 grp (vl,c)) in

    let rec helper rests (grps:(P.spec_var*P.spec_var list * Ts.stree) list list)= match grps with
     | [] -> [rests]
     | h::t-> 
      let rl = List.concat (List.map (fun (c1,c2,c3)-> List.map (fun (c2,c3)-> (c1,c2,c3)) (subst2 h (c2,c3))) rests) in
      let lt = List.map (fun g-> List.concat (List.map (subst3 h) g)) t in
      let r1 = helper rl lt in
	  let h = List.map (fun (c1,c2,c3)-> (PVar c1,c2,c3)) h in
      (h::r1) in
    (*in resteq keep only the unsubstitutible joins*)
    helper resteq groups in
    
  (*end tree sat*)
  let triv_unsat lj = 
    let f = eq_fperm in
    let f1 = isConstXFperm bot_share in
    List.iter (fun (c1,c2,c3) -> if (f c1 c3) || (f c2 c3) || (f c1 c2)|| f1 c1 || f1 c2 || f1 c3 then raise Unsat_exception else ()) lj in	 
	
  let ld_subst (f,t) ld = List.fold_left (fun a (v,d1,d2) -> 
	if (P.eq_spec_var f v) then match t with
			| PVar v-> (v,d1,d2)::a
			| PConst c-> if Ts.contains d2 c && Ts.contains c d1 then a else raise Unsat_exception
	else (v,d1,d2)::a) [] ld in
	
  let rec propag_eqs ss lj ld le = match le with
    | [] -> ss,lj,ld
    | (c1,c2)::t -> match (c1,c2) with
          | PConst s1, PConst s2 -> if (Ts.stree_eq s1 s2) then propag_eqs ss lj ld t else raise Unsat_exception
          | PConst s, PVar v  
          | PVar v, PConst s -> prop_subst ss (v,PConst s) lj ld t
          | PVar v1, PVar v2 ->  if (P.eq_spec_var v1 v2) then propag_eqs ss lj ld t else prop_subst ss (v1, PVar v2) lj ld t
    and prop_subst ss s lj ld t = 
		let f  = subst_perm_expr s in
		let t  = List.map (fun (c1,c2)-> (f c1, f c2)) t in
		let lj = List.map (fun (c1,c2,c3) -> (f c1 , f c2, f c3)) lj in    
		let ld = ld_subst s ld in
		propag_eqs (s::ss) lj ld t in
		
  let rec propag_trip ss lp ld ln = match ln with
		| [] -> ss,lp,ld
		| (c1,c2,c3)::lr -> 
			match (c1,c2,c3) with
				| PConst s1, PConst s2, PConst s3 -> if (Ts.can_join s1 s2) && (Ts.stree_eq s3 (Ts.join s1 s2)) then propag_trip ss lp ld lr else raise Unsat_exception 
				| PConst s1, PConst s2, PVar v  -> hlp (Ts.can_join s1 s2) (v, PConst (Ts.join s1 s2)) lp lr ld ss
				| PConst s1, PVar v, PConst s3
				| PVar v, PConst s1, PConst s3   -> hlp (Ts.contains s3 s1&& not (Ts.stree_eq s3 s1)) (v, PConst (Ts.subtract s3 s1)) lp lr ld ss
				| _ -> propag_trip ss ((c1,c2,c3)::lp) ld lr 
    and hlp tst s lp lr ld ss = 
		if tst then 
			let mf = List.map (fun (c1,c2,c3) -> (subst_perm_expr s c1 , subst_perm_expr s c2, subst_perm_expr s c3)) in
			let ld = ld_subst s ld in
			propag_trip (s::ss) [] ld ((mf lr)@(mf lp)) 
		else raise Unsat_exception in
		
  let lfv l = List.concat (List.map (fun (c1,c2,c3)-> (frac_fv c1)@(frac_fv c2)@(frac_fv c3))l) in
  (*let lfv2 l = List.concat (List.map (fun (c1,c2)-> c1::(frac_fv c2))l) in*)
  let int_consist vm vM = (Ts.contains vM vm) && (not (Ts.empty vM)) in
	
  let inters_restr dest src b = if Ts.contains dest src then (src,b) else ((Ts.intersect src dest),true) in
  let union_grow dest src b = if Ts.contains src dest then (src,b) else ((Ts.union src dest),true) in
  
  let dom_retrieve sol (c1,c2,c3) = 
     let hlp v = match v with | PConst s-> ((s,s),false) |PVar v -> (PMap.find v sol,true) in
	 (hlp c1),(hlp c2),(hlp c3) in
    
  let upd_sol sol c1 d1 c2 d2 c3 d3 = 
    let hlp sol c d = match c with | PConst _ -> sol | PVar v-> PMap.add v d sol in
    (hlp(hlp(hlp sol c1 d1) c2 d2) c3 d3) in
	
  let prop_up_one (sol,b) (c1,c2,c3) =  
    let ((d1m,d1M),b1),((d2m,d2M),b2),((d3m,d3M),b3) = dom_retrieve sol (c1,c2,c3) in
	if not (Ts.can_join d1m d2m) then raise Unsat_exception
	else 
		let apb = Ts.join d1m d2m in 
		let aub = Ts.union d1M d2M in 
		if not (Ts.contains d3M apb) || not (Ts.contains aub d3m) then raise Unsat_exception
		else 
			let d3m,b = union_grow apb d3m b in
			let d3M,b = inters_restr aub d3M b in
			let d1m,d2m,b = 				
				if (Ts.contains apb d3m) then (d1m,d2m,b)
				else if not b2 then (Ts.join d1m (Ts.intersect d3m (Ts.neg_tree apb)), d2m, true)
				else if not b1 then (d1m, Ts.join d2m (Ts.intersect d3m (Ts.neg_tree apb)), true)
				else (d1m,d2m,b) in
			let d1M,d2M,b =  
				if (Ts.contains d3M aub) then (d1M,d2M,b) 
				else if not b2 then (Ts.intersect d1M (Ts.neg_tree d3M), d2M, true)
        else if not b1 then (d1M, Ts.intersect d2M (Ts.neg_tree d3M), true)
        else (d1M,d2M,b) in
			if (int_consist d1m d1M)&&(int_consist d2m d2M)&&(int_consist d3m d3M) then 
          (upd_sol sol c1 (d1m,d1M) c2 (d2m,d2M) c3 (d3m,d3M) , b)
			else raise Unsat_exception in
		  
  let rec prop_upstream sol lc =
	let r1,b = List.fold_left prop_up_one (sol,false) lc in
	if b then prop_upstream r1 lc else r1 in
		
  (*let rec prop_downstream sol lc = (sol,lc, false) in*)
		
  let rec propag_cons sol lc = 	
	let sol = prop_upstream sol lc in
	(*let (sol,lc,b) = prop_downstream sol lc in
	if b then propag_cons sol lc else*) [sol] in
		
  let add_subst l a = List.fold_left (fun a (v,r) -> match r with 
		| PConst s -> PMap.add v (s,s) a
		| PVar v1 -> try PMap.add v (PMap.find v1 a) a with Not_found -> a) a l in
  try 
	let eq_sp, lj,ld = propag_eqs [] lt ld lp in
	let eq_st, lj,ld = propag_trip [] [] ld lj in
	let eq_s = eq_st@eq_sp in (*maintain this order*)
	triv_unsat lj;
	let eqs = tree_unsat lj in
	let sol = List.fold_left (fun a v-> PMap.add v (bot_share,top_share) a) (PMap.create P.cmp_spec_var) (Gen.BList.remove_dups_eq P.eq_spec_var (lfv lj)) in 
	let sol = List.fold_left (fun a (v,d1,d2)-> if (int_consist d1 d2) then PMap.add v (d1,d2) a else raise Unsat_exception) sol ld in
	let sol = propag_cons sol lj in
	(List.map (add_subst eq_s) sol , eq_s, eqs, evs)
  with 
   | Unsat_exception -> ([],[],[],[])
   | Not_found -> (print_string "error in solver \n"; ([],[],[],[]))
     
let is_sat_p_t_w l = List.length (let r,_,_,_ = is_sat_p_t l in r) > 0
   
let is_sat_p_t_w2 f = 
	match list_of_a_f false f with
		| None -> [([],[],[],[])]
		| Some l -> List.map is_sat_p_t l
	
let is_sat_a f = match list_of_a_f false f with 
    | None -> false (*f formula is false*)
    | Some l -> List.exists is_sat_p_t_w l 
      

let gen_table lv =
   let lv = Gen.BList.remove_dups_eq P.eq_spec_var lv  in
   let nv = List.length lv in
   let la = 
    if (nv<24) then 
      let l = 
        ["\\alpha";"\\beta";"\\gamma";"\\delta";"\\epsilon";"\\zeta";"\\eta";"\\theta";"\\iota";"\\kappa";
         "\\lambda";"\\mu";"\\nu";"\\xi";"o";"\\pi";"\\rho";"\\sigma";"\\tau";"\\upsilon";
         "\\phi";"\\chi";"\\psi";"\\omega"] in
      let rec helper i l = if i=0 then [] else (List.hd l)::(helper (i-1) (List.tl l)) in helper nv l
    else let rec helper i = if i=0 then [] else ("v\\_{"^(string_of_int i)^"} ")::(helper (i-1)) in (helper nv) in
   let la = List.map (fun s-> P.SpecVar (Named perm,s,Unprimed)) la in
   List.combine lv la
      
let hline = "---------------------------- \n \n " 

let solve_once2 f = match is_sat_p_t_w2 f with 
		| (hl::[],_,_,_)::[]-> Some hl
		| _ -> None
      
let solve_once f = 
  if not !Globals.enable_frac_perm then None
  else Some (match is_sat_p_t_w2 f with 
		| (hl::[],_,_,_)::[]-> hl
		| _ -> (PMap.create P.cmp_spec_var))

      
let solve_once f =
  if !Globals.enable_frac_print then 
    if not(isConstTrue f) then
      (print_counter:=!print_counter+1;
      let f = subst (gen_table (fv f)) f in
      output_string !perm_log_file ("\n \n "^hline^
      (string_of_int !print_counter)^") solve "^" \n \n \n"^(!latex_of_formula f)^"\n \n \n"))
    else ()
  else ();
  Gen.Debug.no_1 "solve_once" !print_perm_f (fun c-> match c with | None -> "None" | _ -> "Some")
   solve_once f
      
let stub_sol :(P.spec_var,(Ts.stree*Ts.stree)) PMap.t option = 
  if not !Globals.enable_frac_perm then None
  else Some (PMap.create P.cmp_spec_var)

(*imply : f1|-f2*)

let trip_pr (c1,c2,c3) = (!print_frac_f c1) ^ "=" ^ (String.concat "+" (List.map !print_sv c2))^"+" ^(!print_share c3)	
let l_pr f l = "["^(String.concat "," (List.map f l))^"]"
let svl_pr l = l_pr !print_sv l 
let eq_pr (c1,c2) = (!print_sv c1)^" = "^(!print_frac_f c2)
let sol_pr s = PMap.foldi (fun v (d1,d2) a-> (!print_sv v)^"=["^(!print_share d1)^","^(!print_share d2)^"] ; " ^a) s ""

let imply_a glb_evs f1 f2 = 
  let in_2 = fun a (c1,c2)-> if (isConstFperm c2) then true else false in (*to improve completeness, syntactic inclusion check of equation c in a*)
  let in_3 = fun a c-> false in
  let dom_incomp ll rl evs = 
	  let evs = evs @ glb_evs in 
      PMap.foldi (fun rv (rdm,rdM) a -> 
          if a then a 
          else if Gen.BList.mem_eq P.eq_spec_var rv evs then a 
          else try 
			let rlm,rlM = PMap.find rv ll in
            if (Ts.contains rlm rdm)&& (Ts.contains rdM rlM) then a else true 
         with Not_found -> true) rl false in
		 
  let one_imply_one_a (f1s, f1e, f1t) (f2s, f2e, f2t, f2vs) = 
	if f2s=[] then false
	else if (dom_incomp (List.hd f1s) (List.hd f2s) f2vs) then false
	else (List.for_all (in_2 (f1e,f1t)) f2e)&&(List.for_all (in_3 (f1e,f1t)) (List.concat f2t))  in
	
  let one_imply_one a (s,e,t,vs) =
	let pr (s,e,t) = "( sols "^(l_pr sol_pr s)^"\n eqs: "^(l_pr eq_pr e)^"\n trip: "^(l_pr (l_pr trip_pr) t) in
	Gen.Debug.no_2 "1_impl_1" pr pr string_of_bool  (fun _ _ -> one_imply_one_a a (s,e,t,vs)) a (s,e,t) in
  
  let one_imply conseq (f1s, f1e, f1t, _) = 
    if f1s=[] then true
	else 
		let conseq = PMap.foldi (fun v (d1,d2) c-> if (Ts.stree_eq d1 d2)then apply_one_exp  (v,(PConst d1)) c else c) (List.hd f1s) conseq in
		List.exists (one_imply_one (f1s, f1e, f1t)) (is_sat_p_t_w2 conseq) in 
      
  List.for_all (one_imply f2) (is_sat_p_t_w2 f1) 
  
(***bench wrappers *****)
let loop_bound = 99

let prof_harness1 str f1 f2 arg = 
  if !Globals.perm_prof then
		let rec f1_loop cnt r arg  = 
			if cnt=loop_bound then f1 arg 
			else 
				let r = f1 arg  in
				f1_loop (cnt+1) r arg  in
		let rec f2_loop cnt r arg  = 
			if cnt=loop_bound then f2 arg 
			else 
				let r = f2 arg  in
				f2_loop (cnt+1) r arg  in
		let r1 = Gen.Profiling.do_1 ("old_"^str) (f1_loop 0 false) arg in
		let r2 = Gen.Profiling.do_1 ("new_"^str) (f2_loop 0 false) arg in
		let _ = if r1==r2 then () else 
		(print_string ("sat difs \n ante: "^(!print_perm_f arg)^"\n r old: "^(string_of_bool r1)^"\n r new: "^(string_of_bool r2)^"\n");
		Gen.Profiling.inc_counter (str^"_err")) in
		r1
  else f1 arg		
	
let prof_harness2 str f1 f2 arg1 arg2 = 
	if !Globals.perm_prof then
		let rec f1_loop cnt r arg1 arg2 = 
			if cnt=loop_bound then f1 arg1 arg2
			else 
				let r = f1 arg1 arg2 in
				f1_loop (cnt+1) r arg1 arg2 in
				
		let rec f2_loop cnt r arg1 arg2 = 
			if cnt=loop_bound then f2 arg1 arg2
			else 
				let r = f2 arg1 arg2 in
				f2_loop (cnt+1) r arg1 arg2 in
	
		let r1 = Gen.Profiling.do_2 ("old_"^str) (f1_loop 0 false) arg1 arg2 in
		let r2 = Gen.Profiling.do_2 ("new_"^str) (f2_loop 0 false) arg1 arg2 in
		let _ = if r1==r2 then () else 
			(print_string ("imply difs \n ante: "^(!print_perm_f arg1)^" \n conseq :"^(!print_perm_f arg2)^"\n r old: "^(string_of_bool r1)^"\n r new: "^(string_of_bool r2)^"\n");
			Gen.Profiling.inc_counter (str^"_err")) in
		r1
	else f1 arg1 arg2 
    
module Share_prover_w = Share_prover_w
	
let trans_one_2_syst (exl,fef,ffef,doms) =
	let lc,le = List.fold_left (fun (a1,a2) (v1,v2)-> match v1,v2 with 
		| PConst c1, PConst c2 -> a1,a2
		| PConst c, PVar v 
		| PVar v, PConst c -> (Share_prover_w.tr_var v,c)::a1,a2
		| PVar v1, PVar v2 -> a1,(Share_prover_w.tr_var v1,Share_prover_w.tr_var v2)::a2) ([],[]) fef in
	let tr_one v= match v with | PConst c-> Share_prover_w.mkCperm c | PVar v-> Share_prover_w.mkVperm v in
	let eqs = List.map (fun (c1,c2,c3)-> tr_one c1, tr_one c2, tr_one c3) ffef in
	let domex, domeqs = List.fold_left (fun (a1,a2) (v,c1,c2)-> 
		let v = Share_prover_w.mkVperm v in		
		let a1,a2 = 
			if c1=Ts.bot then a1,a2 
			else 
				let freshv = Share_prover.Sv.fresh_var () in
				freshv::a1,(Share_prover_w.mkCperm c1, Share_prover_w.Solver.Vperm freshv,v)::a2 in			
		if c2=Ts.top then a1,a2 
		else 
			let freshv = Share_prover.Sv.fresh_var () in
			freshv::a1, (Share_prover_w.Solver.Vperm freshv, v, Share_prover_w.mkCperm c2)::a2 ) ([],[]) doms in
	let tot_exv = (List.map Share_prover_w.tr_var exl)@domex in
	let tot_eqs = eqs@domeqs in
	let lve = let l1,l2 = List.split le in l1@l2 in
	let clv = tot_exv@ (fst (List.split lc))@ lve @ (List.fold_left (fun a c-> (Share_prover_w.Solver.eq_fv c)@a) [] tot_eqs) in
				{
				Share_prover_w.Solver.eqs_ex = tot_exv ;
				Share_prover_w.Solver.eqs_nzv = Gen.BList.remove_dups_eq Share_prover_w.sv_eq clv;
				Share_prover_w.Solver.eqs_vc = lc;
				Share_prover_w.Solver.eqs_ve = le;
				Share_prover_w.Solver.eqs_eql = tot_eqs;}
	
	
let new_impl_prov f1 f2 = 
	match list_of_a_f false f1 with
		| None -> true
		| Some l_ante -> match list_of_a_f false f2 with
			| None -> not (List.exists (fun c-> Share_prover_w.Solver.is_sat (trans_one_2_syst c)) l_ante)
			| Some l_conseq -> 
				let l_conseq = List.map trans_one_2_syst l_conseq in
				let l_ante = List.map trans_one_2_syst l_ante in
				List.for_all (fun c-> List.exists (fun a-> 
					let new_ex = List.filter (fun c-> not (List.exists (Share_prover.Sv.eq c) a.Share_prover_w.Solver.eqs_nzv)) c.Share_prover_w.Solver.eqs_nzv in
					Share_prover_w.Solver.imply a {c with Share_prover_w.Solver.eqs_ex = c.Share_prover_w.Solver.eqs_ex @ new_ex}) l_ante ) l_conseq
	
let new_sat_prov f = 
	match list_of_a_f false f with
		| None -> false
		| Some l -> List.exists (fun c-> Share_prover_w.Solver.is_sat (trans_one_2_syst c)) l
	
let imply_w evs f1 f2 = prof_harness2 "imply" (imply_a evs) new_impl_prov f1 f2 

let is_sat_w f = prof_harness1 "sat" is_sat_a new_sat_prov f

let imply evs f1 f2 = 
  let pr = Gen.pr_list !print_sv in  
  if !Globals.enable_frac_print then 
    if not(isConstTrue f2) then
      (print_counter:=!print_counter+1;
      let tbl = gen_table ((fv f1)@(fv f2)@evs) in
      let f1 = subst tbl f1 in
      let f2 = subst tbl f2 in
      let evs = List.map (P.subs_one tbl) evs in
      output_string !perm_log_file ("\n \n "^hline^
      (string_of_int !print_counter)^") imply "^(Gen.pr_lst latex_print_sv evs)^"\n \n "^(!latex_of_formula f1)^" \n \n $\\qquad \\qquad \\vdash $ "^
      (!latex_of_formula f2)^" \n \n \n"))
    else ()
   else ();
  Gen.Debug.no_3 "perm imply" pr !print_perm_f !print_perm_f string_of_bool imply_w evs f1 f2 
    
let is_sat f = 
  if !Globals.enable_frac_print then 
    if not(isConstTrue f) then
      (print_counter:=!print_counter+1;
      let f = subst (gen_table (fv f)) f in
      output_string !perm_log_file ("\n \n "^hline^
      (string_of_int !print_counter)^") is\\_sat "^" \n \n \n"^(!latex_of_formula f)^"\n \n \n"))
    else ()
  else ();
  Gen.Debug.no_1 "perm_is_sat" !print_perm_f string_of_bool is_sat_w f
	
	
(*elim exists*)
(*solves f, returns vars without a unique value, and pairs of vars and values*)
 
 let get_perm_sol pr_sol pv = match pr_sol with
  | None -> Ts.top
  | Some l -> match pv with 
    | None -> Ts.top
    | Some pv -> try fst (PMap.find pv l) with Not_found-> Ts.bot 
 
let var_2_prop_var pr_sol (v:P.spec_var) pv = (v,(P.type_of_spec_var v, get_perm_sol pr_sol pv))
    
let var_2_prop_var pr_sol v pv=
  Gen.Debug.no_2 "var_2_prop_var" !print_sv (Gen.pr_option !print_sv) (fun (_,(_,f))-> Ts.string_of_tree_share f) (var_2_prop_var pr_sol) v pv

let var_2_prop_var_list pr_sol vl pv =
  let perm  = get_perm_sol pr_sol pv in
  List.map (fun v-> (v,(P.type_of_spec_var v, perm))) vl
  
let var_2_prop_var_bot (v:P.spec_var) = (v,(P.type_of_spec_var v, Ts.bot))
let var_2_prop_var_top (v:P.spec_var) = (v,(P.type_of_spec_var v, Ts.top))
 
let solve_for_l_w w f = match w with
  | [] -> (w,[])
  | _ -> match is_sat_p_t_w2 f with 
		| (hl::[],_,_,_)::[]->
     (* let aset_l = aset_list w f in*)
      List.fold_left (fun (a1,a2) v -> 
        try 
          let d1,d2 = PMap.find v hl in 
          if (Ts.stree_eq d1 d2) then (a1, (v,PConst d1)::a2)
          else (*match ex_subst aset_l v with| Some v1 -> (a1, (v,v1)::a2)| _ ->*)
            (v::a1,a2) 
         with Not_found -> (v::a1,a2) 
        ) ([],[]) w 
		| _ -> (w,[])
 
let solve_for_l w f = 
	 if !Globals.enable_frac_print then 
    if not(isConstTrue f) then
      (print_counter := !print_counter +1 ;
        let tbl = gen_table ((fv f)@w) in
        let f = subst tbl f in
        let w = List.map (P.subs_one tbl) w in
      output_string !perm_log_file ("\n \n "^hline^
      (string_of_int !print_counter)^") solve "^(Gen.pr_lst latex_print_sv w)^"\n \n "^(!latex_of_formula f)^"\n \n \n"))
    else ()
   else ();
   solve_for_l_w w f
 
 
(*try and eliminate vars from w, what can not be done return*)
let elim_exists_perm w f1 = 
  let l1, l2 = solve_for_l w f1 in
  (l1,(List.fold_left (fun a c-> apply_one_exp c a)f1 l2)) 
  
(*try and eliminate vars from w, what can not be done, push as existentials-eliminate them*)
let elim_pr_exists1 w f1 = 
  let l1, l2 = solve_for_l w f1 in
  (mkExists1 l1 (List.fold_left (fun a c-> apply_one_exp c a)f1 l2) no_pos) 
    
let rec elim_exists_exp_perm1 f = match f with 
  | And (f1,f2,l) -> mkAnd (elim_exists_exp_perm1 f1) (elim_exists_exp_perm1 f2) l
  | Or  (f1,f2,l) -> mkOr (elim_exists_exp_perm1 f1) (elim_exists_exp_perm1 f2) l
  | Exists1 (vl,f,_) -> elim_pr_exists1 vl f      
  | Join _
  | Eq _  
  | Dom _
  | PTrue _
  | PFalse _ -> f

   
   (*end of todos*)
   
let split_universal1 (f0 : perm_formula) (evars : P.spec_var list) (expl_inst_vars : P.spec_var list)(impl_inst_vars : P.spec_var list) (vvars : P.spec_var list) (pos : loc) 
      : perm_formula * perm_formula * (P.spec_var list) =
  let rec split f = match f with
		| And (f1, f2, _) ->
		  let app1, cpp1 = split f1 in
		  let app2, cpp2 = split f2 in
		  (mkAnd app1 app2 pos, mkAnd cpp1 cpp2 pos)
		| _ ->
		  let fvars = fv f in
		  if P.disjoint fvars vvars then (mkTrue pos, mkTrue pos)
		  else if not (P.disjoint (evars@expl_inst_vars@impl_inst_vars) fvars) then (mkTrue pos, f)
		  else (f, mkTrue pos) in
  let rec drop_cons (f : perm_formula) (vvars: P.spec_var list) : perm_formula = match f with
	  | Eq _
	  | Join _
	  | Dom _
	  | Exists1 _ ->
			if P.disjoint (fv f) vvars then mkTrue no_pos else f
	  | And(f1, f2, l) -> mkAnd (drop_cons f1 vvars) (drop_cons f2 vvars) l
	  | Or(f1, f2, l) -> mkOr (drop_cons f1 vvars) (drop_cons f2 vvars)  l
	  | _ -> f in
   let f=f0 in
  (*let f = normalize_to_CNF f0 pos in*)
  let to_ante, to_conseq = split f0 in
  let to_ante = find_rel_constraints to_ante vvars in
  let conseq_fv = fv to_conseq in
  let instantiate = List.filter (fun v -> List.mem v (evars@expl_inst_vars@impl_inst_vars)) conseq_fv in
  let wrapped_to_conseq = mkExists1 instantiate to_conseq pos in
  let to_ante = if fv wrapped_to_conseq <> [] then mkAnd to_ante wrapped_to_conseq no_pos else to_ante in
  let fvars = fv f in
  if !Globals.move_exist_to_LHS & (not(Gen.is_empty (Gen.BList.difference_eq P.eq_spec_var fvars evars)) & not(Gen.is_empty evars))	then
    let new_f = drop_cons f vvars in
	let new_f = mkAnd to_ante (mkExists1 evars new_f pos) pos in
    (new_f,to_conseq, evars)
  else (elim_exists_exp_perm1 to_ante, to_conseq, evars)
   
    
let comp_perm_split_a lsp v_rest v_consumed lhs_p_f rhs_p_f l_perm r_perm = 
  let both_fs = mkAnd lhs_p_f rhs_p_f no_pos in
  try 
    let (rm,rM),rp,rk = match r_perm with 
      | [] -> (top_share,top_share), PConst top_share,true
      | v::_->  match solve_once2 both_fs with
        | None -> raise Not_found
        | Some l-> try
          (PMap.find v l),PVar v,true
          with Not_found -> (bot_share,top_share), PVar v,false in
    let (lm,lM),lp,lk = match l_perm with 
      | [] -> (top_share,top_share),PConst top_share,true
      | v::_-> match solve_once2 lhs_p_f with
        | None -> raise Not_found
        | Some l -> try
          (PMap.find v l),PVar v, true
          with Not_found -> (bot_share, top_share),PVar v,false in
    (*let _ = print_string ("lm:"^(!print_share lm)^ " lM: "^(!print_share lM)^" lk "^(string_of_bool lk)^"\n") in
    let _ = print_string ("rm:"^(!print_share rm)^ " rM: "^(!print_share rM)^" rk "^(string_of_bool rk)^"\n") in
    *)if lsp then 
      if (Ts.contains lm rM || (not rk)) then 
        if (Ts.stree_eq lM rm) then (*perfect match cannot split must consume*) (lhs_p_f,rhs_p_f,0)
        else (*split on left*)
          let default = mkAnd lhs_p_f (mkJoin (mkVPerm v_rest) (mkVPerm v_consumed) lp no_pos) no_pos in 
          let addition = if Ts.stree_eq rm rM then 
                            mkEq (mkVPerm v_consumed) (PConst rm) no_pos 
                         else (mkDom v_consumed rm rM) in
          (mkAnd default addition no_pos,rhs_p_f,1) 
      else (lhs_p_f,rhs_p_f,0) 
    else (*split on right*)
    if not lsp & (Ts.contains rm lM || (lk & not rk)) then 
      let default = mkJoin (mkVPerm v_rest) (mkVPerm v_consumed) rp no_pos in 
      (lhs_p_f,default, -1)
    else (lhs_p_f,rhs_p_f,0)
  with Not_found -> (lhs_p_f,rhs_p_f,0)
  
	  
let comp_perm_split lsp v_rest v_consumed lhs_p_f rhs_p_f l_perm r_perm =
	let pr1 = Gen.Basic.pr_list !print_sv in
	let pr2 = Gen.Basic.pr_triple !print_perm_f !print_perm_f string_of_int in
Gen.Debug.no_6 "comp_perm_split" 
	!print_sv !print_sv !print_perm_f !print_perm_f pr1 pr1 pr2
	(fun _ _ _ _ _ _-> comp_perm_split_a lsp v_rest v_consumed lhs_p_f rhs_p_f l_perm r_perm) v_rest v_consumed lhs_p_f rhs_p_f l_perm r_perm

   
   
let solve_on_a f var = match var with 
	| None -> PTrue no_pos
	| Some v -> match is_sat_p_t_w2 f with 
		| (hl::[],_,_,_)::[]->
			(try 
				let d1,d2 = PMap.find v hl in
				if (Ts.stree_eq d1 d2) then mkEq (PVar v) (PConst d1) no_pos else mkDom v d1 d2 
			 with Not_found -> PTrue no_pos)
		| _ -> PTrue no_pos
    
 let solve_on f var = 
	 if !Globals.enable_frac_print then 
    if not (isConstTrue f) then
      (print_counter:= !print_counter +1;
       let tbl = gen_table ((match var with | None -> [] | Some v-> [v])@(fv f)) in
       let f = subst tbl f in
       let var = match var with | None -> None | Some v -> Some (P.subs_one tbl v) in
      output_string !perm_log_file ("\n \n "^hline^
      (string_of_int !print_counter)^") solve "^(Gen.pr_option latex_print_sv var)^" \n \n  \n"^(!latex_of_formula f)^" \n \n"))
    else ()
   else ();
   solve_on_a f var
   
   
let  start_printing _ = 
    if !Globals.enable_frac_print then 
      (perm_log_file := open_out perm_log_name;
      output_string !perm_log_file 
      "
        \\documentclass{article}
        %\\usepackage{latexsym,amsmath,amssymb,mathtools}
        \\usepackage[nocenter]{qtree}
        \\renewcommand{\\qtreepadding}{2pt}
        \\renewcommand{\\qtreeunaryht}{0.5em}
        \\newcommand{\\qleafhook}{}
        \\begin{document}
        ")
    else ()
    
let stop_printing _ = 
  print_string "\n STOPPPPPING\n";
    if !Globals.enable_frac_print then 
     (output_string !perm_log_file " \\end{document}"; flush !perm_log_file; close_out !perm_log_file)
    else ()
   

let latex_of_frac f = match f with 
  | PConst s -> Ts.latex_of_share s
	| PVar v -> latex_print_sv v
  
let printer_stop = ref 0
  
let rec latex_of_formula_w f = match f with
  | And (f1,f2,_) -> (latex_of_formula_w f1)^" ~~\\wedge~~ "^(latex_of_formula_w f2)
  | Or  (f1,f2,_) -> " ( "^(latex_of_formula_w f1)^" ) ~~\\vee~~ ( "^(latex_of_formula_w f2)^" ) "
  | Join (f1,f2,f3,_) -> 
       (printer_stop := !printer_stop +1;
        (if ( !printer_stop mod 5 ==0 ) then "\\\\ ~~~~~" else "")^
      (latex_of_frac f1)^" \\oplus "^(latex_of_frac f2) ^" = "^(latex_of_frac f3))
  | Eq (f1,f2,_) -> 
    (printer_stop := !printer_stop +1;
      (if ( !printer_stop mod 5 ==0 ) then "\\\\ ~~~~~" else "")^
    (latex_of_frac f1) ^" = "^ (latex_of_frac f2))
  | Exists1 (l,f,_) -> "(\\exists ~"^(String.concat " ~" (List.map latex_print_sv l))^" . ~"^(latex_of_formula_w f)^" ) "
  | Dom (v,s1,s2) ->  (latex_print_sv v)^" ~\\in ~"^(Ts.latex_of_share s1)^" , "^(Ts.latex_of_share s2)
  | PTrue _ -> " True "
  | PFalse _ -> " False ";;
  
latex_of_formula := fun f->
   printer_stop:=0;
 "$ \\noindent "^(latex_of_formula_w f)^"$"
   
   (*start of useless code*)
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   (*
let match_imply l_v r_v l_f r_f l_node e_vars :(bool * P.spec_var * P.spec_var * 'a * 'b * 'c) option = 
    Some (false,l_v, r_v, l_f, r_f, l_node) (*TODO*) 
   	
	(*if (Ts.can_join v1m v2m)&&(Ts.contains v3M (Ts.join v2m v1m) then
				let fmc = Ts.subtract v3M v2m in
				let v1M,b = inters_restr fmc v1M b in
				let v1M,b = inters_restr v3M v1M b in 
				let v3M,b = inters_restr (Ts.union v2M v1M) v3M b in
				let v3m,b = union_grow v2m v3m b in
				let v3m,b = union_grow v1m v3m b in
				let v1m,b = union_grow fmc v1m in
				if (int_consist v1M v1m)&&(int_consist v3M v3m) then [((PMap.add v2 (v3m,v3M) (PMap.add v1 (v1m,v1M) sol)),b)]
				else raise Unsat_exception	
			else  raise Unsat_exception
			
			if (Ts.can_join v1m v2m)&& (Ts.contains v3M (Ts.join v1m v2m)) && (Ts.contains (Ts.union v1M v2M) v3m) then
			   let v1M,b = inters_restr v3M v1M b in
			   let v1M,b = inters_restr (Ts.substract v3M v2m) b in
			   let v2M,b = inters_restr v3M v2M b in
			   let v2M,b = inters_restr (Ts.substract v3M v1m) b in
			   let v1m,b = union_grow (Ts.subtract v3m v2M) v1m b in
			   let v2m,b = union_grow (Ts.subtract v3m v1M) v2m b in
			   if (int_consist v1M v1m)&&(int_consist v2M v2m) then 
					[((PMap.add v2 (v2m,v2M) (PMap.add v1 (v1m,v1M) sol)),b)]
			   else raise Unsat_exception
		    else raise Unsat_exception
			
			*)
  
  --------------------------
  (*let r = List.fold_left (fun lsol c -> List.concat (List.map (fun s -> prop_one s c) lsol)) [(sol,false)] lc in
	List.concat (List.map (fun (c1,c2)-> if c2 then propag_cons c1 lc else [c1]) r) in*)
  
let solve_set l_vars (lp,lt) : (P.spec_var* share) list = 

	let rpl v s c = match c with | PConst _ -> c | PVar v1 -> if P.eq_spec_var v1 v then PConst s else c in
	
	let propag_sol_eq ls le = List.fold_left (fun le (v,s)-> List.map (fun (c1,c2)-> (rpl v s c1 ,rpl v s c2)) le) le ls in

	let propag_sol_join ls lj = List.fold_left (fun lj (v,s)-> List.map (fun (c1,c2,c3)-> (rpl v s c1 ,rpl v s c2, rpl v s c3)) lj) lj ls in
  
  let filter_eq l = 
		List.fold_left (fun (ls,le) (c1,c2)-> match c1,c2 with
			| PConst s1, PConst s2 -> if Ts.stree_eq s1 s2 then (ls,le) else raise Unsat_exception
			| PVar v, PConst s
			| PConst s, PVar v -> ((v,s)::ls, le)
			| PVar v1, PVar v2 -> if P.eq_spec_var v1 v2 then (ls,le) else (ls, (c1,c2)::le)) ([],[]) l in

  let rec filter_eq_prop l = 
    let ls, le = filter_eq l in
    match ls with 
     | [] -> (ls,le)
     | _ ->
        let le = propag_sol_eq ls le in
        let r1,r2 = filter_eq_prop le in
        (ls@r1,r2) in
    
      
  let filter_join l = List.fold_left ( fun (ls,lj) (c1,c2,c3) -> match c1,c2,c3 with
		| PConst s1, PConst s2, PConst s3-> if (Ts.can_join s1 s2) && (Ts.stree_eq s3 (Ts.join s1 s2)) then (ls,lj) else raise Unsat_exception
		| PConst s1, PConst s2, PVar v1  -> if (Ts.can_join s1 s2) then ((v1,Ts.join s1 s2)::ls,lj) else raise Unsat_exception
		| PConst s1, PVar v, PConst s3
		| PVar v, PConst s1, PConst s3   -> if Ts.contains s3 s1 then ((v,Ts.subtract s3 s1)::ls,lj) else raise Unsat_exception
		| _ -> (ls,(c1,c2,c3)::lj)) ([],[]) l in

(*sat*)
    
(*let does_match p = match p with | Some _ -> true | None -> false*)
  
(*let needs_split p = match p with | Some (true,_,_,_,_,_)-> true | _ -> false*)  
   
  	
  let search_eqs l = 
		let f1 (c1,c2,c3) (d1,d2,d3) = match (eq_fperm c1 d1), (eq_fperm c2 d2), (eq_fperm c3 d3) with
			| true,true,true -> ([],[])
			| true,true,false -> ([(c3,d3)],[])
			| true,false,true -> ([(c2,d2)],[])
			| false,true,true -> ([(c1,d1)],[])
			| _ -> ([],[(d1,d2,d3)]) in
		let rec hlp l = match l with
		  | [] -> ([],[])
		  | h::t-> 
			let ne,nt = List.split (List.map (f1 h) t) in
			let ne = List.concat ne in
			let t = List.concat nt in
			let r1,r2 = hlp t in
			(ne@r1,h::r2) in
		hlp l in
	
  let add_to_sol sol ls = List.fold_left (fun a (v,s)-> 
      let prev = PMap.find v a in
      if Ts.stree_eq prev bot_share || Ts.stree_eq prev s then PMap.add v s a else raise Unsat_exception) sol ls in 
  
  let rec compute_substs le : (P.spec_var * P.spec_var)list = match le with
      | [] -> []
      | (c1,c2)::t -> if (P.eq_spec_var c1 c2) then compute_substs t 
        else 
          let t = List.map (fun (d1,d2)-> ((if (P.eq_spec_var d1 c1) then c2 else d1), if (P.eq_spec_var d2 c1) then c2 else d2)) t in
          (c1,c2)::(compute_substs t) in
  
  let rec slv_with_eqs sol lp lt = 
    check_sat lt;
    let (ls,le) = filter_eq_prop lp in
    let le = List.map (fun (c1,c2)-> match (c1,c2) with | PVar v1,PVar v2 -> (v1,v2) | _ -> raise Unsat_exception) le in
    let sol = add_to_sol sol ls in
    let lj = propag_sol_join ls lt in
    let l_sub = compute_substs le in
    let lj = List.fold_left (fun a (v1,v2)-> List.map (fun (d1,d2,d3) -> 
                                                         let rlv f = match f with
                                                          | PConst _ -> f
                                                          | PVar v -> PVar (if (P.eq_spec_var v v1) then v2 else v)   in
                                                         (rlv d1, rlv d2, rlv d3)) a) lj l_sub in
    let sol = slv sol lj in
    List.fold_left (fun sol (v1,v2)-> 
      let r1, r2 = PMap.find v1 sol, PMap.find v2 sol in
      if (Ts.stree_eq r1 r2) then sol
      else 
        match Ts.stree_eq r1 bot_share , Ts.stree_eq r2 bot_share with
          | true, false -> PMap.add v1 r2 sol
          | false, true -> PMap.add v2 r1 sol
          | _ -> raise Unsat_exception ) sol l_sub
   
  and slv sol lj =
     check_sat lj; 
	   let (ls,lj) = filter_join lj in 
     let (le,lj) = search_eqs lj in   (*a+b=c;a+b=d -> c=d*)
	   if ls=[] && le=[] then if is_sat_p_t [] lj then sol else raise Unsat_exception
	   else
			let le = propag_sol_eq ls le in
			let lj = propag_sol_join ls lj in
			let sol = add_to_sol sol ls in
			slv_with_eqs sol le lj 
   in    
   try
      let r = if (lp=[] && lt=[]) then l_vars
      else slv_with_eqs l_vars lp lt in
      PMap.foldi (fun v s a-> (v,s)::a) r []
   with Unsat_exception -> [] (*no solution*)
   
   
let lafv l = 
  let hlp (l1,l2)= 
     List.concat ((List.map (fun (c1,c2,c3)-> (frac_fv c1) @ (frac_fv c2) @ frac_fv c3) l2)@
     (List.map (fun (c1,c2) -> (frac_fv c1) @ (frac_fv c2)) l1)) in
  Gen.remove_dups (List.concat (List.map hlp l))
   
let solve_system f : ((P.spec_var * share option) list list)= 
   let evl,la = list_of_a_f f in
   match la with 
	| None -> [] (*f formula is false*)
	| Some l ->  		
    let lfv = lafv l in
    let sol = List.fold_left (fun a c-> PMap.add c bot_share a) (PMap.create P.cmp_spec_var) lfv in
		let r = List.map (solve_set sol) l in
	    let r = List.filter (fun c-> match c with | [] -> false | _ ->true) r in
		if List.length r > 0 then 
			List.map (List.filter (fun (c1,_)-> Gen.BList.mem_eq (P.eq_spec_var c1) evl)) r
		else [] (*no solutions*)
	
	
  let sort_constraints l = 
	let depends (c1,c2,c3)(d1,d2,d3) = if (isConstFperm d3) then false else ( eq_fperm c1 d3 || eq_fperm c2 d3) in
	let rec splitter (lr1,lr2) l = match l with
		| [] -> (lr1,lr2)
		| h::t -> 
			if (List.exists (depends h) lr2)||(List.exists (depends h) t) then splitter (lr1,h::lr2) t
			else splitter (h::lr1,lr2) t in		
	let rec hlp l = 
		if l=[] then []
		else 
			let ind,dep = splitter l in
			if ind=[] then raise Unsat_exception
			else (List.rev ind)@(hlp dep) in			
	hlp l in
	
   
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
  | _ -> ((mkTrue pos), f1, f2)*)
  
  
(*let heap_partial_imply l_h l_pr perm_imply mkStarHh h_apply_one pos = match perm_imply with
  | Some (b,l_v,r_v,l_f,r_f,l_node)->
    if b then 
      let s1 = fresh_perm_var () in
      let s2 = fresh_perm_var () in
      let l_node' = h_apply_one (l_v,s1) l_node in
      let l_h' = mkStarHh l_node' l_h pos in
      let pr_eq = mkJoin (mkVPerm l_v) (mkVPerm s1) (mkVPerm s2) pos in
      let l_pr'= mkAnd l_pr pr_eq pos in
      (l_h',l_pr',[s1;s2],(r_v,s2))
    else (l_h,l_pr,[],(r_v,l_v))
  | None -> 
    let f = fresh_perm_var () in
    let t = fresh_perm_var () in
    (l_h,l_pr,[],(f,t))*)
	
	
	   
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
 
 and remove_conj (f : perm_formula) (conj : perm_formula) pos : perm_formula = match f with
  | Eq _
  | Join _ -> if eq_perm_formula f conj then mkTrue pos else f
  | And(f1, f2, p) ->
        (mkAnd (remove_conj f1 conj p) (remove_conj f2 conj p) p)
  | _ -> f

 
let check_up_dom_sat l = 
	let r = List.concat(List.map (fun (c1,c2,c3)-> [(c1,c3);(c2,c3)]) lj) in
	let rec prop lc lr = match lr with
		| [] -> ()
		| (c1,c2)::lr-> 
			let r1 = try PMap.find c1 lc with _ -> [] in
			let r2 = try PMap.find c2 lc with _ -> [] in
			if List.exists ('= c2) r1 then raise Unsat_exception 
			else 
				let nd = c1::(r1@r2) in
				let nlc = PMap.add c2 nd lc in
				prop nlc lr
	in prop (PMap.create (<)) r
	
	
(*obtain: v1+...vn+c=v or v1+...vn = c where the rhs never appears on the left*)
	let propag_all lj = 
		let prop1 (c1,c2,c3) (v1,lv)= 
			  let eq_f = eq_fperm in
			  let l1,l2 = List.filter (eq_f c3) lv in
			  match (List.length l1) with 
			   | 0 ->((v1,vl),false)
			   | 1 -> if (eq_f v1 c1) || (eq_f v1 c3) || (eq_f v1 c2) || (List.exists (fun c-> (eq_f c c1) || (eq_f c c2)) vl) then raise Unsat_exception
					  else ((v1,(c1,c2)@l2),true)
			   | _ -> raise Unsat_exception in
			   
		let to_cannon l = 
			let collect_const l = 
				let lc, lv = List.fold_left (fun (a1,a2) c-> match c with | PConst s-> (s::a1,a2) | _ -> (a1,c::a2)) ([],[]) l in
				let c = match lc with 
							| [] -> (None,lv)
							| h::t ->
								let c = List.fold_left (fun a c -> if Ts.can_join a c then Ts.join a c else raise Unsat_exception) h t in
							(Some c , lv) in
			let l = List.map (fun (v,l) -> (v,collect_const l)) l in
			let lv,lc = List.fold_left (fun (v,l)-> match v with | PConst s-> ((s,l)::a1,a2) | _-> (a1,l::a2)) ([],[]) l in
			let lc = List.map (fun (c,(c1,vl))-> match c1 with
									| None -> (c,vl)
									| Some s-> if (Ts.contains c c1) then ((Ts.subtract c c1),vl) else raise Unsat_exception) lc in 
			(lv,lc) in
		let rec hlp lc = 
			let  l,b = List.fold_left (fun (lc,b) c-> 
				let lc,nb = List.split ((List.map prop1 c) lc) in
				let nb = (b|| (List.exists (fun c->c) nb)) in
				(lc,nb)) (lc,false) lj in
			if b then hlp l else lc	in
		let r = hlp (List.map (fun (c1,c2,c3)-> (c3,[c1;c2]))) in
		(to_cannon r) in
			
	
let to_numbers lj = 
  let search cnt lm v = try (PMap.find v lm , cnt, lm) with _ -> let n = cnt+1 in (n, n, PMap.add v n lm) in	
  let r,lm,_ = List.fold_left (fun (lr,lm,cnt) (c1,c2,c3)-> 
	let n1,cnt,lm = search cnt lm c1 in
	let n2,cnt,lm = search cnt lm c2 in
	let n3,cnt,lm = search cnt lm c3 in
	((n1,n2,n3)::lr,lm,cnt)) ([], PMap.create cmp_fperm,1) lj in
   (r,lm) in
(*let rec aset_list l f = 
   let rec get_eqs f = 
     List.fold_left (fun (a1,a2) c -> match c with
         | Eq (f1,f2,_)-> ((f1,f2)::a1,a2)
         | Exists (vl,f,_) -> 
            let r1,r2 = get_eqs f in
             (r1::a1,vl@r2@a2)
         | _ -> a1,a2 )([],[])(list_of_conjs f) in
  let l1,l2 = get_eqs f in
  let l2 = w@l2 in
  let r = List.fold_left (fun a (v1,v2)->
     try
       let l1 = List.partition () a in
  
   ) [] l1 in
  List.map (List.filter (fun v-> not (List.exists (eq_fperm l2) v))) r


let ex_subst l v = try
  let l = List.find (List.exists (eq_fperm v)) l in
  Some (List.find (fun c-> not (eq_fperm v c)) l)
with Not_found -> None 
  *)	
  
 *)