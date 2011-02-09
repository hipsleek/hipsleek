open Globals
module P = Cpure


type frac_perm = P.spec_var option * perm_modifier

type perm_formula = 
  | And of (perm_formula * perm_formula * loc)
  | Or  of (perm_formula * perm_formula * loc)
  | Join of (frac_perm*frac_perm*frac_perm * loc)
  | Eq of (frac_perm*frac_perm *loc)
  | Exists of (P.spec_var  list * perm_formula *loc)
  | PTrue of loc
  | PFalse of loc

let print_perm_f = ref (fun (c:perm_formula)-> " printing not initialized")
let print_frac_f = ref (fun (b:bool) (c:frac_perm)-> "printing not initialized")
  
let frac_of_var v = (Some v,[])
  
let mkPFull () :frac_perm = (None,[])

let mkPerm posib_var splint :frac_perm = (posib_var,splint)

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

let freshPermVar () = P.SpecVar (P.OType "perm", fresh_name (), Unprimed) 

let mkFullVar () : (P.spec_var * perm_formula) = 
  let nv = freshPermVar() in
  (nv,mkEq (frac_of_var nv) (mkPFull ()) no_pos)

let mkJoin v1 v2 v3 pos = Join (v1,v2,v3,pos)

let isConstFalse f = match f with PFalse _ -> true | _ -> false
let isConstTrue  f = match f with PTrue _ -> true | _ -> false

let frac_fv f= match (fst f) with | Some v -> [v] | _ -> []

let rec fv f = match f with
  | And (f1,f2,_) -> P.remove_dups_svl ((fv f1)@(fv f2))
  | Or (f1,f2,_) -> P.remove_dups_svl ((fv f1)@(fv f2))
  | Join (f1,f2,f3,_) -> P.remove_dups_svl ((frac_fv f1)@(frac_fv f2)@(frac_fv f3))
  | Eq (f1,f2,_) -> P.remove_dups_svl ((frac_fv f1)@(frac_fv f2))
  | Exists (l1,f1,_) -> Util.difference_f P.eq_spec_var (fv f1) l1
  | PTrue _ | PFalse _ -> [] 
    
let mkExists vl f pos =  match f with
  | PFalse _
  | PTrue _ -> f
  | _ ->
    let nl = Util.intersect_fct P.eq_spec_var vl (fv f) in
    if nl==[] then f else Exists (nl,f,pos)
    
and subst_perm (fr, t) (o1,o2) = match o1 with
  | Some s -> (Some (P.subst_var (fr,t) s) , o2)
  | _ -> (o1,o2)
  
let rec apply_one (fr,t) f = match f with
  | And (f1,f2,p) -> And (apply_one (fr,t) f1,apply_one (fr,t) f2, p)
  | Or (f1,f2,p) -> Or (apply_one (fr,t) f1,apply_one (fr,t) f2, p)
  | Join (f1,f2,f3,p) -> Join (subst_perm (fr,t) f1, subst_perm (fr,t) f2, subst_perm (fr,t) f3, p)
  | Eq (f1,f2,p) -> Eq (subst_perm (fr,t) f1, subst_perm (fr,t) f2, p)
  | Exists (qsv,f1,p) ->  
      if Util.mem_eq P.eq_spec_var fr qsv then f 
      else Exists (qsv, apply_one (fr,t) f1, p)
  | _ -> f

and subst (sst : (P.spec_var * P.spec_var) list) (f : perm_formula) : perm_formula = match sst with
  | s::ss -> subst ss (apply_one s f) 				(* applies one substitution at a time *)
  | [] -> f

and subst_avoid_capture (fr : P.spec_var list) (t : P.spec_var list) (f : perm_formula) =
  let st1 = List.combine fr t in
  let f2 = apply_subs st1 f in 
  f2
  
and apply_subs_frac sst f = match f with
  | (Some v, x) -> (Some (P.subs_one sst v),x)
  | _ -> f
  
and apply_subs (sst : (P.spec_var * P.spec_var) list) (f : perm_formula) : perm_formula = match f with
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
  
(*elim exists*)
let elim_exists_perm w f pos = f
(*elim perm exists if any*)
let elim_exists_perm_exists f = f

let simpl_perm_formula f = f
(*imply*)
(*sat*)
let is_sat f = true
(*transformers*)

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
      
let fold_frac_perm (e:frac_perm) (arg: 'a) f f_arg (f_comb: frac_perm -> 'b list -> 'b) :(frac_perm * 'b) =
  let r = f arg e in
  match r with
  | Some s -> s
  | None -> (e, f_comb e [])
      
let trans_perm (e:perm_formula) (arg: 'a) f f_arg f_comb_a : (perm_formula * 'b) =
 let f_perm, f_frac = f in
 let f_perm_arg, f_frac_arg = f_arg in
 let f_perm_comb, f_frac_comb = f_comb_a in
 let foldr_frac (arg: 'a) (e: frac_perm): (frac_perm * 'b) = fold_frac_perm e arg f_frac f_frac_arg f_frac_comb in   
    
 let rec foldr_f (arg: 'a) (e:perm_formula) :(perm_formula * 'b) = 
   let r = f_perm e in
   match r with
   | Some e -> e
   | None ->
      let new_arg = f_perm_arg arg e in
      let f_comb = f_perm_comb e in
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

