open Globals

module P = Ipure

(*
and frac_perm = 
  | PFull
  | PConst of perm_splint list
  | PVar of (ident * primed)* (perm_splint list)
*)

type frac_perm  = 
	| PConst of perm_modifier
	| PVar of (ident*primed)
	
type perm_formula = 
  | And of (perm_formula * perm_formula * loc)
  | Or of (perm_formula * perm_formula * loc)
  | Join of (frac_perm*frac_perm*frac_perm * loc)
  | Eq of (frac_perm*frac_perm *loc)
  | Exists of ((ident * primed) list * perm_formula *loc)
  | PTrue of loc
  | PFalse of loc

let print_perm_f = ref (fun (c:perm_formula)-> " printing not initialized")
let print_frac_f = ref (fun (b:bool) (c:frac_perm)-> "printing not initialized")
  
let mkVPerm (v:ident*primed):frac_perm = PVar v

let mkCPerm l : frac_perm = PConst l
 
let mkPFull () :frac_perm = mkCPerm []

let mkPAnnot t = match t with
	| None -> mkPFull ()
	| Some a ->  a
	 

let name_of_frac s f = match f with
  | PConst _ -> Gen.report_error no_pos s
  | PVar v -> v

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
        
let mkEq f1 f2 pos = 
 (* let _ = print_string ("f1: "^(!print_frac_f true f1)^"\n") in 
  let _ = print_string ("f2: "^(!print_frac_f true f2)^"\n") in *)
  let r = Eq (f1,f2,pos) in
  (*let _ = print_string ("r: "^(!print_perm_f r)^"\n") in *)
  r

let frac_fv f= match f with 
	| PVar v -> [v] | PConst _ -> []

let rec fv f = match f with
  | And (f1,f2,_) -> Gen.BList.remove_dups_eq P.eq_var ((fv f1)@(fv f2))
  | Or (f1,f2,_) -> Gen.BList.remove_dups_eq P.eq_var ((fv f1)@(fv f2))
  | Join (f1,f2,f3,_) -> Gen.BList.remove_dups_eq P.eq_var ((frac_fv f1)@(frac_fv f2)@(frac_fv f3))
  | Eq (f1,f2,_) -> Gen.BList.remove_dups_eq P.eq_var ((frac_fv f1)@(frac_fv f2))
  | Exists (l1,f1,_) -> Gen.BList.difference_eq P.eq_var (fv f1) l1
  | PTrue _ | PFalse _ -> [] 

let mkExists vl f pos =  match f with
  | PFalse _
  | PTrue _ -> f
  | _ ->
    let nl = Gen.BList.intersect_eq P.eq_var vl (fv f) in
    if nl==[] then f else Exists (nl,f,pos)

let mkJoin v1 v2 v3 pos = Join (v1,v2,v3,pos)

let mkPFormula o = match o with
	| None -> mkTrue no_pos
	| Some f -> f
	 

let isConstFalse f = match f with PFalse _ -> true | _ -> false
let isConstTrue  f = match f with PTrue _ -> true | _ -> false
    
let isConstFrac f = match f with
 | PConst _ -> true 
 | PVar _ -> false  
	
and subst_perm (fr, t) f = match f with
  | PVar s -> PVar (if P.eq_var s fr then t else s)
  | PConst _ -> f
  
let rec apply_one (fr,t) f = match f with
  | And (f1,f2,p) -> And (apply_one (fr,t) f1,apply_one (fr,t) f2, p)
  | Or (f1,f2,p) -> Or (apply_one (fr,t) f1,apply_one (fr,t) f2, p)
  | Join (f1,f2,f3,p) -> Join (subst_perm (fr,t) f1, subst_perm (fr,t) f2, subst_perm (fr,t) f3, p)
  | Eq (f1,f2,p) -> Eq (subst_perm (fr,t) f1, subst_perm (fr,t) f2, p)
  | Exists (qsv,f1,p) ->  
      if List.mem (fst fr) (List.map fst qsv) then f 
      else Exists (qsv, apply_one (fr,t) f1, p)
  | _ -> f
