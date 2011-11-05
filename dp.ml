open Globals
open Error
open Cpure

let subst_l l s =  List.map (fun (v1,v2)-> (subst_var s v1, subst_var s v2)) l

let rec partitioner f = 
  let rec neg f = match f with 
    | BForm ((bf,lb),p) -> BForm (((match bf with 
		| Eq (e1,e2,p) -> Neq(e1,e2,p)
		| Neq (e1,e2,p) -> Eq(e1,e2,p)
		| _ -> failwith ("found unexpected expression1 :"^(Cprinter.string_of_b_formula (bf,None)))), lb),p)
	| Not (f,_,_) -> f
	| Forall (v,f,l,p) -> Exists (v, neg f, l, p)
	| Exists (v,f,l,p) -> Forall (v, neg f, l, p)
	| And (f1,f2,p) -> Or (neg f1,neg f2,None,p)
	| Or (f1,f2,_,p) -> And (neg f1, neg f2, p) in

  let elim_ex v (le,ln) = 
	let filter (v1,v2) = eq_spec_var v1 v || eq_spec_var v2 v in 
	let subst (le,ln) t = subst_l le (v,t) , subst_l ln (v,t) in
	try 
      let (r1,r2) = List.find filter le in
	  if (eq_spec_var v r1) then (subst (le,ln) r2) else (subst (le,ln) r1)
	with 
	 | Not_found -> (le, List.filter (fun c -> not (filter c)) ln) in
	   
  let rec to_dnf f =  match f with 
    | BForm ((bf,_),_) -> (match bf with 
		| Eq (Var (v1,_),Var(v2,_),_) -> Some (if (eq_spec_var v1 v2) then [([],[])] else [([(v1,v2)],[])])
		| Neq (Var (v1,_),Var(v2,_),_) -> if (eq_spec_var v1 v2) then None else Some [([],[(v1,v2)])] 
		| Eq  (Null _, Var (v,_),_) | Eq  (Var (v,_),Null _,_) -> Some [([(v,null_var)],[])]
		| Neq (Null _, Var (v,_),_) | Neq (Var (v,_),Null _,_) -> Some [([(v,null_var)],[])]
		| Eq (IConst (c1,_),IConst(c2,_),_) -> if (c1=c2) then Some [] else None 
		| Eq (FConst (c1,_),FConst(c2,_),_) -> if (c1=c2) then Some [] else None 
		| Neq (IConst (c1,_),IConst(c2,_),_) -> if (c1=c2) then None else Some []
		| Neq (FConst (c1,_),FConst(c2,_),_) -> if (c1=c2) then None else Some []
		| BConst (b,_) -> if b then Some [] else None
		| _ -> failwith ("found unexpected expression :"^(Cprinter.string_of_b_formula (bf,None))))
	| Not (f,_,_) -> to_dnf (neg f)
	| Forall _ -> failwith "universal unexpected!!!"
	| Exists (v,f,_,_) -> (match to_dnf f with | None -> None | Some l -> Some (List.map (fun c-> elim_ex v c) l))
	| And (f1,f2,p) -> (match (to_dnf f1) with 
		| None -> None
		| Some l1 -> match (to_dnf f2) with 
		 | None -> None
		 | Some l2 -> Some (List.concat (List.map (fun (c1,c2)-> List.map (fun (d1,d2)-> (c1@d1,c2@d2)) l2) l1)))
	| Or (f1,f2,_,_) -> match (to_dnf f1) with 
		| None -> (to_dnf f2) 
		| Some l1 -> match (to_dnf f2) with 
			| None -> Some l1
			| Some l2 -> Some (l1@l2) in	
  (to_dnf f)
   
let partitioner f = 
	let pr1 = Cprinter.string_of_pure_formula in
	let pr4 = Gen.Basic.pr_list (Gen.Basic.pr_pair Cprinter.string_of_spec_var  Cprinter.string_of_spec_var)  in
	let pr3 = Gen.Basic.pr_pair pr4 pr4 in
	let pr2 = Gen.pr_option (Gen.Basic.pr_list pr3) in
	Gen.Debug.no_1 "partitioner" pr1 pr2 partitioner f
   
let check_sat lp = 
  let rec helper le ln =  match le with 
	| [] -> true
	| (f,t)::tl -> 
		let ln = subst_l ln (f,t) in
		if (List.exists (fun (v1,v2)-> eq_spec_var v1 v2) ln) then false 
		else helper (subst_l tl (f,t)) ln in
   if lp=[] then true else List.exists (fun (le,ln)-> ln=[] || helper le ln) lp
	 
	 
let rec asets l = match l with 	
	| [] -> []
	| (v1,v2)::tl -> 
		let le,ln = List.partition (fun c-> (Gen.BList.mem_eq eq_spec_var v1 c)||(Gen.BList.mem_eq eq_spec_var v2 c)) (asets tl) in
		let le = Gen.BList.remove_dups_eq eq_spec_var (v1::(v2::(List.concat le))) in
		le::ln 
		
let get_aset v l = 
	try 
		List.find (Gen.BList.mem_eq eq_spec_var v) l 
	with
	| Not_found -> [v]
		
let impl_test (c_le, c_ln) (a_le_sets,a_ln) = 
	let eq_impl_test (v1,v2) = List.exists (fun l-> Gen.BList.mem_eq eq_spec_var v1 l && Gen.BList.mem_eq eq_spec_var v2 l) a_le_sets in
	let neq_impl_test (v1,v2) = 
		let av1 = get_aset v1 a_le_sets in
		let av2 = get_aset v2 a_le_sets in
		List.exists (fun (v1,v2)-> 
			((Gen.BList.mem_eq eq_spec_var v1 av1) &&(Gen.BList.mem_eq eq_spec_var v2 av2))||
			((Gen.BList.mem_eq eq_spec_var v2 av1) &&(Gen.BList.mem_eq eq_spec_var v1 av2))) a_ln in
    let eq_impl = List.for_all eq_impl_test c_le in
	let neq_impl = List.for_all neq_impl_test c_ln in
	eq_impl && neq_impl

	 
let imply ante conseq s t = match (partitioner ante) with 
	| None -> true
	| Some la -> 
		if not (check_sat la) then true
		else match partitioner conseq with 
		 | None -> false
		 | Some lc -> if not (check_sat lc) then false 
		 else 
		   let la = List.map (fun (le,ln) -> (asets le, ln)) la in 
		 List.exists (fun c_pair-> List.for_all (impl_test c_pair) la) lc 
    
let is_sat f sat_no = match partitioner f with 
	| None -> false
	| Some l -> check_sat l 
