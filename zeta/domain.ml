(**
 * Main data structures for the formal
 * (logical) language 
 *
 * @author Vu An Hoa 
 *)

type domain =
	| SBool (* true/false
					even though representable using 
					integers, separate here for the 
					sake of later translation stages *)
	| SInt	(* set of integers *)
	| SWild of int
					(* unknown set, for domain estimation only *)
	| SMap of domain list
					(* set of map from : {tail} -> head *)

(* getters *)

(*
(**
 * Get the signature of a SMap sort
 *)
let signature_of_smap s = match s with
	| SMap d -> d
	| _ -> failwith "[signature_of_smap] : input sort is not a SMap"

(**
 * Get the signature of a SMap sort
 *)
let signature_of_smap s = match s with
	| SMap d -> d
	| _ -> failwith "[signature_of_smap] : input sort is not a SMap"

(**
 * Get the signature of a SMap sort
 *)
let signature_of_smap s = match s with
	| SMap d -> d
	| _ -> failwith "[signature_of_smap] : input sort is not a SMap"
*)	

(* query *)

let rec has_no_wild s = match s with
	| SBool
	| SInt -> true
	| SWild _ -> false
	| SMap d ->
		List.for_all has_no_wild d

(* compare domains *)

let rec eq_domain s1 s2 = 
	match (s1,s2) with
		| (SWild i, SWild j) -> i = j
		| (SInt, SInt) -> true
		| (SBool, SBool) -> true
		| (SMap d1, SMap d2) ->
				List.for_all2 eq_domain d1 d2
		| _ -> false

(*

(* solve the swild domain constraints *)

let rec unify_sort s1 s2 = match (s1, s2) with
	| (SWild i, SWild j) -> 
		if (j > i) then ([(s1, s2)], s2)
		else if (i > j) then ([(s2, s1)], s1)
		else ([], s1)
	| (SWild _, _) -> ([(s1, s2)], s2)
	| (_, SWild _) -> ([(s2, s1)], s1)
	| (SMap d1, SMap d2) ->
		let soln, rs = List.split (List.map2 unify_sort d1 d2) in
			(List.flatten soln, SMap rs)
	| (SInt, SInt)
	| (SBool, SBool) -> ([], s1)
	| _ -> failwith ("[unify_sort] : sorts " ^ (string_of_sort s1) ^
				" and " ^ (string_of_sort s2) ^ " are not unifiable")

let rec unify_sort_list sl =
	let unf (ps, x) y =
		let ns, z = unify_sort x y in
			(List.append ps ns, z) in
	let soln, rs = List.fold_left unf ([], SWild 0) sl in
	let soln = List.filter (fun (x, y) -> match x with SWild 0 -> false | _ -> true) soln in
		(soln, rs)

let rec subst_sort (s1,s2) s =
	let s1i = match s1 with
		| SWild i -> i
		| _ -> failwith "Unexpected sort" in   
	match s with
		| SWild i ->
			if (i = s1i) then s2 else s
		| SMap d ->
			SMap (List.map (subst_sort (s1,s2)) d)
		| _ -> s

let eq_sort_pair (x,y) (z,t) =
	(eq_sort x z) && (eq_sort y t)

let rec subst_ground_sorts a sl =
	let gr, rs = List.partition (fun (_, y) -> is_ground_sort y) sl in
	let gr = GList.remove_dups_eq eq_sort_pair gr in
	(*let _ = List.map (fun (x,y) -> print_endline ("Ground substitution found : " ^ (string_of_sort x) ^ " --> " ^ (string_of_sort y))) gr in*)
	if (gr = []) then (GList.remove_dups_eq eq_sort_pair a, sl)
	else
		let rs = List.map (fun (x,y) ->
			try let u,v = List.find (fun (z,t) -> eq_sort x z) gr in
				fst (unify_sort y v)
			with Not_found -> [(x,y)]) rs in
		let rs = List.flatten rs in 
		let rs = List.fold_right (fun (x,y) r -> List.map (fun (z,t) -> (z, subst_sort (x,y) t)) r) gr rs in
			subst_ground_sorts (List.append a gr) rs

(**
 * Solve for all SWild from the given list of unification constraints as input
 * @return a list of pairs (i, d) to indicate domain (SWild i) must be unified with a ground domain d 
 *)
let solve_domains uni_constr =
	let soln, _ = List.split (List.map unify_sort_list uni_constr) in
	let soln = List.flatten soln in
	let soln, rem = subst_ground_sorts [] soln in
	let soln = List.sort (fun (x1,_) (x2,_) -> 
		match (x1, x2) with
			| (SWild i, SWild j) -> i - j
			| _ -> failwith "exception") soln in
		soln
*)