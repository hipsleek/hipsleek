(**
 * Useful list utilities
 *
 * @author Vu An Hoa
 *)

(**
 * Partition elements of a list into 
 * equivalence classes, assuming eqv
 * is reflexive, symmetric, and 
 * transitive.
 * @param eqv indicate whether two 
 * elements of the list are equivalent 
 * i.e. belong to the same class
 * @return a list of equivalence classes 
 *)
let rec group_elms eqv l = match l with
	| [] -> []
	| h :: t -> (* select elements in t that are in same class as h *)
		let ch,r = List.partition (eqv h) t in
		let cr = group_elms eqv r in (* partition the rest *)
			(h :: ch) :: cr

(**
 * Remove duplicates in a list.
 *)
let remove_dups_eq eq l =
	let eq_classes = group_elms eq l in
		List.map List.hd eq_classes

(**
 * Check if exists y in l such that [eq x y]
 *)
let memeq eq l x =
	try
		let _ = List.find (eq x) l in
			true
	with
		| Not_found -> false

(**
 * Check if for all y in l: [eq x y] does not hold
 *)	
let notmemeq eq l x = not (memeq eq l x)
	
(**
 * Compute l1 \ l2
 *)
let remove_all_eq eq l1 l2 =
	List.filter (notmemeq eq l2) l1

(**
 * Position-aware list map
 *)		
let mapi f l =
	let rec mapi_helper l i =
		match l with
			| [] -> []
			| h :: t -> (f i h) :: (mapi_helper t (i+1)) in
	mapi_helper l 0
	
(**
 * Check if the elements of l1 is a subset of l2
 *)
let subset_eq eq l1 l2 =
	List.for_all (memeq eq l2) l1

(**
 * Collect common elements of two lists
 *)
let intersect_eq eq l1 l2 =
	List.filter (fun x -> 
		List.exists (eq x) l1) l2