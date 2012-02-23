(**
 * SUPPORTING UTILITIES
 * 
 * @author Vu An Hoa
 *)

(* LIST PROCESSING UTILITIES *)

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
 * Compute l1 \ l2
 *)
let remove_all_eq eq l1 l2 =
	let meml2 x = try
			let _ = List.find (eq x) l2 in
				false
		with Not_found -> true in
	List.filter meml2 l1

(**
 * Position-aware list map
 *)		
let mapi f l =
	let rec mapi_helper l i =
		match l with
			| [] -> []
			| h :: t -> (f i h) :: (mapi_helper t (i+1)) in
	mapi_helper l 0