(**
 * Data structure and utilities to
 * manipulate sorts (i.e. types) in 
 * the formal language.
 *
 * @author Vu An Hoa
 *)

open Zutils

type sort =
	| SBool
	| SInt (* primitive sorts *)
	| SWild of int (* wildcard sort with ID *)
	| SMap of sort list (* head is sort of image and tail is sort of arguments *)

(* SORT PRINTING *)

let rec string_of_sort s = match s with
	| SWild i -> "X_" ^ (string_of_int i)
	| SInt -> "Z"
	| SMap d -> (String.concat "x" (List.map string_of_sort (List.tl d))) ^ "->" ^ (string_of_sort (List.hd d))
	| SBool -> "2"

let rec latex_of_sort s = match s with
	| SWild i -> "\\mathcal{X}_{" ^ (string_of_int i) ^ "}" 
	| SInt -> "\\mathbb{Z}"
	| SMap d -> (String.concat "\\times" (List.map latex_of_sort (List.tl d))) ^
			" \\mapsto " ^ (latex_of_sort (List.hd d))
	| SBool -> "\\mathbb{B}"

(* SORT UTILITIES *)

(**
 * Get the signature of a SMap sort
 *)
let signature_of_smap s = match s with
	| SMap d -> d
	| _ -> failwith "[signature_of_smap] : input sort is not a SMap"

let rec eq_sort s1 s2 = match (s1,s2) with
	| (SWild i, SWild j) -> i = j
	| (SInt, SInt)
	| (SBool, SBool) -> true
	| (SMap d1, SMap d2) -> List.for_all2 (fun x y -> eq_sort x y) d1 d2
	| _ -> false

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

let rec is_ground_sort s = match s with
	| SWild _ -> false
	| SMap d ->
		List.for_all is_ground_sort d
	| _ -> true

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
