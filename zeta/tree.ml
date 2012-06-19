(**
 * General tree data type
 * 
 * @author Vu An Hoa
 *)

(* Remark: All EmptyTree child should be removed *)
type 'a tree = 
	| EmptyTree
	| Node of 'a * ('a tree list)
	
(* Getters *)

let get_childrens t = match t with
	| EmptyTree -> []
	| Node (_,c) -> c

let get_value d t = match t with
	| EmptyTree -> d
	| Node (v,c) -> v

(* Tree transformer *)

let rec map f t = match t with
	| EmptyTree -> t
	| Node (v, c) -> Node (f v, List.map (map f) c)

let rec fold d f t = match t with
	| EmptyTree -> d
	| Node (v, c) ->
		let nc = List.map (fold d f) c in
			f v nc

(**
 * Print a tree $t$ using a supplied node 
 * printing function $pr_val$
 *)
let rec print_tree pr_val t = match t with
	| EmptyTree -> ""
	| Node (v, c) ->
		let cs = List.map (print_tree pr_val) c in
		let cs = List.map (fun x -> "\t" ^ x) cs in
			(pr_val v) ^ "\n" ^ (String.concat "\n" cs)

(* Tree traversal *)

(* Tree folding *)