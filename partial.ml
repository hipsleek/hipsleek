open Globals
open Cformula
open Gen

module CP = Cpure

(* partial field to be captured by
   (var,[hole],num_of_arg)
   [hole] starts from 0
   [hole] < num_of_arg
*)

(* hole abstraction *)
(* pointer, list of holes, total arguments *)
type holeA = (CP.spec_var * int list * int)

let rec collect_holes vars n = match vars with
  | [] -> []
  | x::t -> let th = collect_holes t (n+1) in 
	(match x with 
	  | CP.SpecVar (_,vn,_) -> if (vn.[0] = '#') then n::th else th)

(* [Internal] Create a list [x,x+1,...,x+n-1] *)
let rec first_naturals n x = 
  if n = 0 then [] 
  else x :: (first_naturals (n-1) (x+1)) 

(**
 * An Hoa : Compute the indices of holes in a list of spec vars.
 **)
let compute_holes_list svs = 
	let temp = first_naturals (List.length svs) 0 in
	let res = List.map2 (fun x y -> if (CP.is_hole_spec_var x) then [y] else []) svs temp in
	let res = List.flatten res in
		res

(* [Internal] Extends hvars with holes and collect the
   list of holes! *)
let rec extend_and_collect_holes vs offset num_ptrs =
  let temp = first_naturals num_ptrs 0 in
  (* let _ = print_endline ("Testing code : " ^ (String.concat "," (List.map string_of_int temp))) in *)
  let numargs = List.length vs in
  let holes = List.fold_left (fun l i -> let d = i - offset in
  if (d < 0 || d >= numargs) then List.append l [i] else l)
	[] temp	in
  let newvs = List.map (fun i -> if (List.mem i holes) then 
	CP.SpecVar (UNK,"#",Unprimed) 
  else List.nth vs (i - offset)) temp in
  (* let _ = print_endline ("holes = { " ^ (String.concat "," (List.map string_of_int holes)) ^ " }") in *)
  (* let _ = print_endline ("vars = { " ^ (String.concat "," (List.map Cprinter.string_of_spec_var newvs)) ^ " }") in *)
  (newvs,holes)


(* 1 3 [1,2] [3]   -> true *)
(* 1 3 [1,2] [2,3] -> true *)
(* 1 3 [2] [2,3]   -> false *)
(* 1 3 [1] [2]     -> false *)
(* 0 3 [1] [2,3]   -> false *)
let rec is_mergeable_h n len h1 h2 =
  match h1 with
    | [] -> false
    | x1::r1 ->
          begin
            match h2 with
              | [] -> 
                    if n==x1 then is_mergeable_h (n+1) len r1 h2
                    else false
              | x2::r2 ->
                    if x1==n then
                      if x2==n then is_mergeable_h (n+1) len r1 r2
                      else is_mergeable_h (n+1) len r1 h2
                    else 
                      if x2==n then is_mergeable_h (n+1) len h1 r2
                      else false
          end
  
let mergeable ((sv1,h1,len1) as arg1) ((sv2,h2,len2) as arg2) =
  let t1 = CP.type_of_spec_var sv1 in
  let t2 = CP.type_of_spec_var sv2 in
  if t1!=t2 then false
  else is_mergeable_h 0 (len1-1) h1 h2 

let list_mergeable arg1 ls =
  List.exists (mergeable arg1) ls

(* [],[3]    --> -ve *)
(* [2],[3]   --> 0 *)
(* [2,3],[3] --> +ve *)
let larger (_,h1,_) (_,h2,_) = (List.length h1)-(List.length h2)

(* input : list of holeA
   output : list of distinct nodes, remainder *)
let build_disj (ls:holeA list) : (holeA list * holeA list) =
  (* disjoint_set * rest_of_heap *)
  let ls = List.sort larger ls (* sort by increasing number of holes *) 
  in List.fold_left
      (fun (dl,rest) x ->
      if list_mergeable x dl then (dl,x::rest)
      else (x::dl,rest))
      ([],[]) ls

let build_disj (ls:holeA list) : (holeA list * holeA list) =
  let pr = pr_list (pr_triple !CP.print_sv (pr_list string_of_int) (add_str "args:" string_of_int)) in
  Debug.ho_1 "build_disj" pr (pr_pair (add_str "dist:" pr) (add_str "rest:" pr)) build_disj ls 

(*LDK: TO CHECK ??? how to deal with perms correctly
Permissions v.s pertial fields
*)
(**
 * An Hoa : Supplementary function to merge two data nodes.
 **)
let merge_two_nodes dn1 dn2 =
	match dn1 with
	| DataNode { h_formula_data_node = dnsv1;
		h_formula_data_name = n1;
		h_formula_data_derv = dr1;
		h_formula_data_imm = i1;
		h_formula_data_arguments = args1;
        h_formula_data_perm = perm1;
        h_formula_data_origins = origs1;
        h_formula_data_original = orig1;
		h_formula_data_holes = holes1;
		h_formula_data_label = lb1;
		h_formula_data_remaining_branches = br1;
		h_formula_data_pruning_conditions = pc1;
		h_formula_data_pos = pos1 } -> (match dn2 with
			| DataNode { h_formula_data_node = dnsv2;
						h_formula_data_name = n2;
						h_formula_data_derv = dr2;
						h_formula_data_imm = i2;
						h_formula_data_arguments = args2;
                        h_formula_data_perm = perm2;
                        h_formula_data_origins = origs2;
                        h_formula_data_original = orig2;
						h_formula_data_holes = holes2;
						h_formula_data_label = lb2;
						h_formula_data_remaining_branches = br2;
						h_formula_data_pruning_conditions = pc2;
						h_formula_data_pos = pos2 } -> 
							(* [Internal] Check if a spec_var is a hole spec_var. *)
							let is_hole_specvar sv = 
								let svname = CP.name_of_spec_var sv in
									svname.[0] = '#' in
							(* [Internal] Select the non-hole spec_var. *)
							let combine_vars sv1 sv2 =
								if (is_hole_specvar sv1) then (sv2,true) 
								else if (is_hole_specvar sv2) then (sv1,true)
								else (sv1,false)
							in
							let args, not_clashes = List.split (List.map2 combine_vars args1 args2) in
							let not_clashed = List.for_all (fun x -> x) not_clashes in
							let res = DataNode { h_formula_data_node = dnsv1;
										h_formula_data_name = n1;
						                h_formula_data_derv = dr1; (*TO CHECK*)
										h_formula_data_imm = i1;
										h_formula_data_arguments = args;
                                        h_formula_data_perm = None; (*perm1? perm2???*)
                                        h_formula_data_origins = origs1; (*??? how to merge??*)
                                        h_formula_data_original = orig1;(*??? how to merge??*)
										h_formula_data_holes = 
												Gen.BList.intersect_eq (=) holes1 holes2;
										h_formula_data_label = lb1;
										h_formula_data_remaining_branches = 
											(match br1 with
												| None -> br2
												| Some l1 -> (match br2 with
																| None -> br1
																| Some l2 -> Some (List.append l1 l2)));
										h_formula_data_pruning_conditions = List.append pc1 pc2;
										h_formula_data_pos = no_pos } in 
								if not_clashed then res else HFalse
			| HTrue -> dn1
			| HFalse -> HFalse
			| _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = ("[merge_two_nodes] Expect either HTrue or a DataNode but get " ^ (!print_h_formula dn2))} )
	| HTrue -> dn2
	| HFalse -> HFalse
	| _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = ("[merge_two_nodes] Expect either HTrue or a DataNode but get " ^ (!print_h_formula dn1)) }


(**
 * An Hoa : Merge a list of data nodes with a common root pointer into either
 *          a single data node or HFalse if there is a clash (and HTrue if
 *          we are merging nothing. This case SHOULD NOT happen.)
 **)
let merge_data_nodes_common_ptr dns = 
	List.fold_left merge_two_nodes HTrue dns


let merge_partial_h_formula f = 
	(* let _ = print_endline ("[merge_partial_h_formula] input = { " ^ (!print_h_formula f) ^ " }") in *)
	let sc = split_star_h f in
	(* let _ = print_endline ("[merge_partial_h_formula] split separation conjunction = { " ^ (String.concat " ; " (List.map !print_h_formula sc)) ^ " }") in *)
	let dns,vns = List.partition is_data sc in
	(* let _ = print_endline ("[merge_partial_h_formula] data nodes = " ^ (string_of_set !print_h_formula dns)) in *)
	(* let _ = print_endline ("[merge_partial_h_formula] other nodes = " ^ (string_of_set !print_h_formula vns)) in *)
	(* Collect the data pointers *)
	let dnrootptrs = List.map get_ptr_from_data dns in
	let dnrootptrs = Gen.BList.remove_dups_eq CP.eq_spec_var dnrootptrs in
	(* Partition the data nodes into groups of same pointer *)
	let dnodespart = List.map (fun x -> List.filter (fun y -> CP.eq_spec_var (get_ptr_from_data y) x) dns) dnrootptrs in
	(* let _ = print_endline ("[merge_partial_h_formula] grouped data nodes = " ^ (string_of_set (fun x -> string_of_set !print_h_formula x) dnodespart)) in *)
	(* Merge the data nodes in each group *)
	let merged_data_nodes = List.map merge_data_nodes_common_ptr dnodespart in
	(* let _ = print_endline ("[merge_partial_h_formula] merged data nodes = " ^ (string_of_set !print_h_formula merged_data_nodes)) in *)
	(* Combine the parts to get the result *)
	let f = combine_star_h (List.append merged_data_nodes vns) in
		f


(**
 * An Hoa : Merge the partial heaps into a single heap node
 * For instance, 
 *         h::node<#,#,a> * h::node<#,b,#>
 * reduces to h::node<#,b,a> while
 *         h::node<#,#,a> * h::node<#,#,b>
 * is transformed to False.
 * TODO implement
 **)
let rec merge_partial_heaps f = match f with
	| Base fb -> let nh = merge_partial_h_formula fb.formula_base_heap in
					Base { fb with formula_base_heap = nh }
	| Or fo -> 	let nf1 = merge_partial_heaps fo.formula_or_f1 in
				let nf2 = merge_partial_heaps fo.formula_or_f2 in
					Or { fo with formula_or_f1 = nf1; formula_or_f2 = nf2; }
	| Exists fe -> let nh = merge_partial_h_formula fe.formula_exists_heap in
					Exists { fe with formula_exists_heap = nh }

let hole_abs_of_h_formula_data (h:h_formula_data) =
  let ptr = h.h_formula_data_node in
  let hl = h.h_formula_data_holes in
  let args = h.h_formula_data_arguments in
  (ptr,hl,List.length args)

let hole_abs_of_h_formula (h:h_formula) =
  match h with
    | DataNode hd -> hole_abs_of_h_formula_data hd 
    | _ -> report_error (pos_of_h_formula h) "hole_abs_of_h_formula : data expected"
