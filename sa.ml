open Globals
open Gen
open Cpure
open Cformula

module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq

type drop_loc =  CP.spec_var * int
type drop_loc_lst = drop_loc list
type rel_def  = (CP.rel_cat * (CP.spec_var * (CP.exp list) * loc) * CF.formula)
let str_of_drop_loc (dloc: drop_loc): string = 
  let (a,b) = dloc in
  "(" ^ (CP.name_of_spec_var a) ^ ", " ^ (string_of_int b) ^ ")"

let str_of_drop_loc_lst (dlocs: drop_loc_lst): string = 
  let rec helper(dlocs: drop_loc_lst): string = match dlocs with 
    |[] ->""
    |[x] -> str_of_drop_loc x
    |x::y -> (str_of_drop_loc x) ^ ", " ^ (helper y)
  in
  "[" ^ (helper dlocs) ^ "]"

let eq_drop_loc (l1: drop_loc)(l2:drop_loc):bool=
  let a1,b1 = l1 in
  let a2,b2 = l2 in
  (CP.eq_spec_var a1 a2) && b1==b2

let get_hp_rel_formula (f:CF.formula) =
  match f with 
    |CF.Base  ({CF.formula_base_heap = h1;
		CF.formula_base_pure = p1})
    |CF.Exists ({CF.formula_exists_heap = h1;
		 CF.formula_exists_pure = p1}) -> (
      CF.get_hp_rel_h_formula h1
    )
    |CF.Or f  -> report_error no_pos "not handle yet"

let get_hp_rel_name_formula (f:CF.formula) =
  match f with 
    |CF.Base  ({CF.formula_base_heap = h1;
		CF.formula_base_pure = p1})
    |CF.Exists ({CF.formula_exists_heap = h1;
		 CF.formula_exists_pure = p1}) -> (
      CF.get_hp_rel_name_h_formula h1
    )
    |CF.Or f  -> report_error no_pos "not handle yet"

let string_of_def (def: rel_def): string = 
  let (cat, rel, f) = def in
  let  (r, args, l) = rel in
  (*let str_of_args = (CP.string_of_exp (List.hd args))  ^ (List.fold_left (fun a b -> ", " ^ (CP.string_of_exp b)  ^ a) "" (List.tl args)) in*)
let str_of_args = "" in
  let str_of_rel =  (Cprinter.string_of_spec_var r)^ "(" ^ str_of_args ^ ")" in
  (CP.print_rel_cat cat)^": ("^ str_of_rel ^") --> "^(Cprinter.string_of_formula f)

let rec simplify_hp_lst_assume (hp_assumes: (CF.formula * CF.formula) list): ((CF.formula * CF.formula) list) = 
  let _ = Debug.info_pprint ("----------Simplify list assumes------------- ") no_pos in 
  Debug.info_hprint (add_str "INPUT" (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) hp_assumes no_pos;
  let droped_as = drop_para_hp_lst_assume hp_assumes in 
  Debug.info_hprint (add_str "AFTER DROP: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) droped_as no_pos;
  let new_hp_assume, defs = collect_def_hp_lst_assume droped_as in 
  Debug.info_hprint (add_str "DEFS: " (pr_list_ln string_of_def)) defs no_pos;
  Debug.info_hprint (add_str "AFTER COLLECT DEF: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) new_hp_assume no_pos;
   droped_as

and drop_para_hp_lst_assume (hp_assumes: (CF.formula * CF.formula) list): ((CF.formula * CF.formula) list) = 
  let drlocs = List.map check_drop_para_hp_assume hp_assumes in
  let get_rels (hp_assume: CF.formula * CF.formula): (CP.spec_var list) =
    let (f1,f2) = hp_assume in
    let svs1  = get_hp_rel_name_formula f1 in
    let svs2  = get_hp_rel_name_formula f2 in
    svs1@svs2
    in
  let hrels = List.map (fun a -> (get_rels a)) hp_assumes in
  let assume_sum = List.combine drlocs hrels in 
  let locs = List.concat drlocs in
  let rec check_dupl (locs: drop_loc_lst): drop_loc_lst = match locs with
    | [] -> []
    | [x] -> [x]
    | x::y -> if(List.exists (fun c -> eq_drop_loc x c) y)then check_dupl(y) else x::check_dupl(y) 
  in 
  let locs = check_dupl locs in
  let check_loc_in_all_assume (loc: drop_loc)(ass: (drop_loc_lst * (CP.spec_var list)) list): bool =
    let rec helper  (loc: drop_loc)(as1: drop_loc_lst * (CP.spec_var list)): bool =
      let v,l = loc in 
      let (drlocs, svs) = as1 in
      if((List.exists (fun c -> eq_drop_loc loc c) drlocs)|| not (List.exists (fun c -> CP.eq_spec_var v c) svs)) then true
      else false
    in 
    if(List.exists (fun c -> not(helper loc c)) ass) then false 
    else true
  in  
  let locs = List.concat (List.map (fun c -> if(check_loc_in_all_assume c assume_sum) then [c] else []) locs) in
  let _ = Debug.info_pprint ("Final drop loc list: " ^ (str_of_drop_loc_lst locs)) no_pos in
  let new_hp_assumes = drop_process hp_assumes locs in
  (*find candidates in all assumes, if a case appears in all assmses => apply it*) 
  new_hp_assumes

and check_drop_para_hp_assume (hp_assume: CF.formula * CF.formula): drop_loc_lst =
  let(lhs,rhs) = hp_assume in
  let l1 = check_drop_para_hp_assume_a lhs rhs in
  let l2 = check_drop_para_hp_assume_a rhs lhs in
  l1@l2

and check_drop_para_hp_assume_a (f1: CF.formula) (f2: CF.formula): drop_loc_lst =
  let hds, hvs, hrs = get_hp_rel_formula f1 in
  List.concat (List.map (fun hr -> check_drop_each_pred hr f1 f2) hrs)

and check_drop_each_pred (r: (CP.spec_var * (CP.exp list) * loc))(f1: CF.formula) (f2: CF.formula): drop_loc_lst = 
  let (svar, el, l) = r in
  let _ = Debug.ninfo_pprint ("Check HeapPred:  " ^ (CP.name_of_spec_var svar)) no_pos in 
  (*check all args without type checking*)
  let rec helper (el: CP.exp list)(f1: CF.formula) (f2: CF.formula)(cloc: int): drop_loc_lst =
    if((List.length el) == 0) then [] 
    else (
      let l1 = check_drop_each_para (List.hd el) f1 f2 in
      if(l1) then (svar,cloc)::(helper (List.tl el) f1 f2 (cloc+1))
      else helper (List.tl el) f1 f2 (cloc+1)
    )
  in 
  let res = helper el f1 f2 0 in
  let _ = Debug.ninfo_pprint ("Drop loc list: " ^ (str_of_drop_loc_lst res)) no_pos in
  res

and check_drop_each_para (e: CP.exp)(f1: CF.formula) (f2: CF.formula): bool =
  match e with
    | CP.Var (sv,l) -> (
      let is_defined = check_spec_var_defined sv f1 in
      let is_used = check_spec_var_used sv f2 in
      let is_connected = check_spec_var_connected sv f1 f2 in
      is_defined || (not is_used && not is_connected)
    )
    | _ -> false

and check_spec_var_defined  (v: CP.spec_var)(f: CF.formula): bool = 
  let hds, hvs, hrs = get_hp_rel_formula f in
  match f with
    |CF.Base  ({CF.formula_base_pure = p1})
    |CF.Exists ({ CF.formula_exists_pure = p1}) -> (
      let eqNull1, eqNull2 =  List.split (MCP.ptr_equations_with_null p1) in
      let eqNulls = CP.remove_dups_svl (eqNull1@eqNull2) in
      let def_vs = (eqNulls) @ (List.map (fun hd -> hd.CF.h_formula_data_node) hds) @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs)  in
      let str = List.fold_left (fun a b ->  (CP.name_of_spec_var b ^ "," ^ a )) "" def_vs in
      let _ = Debug.ninfo_pprint ("Defined vars " ^ str) no_pos in
      let b = List.exists (fun c-> if(CP.eq_spec_var v c) then true else false) def_vs in
      if(b) then true 
      else false
    )
    |CF.Or f  -> report_error no_pos "not handle yet"

and check_spec_var_used  (v: CP.spec_var)(f: CF.formula): bool = 
  let hds, hvs, hrs = get_hp_rel_formula f in
  let eqNulls = match f with
    |CF.Base  ({CF.formula_base_pure = p1})
    |CF.Exists ({ CF.formula_exists_pure = p1}) -> (
      let eqNull1, eqNull2 =  List.split (MCP.ptr_equations_with_null p1) in
      CP.remove_dups_svl (eqNull1@eqNull2)
    )
    |CF.Or f  -> report_error no_pos "not handle yet"
  in
  let rhs_vs = (eqNulls) @ (List.map (fun hd -> hd.CF.h_formula_data_node) hds) @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs)  in
  let get_svars el = List.concat (List.map (fun c -> [CP.exp_to_spec_var c] ) el) in
  let rel_args =List.concat ( List.map (fun (_,el,_) -> get_svars el) hrs) in
  let rhs_vs = rhs_vs@rel_args in
  let str = List.fold_left (fun a b ->  (CP.name_of_spec_var b ^ "," ^ a )) "" rhs_vs in
  let _ = Debug.ninfo_pprint ("RHS vars " ^ str) no_pos in
  let b = List.exists (fun c-> if(CP.eq_spec_var v c) then true else false) rhs_vs in
  if(b) then true 
  else false


and check_spec_var_connected (v: CP.spec_var)(f: CF.formula)(f2:CF.formula): bool = 
  let hds, hvs, hrs = get_hp_rel_formula f in
  let hds = List.filter (fun c -> check_spec_var_used c.CF.h_formula_data_node f2) hds in
  let hvs = List.filter (fun c -> check_spec_var_used c.CF.h_formula_view_node f2) hvs in
  let node_args = (List.concat (List.map (fun hd -> hd.CF.h_formula_data_arguments) hds)) @ (List.concat(List.map (fun hv -> hv.CF.h_formula_view_arguments) hvs)) in
  let node_args = List.filter (fun c -> CP.is_node_typ c) node_args in
  let b = List.exists (fun c-> if(CP.eq_spec_var v c) then true else false) node_args in
  if(b) then true 
  else false
 
and drop_process (hp_assumes: (CF.formula * CF.formula) list) (drloc: drop_loc_lst): ( (CF.formula * CF.formula) list) =
  List.map (fun c -> drop_process_one_assume c drloc) hp_assumes

and drop_process_one_assume (hp_assume: CF.formula * CF.formula) (drlocs: drop_loc_lst): (CF.formula * CF.formula) =
  let rels, _ = List.split drlocs in
  let rec helper f drlocs = match f with
    | CF.Base fb -> CF.Base {fb with CF.formula_base_heap = filter_hp_rel_args fb.CF.formula_base_heap drlocs;}
    | CF.Or orf -> CF.Or {orf with CF.formula_or_f1 = helper orf.CF.formula_or_f1 drlocs;
                CF.formula_or_f2 = helper orf.CF.formula_or_f2 drlocs;}
    | CF.Exists fe -> CF.Exists {fe with CF.formula_exists_heap =  filter_hp_rel_args fe.CF.formula_exists_heap drlocs;}
  in 
  let f1 , f2 = hp_assume in
  ((helper f1 drlocs),(helper f2 drlocs))

and filter_hp_rel_args (hf: CF.h_formula) (drlocs: drop_loc_lst): CF.h_formula=
  let rels, _ = List.split drlocs in
  match hf with
    | CF.Star {CF.h_formula_star_h1 = hf1;
               CF.h_formula_star_h2 = hf2;
               CF.h_formula_star_pos = pos} ->
      let n_hf1 = filter_hp_rel_args hf1 drlocs in
      let n_hf2 = filter_hp_rel_args hf2 drlocs in
      (match n_hf1,n_hf2 with
        | (CF.HEmp,CF.HEmp) -> CF.HEmp
        | (CF.HEmp,_) -> n_hf2
        | (_,CF.HEmp) -> n_hf1
        | _ -> CF.Star {CF.h_formula_star_h1 = n_hf1;
			CF.h_formula_star_h2 = n_hf2;
			CF.h_formula_star_pos = pos}
      )
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
		CF.h_formula_conj_h2 = hf2;
		CF.h_formula_conj_pos = pos} ->
      let n_hf1 = filter_hp_rel_args hf1 drlocs in
      let n_hf2 = filter_hp_rel_args hf2 drlocs in
      CF.Conj { CF.h_formula_conj_h1 = n_hf1;
		CF.h_formula_conj_h2 = n_hf2;
		CF.h_formula_conj_pos = pos}
    | CF.Phase { CF.h_formula_phase_rd = hf1;
		 CF.h_formula_phase_rw = hf2;
		 CF.h_formula_phase_pos = pos} ->
      let n_hf1 = filter_hp_rel_args hf1 drlocs in
      let n_hf2 = filter_hp_rel_args hf2 drlocs in
      CF.Phase { CF.h_formula_phase_rd = n_hf1;
		 CF.h_formula_phase_rw = n_hf2;
		 CF.h_formula_phase_pos = pos} 
    | CF.DataNode hd -> hf
    | CF.ViewNode hv -> hf
    | CF.HRel (sv, args, l) -> if(List.exists (fun c-> CP.eq_spec_var c sv) rels) then 
	(
	  let locs = List.concat(List.map (fun (c, loc) -> if(CP.eq_spec_var c sv)then [loc] else []) drlocs)in
	  let rec helper args l = if(List.length args == 0) then [] 
	    else if(List.exists (fun c -> c == l) locs) then (helper (List.tl args) (l+1)) 
	    else (List.hd args)::(helper (List.tl args) (l+1))
	  in
	  let new_args = helper args 0 in 
	  CF.HRel (sv, new_args, l)
	)
      else hf
			  
    | CF.Hole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp -> hf

and collect_def_hp_lst_assume (hp_assumes: (CF.formula * CF.formula) list): ((CF.formula * CF.formula) list) * (rel_def list) = 
  (*return new assumes and defs*)
  (*
    main:::: for each hp_assume ==> collect_defs ==> concat defs
    collect_sef::: for each hprel ==> check welldefined ==> concat def
    check_well_defined::: for each para => check well defined para ==> AND
    check wdefined para:: null, well_node ==> OR
    well_node: each node para => AND
    checkeach nodepara => null, well node, appear in Hrels==> OR
  *)
  let ass, defs = List.split (List.map collect_def_hp_assume hp_assumes) in
  (*check eq => new assume only to have new def*)
  Debug.info_hprint (add_str "DEFS COLLECTED ROUND 1: " (pr_list_ln string_of_def)) (List.concat defs) no_pos;
  let defs1 = get_def_by_substitute_lst_as hp_assumes in 
  (ass, (List.concat defs)@defs1)

and get_def_by_substitute_lst_as (hp_assumes: (CF.formula * CF.formula) list): (rel_def list) = 
  if(List.length hp_assumes < 2) then []
  else (
    let defs_head = List.concat (List.map (fun c -> get_def_by_substitute_two_as c (List.hd hp_assumes)) (List.tl hp_assumes)) in
    defs_head @ (get_def_by_substitute_lst_as (List.tl hp_assumes))
  )

and get_def_by_substitute_two_as  (hp_assume1: CF.formula * CF.formula)  (hp_assume2: CF.formula * CF.formula): (rel_def list) =
  let f11, f12 = hp_assume1 in
  let f21, f22 = hp_assume2 in
  Debug.ninfo_hprint (add_str "Test equiv formulae: " ( Cprinter.string_of_hprel_lhs_rhs)) (f11,f22) no_pos;
  let b1, mt1 = CEQ.checkeq_formulas [] f11 f22 [[]] in
  Debug.ninfo_hprint (add_str "Test equiv formulae: " ( Cprinter.string_of_hprel_lhs_rhs)) (f12,f21) no_pos;
  let b2, mt2 = CEQ.checkeq_formulas [] f12 f21 [[]] in
  let defs1 = if(b1) then (
    Debug.info_hprint (add_str "NEW ASSUME: " ( Cprinter.string_of_hprel_lhs_rhs)) (f12,f21) no_pos;
    let f_1 = CEQ.subst_with_mt (List.hd mt1) f12 in 
    (*let f_2 = CEQ.subst_with_mt (List.hd mt1) f21 in *) (*not sound, should check if both var occur*)
    Debug.info_hprint (add_str "NEW ASSUME AFTER CHANGE VARS: " ( Cprinter.string_of_hprel_lhs_rhs)) (f_1,f21) no_pos;
    let (a, b) =  collect_def_hp_assume (f_1,f21) in 
    b
  )
    else (
      let _ = Debug.info_pprint ("NO EQ------- ") no_pos in 
      []
    )
  in
  let defs2 = if(b2) then  (
    let f_1 = CEQ.subst_with_mt (List.hd mt1) f11 in 
   (* let f_2 = CEQ.subst_with_mt (List.hd mt1) f22 in *)
    Debug.info_hprint (add_str "NEW ASSUME AFTER CHANGE VAR: " ( Cprinter.string_of_hprel_lhs_rhs)) (f_1,f22) no_pos;
    let (a,b) = collect_def_hp_assume (f_1,f22) in
    b
  )
    else (
      let _ = Debug.info_pprint ("NO EQ------- ") no_pos in 
      []
    )
  in
  defs1@defs2

and collect_def_hp_assume(hp_assume: CF.formula * CF.formula): (CF.formula * CF.formula) * (rel_def list) =
  Debug.info_hprint (add_str "Check assume: " ( Cprinter.string_of_hprel_lhs_rhs)) hp_assume no_pos;
  let f1,f2 = hp_assume in
  let hds1, hvs1, hrs1 = get_hp_rel_formula f1 in
  let hds2, hvs2, hrs2 = get_hp_rel_formula f2 in
  let rels = hrs1@hrs2 in
  let defs1 = List.concat (List.map (fun c-> check_well_defined_rel c f1) rels) in
  let defs2 = List.concat (List.map (fun c-> check_well_defined_rel c f2) rels) in
 (* let filter_def def rels= (
    let (cat, rel, f) = def in
    (List.exists (fun c -> CP.eq_spec_var (CP.name_of_rel_form rel) (CP.name_of_rel_form c)) rels)
  )
  in 
  let fdef1= List.map (fun c -> (filter_def c hrs1)) defs1 in
  let new_f1 = equal_simplify_assume hp_assume fdef1 in
  let fdef2= List.map (fun c -> (filter_def c hrs2)) defs1 in
  let new_f2 = equal_simplify_assume hp_assume fdef2 in*)
  (hp_assume,defs1@defs2)

and check_well_defined_rel(rel: (CP.spec_var * (CP.exp list) * loc))(f: CF.formula): (rel_def list)=
  let sv, el, l = rel in
  let _ = Debug.info_pprint ("Check Relation:  " ^ (CP.name_of_spec_var sv)) no_pos in
  let bs = List.map (fun c -> check_well_defined_rel_para rel  c f) el in
  let b = if(List.exists (fun c -> c) bs) then true else false in
  if(b) then (
    let _ = Debug.info_pprint ("This relation is well define:  " ^ (CP.name_of_spec_var sv)) no_pos in
    [(find_hp_rel_define rel f false)] 
  )
  else (
    let _ = Debug.info_pprint ("This relation is not well define: " ^ (CP.name_of_spec_var sv)) no_pos in
    []
  )

(*
and check_well_defined_rel(rel: (CP.spec_var * (CP.exp list) * loc))(hp_assume: CF.formula * CF.formula): (rel_def list)=
  let sv, el, l = rel in
  let _ = Debug.info_pprint ("Check Relation:  " ^ (CP.name_of_spec_var sv)) no_pos in
  let bs = List.map (fun c -> check_well_defined_rel_para rel  c hp_assume) el in
  let b = if(List.exists (fun c -> c) bs) then true else false in
  if(b) then (
    let _ = Debug.info_pprint ("This relation is well define:  " ^ (CP.name_of_spec_var sv)) no_pos in
    [(find_hp_rel_define rel hp_assume false)] 
  )
  else (
    let _ = Debug.info_pprint ("This relation is not well define: " ^ (CP.name_of_spec_var sv)) no_pos in
    []
  )
*)

and check_well_defined_rel_para(rel: (CP.spec_var * (CP.exp list) * loc))(ex: CP.exp)(f: CF.formula): bool = 
  match ex with
    | CP.Var (sv,l) -> check_well_defined_spec_var rel sv f
    | _ -> report_error no_pos "not handle yet"

(*
and check_well_defined_rel_para(rel: (CP.spec_var * (CP.exp list) * loc))(ex: CP.exp)(hp_assume: CF.formula * CF.formula): bool = 
  match ex with
    | CP.Var (sv,l) -> check_well_defined_spec_var rel sv hp_assume
    | _ -> report_error no_pos "not handle yet"

*)

and find_all_null (f: CF.formula) : (CP.spec_var list)=
  match f with
    |CF.Base  ({CF.formula_base_pure = p1})
    |CF.Exists ({ CF.formula_exists_pure = p1}) -> (
      let eqNull1, eqNull2 =  List.split (MCP.ptr_equations_with_null p1) in
      CP.remove_dups_svl (eqNull1@eqNull2)
    )
    |CF.Or f  -> report_error no_pos "not handle yet"

and check_well_defined_spec_var (rel: (CP.spec_var * (CP.exp list) * loc)) (sv: CP.spec_var)(f:  CF.formula): bool = 
 let _ = Debug.info_pprint ("Check Para: " ^ (CP.name_of_spec_var sv)) no_pos in
  let nulls = find_all_null f in
  if(List.exists (fun c -> CP.eq_spec_var sv c) nulls) then true
  else (
    let hds, hvs, hrs = get_hp_rel_formula f in
    let nodes = (List.map (fun hd ->  hd.CF.h_formula_data_node) hds) @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs)in
    if(List.exists (fun c -> CP.eq_spec_var sv c) nodes) then (
      let res1 = try( 
 	let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_data_node sv) hds in
	let args = hd.CF.h_formula_data_arguments in
	let args = List.filter (fun c -> CP.is_node_typ c) args in
	let bs = List.map (fun c -> check_well_defined_node_args rel c f) args in
	(not (List.exists (fun c-> not c) bs))
      )
	with e -> false
      in 
      if(not (res1)) then (
	try( 
	  let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_view_node sv) hvs in
	  let args = hd.CF.h_formula_view_arguments in
	  let args = List.filter (fun c -> CP.is_node_typ c) args in
	  let bs = List.map (fun c -> check_well_defined_node_args rel c f) args in
	  (not (List.exists (fun c-> not c) bs))
	)
	with e -> false
      )
      else true
    )
    else false
  )

(*
and check_well_defined_spec_var (rel: (CP.spec_var * (CP.exp list) * loc)) (sv: CP.spec_var)(hp_assume: CF.formula * CF.formula): bool = 
 let _ = Debug.info_pprint ("Check Para: " ^ (CP.name_of_spec_var sv)) no_pos in
  let f1, f2 = hp_assume in
  let nulls = (find_all_null f1) @ (find_all_null f2) in
  if(List.exists (fun c -> CP.eq_spec_var sv c) nulls) then true
  else (
    let hds1, hvs1, hrs1 = get_hp_rel_formula f1 in
    let hds2, hvs2, hrs2 = get_hp_rel_formula f2 in
    let hds = hds1@hds2 in
    let hvs = hvs1@hvs2 in
    let nodes = (List.map (fun hd ->  hd.CF.h_formula_data_node) hds) @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs)in
    if(List.exists (fun c -> CP.eq_spec_var sv c) nodes) then (
      let res1 = try( 
	let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_data_node sv) hds in
	let args = hd.CF.h_formula_data_arguments in
	let args = List.filter (fun c -> CP.is_node_typ c) args in
	let bs = List.map (fun c -> check_well_defined_node_args rel c hp_assume) args in
	(not (List.exists (fun c-> not c) bs))
      )
	with e -> false
      in 
      if(not (res1)) then (
	try( 
	  let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_view_node sv) hvs in
	  let args = hd.CF.h_formula_view_arguments in
	  let args = List.filter (fun c -> CP.is_node_typ c) args in
	  let bs = List.map (fun c -> check_well_defined_node_args rel c hp_assume) args in
	  (not (List.exists (fun c-> not c) bs))
	)
	with e -> false
      )
      else true
    )
    else false
  )
*)

and check_well_defined_node_args (rel: (CP.spec_var * (CP.exp list) * loc))(arg: CP.spec_var)(f: CF.formula): bool = 
let _ = Debug.info_pprint ("Check arg: " ^ (CP.name_of_spec_var arg)) no_pos in
(*not handle case ocurr in hprel yet*)
  let hds, hvs, hrs = get_hp_rel_formula f in
  let helper arg hr rel = (
    let rel_name,_,_ = rel in
    let rel_name_in_f,el,l = hr in
    if(CP.eq_spec_var rel_name rel_name_in_f) then(
      let svs = List.map (fun e -> CP.exp_to_spec_var e) el in
      List.exists (fun c -> CP.eq_spec_var arg c) svs 
    )
    else false
  )
  in
  let bs = List.map (fun c -> helper arg c rel) hrs in 
  let occur_in_rel = List.exists (fun c-> c) bs in
  if(occur_in_rel) then true 
  else check_well_defined_spec_var rel arg f

(*
and check_well_defined_node_args (rel: (CP.spec_var * (CP.exp list) * loc))(arg: CP.spec_var)(hp_assume: CF.formula * CF.formula): bool = 
let _ = Debug.info_pprint ("Check arg: " ^ (CP.name_of_spec_var arg)) no_pos in
  let f1, f2 = hp_assume in
(*not handle case ocurr in hprel yet*)
  let hds1, hvs1, hrs1 = get_hp_rel_formula f1 in
  let hds2, hvs2, hrs2 = get_hp_rel_formula f2 in
  let hrs = hrs1@hrs2 in
  let helper arg hr rel = (
    let rel_name,_,_ = rel in
    let rel_name_in_f,el,l = hr in
    if(CP.eq_spec_var rel_name rel_name_in_f) then(
      let svs = List.map (fun e -> CP.exp_to_spec_var e) el in
      List.exists (fun c -> CP.eq_spec_var arg c) svs 
    )
    else false
  )
  in
  let bs = List.map (fun c -> helper arg c rel) hrs in 
  let occur_in_rel = List.exists (fun c-> c) bs in
  if(occur_in_rel) then true 
  else check_well_defined_spec_var rel arg hp_assume
*)

and equal_simplify_assume (f: CF.formula) (defs: rel_def list): CF.formula = 
  let rels = List.map (fun (a,b,c) -> b) defs in
  let helper f rels= 
   match f with
    | CF.Base fb -> CF.Base {fb with CF.formula_base_heap =  filter_hp_rel_hf fb.CF.formula_base_heap rels;}
    | CF.Or orf -> CF.Or {orf with CF.formula_or_f1 = filter_spec_var orf.CF.formula_or_f1  rels;
      CF.formula_or_f2 = filter_spec_var orf.CF.formula_or_f2  rels;}
    | CF.Exists fe -> CF.Exists {fe with CF.formula_exists_heap =  filter_hp_rel_hf fe.CF.formula_exists_heap rels;}
  in
  f

and  filter_hp_rel_hf (hf: CF.h_formula) (rels: CP.spec_var list): CF.h_formula =
  let helper arg hr = (
    let rel_name_in_f,el,l = hr in
    let svs = List.map (fun e -> CP.exp_to_spec_var e) el in
    List.exists (fun c -> CP.eq_spec_var arg c) svs 
  )
  in
  match hf with
    | CF.Star {CF.h_formula_star_h1 = hf1;
               CF.h_formula_star_h2 = hf2;
               CF.h_formula_star_pos = pos} ->
      let n_hf1 = filter_spec_var_a hf1 rels in
      let n_hf2 = filter_spec_var_a hf2 rels in
      (match n_hf1,n_hf2 with
        | (CF.HEmp,CF.HEmp) -> CF.HEmp
        | (CF.HEmp,_) -> n_hf2
        | (_,CF.HEmp) -> n_hf1
        | _ -> CF.Star {CF.h_formula_star_h1 = n_hf1;
			CF.h_formula_star_h2 = n_hf2;
			CF.h_formula_star_pos = pos}
      )
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
		CF.h_formula_conj_h2 = hf2;
		CF.h_formula_conj_pos = pos} ->
      let n_hf1 = filter_spec_var_a hf1 rels in
      let n_hf2 = filter_spec_var_a hf2 rels in
      CF.Conj { CF.h_formula_conj_h1 = n_hf1;
		CF.h_formula_conj_h2 = n_hf2;
		CF.h_formula_conj_pos = pos}
    | CF.Phase { CF.h_formula_phase_rd = hf1;
		 CF.h_formula_phase_rw = hf2;
		 CF.h_formula_phase_pos = pos} ->
      let n_hf1 = filter_spec_var_a hf1 rels in
      let n_hf2 = filter_spec_var_a hf2 rels in
      CF.Phase { CF.h_formula_phase_rd = n_hf1;
		 CF.h_formula_phase_rw = n_hf2;
		 CF.h_formula_phase_pos = pos} 
    | CF.DataNode _ 
    | CF.ViewNode _ -> hf
    | CF.HRel hr -> if(List.exists (fun c-> c) (List.map (fun d -> helper d hr) rels)) then CF.HEmp else hf
    | CF.Hole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp -> hf

and find_hp_rel_define (rel: (CP.spec_var * (CP.exp list) * loc))(f: CF.formula)(rel_remanining: bool): rel_def=
  let sv, el, l = rel in
  let vars = List.map CP.exp_to_spec_var el in
  let nulls = find_all_null f in
  let hds, hvs, hrs = get_hp_rel_formula f in
  let helper arg hr= (
    let rel_name_in_f,el,l = hr in
    let svs = List.map (fun e -> CP.exp_to_spec_var e) el in
    if(List.exists (fun c -> CP.eq_spec_var arg c) svs) then
      List.filter (fun c -> not(CP.eq_spec_var arg c)) svs
    else []
  )
  in
  let nodes = (List.map (fun hd ->  hd.CF.h_formula_data_node) hds) @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) in
  (*check if in rel?*)
  let rec add_args vs sv = 
    if(List.exists (fun c -> CP.eq_spec_var c sv) vs) then vs else(
      if(List.exists (fun c -> CP.eq_spec_var sv c) nodes) then (
	try( 
	  let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_data_node sv) hds in
	  let args = hd.CF.h_formula_data_arguments in
	  let args = List.filter (fun c -> CP.is_node_typ c) args in
	  let args = List.filter (fun c -> not(List.exists (fun d-> (CP.eq_spec_var d c)) vs))  args in
	  let new_sv =  List.fold_left (fun a b -> (add_args a b)@a) [] args in (*List.concat(List.map add_args args) in*)
	  let str = List.fold_left (fun a b ->  (CP.name_of_spec_var b ^ "," ^ a )) "" args in
	  let _ = Debug.info_pprint ("check arg of node: " ^ str) no_pos in
	  sv::new_sv
	)
	with e -> (
	  try( 
	    let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_view_node sv) hvs in
	    let args = hd.CF.h_formula_view_arguments in
	    let args = List.filter (fun c -> CP.is_node_typ c) args in
	    let args = List.filter (fun c -> (List.exists (fun d-> not(CP.eq_spec_var d c))vs)) args in
	    let new_sv =  List.fold_left (fun a b -> (add_args a b)@a) [] args in (*List.concat(List.map add_args args) in*)
	    sv::new_sv
	  )
	  with e -> [sv]
	)
      )
      else
	(
	  if(CP.is_node_typ sv) then(
	    (*check if in rel args => add all node *)
	    let args = List.concat( List.map (fun c -> (helper sv c)) hrs) in
	    let args =  List.filter (fun c -> CP.is_node_typ c) args in
	    let args = List.filter (fun c -> (List.exists (fun d-> (CP.eq_spec_var d c))vs)) args in
	    let new_sv =  List.fold_left (fun a b -> (add_args a b)@a) [] args in
	    sv::new_sv
	  )
	  else []
	)
    )
  in
  let svs = List.fold_left (fun a b -> (add_args a b)@a) [] vars in
  let str = List.fold_left (fun a b ->  (CP.name_of_spec_var b ^ "," ^ a )) "" svs in
  let _ = Debug.info_pprint ("Relevent vars, good luck to me " ^ str) no_pos in
  let f2 = filter_spec_var f svs in
  (CP.RelDefn sv, rel,f2) 

(*
and find_hp_rel_define (rel: (CP.spec_var * (CP.exp list) * loc))(hp_assume: CF.formula * CF.formula)(rel_remanining: bool): rel_def=
  let sv, el, l = rel in
  let f1, f2 = hp_assume in
  let vars = List.map CP.exp_to_spec_var el in
  let nulls = (find_all_null f1) @ (find_all_null f2) in
  let hds1, hvs1, hrs1 = get_hp_rel_formula f1 in
  let hds2, hvs2, hrs2 = get_hp_rel_formula f2 in
  let hds = hds1@hds2 in
  let hvs = hvs1@hvs2 in
  let hrs = hrs1@hrs2 in
  let helper arg hr= (
    let rel_name_in_f,el,l = hr in
    let svs = List.map (fun e -> CP.exp_to_spec_var e) el in
    if(List.exists (fun c -> CP.eq_spec_var arg c) svs) then
      List.filter (fun c -> not(CP.eq_spec_var arg c)) svs
    else []
  )
  in
  let nodes = (List.map (fun hd ->  hd.CF.h_formula_data_node) hds) @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) in
  (*check if in rel?*)
  let rec add_args vs sv = 
    if(List.exists (fun c -> CP.eq_spec_var c sv) vs) then vs else(
      if(List.exists (fun c -> CP.eq_spec_var sv c) nodes) then (
	try( 
	  let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_data_node sv) hds in
	  let args = hd.CF.h_formula_data_arguments in
	  let args = List.filter (fun c -> CP.is_node_typ c) args in
	  let args = List.filter (fun c -> not(List.exists (fun d-> (CP.eq_spec_var d c)) vs))  args in
	  let new_sv =  List.fold_left (fun a b -> (add_args a b)@a) [] args in (*List.concat(List.map add_args args) in*)
	  let str = List.fold_left (fun a b ->  (CP.name_of_spec_var b ^ "," ^ a )) "" args in
	  let _ = Debug.info_pprint ("check arg of node: " ^ str) no_pos in
	  sv::new_sv
	)
	with e -> (
	  try( 
	    let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_view_node sv) hvs in
	    let args = hd.CF.h_formula_view_arguments in
	    let args = List.filter (fun c -> CP.is_node_typ c) args in
	    let args = List.filter (fun c -> (List.exists (fun d-> not(CP.eq_spec_var d c))vs)) args in
	    let new_sv =  List.fold_left (fun a b -> (add_args a b)@a) [] args in (*List.concat(List.map add_args args) in*)
	    sv::new_sv
	  )
	  with e -> [sv]
	)
      )
      else
	(
	  if(CP.is_node_typ sv) then(
	    (*check if in rel args => add all node *)
	    let args = List.concat( List.map (fun c -> (helper sv c)) hrs) in
	    let args =  List.filter (fun c -> CP.is_node_typ c) args in
	    let args = List.filter (fun c -> (List.exists (fun d-> (CP.eq_spec_var d c))vs)) args in
	    let new_sv =  List.fold_left (fun a b -> (add_args a b)@a) [] args in
	    sv::new_sv
	  )
	  else []
	)
    )
  in
  let svs = List.fold_left (fun a b -> (add_args a b)@a) [] vars in
  let str = List.fold_left (fun a b ->  (CP.name_of_spec_var b ^ "," ^ a )) "" svs in
  let _ = Debug.info_pprint ("Relevent vars, good luck to me " ^ str) no_pos in
  let f12 = filter_spec_var f1 svs in
  let f22 = filter_spec_var f2 svs in
  Debug.info_hprint (add_str ("Defination candidates of  " ^ (CP.name_of_spec_var sv)^ " : " ) ( Cprinter.string_of_hprel_lhs_rhs)) (f12,f22) no_pos;
  (CP.RelDefn sv, rel,f2) 
*)

and filter_spec_var (f: CF.formula) (relevent_vars: CP.spec_var list): CF.formula =
  match f with
    | CF.Base fb -> CF.Base {fb with CF.formula_base_heap = filter_spec_var_a fb.CF.formula_base_heap relevent_vars;
      CF.formula_base_pure = filter_spec_var_b fb.CF.formula_base_pure relevent_vars;}
    | CF.Or orf -> CF.Or {orf with CF.formula_or_f1 = filter_spec_var orf.CF.formula_or_f1  relevent_vars;
      CF.formula_or_f2 = filter_spec_var orf.CF.formula_or_f2  relevent_vars;}
    | CF.Exists fe -> CF.Exists {fe with CF.formula_exists_pure = filter_spec_var_b fe.CF.formula_exists_pure  relevent_vars;}

and filter_spec_var_a(hf: CF.h_formula) (relevent_vars: CP.spec_var list): CF.h_formula =
  let helper arg hr = (
    let rel_name_in_f,el,l = hr in
    let svs = List.map (fun e -> CP.exp_to_spec_var e) el in
    List.exists (fun c -> CP.eq_spec_var arg c) svs 
  )
  in
  match hf with
    | CF.Star {CF.h_formula_star_h1 = hf1;
               CF.h_formula_star_h2 = hf2;
               CF.h_formula_star_pos = pos} ->
      let n_hf1 = filter_spec_var_a hf1 relevent_vars in
      let n_hf2 = filter_spec_var_a hf2 relevent_vars in
      (match n_hf1,n_hf2 with
        | (CF.HEmp,CF.HEmp) -> CF.HEmp
        | (CF.HEmp,_) -> n_hf2
        | (_,CF.HEmp) -> n_hf1
        | _ -> CF.Star {CF.h_formula_star_h1 = n_hf1;
			CF.h_formula_star_h2 = n_hf2;
			CF.h_formula_star_pos = pos}
      )
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
		CF.h_formula_conj_h2 = hf2;
		CF.h_formula_conj_pos = pos} ->
      let n_hf1 = filter_spec_var_a hf1 relevent_vars in
      let n_hf2 = filter_spec_var_a hf2 relevent_vars in
      CF.Conj { CF.h_formula_conj_h1 = n_hf1;
		CF.h_formula_conj_h2 = n_hf2;
		CF.h_formula_conj_pos = pos}
    | CF.Phase { CF.h_formula_phase_rd = hf1;
		 CF.h_formula_phase_rw = hf2;
		 CF.h_formula_phase_pos = pos} ->
      let n_hf1 = filter_spec_var_a hf1 relevent_vars in
      let n_hf2 = filter_spec_var_a hf2 relevent_vars in
      CF.Phase { CF.h_formula_phase_rd = n_hf1;
		 CF.h_formula_phase_rw = n_hf2;
		 CF.h_formula_phase_pos = pos} 
    | CF.DataNode hd -> if(List.exists (fun c-> CP.eq_spec_var c (hd.CF.h_formula_data_node)) relevent_vars) then hf else CF.HEmp 
    | CF.ViewNode hv -> if(List.exists (fun c-> CP.eq_spec_var c (hv.CF.h_formula_view_node)) relevent_vars) then hf else CF.HEmp
    | CF.HRel hr -> if(List.exists (fun c-> c) (List.map (fun d -> helper d hr) relevent_vars)) then hf else CF.HEmp
    | CF.Hole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp -> CF.HEmp

and filter_spec_var_b(mf: MCP.mix_formula) (relevent_vars: CP.spec_var list): MCP.mix_formula =
  match mf with
    | MCP.MemoF mp -> mf
    | MCP.OnePF f -> MCP.OnePF (CP.filter_var f relevent_vars)
