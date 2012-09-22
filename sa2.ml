open Globals
open Gen

module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq

type hp_def = CP.rel_cat * CF.formula * CF.formula
type hp_para = CP.spec_var * int
type par_def =  CF.formula * CF.formula * CF.formula
let str_of_para_loc (ploc: hp_para): string = 
  let (a,b) = ploc in
  "(" ^ (CP.name_of_spec_var a) ^ ", " ^ (string_of_int b) ^ ")"

let str_of_para_loc_lst (plocs: hp_para list): string = 
  let rec helper(plocs: hp_para list): string = match plocs with 
    |[] ->""
    |[x] -> str_of_para_loc x
    |x::y -> (str_of_para_loc x) ^ ", " ^ (helper y)
  in
  "[" ^ (helper plocs) ^ "]"

let eq_para_loc (l1: hp_para)(l2: hp_para):bool=
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

(*input: constrs
  output: definitions*)
let rec simplify_lst_constrs(constrs: (CF.formula * CF.formula) list): (hp_def list) = 
(*
  input: constrs: (formula * formula) list
  output: definitions: (formula * formula) list
*)
Debug.ninfo_hprint (add_str "INPUT: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) constrs no_pos;
  let constrs = elim_redundant_paras_lst_constr constrs in 
  Debug.ninfo_hprint (add_str "AFTER DROP: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) constrs no_pos;
  let constrs, par_defs = collect_partial_definitions constrs in
  Debug.info_hprint (add_str "PARTIAL DEFINITIONS: " (pr_list_ln Cprinter.string_of_par_def)) par_defs no_pos;
  Debug.ninfo_hprint (add_str "\nAFTER COLLECT PARTIAL DEFINITIONS: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) constrs no_pos;
  (*VP: TO DO: before split: gather fully definitions + filter constraints*)
  let sub_constrs, split_tb = collect_sub_constrs_by_split constrs in
  let sub_constrs, par_defs2 = collect_partial_definitions sub_constrs in
  Debug.info_hprint (add_str "SUBCONSTRS FROM SPLIT: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) sub_constrs no_pos;
  Debug.info_hprint (add_str "PARTIAL DEFINITIONS OF SUBCONSTRS: " (pr_list_ln Cprinter.string_of_par_def)) par_defs2 no_pos;
  []

and elim_redundant_paras_lst_constr constrs =
  let drlocs = List.map check_dropable_paras_constr constrs in
  let get_rels constr =
    let (f1,f2) = constr in
    let svs1  = get_hp_rel_name_formula f1 in
    let svs2  = get_hp_rel_name_formula f2 in
    svs1@svs2
  in
  let hrels = List.map (fun a -> (get_rels a)) constrs in
  let rels_info = List.combine drlocs hrels in 
  let locs = List.concat drlocs in
  let rec check_dupl (locs: hp_para list) = match locs with
    | [] -> []
    | [x] -> [x]
    | x::y -> if(List.exists (fun c -> eq_para_loc x c) y)then check_dupl(y) else x::check_dupl(y) 
  in 
  let locs = check_dupl locs in
  let check_loc_in_all_constr loc rels_info =
    let rec helper  (loc: hp_para)(as1: (hp_para list) * (CP.spec_var list)): bool =
      let v,l = loc in 
      let (drlocs, svs) = as1 in
      if((List.exists (fun c -> eq_para_loc loc c) drlocs)|| not (List.exists (fun c -> CP.eq_spec_var v c) svs)) then true
      else false
    in 
    if(List.exists (fun c -> not(helper loc c)) rels_info) then false 
    else true
  in  
  let locs = List.concat (List.map (fun c -> if(check_loc_in_all_constr c rels_info) then [c] else []) locs) in
  let _ = Debug.ninfo_pprint ("Final drop para list: " ^ (str_of_para_loc_lst locs)) no_pos in
  let new_constrs = drop_process constrs locs in
  (*find candidates in all assumes, if a case appears in all assmses => apply it*) 
  new_constrs

and check_dropable_paras_constr(constr: CF.formula * CF.formula):(hp_para list) =
  Debug.ninfo_hprint (add_str "CONSTRAINT: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) [constr] no_pos;
  let(lhs,rhs) = constr in
  let l1 = check_dropable_paras_RHS rhs in
  let l2 = check_dropable_paras_LHS lhs rhs in
  (*VP: TO DO: with paras that appear in both sides, need check in both sides*)
  l1@l2

and check_dropable_paras_RHS f = 
  (*RHS: dropable if para have just partial defined or more*)
  let hds, hvs, hrs = get_hp_rel_formula f in
  let check_dropable_each_para para f =
    match para with
      | CP.Var (sv,l) -> is_defined_pointer sv f []
      | _ -> false
  in
  let check_dropable_each_pred hr f =
    let (svar, el, l) = hr in
    let _ = Debug.ninfo_pprint ("Check HeapPred:  " ^ (CP.name_of_spec_var svar)) no_pos in 
    let rec helper (el: CP.exp list)(f: CF.formula)(cloc: int): (hp_para list) =
      if((List.length el) == 0) then [] 
      else (
	let l1 = check_dropable_each_para (List.hd el) f in
	if(l1) then (svar,cloc)::(helper (List.tl el) f (cloc+1))
	else helper (List.tl el) f (cloc+1)
      )
    in 
    let res = helper el f 0 in
    let _ = Debug.ninfo_pprint ("Drop loc list: " ^ (str_of_para_loc_lst res)) no_pos in
    res
  in
  List.concat (List.map (fun hr -> check_dropable_each_pred hr f) hrs)
    
and check_dropable_paras_LHS f1 f2: (hp_para list)= 
  let hds, hvs, hrs = get_hp_rel_formula f1 in
  let check_dropable_each_para hr para f1 f2 =
    match para with
      | CP.Var (sv,l) -> (is_well_defined_pointer hr sv f1 []) || (is_not_used sv (f1,f2)) 
      | _ -> false
  in
  let check_dropable_each_pred hr f1 f2 =
    let (svar, el, l) = hr in
    let _ = Debug.ninfo_pprint ("Check HeapPred:  " ^ (CP.name_of_spec_var svar)) no_pos in 
    let rec helper hr (el: CP.exp list)(f1: CF.formula) (f2: CF.formula)(cloc: int): hp_para list =
      if((List.length el) == 0) then [] 
      else (
	let l1 = check_dropable_each_para hr (List.hd el) f1 f2 in
	if(l1) then (svar,cloc)::(helper hr (List.tl el) f1 f2 (cloc+1))
	else helper hr (List.tl el) f1 f2 (cloc+1)
      )
    in 
    let res = helper hr el f1 f2 0 in
    let _ = Debug.ninfo_pprint ("Drop loc list: " ^ (str_of_para_loc_lst res)) no_pos in
    res
  in
  List.concat (List.map (fun hr -> check_dropable_each_pred hr f1 f2) hrs)

and is_defined_pointer sv f defined_hps=
  (*is a pointer first*) 
  let def_pointers = find_defined_pointers f defined_hps in
  (CP.is_node_typ sv)&&(List.exists (fun c -> CP.eq_spec_var sv c) def_pointers)

and find_defined_pointers f defined_hps=
  let nulls = find_all_null f in
  let hds, hvs, hrs = get_hp_rel_formula f in
  let nodes = (List.map (fun hd ->  hd.CF.h_formula_data_node) hds) @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) in
  (*VP: TO DO: find pointer that is para of defined hp*)  
  nulls@nodes

and is_well_defined_pointer hr sv f defined_hps = 
  (*is a pointer first*) 
  let is_wdef = check_well_defined_pointers hr sv f defined_hps in
  (CP.is_node_typ sv) && is_wdef

and check_well_defined_pointers self_hr sv f defined_hps =
  let nulls = find_all_null f in
  let _ = Debug.ninfo_pprint ("Check well defined: " ^ (CP.name_of_spec_var sv)) no_pos in
  if(List.exists (fun c -> CP.eq_spec_var sv c) nulls) then true
  else( (*VP: TO DO: is in defined hps*)
    let hds, hvs, hrs = get_hp_rel_formula f in
    (*check if appear in defined_hps*)
    let helper arg hr hp = (
      let hp_name,_,_ = hp in
      let hp_name_in_f,el,l = hr in
      if(CP.eq_spec_var hp_name hp_name_in_f) then(
	let svs = List.map (fun e -> CP.exp_to_spec_var e) el in
	List.exists (fun c -> CP.eq_spec_var arg c) svs 
      )
      else false
    )
    in
    let check_each_defined_hp arg hrs def_hp =(
	let bs = List.map (fun hr -> helper arg hr def_hp) hrs in 
	List.exists (fun c-> c) bs
    )
    in
    let cs = List.map (fun defined_hp -> check_each_defined_hp sv hrs defined_hp) defined_hps in 
    let occur_in_hp = List.exists (fun c-> c) cs in
    if(occur_in_hp) then true 
    else (
      (*node cases*)
      let nodes = (List.map (fun hd ->  hd.CF.h_formula_data_node) hds) @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs)in
      if(List.exists (fun c -> CP.eq_spec_var sv c) nodes) then (
	let res1 = try( 
	  let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_data_node sv) hds in
	  let args = hd.CF.h_formula_data_arguments in
	  let args = List.filter (fun c -> CP.is_node_typ c) args in
	  let bs = List.map (fun arg -> check_well_defined_node_arg self_hr arg f defined_hps) args in
	  (not (List.exists (fun c-> not c) bs))
	)
	  with e -> false
	in 
	if(not (res1)) then (
	  try( 
	    let hd = List.find (fun hd -> CP.eq_spec_var hd.CF.h_formula_view_node sv) hvs in
	    let args = hd.CF.h_formula_view_arguments in
	    let args = List.filter (fun c -> CP.is_node_typ c) args in
	    let bs = List.map (fun arg -> check_well_defined_node_arg self_hr arg f defined_hps) args in
	    (not (List.exists (fun c-> not c) bs))
	  )
	  with e -> false
	)
	else true
      )
      else false
    )
  )

and check_well_defined_node_arg self_hr arg f defined_hps =
  let _ = Debug.ninfo_pprint ("Check arg: " ^ (CP.name_of_spec_var arg)) no_pos in
  check_well_defined_pointers self_hr arg f (self_hr::defined_hps)

and is_not_used sv constr=
  let lhs, rhs = constr in
  (is_not_used_RHS sv rhs) && (is_not_connect_LHS sv rhs lhs)

and is_not_used_RHS (v: CP.spec_var)(f: CF.formula): bool = 
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
  if(b) then false 
  else true

and is_not_connect_LHS (v: CP.spec_var)(f: CF.formula)(f2:CF.formula): bool = 
  let hds, hvs, hrs = get_hp_rel_formula f in
  let hds = List.filter (fun c -> not(is_not_used_RHS c.CF.h_formula_data_node f2)) hds in
  let hvs = List.filter (fun c -> not(is_not_used_RHS c.CF.h_formula_view_node f2)) hvs in
  let node_args = (List.concat (List.map (fun hd -> hd.CF.h_formula_data_arguments) hds)) @ (List.concat(List.map (fun hv -> hv.CF.h_formula_view_arguments) hvs)) in
  let node_args = List.filter (fun c -> CP.is_node_typ c) node_args in
  let b = List.exists (fun c-> if(CP.eq_spec_var v c) then true else false) node_args in
  if(b) then false
  else true

and find_all_null (f: CF.formula) : (CP.spec_var list)=
  match f with
    |CF.Base  ({CF.formula_base_pure = p1})
    |CF.Exists ({ CF.formula_exists_pure = p1}) -> (
      let eqNull1, eqNull2 =  List.split (MCP.ptr_equations_with_null p1) in
      CP.remove_dups_svl (eqNull1@eqNull2)
    )
    |CF.Or f  -> report_error no_pos "not handle yet"

and drop_process (constrs: (CF.formula * CF.formula) list) (drloc: hp_para list): ( (CF.formula * CF.formula) list) =
  List.map (fun c -> drop_process_one_constr c drloc) constrs

and drop_process_one_constr (constr: CF.formula * CF.formula) (drlocs: hp_para list): (CF.formula * CF.formula) =
  let f1, f2 = constr in
  ((filter_hp_rel_args_f f1 drlocs),(filter_hp_rel_args_f f2 drlocs))


and filter_hp_rel_args_f (f: CF.formula) (drlocs: hp_para list) =
  let rels, _ = List.split drlocs in
  let rec helper f drlocs = match f with
    | CF.Base fb -> CF.Base {fb with CF.formula_base_heap = filter_hp_rel_args fb.CF.formula_base_heap drlocs;}
    | CF.Or orf -> CF.Or {orf with CF.formula_or_f1 = helper orf.CF.formula_or_f1 drlocs;
                CF.formula_or_f2 = helper orf.CF.formula_or_f2 drlocs;}
    | CF.Exists fe -> CF.Exists {fe with CF.formula_exists_heap =  filter_hp_rel_args fe.CF.formula_exists_heap drlocs;}
  in 
  helper f drlocs

and filter_hp_rel_args (hf: CF.h_formula) (drlocs: hp_para list): CF.h_formula=
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
	  if((List.length new_args) == 0) then CF.HEmp
	  else CF.HRel (sv, new_args, l)
	)
      else hf
			  
    | CF.Hole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp -> hf

and collect_partial_definitions constrs: ((CF.formula * CF.formula) list) * (par_def list) =
  let constrs, par_defs = List.split (List.map collect_par_defs_one_constr constrs) in
  (*let tmp_constrains, par_defs *)
  let defs1 = get_def_by_substitute_constrs constrs in (*VP: TO DO: copy, have not normaliza yet*)
  (constrs,defs1@(List.concat par_defs))

and collect_par_defs_one_constr constr =
  let lhs, rhs = constr in
  let hds, hvs, hrs = get_hp_rel_formula lhs in
  
  let check_well_defined_exp hr e f = 
    match e with
      | CP.Var (sv,l) -> is_well_defined_pointer hr sv f []
      | _ -> report_error no_pos "not handle yet"
  in
  let check_well_defined_hp hp f = 
    let sv, el, l = hp in
    let bs = List.map (fun e -> check_well_defined_exp hp e f) el in
    if(List.exists (fun c -> c) bs) then true else false
  in
  
  let check_each_hr hr lhs rhs = 
    if(check_well_defined_hp hr lhs) then (*CASE 1: H and its def is both in LHS*)
      (
	let _ = Debug.ninfo_pprint ("CASE1 ") no_pos in
	let def = find_hp_def hr lhs false in
	let sv,el,loc = hr in
	let f1 = CF.formula_of_heap (CF.HRel(sv, el, loc)) no_pos in
	let f3 = CF.formula_of_heap CF.HEmp no_pos in
	([(f1,def,f3)],[hr])
      )
    else if(check_well_defined_hp hr rhs) then  (*CASE 1: H in LHS and its def is in RHS*)
	(
	  let _ = Debug.ninfo_pprint ("CASE2 ") no_pos in
	  let def = find_hp_def hr rhs true in
	  let sv,el,loc = hr in
	  let f1 = CF.formula_of_heap (CF.HRel(sv, el, loc)) no_pos in
	  let f2 = find_hp_def hr lhs false in (*remaining*)
	  ([(f1,f2,def)],[])
	)
      else (
	let _ = Debug.ninfo_pprint ("NO CASE ") no_pos in
	([],[])
      ) 
  in
  let par_defs_lst,hr_lst = List.split (List.map (fun hr -> check_each_hr hr lhs rhs) hrs) in
  let par_defs = List.concat par_defs_lst in
  let drop_hps = List.concat hr_lst in
  let new_lhs = List.fold_left (fun a drop_hp -> filter_hp drop_hp a) lhs drop_hps in
  ((new_lhs,rhs),par_defs)

and find_hp_def hr f (hold_rel: bool): CF.formula = 
  let sv, el, l = hr in
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
	  let _ = Debug.ninfo_pprint ("check arg of node: " ^ str) no_pos in
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
  let _ = Debug.ninfo_pprint ("Relevent vars, good luck to me " ^ str) no_pos in
  let f2 = filter_spec_var f svs in
  if(hold_rel)then f2
  else (filter_hp hr f2)

and filter_hp hp (f:CF.formula): CF.formula = 
  let sv, el, loc = hp in
  let rec collect_drlocs sv el n= 
    match el with
      |[]  -> []
      |x::y -> (sv,n)::(collect_drlocs sv y (n+1))
  in
  let drlocs = collect_drlocs sv el 0 in
  let _ = Debug.ninfo_pprint ("List drop locs " ^ (str_of_para_loc_lst drlocs)) no_pos in
  filter_hp_rel_args_f f drlocs

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

and get_def_by_substitute_constrs (constrs: (CF.formula * CF.formula) list): (par_def list) = 
  if(List.length constrs < 2) then []
  else (
    let defs_head = List.concat (List.map (fun c -> get_def_by_substitute_two_constr c (List.hd constrs)) (List.tl constrs)) in
    defs_head @ (get_def_by_substitute_constrs (List.tl constrs))
  )

and get_def_by_substitute_two_constr  (constr1: CF.formula * CF.formula)  (constr2: CF.formula * CF.formula): (par_def list) =
  let f11, f12 = constr1 in
  let f21, f22 = constr2 in
  Debug.ninfo_hprint (add_str "Test equiv formulae: " ( Cprinter.string_of_hprel_lhs_rhs)) (f11,f22) no_pos;
  let b1, mt1 = CEQ.checkeq_formulas [] f11 f22 in
  Debug.ninfo_hprint (add_str "Test equiv formulae: " ( Cprinter.string_of_hprel_lhs_rhs)) (f12,f21) no_pos;
  let b2, mt2 = CEQ.checkeq_formulas [] f12 f21 in
  let defs1 = if(b1) then (
    let f_1 = CEQ.subst_with_mt (List.hd mt1) f12 in 
(*change vars*)
    (*let f_2 = CEQ.subst_with_mt (List.hd mt1) f21 in *) (*not sound, should check if both var occur*)
    Debug.ninfo_hprint (add_str "NEW ASSUME AFTER CHANGE VARS: " ( Cprinter.string_of_hprel_lhs_rhs)) (f21,f_1) no_pos;
    let (a, b) =  collect_par_defs_one_constr (f21,f_1) in 
    b
  )
    else []
  in
  let defs2 = if(b2) then  (
    let f_1 = CEQ.subst_with_mt (List.hd mt1) f11 in 
    Debug.ninfo_hprint (add_str "NEW ASSUME AFTER CHANGE VAR: " ( Cprinter.string_of_hprel_lhs_rhs)) (f_1,f22) no_pos;
    let (a,b) = collect_par_defs_one_constr (f_1,f22) in
    b
  )
    else []
  in
  defs1@defs2

and collect_sub_constrs_by_split constrs = 
  (*split only hp that stands alone in RHS and have more than one parameter *)
  let split_tb = [] in
  let splits = List.concat (List.map (fun constr -> get_split_candi constr) constrs) in (*hr list*)
  let get_split_map split piv = (
    let tb, defs = List.split piv in
    let svs, mtbs = List.split tb in
    let sv,el,l = split in
    if(List.exists (fun c -> CP.eq_spec_var sv c) svs) then []
    else(
      let rec helper sv el n =
	match el with
	  | [] -> []
	  |x::y -> (
	    let newhp = CP.fresh_spec_var sv in
	    ((newhp, [n]),CF.HRel(newhp,[x],no_pos))::(helper sv y (n+1))
	  )
      in
      let new_tb, defs = List.split(helper sv el 0)in
      let split_def = CF.formula_of_heap ( (List.fold_left (fun piv def -> CF.mkStarH piv def no_pos) (List.hd defs) (List.tl defs))) no_pos in
      let new_def = (CP.RelDefn sv,CF.formula_of_heap (CF.HRel(sv,el,l)) no_pos,split_def)in
      [((sv,new_tb),new_def)]
    (*add defs here*)
    )
  ) 
  in
  let split_tb, defs = List.split( List.fold_left (fun piv split -> (get_split_map split piv)@piv ) [] splits) in
  let defs = List.map (fun (_,a2,a3)-> (a2,a3)) defs in
  Debug.info_hprint (add_str "DEF OF SPLITS: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) defs no_pos;
  let svs, mtbs = List.split split_tb in
  Debug.info_hprint (add_str "SPLIT: " (pr_list_ln CP.name_of_spec_var)) svs no_pos;
  let new_constrs, sub_constrs = List.split (List.map (fun constr -> process_split constr split_tb) constrs) in
  Debug.ninfo_hprint (add_str "NEW CONSTRAINTS: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) new_constrs no_pos;
  Debug.ninfo_hprint (add_str "SUB CONSTRAINTS: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) (List.concat sub_constrs) no_pos;
  ((List.concat sub_constrs),split_tb)

and process_split constr split_tb = 
  Debug.ninfo_hprint (add_str "Process split: " ( Cprinter.string_of_hprel_lhs_rhs)) constr no_pos;
  let svs, mtbs = List.split split_tb in
  let lhs, rhs = constr in
  let new_lhs = process_split_LHS lhs split_tb in
  Debug.ninfo_hprint (add_str "Process split LHS: " ( Cprinter.string_of_hprel_lhs_rhs)) (lhs, new_lhs) no_pos;
  (*if RHS:stand alone hp => split and create new sub constrs else just split like lhs*)
  let collect_subconstr lhs subhp =
    let hrel = match subhp with
      |CF.HRel hr -> hr 
      |_ -> report_error no_pos "no case"
    in
    let def_of_subhp = find_hp_def hrel lhs true in
    let hp_to_f = CF.formula_of_heap subhp no_pos in
    (def_of_subhp, hp_to_f)
  in 
  try(
    let this_hp = get_split_candi constr in
    try(
      let sub_hps = split_hp (List.hd this_hp) split_tb in (*List.hd for the only 1 hp here*)
      let subconstrs = List.map (fun subhp -> collect_subconstr new_lhs subhp) sub_hps in (*VP: TO DO: separate to 2 sub constr*)
      ((new_lhs,rhs), subconstrs)
    )
    with _ ->  ((new_lhs,rhs),[])
  )
  with _ -> (
    let new_rhs = process_split_LHS rhs split_tb in
    ((new_lhs,new_rhs),[])
  )

and process_split_LHS f split_tb = 
  match f with
    | CF.Base fb -> CF.Base {fb with CF.formula_base_heap = process_split_lhs_hf fb.CF.formula_base_heap split_tb;}
    | CF.Or orf -> CF.Or {orf with CF.formula_or_f1 = process_split_LHS orf.CF.formula_or_f1 split_tb;
                CF.formula_or_f2 = process_split_LHS orf.CF.formula_or_f2 split_tb;}
    | CF.Exists fe -> CF.Exists {fe with CF.formula_exists_heap =  process_split_lhs_hf fe.CF.formula_exists_heap split_tb;}
    
and process_split_lhs_hf hf split_tb = 
  match hf with
    | CF.Star {CF.h_formula_star_h1 = hf1;
               CF.h_formula_star_h2 = hf2;
               CF.h_formula_star_pos = pos} ->
      let n_hf1 = process_split_lhs_hf hf1 split_tb in
      let n_hf2 = process_split_lhs_hf hf2 split_tb in
      CF.Star {CF.h_formula_star_h1 = n_hf1;
	       CF.h_formula_star_h2 = n_hf2;
	       CF.h_formula_star_pos = pos}
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
		CF.h_formula_conj_h2 = hf2;
		CF.h_formula_conj_pos = pos} ->
      let n_hf1 = process_split_lhs_hf hf1 split_tb in
      let n_hf2 = process_split_lhs_hf hf2 split_tb in
      CF.Conj { CF.h_formula_conj_h1 = n_hf1;
		CF.h_formula_conj_h2 = n_hf2;
		CF.h_formula_conj_pos = pos}
    | CF.Phase { CF.h_formula_phase_rd = hf1;
		 CF.h_formula_phase_rw = hf2;
		 CF.h_formula_phase_pos = pos} ->
      let n_hf1 = process_split_lhs_hf hf1 split_tb in
      let n_hf2 = process_split_lhs_hf hf2 split_tb in
      CF.Phase { CF.h_formula_phase_rd = n_hf1;
		 CF.h_formula_phase_rw = n_hf2;
		 CF.h_formula_phase_pos = pos} 
    | CF.DataNode _
    | CF.ViewNode _ -> hf
    | CF.HRel hr ->(
      try
	(
	  let sub_hrs = split_hp hr split_tb in
	  (List.fold_left (fun piv subhr -> CF.mkStarH piv subhr no_pos) (List.hd sub_hrs) (List.tl sub_hrs))
	)
      with _ -> hf
    ) 
    | CF.Hole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp -> hf

and split_hp (hp: (CP.spec_var * CP.exp list * loc)) split_tb=
(*VP: TO DO: from hp -> subhps or not split*)
  let svs, mtbs = List.split split_tb in
  let sv,el,l = hp in
  let collect_params mapping el = 
    let subhp, locs = mapping in
    let rec helper el locs n = match el with
      |[] -> []
      |x::y -> if(List.exists (fun c -> c == n) locs) then x::(helper y locs (n+1)) else (helper y locs (n+1))
    in
    let params = helper el locs 0 in
    CF.HRel (subhp, params, no_pos)
  in
  if(List.exists (fun c -> CP.eq_spec_var sv c) svs) then
    try(
      let split_hp,mappings = (List.find (fun (c,mtb) -> CP.eq_spec_var sv c) split_tb) in 
      List.map (fun mapping -> collect_params mapping el) mappings
    )
    with _ -> report_error no_pos "no case"
  else (raise Not_found)

and get_only_hrel f = match f with 
  |CF.Base {CF.formula_base_heap = hf} -> (match hf with
      | CF.HRel hr -> hr
      | _ -> raise Not_found
  )
  |CF.Exists {CF.formula_exists_heap = hf} -> (match hf with
      | CF.HRel hr -> hr
      | _ -> raise Not_found
  )
  | CF.Or f  -> report_error no_pos "not handle yet"

and get_split_candi constr = 
    (*rhs is only hp with more than 1 param*)
  let lhs,rhs = constr in
  try(
      let hp = get_only_hrel rhs in
      let sv,el,l  = hp in
      if(List.length el >= 2) then [hp]
      else []
    )
  with _ -> []
