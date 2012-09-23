open Globals
open Gen

module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq

type hp_rel_def = CP.rel_cat * CF.formula * CF.formula
type hp_para = CP.spec_var * int
type par_def =  CF.formula * CF.formula * CF.formula

type par_def_w_name =  CP.spec_var * CF.formula * (CF.formula option) *
      (CF.formula option)

let str_of_para_loc (ploc: hp_para): string = 
  let (a,b) = ploc in
  "(" ^ (CP.name_of_spec_var a) ^ ", " ^ (string_of_int b) ^ ")"

let string_of_par_def pd=
  let pr = pr_triple Cprinter.prtt_string_of_formula
    Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula
  in pr pd

let string_of_par_def_w_name pd=
  let pr1 = !CP.print_sv in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = fun x -> match x with
    | None -> "None"
    | Some f -> pr2 f
  in
  let pr = pr_quad pr1 pr2 pr3 pr3 in
  pr pd

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

(**=================================**)

let rec elim_redundant_paras_lst_constr_x constrs =
  let drlocs = List.map check_dropable_paras_constr constrs in
  let get_rels constr =
    let (f1,f2) = constr in
    let svs1  = CF.get_hp_rel_name_formula f1 in
    let svs2  = CF.get_hp_rel_name_formula f2 in
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

and elim_redundant_paras_lst_constr hp_constrs =
let pr = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
Debug.ho_1 "elim_redundant_paras_lst_constr" pr pr (fun _ ->  elim_redundant_paras_lst_constr_x hp_constrs) hp_constrs

and check_dropable_paras_constr(constr: CF.formula * CF.formula):(hp_para list) =
  Debug.ninfo_hprint (add_str "CONSTRAINT: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) [constr] no_pos;
  let(lhs,rhs) = constr in
  let l1 = check_dropable_paras_RHS rhs in
  let l2 = check_dropable_paras_LHS lhs rhs in
  (*VP: TO DO: with paras that appear in both sides, need check in both sides*)
  l1@l2

and check_dropable_paras_RHS f = 
  (*RHS: dropable if para have just partial defined or more*)
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
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
  let hds, hvs, hrs = CF.get_hp_rel_formula f1 in
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
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
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
    let hds, hvs, hrs = CF.get_hp_rel_formula f in
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
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
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
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
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


(*==============*)
(*defined pointers list *
  for recursive constraint(HP name *
 parameter name list)*)
let rec find_defined_pointers_new_x f=
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
  let ( _,mix_f,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mix_f) in
  let eqNull1, eqNull2 =  List.split (MCP.ptr_equations_with_null mix_f) in
  let eqNulls = CP.remove_dups_svl (eqNull1@eqNull2) in
  (*defined vars=  + null + data + view*)
  let def_vs = (eqNulls) @ (List.map (fun hd -> hd.CF.h_formula_data_node) hds)
   @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) in
  (*find closed defined pointers set*)
  (* let def_vs0 = CP.remove_dups_svl def_vs in *)
  let def_vs = CP.remove_dups_svl (List.fold_left Infer.close_def def_vs eqs) in
  (*(HP name * parameter name list)*)
  let hp_paras = List.map
                (fun (id, exps, _) -> (id, List.concat (List.map CP.afv exps)))
                hrs in
  (def_vs, hp_paras, hrs, hds, hvs)

and find_defined_pointers_new f=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv pr1) in
  let pr3 = fun x -> Cprinter.string_of_h_formula (CF.HRel x) in
  let pr4 = fun (a1, a2, a3, a4, a5) ->
      let pr = pr_triple pr1 pr2 pr3 in pr (a1,a2,a3)  in
  Debug.ho_1 "find_defined_pointers_new" Cprinter.prtt_string_of_formula pr4
      (fun _ -> find_defined_pointers_new f) f

let rec collect_partial_definitions_x constrs: (par_def_w_name list) =
  let constrs, par_defs = List.split (List.map collect_par_defs_one_constr_new constrs) in
  
  (List.concat par_defs)

and collect_partial_definitions constrs: (par_def_w_name list) =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 =  pr_list_ln string_of_par_def_w_name in
   Debug.ho_1 "collect_partial_definitions" pr1 pr2 (fun _ -> collect_partial_definitions_x constrs) constrs
(*
let rec loop_up_ptr_args_data_node hd=
  (*data nodes*)
  let data_def =  Cast.look_up_data_def pos prog.Cast.prog_data_decls hd.CF.h_formula_data_name in
  (*get prototype of a node declaration*)
  let args = List.map (fun (t,_) -> t) data_def.Cast.data_fields in
  (*combine with actual areg*)
  let targs = List.combine args hd.CF.h_formula_data_arguments in
  (*get pointer*)
  snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs))

and loop_up_ptr_args_view_node hv=
  (*view node*)
  let view_def =  Cast.look_up_view_def pos prog.Cast.prog_view_decls hd.CF.h_formula_view_name in
  (*get prototype of a node declaration*)
  let args = List.map (fun (t,_) -> t) view_def.Cast.view_fields in
  (*combine with actual areg*)
  let targs = List.combine args hd.CF.h_formula_view_arguments in
  (*get pointer*)
  snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs))

and loop_up_ptr_args_one_node hd_nodes hv_nodes node_name=
  let rec look_up_data_node ls=
    match ls with
      | [] -> []
      | dn::ds -> if CP.eq_spec_var node_name dn.CF.h_formula_data_node then
            loop_up_ptr_args_data_node hd
          else look_up_data_node ds
  in
  let rec look_up_view_node ls=
    match ls with
      | [] -> []
      | dn::ds -> if CP.eq_spec_var node_name dn.CF.h_formula_view_node then
            loop_up_ptr_args_view_node hd
          else look_up_view_node ds
  in
  let ptrs = look_up_data_node hd_nodes in
  if ptrs = [] then look_up_view_node hv_nodes
  else ptrs

and loop_up_ptr_args hd_nodes hv_nodes node_names=
  let rec helper old_ptrs inc_ptrs=
    let new_ptrs = List.concat
      (List.map (loop_up_ptr_args_one_node hd_nodes hv_nodes) inc_ptrs) in
    let diff_ptrs = Gen.BList.difference_eq CP.eq_spec_var new_ptrs old_ptrs in
    if diff_ptrs = [] then old_ptrs
    else (helper (CP.remove_dups_eq CP.eq_spec_var (old_ptrs@inc_ptrs))
      (CP.remove_dups_eq CP.eq_spec_var diff_ptrs))
*)
and collect_par_defs_one_hp f (hrel, args) def_ptrs hrel_vars eq hd_nodes hv_nodes=
begin
  let rec eq_spec_var_list l1 l2=
    match l1,l2 with
      |[],[] -> true
      | v1::ls1,v2::ls2 ->
          if CP.eq_spec_var v1 v2 then
            eq_spec_var_list ls1 ls2
          else false
      | _ -> false
  in
  let rec remove_current_hrel ls r=
    match ls with
      | [] -> r
      | (hp,vars)::hs ->
          if CP.eq_spec_var hp hrel && eq_spec_var_list vars args then
            (r@hs)
          else remove_current_hrel hs (r@[(hp,vars)])
  in
  let rec lookup_recursive_para a hps=
    match hps with
      | [] -> false
      | (hrel1, args)::hs ->
          if (CP.eq_spec_var hrel hrel1) &&  (CP.mem_svl a args) then true
          else lookup_recursive_para a hs
  in
  let rec lookup_undef_args args undef_args=
    match args with
      | [] -> undef_args
      | a::ax -> if CP.mem_svl a def_ptrs then
            lookup_undef_args ax undef_args
          else begin
            let hrel_vars1 = remove_current_hrel hrel_vars [] in
            if lookup_recursive_para a hrel_vars1 then
              lookup_undef_args ax undef_args
            else
            lookup_undef_args ax undef_args@[a]
          end
  in
(*  let undef_args = lookup_undef_args args [] in
  if (List.length undef_args) = 0 then
    (*this hp is well defined, synthesize partial def*)
    let keep_ptrs = loop_up_ptr_args hd_nodes hv_nodes args in
    let check_neq_dnode dn2 dn1_name=
      not(CP.eq_spec_var dn1_name dn2.CF.h_formula_data_node)
    in
    let check_neq_vnode vn2 vn1_name=
    (*return subst of args and add in lhs*)
      not(CP.eq_spec_var vn1_name vn2.CF.h_formula_view_node)
    in
    let check_neq_hrelnode id ls=
      not (CP.mem_svl id ls)
    in
    let r = CF.drop_data_view_hrel_nodes f keep_ptrs keep_ptrs []
      check_neq_dnode check_neq_vnode check_neq_hrelnode in
    [r]
  else *)
    []
end

and collect_par_defs_one_constr_new_x constr =
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
	  let f2 = CF.formula_of_heap CF.HEmp no_pos in (*remaining*)
	  ([(f1,f2,def)],[])
	)
      else (
	let _ = Debug.ninfo_pprint ("NO CASE ") no_pos in
	([],[])
      )
  in
  let lhs, rhs = constr in
  let l_hds, l_hvs, l_hrs = CF.get_hp_rel_formula lhs in
  let r_hds, r_hvs, r_hrs = CF.get_hp_rel_formula rhs in
  (*find all defined pointer (null, nodes) and recursive defined parameters (HP, arg)*)
  let l_def_ptrs, l_hp_args_name,l_hrs,l_dnodes, l_vnodes = find_defined_pointers_new_x lhs in
  let r_def_ptrs, r_hp_args_name,r_hrs, r_dnodes, r_vnodes = find_defined_pointers_new_x lhs in
  (*for each hp constraint, check*)
  (* let par_defs_lst,hr_lst = List.split (List.map (fun hr -> check_each_hr hr lhs rhs) l_hrs) in *)
  (* let par_defs = List.concat par_defs_lst in *)
  (* let drop_hps = List.concat hr_lst in *)
  (* let new_lhs = List.fold_left (fun a drop_hp -> filter_hp drop_hp a) lhs drop_hps in *)
  ([(lhs,rhs)],[])

and collect_par_defs_one_constr_new constr =
  let pr1 = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln string_of_par_def_w_name in
  let pr4 = pr_list_ln pr1 in
  let pr3 = (pr_pair pr4 pr2) in
  Debug.ho_1 "collect_par_defs_one_constr_new" pr1 pr3
      (fun _ -> collect_par_defs_one_constr_new_x constr) constr


(*old*)
and find_hp_def hr f (hold_rel: bool): CF.formula = 
  let sv, el, l = hr in
  let vars = List.map CP.exp_to_spec_var el in
  let nulls = find_all_null f in
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
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

(*END OLD        *)

(* and get_def_by_substitute_constrs (constrs: (CF.formula * CF.formula) list): (par_def list) =  *)
(*   if(List.length constrs < 2) then [] *)
(*   else ( *)
(*     let defs_head = List.concat (List.map (fun c -> get_def_by_substitute_two_constr c (List.hd constrs)) (List.tl constrs)) in *)
(*     defs_head @ (get_def_by_substitute_constrs (List.tl constrs)) *)
(*   ) *)

(* and get_def_by_substitute_two_constr  (constr1: CF.formula * CF.formula)  (constr2: CF.formula * CF.formula): (par_def list) = *)
(*   let f11, f12 = constr1 in *)
(*   let f21, f22 = constr2 in *)
(*   Debug.ninfo_hprint (add_str "Test equiv formulae: " ( Cprinter.string_of_hprel_lhs_rhs)) (f11,f22) no_pos; *)
(*   let b1, mt1 = CEQ.checkeq_formulas [] f11 f22 in *)
(*   Debug.ninfo_hprint (add_str "Test equiv formulae: " ( Cprinter.string_of_hprel_lhs_rhs)) (f12,f21) no_pos; *)
(*   let b2, mt2 = CEQ.checkeq_formulas [] f12 f21 in *)
(*   let defs1 = if(b1) then ( *)
(*     let f_1 = CEQ.subst_with_mt (List.hd mt1) f12 in  *)
(* (\*change vars*\) *)
(*     (\*let f_2 = CEQ.subst_with_mt (List.hd mt1) f21 in *\) (\*not sound, should check if both var occur*\) *)
(*     Debug.ninfo_hprint (add_str "NEW ASSUME AFTER CHANGE VARS: " ( Cprinter.string_of_hprel_lhs_rhs)) (f_1,f21) no_pos; *)
(*     let (a, b) =  collect_par_defs_one_constr(f_1,f21) in  *)
(*     b *)
(*   ) *)
(*     else [] *)
(*   in *)
(*   let defs2 = if(b2) then  ( *)
(*     let f_1 = CEQ.subst_with_mt (List.hd mt1) f11 in  *)
(*     Debug.ninfo_hprint (add_str "NEW ASSUME AFTER CHANGE VAR: " ( Cprinter.string_of_hprel_lhs_rhs)) (f_1,f22) no_pos; *)
(*     let (a,b) = collect_par_defs_one_constr (f_1,f22) in *)
(*     b *)
(*   ) *)
(*     else [] *)
(*   in *)
(*   (defs1@defs2) *)

(*====================*)
let rec simplify_one_constr (lhs, rhs)=
  match lhs,rhs with
    | CF.Base lhs_b, CF.Base rhs_b ->
        let l,r = simplify_one_constr_b lhs_b rhs_b in
        (CF.Base l, CF.Base r)
    | _ -> report_error no_pos "sa.simplify_one_constr"

and simplify_one_constr_b_x lhs_b rhs_b=
  (*return subst of args and add in lhs*)
  let check_eq_data_node dn1 dn2=
    CP.eq_spec_var dn1.CF.h_formula_data_node dn2.CF.h_formula_data_node
  in
  let check_eq_view_node vn1 vn2=
    (*return subst of args and add in lhs*)
    CP.eq_spec_var vn1.CF.h_formula_view_node vn2.CF.h_formula_view_node
  in
  let select_data_node dn1 dn2_name=
    CP.eq_spec_var dn1.CF.h_formula_data_node dn2_name
  in
  let select_view_node vn1 vn2_name=
    (*return subst of args and add in lhs*)
    CP.eq_spec_var vn1.CF.h_formula_view_node vn2_name
  in
  let check_eq_hrel_node  (rl1, args1 ,_)  (rl2, args2,_)=
    let rec helper l1 l2=
      match l1,l2 with
        | [],[] -> true
        | v1::vs1,v2::vs2 ->
            if CP.eq_spec_var v1 v2 then helper vs1 vs2
            else false
        | _ -> false
    in
    (*hp1 = hp2 and args1 = arg2*)
    let svs1 = List.concat (List.map CP.afv args1) in
    let svs2 = List.concat (List.map CP.afv args2) in
    (CP.eq_spec_var rl1 rl2) && (helper svs1 svs2)
  in
(*todo: drop unused pointers in LHS*)
  let lhs_b1 = lhs_b (* Infer.filter_irr_lhs_bf_hp lhs_b rhs_b *) in
(*pointers/hps matching LHS-RHS*)
  (*data nodes, view nodes, rel*)
  let l_hds, l_hvs, l_hrs = CF.get_hp_rel_bformula lhs_b1 in
  let r_hds, r_hvs, r_hrs = CF.get_hp_rel_bformula rhs_b in
  let matched_data_nodes = Gen.BList.intersect_eq check_eq_data_node l_hds r_hds in
  let matched_view_nodes = Gen.BList.intersect_eq check_eq_view_node l_hvs r_hvs in
  let matched_hrel_nodes = Gen.BList.intersect_eq check_eq_hrel_node l_hrs r_hrs in
  let hrels = List.map (fun (id,_,_) -> id) matched_hrel_nodes in
  Debug.ninfo_hprint (add_str "Matched HRel: " !CP.print_svl) hrels no_pos;
  let dnode_names = List.map (fun hd -> hd.CF.h_formula_data_node) matched_data_nodes in
  let vnode_names = List.map (fun hv -> hv.CF.h_formula_view_node) matched_view_nodes in
  let lhs_b2 = CF.drop_data_view_hrel_nodes_fb lhs_b1 select_data_node
    select_view_node CP.mem_svl dnode_names vnode_names hrels in
  let rhs_b2 = CF.drop_data_view_hrel_nodes_fb rhs_b select_data_node
    select_view_node CP.mem_svl dnode_names vnode_names hrels in
(*pure subformulas matching LHS-RHS: drop RHS*)
(lhs_b2, rhs_b2)

and simplify_one_constr_b lhs_b rhs_b=
  let pr = Cprinter.prtt_string_of_formula_base in
  Debug.no_2 "simplify_one_constr_b" pr pr (pr_pair pr pr)
      (fun _ _ -> simplify_one_constr_b_x lhs_b rhs_b) lhs_b rhs_b

let simplify_constrs_x constrs=
  List.map simplify_one_constr constrs

let simplify_constrs constrs=
   let pr = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  Debug.ho_1 "simplify_constrs" pr pr
      (fun _ -> simplify_constrs_x constrs) constrs


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

(*todo: rhs is only hp with more than 1 param*)
let get_hp_split_cands_x constrs =
  let helper (lhs,rhs)=
    try(
        let hp = get_only_hrel rhs in
        let sv,el,l  = hp in
        if(List.length el >= 2) then [(CF.HRel hp)]
        else []
    )
    with _ -> []
  in
  (List.concat (List.map helper constrs))

let get_hp_split_cands constrs =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln (Cprinter.string_of_hrel_formula) in
  Debug.ho_1 "get_hp_split_cands" pr1 pr2
  (fun _ -> get_hp_split_cands_x constrs) constrs

(*split one hp -> mutiple hp and produce corresponding heap formulas for substitution*)
let hp_split_x hps =
  (*each arg, create new hp and its corresponding HRel formula*)
  let helper1 l arg =
    let new_hp_name = Globals.hp_default_prefix_name ^ (string_of_int (Globals.fresh_int())) in
    let new_hp_sv = CP.SpecVar (HpT,new_hp_name, Unprimed) in
    (*should refresh arg*)
    (new_hp_sv, CF.HRel (new_hp_sv, [arg], l))
  in
  (*rhs is only hp with more than 1 parameter*)
  (*for each hp*)
  let helper (CF.HRel (sv,el,l)) =
    let hps = List.map (helper1 l) el in
    let new_hp_names,new_hrel_fs = List.split hps in
    let new_hrels_comb = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 l) (List.hd new_hrel_fs) (List.tl new_hrel_fs) in
    ((sv,new_hp_names),(CF.HRel (sv,el,l), new_hrels_comb))
  in
  let res = List.map helper hps in
  List.split res

let hp_split hps =
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = (pr_list (pr_pair pr1 pr2)) in
  let pr4 = Cprinter.string_of_h_formula in
  let pr5 = pr_list pr4 in
  let pr6 = pr_list (pr_pair pr4 pr4) in
   Debug.ho_1 "hp_split" pr5 (pr_pair pr3 pr6)
       (fun _ -> hp_split_x hps) hps

let subst_constr_with_new_hps hp_constrs hprel_subst=
  let helper (l_constr, r_constr)=
    (CF.subst_hrel_f l_constr hprel_subst, CF.subst_hrel_f r_constr hprel_subst)
  in
  List.map helper hp_constrs

(*return new contraints and hp split map *)
let split_hp_x  (hp_constrs: (CF.formula * CF.formula) list):
      ((CF.formula * CF.formula) list * (CP.spec_var*CP.spec_var list) list) =
  (*get hp candidates*)
  let split_cands = get_hp_split_cands hp_constrs in
  (*split  and get map*)
  let split_map,hprel_subst =  hp_split split_cands in
  (*subs old hrel by new hrels*)
  let new_constrs = subst_constr_with_new_hps hp_constrs hprel_subst in
  (*simplify constrs*)
  let simp_constrs = simplify_constrs new_constrs in
  (simp_constrs, split_map)

let split_hp (hp_constrs: (CF.formula * CF.formula) list):
      ((CF.formula * CF.formula) list * (CP.spec_var*CP.spec_var list) list) =
  let pr1 =  pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = !CP.print_sv in
  let pr3 = !CP.print_svl in
  let pr4 = pr_pair pr1 (pr_list (pr_pair pr2 pr3)) in
  Debug.ho_1 "split_hp" pr1 pr4
      (fun _ -> split_hp_x hp_constrs) hp_constrs

(*
  input: constrs: (formula * formula) list
  output: definitions: (formula * formula) list
*)
let infer_hp_x (hp_constrs: (CF.formula * CF.formula) list): (hp_rel_def list) =
  (*step 1: drop irr parameters*)
  let constrs = elim_redundant_paras_lst_constr hp_constrs in
  Debug.ninfo_hprint (add_str "AFTER DROP: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) constrs no_pos;
   (*step 1': split HP*)
  let constrs1, split_tb = split_hp constrs in
  (*step 3: pick partial definition*)
  let par_defs = collect_partial_definitions constrs1 in
  []

let infer_hp (hp_constrs: (CF.formula * CF.formula) list): (hp_rel_def list) =
  let pr = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr1 = pr_list Cprinter.string_of_hp_rel_def in
  Debug.ho_1 "infer_hp" pr pr1 (fun _ -> infer_hp_x hp_constrs) hp_constrs
