open Globals
open Gen

module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq
module TP = Tpdispatcher

type hp_rel_def = CP.rel_cat * CF.formula * CF.formula
type hp_para = CP.spec_var * int
type par_def =  CF.formula * CF.formula * CF.formula

(*hp_name * args * condition * lhs * rhs *)
type par_def_w_name =  CP.spec_var * CP.spec_var list * CF.formula * (CF.formula option) *
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
  let pr4 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = fun x -> match x with
    | None -> "None"
    | Some f -> pr2 f
  in
  let pr = pr_penta pr1 pr4 pr2 pr3 pr3 in
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
(*todo: how about null? is it defined?*)
let rec find_defined_pointers_raw prog f=
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
  let def_vs_wo_args = CP.remove_dups_svl ((List.fold_left Infer.close_def def_vs eqs)) in
  (def_vs_wo_args, hds, hvs, hrs, eqs)

and find_defined_pointers_after_preprocess prog def_vs_wo_args hds hvs hrs eqs predef_ptrs=
   let tmp = def_vs_wo_args in
  let def_vs = List.filter (check_node_args_defined prog (def_vs_wo_args@predef_ptrs) hds hvs) tmp in
  (*(HP name * parameter name list)*)
  let hp_paras = List.map
                (fun (id, exps, _) -> (id, List.concat (List.map CP.afv exps)))
                hrs in
  (def_vs, hp_paras, hds, hvs, eqs)

and find_defined_pointers_new_x prog f predef_ptrs=
  (* let hds, hvs, hrs = CF.get_hp_rel_formula f in *)
  (* let ( _,mix_f,_,_,_) = CF.split_components f in *)
  (* let eqs = (MCP.ptr_equations_without_null mix_f) in *)
  (* let eqNull1, eqNull2 =  List.split (MCP.ptr_equations_with_null mix_f) in *)
  (* let eqNulls = CP.remove_dups_svl (eqNull1@eqNull2) in *)
  (* (\*defined vars=  + null + data + view*\) *)
  (* let def_vs = (eqNulls) @ (List.map (fun hd -> hd.CF.h_formula_data_node) hds) *)
  (*  @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) in *)
  (* (\*find closed defined pointers set*\) *)
  (* (\* let def_vs0 = CP.remove_dups_svl def_vs in *\) *)
  (* let def_vs_wo_args = CP.remove_dups_svl ((List.fold_left Infer.close_def def_vs eqs)@predef_ptrs) in *)
  (* (\*check nodes'args are defined?*\) *)
  (* let tmp = def_vs_wo_args in  *)
  (* let def_vs = List.filter (check_node_args_defined prog def_vs_wo_args hds hvs) tmp in *)
  (* (\*(HP name * parameter name list)*\) *)
  (* let hp_paras = List.map *)
  (*               (fun (id, exps, _) -> (id, List.concat (List.map CP.afv exps))) *)
  (*               hrs in *)
  (* (def_vs, hp_paras, hds, hvs,eqs) *)
  let (def_vs, hds, hvs, hrs, eqs) = find_defined_pointers_raw prog f in
  find_defined_pointers_after_preprocess prog def_vs hds hvs hrs eqs predef_ptrs

and find_defined_pointers_new prog f predef_ptrs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv pr1) in
  (* let pr3 = fun x -> Cprinter.string_of_h_formula (CF.HRel x) in *)
  let pr4 = fun (a1, a2, _, _, _) ->
      let pr = pr_pair pr1 pr2 in pr (a1,a2)
  in
  Debug.no_2 "find_defined_pointers_new" Cprinter.prtt_string_of_formula pr1 pr4
      (fun _ _ -> find_defined_pointers_new_x prog f predef_ptrs) f predef_ptrs

(*should we mkAnd f1 f2*)
and find_defined_pointers_two_formulas_x prog f1 f2 predef_ptrs=
  let (def_vs1, hds1, hvs1, hrs1, eqs1) = find_defined_pointers_raw prog f1 in
  let (def_vs2, hds2, hvs2, hrs2, eqs2) = find_defined_pointers_raw prog f2 in
  find_defined_pointers_after_preprocess prog (def_vs1@def_vs2) (hds1@hds2) (hvs1@hvs2)
      (hrs2) (eqs1@eqs2) predef_ptrs

and find_defined_pointers_two_formulas prog f1 f2 predef_ptrs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv pr1) in
  (* let pr3 = fun x -> Cprinter.string_of_h_formula (CF.HRel x) in *)
  let pr4 = fun (a1, a2, _, _, _) ->
      let pr = pr_pair pr1 pr2 in pr (a1,a2)
  in
  Debug.no_3 "find_defined_pointers_two_formulas" Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula pr1 pr4
      (fun _ _ _ -> find_defined_pointers_two_formulas_x prog f1 f2 predef_ptrs) f1 f2 predef_ptrs

and check_node_args_defined prog def_svl hd_nodes hv_nodes dn_name=
  let arg_svl = loop_up_ptr_args_one_node prog hd_nodes hv_nodes dn_name in
  let diff_svl = Gen.BList.difference_eq CP.eq_spec_var arg_svl def_svl in
  if diff_svl = [] then true
  else false

and loop_up_ptr_args_data_node prog hd=
  (*data nodes*)
  let data_def =  Cast.look_up_data_def no_pos prog.Cast.prog_data_decls hd.CF.h_formula_data_name in
  (*get prototype of a node declaration*)
  let args = List.map (fun (t,_) -> t) data_def.Cast.data_fields in
  (*combine with actual areg*)
  let targs = List.combine args hd.CF.h_formula_data_arguments in
  (*get pointer*)
  snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs))

(* let loop_up_ptr_args_view_node prog hv= *)
(*   (\*view node*\) *)
(*   let view_def =  Cast.look_up_view_def no_pos prog.Cast.prog_view_decls hv.CF.h_formula_view_name in *)
(*   (\*get prototype of a node declaration*\) *)
(*   let args = List.map (fun (t,_) -> t) view_def.Cast.view_fields in *)
(*   (\*combine with actual areg*\) *)
(*   let targs = List.combine args hd.CF.h_formula_view_arguments in *)
(*   (\*get pointer*\) *)
(*   snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs)) *)

and loop_up_ptr_args_one_node prog hd_nodes hv_nodes node_name=
  let rec look_up_data_node ls=
    match ls with
      | [] -> []
      | dn::ds -> if CP.eq_spec_var node_name dn.CF.h_formula_data_node then
            loop_up_ptr_args_data_node prog dn
          else look_up_data_node ds
  in
  (* let rec look_up_view_node ls= *)
  (*   match ls with *)
  (*     | [] -> [] *)
  (*     | dn::ds -> if CP.eq_spec_var node_name dn.CF.h_formula_view_node then *)
  (*           loop_up_ptr_args_view_node prog hd *)
  (*         else look_up_view_node ds *)
  (* in *)
  let ptrs = look_up_data_node hd_nodes in
  (* if ptrs = [] then look_up_view_node hv_nodes *)
  (* else *) ptrs

let loop_up_ptr_args prog hd_nodes hv_nodes node_names=
  let rec helper old_ptrs inc_ptrs=
    let new_ptrs = List.concat
      (List.map (loop_up_ptr_args_one_node prog hd_nodes hv_nodes) inc_ptrs) in
    let diff_ptrs = Gen.BList.difference_eq CP.eq_spec_var new_ptrs old_ptrs in
    if diff_ptrs = [] then old_ptrs
    else (helper (Gen.BList.remove_dups_eq CP.eq_spec_var (old_ptrs@inc_ptrs))
      (Gen.BList.remove_dups_eq CP.eq_spec_var diff_ptrs))
  in
  helper node_names node_names

(*for computing partial def*)
let rec lookup_undef_args args undef_args def_ptrs=
  match args with
    | [] -> undef_args
    | a::ax -> if CP.mem_svl a def_ptrs then (*defined: omit*)
          lookup_undef_args ax undef_args def_ptrs
        else (*undefined *)
          lookup_undef_args ax (undef_args@[a]) def_ptrs

let check_neq_dnode dn2 dn1_name=
      not(CP.eq_spec_var dn1_name dn2.CF.h_formula_data_node)

let check_neq_vnode vn2 vn1_name=
      not(CP.eq_spec_var vn1_name vn2.CF.h_formula_view_node)

let check_neq_hrelnode id ls=
      not (CP.mem_svl id ls)
(*END for computing partial def*)

(*check_partial_def_eq: to remove duplicate and identify terminating condition*)
let check_partial_def_eq (hp1, args1, cond1, olhs1, orhs1) (hp2, args2, cond2, olhs2, orhs2)=
  (*form a subst*)
  let subst = List.combine args1 args2 in
  let checkeq_w_option of1 of2=
    match of1, of2 with
      | None,None -> true
      | Some _, None -> false
      | None, Some _ -> false
      | Some f1, Some f2 ->
          (*subs*)
          let f1_subst = CF.subst subst f1 in
          let r,_ (*map*) =  CEQ.checkeq_formulas [] f1_subst f2 in
          r
  in
  (CP.eq_spec_var hp1 hp2) && (checkeq_w_option olhs1 olhs2) &&
      (checkeq_w_option orhs1 orhs2)

(*collect partial def ---> hp*)
let collect_par_defs_one_side_one_hp prog f (hrel, args) def_ptrs hrel_vars eq hd_nodes hv_nodes=
begin
  let undef_args = lookup_undef_args args [] def_ptrs in
  if (List.length undef_args) = 0 then
    (*this hp is well defined, synthesize partial def*)
    let keep_ptrs = loop_up_ptr_args prog hd_nodes hv_nodes args in
    let r = CF.drop_data_view_hrel_nodes f check_neq_dnode check_neq_vnode
      check_neq_hrelnode keep_ptrs keep_ptrs []
    in
    [(hrel, args, r, Some r, None)]
  else
    []
end

(* (\*collect hp ---> partial def *\) *)
(* let collect_par_defs_two_side_one_hp prog f (hrel, args) def_ptrs hrel_vars eq hd_nodes hv_nodes= *)
(* begin *)
(*   let undef_args = lookup_undef_args args [] def_ptrs in *)
(*   if (List.length undef_args) = 0 then *)
(*     (\*this hp is well defined, synthesize partial def*\) *)
(*     let keep_ptrs = loop_up_ptr_args prog hd_nodes hv_nodes args in *)
(*     let r = CF.drop_data_view_hrel_nodes f check_neq_dnode check_neq_vnode *)
(*       check_neq_hrelnode keep_ptrs keep_ptrs [] *)
(*     in *)
(*     [(hrel, args, r, Some r, None)] *)
(*   else *)
(*     [] *)
(* end *)

let collect_par_defs_recursive_hp_x prog lhs rhs (hrel, args) def_ptrs hrel_vars eq hd_nodes hv_nodes=
  (* let rec eq_spec_var_list l1 l2= *)
  (*   match l1,l2 with *)
  (*     |[],[] -> true *)
  (*     | v1::ls1,v2::ls2 -> *)
  (*         if CP.eq_spec_var v1 v2 then *)
  (*           eq_spec_var_list ls1 ls2 *)
  (*         else false *)
  (*     | _ -> false *)
  (* in *)
  (* let rec remove_current_hrel ls r= *)
  (*   match ls with *)
  (*     | [] -> r *)
  (*     | (hrel1,vars)::hs -> *)
  (*         if CP.eq_spec_var hrel1 hrel && eq_spec_var_list vars args then *)
  (*           (r@hs) *)
  (*         else remove_current_hrel hs (r@[(hrel1,vars)]) *)
  (* in *)
  (* let rec lookup_recursive_para hps a= *)
  (*   match hps with *)
  (*     | [] -> false *)
  (*     | (hrel1, args1)::hs -> *)
  (*         if (CP.eq_spec_var hrel hrel1) &&  (CP.mem_svl a args1) then true *)
  (*         else lookup_recursive_para hs a *)
  (* in *)
  let build_partial_def ()=
    let keep_ptrs = loop_up_ptr_args prog hd_nodes hv_nodes args in
    let plhs = CF.drop_data_view_hrel_nodes lhs check_neq_dnode check_neq_vnode
      check_neq_hrelnode keep_ptrs keep_ptrs [hrel] in
     let prhs = CF.drop_data_view_hrel_nodes rhs check_neq_dnode check_neq_vnode
      check_neq_hrelnode keep_ptrs keep_ptrs [hrel] in
    [(hrel , args ,plhs, Some plhs, Some prhs) ]
  in
  let undef_args = lookup_undef_args args [] (def_ptrs) in
  if undef_args = [] then (build_partial_def())
  else []

let collect_par_defs_recursive_hp prog lhs rhs (hrel, args) def_ptrs hrel_vars eq hd_nodes hv_nodes=
  let pr1 = !CP.print_svl in
  let pr2 = (pr_pair !CP.print_sv pr1) in
  let pr3 = pr_list_ln string_of_par_def_w_name in
  Debug.no_1 "collect_par_defs_recursive_hp" pr2 pr3
      (fun  _ -> collect_par_defs_recursive_hp_x prog lhs rhs (hrel, args)
          def_ptrs hrel_vars eq hd_nodes hv_nodes) (hrel, args)

let rec collect_par_defs_one_constr_new_x prog (lhs, rhs) =
  let rec get_rec_pair_hps ls (hrel1, arg1)=
    match ls with
      | [] -> []
      | (hrel2, arg2)::ss -> if CP.eq_spec_var hrel1 hrel2 then [((hrel1, arg1), (hrel2, arg2))]
          else get_rec_pair_hps ss (hrel1, arg1)
  in
  (*find all defined pointer (null, nodes) and recursive defined parameters (HP, arg)*)
  let l_def_ptrs, l_hp_args_name,l_dnodes, l_vnodes,leqs = find_defined_pointers_new prog lhs [] in
  (*should mkAnd lhs*rhs?*)
  let r_def_ptrs, r_hp_args_name, r_dnodes, r_vnodes, reqs = find_defined_pointers_two_formulas prog lhs rhs [] in
  (*CASE 1: formula --> hp*)
  (*remove dup hp needs to be process*)
  let check_hp_arg_eq (hp1, args1) (hp2, args2)=
    let rec eq_spec_var_list l1 l2=
      match l1,l2 with
        |[],[] -> true
        | v1::ls1,v2::ls2 ->
            if CP.eq_spec_var v1 v2 then
              eq_spec_var_list ls1 ls2
            else false
        | _ -> false
    in
    ((CP.eq_spec_var hp1 hp2) && (eq_spec_var_list args1 args2))
  in
  let total_hps = (Gen.BList.remove_dups_eq check_hp_arg_eq (l_hp_args_name@r_hp_args_name)) in
  let lpdefs = List.concat (List.map (fun hrel ->
      collect_par_defs_one_side_one_hp prog lhs hrel
          l_def_ptrs (l_hp_args_name@r_hp_args_name) leqs l_dnodes l_vnodes) total_hps) in
  (*CASE32: todo: hp --> formula*)

  (*CASE 3: recursive contraints*)
  let rec_pair_hps = List.concat (List.map (get_rec_pair_hps l_hp_args_name) r_hp_args_name) in
   (*for debugging*)
  (* let pr1 = (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let pr2 = pr_list_ln (pr_pair pr1 pr1) in *)
  (* Debug.info_hprint (add_str "recursive pair: " (pr2)) rec_pair_hps no_pos; *)
  (*END for debugging*)
  let new_constrs, rec_pdefs =
    if rec_pair_hps = [] then
     (*drop constraints that have one hp after collect partial def*)
      let new_constrs=
        if (List.length total_hps) <= 1 then []
        else [(lhs,rhs)]
      in (new_constrs, [])
    else
      let helper ((hp1,args1),(hp2,args2))=
        (*recompute defined ptrs*)
         let l_def_ptrs, _,_, _,_ = find_defined_pointers_new prog lhs args2 in
         (*should mkAnd lhs*rhs?*)
         let r_def_ptrs, _, _, _, _ = find_defined_pointers_two_formulas prog lhs rhs args2 in
        let r1 = collect_par_defs_recursive_hp prog lhs rhs (hp1,args1)
          (l_def_ptrs@r_def_ptrs)  (l_hp_args_name@r_hp_args_name) (leqs@reqs)
          (l_dnodes@r_dnodes) (l_vnodes@r_vnodes) in
        if r1 = [] then
          (*recompute defined ptrs*)
          let l_def_ptrs, _,_, _,_ = find_defined_pointers_new prog lhs args1 in
         (*should mkAnd lhs*rhs?*)
          let r_def_ptrs, _, _, _, _ = find_defined_pointers_two_formulas prog lhs rhs args1 in
          collect_par_defs_recursive_hp prog lhs rhs (hp2,args2)
              (l_def_ptrs@r_def_ptrs)  (l_hp_args_name@r_hp_args_name) (leqs@reqs)
              (l_dnodes@r_dnodes) (l_vnodes@r_vnodes)
        else r1
      in
      let rec_pdefs = List.concat (List.map helper rec_pair_hps) in
      (*drop constraints that have one hp after collect partial def*)
      let new_constrs=
        let num_hp = (List.length total_hps) in
        let num_pair_rec_hp = (List.length rec_pair_hps) in
        if (num_hp - num_pair_rec_hp) <= 1 then []
        else [(lhs,rhs)]
      in (new_constrs, rec_pdefs)
  in
  (new_constrs,lpdefs @ rec_pdefs)

and collect_par_defs_one_constr_new prog constr =
  let pr1 = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln string_of_par_def_w_name in
  let pr4 = pr_list_ln pr1 in
  let pr3 = (pr_pair pr4 pr2) in
  Debug.no_1 "collect_par_defs_one_constr_new" pr1 pr3
      (fun _ -> collect_par_defs_one_constr_new_x prog constr) constr

(* - collect partial def
  - simplify: remove constaints which have <= 1 hp
*)
let rec collect_partial_definitions_x prog constrs: ((CF.formula*CF.formula) list * par_def_w_name list) =
  let simpl_constrs, par_defs = List.split (List.map (collect_par_defs_one_constr_new prog) constrs) in
  (List.concat simpl_constrs, List.concat par_defs)

and collect_partial_definitions prog constrs: ((CF.formula*CF.formula) list * par_def_w_name list) =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 =  pr_list_ln string_of_par_def_w_name in
   Debug.no_1 "collect_partial_definitions" pr1 (pr_pair pr1 pr2)
 (fun _ -> collect_partial_definitions_x prog constrs) constrs


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
  let _ = Debug.ninfo_pprint ("Relevent vars: " ^ str) no_pos in
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
 (*todo: drop unused pointers in LHS*)
  let lhs_b1 = lhs_b (* Infer.filter_irr_lhs_bf_hp lhs_b rhs_b *) in
(*pointers/hps matching LHS-RHS*)
  (*data nodes, view nodes, rel*)
  let l_hds, l_hvs, l_hrs = CF.get_hp_rel_bformula lhs_b1 in
  let r_hds, r_hvs, r_hrs = CF.get_hp_rel_bformula rhs_b in
  let matched_data_nodes = Gen.BList.intersect_eq check_eq_data_node l_hds r_hds in
  let matched_view_nodes = Gen.BList.intersect_eq check_eq_view_node l_hvs r_hvs in
  let matched_hrel_nodes = Gen.BList.intersect_eq CF.check_eq_hrel_node l_hrs r_hrs in
  let hrels = List.map (fun (id,_,_) -> id) matched_hrel_nodes in
  Debug.ninfo_hprint (add_str "Matched HRel: " !CP.print_svl) hrels no_pos;
  let dnode_names = List.map (fun hd -> hd.CF.h_formula_data_node) matched_data_nodes in
  let vnode_names = List.map (fun hv -> hv.CF.h_formula_view_node) matched_view_nodes in
  let lhs_b2 = CF.drop_data_view_hrel_nodes_fb lhs_b1 select_data_node
    select_view_node CP.mem_svl dnode_names vnode_names hrels in
  let rhs_b2 = CF.drop_data_view_hrel_nodes_fb rhs_b select_data_node
    select_view_node CP.mem_svl dnode_names vnode_names hrels in
 (*remove duplicate pure formulas*)
  let lhs_b3 = {lhs_b2 with CF.formula_base_pure = MCP.mix_of_pure
          (CP.remove_redundant (MCP.pure_of_mix lhs_b2.CF.formula_base_pure))} in
  let rhs_b3 = {rhs_b2 with CF.formula_base_pure = MCP.mix_of_pure
          (CP.remove_redundant (MCP.pure_of_mix rhs_b2.CF.formula_base_pure))} in
(*pure subformulas matching LHS-RHS: drop RHS*)
(lhs_b3, rhs_b3)

and simplify_one_constr_b lhs_b rhs_b=
  let pr = Cprinter.prtt_string_of_formula_base in
  Debug.no_2 "simplify_one_constr_b" pr pr (pr_pair pr pr)
      (fun _ _ -> simplify_one_constr_b_x lhs_b rhs_b) lhs_b rhs_b

let simplify_constrs_x constrs=
  List.map simplify_one_constr constrs

let simplify_constrs constrs=
   let pr = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  Debug.no_1 "simplify_constrs" pr pr
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
        let sv,el,l = get_only_hrel rhs in
        if(List.length el >= 2) then [(CF.HRel (sv,el,l))]
        else []
    )
    with _ -> []
  in
  (*remove duplicate*)
  let cands = (List.concat (List.map helper constrs)) in
  Gen.BList.remove_dups_eq (fun (CF.HRel x1) (CF.HRel x2) -> CF.check_eq_hrel_node x1 x2) cands

let get_hp_split_cands constrs =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln (Cprinter.string_of_hrel_formula) in
  Debug.no_1 "get_hp_split_cands" pr1 pr2
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
    ((sv,new_hp_names),(sv, CF.HRel (sv,el,l), new_hrels_comb))
  in
  let res = List.map helper hps in
  List.split res

let hp_split hps =
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = (pr_list (pr_pair pr1 pr2)) in
  let pr4 = Cprinter.string_of_h_formula in
  let pr5 = pr_list pr4 in
  let pr6 = pr_list (pr_triple pr1 pr4 pr4) in
   Debug.no_1 "hp_split" pr5 (pr_pair pr3 pr6)
       (fun _ -> hp_split_x hps) hps

let subst_constr_with_new_hps hp_constrs hprel_subst=
  let elim_first_arg (a1,a2,a3)= (a2,a3) in
  let new_hprel_subst = List.map elim_first_arg hprel_subst in
  let helper (l_constr, r_constr)=
    (CF.subst_hrel_f l_constr new_hprel_subst, CF.subst_hrel_f r_constr new_hprel_subst)
  in
  List.map helper hp_constrs

(*return new contraints and hp split map *)
let split_hp_x (hp_constrs: (CF.formula * CF.formula) list): ((CF.formula * CF.formula) list *
          (CP.spec_var*CP.spec_var list) list * (CP.spec_var * CF.h_formula*CF.h_formula) list) =
  (*get hp candidates*)
  let split_cands = get_hp_split_cands hp_constrs in
  (*split  and get map*)
  let split_map,hprel_subst =  hp_split split_cands in
  (*subs old hrel by new hrels*)
  let new_constrs = hp_constrs in (*subst_constr_with_new_hps hp_constrs hprel_subst in *)
  (new_constrs, split_map, hprel_subst)

let split_hp (hp_constrs: (CF.formula * CF.formula) list):((CF.formula * CF.formula) list *
 (CP.spec_var*CP.spec_var list) list * (CP.spec_var *CF.h_formula*CF.h_formula) list) =
  let pr1 =  pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = !CP.print_sv in
  let pr3 = !CP.print_svl in
  let pr4 = fun (a1,a2,_) -> (*ignore a3*)
      let pr = pr_pair pr1 (pr_list (pr_pair pr2 pr3)) in
      pr (a1, a2)
  in
      (fun _ -> split_hp_x hp_constrs) hp_constrs

(*========subst==============*)
let rec check_unsat_x f=
  match f with
    | CF.Base fb -> check_inconsistency fb.CF.formula_base_heap fb.CF.formula_base_pure
    | CF.Or orf -> (check_unsat orf.CF.formula_or_f1) || (check_unsat orf.CF.formula_or_f2)
    | CF.Exists fe ->
        (*may not correct*)
        check_inconsistency fe.CF.formula_exists_heap fe.CF.formula_exists_pure

and check_unsat f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = string_of_bool in
  Debug.no_1 "check_unsat" pr1 pr2
      (fun _ -> check_unsat_x f) f

and check_inconsistency hf mixf=
  let hds, _, _ (*hvs, hrs*) =  CF.get_hp_rel_h_formula hf in
  (*currently we just work with data nodes*)
  let neqNulls = List.map (fun dn -> CP.mkNeqNull dn.CF.h_formula_data_node dn.CF.h_formula_data_pos) hds in
  let new_mf = MCP.mix_of_pure (CP.join_conjunctions neqNulls) in
  let cmb_mf = MCP.merge_mems mixf new_mf true in
  not (TP.is_sat_raw cmb_mf)

let subst_one_cs_w_one_partial_def f (hp_name, args, def_f)=
(*drop hrel and get current args*)
  let newf, argsl = CF.drop_hrel_f f [hp_name] in
  match argsl with
    | [] -> f
    | [eargs] ->
      begin
  (*generate a susbst*)
        let args2= (List.fold_left List.append [] (List.map CP.afv eargs)) in
        let subst = (List.combine args args2) in
        let def_f_subst = CF.subst subst def_f in
  (*combi ne def_f_subst into newf*)
        let newf1 = CF.mkStar newf def_f_subst CF.Flow_combine (CF.pos_of_formula newf) in
  (*check contradiction*)
        if check_unsat newf1 then f
        else newf1
      end
    | _ -> report_error no_pos "sa.subst_one_cs_w_one_partial_def: should be a singleton"

(*
each constraints, apply lhs and rhs. each partial def in one side ==> generate new constraint

 ldef --> hp: subst all hp in lhs with ldef
 hp --> rdef: subst all hp in rhs with rdef
*)
let subst_one_cs_w_partial_defs ldefs rdefs (lhs,rhs)=
  (*subst lhs*)
  let lhs1 = List.fold_left subst_one_cs_w_one_partial_def lhs ldefs in
  (*subst rhs*)
  let rhs1 = List.fold_left subst_one_cs_w_one_partial_def rhs rdefs in
  (*rhs contradict with lhs?*)
  let cmbf = CF.mkStar lhs1 rhs1 CF.Flow_combine no_pos in
  if check_unsat cmbf then (lhs,rhs)
  else (lhs1,rhs1)

let subst_cs_w_partial_defs_x hp_constrs par_defs=
  (*partition non-recursive partial defs: lhs set and rhs set*)
  let rec partition_par_defs pdefs lpdefs rpdefs=
    match pdefs with
      | [] -> (lpdefs, rpdefs)
      | (hp_name, hp_args, _, oldef, ordef)::ps ->
          (
              match oldef, ordef with
                | Some _ ,Some _ -> (*recursive par def -->currently omit*)
                    partition_par_defs ps lpdefs rpdefs
                | Some f1, None -> (*lhs case*)
                    partition_par_defs ps (lpdefs@[(hp_name, hp_args, f1)]) rpdefs
                | None, Some f2 -> (*rhs case*)
                    partition_par_defs ps lpdefs (rpdefs@[(hp_name, hp_args, f2)])
                | None, None -> (*can not happen*)
                    report_error no_pos "sa.partition_par_defs: can not happen"
          )
  in
  let (ldefs, rdefs) = partition_par_defs par_defs [] [] in
  List.map (subst_one_cs_w_partial_defs ldefs rdefs) hp_constrs

let subst_cs_w_partial_defs hp_constrs par_defs=
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln string_of_par_def_w_name in
  Debug.ho_2 "subst_cs_w_partial_defs" pr1 pr2 pr1
      (fun _ _ -> subst_cs_w_partial_defs_x hp_constrs par_defs) hp_constrs par_defs

(*
sth ====> A*HP
substituted by HP ====> b (currently we only support HP, we can enhance with
more general formula and use imply )
result is sth ====> A*b
*)
let subst_cs_w_other_cs_x constrs=
  (* find all constraints which have lhs is a HP*)
  let check_lhs_hp_only (lhs,rhs)=
    match lhs with
      | CF.Base fb -> if (CP.isConstTrue (MCP.pure_of_mix fb.CF.formula_base_pure)) then
            let r = (CF.get_HRel fb.CF.formula_base_heap) in
            (match r with
              | None -> []
              | Some (hp, args) -> [(hp, args, rhs)]
            )
          else []
      | _ -> report_error no_pos "sa.subst_cs_w_other_cs: not handle yet"
  in
  let cs_susbsts = List.concat (List.map check_lhs_hp_only constrs) in
  List.map (subst_one_cs_w_partial_defs [] cs_susbsts) constrs

let subst_cs_w_other_cs constrs=
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
   Debug.ho_1 "subst_cs_w_other_cs" pr1 pr1
       (fun _ -> subst_cs_w_other_cs_x constrs) constrs

let subst_cs_x hp_constrs par_defs=
(*subst by partial defs*)
  let constrs1 = subst_cs_w_partial_defs hp_constrs par_defs in
(*subst by constrs*)
  subst_cs_w_other_cs constrs1

let subst_cs hp_constrs par_defs=
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln string_of_par_def_w_name in
  Debug.ho_2 "subst_cs" pr1 pr2 pr1
      (fun _ _ -> subst_cs_x hp_constrs par_defs) hp_constrs par_defs

(*===========end subst============*)
(*========generalization==========*)
(*for par_defs*)
let generalize_one_hp prog par_defs=
  (*collect definition for each partial definition*)
  let obtain_and_norm_def args0 (a1,args,a3,a4,a5)=
    let f=
      match a4,a5 with
        | Some f, None -> f
        | None, Some f -> f
        | Some f1, Some f2 -> (*find which formula contains root args*)
            let ptrs1, _,_, _,_ = find_defined_pointers_raw prog f1 in
            let ptrs_diff= Gen.BList.difference_eq CP.eq_spec_var args ptrs1 in
            if ptrs_diff = [] then f1
            else
              (
                  let ptrs2, _,_, _,_ = find_defined_pointers_raw prog f2 in
                  let ptrs_diff= Gen.BList.difference_eq CP.eq_spec_var args ptrs2 in
                  (* (\*for debugging*\) *)
                  (* let _ = Debug.info_pprint ("args: " ^ (!CP.print_svl args)) no_pos in *)
                  (* let _ = Debug.info_pprint ("ldef: " ^ (!CP.print_svl ptrs1)) no_pos in *)
                  (* let _ = Debug.info_pprint ("rdef: " ^ (!CP.print_svl ptrs2)) no_pos in *)
                  (* (\*end for debugging*\) *)
                  if ptrs_diff = [] then f2
                  else report_error no_pos "sa.obtain_def: can't happen 1")
        | None, None -> report_error no_pos "sa.obtain_def: can't happen 2"
    in
    (*normalize args*)
    let subst = List.combine args args0 in
    (CF.subst subst f)
  in
  let hp, args, _,_,_ = (List.hd par_defs) in
  let defs = List.map (obtain_and_norm_def args) par_defs in
  (*make disjunction*)
  let def = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 (CF.pos_of_formula f1))
     (List.hd defs) (List.tl defs) in
  (hp, (CP.HPRelDefn hp, CF.formula_of_heap
      (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, no_pos)) no_pos,
   def))

let generalize_hps_par_def prog par_defs=
  (*partition the set by hp_name*)
  let rec partition_pdefs_by_hp_name pdefs parts=
    match pdefs with
      | [] -> parts
      | (a1,a2,a3,a4,a5)::xs ->
          let part,remains= List.partition (fun (hp_name,_,_,_,_) -> CP.eq_spec_var a1 hp_name) xs in
          partition_pdefs_by_hp_name remains (parts@[[(a1,a2,a3,a4,a5)]@part])
  in
  let groups = partition_pdefs_by_hp_name par_defs [] in
  (*each group, do union partial definition*)
  (List.map (generalize_one_hp prog) groups)

let generalize_hps_cs hp_names cs=
  let rec look_up_hrel id ls=
    match ls with
      | [] -> report_error no_pos "sa.generalize_hps_cs: can not happen"
      | (id1, vars, p)::cs -> if CP.eq_spec_var id id1 then (id1, vars, p)
          else look_up_hrel id cs
  in
  let check_formula_hp_only f=
    match f with
      | CF.Base fb -> if (CP.isConstTrue (MCP.pure_of_mix fb.CF.formula_base_pure)) then
            let r = (CF.get_HRel fb.CF.formula_base_heap) in
            (match r with
              | None -> None
              | Some (hp, args) -> Some (hp, args)
            )
          else None
      | _ -> report_error no_pos "sa.subst_cs_w_other_cs: not handle yet"
  in
  let generalize_hps_one_cs (lhs, rhs)=
    let _,_,l_hp = CF.get_hp_rel_formula lhs in
    let _,_,r_hp = CF.get_hp_rel_formula rhs in
    let hps = List.map (fun (id, _, _) -> id) (l_hp@r_hp) in
    let diff = Gen.BList.difference_eq CP.eq_spec_var hps hp_names in
    match diff with
      | [] -> ([],[]) (*drop constraint, no new definition*)
      | [id] -> let (hp, args, p) = look_up_hrel id (l_hp@r_hp) in
                let ohp = check_formula_hp_only lhs in
                (match ohp with
                  | None ->
                       let ohp = check_formula_hp_only rhs in
                       ( match ohp with
                         | None -> ([(lhs, rhs)],[]) (*keep constraint, no new definition*)
                         |  Some (hp, args) ->
                             ([],[(CP.HPRelDefn hp, CF.formula_of_heap
                                 (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, p)) p, lhs)])
                       )
                  | Some (hp, args) ->
                      ([],[(CP.HPRelDefn hp, CF.formula_of_heap
      (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, p)) p, rhs)])
                )
      | _ -> ([(lhs, rhs)],[]) (*keep constraint, no new definition*)
  in
  let r = List.map generalize_hps_one_cs cs in
  let cs1, hp_defs = List.split r in
  (List.concat cs1, List.concat hp_defs)

let generalize_hps_x prog cs par_defs=
(*general par_defs*)
  let pair_names_defs = generalize_hps_par_def prog par_defs in
  let hp_names,hp_defs = List.split pair_names_defs in
(*for each constraints, we may pick more definitions*)
  let remain_constr, hp_def1 = generalize_hps_cs hp_names cs in
(remain_constr, hp_defs@hp_def1)

let generalize_hps prog cs par_defs=
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln string_of_par_def_w_name in
  let pr3 = pr_list Cprinter.string_of_hp_rel_def in
  Debug.no_2 "generalize_hp" pr1 pr2 (pr_pair pr1 pr3)
      (fun _ _ -> generalize_hps_x prog cs par_defs) cs par_defs

(*========END generalization==========*)
(*===========fix point==============*)
let infer_hps_fix prog constrs =
  let rec helper constrs par_defs =
    let constrs1 = simplify_constrs constrs in
  (*step 3: pick partial definition*)
    let constrs2, new_par_defs = collect_partial_definitions prog constrs1 in
    let par_defs_diff = Gen.BList.difference_eq
      check_partial_def_eq new_par_defs par_defs in
    if par_defs_diff = [] then
      (*teminating condition*)
      (constrs2, par_defs)
    else
      begin
          (*step 4: pick complete def*)
          let constrs3 = constrs2 in
          (*step 5: subst new partial def into constrs*)
          let constrs4 = subst_cs constrs3 (par_defs@par_defs_diff) in
          helper constrs4 (par_defs@par_defs_diff)
      end
  in
  helper constrs []

let generate_hp_def_from_split hp_defs_split=
  let helper (hp_name, hrel, h_def)=
    (CP.HPRelDefn hp_name, CF.formula_of_heap hrel no_pos,
     CF.formula_of_heap h_def no_pos)
  in
  List.map helper hp_defs_split

(*
  input: constrs: (formula * formula) list
  output: definitions: (formula * formula) list
*)
let infer_hps_x prog (hp_constrs: (CF.formula * CF.formula) list):
 ((CF.formula * CF.formula) list * hp_rel_def list) =
  (*step 1: drop irr parameters*)
  let constrs = elim_redundant_paras_lst_constr hp_constrs in
  Debug.ninfo_hprint (add_str "AFTER DROP: " (pr_list_ln Cprinter.string_of_hprel_lhs_rhs)) constrs no_pos;
   (*step 1': split HP*)
  let constrs1, split_tb,hp_defs_split = split_hp constrs in
  let cs, par_defs = infer_hps_fix prog constrs1 in
  (*step 6: over-approximate to generate hp def*)
  let constr2, hp_defs = generalize_hps prog cs par_defs in
  let hp_def_from_split = generate_hp_def_from_split hp_defs_split in
  (constr2, hp_defs@hp_def_from_split)

  (*loop 1*)
  (* (\*simplify constrs*\) *)
  (* let constrs12 = simplify_constrs constrs1 in *)
  (* (\*step 3: pick partial definition*\) *)
  (* let constrs13, par_defs1 = collect_partial_definitions prog constrs12 in *)
  (* (\*step 4: pick complete def*\) *)
  (* (\*step 5: subst new partial def into constrs*\) *)
  (* let constrs14 = subst_cs constrs13 par_defs1 in *)
  (* (\*loop 2*\) *)
  (* (\*simplify constrs*\) *)
  (* let constrs22 = simplify_constrs constrs14 in *)
  (* (\*step 3: pick partial definition*\) *)
  (* let constrs23, par_defs2 = collect_partial_definitions prog constrs22 in *)
  (* let par_defs_diff = Gen.BList.difference_eq check_partial_def_eq par_defs2 par_defs1 in *)

let infer_hps prog (hp_constrs: (CF.formula * CF.formula) list):
 ((CF.formula * CF.formula) list * hp_rel_def list) =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.ho_1 "infer_hp" pr1 (pr_pair pr1 pr2)
      (fun _ -> infer_hps_x prog hp_constrs) hp_constrs
