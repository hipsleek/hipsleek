open Gen.Basic
open Globals
open Cast

module H = Hashtbl
module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq

let string_of_data_decls data_decls =
  let data_decls = List.filter (fun d -> List.length d.data_fields > 0) data_decls in 
  let string_of_data_decl data_decl =
    (
      let name = data_decl.data_name in
      let pr_arg arg =
	let (t,arg_name) = arg in
	(CP.name_of_type t) ^ " " ^ arg_name
      in
      let args = pr_lst "; " pr_arg data_decl.data_fields in
      "data "^ name ^ "{" ^ args ^ "}\n"
    )
  in
  List.fold_left (fun piv e -> piv ^ string_of_data_decl e) "" data_decls


let string_of_iast_data_decls data_decls =
  let string_of_data_decl data_decl =
    (
      let name = data_decl.Iast.data_name in
      let pr_arg arg =
	let ((t,arg_name),_,_) = arg in
	(CP.name_of_type t) ^ " " ^ arg_name
      in
      let args = pr_lst "; " pr_arg data_decl.Iast.data_fields in
      "data "^ name ^ "{" ^ args ^ "}\n"
    )
  in
  List.fold_left (fun piv e -> piv ^ string_of_data_decl e) "" data_decls

let string_of_hp_decls hpdecls =
  (
    let string_of_hp_decl hpdecl =
      (
	let name = hpdecl.hp_name in
	let pr_arg arg =
	  let t = CP.type_of_spec_var arg in
	  let arg_name = Cprinter.string_of_spec_var arg in
	  let arg_name = if(String.compare arg_name "res" == 0) then fresh_name () else arg_name in
	  (CP.name_of_type t) ^ " " ^ arg_name
	in
	let args = pr_lst ", " pr_arg hpdecl.hp_vars in
	"HeapPred "^ name ^ "(" ^ args ^ ").\n"
      )
    in
    List.fold_left (fun piv e -> piv ^ string_of_hp_decl e) "" hpdecls
  )

let print_res_list rl def=
  let pr1 =  pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula in
  let pr_res (c1,c2,mtb) = 
    if(List.length mtb == 0) then  "no-diff-info"
    else (
      let (_,d1,d2) = List.hd mtb in
      if(def) then "Infer def: " ^ pr1 c1 ^ "\nExpected def: " ^ pr1 c2 ^ "\nDiff1: " ^ pr1 d1 ^ "\nDiff2: " ^ pr1 d2 
      else "Infer constr: " ^ pr1 c1 ^ "\nExpected constr: " ^ pr1 c2 ^ "\nDiff1: " ^ pr1 d1 ^ "\nDiff2: " ^ pr1 d2 
    )
  in
  List.fold_left (fun piv sr -> piv  ^ sr ^ "\n" ) "" (List.map (fun r -> (pr_res) r) rl)
 
let process_simplify_hps prog proc hp_lst_assume ls_inferred_hps dropped_hps old_hpdecls sel_hp_rels cout_option =
  let  hp_lst_assume = List.map (fun hp -> (hp.CF.hprel_lhs,hp.CF.hprel_rhs)) hp_lst_assume in
  let ls_inferred_hps =   List.map (fun (_,hf,f2) -> (hf,f2))  ls_inferred_hps  in
  let save_names =  List.map (fun hp-> hp.Cast.hp_name) old_hpdecls in  
  let hpdecls = prog.prog_hp_decls in
(*dropped_hps: decrease num of args --> should chaneg the hp_decl + change name also !!! *)
  let revise_hpdecls hpdecl dropped_hps =
    let name = hpdecl.Cast.hp_name in
    try (
      let (sv,_,eargs) = List.find (fun (a,b,c) -> String.compare (CP.full_name_of_spec_var a) name == 0) dropped_hps in
      let new_hp_vars = List.fold_left List.append [] (List.map CP.afv eargs) in
      let new_name = Globals.hp_default_prefix_name ^ (string_of_int (Globals.fresh_int())) in
      print_string ("from name: " ^name ^" --> name: "^ new_name ^ "\n" );
      let new_sv =  CP.SpecVar (HpT,new_name,Unprimed) in
      let new_hpdecl =  ({hpdecl with Cast.hp_name = new_name;
	Cast.hp_vars = new_hp_vars}) in
      (new_hpdecl::[hpdecl],[(sv,new_sv)])
    )
    with 
      | Not_found -> ([hpdecl],[])
  in
 let get_new_var var vnames =
    (*Notice: (TODO) assume that var are form x_x -> it means new var x1 can not be supl with some x1 :D*)
    let check_dupl n = List.exists (fun sn -> String.compare sn n == 0) save_names in
    let name = CP.full_name_of_spec_var var in
    let (typ,raw_name,p) = match var with
      | CP.SpecVar s -> s
    in
    let mkname name i = 
      if(i < 0) then name else ( name ^ (string_of_int i)) 
    in
    let new_var,new_vnames = 
      let rec add name root_var vnames =
	match vnames with
	  | [] -> 
	    let new_name =   match root_var with
	      | CP.SpecVar (typ,root_name,p) -> root_name
	    in  
	    if(check_dupl new_name) then (
	      add name root_var [(root_var, [("", -1)] )]
	    ) else (root_var,[(root_var, [(name, -1)] )])
	  | (vn,m)::y -> (
	    if(CP.eq_spec_var vn root_var ) then (
	      try (
		let _, indx = List.find (fun (v,i) -> String.compare v name == 0) m in
		let new_name,p =   match root_var with
		  | CP.SpecVar (typ,root_name,p) ->  mkname root_name indx,p
		in  
		let n_var =  CP.SpecVar (typ,new_name,p) in
		(n_var , vnames)
	      )
	      with _ -> (
		let (x,indx) = List.hd m in 
		let indx = indx + 1 in
		let new_name,p =   match root_var with
		  | CP.SpecVar (typ,root_name,p) ->  mkname root_name indx,p
		in  
		if(check_dupl new_name) then  add name root_var ((vn,("",indx)::m)::y)
		else 
		  let n_var =  CP.SpecVar (typ,new_name,p) in
		  (n_var, (vn,(name,indx)::m)::y)
	      )
	    )
	    else  let (n,vns) = add name root_var y in
	      (n,(vn,m)::vns)
	  )
      in
      let root_var  = try (
	let i = String.index name '_' in (*make root var is all a-z -> no worry for x1 case above*)
	let n = String.sub name 0 i in 
	CP.SpecVar (typ, n, Unprimed) 
      ) with _ -> let n = if p = Unprimed then name else raw_name in
		  CP.SpecVar (typ, n, Unprimed) 
      in
      add name root_var vnames 
    in
    (new_var, new_vnames)
  in 
  let simplify_varname sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls =
    let pairs = List.map (fun c-> revise_hpdecls c dropped_hps) hpdecls in
    let e1,e2 = List.split pairs in
    let hpdecls = List.concat e1 in
    let name_mtb = List.concat e2 in (*mtb: name --> new_name*)
		              (* print_string " simplify_varname\n"; *)
    (* let  hp_lst_assume = List.map (fun hp -> (hp.CF.hprel_lhs,hp.CF.hprel_rhs)) hp_lst_assume in *)
    let change_hp f = CF.subst name_mtb f in
    let ls_inferred_hps =   List.map (fun (hf,f2) -> (change_hp (CF.formula_of_heap hf no_pos), change_hp f2))  ls_inferred_hps  in
    let sim_each_ass (f1,f2) mtb vnames =
      let all_vars = CP.remove_dups_svl (CF.fv f1 @ CF.fv f2) in
      let all_vars = List.filter (fun v-> not(List.exists (fun sv -> CP.eq_spec_var sv v) sel_hp_rels)) all_vars in			
      let (new_mtb,vns) = List.fold_left (fun (curr_mtb,curr_vnames) var -> 
	let (new_var,new_vnames) = get_new_var var curr_vnames in
	((var,new_var)::curr_mtb, new_vnames) ) ([],vnames) all_vars 
      in
      let rename_hp f = CF.subst new_mtb f in
      let filter_hp vnames = List.filter (fun (v,_) -> CP.is_hprel_typ v) vnames in
      let filter_mtb mtb = List.filter (fun (v,_) -> CP.is_hprel_typ v) mtb in
      ((rename_hp f1,rename_hp f2),(filter_mtb new_mtb)@mtb,filter_hp vns)
    in 
    let rename_all hpdecls hp_mtb = 
      let rename_one hpdecl hp_mtb = 
	let name = hpdecl.Cast.hp_name in
	let vars = hpdecl.Cast.hp_vars in
	try (
	  let (a, b) = List.find (fun (a,_) -> String.compare (CP.full_name_of_spec_var a) name == 0) hp_mtb in
	  let new_name = CP.full_name_of_spec_var b in
	  let (_,new_vars) = List.fold_left (fun piv v -> 
	    let (index,vs) = piv in
	    let (typ,raw_name,p) = match v with
	      | CP.SpecVar s -> s
	    in
	    let new_name = "v" ^ (string_of_int index) in
	    let new_sv = CP.SpecVar (typ,new_name,p) in
	    (index+1,new_sv::vs)
	  ) (0,[]) vars in
	  [({hpdecl with Cast.hp_name = new_name;
	    Cast.hp_vars = new_vars})]
	)
	with 
	  | Not_found -> [hpdecl]
      in
      List.concat (List.map (fun h -> rename_one h hp_mtb) hpdecls)
    in
    
    let (hp_lst_assume, mtb,vnames) = List.fold_left (fun piv ass -> let (r,m,vn) = piv in
								     let (rh,mh,vn1) = sim_each_ass ass m vn in
								     (rh::r,mh,vn1)
    ) ([],[],[]) hp_lst_assume in
    let (ls_inferred_hps, mtb2,vnames2) = List.fold_left (fun piv hp -> let (r,m,vn) = piv in
									let (rh,mh,vn1) = sim_each_ass hp m vn in
									(rh::r,mh,vn1)
    ) ([],mtb,vnames) ls_inferred_hps in
    let hp_mtb = mtb2 in
   
    let hpdecls = rename_all hpdecls hp_mtb in 
    (* print_string ("DATA DECLARATION4: \n" ^ string_of_hp_decls hpdecls ^ "\n"); *)
    (hpdecls,hp_lst_assume,ls_inferred_hps)
  in
  simplify_varname sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls

let gen_sleek_residues valid rs num_id2 cout_option  =
  let _ = Gen.Profiling.push_time "Gen cp file" in
  let file_name = !Globals.cpfile in
  let res = if(valid) then "SUCCESS" else "FAIL" in
  let list_formula_w_context = CF.list_formula_trace_of_list_context rs in
  let list_formula = List.map (fun (_,(f,_)) -> f) list_formula_w_context in
  let pr1 =  pr_lst ";\n"  Cprinter.prtt_string_of_formula in
  let residue =  "onef[][]:{\n" ^ pr1 list_formula ^ "\n}\n" in
  let message = num_id2 ^ ":" ^ res ^ "[\n"^ residue ^"]" in
  let _ = try
	    (
	      match cout_option with
		| Some cout -> Printf.fprintf cout "%s\n" message;   (* write something *)
		| _ -> ()
	    )
    with Sys_error _ as e ->
      Format.printf "Cannot open file \"%s\": %s\n" file_name (Printexc.to_string e)
  in
  let _ = Gen.Profiling.pop_time "Gen cp file" in
  ()


let gen_sleek_decls prog cout_option =
  let _ = Gen.Profiling.push_time "Gen cp file" in
  let file_name = !Globals.cpfile in
  let message = string_of_data_decls prog.Cast.prog_data_decls in
  let _ = try
	    (
	      match cout_option with
		| Some cout -> Printf.fprintf cout "%s\n" message;   (* write something *)
		| _ -> ()
	    )
    with Sys_error _ as e ->
      Format.printf "Cannot open file \"%s\": %s\n" file_name (Printexc.to_string e)
  in
  let _ = Gen.Profiling.pop_time "Gen cp file" in
  ()

let gen_cpfile prog proc hp_lst_assume ls_inferred_hps dropped_hps old_hpdecls sel_hp_rels str1 str2 cout_option =
  let _ = Gen.Profiling.push_time "Gen cp file" in
  let file_name = !Globals.cpfile in
  (* let hpdecls = prog.prog_hp_decls in *)
  (* print_string ("DATA DECLARATION: \n" ^ string_of_hp_decls hpdecls ^ "\n"); *)
  let (hpdecls,hp_lst_assume, ls_inferred_hps) = process_simplify_hps prog proc hp_lst_assume ls_inferred_hps dropped_hps old_hpdecls sel_hp_rels cout_option in
  let string_of_message sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls =
    let hp_decls = string_of_hp_decls hpdecls in
    let data_decls = string_of_data_decls prog.prog_data_decls in
    let pr_ass f1 f2 (x,y) = (f1 x)^" --> "^(f2 y) in
    let pr1 =  pr_lst ";\n" (pr_ass Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
    let ass_cont = pr1 hp_lst_assume in
    let hpdefs_cont =  pr1 ls_inferred_hps in
    let hp_ass = "ass " ^ (!CP.print_svl sel_hp_rels) ^ "[]: {\n" ^ ass_cont ^ "\n}\n" in
    let hpdefs = "hpdefs " ^ (!CP.print_svl sel_hp_rels) ^ "[]: {\n"  ^ hpdefs_cont ^ "\n}\n"in
    let pure_ass = "pure_assumes " ^ "[]: {\n"  ^ str1 ^ "\n}\n"in
    let pure_rel = "pure_reldefs " ^ "[]: {\n"  ^ str2 ^ "\n}\n"in
    let test_comps = if(List.length sel_hp_rels == 0) then pure_ass ^ pure_rel else hp_ass ^ hpdefs  in (*KEY*)
    let  unmin_name = unmingle_name proc.proc_name in
    let expected_res = "SUCCESS" in (*TODO: final res here (in inference, often SUCCESS*)
    let message = data_decls ^ "\n" ^ hp_decls ^ "\n" ^ unmin_name ^":" ^ expected_res ^"[\n" ^ test_comps ^ "]\n" in
    message
  in
  let message = string_of_message sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls in
  let _ = try
	    (
	      match cout_option with
		| Some cout -> Printf.fprintf cout "%s\n" message;   (* write something *)
		| _ -> ()
	    )
    with Sys_error _ as e ->
      Format.printf "Cannot open file \"%s\": %s\n" file_name (Printexc.to_string e)
  in
  let _ = Gen.Profiling.pop_time "Gen cp file" in
  ()
	      
let cp_test proc hp_lst_assume ls_inferred_hps sel_hp_rels =
  let is_match_constrs il constrs = 
    if(not(!Globals.show_diff_constrs)) then 
      CEQ.checkeq_constrs il (List.map (fun hp -> hp.CF.hprel_lhs,hp.CF.hprel_rhs) hp_lst_assume) constrs 
    else
      let res,res_list = CEQ.checkeq_constrs_with_diff il (List.map (fun hp -> hp.CF.hprel_lhs,hp.CF.hprel_rhs) hp_lst_assume) constrs in
      if(not(res)) then 
	print_string ("\nDiff constrs " ^ proc.proc_name ^ " {\n" ^ (print_res_list res_list false) ^ "\n}\n" );
      res
  in
  let is_match_defs il sl defs = 
    let res,res_list,sl =  
      if(!Globals.sa_subsume) then (
	CEQ.check_subsume_defs_tmp il sl ls_inferred_hps defs sel_hp_rels
      )
      else  let (r,rl) = CEQ.checkeq_defs_with_diff il sl ls_inferred_hps defs sel_hp_rels in
	    (r,rl,[])
    in
    let pr1 b = if(b) then ">=" else "<=" in
    let pr2 = pr_list_ln (pr_triple Cprinter.string_of_spec_var Cprinter.string_of_spec_var pr1 ) in
    let _ = if(not(res)) then (
      if(List.length sl > 0) then print_string ("SUBSUME: "^ pr2 sl ^"\n") ;
      if(!Globals.show_diff_constrs) then ( print_string ("\nDiff defs " ^ proc.proc_name ^ " {\n" ^ (print_res_list res_list true) ^ "\n}\n" ));
    )
      else (if(List.length sl > 0) then print_string ("SUCCESS WITH SUBSUME: "^ pr2 sl ^"\n");)
    in
    res
  in
  let _ = Gen.Profiling.push_time "Compare res with cp file" in
  let test_comps = proc.Cast.proc_test_comps in
  let _ =
    match test_comps with
      | None -> print_string ("!!! Warning: There are no cp info for " ^ proc.proc_name ^ "\n" )
      | Some (tcs) -> (
	let ass = tcs.Cast.expected_hpass in
	let hpdefs = tcs.Cast.expected_hpdefs in
	let _ = match ass with
	  | None -> if(List.length  hp_lst_assume > 0) then  print_string ("!!! Warning: There are no constrs info for " ^ proc.proc_name ^ "\n" )
	  | Some (il,sl,a)-> let res = is_match_constrs il a in
			     if(res) then 
			       print_string ("Compare ass " ^ proc.proc_name ^ " SUCCESS\n" )
			     else 
			       print_string ("Compare ass " ^ proc.proc_name ^ " FAIL\n" )
	in
	let hpdefs = tcs.Cast.expected_hpdefs in
	let _ = match hpdefs with
	  | None -> if(List.length ls_inferred_hps > 0) then print_string ("!!! Warning: There are no hpdefs info for " ^ proc.proc_name ^ "\n" )
	  | Some (il2,sl2,d) ->  let res = is_match_defs il2 sl2 d in 
				 if(res) then 
				   print_string ("Compare defs " ^ proc.proc_name ^ " SUCCESS\n" )
				 else 
				   print_string ("Compare defs " ^ proc.proc_name ^ " FAIL\n" )
	in
	()
      )
  in
  let _ = Gen.Profiling.pop_time "Compare res with cp file" in
  ()

let rec cp_test_proc test_proc1 test_proc2=
  let name = test_proc1.Cast.cp_proc_name in
  let _ = Gen.Profiling.push_time "Compare res with cp file" in
  let test_comps1 = test_proc1.Cast.cp_proc_test_comps in
  let test_comps2 = test_proc2.Cast.cp_proc_test_comps in
  let ass_opt1 = test_comps1.Cast.expected_hpass in
  let hpdefs_opt1 = test_comps1.Cast.expected_hpdefs in
  let onefs_opt1 = test_comps1.Cast.expected_onef in
  let ass_opt2 = test_comps2.Cast.expected_hpass in
  let hpdefs_opt2 = test_comps2.Cast.expected_hpdefs in
  let onefs_opt2 = test_comps2.Cast.expected_onef in
  let _ = match ass_opt1 with
    | None ->  print_string ("!!! Warning: There are no constrs info for " ^ name  ^ "\n" )
    | Some ass1 -> ( match ass_opt2 with
	| None ->  print_string ("!!! Warning: There are no constrs info for " ^ name  ^ "\n" )
	| Some ass2 ->
	  let res = is_match_constrs ass1 ass2 name in
	  if(res) then 
	    print_string ("Compare ass " ^ test_proc1.Cast.cp_proc_name ^ " SUCCESS\n" )
	  else 
	    print_string ("Compare ass " ^ test_proc1.Cast.cp_proc_name  ^ " FAIL\n" )
    )
  in
  let _ = match hpdefs_opt1 with
    | None -> print_string ("!!! Warning: There are no hpdefs info for " ^name  ^ "\n" )
    | Some hpdefs1 -> ( match hpdefs_opt2 with
  	| None -> print_string ("!!! Warning: There are no hpdefs info for " ^ name  ^ "\n" )
  	| Some hpdefs2 -> let res = is_match_defs hpdefs1 hpdefs2 name in
  			  if(res) then
  			    print_string ("Compare defs " ^ name  ^ " SUCCESS\n" )
  			  else
  			    print_string ("Compare defs " ^ name  ^ " FAIL\n" )
    )
  in
  let _ = match onefs_opt1 with
    | None -> print_string ("!!! Warning: There are no onef info for " ^name  ^ "\n" )
    | Some onefs1 -> ( match onefs_opt2 with
  	| None -> print_string ("!!! Warning: There are no onef info for " ^ name  ^ "\n" )
  	| Some onefs2 -> let res = is_match_onefs onefs1 onefs2 name in
  			  if(res) then
  			    print_string ("Compare onefs " ^ name  ^ " SUCCESS\n" )
  			  else
  			    print_string ("Compare onefs " ^ name  ^ " FAIL\n" )
    )
  in
  let _ = Gen.Profiling.pop_time "Compare res with cp file" in
  ()

and is_match_constrs ass1 ass2 name=
  let (il1, sl1, constrs1) = ass1 in
  let (il2, sl2, constrs2) = ass2 in
  if(not(!Globals.show_diff_constrs)) then 
    CEQ.checkeq_constrs (il1@il2) constrs1 constrs2 
  else
    let res,res_list = CEQ.checkeq_constrs_with_diff (il1@il2) constrs1 constrs2 in
    if(not(res)) then 
      print_string ("\nDiff constrs " ^ name^ " {\n" ^ (print_res_list res_list false) ^ "\n}\n" );
    res

and  is_match_defs hpdefs1 hpdefs2 name= 
  let (il1, sl1, defs1) =  hpdefs1 in
  let (il2, sl2, defs2) =  hpdefs2 in
  let defs1 = List.map (fun (f1,f2) -> (CP.HPRelDefn (CP.SpecVar(HpT,"a",Unprimed)),CF.HRel (List.hd (CF.get_hprel f1)),f2)) defs1 in
  let defs2 = List.map (fun (f1,f2) -> (f1,f2)) defs2 in
  let res,res_list,sl =  
    let il1_sv = List.map (fun il -> CP.SpecVar(HpT,il,Unprimed)) il1 in
    if(!Globals.sa_subsume) then (
      CEQ.check_subsume_defs_tmp (il1@il2) sl2 defs1 defs2 il1_sv
    )
    else  let (r,rl) = CEQ.checkeq_defs_with_diff (il1@il2) sl2 defs1 defs2 il1_sv in
	  (r,rl,[])
  in
  let pr1 b = if(b) then ">=" else "<=" in
  let pr2 = pr_list_ln (pr_triple Cprinter.string_of_spec_var Cprinter.string_of_spec_var pr1 ) in
  let _ = if(not(res)) then (
    if(List.length sl > 0) then print_string ("SUBSUME: "^ pr2 sl ^"\n") ;
    if(!Globals.show_diff_constrs) then ( print_string ("\nDiff defs " ^ name  ^ " {\n" ^ (print_res_list res_list true) ^ "\n}\n" ));
  )
    else (if(List.length sl > 0) then print_string ("SUCCESS WITH SUBSUME: "^ pr2 sl ^"\n");)
  in
  res
    
and is_match_onefs onefs1 onefs2 name=
  let (il1, sl1, fs1) = onefs1 in
  let (il2, sl2, fs2) = onefs2 in
  if(not(!Globals.show_diff_constrs)) then 
    CEQ.checkeq_formulas_list (il1@il2) fs1 fs2 
  else
    let res(* ,res_list *) = CEQ.checkeq_formulas_list(* _with_diff *) (il1@il2) fs1 fs2 in
    (* if(not(res)) then  *)
    (*   print_string ("\nDiff onefs " ^ name^ " {\n" ^ (print_res_list res_list false) ^ "\n}\n" ); *)
    res

