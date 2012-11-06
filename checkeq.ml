open Globals
open Gen
open Cpure

module H = Hashtbl
module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module M = Lexer.Make(Token.Token)

(*for testing-compare two formulas*)
let view_diff = false

type map_table = ((CP.spec_var * CP.spec_var) list)

let string_of_pair(x: (CP.spec_var * CP.spec_var)): string =
  (
    let (a,b) = x in 
    let res = "(" ^ (CP.name_of_spec_var a) ^ ", " ^ (CP.name_of_spec_var b) ^ ")" in
    res 
  )
    
let string_of_map_table (mt: map_table): string = 
  let rec helper(mt: map_table): string = match mt with 
    |[] ->""
    |[x] -> string_of_pair x
    |x::y -> (string_of_pair x) ^ ", " ^ (helper y)
  in
  "[" ^ (helper mt) ^ "]"
    
    
let string_of_map_table_list (mtl: map_table list): string = 
  let rec helper (mtl: map_table list): string = match mtl with
    | [] -> ""
    | [x] -> string_of_map_table x
    | x::y -> (string_of_map_table x) ^ ", " ^ (helper y)
  in 
  "[" ^ (helper mtl) ^ "]"
    
let rec checkeq_formulas_x ivars f1 f2 = 
  let mtl = [[]] in
  let (res1, mtl1) = (checkeq_formulas_one ivars f1 f2 mtl) in
  let re_order mt = List.map (fun (a,b) -> (b,a)) mt in
  let imtl = List.map (fun c -> re_order c) mtl1 in
  let (res2, mtl2) =  (checkeq_formulas_one ivars f2 f1 imtl) in
  (res1&&res2, mtl1)

  (* ) *)
  (* else ( *)
  (*   let evars fs = List.filter (fun f -> List.exists (fun ivar -> (String.compare (CP.full_name_of_spec_var f) ivar != 0)) ivars ) fs in  *)
  (*   let fs1,fs2 = evars (CF.fv f1),evars (CF.fv f2) in *)
  (* (\* print_string ("VARS 1: "^ Cprinter.string_of_spec_var_list (CF.fv f1) ^ "\n"); *\) *)
  (* (\* print_string ("VARS 2: "^ Cprinter.string_of_spec_var_list (CF.fv f2) ^ "\n"); *\) *)
  (* (\* print_string ("VARS NEED TO BE ADDED1: "^ Cprinter.string_of_spec_var_list fs1 ^ "\n"); *\) *)
  (* (\* print_string ("VARS NEED TO BE ADDED2: "^ Cprinter.string_of_spec_var_list fs2 ^ "\n"); *\) *)
  (*   let f1,f2 = CF.add_quantifiers fs1 f1, CF.add_quantifiers fs2 f2 in *)
  (* (\*  print_string ("F1 after add quantifiers: "^ Cprinter.prtt_string_of_formula f1 ^ "\n"); *\) *)
  (* (\* print_string ("F2 after add quantifiers: "^ Cprinter.prtt_string_of_formula f2 ^ "\n"); *\) *)
  (*   let f1,f2 = CF.elim_exists f1,CF.elim_exists f2 in *)
  (* (\* print_string ("F1 after elim exists: "^ Cprinter.prtt_string_of_formula f1 ^ "\n"); *\) *)
  (* (\* print_string ("F2 after elim exists: "^ Cprinter.prtt_string_of_formula f2 ^ "\n"); *\) *)
  (*   let (res1, mtl1) = (checkeq_formulas_one ivars f1 f2 mtl) in *)
  (*   let re_order mt = List.map (fun (a,b) -> (b,a)) mt in *)
  (*   let imtl = List.map (fun c -> re_order c) mtl1 in *)
  (*   let (res2, mtl2) =  (checkeq_formulas_one ivars f2 f1 imtl) in *)
  (*   (res1&&res2, mtl1) *)
  (* ) *)

and checkeq_formulas ivars f1 f2 = 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "checkeq_formulas" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  checkeq_formulas_x ivars f1 f2) f1 f2
    
and checkeq_formulas_a ivars f1 f2 mtl = 
    let (res1, mtl1) = (checkeq_formulas_one ivars f1 f2 mtl) in
    let (res2, mtl2) =  (checkeq_formulas_one ivars f2 f1 mtl) in
    (res1&&res2, mtl1)

and checkeq_formulas_one (hvars: ident list) (f1: CF.formula) (f2: CF.formula)(mtl: (map_table list)): (bool*(map_table list))=
  let (f1,f2) = if(not(!Globals.dis_sem)) then (
    match f1,f2 with
      | CF.Or _, _ 
      | _, CF.Or _ -> (f1,f2)
      | _ ->(
	let evars fs = List.filter (fun f -> List.exists (fun ivar -> (String.compare (CP.full_name_of_spec_var f) ivar != 0)) hvars ) fs in 
	let fs1,fs2 = evars (CF.fv f1),evars (CF.fv f2) in
	let f1,f2 = CF.add_quantifiers fs1 f1, CF.add_quantifiers fs2 f2 in
	let f1,f2 = CF.elim_exists f1,CF.elim_exists f2 in
	(f1,f2)
      )
  )
    else (f1,f2)
  in
  match f1 with
    |CF.Base({CF.formula_base_heap = h1;
	      CF.formula_base_pure = p1}) ->(
      match f2 with 
	|CF.Base ({CF.formula_base_heap = h2;
		   CF.formula_base_pure = p2}) -> ( 
	  let (res1,mtl1) = checkeq_h_formulas hvars h1 h2 mtl in 
	  let (res2,mtl2) =  if(res1) then checkeq_mix_formulas hvars p1 p2 mtl1 else (false,[]) in
	  let _= if(res2) then Debug.ninfo_pprint ("EQ. FMT: " ^ (string_of_map_table_list mtl2)) no_pos in
	  (res2,mtl2)	
	)
	|_ ->  (false,[])
    )
    |CF.Exists({CF.formula_exists_qvars = qvars1;
		 CF.formula_exists_heap = h1;
		 CF.formula_exists_pure = p1})-> 
      (match f2 with 
	|CF.Exists ({CF.formula_exists_qvars = qvars2;
		     CF.formula_exists_heap = h2;
		     CF.formula_exists_pure = p2}) -> (
	  let (res1,mtl1) = checkeq_h_formulas hvars h1 h2 mtl in 
	  let (res2,mtl2) =  if(res1) then checkeq_mix_formulas hvars p1 p2 mtl1 else (false,[]) in
	  let _= if(res2) then Debug.ninfo_pprint ("EQ. FMT: " ^ (string_of_map_table_list mtl2)) no_pos in
	  if(res2) then
	    let new_mtl = check_qvars qvars1 qvars2 mtl2 in
	    if(List.length new_mtl > 0) then (true, new_mtl) else (false,mtl2)
	  else (res2,mtl2)
	)
	| _ -> 	(false,[]))
    | CF.Or _ ->  (match f2 with 
     	|CF.Or _  ->(
	  check_or f1 f2 hvars mtl
	)
    	|_ -> (false,[]))

    (* |CF.Or ({CF.formula_or_f1 = f11; *)
    (* 	     CF.formula_or_f2 = f12})  ->  (match f2 with *)
    (* 	|CF.Or ({CF.formula_or_f1 = f21; *)
    (* 		 CF.formula_or_f2 = f22})  ->( *)
    (* 	  let res11, mtl11 = checkeq_formulas_a hvars f11 f21 mtl in *)
    (* 	  let res1,mtl1 = if(res11) then checkeq_formulas_a hvars f12 f22 mtl *)
    (* 	    else (false,[])  *)
    (* 	  in *)
    (* 	  let res12, mtl12 = checkeq_formulas_a hvars f11 f22 mtl in *)
    (* 	  let res2,mtl2 = if(res12) then checkeq_formulas_a hvars f12 f21 mtl *)
    (* 	    else (false, [])  *)
    (* 	  in *)
    (* 	  let helper ll1 ll2 = *)
    (* 	    let helper_x l1 ll2 =  *)
    (* 	      List.map (fun l2 -> l1@l2) ll2 *)
    (* 	    in *)
    (* 	    List.concat (List.map (fun l1 -> helper_x l1 ll2) ll1) *)
    (* 	  in *)
    (* 	  let mtl1 = helper mtl11 mtl1 in *)
    (* 	  let mtl2 = helper mtl12 mtl2 in *)
    (* 	  if(res1 && res2) then (true, mtl1 @ mtl2)   (\*merge tables*\) *)
    (* 	  else if(res1) then (true, mtl1)  *)
    (* 	  else if(res2) then (true, mtl2) *)
    (* 	  else (false, []) *)
    (* 	) *)
    (* 	|_ -> (false,[])) *)

and check_or f1 f2 hvars mtl = 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "check_or" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  check_or_x f1 f2 hvars mtl) f1 f2	  
	  
and check_or_x f1 f2 hvars mtl =
  let new_mtl mtl f = List.map (fun mt -> (mt, f)) mtl in
  let rec check_one2 f1 f2 hvars mt = 
    (* print_string ("Check f1_2: " ^ (Cprinter.prtt_string_of_formula f1) ^ "\n") ; *)
    (* print_string ("Check f2: " ^ (Cprinter.prtt_string_of_formula f2) ^ "\n") ; *)
    match f2 with 
      | CF.Or ({CF.formula_or_f1 = f21;
	     CF.formula_or_f2 = f22})  -> (
	let (res1, mtl1) = check_one2 f1 f21 hvars mt in
	let (res2, mtl2) = check_one2 f1 f22 hvars mt in
	let new_mix_mtl mtl f2 = List.map (fun (mt,f) -> if (CF.isStrictConstTrue f) then (mt,f2) else if (CF.isStrictConstTrue f2) then (mt,f) else (mt, CF.mkOr f f2 no_pos)) mtl in 
	if(res1 && res2) then 
	  (
	    let mix_mtl1 = new_mix_mtl mtl1 f22 in 
	    let mix_mtl2 = new_mix_mtl mtl2 f21 in 
	    (true, mix_mtl1@mix_mtl2)
	  )
	else if(res1) then let mix_mtl1 = new_mix_mtl mtl1 f22 in (true,mix_mtl1)
	else if(res2) then let mix_mtl2 = new_mix_mtl mtl2 f21 in (true,mix_mtl2)
	else (false,[])
      )
      | _ ->  let (res,mtl) = checkeq_formulas_a hvars f1 f2 [mt] in
	      (res, new_mtl mtl (CF.mkTrue_nf no_pos))
  in
  let rec check_one1 f1 hvars mix_mtl=
    (* print_string ("Check f1: " ^ (Cprinter.prtt_string_of_formula f1) ^ "\n") ; *)
    match f1 with
      | CF.Or ({CF.formula_or_f1 = f11;
	     CF.formula_or_f2 = f12})  -> (
	let (res1,mix_mtl1) = check_one1 f11 hvars mix_mtl in
	if(res1) then (
	  let tmp_mtl = List.concat (List.map (fun (mt,l) -> List.map (fun (mt1,f) -> (mt,f)) l ) mix_mtl1 ) in 
	  check_one1 f12 hvars tmp_mtl	  
	)	      
	else (res1,mix_mtl1)
      )
      | _ -> (
	let helper mt f2 =  
	  (* print_string ("Inside one pass: Check f1: " ^ (Cprinter.prtt_string_of_formula f1) ^ "\n") ; *)
	  (* print_string ("Inside one pass: Check f2: " ^ (Cprinter.prtt_string_of_formula f2) ^ "\n") ; *)
	  let (r,l) = check_one2 f1 f2 hvars mt in 
	  (* let _ = if(r) then print_string ("Res: TRUE\n") else  print_string ("Res: FALSE\n") in *)
	  (r,(mt,l))	
	in
	let res_list = List.map (fun (mt,f2) -> helper mt f2) mix_mtl in
	let (bs, mtls) = List.split res_list in
	let b = if( List.exists (fun c -> c==true) bs) then true else false in
	let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
	let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
	if(b) then 
	  let _, mtls =  List.split true_part in
	  (b, mtls)
	else 
	  let _, mtls =  List.split false_part in
	  (b, mtls)
      )
  in
  let (res,tmp) = check_one1 f1 hvars (new_mtl mtl f2) in
  let tmp2 =  List.map (fun (a,b) -> List.map (fun (mt,f) -> mt) b) tmp in
  (res,List.concat tmp2 )

and checkeq_h_formulas_x (hvars: ident list)(hf1: CF.h_formula) (hf2: CF.h_formula)(mtl: map_table list): (bool * (map_table list))=
  let check_false_hf1 = check_false_formula hf1 in
  let check_false_hf2 = check_false_formula hf2 in
  (* let modify_mtl mtl f = List.map (fun mt -> (mt,f)) mtl in *)
  if(check_false_hf1 && check_false_hf2) then (true, [[]])
  else 
    if(check_false_hf1 || check_false_hf2) 
    then (false,[])
    else(
      match hf1 with  
	| CF.Star ({CF.h_formula_star_h1 = h1;
		    CF.h_formula_star_h2 = h2}) 
	| CF.Phase  ({CF.h_formula_phase_rd = h1;
		      CF.h_formula_phase_rw = h2}) 
	| CF.Conj  ({CF.h_formula_conj_h1 = h1;
		     CF.h_formula_conj_h2 = h2})  -> (
	  match h1,h2 with 
	    | CF.HEmp, CF.HEmp -> checkeq_h_formulas hvars h1 hf2 mtl 
	    | CF.HEmp, _ -> checkeq_h_formulas hvars h2 hf2 mtl 
	    | _, CF.HEmp -> checkeq_h_formulas hvars h1 hf2 mtl
	    | _, _ ->(	 
	      let (ph1, mtl_1) = checkeq_h_formulas hvars h1 hf2 mtl in
	      if(ph1) then checkeq_h_formulas hvars h2 hf2 mtl_1
	      else (false, [])  
	    )
	)
	| CF.DataNode n -> match_equiv_node hvars n hf2 mtl
	| CF.ViewNode n ->  match_equiv_view_node hvars n hf2 mtl
	| CF.Hole h1 -> (match hf2 with
	    |CF.Hole h2 ->  (h1 == h2, mtl)
	    |_ -> report_error no_pos "not handle Or f1 yet"
	)
	| CF.HRel r  -> (
(*DONT DELETE: for repuiring exacly the same hprel name!!!*)
	 (*  let rec exists_hp mtl =  *)
(* 	    match mtl with *)
(* 	      | [] -> false *)
(* 	      | (a,b)::y ->  *)
(* 		if(CP.is_hprel_typ a && CP.is_hprel_typ b && (not(CP.eq_spec_var a b))) then 								 true *)
(* 		else exists_hp y *)
(* 	  in *)
(* 	  let res,new_mtl = match_equiv_rel hvars r hf2 mtl in *)
(* (\*TODO: check if map tb holds any hps mapping!!!*\) *)
(* 	  if(res) then ( *)
(* 	    let new_mtl2 = List.filter (fun m -> not(exists_hp m)) new_mtl in *)
(* 	    if(List.length new_mtl2 > 0) then (res,new_mtl2) else (false, new_mtl) *)
(* 	  ) else (res,new_mtl) *)
match_equiv_rel hvars r hf2 mtl
	)
	| CF.HTrue  ->  (true, mtl)
	| CF.HFalse ->  report_error no_pos "not a case"
	| CF.HEmp   ->  (true, mtl) (*TODO: plz check*)
    )

and checkeq_h_formulas ivars hf1 hf2 mtl= 
  let pr1 = Cprinter.prtt_string_of_h_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "checkeq_h_formulas" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  checkeq_h_formulas_x ivars hf1 hf2 mtl) hf1 hf2

and check_false_formula(hf: CF.h_formula): bool =
  match hf with  
    | CF.Star ({CF.h_formula_star_h1 = h1;
		CF.h_formula_star_h2 = h2}) 
    | CF.Phase  ({CF.h_formula_phase_rd = h1;
		  CF.h_formula_phase_rw = h2}) 
    | CF.Conj  ({CF.h_formula_conj_h1 = h1;
		 CF.h_formula_conj_h2 = h2})  ->
      let ph1 = check_false_formula h1 in
      if(not ph1) then check_false_formula h2 else true
    | CF.HFalse -> true
    | CF.DataNode _ 
    | CF.ViewNode _ 
    | CF.Hole _ 
    | CF.HRel _ 
    | CF.HTrue  
    | CF.HEmp   ->  false
      
and match_equiv_node (hvars: ident list) (n: CF.h_formula_data) (hf2: CF.h_formula)(mtl: map_table list): (bool * (map_table list))=
  let rec match_equiv_node_helper (hvars: ident list) (n: CF.h_formula_data) (hf2: CF.h_formula)(mt: map_table): (bool * (map_table list)) = match hf2 with 
    | CF.Star ({CF.h_formula_star_h1 = h1;
		CF.h_formula_star_h2 = h2}) 
    | CF.Phase  ({CF.h_formula_phase_rd = h1;
		  CF.h_formula_phase_rw = h2}) 
    | CF.Conj  ({CF.h_formula_conj_h1 = h1;
		 CF.h_formula_conj_h2 = h2})  ->
     let (ph1, mtl1) =  match_equiv_node_helper hvars n h1 mt in
     let (ph2, mtl2) =  match_equiv_node_helper hvars n h2 mt in
     if(ph1 && ph2) then (true, mtl1 @ mtl2)   (*merge tables*)
     else if(ph1) then (true, mtl1) 
     else if(ph2) then (true, mtl2)
     else (false, [mt])
    | CF.DataNode n2 -> (
      let _ = Debug.ninfo_pprint ("node to compare: " ^ (Cprinter.prtt_string_of_h_formula hf2)) no_pos in
      let (res, mt2) = check_node_equiv hvars n n2 mt in 
      (res, [mt2])
    )
    | CF.ViewNode _
    | CF.Hole _
    | CF.HRel _ 
    | CF.HTrue -> (false,[mt])
    | CF.HFalse -> report_error no_pos "not a case"
    | CF.HEmp   -> (false,[mt])
  in
  let res_list = (List.map (fun c -> match_equiv_node_helper hvars n hf2 c) mtl) in
  let (bs, mtls) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
  let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
  if(b) then 
    let _, mtls =  List.split true_part in
    (b, List.concat mtls)
  else 
    let _, mtls =  List.split false_part in
    (b, List.concat mtls)
    
and check_node_equiv (hvars: ident list)(n1: CF.h_formula_data) (n2:  CF.h_formula_data)(mt: map_table): (bool * map_table)=
  let var1 = n1.CF.h_formula_data_node in
  let name1 = n1.CF.h_formula_data_name in
  (* let ann1 = n1.CF.h_formula_data_imm in *)
  let args1 = n1.CF.h_formula_data_arguments in
  let is_hard_n1 = (List.mem (CP.name_of_spec_var n1.CF.h_formula_data_node) hvars) in
  let var2 = n2.CF.h_formula_data_node in
  let name2 = n2.CF.h_formula_data_name in
  (* let ann2 = n2.CF.h_formula_data_imm in *)
  let args2 = n2.CF.h_formula_data_arguments in
  let is_hard_n2 = (List.mem (CP.name_of_spec_var n2.CF.h_formula_data_node) hvars) in
  (* let rec str hvars  = match hvars with *)
  (*   | [] -> "" *)
  (*   | a::y -> a ^ str y  *)
  (* in *)
  let is_hard = is_hard_n1 || is_hard_n2 in
(* if((not (CF.is_eq_node_name name1 name2)) || (is_hard && (not (CP.eq_spec_var var1 var2))) || (not (CF.is_eq_data_ann ann1 ann2)))  *)
  if((not (CF.is_eq_node_name name1 name2)) || (is_hard && (not (CP.eq_spec_var var1 var2)))) 
  then( 
    let _ = Debug.ninfo_pprint ("diff node diff name diff ann ") no_pos in 
    (false, mt) 
  (*TODO: temp eliminate ann*)
  )
  else (
    let _ = Debug.ninfo_pprint ("match node: " ^ string_of_map_table mt) no_pos in
    let (res, mt1) = if(is_hard && (CP.eq_spec_var var1 var2)) then (true, mt)  
      else add_map_rel mt (var1) (var2) in
    if(res) then check_spec_var_list_equiv hvars args1 args2 mt1
    else (false, mt1)
  )
(*translation has ensured well-typedness. *)

and check_spec_var_list_equiv  (hvars: ident list)(args1: CP.spec_var list)(args2: CP.spec_var list)(mt: map_table): (bool * map_table)=
  (*do not check type*) 
  if((List.length args1) == 0 && (List.length args2) == 0) then (true, mt)
  else (
    let (check_head,mt1) = check_spec_var_equiv hvars (List.hd args1) (List.hd args2) mt in
    if(check_head) then check_spec_var_list_equiv hvars (List.tl args1) (List.tl args2) mt1 else (check_head,[])
  )

and check_spec_var_equiv (hvars: ident list)(v1: CP.spec_var) (v2: CP.spec_var)(mt: map_table): (bool * map_table )=
  let pr1 = CP.name_of_spec_var in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table in
  Debug.no_2 "check_spec_var" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  check_spec_var_equiv_x  hvars v1 v2 mt) v1 v2

and check_spec_var_equiv_x (hvars: ident list)(v1: CP.spec_var) (v2: CP.spec_var)(mt: map_table): (bool * map_table )=
  (*do not check type*) 
  let is_hard_v1 = (List.mem (CP.name_of_spec_var v1) hvars) in
  let is_hard_v2 = (List.mem (CP.name_of_spec_var v2) hvars) in
  let is_hard = is_hard_v1 || is_hard_v2 in
  if((CP.is_null_const v1) || (CP.is_int_const v1) || is_hard) 
  then( 
    let _ = Debug.ninfo_pprint ("null const hard:  " ^ (CP.name_of_spec_var v1)) no_pos in 
    let res = CP.eq_spec_var v1 v2 in
    (res, mt)
  )
  else add_map_rel mt v1 v2

and match_equiv_view_node (hvars: ident list) (n: CF.h_formula_view) (hf2: CF.h_formula)(mtl: map_table list): (bool * (map_table list))=
  let rec match_equiv_view_node_helper (hvars: ident list) (n: CF.h_formula_view) (hf2: CF.h_formula)(mt: map_table): (bool * (map_table list)) = match hf2 with  
    | CF.Star ({CF.h_formula_star_h1 = h1;
		CF.h_formula_star_h2 = h2}) 
    | CF.Phase  ({CF.h_formula_phase_rd = h1;
		  CF.h_formula_phase_rw = h2}) 
    | CF.Conj  ({CF.h_formula_conj_h1 = h1;
		 CF.h_formula_conj_h2 = h2})  ->
      let (ph1,mtl1) =  match_equiv_view_node_helper hvars n h1 mt in
      let (ph2, mtl2) =  match_equiv_view_node_helper hvars n h2 mt in
      if(ph1 && ph2) then (true, mtl1 @ mtl2)   (*merge tables*)
      else if(ph1) then (true, mtl1) 
      else if(ph2) then (true, mtl2)
      else (false, [mt]) 
    | CF.DataNode n2 -> (false,[mt]) 
    | CF.ViewNode n2 -> let (res, mt2) = check_view_node_equiv hvars n n2 mt in (res, [mt2])
    | CF.Hole _
    | CF.HRel _ 
    | CF.HTrue -> (false,[mt])
    | CF.HFalse -> report_error no_pos "not a case"
    | CF.HEmp   -> (false,[mt])
  in
  let res_list = (List.map (fun c -> match_equiv_view_node_helper hvars n hf2 c) mtl) in
  let (bs, mtls) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
  let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
  if(b) then 
    let _, mtls =  List.split true_part in
    (b, List.concat mtls)
  else 
    let _, mtls =  List.split false_part in
    (b, List.concat mtls)

and check_view_node_equiv (hvars: ident list)(n1: CF.h_formula_view) (n2:  CF.h_formula_view)(mt: map_table): (bool * map_table)=
  let var1 = n1.CF.h_formula_view_node in
  let name1 = n1.CF.h_formula_view_name in
  let ann1 = n1.CF.h_formula_view_imm in
  let args1 = n1.CF.h_formula_view_arguments in
  let is_hard_n1 = (List.mem (CP.name_of_spec_var n1.CF.h_formula_view_node) hvars) in
  let var2 = n2.CF.h_formula_view_node in
  let name2 = n2.CF.h_formula_view_name in
  let ann2 = n2.CF.h_formula_view_imm in
  let args2 = n2.CF.h_formula_view_arguments in
  let is_hard_n2 = (List.mem (CP.name_of_spec_var n2.CF.h_formula_view_node) hvars) in
  let is_hard = is_hard_n1 || is_hard_n2 in
  if((not (CF.is_eq_node_name name1 name2)) || (is_hard && (not (CP.eq_spec_var var1 var2))) || (not (CF.is_eq_data_ann ann1 ann2))) 
  then
    (false, mt) 
  else  (
    let (res, mt1) = if(is_hard && (CP.eq_spec_var var1 var2)) then (true, mt)  
      else add_map_rel mt (var1) (var2) in
    if(res) then check_spec_var_list_equiv hvars args1 args2 mt1
    else (false, mt1)
  )

and match_equiv_rel (hvars: ident list) (r: (CP.spec_var * (CP.exp list) * loc)) (hf2: CF.h_formula)(mtl: map_table list): (bool * (map_table list))=
  let rec match_equiv_rel_helper (hvars: ident list) (r: (CP.spec_var * (CP.exp list) * loc)) (hf2: CF.h_formula)(mt: map_table): (bool * (map_table list)) = match hf2 with 
    | CF.Star ({CF.h_formula_star_h1 = h1;
		CF.h_formula_star_h2 = h2}) 
    | CF.Phase  ({CF.h_formula_phase_rd = h1;
		  CF.h_formula_phase_rw = h2}) 
    | CF.Conj  ({CF.h_formula_conj_h1 = h1;
		 CF.h_formula_conj_h2 = h2})  ->
      let (ph1, mtl1) =  match_equiv_rel_helper hvars r h1 mt in
      let (ph2,mtl2) =  match_equiv_rel_helper hvars r h2 mt in
      if(ph1 && ph2) then (true, mtl1 @ mtl2)   (*merge tables*)
      else if(ph1) then (true, mtl1) 
      else if(ph2) then (true, mtl2)
      else (false, [mt]) 
    | CF.DataNode _ 
    | CF.ViewNode _  
    | CF.Hole _ -> (false,[mt]) 
    | CF.HRel r2  ->  (
      let _ = Debug.ninfo_pprint ("Find 2nd relation  " ) no_pos in
      let (res, mt2) = check_rel_equiv hvars r r2 mt in (res, [mt2])
    )
    | CF.HTrue  -> (false,[mt]) 
    | CF.HFalse ->  report_error no_pos "not a case"
    | CF.HEmp   ->  (false,[mt]) 
  in
  let res_list = (List.map (fun c -> match_equiv_rel_helper hvars r hf2 c) mtl) in
  let (bs, mtls) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
  let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
  if(b) then 
    let _, mtls =  List.split true_part in
    (b, List.concat mtls)
  else 
    let _, mtls =  List.split false_part in
    (b, List.concat mtls)
    
and check_rel_equiv (hvars: ident list) (r1:  (CP.spec_var * (CP.exp list) * loc)) (r2:  (CP.spec_var * (CP.exp list) * loc))(mt: map_table): (bool * map_table)=
  let (n1,el1,l1) = r1 in
  let (n2,el2,l2) = r2 in
  let is_hard_r1 = (List.mem (CP.name_of_spec_var n1) hvars) in 
  let is_hard_r2 = (List.mem (CP.name_of_spec_var n2) hvars) in 
  let res = CP.eq_spec_var n1 n2 in (*eq_spec_var means same relation*)
  if(res) then (
    let res, new_mt = add_map_rel mt n1 n2 in 
    if(res) then check_exp_list_equiv hvars el1 el2 new_mt
    else (false,mt)
  )
  else (
    if(is_hard_r1 || is_hard_r2) then (false, [])
    else (
      (* let _ = Debug.ninfo_pprint ("ADD REL BEFORE: " ^ (string_of_map_table mt)) no_pos in *)
      let res, new_mt = add_map_rel mt n1 n2 in
      if(res) then check_exp_list_equiv hvars el1 el2 new_mt 
      else (false, mt)
    )
  )
and check_exp_list_equiv (hvars: ident list) (el1: CP.exp list) (el2: CP.exp list) (mt: map_table): (bool * map_table)=
  if((List.length el1) != (List.length el2)) then (false, mt) 
  else
    if((List.length el1) == 0 && (List.length el2) == 0) then (true, mt)
    else(
      let head1 = List.hd el1 in 
      let head2 = List.hd el2 in
      let (check_head, mt1) = match head1 with
	|CP.Var(sv1,_)-> (
	  let is_hard = (List.mem (CP.name_of_spec_var sv1) hvars) in
	  if(not is_hard) then (
	    match head2 with
	      |CP.Var(sv2,_) ->  let is_hard2 = (List.mem (CP.name_of_spec_var sv2) hvars) in 
				 if(not is_hard2) then (add_map_rel mt sv1 sv2)
				 else (CP.eq_spec_var sv1 sv2, mt)
	      |_ -> (false, mt)
	  )
	  else match head2 with
	    |CP.Var(sv2,_) -> (CP.eq_spec_var sv1 sv2, mt)
	    |_ -> (false, mt)
	) 
	|_ -> (true, mt) (*scale down: process only spec var as relation arguments*)
      in
      if(check_head) then (
	let res, mtt = check_exp_list_equiv hvars (List.tl el1) (List.tl el2) mt1 in 
	(res, mtt)
      )
      else (false, mt)
    )

and match_equiv_emp (hf2: CF.h_formula): bool=
  match hf2 with 
    | CF.Star ({CF.h_formula_star_h1 = h1;
		CF.h_formula_star_h2 = h2}) 
    | CF.Phase  ({CF.h_formula_phase_rd = h1;
		  CF.h_formula_phase_rw = h2}) 
    | CF.Conj  ({CF.h_formula_conj_h1 = h1;
		 CF.h_formula_conj_h2 = h2})  ->
      let ph1 =  match_equiv_emp h1  in
      if(not ph1) then  match_equiv_emp h2 else true
    | CF.DataNode _ 
    | CF.ViewNode _
    | CF.Hole _
    | CF.HRel _ 
    | CF.HTrue 
    | CF.HFalse -> false
    | CF.HEmp   -> true

and add_map_rel_x (mt: map_table) (v1: CP.spec_var) (v2: CP.spec_var): (bool * map_table) = 
  let vn1 = CP.full_name_of_spec_var v1 in
  let vn2 = CP.full_name_of_spec_var v2 in
  let rec check_exist (vn :ident) mto: bool = 
    match mto with 
      | []-> false 
      | i1::y -> (String.compare vn (CP.full_name_of_spec_var i1)) == 0  || (check_exist vn y)
  in
  if(List.exists (fun (i1, i2) -> (((String.compare vn1 (CP.full_name_of_spec_var i1)) == 0 && (String.compare vn2 (CP.full_name_of_spec_var i2)) == 0) )) mt) then (true, mt)
  else (
    let mtl,mtr = List.split mt in
    let check_v1 = check_exist vn1 mtl in
    let check_v2 = check_exist vn2 mtr in
    if(check_v1 || check_v2) then (false, []) else (true, ((v1,v2)::mt))
  )

and add_map_rel (mt: map_table) (v1: CP.spec_var) (v2: CP.spec_var): (bool * map_table) = 
  let pr1 = CP.full_name_of_spec_var in
  let pr2 b = if(b) then "SUCCESS" else "FAIL" in
  let pr3 = string_of_map_table in
  Debug.no_2 "add_map_rel" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  add_map_rel_x mt v1 v2) v1 v2

and checkeq_mix_formulas (hvars: ident list)(mp1: MCP.mix_formula) (mp2: MCP.mix_formula)(mtl: map_table list): (bool * (map_table list))=
  match mp1,mp2 with
    | MCP.MemoF mp1,MCP.MemoF mp2  -> (true, mtl)
    | MCP.OnePF f1, MCP.OnePF f2 ->  checkeq_p_formula hvars f1 f2 mtl
    | _,_ ->  (false, mtl)

and checkeq_p_formula_x (hvars: ident list)(p1: CP.formula) (p2: CP.formula)(mtl: map_table list): (bool * (map_table list))=
  let pf1,pf2 = CP.norm_form p1, CP.norm_form p2 in
  let _ = Debug.ninfo_pprint ("Case 2 formula") no_pos in 
  match pf1 with
    | BForm (b1,_) -> match_equiv_bform hvars b1 pf2 mtl
    | And(f1,f2,_) ->  (
      let res, mtl1 = checkeq_p_formula hvars f1 pf2 mtl in
      if(res) then checkeq_p_formula hvars f2 pf2 mtl1 
      else (res, []) 
    )
    | AndList _ -> report_error no_pos "not handle checkeq 2 formula that have ANDLIST yet"
    | Or f -> match_equiv_orform hvars f pf2 mtl
    | Not(f,_,_) -> match_equiv_notform hvars f pf2 mtl
    | Forall _ 
    | Exists _ -> report_error no_pos "not handle checkeq 2 formula that have forall and exists yet"

and checkeq_p_formula  hvars pf1 pf2 mtl = 
  let pr1 = Cprinter.string_of_pure_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "checkeq_p_formula" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  checkeq_p_formula_x hvars pf1 pf2 mtl) pf1 pf2

and match_equiv_bform  hvars b1 pf2 mtl = 
  let pr1 = Cprinter.string_of_pure_formula in
  let pr4 = Cprinter.string_of_b_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "match_equiv_bform" pr4 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  match_equiv_bform_x hvars b1 pf2 mtl) b1 pf2

and match_equiv_bform_x (hvars: ident list)(b1: CP.b_formula) (pf2: CP.formula)(mtl: map_table list): (bool * (map_table list)) =
  let rec match_equiv_bform_helper hvars b1 pf mt= match pf with
    | BForm (b2,_) -> check_equiv_bform hvars b1 b2 mt
    | And(f1,f2,_) ->  (
      let res1, mtl1 = match_equiv_bform_helper hvars b1 f1 mt in
      let res2, mtl2 = match_equiv_bform_helper hvars b1 f2 mt in 
      if(res1 && res2) then (true, mtl1 @ mtl2)   (*merge tables*)
      else if(res1) then (true, mtl1) 
      else if(res2) then (true, mtl2)
      else (false, [mt])
    )
    | AndList _ ->  report_error no_pos "not support andlist yet"
    | Or _
    | Not _
    | Forall _ 
    | Exists _ -> (false, [mt])
  in
  let res_list = List.map (fun mt ->  match_equiv_bform_helper hvars b1 pf2 mt) mtl in
  let (bs, mtls) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
  let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
  if(b) then 
    let _, mtls =  List.split true_part in
    (b, List.concat mtls)
  else 
    let _, mtls =  List.split false_part in
    (b, List.concat mtls)

and check_equiv_bform  hvars b1 b2 mtl = 
  let pr1 = Cprinter.string_of_b_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "check_equiv_bform" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  check_equiv_bform_x hvars b1 b2 mtl) b1 b2

and check_equiv_bform_x (hvars: ident list)(b1: CP.b_formula) (b2: CP.b_formula)(mt: map_table): (bool * (map_table list)) =
  match b1,b2 with
    | (BConst (true,_),_),  (BConst (true,_),_) -> (true,[mt])
    | (BConst (false,_),_),  (BConst (false,_),_) -> (true,[mt])
    | (Eq (e11,e12,_), _) , (Eq (e21,e22,_) , _) 
    | (Neq (e11,e12,_), _) , (Neq (e21,e22,_) , _)  ->
      (
	let helper e11 e12 e21 e22 = 
	  match e11,e12,e21,e22 with
            | Var (v11,_),Var (v12,_),Var (v21,_),Var (v22,_)-> 
	      let res11, mt11 = check_spec_var_equiv hvars v11 v21 mt in 
	      let res12, mt12 = check_spec_var_equiv hvars v12 v22 mt11 in
	      let res1,mt1 = if(res11&&res12) then (res11,mt12) else (false,mt) in 
	      let res21, mt21 = check_spec_var_equiv hvars v11 v22 mt in 
	      let res22, mt22 = check_spec_var_equiv hvars v12 v21 mt21 in 
	      let res2,mt2 = if(res21&&res22) then (res21,mt22) else (false,mt) in 
	      if(res1 && res2) then (true, [mt1] @ [mt2])   (*merge tables*)
	      else if(res1) then (true, [mt1]) 
	      else if(res2) then (true, [mt2])
	      else (false, [mt])
            | Var (v11,_),IConst (v12,_),Var (v21,_),IConst (v22,_)-> 
	      let res1, mt1 = check_spec_var_equiv hvars v11 v21 mt in 
              let res2 = (v12= v22) in
	      if(res1 && res2) then (true, [mt1])   (*merge tables*)
	      else (false, [mt])
            | Var (v11,_),FConst (v12,_),Var (v21,_),FConst (v22,_)-> 
	      let res1, mt1 = check_spec_var_equiv hvars v11 v21 mt in 
              let res2 = (v12= v22) in
	      if(res1 && res2) then (true, [mt1])   (*merge tables*)
	      else (false, [mt])
	    | Var (v11,_),Null _,Var (v21,_),Null _-> 
	      let res1, mt1 = check_spec_var_equiv hvars v11 v21 mt in 
	      if(res1) then (true, [mt1])   (*merge tables*)
	      else (false, [mt])
            | _ -> (false, [mt])
	in
	let (res1,mtl1) = helper e11 e12 e21 e22 in
	if(res1) then (res1,mtl1)
	else (
	  let (res2,mtl2) = helper e12 e11 e22 e21 in
	  if(res2) then (res2,mtl2)
	  else (
	    let (res3,mtl3) = helper e11 e12 e22 e21 in
	    if(res3) then (res3,mtl3)
	    else (
	      let (res4,mtl4) = helper e12 e11 e21 e22 in
	      if(res4) then (res4,mtl4)
	      else (false, [mt])
	    )
	  )
	)
      )
    | (Lt (e11,e12,_), _) , (Lt (e21,e22,_) , _) 
    | (Lte (e11,e12,_), _) , (Lte (e21,e22,_) , _) 
    | (Gt (e11,e12,_), _) , (Gt (e21,e22,_) , _) 
    | (Gte (e11,e12,_), _) , (Gte (e21,e22,_) , _) -> 
      (match e11,e12,e21,e22 with
        | Var (v11,_),Var (v12,_),Var (v21,_),Var (v22,_)-> 
	  let res11, mt11 = check_spec_var_equiv hvars v11 v21 mt in 
	  let res12, mt12 = check_spec_var_equiv hvars v12 v22 mt11 in
	  let res1,mt1 = if(res11&&res12) then (res11,mt12) else (false,mt) in 
	  if(res1) then (true, [mt1])   (*merge tables*)
	  else (false, [mt])
        | Var (v11,_),IConst (v12,_),Var (v21,_),IConst (v22,_)-> 
	  let res1, mt1 = check_spec_var_equiv hvars v11 v21 mt in 
          let res2 = (v12= v22) in
	  if(res1 && res2) then (true, [mt1])   (*merge tables*)
	  else (false, [mt])
        | IConst (v11,_),Var (v12,_),IConst (v21,_),Var (v22,_)-> 
	  let res1, mt1 = check_spec_var_equiv hvars v12 v22 mt in 
          let res2 = (v11= v21) in
	  if(res1 && res2) then (true, [mt1])   (*merge tables*)
	  else (false, [mt])
        | Var (v11,_),FConst (v12,_),Var (v21,_),FConst (v22,_)-> 
	  let res1, mt1 = check_spec_var_equiv hvars v11 v21 mt in 
          let res2 = (v12= v22) in
	  if(res1 && res2) then (true, [mt1])   (*merge tables*)
	  else (false, [mt])
        | FConst (v11,_),Var (v12,_),FConst (v21,_),Var (v22,_)-> 
	  let res1, mt1 = check_spec_var_equiv hvars v12 v22 mt in 
          let res2 = (v11= v21) in
	  if(res1 && res2) then (true, [mt1])   (*merge tables*)
	  else (false, [mt])
        | _ -> (false, [mt])
      )
    | (BVar (v1,_),_),(BVar (v2,_),_) -> let res, mt = check_spec_var_equiv hvars v1 v2 mt in if(res) then (res,[mt]) else (false,[mt])
    | (RelForm r1,_), (RelForm r2,_) ->  let res, new_mt = check_rel_equiv hvars r1 r2 mt in (res,[new_mt])
    | _ -> (false, [mt])

and match_equiv_orform (hvars: ident list) (of1: (formula * formula * (formula_label option) * loc)) (pf2: CP.formula)(mtl: map_table list): (bool * (map_table list)) =
  let rec match_equiv_bform_helper hvars of1 pf mt= match pf with
    | BForm (b2,_) ->  (false, [mt])
    | And(f1,f2,_) ->  (
      let res1, mtl1 = match_equiv_bform_helper hvars of1 f1 mt in
      let res2, mtl2 = match_equiv_bform_helper hvars of1 f2 mt in 
      if(res1 && res2) then (true, mtl1 @ mtl2)   (*merge tables*)
      else if(res1) then (true, mtl1) 
      else if(res2) then (true, mtl2)
      else (false, [mt])
    )
    | AndList _ -> (
      report_error no_pos "and list"
    )
    | Or(f1,f2,_,_)->( 
      let (if1, if2,_,_) = of1 in
      let res11, mtl11 = checkeq_p_formula hvars f1 if1 [mt] in
      let res1,mtl1 = checkeq_p_formula hvars f2 if2 mtl11 in
      let res12, mtl12 = checkeq_p_formula hvars f1 if2 [mt] in
      let res2,mtl2 = checkeq_p_formula hvars f2 if1 mtl12 in
      if(res1 && res2) then (true, mtl1 @ mtl2)   (*merge tables*)
      else if(res1) then (true, mtl1)
      else if(res2) then (true, mtl2)
      else (false, [])
    )
    | Not _
    | Forall _ 
    | Exists _ -> (false, [mt])
  in
  let res_list = List.map (fun mt ->  match_equiv_bform_helper hvars of1 pf2 mt) mtl in
  let (bs, mtls) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
  let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
  if(b) then 
    let _, mtls =  List.split true_part in
    (b, List.concat mtls)
  else 
    let _, mtls =  List.split false_part in
    (b, List.concat mtls)
    

and match_equiv_notform  hvars b1 pf2 mtl = 
  let pr1 = Cprinter.string_of_pure_formula in
  let pr4 = Cprinter.string_of_pure_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "match_equiv_notform" pr4 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  match_equiv_notform_x hvars b1 pf2 mtl) b1 pf2

and match_equiv_notform_x  (hvars: ident list)(f1: CP.formula) (pf2: CP.formula)(mtl: map_table list): (bool * (map_table list)) =
  let rec match_equiv_notform_helper hvars f1 pf2 mt= 
    match pf2 with
      | BForm (b1,_) -> (false,[mt])
      | And(pf1,pf2,_) ->  (
	let res1, mtl1 = match_equiv_notform_helper hvars f1 pf1 mt in
	let res2, mtl2 = match_equiv_notform_helper hvars f1 pf2 mt in 
	if(res1 && res2) then (true, mtl1 @ mtl2)   (*merge tables*)
	else if(res1) then (true, mtl1) 
	else if(res2) then (true, mtl2)
	else (false, [mt])
      )
      | AndList _ -> report_error no_pos "not handle ANDLIST yet"
      | Or f -> (false,[mt])
      | Not(f2,_,_) -> report_error no_pos "temp: not handle not yet" (* checkeq_p_formula hvars f1 f2 mtl *)
      | Forall _ 
      | Exists _ -> report_error no_pos "not handle forall and exists yet"
  in
  let res_list = List.map (fun mt ->  match_equiv_notform_helper hvars f1 pf2 mt) mtl in
  let (bs, mtls) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
  let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
  if(b) then 
    let _, mtls =  List.split true_part in
    (b, List.concat mtls)
  else 
    let _, mtls =  List.split false_part in
    (b, List.concat mtls)

and check_qvars_helper sv mt =
    match mt with
      | [] -> None
      | (a,b)::y -> if(CP.eq_spec_var sv a) then  Some b
	else if(CP.eq_spec_var sv b) then Some a
	else check_qvars_helper sv y

and check_qvars_mt qvars1 qvars2 mt = 
    if(List.length qvars1 == List.length qvars2) then (
      match qvars1 with
	| [] -> true
	| sv::y -> (
	  let sv2l = check_qvars_helper sv mt in
	  match sv2l with
	    | None -> false
	    | Some sv2 -> (
	      let y2 = List.filter (fun a -> not (CP.eq_spec_var a sv2) ) qvars2 in
	      check_qvars_mt y y2 mt
	    )
	)
    )
    else false

and check_qvars qvars1 qvars2 mtl =
(*there is no similar specvar in qvars*)
  List.concat (List.map (fun mt -> let res = check_qvars_mt qvars1 qvars2 mt in if(res) then [mt] else []) mtl )

and check_qvars_mix_mtl qvars1 qvars2 mix_mtl =
  List.concat (List.map (fun (mt,f) -> let res = check_qvars_mt qvars1 qvars2 mt in if(res) then [(mt,f)] else []) mix_mtl )

(*******************************check equivalent with diff***************************************)
(************************************************************************************************)
and checkeq_formulas_with_diff_mt_x ivars f1 f2 mtl = 
  let re_order mt = List.map (fun (a,b) -> (b,a)) mt in
  let (res1, mix_mtl1) = (checkeq_formulas_one_with_diff ivars f1 f2 mtl) in
  let check_back mix_mt f2 f1 res1= (
    let mt,f = mix_mt in 		
    let (res2, mix_mtl2) =  (checkeq_formulas_one_with_diff ivars f2 f1 [re_order mt]) in
    (res2&&res1,List.map (fun (mt1,f1) -> (mt,f,f1)) mix_mtl2)
  )
  in 
  if(List.length mix_mtl1  == 0) then (
    let _ = checkeq_formulas_one_with_diff ivars f2 f1 [[]] in
    (false, [])
  )
  else (
    let res_list = List.map (fun mix_mt -> check_back mix_mt f2 f1 res1) mix_mtl1 in 
    let (bs, mtls) = List.split res_list in
    let b = if( List.exists (fun c -> c==true) bs) then true else false in
    let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
    let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
    let fres = b &&res1 in 
    let (r,fs) = if(fres) then 
	let _, mtls =  List.split true_part in
	(fres, List.concat mtls)
      else 
	let _, mtls =  List.split false_part in
	(fres, List.concat mtls)
    in
    let _ = 
      if(!Globals.show_diff) then (
	if(r) then (
	  let mtl =  List.map (fun (a,_,_) -> a) fs in 
	  Debug.info_pprint ("Final MTL: " ^ (string_of_map_table_list mtl)) no_pos
	)
	else (
	  let print_triple mt f1 f2 =  
	    let str = ("\nDIFF F1: " ^ Cprinter.prtt_string_of_formula f1 ^ "\n" 
		       ^ "DIFF F2: " ^ Cprinter.prtt_string_of_formula f2 ^ "\n"
		       ^ "CURRENT MT: " ^ string_of_map_table mt)
	    in
	    Debug.info_pprint (str) no_pos 
	  in 
	  let _ = List.map (fun (a,b,c) -> print_triple a b c) fs in
	  ()
	)
      )
    in
    (r,fs)
  )

and checkeq_formulas_with_diff_mt ivars f1 f2 mtl= 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = pr_list_ln (pr_triple string_of_map_table pr1 pr1) in
  Debug.no_2 "checkeq_formulas_with_diff_mt" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  checkeq_formulas_with_diff_mt_x ivars f1 f2 mtl) f1 f2

and checkeq_formulas_with_diff_x ivars f1 f2 = 
  let mtl = [[]] in
  checkeq_formulas_with_diff_mt ivars f1 f2 mtl
    
and checkeq_formulas_with_diff ivars f1 f2 = 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = pr_list_ln (pr_triple string_of_map_table pr1 pr1) in
  Debug.no_2 "checkeq_formulas_with_diff" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  checkeq_formulas_with_diff_x ivars f1 f2) f1 f2

and checkeq_formulas_one_with_diff ivars f1 f2 mtl= 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = pr_list_ln (pr_pair string_of_map_table pr1) in
  Debug.no_2 "checkeq_formulas_one_with_diff" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  checkeq_formulas_one_with_diff_x ivars f1 f2 mtl) f1 f2

and checkeq_formulas_one_with_diff_x (hvars: ident list) (f1: CF.formula) (f2: CF.formula)(mtl: (map_table list)): (bool*((map_table * CF.formula) list))=
  let (f1,f2) = if(not(!Globals.dis_sem)) then (
    match f1,f2 with
      | CF.Or _, _ 
      | _, CF.Or _ -> (f1,f2)
      | _ ->(
	let evars fs = List.filter (fun f -> List.exists (fun ivar -> (String.compare (CP.full_name_of_spec_var f) ivar != 0)) hvars ) fs in 
	let fs1,fs2 = evars (CF.fv f1),evars (CF.fv f2) in
	let f1,f2 = CF.add_quantifiers fs1 f1, CF.add_quantifiers fs2 f2 in
	let f1,f2 = CF.elim_exists f1,CF.elim_exists f2 in
	(f1,f2)
      )
  )
    else (f1,f2)
  in
  match f1 with
    |CF.Base({CF.formula_base_heap = h1;
	      CF.formula_base_pure = p1}) ->(
      match f2 with 
	|CF.Base ({CF.formula_base_heap = h2;
		   CF.formula_base_pure = p2}) -> (
	  let (res1,mix_mtl1) = checkeq_h_formulas_with_diff hvars h1 h2 mtl in
	  let mtl1,diff1 = List.split mix_mtl1 in (*temporary*)
	  let (res2,mix_mtl2) =  checkeq_mix_formulas_with_diff hvars p1 p2 mix_mtl1 in
	  let mtl2,diff2 = List.split mix_mtl2 in (*temporary*)
	  (res1&&res2,mix_mtl2)
	)
	|_ ->  let _ = if(!Globals.show_diff) then Debug.info_pprint ("DIFF: Base formula") no_pos in
	       (false,[])
    )
    |CF.Exists({CF.formula_exists_qvars = qvars1;
		 CF.formula_exists_heap = h1;
		 CF.formula_exists_pure = p1})->
      (match f2 with 
	|CF.Exists ({CF.formula_exists_qvars = qvars2;
		     CF.formula_exists_heap = h2;
		     CF.formula_exists_pure = p2}) -> (
	  let (res1,mix_mtl1) = checkeq_h_formulas_with_diff hvars h1 h2 mtl in
	  let mtl1,diff1 = List.split mix_mtl1 in (*temporary*)
	  let (res2,mix_mtl2) =  checkeq_mix_formulas_with_diff hvars p1 p2 mix_mtl1 in
	  let mtl2,diff2 = List.split mix_mtl2 in (*temporary*)
	  let res= res1&&res2 in
	  if(res) then
	    let new_mix_mtl = check_qvars_mix_mtl qvars1 qvars2 mix_mtl2 in
	    if(List.length new_mix_mtl > 0) then (true, new_mix_mtl) else (false,mix_mtl2)
	  else  (res,mix_mtl2)
	)
	| _ ->  let _ = if(!Globals.show_diff) then Debug.info_pprint ("DIFF: Exists formula") no_pos in 
		 (false,[]))
    |CF.Or ({CF.formula_or_f1 = f11;
	     CF.formula_or_f2 = f12})  ->  (match f2 with
	|CF.Or ({CF.formula_or_f1 = f21;
		 CF.formula_or_f2 = f22})  -> (
	  let res11, mix_mtl11 = checkeq_formulas_one_with_diff hvars f11 f21 mtl in
	  let res12, mix_mtl12 = checkeq_formulas_one_with_diff hvars f12 f22 mtl in
	  let res1 = res11 && res12 in
	  let res21, mix_mtl21 = checkeq_formulas_one_with_diff hvars f11 f22 mtl in
	  let res22, mix_mtl22 = checkeq_formulas_one_with_diff hvars f12 f21 mtl in
	  let res2 = res21 && res22 in

	  let helper ll1 ll2 =
	    let helper_x l1 ll2 = 
	      List.map (fun l2 -> let mt1,f1 = l1 in
				  let mt2,f2 = l2 in
				  (mt1@mt2, CF.Or ({CF.formula_or_f1 = f1; CF.formula_or_f2 = f2;CF.formula_or_pos = no_pos}))
	      ) ll2
	    in
	    List.concat (List.map (fun l1 -> helper_x l1 ll2) ll1)
	  in

	  let mix_mtl1 = helper mix_mtl11 mix_mtl12 in
	  let mix_mtl2 = helper mix_mtl21 mix_mtl22 in
	  let count mix_mtls = match mix_mtls with
	    | [] -> 0
	    | (mt,x)::y -> CF.no_of_cnts_fml x (*no count of relation*)
	  in
	  let choose m1 m2 = let c1 = count m1 in
			     let c2 = count m2 in
			     if(c2 > c1) then m1 else
			       if(c1 > c2) then m2 else 
				 m1@m2
	  in
	  if(res1 && res2) then (true, mix_mtl1 @ mix_mtl2)   (*merge tables*)
	  else if(res1) then (true, mix_mtl1) 
	  else if(res2) then (true, mix_mtl2)
	  else (false, choose mix_mtl1 mix_mtl2)
	)
	|_ ->   let _ =  if(!Globals.show_diff) then Debug.info_pprint ("DIFF: Or formula") no_pos in  (false,[]))

and checkeq_h_formulas_with_diff_x (hvars: ident list)(hf1: CF.h_formula) (hf2: CF.h_formula)(mtl: map_table list): (bool * ((map_table * CF.h_formula) list))=
  let _ = Debug.ninfo_pprint ("Compare heap formulas ") no_pos in
  let check_false_hf1 = check_false_formula hf1 in
  let check_false_hf2 = check_false_formula hf2 in
  let modify_mtl mtl f = List.map (fun mt -> (mt,f)) mtl in
  if(check_false_hf1 && check_false_hf2) then (true, [([],CF.HFalse)])
  else 
    if(check_false_hf1 || check_false_hf2) 
    then (false,[([],CF.HFalse)])
    else(
      match hf1 with  
	| CF.Star ({CF.h_formula_star_h1 = h1;
		    CF.h_formula_star_h2 = h2}) 
	| CF.Phase  ({CF.h_formula_phase_rd = h1;
		      CF.h_formula_phase_rw = h2}) 
	| CF.Conj  ({CF.h_formula_conj_h1 = h1;
		     CF.h_formula_conj_h2 = h2})  -> (
	  match h1,h2 with 
	    | CF.HEmp, CF.HEmp -> checkeq_h_formulas_with_diff hvars h1 hf2 mtl 
	    | CF.HEmp, _ -> checkeq_h_formulas_with_diff hvars h2 hf2 mtl 
	    | _, CF.HEmp -> checkeq_h_formulas_with_diff hvars h1 hf2 mtl
	    | _, _ ->(	 
	      let helper fl hf =  let _ = Debug.ninfo_pprint ("ADD h_formula: " ^ (Cprinter.prtt_string_of_h_formula hf)) no_pos in
				  List.map (fun f -> CF.mkStarH f hf no_pos) fl in 
	      let count_hd fl = match fl with
		| [] -> 0
		| x::y -> CF.no_of_cnts_heap x
	      in
	      let (ph1, mix_mtl_1) = checkeq_h_formulas_with_diff hvars h1 hf2 mtl in

	      let mtl_1 = List.map (fun (a,b) -> a) mix_mtl_1 in (*temporary*)
	      let diff_1 = List.map (fun (a,b) -> b) mix_mtl_1 in (*temporary*) 
	      let b1,mix_mtl1 = if(ph1) then (
		let _ = Debug.ninfo_pprint ("INPUT MTL for RHS" ^ (string_of_map_table_list mtl_1)) no_pos in
		let (ph2, mix_mtl_2) = checkeq_h_formulas_with_diff hvars h2 hf2 mtl_1 in
		let pr3 =  pr_list_ln (pr_pair string_of_map_table Cprinter.prtt_string_of_h_formula) in
		let _ = Debug.ninfo_pprint ("RHS:::::" ^ (pr3 mix_mtl_2)) no_pos in
		if(ph2)then (true,mix_mtl_2) else  (false,mix_mtl_2)
	      )
		else (false,List.combine mtl_1 (helper diff_1 h2))  
	      in
	      let b2, mix_mtl2 = if(b1) then (b1,mix_mtl1)
		else (
		  let (ph1_2, mix_mtl1_2) = checkeq_h_formulas_with_diff hvars h2 hf2 mtl in
		  let mtl1_2 = List.map (fun (a,b) -> a) mix_mtl1_2 in (*temporary*)
		  let diff1_2 = List.map (fun (a,b) -> b) mix_mtl1_2 in (*temporary*)
		  if(ph1_2) then (
		    let (ph2_2, mix_mtl2_2) = checkeq_h_formulas_with_diff hvars h1 hf2 mtl1_2 in
		    if(ph2_2) then (true,mix_mtl2_2) else (false,mix_mtl2_2)
		  )
		  else  (false,List.combine mtl1_2 (helper diff1_2 h1))  
		)
	      in
	      if(b1) then (b1,mix_mtl1) else(
		if(b2) then (b2,mix_mtl2) else (
		  let mtl1 = List.map (fun (a,b) -> a) mix_mtl1 in (*temporary*) 
		  let diff1 = List.map (fun (a,b) -> b) mix_mtl1 in (*temporary*)
		  let mtl2 = List.map (fun (a,b) -> a) mix_mtl2 in (*temporary*)  
		  let diff2 = List.map (fun (a,b) -> b) mix_mtl2 in (*temporary*)
		  let c1 = count_hd diff1 in
		  let c2 = count_hd diff2 in
		  if(c2 > c1) then (false,mix_mtl1) 
		  else if(c1 > c2) then (false,mix_mtl2)
		  else if(c1 = CF.no_of_cnts_heap hf1) then (false,mix_mtl1)
		  else (false,List.combine (mtl1 @ mtl2) (diff1 @ diff2))
		)
	      )
	    )
	)
	| CF.DataNode n -> let (a,b) = match_equiv_node hvars n hf2 mtl in if(a) then (a,modify_mtl b CF.HEmp) else (a,modify_mtl b hf1)
	| CF.ViewNode n -> let (a,b) = match_equiv_view_node hvars n hf2 mtl in if(a) then (a,modify_mtl b CF.HEmp) else (a,modify_mtl b hf1)
	| CF.Hole h1 -> (match hf2 with
	    |CF.Hole h2 -> let (a,b) = (h1 == h2, mtl)  in if(a) then (a,modify_mtl b CF.HEmp) else (a,modify_mtl b hf1)
	    |_ -> report_error no_pos "not handle Or f1 yet"
	)
	| CF.HRel r  -> (
	  let res,new_mtl = match_equiv_rel hvars r hf2 mtl in
	  if(res) then (res,modify_mtl new_mtl CF.HEmp) else (res,modify_mtl new_mtl hf1)
	  (* let rec exists_hp mtl =  *)
	  (*   match mtl with *)
	  (*     | [] -> false *)
	  (*     | (a,b)::y ->  *)
	  (* 	if(CP.is_hprel_typ a && CP.is_hprel_typ b && (not(CP.eq_spec_var a b))) then 								 true *)
	  (* 	else exists_hp y *)
	  (* in *)
	  (* let res,new_mtl = match_equiv_rel hvars r hf2 mtl in *)
	  (* (\*TODO: check if map tb holds any hps mapping!!!*\) *)
	  (* if(res) then ( *)
	  (*   let new_mtl2 = List.filter (fun m -> not(exists_hp m)) new_mtl in *)
	  (*   if(List.length new_mtl2 > 0) then (res,modify_mtl new_mtl2 CF.HEmp) else (false,modify_mtl new_mtl hf1) *)
	  (* ) else (res,modify_mtl new_mtl hf1) *)
	)
	| CF.HTrue  ->  (true, modify_mtl mtl CF.HEmp)
	| CF.HFalse ->  report_error no_pos "not a case"
	| CF.HEmp   ->  (true, modify_mtl mtl CF.HEmp) (*TODO: plz check*)
    )

and checkeq_h_formulas_with_diff ivars hf1 hf2 mtl= 
  let pr1 = Cprinter.prtt_string_of_h_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 =  pr_list_ln (pr_pair string_of_map_table Cprinter.prtt_string_of_h_formula) in
  (* let pr4 = pr_list_ln Cprinter.prtt_string_of_h_formula in *)
  let pr5 =  string_of_map_table_list in
  Debug.no_3 "checkeq_h_formulas_with_diff" pr5 pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ _ ->  checkeq_h_formulas_with_diff_x ivars hf1 hf2 mtl) mtl hf1 hf2

and checkeq_mix_formulas_with_diff (hvars: ident list)(mp1: MCP.mix_formula) (mp2: MCP.mix_formula)(mix_mtl: (map_table * CF.h_formula) list): (bool * ((map_table * CF.formula) list))=
  let pr1 = Cprinter.string_of_mix_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 =  pr_list_ln (pr_pair string_of_map_table Cprinter.prtt_string_of_formula) in
 let pr5 =  pr_list_ln (pr_pair string_of_map_table Cprinter.prtt_string_of_h_formula) in
  let pr4 = pr_list_ln Cprinter.prtt_string_of_h_formula in
  Debug.no_3 "checkeq_mix_formulas_with_diff" pr5 pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ _ ->  checkeq_mix_formulas_with_diff_x hvars mp1 mp2 mix_mtl) mix_mtl mp1 mp2

and checkeq_mix_formulas_with_diff_x (hvars: ident list)(mp1: MCP.mix_formula) (mp2: MCP.mix_formula)(mix_mtl: (map_table * CF.h_formula) list): (bool * ((map_table * CF.formula) list))=
  let check_heap = List.exists (fun (mt, hf) -> CF.is_empty_heap hf) mix_mtl in  
  let count mix_mtls = match mix_mtls with
    | [] -> 0
    | (mt,x)::y -> CF.no_of_cnts_fml x (*no count of relation*)
  in
  let rec get_min_f lst_of_mix_mtls =
    match lst_of_mix_mtls with
      | [] -> report_error no_pos "should not be emp: checkeq_mix_formulas.get_min_f"
      | [x] -> (count x,x)
      | hd::tl -> (
	let (t,m_mtls) = get_min_f tl in
	let c = count hd in
	if(c < t) then (c, hd)
	else if(c == t) then (c,hd@m_mtls)
	else (t,m_mtls)
      )	  
  in
  let checkeq_mix_formulas_one mp1 mp2 mtl = (
    match mp1,mp2 with
      | MCP.MemoF mp1,MCP.MemoF mp2  -> report_error no_pos "Have not support comparing 2 MemoF yet"
      | MCP.OnePF f1, MCP.OnePF f2 ->  checkeq_p_formula_with_diff hvars f1 f2 mtl
      | _,_ ->  (false, List.map (fun mt -> (mt,CP.mkTrue no_pos)) mtl)
  ) in
  let helper mp1 mp2 mt hf =
    let _ = Debug.ninfo_pprint ("Need to add hf: " ^ (Cprinter.string_of_h_formula hf)) no_pos in 
    let (b,nmtl) = checkeq_mix_formulas_one mp1 mp2 [mt] in
    let mkF hf pf = CF.mkBase hf (MCP.OnePF (pf)) CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in 
    let mix_mtl1 = List.map (fun (mt1, pf) -> (mt1,mkF hf pf)) nmtl in
    (b,mix_mtl1)
  in 
  let res_list = List.map (fun (mt, hf) -> helper mp1 mp2 mt hf) mix_mtl in 
  let (bs, _) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
  let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
  if(b) then 
    let _, mtls =  List.split true_part in
    (b, List.concat mtls)
  else 
    let _, mtls =  List.split false_part in
    let (c,new_mtls) = get_min_f mtls in
    (b, new_mtls)

and checkeq_p_formula_with_diff_x (hvars: ident list)(p1: CP.formula) (p2: CP.formula)(mtl: map_table list): (bool * (map_table * CP.formula) list)=
(*(MCP.mkMTrue pos)*)
  let pf1,pf2 = CP.norm_form p1, CP.norm_form p2 in
  let _ = Debug.ninfo_pprint ("Case 2 formula") no_pos in 
  let modify mtl pf = List.map (fun mt -> (mt,pf)) mtl in
  match pf1 with
    | BForm (b1,_) -> let (a,b) = match_equiv_bform hvars b1 pf2 mtl in 
		      if (a) then (a, modify b (CP.mkTrue no_pos)) else ( (a,modify b pf1)) 
    | And(f1,f2,_) ->  (
      let helper fl pf = List.map (fun f-> CP.mkAnd f pf no_pos) fl in
      let count_hd fl = match fl with 
	| [] -> 0
	| x::y -> no_of_cnts x
      in 
      let res11, mix_mtl11 = checkeq_p_formula_with_diff hvars f1 pf2 mtl in
      let mtl11,diff11 =List.split mix_mtl11 in 
      let res12, mix_mtl12 = 
	  if(res11) then checkeq_p_formula_with_diff hvars f2 pf2 mtl11
	  else  (false, List.combine mtl11 (helper diff11 f2))
      in
      let res22, mix_mtl22 = 
	if(res12) then (res11, mix_mtl11)
	else (
	  let res21, mix_mtl21 = checkeq_p_formula_with_diff hvars f2 pf2 mtl in
	  let mtl21,diff21 =List.split mix_mtl21 in 
	  if(res21) then checkeq_p_formula_with_diff hvars f1 pf2 mtl11
	  else (false, List.combine mtl21 (helper diff21 f1))
	)
      in
      if(res12) then (res12, mix_mtl12)
      else if (res22) then (res22, mix_mtl22)
      else (
	let mtl12,diff12 = List.split mix_mtl12 in 
	let mtl22,diff22 = List.split mix_mtl22 in 
	let c1 = count_hd diff12 in
	let c2 = count_hd diff22 in 
	if(c1 < c2) then (false, mix_mtl12)
	else if(c1 > c2) then (false, mix_mtl22)
	else if(c1 = no_of_cnts pf1) then (false,mix_mtl12)
	else (false, List.combine (mtl12@mtl22) (diff12@diff22))
      )
    )
    | AndList _ -> report_error no_pos "not handle checkeq 2 formula that have ANDLIST yet"
    | Or f -> report_error no_pos "not handle checkeq 2 formula that have OR yet" (*todo: match_equiv_orform hvars f pf2 mtl *) 
    | Not(f,_,_) ->  let (a,b) = match_equiv_notform hvars f pf2 mtl in 
		     if (a) then (a, modify b (CP.mkTrue no_pos)) else (a,modify b pf1)
    | Forall _ 
    | Exists _ -> report_error no_pos "not handle checkeq 2 formula that have forall and exists yet"

and checkeq_p_formula_with_diff  hvars pf1 pf2 mtl = 
  let pr1 = Cprinter.string_of_pure_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = pr_list_ln (pr_pair string_of_map_table Cprinter.string_of_pure_formula) in
  let pr4 = string_of_map_table_list in
  Debug.no_3 "checkeq_p_formula_with_diff" pr4 pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ _ ->  checkeq_p_formula_with_diff_x hvars pf1 pf2 mtl) mtl pf1 pf2

(*******************************END: check equivalent with diff***************************************)
(************************************************************************************************)

let subst_with_mt (mt: map_table) (f: CF.formula): CF.formula =   (*Note: support function for other files*)
  let frs,ts = List.split mt in
  CF.subst_avoid_capture frs ts f



(*******************************check equivalent constr******************************************)
(************************************************************************************************)
let check_equiv_constr_x hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula): (bool * map_table list) = 
  let f11,f12 = constr1 in
  let f21, f22 =  constr2 in
  let mtl = [[]] in
  let (res11, mtl11) = (checkeq_formulas_one hvars f11 f21 mtl) in
  let (res21, mtl21) = (checkeq_formulas_one hvars f21 f11 mtl) in
  if(res11&&res21)then(
    let (res12, mtl12) = (checkeq_formulas_one hvars f12 f22 mtl11) in
    let (res22, mtl22) = (checkeq_formulas_one hvars f22 f12 mtl21) in
    (res12&&res22, mtl12)
  ) else (false,[[]])

let check_equiv_constr  hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula): (bool * map_table list) = 
  let pr1 = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 b = if(b) then "VALID\n" else "INVALID\n" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "check_equiv_constr" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  check_equiv_constr_x hvars constr1 constr2) constr1 constr2

let rec checkeq_constrs_x hvars (constrs: (CF.formula * CF.formula) list) ( infile_constrs: (CF.formula * CF.formula) list): bool =
  let res = if(List.length constrs == 0 && (List.length infile_constrs == 0)) then true
  else (
    let rec check_head head constrs =
      match constrs with
	| [] -> (false, [])
	| x::y -> (
	  let r1,tmp = check_equiv_constr hvars head x in
	  if(r1) then (
	    let _ =  Debug.ninfo_pprint ("CONSTR MATCH") no_pos in
	    (r1,y)
	  )
	  else (
	    let r2,ncs = check_head head y in
	    (r2,x::ncs)
	  )
	)
    in
    let res1,new_constrs = check_head (List.hd constrs) infile_constrs in
    if(res1) then (
      let _ = Debug.ninfo_hprint (add_str "Success eq constr: " Cprinter.string_of_hprel_lhs_rhs) (List.hd constrs) no_pos in
      checkeq_constrs_x hvars (List.tl constrs) new_constrs 
    )
    else (
      let _ = Debug.ninfo_hprint (add_str "FAIL constr: " Cprinter.string_of_hprel_lhs_rhs) (List.hd constrs) no_pos in
      res1
    )
  )
  in
  res

let rec checkeq_constrs hvars (constrs: (CF.formula * CF.formula) list) ( infile_constrs: (CF.formula * CF.formula) list): bool =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 b = if(b) then "CP-CONSTRS: VALID\n" else "CP-CONSTRS: INVALID\n" in
  Debug.no_2 "check_constrs" pr1 pr1 (pr2)
      (fun _ _ -> checkeq_constrs_x hvars constrs infile_constrs) constrs infile_constrs

(*******************************check equivalent constrs with diff*******************************)
(************************************************************************************************)
let check_equiv_constr_with_diff_x hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula): (bool * (map_table * (CF.formula * CF.formula)*(CF.formula * CF.formula) ) list) = 
  let f11, f12 = constr1 in
  let f21, f22 =  constr2 in
  let mtl = [[]] in
  let check_back mix_mt f1 f2 res1=
    let (mt,df11,df12) = mix_mt in 	
    let (res2, mix_mtl2) =  (checkeq_formulas_with_diff_mt hvars f1 f2 [mt]) in
    (res2&&res1, List.map (fun (mt1,df21,df22) -> (mt1,(df11,df21),(df12,df22))) mix_mtl2)
  in
  let (res1, mix_mtl1) = (checkeq_formulas_with_diff hvars f11 f21) in
  if(List.length mix_mtl1 == 0) then (
    report_error no_pos "skip: diff type, no mtl"
  )
  else (
    let res_list = List.map (fun mix_mt -> check_back mix_mt f12 f22 res1) mix_mtl1 in 
    let (bs, mtls) = List.split res_list in
    let b = if( List.exists (fun c -> c==true) bs) then true else false in
    let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
    let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
    let fres = b &&res1 in 
    let (r,fs) = if(fres) then 
	let _, mtls =  List.split true_part in
	(fres, List.concat mtls)
      else 
	let _, mtls =  List.split false_part in
	(fres, List.concat mtls)
    in
    (r,fs)
  )

let check_equiv_constr_with_diff  hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula): (bool * (map_table * (CF.formula * CF.formula)*(CF.formula * CF.formula) ) list) = 
  let pr1 = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 b = if(b) then "VALID\n" else "INVALID\n" in
  let pr3 = pr_list_ln (pr_triple string_of_map_table pr1 pr1) in
  Debug.no_2 "check_equiv_constr_with_diff" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ ->  check_equiv_constr_with_diff_x hvars constr1 constr2) constr1 constr2

let rec checkeq_constrs_with_diff_step1_x hvars (constrs: (CF.formula * CF.formula) list) ( infile_constrs: (CF.formula * CF.formula) list): (bool * ((CF.formula * CF.formula) list) * ((CF.formula * CF.formula) list)) =
  let res = if(List.length constrs == 0 && (List.length infile_constrs == 0)) then (true,[],[])
    else if(List.length constrs == 0) then
      (
	(false,[],infile_constrs)
      )
    else (
      let rec check_head head constrs =
	match constrs with
	  | [] -> (false, [])
	  | x::y -> (
	    let r1,tmp = check_equiv_constr hvars head x in
	    if(r1) then (
	      let _ =  Debug.ninfo_pprint ("CONSTR MATCH") no_pos in
	      (r1,y)
	    )
	    else (
	      let r2,ncs = check_head head y in
	      (r2,x::ncs)
	    )
	  )
      in
      let res1,new_constrs = check_head (List.hd constrs) infile_constrs in
      if(res1) then (
	let _ = Debug.ninfo_hprint (add_str "Success eq constr: " Cprinter.string_of_hprel_lhs_rhs) (List.hd constrs) no_pos in
	checkeq_constrs_with_diff_step1_x hvars (List.tl constrs) new_constrs 
      )
      else (
	let _ = Debug.ninfo_hprint (add_str "FAIL constr: " Cprinter.string_of_hprel_lhs_rhs) (List.hd constrs) no_pos in
	let (b,ctrs1, ctrs2) = checkeq_constrs_with_diff_step1_x hvars (List.tl constrs) infile_constrs in
	(b,(List.hd constrs)::ctrs1,ctrs2)
      )
    )
  in
  res
(*STEP1: find all constrs that are not match*)
let rec checkeq_constrs_with_diff_step1 hvars (constrs: (CF.formula * CF.formula) list) ( infile_constrs: (CF.formula * CF.formula) list):  (bool * ((CF.formula * CF.formula) list)* ((CF.formula * CF.formula) list)) =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 b = if(b) then "CP-CONSTRS: VALID\n" else "CP-CONSTRS: INVALID\n" in
  Debug.no_2 "check_constrs_with_diff_step1" pr1 pr1 (pr_triple pr2 pr1 pr1)
      (fun _ _ -> checkeq_constrs_with_diff_step1_x hvars constrs infile_constrs) constrs infile_constrs

let rec checkeq_constrs_with_diff_x hvars (constrs: (CF.formula * CF.formula) list) ( infile_constrs: (CF.formula * CF.formula) list): (bool*(((CF.formula * CF.formula) *  (CF.formula * CF.formula) * ((map_table * (CF.formula * CF.formula)*(CF.formula * CF.formula)) list)) list)) =
  let count_constr mix_mtls = 
    match mix_mtls with
      | [] -> 0 
      | x::y -> let (_,(d11,d12),(d21,d22)) = x in 
		CF.no_of_cnts_fml d11+ CF.no_of_cnts_fml d12 + CF.no_of_cnts_fml d21 + CF.no_of_cnts_fml d22		
  in
  let (res,diff_constrs1,diff_constrs2) = checkeq_constrs_with_diff_step1 hvars constrs infile_constrs in
  let rec check_diff_one_constr constr diff_constrs =
      match diff_constrs with
      | [] -> report_error no_pos " checkeq_constrs_with_diff_x.check_diff_one_constr: should not be empty here"
      | [x] -> (
	let (b,mix_mtls) = check_equiv_constr_with_diff hvars constr x in
	let count_hd =  count_constr mix_mtls in
	(count_hd,x,mix_mtls,[])
      )
      | x::y ->  (
	let (mt,xt,mtls_t,rt) = check_diff_one_constr constr y in
	let (mh,xh,mtls_h,rh) = check_diff_one_constr constr [x] in
	if(mh <= mt) then (mh,xh,mtls_h,y)
	else (mt,xt,mtls_t,x::rt)
      )
  in
  let (res_list,_) = List.fold_left (fun (tmp_res,constrs) c  ->  let (m,x,mtls,r) = check_diff_one_constr c constrs in ((c,x,mtls)::tmp_res,r) ) ([],diff_constrs2)  diff_constrs1 in
  (res,res_list)

let rec checkeq_constrs_with_diff hvars (constrs: (CF.formula * CF.formula) list) ( infile_constrs: (CF.formula * CF.formula) list)=
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 b = if(b) then "CP-CONSTRS: VALID\n" else "CP-CONSTRS: INVALID\n" in
  let pr_constr = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr_mix_mtl =   pr_list_ln (pr_triple string_of_map_table pr_constr pr_constr) in
  let pr3 = pr_list_ln (pr_triple pr_constr pr_constr pr_mix_mtl) in
  Debug.no_2 "check_constrs_with_diff" pr1 pr1 (pr_pair pr2 pr3)
      (fun _ _ -> checkeq_constrs_with_diff_x hvars constrs infile_constrs) constrs infile_constrs

(*******************************check equivalent definition**************************************)
(************************************************************************************************)

let check_equiv_def hvars (def1: (CF.formula * CF.formula)) (def2: (CF.formula * CF.formula)) hp_map: ((CP.spec_var * CP.spec_var) list) =
(*def means 1st element is the only HP*)
  let is_hold p (hp1, hp2) hp_map =
    let a,b = p in
    if(CP.is_hprel_typ a && CP.is_hprel_typ b) then 
      if(CP.eq_spec_var a hp1 && CP.eq_spec_var b hp2) then false 
      else 
	  (*HERE: check if pair is in hp_map already. NOTE: a,b: gen, infile <-> hp_map:  [gen], infile*)
	  try
	    let (cands, _) = List.find (fun (hps,hp) -> CP.eq_spec_var b hp) hp_map in
	    let b = List.exists (fun c -> CP.eq_spec_var a c) cands in
	    if(b) then false else true
	  with 
	    |Not_found -> true
    else false
  in
  let rec helper mt (hp1,hp2) hp_map= 
    match mt with
      | [] -> []
      | x::y -> if(is_hold x (hp1, hp2) hp_map) then x::(helper y (hp1,hp2) hp_map) else (helper y  (hp1,hp2) hp_map)
  in 
  let hp1,_ = def1 in
  let hp2,_ = def2 in
  let (hp1, hp2) =  ((List.hd (CF.get_hp_rel_name_formula hp1)),(List.hd  (CF.get_hp_rel_name_formula hp2))) in
  let m,mtl = check_equiv_constr hvars def1 def2 in (*bool, map_table_list*)
  if(m)then
    (
      let rel_mtl = List.map (fun mt -> helper mt (hp1, hp2) hp_map) mtl in 
      let _ = Debug.ninfo_pprint ("***Relation. MTL: " ^ (string_of_map_table_list rel_mtl)) no_pos in
      let tmp = List.exists (fun mt -> List.length mt == 0) rel_mtl in
      if(tmp) then [(hp1, hp2)] else []
    )
  else []

let match_def_x hvars defs def hp_map =
 let hp,_ = def in
 let _ = if(List.length (CF.get_hp_rel_name_formula hp) == 0) then report_error no_pos "lhs is not only HP" in
 let hp =  List.hd (CF.get_hp_rel_name_formula hp) in
 let add_hp_map (hps,hp) hp_map =
   try
     let (cands, _) = List.find (fun (hps1,hp1) -> CP.eq_spec_var hp hp1) hp_map in
     let new_ele = (CP.remove_dups_svl (cands @ hps), hp) in
     let tmp_hp_map = List.filter (fun (_,hp1) -> not(CP.eq_spec_var hp hp1)) hp_map in
     tmp_hp_map@[new_ele]
   with 
     |Not_found -> hp_map@[(hps,hp)]
 in
 let match_def_helper hvars idef def2 hp_map= 
   let (rc, hf,f) = idef in
   let def1 = (CF.formula_of_heap hf no_pos, f) in
   check_equiv_def hvars def1 def2 hp_map
 in 
 let ls_res = List.concat (List.map (fun idef -> match_def_helper hvars idef def hp_map) defs) in
 if(List.length ls_res > 0) then(
   let hps,_ = List.split ls_res in
   add_hp_map (hps,hp) hp_map
 )
 else add_hp_map ([],hp) hp_map

let match_def hvars defs def hp_map =
  let pr1 = pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr3 = pr_list_ln (pr_pair Cprinter.string_of_spec_var_list Cprinter.string_of_spec_var) in
  Debug.no_2 "match_def" pr2 pr1 (pr3)
    (fun _ _ -> match_def_x hvars defs def hp_map) defs def

let checkeq_defs_x hvars (defs: (CP.rel_cat * CF.h_formula * CF.formula) list) ( infile_defs: (CF.formula * CF.formula) list) =
  let no_change hp_mt1 hp_mt2 = 
    let size_of_mt hp_mt = List.fold_left (fun piv (hps,hp) -> piv + List.length hps) 0 hp_mt in
    (size_of_mt hp_mt1 == size_of_mt hp_mt2)
  in
  let rec helper hvars defs1 defs2 hp_mt=
    let hp_map1 = List.fold_left (fun piv def -> match_def hvars defs1 def piv) hp_mt defs2 in
    if(no_change hp_map1 hp_mt) then  (*terminate condition*)
      hp_map1 
    else 
      helper hvars defs1 defs2 hp_map1
  in
  helper hvars defs infile_defs [] 
  
let checkeq_defs hvars (defs: (CP.rel_cat * CF.h_formula * CF.formula) list) ( infile_defs: (CF.formula * CF.formula) list) =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr3 = pr_list_ln (pr_pair Cprinter.string_of_spec_var_list Cprinter.string_of_spec_var) in
  Debug.no_2 "check_defs" pr2 pr1 (pr3)
    (fun _ _ -> checkeq_defs_x hvars defs infile_defs) defs infile_defs

let checkeq_defs_bool hvars (defs: (CP.rel_cat * CF.h_formula * CF.formula) list) ( infile_defs: (CF.formula * CF.formula) list) inf_vars=
  let mtb = checkeq_defs hvars defs infile_defs in
  let helper v mtb = 
    let exist v mt = 
      let (ls, key) = mt in 
      CP.eq_spec_var v key && List.exists (fun c -> CP.eq_spec_var c v) ls
    in
    List.fold_left (fun piv mt -> if(piv) then true else if(exist v mt) then true else false) false mtb 
  in
  let mixs = List.map (fun c -> (helper c mtb,c)) inf_vars in
  let rs,vars = List.split mixs in
  let _,remain_vars = List.split (List.filter (fun (r,v) -> r == false) mixs) in
  let res = not (List.exists (fun c -> not(c)) rs) in
  (res,remain_vars)

let checkeq_defs_with_diff_x hvars (defs: (CP.rel_cat * CF.h_formula * CF.formula) list) ( infile_defs: (CF.formula * CF.formula) list) inf_vars :  (bool*(((CF.formula * CF.formula) *  (CF.formula * CF.formula) * ((map_table * (CF.formula * CF.formula)*(CF.formula * CF.formula)) list)) list))=
  let mtb = checkeq_defs hvars defs infile_defs in
  let helper v mtb =
    let exist v mt =
      let (ls, key) = mt in
      CP.eq_spec_var v key && List.exists (fun c -> CP.eq_spec_var c v) ls
    in
    List.fold_left (fun piv mt -> if(piv) then true else if(exist v mt) then true else false) false mtb
  in
  let mixs = List.map (fun c -> (helper c mtb,c)) inf_vars in
  let rs,vars = List.split mixs in
  let _,remain_vars = List.split (List.filter (fun (r,v) -> r == false) mixs) in
  let res = not (List.exists (fun c -> not(c)) rs) in
  if(res) then (res,[])
  else (
    let rec check_hps vars = (
      let find_hpdef v defs infile_defs =
	try (
	  let check_hp hp v =
	    let hp_names = CF.get_hp_rel_name_formula hp in
	    let hp_name = match hp_names with
	      | [x] -> x
	      | _ -> report_error no_pos "check_defs: should be the only HP"
	    in
	    CP.eq_spec_var hp_name v
	  in
	  let def1 = List.find (fun (_,hp,_) -> check_hp (CF.formula_of_heap hp no_pos) v) defs in
	  let def2 = List.find (fun (hp,_) -> check_hp hp v) infile_defs in
	  let (a,b,c) = def1 in
	  ((CF.formula_of_heap b no_pos,c),def2)
	)
	with Not_found -> report_error no_pos "Diff HP not found in either defs or infile_defs"
      in
      let hps = List.map (fun v -> find_hpdef v defs infile_defs) vars in
      let res_list = List.map (fun (d1,d2) -> let b,mtl =  check_equiv_constr_with_diff hvars d1 d2 in (d1,d2,mtl)) hps in
      res_list
    )
    in
    (res,check_hps remain_vars) 
  (*TODO: here, b can used to decide if it's actually false or just false with HP diff_name (check again here)*)   
  )
    

let checkeq_defs_with_diff hvars (defs: (CP.rel_cat * CF.h_formula * CF.formula) list) ( infile_defs: (CF.formula * CF.formula) list) inf_vars =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr3 = pr_list_ln (pr_pair Cprinter.string_of_spec_var_list Cprinter.string_of_spec_var) in
  Debug.no_2 "checkeq_defs_with_diff" pr2 pr1 (pr3)
    (fun _ _ -> checkeq_defs_with_diff_x hvars defs infile_defs inf_vars) defs infile_defs
