#include "xdebug.cppo"
open VarGen
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

(*Remove duplicatated pairs in mtl*)
let remove_dupl_mt (mtl: map_table) : map_table =
  let is_dupl (x1,x2) (y1,y2) =
    (eq_spec_var x1 y1) && (eq_spec_var x2 y2)
  in Gen.BList.remove_dups_eq is_dupl mtl

(*Remove trivial pairs, e.g. (x,x)*)
let remove_trivial_mt (mtl: map_table) : map_table =
  List.filter (fun (x,y) -> not(eq_spec_var x y)) mtl

let rec simplify_f f hvars rvars1 = 
  let rvars1_str = List.map (fun v -> CP.full_name_of_spec_var v) rvars1 in
  let evars fs rvars= if(List.length hvars == 0) then fs else
      List.filter (fun f -> not (List.exists (fun hvar -> (String.compare (CP.full_name_of_spec_var f) hvar == 0)) (hvars@rvars))) fs in 

  match f with
  | CF.Or ({ CF.formula_or_f1 = f1;
             CF.formula_or_f2 = f2;
             CF.formula_or_pos = pos}) -> f
  (* let ef1 =  simplify_f f1 hvars rvars1 in *)
  (* let ef2 =  simplify_f f2 hvars rvars1 in *)
  (* CF.mkOr ef1 ef2 pos *)
  | _ ->(  
      let fs1 = evars (CF.fv f) rvars1_str in
      let f = CF.add_quantifiers fs1 f in
      let f = CF.elim_exists_preserve f rvars1_str in
      f
    )

let simplify_2f f1 f2 hvars rvars = 
  let (rvars1, rvars2) = rvars in
  (simplify_f f1 hvars rvars1 , simplify_f f2 hvars rvars2 )


let rec checkeq_formulas_x ivars f1 f2 = 
  match f1,f2 with 
  | CF.Or _, CF.Or _ -> check_or f1 f2 ivars  ([],[]) [[]] 
  | _ ->(
      let mtl = [[]] in
      let (res1, mtl1) = (checkeq_formulas_one ivars ([],[]) f1 f2 mtl) in
      let re_order mt = List.map (fun (a,b) -> (b,a)) mt in
      let imtl = List.map (fun c -> re_order c) mtl1 in
      let (res2, mtl2) =  (checkeq_formulas_one ivars ([],[]) f2 f1 imtl) in
      (res1&&res2, mtl1)
    )

and checkeq_formulas ivars f1 f2 = 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_3 "checkeq_formulas" (pr_list pr_id) pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ _ ->  checkeq_formulas_x ivars f1 f2) ivars f1 f2

and checkeq_formulas_a ivars rvars f1 f2 mtl =
  let (res1, mtl1) = (checkeq_formulas_one ivars rvars f1 f2 mtl) in
  let (res2, mtl2) =  (checkeq_formulas_one ivars rvars f2 f1 mtl) in
  (res1&&res2, mtl1)


and checkeq_formulas_one ivars rvars f1 f2 mtl = 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_3 "checkeq_formulas_one" pr1 pr1 pr3 (pr_pair pr2 pr3)
    (fun _ _ _ ->  checkeq_formulas_one_x ivars rvars f1 f2 mtl) f1 f2 mtl

and checkeq_formulas_one_x (hvars: ident list) rvars  (f1: CF.formula) (f2: CF.formula)(mtl: (map_table list)): (bool*(map_table list))=
  (* print_string (" f1: "^(Cprinter.prtt_string_of_formula f1)^"\n"); *)
  (* print_string (" f2: "^(Cprinter.prtt_string_of_formula f2)^ "\n"); *) 
  let check_no f1 f2 =  match f1,f2 with 
    | CF.Or _, CF.Or _
    | _ -> (CF.no_of_cnts_fml f1 == CF.no_of_cnts_fml f2) 
  in
  let helper hvars f1 f2 mtl = 
    match f1 with
    |CF.Base({CF.formula_base_heap = h1;
              CF.formula_base_pure = p1}) ->(
        match f2 with 
        |CF.Base ({CF.formula_base_heap = h2;
                   CF.formula_base_pure = p2}) -> ( 
            let (res1,mtl1) = checkeq_h_formulas hvars h1 h2 mtl in 
            let (res2,mtl2) =  if(res1) then checkeq_mix_formulas hvars p1 p2 mtl1 else (false,[]) in
            let _= if(res2) then Debug.ninfo_zprint (lazy  ("EQ. FMT: " ^ (string_of_map_table_list mtl2))) no_pos in
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
           let _= if(res2) then Debug.ninfo_zprint (lazy  ("EQ. FMT: " ^ (string_of_map_table_list mtl2))) no_pos in
           if(res2) then
             let new_mtl = check_qvars qvars1 qvars2 mtl2 in
             if(List.length new_mtl > 0) then (true, new_mtl) else (false,mtl2)
           else (res2,mtl2)
         )
       | _ -> 	(false,[]))
    | CF.Or _ ->  (match f2 with 
        |CF.Or _  ->(
            let rec  no_or f = 

              match f with
              | CF.Or ({ CF.formula_or_f1 = f1;
                         CF.formula_or_f2 = f2}) -> no_or f1 + no_or f2 
              | _ -> 1
            in
            (* print_string "\nno_or1: " ;print_int  (no_or f1); *)
            (* print_string "\nno_or2: " ;print_int  (no_or f2); *)
            (* print_string "\n"; *)
            let check_no = (no_or f1 == no_or f2) in
            if(check_no) then check_or f1 f2 hvars rvars mtl else (false,[])
          )
        |_ -> (false,[]))
  in
  let (res,new_mtl) = if(check_no f1 f2) then helper hvars f1 f2 mtl else (false,[[]]) in
  if(not(res) && not(!Globals.dis_sem)) then (
    let (f1,f2) = simplify_2f f1 f2 hvars rvars in (* *)
    (* print_string (" sim f1: "^(Cprinter.prtt_string_of_formula f1)^"\n"); *)
    (* print_string (" sim f2: "^(Cprinter.prtt_string_of_formula f2)^ "\n"); *)
    let (res2,new_mtl2) = if(check_no f1 f2) then helper hvars f1 f2 mtl else (false,[[]])  in
    if(res2) then  (res2,new_mtl2)
    else (res,new_mtl)
  )
  else (res,new_mtl)

and check_or f1 f2 hvars rvars  mtl = 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "check_or" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  check_or_x f1 f2 hvars rvars  mtl) f1 f2	  

and check_or_x f1 f2 hvars rvars mtl =
  let new_mtl mtl f = List.map (fun mt -> (mt, f)) mtl in
  let rec check_one2 f1 f2 hvars mt = 
    (* print_string ("Check f1_2: " ^ (Cprinter.prtt_string_of_formula f1) ^ "\n") ; *)
    (* print_string ("Check f2: " ^ (Cprinter.prtt_string_of_formula f2) ^ "\n") ;  *)
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
    | _ ->  (* print_string ("MT check f: " ^ (string_of_map_table mt)); *)
      let (res,mtl) = checkeq_formulas_a hvars rvars f1 f2 [mt] in
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
          (* let () = if(r) then print_string ("Res: TRUE\n") else  print_string ("Res: FALSE\n") in *)
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
    | CF.ThreadNode n1 ->
      (match hf2 with
       | CF.ThreadNode n2 ->
         let eq_rsr,mt_rsr = checkeq_formulas hvars n1.CF.h_formula_thread_resource n2.CF.h_formula_thread_resource in
         let eq_dl,mt_dl = checkeq_p_formula hvars n1.CF.h_formula_thread_delayed n2.CF.h_formula_thread_delayed mt_rsr in
         if (eq_rsr && eq_dl) then (true,mt_dl)
         else (false,[])
       | _ -> (false,[]))
    | CF.Hole h1 -> (match hf2 with
        |CF.Hole h2 ->  (h1 == h2, mtl)
        |_ -> (false,[]) (* report_error no_pos "not handle Or f1 yet" *)
      )
    | CF.FrmHole h1 -> (match hf2 with
        |CF.FrmHole h2 ->  (h1 == h2, mtl)
        |_ -> (false,[]) (* report_error no_pos "not handle Or f1 yet" *)
      )
    | CF.HRel r  -> 
      (*DONT DELETE: for repuiring exacly the same hprel name!!!
        let rec exists_hp mtl =
        	    match mtl with
        	      | [] -> false
        	      | (a,b)::y ->
        		if(CP.is_hprel_typ a && CP.is_hprel_typ b && (not(CP.eq_spec_var a b))) then 								 true
        		else exists_hp y
        	  in
        	  let res,new_mtl = match_equiv_rel hvars r hf2 mtl in
        (*TODO: check if map tb holds any hps mapping!!!*)
        	  if(res) then (
        	    let new_mtl2 = List.filter (fun m -> not(exists_hp m)) new_mtl in
        	    if(List.length new_mtl2 > 0) then (res,new_mtl2) else (false, new_mtl)
        	  ) else (res,new_mtl)*)
      match_equiv_rel hvars r hf2 mtl
    | CF.HTrue  ->  (true, mtl)
    | CF.HFalse | CF.HVar _ ->  report_error no_pos "not a case hfalse/hvar"
    | CF.HEmp   ->  (true, mtl) (*TODO: plz check*)
    | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> Error.report_no_pattern()
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
  | CF.ThreadNode _ 
  | CF.Hole _ | CF.FrmHole _ 
  | CF.HRel _ 
  | CF.HTrue  
  | CF.HEmp   | CF.HVar _ ->  false
  | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> Error.report_no_pattern()

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
        let () = Debug.ninfo_zprint (lazy  ("node to compare: " ^ (Cprinter.prtt_string_of_h_formula hf2))) no_pos in
        let (res, mt2) = check_node_equiv hvars n n2 mt in 
        (res, [mt2])
      )
    | CF.ThreadNode _ (*TOCHECK*)
    | CF.ViewNode _
    | CF.Hole _ | CF.FrmHole _
    | CF.HRel _ 
    | CF.HTrue -> (false,[mt])
    | CF.HFalse -> report_error no_pos "not a case"
    | CF.HEmp | CF.HVar _  -> (false,[mt])
    | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> Error.report_no_pattern()
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
  let permvars1,permvars2 = Perm.get_perm_var_lists n1.CF.h_formula_data_perm n2.CF.h_formula_data_perm in
  let is_hard_n2 = (List.mem (CP.name_of_spec_var n2.CF.h_formula_data_node) hvars) in
  (* let rec str hvars  = match hvars with *)
  (*   | [] -> "" *)
  (*   | a::y -> a ^ str y  *)
  (* in *)
  let is_hard = is_hard_n1 || is_hard_n2 in
  (* if((not (CF.is_eq_node_name name1 name2)) || (is_hard && (not (CP.eq_spec_var var1 var2))) || (not (CF.is_eq_data_ann ann1 ann2)))  *)
  if((not (CF.is_eq_node_name name1 name2)) || (is_hard && (not (CP.eq_spec_var var1 var2)))) 
  then( 
    let () = Debug.ninfo_zprint (lazy  ("diff node diff name diff ann ")) no_pos in 
    (false, mt) 
    (*TODO: temp eliminate ann*)
  )
  else (
    let () = Debug.ninfo_zprint (lazy  ("match node: " ^ string_of_map_table mt)) no_pos in
    let (res, mt1) = if(is_hard && (CP.eq_spec_var var1 var2)) then (true, mt)  
      else add_map_rel mt (var1) (var2) in
    if(res) then check_spec_var_list_equiv hvars (permvars1@args1) (permvars2@args2) mt1
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
    let () = Debug.ninfo_zprint (lazy  ("null const hard:  " ^ (CP.name_of_spec_var v1))) no_pos in 
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
    | CF.ThreadNode n2 -> (false,[mt]) 
    | CF.DataNode n2 -> (false,[mt]) 
    | CF.ViewNode n2 -> let (res, mt2) = check_view_node_equiv hvars n n2 mt in (res, [mt2])
    | CF.Hole _ | CF.FrmHole _
    | CF.HRel _ 
    | CF.HTrue -> (false,[mt])
    | CF.HFalse -> report_error no_pos "not a case"
    | CF.HEmp | CF.HVar _  -> (false,[mt])
    | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> Error.report_no_pattern()
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
  let permvars1,permvars2 = Perm.get_perm_var_lists n1.CF.h_formula_view_perm n2.CF.h_formula_view_perm in
  let is_hard_n2 = (List.mem (CP.name_of_spec_var n2.CF.h_formula_view_node) hvars) in
  let is_hard = is_hard_n1 || is_hard_n2 in
  if(List.length args1 != List.length args2 ||
     (not (String.compare name1 name2==0)) ||
     (is_hard && (not (CP.eq_spec_var var1 var2))) ||
     (not (CF.is_eq_data_ann ann1 ann2))) 
  then
    (false, mt) 
  else  (
    let (res, mt1) = if(is_hard && (CP.eq_spec_var var1 var2)) then (true, mt)  
      else add_map_rel mt (var1) (var2) in
    if(res) then check_spec_var_list_equiv hvars (permvars1@args1) (permvars2@args2) mt1
    else (false, mt1)
  )

and match_equiv_rel (hvars: ident list) (r: (CP.spec_var * ((CP.exp ) list) * loc)) (hf2: CF.h_formula)(mtl: map_table list): (bool * (map_table list))=
  let rec match_equiv_rel_helper (hvars: ident list) (r: (CP.spec_var * ((CP.exp) list) * loc)) (hf2: CF.h_formula)(mt: map_table): (bool * (map_table list)) = match hf2 with 
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
    | CF.ThreadNode _ 
    | CF.Hole _ -> (false,[mt]) | CF.FrmHole _ -> (false,[mt]) 
    | CF.HRel r2  ->  (
        let () = Debug.ninfo_zprint (lazy  ("Find 2nd relation  " )) no_pos in
        let (res, mt2) = check_rel_equiv hvars r r2 mt in (res, [mt2])
      )
    | CF.HTrue  -> (false,[mt]) 
    | CF.HFalse ->  report_error no_pos "not a case"
    | CF.HEmp  | CF.HVar _  ->  (false,[mt]) 
    | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> Error.report_no_pattern()
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

and check_rel_equiv (hvars: ident list) (r1:  (CP.spec_var * ((CP.exp) list) * loc)) (r2:  (CP.spec_var * ((CP.exp) list) * loc))(mt: map_table): (bool * map_table)=
  let (n1,el1,l1) = r1 in
  let (n2,el2,l2) = r2 in
  let is_hard_r1 = (List.mem (CP.name_of_spec_var n1) hvars) in 
  let is_hard_r2 = (List.mem (CP.name_of_spec_var n2) hvars) in 
  let res = CP.eq_spec_var n1 n2 in (*eq_spec_var means same relation*)
  if(res) then (
    let res, new_mt = add_map_rel mt n1 n2 in 
    if(res) then
      check_exp_list_equiv hvars el1 el2 new_mt
    else (false,mt)
  )
  else (
    if(is_hard_r1 || is_hard_r2) then (false, [])
    else (
      let () = Debug.ninfo_zprint (lazy  ("ADD REL BEFORE: " ^ (string_of_map_table mt))) no_pos in 
      let res, new_mt = add_map_rel mt n1 n2 in
      if(res) then
        check_exp_list_equiv hvars el1 el2 new_mt 
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
  | CF.ThreadNode _
  | CF.Hole _ | CF.FrmHole _
  | CF.HRel _ 
  | CF.HTrue 
  | CF.HFalse | CF.HVar _ -> false
  | CF.HEmp   -> true
  | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> Error.report_no_pattern()

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
  let () = Debug.ninfo_pprint  ("Case 2 formula") no_pos in 
  match pf1 with
  | BForm (b1,_) -> match_equiv_bform hvars b1 pf2 mtl
  | And(f1,f2,_) ->  (
      let res, mtl1 = checkeq_p_formula hvars f1 pf2 mtl in
      if(res) then checkeq_p_formula hvars f2 pf2 mtl1 
      else (res, []) 
    )
  | AndList _ ->
    false,mtl
  (* report_error no_pos "not handle checkeq 2 formula that have ANDLIST yet" *)
  | Or f -> match_equiv_orform hvars f pf2 mtl
  | Not(f,_,_) -> match_equiv_notform hvars f pf2 mtl
  | Forall _ 
  | Exists _ -> false,mtl (* report_error no_pos "not handle checkeq 2 formula that have forall and exists yet" *)

and checkeq_p_formula  hvars pf1 pf2 mtl = 
  let pr1 = Cprinter.string_of_pure_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  Debug.no_3 "checkeq_p_formula" pr1 pr1 pr3 (pr_pair pr2 pr3)
    (fun _ _ _ ->  checkeq_p_formula_x hvars pf1 pf2 mtl) pf1 pf2 mtl

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

and check_equiv_exp  hvars e1 e2 mtl = 
  let pr1 = Cprinter.string_of_formula_exp in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table in
  let pr4 = string_of_map_table in
  Debug.no_3 "check_equiv_bform" pr1 pr1 pr4 (pr_pair pr2 pr3)
    (fun _ _ _ ->  check_equiv_exp_x hvars e1 e2 mtl) e1 e2 mtl

and check_equiv_exp_x hvars (e1:CP.exp) (e2:CP.exp) mt = 
  match e1,e2 with
  | CP.Null _ , CP.Null _ -> (true, mt)
  | Var (v1,_) , Var (v2,_) -> check_spec_var_equiv hvars v1 v2 mt
  | Level (v1,_) , Level (v2,_) -> check_spec_var_equiv hvars v1 v2 mt
  | IConst (i1,_), IConst (i2,_) -> (i1=i2,mt)
  | FConst (i1,_), FConst (i2,_) -> (i1=i2,mt)
  | Bptriple ((v11,v12,v13),_), Bptriple ((v21,v22,v23),_) ->
    let res1,mt1 = check_spec_var_equiv hvars v11 v21 mt in
    let res2,mt2 = check_spec_var_equiv hvars v12 v22 mt1 in
    let res3,mt3 = check_spec_var_equiv hvars v13 v23 mt2 in
    (res1 && res2 && res3,mt3)
  | Add (e11,e12,_),Add (e21,e22,_) ->
    let res1,mt1 = check_equiv_exp hvars e11 e21 mt in
    let res2,mt2 = check_equiv_exp hvars e12 e22 mt1 in
    (res1 && res2, mt2)
  (*TODO: implement for your need*)
  | _ -> (false, mt)

and check_equiv_bform  hvars b1 b2 mtl = 
  let pr1 = Cprinter.string_of_b_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = string_of_map_table_list in
  let pr4 = string_of_map_table in
  Debug.no_3 "check_equiv_bform" pr1 pr1 pr4 (pr_pair pr2 pr3)
    (fun _ _ _ ->  check_equiv_bform_x hvars b1 b2 mtl) b1 b2 mtl

and check_equiv_bform_x (hvars: ident list)(b1: CP.b_formula) (b2: CP.b_formula)(mt: map_table): (bool * (map_table list)) =
  let rec check_eq_order_spec_var_list svl1 svl2 mt0=
    match svl1,svl2 with
    | [],[] -> (true,mt0)
    | sv1::tl1,sv2::tl2 ->
      let res, r_mt = check_spec_var_equiv hvars sv1 sv2 mt0 in
      if res then
        check_eq_order_spec_var_list tl1 tl2 r_mt
      else (false,mt0)
    | _ -> (false,mt0)
  in
  match b1,b2 with
  | (BConst (true,_),_),  (BConst (true,_),_) -> (true,[mt])
  | (BConst (false,_),_),  (BConst (false,_),_) -> (true,[mt])
  | (BagNotIn (v1,e1,_),_),  (BagNotIn (v2,e2,_),_)
  | (BagIn (v1,e1,_),_),  (BagIn (v2,e2,_),_) -> (*MUSTDO*)
    let res1,mt1 = check_spec_var_equiv hvars v1 v2 mt in
    let res2,mt2 = check_equiv_exp hvars e1 e2 mt1 in
    (res1 && res2,[mt2])
  | (XPure xp1,_),  (XPure xp2,_) ->

    if xp1.xpure_view_name = xp1.xpure_view_name then
      match xp1.xpure_view_node,xp1.xpure_view_node with
      | None,None -> let r,r_mt = check_eq_order_spec_var_list xp1.xpure_view_arguments xp2.xpure_view_arguments mt in
        (r,[r_mt])
      | Some r1,Some r2 -> let r,r_mt = check_eq_order_spec_var_list (r1::xp1.xpure_view_arguments) (r2::xp2.xpure_view_arguments) mt in
        (r,[r_mt])
      | _ -> (false,[mt])
    else (false,[mt])
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
    let res1,mt1 = check_equiv_exp hvars e11 e21 mt in
    let res2,mt2 = check_equiv_exp hvars e12 e22 mt1 in
    (res1&&res2, [mt2])
  (* (match e11,e12,e21,e22 with *)
  (*   | Var (v11,_),Var (v12,_),Var (v21,_),Var (v22,_)->  *)
  (*     let res11, mt11 = check_spec_var_equiv hvars v11 v21 mt in  *)
  (*     let res12, mt12 = check_spec_var_equiv hvars v12 v22 mt11 in *)
  (*     let res1,mt1 = if(res11&&res12) then (res11,mt12) else (false,mt) in  *)
  (*     if(res1) then (true, [mt1])   (\*merge tables*\) *)
  (*     else (false, [mt]) *)
  (*   | Var (v11,_),IConst (v12,_),Var (v21,_),IConst (v22,_)->  *)
  (*     let res1, mt1 = check_spec_var_equiv hvars v11 v21 mt in  *)
  (*     let res2 = (v12= v22) in *)
  (*     if(res1 && res2) then (true, [mt1])   (\*merge tables*\) *)
  (*     else (false, [mt]) *)
  (*   | IConst (v11,_),Var (v12,_),IConst (v21,_),Var (v22,_)->  *)
  (*     let res1, mt1 = check_spec_var_equiv hvars v12 v22 mt in  *)
  (*     let res2 = (v11= v21) in *)
  (*     if(res1 && res2) then (true, [mt1])   (\*merge tables*\) *)
  (*     else (false, [mt]) *)
  (*   | Var (v11,_),FConst (v12,_),Var (v21,_),FConst (v22,_)->  *)
  (*     let res1, mt1 = check_spec_var_equiv hvars v11 v21 mt in  *)
  (*     let res2 = (v12= v22) in *)
  (*     if(res1 && res2) then (true, [mt1])   (\*merge tables*\) *)
  (*     else (false, [mt]) *)
  (*   | FConst (v11,_),Var (v12,_),FConst (v21,_),Var (v22,_)->  *)
  (*     let res1, mt1 = check_spec_var_equiv hvars v12 v22 mt in  *)
  (*     let res2 = (v11= v21) in *)
  (*     if(res1 && res2) then (true, [mt1])   (\*merge tables*\) *)
  (*     else (false, [mt]) *)
  (*   | _ -> (false, [mt]) *)
  (* ) *)
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
    | Not(f2,_,_) -> 	let res, mtl = match_equiv_notform_helper hvars f1 f2 mt in
      if res then (true, mtl) else (false, [mt])
    (* report_error no_pos "temp: not handle not yet" (\* checkeq_p_formula hvars f1 f2 mtl *\) *)
    | Forall _ 
    | Exists _ -> (false,[mt])
    (* report_error no_pos "not handle forall and exists yet" *)
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
and checkeq_formulas_with_diff_mt_x ivars rvars f1 f2 mtl = 
  let (a,b) = rvars in
  let rvars2 = (b,a) in
  let (r,fs) = match f1,f2 with 
    |CF.Or _ ,
     CF.Or _  -> (
        check_or_with_diff_x f1 f2 ivars mtl
      )
    | _ -> (
        let re_order mt = List.map (fun (a,b) -> (b,a)) mt in
        let (res1, mix_mtl1) = (checkeq_formulas_one_with_diff ivars rvars f1 f2 mtl) in
        let check_back mix_mt f2 f1 res1= (
          let mt,f = mix_mt in 		
          let (res2, mix_mtl2) =  (checkeq_formulas_one_with_diff ivars rvars2 f2 f1 [re_order mt]) in
          (res2&&res1,List.map (fun (mt1,f1) -> (mt,f,f1)) mix_mtl2)
        )
        in 
        if(List.length mix_mtl1  == 0) then (
          let todo_unk = checkeq_formulas_one_with_diff ivars rvars2 f2 f1 [[]] in
          (false, [])
        )
        else (
          let res_list = List.map (fun mix_mt -> check_back mix_mt f2 f1 res1) mix_mtl1 in 
          let (bs, mtls) = List.split res_list in
          let b = if( List.exists (fun c -> c==true) bs) then true else false in
          let true_part = List.filter (fun (res,mtl) -> res==true) res_list in 
          let false_part = List.filter (fun (res,mtl) -> res==false) res_list in
          let fres = b &&res1 in 
          if(fres) then 
            let _, mtls =  List.split true_part in
            (fres, List.concat mtls)
          else 
            let _, mtls =  List.split false_part in
            (fres, List.concat mtls)
        )
      )
  in

  (r,fs)

and checkeq_formulas_with_diff_mt ivars rvars f1 f2 mtl= 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = pr_list_ln (pr_triple string_of_map_table pr1 pr1) in
  Debug.no_2 "checkeq_formulas_with_diff_mt" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  checkeq_formulas_with_diff_mt_x ivars rvars f1 f2 mtl) f1 f2

and checkeq_formulas_with_diff_x ivars f1 f2 = 
  let showdiff r fs = (
    if(r) then (
      let mtl =  List.map (fun (a,_,_) -> a) fs in 
      Debug.info_zprint (lazy  ("Final MTL: " ^ (string_of_map_table_list mtl))) no_pos
    )
    else (
      let print_triple mt f1 f2 =  
        let str = ("\nDIFF F1: " ^ Cprinter.prtt_string_of_formula f1 ^ "\n" 
                   ^ "DIFF F2: " ^ Cprinter.prtt_string_of_formula f2 ^ "\n"
                   ^ "CURRENT MT: " ^ string_of_map_table mt)
        in
        Debug.ninfo_pprint  (str) no_pos 
      in 
      if(List.length fs > 0) then (
        let todo_unk = List.map (fun (a,b,c) -> print_triple a b c) fs in
        ()
      )
      else 	Debug.ninfo_pprint ("no diff info") no_pos 
    )
  )
  in
  let mtl = [[]] in
  let (r,fs) = checkeq_formulas_with_diff_mt ivars ([],[]) f1 f2 mtl in
  let () = 
    if(not !Globals.dis_show_diff) then showdiff r fs
  in
  (r,fs)

(* ivars: set of roots (otherwise, all permutations)
   return (mt*formula1*formula2) list
     where for each element
       mt: mapping table
       formula1: remaining formula of f1
       formula2: renaming formula of f2*)
and checkeq_formulas_with_diff ivars f1 f2 = 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = pr_list_ln (pr_triple string_of_map_table pr1 pr1) in
  Debug.no_2 "checkeq_formulas_with_diff" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  checkeq_formulas_with_diff_x ivars f1 f2) f1 f2

and checkeq_formulas_one_with_diff ivars rvars f1 f2 mtl= 
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 b = if(b) then "VALID" else "INVALID" in
  let pr3 = pr_list_ln (pr_pair string_of_map_table pr1) in
  Debug.no_2 "checkeq_formulas_one_with_diff" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  checkeq_formulas_one_with_diff_x ivars rvars f1 f2 mtl) f1 f2

and checkeq_formulas_one_with_diff_x (hvars: ident list) rvars (f1: CF.formula) (f2: CF.formula)(mtl: (map_table list)): (bool*((map_table * CF.formula) list))=
  let helper hvars f1 f2 mtl = 
    match f1 with
    |CF.Base({CF.formula_base_heap = h1;
              CF.formula_base_pure = p1}) ->(
        match f2 with 
        |CF.Base ({CF.formula_base_heap = h2;
                   CF.formula_base_pure = p2}) -> (
            let (res1,mix_mtl1) = checkeq_h_formulas_with_diff hvars h1 h2 mtl in
            let (res2,mix_mtl2) =  checkeq_mix_formulas_with_diff hvars p1 p2 mix_mtl1 in
            (res1&&res2,mix_mtl2)
          )
        |_ ->  let () = if(not !Globals.dis_show_diff) then Debug.ninfo_pprint  ("DIFF: Base formula") no_pos in
          (false,[([],f1)])
      )
    |CF.Exists({CF.formula_exists_qvars = qvars1;
                CF.formula_exists_heap = h1;
                CF.formula_exists_pure = p1})->
      (match f2 with 
       |CF.Exists ({CF.formula_exists_qvars = qvars2;
                    CF.formula_exists_heap = h2;
                    CF.formula_exists_pure = p2}) -> (
           let (res1,mix_mtl1) = checkeq_h_formulas_with_diff hvars h1 h2 mtl in
           let (res2,mix_mtl2) =  checkeq_mix_formulas_with_diff hvars p1 p2 mix_mtl1 in
           let res= res1&&res2 in
           if(res) then
             let new_mix_mtl = check_qvars_mix_mtl qvars1 qvars2 mix_mtl2 in
             if(List.length new_mix_mtl > 0) then (true, new_mix_mtl) else (false,mix_mtl2)
           else  (res,mix_mtl2)
         )
       | _ -> let () = if(not !Globals.dis_show_diff) then Debug.ninfo_pprint  ("DIFF: Exists formula") no_pos in 
         (false,[([],f1)]))
    |CF.Or ({CF.formula_or_f1 = f11;
             CF.formula_or_f2 = f12})  ->  (match f2 with
        |CF.Or ({CF.formula_or_f1 = f21;
                 CF.formula_or_f2 = f22})  -> (
            let () =  if(not !Globals.dis_show_diff) then Debug.ninfo_pprint  ("DIFF: Or formula") no_pos in  
            (false,[([],f1)])
          )
        |_ ->   let () =  if(not !Globals.dis_show_diff) then Debug.ninfo_pprint  ("DIFF: Or formula") no_pos in  (false,[([],f1)]))
  in
  (* print_string ("f1: "^(Cprinter.prtt_string_of_formula f1)^"\n"); *)
  (*     print_string ("f2: "^(Cprinter.prtt_string_of_formula f2)^ "\n"); *)
  let (res,new_mtl) = helper hvars f1 f2 mtl in
  if(not(res) && not(!Globals.dis_sem)) then (
    let (f1,f2) = simplify_2f f1 f2 hvars rvars in
    (*  print_string ("sim f1: "^(Cprinter.prtt_string_of_formula f1)^"\n"); *)
    (* print_string ("sim f2: "^(Cprinter.prtt_string_of_formula f2)^ "\n"); *)
    let (res2,new_mtl2) = helper hvars f1 f2 mtl in
    if(res2) then  (res2,new_mtl2)
    else (res,new_mtl2)
  )
  else (res,new_mtl)

(* and check_or_with_diff f1 f2 hvars mtl = *)
(*   let pr1 = Cprinter.prtt_string_of_formula in *)
(*   let pr2 b = if(b) then "VALID" else "INVALID" in *)
(*   let pr3 = string_of_map_table_list in *)
(*   Debug.no_2 "check_or_with_diff" pr1 pr1 (pr_pair pr2 pr3) *)
(*       (fun _ _ ->  check_or_with_diff_x f1 f2 hvars mtl) f1 f2 *)

and check_or_with_diff_x f1 f2 hvars mtl =
  let new_mtl mtl1 d1 d2 f = List.map (fun mt -> (mt,d1,d2, f)) mtl1 in
  let new_mix_mtl mix_mtl f = List.map (fun (mt,d1,d2) -> (mt, d1,d2,f)) mix_mtl in
  let rec check_one2 f1 f2 hvars mt = 
    (* print_string ("Check f1_2: " ^ (Cprinter.prtt_string_of_formula f1) ^ "\n") ;  *)
    (* print_string ("Check f2_2: " ^ (Cprinter.prtt_string_of_formula f2) ^ "\n") ;  *)
    match f2 with 
    | CF.Or ({CF.formula_or_f1 = f21;
              CF.formula_or_f2 = f22})  -> (
        let (res1, mix_mtl1) = check_one2 f1 f21 hvars mt in
        let (res2, mix_mtl2) = check_one2 f1 f22 hvars mt in
        let new_mix_mtl2 mix_mtl f2 = List.map (fun (mt,d1,d2,f) ->  (* print_string ("mix with: " ^ (Cprinter.prtt_string_of_formula f2) ^ "\n") ; *)if (CF.isStrictConstTrue f) then (mt,d1,d2,f2) else if (CF.isStrictConstTrue f2) then (mt,d1,d2,f) else (mt,d1,d2, CF.mkOr f f2 no_pos)) mix_mtl in 
        if(res1 && res2) then 
          (
            let nmix_mtl1 = new_mix_mtl2 mix_mtl1 f22 in 
            let nmix_mtl2 = new_mix_mtl2 mix_mtl2 f21 in 
            (true, nmix_mtl1@nmix_mtl2)
          )
        else if(res1) then let nmix_mtl1 = new_mix_mtl2 mix_mtl1 f22 in (true,nmix_mtl1)
        else if(res2) then let nmix_mtl2 = new_mix_mtl2 mix_mtl2 f21 in (true,nmix_mtl2)
        else (
          let count mix_mtls = match mix_mtls with
            | [] -> 0
            | (mt,d1,d2,x)::y -> CF.no_of_cnts_fml d1 + CF.no_of_cnts_fml d2 (*no count of relation*)
          in
          let choose_helper m1 m2 f1 f2 = let c1 = count m1 in
            let c2 = count m2 in
            if(c2 > c1) then new_mix_mtl2 m1 f2 else
            if(c1 > c2) then new_mix_mtl2 m2 f1 else ( 
              (new_mix_mtl2 m1 f2)@(new_mix_mtl2 m2 f1))
          in
          let nmix_mtl = choose_helper mix_mtl1 mix_mtl2 f21 f22 in
          (false, nmix_mtl)
        )
      )
    | _ ->  let (res,mix_mtl) =  checkeq_formulas_with_diff_mt hvars ([],[]) f1 f2 [mt] in
      let mix_mtl = if(res && List.length mix_mtl > 0) then [(List.hd mix_mtl)] else mix_mtl in
      (res, new_mix_mtl mix_mtl (CF.mkTrue_nf no_pos))
  in
  let rec check_one1 f1 hvars mix_mtl=
    (* print_string ("Check f1: " ^ (Cprinter.prtt_string_of_formula f1) ^ "\n") ;  *)
    match f1 with
    | CF.Or ({CF.formula_or_f1 = f11;
              CF.formula_or_f2 = f12})  -> (
        let (res1,mix_mtl1) = check_one1 f11 hvars mix_mtl in
        let tmp_mtl = List.concat (List.map (fun (mt,l) -> List.map (fun (mt1,d1,d2,f) -> (mt,d1,d2,f)) l ) mix_mtl1 ) in
        let (res2,mix_mtl2) = check_one1 f12 hvars tmp_mtl in
        (res1&&res2,mix_mtl2)
      )
    | _ -> (
        let helper mt d1 d2 f2 =  
          (* print_string ("Inside one pass: Check f1: " ^ (Cprinter.prtt_string_of_formula f1) ^ "\n") ;   *)
          (* print_string ("Inside one pass: Check f2: " ^ (Cprinter.prtt_string_of_formula f2) ^ "\n") ;  *) 
          let (r,l) = check_one2 f1 f2 hvars mt in 
          (* let () = if(r) then print_string ("Res: TRUE\n") else  print_string ("Res: FALSE\n") in   *)
          let new_diff d1 d2 = if (CF.isStrictConstTrue d1) then d2 else if (CF.isStrictConstTrue d2) then d1 else CF.mkOr d1 d2 no_pos in 
          let new_mtl = List.map (fun (mt, d21, d22,f) -> (mt,new_diff d1 d21,new_diff d2 d22,f)) l in
          (r,(mt,new_mtl))	
        in
        let res_list = List.map (fun (mt,d1,d2,f2) -> helper mt d1 d2 f2) mix_mtl in
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
  let emp_f = CF.mkTrue_nf no_pos in
  let (res,tmp) = check_one1 f1 hvars (new_mtl mtl emp_f emp_f f2) in
  let tmp2 =   List.map (fun (a,b) -> List.map (fun (mt,d1,d2,f) -> (mt,d1,d2)) b)  tmp in
  (res,List.concat tmp2 )

and checkeq_h_formulas_with_diff_x (hvars: ident list)(hf1: CF.h_formula) (hf2: CF.h_formula)(mtl: map_table list): (bool * ((map_table * CF.h_formula) list))=
  let () = Debug.ninfo_pprint  ("Compare heap formulas ") no_pos in
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
            let helper fl hf =  let () = Debug.ninfo_zprint (lazy  ("ADD h_formula: " ^ (Cprinter.prtt_string_of_h_formula hf))) no_pos in
              List.map (fun f -> CF.mkStarH f hf no_pos) fl in 
            let count_hd fl = match fl with
              | [] -> 0
              | x::y -> CF.no_of_cnts_heap x
            in
            let (ph1, mix_mtl_1) = checkeq_h_formulas_with_diff hvars h1 hf2 mtl in

            let mtl_1 = List.map (fun (a,b) -> a) mix_mtl_1 in (*temporary*)
            let diff_1 = List.map (fun (a,b) -> b) mix_mtl_1 in (*temporary*) 
            let b1,mix_mtl1 = if(ph1) then (
                let () = Debug.ninfo_zprint (lazy  ("INPUT MTL for RHS" ^ (string_of_map_table_list mtl_1))) no_pos in
                let (ph2, mix_mtl_2) = checkeq_h_formulas_with_diff hvars h2 hf2 mtl_1 in
                let pr3 =  pr_list_ln (pr_pair string_of_map_table Cprinter.prtt_string_of_h_formula) in
                let () = Debug.ninfo_zprint (lazy  ("RHS:::::" ^ (pr3 mix_mtl_2))) no_pos in
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
    | CF.FrmHole h1 -> (match hf2 with
        |CF.FrmHole h2 -> let (a,b) = (h1 == h2, mtl)  in if(a) then (a,modify_mtl b CF.HEmp) else (a,modify_mtl b hf1)
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
    | CF.HTrue  -> (match hf2 with
        | CF.HTrue -> (true, modify_mtl mtl CF.HEmp)
        | _ ->   (false, modify_mtl mtl CF.HTrue))
    | CF.HFalse | CF.HVar _ ->  report_error no_pos "not a case hfalse/hvar "
    | CF.HEmp   ->  (true, modify_mtl mtl CF.HEmp) (*TODO: plz check*)
    | CF.ThreadNode _ (*TOCHECK*)
    | CF.ConjConj _ | CF.StarMinus _ | CF.ConjStar _ -> Error.report_no_pattern()
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
  Debug.no_3 "checkeq_mix_formulas_with_diff" pr5 pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ _ ->  checkeq_mix_formulas_with_diff_x hvars mp1 mp2 mix_mtl) mix_mtl mp1 mp2

and checkeq_mix_formulas_with_diff_x (hvars: ident list)(mp1: MCP.mix_formula) (mp2: MCP.mix_formula)(mix_mtl: (map_table * CF.h_formula) list): (bool * ((map_table * CF.formula) list))=
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
    | MCP.MemoF _,MCP.MemoF _  -> 
      if (not !allow_threads_as_resource) then
        report_error no_pos "Have not support comparing 2 MemoF yet"
      else
        (* temporarily convert to pure formula*)
        let () = print_endline_quiet ("Have not support comparing 2 MemoF yet") in
        let p1 = MCP.fold_mem_lst (mkTrue no_pos) false true mp1 in
        let p2 = MCP.fold_mem_lst (mkTrue no_pos) false true mp2 in
        checkeq_p_formula_with_diff hvars p1 p2 mtl
    | MCP.OnePF f1, MCP.OnePF f2 ->  checkeq_p_formula_with_diff hvars f1 f2 mtl
    | _,_ ->  (false, List.map (fun mt -> (mt,CP.mkTrue no_pos)) mtl)
  ) in
  let helper mp1 mp2 mt hf =
    let () = Debug.ninfo_zprint (lazy  ("Need to add hf: " ^ (Cprinter.string_of_h_formula hf))) no_pos in 
    let (b,nmtl) = checkeq_mix_formulas_one mp1 mp2 [mt] in
    let mkF hf pf = CF.mkBase hf (* (MCP.OnePF (pf)) *) (MCP.mix_of_pure pf) CvpermUtils.empty_vperm_sets CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in 
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
  let () = Debug.ninfo_pprint  ("Case 2 formula") no_pos in 
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
  | AndList _ -> report_error no_pos "not handle checkeq 2 pure formula that have ANDLIST yet"
  | Or f -> report_error no_pos "not handle checkeq 2 pure formula that have OR yet" (*todo: match_equiv_orform hvars f pf2 mtl *) 
  | Not(f,_,_) ->  let (a,b) = match_equiv_notform hvars f pf2 mtl in 
    if (a) then (a, modify b (CP.mkTrue no_pos)) else (a,modify b pf1)
  | Forall _ 
  | Exists _ -> (false,[]) (* report_error no_pos "not handle checkeq 2 formula that have forall and exists yet" *)

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
let check_equiv_2f_x hvars (def1: CF.formula * CF.formula) (def2: CF.formula * CF.formula) def: (bool * map_table list)= 
  let f11,f12 = def1 in
  let f21, f22 = def2 in
  (*should be removed when 0<0 is eliminated*)
  let f11 = x_add_1 CF.simplify_pure_f_old f11 in
  let f12 = x_add_1 CF.simplify_pure_f_old f12 in
  let f21 = x_add_1 CF.simplify_pure_f_old f21 in
  let f22 = x_add_1 CF.simplify_pure_f_old f22 in
  (**END**)
  let mtl = [[]] in
  let rvars1,rvars2 = if(def) then CF.get_hp_rel_vars_formula f11, CF.get_hp_rel_vars_formula f21 else [],[] in

  let (res11, mtl11) = (checkeq_formulas_one hvars ([],[]) f11 f21 mtl) in
  let (res21, mtl21) = (checkeq_formulas_one hvars ([],[]) f21 f11 mtl) in
  if(res11&&res21)then(
    let (res12, mtl12) = (checkeq_formulas_one hvars (rvars1,rvars2) f12 f22 mtl11) in
    let (res22, mtl22) = (checkeq_formulas_one hvars (rvars2,rvars1) f22 f12 mtl21) in
    (res12&&res22, mtl12)
  ) else (false,[[]])

let check_equiv_2f  hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula) def: (bool * map_table list)  = 
  let pr1 = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 b = if(b) then "VALID\n" else "INVALID\n" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "check_equiv_2f" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  check_equiv_2f_x hvars constr1 constr2 def) constr1 constr2

let check_equiv_constr_x hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula): (bool * map_table list) = 
  check_equiv_2f  hvars constr1 constr2 false

let check_equiv_constr  hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula): (bool * map_table list) = 
  let pr1 = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 b = if(b) then "VALID\n" else "INVALID\n" in
  let pr3 = string_of_map_table_list in
  Debug.no_2 "check_equiv_constr" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  check_equiv_constr_x hvars constr1 constr2) constr1 constr2

let rec checkeq_constrs_x hvars (constrs: (CF.formula * CF.formula) list) ( infile_constrs: (CF.formula * CF.formula) list): bool =
  let res = if(List.length constrs == 0 && (List.length infile_constrs == 0)) then true
    else (
      if (List.length constrs != List.length infile_constrs) 
      then false
      else (
        let rec check_head head constrs =
          match constrs with
          | [] -> (false, [])
          | x::y -> (
              let r1,tmp = check_equiv_constr hvars head x in
              if(r1) then (
                let () =  Debug.ninfo_pprint  ("CONSTR MATCH") no_pos in
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
          let () = Debug.ninfo_hprint (add_str "Success eq constr: " Cprinter.string_of_hprel_lhs_rhs) (List.hd constrs) no_pos in
          checkeq_constrs_x hvars (List.tl constrs) new_constrs 
        )
        else (
          let () = Debug.ninfo_hprint (add_str "FAIL constr: " Cprinter.string_of_hprel_lhs_rhs) (List.hd constrs) no_pos in
          res1
        )
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


let check_equiv_2f_with_diff_x hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula) spairs def: (bool * (map_table * (CF.formula * CF.formula)*(CF.formula * CF.formula) ) list) = 
  let f11, f12 = constr1 in
  let f21, f22 =  constr2 in
  let rvars = if(def) then (
      let rvars1 = CF.get_hp_rel_vars_formula f11 in
      let rvars2 = CF.get_hp_rel_vars_formula f21 in
      (rvars1, rvars2)
    )
    else ([],[])
  in

  let check_back mix_mt f1 f2 res1=
    let (mt,df11,df12) = mix_mt in
    let (res2, mix_mtl2) =  (checkeq_formulas_with_diff_mt hvars rvars f1 f2 [mt@spairs]) in
    (res2&&res1, List.map (fun (mt1,df21,df22) -> (mt1,(df11,df21),(df12,df22))) mix_mtl2)
  in
  let (res1, mix_mtl1) = (checkeq_formulas_with_diff_mt hvars rvars f11 f21 [spairs]) in
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

let check_equiv_2f_with_diff  hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula) spairs def: (bool * (map_table * (CF.formula * CF.formula)*(CF.formula * CF.formula) ) list) = 
  let pr1 = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 b = if(b) then "VALID\n" else "INVALID\n" in
  let pr3 = pr_list_ln (pr_triple string_of_map_table pr1 pr1) in
  Debug.no_2 "check_equiv_2fc_with_diff" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  check_equiv_2f_with_diff_x hvars constr1 constr2 spairs def) constr1 constr2

let check_equiv_constr_with_diff_x hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula) spairs: (bool * (map_table * (CF.formula * CF.formula)*(CF.formula * CF.formula) ) list) = 
  check_equiv_2f_with_diff  hvars constr1 constr2 spairs false

let check_equiv_constr_with_diff  hvars (constr1: CF.formula * CF.formula) (constr2: CF.formula * CF.formula) spairs: (bool * (map_table * (CF.formula * CF.formula)*(CF.formula * CF.formula) ) list) = 
  let pr1 = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 b = if(b) then "VALID\n" else "INVALID\n" in
  let pr3 = pr_list_ln (pr_triple string_of_map_table pr1 pr1) in
  Debug.no_2 "check_equiv_constr_with_diff" pr1 pr1 (pr_pair pr2 pr3)
    (fun _ _ ->  check_equiv_constr_with_diff_x hvars constr1 constr2 spairs) constr1 constr2

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
              let () =  Debug.ninfo_pprint ("CONSTR MATCH") no_pos in
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
        let () = Debug.ninfo_hprint (add_str "Success eq constr: " Cprinter.string_of_hprel_lhs_rhs) (List.hd constrs) no_pos in
        checkeq_constrs_with_diff_step1_x hvars (List.tl constrs) new_constrs 
      )
      else (
        let () = Debug.ninfo_hprint (add_str "FAIL constr: " Cprinter.string_of_hprel_lhs_rhs) (List.hd constrs) no_pos in
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
  let infile_constrs1 = List.map (fun (hf,t) -> (CF.elim_exists hf, t)) infile_constrs in
  let (res,diff_constrs1,diff_constrs2) = checkeq_constrs_with_diff_step1 hvars constrs infile_constrs1 in
  let rec check_diff_one_constr constr diff_constrs =
    match diff_constrs with
    | [] -> let e = (CF.formula_of_heap CF.HEmp no_pos,CF.formula_of_heap CF.HEmp no_pos) in
      let (b,mix_mtls) = check_equiv_constr_with_diff hvars constr e [] in
      let count_hd =  count_constr mix_mtls in
      (count_hd,e,mix_mtls,[])
    | [x] -> (
        let (b,mix_mtls) = check_equiv_constr_with_diff hvars constr x [] in
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
  if(List.length diff_constrs1 != 0) then
    let (res_list,_) = List.fold_left (fun (tmp_res,constrs) c  ->
        let (m,x,mtls,r) = check_diff_one_constr c constrs in
        ((c,x,mtls)::tmp_res,r) ) ([],diff_constrs2
                                  )  diff_constrs1 in
    (res,res_list)
  else
    let e = (CF.formula_of_heap CF.HEmp no_pos,CF.formula_of_heap CF.HEmp no_pos) in
    let (res_list,_) = List.fold_left (fun (tmp_res,constrs) c  ->
        let (m,x,mtls,r) = check_diff_one_constr e constrs in
        ((e,x,mtls)::tmp_res,r)
      ) ([],diff_constrs2)  diff_constrs2 in
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
let process_spairs_x smts spairs =
  let rec check_mt1 mt spairs =
    match mt with 
    | [] -> true
    | x::y -> let (sv1,sv2) = x in
      let res_t = try (
        (* let (c,s) = List.find (fun (cand,sv) -> (String.compare sv (CP.name_of_spec_var sv1) == 0)) spairs in *)
        let rec check_spairs spairs (sv1,sv2) = 
          match spairs with
          | [] -> true
          | x1::y1 -> let rt = check_spairs y1 (sv1,sv2) in
            if(rt) then (
              let (c,s) = x1 in
              match s with 
              | None -> report_error no_pos "process_spairs: should not happen (chose mt that have that option)"
              | Some so -> (
                  if(CP.eq_spec_var so sv1) then (
                    if(String.compare c (CP.name_of_spec_var sv2) == 0) then rt else false
                  )	
                  else rt	 
                ) 
            )
            else false
        in
        check_spairs spairs (sv1,sv2)
      )
        with _ -> false
      in
      if(res_t) then check_mt1 y spairs else false
  in
  let rec check_mt2 mt spairs =
    match mt with 
    | [] -> (true,spairs)
    | x::y -> let (sv1,sv2) = x in
      let (res_h, n_spairs) = try (
        (* let (s,c) = List.find (fun (sv,cand) -> (String.compare sv (CP.name_of_spec_var sv2) == 0)) spairs in *)
        let rec check_spairs spairs (sv1,sv2) = 
          match spairs with
          | [] -> (true,[])
          | x1::y1 -> let (rt,spt) = check_spairs y1 (sv1,sv2) in
            let (s,c) = x1 in
            if(String.compare s (CP.name_of_spec_var sv2) == 0) then (
              match c with 
              | None -> (rt,(s, Some sv1)::spt)
              | Some sv -> if(CP.eq_spec_var sv sv1) then (rt,x1::spt) else (false,x1::spt)
            )	
            else (rt,x1::spt)	  
        in
        check_spairs spairs (sv1,sv2)
      )
        with _ -> (false, spairs)
      in
      if(res_h) then  check_mt2 y n_spairs  else (false, n_spairs)
  in
  let rec check_mts2 smts spairs = 
    match smts with
    | [] -> (false, spairs)
    | (mts1,mts2)::y -> let (rh1,sph) = check_mt2 mts2 spairs in
      let rh2 = check_mt1 mts1 spairs in
      if(rh1&&rh2) then (true, sph) else  check_mts2 y spairs
  in
  if(List.length smts == 0) then (true,spairs) else check_mts2 smts spairs

let process_spairs (smts: ((CP.spec_var * CP.spec_var) list * (CP.spec_var * CP.spec_var) list) list) spairs =
  let pr1a =   pr_list_ln (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) in
  let pr1 =  pr_list_ln (pr_pair pr1a pr1a) in
  let pr_spec_var_option sv = match sv with
    | None -> ""
    | Some x ->  Cprinter.string_of_spec_var x 
  in
  let pr_string str = str in
  let pr2 = pr_list_ln (pr_pair  pr_string pr_spec_var_option) in
  let pr4 b = if(b) then "VALID\n" else "INVALID\n" in
  let pr3 = pr_pair pr4 pr2 in
  Debug.no_2 "process_spairs" pr1 pr2 (pr3)
    (fun _ _ -> process_spairs_x smts spairs) smts spairs

let check_equiv_def_x hvars (def1: (CF.formula * CF.formula)) (def2: (CF.formula * CF.formula)) (hp_map, spairs) =
  (*def means 1st element is the only HP*)
  let hp,_ = def2 in
  let () = if(List.length (CF.get_hp_rel_name_formula hp) == 0) then report_error no_pos "lhs is not only HP" in

  let hp =  List.hd (CF.get_hp_rel_name_formula hp) in

  let add_hp_map (hps,hp) hp_map =
    try
      let (cands, _) = List.find (fun (hps1,hp1) -> CP.eq_spec_var hp hp1) hp_map in
      let new_ele = (remove_dups_svl (cands@hps), hp) in
      let tmp_hp_map = List.filter (fun (_,hp1) -> not(CP.eq_spec_var hp hp1)) hp_map in
      tmp_hp_map@[new_ele]
    with 
    |Not_found -> hp_map@[(hps,hp)]
  in
  let rec find_ovars spairs = match spairs with
    | [] -> []
    | (v,o)::y -> let h = match o with
      | None -> []
      | Some x -> [CP.string_of_spec_var x] 
      in
      h@(find_ovars y)
  in
  let ovars = find_ovars spairs in  
  let svars,_ = List.split spairs in  
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
  let rec helper mt (hp1,hp2) hp_map ovars svars = 
    match mt with
    | [] -> ([],([],[]))
    | x::y -> let a = is_hold x (hp1, hp2) hp_map in
      let (x1,x2) = x in
      let b =  List.exists (fun t -> String.compare t (CP.name_of_spec_var x1) == 0) ovars in
      let c =  List.exists (fun t -> String.compare t (CP.name_of_spec_var x2) == 0) svars in
      let (n1,(n2,n3)) = helper y (hp1,hp2) hp_map ovars svars in
      let n11 = if(a) then x::n1 else n1 in
      let n21 = if(b) then x::n2 else n2 in
      let n31 = if(c) then x::n3 else n3 in
      (n11,(n21,n31))
  in 
  let hp1,_ = def1 in
  let hp2,_ = def2 in
  let (hp1, hp2) =  ((List.hd (CF.get_hp_rel_name_formula hp1)),(List.hd  (CF.get_hp_rel_name_formula hp2))) in
  let m,mtl = check_equiv_2f hvars def1 def2 true in (*bool, map_table_list*)
  if(m)then
    (
      let rel_mtl = List.map (fun mt -> helper mt (hp1, hp2) hp_map ovars svars ) mtl in 
      (* let () = Debug.ninfo_zprint (lazy ("***Relation. MTL: " ^ (string_of_map_table_list rel_mtl))) no_pos in *)
      let tmp = List.filter (fun (rmt,_) -> List.length rmt == 0) rel_mtl in
      if(List.length tmp > 0) then (
        let _,smts = List.split tmp in 
        (* let smts = List.filter (fun (b,c) ->( List.length b > 0) || (List.length c > 0)) smts in *)
        let (r,new_spairs) =  process_spairs smts spairs  in
        if(r) then (add_hp_map ([hp1],hp) hp_map,new_spairs) else (add_hp_map ([],hp) hp_map,new_spairs)
      )
      else (add_hp_map ([],hp) hp_map,spairs)
    )
  else (add_hp_map ([],hp) hp_map,spairs)

let check_equiv_def hvars def1 def2 (hp_map,spairs) =
  let pr1 = pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula in
  let pr4 = pr_list_ln (pr_pair Cprinter.string_of_spec_var_list Cprinter.string_of_spec_var) in
  let pr_spec_var_option sv = match sv with
    | None -> ""
    | Some x ->  Cprinter.string_of_spec_var x 
  in
  let pr_string str = str in
  let pr2 = pr_list_ln (pr_pair pr_string pr_spec_var_option) in
  let pr3 = pr_pair pr4 pr2 in
  Debug.no_2 "check_equiv_def" pr1 pr1 (pr3)
    (fun _ _ ->  check_equiv_def_x hvars def1 def2 (hp_map,spairs)) def1 def2

let match_def_x hvars defs def (hp_map,spairs) =
  let match_def_helper hvars idef def2 (hp_map,spairs)=
    let (rc, hf, f) = CF.flatten_hp_rel_def_wo_guard idef in
    let def1 = (CF.formula_of_heap hf no_pos, f) in
    check_equiv_def hvars def1 def2 (hp_map,spairs)
  in
  let (new_hp_map,new_spairs) = List.fold_left (fun piv idef ->  match_def_helper hvars idef def piv) (hp_map,spairs) defs in
  (new_hp_map,new_spairs)

let match_def hvars defs def (hp_map,spairs) =
  let pr1 = pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr4 = pr_list_ln (pr_pair Cprinter.string_of_spec_var_list Cprinter.string_of_spec_var) in
  let pr_spec_var_option sv = match sv with
    | None -> ""
    | Some x ->  Cprinter.string_of_spec_var x
  in
  let pr_string str = str in
  let pr5 = pr_list_ln (pr_pair  pr_string pr_spec_var_option) in
  let pr3 = pr_pair pr4 pr5 in
  Debug.no_2 "match_def" pr2 pr1 (pr3)
    (fun _ _ -> match_def_x hvars defs def (hp_map,spairs)) defs def


let checkeq_defs_x hvars svars (defs: CF.hp_rel_def list) ( infile_defs: (CF.formula * CF.formula) list) =
  let spairs = List.map (fun c -> (c,None)) svars in
  let no_change hp_mt1 hp_mt2 =
    let size_of_mt hp_mt = List.fold_left (fun piv (hps,hp) -> piv + List.length hps) 0 hp_mt in
    (size_of_mt hp_mt1 == size_of_mt hp_mt2)
  in
  let rec helper hvars defs1 defs2 (hp_mt,spairs)=
    let (hp_map1,new_spairs) = List.fold_left (fun piv def -> match_def hvars defs1 def piv) (hp_mt,spairs) defs2 in
    if(no_change hp_map1 hp_mt) then  (*terminate condition*)
      (hp_map1,new_spairs)
    else 
      helper hvars defs1 defs2 (hp_map1,new_spairs)
  in
  let (map,new_spairs) = helper hvars defs infile_defs ([],spairs) in
  let rec refine_spairs spairs= match spairs with
    | [] -> []
    | (c,o)::y -> match o with
      | None -> refine_spairs y 
      | Some x -> let new_c = CP.SpecVar (CP.type_of_spec_var x, c, Unprimed) in (x,new_c)::(refine_spairs y) (*reverse ocurr here*)
  in
  (map,refine_spairs new_spairs)

let checkeq_defs hvars svars (defs: CF.hp_rel_def list) ( infile_defs: (CF.formula * CF.formula) list) =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr5 = pr_list_ln (pr_pair Cprinter.string_of_spec_var_list Cprinter.string_of_spec_var) in
  let pr4 = pr_list_ln (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) in
  let pr3 = (pr_pair pr5 pr4) in
  Debug.no_2 "check_defs" pr2 pr1 (pr3)
    (fun _ _ -> checkeq_defs_x hvars svars defs infile_defs) defs infile_defs

let checkeq_defs_bool hvars svars (defs: CF.hp_rel_def list) ( infile_defs: (CF.formula * CF.formula) list) inf_vars=
  let  (mtb,_)  = checkeq_defs hvars svars defs infile_defs in
  (* let (mtb,smap) = process_svars full_tb svars inf_vars in *)
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

let check_equiv_def_with_diff hvars svars (def1: (CF.formula * CF.formula)) (def2: (CF.formula * CF.formula)) hp_map spairs =
  let is_hp_pair p (hp1, hp2) hp_map =
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
    | x::y -> if(is_hp_pair x (hp1, hp2) hp_map) then x::(helper y (hp1,hp2) hp_map) else (helper y  (hp1,hp2) hp_map)
  in 
  let hp1,_ = def1 in
  let hp2,_ = def2 in
  let (hp1, hp2) =  ((List.hd (CF.get_hp_rel_name_formula hp1)),(List.hd  (CF.get_hp_rel_name_formula hp2))) in
  let m,mtl = check_equiv_2f_with_diff hvars def1 def2 spairs true in (*bool, map_table_list*)
  if(m)then
    (
      let rec get_min_mt mts =
        match mts with
        | [] -> report_error no_pos "check_equiv_def_with_diff: eliminated already."
        | [x] -> (List.length x,[x])
        | hd::tl -> (
            let (t,mts1) = get_min_mt tl in
            let c = List.length hd in
            if(c < t) then (c, [hd])
            else if(c == t) then (c,hd::mts1)
            else (t,mts1)
          )	  
      in
      let rel_mtl = List.map (fun (mt,fs1,fs2) -> helper mt (hp1, hp2) hp_map) mtl in 
      let tmp = List.exists (fun mt -> List.length mt == 0) rel_mtl in
      let (_,mts) = get_min_mt rel_mtl in
      if(tmp) then (m,mtl,[]) else (m,mtl,mts)
    )
  else (m,mtl,[])

let checkeq_defs_with_diff_x hvars svars (defs: CF.hp_rel_def list)
    ( infile_defs: (CF.formula * CF.formula) list) inf_vars :  (bool*(((CF.formula * CF.formula) *  (CF.formula * CF.formula) * ((map_table * (CF.formula * CF.formula)*(CF.formula * CF.formula)) list)) list))=
  let  (mtb,spairs)  = checkeq_defs hvars svars defs infile_defs in
  (* let pr3 = pr_list_ln (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) in *)
  (* print_string ("smap: "^(pr3 spairs)^ "\n"); *)
  (* let pr4 = pr_list_ln (pr_pair Cprinter.string_of_spec_var_list Cprinter.string_of_spec_var) in *)
  (* print_string ("current map: "^(pr4 mtb)^ "\n"); *)
  let exists_helper v1 v2 mtb =
    let exist v1 v2 mt =
      let (ls, key) = mt in
      CP.eq_spec_var v2 key && List.exists (fun c -> CP.eq_spec_var c v1) ls
    in
    let res = List.fold_left (fun piv mt -> if(piv) then true else if(exist v1 v2 mt) then true else false) false mtb in
    res
  in
  let find_hpdef v1 v2 parent=
    try (
      let check_hp hp v =
        let hp_names = CF.get_hp_rel_name_formula hp in
        let hp_name = match hp_names with
          | [x] -> x
          | _ -> report_error no_pos "check_defs: should be the only HP"
        in
        CP.eq_spec_var hp_name v
      in
      let def1 = List.find (fun def ->
          let (_,hp,_) = CF.flatten_hp_rel_def_wo_guard def in
          (* let () = print_endline ("Diff Hp: " ^ (Cprinter.string_of_h_formula hp)) in *)
          check_hp (CF.formula_of_heap hp no_pos) v1) defs in
      let def2 = List.find (fun (hp,_) -> check_hp hp v2) infile_defs in
      let (a,b,c) = CF.flatten_hp_rel_def_wo_guard def1 in
      Some ((CF.formula_of_heap b no_pos,c),def2)
    )
    with Not_found -> if(parent) then
        report_error no_pos ("Diff HP: "^Cprinter.string_of_spec_var v1 ^" " ^Cprinter.string_of_spec_var v2 ^" not found in either defs or infile_defs")
      else None
  in
  let modify_mtl d1 d2 mtl hps=
    let find_hrel hprel_name hrs pv = 
      let res =
        try (
          let hr = List.find (fun (n,_,_) -> CP.eq_spec_var n hprel_name) hrs in
          CF.HRel hr
        )
        with Not_found -> CF.HEmp
      in
      CF.mkStarH res pv no_pos
    in
    let (_,f1) = d1 in
    let (_,f2) = d2 in
    let hrs1, hrs2 = CF.get_hprel f1,CF.get_hprel f2 in
    let (diff1,diff2) = List.fold_left (fun (pv1,pv2) (a,b) -> (find_hrel a hrs1 pv1,find_hrel b hrs2 pv2)) (CF.HEmp, CF.HEmp) hps in
    List.map (fun (mt,(a,df1),(b,df2)) -> (mt, (a,CF.formula_of_heap diff1 no_pos), (b,CF.formula_of_heap diff2 no_pos))) mtl
  in
  let mixs = List.map (fun c -> (exists_helper c c mtb,c)) inf_vars in
  let rs,vars = List.split mixs in
  let _,remain_vars = List.split (List.filter (fun (r,v) -> r == false) mixs) in
  let res = not (List.exists (fun c -> not(c)) rs) in
  let res = if(List.length remain_vars == 0) then true else res in 
  if(res) then (res,[])
  else (
    let rec check_hps pair_vars checking parent= ( 
      let check_one_def v1 v2 =
        let () = Debug.ninfo_hprint (add_str "v1 " (!CP.print_sv)) v1 no_pos in
        let () = Debug.ninfo_hprint (add_str "v2 " (!CP.print_sv)) v2 no_pos in
        let ds = find_hpdef v1 v2 parent in
        match ds with
        | Some (d1,d2) -> (
            let b,mtl,new_hps =  check_equiv_def_with_diff hvars svars d1 d2 mtb spairs in
            if(b) then
              if(List.length new_hps == 0) then ((* print_string "the cp diff show Success but really fail"; *) []) 
              else 
                (
                  let hps = List.hd new_hps in (*choose one only *)	
                  let check_term = List.exists (fun (a1,b1) -> List.exists (fun (a2,b2) -> (CP.eq_spec_var a1 a2 && CP.eq_spec_var a2 b2)) hps) (checking@pair_vars) in
                  let parent_def = (d1,d2,modify_mtl d1 d2 mtl hps) in
                  if(check_term) then [parent_def] else 
                    let (_,new_diff) = check_hps hps (checking@pair_vars) false in
                    parent_def::new_diff
                )
            else [(d1,d2,mtl)]
          )
        | None -> (
            report_error no_pos "checkeq_defs_with_diff: have not handled if the def of diff predicates can not be found "
          )
      in 
      let res_pairs = List.map (fun (v1,v2) -> let res = check_one_def v1 v2 in
                                 if(List.length res == 0) then ([(v1,v2)],res) else ([],res)) pair_vars in
      let trues, diffs = List.split res_pairs in
      (List.concat trues, List.concat diffs)
    )
    in
    let pair_vars = List.map (fun v-> (v,v)) remain_vars in
    let (trues, diffs) = check_hps pair_vars [] true in
    let true_vars = List.map (fun (a,_) -> a) trues in
    let remain_vars = List.filter (fun c -> not (List.exists (fun b -> CP.eq_spec_var b c) true_vars)) remain_vars in
    let res = if(List.length remain_vars == 0) then true else res in
    (res,diffs) 
    (*TODO: here, b can used to decide if it's actually false or just false with HP diff_name (check again here)*)   
  )

let checkeq_defs_with_diff hvars svars (defs: CF.hp_rel_def list) ( infile_defs: (CF.formula * CF.formula) list) inf_vars =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr4 b = if(b) then "VALID" else "INVALID" in
  let pr5 = pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula in
  let pr6 = pr_list_ln (pr_triple string_of_map_table pr5 pr5) in
  let pr7 =pr_list_ln (pr_triple pr5 pr5 pr6) in
  Debug.no_2 "checkeq_defs_with_diff" pr2 pr1 (pr_pair pr4 pr7)
    (fun _ _ -> checkeq_defs_with_diff_x hvars svars defs infile_defs inf_vars) defs infile_defs

let check_subsume hvars def1 def2 =
  let pr1 = (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let () = print_string ("Check subsume, \nf1: "^ pr1 def1 ^ "\nf2: " ^ pr1 def2 ^ "\n") in
  ()

let check_subsume_defs_x hvars svars (defs: CF.hp_rel_def list)
    ( infile_defs: (CF.formula * CF.formula) list) inf_vars =
  let (res, diffs) = checkeq_defs_with_diff hvars svars defs infile_defs inf_vars in
  if(res) then (res,diffs,[])
  else (
    let get_hrel_hform h =
      match h with
      | CF.HRel  (rl,_,_) -> (true,[rl])
      | _ ->  (false, [])
    in
    let rec get_hrel_form f =
      match f with
      | CF.Or ({CF.formula_or_f1 = f1;
                CF.formula_or_f2 = f2})  -> (
          let (r1,hps1) = get_hrel_form f1 in(*right order, TODO: consider other cases*)
          let (r2,hps2) = get_hrel_form f1 in
          if(r1&&r2) then (true, hps1@hps2)
          else (false,[])
        )
      |CF.Base({CF.formula_base_heap = h}) -> get_hrel_hform h
      |CF.Exists({CF.formula_exists_heap = h })-> get_hrel_hform h
    in
    let check_subsume_helper f1 f2 mixmts (subsumes, remains) = 
      let hp1,_ = f1 in
      let hp2,_ = f2 in
      let (hp1, hp2) =  ((List.hd (CF.get_hp_rel_name_formula hp1)),(List.hd  (CF.get_hp_rel_name_formula hp2))) in
      let rec helper mixmts = match mixmts with
        | [] -> ([],[])
        | x::y -> (
            let (s_t,r_t) = helper y in
            if(List.length s_t > 0) then (s_t,r_t)
            else (
              let (mt,(_,d1),(_,d2)) = x in
              let res1,rs1 =  get_hrel_form d1 in
              let res2,rs2 =  get_hrel_form d2 in
              if(res1 && res2 && List.length rs1 == List.length rs2) then (
                let pairs = List.combine rs1 rs2 in 
                let check_each_pair (r1,r2) (v1,v2) = (
                  if(CP.eq_spec_var r1 hp1) then (v1+1,v2)
                  else if(CP.eq_spec_var r2 hp2) then (v1,v2+1)
                  else (
                    (* let pr3 = pr_list_ln (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var  ) in *)
                    (* print_string ("Check with subsumes: "^ pr3 ([(r1,r2)]) ^ "\n"); *)
                    let check1 = List.exists (fun (hr1,hr2,r) ->r && CP.eq_spec_var r1 hr1 && CP.eq_spec_var r2 hr2) subsumes in
                    let check2 = List.exists (fun (hr1,hr2,r) -> (not r) && CP.eq_spec_var r1 hr1 && CP.eq_spec_var r2 hr2) subsumes in
                    if(check1) then (v1+1,v2)
                    else if(check2) then (v1,v2+1)
                    else (v1,v2)
                  )
                ) 
                in
                let (v1,v2) = List.fold_left (fun piv pair -> check_each_pair pair piv) (0,0) pairs in
                let l = List.length pairs in
                if(v1 == l) then ([(hp1,hp2,true)],[])
                else if (v2 == l) then ([(hp1,hp2,false)],[])
                else if(v1+v2 == l) then ([],r_t)
                else ([],x::r_t)
              )
              else ([],[])
            )
          )
      in
      let (s,r_mix) = helper mixmts in 
      (s@subsumes, (f1,f2,r_mix)::remains)
    in

    let rec helper (subsumes, remains) = 
      (* let pr3 = pr_list_ln (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var  ) in *)
      (* print_string ("Subsumes: "^pr3 subsumes ^ "\n"); *)
      let (subsume_list, remain_diffs) = List.fold_left (fun piv (f1,f2,mixmts) -> check_subsume_helper f1 f2 mixmts piv) (subsumes,[]) remains in
      if(List.length subsumes == List.length subsume_list) then  (*terminate condition*)
        (subsume_list, remain_diffs)
      else 
        helper (subsume_list, remain_diffs)
    in
    let (r,_) = helper ([],diffs) in
    (res,diffs,r)
  )

let check_subsume_defs hvars svars (defs: CF.hp_rel_def list) ( infile_defs: (CF.formula * CF.formula) list) inf_vars =
  let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr4 b = if(b) then ">=" else "<=" in
  let pr3 = pr_list_ln (pr_triple Cprinter.string_of_spec_var Cprinter.string_of_spec_var pr4 ) in (*a >= b*)
  let pr5 b = let (_,_,c) = b in pr3 c in 
  Debug.no_2 "check_subsume_defs" pr2 pr1 (pr5)
    (fun _ _ -> check_subsume_defs_x hvars svars defs infile_defs inf_vars) defs infile_defs

let check_subsume_defs_tmp hvars svars (defs: CF.hp_rel_def list) ( infile_defs: (CF.formula * CF.formula) list) inf_vars =
  let (r,rl,sl) = check_subsume_defs hvars svars defs infile_defs inf_vars in
  let check_subsume r sl =
    let (f1,f2,_) = r in
    let hp1,_ = f1 in
    let hp2,_ = f2 in
    let (hp1, hp2) =  ((List.hd (CF.get_hp_rel_name_formula hp1)),(List.hd  (CF.get_hp_rel_name_formula hp2))) in
    List.exists (fun (r1,r2,_) ->  CP.eq_spec_var r1 hp1 && CP.eq_spec_var r2 hp2) sl
  in
  let new_rl = List.fold_left (fun piv r ->
      let c = check_subsume r sl in
      if(c) then piv else r::piv
    ) [] rl in
  if(List.length new_rl == 0) then (true, [],sl)
  else (r,new_rl,sl)

let gen_cpfile prog proc hp_lst_assume ls_inferred_hps dropped_hps old_hpdecls sel_hp_rels cout_option = 
  let save_names = List.map (fun hp-> hp.Cast.hp_name) old_hpdecls in
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
                  if(check_dupl new_name) then (
                    add name root_var ((vn,("",indx)::m)::y)
                  )
                  else (
                    let n_var =  CP.SpecVar (typ,new_name,p) in
                    (n_var, (vn,(name,indx)::m)::y)
                  )
                )
            )
            else (
              let (n,vns) = add name root_var y in
              (n,(vn,m)::vns)
            )
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
  let simplify_varname  sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls name_mtb =
    (* print_string " simplify_varname\n"; *)
    let  hp_lst_assume = List.map (fun hp -> (hp.CF.hprel_lhs,hp.CF.hprel_rhs)) hp_lst_assume in
    let change_hp f = x_add CF.subst name_mtb f in
    let ls_inferred_hps =   List.map (fun (_,hf,f2) -> (change_hp (CF.formula_of_heap hf no_pos), change_hp f2))  ls_inferred_hps  in
    let sim_each_ass (f1,f2) mtb vnames =
      let all_vars = CP.remove_dups_svl (CF.fv f1 @ CF.fv f2) in
      let all_vars = List.filter (fun v-> not(List.exists (fun sv -> CP.eq_spec_var sv v) sel_hp_rels)) all_vars in			
      let (new_mtb,vns) = List.fold_left (fun (curr_mtb,curr_vnames) var -> 
          let (new_var,new_vnames) = get_new_var var curr_vnames in
          ((var,new_var)::curr_mtb, new_vnames) ) ([],vnames) all_vars 
      in
      let rename_hp f = x_add CF.subst new_mtb f in
      let filter_hp vnames = List.filter (fun (v,_) -> CP.is_hprel_typ v) vnames in
      let filter_mtb mtb = List.filter (fun (v,_) -> CP.is_hprel_typ v) mtb in
      ((rename_hp f1,rename_hp f2),(filter_mtb new_mtb)@mtb,filter_hp vns)
    in 
    let rename_all hpdecls hp_mtb = 
      let rename_one hpdecl hp_mtb = 
        let name = hpdecl.Cast.hp_name in
        let vars, insts = (List.split hpdecl.Cast.hp_vars_inst) in
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
                         Cast.hp_vars_inst = List.combine new_vars insts})]
        )
        with
        | Not_found -> []
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
    (hpdecls,hp_lst_assume,ls_inferred_hps)
  in
  let string_of_hp_decls hpdecls = 
    (
      let string_of_hp_decl hpdecl =
        (
          let name = hpdecl.Cast.hp_name in
          let pr_arg arg = 
            let t = CP.type_of_spec_var arg in 
            let arg_name = Cprinter.string_of_spec_var arg in
            let arg_name = if(String.compare arg_name "res" == 0) then fresh_name () else arg_name in
            (CP.name_of_type t) ^ " " ^ arg_name
          in
          let pr_inst (sv, i) = (pr_arg sv) ^ (if i=NI then "@NI" else "") in
          let args = pr_lst ", " pr_inst hpdecl.Cast.hp_vars_inst in
          "HeapPred "^ name ^ "(" ^ args ^ ").\n"
        )
      in
      List.fold_left (fun piv e -> piv ^ string_of_hp_decl e) "" hpdecls 
    )
  in
  let string_of_message sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls = 
    let hp_decls = string_of_hp_decls hpdecls in
    let pr_ass f1 f2 (x,y) = (f1 x)^" --> "^(f2 y) in
    let pr1 =  pr_lst ";\n" (pr_ass Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
    let ass_cont = pr1 hp_lst_assume in
    let hpdefs_cont =  pr1 ls_inferred_hps in 
    let ass = "ass " ^ (!CP.print_svl sel_hp_rels) ^ "[]: {\n" ^ ass_cont ^ "\n}\n" in
    let hpdefs = "hpdefs " ^ (!CP.print_svl sel_hp_rels) ^ "[]: {\n"  ^ hpdefs_cont ^ "\n}\n"in
    let test_comps = ass ^ hpdefs  in
    let unmin_name = Cast.unmingle_name proc.Cast.proc_name in
    let expected_res = "SUCCESS" in (*TODO: final res here (in inference, often SUCCESS*)
    let message = hp_decls ^ "\n" ^ unmin_name ^":" ^ expected_res ^"[\n" ^ test_comps ^ "]\n" in
    message
  in
  let () = Gen.Profiling.push_time "Gen cp file" in
  let file_name = !Globals.cpfile in
  let hpdecls = prog.Cast.prog_hp_decls in
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
                                      Cast.hp_vars_inst = List.map (fun sv -> (sv, I)) new_hp_vars}) in
      (new_hpdecl::[hpdecl],[(sv,new_sv)])
    )
    with 
    | Not_found -> ([hpdecl],[])
  in
  let pairs = List.map (fun c-> revise_hpdecls c dropped_hps) hpdecls in
  let e1,e2 = List.split pairs in
  let hpdecls = List.concat e1 in
  let name_mtb = List.concat e2 in (*mtb: name --> new_name*)
  let (hpdecls1,hp_lst_assume1, ls_inferred_hps1) = simplify_varname sel_hp_rels hp_lst_assume ls_inferred_hps hpdecls name_mtb in
  let message = string_of_message sel_hp_rels hp_lst_assume1 ls_inferred_hps1 hpdecls1 in
  let () = try
      (
        match cout_option with
        | Some cout -> Printf.fprintf cout "%s\n" message;   (* write something *)
        | _ -> ()
      )
    with Sys_error _ as e ->
      Format.printf "Cannot open file \"%s\": %s\n" file_name (Printexc.to_string e)
  in
  let () = Gen.Profiling.pop_time "Gen cp file" in
  ()

let validate proc hp_lst_assume inferred_hp_defs sel_hp_rels =
  let print_res_list rl def=
    let pr1 =  pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula in
    (* let pr_mix_mtl =   pr_list_ln (pr_triple CEQ.string_of_map_table pr1 pr1) in *)
    let pr_res (c1,c2,mtb) =
      if(List.length mtb == 0) then  "no-diff-info"
      else (
        let (_,d1,d2) = List.hd mtb in
        if(def) then "Infer def: " ^ pr1 c1 ^ "\nExpected def: " ^ pr1 c2 ^ "\nDiff1: " ^ pr1 d1 ^ "\nDiff2: " ^ pr1 d2
        else "Infer constr: " ^ pr1 c1 ^ "\nExpected constr: " ^ pr1 c2 ^ "\nDiff1: " ^ pr1 d1 ^ "\nDiff2: " ^ pr1 d2
      )
    in
    List.fold_left (fun piv sr -> piv  ^ sr ^ "\n" ) "" (List.map (fun r -> (pr_res) r) rl)
  in

  let is_match_constrs il constrs =
    if((!Globals.dis_show_diff)) then
      checkeq_constrs il (List.map (fun hp -> hp.CF.hprel_lhs,hp.CF.hprel_rhs) hp_lst_assume) constrs
    else
      let res,res_list = checkeq_constrs_with_diff il (List.map (fun hp -> hp.CF.hprel_lhs,hp.CF.hprel_rhs) hp_lst_assume) constrs in
      if(not(res)) then
        print_string ("\nDiff constrs " ^ proc.Cast.proc_name ^ " {\n" ^ (print_res_list res_list false) ^ "\n}\n" );
      res
  in
  let is_match_defs il sl defs =
    let res,res_list,sl =
      if(!Globals.sa_subsume) then (
        check_subsume_defs_tmp il sl inferred_hp_defs defs sel_hp_rels
      )
      else  let (r,rl) = checkeq_defs_with_diff il sl inferred_hp_defs defs sel_hp_rels in
        (r,rl,[])
    in
    let pr1 b = if(b) then ">=" else "<=" in
    let pr2 = pr_list_ln (pr_triple Cprinter.string_of_spec_var Cprinter.string_of_spec_var pr1 ) in
    let () = if(not(res)) then (
        if(List.length sl > 0) then print_string ("SUBSUME: "^ pr2 sl ^"\n") ;
        if(not !Globals.dis_show_diff) then ( print_string ("\nDiff defs " ^ proc.Cast.proc_name ^ " {\n" ^ (print_res_list res_list true) ^ "\n}\n" ));
      )
      else (if(List.length sl > 0) then print_string ("SUCCESS WITH SUBSUME: "^ pr2 sl ^"\n");)
    in
    res
  in
  let () = Gen.Profiling.push_time "Validating" in
  let () = print_endline_quiet ("Validating procedure " ^ proc.Cast.proc_name ^ "....") in
  let test_comps = proc.Cast.proc_test_comps in
  let (res1, res2) =
    match test_comps with
    | None ->(false,false)
    | Some (tcs) -> (
        let ass = tcs.Cast.expected_ass in
        let hpdefs = tcs.Cast.expected_hpdefs in
        match ass,hpdefs with
        | None, None -> (false, false)
        | Some (il,sl,a), None -> (is_match_constrs il a, false)
        | None, Some (il,sl,d) -> (false, is_match_defs il sl d)
        | Some (il1,sl1,a), Some (il2,sl2,d) ->  (is_match_constrs il1 a, is_match_defs il2 sl2 d)
      )
  in
  let is_have_tc = match test_comps with
    | None -> false
    | _ -> true
  in
  let _ =
    if(is_have_tc) then(
      let () = 
        if res1 && res2 then
          print_endline_quiet ("Validate " ^ proc.Cast.proc_name ^ " SUCCESS.")
        else
          let f_ass_msg = if not res1 then "assumption" else "" in
          let f_msg = if not res2 then f_ass_msg ^ " definition" else f_ass_msg in
          print_endline_quiet ("Validate " ^ proc.Cast.proc_name ^ " FAIL. (at " ^ f_msg ^")")
          (* let () = if(res1) then *)
          (*           print_string ("Validate assumption: " ^ proc.Cast.proc_name ^ " SUCCESS\n" ) *)
          (*         else *)
          (*           print_string ("Validate assumption: " ^ proc.Cast.proc_name ^ " FAIL\n" ) *)
          (* in *)
          (* let () = if(res2) then *)
          (*           print_string ("Validate shape: " ^ proc.Cast.proc_name ^ " SUCCESS\n" ) *)
          (*         else *)
          (*           print_string ("Validate shape: " ^ proc.Cast.proc_name ^ " FAIL\n" ) *)
      in
      ()
    )
    else print_string ("!!! Warning: There are no cp info for " ^ proc.Cast.proc_name ^ "\n" )
  in
  let () = Gen.Profiling.pop_time "Compare res with cp file" in
  ()


let update_lib_x hpdefs hp_defs sel_hps=
  let update_lib_one hp_def=
    match hp_def.Cformula.def_cat with
    | CP.HPRelDefn (hp,_,_) -> begin if CP.mem_svl hp sel_hps then
          try
            let def = Cformula.look_up_hpdef hpdefs hp in
            match def.Cformula.hprel_def_body_lib with
            | [] -> hp_def
            | [(f,oflow)] -> {hp_def with Cformula.def_rhs = [(f,None)]}
            | fs -> {hp_def with Cformula.def_rhs = List.map (fun (f, _) -> (f,None)) fs}
          with _ -> hp_def
        else hp_def
      end
    | _ -> hp_def
  in
  List.map update_lib_one hp_defs

let update_lib hpdefs hp_defs sel_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_3 "update_lib" pr1 pr2 !CP.print_svl pr2
    (fun _ _ _ -> update_lib_x hpdefs hp_defs sel_hps)
    hpdefs hp_defs sel_hps;;

Cpure.syn_checkeq := checkeq_p_formula;
