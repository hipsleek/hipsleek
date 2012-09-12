open Globals
open Gen
open Cpure
open Cformula 

module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure

(*for testing-compare two formulas*)

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

(*let rec rm_double_mapping (mt: map_table): map_table = 
if((List.length mt) == 0) then mt else (
  let hd = List.hd mt in
  let tl = List.tl mt in
  if(List.exists (fun c -> c == hd) tl) then (rm_double_mapping tl) else (rm_double_mapping tl)@[hd] 
)*)

let rec checkeq_formulas (hvars: ident list) (f1: CF.formula) (f2: CF.formula)(mtl: (map_table list)): (bool*(map_table list))=
  let _ = Debug.ninfo_pprint ("Compare formulas ") no_pos in 
  match f1 with
    |CF.Base({CF.formula_base_heap = h1;
	      CF.formula_base_pure = p1}) ->(match f2 with 
	|CF.Base ({CF.formula_base_heap = h2;
	      CF.formula_base_pure = p2}) -> (
	  let (res,mtl1) = checkeq_h_formulas hvars h1 h2 mtl in
	  let _ = if(res) then Debug.info_pprint ("Res: " ^ (string_of_map_table_list mtl1)) no_pos in
	  (res,mtl1) (*h formula only*)
	)
	|_ -> report_error no_pos "not handle Or f1 yet") (*(false,mtl))*)
    |CF.Exists({CF.formula_exists_heap = h1;
		CF.formula_exists_pure = p1})->(match f2 with 
	|CF.Exists ({CF.formula_exists_heap = h2;
	      CF.formula_exists_pure = p2}) -> (
	  let (res,mtl1) = checkeq_h_formulas hvars h1 h2 mtl in 
	  let _ = if(res) then Debug.info_pprint ("Res: " ^(string_of_map_table_list mtl1)) no_pos in
	  (res,mtl1)
	)
	|_ -> report_error no_pos "not handle Or f1 yet" )(*(false,mtl))*)
    |CF.Or b1 ->  report_error no_pos "not handle Or f1 yet"
  
and checkeq_h_formulas (hvars: ident list)(hf1: CF.h_formula) (hf2: CF.h_formula)(mtl: map_table list): (bool * (map_table list))=
  let _ = Debug.ninfo_pprint ("Compare heap formulas ") no_pos in
(*create list*)
  let check_false_hf1 = check_false_formula hf1 in
  let check_false_hf2 = check_false_formula hf2 in
  if(check_false_hf1 && check_false_hf2) then (true, [])
  else if(check_false_hf1 || check_false_hf2) then (false,[])
  else(
let _ = Debug.ninfo_pprint ("Compare h_formula1: " ^ (Cprinter.string_of_h_formula hf1)) no_pos in
let _ = Debug.ninfo_pprint ("Compare h_formula2: " ^ (Cprinter.string_of_h_formula hf2)) no_pos in
    match hf1 with  
      | CF.Star ({CF.h_formula_star_h1 = h1;
		  CF.h_formula_star_h2 = h2}) 
      | CF.Phase  ({CF.h_formula_phase_rd = h1;
		    CF.h_formula_phase_rw = h2}) 
      | CF.Conj  ({CF.h_formula_conj_h1 = h1;
		   CF.h_formula_conj_h2 = h2})  ->
	let (ph1, mtl1) = checkeq_h_formulas hvars h1 hf2 mtl in
	let _ = Debug.ninfo_pprint (string_of_map_table_list mtl1) no_pos in
	if(ph1) then checkeq_h_formulas hvars h2 hf2 mtl1 else (false, mtl1)
      | CF.DataNode n -> match_equiv_node hvars n hf2 mtl
      | CF.ViewNode n -> match_equiv_view_node hvars n hf2 mtl
      | CF.Hole h1 -> (match hf2 with
	  |CF.Hole h2 -> (h1 = h2, mtl)
	  |_ -> report_error no_pos "not handle Or f1 yet") (*(false,mtl))*)
      | CF.HRel r  -> (
	let _ = Debug.ninfo_pprint ("Compare relation ") no_pos in
	match_equiv_rel hvars r hf2 mtl
      )
      | CF.HTrue  ->  (true, mtl)
      | CF.HFalse ->  report_error no_pos "not a case"
      | CF.HEmp   ->  (match_equiv_emp hf2, mtl)
  )

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
 (* let _ = if(is_hard) then Debug.info_pprint ("check hard node ") no_pos else  Debug.info_pprint ("check soft node ") no_pos in*)
 
let rec match_equiv_node_helper (hvars: ident list) (n: CF.h_formula_data) (hf2: CF.h_formula)(mt: map_table): (bool * (map_table list)) = match hf2 with 
    | CF.Star ({CF.h_formula_star_h1 = h1;
		CF.h_formula_star_h2 = h2}) 
    | CF.Phase  ({CF.h_formula_phase_rd = h1;
		  CF.h_formula_phase_rw = h2}) 
    | CF.Conj  ({CF.h_formula_conj_h1 = h1;
		 CF.h_formula_conj_h2 = h2})  ->
      let (ph1, mtl1) =  match_equiv_node_helper hvars n h1 mt in
      let (ph2, mtl2) =  match_equiv_node_helper hvars n h2 mt in
      let _ = Debug.ninfo_pprint (string_of_map_table_list mtl1) no_pos in
      let _ = Debug.ninfo_pprint (string_of_map_table_list mtl2) no_pos in
      if(ph1 && ph2) then (true, mtl1 @ mtl2)   (*merge tables*)
      else if(ph1) then (true, mtl1) 
      else if(ph2) then (true, mtl2)
      else (false, mtl)
    | CF.DataNode n2 -> let (res, mt2) = check_node_equiv hvars n n2 mt in (res, [mt2])
    | CF.ViewNode _
    | CF.Hole _
    | CF.HRel _ 
    | CF.HTrue -> (false,mtl)
    | CF.HFalse -> report_error no_pos "not a case"
    | CF.HEmp   -> (false,mtl)
  in
  let res_list = (List.map (fun c -> match_equiv_node_helper hvars n hf2 c) mtl) in
  let (bs, mtls) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let mtl2 = List.concat mtls in
  (b, mtl2) 
    
and check_node_equiv (hvars: ident list)(n1: CF.h_formula_data) (n2:  CF.h_formula_data)(mt: map_table): (bool * map_table)=
  let var1 = n1.CF.h_formula_data_node in
  let name1 = n1.CF.h_formula_data_name in
  let ann1 = n1.CF.h_formula_data_imm in
  let args1 = n1.CF.h_formula_data_arguments in
  let is_hard_n1 = (List.mem (CP.name_of_spec_var n1.CF.h_formula_data_node) hvars) in
  let var2 = n2.CF.h_formula_data_node in
  let name2 = n2.CF.h_formula_data_name in
  let ann2 = n2.CF.h_formula_data_imm in
  let args2 = n2.CF.h_formula_data_arguments in
  let is_hard_n2 = (List.mem (CP.name_of_spec_var n2.CF.h_formula_data_node) hvars) in
  let is_hard = is_hard_n1 || is_hard_n2 in
  if((not (CF.is_eq_node_name name1 name2)) || (is_hard && (not (CP.eq_spec_var var1 var2))) || (not (CF.is_eq_data_ann ann1 ann2))) 
  then( 
    (*let _ = Debug.info_pprint ("diff node diff name diff ann ") no_pos in *)
    (false, mt) 
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
    if(check_head) then check_spec_var_list_equiv hvars (List.tl args1) (List.tl args2) mt1 else (check_head,mt1)
  )

and check_spec_var_equiv (hvars: ident list)(v1: CP.spec_var) (v2: CP.spec_var)(mt: map_table): (bool * map_table )=
  (*do not check type*) 
 let _ = Debug.ninfo_pprint ("name of node:  " ^ (CP.name_of_spec_var v1)) no_pos in 
  let is_hard_v1 = (List.mem (CP.name_of_spec_var v1) hvars) in
  let is_null_var (v: CP.spec_var):bool= 
    let name = CP.name_of_spec_var v in
    let re = Str.regexp_string "flted" in
        try ignore (Str.search_forward re name 0); true
        with Not_found -> false
  in 
  if((is_null_var v1) && (is_null_var v2)) then (true, mt) 
  else
  if((CP.is_null_const v1) || (CP.is_int_const v1) || is_hard_v1) 
  then( 

    let _ = Debug.ninfo_pprint ("null const hard:  " ^ (CP.name_of_spec_var v1)) no_pos in 
    let res = CP.eq_spec_var v1 v2 in
    (res, mt)
  )
  else add_map_rel mt v1 v2


and match_equiv_view_node (hvars: ident list) (n: CF.h_formula_view) (hf2: CF.h_formula)(mtl: map_table list): (bool * (map_table list))=
 (* let _ = if(is_hard) then Debug.info_pprint ("check hard node ") no_pos else  Debug.info_pprint ("check soft node ") no_pos in*)
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
      else (false, mtl) 
    | CF.DataNode n2 -> (false,mtl) 
    | CF.ViewNode n2 -> let (res, mt2) = check_view_node_equiv hvars n n2 mt in (res, [mt2])
    | CF.Hole _
    | CF.HRel _ 
    | CF.HTrue -> (false,mtl)
    | CF.HFalse -> report_error no_pos "not a case"
    | CF.HEmp   -> (false,mtl)
  in
  let res_list = (List.map (fun c -> match_equiv_view_node_helper hvars n hf2 c) mtl) in
  let (bs, mtls) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let mtl2 = List.concat mtls in
  (b, mtl2) 

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
  then( 
    (*let _ = Debug.info_pprint ("diff node diff name diff ann ") no_pos in *)
    (false, mt) 
  )
  else  (
    let _ = Debug.ninfo_pprint ("match node: " ^ string_of_map_table mt) no_pos in
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
      else (false, mtl) 
    | CF.DataNode _ 
    | CF.ViewNode _  
    | CF.Hole _ -> (false,mtl) 
    | CF.HRel r2  ->  (
       let _ = Debug.ninfo_pprint ("Find 2nd relation  " ) no_pos in
       let (res, mt2) = check_rel_equiv hvars r r2 mt in (res, [mt2])
    )
    | CF.HTrue  -> (false,mtl) 
    | CF.HFalse ->  report_error no_pos "not a case"
    | CF.HEmp   ->  (false,mtl) 
  in
let _ = Debug.ninfo_pprint ("??? Star mapping   " ^ (Cprinter.string_of_h_formula hf2) ) no_pos in
  let res_list = (List.map (fun c -> match_equiv_rel_helper hvars r hf2 c) mtl) in
  let (bs, mtls) = List.split res_list in
  let b = if( List.exists (fun c -> c==true) bs) then true else false in
  let mtl2 = List.concat mtls in
  (b, mtl2) 

and check_rel_equiv (hvars: ident list) (r1:  (CP.spec_var * (CP.exp list) * loc)) (r2:  (CP.spec_var * (CP.exp list) * loc))(mt: map_table): (bool * map_table)=
  let (n1,el1,l1) = r1 in
  let (n2,el2,l2) = r2 in
  let _ = Debug.ninfo_pprint ("Check rel equiv:  " ^ CP.name_of_spec_var n1 ^ " " ^ CP.name_of_spec_var n2 ) no_pos in
  (*let is_hard_r1 = (List.mem (CP.name_of_spec_var n1) hvars) in *)
  let res = CP.eq_spec_var n1 n2 in (*eq_spec_var means same relation*)
  if(res) then check_exp_list_equiv hvars el1 el2 mt (*check hard var in relation*)
  else (false, mt)

and check_exp_list_equiv (hvars: ident list) (el1: CP.exp list) (el2: CP.exp list) (mt: map_table): (bool * map_table)=
  if((List.length el1) == 0 && (List.length el2) == 0) then (true, mt)
  else(
    let head1 = List.hd el1 in 
    let head2 = List.hd el2 in
    let (check_head, mt1) = match head1 with
      |CP.Var(sv1,_)-> (
	let is_hard = (List.mem (CP.name_of_spec_var sv1) hvars) in
	if(not is_hard) then (
	  match head2 with
	    |CP.Var(sv2,_) -> (add_map_rel mt sv1 sv2)
	    |_ -> (false, mt)
	)
	else match head2 with
	  |CP.Var(sv2,_) -> (CP.eq_spec_var sv1 sv2, mt)
	  |_ -> (false, mt)
      ) 
      |_ -> (true, mt) (*scale down: process only spec var as relation arguments*)
    in
    if(check_head) then (
      let res, mtt = check_exp_list_equiv hvars (List.tl el1) (List.tl el2) mt in 
      (res, mt1@mtt)
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

and add_map_rel (mt: map_table) (v1: CP.spec_var) (v2: CP.spec_var): (bool * map_table) = 
 (* let _ = Debug.ninfo_pprint ("node 1: "  ^ v1 ^ " node2 " ^ v2 ^ "   " ^  string_of_map_table mt) no_pos in*)
  let vn1 = CP.name_of_spec_var v1 in
  let vn2 = CP.name_of_spec_var v2 in
let _ = Debug.ninfo_pprint ("node 1: "  ^ vn1 ^ " node2 " ^ vn2 ^ "   " ^  string_of_map_table mt) no_pos in
  let rec check_exist (vn :ident) (mt: map_table): bool = 
    match mt with 
      | []-> false 
      | [(i1,i2)] -> (String.compare vn (CP.name_of_spec_var i1)) == 0 || (String.compare  vn (CP.name_of_spec_var i2)) == 0 
      | (i1, i2)::y -> (String.compare vn (CP.name_of_spec_var i1)) == 0 || (String.compare vn (CP.name_of_spec_var i2)) == 0  || (check_exist vn y)
  in
  if(List.exists (fun (i1, i2) -> (((String.compare vn1 (CP.name_of_spec_var i1)) == 0 && (String.compare vn2 (CP.name_of_spec_var i2)) == 0)  || ((String.compare vn1 (CP.name_of_spec_var i2)) == 0 && (String.compare vn2 (CP.name_of_spec_var i1)) == 0))) mt) then (
    let _ = Debug.ninfo_pprint ("Exists node 1: "  ^ vn1 ^ " node2 " ^ vn2 ^ "   " ^ string_of_map_table mt) no_pos in
    (true, mt)
  ) else 
    (
      let _ = Debug.ninfo_pprint ("not yet node 1: "  ^ vn1 ^ " node2 " ^ vn2 ^ "   " ^ string_of_map_table mt) no_pos in
      let check_v1 = check_exist vn1 mt in
      let check_v2 = check_exist vn2 mt in
      if(check_v1 || check_v2) then (
	let _ = Debug.ninfo_pprint ("ADD FAIL node 1: "  ^ vn1 ^ " node2 " ^ vn2 ^ "   " ^  string_of_map_table mt) no_pos in
	(false, mt)
      )
      else (let _ = Debug.ninfo_pprint ("ADD: node 1: "  ^ vn1 ^ " node2 " ^ vn2 ^ "   " ^ string_of_map_table ((v1,v2)::mt)) no_pos in 
	    (true, ((v1,v2)::mt))
      )
    )

let subst_with_mt (mt: map_table) (f: CF.formula): CF.formula = 
  CF.subst mt f

